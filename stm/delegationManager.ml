(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


let _debug_delegation_manager = CDebug.create ~name:"delegation-manager"

let log msg =
  if CDebug.get_debug_level "delegation-manager" >= 1 then
  Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type sentence_id = Stateid.t
type ('a,'b) coqtop_extra_args_fn = opts:'b -> string list -> 'a * string list

type link = {
  write_to :  Unix.file_descr;
  read_from:  Unix.file_descr;
}

type execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

type update_request =
  | UpdateExecStatus of sentence_id * execution_status
  | AppendFeedback of sentence_id * (Feedback.level * Loc.t option * Pp.t)

let write_value { write_to; _ } x =
  let data = Marshal.to_bytes x [] in
  let datalength = Bytes.length data in
  log @@ "[M] marshaling " ^ string_of_int datalength;
  let writeno = Unix.write write_to data 0 datalength in
  assert(writeno = datalength);
  flush_all ()

module type Job = sig
  type t
  val name : string
  val binary_name : string
  val pool_size : int
end

type job_id = int option ref

let mk_job_id () = ref None
let cancel_job id =
  match !id with
  | None -> ()
  | Some pid -> Unix.kill pid 9

(* TODO: this queue should not be here, it should be "per URI" but we want to
   keep here the conversion (STM) feedback -> (LSP) feedback *)
let master_feedback_queue = Queue.create ()

let install_feedback send =
  Feedback.add_feeder (fun fb ->
    match fb.Feedback.contents with
    (* | Feedback.Message(Feedback.Info,_,_) -> () idtac sends an info *)
    | Feedback.Message(lvl,loc,m) -> send (fb.Feedback.span_id,(lvl,loc,m))
    | Feedback.AddedAxiom -> send (fb.Feedback.span_id,(Feedback.Warning,None,Pp.str "axiom added"))
      (* STM feedbacks are handled differently *)
    | _ -> ())

let master_feeder = install_feedback (fun x -> Queue.push x master_feedback_queue)

let local_feedback : (sentence_id * (Feedback.level * Loc.t option * Pp.t)) Sel.event =
  Sel.on_queue master_feedback_queue (fun x -> x)

let install_feedback_worker link =
  Feedback.del_feeder master_feeder;
  ignore(install_feedback (fun (id,fb) -> write_value link (AppendFeedback(id,fb))));

module MakeWorker (Job : Job) = struct

let option_name = "-" ^ Str.global_replace (Str.regexp_string " ") "." Job.name ^ "_master_address"

type delegation =
 | WorkerStart : job_id * 'job * ('job -> link -> unit) * string -> delegation
 | WorkerProgress of { link : link; update_request : update_request }
 | WorkerEnd of (int * Unix.process_status)
 | WorkerIOError of exn
type events = delegation Sel.event list

let worker_progress link : delegation Sel.event =
  Sel.on_ocaml_value link.read_from (function
    | Error e -> WorkerIOError e
    | Ok update_request -> WorkerProgress { link; update_request; })

type role = Master | Worker of link

let pool = Queue.create ()
let () = for _i = 0 to Job.pool_size do Queue.push () pool done

let wait_worker pid : delegation Sel.event =
  Sel.on_death_of ~pid (fun reason -> WorkerEnd(pid,reason))

let fork_worker : job_id -> (role * events) = fun job_id ->
  let open Unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0));
  listen chan 1;
  let address = getsockname chan in
  log @@ "[M] Forking...";
  flush_all ();
  let null = openfile "/dev/null" [O_RDWR] 0o640 in
  let pid = fork () in
  if pid = 0 then begin
    (* Children process *)
    dup2 null stdin;
    close chan;
    log @@ "[W] Borning...";
    let chan = socket PF_INET SOCK_STREAM 0 in
    connect chan address;
    let read_from = chan in
    let write_to = chan in
    let link = { write_to; read_from } in
    install_feedback_worker link;
    (Worker link, [])
  end else
    (* Parent process *)
    let () = job_id := Some pid in
    let worker, _worker_addr = accept chan  in (* TODO, error *) (* TODO: timeout *)
    close chan;
    log @@ "[M] Forked pid " ^ string_of_int pid;
    let read_from = worker in
    let write_to = worker in
    let link = { write_to; read_from } in
    (Master, [worker_progress link; wait_worker pid])
;;

let create_process_worker procname job_id job =
  let open Unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0));
  listen chan 1;
  let port = match getsockname chan with
    | ADDR_INET(_,port) -> port
    | _ -> assert false in
  let null = openfile "/dev/null" [O_RDWR] 0o640 in
  let extra_flags = if !Flags.debug then [|"-debug"|] else [||] in
  let args = Array.append  [|procname;option_name;string_of_int port|] extra_flags in
  let pid = create_process procname args null stdout stderr in
  close null;
  let () = job_id := Some pid in
  log @@ "[M] Created worker pid waiting on port " ^ string_of_int port;
  let worker, _worker_addr = accept chan  in (* TODO, error *) (* TODO: timeout *)
  close chan;
  let read_from = worker in
  let write_to = worker in
  let link = { write_to; read_from } in
  install_feedback_worker link;
  log @@ "[M] sending job";
  write_value link job;
  flush_all ();
  log @@ "[M] sent";
  [worker_progress link; wait_worker pid]

let handle_event = function
  | WorkerIOError e ->
     log @@ "[M] Worker IO Error: " ^ Printexc.to_string e;
     (None, [])
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "[M] Worker %d went on holidays" pid;
      Queue.push () pool;
      (None,[])
  | WorkerProgress { link; update_request } ->
      log "[M] WorkerProgress";
      (Some update_request, [worker_progress link])
  | WorkerStart (job_id,job,action,procname) ->
    log "[M] WorkerStart";
    if Sys.os_type = "Unix" then
      let role, events = fork_worker job_id in
      match role with
      | Master ->
        log "[M] Worker forked, returning events";
        (None, events)
      | Worker link ->
        action job link;
        exit 0
    else
      let events = create_process_worker procname job_id job in
      (None, events)

let pr_event = function
  | WorkerEnd _ -> Pp.str "WorkerEnd"
  | WorkerIOError _ -> Pp.str "WorkerIOError"
  | WorkerProgress _ -> Pp.str "WorkerProgress"
  | WorkerStart _ -> Pp.str "WorkerStart"

let worker_available ~jobs ~fork_action : delegation Sel.event =
  Sel.on_queues jobs pool (fun (job_id, job) () ->
    WorkerStart (job_id,job,fork_action,Job.binary_name))

type options = int

let setup_plumbing port = try
  let open Unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  let address = ADDR_INET (inet_addr_loopback,port) in
  log @@ "[PW] connecting to " ^ string_of_int port;
  connect chan address;
  let read_from = chan in
  let write_to = chan in
  let link = { read_from; write_to } in
  (* Unix.read_value does not exist, we use Sel *)
  match Sel.wait [Sel.on_ocaml_value read_from (fun x -> x)] with
  | [Ok (job : Job.t)], _ -> (link, job)
  | [Error exn], _ ->
    log @@ "[PW] error receiving job: " ^ Printexc.to_string exn;
    exit 1
  | _ -> assert false
with Unix.Unix_error(code,syscall,param) ->
  log @@ "[PW] error starting: " ^ syscall ^ ": " ^ param ^ ": " ^ Unix.error_message code;
  exit 1

let parse_options ~opts extra_args =
  match extra_args with
  [ o ; port ] when o = option_name -> int_of_string port, []
  | _ -> assert false (* TODO: error *)

end
