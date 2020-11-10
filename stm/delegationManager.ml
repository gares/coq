(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let debug_delegation_manager = CDebug.create ~name:"delegation-manager"

let log msg =
  if CDebug.get_debug_level "delegation-manager" >= 1 then
  Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type sentence_id = Stateid.t
type ('a,'b) coqtop_extra_args_fn = opts:'b -> string list -> 'a * string list

type link = {
  write_to :  Unix.file_descr;
  read_from:  Unix.file_descr;
  pid : int;
}

let write_value { write_to; _ } x =
  let data = Marshal.to_bytes x [] in
  let datalength = Bytes.length data in
  log @@ "[M] marshaling " ^ string_of_int datalength;
  let writeno = Unix.write write_to data 0 datalength in
  assert(writeno = datalength);
  flush_all ()

let kill_link { pid } () = Unix.kill pid 9

module M = Map.Make(Stateid)

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

type execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

module MakeWorker (Job : Job) = struct

let option_name = "-" ^ Str.global_replace (Str.regexp_string " ") "." Job.name ^ "_master_address"

type dm =
 | WorkerStart : job_id * 'job * ('job -> link -> unit) * string -> dm
 | WorkerProgress of { link : link; sentence_id : sentence_id; result : execution_status }
 | WorkerEnd of (int * Unix.process_status)
type events = dm Sel.event list

let worker_progress link : dm Sel.event =
  Sel.on_ocaml_value link.read_from (function
    | Error e ->
      log @@ "[M] Worker died: " ^ Printexc.to_string e;
      WorkerEnd(0,Unix.WEXITED 0)
    | Ok (sentence_id,result) ->
      log @@ "[M] Worker sent back result for " ^ Stateid.to_string sentence_id ^ "  " ^
        (match result with Success _ -> "ok" | _ -> "ko");
      WorkerProgress { link; sentence_id; result })

type role = Master | Worker of link

let pool = Queue.create ()
let () = for i = 0 to Job.pool_size do Queue.push () pool done

let wait_worker pid : dm Sel.event =
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
    let link = { write_to; read_from; pid } in
    (Worker link, [])
  end else
    (* Parent process *)
    let () = job_id := Some pid in
    let worker, _worker_addr = accept chan  in (* TODO, error *) (* TODO: timeout *)
    close chan;
    log @@ "[M] Forked pid " ^ string_of_int pid;
    let read_from = worker in
    let write_to = worker in
    let link = { write_to; read_from; pid } in
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
  let pid = create_process procname [|procname;option_name;string_of_int port;"-debug"|] null stdout stderr in
  close null;
  let () = job_id := Some pid in
  log @@ "[M] Created worker pid waiting on port " ^ string_of_int port;
  let worker, _worker_addr = accept chan  in (* TODO, error *) (* TODO: timeout *)
  close chan;
  let read_from = worker in
  let write_to = worker in
  let link = { write_to; read_from; pid } in
  log @@ "[M] sending job";
  write_value link job;
  flush_all ();
  log @@ "[M] sent";
  [worker_progress link; wait_worker pid]

let handle_event = function
  | WorkerEnd (0, Unix.WEXITED 0) -> (* dummy *)
      (None, [])
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "[M] Worker %d went on holidays" pid;
      Queue.push () pool;
      (None,[])
  | WorkerProgress { link; sentence_id; result } ->
      log "[M] WorkerProgress";
      (Some (sentence_id,result), [worker_progress link])
  | WorkerStart (job_id,job,action,procname) ->
    log "[M] WorkerStart";
    if false (* Sys.os_type = "Unix" *) then
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
  | WorkerEnd (pid, _status) ->
    Pp.str "WorkerEnd"
  | WorkerProgress _ ->
    Pp.str "WorkerProgress"
  | WorkerStart _ ->
    Pp.str "WorkerStart"

let worker_available ~jobs ~fork_action : dm Sel.event list = [
  Sel.on_queues jobs pool (fun (job_id, job) () ->
    WorkerStart (job_id,job,fork_action,Job.binary_name))
]

type options = int

let rec read_exactly read_from buff off data_size =
  let readno = Unix.read read_from buff off data_size in
  if readno = 0 then (log @@ "[PM] cannot read job"; exit 1)
  else if readno != data_size then read_exactly read_from buff (off + readno) (data_size - readno)
  else ()

let setup_plumbing port = try
  let open Unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  let address = ADDR_INET (inet_addr_loopback,port) in
  log @@ "[PW] connecting to " ^ string_of_int port;
  connect chan address;
  let read_from = chan in
  let write_to = chan in
  let link = { read_from; write_to; pid = 0 } in
  let buff = Bytes.create Marshal.header_size in
  let readno = read read_from buff 0 Marshal.header_size in
  if(readno != Marshal.header_size) then begin
    log @@ "[PW] error receiving job head, read " ^ string_of_int readno ^ " != " ^ string_of_int Marshal.header_size;
    exit 1;
  end;
  let data_size = Marshal.data_size buff 0 in
  let buff = Bytes.extend buff 0 data_size in
  read_exactly read_from buff Marshal.header_size data_size;
  let job : Job.t = Marshal.from_bytes buff 0 in
  (link, job)
with Unix.Unix_error(code,syscall,param) ->
  log @@ "[PW] error starting: " ^ syscall ^ ": " ^ param ^ ": " ^ Unix.error_message code;
  exit 1

let parse_options ~opts extra_args =
  match extra_args with
  [ o ; port ] when o = option_name -> int_of_string port, []
  | _ -> assert false (* TODO: error *)

end
