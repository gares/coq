(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Lwt.Infix
open Lwt_err.Infix

let debug_delegation_manager = CDebug.create ~name:"delegation-manager"

let log msg =
  if CDebug.get_debug_level "delegation-manager" >= 1 then
  Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type sentence_id = Stateid.t
type ('a,'b) coqtop_extra_args_fn = opts:'b -> string list -> 'a * string list

type link = {
  write_to :  Lwt_io.output_channel;
  read_from:  Lwt_io.input_channel;
  pid : int option;
}

let write { write_to; _ } x = Lwt_io.write_value write_to x

let kill_link { pid } () = match pid with
  | Some pid -> Unix.kill pid 9
  | None -> ()

type ('a,'b) corresponding = { on_worker : 'b; on_master : 'a; cancel : 'b }

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

type event =
 | WorkerStart : job_id * 'job * ('job -> link -> unit Lwt.t) * string -> event
 | WorkerDied
 | WorkerProgress of { link : link; sentence_id : sentence_id; result : execution_status }
 | WorkerEnd of (int * Unix.process_status)
type events = event Lwt.t list

let worker_progress link =
  Lwt_io.read_value link.read_from >?= function
    | Result.Error e ->
      log @@ "[M] Worker died: " ^ Printexc.to_string e;
      Lwt.return WorkerDied
    | Result.Ok (sentence_id,result) ->
      log @@ "[M] Worker sent back result for " ^ Stateid.to_string sentence_id ^ "  " ^
        (match result with Success _ -> "ok" | _ -> "ko");
      Lwt.return @@ WorkerProgress { link; sentence_id; result }

type role = Master | Worker of link

let pool = Lwt_condition.create ()
let pool_occupants = ref 0
let pool_size = Job.pool_size

let wait_worker pid =
  Lwt_unix.wait () >>= fun x ->
  decr pool_occupants; Lwt_condition.signal pool ();
  log @@ "[T] vacation request ready";
  Lwt.return @@ WorkerEnd x

let wait_process proc =
  proc#close >>= fun x ->
  decr pool_occupants; Lwt_condition.signal pool ();
  log @@ "[T] vacation request ready";
  Lwt.return @@ WorkerEnd (0,x)

let fork_worker : job_id -> (role * events) Lwt.t = fun job_id ->
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >>= fun () ->
  listen chan 1;
  let address = getsockname chan in
  log @@ "[M] Forking...";
  Lwt_io.flush_all () >!= fun () ->
  openfile "/dev/null" [O_RDWR] 0o640 >>= fun null ->
  let pid = Lwt_unix.fork () in
  if pid = 0 then begin
    (* Children process *)
    dup2 null stdin;
    close chan >>= fun () ->
    log @@ "[W] Borning...";
    let chan = socket PF_INET SOCK_STREAM 0 in
    connect chan address >>= fun () ->
    let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input chan in
    let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output chan in
    let link = { write_to; read_from; pid = None } in
    Lwt.return (Worker link, [])
  end else
    (* Parent process *)
    let () = job_id := Some pid in
    let timeout = sleep 2. >>= fun () -> Lwt.return None in
    let accept = accept chan >>= fun x -> Lwt.return @@ Some x in
    Lwt.pick [timeout; accept] >>= function
      | None ->
          log @@ "[M] Forked worker does not connect back";
          Lwt.return (Master, []) (* TODO, error *)
      | Some (worker, _worker_addr) -> (* TODO: timeout *)
          close chan >!= fun () ->
          log @@ "[M] Forked pid " ^ string_of_int pid;
          let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input worker in
          let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output worker in
          let link = { write_to; read_from; pid = Some pid } in
          Lwt.return (Master, [worker_progress link; wait_worker pid])
;;

let create_process_worker procname job_id job =
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >!= fun () ->
  listen chan 1;
  let port = match getsockname chan with
    | ADDR_INET(_,port) -> port
    | _ -> assert false in
  let proc =
    new Lwt_process.process_none
      (procname,[|procname;option_name;string_of_int port|]) in
  let () = job_id := Some proc#pid in
  log @@ "[M] Created worker pid waiting on port " ^ string_of_int port;
  let timeout = sleep 2. >>= fun () -> Lwt.return None in
  let accept = accept chan >>= fun x -> Lwt.return @@ Some x in
  Lwt.pick [timeout; accept] >>= function
  | None -> log @@ "[M] Created worker does not connect back"; Lwt.return [] (* TODO ERR *)
  | Some (worker, _) ->
      close chan >>= fun () ->
      let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input worker in
      let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output worker in
      let link = { write_to; read_from; pid = Some proc#pid } in
      log @@ "[M] sending job";
      Lwt_io.write_value write_to job >!= fun () ->
      Lwt.return [worker_progress link; wait_process proc]

let handle_event = function
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "[M] Worker %d went on holidays" pid;
      Lwt.return (None,[])
  | WorkerDied ->
      log @@ Printf.sprintf "[M] Worker died";
      Lwt.return (None,[])
  | WorkerProgress { link; sentence_id; result } ->
      log "[M] WorkerProgress";
      Lwt.return  (Some (sentence_id,result), [worker_progress link])
  | WorkerStart (job_id,job,action,procname) ->
    log "[M] WorkerStart";
    if false (* Sys.os_type = "Unix" *) then
      fork_worker job_id >>= fun (role,events) ->
      match role with
      | Master ->
        log "[M] Worker forked, returning events";
        Lwt.return (None, events)
      | Worker link ->
        action job link >>= fun () ->
        log "[W] I'm going on holidays"; Lwt_io.flush_all () >>= fun () -> exit 0
    else
      create_process_worker procname job_id job >>= fun events ->
      Lwt.return (None, events)

let pr_event = function
  | WorkerEnd (pid, _status) ->
    Pp.str "WorkerEnd"
  | WorkerDied ->
    Pp.str "WorkerDied"
  | WorkerProgress _ ->
    Pp.str "WorkerProgress"
  | WorkerStart _ ->
    Pp.str "WorkerStart"

let worker_available ~job ~fork_action = [
  begin
    if !pool_occupants >= pool_size
    then Lwt_condition.wait pool
    else Lwt.return (incr pool_occupants)
  end
  >>= fun () ->
  job () >>= fun (job_id, job) ->
  Lwt.return @@ WorkerStart (job_id,job,fork_action,Job.binary_name)
]
;;

type options = int

let setup_plumbing port =
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  let address = ADDR_INET (Unix.inet_addr_loopback,port) in
  log @@ "[PW] connecting to " ^ string_of_int port;
  connect chan address >!= fun () ->
  let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input chan in
  let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output chan in
  let link = { read_from; write_to; pid = None } in
  Lwt_io.read_value link.read_from >!= fun (job : Job.t) ->
  Lwt.return (link, job)

let parse_options ~opts extra_args =
  match extra_args with
  [ o ; port ] when o = option_name -> int_of_string port, []
  | _ -> assert false (* TODO: error *)

end
