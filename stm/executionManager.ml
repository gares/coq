(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Scheduler

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

module SM = Map.Make (Stateid)

type remote_feedback = OK | ERROR of string Loc.located
type execution_status =
  | Executing
  | Success of Vernacstate.t
  | Error of string Loc.located * Vernacstate.t (* State to use for resiliency *)

(* TODO store current sentence id for optimizations *)
type state = {
  initial : Vernacstate.t;
  cache : execution_status SM.t;
}

let init vernac_state = {
    initial = vernac_state;
    cache = SM.empty;
  }

let base_vernac_st st base_id =
  match base_id with
  | None -> st.initial
  | Some base_id ->
    begin match SM.find_opt base_id st.cache with
    | Some (Success vernac_st) -> vernac_st
    | Some (Error (_, vernac_st)) -> vernac_st (* Error resiliency *)
    | _ -> CErrors.anomaly Pp.(str "Missing state in cache (execute): " ++ Stateid.print base_id)
    end


let string_of_cache = function
  | None -> "-"
  | Some (Success _) -> "OK"
  | Some (Error _) -> "ERR"
  | Some (Executing _) -> "?"

let send_report st ids =
  ids |> List.iter (fun id ->
    log @@ Printf.sprintf "back to %d report %s is %s" (Unix.getppid ())
             (Stateid.to_string id)
             (string_of_cache (SM.find_opt id st.cache)))

let return_update ~update_id_entry id ex st =
  let open Lwt.Infix in
  update_id_entry id ex >>= fun () ->
  Lwt.return { st with cache = SM.add id ex st.cache }

(* Like Lwt.wait but the resolved is remote, via IPC *)
let lwt_wait_remote chan : remote_feedback Lwt.t * remote_feedback Lwt.u =
  assert false

let remote_tasks_for ~hack ~update_id_entry st base_id ids chan =
   let open Lwt.Infix in
   Lwt_list.fold_left_s (fun (base,acc,st) id ->
     match hack id with
     | None -> Lwt.return (Some id, acc, st) (* error resiliency, we skip the proof step, TODO: mark in st SKIP *)
     | Some ast ->
         let p,r = lwt_wait_remote chan in
         Lwt.on_success p (fun x -> update_id_entry id x);
         return_update ~update_id_entry id Executing st >>= fun st ->
         Lwt.return (Some id, (base,Exec(id, ast),id,r) :: acc,st)) (base_id,[],st) ids
  >>= fun (_, tasks_rev,st) ->
  let tasks = List.rev tasks_rev in
  Lwt.return (tasks, st)

let rec delegate ~hack ~update_id_entry st base_id ids : state Lwt.t =
  let open Lwt.Infix in
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >>= fun () ->
  listen chan 1;
  let address = getsockname chan in

  remote_tasks_for ~hack ~update_id_entry st base_id ids chan >>= fun (tasks, st) ->
  Lwt_io.flush_all () >>= fun () ->
  let pid = Lwt_unix.fork () in
  if pid = 0 then
    let chan = socket PF_INET SOCK_STREAM 0 in
    connect chan address >>= fun () ->
    Lwt_list.fold_left_s (execute_remote ~hack ~update_id_entry:update_id_entry_remote) st tasks >>= fun final_st ->
    send_report final_st ids;
    exit 0
  else begin
    accept chan >>= fun (worker, worker_addr) -> (* TODO: timeout *)
    close chan >>= fun () ->
    log @@ "Forked pid " ^ string_of_int pid;
    Lwt.return st
  end

and execute_remote ~hack ~update_id_entry st remote_task : state Lwt.t =
  let open Lwt.Infix in
  let base, task, id, promise_resolver = remote_task in
  execute ~hack ~update_id_entry st (base,task) >>= fun st ->
  begin match SM.find id st.cache with
  | Error (msg, _) -> Lwt.wakeup promise_resolver (ERROR msg)
  | Success _vst -> Lwt.wakeup promise_resolver OK (* TODO: sent vst back? *)
  | Executing _ -> assert false (* TODO: double delegation? *)
  | exception Not_found -> assert false (* looks like an invartiant of execute *)
  end;
  Lwt.return st

and execute ~hack ~update_id_entry st task : state Lwt.t =
  let open Lwt.Infix in
  let return = return_update ~update_id_entry in
  match task with
  | base_id, Skip id ->
    let vernac_st = base_vernac_st st base_id in
    return id (Success vernac_st) st
  | base_id, Exec(id,ast) ->
    log @@ "Going to execute: " ^ Stateid.to_string id ^ " : " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
    let vernac_st = base_vernac_st st base_id in
    begin try
      Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
      let vernac_st = Vernacinterp.interp ~st:vernac_st ast in (* TODO set status to "Executing" *)
      Sys.(set_signal sigint Signal_ignore);
      return id (Success vernac_st) st
    with
    | Sys.Break as exn ->
      let exn = Exninfo.capture exn in
      Sys.(set_signal sigint Signal_ignore);
      Exninfo.iraise exn
    | any ->
      let (e, info) = Exninfo.capture any in
      Sys.(set_signal sigint Signal_ignore);
      let loc = Loc.get_loc info in
      let msg = CErrors.iprint (e, info) in
      return id (Error ((loc, Pp.string_of_ppcmds msg), vernac_st)) st
    end
  | base_id, OpaqueProof (id,ids) ->
    let vernac_st = base_vernac_st st base_id in
    delegate ~hack ~update_id_entry st base_id ids >>= fun st ->
    begin try
      Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
      let ast = Vernacexpr.{ expr = VernacEndProof Admitted; attrs = []; control = [] } in
      let vernac_st = Vernacinterp.interp ~st:vernac_st (CAst.make ast) in (* TODO set status to "Executing" *)
      Sys.(set_signal sigint Signal_ignore);
      return id (Success vernac_st) st
    with
    | Sys.Break as exn ->
      let exn = Exninfo.capture exn in
      Sys.(set_signal sigint Signal_ignore);
      Exninfo.iraise exn
    | any ->
      let (e, info) = Exninfo.capture any in
      Sys.(set_signal sigint Signal_ignore);
      let loc = Loc.get_loc info in
      let msg = CErrors.iprint (e, info) in
      return id (Error ((loc, Pp.string_of_ppcmds msg), vernac_st)) st
    end
  | _ -> CErrors.anomaly Pp.(str "task not supported yet")

let observe ~hack ~update_state schedule id st : state Lwt.t =
  log @@ "Observe " ^ Stateid.to_string id;
  let rec build_tasks id tasks =
    begin match SM.find_opt id st.cache with
    | Some (Success vernac_st) ->
      (* We reached an already computed state *)
      log @@ "Reached computed state " ^ Stateid.to_string id;
      tasks
    | Some (Executing _) -> CErrors.anomaly Pp.(str "depending on a state that is being executed")
    | Some (Error _) ->
      (* We try to be resilient to an error *)
      log @@ "Error resiliency on state " ^ Stateid.to_string id;
      tasks
    | None ->
      log @@ "Non-computed state " ^ Stateid.to_string id;
      let (base_id, task as todo) = task_for_sentence schedule id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        todo :: tasks
      | Some base_id ->
        build_tasks base_id (todo::tasks)
      end
    end
  in
  let update_id_entry id ex : unit Lwt.t =
    update_state ~f:(fun st -> { st with cache = SM.add id ex st.cache }) in
  let tasks = build_tasks id [] in
  let interrupted = ref false in
  let execute st task =
    let open Lwt.Infix in
    if !interrupted then Lwt.return st
    else
    try execute ~hack ~update_id_entry st task
    with Sys.Break -> (interrupted := true; Lwt.return st)
  in
  Lwt_list.fold_left_s execute st tasks

let errors st =
  List.fold_left (fun acc (id, status) -> match status with Error ((loc,e),_st) -> (id,loc,e) :: acc | _ -> acc)
    [] @@ SM.bindings st.cache

let shift_locs st pos offset =
  let shift_error status = match status with
  | Error ((Some loc,e),st) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then Error ((Some (Loc.shift_loc offset offset loc),e),st)
    else if stop >= pos then Error ((Some (Loc.shift_loc 0 offset loc),e),st)
    else status
  | _ -> status
  in
  { st with cache = SM.map shift_error st.cache }

let executed_ids st =
  SM.fold (fun id status acc -> match status with Success _ | Error _ -> id :: acc | _ -> acc) st.cache []

let is_executed st id =
  match SM.find_opt id st.cache with
  | Some (Success _ | Error _) -> true
  | _ -> false

let query id st ast = assert false

let rec invalidate schedule id st =
  log @@ "Invalidating: " ^ Stateid.to_string id;
  let cache = SM.remove id st.cache in
  if cache == st.cache then st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (fun dep_id st -> invalidate schedule dep_id st) deps { st with cache }

let get_parsing_state_after st id =
  Option.bind (SM.find_opt id st.cache)
    (function Success st | Error (_,st) -> Some st.Vernacstate.parsing | _ -> None)

let get_proofview st id =
  match SM.find_opt id st.cache with
  | None -> log "Cannot find state for proofview"; None
  | Some (Executing _) -> log "Proofview requested in state under execution"; None
  | Some (Error _) -> log "Proofview requested in error state"; None
  | Some (Success st) ->
    Vernacstate.unfreeze_interp_state st;
    try
      let newp = Vernacstate.Declare.give_me_the_proof () in
      Some (Proof.data newp)
    with Vernacstate.Declare.NoCurrentProof -> None
  [@@ocaml.warning "-3"];;
