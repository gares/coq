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
open Lwt.Infix

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

module SM = Map.Make (Stateid)

type execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

let success vernac_st = Success (Some vernac_st)
let error loc msg vernac_st = Error ((loc,msg),(Some vernac_st))

(* TODO store current sentence id for optimizations *)
type state = {
  initial : Vernacstate.t;
  cache : execution_status Lwt.t SM.t;
}

type progress_hook = state option -> unit Lwt.t

let init vernac_state = {
    initial = vernac_state;
    cache = SM.empty;
  }

let find_fulfilled_opt x m =
  try
    let p = SM.find x m in
    match Lwt.state p with
    | Lwt.Return v -> Some v
    | Lwt.Fail exn -> assert false
    | Lwt.Sleep -> None
  with Not_found -> None

let base_vernac_st st base_id =
  match base_id with
  | None -> Lwt.return st.initial
  | Some base_id ->
    begin try
      SM.find base_id st.cache >>= function
      | Success (Some vernac_st) -> Lwt.return vernac_st
      | Error (_, Some vernac_st) -> Lwt.return vernac_st (* Error resiliency *)
      | _ -> assert false
    with Not_found -> CErrors.anomaly Pp.(str "Missing state in cache (execute): " ++ Stateid.print base_id)
    end


let queue = ref []
let queue_lock = Lwt_mutex.create ()
let queue_cond = Lwt_condition.create ()

type remote_tasks = (ast * execution_status Lwt.u) list

let enqueue (m : execution_status DelegationManager.remote_mapping * (remote_tasks * Vernacstate.t * Stateid.t)) : unit Lwt.t =
  Lwt_mutex.with_lock queue_lock (fun () -> (log @@ "pushing in the queue");
    queue := !queue @ [m]; Lwt_condition.signal queue_cond (); Lwt.return ())

let dequeue () : (execution_status DelegationManager.remote_mapping * (remote_tasks * Vernacstate.t * Stateid.t)) Lwt.t =
  Lwt_mutex.with_lock queue_lock (fun () ->
    begin
      if !queue = []
      then (log @@ "[Q] empty queue... wait"; Lwt_condition.wait ~mutex:queue_lock queue_cond)
      else Lwt.return ()
    end >>= fun () ->
    log @@ "[Q] non empty queue";
    let x = List.hd !queue in
    queue := List.tl !queue;
    Lwt.return x)

let invalidate_delegation_queue id : unit Lwt.t =
  Lwt_mutex.with_lock queue_lock (fun () ->
    queue := List.filter (fun (_,(_,_,id1)) -> not(Stateid.equal id id1)) !queue;
    Lwt.return ())

let exec1 vernac_st ast =
  try
    Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
    let vernac_st = Vernacinterp.interp ~st:vernac_st ast in (* TODO set status to "Delegated" *)
    Sys.(set_signal sigint Signal_ignore);
    log @@ "[V] Executed: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
      " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
    success vernac_st
  with
  | Sys.Break as exn ->
    let exn = Exninfo.capture exn in
    Sys.(set_signal sigint Signal_ignore);
    log @@ "[V] Interrupted executing: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
    Exninfo.iraise exn
  | any ->
    let (e, info) = Exninfo.capture any in
    Sys.(set_signal sigint Signal_ignore);
    log @@ "[V] Failed to execute: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    error loc (Pp.string_of_ppcmds msg) vernac_st

let exec1_remote st (ast,resolver) : Vernacstate.t option =
  match st with
  | None -> None
  | Some st ->
      log @@ "[W] Going to execute " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
        " on worker";
      let v = exec1 st ast in
      log @@ "[W] notifying master";
      Lwt.wakeup resolver v;
      log @@ "[W] next task...";
      match v with
      | Success (Some st) -> Some st
      | _ -> None

let worker_action (remote_tasks , initial_state, _state_id) =
  let _ = List.fold_left exec1_remote (Some initial_state) remote_tasks in
  log @@ "[W] Worker goes on holidays"; (* Send back states? *)
  exit 0
;;

let build_remote_tasks ~hack st remote_mapping ids =
  let tasks_rev, st, remote_mapping = List.fold_left (fun (acc,st,remote_mapping) id ->
    match hack id with
    | None -> acc, st, remote_mapping (* error resiliency, we skip the proof step *)
    | Some ast ->
        let remote_mapping, (p,r) = DelegationManager.lwt_remotely_wait remote_mapping in
        let st = { st with cache = SM.add id p st.cache } in
        (ast,r) :: acc, st, remote_mapping)
    ([],st,remote_mapping) ids in
  List.rev tasks_rev, st, remote_mapping

let rec delegate ~hack ~progress_hook base_id ids st vernac_st : state Lwt.t =
  let remote_mapping = DelegationManager.empty_remote_mapping ~progress_hook:(fun () -> progress_hook None) in
  let remote_tasks, st, remote_mapping = build_remote_tasks ~hack st remote_mapping ids in
  enqueue (remote_mapping, (remote_tasks, vernac_st, Option.get base_id)) >>= fun () ->
  Lwt.return st

and execute ~hack ~progress_hook st task : (state * 'a DelegationManager.events) Lwt.t =
  let update_st st id v acts = Lwt.return ({ st with cache = SM.add id (Lwt.return v) st.cache },acts) in
  match task with
  | base_id, Skip id ->
    base_vernac_st st base_id >>= fun vernac_st ->
    update_st st id (success vernac_st) []
  | base_id, Exec(id,ast) ->
    base_vernac_st st base_id >>= fun vernac_st ->
    log @@ "[M] Going to execute: " ^ Stateid.to_string id ^ ": (" ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
      ") on top of " ^ (Stateid.to_string (Option.default Stateid.initial base_id)) ^
      " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
    update_st st id (exec1 vernac_st ast) []
  | base_id, OpaqueProof (id,ids) ->
    log @@ "[M] Going to delegate: " ^ Stateid.to_string id;
    base_vernac_st st base_id >>= fun vernac_st ->
    delegate ~hack ~progress_hook base_id ids st vernac_st >>= fun st ->
    let ast = CAst.make @@ Vernacexpr.{ expr = VernacEndProof Admitted; attrs = []; control = [] } in
    update_st st id (exec1 vernac_st ast) (DelegationManager.worker_available ~job:dequeue ~action:worker_action)
  | _ -> CErrors.anomaly Pp.(str "task not supported yet")

let observe ~hack progress_hook schedule id st : (state * 'a DelegationManager.events) Lwt.t =
  log @@ "[M] Observe " ^ Stateid.to_string id;
  let rec build_tasks id tasks =
    begin match find_fulfilled_opt id st.cache with
    | Some (Success (Some _)) ->
      (* We reached an already computed state *)
      log @@ "[M] Reached computed state " ^ Stateid.to_string id;
      tasks
    | Some (Error(_,Some _)) ->
      (* We try to be resilient to an error *)
      log @@ "[M] Error resiliency on state " ^ Stateid.to_string id;
      tasks
    | _ ->
      log @@ "[M] Non (locally) computed state " ^ Stateid.to_string id;
      let (base_id, task as todo) = task_for_sentence schedule id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        todo :: tasks
      | Some base_id ->
        build_tasks base_id (todo::tasks)
      end
    end
  in
  let tasks = build_tasks id [] in
  let interrupted = ref false in
  let execute (st,acts) task =
    if !interrupted then Lwt.return (st,acts)
    else
    try
      execute ~hack ~progress_hook st task >>= fun (st,acts') ->
      progress_hook (Some st) >>= fun () ->
      Lwt_io.flush_all () >>= fun () ->
      Lwt.return (st,acts @ acts')
    with Sys.Break -> (interrupted := true; Lwt.return (st,acts))
  in
  Lwt_list.fold_left_s execute (st,[]) tasks

let get_fulfilled_opt x =
  match Lwt.state x with
  | Lwt.Return x -> Some x
  | _ -> None

let errors st =
  List.fold_left (fun acc (id, status) ->
    match get_fulfilled_opt status with
    | Some (Error ((loc,e),_st)) -> (id,loc,e) :: acc
    | _ -> acc)
    [] @@ SM.bindings st.cache

let shift_locs st pos offset =
  let shift_error status = match get_fulfilled_opt status with
  | Some (Error ((Some loc,e),st)) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then Lwt.return @@ Error ((Some (Loc.shift_loc offset offset loc),e),st)
    else if stop >= pos then Lwt.return @@ Error ((Some (Loc.shift_loc 0 offset loc),e),st)
    else status
  | _ -> status
  in
  { st with cache = SM.map shift_error st.cache }

let executed_ids st =
  SM.fold (fun id status acc ->
    match get_fulfilled_opt status with
    | Some (Success _ | Error _) -> id :: acc
    | _ -> acc) st.cache []

let is_executed st id =
  match find_fulfilled_opt id st.cache with
  | Some (Success (Some _) | Error (_,Some _)) -> true
  | _ -> false

let is_remotely_executed st id =
  match find_fulfilled_opt id st.cache with
  | Some (Success None | Error (_,None)) -> true
  | _ -> false

let query id st ast = assert false

let invalidate1 cache id =
  try
    let p = SM.find id cache in
    match Lwt.state p with
    | Lwt.Sleep ->
        Lwt.cancel p; (* TODO: hook worker killing or job dequeue, eg Lwt.on_cancel  *)
        SM.remove id cache
    | _ -> SM.remove id cache
  with Not_found -> cache

let rec invalidate schedule id st =
  log @@ "Invalidating: " ^ Stateid.to_string id;
  let cache = invalidate1 st.cache id in
  invalidate_delegation_queue id >>= fun () ->
  if cache == st.cache then Lwt.return st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (fun dep_id st ->
    st >>= fun st -> invalidate schedule dep_id st) deps
    (Lwt.return { st with cache })

let get_parsing_state_after st id =
  Option.bind (find_fulfilled_opt id st.cache)
    (function Success (Some st) | Error (_,Some st) -> Some st.Vernacstate.parsing | _ -> None)

let get_proofview st id =
  match find_fulfilled_opt id st.cache with
  | None -> log "Cannot find state for proofview"; None
  | Some (Error _) -> log "Proofview requested in error state"; None
  | Some (Success None) -> log "Proofview requested in a remotely checked state"; None
  | Some (Success (Some { Vernacstate.lemmas = None; _ })) -> log "Proofview requested in a state with no proof"; None
  | Some (Success (Some { Vernacstate.lemmas = Some st; _ })) ->
      (* nicely design API: Proof is both a file and a deprecated module *)
      let open Proof in
      let open Declare in
      let open Vernacstate in
      st |> LemmaStack.with_top_pstate ~f:Proof.get_proof |> data |> Option.make