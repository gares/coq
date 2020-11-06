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

(* TODO: move away? *)
module type QueueElement = sig
  type data
  type dependency
  val is_invalid : dependency -> data -> bool
end

module MakeQueue(E : QueueElement) : sig
  val enqueue : E.data -> unit
  val dequeue : unit -> E.data Lwt.t
  val remove_invalid : E.dependency -> E.data list
end = struct

type t = E.data list ref
let queue : t = ref []
let queue_cond = Lwt_condition.create ()

let enqueue m =
  queue := !queue @ [m];
  Lwt_condition.signal queue_cond ()

let dequeue () =
  begin
    if !queue = []
    then Lwt_condition.wait queue_cond
    else Lwt.return ()
  end >>= fun () ->
  let x = List.hd !queue in
  queue := List.tl !queue;
  Lwt.return x

let remove_invalid id =
  let invalid, valid = List.partition (E.is_invalid id) !queue in
  queue := valid;
  invalid

end

open Scheduler

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type execution_status = DelegationManager.execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

let success vernac_st = Success (Some vernac_st)
let error loc msg vernac_st = Error ((loc,msg),(Some vernac_st))

type prepared_task =
  | PSkip of sentence_id
  | PExec of sentence_id * ast
  | PDelegate of { terminator_id: sentence_id;
                   opener_id: sentence_id;
                   last_step_id: sentence_id;
                   tasks: prepared_task list;
                 }

type job = {
  tasks : prepared_task list;
  initial_vernac_state : Vernacstate.t;
  doc_id : int;
  terminator_id : sentence_id;
  last_proof_step_id : sentence_id;
}

module ProofWorker = DelegationManager.MakeWorker(struct
  type t = job
  let name = "proof"
  let binary_name = "vscoqtop_worker.opt"
  let pool_size = 1
end)

type event = ProofWorkerEvent of ProofWorker.event (*| TacticWorkerEvent of Declare.Proof.event*)
type events = event Lwt.t list

let pr_event = function
  | ProofWorkerEvent event -> ProofWorker.pr_event event

let interp_ast ~doc_id ~state_id vernac_st ast =
    Feedback.set_id_for_feedback doc_id state_id;
    Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
    let result =
      try Ok(Vernacinterp.interp ~st:vernac_st ast,[])
      with e when CErrors.noncritical e ->
        let e, info = Exninfo.capture e in
        Error (e, info) in
    Sys.(set_signal sigint Signal_ignore);
    match result with
    | Ok (vernac_st, events) ->
        log @@ "[V] Executed: " ^ Stateid.to_string state_id ^ "  " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
          " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
        vernac_st, success vernac_st, (*List.map inject_pm_event*) events
    | Error (Sys.Break, _ as exn) ->
        log @@ "[V] Interrupted executing: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
        Exninfo.iraise exn
    | Error (e, info) ->
        log @@ "[V] Failed to execute: " ^ Stateid.to_string state_id ^ "  " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
        let loc = Loc.get_loc info in
        let msg = CErrors.iprint (e, info) in
        vernac_st, error loc (Pp.string_of_ppcmds msg) vernac_st,[]

let interp_qed_delayed ~state_id vernac_st =
  let f proof =
    let fix_exn x = x in (* FIXME *)
    let f, assign = Future.create_delegate ~blocking:false ~name:"XX" fix_exn in
    Declare.Proof.close_future_proof ~feedback_id:state_id proof f, assign
  in
  let lemmas = Option.get @@ vernac_st.Vernacstate.lemmas in
  let proof, assign = Vernacstate.LemmaStack.with_top lemmas ~f in
  let pinfo = Declare.Proof.Proof_info.default () in
  let control = [] (* FIXME *) in
  let opaque = Vernacexpr.Opaque in
  let pending = CAst.make @@ Vernacexpr.Proved (opaque, None) in
  log "calling interp_qed_delayed done";
  let vernac_st = Vernacinterp.interp_qed_delayed_proof ~proof ~pinfo ~st:vernac_st ~control pending in
  log "interp_qed_delayed done";
  vernac_st, success vernac_st, assign

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

module SM = Map.Make (Stateid)

type feedback_message = Feedback.level * Loc.t option * Pp.t

type sentence_state =
  | Done of DelegationManager.execution_status
  | Delegated of DelegationManager.job_id * (DelegationManager.execution_status -> unit) option

type state = {
  initial : Vernacstate.t;
  of_sentence : (sentence_state * feedback_message list) SM.t;
}

type progress_hook = unit -> unit Lwt.t

let init_master vernac_state = {
  initial = vernac_state;
  of_sentence = SM.empty;
}

let inject_dm_event x : event Lwt.t =
  Lwt.map (fun x -> ProofWorkerEvent x) x

let inject_dm_events st l =
  Lwt.return (st, List.map inject_dm_event l)

let update_all id v fl state =
  { state with of_sentence = SM.add id (v, fl) state.of_sentence }
;;
let update state id v =
  let fl = try snd (SM.find id state.of_sentence) with Not_found -> [] in
  update_all id (Done v) fl state
;;

let handle_event event state =
  match event with
  | ProofWorkerEvent event -> ProofWorker.handle_event event >>= fun (state_update,events) ->
      let state =
        match state_update with
        | None -> None
        | Some(id,v) ->
            match SM.find id state.of_sentence with
            | (Delegated (_,completion), fl) ->
                Option.default ignore completion v;
                Some (update_all id (Done v) fl state)
            | (Done _, fl) -> None (* TODO: is this possible? *)
            | exception Not_found -> None (* TODO: is this possible? *)
      in
      inject_dm_events state events


let find_fulfilled_opt x m =
  try
    let ss,_ = SM.find x m in
    match ss with
    | Done x -> Some x
    | Delegated _ -> None
  with Not_found -> None

module Jobs = struct
  type data = DelegationManager.job_id * job
  type dependency = sentence_id
  let is_invalid id (_, { terminator_id;_ }) = Stateid.equal id terminator_id
end
module Queue = MakeQueue(Jobs)

let remotize doc id =
  match Document.get_sentence doc id with
  | None -> PSkip id
  | Some sentence ->
    begin match sentence.Document.ast with
    | Document.ValidAst (ast,_) -> PExec(id,ast)
    | Document.ParseError _ -> PSkip id
    end

let prepare_task ~progress_hook doc task : prepared_task =
  match task with
  | Skip id -> PSkip id
  | Exec(id,ast) -> PExec(id,ast)
  | OpaqueProof { terminator_id; opener_id; tasks_ids } ->
     let tasks = List.map (remotize doc) tasks_ids in
     let last_step_id = if CList.is_empty tasks_ids then terminator_id (* FIXME probably wrong, check what to do with empty proofs *) else CList.last tasks_ids in
     PDelegate {terminator_id; opener_id; last_step_id; tasks}
  | _ -> CErrors.anomaly Pp.(str "task not supported yet")

let id_of_prepared_task = function
  | PSkip id -> id
  | PExec(id, _) -> id
  | PDelegate { terminator_id } -> terminator_id

let purge_state = function
  | Success _ -> Success None
  | Error(e,_) -> Error (e,None)

let ensure_proof_over = function
  | Success (Some st) as x ->
      Vernacstate.LemmaStack.with_top (Option.get @@ st.Vernacstate.lemmas)
        ~f:(fun p -> if Proof.is_done @@ Declare.Proof.get p then x else Error((None,"Proof is not finished"),None))
  | x -> x

open Lwt_err.Infix

(* TODO move to proper place *)
let worker_execute ~doc_id last_step_id link (vs,events) = function
  | PSkip id ->
    Lwt.return (vs, events)
  | PExec (id,ast) ->
    let vs, v, ev = interp_ast ~doc_id ~state_id:id vs ast in
    let v = if Stateid.equal id last_step_id then ensure_proof_over v else purge_state v in
    DelegationManager.write link (id,v) >!= fun () ->
    Lwt.return (vs, events @ ev)
  | _ -> assert false

let worker_main { tasks; initial_vernac_state = vs; doc_id; last_proof_step_id; _ } link =
  Lwt_list.fold_left_s (worker_execute ~doc_id last_proof_step_id link) (vs,[]) tasks >>= fun (last_vs, _) ->
  Lwt_io.flush_all () >>= fun () ->
  exit 0

let execute ~doc_id st (vs, events, interrupted) task =
  if interrupted then begin
    let st = update st (id_of_prepared_task task) (Error ((None,"interrupted"),None)) in
    Lwt.return (st, vs, events, true)
  end else
    try
      match task with
      | PSkip id ->
          let st = update st id (success vs) in
          Lwt.return (st, vs, events, false)
      | PExec (id,ast) ->
          let vs, v, ev = interp_ast ~doc_id ~state_id:id vs ast in
          let st = update st id v in
          Lwt.return (st, vs, events @ ev, false)
      | PDelegate { terminator_id; opener_id; last_step_id; tasks } ->
          begin match find_fulfilled_opt opener_id st.of_sentence with
          | Some (Success _) ->
            let job =  { tasks; initial_vernac_state = vs; doc_id; terminator_id; last_proof_step_id  = last_step_id } in
            let job_id = DelegationManager.mk_job_id () in
            (* The proof was successfully opened *)
            let last_vs, v, assign = interp_qed_delayed ~state_id:terminator_id vs in
            let complete_job status =
              try match status with
              | Success None -> assert false
              | Success (Some vernac_st) ->
                let f proof =
                  log "Resolved future";
                  assign (`Val (Declare.Proof.return_proof proof))
                in
                Vernacstate.LemmaStack.with_top (Option.get @@ vernac_st.Vernacstate.lemmas) ~f
              | Error ((loc,err),_) ->
                  log "Aborted future";
                  assign (`Exn (CErrors.UserError(None,Pp.str err), Option.fold_left Loc.add_loc Exninfo.null loc))
              with exn when CErrors.noncritical exn ->
                assign (`Exn (CErrors.UserError(None,Pp.str "error closing proof"), Exninfo.null))
            in
            let st = update st terminator_id (success last_vs) in
            let st = List.fold_left (fun st id ->
               if Stateid.equal id last_step_id then
                 update_all id (Delegated (job_id,Some complete_job)) [] st
               else
                 update_all id (Delegated (job_id,None)) [] st)
               st (List.map id_of_prepared_task tasks) in
            Queue.enqueue (job_id, job);
            let e =
              ProofWorker.worker_available ~job:Queue.dequeue
                ~fork_action:worker_main in
            Lwt.return (st, last_vs,events @ List.map inject_dm_event e ,false)
          | _ ->
            (* If executing the proof opener failed, we skip the proof *)
            let st = update st terminator_id (success vs) in
            Lwt.return (st, vs,events,false)
          end
    with Sys.Break ->
      let st = update st (id_of_prepared_task task) (Error ((None,"interrupted"),None)) in
      Lwt.return (st, vs, events, true)

let build_tasks_for ~progress_hook doc st id =
  let rec build_tasks id tasks =
    begin match find_fulfilled_opt id st.of_sentence with
    | Some (Success (Some vs)) ->
      (* We reached an already computed state *)
      log @@ "[M] Reached computed state " ^ Stateid.to_string id;
      vs, tasks
    | Some (Error(_,Some vs)) ->
      (* We try to be resilient to an error *)
      log @@ "[M] Error resiliency on state " ^ Stateid.to_string id;
      vs, tasks
    | _ ->
      log @@ "[M] Non (locally) computed state " ^ Stateid.to_string id;
      let (base_id, task) = task_for_sentence (Document.schedule doc) id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        st.initial, task :: tasks
      | Some base_id ->
        build_tasks base_id (task::tasks)
      end
    end
  in
  let vs, tasks = build_tasks id [] in
  vs, List.map (prepare_task ~progress_hook doc) tasks

(* If we don't work we have re-create a minimal state that is good enough to
   execute the sentences and send feedback. It is easier/faster than sending a
   stripped state *)
let init_worker () =
  Lwt.return ()

let errors st =
  List.fold_left (fun acc (id, (p,_)) ->
    match p with
    | Done (Error ((loc,e),_st)) -> (id,loc,e) :: acc
    | _ -> acc)
    [] @@ SM.bindings st.of_sentence

let mk_feedback id (lvl,loc,msg) = (id,lvl,loc,Pp.string_of_ppcmds msg)

let feedback st =
  List.fold_left (fun acc (id, (_,l)) -> List.map (mk_feedback id) l @ acc) [] @@ SM.bindings st.of_sentence

let shift_locs st pos offset =
  (* FIXME shift loc in feedback *)
  let shift_error (p,r as orig) = match p with
  | Done (Error ((Some loc,e),st)) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then ((Done (Error ((Some (Loc.shift_loc offset offset loc),e),st))),r)
    else if stop >= pos then ((Done (Error ((Some (Loc.shift_loc 0 offset loc),e),st))),r)
    else orig
  | _ -> orig
  in
  { st with of_sentence = SM.map shift_error st.of_sentence }

let executed_ids st =
  SM.fold (fun id (p,_) acc ->
    match p with
    | Done _ -> id :: acc
    | _ -> acc) st.of_sentence []

let is_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success (Some _) | Error (_,Some _)) -> true
  | _ -> false

let is_remotely_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success None | Error (_,None)) -> true
  | _ -> false

let query id st ast = assert false

let invalidate1 of_sentence id =
  try
    let p,_ = SM.find id of_sentence in
    match p with
    | Delegated (job_id,_) ->
        DelegationManager.cancel_job job_id;
        SM.remove id of_sentence
    | _ -> SM.remove id of_sentence
  with Not_found -> of_sentence

let rec invalidate schedule id st =
  log @@ "Invalidating: " ^ Stateid.to_string id;
  let of_sentence = invalidate1 st.of_sentence id in
  let removed = Queue.remove_invalid id in
  let of_sentence = List.fold_left invalidate1 of_sentence
    List.(concat (map (fun (_, { tasks; _ }) -> map id_of_prepared_task tasks) removed)) in
  if of_sentence == st.of_sentence then Lwt.return st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (fun dep_id st ->
    st >>= fun st -> invalidate schedule dep_id st) deps
    (Lwt.return { st with of_sentence })

let get_parsing_state_after st id =
  Option.bind (find_fulfilled_opt id st.of_sentence)
    (function Success (Some st) | Error (_,Some st) -> Some st.Vernacstate.parsing | _ -> None)

let get_proofview st id =
  match find_fulfilled_opt id st.of_sentence with
  | None -> log "Cannot find state for proofview"; None
  | Some (Error _) -> log "Proofview requested in error state"; None
  | Some (Success None) -> log "Proofview requested in a remotely checked state"; None
  | Some (Success (Some { Vernacstate.lemmas = None; _ })) -> log "Proofview requested in a state with no proof"; None
  | Some (Success (Some { Vernacstate.lemmas = Some st; _ })) ->
      log "Proofview is there";
      (* nicely designed API: Proof is both a file and a deprecated module *)
      let open Proof in
      let open Declare in
      let open Vernacstate in
      st |> LemmaStack.with_top ~f:Proof.get |> data |> Option.make

let handle_feedback state_id contents st =
  match contents with
  | Feedback.Message(Feedback.Info,_,_) -> st
  | Feedback.Message(lvl,loc,msg) ->
    begin match SM.find_opt state_id st.of_sentence with
    | None -> log @@ "Received feedback on non-existing state id " ^ Stateid.to_string state_id; st
    | Some (p,l) ->
      let of_sentence = SM.add state_id (p, (lvl,loc,msg) :: l) st.of_sentence in
      { st with of_sentence }
    end
  | _ -> st

module WorkerProcess = struct
  type options = ProofWorker.options
  let parse_options = ProofWorker.parse_options
  let main ~st:initial_vernac_state options =
    ProofWorker.setup_plumbing options >>= fun (link, job) ->
    worker_main job link
end
