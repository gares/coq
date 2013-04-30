(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let debug = false
let prerr_endline =
  if debug then prerr_endline else fun _ -> ()

open Stategraph
open Vernacexpr
open Errors
open Pp

(* This could be in a .ml file defining basic utils on vernacexpr *)

(* These types are designed for lazy processing, but not lazy parsing, a file *)
type vernac_type =
  | VtUnknown      (* for retrocompatibility, ideally nothing should be there *)
  | VtNow          (* commands that may alter the parsing of following lines,
                      like defining a notation *)
  | VtStartProof of string (* commands that jump in proof mode *)
  | VtSideff       (* commands with global sideffects on the prover state, like
                      adding a lemma to a db, setting options, etc that do
                      not change the way following lines are parsed *)
  | VtQed          (* commands that end proof mode *)
  | VtProofStep    (* commands that stay in proof mode, like a tactic or
                      Check. Also Print, Eval etc should be there *)
  | VtBack of state_id  (* Undo action, to the given state *)
  | VtAlias of state_id (* Undo action saved on script, to the given state *)

let string_of_vernac_type = function
  | VtUnknown -> "Unknown"
  | VtNow -> "Now"
  | VtStartProof s -> "StartProof (mode: " ^ s ^ ")"
  | VtSideff -> "Sideff"
  | VtQed -> "Qed"
  | VtProofStep -> "ProofStep"
  | VtBack id -> "Back " ^ string_of_state_id id
  | VtAlias id -> "Alias " ^ string_of_state_id id

(* Since the set of vernaculars is extensible, also the classification function
   has to be. *)
(* XXX add this to the Summary, since a Declare ML could be undone *)
let classifiers = ref []
let declare_vernac_classifier 
  (f : vernac_expr -> vernac_type) =
  classifiers := f :: !classifiers

let classify_vernac e =
  let rec static_classifier = function
    (* Impossible, Vernac handles these *)
    | VernacList _ -> anomaly (str "VernacList not handled by Vernac")
    | VernacLoad _ -> anomaly (str "VernacLoad not handled by Vernac")
    (* Nested vernac exprs *)
    | VernacProgram e -> static_classifier e
    | VernacLocal (_,e) -> static_classifier e
    | VernacFail e -> static_classifier e
    | VernacTimeout (_,e) -> static_classifier e
    | VernacTime e -> static_classifier e
    (* Qed *)
    | VernacEndProof _ | VernacAbort _ | VernacExactProof _ -> VtQed
    (* ProofStep *)
    | VernacShow _ | VernacPrint _ | VernacSearch _ | VernacLocate _
    | VernacCheckMayEval _
    | VernacProof _ | VernacProofMode _ 
    | VernacBullet _ 
    | VernacFocus _ | VernacUnfocus _
    | VernacSubproof _ | VernacEndSubproof _ 
    | VernacSolve _ 
    | VernacRestart _
    | VernacCheckGuard _
    | VernacUnfocused _
    | VernacSolveExistential _ -> VtProofStep
    (* Back *)
    | VernacBacktrack (id,_,_) -> VtBack (state_id_of_int id)
    (* StartProof *)
    | VernacDefinition (_,_,ProveBody _)
    | VernacStartTheoremProof _
    | VernacGoal _ -> VtStartProof "Classic"
    (* Sideff *)
    | VernacAssumption _
    | VernacDefinition (_,_,DefineBody _)
    | VernacInductive _ | VernacFixpoint _ | VernacCoFixpoint _
    | VernacScheme _ | VernacCombinedScheme _
    | VernacBeginSection _ | VernacEndSegment _
    | VernacCanonical _ | VernacCoercion _ | VernacIdentityCoercion _
    | VernacAddLoadPath _ | VernacRemoveLoadPath _ | VernacAddMLPath _
    | VernacChdir _ 
    | VernacCreateHintDb _ | VernacRemoveHints _ | VernacHints _
    | VernacSyntacticDefinition _
    | VernacDeclareImplicits _ | VernacArguments _ | VernacArgumentsScope _
    | VernacReserve _
    | VernacGeneralizable _
    | VernacSetOpacity _ | VernacSetStrategy _
    | VernacUnsetOption _ | VernacSetOption _
    | VernacAddOption _ | VernacRemoveOption _
    | VernacMemOption _ | VernacPrintOption _
    | VernacGlobalCheck _
    | VernacDeclareReduction _
    | VernacComments _ -> VtSideff
    (* Now *)
    | VernacNop (* We use this to force a Join *)
    | VernacDeclareModule _ | VernacDefineModule _
    | VernacDeclareModuleType _ (* Because the can import notations *)
    | VernacOpenCloseScope _ | VernacDelimiters _ | VernacBindScope _
    | VernacInfix _ | VernacNotation _ | VernacSyntaxExtension _ 
    | VernacDeclareTacticDefinition _ | VernacTacticNotation _
    | VernacRequire _ | VernacImport _ | VernacInclude _
    | VernacDeclareMLModule _
    | VernacContext _
    | VernacInstance _ | VernacDeclareClass _ | VernacDeclareInstances _
    | VernacRequireFrom _ -> VtNow
    (* Unable to handle here, Stm will handle these *)
    | VernacBackTo _ | VernacBack _ 
    | VernacUndoTo _ | VernacUndo _
    | VernacResetName _ | VernacResetInitial _ | VernacAbortAll 
    (* XXX What are these? *)
    | VernacToplevelControl _
    | VernacRestoreState _
    | VernacWriteState _ -> VtUnknown
    (* Plugins should classify their commands *)
    | VernacExtend _ -> VtUnknown in
  let rec extended_classifier = function
    | [] -> static_classifier e
    | f::fs -> 
        match f e with
        | VtUnknown -> extended_classifier fs
        | x -> x
  in
  extended_classifier !classifiers
;;

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* It makes no sense to make this module public since is assumes that all
 * effects on the global state are followed by a define_state, an invariant
 * that is only respected locally to STM *)

(* Imperative module holding a cache of complete system states (including
 * the proof state *)
module StateCache : sig

  val install : state_id -> unit
  val is_defined : state_id -> bool
  val dispose : state_id -> unit
  
  (* defining a state does not automatically store it in the cache, since
   * the current system state is a sort of inplicit cache slot. e.g.
   * a "define_state ~cache:false .. id" followed by "install id" is a no-op *)
  val define_state :
      ?cache:bool -> ('a -> unit) -> 'a -> state_id ->
       (state_id option -> exn -> exn) -> unit

end = struct

  (* cur_id holds dummy_state_id in case the last attempt to define a state
   * failed, so the global state may contain garbage *)
  let cur_id = ref initial_state_id

  (* XXX look at weak hash tables *)
  let cache : (state_id, (States.state * Proof_global.state)) Hashtbl.t =
    Hashtbl.create 17
  
  (* helpers *)
  let freeze_global_state () = 
    States.freeze ~marshallable:false, Proof_global.freeze ()
  let unfreeze_global_state (s,p) =
    States.unfreeze s; Proof_global.unfreeze p
  
  (* hack to make futures functional *)
  let in_t, out_t = Dyn.create "state4future"
  let () = Future.set_freeze 
    (fun () -> in_t (freeze_global_state (), !cur_id))
    (fun t -> let s,i = out_t t in unfreeze_global_state s; cur_id := i)
  
  let install id =
    if id = !cur_id then () else (* optimization *)
    let s = 
      try Hashtbl.find cache id
      with Not_found -> anomaly (str "unfreezing a non existing state") in
    unfreeze_global_state s; cur_id := id
  
  let is_defined id =
    if id = !cur_id then true else (* optimization *)
    try ignore(Hashtbl.find cache id); true
    with Not_found -> false
  
  let dispose id = Hashtbl.remove cache id
  
  let freeze id =
    let state = freeze_global_state () in
    Hashtbl.add cache id state;
    cur_id := id
  
  let define_state ?(cache=false) f x id g =
    if is_defined id then anomaly (Pp.str "defining a state twice");
    try f x; if cache then freeze id else cur_id := id (* optimization *)
    with e ->
      let id = if !cur_id <> dummy_state_id then Some !cur_id else None in
      cur_id := dummy_state_id;
      raise (g id e)

end

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Util
open Ppvernac

(* pointers to open branches *)
type head_kind = 
  | Proof of string * int (* mode * depth *)
  | Master
            (* name, (pos, kind, root) *)
type head = string * (state_id * head_kind * state_id)

(* edges of the graph *)
type transaction = 
  | Cmd of vernac_expr 
  | Fork of vernac_expr * string
  | Qed of vernac_expr * head
  | Sideff of vernac_expr option
  | Alias of state_id
  | Noop

let string_of_transaction = function
  | Cmd t | Fork (t, _) -> 
      (try string_of_ppcmds (pr_vernac t) with _ -> "ERR")
  | Sideff (Some t) -> 
      Printf.sprintf "Sideff(%s)" 
        (try string_of_ppcmds (pr_vernac t) with _ -> "ERR")
  | Sideff None -> "EnvChange"
  | Noop -> ""
  | Alias id -> Printf.sprintf "Alias(%s)" (string_of_state_id id)
  | Qed (_,(b,_)) -> "Qed of " ^ b

module Dag = Stategraph.Dag

let graph = ref (Dag.empty : transaction Dag.graph)

(* Graph evaluation *)

let pstate = ["meta counter"; "evar counter"; "program-tcc-table"]

type perform =
  ?proof:Proof_global.closed_proof -> Vernacexpr.vernac_expr -> unit

(* XXX side effect collection is probably useless, since we reach the tip of
 * master to obtain the same effects *)
let collect_proof cur hd id =
 let rec collect last (accn,accs) id =
(*
  if StateCache.is_defined id then `NotOptimizable `Freezed
  else
*)
    match last, Dag.from_node id !graph with
    | _, [parent, Cmd x] -> collect (Some (id,x)) (id::accn,accs) parent
    | _, [parent, Alias _] -> collect None (id::accn,accs) parent
    | Some (parent, VernacProof(_,Some _)), [_, Fork (_, hd')] -> 
        assert( hd = hd' );
        `Optimizable (parent,accs,accn)
    | Some (parent, VernacExactProof _), [_, Fork _] ->
        `NotOptimizable `Immediate
    | Some (parent, _), [_, Fork (_, hd')] ->
        assert( hd = hd' );
        `MaybeOptimizable (parent,accs,accn)
    | _, ([parent, Sideff se ; _, Noop ] | [ _, Noop ; parent, Sideff se ]) ->
        collect None (id::accn,se::accs) parent
    | _ -> `NotOptimizable `Unknown in
 collect (Some cur) ([],[]) id

let is_a_fork = function [ _, Fork _ ] -> true | _ -> false

let create_future f =
  Future.create (fun () ->
    try f () with e -> raise (Cerrors.process_vernac_interp_error e))
 
(* StateCache.define_state with graph handling *)
let reach_state ?cache f x id =
  let on_failure good_id = function
    | ErrorReachingState _ as e -> e
(*     | e when Errors.is_anomaly e -> e *)
    | e ->
       let e = Errors.push e in
       let e = Cerrors.process_vernac_interp_error e in
       graph := Dag.reach id false !graph;
       ErrorReachingState (good_id, id, e) in
  StateCache.define_state ?cache f x id on_failure;
  graph := Dag.reach id true !graph
     
let reach_known_state (perform : state_id -> perform) ~cache id =

  (* ugly functions to process nested lemmas, i.e. hard to reproduce
   * side effects *)
  let cherry_pick_non_pstate () =
    Summary.freeze_summary ~complement:true pstate,
    Lib.freeze ~marshallable:false in
  let inject_non_pstate (s,l) = Summary.unfreeze_summary s; Lib.unfreeze l in

  let rec pure_cherry_pick_non_pstate id = Future.purify (fun id ->
    prerr_endline ("cherry-pick non pstate " ^ string_of_state_id id);
    reach id;
    cherry_pick_non_pstate ()) id

  and reach id =
    prerr_endline ("reaching: " ^ string_of_state_id id);
    if StateCache.is_defined id then begin
      StateCache.install id;
      prerr_endline ("reached (cache)")
    end else
    let step, cache_step =
      match Dag.from_node id !graph with
      | [ parent, Alias id ] ->
           (fun () -> reach parent; reach id),
           (cache && Dag.cluster_of id !graph = None)
      | [ parent, Cmd x ] ->
           (fun () -> reach parent; perform id x),
           (cache && Dag.cluster_of id !graph = None)
      | [ parent, Fork (x,_) ] ->
           (fun () -> reach parent; perform id x),
           true
      | [ p1,Qed (x,(hd,_)); p2, Noop ] | [ p2, Noop ; p1,Qed (x,(hd,_)) ] ->
           let rec aux = function
           | `Optimizable (start, seff, nodes) ->
               (fun () ->
                 graph := Dag.create_cluster nodes !graph;
                 reach start;
                 let f = create_future (fun () -> reach p2) in
                 let proof = Proof_global.close_future_proof f in
                 reach p1;
                 perform id ~proof x;
                 Proof_global.discard_all ())
           | `MaybeOptimizable (start, seff, nodes) ->
               (fun () ->
                 reach start;
                 (* no sections and no modules *)
                 if Environ.named_context (Global.env ()) = [] &&
                    Safe_typing.is_curmod_library (Global.safe_env ()) then
                   aux (`Optimizable (start, seff, nodes)) ()
                 else
                   aux (`NotOptimizable `Unknown) ())
           | `NotOptimizable `Immediate -> assert (p1 = p2);
               (fun () -> reach p2; perform id x; Proof_global.discard_all ())
           | `NotOptimizable _ ->
               (fun () ->
                 reach p2;
                 let proof = Proof_global.close_proof () in
                 reach p1;
                 perform id ~proof x;
                 Proof_global.discard_all ())
           in aux (collect_proof (p1,x) hd p2), true
      | [ p1,Sideff None; p2, Noop ] | [ p2, Noop; p1,Sideff None]->
           (fun () ->
              let s = pure_cherry_pick_non_pstate p2 in
              reach p1;
              inject_non_pstate s),
           cache
      | [ p1,Sideff (Some x); _, Noop ] | [ _, Noop; p1,Sideff (Some x)]->
           (fun () -> reach p1; perform id x),
           cache
      | _ -> anomaly (str "malformed dag")
    in
    reach_state ~cache:cache_step step () id;
    prerr_endline ("reached: "^ string_of_state_id id) in

  reach id
  (* TODO: we could mark as unreachable all the states depending on id
   * within the same "future"/task boundary *)
;;

(* Graph building *)

let master = "master"
let master_initial_id = initial_state_id

let heads : head list ref = 
  ref [master,(master_initial_id,Master,dummy_state_id)]
let cur_head : string ref = ref master

let new_node () = fresh_state_id ()

let get_head head = 
  try List.assoc head !heads
  with Not_found ->
    anomaly (str"head " ++ str head ++ str" not found")

let get_id head = let id, _k, _r = get_head head in id

let add_node id edges =
  assert (edges <> []);
  List.iter (fun (tr,tgt) -> graph := Dag.add_edge id tr tgt !graph) edges

let reset head id =
  heads := List.map (fun (name,(x,k,r) as h) -> 
    if name = head then (name,(id,k,r)) else h) !heads

let branch_from root name kind =
  let id = get_id root in
  heads := (name, (id,kind,id)) :: !heads;
  cur_head := name

let branch_D name = heads := List.filter (fun (n, _) -> n <> name) !heads

let merge ~state:id ~msg:(tr1,tr2) ?into name =
  let into, local =
    match into with Some x -> x, false | _ -> !cur_head, true in
  assert (name <> into);
  prerr_endline ("merging "^name^" into " ^ into);
  let br_id = get_id name in
  let cur_id = get_id into in
  add_node id [tr1,cur_id; tr2,br_id];
  reset into id;
  if local then reset name id

let commit ~state:id ~msg:tr =
  add_node id [tr, get_id !cur_head];
  reset !cur_head id

let checkout name = 
  prerr_endline ("Checkout " ^ name);
  cur_head := name

let proof_nesting heads = 
  List.fold_left max 0 
    (List.map_filter 
      (function (_,(_,Proof (_,n),_)) -> Some n | _ -> None) heads)

let find_proof_at_depth pl heads =
  try
    List.find (function | h, (_, Proof (m, n), _) -> n = pl | _ -> false) heads
  with Not_found -> failwith "find_proof_at_depth"

let branch name kind = branch_from !cur_head name kind

(* XXX check *)
let vcs_backup () = !cur_head, !heads
let vcs_restore (h,hs) = cur_head := h; heads := hs

let head () = !cur_head
let branches () = List.map fst !heads
let set_heads h = heads := h
let heads () = !heads

let checkout_shallowest_proof_branch () =
  let pl = proof_nesting (heads ()) in
  try 
    let branch, mode = match find_proof_at_depth pl (heads ()) with
      | h, (_, Proof (m, _), _) -> h, m | _ -> assert false in
    checkout branch;
    Proof_global.activate_proof_mode mode
  with Failure _ -> 
    checkout master;
    Proof_global.disactivate_proof_mode "Classic" (* XXX *)

let mk_branch_name = 
  let bid = ref 0 in
  fun x -> incr bid; string_of_int !bid ^ "_" ^ match x with
  | VernacDefinition (_,(_,i),_) -> string_of_id i
  | VernacStartTheoremProof (_,[Some (_,i),_],_) -> string_of_id i
  | _ -> "branch"

(* copies the transaction on every open branch *)
let propagate_sideff t =
  List.iter (fun b -> 
    checkout b;
    let id = new_node () in
    merge ~state:id ~msg:(Sideff t,Noop) ~into:b master)
  (List.filter ((<>) master) (branches ()))

(* Backtrack *)
type hystory_elt = {
  id : state_id ;
  hds : head list; dag : transaction Dag.graph;
  label : int; (* to implement Reset without using Lib *)
}

let graph_history : hystory_elt Searchstack.t =
  let s = Searchstack.create () in
  Searchstack.push {
    id = master_initial_id;
    dag = !graph;
    hds = heads ();
    label = Lib.first_command_label } s;
  s

let () =
  declare_vernac_classifier begin function
  | VernacResetInitial -> VtBack initial_state_id
  | VernacResetName name ->
      let lib_name = Lib.label_before_name name in
      let s = Searchstack.find (fun _ s ->
         if s.label = lib_name then `Stop s else `Cont ()) () graph_history in
      VtBack s.id
  | VernacBackTo id -> VtBack (state_id_of_int id)
  | VernacBack n
  | VernacUndo n ->
      let s = Searchstack.find (fun n s ->
        if n = 0 then `Stop s else `Cont (n-1)) n graph_history in
      VtAlias s.id
  | VernacUndoTo _
  | VernacRestart as e ->
      let m = match e with VernacUndoTo m -> m | _ -> 0 in
      let hds = (Searchstack.top graph_history).hds in
      let cur_branch, _ = find_proof_at_depth (proof_nesting hds) hds in
      let n = Searchstack.find (fun n s ->
        if List.mem_assoc cur_branch s.hds then `Cont (n+1) else `Stop n)
        0 graph_history in
      let s = Searchstack.find (fun n s ->
        if n = 0 then `Stop s else `Cont (n-1)) (n-m) graph_history in
      VtAlias s.id
  | VernacAbortAll ->
      let s = Searchstack.find (fun n s -> match s.hds with
        | [_] -> `Stop s | _ -> `Cont n) () graph_history in
      VtAlias s.id
  | _ -> VtUnknown
end

let record_graph () =
  let id = get_id (head()) in
  Searchstack.push {
    id = id; dag = !graph ; hds = heads ();
    label = Lib.current_command_label () }
  graph_history

let process_transaction (f : perform) x =
  let f id = Pp.set_id_for_feedback (Interface.State id); f in
  if not (StateCache.is_defined master_initial_id ) then
    reach_state ~cache:true (fun () -> ()) () master_initial_id;
  prerr_endline ("{{{ execute: "^string_of_ppcmds (pr_vernac x));
  let vcs = vcs_backup () in
  let head = head () in
  checkout head;
  try
    let rc = 
      let c = classify_vernac x in
      prerr_endline ("  classified as: " ^ string_of_vernac_type c);
      match x, c with
      | _, VtQed ->
          let branch = assert (head <> master); head in
          let info = List.assoc branch (heads ()) in
          checkout master;
          let id = new_node () in
          merge ~state:id ~msg:(Qed (x,(branch, info)),Noop) branch;
          branch_D branch;
          propagate_sideff None;
          checkout_shallowest_proof_branch ();
          record_graph ()
      | _, VtProofStep
      | VernacSetOption (["Silent"],_), _ (* XXX this must disappear *)
      | VernacUnsetOption (["Silent"]), _ ->
          let id = new_node () in
          commit ~state:id ~msg:(Cmd x);
          record_graph ()
      | _, VtAlias aid ->
          let id = new_node () in
          commit ~state:id ~msg:(Alias aid);
          record_graph ()
      | _, VtBack id -> 
        prerr_endline ("undo to state " ^ string_of_state_id id);

        let n_to_clear, old =
          let finder n ({ id = old_id } as g) =
            if id = old_id then `Stop (n,g) else `Cont (n+1) in
          try Searchstack.find finder 0 graph_history
          with Not_found ->
            anomaly (str "unknown state id " ++ str (string_of_state_id id)) in

        set_heads old.hds;
        checkout_shallowest_proof_branch ();
        begin
        try 
          reach_known_state f ~cache:!Flags.ide_slave id;

          (* history and graph cleanup: BROKEN 
          while (Searchstack.top graph_history).id <> id do
            ignore(Searchstack.pop graph_history) done;
          let dust = ref [] in
          let olddag = old.dag in
          Dag.iter (fun id _ _ _ ->
            if not (Dag.mem id olddag) then dust := id::!dust) !graph;
          List.iter StateCache.dispose !dust; *)

        with
         | ErrorReachingState (None, _, _) as exn -> raise exn
         | ErrorReachingState (Some good_id, eid, e) as exn ->
             try Searchstack.find
                   (fun () { id } -> (* It may be an internal id *)
                      if id = good_id then `Stop () else `Cont ())
                   () graph_history;
                 raise exn
             with Not_found -> raise (ErrorReachingState (None, eid, e))
        end

      | _, VtStartProof mode ->
(*     XXX MOVE TO VCS
      begin
        List.iter begin fun (id_ex,_,_) ->
          if Names.id_ord id id_ex = 0 then raise AlreadyExists
        end !pstates
      end;
      (* arnaud: ajouter une vérification pour la présence de id dans le
       * proof_global *)
*)    
          checkout master;
          let id = new_node () in
          let bname = mk_branch_name x in
          commit ~state:id ~msg:(Fork (x, bname));
          branch bname (Proof (mode, proof_nesting (heads ()) + 1));
          (* parsing mode for tactics *) 
          Proof_global.activate_proof_mode mode;
          record_graph ()
      | _, VtSideff ->
          checkout master;
          let id = new_node () in
          commit ~state:id ~msg:(Cmd x);
          propagate_sideff (Some x);
          checkout_shallowest_proof_branch ();
          record_graph ()
      | _, (VtNow | VtUnknown) ->
          let id = new_node () in
          let step () =
            reach_known_state f ~cache:false (get_id master);
            Proof_global.discard_all ();
            f id x;
            checkout master;
            if Proof_global.there_are_pending_proofs () then begin
              let bname = mk_branch_name x in
              commit ~state:id ~msg:(Fork (x,bname));
              branch bname (Proof ("Classic", proof_nesting (heads ()) + 1))
            end else begin
              commit ~state:id ~msg:(Cmd x);
              propagate_sideff (Some x);
              checkout_shallowest_proof_branch ();
            end in
          reach_state ~cache:true step () id;
          record_graph ()
    in
    prerr_endline "executed }}}";
    rc
  with
  | (ErrorReachingState (_, state_id, exn)) as e ->
      vcs_restore vcs;
      raise e
(*   | e when Errors.is_anomaly e -> vcs_restore vcs; raise e *)
  | e -> anomaly (str ("execute: "^ Printexc.to_string e ^ "}}}"))

let print_graph fname is_green is_red head heads graph =
  let quote s = 
    Str.global_replace (Str.regexp "\n") " "
     (Str.global_replace (Str.regexp "\"") "\\\""
      (Str.global_replace (Str.regexp "\\") " "
       (String.sub s 0 (min (String.length s) 20)))) in
  let fname_dot, fname_ps =
    let f = "/tmp/" ^ Filename.basename fname in
    f ^ ".dot", f ^ ".ps" in
  let oc = open_out fname_dot in
  let node id = "s" ^ string_of_state_id id in
  let edge tr = quote (string_of_transaction tr) in
  output_string oc "digraph states {\n";
  let ids = ref StateidSet.empty in
  let clus = Hashtbl.create 13 in
  let add_to_clus_or_ids from cf =
    match cf with 
    | None -> ids := StateidSet.add from !ids; false
    | Some c -> Hashtbl.replace clus c 
       (try let n = Hashtbl.find clus c in from::n 
       with Not_found -> [from]); true in
  Dag.iter (fun from cf _ l ->
    let c1 = add_to_clus_or_ids from cf in
    List.iter (fun (dest, trans) ->
     let c2 = add_to_clus_or_ids dest (Dag.cluster_of dest graph) in
     Printf.fprintf oc "%s -> %s [label=\"%s\",labelfloat=%b];\n" 
         (node from) (node dest) (edge trans) (c1 && c2)) l
  ) graph;
  StateidSet.iter (fun id ->
    if is_red id then
      Printf.fprintf oc "%s [label=\"%s (%d)\",style=filled,fillcolor=red];\n" 
        (node id) (node id) (Dag.n_reached id graph)
    else if is_green id then
      Printf.fprintf oc "%s [label=\"%s (%d)\",style=filled,fillcolor=green];\n"
        (node id) (node id) (Dag.n_reached id graph)
    else
        Printf.fprintf oc "%s [label=\"%s (%d)\"];\n" 
        (node id) (node id) (Dag.n_reached id graph))
    !ids;
  Hashtbl.iter (fun c nodes ->
     Printf.fprintf oc "subgraph cluster_%s {\n" 
       (Dag.string_of_cluster_id c);
     List.iter (fun id -> 
       if is_red id then
         Printf.fprintf oc 
           "%s [label=\"%s (%d)\",style=filled,fillcolor=red];\n" 
             (node id) (node id) (Dag.n_reached id graph)
       else if is_green id then
         Printf.fprintf oc 
           "%s [label=\"%s (%d)\",style=filled,fillcolor=green];\n" 
             (node id) (node id) (Dag.n_reached id graph)
       else Printf.fprintf oc "%s [label=\"%s (%d)\"];\n" 
        (node id) (node id) (Dag.n_reached id graph))
       nodes;
     Printf.fprintf oc "color=blue; }\n"
  ) clus;
  List.iteri (fun i (b,id) ->
    let shape = if head = b then "box3d" else "box" in
    Printf.fprintf oc "b%d -> %s;\n" i (node id);
    Printf.fprintf oc "b%d [shape=%s,label=\"%s\"];\n" i shape b;
    )
    heads;
  output_string oc "}\n";
  close_out oc;
  ignore(Sys.command ("dot -Tps -Gcharset=latin1 " ^ fname_dot ^ " -o" ^ fname_ps))

(* Query API *)

let observe f id =
  let f id = Pp.set_id_for_feedback (Interface.State id); f in
  let vcs = vcs_backup () in
  try
    prerr_endline ("OBSERVE: " ^ string_of_state_id id);
    reach_known_state f ~cache:!Flags.ide_slave id;
    if !Flags.ide_slave then
      print_graph "coqide" 
        StateCache.is_defined
        (fun id -> Dag.n_reached id !graph = ~-1)
        (head ()) 
        (List.map (fun (x,(y,_,_)) -> x,y) (heads())) !graph
  with e ->
    vcs_restore vcs;
    prerr_endline "ERROR while observing";
    raise (Cerrors.process_vernac_interp_error e)

let finish f =
  prerr_endline "FINISH";
  try observe f (get_id (head ())); prerr_endline "FINISHED"
  with e -> raise e

(* XXX maybe we should make a new cached state for that? *)
let join () = Global.join_safe_environment ()

let get_current_state () =
  let id = (Searchstack.top graph_history).id in
  prerr_endline ("cur_id: " ^ string_of_state_id id);
  id

let current_proof_depth () =
  let head = head () in
  match List.assoc head (heads ()) with
  | _, Master, _ -> 0
  | cur, Proof (_,n), root -> 
      let rec distance cur =
        if cur = root then 0
        else 
          let l = Dag.from_node cur !graph in
          let l = List.map fst l in
          1 + (List.fold_left min max_int (List.map distance l)) in
      distance cur

let unmangle n = 
  let idx = String.index n '_' + 1 in
  Names.id_of_string (String.sub n idx (String.length n - idx))

let proofname = function (name, (_,Proof _,_)) -> Some name | _ -> None

let get_all_proof_names () =
  List.map unmangle (List.map_filter proofname (heads()))

let get_current_proof_name () = 
  Option.map unmangle (proofname (head(),(List.assoc (head ()) (heads ()))))

let get_checked_states () = Dag.reached !graph

let get_script prf = assert false (* XXX
  let infos = ref [] in
  let select i = match i.prfname with
    | None -> raise Not_found
    | Some p when p=prf -> infos := i :: !infos
    | _ -> ()
  in
  (try List.iter select (Script.dump script) with Not_found -> ());
  (* Get rid of intermediate commands which don't grow the depth *)
  let rec filter n = function
    | [] -> []
    | {prfdepth=d; cmd=c}::l when n < d -> c :: filter d l
    | {prfdepth=d}::l -> filter d l
  in
  (* initial proof depth (after entering the lemma statement) is 1 *)
  filter 1 !infos
*)

let _ = register_handler begin function
  | ErrorReachingState (_,id, e) when debug ->
      v 0 (str"debug: reaching state " ++ str(string_of_state_id id) ++
         cut() ++ print e)
  | ErrorReachingState (_,id, e) -> (* FIXME: remove that in production *)
     str "error reaching state " ++ str(string_of_state_id id)
  | _ -> raise Unhandled
end

