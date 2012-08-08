(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Module defining the last essential tiles of interactive proofs.
   The features of the Proof module are undoing and focusing.
   A proof is a mutable object, it contains a proofview, and some information
   to be able to undo actions, and to unfocus the current view. All three
   of these being meant to evolve.
   - Proofview: a proof is primarily the data of the current view.
     That which is shown to the user (as a remainder, a proofview
     is mainly the logical state of the proof, together with the
     currently focused goals).
   - Focus: a proof has a focus stack: the top of the stack contains
     the context in which to unfocus the current view to a view focused
     with the rest of the stack.
     In addition, this contains, for each of the focus context,  a 
     "focus kind" and a "focus condition" (in practice, and for modularity,
     the focus kind is actually stored inside the condition). To unfocus, one
     needs to know the focus kind, and the condition (for instance "no condition" or
     the proof under focused must be complete) must be met.
   - Undo: since proofviews and focus stacks are immutable objects, 
     it could suffice to hold the previous states, to allow to return to the past.
     However, we also allow other modules to do actions that can be undone.
     Therefore the undo stack stores action to be ran to undo.
*)

open Term

type _focus_kind = int
type 'a focus_kind = _focus_kind
type focus_info = Obj.t
type unfocusable =
  | Cannot of exn
  | Loose
  | Strict
type _focus_condition = 
    (_focus_kind -> Proofview.proofview -> unfocusable) *
    (_focus_kind -> bool)
type 'a focus_condition = _focus_condition

let next_kind = ref 0
let new_focus_kind () =
  let r = !next_kind in
  incr next_kind;
  r

(* Auxiliary function to define conditions. *)
let check kind1 kind2 = kind1=kind2

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.*)
(* spiwack: we could consider having a list of authorized focus_kind instead
    of just one, if anyone needs it *)
(* [no_cond] only checks that the unfocusing command uses the right
    [focus_kind]. *)

module Cond = struct
  (* first attempt at an algebra of condition *)
  (* semantics:
     - [Cannot] means that the condition is not met
     - [Strict] that the condition is met
     - [Loose] that the condition is not quite met
       but authorises to unfocus provided a condition
       of a previous focus on the stack is (strictly)
       met. [Loose] focuses are those, like bullets,
       which do not have a closing command and
       are hence closed by unfocusing actions unrelated
       to their focus_kind.
  *)
  let bool e b =
    if b then fun _ _ -> Strict
    else fun _ _ -> Cannot e
  let loose c k p = match c k p with
    | Cannot _ -> Loose
    | c -> c
  let cloose l c =
    if l then loose c
    else c
  let (&&&) c1 c2 k p=
    match c1 k p , c2 k p with
    | Cannot e , _ 
    | _ , Cannot e -> Cannot e
    | Strict, Strict -> Strict
    | _ , _ -> Loose
  let kind e k0 k p = bool e (k0=k) k p 
  let pdone e k p = bool e (Proofview.finished p) k p
end


(* Unfocus command.
   Fails if the proof is not focused. *)
exception CannotUnfocusThisWay
let _ = Errors.register_handler begin function
  | CannotUnfocusThisWay ->
    Errors.error "This proof is focused, but cannot be unfocused this way"
  | _ -> raise Errors.Unhandled
end

open Cond
let no_cond_gen e ~loose_end k0 =
  cloose loose_end (kind e k0)
let no_cond_gen e ?(loose_end=false) k = no_cond_gen e ~loose_end k , check k
let no_cond ?loose_end = no_cond_gen CannotUnfocusThisWay ?loose_end
(* [done_cond] checks that the unfocusing command uses the right [focus_kind]
    and that the focused proofview is complete. *)
let done_cond_gen e ~loose_end k0 =
  (cloose loose_end (kind e k0)) &&& pdone e
let done_cond_gen e ?(loose_end=false) k = done_cond_gen e ~loose_end k , check k
let done_cond ?loose_end = done_cond_gen CannotUnfocusThisWay ?loose_end


(* Subpart of the type of proofs. It contains the parts of the proof which
   are under control of the undo mechanism *)
type proof = {
  (* Current focused proofview *)
  proofview: Proofview.proofview;
  (* History of the focusings, provides information on how
     to unfocus the proof and the extra information stored while focusing.
     The list is empty when the proof is fully unfocused. *)
  focus_stack: (_focus_condition*focus_info*Proofview.focus_context) list;
  (* Extra information which can be freely used to create new behaviours. *)
  intel: Store.t
}

(*** General proof functions ***)

let proof p =
  let (goals,sigma) = Proofview.proofview p.proofview in
  (* spiwack: beware, the bottom of the stack is used by [Proof]
     internally, and should not be exposed. *)
  let rec map_minus_one f = function
    | [] -> assert false
    | [_] -> []
    | a::l -> f a :: (map_minus_one f l)
  in
  let stack =
    map_minus_one (fun (_,_,c) -> Proofview.focus_context c) p.focus_stack
  in
  (goals,stack,sigma)

let rec unroll_focus pv = function
  | (_,_,ctx)::stk -> unroll_focus (Proofview.unfocus ctx pv) stk
  | [] -> pv

(* spiwack: a proof is considered completed even if its still focused, if the focus
   doesn't hide any goal.
   Unfocusing is handled in {!return}. *)
let is_done p =
  Proofview.finished p.proofview && 
  Proofview.finished (unroll_focus p.proofview p.focus_stack)

(* spiwack: for compatibility with <= 8.2 proof engine *)
let has_unresolved_evar p =
  Proofview.V82.has_unresolved_evar p.proofview

(* Returns the list of partial proofs to initial goals *)
let partial_proof p = Proofview.partial_proof p.proofview

(*** The following functions implement the basic internal mechanisms
     of proofs, they are not meant to be exported in the .mli ***)

(* An auxiliary function to push a {!focus_context} on the focus stack. *)
let push_focus cond inf context pr =
  { pr with focus_stack = (cond,inf,context)::pr.focus_stack }

exception FullyUnfocused
let _ = Errors.register_handler begin function
  | FullyUnfocused -> Errors.error "The proof is not focused"
  | _ -> raise Errors.Unhandled
end
(* An auxiliary function to read the kind of the next focusing step *)
let cond_of_focus pr =
  match pr.focus_stack with
  | (cond,_,_)::_ -> cond
  | _ -> raise FullyUnfocused

(* An auxiliary function to pop and read the last {!Proofview.focus_context} 
   on the focus stack. *)
let pop_focus pr =
  match pr.focus_stack with
  | focus::other_focuses -> 
      { pr with focus_stack = other_focuses }, focus
  | _ -> 
      raise FullyUnfocused

(* This function focuses the proof [pr] between indices [i] and [j] *)
let _focus cond inf i j pr =
  let focused, context = Proofview.focus i j pr.proofview in
  let pr = push_focus cond inf context pr in
  { pr with proofview = focused }

(* This function unfocuses the proof [pr], it raises [FullyUnfocused],
   if the proof is already fully unfocused.
   This function does not care about the condition of the current focus. *)
let _unfocus pr =
  let pr, (_,_,fc) = pop_focus pr in
   { pr with proofview = Proofview.unfocus fc pr.proofview }

(* Focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
let focus cond inf i pr =
  _focus cond (Obj.repr inf) i i pr

let rec unfocus kind pr () =
  let cond = cond_of_focus pr in
  match fst cond kind pr.proofview with
  | Cannot e -> raise e
  | Strict -> 
     let pr = _unfocus pr in
     pr
  | Loose ->
    begin try
            let pr = _unfocus pr in
	    unfocus kind pr ()
      with FullyUnfocused -> raise CannotUnfocusThisWay
    end

exception NoSuchFocus
(* no handler: should not be allowed to reach toplevel. *)
let rec get_in_focus_stack kind stack =
  match stack with
  | ((_,check),inf,_)::stack ->
      if check kind then inf
      else get_in_focus_stack kind stack
  | [] -> raise NoSuchFocus
let get_at_focus kind pr =
  Obj.magic (get_in_focus_stack kind pr.focus_stack)

let is_last_focus kind pr =
  let ((_,check),_,_) = List.hd pr.focus_stack in
  check kind

let no_focused_goal p =
  Proofview.finished p.proofview

(* ugly code XXX *)
let maximal_unfocus k p =
  let rec aux p = 
    if no_focused_goal p then p
    else 
      try aux (unfocus k p ())
      with FullyUnfocused | CannotUnfocusThisWay -> p
  in 
    aux p


(*** Proof Creation/Termination ***)

(* [end_of_stack] is unfocused by return to close every loose focus. *)
let end_of_stack_kind = new_focus_kind ()
let end_of_stack = done_cond_gen FullyUnfocused end_of_stack_kind

let unfocused = is_last_focus end_of_stack_kind

let start goals =
  let pr = { 
    proofview = Proofview.init goals ;
    focus_stack = [] ;
    intel = Store.empty} in
  _focus end_of_stack (Obj.repr ()) 1 (List.length goals) pr

exception UnfinishedProof
exception HasUnresolvedEvar
let _ = Errors.register_handler begin function
  | UnfinishedProof -> Errors.error "Some goals have not been solved."
  | HasUnresolvedEvar -> Errors.error "Some existential variables are uninstantiated."
  | _ -> raise Errors.Unhandled
end

let return p t =
  if not (is_done p) then
    raise UnfinishedProof
  else if has_unresolved_evar p then 
    (* spiwack: for compatibility with <= 8.3 proof engine *)
    raise HasUnresolvedEvar
  else
    let p = unfocus end_of_stack_kind p () in
    Proofview.return p.proofview t

let initial_goals p = Proofview.initial_goals p.proofview

(*** Function manipulation proof extra informations ***)

let get_proof_info pr = pr.intel

let set_proof_info info pr = { pr with intel = info }

(*** Tactics ***)

let run_tactic env tac pr =
  let sp = pr.proofview in
  let tacticced_proofview = Proofview.apply env tac sp in
  { pr with proofview = tacticced_proofview }

let emit_side_effects eff pr = 
  {pr with proofview = Proofview.emit_side_effects eff pr.proofview}

(*** Commands ***)

let in_proof p k = Proofview.in_proofview p.proofview k

(*** Compatibility layer with <=v8.2 ***)
module V82 = struct
  let subgoals p =
    Proofview.V82.goals p.proofview

  let background_subgoals p =
    Proofview.V82.goals (unroll_focus p.proofview p.focus_stack)

  let top_goal p = 
    let { Evd.it=gls ; sigma=sigma; eff=eff } = 
	Proofview.V82.top_goals p.proofview
    in
    { Evd.it=List.hd gls ; sigma=sigma; eff=eff }

  let top_evars p =
    Proofview.V82.top_evars p.proofview

  let grab_evars p =
    if not (is_done p) then
      raise UnfinishedProof
    else
      { p with proofview = Proofview.V82.grab p.proofview }
    

    let instantiate_evar n com pr =
      let sp = pr.proofview in
      try
	let new_proofview = Proofview.V82.instantiate_evar n com sp in
        { pr with proofview = new_proofview }
      with e -> 
	raise e
end
