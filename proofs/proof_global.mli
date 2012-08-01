(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines proof facilities relevant to the toplevel.
 *  In particular it defines the global proof environment. *)

exception NoCurrentProof

type lemma_possible_guards = int list list

type closed_proof =
  Names.identifier * 
  (Entries.definition_entry list * lemma_possible_guards * 
    Decl_kinds.goal_kind * unit Tacexpr.declaration_hook)

(**********************************************************)
(*                                                        *)
(*   Imperative interface to the list of ongoing proofs   *)
(*                                                        *)
(**********************************************************)

val there_are_pending_proofs : unit -> bool
val check_no_pending_proof : unit -> unit

val get_used_variables : unit -> Sign.section_context option
val get_current_proof_name : unit -> Names.identifier
val get_all_proof_names : unit -> Names.identifier list

val set_endline_tactic : unit Proofview.tactic -> unit
val set_used_variables : Names.identifier list -> unit

val give_me_the_proof : unit -> Proof.proof

(* (more) functional interface to the current proof *)
val with_current_proof :
  (unit Proofview.tactic -> Proof.proof -> Proof.proof) -> unit

(* hook is a function to be applied at proof end (e.g. to declare the built
   constructions as a coercion or a setoid morphism). *)
val start_proof :
  Names.identifier -> Decl_kinds.goal_kind ->
  (Environ.env * Term.types) list -> ?compute_guard:lemma_possible_guards -> 
  unit Tacexpr.declaration_hook -> unit

val close_proof : unit -> closed_proof
val close_future_proof : unit Future.computation -> closed_proof
val discard : Names.identifier Loc.located -> unit
val discard_current : unit -> unit
val discard_all : unit -> unit

(**********************************************************)
(*                                                        *)
(*                            Proof modes                 *)
(*                                                        *)
(**********************************************************)

(** Type of proof modes :
    - A name
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it *)
type proof_mode = {
  name : string ;
  set : unit -> unit ;
  reset : unit -> unit
}

(** Registers a new proof mode which can then be adressed by name
    in [set_default_proof_mode].
    One mode is already registered - the standard mode - named "No",
    It corresponds to Coq default setting are they are set when coqtop starts *)
val register_proof_mode : proof_mode -> unit

(** [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. 
    bad: uses the proof status *)
val set_proof_mode : string -> unit

val activate_proof_mode : string -> unit
val disactivate_proof_mode : string -> unit

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet : sig
  type t = Vernacexpr.bullet

  (** A [behavior] is the data of a put function which
      is called when a bullet prefixes a tactic, together
      with a name to identify it. *)
  type behavior = {
    name : string;
    put : Proof.proof -> t -> Proof.proof
  }

  (** A registered behavior can then be accessed in Coq
      through the command [Set Bullet Behavior "name"].

      Two modes are registered originally:
      * "Strict Subproofs":
        - If this bullet follows another one of its kind, defocuses then focuses
          (which fails if the focused subproof is not complete).
        - If it is the first bullet of its kind, then focuses a new subproof.
      * "None": bullets don't do anything *)
  val register_behavior : behavior -> unit

  (** Handles focusing/defocusing with bullets: *)
  val put : Proof.proof -> t -> Proof.proof
end

module V82 : sig
  val get_current_initial_conclusions :
    unit ->
      Names.identifier * 
       (Term.types list * Decl_kinds.goal_kind * unit Tacexpr.declaration_hook)
end

(**********************************************************)
(*                                                        *)
(*                 XXX not part of summary                *)
(*                                                        *)
(**********************************************************)

type state
val freeze : unit -> state
val unfreeze : state -> unit
