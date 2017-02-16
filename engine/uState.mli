(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines universe unification states which are part of evarmaps.
    Most of the API below is reexported in {!Evd}. Consider using higher-level
    primitives when needed. *)

open Names

exception UniversesDiffer

type t
(** Type of universe unification states. They allow the incremental building of
    universe constraints during an interactive proof. *)

(** {5 Constructors} *)

val empty : t

val make : Sorts.Graph.t -> t

val is_empty : t -> bool

val union : t -> t -> t

val of_context_set : Sorts.universe_context_set -> t

val of_binders : Universes.universe_binders -> t

(** {5 Projections} *)

val context_set : t -> Sorts.universe_context_set
(** The local context of the state, i.e. a set of bound variables together
    with their associated constraints. *)

val subst : t -> Universes.universe_opt_subst
(** The local universes that are unification variables *)

val ugraph : t -> Sorts.Graph.t
(** The current graph extended with the local constraints *)

val algebraic_univs : t -> Univ.USet.t
val algebraic_truncs : t -> Trunc.TSet.t
(** The subset of unification variables that can be instantiated with algebraic
    universes as they appear in inferred types only. *)

val constraints : t -> Sorts.constraints
(** Shorthand for {!context_set} composed with {!ContextSet.constraints}. *)

val context : t -> Sorts.universe_context
(** Shorthand for {!context_set} with {!Context_set.to_context}. *)

(** {5 Constraints handling} *)

val add_constraints : t -> Sorts.constraints -> t
(**
  @raise UniversesDiffer when universes differ
*)

val add_universe_constraints : t -> Universes.universe_constraints -> t
(**
  @raise UniversesDiffer when universes differ
*)

(** {5 Names} *)

val add_universe_name : t -> string -> Univ.Level.t -> t
(** Associate a human-readable name to a local variable. *)

val add_truncation_name : t -> string -> Trunc.TLevel.t -> t

val universe_of_name : t -> string -> Univ.Level.t
(** Retrieve the universe associated to the name. *)

val truncation_of_name : t -> string -> Trunc.TLevel.t

(** {5 Unification} *)

val restrict : t -> Univ.universe_set -> Trunc.truncation_set -> t

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

val univ_rigid : rigid
val univ_flexible : rigid
val univ_flexible_alg : rigid

val merge : ?loc:Loc.t -> bool -> rigid -> t -> Sorts.universe_context_set -> t
val merge_subst : t -> Universes.universe_opt_subst -> t
val emit_side_effects : Safe_typing.private_constants -> t -> t

val new_univ_variable : ?loc:Loc.t -> rigid -> string option -> t -> t * Univ.Level.t
val add_global_univ : t -> Univ.Level.t -> t
val make_flexible_univ_variable : t -> bool -> Univ.Level.t -> t

val new_trunc_variable : ?loc:Loc.t -> rigid -> string option -> t -> t * Trunc.TLevel.t
val add_global_trunc : t -> Trunc.TLevel.t -> t
val make_flexible_trunc_variable : t -> bool -> Trunc.TLevel.t -> t

val is_univ_variable : t -> Univ.Universe.t -> Univ.Level.t option
val is_trunc_variable : t -> Trunc.Truncation.t -> Trunc.TLevel.t option

val normalize_variables : t -> Sorts.sort_subst * t

val constrain_variables : Univ.USet.t -> Trunc.TSet.t -> t -> Sorts.constraints

val abstract_undefined_variables : t -> t

val fix_undefined_variables : t -> t

val refresh_undefined_variables : t -> t * Sorts.level_subst

val normalize : t -> t

(** {5 TODO: Document me} *)

type universe_names =
  { univ_names : (Id.t Loc.located) list
  ; trunc_names : (Id.t Loc.located) list }

val universe_names_equal : universe_names -> universe_names -> bool

val universe_context :
  ?names:universe_names -> t ->
  Universes.universe_binders * Sorts.universe_context

val update_sigma_env : t -> Environ.env -> t

(** {5 Pretty-printing} *)

val pr_uctx_univ_level : t -> Univ.Level.t -> Pp.std_ppcmds
val pr_uctx_trunc_level : t -> Trunc.TLevel.t -> Pp.std_ppcmds
val pr_uctx_level : t -> Sorts.level_printer
