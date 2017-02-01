(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {6 The sorts of CCI. } *)

type family = InProp | InSet | InType

type sorts
type t = sorts

val set  : sorts
val prop : sorts
val type1  : sorts

val equal : sorts -> sorts -> bool
val compare : sorts -> sorts -> int
val hash : sorts -> int

val is_set : sorts -> bool
val is_prop : sorts -> bool
val is_small : sorts -> bool
val family : sorts -> family
val family_mem : sorts -> family -> bool

val hcons : sorts -> sorts

val family_equal : family -> family -> bool

val family_leq : family -> family -> bool

val family_of_sort : sorts -> family

val sort_of_product : is_impredicative_set:bool -> sorts -> sorts -> sorts

val sup : sorts -> sorts -> sorts
val super : sorts -> sorts

val univ_of_sort : sorts -> Univ.universe

type level_printer = Univ.Level.t -> Pp.std_ppcmds

(** {6 Constraints. } *)
type constraint_type = Graphgen.constraint_type = Lt | Le | Eq

val pr_constraint_type : constraint_type -> Pp.std_ppcmds

type univ_constraint = Univ.Level.t * constraint_type * Univ.Level.t
type sort_constraint =
  | UnivConstraint of univ_constraint

module Constraint :
sig
  include Set.S with type elt = sort_constraint

  val add_univ : univ_constraint -> t -> t

  val pr : level_printer -> t -> Pp.std_ppcmds
end

type constraints = Constraint.t

val hcons_constraints : constraints -> constraints

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

val constraints_of : 'a constrained -> constraints

(** Enforcing constraints. *)
type 'a constraint_function = 'a -> 'a -> constraints -> constraints

(** Type explanation is used to decorate error messages to provide
  useful explanation why a given constraint is rejected. It is composed
  of a path of universes and relation kinds [(r1,u1);..;(rn,un)] means
   .. <(r1) u1 <(r2) ... <(rn) un (where <(ri) is the relation symbol
  denoted by ri, currently only < and <=). The lowest end of the chain
  is supposed known (see UniverseInconsistency exn). The upper end may
  differ from the second univ of UniverseInconsistency because all
  universes in the path are canonical. Note that each step does not
  necessarily correspond to an actual constraint, but reflect how the
  system stores the graph and may result from combination of several
  constraints...
 *)
type univ_explanation = (constraint_type * Univ.universe) list
type univ_inconsistency = constraint_type * Univ.universe * Univ.universe * univ_explanation option

exception UniverseInconsistency of univ_inconsistency

val explain_inconsistency : level_printer -> univ_inconsistency -> Pp.std_ppcmds

val enforce_eq : sorts constraint_function
val enforce_leq : sorts constraint_function
val univ_enforce_eq : Univ.Universe.t constraint_function
val univ_enforce_leq : Univ.Universe.t constraint_function
val univ_enforce_eq_level : Univ.Level.t constraint_function
val univ_enforce_leq_level : Univ.Level.t constraint_function

(** {6 Substitution. } *)

type level_subst = Univ.universe_level_subst
val pr_level_subst : level_subst -> Pp.std_ppcmds
val empty_level_subst : level_subst
val is_empty_level_subst : level_subst -> bool

type sort_subst = Univ.universe_subst
val pr_sort_subst : sort_subst -> Pp.std_ppcmds
val empty_sort_subst : sort_subst
val is_empty_sort_subst : sort_subst -> bool

type level_subst_fn = Univ.universe_level_subst_fn
type sort_subst_fn = Univ.universe_subst_fn

val level_subst_fn : level_subst -> level_subst_fn
val sort_subst_fn : sort_subst -> sort_subst_fn

val level_subst_sorts : level_subst -> sorts -> sorts
val level_subst_constraints : level_subst -> constraints -> constraints

val subst_sorts : sort_subst_fn -> sorts -> sorts
val subst_constraints : sort_subst_fn -> constraints -> constraints

(** {6 Instances. } *)

module Instance :
sig
  type t

  val empty : t
  val is_empty : t -> bool

  val of_array : Univ.Level.t array -> t
  val to_array : t -> Univ.Level.t array

  val append : t -> t -> t
  (** To concatenate two instances, used for discharge *)

  val equal : t -> t -> bool
  (** Equality *)

  val length : t -> int
  (** Instance length *)

  val hcons : t -> t
  (** Hash-consing. *)

  val hash : t -> int
  (** Hash value *)

  val share : t -> t * int
  (** Simultaneous hash-consing and hash-value computation *)

  val make_subst : t -> level_subst
  val make_subst_fn : t -> level_subst_fn
  (** Substitution from an instance. *)

  val apply_subst : level_subst_fn -> t -> t
  (** Substitution by a level-to-level function. *)

  val pr : level_printer -> t -> Pp.std_ppcmds
  (** Pretty-printing, no comments *)

  val to_set : t -> Univ.USet.t
  (** The set of levels in the instance *)
end

type sort_instance = Instance.t

val subst_instance_instance : sort_instance -> sort_instance -> sort_instance
val subst_instance_sort : sort_instance -> sorts -> sorts
val subst_instance_constraints : sort_instance -> constraints -> constraints

val enforce_eq_instances : sort_instance constraint_function

type 'a polymorphic = 'a * sort_instance
val out_polymorphic : 'a polymorphic -> 'a
val in_monomorphic : 'a -> 'a polymorphic

val eq_polymorphic : ('a -> 'a -> bool) -> 'a polymorphic -> 'a polymorphic -> bool

(** {6 Sort graphs. } *)
module Graph :
sig
  type t

  (** The graph with only relations between litteral levels (Prop, Set, HSet, HInf).*)
  val initial : t

  val is_initial : t -> bool

  (** [sort_universes g] builds a totally ordered universe graph.  The
      output graph should imply the input graph (and the implication
      will be strict most of the time), but is not necessarily minimal.
      Moreover, it adds levels [Type.n] to identify universes at level
      n. An artificial constraint Set < Type.2 is added to ensure that
      Type.n and small universes are not merged. Note: the result is
      unspecified if the input graph already contains [Type.n] nodes
      (calling a module Type is probably a bad idea anyway).
      Seems to be only for printing. *)
  val sort : t -> t

  exception AlreadyDeclared (* = Graphgen.AlreadyDeclared *)
  val add_universe : Univ.Level.t -> bool -> t -> t

  (** Merge of constraints in a universes graph.
      The function [merge_constraints] merges a set of constraints in a given
      universes graph. It raises the exception [UniverseInconsistency] if the
      constraints are not satisfiable. *)
  val enforce_constraint : sort_constraint -> t -> t
  val merge_constraints : constraints -> t -> t

  val to_constraints : t -> constraints

  (* FIXME consistency in order of arguments. *)
  val check_constraint : t -> sort_constraint -> bool
  val check_constraints : constraints -> t -> bool

  (** Pretty-printing *)
  val pr : level_printer -> t -> Pp.std_ppcmds

  (** Dumping to a file. *)
  val dump :
    (constraint_type -> string -> string -> unit) ->
    t -> unit

  type 'a check_function = t -> 'a -> 'a -> bool

  val univ_check_eq : Univ.Universe.t check_function
  val univ_check_leq : Univ.Universe.t check_function
  val check_eq : sorts check_function
  val check_leq : sorts check_function

  (** Check equality of instances w.r.t. a universe graph. *)
  val check_eq_instances : Instance.t check_function
end

(** A vector of universe levels with universe constraints,
    representiong local universe variables and associated constraints *)

module UContext :
sig
  type t

  val make : Instance.t constrained -> t

  val empty : t
  val is_empty : t -> bool

  val instance : t -> Instance.t
  val constraints : t -> constraints

  val dest : t -> Instance.t * constraints

  (** Keeps the order of the instances *)
  val union : t -> t -> t

  (* the number of universes in the context *)
  val size : t -> int

  val hcons : t -> t

  val pr : level_printer -> t -> Pp.std_ppcmds
end

type universe_context = UContext.t

val instantiate_univ_context : universe_context -> universe_context

val instantiate_univ_constraints : sort_instance -> universe_context -> constraints

(** Universe contexts (as sets) *)

module ContextSet :
sig
  type t = Univ.universe_set constrained

  val empty : t
  val is_empty : t -> bool

  val singleton : Univ.Level.t -> t
  val of_instance : Instance.t -> t
  val of_set : Univ.universe_set -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_universe : Univ.Level.t -> t -> t
  val add_constraints : constraints -> t -> t
  val add_instance : Instance.t -> t -> t

  (** Arbitrary choice of linear order of the variables *)
  val to_context : t -> universe_context
  val of_context : universe_context -> t

  val constraints : t -> constraints
  val levels : t -> Univ.universe_set

  val hcons : t -> t

  val pr : level_printer -> t -> Pp.std_ppcmds
end

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
 *)
type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

val abstract_sorts : bool -> universe_context -> level_subst * universe_context

(** Incomplete *)

val of_level : Univ.Level.t -> sorts
val level : sorts -> Univ.Level.t option
val levels : sorts -> Univ.USet.t
val level_mem : Univ.Level.t -> sorts -> bool

val is_variable : sorts -> bool

val pr : sorts -> Pp.std_ppcmds
val pr_with : level_printer -> sorts -> Pp.std_ppcmds
