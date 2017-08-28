(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Identity complexity. *)

module TLevel :
sig
  type t
  (** Type of truncation levels. A truncation level is essentially a unique name
      that will be associated to constraints later on. *)

  val hprop : t
  val hset : t
  val hinf : t

  val is_hprop : t -> bool
  val is_hset : t -> bool
  val is_hinf : t -> bool
  val is_litteral : t -> bool

  val apart : t -> t -> bool

  val equal : t -> t -> bool
  (** Equality function *)

  val leq : t -> t -> bool

  val compare : t -> t -> int
  (** Comparison function *)

  val hash : t -> int
  val hcons : t -> t

  val of_path : Names.DirPath.t -> int -> t
  (** Create a new level from a unique identifier and an associated
      module path. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option
end

type truncation_level = TLevel.t

module TSet :
sig
  include CSig.SetS with type elt = TLevel.t

  val hcons : t -> t

  val pr : (TLevel.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds

  val of_array : TLevel.t array -> t
end

type truncation_set = TSet.t

module TMap :
sig
  include CMap.ExtS with type key = TLevel.t and module Set := TSet

  val union : 'a t -> 'a t -> 'a t
  (** [union x y] favors the bindings in the first map. *)

  val diff : 'a t -> 'a t -> 'a t
  (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

  val subst_union : 'a option t -> 'a option t -> 'a option t
  (** [subst_union x y] favors the bindings of the first map that are [Some],
      otherwise takes y's bindings. *)

  val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
  (** Pretty-printing *)
end

type 'a truncation_map = 'a TMap.t

module Truncation :
sig
  type t

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int
  (** Hash function *)

  val hcons : t -> t
  (** Hash-consing *)

  val of_level : TLevel.t -> t
  (** Create a truncation representing the given level. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val pr_with : (TLevel.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds

  val is_level : t -> bool
  (** Test if the truncation is a level or an algebraic truncation. *)

  val level : t -> TLevel.t option
  (** Try to get a level out of a truncation, returns [None] if it
      is an algebraic truncation. *)

  val levels : t -> TSet.t
  (** Get the levels inside the truncation *)

  val level_mem : TLevel.t -> t -> bool
  (** [level_mem l u]: does l appear in u?
      Not meaningful for l=hset since that's neutral for sup. *)

  val level_rem : TLevel.t -> t -> t -> t
  (** [level_rem u v min] removes [u] from [v], resulting in [min]
      if [v] was exactly [u]. *)

  val sup : t -> t -> t
  (** The l.u.b. of 2 truncations *)

  val leq : t -> t -> bool

  val hprop : t
  val hset : t
  val hinf : t

  val is_hprop : t -> bool
  val is_hset : t -> bool
  val is_hinf : t -> bool

  val fold : (TLevel.t -> 'a -> 'a) -> t -> 'a -> 'a

  val exists : (TLevel.t -> bool) -> t -> bool
  val for_all : (TLevel.t -> bool) -> t -> bool
end

type truncation = Truncation.t

(** {6 Substitution} *)

type truncation_subst_fn = truncation_level -> truncation
type truncation_level_subst_fn = truncation_level -> truncation_level

(** A full substitution, might involve algebraic truncations *)
type truncation_subst = truncation truncation_map
type truncation_level_subst = truncation_level truncation_map

val trunc_level_subst_of : truncation_subst_fn -> truncation_level_subst_fn

val empty_trunc_level_subst : truncation_level_subst
val is_empty_trunc_level_subst : truncation_level_subst -> bool

(** Substitution of truncations. *)
val subst_truncs_level_level : truncation_level_subst -> truncation_level -> truncation_level
val subst_truncs_level_truncation : truncation_level_subst -> truncation -> truncation
val subst_truncs_level_truncation_fn : truncation_level_subst_fn -> truncation -> truncation

(** Level to truncation substitutions. *)

val empty_trunc_subst : truncation_subst
val is_empty_trunc_subst : truncation_subst -> bool
val make_trunc_subst : truncation_subst -> truncation_subst_fn

val subst_truncs_truncation : truncation_subst_fn -> truncation -> truncation

(** {6 Pretty-printing of truncations. } *)

val pr_truncation_level_subst : truncation_level_subst -> Pp.std_ppcmds
val pr_truncation_subst : truncation_subst -> Pp.std_ppcmds
