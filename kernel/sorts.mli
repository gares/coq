(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {6 The sorts of CCI. } *)

type family = InProp | InSet | InType

type t

val set  : t
val prop : t
val type1  : t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val is_set : t -> bool
val is_prop : t -> bool
val is_small : t -> bool
val family : t -> family
val family_mem : t -> family -> bool

val hcons : t -> t

val family_equal : family -> family -> bool

val family_leq : family -> family -> bool

val family_of_sort : t -> family

val sort_of_product : is_impredicative_set:bool -> t -> t -> t

val sup : t -> t -> t
val super : t -> t

val univ_of_sort : t -> Univ.universe

val check_eq : t UGraph.check_function
val check_leq : t UGraph.check_function

val enforce_eq : t Univ.constraint_function
val enforce_leq : t Univ.constraint_function

val subst_univs_sort : Univ.universe_subst_fn -> t -> t
val subst_univs_level_sort : Univ.universe_level_subst -> t -> t
val subst_instance_sort : Univ.universe_instance -> t -> t

val of_level : Univ.Level.t -> t
val level : t -> Univ.Level.t option
val levels : t -> Univ.LSet.t
val level_mem : Univ.Level.t -> t -> bool

val is_variable : t -> bool

val pr : t -> Pp.std_ppcmds
val pr_with : (Univ.Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
