(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ

type family = InProp | InSet | InType

type t = universe

let prop = Universe.type0m
let set = Universe.type0
let type1 = type1_univ

let univ_of_sort s = s

let compare = Universe.compare

let equal = Universe.equal

let is_prop = is_type0m_univ

let is_set = is_type0_univ

let is_small = is_small_univ

let family s =
  if is_prop s then InProp
  else if is_set s then InSet
  else InType

let family_mem s = function
  | InProp -> is_prop s
  | InSet -> is_small s
  | InType -> true

let family_equal = (==)

let family_leq l r =
  match l, r with
  | InProp, _ | InSet, InSet | _, InType -> true
  | _, _ -> false

let family_of_sort s =
  if is_prop s then InProp
  else if is_set s then InSet
  else InType

let is_impredicative ~is_impredicative_set s =
  if is_impredicative_set then is_small s
  else is_prop s

let sort_of_product ~is_impredicative_set domsort rangsort =
  if is_impredicative ~is_impredicative_set rangsort then rangsort
  else Universe.sup domsort rangsort

let sup = Universe.sup

let super = Universe.super

module List = struct
  let mem = List.memq
  let intersect l l' = CList.intersect family_equal l l'
end

let hcons = hcons_univ
let hash = Universe.hash

let check_eq = UGraph.check_eq
let check_leq = UGraph.check_leq

let enforce_eq = Univ.enforce_eq
let enforce_leq = Univ.enforce_leq

let subst_univs_sort = subst_univs_universe
let subst_univs_level_sort = subst_univs_level_universe
let subst_instance_sort = subst_instance_universe

let of_level = Universe.make
let is_level = Universe.is_level
let level = Universe.level
let levels = Universe.levels
let level_mem = univ_level_mem

let is_variable = is_univ_variable

let pr = Universe.pr
let pr_with = Universe.pr_with
