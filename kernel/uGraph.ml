(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ

(* Shim to call Graphgen *)
module UGraphIn = struct
  module Level = struct
    type t = Level.t
    let equal = Level.equal
    let is_litteral = Level.is_small
    let min = Level.prop
    let var_min = Level.set
    let is_min = Level.is_prop
    let is_var_min = Level.is_set
    let max = None
    let is_max _ = false

    let of_path = Level.make
    let to_string = Level.to_string
    let pr = Level.pr
  end
  module LSet = Univ.LSet
  module LMap = Univ.LMap

  type constraint_type = Univ.constraint_type = Lt | Le | Eq

  type level_constraint = Univ.univ_constraint

  module Constraints = Univ.Constraint

  type explanation = (constraint_type * Level.t) list
  let error_inconsistency o u v exp =
    raise (UniverseInconsistency (o, Universe.make u, Universe.make v,
                                  Option.map (List.map (fun (o, u) -> o, Universe.make u)) exp))
end

module UGraph = Graphgen.Make(UGraphIn)
include UGraph

type universes = UGraph.t
let pr_universes = pr
let add_universe = add_level
let is_initial_universes = is_initial
let initial_universes = initial
let empty_universes = empty

let check_equal g u v = check_constraint g (u,Eq,v)

let check_eq_level g u v = u == v || check_equal g u v

let check_smaller g strict u v =
  let o = if strict then Lt else Le in
  check_constraint g (u,o,v)

(** Then, checks on universes *)

type 'a check_function = universes -> 'a -> 'a -> bool

let check_smaller_expr g (u,n) (v,m) =
  let diff = n - m in
    match diff with
    | 0 -> check_smaller g false u v
    | 1 -> check_smaller g true u v
    | x when x < 0 -> check_smaller g false u v
    | _ -> false

let exists_bigger g ul l =
  Universe.exists (fun ul' ->
    check_smaller_expr g ul ul') l

let real_check_leq g u v =
  Universe.for_all (fun ul -> exists_bigger g ul v) u

let check_leq g u v =
  Universe.equal u v ||
    is_type0m_univ u ||
    real_check_leq g u v

let check_eq_univs g l1 l2 =
  real_check_leq g l1 l2 && real_check_leq g l2 l1

let check_eq g u v =
  Universe.equal u v || check_eq_univs g u v

(** Instances *)

let check_eq_instances g t1 t2 =
  let t1 = Instance.to_array t1 in
  let t2 = Instance.to_array t2 in
  t1 == t2 ||
    (Int.equal (Array.length t1) (Array.length t2) &&
        let rec aux i =
          (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
        in aux 0)

(** Profiling *)
let check_eq =
  if Flags.profile then
    let check_eq_key = Profile.declare_profile "check_eq" in
    Profile.profile3 check_eq_key check_eq
  else check_eq

let check_leq =
  if Flags.profile then
    let check_leq_key = Profile.declare_profile "check_leq" in
    Profile.profile3 check_leq_key check_leq
  else check_leq
