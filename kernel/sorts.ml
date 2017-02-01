(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ
open Util

type family = InProp | InSet | InType

type sorts = universe
type t = sorts

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
  is_prop s || (is_impredicative_set && is_set s)

let sort_of_product ~is_impredicative_set domsort rangsort =
  if is_impredicative ~is_impredicative_set rangsort then rangsort
  else Universe.sup domsort rangsort

let sup = Universe.sup

let super = Universe.super

let hcons = hcons_univ
let hash = Universe.hash

type level_printer = Level.t -> Pp.std_ppcmds

type constraint_type = Graphgen.constraint_type = Lt | Le | Eq

let pr_constraint_type op =
  let op_str = match op with
    | Lt -> " < "
    | Le -> " <= "
    | Eq -> " = "
  in Pp.str op_str

let constraint_type_ord c1 c2 =
  match c1, c2 with
  | Lt, Lt -> 0
  | Lt, _ -> -1
  | Le, Lt -> 1
  | Le, Le -> 0
  | Le, Eq -> -1
  | Eq, Eq -> 0
  | Eq, _ -> 1

type univ_constraint = Univ.Level.t * constraint_type * Univ.Level.t
let compare_univ_constraint (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = Level.compare u u' in
    if not (Int.equal i' 0) then i'
    else Level.compare v v'

type sort_constraint =
  | UnivConstraint of univ_constraint

module ConstraintOrd =
  struct
    type t = sort_constraint
    let compare a b =
      match a, b with
      | UnivConstraint a, UnivConstraint b -> compare_univ_constraint a b
  end

module Constraint = struct
  module M = Set.Make(ConstraintOrd)
  include M

  let pr prl c =
    let open Pp in
    fold
      (fun c pp_std ->
        match c with
        | UnivConstraint (u,op,v) ->
           pp_std ++ prl u ++ pr_constraint_type op ++ prl v ++ fnl ())
      c (str "")

  let add_univ c cs = add (UnivConstraint c) cs
end

type constraints = Constraint.t

module Hconstraint =
  Hashcons.Make(
    struct
      type t = sort_constraint
      type u = universe_level -> universe_level
      let hashcons hul (UnivConstraint (l1,k,l2)) = UnivConstraint (hul l1, k, hul l2)
      let eq (UnivConstraint (l1,k,l2)) (UnivConstraint (l1',k',l2')) =
	l1 == l1' && k == k' && l2 == l2'
      let hash = Hashtbl.hash
    end)

module Hconstraints =
  Hashcons.Make(
    struct
      type t = constraints
      type u = sort_constraint -> sort_constraint
      let hashcons huc s =
	Constraint.fold (fun x -> Constraint.add (huc x)) s Constraint.empty
      let eq s s' =
	List.for_all2eq (==)
	  (Constraint.elements s)
	  (Constraint.elements s')
      let hash = Hashtbl.hash
    end)

let hcons_constraint =
  Hashcons.simple_hcons Hconstraint.generate Hconstraint.hcons Level.hcons
let hcons_constraints =
  Hashcons.simple_hcons Hconstraints.generate Hconstraints.hcons hcons_constraint

type 'a constrained = 'a * constraints

let constraints_of (_,c) = c

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

type univ_explanation = (constraint_type * Univ.universe) list
type univ_inconsistency = constraint_type * Univ.universe * Univ.universe * univ_explanation option

exception UniverseInconsistency of univ_inconsistency

let explain_universe_inconsistency prl (o,u,u',p) =
  let open Pp in
  let pr_uni = Universe.pr_with prl in
  let pr_rel = function
    | Eq -> str"=" | Lt -> str"<" | Le -> str"<="
  in
  let reason = match p with
    | None | Some [] -> mt()
    | Some p ->
      str " because" ++ spc() ++ pr_uni u' ++
	prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ pr_uni v)
	p ++
	(if Universe.equal (snd (List.last p)) u then mt() else
	    (spc() ++ str "= " ++ pr_uni u))
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni u' ++ reason

let explain_inconsistency = explain_universe_inconsistency

let univ_enforce_eq_level u v c =
  if Level.equal u v then c
  else if Level.apart u v then
    raise (UniverseInconsistency (Eq, Universe.make u, Universe.make v, None))
  else Constraint.add_univ (u, Eq, v) c

let univ_enforce_eq u v c =
  if Universe.equal u v then c
  else
    match Universe.level u, Universe.level v with
    | Some u, Some v -> univ_enforce_eq_level u v c
    | _ -> CErrors.anomaly (Pp.str "A universe comparison can only happen between variables")

let enforce_eq = univ_enforce_eq

let univ_enforce_leq_expr (x,n) (y,m) c =
  if Level.equal x y && Int.equal n m then c
  else
    let j = m - n in
    if j = -1 (* n = m+1, v+1 <= u <-> v < u *) then
      Constraint.add_univ (x,Lt,y) c
    else if j <= -1 (* n = m+k, v+k <= u <-> v+(k-1) < u *) then
      if Level.equal x y then (* u+(k+1) <= u *)
        let plusn u n =
          let rec aux u n =
            if n == 0 then u
            else aux (Universe.super u) (n-1)
          in
          aux (Universe.make u) n
        in
	raise (UniverseInconsistency (Le, plusn x n, plusn y m, None))
      else CErrors.anomaly (Pp.str "Unable to handle arbitrary u+k <= v constraints")
    else if j = 0 then
      Constraint.add_univ (x,Le,y) c
    else (* j >= 1 *) (* m = n + k, u <= v+k *)
      if Level.equal x y then c (* u <= u+k, trivial *)
      else if Level.is_small x then c (* Prop,Set <= u+S k, trivial *)
      else CErrors.anomaly (Pp.str "Unable to handle arbitrary u <= v+k constraints")

let check_univ_leq_one u v = Universe.exists (Universe.Expr.leq u) v

let check_univ_leq u v =
  Universe.for_all (fun u -> check_univ_leq_one u v) u

let univ_enforce_leq u v c =
  if check_univ_leq u v then c
  else Universe.fold (fun v -> Universe.fold (fun u -> univ_enforce_leq_expr u v) u) v c

let enforce_leq = univ_enforce_leq

let univ_enforce_leq_level u v c =
  if Level.equal u v then c
  else Constraint.add_univ (u, Le, v) c

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (super u) v

(** Substitutions. *)
type level_subst = Univ.universe_level_subst
let pr_level_subst = Univ.pr_universe_level_subst
let empty_level_subst = Univ.empty_univ_level_subst
let is_empty_level_subst = Univ.is_empty_univ_level_subst

type sort_subst = Univ.universe_subst
let pr_sort_subst  = Univ.pr_universe_subst
let empty_sort_subst = Univ.empty_univ_subst
let is_empty_sort_subst = Univ.is_empty_univ_subst

type level_subst_fn = Univ.universe_level_subst_fn
type sort_subst_fn = Univ.universe_subst_fn

let level_subst_fn = subst_univs_level_level
let sort_subst_fn = Univ.make_univ_subst

let level_subst_sorts = subst_univs_level_universe

let level_subst_constraint subst = function
  | UnivConstraint (u,d,v) ->
     let u' = level_subst_fn subst u in
     let v' = level_subst_fn subst v in
     if d != Lt && Level.equal u' v' then None
     else Some (UnivConstraint (u', d, v'))

let level_subst_constraints subst cs =
  Constraint.fold
    (fun c -> Option.fold_right Constraint.add (level_subst_constraint subst c))
  cs Constraint.empty

let subst_sorts = subst_univs_universe

let subst_univs_level fn l =
  try Some (fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_univs_level fn u in
  let v' = subst_univs_level fn v in
  match u', v' with
  | None, None -> Constraint.add_univ c cstrs
  | Some u, None -> enforce_univ_constraint (u, d, Universe.make v) cstrs
  | None, Some v -> enforce_univ_constraint (Universe.make u, d, v) cstrs
  | Some u, Some v -> enforce_univ_constraint (u, d, v) cstrs


let subst_constraints fn cs =
  Constraint.fold
    (fun (UnivConstraint c) cs -> subst_univs_constraint fn c cs)
  cs Constraint.empty

(** Instances. *)

module Instance = struct
  type t = Level.t array

  let empty = [| |]

  module HInstancestruct =
  struct
    type _t = t
    type t = _t
    type u = Level.t -> Level.t

    let hashcons huniv a =
      let len = Array.length a in
	if Int.equal len 0 then empty
	else begin
	  for i = 0 to len - 1 do
	    let x = Array.unsafe_get a i in
	    let x' = huniv x in
	      if x == x' then ()
	      else Array.unsafe_set a i x'
	  done;
	  a
	end

    let eq t1 t2 =
      t1 == t2 ||
	(Int.equal (Array.length t1) (Array.length t2) &&
	   let rec aux i =
	     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	   in aux 0)

    let hash a =
      let accu = ref 0 in
	for i = 0 to Array.length a - 1 do
	  let l = Array.unsafe_get a i in
	  let h = Level.hash l in
	    accu := Hashset.Combine.combine !accu h;
	done;
	(* [h] must be positive. *)
	let h = !accu land 0x3FFFFFFF in
	  h
  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons Level.hcons

  let hash = HInstancestruct.hash

  let share a = (hcons a, hash a)

  let empty = hcons [||]

  let is_empty x = Int.equal (Array.length x) 0

  let append x y =
    if Array.length x = 0 then y
    else if Array.length y = 0 then x
    else Array.append x y

  let of_array a =
    assert(Array.for_all (fun x -> not (Level.is_prop x)) a);
    a

  let to_array a = a

  let length a = Array.length a

  let subst_fn fn t =
    let t' = CArray.smartmap fn t in
      if t' == t then t else of_array t'

  let to_set x = USet.of_array x

  let pr =
    Pp.prvect_with_sep Pp.spc

  let equal t u =
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
      (CArray.for_all2 Level.equal t u
	 (* Necessary as universe instances might come from different modules and
	    unmarshalling doesn't preserve sharing *))

  let make_subst inst =
    Array.fold_left_i
      (fun i acc l ->
        UMap.add l (Level.var i) acc)
      UMap.empty inst

  let make_subst_fn inst l =
    match Level.var_index l with
    | None -> l
    | Some n -> inst.(n)

  let apply_subst fn t = CArray.smartmap fn t
end

type sort_instance = Instance.t

let subst_instance_instance s i = Instance.apply_subst (Instance.make_subst_fn s) i

let subst_instance_sort s u = subst_univs_level_universe_fn (Instance.make_subst_fn s) u

let subst_instance_univ_constraint s (u,d,v as c) =
  let u' = Instance.make_subst_fn s u in
  let v' = Instance.make_subst_fn s v in
  if u' == u && v' == v then c
  else (u',d,v')

let subst_instance_constraints s cs =
  Constraint.fold
    (fun (UnivConstraint c) cs -> Constraint.add_univ (subst_instance_univ_constraint s c) cs)
    cs Constraint.empty

let enforce_eq_instances ax ay =
  begin
    if Array.length ax != Array.length ay then
      let open Pp in
      CErrors.anomaly
        (str "Invalid argument: enforce_eq_instances called with" ++
           str " instances of different lengths")
  end;
  CArray.fold_right2 univ_enforce_eq_level ax ay

(** A polymorphic thing is a thing with an instance. *)
type 'a polymorphic = 'a * Instance.t
let out_polymorphic (x, _) = x
let in_monomorphic x = (x, Instance.empty)

let eq_polymorphic eq (x,ix) (y,iy) =
  eq x y && Instance.equal ix iy

module Graph = struct
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
    module USet = Univ.USet
    module UMap = Univ.UMap

    type level_constraint = univ_constraint
    type constraints = Constraint.t
    let add_constraint = Constraint.add_univ

    type explanation = (constraint_type * Level.t) list
    let error_inconsistency o u v exp =
      raise (UniverseInconsistency (o, Universe.make u, Universe.make v,
                                    Option.map (List.map (fun (o, u) -> o, Universe.make u)) exp))
  end

  module UGraph = Graphgen.Make(UGraphIn)

  type t = UGraph.t

  let initial = UGraph.initial
  let is_initial = UGraph.is_initial

  let sort = UGraph.sort_universes

  exception AlreadyDeclared = Graphgen.AlreadyDeclared
  let add_universe = UGraph.add_level

  let enforce_constraint c t =
    match c with
    | UnivConstraint c -> UGraph.enforce_constraint c t

  let merge_constraints cs t =
    Constraint.fold enforce_constraint cs t

  let to_constraints t =
    UGraph.constraints_of_universes t Constraint.empty

  let check_univ_constraint = UGraph.check_constraint

  let check_constraint t c =
    match c with
    | UnivConstraint c -> UGraph.check_constraint t c

  let check_constraints cs t =
    Constraint.for_all (check_constraint t) cs

  let pr = UGraph.pr

  let dump = UGraph.dump_universes

  type 'a check_function = t -> 'a -> 'a -> bool

  let check_leq_univ_level g u v = check_univ_constraint g (u, Le, v)
  let check_lt_univ_level g u v = check_univ_constraint g (u, Lt, v)

  let check_leq_univ_expr g (u,n) (v,m) =
    let diff = n - m in
    if diff <= 0 then check_leq_univ_level g u v
    else if diff == 1 then check_lt_univ_level g u v
    else false

  let univ_exists_bigger g ul l =
    Universe.exists (fun ul' ->
        check_leq_univ_expr g ul ul') l

  let real_univ_check_leq g u v =
    Universe.for_all (fun ul -> univ_exists_bigger g ul v) u

  let univ_check_leq g u v =
    Universe.equal u v ||
      is_type0m_univ u ||
      real_univ_check_leq g u v

  let real_univ_check_eq g u v =
    real_univ_check_leq g u v && real_univ_check_leq g v u

  let univ_check_eq g u v =
    Universe.equal u v || real_univ_check_eq g u v

  let check_eq = univ_check_eq
  let check_leq = univ_check_leq

  let univ_check_eq_level g u v = Level.equal u v || UGraph.check_constraint g (u, Eq, v)
  let check_eq_instances g t1 t2 =
    t1 == t2 ||
      (Int.equal (Array.length t1) (Array.length t2) &&
         let rec aux i =
           (Int.equal i (Array.length t1)) || (univ_check_eq_level g t1.(i) t2.(i) && aux (i + 1))
         in aux 0)

  (** Profiling *)
  let merge_constraints =
    if Flags.profile then
      let key = Profile.declare_profile "merge_constraints" in
      Profile.profile2 key merge_constraints
    else merge_constraints
  let check_constraints =
    if Flags.profile then
      let key = Profile.declare_profile "check_constraints" in
      Profile.profile2 key check_constraints
    else check_constraints
end

module UContext = struct
  type t = Instance.t constrained

  let make x = x

  let empty = (Instance.empty, Constraint.empty)
  let is_empty (us,cs) = Instance.is_empty us && Constraint.is_empty cs

  let instance (us, _) = us
  let constraints (_, cs) = cs

  let dest x = x

  let union (us, cs) (us', cs') =
    Instance.append us us', Constraint.union cs cs'

  let size (us, _) = Instance.length us

  let hcons (univs, cst) =
    (Instance.hcons univs, hcons_constraints cst)

  let pr prl (us, cs as ucs) =
    if is_empty ucs then Pp.mt()
    else
      let open Pp in
      h 0 (Instance.pr prl us ++ str " |= ") ++ h 0 (v 0 (Constraint.pr prl cs))
end

type universe_context = UContext.t

let instantiate_univ_context (us, cs) = (us, subst_instance_constraints us cs)
let instantiate_univ_constraints u (_, cs) = subst_instance_constraints u cs

module ContextSet = struct
  type t = Univ.universe_set constrained

  let empty = (USet.empty, Constraint.empty)
  let is_empty (us, cs) = USet.is_empty us && Constraint.is_empty cs

  let of_set s = s, Constraint.empty
  let singleton l = of_set (USet.singleton l)
  let of_instance i = of_set (Instance.to_set i)

  let equal (us, cs as x) (us', cs' as y) =
    x == y || (USet.equal us us' && Constraint.equal cs cs')

  let union (us, cs as x) (us', cs' as y) =
    if x == y then x
    else USet.union us us', Constraint.union cs cs'

  let append (us, cs) (us', cs') =
    let us = USet.fold USet.add us us' in
    let cs = Constraint.fold Constraint.add cs cs' in
    us, cs

  let diff (us, cs) (us', cs') =
    USet.diff us us', Constraint.diff cs cs'

  let add_universe u (us, cs) =
    USet.add u us, cs

  let add_constraints cs' (us, cs) =
    us, Constraint.union cs cs'

  let add_instance inst (us, cs) =
    let us = Array.fold_left (fun us u -> USet.add u us) us inst in
    us, cs

  let sort_levels a =
    Array.sort Level.natural_compare a; a
  let to_context (us, cs) =
    Instance.of_array (sort_levels (Array.of_list (USet.elements us))), cs

  let of_context (us, cs) =
    Instance.to_set us, cs

  let constraints (_, cs) = cs
  let levels (us, cs) = us

  let hcons (us, cs) =
    hcons_universe_set us, hcons_constraints cs

  let pr prl (us, cs as ctx) =
    if is_empty ctx then Pp.mt()
    else
      let open Pp in
      h 0 (USet.pr prl us ++ str " |= ") ++ h 0 (v 0 (Constraint.pr prl cs))
end

type universe_context_set = ContextSet.t

type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

let abstract_sorts poly ctx =
  let instance = UContext.instance ctx in
  if poly
  then
    let subst = Instance.make_subst instance in
    let cs = subst_instance_constraints instance (UContext.constraints ctx) in
    let ctx = UContext.make (instance, cs) in
    subst, ctx
  else
    empty_level_subst, ctx

(* ************** *)
let of_level = Universe.make
let level = Universe.level
let levels = Universe.levels
let level_mem = univ_level_mem

let is_variable = is_univ_variable

let pr = Universe.pr
let pr_with = Universe.pr_with

let subst_instance_constraints =
  if Flags.profile then
    let key = Profile.declare_profile "subst_instance_constraints" in
      Profile.profile2 key subst_instance_constraints
  else subst_instance_constraints
