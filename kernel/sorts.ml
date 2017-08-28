(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ
open Trunc
open Util

type family = InProp | InSet | InType

module Raw : sig
  type sorts = private {univ : universe; trunc : truncation; hash : int}

  val hcons : sorts -> sorts

  val make : universe -> truncation -> sorts
end = struct
  type sorts = {univ : universe; trunc : truncation; hash : int}


  module Self = struct
    type t = sorts
    type u = unit
    let eq x y =
      x.hash == y.hash
      && Universe.equal x.univ y.univ
      && Truncation.equal x.trunc y.trunc

    let hash x = x.hash

    let hashcons () x =
      let univ' = hcons_univ x.univ in
      let trunc' = Truncation.hcons x.trunc in
      if x.univ == univ' && x.trunc == trunc' then x
      else {x with univ = univ'; trunc = trunc'}
  end

  let hcons =
    let module H = Hashcons.Make(Self) in
    Hashcons.simple_hcons H.generate H.hcons ()

  let hash u t =
    Hashset.Combine.combine (Universe.hash u) (Truncation.hash t)

  let make univ trunc = hcons { hash = hash univ trunc; univ; trunc }
end

type sorts = Raw.sorts =
  private {univ : universe; trunc : truncation; hash : int}

let hash x = x.hash
let hcons : sorts -> sorts = Raw.hcons
let make : universe -> truncation -> sorts = Raw.make

let equal x y =
  x == y ||
    Int.equal x.hash y.hash
    && Universe.equal x.univ y.univ
    && Truncation.equal x.trunc y.trunc

type t = sorts

let compare s1 s2 =
  if s1 == s2 then 0
  else
    let cu = Universe.compare s1.univ s2.univ in
    if Int.equal cu 0 then Truncation.compare s1.trunc s2.trunc
    else cu

let prop = make Universe.type0m Truncation.hprop
let set = make Universe.type0 Truncation.hset
let type1 = make type1_univ Truncation.hinf

let univ_of_sort s = s.univ
let trunc_of_sort s = s.trunc

let is_prop s = is_type0m_univ (univ_of_sort s)

let is_set s = is_type0_univ (univ_of_sort s)

let is_small s = is_small_univ (univ_of_sort s)

let is_hprop s = Truncation.is_hprop (trunc_of_sort s)

let is_hset s = Truncation.is_hset (trunc_of_sort s)

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

type set_predicativity = ImpredicativeSet | PredicativeSet
let is_impredicative predset s =
  is_prop s || (match predset with ImpredicativeSet -> is_set s | PredicativeSet -> false)

let sort_of_product predset domsort rangsort =
  if is_impredicative predset rangsort then rangsort
  else
    let u = Universe.sup (univ_of_sort domsort) (univ_of_sort rangsort) in
    make u (trunc_of_sort rangsort)

let sup s1 s2 =
  make (Universe.sup s1.univ s2.univ) (Truncation.sup s1.trunc s2.trunc)

let super s =
  make (Universe.super s.univ) Truncation.hinf

type level_printer = (Level.t -> Pp.std_ppcmds) * (TLevel.t -> Pp.std_ppcmds)

let default_level_printer : level_printer = Level.pr, TLevel.pr

let prl_u (prl:level_printer) = fst prl
let prl_t (prl:level_printer) = snd prl

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
type trunc_constraint = Trunc.TLevel.t * constraint_type * Trunc.TLevel.t

let compare_univ_constraint (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = Level.compare u u' in
    if not (Int.equal i' 0) then i'
    else Level.compare v v'

let compare_trunc_constraint (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = TLevel.compare u u' in
    if not (Int.equal i' 0) then i'
    else TLevel.compare v v'

type sort_constraint =
  | UnivConstraint of univ_constraint
  | TruncConstraint of trunc_constraint

module UConstraintOrd =
  struct
    type t = univ_constraint
    let compare = compare_univ_constraint
  end

module UConstraint = struct
  module M = Set.Make(UConstraintOrd)
  include M

  let pr prl c =
    let open Pp in
    fold
      (fun (u,op,v) pp_std ->
        pp_std ++ prl u ++ pr_constraint_type op ++ prl v ++ fnl ())
      c (str "")
end

module TConstraintOrd =
  struct
    type t = trunc_constraint
    let compare = compare_trunc_constraint
  end

module TConstraint = struct
  module M = Set.Make(TConstraintOrd)
  include M

  let pr prl c =
    let open Pp in
    fold
      (fun (u,op,v) pp_std ->
        pp_std ++ prl u ++ pr_constraint_type op ++ prl v ++ fnl ())
      c (str "")
end

module ConstraintOrd =
  struct
    type t = sort_constraint
    let compare a b =
      match a, b with
      | UnivConstraint a, UnivConstraint b -> compare_univ_constraint a b
      | TruncConstraint a, TruncConstraint b -> compare_trunc_constraint a b
      | UnivConstraint _, TruncConstraint _ -> -1
      | TruncConstraint _, UnivConstraint _ -> 1
  end

module Constraint = struct
  module M = Set.Make(ConstraintOrd)
  include M

  let pr prl c =
    if is_empty c then Pp.str ""
    else
      let open Pp in
      let pp_us, pp_ts =
        fold
          (fun c (pp_us, pp_ts) ->
            match c with
            | UnivConstraint (u,op,v) ->
               let pp_us = pp_us ++ prl_u prl u ++ pr_constraint_type op ++ prl_u prl v ++ fnl () in
               pp_us, pp_ts
            | TruncConstraint (u,op,v) ->
               let pp_ts = pp_ts ++ prl_t prl u ++ pr_constraint_type op ++ prl_t prl v ++ fnl () in
               pp_us, pp_ts)
          c (str "", str "")
      in
      pp_us ++ str "; " ++ pp_ts

  let add_univ c cs = add (UnivConstraint c) cs

  let add_trunc c cs = add (TruncConstraint c) cs
end

type constraints = Constraint.t

let split_constraints csts =
  Constraint.fold
    (fun cstr (ucsts, tcsts) ->
      match cstr with
      | UnivConstraint cstr -> UConstraint.add cstr ucsts, tcsts
      | TruncConstraint cstr -> ucsts, TConstraint.add cstr tcsts)
    csts (UConstraint.empty, TConstraint.empty)

let merge_constraints ucsts tcsts =
  Constraint.empty
  |> UConstraint.fold Constraint.add_univ ucsts
  |> TConstraint.fold Constraint.add_trunc tcsts

module Hconstraint =
  Hashcons.Make(
    struct
      type t = sort_constraint
      type u = (universe_level -> universe_level) * (truncation_level -> truncation_level)
      let hashcons hul = function
        | UnivConstraint (l1,k,l2) -> UnivConstraint (fst hul l1, k, fst hul l2)
        | TruncConstraint (l1,k,l2) -> TruncConstraint (snd hul l1, k, snd hul l2)
      let eq a b =
        match a, b with
        | UnivConstraint (l1,k,l2), UnivConstraint (l1',k',l2') ->
	   l1 == l1' && k == k' && l2 == l2'
        | TruncConstraint (l1,k,l2), TruncConstraint (l1',k',l2') ->
	   l1 == l1' && k == k' && l2 == l2'
        | UnivConstraint _, TruncConstraint _ | TruncConstraint _, UnivConstraint _ -> false
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
  Hashcons.simple_hcons Hconstraint.generate Hconstraint.hcons (Level.hcons, TLevel.hcons)
let hcons_constraints =
  Hashcons.simple_hcons Hconstraints.generate Hconstraints.hcons hcons_constraint

type 'a constrained = 'a * constraints

let constraints_of (_,c) = c

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

type univ_explanation = (constraint_type * Univ.universe) list
type univ_inconsistency = constraint_type * Univ.universe * Univ.universe * univ_explanation option
type trunc_explanation = (constraint_type * truncation) list
type trunc_inconsistency = constraint_type * truncation * truncation * trunc_explanation option

type sort_inconsistency =
  | UnivInconsistency of univ_inconsistency
  | TruncInconsistency of trunc_inconsistency

exception SortInconsistency of sort_inconsistency

let explain_universe_inconsistency prl (o,u,u',p) =
  let open Pp in
  let pr_uni = Universe.pr_with (prl_u prl) in
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

let explain_truncation_inconsistency prl (o,u,u',p) =
  let open Pp in
  let pr_uni = Truncation.pr_with (prl_t prl) in
  let pr_rel = function
    | Eq -> str"=" | Lt -> str"<" | Le -> str"<="
  in
  let reason = match p with
    | None | Some [] -> mt()
    | Some p ->
      str " because" ++ spc() ++ pr_uni u' ++
	prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ pr_uni v)
	p ++
	(if Truncation.equal (snd (List.last p)) u then mt() else
	    (spc() ++ str "= " ++ pr_uni u))
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni u' ++ reason

let explain_inconsistency prl = function
  | UnivInconsistency i -> explain_universe_inconsistency prl i
  | TruncInconsistency i -> explain_truncation_inconsistency prl i

let sort_univ_inconsistency x =
  SortInconsistency (UnivInconsistency x)

let sort_trunc_inconsistency x =
  SortInconsistency (TruncInconsistency x)

let univ_enforce_eq_level u v c =
  if Level.equal u v then c
  else if Level.apart u v then
    raise (sort_univ_inconsistency (Eq, Universe.make u, Universe.make v, None))
  else Constraint.add_univ (u, Eq, v) c

let univ_enforce_eq u v c =
  if Universe.equal u v then c
  else
    match Universe.level u, Universe.level v with
    | Some u, Some v -> univ_enforce_eq_level u v c
    | _ -> CErrors.anomaly (Pp.str "A universe comparison can only happen between variables")

let trunc_enforce_eq_level u v c =
  if TLevel.equal u v then c
  else if TLevel.apart u v then
    raise (sort_trunc_inconsistency (Eq, Truncation.of_level u, Truncation.of_level v, None))
  else Constraint.add_trunc (u, Eq, v) c

let trunc_enforce_eq u v c =
  if Truncation.equal u v then c
  else
    match Truncation.level u, Truncation.level v with
    | Some u, Some v -> trunc_enforce_eq_level u v c
    | _ -> CErrors.anomaly (Pp.str "A truncation comparison can only happen between variables")

let enforce_eq s1 s2 c =
  c |> univ_enforce_eq s1.univ s2.univ |> trunc_enforce_eq s1.trunc s2.trunc

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
	raise (sort_univ_inconsistency (Le, plusn x n, plusn y m, None))
      else CErrors.anomaly (Pp.str "Unable to handle arbitrary u+k <= v constraints")
    else if j = 0 then
      Constraint.add_univ (x,Le,y) c
    else (* j >= 1 *) (* m = n + k, u <= v+k *)
      if Level.equal x y then c (* u <= u+k, trivial *)
      else if Level.is_small x then c (* Prop,Set <= u+S k, trivial *)
      else CErrors.anomaly (Pp.str "Unable to handle arbitrary u <= v+k constraints")

let check_univ_leq_one u v =
  Universe.exists (Universe.Expr.leq u) v

let check_univ_leq u v =
  Universe.for_all (fun u -> check_univ_leq_one u v) u

let univ_enforce_leq u v c =
  if check_univ_leq u v then c
  else Universe.fold (fun v -> Universe.fold (fun u -> univ_enforce_leq_expr u v) u) v c

let check_trunc_leq_one u v =
  Truncation.exists (TLevel.leq u) v

let check_trunc_leq u v =
  Truncation.for_all (fun u -> check_trunc_leq_one u v) u

let trunc_enforce_leq u v c =
  if check_trunc_leq u v then c
  else Truncation.fold (fun v -> Truncation.fold (fun u -> Constraint.add_trunc (u, Le, v)) u) v c

let enforce_leq s1 s2 c =
  c |> univ_enforce_leq s1.univ s2.univ |> trunc_enforce_leq s1.trunc s2.trunc

let univ_enforce_leq_level u v c =
  if Level.equal u v then c
  else Constraint.add_univ (u, Le, v) c

let trunc_enforce_leq_level u v c =
  if TLevel.leq u v then c
  else Constraint.add_trunc (u, Le, v) c

let enforce_univ_constraint (u, d, v) =
  match d with
  | Eq -> univ_enforce_eq u v
  | Le -> univ_enforce_leq u v
  | Lt -> univ_enforce_leq (Universe.super u) v

let enforce_trunc_constraint (u, d, v) =
  match d with
  | Eq -> trunc_enforce_eq u v
  | Le -> trunc_enforce_leq u v
  | Lt -> CErrors.anomaly (Pp.str "No strict comparisons between truncations")

(** Substitutions. *)
type level_subst = universe_level_subst * truncation_level_subst
let pr_level_subst (su,st) =
  Pp.(pr_universe_level_subst su ++ str "; " ++ pr_truncation_level_subst st)
let empty_level_subst = empty_univ_level_subst, empty_trunc_level_subst
let is_empty_level_subst (su,st) =
  is_empty_univ_level_subst su && is_empty_trunc_level_subst st

type sort_subst = universe_subst * truncation_subst
let pr_sort_subst (su,st) =
  Pp.(pr_universe_subst su ++ str "; " ++ pr_truncation_subst st)
let empty_sort_subst = empty_univ_subst, empty_trunc_subst
let is_empty_sort_subst (su,st) =
  is_empty_univ_subst su && is_empty_trunc_subst st

type level_subst_fn = universe_level_subst_fn * truncation_level_subst_fn
type sort_subst_fn = universe_subst_fn * truncation_subst_fn

let level_subst_fn_of (su,st) =
  Univ.univ_level_subst_of su, Trunc.trunc_level_subst_of st

let level_subst_fn (su,st) = subst_univs_level_level su, subst_truncs_level_level st
let sort_subst_fn (su,st) = make_univ_subst su, make_trunc_subst st

let level_subst_sorts (su,st) s =
  make (subst_univs_level_universe su s.univ) (subst_truncs_level_truncation st s.trunc)

let level_subst_sorts_fn (su, st) s =
  make (subst_univs_level_universe_fn su s.univ) (subst_truncs_level_truncation_fn st s.trunc)

let univ_level_subst_constraint subst (u,d,v) =
  let u' = subst_univs_level_level subst u in
  let v' = subst_univs_level_level subst v in
  if d != Lt && Level.equal u' v' then None
  else Some (u',d,v')

let trunc_level_subst_constraint subst (u,d,v) =
  let u' = subst_truncs_level_level subst u in
  let v' = subst_truncs_level_level subst v in
  if d != Lt && TLevel.equal u' v' then None
  else Some (u', d, v')

let level_subst_constraint subst = function
  | UnivConstraint c ->
     Option.map (fun c -> UnivConstraint c) (univ_level_subst_constraint (fst subst) c)
  | TruncConstraint c ->
     Option.map (fun c -> TruncConstraint c) (trunc_level_subst_constraint (snd subst) c)

let univ_level_subst_constraints subst cs =
  UConstraint.fold
    (fun c -> Option.fold_right UConstraint.add (univ_level_subst_constraint subst c))
  cs UConstraint.empty

let trunc_level_subst_constraints subst cs =
  TConstraint.fold
    (fun c -> Option.fold_right TConstraint.add (trunc_level_subst_constraint subst c))
  cs TConstraint.empty

let level_subst_constraints subst cs =
  Constraint.fold
    (fun c -> Option.fold_right Constraint.add (level_subst_constraint subst c))
  cs Constraint.empty

let subst_sorts (su,st) s =
  make (subst_univs_universe su s.univ) (subst_truncs_truncation st s.trunc)

let subst_catcher fn l =
  try Some (fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_catcher (fst fn) u in
  let v' = subst_catcher (fst fn) v in
  match u', v' with
  | None, None -> Constraint.add_univ c cstrs
  | Some u, None -> enforce_univ_constraint (u, d, Universe.make v) cstrs
  | None, Some v -> enforce_univ_constraint (Universe.make u, d, v) cstrs
  | Some u, Some v -> enforce_univ_constraint (u, d, v) cstrs

let subst_truncs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_catcher (snd fn) u in
  let v' = subst_catcher (snd fn) v in
  match u', v' with
  | None, None -> Constraint.add_trunc c cstrs
  | Some u, None -> enforce_trunc_constraint (u, d, Truncation.of_level v) cstrs
  | None, Some v -> enforce_trunc_constraint (Truncation.of_level u, d, v) cstrs
  | Some u, Some v -> enforce_trunc_constraint (u, d, v) cstrs

let subst_constraints fn cs =
  Constraint.fold
    (fun c cs ->
      match c with
      | UnivConstraint c -> subst_univs_constraint fn c cs
      | TruncConstraint c -> subst_truncs_constraint fn c cs)
  cs Constraint.empty

(** Instances. *)

module Instance = struct
  type raw = Level.t array * TLevel.t array
  type t = raw

  let empty = [| |], [| |]

  module HInstancestruct =
  struct
    type _t = t
    type t = _t
    type u = (Level.t -> Level.t) * (TLevel.t -> TLevel.t)

    let hashcons huniv (a,b) =
      let lena = Array.length a and lenb = Array.length b in
	if Int.equal lena 0 && Int.equal lenb 0 then empty
	else begin
	  for i = 0 to lena - 1 do
	    let x = Array.unsafe_get a i in
	    let x' = fst huniv x in
	      if x == x' then ()
	      else Array.unsafe_set a i x'
	  done;
          for i = 0 to lenb - 1 do
	    let x = Array.unsafe_get b i in
	    let x' = snd huniv x in
	      if x == x' then ()
	      else Array.unsafe_set b i x'
	  done;
	  a, b
	end

    let array_hequal t1 t2 =
      t1 == t2 ||
	(Int.equal (Array.length t1) (Array.length t2) &&
	   let rec aux i =
	     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	   in aux 0)

    let eq (at1,bt1) (at2,bt2) =
      array_hequal at1 at2 && array_hequal bt1 bt2

    let hash (a,b) =
      let accu = ref 0 in
	for i = 0 to Array.length a - 1 do
	  let l = Array.unsafe_get a i in
	  let h = Level.hash l in
	    accu := Hashset.Combine.combine !accu h;
	done;
	for i = 0 to Array.length b - 1 do
	  let l = Array.unsafe_get b i in
	  let h = TLevel.hash l in
	    accu := Hashset.Combine.combine !accu h;
	done;
	(* [h] must be positive. *)
	let h = !accu land 0x3FFFFFFF in
	  h
  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons (Level.hcons,TLevel.hcons)

  let hash = HInstancestruct.hash

  let share a = (hcons a, hash a)

  let empty = hcons ([| |], [| |])

  let is_empty (x,y) =
    Int.equal (Array.length x) 0 && Int.equal (Array.length y) 0

  let append (x1,x2) (y1,y2) =
    let a =
      if Array.length x1 = 0 then y1
      else if Array.length y1 = 0 then x1
      else Array.append x1 y1
    in
    let b =
      if Array.length x2 = 0 then y2
      else if Array.length y2 = 0 then x2
      else Array.append x2 y2
    in
    a, b

  let of_arrays (a,_ as i) : t =
    assert(Array.for_all (fun x -> not (Level.is_prop x)) a);
    i

  let to_arrays a = a

  let lengths (a,b) = Array.length a, Array.length b

  let to_sets (x,y) = USet.of_array x, TSet.of_array y

  let pr (fn1,fn2) (a1,a2) =
    let open Pp in
    prvect_with_sep spc fn1 a1 ++ str " ; " ++ prvect_with_sep spc fn2 a2

  let equal_one lev_eq t u =
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
        (CArray.for_all2 lev_eq t u
	(* Necessary as universe instances might come from different modules and
	   unmarshalling doesn't preserve sharing *))

  let equal (t1,t2) (u1,u2) =
    equal_one Level.equal t1 u1 && equal_one TLevel.equal t2 u2

  let make_univ_subst (instu, _) =
    Array.fold_left_i
      (fun i acc l ->
        UMap.add l (Level.var i) acc)
      UMap.empty instu

  let make_trunc_subst (_, instt) =
    Array.fold_left_i
      (fun i acc l ->
        TMap.add l (TLevel.var i) acc)
      TMap.empty instt

  let make_subst i =
    make_univ_subst i, make_trunc_subst i

  let make_univ_subst_fn (iu, _) l =
    match Level.var_index l with
    | None -> l
    | Some n -> iu.(n)

  let make_trunc_subst_fn (_, it) l =
    match TLevel.var_index l with
    | None -> l
    | Some n -> it.(n)

  let make_subst_fn i =
    make_univ_subst_fn i, make_trunc_subst_fn i

  let apply_subst (fn1,fn2) (t1,t2 as t) =
    let t1' = CArray.smartmap fn1 t1 in
    let t2' = CArray.smartmap fn2 t2 in
    if t1' == t1 && t2' == t2 then t else of_arrays (t1',t2')

end

type sort_instance = Instance.t

let subst_instance_instance s i = Instance.apply_subst (Instance.make_subst_fn s) i

let subst_instance_sort i s =
  let subst = Instance.make_subst_fn i in
  level_subst_sorts_fn subst s

let subst_instance_univ_constraint s (u,d,v as c) =
  let u' = Instance.make_univ_subst_fn s u in
  let v' = Instance.make_univ_subst_fn s v in
  if u' == u && v' == v then c
  else (u',d,v')

let subst_instance_trunc_constraint s (u,d,v as c) =
  let u' = Instance.make_trunc_subst_fn s u in
  let v' = Instance.make_trunc_subst_fn s v in
  if u' == u && v' == v then c
  else (u',d,v')

let subst_instance_constraints s cs =
  Constraint.fold
    (fun c cs ->
      match c with
      | UnivConstraint c -> Constraint.add_univ (subst_instance_univ_constraint s c) cs
      | TruncConstraint c -> Constraint.add_trunc (subst_instance_trunc_constraint s c) cs)
    cs Constraint.empty

let subst_instance_constraints =
  if Flags.profile then
    let key = Profile.declare_profile "subst_instance_constraints" in
      Profile.profile2 key subst_instance_constraints
  else subst_instance_constraints

let enforce_eq_instances (ax1,ax2) (ay1,ay2) c =
  begin
    if Array.length ax1 != Array.length ay1 || Array.length ax2 != Array.length ay2 then
      let open Pp in
      CErrors.anomaly
        (str "Invalid argument: enforce_eq_instances called with" ++
           str " instances of different lengths")
  end;
  c |> CArray.fold_right2 univ_enforce_eq_level ax1 ay1
  |> CArray.fold_right2 trunc_enforce_eq_level ax2 ay2

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
      raise (sort_univ_inconsistency (o, Universe.make u, Universe.make v,
                                    Option.map (List.map (fun (o, u) -> o, Universe.make u)) exp))
  end

  module UGraph = Graphgen.Make(UGraphIn)

  module TGraphIn = struct
    module Level = struct
      type t = TLevel.t
      let equal = TLevel.equal
      let is_litteral = TLevel.is_litteral
      let min = TLevel.hprop
      let var_min = TLevel.hset
      let is_min = TLevel.is_hprop
      let is_var_min = TLevel.is_hset
      let max = Some TLevel.hinf
      let is_max = TLevel.is_hinf

      let of_path = TLevel.of_path
      let to_string = TLevel.to_string
      let pr = TLevel.pr
    end
    module USet = Trunc.TSet
    module UMap = Trunc.TMap

    type level_constraint = trunc_constraint
    type constraints = Constraint.t
    let add_constraint = Constraint.add_trunc

    type explanation = (constraint_type * TLevel.t) list
    let error_inconsistency o u v exp =
      raise (sort_trunc_inconsistency
               (o, Truncation.of_level u, Truncation.of_level v,
                Option.map (List.map (fun (o, u) -> o, Truncation.of_level u)) exp))
  end

  module TGraph = Graphgen.Make(TGraphIn)

  type t = UGraph.t * TGraph.t

  let initial = UGraph.initial, TGraph.initial
  let is_initial (ug, tg) = UGraph.is_initial ug && TGraph.is_initial tg

  let sort (ug, tg) = UGraph.sort_universes ug, TGraph.sort_universes tg

  exception AlreadyDeclared = Graphgen.AlreadyDeclared
  let add_universe l b (ug, tg) = UGraph.add_level l b ug, tg
  let add_truncation l (ug, tg) = ug, TGraph.add_level l false tg

  let enforce_constraint c (ug, tg) =
    match c with
    | UnivConstraint c -> UGraph.enforce_constraint c ug, tg
    | TruncConstraint c -> ug, TGraph.enforce_constraint c tg

  let merge_constraints cs t =
    Constraint.fold enforce_constraint cs t

  let to_constraints (ug, tg) =
    Constraint.empty |> UGraph.constraints_of_universes ug
    |> TGraph.constraints_of_universes tg

  let check_univ_constraint (ug, tg) c = UGraph.check_constraint ug c
  let check_trunc_constraint (ug, tg) c = TGraph.check_constraint tg c

  let check_constraint t c =
    match c with
    | UnivConstraint c -> check_univ_constraint t c
    | TruncConstraint c -> check_trunc_constraint t c

  let check_constraints cs t =
    Constraint.for_all (check_constraint t) cs

  let pr (fn1, fn2) (ug, tg) =
    Pp.(UGraph.pr fn1 ug ++ str "\n;\n" ++ TGraph.pr fn2 tg)

  let dump out (ug, tg) =
    UGraph.dump_universes out ug;
    TGraph.dump_universes out tg

  type 'a check_function = t -> 'a -> 'a -> bool

  let check_eq_univ_level g u v = check_univ_constraint g (u, Eq, v)
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

  let check_eq_trunc_level g u v = check_trunc_constraint g (u, Eq, v)
  let check_leq_trunc_level g u v = check_trunc_constraint g (u, Le, v)

  let trunc_exists_bigger g ul l =
    Truncation.exists (fun ul' ->
        check_leq_trunc_level g ul ul') l

  let real_trunc_check_leq g u v =
    Truncation.for_all (fun ul -> trunc_exists_bigger g ul v) u

  let trunc_check_leq g u v =
    Truncation.leq u v
    || real_trunc_check_leq g u v

  let real_trunc_check_eq g u v =
    real_trunc_check_leq g u v && real_trunc_check_leq g v u

  let trunc_check_eq g u v =
    Truncation.equal u v || real_trunc_check_eq g u v
    
  let check_eq g s1 s2 =
    univ_check_eq g s1.univ s2.univ && trunc_check_eq g s1.trunc s2.trunc

  let check_leq g s1 s2 =
    univ_check_leq g s1.univ s2.univ && trunc_check_leq g s1.trunc s2.trunc

  let check_eq_instances_univ g t1 t2 =
    t1 == t2 ||
      (Int.equal (Array.length t1) (Array.length t2) &&
         let rec aux i =
           (Int.equal i (Array.length t1)) || (check_eq_univ_level g t1.(i) t2.(i) && aux (i + 1))
         in aux 0)

  let check_eq_instances_trunc g t1 t2 =
    t1 == t2 ||
      (Int.equal (Array.length t1) (Array.length t2) &&
         let rec aux i =
           (Int.equal i (Array.length t1)) || (check_eq_trunc_level g t1.(i) t2.(i) && aux (i + 1))
         in aux 0)

  let check_eq_instances g (a1, b1) (a2, b2) =
    check_eq_instances_univ g a1 a2 && check_eq_instances_trunc g b1 b2

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

  let sizes (us, _) = Instance.lengths us

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
  type t = (universe_set * truncation_set) constrained

  let empty : t = ((USet.empty, TSet.empty), Constraint.empty)
  let is_empty ((us, ts), cs) = USet.is_empty us && TSet.is_empty ts && Constraint.is_empty cs

  let of_sets (su, st) = (su, st), Constraint.empty
  let singleton lu lt = of_sets ((USet.singleton lu), (TSet.singleton lt))
  let of_instance i = of_sets (Instance.to_sets i)

  let equal ((us, ts), cs as x) ((us', ts'), cs' as y) =
    x == y || (USet.equal us us' && TSet.equal ts ts' && Constraint.equal cs cs')

  let union ((us, ts), cs as x) ((us', ts'), cs' as y) =
    if x == y then x
    else (USet.union us us', TSet.union ts ts'), Constraint.union cs cs'

  let append ((us, ts), cs) ((us', ts'), cs') =
    let us = USet.fold USet.add us us' in
    let ts = TSet.fold TSet.add ts ts' in
    let cs = Constraint.fold Constraint.add cs cs' in
    (us, ts), cs

  let diff ((us, ts), cs) ((us', ts'), cs') =
    (USet.diff us us', TSet.diff ts ts'),Constraint.diff cs cs'

  let add_universe u ((us, ts), cs) =
    (USet.add u us, ts), cs

  let add_truncation t ((us, ts), cs) =
    (us, TSet.add t ts), cs

  let add_constraints cs' (us, cs) =
    us, Constraint.union cs cs'

  let add_instance (instu, instt) ((us, ts), cs) =
    let us = Array.fold_left (fun us u -> USet.add u us) us instu in
    let ts = Array.fold_left (fun ts t -> TSet.add t ts) ts instt in
    (us, ts), cs

  let sort_levels a =
    Array.sort Level.natural_compare a; a
  let sort_tlevels a =
    Array.sort TLevel.compare a; a
  let to_context ((us, ts), cs) =
    let ua = sort_levels (Array.of_list (USet.elements us)) in
    let ta = sort_tlevels (Array.of_list (TSet.elements ts)) in
    Instance.of_arrays (ua, ta), cs

  let of_context (us, cs) =
    Instance.to_sets us, cs

  let constraints (_, cs) = cs
  let univ_levels ((us, _), cs) = us
  let trunc_levels ((_, ts), cs) = ts

  let hcons ((us, ts), cs) =
    (hcons_universe_set us, TSet.hcons ts), hcons_constraints cs

  let pr prl ((us, ts), cs as ctx) =
    if is_empty ctx then Pp.mt()
    else
      let open Pp in
      h 0 (USet.pr (prl_u prl) us ++ str "\n;\n" ++ TSet.pr (prl_t prl) ts ++ str " |= ") ++
        h 0 (v 0 (Constraint.pr prl cs))
end

type universe_context_set = ContextSet.t

type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

let abstract_sorts poly ctx =
  let instance = UContext.instance ctx in
  if poly
  then
    let subst = Instance.make_subst instance in
    let cs = level_subst_constraints subst (UContext.constraints ctx) in
    let ctx = UContext.make (instance, cs) in
    subst, ctx
  else
    empty_level_subst, ctx

(* ************** *)
let of_levels u t = make (Universe.make u) (Truncation.of_level t)
let univ_level s = Universe.level s.univ
let univ_levels s = Universe.levels s.univ
let univ_level_mem u s = univ_level_mem u s.univ

let trunc_level s = Truncation.level s.trunc
let trunc_levels s = Truncation.levels s.trunc
let trunc_level_mem t s = Truncation.level_mem t s.trunc

let pr s =
  let open Pp in
  Universe.pr s.univ ++ str"; " ++ Truncation.pr s.trunc

let pr_with prl s =
  let open Pp in
  Universe.pr_with (prl_u prl) s.univ ++ Truncation.pr_with (prl_t prl) s.trunc
