(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names

module TLevel =
  struct
    module Raw = struct
      type t =
        | HProp
        | HSet
        | HInf
        | Level of int * DirPath.t
        | Var of int (* De Bruijn index *)

      let compare a b =
        match a, b with
        | HProp, HProp -> 0
        | HProp, _ -> -1
        | _, HProp -> 1
        | HSet, HSet -> 0
        | HSet, _ -> -1
        | _, HSet -> 1
        | Level (i1, dp1), Level (i2, dp2) ->
           if i1 < i2 then -1
           else if i1 > i2 then 1
           else DirPath.compare dp1 dp2
        | Level _, _ -> -1
        | _, Level _ -> 1
        | Var n, Var m ->
           Int.compare n m
        | Var _, _ -> -1
        | _, Var _ -> 1
        | HInf, HInf -> 0

      let equal a b =
        match a, b with
        | HProp, HProp | HSet, HSet | HInf, HInf -> true
        | Level (n, d), Level (n', d') -> n == n' && d == d'
        | Var n, Var m -> n == m
        | _ -> false

      let hcons = function
        | HProp -> HProp
        | HSet -> HSet
        | HInf -> HInf
        | Level (n, d) as x ->
           let d' = DirPath.hcons d in
           if d' == d then x else Level (n, d')
        | Var _ as x -> x

      let hash =
        let open Hashset.Combine in
        function
        | HProp -> combinesmall 1 0
        | HSet -> combinesmall 1 1
        | HInf -> combinesmall 1 2
        | Var n -> combinesmall 2 n
        | Level (n, d) -> combinesmall 3 (combine n (DirPath.hash d))
    end

    type t = {
        hash : int;
        data : Raw.t }

    module Self = struct
      type self = t
      type t = self
      type u = unit
      let eq x y = x.hash == y.hash && Raw.equal x.data y.data
      let hash x = x.hash
      let hashcons () x =
        let data' = Raw.hcons x.data in
        if x.data == data' then x else { x with data = data' }
    end

    let hcons : t -> t =
      let module H = Hashcons.Make(Self) in
      Hashcons.simple_hcons H.generate H.hcons ()

    let make l = hcons { hash = Raw.hash l; data = l }

    let hash x = x.hash

    let equal (x:t) y = x == y

    (* For hashconsing *)
    let eq = equal

    let compare u v =
      if u == v then 0
      else
        let c = Int.compare u.hash v.hash in
        if c == 0 then Raw.compare u.data v.data
        else c

    let hprop = make Raw.HProp
    let hset = make Raw.HSet
    let hinf = make Raw.HInf

    let is_hprop x = equal hprop x
    let is_hset x = equal hset x
    let is_hinf x = equal hinf x
    let is_litteral x = is_hprop x || is_hset x || is_hinf x

    (* FIXME not sure about this... *)
    let leq x y =
      equal x y || is_hprop x || (is_hset x && not (is_hprop y)) || is_hinf y

    let apart x y =
      is_litteral x && is_litteral y && not (equal x y)

    let of_path d i = make (Raw.Level (i, DirPath.hcons d))

    let var i = make (Raw.Var i)

    let var_index u =
      match u.data with
      | Raw.Var i -> Some i
      | _ -> None

    let to_string x =
      match x.data with
      | Raw.HProp -> "HProp"
      | Raw.HSet -> "HSet"
      | Raw.HInf -> "HInf"
      | Raw.Level (n, d) -> DirPath.to_string d ^ "." ^ string_of_int n
      | Raw.Var i -> "Var(" ^ string_of_int i ^ ")"

    let pr u = str (to_string u)
  end

type truncation_level = TLevel.t

module TMap =
  struct
    module M = HMap.Make (TLevel)
    include M

    let union l r =
      merge (fun k l r ->
          match l, r with
          | Some _, _ -> l
          | _, _ -> r) l r

    let subst_union l r =
      merge (fun k l r ->
          match l, r with
          | Some (Some _), _ -> l
          | Some None, None -> l
          | _, _ -> r) l r

    let diff ext orig =
      fold (fun u v acc ->
          if mem u orig then acc
          else add u v acc)
           ext empty

    let pr f m =
      h 0 (prlist_with_sep fnl (fun (u, v) ->
                             TLevel.pr u ++ f v) (bindings m))
  end

type 'a truncation_map = 'a TMap.t

module TSet =
  struct
    include TMap.Set

    module Hset =
      Hashcons.Make(
          struct
            type t = TMap.Set.t
            type u = TLevel.t -> TLevel.t
            let hashcons huc s =
	      fold (fun x -> add (huc x)) s empty
            let eq s s' =
	      equal s s'
            let hash = Hashtbl.hash
          end)

    let hcons =
      Hashcons.simple_hcons Hset.generate Hset.hcons TLevel.hcons

    let pr prl s =
      str"{" ++ prlist_with_sep spc prl (elements s) ++ str"}"

    let of_array l =
      Array.fold_left (fun acc x -> add x acc) empty l
  end

type truncation_set = TSet.t

module Truncation =
  struct
    module M = Hashlist.Make(TLevel)
    type t = M.t
    open M

    let equal (x : t) (y : t) = x == y

    let hash : t -> int = M.hash
    let rec hcons = function
      | Nil -> nil
      | Cons (x, _, l) -> cons x (hcons l)

    let compare x y =
      if x == y then 0
      else
        let hx = hash x and hy = hash y in
        let c = Int.compare hx hy in
        if c == 0 then
          M.compare TLevel.compare x y
        else c

    let of_level (l : TLevel.t) : t = M.tip l

    let pr x =
      match x with
      | Cons (u, _, Nil) -> TLevel.pr u
      | _ ->
         str "max(" ++ hov 0
                           (prlist_with_sep pr_comma TLevel.pr (to_list x)) ++
           str")"

    let pr_with f x =
      match x with
      | Cons (u, _, Nil) -> f u
      | _ ->
         str "max(" ++ hov 0
                           (prlist_with_sep pr_comma f (to_list x)) ++
           str")"

    let is_level = function
      | Cons (l, _, Nil) -> true
      | _ -> false

    let level = function
      | Cons (l, _, Nil) -> Some l
      | _ -> None

    let levels x =
      M.fold TSet.add x TSet.empty

    let level_mem = M.mem

    let level_rem u v min =
      match level v with
      | Some u' -> if TLevel.equal u u' then min else v
      | None -> remove u v

    let hprop = of_level TLevel.hprop
    let hset = of_level TLevel.hset
    let hinf = of_level TLevel.hinf

    let is_hprop x = equal hprop x
    let is_hset x = equal hset x
    let is_hinf x = equal hinf x

    let super _ = hinf

    (* Add l to x which does not contain hset/hinf, keeping it sorted w.r.t. TLevel.compare *)
    let rec add_level_name l x =
      match x with
      | Nil -> of_level l
      | Cons (l', _, x') ->
         let c = TLevel.compare l l' in
         if c == 0 then x
         else if c < 0 then cons l x
         else cons l' (add_level_name l x')

    let add_level l x =
      if TLevel.is_hprop l then x
      else if TLevel.is_hinf l || is_hinf x then hinf
      else if is_hprop x then of_level l
      else add_level_name l x

    let sort x =
      fold add_level x nil

    let sup x y =
      fold add_level x y

    let fold = M.fold

    let exists = M.exists
    let for_all = M.for_all

    let smartmap = M.smartmap
  end

type truncation = Truncation.t

(** Substitution *)

type truncation_level_subst = TLevel.t truncation_map

type truncation_subst = truncation truncation_map

let trunc_level_subst_of f =
  fun l ->
  try let u = f l in
      match Truncation.level u with
      | None -> l
      | Some l -> l
  with Not_found -> l

let empty_trunc_subst = TMap.empty
let is_empty_trunc_subst = TMap.is_empty

let empty_trunc_level_subst = TMap.empty
let is_empty_trunc_level_subst = TMap.is_empty

let subst_truncs_level_level subst l =
  try TMap.find l subst
  with Not_found -> l

let subst_truncs_level_truncation subst u =
  let u' = Truncation.smartmap (subst_truncs_level_level subst) u in
  if u == u' then u
  else Truncation.sort u'

let subst_truncs_level_truncation_fn subst u =
  let u' = Truncation.smartmap subst u in
  if u == u' then u
  else Truncation.sort u'

type truncation_level_subst_fn = TLevel.t -> TLevel.t
type truncation_subst_fn = truncation_level -> truncation

let make_trunc_subst subst = fun l -> TMap.find l subst

let subst_truncs_truncation fn ul =
  let subst, nosubst =
    Truncation.fold (fun u (subst, nosubst) ->
        try let a' = fn u in
            (a' :: subst, nosubst)
        with Not_found -> (subst, u :: nosubst))
                    ul ([], [])
  in
  if CList.is_empty subst then ul
  else
    let substs = List.fold_left Truncation.sup Truncation.M.nil subst in
    List.fold_left (fun acc u -> Truncation.add_level u acc) substs nosubst

(** Printing *)
let pr_truncation_subst =
  TMap.pr (fun u -> str" := " ++ Truncation.pr u ++ spc ())

let pr_truncation_level_subst =
  TMap.pr (fun u -> str" := " ++ TLevel.pr u ++ spc ())
