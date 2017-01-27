(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type Hashconsed =
  sig
    type t
    val hash : t -> int
    val eq : t -> t -> bool
    val hcons : t -> t
  end

module HashedList (M : Hashconsed) :
sig
  type t = private Nil | Cons of M.t * int * t
  val nil : t
  val cons : M.t -> t -> t
end =
  struct
    type t = Nil | Cons of M.t * int * t
    module Self =
      struct
        type _t = t
        type t = _t
        type u = (M.t -> M.t)
        let hash = function Nil -> 0 | Cons (_, h, _) -> h
        let eq l1 l2 = match l1, l2 with
          | Nil, Nil -> true
          | Cons (x1, _, l1), Cons (x2, _, l2) -> x1 == x2 && l1 == l2
          | _ -> false
        let hashcons hc = function
          | Nil -> Nil
          | Cons (x, h, l) -> Cons (hc x, h, l)
      end
    module Hcons = Hashcons.Make(Self)
    let hcons = Hashcons.simple_hcons Hcons.generate Hcons.hcons M.hcons
    (** No recursive call: the interface guarantees that all HLists from this
      program are already hashconsed. If we get some external HList, we can
      still reconstruct it by traversing it entirely. *)
    let nil = Nil
    let cons x l =
      let h = M.hash x in
      let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
      let h = Hashset.Combine.combine h hl in
      hcons (Cons (x, h, l))
  end

module type S = sig
  type elt
  type t = private Nil | Cons of elt * int * t
  val hash : t -> int
  val nil : t
  val cons : elt -> t -> t
  val tip : elt -> t
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val map : (elt -> elt) -> t -> t
  val smartmap : (elt -> elt) -> t -> t
  val exists : (elt -> bool) -> t -> bool
  val for_all : (elt -> bool) -> t -> bool
  val for_all2 : (elt -> elt -> bool) -> t -> t -> bool
  val mem : elt -> t -> bool
  val remove : elt -> t -> t
  val to_list : t -> elt list
  val compare : (elt -> elt -> int) -> t -> t -> int
end

module Make (H : Hashconsed) : S with type elt = H.t =
  struct
    type elt = H.t
    include HashedList(H)

    let hash = function Nil -> 0 | Cons (_, h, _) -> h

    let tip e = cons e nil
              
    let rec fold f l accu = match l with
      | Nil -> accu
      | Cons (x, _, l) -> fold f l (f x accu)

    let rec map f = function
      | Nil -> nil
      | Cons (x, _, l) -> cons (f x) (map f l)

    let smartmap = map
    (** Apriori hashconsing ensures that the map is equal to its argument *)

    let rec exists f = function
      | Nil -> false
      | Cons (x, _, l) -> f x || exists f l

    let rec for_all f = function
      | Nil -> true
      | Cons (x, _, l) -> f x && for_all f l

    let rec for_all2 f l1 l2 = match l1, l2 with
      | Nil, Nil -> true
      | Cons (x1, _, l1), Cons (x2, _, l2) -> f x1 x2 && for_all2 f l1 l2
      | _ -> false

    let rec to_list = function
      | Nil -> []
      | Cons (x, _, l) -> x :: to_list l

    let rec remove x = function
      | Nil -> nil
      | Cons (y, _, l) ->
         if H.eq x y then l
         else cons y (remove x l)

    let rec mem x = function
      | Nil -> false
      | Cons (y, _, l) -> H.eq x y || mem x l

    let rec compare cmp l1 l2 = match l1, l2 with
      | Nil, Nil -> 0
      | Cons (x1, h1, l1), Cons (x2, h2, l2) ->
         let c = Int.compare h1 h2 in
         if c == 0 then
           let c = cmp x1 x2 in
           if c == 0 then
             compare cmp l1 l2
           else c
         else c
      | Cons _, Nil -> 1
      | Nil, Cons _ -> -1

  end
