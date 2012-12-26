(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Term
open Univ
open Environ
open Mini_evd

(* With smaller hashtables it slows down. Reset costs a lot: 0.0072 *)
let uf_table_size = 100003

module Hclosure : sig

  type closure

  type ctx
  type subs
  type hconstr = Term.H.hconstr

  type dummy (* like unit, no content *)

  type kind_of_ctx =
    | Znil
    | Zapp    of dummy * closure array * ctx
              (* Zapp (_,a,_) is just the zipper for an App's head *)
    | Zcase   of dummy * case_info * closure * closure array * ctx
              (* Zcase (_,ci,p,br,_) is just the zipper for a Case's head *)
    | Zfix    of dummy * closure * ctx
              (* Zfix (_,(_,_,_,c as cl),_) cl is the fix and its params
                 are already prepared in the context c, morally to be
                 prepended to the recarg and the actual term context *)
    | Zupdate of dummy * closure array * int * ctx
              (* Zupdate (_,a,i,_) means that the whnf of the term must
                 be stored in a.(i) *)
    | Zshift  of dummy * int * ctx
              (* Zshift (_,s,_) means that the term should be lifted by s *)

  type kind_of_subs =
    | Eid    of int
              (* Eid n is the identity subst of length n *)
    | Econs  of dummy * closure array * subs
              (* Econs (_,ca,_) represents Array.length ca assignements *)
    | Eshift of dummy * int * subs
              (* Eshift (_,n,_) lefts free Debruijn indexes of n *)
    | Elift  of dummy * int * subs
              (* Elift (_,n,_) moves the subst under n lambdas *)

  module Ctx : sig
    val nil : ctx
    val app : closure array -> ctx -> ctx
    val case : case_info -> closure -> closure array -> ctx -> ctx
    val fix : closure -> ctx -> ctx
    val update : closure array -> int -> ctx -> ctx
    val shift : int -> ctx -> ctx
    val kind_of : ctx -> kind_of_ctx
    val append : ctx -> ctx -> ctx
    val equal : ctx -> ctx -> bool
  end
  module Subs : sig
    val id : int -> subs
    val cons : closure array -> subs -> subs
    val shift : int -> subs -> subs
    val lift : int -> subs -> subs
    val kind_of : subs -> kind_of_subs
    val equal : subs -> subs -> bool
  end
  module Clos : sig
    val mk : ?subs:subs -> ?ctx:ctx -> hconstr -> closure
    val kind_of : closure -> dummy * subs * hconstr * ctx
    val pp : int -> closure -> Pp.std_ppcmds
    module H : sig
      type hclosure
      val equal : hclosure -> hclosure -> bool
      val hash : hclosure -> int
      val compare : hclosure -> hclosure -> int
      val reset : unit -> unit
      val distribution : unit -> (hclosure * int) list list
      val intern : closure -> hclosure
      val extern : hclosure -> closure
      val kind_of : hclosure -> dummy * subs * hconstr * ctx
      val pp : int -> hclosure -> Pp.std_ppcmds
    end
  end

  module type HashtblEx = sig
    include Hashtbl.S with type key = Clos.H.hclosure
    val reset : int -> 'a t -> unit
  end
  module Table : HashtblEx

end = struct (* {{{ *)

  type hconstr = Term.H.hconstr

  type hash = int
  type dummy = hash

  type ctx =
    | Znil
    | Zapp    of hash * closure array * ctx
    | Zcase   of hash * case_info * closure * closure array * ctx
    | Zfix    of hash * closure * ctx
    | Zupdate of hash * closure array * int * ctx
    | Zshift  of hash * int * ctx
  and subs =
    | Eid    of int
    | Econs  of hash * closure array * subs
    | Eshift of hash * int * subs
    | Elift  of hash * int * subs
  and closure = hash * subs * hconstr * ctx

  open Pp
  let rec ps m s =
    if s = Eid 0 then str"-" else
    let rec tol s = match s with
    | Eshift (_,n,s) -> `Shift n :: tol s
    | Eid 0 -> []
    | Eid n -> [`Id n]
    | Econs (_,cv,s) -> `Cons cv :: tol s
    | Elift (_,n,s) -> `Lift n :: tol s in
    str"{" ++ hv 0 (prlist_with_sep (fun () -> str";"++cut()) (function
    | `Shift n -> str "S " ++ int n
    | `Id n -> str"I " ++ int n
    | `Lift n -> str"L " ++ int n
    | `Cons v -> str"C " ++ pclv m v) (tol s)) ++ str"}"
  and pclv m cv =
    let s_of_cl cl = let _,s,_,_ = cl in s in
    let s = s_of_cl cv.(0) in
    if Array.for_all (fun cl -> s_of_cl cl == s) cv && m > 0
    && Array.length cv > 1 then
      let pcl m cl =
        let _,s,t,c = cl in
        pcl m (0,Eid 0,t,c) in
      str"/" ++ ps m s ++ str"/ on"++ spc() ++prvect_with_sep spc (pcl m) cv
    else prvect_with_sep spc (pcl m) cv
  and pc m c =
    if c = Znil then str"-" else
    let rec tol c = match c with
    | Znil -> []
    | Zapp (_,a,c) -> `App a :: tol c
    | Zfix (_,f,c) -> `Fix f :: tol c
    | Zcase (_,ci,t,br,c) -> `Case (t,br) :: tol c
    | Zupdate (_,_,i,c) -> `Up i :: tol c
    | Zshift  (_,s,c) -> `Shift s :: tol c in
    str"[" ++ hv 0 (prlist_with_sep (fun () -> str";"++cut()) (function
      | `App cv -> str"A " ++ pclv m cv
      | `Fix c -> str"F " ++ pcl m c
      | `Up i -> str"#" ++ int i
      | `Shift s -> str"^" ++ int s
      | `Case (p,br) -> str"M " ++ pcl m p ++ prvect_with_sep spc (pcl m) br)
      (tol c)) ++ str"]"
  and pcl m cl = if m = 0 then str"…" else let m = m-1 in
   let _,s,t,c = cl in
   if s = Eid 0 && c = Znil then
     hv 1 (str"(; " ++ Term.H.ll_pr_hconstr m [] t ++ str" ;)")
   else
     hv 1 (str"(" ++ ps m s ++ str";" ++ spc() ++
                  Term.H.ll_pr_hconstr m [] t ++ str";" ++ spc() ++
                  pc m c ++
        str")")

  type kind_of_ctx = ctx =
    | Znil
    | Zapp    of hash * closure array * ctx
    | Zcase   of hash * case_info * closure * closure array * ctx
    | Zfix    of hash * closure * ctx
    | Zupdate of hash * closure array * int * ctx
    | Zshift  of hash * int * ctx
  type kind_of_subs = subs =
    | Eid    of int
    | Econs  of hash * closure array * subs
    | Eshift of hash * int * subs
    | Elift  of hash * int * subs

  let array_peq t1 t2 = t1 == t2 || Util.Array.for_all2 (==) t1 t2

  let rec equal_ctx c1 c2 = c1 == c2 || match c1, c2 with
    | Znil, Znil -> true
    | Zapp (_,a1,c1), Zapp (_,a2,c2) -> array_peq a1 a2 && equal_ctx c1 c2
    | Zcase (_,_,t1,a1,c1), Zcase (_,_,t2,a2,c2) ->
        t1 == t2 && array_peq a1 a2 && equal_ctx c1 c2
    | Zfix (_,f1,c1), Zfix (_,f2,c2) -> f1 == f2 && equal_ctx c1 c2
    | Zupdate (_,_,_,c1), _ -> equal_ctx c1 c2
    | _, Zupdate (_,_,_,c2) -> equal_ctx c1 c2
    | Zshift (_,n,c1), Zshift (_,m,c2) -> n = m && equal_ctx c1 c2
    | _ -> false
  let rec equal_subs s1 s2 = s1 == s2 || match s1, s2 with
    | Eid n, Eid m -> n = m
    | Econs (h1,a1,s1), Econs (h2,a2,s2) ->
        h1 = h2 && array_peq a1 a2 && equal_subs s1 s2
    | Eshift (h1,n,s1), Eshift (h2,m,s2)
    | Elift (h1,n,s1), Elift (h2,m,s2) -> h1 = h2 && n = m && equal_subs s1 s2
    | _ -> false
  let equal_closure (_,s1,t1,c1) (_,s2,t2,c2) =
    Term.H.equal t1 t2 && equal_subs s1 s2 && equal_ctx c1 c2

  module HashsetClos = struct

    type elt = closure

    type bucketlist = Empty | Cons of elt * int * bucketlist

    type t = {
      mutable size : int;
      mutable data : bucketlist array; }

    let create s =
      let s = min (max 1 s) Sys.max_array_length in
      { size = 0; data = Array.make s Empty }

    let reset s t =
      let t' = create s in t.size <- t'.size; t.data <- t'.data

    let resize table =
      let odata = table.data in
      let osize = Array.length odata in
      let nsize = min (2 * osize + 1) Sys.max_array_length in
      if nsize <> osize then begin
        let ndata = Array.create nsize Empty in
        let rec insert_bucket = function
        | Empty -> ()
        | Cons (key, hash, rest) ->
            let nidx = abs hash mod nsize in
            let obucket = ndata.(nidx) in
            ndata.(nidx) <- Cons (key, hash, obucket);
            insert_bucket rest
        in
        for i = 0 to osize - 1 do insert_bucket odata.(i) done;
        table.data <- ndata
      end

    let add hash key table =
      let odata = table.data in
      let osize = Array.length odata in
      let i = abs hash mod osize in
      odata.(i) <- Cons (key, hash, odata.(i));
      table.size <- table.size + 1;
      if table.size > osize lsl 1 then resize table

    let find_rec hash key table bucket =
      let rec aux = function
        | Empty ->
          add hash key table; key
        | Cons (k, h, rest) ->
          if hash == h && equal_closure key k then k else aux rest
      in
      aux bucket

    let repr hash key table =
      let odata = table.data in
      let osize = Array.length odata in
      let i = abs hash mod osize in
      match odata.(i) with
        | Empty -> add hash key table; key
        | Cons (k1, h1, rest1) ->
          if hash == h1 && equal_closure key k1 then k1 else
            match rest1 with
              | Empty -> add hash key table; key
              | Cons (k2, h2, rest2) ->
                if hash == h2 && equal_closure key k2 then k2 else
                  match rest2 with
                    | Empty -> add hash key table; key
                    | Cons (k3, h3, rest3) ->
                      if hash == h2 && equal_closure key k3 then k3
                      else find_rec hash key table rest3

    let distribution table =
      let rec tol = function Empty -> [] | Cons (v,h,l) -> (v,h)::tol l in
      List.fold_left (fun acc -> function
        | Empty -> acc
        | Cons _ as l -> tol l :: acc)
      [] (Array.to_list table.data)
  end

  let clos_table = HashsetClos.create uf_table_size
  let reset () = HashsetClos.reset uf_table_size clos_table

  let no_hash = 0

  let alpha = 65599
  let beta  = 7
  let combine x y     = x * alpha + y
  let combine3 x y z   = combine x (combine y z)
  let combine4 x y z t = combine x (combine3 y z t)
  let combinesmall x y =
    let h = beta * x + y in
    if h = no_hash then no_hash + 1 else h

  let intern_closure =
    let rec hash_closure (h,s,t,c) =
      assert (h = no_hash );
      let s, h1 = hash_subs s in
      let    h2 = Term.H.hash t in
      let c, h3 = hash_ctx c in
      let h = combinesmall 24 (combine3 h1 h2 h3) in
      assert (h <> no_hash );
      h,s,t,c
    and hash_array a =
      assert(Array.length a > 0);
      let _, s0, _,_ as a0 = a.(0) in
      let (_, s0', _,_ as a0'), h = sh_rec a0 in
      let accu = ref (combine 0 h) in
      if a0' != a0 then a.(0) <- a0';
      for i = 1 to Array.length a - 1 do
        let hi, si, ti, ci as ai = a.(i) in
        let ai', hi =
          if si == s0 && hi = no_hash then sh_rec (hi,s0',ti,ci)
          else sh_rec ai in
        accu := combine !accu hi;
        if ai' != ai then a.(i) <- ai';
      done;
      !accu
    and hash_subs = function
    | Eid n as orig -> orig, n
    | Econs (h,a,s) as orig -> if h <> no_hash then orig, h else
       let h1 = hash_array a in
       let s, h2 = hash_subs s in
       let h = combinesmall 21 (combine h1 h2) in
       Econs (h,a,s), h
    | Eshift (h,n,s) as orig -> if h <> no_hash then orig, h else
       let s, h2 = hash_subs s in
       let h = combinesmall 22 (combine n h2) in
       Eshift (h,n,s), h
    | Elift (h,n,s) as orig -> if h <> no_hash then orig, h else
       let s, h2 = hash_subs s in
       let h = combinesmall 23 (combine n h2) in
       Elift (h,n,s), h
    and hash_ctx = function
    | Znil as orig -> orig, 0
    | Zapp (h,a,c) as orig -> if h <> no_hash then orig, h else
       let h1 = hash_array a in
       let c, h2 = hash_ctx c in
       let h = combinesmall 17 (combine h1 h2) in
       Zapp (h,a,c), h
    | Zcase (h,ci,m,p,c) as orig -> if h <> no_hash then orig, h else
       let m, h1 = sh_rec m in
       let h2 = if Array.length p > 0 then hash_array p else 0 in
       let c, h3 = hash_ctx c in
       let h = combinesmall 18 (combine3 h1 h2 h3) in
       Zcase (h,ci,m,p,c), h
    | Zfix (h,m,c) as orig -> if h <> no_hash then orig, h else
       let m, h1 = sh_rec m in
       let c, h2 = hash_ctx c in
       let h = combinesmall 19 (combine h1 h2) in
       Zfix (h,m,c), h
    | Zupdate (h,a,i,c) as orig -> if h <> no_hash then orig, h else
       let c, h = hash_ctx c in
       Zupdate (h,a,i,c), h
    | Zshift (h,s,c) as orig -> if h <> no_hash then orig, h else
       let c, h1 = hash_ctx c in
       let h = combinesmall 20 (combine s h1) in
       Zshift (h,s,c), h
    and sh_rec (h,_,_,_ as cl) =
      if h <> no_hash then cl, h
      else
        let h, _,_,_ as cl = hash_closure cl in
        HashsetClos.repr h cl clos_table, h
    in
     (fun cl -> fst (sh_rec cl))

  module Ctx = struct
  let nil = Znil
  let app a c = Zapp (no_hash,a,c)
  let case ci m p c = Zcase (no_hash,ci,m,p,c)
  let fix m c = Zfix (no_hash,m,c)
  let update a i c = Zupdate (no_hash,a,i,c)
  let shift s c =
    if s = 0 then c
    else match c with
    | Zshift (_,n,c) -> Zshift (no_hash, s+n,c)
    | _ -> Zshift(no_hash,s,c)
  let kind_of c = c
  let rec append c1 c2 = match c1 with
    | Znil -> c2
    | Zapp (_,a,c) -> app a (append c c2)
    | Zcase (_,ci,m,p,c) -> case ci m p (append c c2)
    | Zfix (_,m,c) -> fix m (append c c2)
    | Zupdate (_,a,i,c) -> update a i (append c c2)
    | Zshift (_,s,c) -> shift s (append c c2)
  let equal = equal_ctx
  end

  module Subs = struct
  let id n = Eid n
  let cons a s = Econs (no_hash,a,s)
  let shift n s =
    if n = 0 then s
    else match s with
    | Eshift (_,m,s) -> Eshift (no_hash,n + m,s)
    | _ -> Eshift (no_hash,n,s)
  let lift n s =
    if n = 0 then s
    else match s with
    | Elift (_,m,s) -> Elift (no_hash,n + m,s)
    | _ -> Elift(no_hash,n,s)
  let kind_of s = s
  let equal = equal_subs
  end

  module Clos = struct
  let empty_subs = Subs.id 0
  let empty_ctx = Ctx.nil
  let mk ?(subs=empty_subs) ?(ctx=empty_ctx) t = no_hash, subs, t ,ctx
  let kind_of c = c
  let pp m c = pcl m c
  module H = struct
  type hclosure = closure
  let intern = intern_closure
  let extern c = c
  let pp m c = pcl m (extern c)
  let kind_of c = c
  let hash (h,_,_,_) = h
  let equal c1 c2 = c1 == c2
  let compare c1 c2 =
    if equal c1 c2 then 0
    else
      let diff = hash c1 - hash c2 in
      if diff = 0 then Pervasives.compare c1 c2 else diff

  let reset = reset
  let distribution () = HashsetClos.distribution clos_table
  end
  end

  module type HashtblEx = sig
    include Hashtbl.S with type key = Clos.H.hclosure
    val reset : int -> 'a t -> unit
  end

  module Table : HashtblEx = struct
    type key = Clos.H.hclosure
    type 'a t =
      { mutable size: int;
        mutable data: 'a bucketlist array }
    and 'a bucketlist =
        Empty
      | Cons of key * 'a * 'a bucketlist

    let create initial_size =
      let s = min (max 1 initial_size) Sys.max_array_length in
      { size = 0; data = Array.make s Empty }

    let clear h =
      for i = 0 to Array.length h.data - 1 do
        h.data.(i) <- Empty
      done;
      h.size <- 0

    let reset s h =
      let h' = create s in
      h.size <- h'.size; h.data <- h'.data

    let copy h =
      { size = h.size;
        data = Array.copy h.data }

    let resize hashfun tbl =
      let odata = tbl.data in
      let osize = Array.length odata in
      let nsize = min (2 * osize + 1) Sys.max_array_length in
      if nsize <> osize then begin
        let ndata = Array.create nsize Empty in
        let rec insert_bucket = function
            Empty -> ()
          | Cons(key, data, rest) ->
              insert_bucket rest; (* preserve original order of elements *)
              let nidx = (hashfun key) mod nsize in
              ndata.(nidx) <- Cons(key, data, ndata.(nidx)) in
        for i = 0 to osize - 1 do
          insert_bucket odata.(i)
        done;
        tbl.data <- ndata;
      end

    let length h = h.size

    let safehash key = (Clos.H.hash key) land max_int

    let add h key info =
      let i = (safehash key) mod (Array.length h.data) in
      let bucket = Cons(key, info, h.data.(i)) in
      h.data.(i) <- bucket;
      h.size <- succ h.size;
      if h.size > Array.length h.data lsl 1 then resize safehash h

    let remove h key =
      let rec remove_bucket = function
          Empty ->
            Empty
        | Cons(k, i, next) ->
            if Clos.H.equal k key
            then begin h.size <- pred h.size; next end
            else Cons(k, i, remove_bucket next) in
      let i = (safehash key) mod (Array.length h.data) in
      h.data.(i) <- remove_bucket h.data.(i)

    let rec find_rec key = function
        Empty ->
          raise Not_found
      | Cons(k, d, rest) ->
          if Clos.H.equal key k then d else find_rec key rest

    let find h key =
      match h.data.((safehash key) mod (Array.length h.data)) with
        Empty -> raise Not_found
      | Cons(k1, d1, rest1) ->
          if Clos.H.equal key k1 then d1 else
          match rest1 with
            Empty -> raise Not_found
          | Cons(k2, d2, rest2) ->
              if Clos.H.equal key k2 then d2 else
              match rest2 with
                Empty -> raise Not_found
              | Cons(k3, d3, rest3) ->
                  if Clos.H.equal key k3 then d3 else find_rec key rest3

    let find_all h key =
      let rec find_in_bucket = function
        Empty ->
          []
      | Cons(k, d, rest) ->
          if Clos.H.equal k key
          then d :: find_in_bucket rest
          else find_in_bucket rest in
      find_in_bucket h.data.((safehash key) mod (Array.length h.data))

    let replace h key info =
      let rec replace_bucket = function
          Empty ->
            raise Not_found
        | Cons(k, i, next) ->
            if Clos.H.equal k key
            then Cons(k, info, next)
            else Cons(k, i, replace_bucket next) in
      let i = (safehash key) mod (Array.length h.data) in
      let l = h.data.(i) in
      try
        h.data.(i) <- replace_bucket l
      with Not_found ->
        h.data.(i) <- Cons(key, info, l);
        h.size <- succ h.size;
        if h.size > Array.length h.data lsl 1 then resize safehash h

    let mem h key =
      let rec mem_in_bucket = function
      | Empty ->
          false
      | Cons(k, d, rest) ->
          Clos.H.equal k key || mem_in_bucket rest in
      mem_in_bucket h.data.((safehash key) mod (Array.length h.data))

    let iter f h =
      let rec do_bucket = function
          Empty ->
            ()
        | Cons(k, d, rest) ->
            f k d; do_bucket rest in
      let d = h.data in
      for i = 0 to Array.length d - 1 do
        do_bucket d.(i)
      done

    let fold f h init =
      let rec do_bucket b accu =
        match b with
          Empty ->
            accu
        | Cons(k, d, rest) ->
            do_bucket rest (f k d accu) in
      let d = h.data in
      let accu = ref init in
      for i = 0 to Array.length d - 1 do
        accu := do_bucket d.(i) !accu
      done;
      !accu

  end

end (* }}} *)

module UF : sig

  open Hclosure.Clos.H

  val find : hclosure -> hclosure
  val union : hclosure -> hclosure -> unit
  val partition : hclosure -> hclosure -> unit
  val same : hclosure -> hclosure -> [`Yes | `No | `Maybe]
  val reset : unit -> unit

end = struct (* {{{ *)

  open Hclosure
  module HT = Hclosure.Table

  let rank : int HT.t = HT.create uf_table_size
  let father : Clos.H.hclosure HT.t = HT.create uf_table_size

  let father_of t =
    try HT.find father t with Not_found -> HT.replace father t t; t

  let rank_of rx = try HT.find rank rx with Not_found -> 0

  let rec find i =
    let fi = father_of i in
    if Clos.H.equal fi i then i
    else
      let ri = find fi in
      HT.replace father i ri;
      ri

  module UFCset = Set.Make(struct
    type t = Clos.H.hclosure
    let compare x y =
      let rx = find x in
      let ry = find y in
      Clos.H.compare rx ry
  end)

  let partitions : UFCset.t HT.t = HT.create uf_table_size

  let diff_of rx = try HT.find partitions rx with Not_found -> UFCset.empty

  let partition x y =
    let rx = find x in
    let ry = find y in
    assert(Clos.H.equal rx ry = false);
    HT.replace partitions rx (UFCset.add ry (diff_of rx));
    HT.replace partitions ry (UFCset.add rx (diff_of ry))

  let same x y =
    let rx = find x in
    let ry = find y in
    if Clos.H.equal rx ry then `Yes
    else if UFCset.mem rx (diff_of ry) then `No (* XXX HUMMMMM is it complete?*)
    else `Maybe

  let reset () =
    HT.reset uf_table_size rank;
    HT.reset uf_table_size father;
    HT.reset uf_table_size partitions

  let union x y =
    let rx = find x in
    let ry = find y in
    if not (Clos.H.equal rx ry) then begin
      let rkx = rank_of x in
      let rky = rank_of y in
      if rkx > rky then begin
        HT.replace father ry rx;
        HT.replace partitions rx (UFCset.union (diff_of rx) (diff_of ry));
      end else if rkx < rky then begin
        HT.replace father rx ry;
        HT.replace partitions ry (UFCset.union (diff_of rx) (diff_of ry));
      end else begin
        HT.replace rank rx (rkx + 1);
        HT.replace father ry rx;
        HT.replace partitions rx (UFCset.union (diff_of rx) (diff_of ry));
      end
    end

end (* }}} *)

open Hclosure
open Term.H

(* This gives the meaning to an explicit substitution. Output:
   - `Var is bound by the subst to a Rel
   - `InEnv escapes the subst
   - `Code is assigned by the subst *)
let expand_rel k s =
  let rec aux_rel liftno k s = match Subs.kind_of s with
    | Econs (_,def,s) when k > Array.length def ->
        aux_rel liftno (k - Array.length def) s
    | Econs (_,def,_) ->
        let def_len = Array.length def in
        let idx = def_len - k in
        `Code(liftno, def.(idx), def, idx)
    | Elift (_,n,s) when k > n -> aux_rel (liftno + n) (k - n) s
    | Elift (_,n,_) -> `Var (liftno + k)
    | Eshift (_,n,s) -> aux_rel (liftno + n) k s
    | Eid n when k > n -> `InEnv(liftno + k, k - n)
    | Eid _ -> `Var (liftno + k)
  in
   aux_rel 0 k s

let shift_closure_array k clv =
  if k = 0 then clv else
  let cshift = Ctx.shift k Ctx.nil in
  Array.map (fun cl ->
      let _, subs, t, ctx = Clos.kind_of cl in
      Clos.mk ~subs t ~ctx:(Ctx.append ctx cshift))
    clv

let shift_closure k cl =
  if k = 0 then cl else
  let cshift = Ctx.shift k Ctx.nil in
  let _, subs, t, ctx = Clos.kind_of cl in
  Clos.mk ~subs t ~ctx:(Ctx.append ctx cshift)

let fix_body subs fix =
  let (reci,i),(_,_,bds as rdcl) = match kind_of fix with
    | HFix (_,a,b) -> a, b
    | _ -> assert false in
  let make_body j = Clos.mk ~subs (mkHFix ((reci,j),rdcl)) in
  let nfix = Array.length bds in
  Subs.cons (Array.init nfix make_body) subs, bds.(i)

let rec unzip t c = match Ctx.kind_of c with
  | Znil -> t
  | Zapp (_,a,ctx) -> unzip (mkApp (t, Array.map clos_to_constr a)) ctx
(* very suboptimal, maybe wrong *)
  | Zcase (_,ci,p,br,ctx) ->
     unzip (mkCase (ci,clos_to_constr p,t,Array.map clos_to_constr br)) ctx
  | Zfix (_,fx,ctx) ->
     unzip (clos_to_constr fx) (Ctx.app [|Clos.mk (intern t)|] ctx)
  | Zupdate (_,_,_,ctx) -> unzip t ctx
  | Zshift (_,s,ctx) -> unzip (lift s t) ctx
and apply_subs s t = match kind_of t with
  | HConst _
  | HInd _
  | HConstruct _
  | HSort _
  | HVar _
  | HMeta _ -> extern t
  | HEvar (_,k,a) -> mkEvar (k, Array.map (apply_subs s) a)
  | HCast (_,t,k,ty) -> mkCast (apply_subs s t, k, apply_subs s ty)
  | HProd (_,n,t1,t2) ->
      mkProd (n, apply_subs s t1, apply_subs (Subs.lift 1 s) t2)
  | HLambda (_,n,t1,t2) ->
      mkLambda (n, apply_subs s t1, apply_subs (Subs.lift 1 s) t2)
  | HLetIn (_,n, b,ty,t) ->
      mkLetIn (n, apply_subs s b, apply_subs s ty, apply_subs (Subs.lift 1 s) t)
  | HApp (_,f,a) -> mkApp (apply_subs s f, Array.map (apply_subs s) a)
  | HCase (_,ci,t,p,bs) ->
      mkCase (ci, apply_subs s t, apply_subs s p, Array.map (apply_subs s) bs)
  | HFix f -> extern t (* XXX *)
  | HCoFix c -> extern t (* XXX *)
  | HRel i ->
      match expand_rel i s with
      | `Code (n, t, _, _) -> lift n (clos_to_constr t)
      | `Var k -> mkRel k
      | `InEnv (k, p) -> lift (k-p) (mkRel p)
and clos_to_constr c =
  let _,s,t,c = Clos.kind_of c in
  unzip (apply_subs s t) c

open Pp

let print cmds = prerr_endline (string_of_ppcmds cmds)

let ppt ?(depth=3) e x =
  Term.ll_pr_constr depth (Environ.rel_context e) x

let print_status s t c = print(Clos.pp 10 (Clos.mk ~subs:s t ~ctx:c))

type options = {
  beta  : bool; (* App(Lambda _,_) reduction *)
  iota  : bool; (* Fix and CoFix unfolding; Case analysis *)
  zeta  : bool; (* LetIn reduction *)
  delta_rel : bool;    (* Rel unfolding *)
  delta_var : Idpred.t; (* Var unfolding *) 
  delta_con : Cpred.t;  (* Const unfolding *)
}

let betadeltaiotazeta = {
  beta = true;
  iota = true;
  zeta = true;
  delta_rel = true;
  delta_var = Idpred.full;
  delta_con = Cpred.full;
}

let betaiotazeta = {
  beta = true;
  iota = true;
  zeta = true;
  delta_rel = false;
  delta_var = Idpred.empty;
  delta_con = Cpred.empty;
}

type env_cache = {
  env_def : env; cache_def : (constant, H.hconstr) Hashtbl.t;
  env_rel : int * (int * constr) list;
  env_var : (identifier * constr) list;
}

(* XXX reduction does not really need intern *)
let unfold, unfold_intern =
  let lookup env c = (* TODO: lookup cache (w intern) *)
  try
    match c with
    | RelKey n ->
        let len, ctx = env.env_rel in
        let t = lift n (List.assoc (len - n) ctx) in
        Some t
    | VarKey id ->
        let t = List.assoc id env.env_var in
        Some t
    | ConstKey k ->
        let t = constant_value env.env_def k in
        if eq_constr t (mkConst k) then None (* XXX WTF! *) else
        Some t
  with Not_found | NotEvaluableConst _ -> None
  in
  (* lookup *)(fun e c -> Option.map intern (lookup e c)),
  (fun e c -> Option.map intern (lookup e c))

let create_env_cache env =
  (* TODO: make an array of closures to be updated, see also dummy array
     in HRel case, there we should stick in the Ctx.update the array
     representing the context *)
  let rel_env_len, rel_context =
    Sign.fold_rel_context
      (fun (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      (rel_context env) ~init:(0,[]) in
  (* TODO: the same *)
  let var_context =
    Sign.fold_named_context
      (fun (id,b,_) e ->
	 match b with
	   | None -> e
	   | Some body -> (id, body)::e)
       (named_context env) ~init:[] in
  { env_def = env; cache_def = Hashtbl.create 17;
    env_rel = rel_env_len, rel_context;
    env_var = var_context }


(* Since we assign subst elements, we can't build a new subst. We have to
 * keep the same arrays. We could try to drop the head and the tail when
 * they are not used and replace them by shift/id *)
let opt_subst s t = s

type why = Whnf | Opts

(* {{{ REDUCTION ************************************************************)

(* TODO: now works on hconstr, but could work on constr *)
let whd opt env evars c =
  (* Two exists: because in whnf or because opt says so *)
  let return s t c = s, t, c, Whnf in
  let stop_at s t c = s, t, c, Opts in

  let rec aux subs hd ctx =
(*
   print_status subs hd ctx;
   print (ppt ~depth:100 env.env_def (clos_to_constr (Clos.mk ~subs hd ~ctx)));
*)
    match kind_of hd with
    | HRel i -> (match expand_rel i subs with
        | `Code(liftno, cl, a, i) ->
            let _,subs, t, c = Clos.kind_of cl in
(*            let () = a.(i) <- Clos.mk (intern (mkProp)) in *)
            aux subs t (Ctx.append c (Ctx.update a i (Ctx.shift liftno ctx)))
        | `Var k ->
            return (Subs.id k) (intern (mkRel k)) ctx
        | `InEnv(liftno, k) when opt.delta_rel = false ->
            stop_at (Subs.id 0) (intern (mkRel k)) (Ctx.shift (liftno - k) ctx)
        | `InEnv(liftno, k) ->
            (match unfold env (RelKey k) with
            | Some t ->
                (* XXX see TODO above*)
                let a,i = [|Clos.mk (intern mkProp)|], 0 in
                aux (Subs.id 0) t (Ctx.update a i (Ctx.shift (liftno - k) ctx))
            | None -> (* mkRel(k + (liftno - k)) = mkRel liftno *)
                return (Subs.id 0) (intern(mkRel (liftno))) ctx))
    | HVar id when not (Idpred.mem id opt.delta_var) -> stop_at subs hd ctx
    | HVar id ->
            (match unfold env (VarKey id) with
            | Some t -> aux subs t ctx
            | None -> return (Subs.id 0) hd ctx)
    | HEvar (_,e,v) ->
       (match
        try Some (EvarMap.existential_value evars (e, extern_array v))
        with NotInstantiatedEvar -> None
       with
       | None -> return subs hd ctx
       | Some t -> aux subs (intern t) ctx)
    | HLetIn _ when opt.zeta = false -> stop_at subs hd ctx
    | HLetIn (_,_,t,_,bo) -> aux (Subs.cons [|Clos.mk ~subs t|] subs) bo ctx
    | HCast (_,t,_,_) -> aux subs t ctx
    | HApp (_,f,a) ->
       let clos_mk ~subs t = match kind_of t with
         | HConst _ | HVar _ | HInd _ | HConstruct _ | HSort _ | HMeta _ ->
             Clos.mk t
         | _ -> Clos.mk ~subs t in
       aux subs f (Ctx.app (Array.map (clos_mk ~subs) a) ctx)
    | HCase (_,ci,p,t,br) ->
        (* TODO: we could store in Ctx case the branches as hconstr, then
           since the subs is in p, take it out and apply it to the right branch
           only when the case is reduced. *)
        aux subs t
          (Ctx.case ci (Clos.mk ~subs p) (Array.map (Clos.mk ~subs) br) ctx)
    | HFix (_,(rargs,fixno),_) ->
        let rarg = rargs.(fixno) in
        let rec fix_params n c =
          match Ctx.kind_of c with
          | Zapp (_, args, c) -> if n <= 0 then Ctx.nil else
              let nargs = Array.length args in
              if n >= nargs then Ctx.app args (fix_params (n - nargs) c)
              else Ctx.app (Array.sub args 0 n) Ctx.nil
          | Zshift (_,s,c) -> Ctx.shift s (fix_params n c)
          | Zupdate (_,_,_,c) -> fix_params n c
          | Znil -> assert false
          | Zcase _ -> assert false
          | Zfix _ -> assert false in
        let rec find_arg n c = match Ctx.kind_of c with
          | Znil -> return subs hd ctx
          | Zapp (_,args,c) ->
              let nargs = Array.length args in
              if n >= nargs then find_arg (n - nargs) c
              else
                let afterctx =
                  let after = nargs - n - 1 in
                  if after > 0 then Ctx.app (Array.sub args (n + 1) after) c
                  else c in
                let _, s, t, c = Clos.kind_of args.(n) in
                aux s t (Ctx.append c
                  (Ctx.fix (Clos.mk ~subs ~ctx:(fix_params rarg ctx) hd)
                  afterctx))
          | Zshift (_,_,c) -> find_arg n c
          | Zupdate (_,_,_,c) -> find_arg n c
          | Zcase _ -> assert false
          | Zfix _ -> assert false in
        find_arg rarg ctx
    | HConstruct _ when opt.iota = false -> stop_at subs hd ctx
    | HConstruct (ind, k) ->
        (* TODO: coded in an inefficient way, measure if an acc made of a list
         * + List.rev is faster that re-traversing ctx many times (exp for
         * updates *)
        let rec ctx_for_case totshift n c = match Ctx.kind_of c with
          | Zapp (_,args,c) when n = 0 ->
              let args = shift_closure_array totshift args in
              Ctx.app args (ctx_for_case totshift n c)
          | Zapp (_,args,c) ->
              let nargs = Array.length args in
              if n > nargs then ctx_for_case totshift (n - nargs) c
              else if n = nargs then ctx_for_case totshift 0 c
              else
                let after = Array.sub args n (nargs - n) in
                ctx_for_case totshift 0 (Ctx.app after c)
          | Zcase (_,_,_,_,c) -> c
          | Zupdate (_,_,_,c) -> ctx_for_case totshift n c
          | Zshift (_,s,c) -> ctx_for_case (totshift - s) n c
          | Znil -> assert false
          | Zfix _ -> assert false in
        let rec ctx_for_fix_arg args = match Ctx.kind_of args with
          | Zfix (_,_,c) -> Ctx.nil
          | Zapp (_,a,c) -> Ctx.app a (ctx_for_fix_arg c)
          | Zupdate (_,_,_,c) -> ctx_for_fix_arg c
          | Zshift (_,s,c) -> Ctx.shift s (ctx_for_fix_arg c)
          | Zcase _ -> assert false
          | Znil _ -> assert false in
        let rec ctx_for_update n c = match Ctx.kind_of c with
          | Zupdate _ when n = 0 -> Ctx.nil
          | Zupdate (_,_,_,c) -> ctx_for_update (n-1) c
          | Zapp (_,a,c) -> Ctx.app a (ctx_for_update n c)
          | Zshift (_,s,c) -> Ctx.shift s (ctx_for_update n c)
          | _ -> assert false in
        let rec find_iota nupds totshift c = match Ctx.kind_of c with
          | Zapp (_,_,c) -> find_iota nupds totshift c
          | Zshift (_,s,c) -> find_iota nupds (totshift + s) c
          | Zcase (_,ci,p,br,_) ->
              let _, subs, b, c = Clos.kind_of br.(k-1) in
              (* c may contain a shift *)
              aux subs b (Ctx.append c (ctx_for_case totshift ci.ci_npar ctx))
          | Zfix (_,fx,c) ->
              let _, fxsubs, fxbo, fctx = Clos.kind_of fx in
              let fisubs, fi = fix_body fxsubs fxbo in
              aux fisubs fi (Ctx.append fctx
                (Ctx.app [|Clos.mk ~ctx:(ctx_for_fix_arg ctx) hd|] c))
          | Zupdate (_,a,i,c) ->
              let hnf = Clos.mk ~ctx:(ctx_for_update nupds ctx) hd in
              a.(i) <- hnf;
              find_iota (nupds + 1) totshift  c
          | Znil -> return subs hd ctx
        in
          find_iota 0 0 ctx
    | HLambda _ when opt.beta = false -> stop_at subs hd ctx
    | HLambda (_,_,_,t) -> (* XXX n-ary lambdas in hconstr too! *)
        let rec nlam n acc t = match kind_of t with
          | HLambda (_,_,_,bo) -> nlam (n+1) (t::acc) bo
          | _ -> n, acc, t in
        let nlam, spine, bo = nlam 1 [hd] t in
        let rec eat_lam subs n c =
          if n = nlam then aux subs bo c
          else match Ctx.kind_of c with
          | (Znil | Zcase _ | Zfix _) ->
             if n > 0 then
               let bo = List.nth spine (nlam - n - 1) in
               aux (opt_subst subs bo) bo c
             else return subs hd c
          | Zshift (_,s,c) -> eat_lam (Subs.shift s subs) n c
          | Zupdate (_,a,i,c) ->
              a.(i) <- Clos.mk ~subs (List.nth spine (nlam - n - 1));
              eat_lam subs n c
          | Zapp (_,args,c) ->
              let nargs = Array.length args in
              if n + nargs = nlam then
                aux (opt_subst (Subs.cons args subs) bo) bo c
              else if n + nargs < nlam then
                eat_lam (Subs.cons args subs) (n + nargs) c
              else
                let before = Array.sub args 0 (nlam - n) in
                let after = Array.sub args (nlam - n) (nargs - (nlam - n)) in
                aux (opt_subst (Subs.cons before subs) bo) bo (Ctx.app after c) in
        eat_lam subs 0 ctx
    | HConst c when not(Cpred.mem c opt.delta_con) -> stop_at (Subs.id 0) hd ctx
    | HConst c ->
        (match unfold env (ConstKey c) with
        | None -> return (Subs.id 0) hd ctx
        | Some bo -> aux (Subs.id 0) bo ctx)
    (* head normal terms *)
    | HSort _ | HMeta _ | HProd _ | HInd _ -> return subs hd ctx
    | HCoFix _ -> assert false (* TODO *)
  in
  let _, s, t, c = Clos.kind_of c in
  let s, t, c, why = aux s t c in
  Clos.mk ~subs:s ~ctx:c t, why
(* }}} END REDUCTION *********************************************************)

let unwind c = clos_to_constr c

let red_whd env evars t =
  reset ();
  let c = Clos.mk (intern t) in
  let n, _ =
    whd betadeltaiotazeta (create_env_cache env) evars.Mini_evd.evars c in
  unwind n

let red_strong env evars t =
  let env = create_env_cache env in
  let rec red_aux cl =
    let n, _ =
      whd betadeltaiotazeta env evars.Mini_evd.evars cl in
    let _, s, t, c = Clos.kind_of n in
    let t = subs_aux s t in
    unzip_aux t c
  and unzip_aux t c = match Ctx.kind_of c with
  | Znil -> t
  | Zapp (_,a,ctx) -> unzip_aux (mkApp (t, Array.map red_aux a)) ctx
  | Zcase (_,ci,p,br,ctx) ->
     unzip_aux (mkCase (ci,red_aux p,t,Array.map red_aux br)) ctx
  | Zfix (_,fx,ctx) ->
     unzip_aux (red_aux fx) (Ctx.app [|Clos.mk (intern t)|] ctx)
  | Zupdate (_,a,i,ctx) -> a.(i) <- (Clos.mk (intern t)); unzip_aux t ctx
  | Zshift (_,s,ctx) -> unzip_aux (lift s t) ctx
  and subs_aux s t = match kind_of t with
  | HConst _
  | HInd _
  | HConstruct _
  | HSort _
  | HVar _
  | HMeta _ -> extern t
  | HEvar (_,k,a) -> mkEvar (k, Array.map (subs_aux s) a)
  | HCast (_,t,k,ty) -> mkCast (subs_aux s t, k, subs_aux s ty)
  | HProd (_,n,t1,t2) ->
      mkProd (n, red_aux (Clos.mk ~subs:s t1),
        red_aux (Clos.mk ~subs:(Subs.lift 1 s) t2))
  | HLambda (_,n,t1,t2) ->
      mkLambda (n, red_aux (Clos.mk ~subs:s t1),
        red_aux (Clos.mk ~subs:(Subs.lift 1 s) t2))
  | HLetIn (_,n, b,ty,t) -> (* this may happen if one says no-z *)
      mkLetIn (n, red_aux (Clos.mk ~subs:s b),
        red_aux (Clos.mk ~subs:s ty), red_aux (Clos.mk ~subs:(Subs.lift 1 s) t))
  | HApp (_,f,a) -> mkApp (subs_aux s f, Array.map (subs_aux s) a)
  | HCase (_,ci,t,p,bs) ->
      mkCase (ci, subs_aux s t, subs_aux s p, Array.map (subs_aux s) bs)
  | HFix f -> extern t (* XXX *)
  | HCoFix c -> extern t (* XXX *)
  | HRel i ->
      match expand_rel i s with
      | `Code (n, t, _, _) -> lift n (red_aux t) (* XXX no updates *)
      | `Var k -> mkRel k
      | `InEnv (k, p) -> lift (k-p) (mkRel p)
  in
  reset ();
  red_aux (Clos.mk (intern t))

exception NotConvertible

(* {{{ TRACING INSTRUMENTATION *)

let debug = ref true
let indent = ref "";;
let times = ref [];;
let last_time = ref 0.0;;
(*D*  let pp s = if !debug then prerr_endline (string_of_ppcmds (Lazy.force s))  *D*)
let __time () = (Unix.times ()).Unix.tms_utime
let __time () = Unix.gettimeofday ()
let __inside s =
 if !debug then begin
   let time1 = __time () in
   let c = s.[0] in
   times := time1 :: !times;
   Printf.eprintf "{{{ %s %s\n" !indent s;
   indent := !indent ^ String.make 1 c;
  end
;;
let __outside ?cmp_opt exc_opt =
 if !debug then
  begin
   let time2 = __time () in
   let time1 =
     match !times with time1::tl -> times := tl; time1 | [] -> assert false in
   let time = time2 -. time1 in
   last_time := time;
   Printf.eprintf "}}}\n    %s%s%s\n" (String.make (String.length !indent) ' ')
   (match exc_opt with
   | None ->   Printf.sprintf "returned in %.3f" time
   | Some e -> Printf.sprintf "failed in   %.3f (%s)" time
       (Printexc.to_string e))
   (match cmp_opt with
   | None -> ""
   | Some t when abs_float (t -. time) < 0.000001 -> ""
   | Some t ->
      Printf.sprintf " %s %.3f" (if t > time then "FASTER" else "SLOWER") t);
   try
    indent := String.sub !indent 0 (String.length !indent -1)
   with
    Invalid_argument _ -> indent := "??"; ()
  end
;;

(* }}} TRACING INSTRUMENTATION *)

let sum_shifts ctx =
  let rec sum_aux n c = match Ctx.kind_of c with
  | Znil -> n
  | Zshift(_,m,c) -> sum_aux (n+m) c
  | Zupdate(_,_,_,c) | Zapp(_,_,c) | Zfix(_,_,c) | Zcase(_,_,_,_,c) ->
      sum_aux n c in
  sum_aux 0 ctx

(* XXX we could normalize the closure before interning it:
           s, t, [ c1; ^1; c2; ^3; c3 ] --->
           s, t, [ ^4; c1^4; c2^3; c3 ]
   benefits:
       1. the stack is ready for convert_stacks
       2. this interning phase interns already the right closures for
          the UF calls in convert_stacks
       3. sum_shifts is done here once
       4. new invariant, UF handles whnf-canonical-in-shifts-too
       5. this would break an assert in whd on Case, but can be fixed
       6. to be understood how to deal with updates in the stack, maybe it
          is sufficient to fire them as in fapp_stack
   question: can we pass the ^4 into s and (apply it if t is Rel)?
       1. this si consistent with clos_to_constr
       2. easy to call on subterms when t is Lam/Prod/Evar/Fix
       3. back to my original idea of not having Zshift, but we now know
          it make sense to have it temporarily to avoid loosing
          sharing / updates, but can always be eliminated
    problem: what to do about updates?
       1. they get lost? I mean they can fired only once

let canon_closure cl =
  let _, s, t, c = Clos.kind_of cl in
  let n = sum_shifts c in
  let rec distribute_shifts n c = match Ctx.kind_of c with
  | Znil -> Ctx.nil
  | Zshift (_,m,c) -> distribute_shifts (n - m) c
  | Zapp (_,a,c) -> Ctx.app (shift_closure_array n a) (distribute_shifts n c)
  | Zcase (_,ci,p,br,c) ->
      Ctx.case ci (shift_closure n p) (shift_closure_array n br)
        (distribute_shifts n c)
  | Zfix (_,f,c) -> Ctx.fix (shift_closure n f) (distribute_shifts n c)
  | Zupdate (_,_,_,c) -> distribute_shifts n c in
  match kind_of t with
  | HRel i -> Clos.mk (intern(mkRel (i+n))) ~ctx:(distribute_shifts n c)
  | _ -> Clos.mk ~subs:(Subs.shift n s) t ~ctx:(distribute_shifts n c)

let fire_clear_updates cl = (* this time we do that with closures *)
  let _, subs, t, ctx = Clos.kind_of cl in
  let rec fire f c = match Ctx.kind_of c with
  | Znil -> Ctx.nil
  | Zshift (_,n,c) -> Ctx.shift n (fire (fun c -> f (Ctx.shift n c)) c)
  | Zupdate (_,a,i,c) -> a.(i) <- Clos.mk ~subs ~ctx:(f Ctx.nil) t; fire f c
  | Zapp (_,a,c) -> Ctx.app a (fire (fun c -> f (Ctx.app a c)) c)
  | Zfix (_,fx,c) -> Ctx.fix fx (fire (fun c -> f (Ctx.fix fx c)) c)
  | Zcase (_,ci,p,br,c) ->
       Ctx.case ci p br (fire (fun c -> f (Ctx.case ci p br c)) c) in
  Clos.mk ~subs t ~ctx:(fire (fun x -> x) ctx)
*)

(* this is the equivalent of "let _ = fapp_stack ..." in reduction.ml *)
(* XXX: we could also intern/extern the closures we assign *)
let fire_updates cl =
  (* this time we do that in CPS style *)
  (* TODO: measure speed w.r.t. List.rev and retraversing the list *)
  let _, subs, t, ctx = Clos.kind_of cl in
  let rec fire f c = match Ctx.kind_of c with
  | Znil -> ()
  | Zshift (_,n,c) -> fire (fun c -> f (Ctx.shift n c)) c
  | Zupdate (_,a,i,c) -> a.(i) <- Clos.mk ~subs ~ctx:(f Ctx.nil) t; fire f c
  | Zapp (_,a,c) -> fire (fun c -> f (Ctx.app a c)) c
  | Zfix (_,fx,c) -> fire (fun c -> f (Ctx.fix fx c)) c
  | Zcase (_,ci,p,br,c) -> fire (fun c -> f (Ctx.case ci p br c)) c in
  fire (fun x -> x) ctx

let sort_cmp pb s0 s1 cuniv =
  match (s0,s1) with
  | (Prop c1, Prop c2) when pb = CUMUL ->
      if c1 = Null or c2 = Pos then cuniv   (* Prop <= Set *)
      else raise NotConvertible
  | (Prop c1, Prop c2) ->
      if c1 = c2 then cuniv else raise NotConvertible
  | (Prop c1, Type u) when pb = CUMUL -> assert (is_univ_variable u); cuniv
  | (Type u1, Type u2) ->
      assert (is_univ_variable u2);
      (match pb with
         | CONV -> enforce_eq u1 u2 cuniv
         | CUMUL -> enforce_leq u1 u2 cuniv)
  | (_, _) -> raise NotConvertible

(* {{{ CONVERSION ***********************************************************)

let are_convertible (trans_var, trans_def) cv_pb ~l2r evars env t1 t2 =
  let env = create_env_cache env in
  let whd cl =
    let cl, why = whd betaiotazeta env evars cl in
    (* XXX fire_updates as in fapp_stack? *)
    Clos.H.intern cl, why in
  let mk_whd_clos ?subs ?ctx t = whd (Clos.mk ?subs ?ctx t) in
  let same_len a1 a2 = Array.length a1 = Array.length a2 in
  let slift = Subs.lift 1 in
  let sshift n = Subs.shift n in
  let fold_left2 = Util.Array.fold_left2 in
  let fold_right2 = Util.Array.fold_right2 in
(*A* let hclos_to_constr c = clos_to_constr (Clos.H.extern c) in *A*)
  let unfold_flex e t = match kind_of t with
    | HRel n -> unfold_intern e (RelKey n) (* TODO: lookup up every time *)
    | HVar id when Idpred.mem id trans_var -> unfold_intern e (VarKey id)
    | HConst k when Cpred.mem k trans_def -> unfold_intern e (ConstKey k)
    | _ -> None in
  let eq_flex l1 t1 l2 t2 = match kind_of t1 with (* t1/t2 of the same kind *)
    | HRel _ -> Term.H.equal t1 t2 && l1 = l2
    | _ -> Term.H.equal t1 t2 (* Var or Const *) in 
  let oracle_flex t1 t2 =
    let oracle = Conv_oracle.oracle_order l2r in
    match kind_of t1, kind_of t2 with
    | HRel n1, HRel n2 -> oracle (RelKey n1) (RelKey n2)
    | HVar id1, HVar id2 -> oracle (VarKey id1) (VarKey id2)
    | HConst k1, HConst k2 -> oracle (ConstKey k1) (ConstKey k2)
    | _ -> assert false in

  let eta_expand_ctx c =
    let eta_expand_suffix =
      let r1 = Clos.mk ~subs:(Subs.lift 1 (Subs.id 0)) (intern (mkRel 1)) in
      Ctx.shift 1 (Ctx.app [|r1|] Ctx.nil) in
    Ctx.append c eta_expand_suffix in

  let _pr_status cl1 cl2 i =
       let pcl n e c = Clos.H.pp n c in
       let env = Environ.reset_context env.env_def in
    hv 0 (pcl i env cl1 ++ spc()++
           str "=?"++str"="++spc()++ pcl i env cl2) in
  let _pr_heads l1 s1 t1 l2 s2 t2 =
    let t1, t2 = lift l1 (apply_subs s1 t1), lift l2 (apply_subs s2 t2) in
    print(ppt ~depth:1 env.env_def t1 ++ str" " ++
          ppt ~depth:1 env.env_def t2) in

  let rec convert_whd cv_pb s1 s2 cst t1 t2 =
    convert cv_pb cst (mk_whd_clos ~subs:s1 t1) (mk_whd_clos ~subs:s2 t2)

  and convert cv_pb cst (cl1, why1 as lhs) (cl2, why2 as rhs) =
(*D* __inside "convert"; try let __rc = pp(lazy(_pr_status cl1 cl2 1)); *D*)
    match UF.same cl1 cl2 with
    | `Yes   -> (*D* pp(lazy(str" UF: YES")); *D*) cst
    | `No    -> (*D* pp(lazy(str" UF: NO"));  *D*) raise NotConvertible
    | `Maybe ->
    let _, s1, t1, c1 = Clos.H.kind_of cl1 in
    let _, s2, t2, c2 = Clos.H.kind_of cl2 in
    let l1, l2 = sum_shifts c1, sum_shifts c2 in
(*A* let eq_c = eq_constr (hclos_to_constr cl1) (hclos_to_constr cl2) in
      pp(lazy(str" UF: MAYBE " ++ bool eq_c));
      try *A*)
(*D* _pr_heads l1 s1 t1 l2 s2 t2; *D*)
    match kind_of t1, kind_of t2 with
    | HSort s1, HSort s2 -> sort_cmp cv_pb s1 s2 cst
    | HMeta n1, HMeta n2 when n1 = n2 ->
        congruence cv_pb cst cl1 cl2 l1 c1 l2 c2
    | HEvar (_,n1,a1), HEvar (_,n2,a2) when n1 = n2 && same_len a1 a2 ->
        (try
          let s1, s2 = sshift l1 s1, sshift l2 s2 in
          let cst = fold_left2 (convert_whd cv_pb s1 s2) cst a1 a2 in
          let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
          UF.union cl1 cl2; cst
        with NotConvertible as e -> UF.partition cl1 cl2; raise e)
    | HRel n1, HRel n2 when why1 = Whnf && why2 = Whnf && n1 + l1 = n2 + l2 ->
        congruence cv_pb cst cl1 cl2 l1 c1 l2 c2
    | HInd i1, HInd i2 when eq_ind i1 i2 ->
        congruence cv_pb cst cl1 cl2 l1 c1 l2 c2
    | HConstruct (i1,n1), HConstruct (i2,n2) when eq_ind i1 i2 && n1 = n2 ->
        congruence cv_pb cst cl1 cl2 l1 c1 l2 c2
    | HLambda (_,_,ty1,bo1), HLambda (_,_,ty2,bo2) ->
        (try
          let s1, s2 = sshift l1 s1, sshift l2 s2 in
          let cst = convert_whd CONV s1 s2 cst ty1 ty2 in
          let cst = convert_whd CONV (slift s1) (slift s2) cst bo1 bo2 in
          UF.union cl1 cl2; cst
        with NotConvertible as e -> UF.partition cl1 cl2; raise e)
    | HProd (_,_,ty1,bo1), HProd (_,_,ty2,bo2) ->
        (try
          let s1, s2 = sshift l1 s1, sshift l2 s2 in
          let cst = convert_whd CONV s1 s2 cst ty1 ty2 in
          let cst = convert_whd cv_pb (slift s1) (slift s2) cst bo1 bo2 in
          UF.union cl1 cl2; cst
        with NotConvertible as e -> UF.partition cl1 cl2; raise e)
(* TODO:
    | CoFix, CoFix ->
 *)
    | HFix(_,op1,(_,tys1,bos1)), HFix(_,op2,(_,tys2,bos2))
      when op1 = op2 && same_len tys1 tys2 && same_len bos1 bos2 ->
        (try
          let s1, s2 = sshift l1 s1, sshift l2 s2 in
          let cst = fold_left2 (convert_whd CONV s1 s2) cst tys1 tys2 in
	  let n = Array.length bos1 in
          let s1' = Subs.lift n s1 and s2' = Subs.lift n s2 in
          let cst = fold_left2 (convert_whd CONV s1' s2') cst bos1 bos2 in
          let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
          UF.union cl1 cl2; cst
        with NotConvertible as e -> UF.partition cl1 cl2; raise e)
    | HRel _, HRel _
    | HVar _, HVar _
    | HConst _, HConst _ ->
        (try
          if not (eq_flex l1 t1 l2 t2) then raise NotConvertible
          else
            let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
            UF.union cl1 cl2;
            cst
        with NotConvertible ->
          (* TODO: inefficient, we always lookup both constants *)
          let bo1, bo2 =
            match unfold_flex env t1, unfold_flex env t2 with
            | None, None -> UF.partition cl1 cl2; raise NotConvertible
            | Some bo, None -> bo, t2
            | None, Some bo -> t1, bo
            | Some bo1, Some bo2 ->
                if oracle_flex t1 t2 then bo1, t2 else t1, bo2 in
          (* TODO: call this only when needed *)
          let cl1', _ as lhs = mk_whd_clos ~ctx:c1 bo1 in
          let cl2', _ as rhs = mk_whd_clos ~ctx:c2 bo2 in
          UF.union cl1' cl1;
          UF.union cl2' cl2;
          convert cv_pb cst lhs rhs)
    | HLambda (_,_,_,bo1), _ -> (* XXX see msg on coq club *)
        let eta_cl2 = Clos.mk ~subs:s2 t2 ~ctx:(eta_expand_ctx c2) in
        convert CONV cst (mk_whd_clos ~subs:(slift s1) bo1) (whd eta_cl2)
    | _, HLambda (_,_,_,bo2) ->
        let eta_cl1 = Clos.mk ~subs:s1 t1 ~ctx:(eta_expand_ctx c1) in
        convert CONV cst (whd eta_cl1) (mk_whd_clos ~subs:(slift s2) bo2)
    | (HConst _ | HRel _ | HVar _), _
    | _, (HConst _ | HRel _ | HVar _) ->
        (match unfold_flex env t1 with
        | Some bo ->
            let cl1',_ as lhs = mk_whd_clos ~ctx:c1 bo in
            UF.union cl1' cl1;
            convert cv_pb cst lhs rhs
        | None ->
            (match unfold_flex env t2 with
            | Some bo ->
                let cl2', _ as rhs = mk_whd_clos ~ctx:c2 bo in
                UF.union cl2' cl2;
                convert cv_pb cst lhs rhs
            | None -> UF.partition cl1 cl2; raise NotConvertible))
    | (HLetIn _,_) | (_,HLetIn _) -> assert false
    | (HApp _,_)   | (_,HApp _)   -> assert false
    | (HCase _,_)  | (_,HCase _)  -> assert false
    | _ -> UF.partition cl1 cl2; raise NotConvertible
(*A*  with NotConvertible as e ->
        if eq_c then
          print (ppt env.env_def (hclos_to_constr cl1) ++ spc() ++
                 ppt env.env_def (hclos_to_constr cl2) ++ spc() ++
                 Clos.H.pp 10 cl1 ++ spc() ++ Clos.H.pp 10 cl2);
        assert(eq_c = false); raise e *A*)
(*D*  in __outside None; __rc with exn -> __outside (Some exn); raise exn *D*)

  and congruence cv_pb cst cl1 cl2 l1 c1 l2 c2 =
(*D* __inside "Congruence"; try let __rc =  *D*)
    try
      let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
      UF.union cl1 cl2; cst
    with NotConvertible as e -> UF.partition cl1 cl2; raise e
(*D*  in __outside None; __rc with exn -> __outside (Some exn); raise exn *D*)

  and convert_whd_shift_cl cv_pb l1 l2 cl1 cl2 cst =
      convert cv_pb cst
        (whd (shift_closure l1 cl1)) (whd (shift_closure l2 cl2))

  (* TODO: change order (to left-to-right).
   * this changes a lot, so measure it independently.
   * moreover it is easy if closures on the context are already shifted.
   * this requires a compare_stack_shape to avoid stupid comparisons *)
  and convert_stacks cv_pb cst l1 c1 l2 c2 =
(*D* __inside "stack"; try let __rc =  *D*)
    match Ctx.kind_of c1, Ctx.kind_of c2 with
    | Znil, Znil -> cst
    | Zshift (_,n, c1), _ ->
        convert_stacks cv_pb cst (l1 - n) c1 l2 c2
    | _, Zshift (_,n, c2) ->
        convert_stacks cv_pb cst l1 c1 (l2 - n) c2
    | Zupdate (_,_,_, c1), _ -> convert_stacks cv_pb cst l1 c1 l2 c2
    | _, Zupdate (_,_,_, c2) -> convert_stacks cv_pb cst l1 c1 l2 c2
    | Zapp (_, a1, c1), Zapp (_, a2, c2) when same_len a1 a2 ->
        let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
        fold_right2 (convert_whd_shift_cl cv_pb l1 l2) a1 a2 cst
    | Zapp (_, a1, c1), Zapp (_, a2, c2) ->
        let la1, la2 = Array.length a1, Array.length a2 in
        let a1, a2, c1, c2 =
          if la1 < la2 then
            a1, Array.sub a2 0 la1, c1, Ctx.app (Array.sub a2 la1 (la2-la1)) c2
          else
            Array.sub a1 0 la2, a2, Ctx.app (Array.sub a1 la2 (la1-la2)) c1, c2
        in
        let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
        fold_right2 (convert_whd_shift_cl cv_pb l1 l2) a1 a2 cst
    | Zcase (_, i1, p1, br1, c1), Zcase (_, i2, p2, br2, c2)
      when eq_ind i1.ci_ind i2.ci_ind ->
        let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
        let cst = convert_whd_shift_cl cv_pb l1 l2 p1 p2 cst in
        fold_right2 (convert_whd_shift_cl cv_pb l1 l2) br1 br2 cst
    | Zfix (_, f1, c1), Zfix (_, f2, c2) ->
        let cst = convert_stacks cv_pb cst l1 c1 l2 c2 in
        convert_whd_shift_cl cv_pb l1 l2 f1 f2 cst
    | _ -> raise NotConvertible
(*D*  in __outside None; __rc with exn -> __outside (Some exn); raise exn *D*)

  in
(*D* pp(lazy(ppt env.env_def ~depth:9 t1++str" VS "++spc()++
              ppt env.env_def ~depth:9 t2)); *D*)
  reset ();
  Clos.H.reset ();
  UF.reset ();
  let t1 = intern t1 in
  let t2 = intern t2 in
  convert_whd cv_pb (Subs.id 0) (Subs.id 0) empty_constraint t1 t2

(* }}} END CONVERSION *******************************************************)

(* vim:set foldmethod=marker: *)
