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

(* when false, not hashconsing is performed, just for testing performances *)
let interning = false

let array_peq t1 t2 = t1 == t2 || Util.Array.for_all2 (==) t1 t2

module Hclosure : sig

  type ctx
  type closure
  type subs
  type hconstr = Term.H.hconstr

  type dummy (* like unit, no content *)
  
  type kind_of_ctx =
    | Znil
    | Zapp   of dummy * closure array * ctx
    | Zcase  of dummy * case_info * closure * closure array * ctx
    | Zfix   of dummy * closure * ctx
    | Zshift of dummy * int * ctx
  type kind_of_subs =
    | ESID  of int
    | CONS  of dummy * closure array * subs
    | SHIFT of dummy * int * subs
    | LIFT  of dummy * int * subs

  module Ctx : sig
    val nil : ctx
    val app : closure array -> ctx -> ctx
    val case : case_info -> closure -> closure array -> ctx -> ctx
    val fix : closure -> ctx -> ctx
    val shift : int -> ctx -> ctx
    val kind_of : ctx -> kind_of_ctx
    val equal : ctx -> ctx -> bool
    val append : ctx -> ctx -> ctx
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
    val equal : closure -> closure -> bool
    val hash : closure -> int
    val compare : closure -> closure -> int
    val reset : unit -> unit 
    val distribution : unit -> (closure * int) list list

    val intern : subs -> hconstr -> ctx -> closure
    val extern : closure -> dummy * subs * hconstr * ctx
  end

  module Table : Hashtbl.S with type key = closure

end = struct

  type hconstr = Term.H.hconstr

  type hash = int
  type dummy = hash

  type ctx =
    | Znil
    | Zapp   of hash * closure array * ctx
    | Zcase  of hash * case_info * closure * closure array * ctx
    | Zfix   of hash * closure * ctx
    | Zshift of hash * int * ctx
  and subs =
    | ESID  of int
    | CONS  of hash * closure array * subs
    | SHIFT of hash * int * subs
    | LIFT  of hash * int * subs
  and closure = hash * subs * hconstr * ctx

  type kind_of_ctx = ctx =
    | Znil
    | Zapp   of hash * closure array * ctx
    | Zcase  of hash * case_info * closure * closure array * ctx
    | Zfix   of hash * closure * ctx
    | Zshift of hash * int * ctx
  type kind_of_subs = subs =
    | ESID  of int
    | CONS  of hash * closure array * subs
    | SHIFT of hash * int * subs
    | LIFT  of hash * int * subs

  (* one level comparson, used to hashcons only. closures are shared *)
  (* XXX think about comparing the hash *)
  let rec equal_ctx c1 c2 = c1 == c2 || match c1, c2 with
    | Znil, Znil -> true
    | Zapp (_,a1,c1), Zapp (_,a2,c2) ->
        array_peq a1 a2 && equal_ctx c1 c2
    | Zcase (_,_,t1,a1,c1), Zcase (_,_,t2,a2,c2) ->
        t1 == t2 && array_peq a1 a2 && equal_ctx c1 c2
    | Zfix (_,f1,c1), Zfix (_,f2,c2) -> f1 == f2 && equal_ctx c1 c2
    | Zshift (_,n1,c1), Zshift (_,n2,c2) -> n1 = n2 && equal_ctx c1 c2
    | _ -> false

  (* XXX think about comparing the hash *)
  let rec equal_subs s1 s2 = s1 == s2 || match s1, s2 with
    | ESID n, ESID m -> n = m
    | CONS (_,a1,s1), CONS (_,a2,s2) -> array_peq a1 a2 && equal_subs s1 s2
    | SHIFT (_,n,s1), SHIFT (_,m,s2)
    | LIFT (_,n,s1), LIFT (_,m,s2) -> n = m && equal_subs s1 s2
    | _ -> false

  (* XXX think about comparing the hash *)
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
        |	Empty -> add hash key table; key
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

  let clos_table = HashsetClos.create 19991
  let reset () = HashsetClos.reset 19991 clos_table

  let hash_ctx = function
    | Znil -> 0
    | Zapp (h,_,_) | Zcase (h,_,_,_,_) | Zfix (h,_,_) | Zshift (h,_,_) -> h

  let hash_subs = function
    | ESID n -> n
    | CONS (h,_,_) | SHIFT (h,_,_) | LIFT (h,_,_) -> h
 
  let hash (h,_,_,_) = h

  open Hashset.Combine

  let hash_array t =
    let accu = ref 0 in
    for i = 0 to Array.length t - 1 do
      accu := combine !accu (hash t.(i));
    done;
    !accu

  (* ctx constructor *)
  module Ctx = struct
  let nil = Znil
  let app = if not interning then (fun a c -> Zapp (0,a,c))
    else (fun a c ->
       let h = combinesmall 17 (combine (hash_array a) (hash_ctx c)) in
       Zapp (h,a,c))
  let case = if not interning then (fun ci m p c -> Zcase (0,ci,m,p,c))
    else (fun ci m p c ->
      let h = combinesmall 18 (combine3 (hash m) (hash_array p) (hash_ctx c)) in
      Zcase (h,ci,m,p,c))
  let fix = if not interning then (fun m c -> Zfix (0,m,c))
    else (fun m c ->
      let h = combinesmall 19 (combine (hash m) (hash_ctx c)) in
      Zfix (h,m,c))
  let shift = if not interning then (fun n c -> Zshift (0,n,c))
    else (fun n c ->
      let h = combinesmall 20 (combine n (hash_ctx c)) in
      Zshift (h,n,c))
  let kind_of c = c
  let equal c1 c2 =
    let h1 = hash_ctx c1 in let h2 = hash_ctx c2 in
    h1 = h2 && equal_ctx c1 c2 (* XXX think about comparing the hash *)
  let rec append c1 c2 = match c1 with
    | Znil -> c2
    | Zapp (_,a,c) -> app a (append c c2)
    | Zcase (_,ci,m,p,c) -> case ci m p (append c c2)
    | Zfix (_,m,c) -> fix m (append c c2)
    | Zshift (_,n,c) -> shift n (append c c2)
  end

  (* subs constructors *)
  module Subs = struct
  let id n = ESID n
  let cons = if not interning then (fun a s -> CONS (0,a,s))
    else (fun a s ->
      let h = combinesmall 21 (combine (hash_array a) (hash_subs s)) in
      CONS (h,a,s))
  let shift = if not interning then (fun n s -> 
      if n = 0 then s
      else match s with
      | SHIFT (_,m,s) -> SHIFT (0,n + m,s)
      | _ -> SHIFT (0,n,s))
    else (fun n s ->
      if n = 0 then s
      else match s with
      | SHIFT (_,m,s) ->
          let n = n + m in
          let h = combinesmall 22 (combine n (hash_subs s)) in
          SHIFT (h,n,s)
      | _ ->
          let h = combinesmall 22 (combine n (hash_subs s)) in
          SHIFT (h,n,s))
  let lift = if not interning then (fun n s -> LIFT(0,n,s))
    else (fun n s ->
      let h = combinesmall 23 (combine n (hash_subs s)) in
      LIFT (h,n,s))
  let kind_of s = s
  let equal s1 s2 =
    let h1 = hash_subs s2 in let h2 = hash_subs s2 in
    h1 = h2 && equal_subs s1 s2 (* XXX think about comparing the hash *)
  end

  module Clos = struct
  let intern =
    if not interning then fun s t c -> 0, s, t ,c
    else fun s t c ->
      let h =
        combinesmall 24 (combine3 (hash_subs s) (Term.H.hash t) (hash_ctx c)) in
      HashsetClos.repr h (h,s,t,c) clos_table

  let extern c = c

  let hash = hash

  let equal c1 c2 = c1 == c2

  let compare c1 c2 =
    if equal c1 c2 then 0
    else
      let diff = hash c1 - hash c2 in
      if diff = 0 then Pervasives.compare c1 c2 else diff

  let reset = reset
  let distribution () = HashsetClos.distribution clos_table
  end

  module Table = Hashtbl.Make(struct
    type t = closure
    let equal = Clos.equal
    let hash = Clos.hash
  end)

end

module UF : sig

  open Hclosure

  val find : closure -> closure
  val union : smaller:closure -> closure -> unit
  val partition : closure -> closure -> unit
  val same : closure -> closure -> [`Yes | `No | `Maybe of closure * closure]
  val reset : unit -> unit
  
end = struct

  open Hclosure
  module HT = Hclosure.Table

  let rank : int HT.t = HT.create 1099
  let father : closure HT.t = HT.create 1099
  let smallest : closure HT.t = HT.create 1099

  let father_of t =
    try HT.find father t with Not_found -> HT.replace father t t; t

  let rank_of rx = try HT.find rank rx with Not_found -> 0
  
  let rec find i =
    let fi = father_of i in
    if Clos.equal fi i then i
    else
      let ri = find fi in 
      HT.replace father i ri;
      ri

  let smallest_of rx =
    try HT.find smallest rx
    with Not_found -> rx

  module UFCset = Set.Make(struct
    type t = closure
    let compare x y =
      let rx = find x in
      let ry = find y in
      Clos.compare rx ry
  end)
    
  let partitions : UFCset.t HT.t = HT.create 1099
  
  let diff_of rx = try HT.find partitions rx with Not_found -> UFCset.empty

  let partition x y =
    let rx = find x in
    let ry = find y in
    assert(Clos.equal rx ry = false);
    HT.replace partitions rx (UFCset.add ry (diff_of rx));
    HT.replace partitions ry (UFCset.add rx (diff_of ry))

  let same x y =
    let rx = find x in
    let ry = find y in
    if Clos.equal rx ry then `Yes
    else if UFCset.mem rx (diff_of ry) then `No
    else `Maybe (smallest_of rx,smallest_of ry)

  let reset () =
    HT.clear rank;
    HT.clear father;
    HT.clear smallest;
    HT.clear partitions

  let union ~smaller:x y =
    let rx = find x in
    let ry = find y in
    if not (Clos.equal rx ry) then begin
      let rkx = rank_of x in
      let rky = rank_of y in
      let sx = smallest_of rx in
      if rkx > rky then begin
        HT.replace father ry rx;
        HT.replace smallest rx sx;
        HT.replace partitions rx (UFCset.union (diff_of rx) (diff_of ry));
      end else if rkx < rky then begin
        HT.replace father rx ry;
        HT.replace smallest ry sx;
        HT.replace partitions ry (UFCset.union (diff_of rx) (diff_of ry));
      end else begin
        HT.replace rank rx (rkx + 1);
        HT.replace father ry rx;
        HT.replace smallest rx sx;
        HT.replace partitions rx (UFCset.union (diff_of rx) (diff_of ry));
      end
    end

end

open Hclosure
open Term.H

let intern =
  if not interning then Obj.magic
  else intern

let rec len_subs s n = match Subs.kind_of s with
  | LIFT(_,_,s) |CONS (_,_,s) | SHIFT(_,_,s) -> len_subs s (n+1)
  | _ -> n

let len = ref 0;;

let expand_rel k s =
(*   len := max !len (len_subs s 0); *)
  let rec aux_rel lams k s = match Subs.kind_of s with
    | CONS (_,def,_) when k <= Array.length def
                           -> Inl(lams,def.(Array.length def - k))
    | CONS (_,v,l)           -> aux_rel lams (k - Array.length v) l
    | LIFT (_,n,_) when k<=n -> Inr(lams+k,None)
    | LIFT (_,n,l)           -> aux_rel (n+lams) (k-n) l
    | SHIFT (_,n,s)          -> aux_rel (n+lams) k s
    | ESID n when k<=n     -> Inr(lams+k,None)
    | ESID n               -> Inr(lams+k,Some (k-n))
  in
   aux_rel 0 k s

let assoc_opt l v =
  try Some (List.assoc v l)
  with Not_found -> None

let mk_clos ?(subs=Subs.id 0) ?(ctx=Ctx.nil) t =
  match kind_of t with
  | HRel i ->
        (match expand_rel i subs with
        | Inl(n,cl) ->
            let _,subs, t, c = Clos.extern cl in
            Clos.intern (Subs.shift n subs) t (Ctx.append c ctx)
        | Inr(k,None) -> Clos.intern subs (intern (mkRel k)) ctx
        | _ -> Clos.intern subs t ctx)
  | _ -> Clos.intern subs t ctx

let lift_closure_array k clv =
  Array.map (fun cl ->
  let _,s,t,c = Clos.extern cl in
  Clos.intern (Subs.shift k s) t c) clv

let rec get_args n e stk =
  match Ctx.kind_of stk with
    | Zshift(_,k,s) -> get_args n (Subs.shift k e) s
    | Zapp(_,l,s) ->
        let na = Array.length l in
        if n = na then (Inl (Subs.cons l e), s)
        else if n < na then (* more arguments *)
          let args = Array.sub l 0 n in
          let eargs = Array.sub l n (na-n) in
          (Inl (Subs.cons args e), Ctx.app eargs s)
        else (* more lambdas *)
          get_args (n-na) (Subs.cons l e) s
    | _ -> (Inr (n,e), stk)

let rec unzip t c = match Ctx.kind_of c with
  | Znil -> t
  | Zapp (_,a,ctx) -> unzip (mkApp (t, Array.map clos_to_constr a)) ctx
(* very suboptimal, maybe wrong *)
  | Zshift (_,k,ctx) -> unzip (apply_subs (Subs.shift k (Subs.id 0)) (intern t)) ctx
  | Zcase (_,ci,p,br,ctx) ->
     unzip (mkCase (ci,clos_to_constr p,t,Array.map clos_to_constr br)) ctx
  | Zfix (_,fx,ctx) ->
     unzip (clos_to_constr fx) (Ctx.app [|mk_clos (intern t)|] ctx)
and apply_subs s t = match kind_of t with
  | HConst _
  | HInd _
  | HConstruct _
  | HSort _
  | HVar _
  | HMeta _ -> extern t
  | HEvar (_,k,a) -> mkEvar (k, Array.map (apply_subs s) a)
  | HCast (_,t,k,ty) -> mkCast (apply_subs s t, k, apply_subs s ty)
  | HProd (_,n,t1,t2) -> mkProd (n, apply_subs s t1, apply_subs (Subs.lift 1 s) t2)
  | HLambda (_,n,t1,t2) -> mkLambda (n, apply_subs s t1, apply_subs (Subs.lift 1 s) t2)
  | HLetIn (_,n, b,ty,t) ->
      mkLetIn (n, apply_subs s b, apply_subs s ty, apply_subs (Subs.lift 1 s) t)
  | HApp (_,f,a) -> mkApp (apply_subs s f, Array.map (apply_subs s) a)
  | HCase (_,ci,t,p,bs) ->
      mkCase (ci, apply_subs s t, apply_subs s p, Array.map (apply_subs s) bs)
  | HFix f -> extern t (* XXX *)
  | HCoFix c -> extern t (* XXX *)
  | HRel i ->
      match expand_rel i s with
      | Inl (n, t) -> lift n (clos_to_constr t)
      | Inr (k, None) -> mkRel k
      | Inr (k, Some p) -> lift (k-p) (mkRel p)
and clos_to_constr c =
  let _,s,t,c = Clos.extern c in
  unzip (apply_subs s t) c

let fix_body subs fix =
  let (reci,i),(_,_,bds as rdcl) = match kind_of fix with
    | HFix (_,a,b) -> a, b
    | _ -> assert false in
  let make_body j = mk_clos ~subs (mkHFix ((reci,j),rdcl)) in
  let nfix = Array.length bds in
  Subs.cons (Array.init nfix make_body) subs, bds.(i)

open Pp

let pp ?(depth=3) e x =
  Term.ll_pr_constr depth (Environ.rel_context e) x

let pph ?depth e x = pp?depth e (extern x)

let print cmds = prerr_endline (string_of_ppcmds cmds)

let rec ps m e s =
  if Subs.kind_of s = ESID 0 then str"-" else
  let rec tol s = match Subs.kind_of s with
  | SHIFT (_,n,s) -> `Shift n :: tol s
  | ESID 0 -> []
  | ESID n -> [`Id n]
  | CONS (_,cv,s) -> `Cons cv :: tol s
  | LIFT (_,n,s) -> `Lift n :: tol s in
  str"{" ++ hv 1 (prlist_with_sep (fun () -> str";"++cut()) (function
  | `Shift n -> str "S " ++ int n
  | `Id n -> str"I " ++ int n
  | `Lift n -> str"L " ++ int n
  | `Cons v -> str"C " ++ prvect_with_sep spc (pcl m e) v) (tol s)) ++ str"}"

and pc m e c =
  if Ctx.kind_of c = Znil then str"-" else
  let rec tol c = match Ctx.kind_of c with
  | Znil -> []
  | Zapp (_,a,c) -> `App a :: tol c
  | Zfix (_,f,c) -> `Fix f :: tol c
  | Zcase (_,ci,t,br,c) -> `Case (t,br) :: tol c
  | Zshift (_,n,c) -> `Shift n :: tol c in
  str"[" ++ hv 1 (prlist_with_sep (fun () -> str";"++cut()) (function 
    | `App cv -> str"A " ++ prvect_with_sep spc (pcl m e) cv
    | `Fix c -> str"F " ++ pcl m e c
    | `Case (p,br) -> str"M " ++ pcl m e p ++ prvect_with_sep spc (pcl m e) br
    | `Shift n -> str"S "++int n) 
    (tol c)) ++ str"]"

and pcl m e cl = if m = 0 then str"…" else let m = m-1 in
 let _,s,t,c = Clos.extern cl in
 if Subs.kind_of s = ESID 0 && Ctx.kind_of c = Znil then
  hv 1 (str"(; " ++ pp e (extern t) ++ str" ;)")
 else
  hv 1 (str"(" ++ ps m e s ++ str";" ++ spc() ++
                pp e (extern t) ++ str";" ++ spc() ++
                pc m e c ++
      str")")

let print_status e s t c = print(pcl 3 e (Clos.intern s t c))

let whd env evars c =
  let rel_context_len, rel_context =
    Sign.fold_rel_context
      (fun (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      (rel_context env) ~init:(0,[]) in
  let var_context =
    Sign.fold_named_context
      (fun (id,b,_) e ->
	 match b with
	   | None -> e
	   | Some body -> (id, body)::e)
       (named_context env) ~init:[] in
  let rec aux subs hd ctx =
(*     print_status env subs hd ctx; *)
    match kind_of hd with
    | HRel i -> (match expand_rel i subs with
        | Inl(n,cl) ->
            let _,subs, t, c = Clos.extern cl in
            aux (Subs.shift n subs) t (Ctx.append c ctx)
        | Inr(k,None) -> subs, intern (mkRel k), ctx
        | Inr(k,Some p) ->
            let subs = Subs.shift (k-p) subs in
            (* XXX lookup not cached *)
            (match assoc_opt rel_context (rel_context_len - p) with
            | Some t -> aux subs (intern (lift p t)) ctx
            | None -> subs, hd, ctx))
    | HVar id ->
            (match assoc_opt var_context id with
            | Some t -> aux subs (intern t) ctx
            | None -> subs, hd, ctx)
(*
    | Evar k -> evars[k]
*)
    | HLetIn (_,_,t,_,bo) -> aux (Subs.cons [|mk_clos ~subs t|] subs) bo ctx
    | HCast (_,t,_,_) -> aux subs t ctx
    | HApp (_,f,a) -> aux subs f (Ctx.app (Array.map (mk_clos ~subs) a) ctx)
    | HCase (_,ci,p,t,br) ->
        aux subs t
          (Ctx.case ci (mk_clos ~subs p) (Array.map (mk_clos ~subs) br) ctx)
    | HFix (_,(_,rarg),_) ->
        let rec fix_params n c = if n <= 0 then Ctx.nil else
          match Ctx.kind_of c with
          | Zapp (_, args, c) ->
              let nargs = Array.length args in
              if n >= nargs then Ctx.app args (fix_params (n - nargs) c)
              else Ctx.app (Array.sub args 0 n) Ctx.nil
(*           | Zshift (_,k,c) -> Ctx.shift k (fix_params n c) *)
          | Znil -> assert false
          | Zcase _ -> assert false
          | Zfix _ -> assert false in
        let rec find_arg n c = match Ctx.kind_of c with
          | Znil -> subs, hd, ctx
          | Zapp (_,args,c) ->
              let nargs = Array.length args in
              if n >= nargs then find_arg (n - nargs) c
              else
                let afterctx =
                  let after = nargs - n - 1 in
                  if after > 0 then Ctx.app (Array.sub args (n + 1) after) c
                  else c in
                let _, s, t, c = Clos.extern args.(n) in
                aux s t (Ctx.append c 
                  (Ctx.fix (mk_clos ~subs ~ctx:(fix_params (rarg-1) ctx) hd)
                  afterctx))
(*           | Zshift (_,_,c) -> find_arg n c *)
          | Zcase _ -> assert false
          | Zfix _ -> assert false in
        find_arg rarg ctx
    | HConstruct (ind, k) ->
        let rec ctx_for_case depth n c = match Ctx.kind_of c with
          | Zapp (_,args,c) when n = 0 ->
              let args = if depth = 0 then args else
                      lift_closure_array depth args in
              Ctx.app args (ctx_for_case depth n c)
          | Zapp (_,args,c) ->
              let nargs = Array.length args in
              if n > nargs then ctx_for_case depth (n - nargs) c
              else if n = nargs then ctx_for_case depth 0 c
              else
                let after = Array.sub args n (nargs - n) in
                ctx_for_case depth 0 (Ctx.app after c)
          | Zshift (_,k,c) -> ctx_for_case (depth - k) n c
          | Zcase (_,_,_,_,c) -> c
          | Znil -> assert false
          | Zfix _ -> assert false in
        let rec ctx_for_fix_arg args = match Ctx.kind_of args with
          | Zfix (_,_,c) -> Ctx.nil
          | Zapp (_,a,c) -> Ctx.app a (ctx_for_fix_arg c)
          | Zshift (_,k,c) -> Ctx.shift k (ctx_for_fix_arg c)
          | Zcase _ -> assert false
          | Znil _ -> assert false in
        let rec find_iota depth c = match Ctx.kind_of c with
          | Zapp (_,_,c) -> find_iota depth c
          | Zshift (_,k,c) -> find_iota (depth + k) c
          | Zcase (_,ci,p,br,_) ->
              let _, subs, b, c = Clos.extern br.(k-1) in
              assert(Ctx.equal c Ctx.nil);
              aux subs b (ctx_for_case depth ci.ci_npar ctx)
          | Zfix (_,fx,c) ->
              let _, fxsubs, fxbo, fctx = Clos.extern fx in
              let fisubs, fi = fix_body fxsubs fxbo in
              aux fisubs fi (Ctx.append fctx
                (Ctx.app [|mk_clos ~subs ~ctx:(ctx_for_fix_arg ctx) hd|] c))
          | Znil -> subs, hd, ctx
        in
          find_iota 0 ctx
    | HLambda (_,_,_,t) -> (* XXX n-ary lambdas in hconstr too! *)
        let rec nlam n acc t = match kind_of t with
          | HLambda (_,_,_,bo) -> nlam (n+1) (t::acc) bo
          | _ -> n, acc, t in
        let nlam, spine, bo = nlam 1 [hd] t in
        let rec eat_lam subs n c =
          if n = nlam then aux subs bo c
          else match Ctx.kind_of c with
          | (Znil | Zcase _ | Zfix _) ->
             if n > 0 then aux subs (List.nth spine (nlam - n)) c
             else subs, hd, c
          | Zshift (_,k,c) -> eat_lam (Subs.shift k subs) n c
          | Zapp (_,args,c) ->
              let nargs = Array.length args in
              if n + nargs = nlam then
                aux (Subs.cons args subs) bo c
              else if n + nargs < nlam then
                eat_lam (Subs.cons args subs) (n + nargs) c
              else
                let before = Array.sub args 0 (nlam - n) in
                let after = Array.sub args (nlam - n) (nargs - (nlam - n)) in
                aux (Subs.cons before subs) bo (Ctx.app after c) in
        eat_lam subs 0 ctx
    | HConst c ->
        let bo =
          try Some (constant_value env c) with NotEvaluableConst _ -> None in
        (match bo with
        | None -> subs, hd, ctx
        | Some bo -> aux subs (intern bo) ctx)
    | HSort _ 
    | HMeta _ 
    | HProd _ 
    | HInd _ 
    | HCoFix _ -> subs, hd, ctx
    | _ -> subs, hd, ctx
  in
  let _, s, t, c = Clos.extern c in
  let s, t, c = aux s t c in
  Clos.intern s t c

let unwind c = clos_to_constr c

(*
let rec convert c1 ctx1 c2 ctx2 =

and convert_ctx
*)

let clos_fconv trans cv_pb l2r evars env t1 t2 =
(*
  Term.H.reset ();
  Clos.reset ();
  UF.reset ();
  print (pp env t1 ++ Pp.spc () ++ Pp.str " ==> " ++ 
    pp env (unwind (whd env evars (mk_clos (Term.H.intern t1)))) ++ str"\n");
*)
  empty_constraint

let red_whd env evars t =
  reset ();
  Clos.reset ();
  UF.reset ();
  let c = mk_clos (intern t) in
  let n = whd env evars.Mini_evd.evars c in
(*
  print (str "mas subs len " ++ int !len);
  let m = ref Intmap.empty in
  List.iter (fun l ->
     let n = List.length l in
     try let k = Intmap.find n !m in m := Intmap.add n (k+1) !m
     with Not_found -> m := Intmap.add n 1 !m)
    (Clos.distribution ());
  Intmap.iter (fun n k -> Printf.eprintf "%4n %n\n" n k ) !m;
*)
  unwind n
