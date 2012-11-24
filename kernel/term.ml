(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* File initially created by Gérard Huet and Thierry Coquand in 1984 *)
(* Extension to inductive constructions by Christine Paulin for Coq V5.6 *)
(* Extension to mutual inductive constructions by Christine Paulin for
   Coq V5.10.2 *)
(* Extension to co-inductive constructions by Eduardo Gimenez *)
(* Optimization of substitution functions by Chet Murthy *)
(* Optimization of lifting functions by Bruno Barras, Mar 1997 *)
(* Hash-consing by Bruno Barras in Feb 1998 *)
(* Restructuration of Coq of the type-checking kernel by Jean-Christophe 
   Filliâtre, 1999 *)
(* Abstraction of the syntax of terms and iterators by Hugo Herbelin, 2000 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)

(* This file defines the internal syntax of the Calculus of
   Inductive Constructions (CIC) terms together with constructors,
   destructors, iterators and basic functions *)

open Errors
open Util
open Pp
open Names
open Univ
open Esubst


type existential_key = int
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)
(* Warning: REVERTcast is not exported to vo-files; as of r14492, it has to *)
(* come after the vo-exported cast_kind so as to be compatible with coqchk *)
type cast_kind = VMcast | DEFAULTcast | REVERTcast

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
type case_printing =
  { ind_nargs : int; (* length of the arity of the inductive type *)
    style     : case_style }
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (* number of pattern vars of each constructor *)
    ci_pp_info    : case_printing (* not interpreted by the kernel *)
  }

(* Sorts. *)

type contents = Pos | Null

type sorts =
  | Prop of contents                      (* proposition types *)
  | Type of universe

let prop_sort = Prop Null
let set_sort = Prop Pos
let type1_sort = Type type1_univ

type sorts_family = InProp | InSet | InType

let family_of_sort = function
  | Prop Null -> InProp
  | Prop Pos -> InSet
  | Type _ -> InType

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

type hash = int
let no_hash = 0

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr hpexistential = hash * existential_key * 'constr array
type ('constr, 'types) prec_declaration =
    name array * 'types array * 'constr array
type ('constr, 'types) hpfixpoint =
    hash * (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) hpcofixpoint =
    hash * int * ('constr, 'types) prec_declaration

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)

type ('constr, 'types) kind_of_hterm =
  | HRel       of int
  | HVar       of identifier
  | HMeta      of metavariable
  | HEvar      of 'constr hpexistential
  | HSort      of sorts
  | HCast      of hash * 'constr * cast_kind * 'types
  | HProd      of hash * name * 'types * 'types
  | HLambda    of hash * name * 'types * 'constr
  | HLetIn     of hash * name * 'constr * 'types * 'constr
  | HApp       of hash * 'constr * 'constr array
  | HConst     of constant
  | HInd       of inductive
  | HConstruct of constructor
  | HCase      of hash * case_info * 'constr * 'constr * 'constr array
  | HFix       of ('constr, 'types) hpfixpoint
  | HCoFix     of ('constr, 'types) hpcofixpoint

(* constr is the fixpoint of the previous type. Requires option
   -rectypes of the Caml compiler to be set *)
type constr = (constr,constr) kind_of_hterm

type existential = existential_key * constr array
type rec_declaration = name array * constr array * constr array
type fixpoint = (int array * int) * rec_declaration
type cofixpoint = int * rec_declaration


(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let rels =
  [|HRel  1;HRel  2;HRel  3;HRel  4;HRel  5;HRel  6;HRel  7; HRel  8;
    HRel  9;HRel 10;HRel 11;HRel 12;HRel 13;HRel 14;HRel 15; HRel 16|]

let mkRel n = if 0<n && n<=16 then rels.(n-1) else HRel n

(* Construct a type *)
let mkProp   = HSort prop_sort
let mkSet    = HSort set_sort
let mkType u = HSort (Type u)
let mkSort   = function
  | Prop Null -> mkProp (* Easy sharing *)
  | Prop Pos -> mkSet
  | s -> HSort s

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast (t1,k2,t2) =
  match t1 with
  | HCast (_,c,k1, _) when k1 = VMcast & k1 = k2 -> HCast (no_hash,c,k1,t2)
  | _ -> HCast (no_hash,t1,k2,t2)

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = HProd (no_hash,x,t1,t2)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = HLambda (no_hash,x,t1,t2)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = HLetIn (no_hash,x,c1,t,c2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at least one argument and the
   function is not itself an applicative term *)
let mkApp (f, a) =
  if Array.length a = 0 then f else
    match f with
      | HApp (_,g, cl) -> HApp (no_hash, g, Array.append cl a)
      | _ -> HApp (no_hash, f, a)

(* Constructs a constant *)
let mkConst c = HConst c

(* Constructs an existential variable *)
let mkEvar (e,v) = HEvar (no_hash, e, v)

(* Constructs the ith (co)inductive type of the block named kn *)
let mkInd m = HInd m

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. The array of terms correspond to the variables
   introduced in the section *)
let mkConstruct c = HConstruct c

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase (ci, p, c, ac) = HCase (no_hash, ci, p, c, ac)

(* If recindxs = [|i1,...in|]
      funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkFix ((recindxs,i),(funnames,typarray,bodies))

   constructs the ith function of the block

    Fixpoint f1 [ctx1] : t1 := b1
    with     f2 [ctx2] : t2 := b2
    ...
    with     fn [ctxn] : tn := bn.

   where the lenght of the jth context is ij.
*)

let mkFix (ra,d) = HFix (no_hash,ra,d)

(* If funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkCoFix (i,(funnames,typsarray,bodies))

   constructs the ith function of the block

    CoFixpoint f1 : t1 := b1
    with       f2 : t2 := b2
    ...
    with       fn : tn := bn.
*)
let mkCoFix (i,d) = HCoFix (no_hash, i, d)

(* Constructs an existential variable named "?n" *)
let mkMeta  n =  HMeta n

(* Constructs a Variable named id *)
let mkVar id = HVar id


(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

type 'constr pexistential = existential_key * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of identifier
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of sorts
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of name * 'types * 'types
  | Lambda    of name * 'types * 'constr
  | LetIn     of name * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint

let kind_of_term = function
  | HRel i              -> Rel i
  | HVar v              -> Var v
  | HMeta m             -> Meta m
  | HEvar (_,e,v)       -> Evar (e,v)
  | HSort s             -> Sort s
  | HCast (_,t,c,ty)    -> Cast (t,c,ty)
  | HProd (_,n,ty,c)    -> Prod(n,ty,c)
  | HLambda (_,n,ty,c)  -> Lambda(n,ty,c)
  | HLetIn (_,n,t,ty,c) -> LetIn(n,t,ty,c)
  | HApp (_,hd,tl)      -> App(hd,tl)
  | HConst c            -> Const c
  | HInd i              -> Ind i
  | HConstruct c        -> Construct c
  | HCase (_,i,t,rty,b) -> Case(i,t,rty,b)
  | HFix (_,ra,d)       -> Fix(ra,d)
  | HCoFix (_,i,d)      -> CoFix(i,d)

(* Experimental, used in Presburger contrib *)
type ('constr, 'types) kind_of_type =
  | SortType   of sorts
  | CastType   of 'types * 'types
  | ProdType   of name * 'types * 'types
  | LetInType  of name * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

let kind_of_type = function
  | HSort s -> SortType s
  | HCast (_,c,_,t) -> CastType (c, t)
  | HProd (_,na,t,c) -> ProdType (na, t, c)
  | HLetIn (_,na,b,t,c) -> LetInType (na, b, t, c)
  | HApp (_,c,l) -> AtomicType (c, l)
  | (HRel _ | HMeta _ | HVar _ | HEvar _ | HConst _ | HCase _ | HFix _ | HCoFix _ | HInd _ as c)
    -> AtomicType (c,[||])
  | (HLambda _ | HConstruct _) -> failwith "Not a type"

(**********************************************************************)
(*          Non primitive term destructors                            *)
(**********************************************************************)

(* Destructor operations : partial functions
   Raise invalid_arg "dest*" if the const has not the expected form *)

(* Destructs a DeBrujin index *)
let destRel = function
  | HRel n -> n
  | _ -> invalid_arg "destRel"

(* Destructs an existential variable *)
let destMeta = function
  | HMeta n -> n
  | _ -> invalid_arg "destMeta"

let isMeta = function HMeta _ -> true | _ -> false
let isMetaOf mv = function HMeta mv' -> mv = mv' | _ -> false

(* Destructs a variable *)
let destVar = function
  | HVar id -> id
  | _ -> invalid_arg "destVar"

(* Destructs a type *)
let isSort = function
  | HSort s -> true
  | _ -> false

let destSort = function
  | HSort s -> s
  | _ -> invalid_arg "destSort"

let rec isprop = function
  | HSort (Prop _) -> true
  | HCast (_,c,_,_) -> isprop c
  | _ -> false

let rec is_Prop = function
  | HSort (Prop Null) -> true
  | HCast (_,c,_,_) -> is_Prop c
  | _ -> false

let rec is_Set = function
  | HSort (Prop Pos) -> true
  | HCast (_,c,_,_) -> is_Set c
  | _ -> false

let rec is_Type = function
  | HSort (Type _) -> true
  | HCast (_,c,_,_) -> is_Type c
  | _ -> false

let is_small = function
  | Prop _ -> true
  | _ -> false

let iskind c = isprop c or is_Type c

(* Tests if an evar *)
let isEvar = function HEvar _ -> true | _ -> false

let isEvar_or_Meta = function
  | HEvar _ | HMeta _ -> true
  | _ -> false

(* Destructs a casted term *)
let destCast = function
  | HCast (_,t1,k,t2) -> (t1,k,t2)
  | _ -> invalid_arg "destCast"

let isCast = function HCast _ -> true | _ -> false


(* Tests if a de Bruijn index *)
let isRel = function HRel _ -> true | _ -> false
let isRelN n = function HRel n' -> n = n' | _ -> false

(* Tests if a variable *)
let isVar = function HVar _ -> true | _ -> false
let isVarId id = function HVar id' -> id = id' | _ -> false

(* Tests if an inductive *)
let isInd = function HInd _ -> true | _ -> false

(* Destructs the product (x:t1)t2 *)
let destProd = function
  | HProd (_,x,t1,t2) -> (x,t1,t2)
  | _ -> invalid_arg "destProd"

let isProd = function HProd _ -> true | _ -> false

(* Destructs the abstraction [x:t1]t2 *)
let destLambda = function
  | HLambda (_,x,t1,t2) -> (x,t1,t2)
  | _ -> invalid_arg "destLambda"

let isLambda = function HLambda _ -> true | _ -> false

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn = function
  | HLetIn (_,x,b,t1,t2) -> (x,b,t1,t2)
  | _ -> invalid_arg "destLetIn"

let isLetIn = function HLetIn _ -> true | _ -> false

(* Destructs an application *)
let destApp = function
  | HApp (_,f,a) -> (f, a)
  | _ -> invalid_arg "destApplication"

let destApplication = destApp

let isApp = function HApp _ -> true | _ -> false

(* Destructs a constant *)
let destConst = function
  | HConst kn -> kn
  | _ -> invalid_arg "destConst"

let isConst = function HConst _ -> true | _ -> false

(* Destructs an existential variable *)
let destEvar = function
  | HEvar (_, kn, a) -> kn, a
  | _ -> invalid_arg "destEvar"

(* Destructs a (co)inductive type named kn *)
let destInd = function
  | HInd (kn, a as r) -> r
  | _ -> invalid_arg "destInd"

(* Destructs a constructor *)
let destConstruct = function
  | HConstruct (kn, a as r) -> r
  | _ -> invalid_arg "dest"

let isConstruct = function HConstruct _ -> true | _ -> false

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase = function
  | HCase (_,ci,p,c,v) -> (ci,p,c,v)
  | _ -> anomaly "destCase"

let isCase = function HCase _ -> true | _ -> false

let destFix = function
  | HFix (_,ra,d) -> ra,d
  | _ -> invalid_arg "destFix"

let isFix = function HFix _ -> true | _ -> false

let destCoFix = function
  | HCoFix (_,i,d) -> i,d
  | _ -> invalid_arg "destCoFix"

let isCoFix = function HCoFix _ -> true | _ -> false

(******************************************************************)
(* Cast management                                                *)
(******************************************************************)

let rec strip_outer_cast = function
  | HCast (_,c,_,_) -> strip_outer_cast c
  | c -> c

(* Fonction spéciale qui laisse les cast clés sous les Fix ou les Case *)

let under_outer_cast f = function
  | HCast (_,b,k,t) -> mkCast (f b, k, f t)
  | c -> f c

let rec under_casts f = function
  | HCast (_,c,k,t) -> mkCast (under_casts f c, k, t)
  | c            -> f c

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

(* flattens application lists throwing casts in-between *)
let collapse_appl = function
  | HApp (_,f,cl) ->
      let rec collapse_rec f cl2 =
        match strip_outer_cast f with
	| HApp (_,g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| _ -> mkApp (f,cl2)
      in
      collapse_rec f cl
  | c -> c

let decompose_app = function
    | HApp (_,f,cl) -> (f, Array.to_list cl)
    | c -> (c,[])

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold_constr f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold_constr f acc = function
  | (HRel _ | HMeta _ | HVar _   | HSort _ | HConst _ | HInd _
    | HConstruct _) -> acc
  | HCast (_,c,_,t) -> f (f acc c) t
  | HProd (_,_,t,c) -> f (f acc t) c
  | HLambda (_,_,t,c) -> f (f acc t) c
  | HLetIn (_,_,b,t,c) -> f (f (f acc b) t) c
  | HApp (_,c,l) -> Array.fold_left f (f acc c) l
  | HEvar (_,_,l) -> Array.fold_left f acc l
  | HCase (_,_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | HFix (_,_,(lna,tl,bl)) ->
      let fd = Array.map3 (fun na t b -> (na,t,b)) lna tl bl in
      Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd
  | HCoFix (_,_,(lna,tl,bl)) ->
      let fd = Array.map3 (fun na t b -> (na,t,b)) lna tl bl in
      Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd

(* [iter_constr f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter_constr f = function
  | (HRel _ | HMeta _ | HVar _   | HSort _ | HConst _ | HInd _
    | HConstruct _) -> ()
  | HCast (_,c,_,t) -> f c; f t
  | HProd (_,_,t,c) -> f t; f c
  | HLambda (_,_,t,c) -> f t; f c
  | HLetIn (_,_,b,t,c) -> f b; f t; f c
  | HApp (_,c,l) -> f c; Array.iter f l
  | HEvar (_,_,l) -> Array.iter f l
  | HCase (_,_,p,c,bl) -> f p; f c; Array.iter f bl
  | HFix (_,_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | HCoFix (_,_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl

(* [iter_constr_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_constr_with_binders g f n = function
  | (HRel _ | HMeta _ | HVar _   | HSort _ | HConst _ | HInd _
    | HConstruct _) -> ()
  | HCast (_,c,_,t) -> f n c; f n t
  | HProd (_,_,t,c) -> f n t; f (g n) c
  | HLambda (_,_,t,c) -> f n t; f (g n) c
  | HLetIn (_,_,b,t,c) -> f n b; f n t; f (g n) c
  | HApp (_,c,l) -> f n c; Array.iter (f n) l
  | HEvar (_,_,l) -> Array.iter (f n) l
  | HCase (_,_,p,c,bl) -> f n p; f n c; Array.iter (f n) bl
  | HFix (_,_,(_,tl,bl)) ->
      Array.iter (f n) tl;
      Array.iter (f (iterate g (Array.length tl) n)) bl
  | HCoFix (_,_,(_,tl,bl)) ->
      Array.iter (f n) tl;
      Array.iter (f (iterate g (Array.length tl) n)) bl

(* [map_constr f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map_constr f = function
  | (HRel _ | HMeta _ | HVar _   | HSort _ | HConst _ | HInd _
    | HConstruct _) as c -> c
  | HCast (_,c,k,t) -> mkCast (f c, k, f t)
  | HProd (_,na,t,c) -> mkProd (na, f t, f c)
  | HLambda (_,na,t,c) -> mkLambda (na, f t, f c)
  | HLetIn (_,na,b,t,c) -> mkLetIn (na, f b, f t, f c)
  | HApp (_,c,l) -> mkApp (f c, Array.map f l)
  | HEvar (_,e,l) -> mkEvar (e, Array.map f l)
  | HCase (_,ci,p,c,bl) -> mkCase (ci, f p, f c, Array.map f bl)
  | HFix (_,ln,(lna,tl,bl)) ->
      mkFix (ln,(lna,Array.map f tl,Array.map f bl))
  | HCoFix(_,ln,(lna,tl,bl)) ->
      mkCoFix (ln,(lna,Array.map f tl,Array.map f bl))

(* [map_constr_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_constr_with_binders g f l = function
  | (HRel _ | HMeta _ | HVar _ | HSort _ | HConst _ | HInd _
    | HConstruct _) as c -> c
  | HCast (_,c,k,t) -> mkCast (f l c, k, f l t)
  | HProd (_,na,t,c) -> mkProd (na, f l t, f (g l) c)
  | HLambda (_,na,t,c) -> mkLambda (na, f l t, f (g l) c)
  | HLetIn (_,na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g l) c)
  | HApp (_,c,al) -> mkApp (f l c, Array.map (f l) al)
  | HEvar (_,e,al) -> mkEvar (e, Array.map (f l) al)
  | HCase (_,ci,p,c,bl) -> mkCase (ci, f l p, f l c, Array.map (f l) bl)
  | HFix (_,ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | HCoFix(_,ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))

(* [compare_constr f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)



let compare_constr f t1 t2 =
  match t1, t2 with
  | HRel n1, HRel n2 -> n1 = n2
  | HMeta m1, HMeta m2 -> m1 = m2
  | HVar id1, HVar id2 -> id1 = id2
  | HSort s1, HSort s2 -> s1 = s2
  | HCast (_,c1,_,_), _ -> f c1 t2
  | _, HCast (_,c2,_,_) -> f t1 c2
  | HProd (_,_,t1,c1), HProd (_,_,t2,c2) -> f t1 t2 && f c1 c2
  | HLambda (_,_,t1,c1), HLambda (_,_,t2,c2) -> f t1 t2 && f c1 c2
  | HLetIn (_,_,b1,t1,c1),HLetIn (_,_,b2,t2,c2) -> f b1 b2 && f t1 t2 && f c1 c2
  | HApp (_,c1,l1), _ when isCast c1 -> f (mkApp (pi1 (destCast c1),l1)) t2
  | _, HApp (_,c2,l2) when isCast c2 -> f t1 (mkApp (pi1 (destCast c2),l2))
  | HApp (_,c1,l1), HApp (_,c2,l2) ->
    Array.length l1 = Array.length l2 &&
      f c1 c2 && Array.for_all2 f l1 l2
  | HEvar (_,e1,l1), HEvar (_,e2,l2) -> e1 = e2 && Array.for_all2 f l1 l2
  | HConst c1, HConst c2 -> eq_constant c1 c2
  | HInd c1, HInd c2 -> eq_ind c1 c2
  | HConstruct c1, HConstruct c2 -> eq_constructor c1 c2
  | HCase (_,_,p1,c1,bl1), HCase (_,_,p2,c2,bl2) ->
      f p1 p2 && f c1 c2 && Array.for_all2 f bl1 bl2
  | HFix (_,ln1,(_,tl1,bl1)), HFix (_,ln2,(_,tl2,bl2)) ->
      ln1 = ln2 && Array.for_all2 f tl1 tl2 && Array.for_all2 f bl1 bl2
  | HCoFix(_,ln1,(_,tl1,bl1)), HCoFix(_,ln2,(_,tl2,bl2)) ->
      ln1 = ln2 && Array.for_all2 f tl1 tl2 && Array.for_all2 f bl1 bl2
  | _ -> false

(*******************************)
(*  alpha conversion functions *)
(*******************************)

(* alpha conversion : ignore print names and casts *)

let rec eq_constr m n =
  (m==n) or
  compare_constr eq_constr m n

let eq_constr m n = eq_constr m n (* to avoid tracing a recursive fun *)

let constr_ord_int f t1 t2 =
  let (=?) f g i1 i2 j1 j2=
    let c=f i1 i2 in
    if c=0 then g j1 j2 else c in
  let (==?) fg h i1 i2 j1 j2 k1 k2=
    let c=fg i1 i2 j1 j2 in
    if c=0 then h k1 k2 else c in
  match t1, t2 with
    | HRel n1, HRel n2 -> n1 - n2
    | HMeta m1, HMeta m2 -> m1 - m2
    | HVar id1, HVar id2 -> id_ord id1 id2
    | HSort s1, HSort s2 -> Pervasives.compare s1 s2
    | HCast (_,c1,_,_), _ -> f c1 t2
    | _, HCast (_,c2,_,_) -> f t1 c2
    | HProd (_,_,t1,c1), HProd (_,_,t2,c2)
    | HLambda (_,_,t1,c1), HLambda (_,_,t2,c2) ->
	(f =? f) t1 t2 c1 c2
    | HLetIn (_,_,b1,t1,c1), HLetIn (_,_,b2,t2,c2) ->
	((f =? f) ==? f) b1 b2 t1 t2 c1 c2
    | HApp (_,c1,l1), _ when isCast c1 -> f (mkApp (pi1 (destCast c1),l1)) t2
    | _, HApp (_,c2,l2) when isCast c2 -> f t1 (mkApp (pi1 (destCast c2),l2))
    | HApp (_,c1,l1), HApp (_,c2,l2) -> (f =? (Array.compare f)) c1 c2 l1 l2
    | HEvar (_,e1,l1), HEvar (_,e2,l2) ->
	((-) =? (Array.compare f)) e1 e2 l1 l2
    | HConst c1, HConst c2 -> kn_ord (canonical_con c1) (canonical_con c2)
    | HInd (spx, ix), HInd (spy, iy) ->
	let c = ix - iy in if c = 0 then kn_ord (canonical_mind spx) (canonical_mind spy) else c
    | HConstruct ((spx, ix), jx), HConstruct ((spy, iy), jy) ->
	let c = jx - jy in if c = 0 then
	  (let c = ix - iy in if c = 0 then kn_ord (canonical_mind spx) (canonical_mind spy) else c)
	else c
    | HCase (_,_,p1,c1,bl1), HCase (_,_,p2,c2,bl2) ->
	((f =? f) ==? (Array.compare f)) p1 p2 c1 c2 bl1 bl2
    | HFix (_,ln1,(_,tl1,bl1)), HFix (_,ln2,(_,tl2,bl2)) ->
	((Pervasives.compare =? (Array.compare f)) ==? (Array.compare f))
	ln1 ln2 tl1 tl2 bl1 bl2
    | HCoFix(_,ln1,(_,tl1,bl1)), HCoFix(_,ln2,(_,tl2,bl2)) ->
	((Pervasives.compare =? (Array.compare f)) ==? (Array.compare f))
	ln1 ln2 tl1 tl2 bl1 bl2
    | t1, t2 -> Pervasives.compare t1 t2

let rec constr_ord m n=
  constr_ord_int constr_ord m n

(***************************************************************************)
(*     Type of assumptions                                                 *)
(***************************************************************************)

type types = constr

type strategy = types option

type named_declaration = identifier * constr option * types
type rel_declaration = name * constr option * types

let map_named_declaration f (id, (v : strategy), ty) = (id, Option.map f v, f ty)
let map_rel_declaration = map_named_declaration

let fold_named_declaration f (_, v, ty) a = f ty (Option.fold_right f v a)
let fold_rel_declaration = fold_named_declaration

let exists_named_declaration f (_, v, ty) = Option.cata f false v || f ty
let exists_rel_declaration f (_, v, ty) = Option.cata f false v || f ty

let for_all_named_declaration f (_, v, ty) = Option.cata f true v && f ty
let for_all_rel_declaration f (_, v, ty) = Option.cata f true v && f ty

let eq_named_declaration (i1, c1, t1) (i2, c2, t2) =
  id_ord i1 i2 = 0 && Option.Misc.compare eq_constr c1 c2 && eq_constr t1 t2

let eq_rel_declaration (n1, c1, t1) (n2, c2, t2) =
  n1 = n2 && Option.Misc.compare eq_constr c1 c2 && eq_constr t1 t2

(***************************************************************************)
(*     Type of local contexts (telescopes)                                 *)
(***************************************************************************)

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices (to represent bound variables) *)

type rel_context = rel_declaration list

let empty_rel_context = []

let add_rel_decl d ctxt = d::ctxt

let rec lookup_rel n sign =
  match n, sign with
  | 1, decl :: _ -> decl
  | n, _ :: sign -> lookup_rel (n-1) sign
  | _, []        -> raise Not_found

let rel_context_length = List.length

let rel_context_nhyps hyps =
  let rec nhyps acc = function
    | [] -> acc
    | (_,None,_)::hyps -> nhyps (1+acc) hyps
    | (_,Some _,_)::hyps -> nhyps acc hyps in
  nhyps 0 hyps

(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(*********************)
(*     Occurring     *)
(*********************)

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n = function
    | HRel m -> if m>n then raise LocalOccur
    | c -> iter_constr_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

let closed0 = closedn 0

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n = function
    | HRel m -> if m = n then raise LocalOccur
    | c -> iter_constr_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n = function
    | HRel(p) -> if n<=p && p<n+m then raise LocalOccur
    | c        -> iter_constr_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

let noccur_with_meta n m term =
  let rec occur_rec n = function
    | HRel p -> if n<=p & p<n+m then raise LocalOccur
    | HApp(_,f,cl) as c ->
	(match f with
           | HCast (_,c,_,_) when isMeta c -> ()
           | HMeta _ -> ()
	   | _ -> iter_constr_with_binders succ occur_rec n c)
    | HEvar _ -> ()
    | c -> iter_constr_with_binders succ occur_rec n c
  in
  try (occur_rec n term; true) with LocalOccur -> false


(*********************)
(*      Lifting      *)
(*********************)

(* The generic lifting function *)
let rec exliftn el = function
  | HRel i -> mkRel(reloc_rel i el)
  | c -> map_constr_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn n k =
  match el_liftn (pred k) (el_shft n el_id) with
    | ELID -> (fun c -> c)
    | el -> exliftn el

let lift n = liftn n 1

(*********************)
(*   Substituting    *)
(*********************)

(* (subst1 M c) substitutes M for Rel(1) in c
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let rec lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
        s.sinfo <- if closed0 s.sit then Closed else Open;
        lift_substituend depth s

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n c =
  let lv = Array.length lamv in
  if lv = 0 then c
  else
    let rec substrec depth = function
      | HRel k as c ->
          if k<=depth then c
          else if k-depth <= lv then lift_substituend depth lamv.(k-depth-1)
          else mkRel (k-lv)
      | c -> map_constr_with_binders succ substrec depth c in
    substrec n c

(*
let substkey = Profile.declare_profile "substn_many";;
let substn_many lamv n c = Profile.profile3 substkey substn_many lamv n c;;
*)

let substnl laml n =
  substn_many (Array.map make_substituend (Array.of_list laml)) n
let substl laml = substnl laml 0
let subst1 lam = substl [lam]

let substnl_decl laml k = map_rel_declaration (substnl laml k)
let substl_decl laml = substnl_decl laml 0
let subst1_decl lam = substl_decl [lam]
let substl_named_decl = substl_decl
let subst1_named_decl = subst1_decl

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (((id,{ sit = v }) as s)::tl) when isVar v ->
      if id = destVar v then thin_val tl else s::(thin_val tl)
  | h::tl -> h::(thin_val tl)

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist =
  let var_alist =
    List.map (fun (str,c) -> (str,make_substituend c)) var_alist in
  let var_alist = thin_val var_alist in
  let rec substrec n = function
    | HVar x as c ->
        (try lift_substituend n (List.assoc x var_alist)
         with Not_found -> c)
    | c -> map_constr_with_binders succ substrec n c
  in
  if var_alist = [] then (function x -> x) else substrec 0

(*
let repvarkey = Profile.declare_profile "replace_vars";;
let replace_vars vl c = Profile.profile2 repvarkey replace_vars vl c ;;
*)

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = replace_vars [(str, mkRel 1)]

(* (subst_vars [id1;...;idn] t) substitute (VAR idj) by (Rel j) in t *)
let substn_vars p vars =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var,mkRel n)::l)) (p,[]) vars
  in replace_vars (List.rev subst)

let subst_vars = substn_vars 1

(***************************)
(* Other term constructors *)
(***************************)

let mkNamedProd id typ c = mkProd (Name id, typ, subst_var id c)
let mkNamedLambda id typ c = mkLambda (Name id, typ, subst_var id c)
let mkNamedLetIn id c1 t c2 = mkLetIn (Name id, c1, t, subst_var id c2)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedProd_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id t c
    | Some b -> mkNamedLetIn id b t c

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
let mkProd_wo_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na,  t, c)
    | Some b -> subst1 b c

let mkNamedProd_wo_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id t c
    | Some b -> subst1 b (subst_var id c)

(* non-dependent product t1 -> t2 *)
let mkArrow t1 t2 = mkProd (Anonymous, t1, t2)

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
let mkLambda_or_LetIn (na,body,t) c =
  match body with
    | None -> mkLambda (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedLambda_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedLambda id t c
    | Some b -> mkNamedLetIn id b t c

(* prodn n [xn:Tn;..;x1:T1;Gamma] b = (x1:T1)..(xn:Tn)b *)
let prodn n env b =
  let rec prodrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, mkProd (v,t,b))
    | _ -> assert false
  in
  prodrec (n,env,b)

(* compose_prod [xn:Tn;..;x1:T1] b = (x1:T1)..(xn:Tn)b *)
let compose_prod l b = prodn (List.length l) l b

(* lamn n [xn:Tn;..;x1:T1;Gamma] b = [x1:T1]..[xn:Tn]b *)
let lamn n env b =
  let rec lamrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> lamrec (n-1,  l, mkLambda (v,t,b))
    | _ -> assert false
  in
  lamrec (n,env,b)

(* compose_lam [xn:Tn;..;x1:T1] b = [x1:T1]..[xn:Tn]b *)
let compose_lam l b = lamn (List.length l) l b

let applist (f,l) = mkApp (f, Array.of_list l)

let applistc f l = mkApp (f, Array.of_list l)

let appvect = mkApp

let appvectc f l = mkApp (f,l)

(* to_lambda n (x1:T1)...(xn:Tn)T =
 * [x1:T1]...[xn:Tn]T *)
let rec to_lambda n prod =
  if n = 0 then
    prod
  else
    match prod with
      | HProd (_,na,ty,bd) -> mkLambda (na,ty,to_lambda (n-1) bd)
      | HCast (_,c,_,_) -> to_lambda n c
      | _   -> errorlabstrm "to_lambda" (mt ())

let rec to_prod n lam =
  if n=0 then
    lam
  else
    match lam with
      | HLambda (_,na,ty,bd) -> mkProd (na,ty,to_prod (n-1) bd)
      | HCast (_,c,_,_) -> to_prod n c
      | _   -> errorlabstrm "to_prod" (mt ())

(* pseudo-reduction rule:
 * [prod_app  s (Prod(_,B)) N --> B[N]
 * with an strip_outer_cast on the first argument to produce a product *)

let prod_app t n =
  match strip_outer_cast t with
    | HProd (_,_,_,b) -> subst1 n b
    | _ ->
	errorlabstrm "prod_app"
	  (str"Needed a product, but didn't find one" ++ fnl ())


(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_appvect t nL = Array.fold_left prod_app t nL

(* prod_applist T [ a1 ; ... ; an ] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn = List.fold_left (fun c d -> mkLambda_or_LetIn d c)

(*********************************)
(* Other term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod =
  let rec prodec_rec l = function
    | HProd (_,x,t,c) -> prodec_rec ((x,t)::l) c
    | HCast (_,c,_,_)   -> prodec_rec l c
    | c              -> l,c
  in
  prodec_rec []

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam =
  let rec lamdec_rec l = function
    | HLambda (_,x,t,c) -> lamdec_rec ((x,t)::l) c
    | HCast (_,c,_,_)     -> lamdec_rec l c
    | c                -> l,c
  in
  lamdec_rec []

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then error "decompose_prod_n: integer parameter must be positive";
  let rec prodec_rec l n c =
    if n=0 then l,c
    else match c with
      | HProd (_,x,t,c) -> prodec_rec ((x,t)::l) (n-1) c
      | HCast (_,c,_,_)   -> prodec_rec l n c
      | _ -> error "decompose_prod_n: not enough products"
  in
  prodec_rec [] n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n n =
  if n < 0 then error "decompose_lam_n: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if n=0 then l,c
    else match c with
      | HLambda (_,x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | HCast (_,c,_,_)     -> lamdec_rec l n c
      | _ -> error "decompose_lam_n: not enough abstractions"
  in
  lamdec_rec [] n

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_assum =
  let rec prodec_rec l c =
    match c with
    | HProd (_,x,t,c)    -> prodec_rec (add_rel_decl (x,None,t) l) c
    | HLetIn (_,x,b,t,c) -> prodec_rec (add_rel_decl (x,Some b,t) l) c
    | HCast (_,c,_,_)      -> prodec_rec l c
    | c               -> l,c
  in
  prodec_rec empty_rel_context

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam_assum =
  let rec lamdec_rec l c =
    match c with
    | HLambda (_,x,t,c)  -> lamdec_rec (add_rel_decl (x,None,t) l) c
    | HLetIn (_,x,b,t,c) -> lamdec_rec (add_rel_decl (x,Some b,t) l) c
    | HCast (_,c,_,_)      -> lamdec_rec l c
    | c               -> l,c
  in
  lamdec_rec empty_rel_context

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n_assum n =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c =
    if n=0 then l,c
    else match c with
    | HProd (_,x,t,c)    -> prodec_rec (add_rel_decl (x,None,t) l) (n-1) c
    | HLetIn (_,x,b,t,c) -> prodec_rec (add_rel_decl (x,Some b,t) l) (n-1) c
    | HCast (_,c,_,_)      -> prodec_rec l n c
    | _ -> error "decompose_prod_n_assum: not enough assumptions"
  in
  prodec_rec empty_rel_context n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T)
   Lets in between are not expanded but turn into local definitions,
   but n is the actual number of destructurated lambdas.  *)
let decompose_lam_n_assum n =
  if n < 0 then
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if n=0 then l,c
    else match c with
    | HLambda (_,x,t,c)  -> lamdec_rec (add_rel_decl (x,None,t) l) (n-1) c
    | HLetIn (_,x,b,t,c) -> lamdec_rec (add_rel_decl (x,Some b,t) l) n c
    | HCast (_,c,_,_)      -> lamdec_rec l n c
    | c -> error "decompose_lam_n_assum: not enough abstractions"
  in
  lamdec_rec empty_rel_context n

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
let nb_lam =
  let rec nbrec n = function
    | HLambda (_,_,_,c) -> nbrec (n+1) c
    | HCast (_,c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0

(* similar to nb_lam, but gives the number of products instead *)
let nb_prod =
  let rec nbrec n = function
    | HProd (_,_,_,c) -> nbrec (n+1) c
    | HCast (_,c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0

let prod_assum t = fst (decompose_prod_assum t)
let prod_n_assum n t = fst (decompose_prod_n_assum n t)
let strip_prod_assum t = snd (decompose_prod_assum t)
let strip_prod t = snd (decompose_prod t)
let strip_prod_n n t = snd (decompose_prod_n n t)
let lam_assum t = fst (decompose_lam_assum t)
let lam_n_assum n t = fst (decompose_lam_n_assum n t)
let strip_lam_assum t = snd (decompose_lam_assum t)
let strip_lam t = snd (decompose_lam t)
let strip_lam_n n t = snd (decompose_lam_n n t)

(***************************)
(* Arities                 *)
(***************************)

(* An "arity" is a term of the form [[x1:T1]...[xn:Tn]s] with [s] a sort.
   Such a term can canonically be seen as the pair of a context of types
   and of a sort *)

type arity = rel_context * sorts

let destArity =
  let rec prodec_rec l c =
    match c with
    | HProd (_,x,t,c)    -> prodec_rec ((x,None,t)::l) c
    | HLetIn (_,x,b,t,c) -> prodec_rec ((x,Some b,t)::l) c
    | HCast (_,c,_,_)    -> prodec_rec l c
    | HSort s            -> l,s
    | _                  -> anomaly "destArity: not an arity"
  in
  prodec_rec []

let mkArity (sign,s) = it_mkProd_or_LetIn (mkSort s) sign

let rec isArity c =
  match c with
  | HProd (_,_,_,c)    -> isArity c
  | HLetIn (_,_,b,_,c) -> isArity (subst1 b c)
  | HCast (_,c,_,_)    -> isArity c
  | HSort _            -> true
  | _                  -> false

(*******************)
(*  hash-consing   *)
(*******************)

(* Hash-consing of [constr] does not use the module [Hashcons] because
   [Hashcons] is not efficient on deep tree-like data
   structures. Indeed, [Hashcons] is based the (very efficient)
   generic hash function [Hashtbl.hash], which computes the hash key
   through a depth bounded traversal of the data structure to be
   hashed. As a consequence, for a deep [constr] like the natural
   number 1000 (S (S (... (S O)))), the same hash is assigned to all
   the sub [constr]s greater than the maximal depth handled by
   [Hashtbl.hash]. This entails a huge number of collisions in the
   hash table and leads to cubic hash-consing in this worst-case.

   In order to compute a hash key that is independent of the data
   structure depth while being constant-time, an incremental hashing
   function must be devised. A standard implementation creates a cache
   of the hashing function by decorating each node of the hash-consed
   data structure with its hash key. In that case, the hash function
   can deduce the hash key of a toplevel data structure by a local
   computation based on the cache held on its substructures.
   Unfortunately, this simple implementation introduces a space
   overhead that is damageable for the hash-consing of small [constr]s
   (the most common case). One can think of an heterogeneous
   distribution of caches on smartly chosen nodes, but this is forbidden
   by the use of generic equality in Coq source code. (Indeed, this forces
   each [constr] to have a unique canonical representation.)

   Given that hash-consing proceeds inductively, we can nonetheless
   computes the hash key incrementally during hash-consing by changing
   a little the signature of the hash-consing function: it now returns
   both the hash-consed term and its hash key. This simple solution is
   implemented in the following code: it does not introduce a space
   overhead in [constr], that's why the efficiency is unchanged for
   small [constr]s. Besides, it does handle deep [constr]s without
   introducing an unreasonable number of collisions in the hash table.
   Some benchmarks make us think that this implementation of
   hash-consing is linear in the size of the hash-consed data
   structure for our daily use of Coq.
*)


let array_eqeq t1 t2 =
  t1 == t2 ||
  (Array.length t1 = Array.length t2 &&
   let rec aux i =
     (i = Array.length t1) || (t1.(i) == t2.(i) && aux (i + 1))
   in aux 0)

let equals_constr t1 t2 =
  match t1, t2 with
    | HRel n1, HRel n2 -> n1 == n2
    | HMeta m1, HMeta m2 -> m1 == m2
    | HVar id1, HVar id2 -> id1 == id2
    | HSort s1, HSort s2 -> s1 == s2
    | HCast (_,c1,k1,t1), HCast (_,c2,k2,t2) -> c1 == c2 && k1 == k2 && t1 == t2
    | HProd (_,n1,t1,c1), HProd (_,n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
    | HLambda (_,n1,t1,c1), HLambda (_,n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
    | HLetIn (_,n1,b1,t1,c1), HLetIn (_,n2,b2,t2,c2) ->
      n1 == n2 && b1 == b2 && t1 == t2 && c1 == c2
    | HApp (_,c1,l1), HApp (_,c2,l2) -> c1 == c2 && array_eqeq l1 l2
    | HEvar (_,e1,l1), HEvar (_,e2,l2) -> e1 = e2 && array_eqeq l1 l2
    | HConst c1, HConst c2 -> c1 == c2
    | HInd (sp1,i1), HInd (sp2,i2) -> sp1 == sp2 && i1 = i2
    | HConstruct ((sp1,i1),j1), HConstruct ((sp2,i2),j2) ->
      sp1 == sp2 && i1 = i2 && j1 = j2
    | HCase (_,ci1,p1,c1,bl1), HCase (_,ci2,p2,c2,bl2) ->
      ci1 == ci2 && p1 == p2 && c1 == c2 && array_eqeq bl1 bl2
    | HFix (_,ln1,(lna1,tl1,bl1)), HFix (_,ln2,(lna2,tl2,bl2)) ->
      ln1 = ln2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | HCoFix(_,ln1,(lna1,tl1,bl1)), HCoFix(_,ln2,(lna2,tl2,bl2)) ->
      ln1 = ln2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | _ -> false

(** Note that the following Make has the side effect of creating
    once and for all the table we'll use for hash-consing all constr *)

module HashsetTerm = Hashset.Make(
  struct type t = constr let equal = equals_constr end
)

let term_table = ref (HashsetTerm.create 19991)
let reset () =
  term_table := (HashsetTerm.create 19991)

(* The associative table to hashcons terms. *)

open Hashset.Combine

(* [hcons_term hash_consing_functions constr] computes an hash-consed
   representation for [constr] using [hash_consing_functions] on
   leaves. *)
let hcons_term (sh_sort,sh_ci,sh_construct,sh_ind,sh_con,sh_na,sh_id) =

  (* Note : we hash-cons constr arrays *in place* *)

  let rec hash_term_array t =
    let accu = ref 0 in
    for i = 0 to Array.length t - 1 do
      let x, h = sh_rec t.(i) in
      accu := combine !accu h;
      t.(i) <- x
    done;
    !accu

  and hash_term t =
    match t with
      | HVar i ->
	(HVar (sh_id i), combinesmall 1 (Hashtbl.hash i))
      | HSort s ->
	(HSort (sh_sort s), combinesmall 2 (Hashtbl.hash s))
      | HCast (_,c, k, t) ->
	let c, hc = sh_rec c in
	let t, ht = sh_rec t in
	(HCast (no_hash,c, k, t), combinesmall 3 (combine3 hc (Hashtbl.hash k) ht))
      | HProd (_,na,t,c) ->
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
	(HProd (no_hash,sh_na na, t, c), combinesmall 4 (combine3 (Hashtbl.hash na) ht hc))
      | HLambda (_,na,t,c) ->
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
	(HLambda (no_hash,sh_na na, t, c), combinesmall 5 (combine3 (Hashtbl.hash na) ht hc))
      | HLetIn (_,na,b,t,c) ->
	let b, hb = sh_rec b in
	let t, ht = sh_rec t in
	let c, hc = sh_rec c in
	(HLetIn (no_hash,sh_na na, b, t, c), combinesmall 6 (combine4 (Hashtbl.hash na) hb ht hc))
      | HApp (_,c,l) ->
	let c, hc = sh_rec c in
	let hl = hash_term_array l in
	(HApp (no_hash,c, l), combinesmall 7 (combine hl hc))
      | HEvar (_,e,l) as t ->
	let hl = hash_term_array l in
	(* since the array have been hashed in place : *)
	(t, combinesmall 8 (combine (Hashtbl.hash e) hl))
      | HConst c ->
	(HConst (sh_con c), combinesmall 9 (Hashtbl.hash c))
      | HInd ((kn,i) as ind) ->
	(HInd (sh_ind ind), combinesmall 9 (combine (Hashtbl.hash kn) i))
      | HConstruct (((kn,i),j) as c)->
	(HConstruct (sh_construct c), combinesmall 10 (combine3 (Hashtbl.hash kn) i j))
      | HCase (_,ci,p,c,bl) ->
	let p, hp = sh_rec p
	and c, hc = sh_rec c in
	let hbl = hash_term_array bl in
	let hbl = combine (combine hc hp) hbl in
	(HCase (no_hash, sh_ci ci, p, c, bl), combinesmall 11 hbl)
      | HFix (_,ln,(lna,tl,bl)) as t ->
	let hbl = hash_term_array  bl in
	let htl = hash_term_array  tl in
	Array.iteri (fun i x -> lna.(i) <- sh_na x) lna;
	(* since the three arrays have been hashed in place : *)
	(t, combinesmall 13 (combine (Hashtbl.hash lna) (combine hbl htl)))
      | HCoFix(_,ln,(lna,tl,bl)) as t ->
	let hbl = hash_term_array bl in
	let htl = hash_term_array tl in
	Array.iteri (fun i x -> lna.(i) <- sh_na x) lna;
	(* since the three arrays have been hashed in place : *)
	(t, combinesmall 14 (combine (Hashtbl.hash lna) (combine hbl htl)))
      | HMeta n as t ->
	(t, combinesmall 15 n)
      | HRel n as t ->
	(t, combinesmall 16 n)

  and sh_rec t =
    let (y, h) = hash_term t in
    (* [h] must be positive. *)
    let h = h land 0x3FFFFFFF in
    (HashsetTerm.repr h y !term_table, h)

  in
  (* Make sure our statically allocated Rels (1 to 16) are considered
     as canonical, and hence hash-consed to themselves *)
  ignore (hash_term_array rels);

  fun t -> fst (sh_rec t)

(* Exported hashing fonction on constr, used mainly in plugins.
   Appears to have slight differences from [snd (hash_term t)] above ? *)

let rec hash_constr t =
  match kind_of_term t with
    | Var i -> combinesmall 1 (Hashtbl.hash i)
    | Sort s -> combinesmall 2 (Hashtbl.hash s)
    | Cast (c, _, _) -> hash_constr c
    | Prod (_, t, c) -> combinesmall 4 (combine (hash_constr t) (hash_constr c))
    | Lambda (_, t, c) -> combinesmall 5 (combine (hash_constr t) (hash_constr c))
    | LetIn (_, b, t, c) ->
      combinesmall 6 (combine3 (hash_constr b) (hash_constr t) (hash_constr c))
    | App (c,l) when isCast c -> hash_constr (mkApp (pi1 (destCast c),l))
    | App (c,l) ->
      combinesmall 7 (combine (hash_term_array l) (hash_constr c))
    | Evar (e,l) ->
      combinesmall 8 (combine (Hashtbl.hash e) (hash_term_array l))
    | Const c ->
      combinesmall 9 (Hashtbl.hash c)	(* TODO: proper hash function for constants *)
    | Ind (kn,i) ->
      combinesmall 9 (combine (Hashtbl.hash kn) i)
    | Construct ((kn,i),j) ->
      combinesmall 10 (combine3 (Hashtbl.hash kn) i j)
    | Case (_ , p, c, bl) ->
      combinesmall 11 (combine3 (hash_constr c) (hash_constr p) (hash_term_array bl))
    | Fix (ln ,(_, tl, bl)) ->
      combinesmall 13 (combine (hash_term_array bl) (hash_term_array tl))
    | CoFix(ln, (_, tl, bl)) ->
       combinesmall 14 (combine (hash_term_array bl) (hash_term_array tl))
    | Meta n -> combinesmall 15 n
    | Rel n -> combinesmall 16 n

and hash_term_array t =
  Array.fold_left (fun acc t -> combine (hash_constr t) acc) 0 t

module Hsorts =
  Hashcons.Make(
    struct
      type t = sorts
      type u = universe -> universe
      let hashcons huniv = function
          Prop c -> Prop c
        | Type u -> Type (huniv u)
      let equal s1 s2 =
        match (s1,s2) with
            (Prop c1, Prop c2) -> c1=c2
          | (Type u1, Type u2) -> u1 == u2
          |_ -> false
      let hash = Hashtbl.hash
    end)

module Hcaseinfo =
  Hashcons.Make(
    struct
      type t = case_info
      type u = inductive -> inductive
      let hashcons hind ci = { ci with ci_ind = hind ci.ci_ind }
      let equal ci ci' =
	ci.ci_ind == ci'.ci_ind &&
	ci.ci_npar = ci'.ci_npar &&
	ci.ci_cstr_ndecls = ci'.ci_cstr_ndecls && (* we use (=) on purpose *)
	ci.ci_pp_info = ci'.ci_pp_info  (* we use (=) on purpose *)
      let hash = Hashtbl.hash
    end)

let hcons_sorts = Hashcons.simple_hcons Hsorts.generate hcons_univ
let hcons_caseinfo = Hashcons.simple_hcons Hcaseinfo.generate hcons_ind

let hcons_constr =
  hcons_term
    (hcons_sorts,
     hcons_caseinfo,
     hcons_construct,
     hcons_ind,
     hcons_con,
     hcons_name,
     hcons_ident)

let hcons_types = hcons_constr

(* BEGIN PP *)
open Pp

let pr_id id = str (string_of_id id)

let print_sort = function
  | Prop Pos -> (str "Set")
  | Prop Null -> (str "Prop")
  | Type u -> (str "Type")

let pr_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let pr_name = function
  | Name id -> pr_id id
  | Anonymous -> str "_"

let pr_con sp = str(string_of_label(con_label sp))

let pr_rel_name e n =
  try let name, _, _= lookup_rel n e in pr_name name
  with _ -> str"__" ++ int (n - rel_context_length e)

let rec pr_constr h e c = if h < 0 then str".." else match c with
  | HRel n -> pr_rel_name e n (*++str"("++int n++str")"*)
  | HMeta n -> str "?m(" ++ int n ++ str ")"
  | HVar id -> pr_id id
  | HSort s -> print_sort s
  | HCast (_,c,_, t) -> hov 1
      (str"(" ++ pr_constr (h-1) e c ++ cut() ++
       str":" ++ pr_constr (h-1) e t ++ str")")
  | HProd (_,(Name(id) as n),t,c) -> hov 1
      (str"forall " ++ pr_id id ++ str":" ++ pr_constr (h-1) e t ++ str"," ++
       spc() ++ pr_constr (h-1) (add_rel_decl (n,None,t) e) c)
  | HProd (_,(Anonymous as n),t,c) -> hov 0
      (str"(" ++ pr_constr (h-1) e t ++ str " ->" ++ spc() ++
       pr_constr (h-1) (add_rel_decl (n,None,t) e) c ++ str")")
  | HLambda (_,na,t,c) -> hov 1
      (str"(fun (" ++ pr_name na ++ str":" ++
       pr_constr (h-1) e t ++ str") =>" ++ spc() ++ pr_constr (h-1) (add_rel_decl
       (na,None,t) e) c ++ str")")
  | HLetIn (_,na,b,t,c) -> hov 0
      (str"let " ++ pr_name na ++ str":=" ++ pr_constr (h-1) e b ++
       str":" ++ brk(1,2) ++ pr_constr (h-1) e t ++ str" in " ++ cut() ++
       pr_constr (h-1) (add_rel_decl (na,Some b,t) e) c)
  | HApp (_,c,l) ->  hov 1
      (str"(" ++ pr_constr (h-1) e c ++ spc() ++
       prlist_with_sep spc (pr_constr (h-1) e) (Array.to_list l) ++ str")")
  | HEvar (_,e,l) -> hov 1
      (str"?e(" ++ int e ++ str")")
(*        str"{" ++ prlist_with_sep spc pr_constr (h-1) e (Array.to_list l) ++str"}") *)
  | HConst c -> pr_con c
  | HInd (sp,i) -> let _, _, l = repr_mind sp in
      str(string_of_label l)++str"[" ++ int i ++ str"]"
  | HConstruct ((sp,i),j) -> let _, _, l = repr_mind sp in
      str(string_of_label l)++str"[" ++ int i ++ str "," ++ int j++ str"]"
  | HCase (_,ci,p,c,bl) -> v 0
      (hv 0 (hov 0 (str"case " ++ pr_constr (h-1) e c ++spc()++
       str"return "++pr_constr (h-1) e p++spc()++str"with ")) ++ cut() ++
       prlist_with_sep (fun _ -> cut()) 
         (fun t -> str"| " ++ pr_constr (h-1) e t)
         (Array.to_list bl) ++
      cut() ++ str"end")
  | HFix (_,(t,i),(lna,tl,bl)) ->
      hov 1 (str"fix " ++ int i ++ str" " ++ prvect_with_sep spc pr_name lna)
  | HCoFix(_,i,(lna,tl,bl)) ->
      (* FIX env *)
(*       let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in *)
      hov 1
        (str"cofix " ++ int i (* ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,ty,bd) ->
           pr_name na ++ str":" ++ pr_constr (h-1) e ty ++
           cut() ++ str":=" ++ pr_constr (h-1) e bd) (Array.to_list fixl)) ++
         str"}"*))
;;
(* END PP *)

let ll_pr_constr = pr_constr

(* alpha eq aware internalized constr *)
module H = struct
  type dummy = hash
  type hconstr = constr
  type 'a existential = 'a hpexistential
  type ('a,'b) rec_declaration = ('a,'b) prec_declaration
  type ('a,'b) fixpoint = ('a,'b) hpfixpoint
  type ('a,'b) cofixpoint = ('a,'b) hpcofixpoint
  type ('constr,'types) kind_of_hconstr = ('constr,'types) kind_of_hterm =
  | HRel       of int
  | HVar       of identifier
  | HMeta      of metavariable
  | HEvar      of 'constr existential
  | HSort      of sorts
  | HCast      of dummy * 'constr * cast_kind * 'types
  | HProd      of dummy * name * 'types * 'types
  | HLambda    of dummy * name * 'types * 'constr
  | HLetIn     of dummy * name * 'constr * 'types * 'constr
  | HApp       of dummy * 'constr * 'constr array
  | HConst     of constant
  | HInd       of inductive
  | HConstruct of constructor
  | HCase      of dummy * case_info * 'constr * 'constr * 'constr array
  | HFix       of ('constr, 'types) fixpoint
  | HCoFix     of ('constr, 'types) cofixpoint
          
  let kind_of t = t

  let ll_pr_hconstr = ll_pr_constr

  let equals_constr t1 t2 =
    match t1, t2 with
      | HRel n1, HRel n2 -> n1 == n2
      | HMeta m1, HMeta m2 -> m1 == m2
      | HVar id1, HVar id2 -> id1 == id2
      | HSort s1, HSort s2 -> s1 == s2
      | HCast (_,c1,k1,t1), HCast (_,c2,k2,t2) -> c1 == c2 && k1 == k2 && t1 == t2
      | HProd (_,n1,t1,c1), HProd (_,n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
      | HLambda (_,n1,t1,c1), HLambda (_,n2,t2,c2) -> n1 == n2 && t1 == t2 && c1 == c2
      | HLetIn (_,n1,b1,t1,c1), HLetIn (_,n2,b2,t2,c2) ->
        n1 == n2 && b1 == b2 && t1 == t2 && c1 == c2
      | HApp (_,c1,l1), HApp (_,c2,l2) -> c1 == c2 && array_eqeq l1 l2
      | HEvar (_,e1,l1), HEvar (_,e2,l2) -> e1 = e2 && array_eqeq l1 l2
      | HConst c1, HConst c2 -> c1 == c2
      | HInd (sp1,i1), HInd (sp2,i2) -> sp1 == sp2 && i1 = i2
      | HConstruct ((sp1,i1),j1), HConstruct ((sp2,i2),j2) ->
        sp1 == sp2 && i1 = i2 && j1 = j2
      | HCase (_,ci1,p1,c1,bl1), HCase (_,ci2,p2,c2,bl2) ->
        ci1 == ci2 && p1 == p2 && c1 == c2 && array_eqeq bl1 bl2
      | HFix (_,ln1,(lna1,tl1,bl1)), HFix (_,ln2,(lna2,tl2,bl2)) ->
        ln1 = ln2
        && array_eqeq lna1 lna2
        && array_eqeq tl1 tl2
        && array_eqeq bl1 bl2
      | HCoFix(_,ln1,(lna1,tl1,bl1)), HCoFix(_,ln2,(lna2,tl2,bl2)) ->
        ln1 = ln2
        && array_eqeq lna1 lna2
        && array_eqeq tl1 tl2
        && array_eqeq bl1 bl2
      | _ -> false

  module HashsetTerm = Hashset.Make(
    struct type t = constr let equal = equals_constr end)

  let size = 19991
  let term_table = HashsetTerm.create size
  let distribution () = HashsetTerm.distribution term_table

  let alpha = 65599
  let beta  = 7
  let combine x y     = x * alpha + y
  let combine3 x y z   = combine x (combine y z)
  let combine4 x y z t = combine x (combine3 y z t)
  let combinesmall x y =
    let h = beta * x + y in
    if h = no_hash then no_hash + 1 else h

  let genhash = Hashtbl.hash

  let hash_of_term = function
    | HCast (n,_,_,_) | HProd (n,_,_,_) | HLambda (n,_,_,_)
    | HLetIn (n,_,_,_,_) | HApp (n,_,_) | HEvar (n,_,_)
    | HCase (n,_,_,_,_) | HFix (n,_,_) | HCoFix (n,_,_) -> assert (n <> 0); n
    | HVar i -> combinesmall 1 (genhash i)
    | HSort s -> combinesmall 2 (genhash s)
    | HConst c -> combinesmall 9 (genhash c) (* XXX *)
    | HInd (kn,i) -> combinesmall 9 (combine (genhash kn) i)
    | HConstruct ((kn,i),j)-> combinesmall 10 (combine3 (genhash kn) i j)
    | HMeta n -> combinesmall 15 n
    | HRel n -> combinesmall 16 n

  let extern x = x

  let intern, hash_term_array =
    let (sh_sort,sh_ci,sh_construct,sh_ind,sh_con,sh_na,sh_id) =
      (hcons_sorts, hcons_caseinfo, hcons_construct,
       hcons_ind, hcons_con, hcons_name, hcons_ident) in

    let rec hash_term_array t =
      let accu = ref 0 in
      for i = 0 to Array.length t - 1 do
        let x, h = sh_rec t.(i) in
        accu := combine !accu h;
        t.(i) <- x
      done;
      !accu

    and hash_term = function
      | HVar i ->
	(HVar (sh_id i), combinesmall 1 (genhash i))
      | HSort s ->
	(HSort (sh_sort s), combinesmall 2 (genhash s))
      | HCast (h, c, k, t) as orig -> if h <> no_hash then (orig, h) else
	let c, hc = sh_rec c in
	let t, ht = sh_rec t in
        let h = combinesmall 3 (combine3 hc (genhash k) ht) in
	(HCast (h, c, k, t), h)
      | HProd (h, na,t,c) as orig -> if h <> no_hash then (orig, h) else
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
        let h = combinesmall 4 (combine ht hc) in
	(HProd (h, sh_na na, t, c), h)
      | HLambda (h, na,t,c) as orig -> if h <> no_hash then (orig, h) else
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
        let h = combinesmall 5 (combine ht hc) in
	(HLambda (h, sh_na na, t, c), h)
      | HLetIn (h, na,b,t,c) as orig -> if h <> no_hash then (orig, h) else
	let b, hb = sh_rec b in
	let t, ht = sh_rec t in
	let c, hc = sh_rec c in
        let h = combinesmall 6 (combine3 hb ht hc) in
	(HLetIn (h, sh_na na, b, t, c), h)
      | HApp (h, c,l) as orig -> if h <> no_hash then (orig, h) else
	let c, hc = sh_rec c in
	let hl = hash_term_array l in
        let h = combinesmall 7 (combine hl hc) in
	(HApp (h, c, l), h)
      | HEvar (h, e,l) as orig -> if h <> no_hash then (orig, h) else
	let hl = hash_term_array l in
        let h = combinesmall 8 (combine (genhash e) hl) in
	(HEvar (h, e, l), h)
      | HConst c ->
	(HConst (sh_con c), combinesmall 9 (genhash c))
      | HInd ((kn,i) as ind) ->
	(HInd (sh_ind ind), combinesmall 9 (combine (genhash kn) i))
      | HConstruct (((kn,i),j) as c)->
	(HConstruct(sh_construct c),combinesmall 10 (combine3 (genhash kn) i j))
      | HCase (h, ci,p,c,bl) as orig -> if h <> no_hash then (orig, h) else
	let p, hp = sh_rec p
	and c, hc = sh_rec c in
	let hbl = hash_term_array bl in
	let hbl = combine (combine hc hp) hbl in
        let h = combinesmall 11 hbl in
	(HCase (h, sh_ci ci, p, c, bl), h)
      | HFix (h, ln,(lna,tl,bl)) as orig -> if h <> no_hash then (orig, h) else
              (* XXX why ln is not used!!! *)
	let hbl = hash_term_array  bl in
	let htl = hash_term_array  tl in
	Array.iteri (fun i x -> lna.(i) <- sh_na x) lna;
        let h = combinesmall 13 (combine (genhash lna) (combine hbl htl)) in
	(HFix (h, ln,(lna,tl,bl)), h)
      | HCoFix(h, ln,(lna,tl,bl)) as orig -> if h <> no_hash then (orig, h) else
	let hbl = hash_term_array bl in
	let htl = hash_term_array tl in
	Array.iteri (fun i x -> lna.(i) <- sh_na x) lna;
        let h = combinesmall 14 (combine (genhash lna) (combine hbl htl)) in
	(HCoFix(h, ln,(lna,tl,bl)), h)
      | HMeta n as t ->
	(t, combinesmall 15 n)
      | HRel n as t ->
	(t, combinesmall 16 n)

    and sh_rec t =
      let (y, h) = hash_term t in
      (HashsetTerm.repr h y term_table, h)

  in
  (* Make sure our statically allocated Rels (1 to 16) are considered
     as canonical, and hence hash-consed to themselves *)
  ignore (hash_term_array rels);

  (fun t -> fst (sh_rec t)), hash_term_array
  
  let reset () =
    HashsetTerm.reset size term_table;
    ignore(hash_term_array rels)

  let equal = (==)

  let compare t1 t2 =
    if t1 == t2 then 0
    else
      let diff = hash_of_term t1 - hash_of_term t2 in
      if diff = 0 then Pervasives.compare t1 t2 else diff

  let hash = hash_of_term

  let mkHFix (x,y) = intern (HFix (0,x,y))

  module HET = struct
    type t = hconstr
    let equal = equal
    let hash = hash
  end
  module Table = Hashtbl.Make(HET)

  module HOT = struct
    type t = hconstr
    let compare = compare
  end
  module Map = Map.Make(HOT)
  module Set = Set.Make(HOT)

end


(*******)
(* Type of abstract machine values *)
type values
