(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Names
open Sorts
open Term
open Vars
open Declarations
open Declareops
open Environ
open CClosure
open Type_errors
open Context.Rel.Declaration

type mind_specif = mutual_inductive_body * one_inductive_body

(* raise Not_found if not an inductive type *)
let lookup_mind_specif env (kn,tyi) =
  let mib = Environ.lookup_mind kn env in
  if tyi >= Array.length mib.mind_packets then
    error "Preinductive.lookup_mind_specif: invalid inductive index";
  (mib, mib.mind_packets.(tyi))

let find_rectype env c =
  let (t, l) = decompose_app (whd_all env c) in
  match kind_of_term t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

let find_inductive env c =
  let (t, l) = decompose_app (whd_all env c) in
  match kind_of_term t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_polymorphic ind))).mind_finite <> Decl_kinds.CoFinite -> (ind, l)
    | _ -> raise Not_found

let find_coinductive env c =
  let (t, l) = decompose_app (whd_all env c) in
  match kind_of_term t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_polymorphic ind))).mind_finite == Decl_kinds.CoFinite -> (ind, l)
    | _ -> raise Not_found

let inductive_params (mib,_) = mib.mind_nparams

let inductive_paramdecls (mib,u) = 
  Vars.subst_instance_context u mib.mind_params_ctxt

let instantiate_inductive_constraints mib u =
  if mib.mind_polymorphic then
    subst_instance_constraints u (UContext.constraints mib.mind_universes)
  else Constraint.empty

(* Build the substitution that replaces Rels by the appropriate *)
(* inductives *)
let ind_subst mind mib u =
  let ntypes = mib.mind_ntypes in
  let make_Ik k = mkIndU ((mind,ntypes-k-1),u) in
  List.init ntypes make_Ik

(* Instantiate inductives in constructor type *)
let constructor_instantiate mind u mib c =
  let s = ind_subst mind mib u in
    substl s (subst_instance_constr u c)

(* Template polymorphism *)

(************************************************************************)
(************************************************************************)

(* Functions to build standard types related to inductive *)

(*
Computing the actual sort of an applied or partially applied inductive type:

I_i: forall uniformparams:utyps, forall otherparams:otyps, Type(a)
uniformargs : utyps
otherargs : otyps
I_1:forall ...,s_1;...I_n:forall ...,s_n |- sort(C_kj(uniformargs)) = s_kj
s'_k = max(..s_kj..)
merge(..s'_k..) = ..s''_k..
--------------------------------------------------------------------
Gamma |- I_i uniformargs otherargs : phi(s''_i)

where

- if p=0, phi() = Prop
- if p=1, phi(s) = s
- if p<>1, phi(s) = sup(Set,s)

Remark: Set (predicative) is encoded as Type(0)
*)

(* cons_subst add the mapping [u |-> su] in subst if [u] is not *)
(* in the domain or add [u |-> sup x su] if [u] is already mapped *)
(* to [x]. *)
let cons_univ_subst u su subst =
  try
    Univ.UMap.add u (Univ.sup (Univ.UMap.find u subst) su) subst
  with Not_found -> Univ.UMap.add u su subst

let cons_trunc_subst u su subst =
  try
    Trunc.TMap.add u (Trunc.Truncation.sup (Trunc.TMap.find u subst) su) subst
  with Not_found -> Trunc.TMap.add u su subst

(* remember_subst updates the mapping [u |-> x] by [u |-> sup x u] *)
(* if it is presents and returns the substitution unchanged if not.*)
let remember_univ_subst u subst =
  try
    let su = Univ.Universe.make u in
    Univ.UMap.add u (Univ.sup (Univ.UMap.find u subst) su) subst
  with Not_found -> subst

let remember_trunc_subst u subst =
  try
    let su = Trunc.Truncation.of_level u in
    Trunc.TMap.add u (Trunc.Truncation.sup (Trunc.TMap.find u subst) su) subst
  with Not_found -> subst

(* Bind expected levels of parameters to actual levels *)
(* Propagate the new levels in the signature *)
let make_univ_subst env =
  let rec make subst = function
    | LocalDef _ :: sign, exp, args ->
        make subst (sign, exp, args)
    | d::sign, None::exp, args ->
        let args = match args with _::args -> args | [] -> [] in
        make subst (sign, exp, args)
    | d::sign, Some u::exp, a::args ->
        (* We recover the level of the argument, but we don't change the *)
        (* level in the corresponding type in the arity; this level in the *)
        (* arity is a global level which, at typing time, will be enforce *)
        (* to be greater than the level of the argument; this is probably *)
        (* a useless extra constraint *)
        let s = univ_of_sort (snd (dest_arity env (Lazy.force a))) in
          make (cons_univ_subst u s subst) (sign, exp, args)
    | LocalAssum (na,t) :: sign, Some u::exp, [] ->
        (* No more argument here: we add the remaining universes to the *)
        (* substitution (when [u] is distinct from all other universes in the *)
        (* template, it is identity substitution  otherwise (ie. when u is *)
        (* already in the domain of the substitution) [remember_subst] will *)
        (* update its image [x] by [sup x u] in order not to forget the *)
        (* dependency in [u] that remains to be fullfilled. *)
        make (remember_univ_subst u subst) (sign, exp, [])
    | sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
    | [], _, _ ->
        assert false
  in
  make Univ.UMap.empty

let make_trunc_subst env =
  let rec make subst = function
    | LocalDef _ :: sign, exp, args ->
        make subst (sign, exp, args)
    | d::sign, None::exp, args ->
        let args = match args with _::args -> args | [] -> [] in
        make subst (sign, exp, args)
    | d::sign, Some u::exp, a::args ->
        (* We recover the level of the argument, but we don't change the *)
        (* level in the corresponding type in the arity; this level in the *)
        (* arity is a global level which, at typing time, will be enforce *)
        (* to be greater than the level of the argument; this is probably *)
        (* a useless extra constraint *)
        let s = trunc_of_sort (snd (dest_arity env (Lazy.force a))) in
          make (cons_trunc_subst u s subst) (sign, exp, args)
    | LocalAssum (na,t) :: sign, Some u::exp, [] ->
        (* No more argument here: we add the remaining universes to the *)
        (* substitution (when [u] is distinct from all other universes in the *)
        (* template, it is identity substitution  otherwise (ie. when u is *)
        (* already in the domain of the substitution) [remember_subst] will *)
        (* update its image [x] by [sup x u] in order not to forget the *)
        (* dependency in [u] that remains to be fullfilled. *)
        make (remember_trunc_subst u subst) (sign, exp, [])
    | sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
    | [], _, _ ->
        assert false
  in
  make Trunc.TMap.empty


let instantiate_universes env ctx ar argsorts =
  let args = Array.to_list argsorts in
  let usubst = make_univ_subst env (ctx,ar.template_param_univ_levels,args) in
  let tsubst = make_trunc_subst env (ctx,ar.template_param_trunc_levels,args) in
  let subst = Sorts.sort_subst_fn (usubst, tsubst) in
  let level = Sorts.subst_sorts subst ar.template_level in
    (ctx, level)


exception SingletonInductiveBecomesProp of Id.t

(* Type of an inductive type *)

let type_of_inductive_gen ?(polyprop=true) env ((mib,mip),u) paramtyps =
  match mip.mind_arity with
  | RegularArity a -> subst_instance_constr u a.mind_user_arity
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
    let ctx,s = instantiate_universes env ctx ar paramtyps in
      (* The Ocaml extraction cannot handle (yet?) "Prop-polymorphism", i.e.
         the situation where a non-Prop singleton inductive becomes Prop
         when applied to Prop params *)
      if not polyprop && not (is_prop_sort ar.template_level) && is_prop_sort s
      then raise (SingletonInductiveBecomesProp mip.mind_typename);
      mkArity (List.rev ctx,s)

let type_of_inductive env pind = 
  type_of_inductive_gen env pind [||]

let constrained_type_of_inductive env ((mib,mip),u as pind) =
  let ty = type_of_inductive env pind in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let constrained_type_of_inductive_knowing_parameters env ((mib,mip),u as pind) args =
  let ty = type_of_inductive_gen env pind args in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let type_of_inductive_knowing_parameters env ?(polyprop=true) mip args =
  type_of_inductive_gen ~polyprop env mip args

(************************************************************************)
(* Type of a constructor *)

let type_of_constructor (cstr, u) (mib,mip) =
  let ind = inductive_of_constructor cstr in
  let specif = mip.mind_user_lc in
  let i = index_of_constructor cstr in
  let nconstr = Array.length mip.mind_consnames in
  if i > nconstr then error "Not enough constructors in the type.";
  constructor_instantiate (fst ind) u mib specif.(i-1)

let constrained_type_of_constructor (cstr,u as cstru) (mib,mip as ind) =
  let ty = type_of_constructor cstru ind in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let arities_of_specif (kn,u) (mib,mip) =
  let specif = mip.mind_nf_lc in
    Array.map (constructor_instantiate kn u mib) specif

let arities_of_constructors ind specif =
  arities_of_specif (fst (fst ind), snd ind) specif

let type_of_constructors (ind,u) (mib,mip) =
  let specif = mip.mind_user_lc in
    Array.map (constructor_instantiate (fst ind) u mib) specif

(* [p] is the predicate, [c] is the match object, [realargs] is the
   list of real args of the inductive type *)
let build_case_type env n p c realargs =
  whd_betaiota env (lambda_appvect_assum (n+1) p (Array.of_list (realargs@[c])))

let type_of_case env (pind,largs) p c =
  let specif = lookup_mind_specif env (fst pind) in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  build_case_type env (snd specif).mind_nrealdecls p c realargs
