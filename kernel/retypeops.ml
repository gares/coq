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
open Univ
open Term
open Vars
open Declarations
open Environ
open CClosure
open Type_errors
open Preinductive

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(* This should be a type (a priori without intention to be an assumption) *)
let type_judgment env c t =
  match kind_of_term(whd_all env t) with
    | Sort s -> {utj_val = c; utj_type = s }
    | _ -> error_not_type env (make_judge c t)

let check_type env c t =
  match kind_of_term(whd_all env t) with
  | Sort s -> s
  | _ -> error_not_type env (make_judge c t)

(************************************************)
(* Incremental typing rules: builds a typing judgment given the *)
(* judgments for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let judge_of_prop = mkSort type1_sort

(* Type of Type(i). *)

let judge_of_type u =
  let uu = Sorts.super u in
    mkSort uu

(*s Type of a de Bruijn index. *)

let judge_of_relative env n =
  try
    env |> lookup_rel n |> RelDecl.get_type |> lift n
  with Not_found ->
    error_unbound_rel env n

(* Type of variables *)
let judge_of_variable env id =
  try named_type id env
  with Not_found ->
    error_unbound_var env id

(* Type of constants *)

let type_of_constant_knowing_parameters_arity env t paramtyps =
  match t with
  | RegularArity t -> t
  | TemplateArity (sign,ar) ->
      let ctx = List.rev sign in
      let ctx,s = instantiate_universes env ctx ar paramtyps in
      mkArity (List.rev ctx,s)

let type_of_constant_knowing_parameters env cst paramtyps =
  let ty = constant_type_in env cst in
  type_of_constant_knowing_parameters_arity env ty paramtyps

let judge_of_constant env cst =
  type_of_constant_knowing_parameters env cst [||]

(* Type of a lambda-abstraction. *)

(* [judge_of_abstraction env name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let judge_of_abstraction env name var ty =
  mkProd (name, var, ty)

(* Type of an application. *)

let make_judgev c t = 
  Array.map2 make_judge c t

let judge_of_apply env func funt argsv argstv =
  let len = Array.length argsv in
  let rec apply_rec i typ = 
    if Int.equal i len then typ
    else 
      (match kind_of_term (whd_all env typ) with
      | Prod (_,c1,c2) ->
	let arg = argsv.(i) in
	apply_rec (i+1) (subst1 arg c2)
      | _ ->
	error_cant_apply_not_functional env 
	  (make_judge func funt)
	  (make_judgev argsv (Array.map Lazy.force argstv)))
  in apply_rec 0 funt

(* Type of product *)

(* [judge_of_product env name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ1 |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)
let judge_of_product env name s1 s2 =
  let s = sort_of_product env s1 s2 in
    mkSort s

(* Inductive types. *)

(* The type is parametric over the uniform parameters whose conclusion
   is in Type; to enforce the internal constraints between the
   parameters and the instances of Type occurring in the type of the
   constructors, we use the level variables _statically_ assigned to
   the conclusions of the parameters as mediators: e.g. if a parameter
   has conclusion Type(alpha), static constraints of the form alpha<=v
   exist between alpha and the Type's occurring in the constructor
   types; when the parameters is finally instantiated by a term of
   conclusion Type(u), then the constraints u<=alpha is computed in
   the App case of execute; from this constraints, the expected
   dynamic constraints of the form u<=v are enforced *)

let judge_of_inductive_knowing_parameters env (ind,u) args =
  let (mib,mip) as spec = lookup_mind_specif env ind in
  type_of_inductive_knowing_parameters env (spec,u) args

let judge_of_inductive env (ind,u) =
  let (mib,mip) = lookup_mind_specif env ind in
  type_of_inductive env ((mib,mip),u)

(* Constructors. *)

let judge_of_constructor env (c,u as cu) =
  let specif = lookup_mind_specif env (inductive_of_constructor c) in
  type_of_constructor cu specif

(* Case. *)

let judge_of_case env p c ct =
  let (pind, _ as indspec) =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  type_of_case env indspec p c

let judge_of_projection env p c ct =
  let pb = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
  assert(eq_mind pb.proj_ind (fst ind));
  let ty = Vars.subst_instance_constr u pb.Declarations.proj_type in
  substl (c :: List.rev args) ty

(************************************************************************)
(************************************************************************)

(* The typing machine. *)
    (* ATTENTION : faudra faire le typage du contexte des Const,
    Ind et Constructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)
let execute env sigma cstr =
  let rec execute env cstr =
  let open Context.Rel.Declaration in
  match kind_of_term cstr with
    (* Atomic terms *)
    | Sort s when is_small s ->
      judge_of_prop
	
    | Sort u ->
      judge_of_type u

    | Rel n ->
      judge_of_relative env n

    | Var id ->
      judge_of_variable env id

    | Const c ->
      judge_of_constant env c
	
    | Proj (p, c) ->
        let ct = execute env c in
        judge_of_projection env p c ct

    (* Lambda calculus operators *)
    | App (f,args) ->
        let argst = Array.map (fun c -> lazy (execute env c)) args in
	let ft =
	  match kind_of_term f with
	  | Ind ind when Environ.template_polymorphic_pind ind env ->
	      (* Template sort-polymorphism of inductive types *)
	      judge_of_inductive_knowing_parameters env ind argst
	  | Const cst when Environ.template_polymorphic_pconstant cst env ->
	      (* Template sort-polymorphism of constants *)
	      type_of_constant_knowing_parameters env cst argst
	  | _ ->
	    (* Full or no sort-polymorphism *)
            execute env f
	in
	judge_of_apply env f ft args argst

    | Lambda (name,c1,c2) ->
      let env1 = push_rel (LocalAssum (name,c1)) env in
      let c2t = execute env1 c2 in
        judge_of_abstraction env name c1 c2t

    | Prod (name,c1,c2) ->
      let vars = execute_is_type env c1 in
      let env1 = push_rel (LocalAssum (name,c1)) env in
      let vars' = execute_is_type env1 c2 in
	judge_of_product env name vars vars'

    | LetIn (name,c1,c2,c3) ->
      let env1 = push_rel (LocalDef (name,c1,c2)) env in
      let c3t = execute env1 c3 in
	subst1 c1 c3t

    | Cast (c,k,t) -> t

    (* Inductive types *)
    | Ind ind ->
      judge_of_inductive env ind

    | Construct c ->
      judge_of_constructor env c

    | Case (ci,p,c,lf) ->
        let ct = execute env c in
        judge_of_case env p c ct

    | Fix ((vn,i),(_,lar,_)) ->
       lar.(i)
	  
    | CoFix (i,(_,lar,_)) ->
       lar.(i)

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
	anomaly (Pp.str "the kernel does not support metavariables")

    | Evar _ ->
	anomaly (Pp.str "the kernel does not support existential variables")

  and execute_is_type env constr =
    let t = execute env constr in
    check_type env constr t

  in
  execute env cstr

let execute_type env sigma constr =
  let t = execute env sigma constr in
    type_judgment env constr t

(* Derived functions *)
let infer env sigma constr =
  let t = execute env sigma constr in
    make_judge constr t

let infer = 
  if Flags.profile then
    let infer_key = Profile.declare_profile "Fast_infer" in
      Profile.profile3 infer_key (fun a b c -> infer a b c)
  else (fun a b c -> infer a b c)

let infer_type env sigma constr =
  execute_type env sigma constr

let infer_v env sigma cv =
  make_judgev cv (Array.map (execute env sigma) cv)
