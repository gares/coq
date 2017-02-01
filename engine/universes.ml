(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Environ
open Univ
open Sorts
open Globnames
open Decl_kinds

let pr_with_global_universes l = 
  try Nameops.pr_id (UMap.find l (snd (Global.global_universe_names ())))
  with Not_found -> Level.pr l

(** Local universe names of polymorphic references *)

type universe_binders = (Id.t * Univ.universe_level) list

let universe_binders_table = Summary.ref Refmap.empty ~name:"universe binders"

let universe_binders_of_global ref =
  try
    let l = Refmap.find ref !universe_binders_table in l
  with Not_found -> []

let register_universe_binders ref l =
  universe_binders_table := Refmap.add ref l !universe_binders_table
		     
(* To disallow minimization to Set *)

let set_minimization = ref true
let is_set_minimization () = !set_minimization
			    
type universe_constraint_type = ULe | UEq | ULub

type universe_constraint = sorts * universe_constraint_type * sorts

module Constraints = struct
  module S = Set.Make(
  struct 
    type t = universe_constraint

    let compare_type c c' =
      match c, c' with
      | ULe, ULe -> 0
      | ULe, _ -> -1
      | _, ULe -> 1
      | UEq, UEq -> 0
      | UEq, _ -> -1
      | ULub, ULub -> 0
      | ULub, _ -> 1
      
    let compare (u,c,v) (u',c',v') =
      let i = compare_type c c' in
	if Int.equal i 0 then
          let i' = Sorts.compare u u' in
            if Int.equal i' 0 then Sorts.compare v v'
	    else 
              if c != ULe && Sorts.compare u v' = 0 && Sorts.compare v u' = 0 then 0
	      else i'
	else i
  end)
  
  include S
  
  let add (l,d,r as cst) s = 
    if Sorts.equal l r then s
    else add cst s

  let tr_dir = function
    | ULe -> Le
    | UEq -> Eq
    | ULub -> Eq

  let op_str = function ULe -> " <= " | UEq -> " = " | ULub -> " /\\ "

  let pr c =
    fold (fun (u1,op,u2) pp_std ->
        pp_std ++ Sorts.pr u1 ++ str (op_str op) ++
        Sorts.pr u2 ++ fnl ()) c (str "")

  let equal x y = 
    x == y || equal x y

end

type universe_constraints = Constraints.t
type 'a constraint_accumulator = universe_constraints -> 'a -> 'a option
type 'a universe_constrained = 'a * universe_constraints

type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

let enforce_eq_instances_univs strict x y c = 
  let d = if strict then ULub else UEq in
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      CErrors.anomaly (Pp.str "Invalid argument: enforce_eq_instances_univs called with" ++
	       Pp.str " instances of different lengths");
    CArray.fold_right2
      (fun x y -> Constraints.add (Sorts.of_level x, d, Sorts.of_level y))
      ax ay c

let to_constraints g s = 
  let tr (x,d,y) acc =
    let add l d l' acc = Constraint.add_univ (l,Constraints.tr_dir d,l') acc in
      match Sorts.level x, d, Sorts.level y with
      | Some l, (ULe | UEq | ULub), Some l' -> add l d l' acc
      | _, ULe, Some l' -> Sorts.enforce_leq x y acc
      | _, ULub, _ -> acc
      | _, d, _ -> 
        let f = if d == ULe then Sorts.Graph.check_leq else Sorts.Graph.check_eq in
	  if f g x y then acc else 
	    raise (Invalid_argument 
		   "to_constraints: non-trivial algebraic constraint between universes")
  in Constraints.fold tr s Constraint.empty

let test_constr_univs_infer leq univs fold m n accu =
  if m == n then Some accu
  else 
    let cstrs = ref accu in
    let eq_universes strict l l' = Sorts.Graph.check_eq_instances univs l l' in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else
        match fold (Constraints.singleton (s1, UEq, s2)) !cstrs with
	| None -> false
	| Some accu -> cstrs := accu; true
    in
    let leq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else 
        match fold (Constraints.singleton (s1, ULe, s2)) !cstrs with
	| None -> false
	| Some accu -> cstrs := accu; true
    in
    let rec eq_constr' m n = 
      m == n || Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let res =
      if leq then
        let rec compare_leq m n =
          Constr.compare_head_gen_leq eq_universes leq_sorts 
            eq_constr' leq_constr' m n
        and leq_constr' m n = m == n || compare_leq m n in
        compare_leq m n
      else Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    if res then Some !cstrs else None

let eq_constr_univs_infer univs fold m n accu =
  test_constr_univs_infer false univs fold m n accu

let leq_constr_univs_infer univs fold m n accu =
  test_constr_univs_infer true univs fold m n accu

(** Variant of [eq_constr_univs_infer] taking kind-of-term functions,
    to expose subterms of [m] and [n], arguments. *)
let eq_constr_univs_infer_with kind1 kind2 univs fold m n accu =
  (* spiwack: duplicates the code of [eq_constr_univs_infer] because I
     haven't find a way to factor the code without destroying
     pointer-equality optimisations in [eq_constr_univs_infer].
     Pointer equality is not sufficient to ensure equality up to
     [kind1,kind2], because [kind1] and [kind2] may be different,
     typically evaluating [m] and [n] in different evar maps. *)
  let cstrs = ref accu in
  let eq_universes strict = Sorts.Graph.check_eq_instances univs in
  let eq_sorts s1 s2 = 
    if Sorts.equal s1 s2 then true
    else
      match fold (Constraints.singleton (s1, UEq, s2)) !cstrs with
      | None -> false
      | Some accu -> cstrs := accu; true
  in
  let rec eq_constr' m n = 
    Constr.compare_head_gen_with kind1 kind2 eq_universes eq_sorts eq_constr' m n
  in
  let res = Constr.compare_head_gen_with kind1 kind2 eq_universes eq_sorts eq_constr' m n in
  if res then Some !cstrs else None

let test_constr_universes leq m n =
  if m == n then Some Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else (cstrs := Constraints.add (s1, UEq, s2) !cstrs; true)
    in
    let leq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else (cstrs := Constraints.add (s1, ULe, s2) !cstrs; true)
    in
    let rec eq_constr' m n = 
      m == n || Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let res =
      if leq then
        let rec compare_leq m n =
          Constr.compare_head_gen_leq eq_universes leq_sorts eq_constr' leq_constr' m n
        and leq_constr' m n = m == n || compare_leq m n in
        compare_leq m n
      else
        Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    if res then Some !cstrs else None

let eq_constr_universes m n = test_constr_universes false m n
let leq_constr_universes m n = test_constr_universes true m n

let compare_head_gen_proj env equ eqs eqc' m n =
  match kind_of_term m, kind_of_term n with
  | Proj (p, c), App (f, args)
  | App (f, args), Proj (p, c) -> 
      (match kind_of_term f with
      | Const (p', u) when eq_constant (Projection.constant p) p' -> 
          let pb = Environ.lookup_projection p env in
          let npars = pb.Declarations.proj_npars in
	  if Array.length args == npars + 1 then
	    eqc' c args.(npars)
	  else false
      | _ -> false)
  | _ -> Constr.compare_head_gen equ eqs eqc' m n
      
let eq_constr_universes_proj env m n =
  if m == n then true, Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else (cstrs := Constraints.add (s1, UEq, s2) !cstrs; true)
    in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen_proj env eq_universes eq_sorts eq_constr' m n
    in
    let res = eq_constr' m n in
    res, !cstrs

(* Generator of levels *)
let new_univ_level, set_remote_new_univ_level =
  RemoteCounter.new_counter ~name:"Universes" 0 ~incr:((+) 1)
    ~build:(fun n -> Univ.Level.make (Global.current_dirpath ()) n)

let fresh_level = new_univ_level

(* (\* TODO: remove *\) *)
(* let new_univ dp = Univ.Universe.make (new_univ_level dp) *)
(* let new_Type dp = mkType (new_univ dp) *)

let fresh_universe_instance ctx =
  Instance.apply_subst (fun _ -> new_univ_level ())
    (UContext.instance ctx)

let fresh_instance_from_context ctx =
  let inst = fresh_universe_instance ctx in
  let constraints = instantiate_univ_constraints inst ctx in
    inst, constraints

let fresh_instance ctx =
  let ctx' = ref USet.empty in
  let inst = 
    Instance.apply_subst (fun v ->
      let u = new_univ_level () in
	ctx' := USet.add u !ctx'; u)
      (UContext.instance ctx)
  in !ctx', inst

let existing_instance ctx inst = 
  let () = 
    let a1 = Instance.to_array inst 
    and a2 = Instance.to_array (UContext.instance ctx) in
    let len1 = Array.length a1 and len2 = Array.length a2 in 
      if not (len1 == len2) then
	CErrors.user_err ~hdr:"Universes"
	  (str "Polymorphic constant expected " ++ int len2 ++ 
	     str" levels but was given " ++ int len1)
      else ()
  in USet.empty, inst

let fresh_instance_from ctx inst =
  let ctx', inst = 
    match inst with 
    | Some inst -> existing_instance ctx inst
    | None -> fresh_instance ctx 
  in
  let constraints = instantiate_univ_constraints inst ctx in
    inst, (ctx', constraints)

let unsafe_instance_from ctx =
  (Sorts.UContext.instance ctx, ctx)
    
(** Fresh universe polymorphic construction *)

let fresh_constant_instance env c inst =
  let cb = lookup_constant c env in
    if cb.Declarations.const_polymorphic then
      let inst, ctx =
        fresh_instance_from
          (Declareops.universes_of_constant (Environ.opaque_tables env) cb) inst
      in
	((c, inst), ctx)
    else ((c,Instance.empty), ContextSet.empty)

let fresh_inductive_instance env ind inst = 
  let mib, mip = Preinductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = fresh_instance_from mib.Declarations.mind_universes inst in
	((ind,inst), ctx)
    else ((ind,Instance.empty), ContextSet.empty)

let fresh_constructor_instance env (ind,i) inst = 
  let mib, mip = Preinductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = fresh_instance_from mib.Declarations.mind_universes inst in
	(((ind,i),inst), ctx)
    else (((ind,i),Instance.empty), ContextSet.empty)

let unsafe_constant_instance env c =
  let cb = lookup_constant c env in
    if cb.Declarations.const_polymorphic then
      let inst, ctx = unsafe_instance_from
        (Declareops.universes_of_constant (Environ.opaque_tables env) cb) in
	((c, inst), ctx)
    else ((c,Instance.empty), UContext.empty)

let unsafe_inductive_instance env ind = 
  let mib, mip = Preinductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = unsafe_instance_from mib.Declarations.mind_universes in
	((ind,inst), ctx)
    else ((ind,Instance.empty), UContext.empty)

let unsafe_constructor_instance env (ind,i) = 
  let mib, mip = Preinductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = unsafe_instance_from mib.Declarations.mind_universes in
	(((ind,i),inst), ctx)
    else (((ind,i),Instance.empty), UContext.empty)

open Globnames

let fresh_global_instance ?names env gr =
  match gr with
  | VarRef id -> mkVar id, ContextSet.empty
  | ConstRef sp -> 
     let c, ctx = fresh_constant_instance env sp names in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = fresh_constructor_instance env sp names in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = fresh_inductive_instance env sp names in
       mkIndU c, ctx

let fresh_constant_instance env sp = 
  fresh_constant_instance env sp None

let fresh_inductive_instance env sp = 
  fresh_inductive_instance env sp None

let fresh_constructor_instance env sp = 
  fresh_constructor_instance env sp None

let unsafe_global_instance env gr =
  match gr with
  | VarRef id -> mkVar id, UContext.empty
  | ConstRef sp -> 
     let c, ctx = unsafe_constant_instance env sp in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = unsafe_constructor_instance env sp in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = unsafe_inductive_instance env sp in
       mkIndU c, ctx

let constr_of_global gr =
  let c, ctx = fresh_global_instance (Global.env ()) gr in
    if not (Sorts.ContextSet.is_empty ctx) then
      if Univ.USet.is_empty (Sorts.ContextSet.levels ctx) then
	(* Should be an error as we might forget constraints, allow for now
	   to make firstorder work with "using" clauses *)
	c
      else raise (Invalid_argument 
		    ("constr_of_global: globalization of polymorphic reference " ^ 
			Pp.string_of_ppcmds (Nametab.pr_global_env Id.Set.empty gr) ^
			" would forget universes."))
    else c

let constr_of_reference = constr_of_global

let unsafe_constr_of_global gr =
  unsafe_global_instance (Global.env ()) gr

let constr_of_global_univ (gr,u) =
  match gr with
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConstU (sp,u)
  | ConstructRef sp -> mkConstructU (sp,u)
  | IndRef sp -> mkIndU (sp,u)

let fresh_global_or_constr_instance env = function
  | IsConstr c -> c, ContextSet.empty
  | IsGlobal gr -> fresh_global_instance env gr

let global_of_constr c =
  match kind_of_term c with
  | Const (c, u) -> ConstRef c, u
  | Ind (i, u) -> IndRef i, u
  | Construct (c, u) -> ConstructRef c, u
  | Var id -> VarRef id, Instance.empty
  | _ -> raise Not_found

let global_app_of_constr c =
  match kind_of_term c with
  | Const (c, u) -> (ConstRef c, u), None
  | Ind (i, u) -> (IndRef i, u), None
  | Construct (c, u) -> (ConstructRef c, u), None
  | Var id -> (VarRef id, Instance.empty), None
  | Proj (p, c) -> (ConstRef (Projection.constant p), Instance.empty), Some c
  | _ -> raise Not_found

open Declarations

let type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env, ContextSet.empty
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
     let ty = Typeops.type_of_constant_type env cb.const_type in
       if cb.const_polymorphic then
	 let inst, ctx = fresh_instance_from (Declareops.universes_of_constant (Environ.opaque_tables env) cb) None in
	   Vars.subst_instance_constr inst ty, ctx
       else ty, ContextSet.empty

  | IndRef ind ->
     let (mib, oib as specif) = Preinductive.lookup_mind_specif env ind in
       if mib.mind_polymorphic then
	 let inst, ctx = fresh_instance_from mib.mind_universes None in
	 let ty = Preinductive.type_of_inductive env (specif, inst) in
	   ty, ctx
       else
	 let ty = Preinductive.type_of_inductive env (specif, Sorts.Instance.empty) in
	   ty, ContextSet.empty
  | ConstructRef cstr ->
     let (mib,oib as specif) = Preinductive.lookup_mind_specif env (inductive_of_constructor cstr) in
       if mib.mind_polymorphic then
	 let inst, ctx = fresh_instance_from mib.mind_universes None in
	   Preinductive.type_of_constructor (cstr,inst) specif, ctx
       else Preinductive.type_of_constructor (cstr,Instance.empty) specif, ContextSet.empty

let type_of_global t = type_of_reference (Global.env ()) t

let unsafe_type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
       Typeops.type_of_constant_type env cb.const_type

  | IndRef ind ->
     let (mib, oib as specif) = Preinductive.lookup_mind_specif env ind in
     let (_, inst), _ = unsafe_inductive_instance env ind in
       Preinductive.type_of_inductive env (specif, inst)

  | ConstructRef (ind, _ as cstr) ->
     let (mib,oib as specif) = Preinductive.lookup_mind_specif env (inductive_of_constructor cstr) in
     let (_, inst), _ = unsafe_inductive_instance env ind in
       Preinductive.type_of_constructor (cstr,inst) specif

let unsafe_type_of_global t = unsafe_type_of_reference (Global.env ()) t

let fresh_sort_in_family env = function
  | InProp -> prop_sort, ContextSet.empty
  | InSet -> set_sort, ContextSet.empty
  | InType -> 
    let u = fresh_level () in
      Sorts.of_level u, ContextSet.singleton u

let new_sort_in_family sf =
  fst (fresh_sort_in_family (Global.env ()) sf)

let extend_context (a, ctx) (ctx') =
  (a, ContextSet.union ctx ctx')

let new_global_univ () =
  let u = fresh_level () in
    (Univ.Universe.make u, ContextSet.singleton u)

let new_global_sort () =
  let u = fresh_level () in
    (Sorts.of_level u, ContextSet.singleton u)

(** Simplification *)

module LevelUnionFind = Unionfind.Make (Univ.USet) (Univ.UMap)

let add_list_map u t map =
  try
    let l = UMap.find u map in
    UMap.update u (t :: l) map
  with Not_found ->
    UMap.add u [t] map

module UF = LevelUnionFind

(** Precondition: flexible <= ctx *)
let choose_canonical ctx flexible algs s =
  let global = USet.diff s ctx in
  let flexible, rigid = USet.partition flexible (USet.inter s ctx) in
    (** If there is a global universe in the set, choose it *)
    if not (USet.is_empty global) then
      let canon = USet.choose global in
	canon, (USet.remove canon global, rigid, flexible)
    else (** No global in the equivalence class, choose a rigid one *)
	if not (USet.is_empty rigid) then
	  let canon = USet.choose rigid in
	    canon, (global, USet.remove canon rigid, flexible)
	else (** There are only flexible universes in the equivalence
		 class, choose a non-algebraic. *)
	  let algs, nonalgs = USet.partition (fun x -> USet.mem x algs) flexible in
	    if not (USet.is_empty nonalgs) then
	      let canon = USet.choose nonalgs in
		canon, (global, rigid, USet.remove canon flexible)
	    else
	      let canon = USet.choose algs in
		canon, (global, rigid, USet.remove canon flexible)

let subst_univs_fn_puniverses lsubst (c, u as cu) =
  let u' = Instance.apply_subst lsubst u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_opt_subst f subst =
  let subst = fun l -> match UMap.find l subst with None -> raise Not_found | Some l' -> l' in
  let lsubst = Univ.univ_level_subst_of subst in
  let rec aux c =
    match kind_of_term c with
    | Evar (evk, args) ->
      let args = Array.map aux args in
      (match try f (evk, args) with Not_found -> None with
      | None -> c
      | Some c -> aux c)
    | Const pu -> 
      let pu' = subst_univs_fn_puniverses lsubst pu in
	if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
	if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
	if pu' == pu then c else mkConstructU pu'
    | Sort s ->
       let s' = Sorts.subst_sorts subst s in
       if s' == s then c else mkSort s'
    | _ -> map_constr aux c
  in aux

let fresh_universe_context_set_instance ctx =
  if ContextSet.is_empty ctx then UMap.empty, ctx
  else
    let (univs, cst) = ContextSet.levels ctx, ContextSet.constraints ctx in
    let univs',subst = USet.fold
      (fun u (univs',subst) ->
	let u' = fresh_level () in
	  (USet.add u' univs', UMap.add u u' subst))
      univs (USet.empty, UMap.empty)
    in
    let cst' = Sorts.level_subst_constraints subst cst in
      subst, (univs', cst')

let normalize_univ_variable ~find ~update =
  let rec aux cur =
    let b = find cur in
    let b' = subst_univs_universe aux b in
      if Universe.equal b' b then b
      else update cur b'
  in aux

let normalize_univ_variable_opt_subst ectx =
  let find l = 
    match Univ.UMap.find l !ectx with
    | Some b -> b
    | None -> raise Not_found
  in
  let update l b =
    assert (match Universe.level b with Some l' -> not (Level.equal l l') | None -> true);
    try ectx := Univ.UMap.add l (Some b) !ectx; b with Not_found -> assert false
  in normalize_univ_variable ~find ~update

let normalize_univ_variable_subst subst =
  let find l = Univ.UMap.find l !subst in
  let update l b =
    assert (match Universe.level b with Some l' -> not (Level.equal l l') | None -> true);
    try subst := Univ.UMap.update l b !subst; b with Not_found -> assert false in
    normalize_univ_variable ~find ~update

let normalize_universe_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
    subst_univs_universe normlevel

let normalize_sort_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
  Sorts.subst_sorts normlevel

let normalize_opt_subst ctx =
  let ectx = ref ctx in
  let normalize = normalize_univ_variable_opt_subst ectx in
  let () =
    Univ.UMap.iter (fun u v ->
      if Option.is_empty v then ()
      else try ignore(normalize u) with Not_found -> assert(false)) ctx 
  in !ectx

type universe_opt_subst = universe option universe_map
	  
let make_opt_subst s = 
  fun x -> 
    (match Univ.UMap.find x s with
    | Some u -> u
    | None -> raise Not_found)

let subst_opt_univs_constr s = 
  let f = make_opt_subst s in
    Vars.subst_univs_fn_constr f


let normalize_univ_variables ctx = 
  let ctx = normalize_opt_subst ctx in
  let undef, def, subst =
    Univ.UMap.fold (fun u v (undef, def, subst) ->
      match v with
      | None -> (Univ.USet.add u undef, def, subst)
      | Some b -> (undef, Univ.USet.add u def, Univ.UMap.add u b subst))
    ctx (Univ.USet.empty, Univ.USet.empty, Univ.UMap.empty)
  in ctx, undef, def, subst

let pr_universe_body = function
  | None -> mt ()
  | Some v -> str" := " ++ Univ.Universe.pr v

let pr_universe_opt_subst = Univ.UMap.pr pr_universe_body

let compare_constraint_type d d' =
  match d, d' with
  | Eq, Eq -> 0
  | Eq, _ -> -1
  | _, Eq -> 1
  | Le, Le -> 0
  | Le, _ -> -1
  | _, Le -> 1
  | Lt, Lt -> 0

type lowermap = constraint_type UMap.t

let lower_union =
  let merge k a b =
    match a, b with
    | Some _, None -> a
    | None, Some _ -> b
    | None, None -> None
    | Some l, Some r ->
       if compare_constraint_type l r >= 0 then a
       else b
  in UMap.merge merge

let lower_add l c m =
  try let c' = UMap.find l m in
      if compare_constraint_type c c' > 0 then
        UMap.add l c m
      else m
  with Not_found -> UMap.add l c m

let lower_of_list l =
  List.fold_left (fun acc (d,l) -> UMap.add l d acc) UMap.empty l

exception Found of Level.t * lowermap
let find_inst insts v =
  try UMap.iter (fun k (enf,alg,v',lower) ->
    if not alg && enf && Universe.equal v' v then raise (Found (k, lower)))
	insts; raise Not_found
  with Found (f,l) -> (f,l)

let compute_lbound left =
 (** The universe variable was not fixed yet.
     Compute its level using its lower bound. *)
  let sup l lbound = 
    match lbound with
    | None -> Some l
    | Some l' -> Some (Universe.sup l l')
  in
    List.fold_left (fun lbound (d, l) -> 
      if d == Le (* l <= ?u *) then sup l lbound
      else (* l < ?u *) 
	(assert (d == Lt); 
	 if Universe.is_level l then
	   sup (Universe.super l) lbound
	 else None))
      None left
  
let instantiate_with_lbound u lbound lower alg enforce (ctx, us, algs, insts, cstrs) =
  if enforce then
    let inst = Universe.make u in
    let cstrs' = univ_enforce_leq lbound inst cstrs in
      (ctx, us, USet.remove u algs,
       UMap.add u (enforce,alg,lbound,lower) insts, cstrs'),
      (enforce, alg, inst, lower)
  else (* Actually instantiate *)
    (Univ.USet.remove u ctx, Univ.UMap.add u (Some lbound) us, algs,
     UMap.add u (enforce,alg,lbound,lower) insts, cstrs),
    (enforce, alg, lbound, lower)

type constraints_map = (Sorts.constraint_type * Univ.UMap.key) list Univ.UMap.t

let pr_constraints_map cmap =
  UMap.fold (fun l cstrs acc ->
    Level.pr l ++ str " => " ++ 
      prlist_with_sep spc (fun (d,r) -> pr_constraint_type d ++ Level.pr r) cstrs ++
      fnl () ++ acc)
    cmap (mt ())

let remove_alg l (ctx, us, algs, insts, cstrs) =
  (ctx, us, USet.remove l algs, insts, cstrs)

let remove_lower u lower =
  let levels = Universe.levels u in
  USet.fold (fun l acc -> UMap.remove l acc) levels lower
    
let minimize_univ_variables ctx us algs left right cstrs =
  let left, lbounds = 
    Univ.UMap.fold (fun r lower (left, lbounds as acc)  ->
      if Univ.UMap.mem r us || not (Univ.USet.mem r ctx) then acc
      else (* Fixed universe, just compute its glb for sharing *)
	let lbounds' = 
	  match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
	  | None -> lbounds
	  | Some lbound -> UMap.add r (true, false, lbound, lower_of_list lower)
                                   lbounds
	in (Univ.UMap.remove r left, lbounds'))
      left (left, Univ.UMap.empty)
  in
  let rec instance (ctx', us, algs, insts, cstrs as acc) u =
    let acc, left, lower =
      try
        let l = UMap.find u left in
	let acc, left, newlow, lower =
          List.fold_left
	  (fun (acc, left', newlow, lower') (d, l) ->
	   let acc', (enf,alg,l',lower) = aux acc l in
	   let l' =
	     if enf then Universe.make l
	     else l'
	   in acc', (d, l') :: left',
              lower_add l d newlow, lower_union lower lower')
	  (acc, [], UMap.empty, UMap.empty) l
        in
        let not_lower (d,l) =
        (* We're checking if (d,l) is already implied by the lower
	  constraints on some level u. If it represents l < u (d is Lt
	  or d is Le and i > 0, the i < 0 case is impossible due to
	  invariants of Univ), and the lower constraints only have l <=
	  u then it is not implied. *)
          Univ.Universe.exists
          (fun (l,i) ->
             let d =
               if i == 0 then d
               else match d with
                    | Le -> Lt
                    | d -> d
             in
             try let d' = UMap.find l lower in
                 (* If d is stronger than the already implied lower
                  * constraints we must keep it. *)
                 compare_constraint_type d d' > 0
             with Not_found ->
               (** No constraint existing on l *) true) l
        in
        let left = List.uniquize (List.filter not_lower left) in
        (acc, left, UMap.union newlow lower)
      with Not_found -> acc, [], UMap.empty
    and right =
      try Some (UMap.find u right)
      with Not_found -> None
    in
    let instantiate_lbound lbound =
      let alg = USet.mem u algs in
	if alg then
	  (* u is algebraic: we instantiate it with its lower bound, if any,
              or enforce the constraints if it is bounded from the top. *)
          let lower = remove_lower lbound lower in
	  instantiate_with_lbound u lbound lower true false acc
	else (* u is non algebraic *)
	  match Universe.level lbound with
	  | Some l -> (* The lowerbound is directly a level *) 
	     (* u is not algebraic but has no upper bounds,
  	        we instantiate it with its lower bound if it is a 
	        different level, otherwise we keep it. *)
             let lower = UMap.remove l lower in
	     if not (Level.equal l u) then
	       (* Should check that u does not 
  	          have upper constraints that are not already in right *)
	       let acc' = remove_alg l acc in
		 instantiate_with_lbound u lbound lower false false acc'
	     else acc, (true, false, lbound, lower)
	  | None ->
	     try
	       (* Another universe represents the same lower bound,
                  we can share them with no harm. *)
	       let can, lower = find_inst insts lbound in
               let lower = UMap.remove can lower in
	       instantiate_with_lbound u (Universe.make can) lower false false acc
	  with Not_found -> 
	    (* We set u as the canonical universe representing lbound *)
	    instantiate_with_lbound u lbound lower false true acc
    in
    let acc' acc = 
      match right with
      | None -> acc
      | Some cstrs -> 
	let dangling = List.filter (fun (d, r) -> not (UMap.mem r us)) cstrs in
	  if List.is_empty dangling then acc
	  else
	    let ((ctx', us, algs, insts, cstrs), (enf,_,inst,lower as b)) = acc in
	    let cstrs' = List.fold_left (fun cstrs (d, r) -> 
	      if d == Sorts.Le then
		univ_enforce_leq inst (Universe.make r) cstrs
	      else
		try let lev = Option.get (Universe.level inst) in
		      Constraint.add_univ (lev, d, r) cstrs
		with Option.IsNone -> failwith "")
	      cstrs dangling
	    in
	      (ctx', us, algs, insts, cstrs'), b
    in
      if not (USet.mem u ctx) then acc' (acc, (true, false, Universe.make u, lower))
      else
	let lbound = compute_lbound left in
	  match lbound with
	  | None -> (* Nothing to do *)
	    acc' (acc, (true, false, Universe.make u, lower))
	  | Some lbound ->
	     try acc' (instantiate_lbound lbound) 
	     with Failure _ -> acc' (acc, (true, false, Universe.make u, lower))
  and aux (ctx', us, algs, seen, cstrs as acc) u =
    try acc, UMap.find u seen
    with Not_found -> instance acc u
  in
    UMap.fold (fun u v (ctx', us, algs, seen, cstrs as acc) ->
      if v == None then fst (aux acc u)
      else USet.remove u ctx', us, USet.remove u algs, seen, cstrs)
      us (ctx, us, algs, lbounds, cstrs)

let normalize_context_set ctx us algs = 
  let (ctx, csts) = ContextSet.levels ctx, ContextSet.constraints ctx in
  let uf = UF.create () in
  (** Keep the Prop/Set <= i constraints separate for minimization *)
  let smallles, csts =
    Constraint.fold (fun (UnivConstraint (l,d,r) as cstr) (smallles, noneqs) ->
        if d == Le then
	  if Univ.Level.is_small l then
	    if is_set_minimization () && USet.mem r ctx then
	      (Constraint.add cstr smallles, noneqs)
	    else (smallles, noneqs)
	  else if Level.is_small r then
	    if Level.is_prop r then
	      raise (Sorts.UniverseInconsistency
		       (Le,Universe.make l,Universe.make r,None))
	    else (smallles, Constraint.add_univ (l,Eq,r) noneqs)
	  else (smallles, Constraint.add cstr noneqs)
	else (smallles, Constraint.add cstr noneqs))
    csts (Constraint.empty, Constraint.empty)
  in
  let csts = 
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = Univ.USet.fold (fun v g -> Sorts.Graph.add_universe v false g)
			   ctx Sorts.Graph.initial
    in
    let g =
      Sorts.Constraint.fold
	(fun (UnivConstraint (l, d, r)) g ->
	 let g =
	   if not (Level.is_small l || USet.mem l ctx) then
	     try Sorts.Graph.add_universe l false g
	     with Sorts.Graph.AlreadyDeclared -> g
	   else g
	 in
	 let g =
	   if not (Level.is_small r || USet.mem r ctx) then
	     try Sorts.Graph.add_universe r false g
	     with Sorts.Graph.AlreadyDeclared -> g
	   else g
	 in g) csts g
    in
    let g = Sorts.Constraint.fold Sorts.Graph.enforce_constraint csts g in
      Sorts.Graph.to_constraints g
  in
  let noneqs =
    Constraint.fold (fun (UnivConstraint (l,d,r) as cstr) noneqs ->
      if d == Eq then (UF.union l r uf; noneqs)
      else (* We ignore the trivial Prop/Set <= i constraints. *)
	if d == Le && Univ.Level.is_small l then noneqs
	else if Univ.Level.is_prop l && d == Lt && Univ.Level.is_set r
	then noneqs
	else Constraint.add cstr noneqs)
      csts Constraint.empty
  in
  let noneqs = Constraint.union noneqs smallles in
  let partition = UF.partition uf in
  let flex x = UMap.mem x us in
  let ctx, subst, us, eqs = List.fold_left (fun (ctx, subst, us, cstrs) s ->
    let canon, (global, rigid, flexible) = choose_canonical ctx flex algs s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = USet.fold (fun g cst ->
      Constraint.add_univ (canon, Eq, g) cst) global
      cstrs 
    in
    (* Also add equalities for rigid variables *)
    let cstrs = USet.fold (fun g cst ->
      Constraint.add_univ (canon, Eq, g) cst) rigid
      cstrs
    in
    let subst = USet.fold (fun f -> UMap.add f canon) rigid subst in
    let subst = USet.fold (fun f -> UMap.add f canon) flexible subst in
    let canonu = Some (Universe.make canon) in
    let us = USet.fold (fun f -> UMap.add f canonu) flexible us in
      (USet.diff ctx flexible, subst, us, cstrs))
    (ctx, UMap.empty, us, Constraint.empty) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let noneqs = level_subst_constraints subst noneqs in
  (* Compute the left and right set of flexible variables, constraints
     mentionning other variables remain in noneqs. *)
  let noneqs, ucstrsl, ucstrsr = 
    Constraint.fold (fun (UnivConstraint (l,d,r) as cstr) (noneq, ucstrsl, ucstrsr) ->
      let lus = UMap.mem l us and rus = UMap.mem r us in
      let ucstrsl' = 
	if lus then add_list_map l (d, r) ucstrsl
	else ucstrsl
      and ucstrsr' = 
	add_list_map r (d, l) ucstrsr
      in 
      let noneqs = 
	if lus || rus then noneq 
	else Constraint.add cstr noneq
      in (noneqs, ucstrsl', ucstrsr'))
    noneqs (Constraint.empty, UMap.empty, UMap.empty)
  in
  (* Now we construct the instantiation of each variable. *)
  let ctx', us, algs, inst, noneqs = 
    minimize_univ_variables ctx us algs ucstrsr ucstrsl noneqs
  in
  let us = normalize_opt_subst us in
    (us, algs), (ctx', Constraint.union noneqs eqs)

(* let normalize_conkey = Profile.declare_profile "normalize_context_set" *)
(* let normalize_context_set a b c = Profile.profile3 normalize_conkey normalize_context_set a b c *)

let universes_of_constr c =
  let rec aux s c = 
    match kind_of_term c with
    | Const (_, u) | Ind (_, u) | Construct (_, u) ->
      USet.fold USet.add (Instance.to_set u) s
    | Sort u when not (Sorts.is_small u) ->
      USet.fold USet.add (Sorts.levels u) s
    | _ -> fold_constr aux s c
  in aux USet.empty c

let restrict_universe_context (univs,csts) s =
  (* Universes that are not necessary to typecheck the term.
     E.g. univs introduced by tactics and not used in the proof term. *)
  let diff = USet.diff univs s in
  let rec aux diff candid univs ness = 
    let (diff', candid', univs', ness') = 
      Constraint.fold
	(fun (UnivConstraint (l, d, r) as c) (diff, candid, univs, csts) ->
	  if not (USet.mem l diff) then
	    (USet.remove r diff, candid, univs, Constraint.add c csts)
	  else if not (USet.mem r diff) then
	    (USet.remove l diff, candid, univs, Constraint.add c csts)
	  else (diff, Constraint.add c candid, univs, csts))
	candid (diff, Constraint.empty, univs, ness)
    in
      if ness' == ness then (USet.diff univs diff', ness)
      else aux diff' candid' univs' ness'
  in aux diff csts univs Constraint.empty

let simplify_universe_context (univs,csts) =
  let uf = UF.create () in
  let noneqs =
    Constraint.fold (fun (UnivConstraint (l,d,r)) noneqs ->
      if d == Eq && (USet.mem l univs || USet.mem r univs) then
	(UF.union l r uf; noneqs)
      else Constraint.add_univ (l,d,r) noneqs)
      csts Constraint.empty
  in
  let partition = UF.partition uf in
  let flex x = USet.mem x univs in
  let subst, univs', csts' = List.fold_left (fun (subst, univs, cstrs) s -> 
    let canon, (global, rigid, flexible) = choose_canonical univs flex USet.empty s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = USet.fold (fun g cst ->
      Constraint.add_univ (canon, Eq, g) cst) (USet.union global rigid)
      cstrs 
    in
    let subst = USet.fold (fun f -> UMap.add f canon)
      flexible subst
    in (subst, USet.diff univs flexible, cstrs))
    (UMap.empty, univs, noneqs) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let csts' = level_subst_constraints subst csts' in
    (univs', csts'), subst

let is_trivial_leq (l,d,r) =
  Univ.Level.is_prop l && (d == Le || (d == Lt && Univ.Level.is_set r))

(* Prop < i <-> Set+1 <= i <-> Set < i *)
let translate_cstr (l,d,r as cstr) =
  if Level.equal Level.prop l && d == Lt && not (Level.equal Level.set r) then
    (Level.set, d, r)
  else cstr

let refresh_constraints univs (ctx, cstrs) =
  let cstrs', univs' = 
    Sorts.Constraint.fold (fun (UnivConstraint c as c0) (cstrs', univs as acc) ->
      let c = translate_cstr c in
      if is_trivial_leq c then acc
      else (Sorts.Constraint.add c0 cstrs', Sorts.Graph.enforce_constraint c0 univs))
      cstrs (Sorts.Constraint.empty, univs)
  in ((ctx, cstrs'), univs')