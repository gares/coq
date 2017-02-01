(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names

module StringOrd = struct type t = string let compare = String.compare end
module UNameMap = struct
    
  include Map.Make(StringOrd)
    
  let union s t = 
    if s == t then s
    else
      merge (fun k l r -> 
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t
end

type uinfo = {
  uname : string option;
  uloc : Loc.t option;
}

(* 2nd part used to check consistency on the fly. *)
type t =
 { uctx_names : Univ.Level.t UNameMap.t * uinfo Univ.UMap.t;
   uctx_local : Sorts.universe_context_set; (** The local context of variables *)
   uctx_univ_variables : Universes.universe_opt_subst;
   (** The local universes that are unification variables *)
   uctx_univ_algebraic : Univ.universe_set; 
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   uctx_universes : Sorts.Graph.t; (** The current graph extended with the local constraints *)
   uctx_initial_universes : Sorts.Graph.t; (** The graph at the creation of the evar_map *)
 }
  
let empty =
  { uctx_names = UNameMap.empty, Univ.UMap.empty;
    uctx_local = Sorts.ContextSet.empty;
    uctx_univ_variables = Univ.UMap.empty;
    uctx_univ_algebraic = Univ.USet.empty;
    uctx_universes = Sorts.Graph.initial;
    uctx_initial_universes = Sorts.Graph.initial; }

let make u =
    { empty with 
      uctx_universes = u; uctx_initial_universes = u}

let is_empty ctx =
  Sorts.ContextSet.is_empty ctx.uctx_local &&
    Univ.UMap.is_empty ctx.uctx_univ_variables

let union ctx ctx' =
  if ctx == ctx' then ctx
  else if is_empty ctx' then ctx
  else
    let local = Sorts.ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let names = UNameMap.union (fst ctx.uctx_names) (fst ctx'.uctx_names) in
    let newus = Univ.USet.diff (Sorts.ContextSet.levels ctx'.uctx_local)
                               (Sorts.ContextSet.levels ctx.uctx_local) in
    let newus = Univ.USet.diff newus (Univ.UMap.domain ctx.uctx_univ_variables) in
    let declarenew g =
      Univ.USet.fold (fun u g -> Sorts.Graph.add_universe u false g) newus g
    in
    let names_rev = Univ.UMap.union (snd ctx.uctx_names) (snd ctx'.uctx_names) in
      { uctx_names = (names, names_rev);
        uctx_local = local;
        uctx_univ_variables = 
          Univ.UMap.subst_union ctx.uctx_univ_variables ctx'.uctx_univ_variables;
        uctx_univ_algebraic = 
          Univ.USet.union ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
        uctx_initial_universes = declarenew ctx.uctx_initial_universes;
        uctx_universes = 
          if local == ctx.uctx_local then ctx.uctx_universes
          else
            let cstrsr = Sorts.ContextSet.constraints ctx'.uctx_local in
            Sorts.Graph.merge_constraints cstrsr (declarenew ctx.uctx_universes) }

let context_set ctx = ctx.uctx_local

let constraints ctx = snd ctx.uctx_local

let context ctx = Sorts.ContextSet.to_context ctx.uctx_local

let of_context_set ctx = { empty with uctx_local = ctx }

let subst ctx = ctx.uctx_univ_variables

let ugraph ctx = ctx.uctx_universes

let algebraics ctx = ctx.uctx_univ_algebraic

let constrain_variables diff ctx =
  Univ.USet.fold
    (fun l cstrs ->
      try
        match Univ.UMap.find l ctx.uctx_univ_variables with
        | Some u -> Sorts.Constraint.add_univ (l, Sorts.Eq, Option.get (Univ.Universe.level u)) cstrs
        | None -> cstrs
      with Not_found | Option.IsNone -> cstrs)
    diff Sorts.Constraint.empty

let add_uctx_names ?loc s l (names, names_rev) =
  (UNameMap.add s l names, Univ.UMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, Univ.UMap.add l { uname = None; uloc = loc } names_rev)

let of_binders b =
  let ctx = empty in
  let names =
    List.fold_left (fun acc (id, l) -> add_uctx_names (Id.to_string id) l acc)
                   ctx.uctx_names b
  in { ctx with uctx_names = names }

let instantiate_variable l b v =
  try v := Univ.UMap.update l (Some b) !v
  with Not_found -> assert false

exception UniversesDiffer

let process_universe_constraints ctx cstrs =
  let univs = ctx.uctx_universes in
  let vars = ref ctx.uctx_univ_variables in
  let normalize = Universes.normalize_universe_opt_subst vars in
  let rec unify_universes fo l d r local =
    let l = normalize l and r = normalize r in
      if Univ.Universe.equal l r then local
      else 
        let varinfo x = 
          match Univ.Universe.level x with
          | None -> Inl x
          | Some l -> Inr (l, Univ.UMap.mem l !vars, Univ.USet.mem l ctx.uctx_univ_algebraic)
        in
        begin match d with
        | Universes.ULe ->
            if Sorts.Graph.univ_check_leq univs l r then
              (** Keep Prop/Set <= var around if var might be instantiated by prop or set
                  later. *)
              match Univ.Universe.level l, Univ.Universe.level r with
              | Some l, Some r ->
                 Sorts.Constraint.add_univ (l, Sorts.Le, r) local
              | _ -> local
            else
              begin match Univ.Universe.level r with
              | None -> error ("Algebraic universe on the right")
              | Some rl ->
                if Univ.Level.is_small rl then
                  let levels = Univ.Universe.levels l in
                    Univ.USet.fold (fun l local ->
                      if Univ.Level.is_small l || Univ.UMap.mem l !vars then
                        unify_universes fo (Univ.Universe.make l) Universes.UEq r local
                      else raise (Sorts.UniverseInconsistency (Sorts.Le, Univ.Universe.make l, r, None)))
                      levels local
                else
                  Sorts.univ_enforce_leq l r local
              end
        | Universes.ULub ->
            begin match varinfo l, varinfo r with
            | (Inr (l, true, _), Inr (r, _, _)) 
            | (Inr (r, _, _), Inr (l, true, _)) -> 
              instantiate_variable l (Univ.Universe.make r) vars; 
              Sorts.univ_enforce_eq_level l r local
            | Inr (_, _, _), Inr (_, _, _) ->
              unify_universes true l Universes.UEq r local
            | _, _ -> assert false
            end
        | Universes.UEq ->
            begin match varinfo l, varinfo r with
            | Inr (l', lloc, _), Inr (r', rloc, _) ->
              let () = 
                if lloc then
                  instantiate_variable l' r vars
                else if rloc then 
                  instantiate_variable r' l vars
                else if not (Sorts.Graph.univ_check_eq univs l r) then
                  (* Two rigid/global levels, none of them being local,
                     one of them being Prop/Set, disallow *)
                  if Univ.Level.is_small l' || Univ.Level.is_small r' then
                    raise (Sorts.UniverseInconsistency (Sorts.Eq, l, r, None))
                  else
                    if fo then 
                      raise UniversesDiffer
              in
                Sorts.univ_enforce_eq_level l' r' local
            | Inr (l, loc, alg), Inl r
            | Inl r, Inr (l, loc, alg) ->
               let inst = Univ.univ_level_rem l r r in
                 if alg then (instantiate_variable l inst vars; local)
                 else
                   let lu = Univ.Universe.make l in
                   if Univ.univ_level_mem l r then
                     Sorts.univ_enforce_leq inst lu local
                   else raise (Sorts.UniverseInconsistency (Sorts.Eq, lu, r, None))
            | _, _ (* One of the two is algebraic or global *) -> 
             if Sorts.Graph.univ_check_eq univs l r then local
             else raise (Sorts.UniverseInconsistency (Sorts.Eq, l, r, None))
            end
        end
  in
  let local = 
    Universes.Constraints.fold (fun (l,d,r) local ->
        unify_universes false (Sorts.univ_of_sort l) d (Sorts.univ_of_sort r) local)
      cstrs Sorts.Constraint.empty
  in
    !vars, local

let add_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let cstrs' = Sorts.Constraint.fold (fun (Sorts.UnivConstraint (l,d,r)) acc ->
    let l = Sorts.of_level l and r = Sorts.of_level r in
    let cstr' =
      match d with
      | Sorts.Lt -> (Sorts.super l, Universes.ULe, r)
      | Sorts.Le -> (l, Universes.ULe, r)
      | Sorts.Eq -> (l, Universes.UEq, r)
    in Universes.Constraints.add cstr' acc)
    cstrs Universes.Constraints.empty
  in
  let vars, local' = process_universe_constraints ctx cstrs' in
    { ctx with uctx_local = (univs, Sorts.Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = Sorts.Graph.merge_constraints local' ctx.uctx_universes }

(* let addconstrkey = Profile.declare_profile "add_constraints_context";; *)
(* let add_constraints_context = Profile.profile2 addconstrkey add_constraints_context;; *)

let add_universe_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let vars, local' = process_universe_constraints ctx cstrs in
    { ctx with uctx_local = (univs, Sorts.Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = Sorts.Graph.merge_constraints local' ctx.uctx_universes }

let pr_uctx_level uctx = 
  let map, map_rev = uctx.uctx_names in 
    fun l ->
      try str (Option.get (Univ.UMap.find l map_rev).uname)
      with Not_found | Option.IsNone ->
        Universes.pr_with_global_universes l

let universe_context ?names ctx =
  match names with
  | None -> [], Sorts.ContextSet.to_context ctx.uctx_local
  | Some pl ->
     let levels = Sorts.ContextSet.levels ctx.uctx_local in
     let newinst, map, left =
       List.fold_right
         (fun (loc,id) (newinst, map, acc) ->
          let l =
            try UNameMap.find (Id.to_string id) (fst ctx.uctx_names)
            with Not_found ->
              user_err ~loc ~hdr:"universe_context"
                            (str"Universe " ++ Nameops.pr_id id ++ str" is not bound anymore.")
          in (l :: newinst, (id, l) :: map, Univ.USet.remove l acc))
         pl ([], [], levels)
     in
       if not (Univ.USet.is_empty left) then
         let n = Univ.USet.cardinal left in
         let loc =
           try
             let info =
               Univ.UMap.find (Univ.USet.choose left) (snd ctx.uctx_names) in
             Option.default Loc.ghost info.uloc
           with Not_found -> Loc.ghost
         in
           user_err ~loc ~hdr:"universe_context"
                        ((str(CString.plural n "Universe") ++ spc () ++
			     Univ.USet.pr (pr_uctx_level ctx) left ++
			   spc () ++ str (CString.conjugate_verb_to_be n) ++
                           str" unbound."))
      else
        let inst = Sorts.Instance.of_array (Array.of_list newinst) in
        let ctx = Sorts.UContext.make (inst,
          Sorts.ContextSet.constraints ctx.uctx_local)
        in map, ctx

let restrict ctx vars =
  let uctx' = Universes.restrict_universe_context ctx.uctx_local vars in
  { ctx with uctx_local = uctx' }

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let merge ?loc sideff rigid uctx ctx' =
  let open Univ in
  let levels = Sorts.ContextSet.levels ctx' in
  let uctx = if sideff then uctx else
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      let fold u accu =
        if UMap.mem u accu then accu
        else UMap.add u None accu
      in
      let uvars' = USet.fold fold levels uctx.uctx_univ_variables in
        if b then
          { uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = USet.union uctx.uctx_univ_algebraic levels }
        else { uctx with uctx_univ_variables = uvars' }
  in
  let uctx_local =
    if sideff then uctx.uctx_local
    else Sorts.ContextSet.append ctx' uctx.uctx_local
  in
  let declare g =
    USet.fold (fun u g ->
               try Sorts.Graph.add_universe u false g
               with Sorts.Graph.AlreadyDeclared when sideff -> g)
              levels g
  in
  let uctx_names =
    let fold u accu =
      let modify _ info = match info.uloc with
      | None -> { info with uloc = loc }
      | Some _ -> info
      in
      try UMap.modify u modify accu
      with Not_found -> UMap.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.uctx_names, USet.fold fold levels (snd uctx.uctx_names))
  in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare uctx.uctx_universes in
  let uctx_universes = Sorts.Graph.merge_constraints (Sorts.ContextSet.constraints ctx') univs in
  { uctx with uctx_names; uctx_local; uctx_universes;
              uctx_initial_universes = initial }

let merge_subst uctx s =
  { uctx with uctx_univ_variables = Univ.UMap.subst_union uctx.uctx_univ_variables s }

let emit_side_effects eff u =
  let uctxs = Safe_typing.universes_of_private eff in
  List.fold_left (merge true univ_rigid) u uctxs

let new_univ_variable ?loc rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as uctx) =
  let u = Universes.new_univ_level () in
  let ctx' = Sorts.ContextSet.add_universe u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b -> 
      let uvars' = Univ.UMap.add u None uvars in
        if b then {uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = Univ.USet.add u avars}, false
        else {uctx with uctx_univ_variables = uvars'}, false
  in
  let names = 
    match name with
    | Some n -> add_uctx_names ?loc n u uctx.uctx_names
    | None -> add_uctx_loc u loc uctx.uctx_names
  in
  let initial =
    Sorts.Graph.add_universe u false uctx.uctx_initial_universes
  in                                                 
  let uctx' =
    {uctx' with uctx_names = names; uctx_local = ctx';
                uctx_universes = Sorts.Graph.add_universe u false uctx.uctx_universes;
                uctx_initial_universes = initial}
  in uctx', u

let add_global_univ uctx u =
  let initial =
    Sorts.Graph.add_universe u true uctx.uctx_initial_universes
  in
  let univs = 
    Sorts.Graph.add_universe u true uctx.uctx_universes
  in
  { uctx with uctx_local = Sorts.ContextSet.add_universe u uctx.uctx_local;
                                     uctx_initial_universes = initial;
                                     uctx_universes = univs }

let make_flexible_variable ctx b u =
  let {uctx_univ_variables = uvars; uctx_univ_algebraic = avars} = ctx in
  let uvars' = Univ.UMap.add u None uvars in
  let avars' = 
    if b then
      let uu = Univ.Universe.make u in
      let substu_not_alg u' v =
        Option.cata (fun vu -> Univ.Universe.equal uu vu && not (Univ.USet.mem u' avars)) false v
      in
        if not (Univ.UMap.exists substu_not_alg uvars)
        then Univ.USet.add u avars else avars
    else avars 
  in
  {ctx with uctx_univ_variables = uvars'; 
      uctx_univ_algebraic = avars'}

let is_sort_variable uctx s = 
  match Sorts.level s with
  | Some l as x ->
     if Univ.USet.mem l (Sorts.ContextSet.levels uctx.uctx_local) then x
     else None
  | None -> None

let subst_univs_context_with_def def usubst (ctx, cst) =
  (Univ.USet.diff ctx def, Sorts.subst_constraints usubst cst)

let normalize_variables uctx =
  let normalized_variables, undef, def, subst = 
    Universes.normalize_univ_variables uctx.uctx_univ_variables 
  in
  let ctx_local = subst_univs_context_with_def def (Univ.make_univ_subst subst) uctx.uctx_local in
  let ctx_local', univs = Universes.refresh_constraints uctx.uctx_initial_universes ctx_local in
    subst, { uctx with uctx_local = ctx_local';
      uctx_univ_variables = normalized_variables;
      uctx_universes = univs }

let abstract_undefined_variables uctx =
  let vars' = 
    Univ.UMap.fold (fun u v acc ->
      if v == None then Univ.USet.remove u acc
      else acc)
    uctx.uctx_univ_variables uctx.uctx_univ_algebraic
  in { uctx with uctx_local = Sorts.ContextSet.empty;
      uctx_univ_algebraic = vars' }

let fix_undefined_variables uctx =
  let algs', vars' = 
    Univ.UMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (Univ.USet.remove u algs, Univ.UMap.remove u vars)
      else acc)
      uctx.uctx_univ_variables 
      (uctx.uctx_univ_algebraic, uctx.uctx_univ_variables)
  in
  { uctx with uctx_univ_variables = vars';
    uctx_univ_algebraic = algs' }

let refresh_undefined_univ_variables uctx =
  let subst, ctx' = Universes.fresh_universe_context_set_instance uctx.uctx_local in
  let alg = Univ.USet.fold (fun u acc -> Univ.USet.add (Univ.subst_univs_level_level subst u) acc)
    uctx.uctx_univ_algebraic Univ.USet.empty
  in
  let vars = 
    Univ.UMap.fold
      (fun u v acc ->
        Univ.UMap.add (Univ.subst_univs_level_level subst u)
          (Option.map (Univ.subst_univs_level_universe subst) v) acc)
      uctx.uctx_univ_variables Univ.UMap.empty
  in
  let declare g = Univ.USet.fold (fun u g -> Sorts.Graph.add_universe u false g)
                                   (Sorts.ContextSet.levels ctx') g in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare Sorts.Graph.initial in
  let uctx' = {uctx_names = uctx.uctx_names;
               uctx_local = ctx'; 
               uctx_univ_variables = vars; uctx_univ_algebraic = alg;
               uctx_universes = univs;
               uctx_initial_universes = initial } in
    uctx', subst

let normalize uctx = 
  let ((vars',algs'), us') = 
    Universes.normalize_context_set uctx.uctx_local uctx.uctx_univ_variables
				    uctx.uctx_univ_algebraic
  in
  if Sorts.ContextSet.equal us' uctx.uctx_local then uctx
  else
    let us', universes =
      Universes.refresh_constraints uctx.uctx_initial_universes us'
    in
      { uctx_names = uctx.uctx_names;
        uctx_local = us'; 
        uctx_univ_variables = vars'; 
        uctx_univ_algebraic = algs';
        uctx_universes = universes;
        uctx_initial_universes = uctx.uctx_initial_universes }

let universe_of_name uctx s = 
  UNameMap.find s (fst uctx.uctx_names)

let add_universe_name uctx s l =
  let names' = add_uctx_names s l uctx.uctx_names in
  { uctx with uctx_names = names' }

let update_sigma_env uctx env =
  let univs = Environ.universes env in
  let eunivs =
    { uctx with uctx_initial_universes = univs;
                         uctx_universes = univs }
  in
  merge true univ_rigid eunivs eunivs.uctx_local
