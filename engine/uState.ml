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
 { uctx_unames : Univ.Level.t UNameMap.t * uinfo Univ.UMap.t;
   uctx_tnames : Trunc.TLevel.t UNameMap.t * uinfo Trunc.TMap.t;
   uctx_local : Sorts.universe_context_set; (** The local context of variables *)
   uctx_univ_variables : Universes.universe_opt_subst;
  (** The local universes that are unification variables *)
   uctx_univ_algebraic : Univ.universe_set;
   uctx_trunc_algebraic : Trunc.truncation_set;
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   uctx_universes : Sorts.Graph.t; (** The current graph extended with the local constraints *)
   uctx_initial_universes : Sorts.Graph.t; (** The graph at the creation of the evar_map *)
 }
  
let empty =
  { uctx_unames = UNameMap.empty, Univ.UMap.empty;
    uctx_tnames = UNameMap.empty, Trunc.TMap.empty;
    uctx_local = Sorts.ContextSet.empty;
    uctx_univ_variables = Universes.empty_opt_subst;
    uctx_univ_algebraic = Univ.USet.empty;
    uctx_trunc_algebraic = Trunc.TSet.empty;
    uctx_universes = Sorts.Graph.initial;
    uctx_initial_universes = Sorts.Graph.initial; }

let make u =
    { empty with 
      uctx_universes = u; uctx_initial_universes = u}

let is_empty ctx =
  Sorts.ContextSet.is_empty ctx.uctx_local &&
    Universes.is_empty_opt_subst ctx.uctx_univ_variables

let union ctx ctx' =
  if ctx == ctx' then ctx
  else if is_empty ctx' then ctx
  else
    let local = Sorts.ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let unames = UNameMap.union (fst ctx.uctx_unames) (fst ctx'.uctx_unames) in
    let tnames = UNameMap.union (fst ctx.uctx_tnames) (fst ctx'.uctx_tnames) in
    let unames_rev = Univ.UMap.union (snd ctx.uctx_unames) (snd ctx'.uctx_unames) in
    let tnames_rev = Trunc.TMap.union (snd ctx.uctx_tnames) (snd ctx'.uctx_tnames) in
    let newus = Univ.USet.diff (Sorts.ContextSet.univ_levels ctx'.uctx_local)
                               (Sorts.ContextSet.univ_levels ctx.uctx_local) in
    let newus = Univ.USet.diff newus (Univ.UMap.domain (fst ctx.uctx_univ_variables)) in
    let newts = Trunc.TSet.diff (Sorts.ContextSet.trunc_levels ctx'.uctx_local)
                               (Sorts.ContextSet.trunc_levels ctx.uctx_local) in
    let newts = Trunc.TSet.diff newts (Trunc.TMap.domain (snd ctx.uctx_univ_variables)) in
    let declarenew g =
      g
      |> Univ.USet.fold (fun u g -> Sorts.Graph.add_universe u false g) newus
      |> Trunc.TSet.fold (fun u g -> Sorts.Graph.add_truncation u g) newts
    in
    { uctx_unames = (unames, unames_rev);
      uctx_tnames = (tnames, tnames_rev);
      uctx_local = local;
      uctx_univ_variables =
        Universes.opt_subst_union ctx.uctx_univ_variables ctx'.uctx_univ_variables;
      uctx_univ_algebraic =
        Univ.USet.union ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
      uctx_trunc_algebraic =
        Trunc.TSet.union ctx.uctx_trunc_algebraic ctx'.uctx_trunc_algebraic;
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

let algebraic_univs ctx = ctx.uctx_univ_algebraic
let algebraic_truncs ctx = ctx.uctx_trunc_algebraic

let constrain_variables udiff tdiff ctx =
  Sorts.Constraint.empty
  |> Univ.USet.fold
       (fun l cstrs ->
         try
           match Univ.UMap.find l (fst ctx.uctx_univ_variables) with
           | Some u ->
              Sorts.Constraint.add_univ (l, Sorts.Eq, Option.get (Univ.Universe.level u)) cstrs
           | None -> cstrs
         with Not_found | Option.IsNone -> cstrs)
       udiff
  |> Trunc.TSet.fold
       (fun l cstrs ->
         try
           match Trunc.TMap.find l (snd ctx.uctx_univ_variables) with
           | Some u ->
              Sorts.Constraint.add_trunc (l, Sorts.Eq, Option.get (Trunc.Truncation.level u)) cstrs
           | None -> cstrs
         with Not_found | Option.IsNone -> cstrs)
       tdiff

let add_uctx_unames ?loc s l (names, names_rev) =
  (UNameMap.add s l names, Univ.UMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_tnames ?loc s l (names, names_rev) =
  (UNameMap.add s l names, Trunc.TMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_univ_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, Univ.UMap.add l { uname = None; uloc = loc } names_rev)

let add_uctx_trunc_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, Trunc.TMap.add l { uname = None; uloc = loc } names_rev)

let of_binders (b:Universes.universe_binders) =
  let ctx = empty in
  let unames =
    List.fold_left (fun acc (id, l) -> add_uctx_unames (Id.to_string id) l acc)
                   ctx.uctx_unames b.Universes.univ_binders
  in
  let tnames =
    List.fold_left (fun acc (id, l) -> add_uctx_tnames (Id.to_string id) l acc)
                   ctx.uctx_tnames b.Universes.trunc_binders
  in
  { ctx with uctx_unames = unames; uctx_tnames = tnames }

let instantiate_univ_variable l b v =
  let uv, tv = !v in
  try v := Univ.UMap.update l (Some b) uv, tv
  with Not_found -> assert false

let instantiate_trunc_variable l b v =
  let uv, tv = !v in
  try v := uv, Trunc.TMap.update l (Some b) tv
  with Not_found -> assert false

exception UniversesDiffer

type opt_subst = Universes.universe_opt_subst

module type UnifyIn = sig
  type level
  type algebraic

  val algebraic_equal : algebraic -> algebraic -> bool

  module LSet : CSig.SetS with type elt = level
  module LMap : CMap.ExtS with type key = level and module Set := LSet

  val level : algebraic -> level option
  val levels : algebraic -> LSet.t

  val make_alg : level -> algebraic
  val level_mem : level -> algebraic -> bool
  val level_rem : level -> algebraic -> algebraic -> algebraic

  val is_minimal : level -> bool

  (* Univ mode: do not allow [l = Set] when [l] is rigid.
     Trunc mode: do allow [l = HSet] even when [l] is rigid. *)
  val allow_eq_rigid_litteral : bool

  val opt_subst_mem : level -> opt_subst -> bool
  val normalize : opt_subst ref -> algebraic -> algebraic

  val instantiate_variable : level -> algebraic -> opt_subst ref -> unit

  val check_leq : algebraic Sorts.Graph.check_function
  val check_eq : algebraic Sorts.Graph.check_function

  val enforce_leq : algebraic Sorts.constraint_function
  val enforce_leq_level : level Sorts.constraint_function
  val enforce_eq_level : level Sorts.constraint_function

  val add_constraint :
    (level * Sorts.constraint_type * level) ->
    Sorts.constraints -> Sorts.constraints

  val error_inconsistency :
    Sorts.constraint_type * algebraic * algebraic * (Sorts.constraint_type * algebraic) list option ->
    'a
end

module UnifyGen (In : UnifyIn) = struct

  let varinfo opt_subst algs x =
    match In.level x with
    | None -> Inl x
    | Some l -> Inr (l, In.opt_subst_mem l opt_subst, In.LSet.mem l algs)

  let process_ule unify univs vars fo l r local =
    if In.check_leq univs l r then
      (** Keep Prop/Set <= var around if var might be instantiated by prop or set
                  later  . *)
      match In.level l, In.level r with
      | Some l, Some r ->
         In.add_constraint (l, Sorts.Le, r) local
      | _ -> local
    else
      begin match In.level r with
      | None -> error ("Algebraic universe on the right")
      | Some rl ->
         if In.is_minimal rl then
           let levels = In.levels l in
           In.LSet.fold
             (fun l local ->
               if In.allow_eq_rigid_litteral || In.is_minimal l || In.opt_subst_mem l !vars then
                 unify fo (In.make_alg l) Universes.UEq r local
               else In.error_inconsistency
                             (Sorts.Le, In.make_alg l, r, None))
             levels local
         else
           In.enforce_leq l r local
      end

  let process_ulub unify algs vars l r local =
    begin match varinfo !vars algs l, varinfo !vars algs r with
    | (Inr (l, true, _), Inr (r, _, _))
      | (Inr (r, _, _), Inr (l, true, _)) ->
       In.instantiate_variable l (In.make_alg r) vars;
       In.enforce_eq_level l r local
    | Inr (_, _, _), Inr (_, _, _) ->
       unify true l Universes.UEq r local
    | _, _ -> assert false
    end

  let process_ueq univs algs vars fo l r local =
    begin match varinfo !vars algs l, varinfo !vars algs r with
    | Inr (l', lloc, _), Inr (r', rloc, _) ->
       let () =
         if lloc then
           In.instantiate_variable l' r vars
         else if rloc then
           In.instantiate_variable r' l vars
         else if not (In.check_eq univs l r) then
           (* Two rigid/global levels, none of them being local,
              one of them being Prop/Set, disallow *)
           if not In.allow_eq_rigid_litteral && (In.is_minimal l' || In.is_minimal r') then
             In.error_inconsistency (Sorts.Eq, l, r, None)
           else
             if fo then
               raise UniversesDiffer
       in
       In.enforce_eq_level l' r' local
    | Inr (l, loc, alg), Inl r
      | Inl r, Inr (l, loc, alg) ->
       let inst = In.level_rem l r r in
       if alg then (In.instantiate_variable l inst vars; local)
       else
         let lu = In.make_alg l in
         if In.level_mem l r then
           In.enforce_leq inst lu local
         else In.error_inconsistency (Sorts.Eq, lu, r, None)
    | Inl _, Inl _ (* Both are algebraic *) ->
       if In.check_eq univs l r then local
       else In.error_inconsistency (Sorts.Eq, l, r, None)
    end

  let unify univs algs vars fo l d r local =
    let normalize = In.normalize vars in
    let rec unify fo l d r local =
      let l = normalize l and r = normalize r in
      if In.algebraic_equal l r then local
      else
        begin match d with
        | Universes.ULe ->
           process_ule unify univs vars fo l r local
        | Universes.ULub ->
           process_ulub unify algs vars l r local
        | Universes.UEq ->
           process_ueq univs algs vars fo l r local
        end
    in
    unify fo l d r local

end

module UnifyUnivsIn : UnifyIn with
         type level = Univ.Level.t and type algebraic = Univ.universe
         and module LSet = Univ.USet and module LMap = Univ.UMap
  = struct
  open Univ

  type level = Level.t
  type algebraic = universe
  module LSet = USet
  module LMap = UMap

  let algebraic_equal = Universe.equal

  let level = Universe.level
  let levels = Universe.levels
  let make_alg = Universe.make
  let level_mem = univ_level_mem
  let level_rem = univ_level_rem
  let is_minimal = Level.is_small

  let allow_eq_rigid_litteral = false

  let opt_subst_mem l (usubst,_) = UMap.mem l usubst
  let normalize = Universes.normalize_universe_opt_subst

  let instantiate_variable = instantiate_univ_variable

  let check_leq = Sorts.Graph.univ_check_leq
  let check_eq = Sorts.Graph.univ_check_eq

  let enforce_leq = Sorts.univ_enforce_leq
  let enforce_leq_level = Sorts.univ_enforce_leq_level
  let enforce_eq_level = Sorts.univ_enforce_eq_level

  let add_constraint = Sorts.Constraint.add_univ

  let error_inconsistency e =
    raise (Sorts.sort_univ_inconsistency e)
end

module UnifyUnivs = UnifyGen(UnifyUnivsIn)

module UnifyTruncsIn : UnifyIn with
         type level = Trunc.TLevel.t and type algebraic = Trunc.truncation
         and module LSet = Trunc.TSet and module LMap = Trunc.TMap
  = struct
  open Trunc

  (* TODO FIXME for hprop *)
  type level = TLevel.t
  type algebraic = truncation
  module LSet = TSet
  module LMap = TMap

  let algebraic_equal = Truncation.equal

  let level = Truncation.level
  let levels = Truncation.levels
  let make_alg = Truncation.of_level
  let level_mem = Truncation.level_mem
  let level_rem = Truncation.level_rem
  let is_minimal x = TLevel.is_hset x || TLevel.is_hprop x

  let allow_eq_rigid_litteral = true

  let opt_subst_mem l (_,tsubst) = TMap.mem l tsubst
  let normalize = Universes.normalize_truncation_opt_subst

  let instantiate_variable = instantiate_trunc_variable

  let check_leq = Sorts.Graph.trunc_check_leq
  let check_eq = Sorts.Graph.trunc_check_eq

  let enforce_leq = Sorts.trunc_enforce_leq
  let enforce_leq_level = Sorts.trunc_enforce_leq_level
  let enforce_eq_level = Sorts.trunc_enforce_eq_level

  let add_constraint = Sorts.Constraint.add_trunc

  let error_inconsistency e =
    raise (Sorts.sort_trunc_inconsistency e)
end

module UnifyTruncs = UnifyGen(UnifyTruncsIn)

let process_universe_constraints ctx cstrs =
  let univs = ctx.uctx_universes in
  let ualgs = ctx.uctx_univ_algebraic in
  let talgs = ctx.uctx_trunc_algebraic in
  let vars = ref ctx.uctx_univ_variables in
  let local =
    Universes.Constraints.fold (fun c local ->
        match c with
        | Universes.UnivConstraint (l,d,r) ->
           UnifyUnivs.unify univs ualgs vars false l d r local
        | Universes.TruncConstraint (l,d,r) ->
           UnifyTruncs.unify univs talgs vars false l d r local)
      cstrs Sorts.Constraint.empty
  in
    !vars, local

let add_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let cstrs' =
    Sorts.Constraint.fold
      (fun c acc ->
        match c with
        | Sorts.UnivConstraint (l,d,r) ->
           let open Univ in
           let l = Universe.make l and r = Universe.make r in
           let cstr' =
             match d with
             | Sorts.Lt -> (Universe.super l, Universes.ULe, r)
             | Sorts.Le -> (l, Universes.ULe, r)
             | Sorts.Eq -> (l, Universes.UEq, r)
           in Universes.Constraints.add (Universes.UnivConstraint cstr') acc
        | Sorts.TruncConstraint (l,d,r) ->
           let open Trunc in
           let l = Truncation.of_level l and r = Truncation.of_level r in
           let cstr' =
             match d with
             | Sorts.Lt -> anomaly (str "Strict constraint between truncations")
             | Sorts.Le -> (l, Universes.ULe, r)
             | Sorts.Eq -> (l, Universes.UEq, r)
           in Universes.Constraints.add (Universes.TruncConstraint cstr') acc)
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

let pr_uctx_univ_level uctx =
  let map, map_rev = uctx.uctx_unames in
    fun l ->
      try str (Option.get (Univ.UMap.find l map_rev).uname)
      with Not_found | Option.IsNone ->
        fst Universes.pr_with_global_universes l

let pr_uctx_trunc_level uctx =
  let map, map_rev = uctx.uctx_tnames in
    fun l ->
      try str (Option.get (Trunc.TMap.find l map_rev).uname)
      with Not_found | Option.IsNone ->
        snd Universes.pr_with_global_universes l

let pr_uctx_level uctx = pr_uctx_univ_level uctx, pr_uctx_trunc_level uctx

type universe_names =
  { univ_names : (Id.t Loc.located) list
  ; trunc_names : (Id.t Loc.located) list }

let universe_names_equal x y =
  CList.for_all2eq (fun x y -> Id.equal (snd x) (snd y)) x.univ_names y.univ_names
  && CList.for_all2eq (fun x y -> Id.equal (snd x) (snd y)) x.trunc_names y.trunc_names

let universe_context_univ ctx univ_names =
  let ulevels = Sorts.ContextSet.univ_levels ctx.uctx_local in
  let newinst, map, left =
    List.fold_right
      (fun (loc,id) (newinst, map, acc) ->
        let l =
          try UNameMap.find (Id.to_string id) (fst ctx.uctx_unames)
          with Not_found ->
            user_err ~loc ~hdr:"universe_context"
                     (str"Universe " ++ Nameops.pr_id id ++ str" is not bound anymore.")
        in (l :: newinst, (id, l) :: map, Univ.USet.remove l acc))
      univ_names ([], [], ulevels)
  in
  if not (Univ.USet.is_empty left) then
    let n = Univ.USet.cardinal left in
    let loc =
      try
        let info =
          Univ.UMap.find (Univ.USet.choose left) (snd ctx.uctx_unames) in
        Option.default Loc.ghost info.uloc
      with Not_found -> Loc.ghost
    in
    user_err ~loc ~hdr:"universe_context"
             ((str(CString.plural n "Universe") ++ spc () ++
		 Univ.USet.pr (pr_uctx_univ_level ctx) left ++
		 spc () ++ str (CString.conjugate_verb_to_be n) ++
                 str" unbound."))
  else
    map, newinst

let universe_context_trunc ctx trunc_names =
  let tlevels = Sorts.ContextSet.trunc_levels ctx.uctx_local in
  let newinst, map, left =
    List.fold_right
      (fun (loc,id) (newinst, map, acc) ->
        let l =
          try UNameMap.find (Id.to_string id) (fst ctx.uctx_tnames)
          with Not_found ->
            user_err ~loc ~hdr:"universe_context"
                     (str"Universe " ++ Nameops.pr_id id ++ str" is not bound anymore.")
        in (l :: newinst, (id, l) :: map, Trunc.TSet.remove l acc))
      trunc_names ([], [], tlevels)
  in
  if not (Trunc.TSet.is_empty left) then
    let n = Trunc.TSet.cardinal left in
    let loc =
      try
        let info =
          Trunc.TMap.find (Trunc.TSet.choose left) (snd ctx.uctx_tnames) in
        Option.default Loc.ghost info.uloc
      with Not_found -> Loc.ghost
    in
    user_err ~loc ~hdr:"universe_context"
             ((str(CString.plural n "Truncation") ++ spc () ++
		 Trunc.TSet.pr (pr_uctx_trunc_level ctx) left ++
		 spc () ++ str (CString.conjugate_verb_to_be n) ++
                 str" unbound."))
  else
    map, newinst

let universe_context ?names ctx =
  match names with
  | None -> Universes.empty_universe_binders, Sorts.ContextSet.to_context ctx.uctx_local
  | Some {univ_names; trunc_names} ->
     let univ_binders, unewinst = universe_context_univ ctx univ_names in
     let trunc_binders, tnewinst = universe_context_trunc ctx trunc_names in
     let inst = Sorts.Instance.of_arrays (Array.of_list unewinst, Array.of_list tnewinst) in
     let ctx = Sorts.UContext.make (inst,
                                    Sorts.ContextSet.constraints ctx.uctx_local)
     in
     let open Universes in
     {univ_binders; trunc_binders}, ctx

let restrict ctx uvars tvars =
  let uctx' = Universes.restrict_universe_context ctx.uctx_local uvars tvars in
  { ctx with uctx_local = uctx' }

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let merge ?loc sideff rigid uctx ctx' =
  let open Univ in
  let open Trunc in
  let ulevels = Sorts.ContextSet.univ_levels ctx' in
  let tlevels = Sorts.ContextSet.trunc_levels ctx' in
  let uctx = if sideff then uctx else
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      let ufold u (accu, acct as acc) =
        if UMap.mem u accu then acc
        else UMap.add u None accu, acct
      in
      let tfold t (accu, acct as acc) =
        if TMap.mem t acct then acc
        else accu, TMap.add t None acct
      in
      let uvars' = uctx.uctx_univ_variables
                   |> USet.fold ufold ulevels
                   |> TSet.fold tfold tlevels
      in
      if b then
        { uctx with uctx_univ_variables = uvars';
                    uctx_univ_algebraic = USet.union uctx.uctx_univ_algebraic ulevels;
                    uctx_trunc_algebraic = TSet.union uctx.uctx_trunc_algebraic tlevels;}
      else { uctx with uctx_univ_variables = uvars' }
  in
  let uctx_local =
    if sideff then uctx.uctx_local
    else Sorts.ContextSet.append ctx' uctx.uctx_local
  in
  let declare g =
    g
    |> USet.fold
         (fun u g ->
           try Sorts.Graph.add_universe u false g
           with Sorts.Graph.AlreadyDeclared when sideff -> g)
         ulevels
    |> TSet.fold
         (fun u g ->
           try Sorts.Graph.add_truncation u g
           with Sorts.Graph.AlreadyDeclared when sideff -> g)
         tlevels
  in
  let uctx_unames =
    let fold u accu =
      let modify _ info = match info.uloc with
      | None -> { info with uloc = loc }
      | Some _ -> info
      in
      try UMap.modify u modify accu
      with Not_found -> UMap.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.uctx_unames, USet.fold fold ulevels (snd uctx.uctx_unames))
  in
  let uctx_tnames =
    let fold u accu =
      let modify _ info = match info.uloc with
      | None -> { info with uloc = loc }
      | Some _ -> info
      in
      try TMap.modify u modify accu
      with Not_found -> TMap.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.uctx_tnames, TSet.fold fold tlevels (snd uctx.uctx_tnames))
  in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare uctx.uctx_universes in
  let uctx_universes = Sorts.Graph.merge_constraints (Sorts.ContextSet.constraints ctx') univs in
  { uctx with uctx_unames; uctx_tnames; uctx_local; uctx_universes;
              uctx_initial_universes = initial }

let merge_subst uctx (usubst, tsubst) =
  let uvars, tvars = uctx.uctx_univ_variables in
  let uvars = Univ.UMap.subst_union uvars usubst in
  let tvars = Trunc.TMap.subst_union tvars tsubst in
  { uctx with uctx_univ_variables = uvars, tvars }

let emit_side_effects eff u =
  let uctxs = Safe_typing.universes_of_private eff in
  List.fold_left (merge true univ_rigid) u uctxs

let new_univ_variable ?loc rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars,tvars; uctx_univ_algebraic = avars} as uctx) =
  let u = Universes.new_univ_level () in
  let ctx' = Sorts.ContextSet.add_universe u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b -> 
      let uvars' = Univ.UMap.add u None uvars in
        if b then {uctx with uctx_univ_variables = uvars',tvars;
          uctx_univ_algebraic = Univ.USet.add u avars}, false
        else {uctx with uctx_univ_variables = uvars',tvars}, false
  in
  let unames =
    match name with
    | Some n -> add_uctx_unames ?loc n u uctx.uctx_unames
    | None -> add_uctx_univ_loc u loc uctx.uctx_unames
  in
  let initial =
    Sorts.Graph.add_universe u false uctx.uctx_initial_universes
  in                                                 
  let uctx' =
    {uctx' with uctx_unames = unames; uctx_local = ctx';
                uctx_universes = Sorts.Graph.add_universe u false uctx.uctx_universes;
                uctx_initial_universes = initial}
  in uctx', u

let new_trunc_variable ?loc rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars,tvars; uctx_trunc_algebraic = avars} as uctx) =
  let u = Universes.new_trunc_level () in
  let ctx' = Sorts.ContextSet.add_truncation u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b ->
      let tvars' = Trunc.TMap.add u None tvars in
        if b then {uctx with uctx_univ_variables = uvars,tvars';
          uctx_trunc_algebraic = Trunc.TSet.add u avars}, false
        else {uctx with uctx_univ_variables = uvars,tvars'}, false
  in
  let tnames =
    match name with
    | Some n -> add_uctx_tnames ?loc n u uctx.uctx_tnames
    | None -> add_uctx_trunc_loc u loc uctx.uctx_tnames
  in
  let initial =
    Sorts.Graph.add_truncation u uctx.uctx_initial_universes
  in
  let uctx' =
    {uctx' with uctx_tnames = tnames; uctx_local = ctx';
                uctx_universes = Sorts.Graph.add_truncation u uctx.uctx_universes;
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

let add_global_trunc uctx u =
  let initial =
    Sorts.Graph.add_truncation u uctx.uctx_initial_universes
  in
  let univs =
    Sorts.Graph.add_truncation u uctx.uctx_universes
  in
  { uctx with uctx_local = Sorts.ContextSet.add_truncation u uctx.uctx_local;
                                     uctx_initial_universes = initial;
                                     uctx_universes = univs }

let make_flexible_univ_variable ctx b u =
  let {uctx_univ_variables = uvars,tvars; uctx_univ_algebraic = avars} = ctx in
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
  {ctx with uctx_univ_variables = uvars',tvars;
      uctx_univ_algebraic = avars'}

let make_flexible_trunc_variable ctx b u =
  let {uctx_univ_variables = uvars,tvars; uctx_trunc_algebraic = avars} = ctx in
  let tvars' = Trunc.TMap.add u None tvars in
  let avars' =
    if b then
      let uu = Trunc.Truncation.of_level u in
      let substu_not_alg u' v =
        Option.cata (fun vu -> Trunc.Truncation.equal uu vu && not (Trunc.TSet.mem u' avars)) false v
      in
        if not (Trunc.TMap.exists substu_not_alg tvars)
        then Trunc.TSet.add u avars else avars
    else avars
  in
  {ctx with uctx_univ_variables = uvars,tvars';
      uctx_trunc_algebraic = avars'}

let is_univ_variable uctx s =
  match Univ.Universe.level s with
  | Some l as x ->
     if Univ.USet.mem l (Sorts.ContextSet.univ_levels uctx.uctx_local) then x
     else None
  | None -> None

let is_trunc_variable uctx s =
  match Trunc.Truncation.level s with
  | Some l as x ->
     if Trunc.TSet.mem l (Sorts.ContextSet.trunc_levels uctx.uctx_local) then x
     else None
  | None -> None

let subst_univs_context_with_def udef tdef usubst ((uctx, tctx), cst) =
  ((Univ.USet.diff uctx udef, Trunc.TSet.diff tctx tdef), Sorts.subst_constraints usubst cst)

let normalize_variables uctx =
  let normalized_variables, _, univ_def, _, trunc_def, subst =
    Universes.normalize_variables uctx.uctx_univ_variables
  in
  let ctx_local =
    subst_univs_context_with_def
      univ_def trunc_def
      (Sorts.sort_subst_fn subst) uctx.uctx_local
  in
  let ctx_local', univs = Universes.refresh_constraints uctx.uctx_initial_universes ctx_local in
    subst, { uctx with uctx_local = ctx_local';
      uctx_univ_variables = normalized_variables;
      uctx_universes = univs }

let abstract_undefined_variables uctx =
  let usubst, tsubst = uctx.uctx_univ_variables in
  let uvars' = 
    Univ.UMap.fold (fun u v acc ->
      if v == None then Univ.USet.remove u acc
      else acc)
    usubst uctx.uctx_univ_algebraic
  in
  let tvars' =
    Trunc.TMap.fold (fun u v acc ->
      if v == None then Trunc.TSet.remove u acc
      else acc)
    tsubst uctx.uctx_trunc_algebraic
  in
  { uctx with uctx_local = Sorts.ContextSet.empty;
              uctx_univ_algebraic = uvars';
              uctx_trunc_algebraic = tvars'}

let fix_undefined_variables uctx =
  let uvars, tvars = uctx.uctx_univ_variables in
  let ualgs', uvars' =
    Univ.UMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (Univ.USet.remove u algs, Univ.UMap.remove u vars)
      else acc)
      uvars
      (uctx.uctx_univ_algebraic, uvars)
  in
  let talgs', tvars' =
    Trunc.TMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (Trunc.TSet.remove u algs, Trunc.TMap.remove u vars)
      else acc)
      tvars
      (uctx.uctx_trunc_algebraic, tvars)
  in
  { uctx with uctx_univ_variables = uvars',tvars';
              uctx_univ_algebraic = ualgs';
              uctx_trunc_algebraic = talgs' }

let refresh_undefined_variables uctx =
  let (usubst, tsubst as subst), ctx' =
    Universes.fresh_universe_context_set_instance uctx.uctx_local
  in
  let ualg = Univ.USet.fold
               (fun u acc -> Univ.USet.add (Univ.subst_univs_level_level usubst u) acc)
               uctx.uctx_univ_algebraic Univ.USet.empty
  in
  let talg = Trunc.TSet.fold
               (fun u acc -> Trunc.TSet.add (Trunc.subst_truncs_level_level tsubst u) acc)
               uctx.uctx_trunc_algebraic Trunc.TSet.empty
  in
  let uvars, tvars = uctx.uctx_univ_variables in
  let uvars =
    Univ.UMap.fold
      (fun u v acc ->
        Univ.UMap.add (Univ.subst_univs_level_level usubst u)
          (Option.map (Univ.subst_univs_level_universe usubst) v) acc)
      uvars Univ.UMap.empty
  in
  let tvars =
    Trunc.TMap.fold
      (fun u v acc ->
        Trunc.TMap.add (Trunc.subst_truncs_level_level tsubst u)
          (Option.map (Trunc.subst_truncs_level_truncation tsubst) v) acc)
      tvars Trunc.TMap.empty
  in
  let declare g =
    g
    |> Univ.USet.fold (fun u g -> Sorts.Graph.add_universe u false g)
                      (Sorts.ContextSet.univ_levels ctx')
    |> Trunc.TSet.fold (fun u g -> Sorts.Graph.add_truncation u g)
                      (Sorts.ContextSet.trunc_levels ctx')
  in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare Sorts.Graph.initial in
  let uctx' = {uctx_unames = uctx.uctx_unames;
               uctx_tnames = uctx.uctx_tnames;
               uctx_local = ctx'; 
               uctx_univ_variables = uvars,tvars;
               uctx_univ_algebraic = ualg;
               uctx_trunc_algebraic = talg;
               uctx_universes = univs;
               uctx_initial_universes = initial } in
    uctx', subst

let normalize uctx = 
  let ((vars',ualgs',talgs'), us') =
    Universes.normalize_context_set uctx.uctx_local uctx.uctx_univ_variables
				    uctx.uctx_univ_algebraic
                                    uctx.uctx_trunc_algebraic
  in
  if Sorts.ContextSet.equal us' uctx.uctx_local then uctx
  else
    let us', universes =
      Universes.refresh_constraints uctx.uctx_initial_universes us'
    in
    { uctx_unames = uctx.uctx_unames;
      uctx_tnames = uctx.uctx_tnames;
      uctx_local = us';
      uctx_univ_variables = vars';
      uctx_univ_algebraic = ualgs';
      uctx_trunc_algebraic = talgs';
      uctx_universes = universes;
      uctx_initial_universes = uctx.uctx_initial_universes }

let universe_of_name uctx s = 
  UNameMap.find s (fst uctx.uctx_unames)

let truncation_of_name uctx s =
  UNameMap.find s (fst uctx.uctx_tnames)

let add_universe_name uctx s l =
  let names' = add_uctx_unames s l uctx.uctx_unames in
  { uctx with uctx_unames = names' }

let add_truncation_name uctx s l =
  let names' = add_uctx_tnames s l uctx.uctx_tnames in
  { uctx with uctx_tnames = names' }

let update_sigma_env uctx env =
  let univs = Environ.universes env in
  let eunivs =
    { uctx with uctx_initial_universes = univs;
                         uctx_universes = univs }
  in
  merge true univ_rigid eunivs eunivs.uctx_local
