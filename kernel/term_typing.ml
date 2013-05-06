(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module provides the main entry points for type-checking basic
   declarations *)

open Errors
open Util
open Names
open Univ
open Term
open Context
open Declarations
open Environ
open Entries
open Typeops

let debug = false
let prerr_endline =
  if debug then prerr_endline else fun _ -> ()

let constrain_type env j cst1 = function
  | None ->
      make_polymorphic_if_constant_for_ind env j, cst1
  | Some t ->
      let (tj,cst2) = infer_type env t in
      let (_,cst3) = judge_of_cast env j DEFAULTcast tj in
      assert (eq_constr t tj.utj_val);
      let cstrs = union_constraints (union_constraints cst1 cst2) cst3 in
      NonPolymorphicType t, cstrs


let translate_local_assum env t =
  let (j,cst) = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    (t,cst)


(* Insertion of constants and parameters in environment. *)

let handle_side_effects env body side_eff =
  let handle_sideff t (NewConstant (c,cb)) =
    let cname = 
      let name = string_of_con c in
      for i = 0 to String.length name - 1 do
        if name.[i] = '.' || name.[i] = '#' then name.[i] <- '_' done;
      Name (id_of_string name) in
    let rec sub i x = match kind_of_term x with
      | Const c' when eq_constant c c' -> mkRel i
      | _ -> map_constr_with_binders ((+) 1) sub i x in
    match cb.const_body with
    | Undef _ -> assert false
    | Def b ->
        let b = Lazyconstr.force b in
        let b_ty = Typeops.type_of_constant_type env cb.const_type in
        let t = sub 1 (Vars.lift 1 t) in (* XXX lift should be useless, ask Bruno *)
        mkLetIn (cname, b, b_ty, t)
    | OpaqueDef b -> 
        let b = Lazyconstr.force_opaque (Future.force b) in
        let b_ty = Typeops.type_of_constant_type env cb.const_type in
        let t = sub 1 (Vars.lift 1 t) in (* XXX lift should be useless, ask Bruno *)
        mkApp (mkLambda (cname, b_ty, t), [|b|])
  in
  (* TODO assure proper order *)
  Declareops.fold_side_effects handle_sideff body
    (Declareops.uniquize_side_effects side_eff)

(* what is used for debugging only *)
let what = "UNKNOWN"
let infer_declaration ?(what=what) env dcl =
  match dcl with
  | DefinitionEntry c ->
      let ctx, entry_body = c.const_entry_secctx, c.const_entry_body in
      if c.const_entry_opaque && c.const_entry_type <> None then
        let _ = prerr_endline ("deferring typing of "^what) in
        let body_cst = Future.chain ~id:("infer_declaration " ^ what)
            entry_body (fun entry_body ->
          let _ = prerr_endline ("forcing deferred typing of "^what) in
          let body, side_eff = entry_body in
          let _ = prerr_endline ("... got proof of "^what) in
          let body = if side_eff = Declareops.no_side_effects then body else
            let _ = prerr_endline ("    Handling the following side eff:") in
            Declareops.iter_side_effects (fun e -> 
              prerr_endline("     " ^ Declareops.string_of_side_effect e)) 
              side_eff;
            handle_side_effects env body side_eff in
          let (j,cst) = infer env body in
          let _ = prerr_endline ("... typed proof of "^what) in
          let j =
            {uj_val = hcons_constr j.uj_val;
             uj_type = hcons_constr j.uj_type} in
          let (_typ,cst) = constrain_type env j cst c.const_entry_type in
          Lazyconstr.opaque_from_val j.uj_val, cst) in
        let body, cst = Future.split2 body_cst in
        let def = OpaqueDef body in
        let typ = match c.const_entry_type with
        | None -> assert false
        | Some typ -> NonPolymorphicType typ in
        (def, typ, cst, c.const_entry_inline_code, ctx)
      else
        let _ = prerr_endline ("typing now "^what) in
        let body, side_eff = Future.force entry_body in
        let body = if side_eff = Declareops.no_side_effects then body else
          let _ = prerr_endline ("    Handling the following side eff:") in
          Declareops.iter_side_effects (fun e -> 
            prerr_endline("     " ^ Declareops.string_of_side_effect e))
            side_eff;
          handle_side_effects env body side_eff in
        let (j,cst) =
          try infer env body 
          with Not_found as e -> 
            prerr_endline ("infer not found " ^ what);
            raise e in
        let j =
          {uj_val = hcons_constr j.uj_val;
           uj_type = hcons_constr j.uj_type} in
        let (typ,cst) = constrain_type env j cst c.const_entry_type in
        let _ = prerr_endline ("...typed "^what) in
        let def = Def (Lazyconstr.from_val j.uj_val) in
        (def, typ, Future.from_val cst, c.const_entry_inline_code, ctx)
  | ParameterEntry (ctx,t,nl) ->
      let (j,cst) = infer env t in
      let t = hcons_constr (Typeops.assumption_of_judgment env j) in
      Undef nl, NonPolymorphicType t, Future.from_val cst, false, ctx

let global_vars_set_constant_type env = function
  | NonPolymorphicType t -> global_vars_set env t
  | PolymorphicArity (ctx,_) ->
      Context.fold_rel_context
        (fold_rel_declaration
	  (fun t c -> Id.Set.union (global_vars_set env t) c))
      ctx ~init:Id.Set.empty

let build_constant_declaration kn env (def,typ,cst,inline_code,ctx) =
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map pi1 l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      error ("The following section variable are used but not declared:\n"^
        (String.concat ", " (List.map Id.to_string
          (Id.Set.elements (Idset.diff inferred_set declared_set))))) in
  let hyps, def = 
    match ctx with
    | None when named_context env <> [] -> 
        (* No declared section vars, and non empty section context *)
        let ids_typ = global_vars_set_constant_type env typ in
        let ids_def = match def with
        | Undef _ -> Idset.empty
        | Def cs -> global_vars_set env (Lazyconstr.force cs)
        | OpaqueDef lc -> 
            (* we force the cst too, so the peek says Val *)
            ignore(Future.join cst);
            global_vars_set env (Lazyconstr.force_opaque (Future.force lc)) in
        keep_hyps env (Idset.union ids_typ ids_def), def
    | None ->
        (* Empty section context, like declaring [] and no need to check *)
        [], def
    | Some declared ->
        declared,
        match def with
        | Undef _ as x -> x (* nothing to check *)
        | Def cs as x ->
            let ids_typ = global_vars_set_constant_type env typ in
            let ids_def = global_vars_set env (Lazyconstr.force cs) in
            let inferred = keep_hyps env (Idset.union ids_typ ids_def) in
            check declared inferred;
            x
        | OpaqueDef lc -> (* In this case we can postpone the check *)
            OpaqueDef (Future.chain ~id:(string_of_con kn) lc (fun lc ->
              let ids_typ = global_vars_set_constant_type env typ in
              let ids_def =
                global_vars_set env (Lazyconstr.force_opaque lc) in
              let inferred = keep_hyps env (Idset.union ids_typ ids_def) in
              check declared inferred; lc)) in
  let tps = Cemitcodes.from_val (
    match def with (* hack to avoid compilation *)
    | Undef _ | OpaqueDef _ -> Cemitcodes.BCconstant 
    | _ -> compile_constant_body env def) in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_body_code = tps;
    const_constraints = cst;
    const_native_name = ref NotLinked;
    const_inline_code = inline_code }

(*s Global and local constant declaration. *)

let translate_constant env kn ce =
  build_constant_declaration kn env 
    (infer_declaration ~what:(string_of_con kn) env ce)

let translate_recipe env kn r =
  let def,typ,cst,inline_code,hyps = Cooking.cook_constant env r in
  build_constant_declaration kn env (def,typ,cst,inline_code,hyps)

let translate_local_def env id centry =
  let def,typ,cst,inline_code,ctx =
    infer_declaration ~what:(string_of_id id) env (DefinitionEntry centry) in
  let typ = type_of_constant_type env typ in
  def, typ, cst

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie

let handle_side_effects env ce = { ce with
  const_entry_body = Future.chain ~id:"handle_side_effects" 
    ce.const_entry_body (fun (body, side_eff) ->
    handle_side_effects env body side_eff, Declareops.no_side_effects);
}
