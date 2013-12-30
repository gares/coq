(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Environ
open Util
open Vernacexpr

(* Proof using Type.
 * Proof using All.
 * Proof using (All).
 * Proof using x y z.
 * Proof using -(x y z)
 * *)
let to_string = function
  | SsAll -> "All"
  | SsType -> "Type"
  | SsExpr e ->
      let rec aux = function
        | SsSet l ->
          "(" ^ String.concat " " (List.map Id.to_string (List.map snd l)) ^ ")"
        | SsCompl e -> "(-" ^ aux e^")"
        | SsUnion(e1,e2) -> "("^aux e1 ^" + "^ aux e2^")"
        | SsSubstr(e1,e2) -> "("^aux e1 ^" - "^ aux e2^")"
      in aux e

let process_expr e = prerr_endline (to_string e); []


let minimize_hyps env ids =
  let rec aux ids =
    let ids' =
      Id.Set.fold (fun id alive ->
        let impl_by_id =
          Id.Set.remove id (really_needed env (Id.Set.singleton id)) in
        if Id.Set.is_empty impl_by_id then alive
        else Id.Set.diff alive impl_by_id)
      ids ids in
    if Id.Set.equal ids ids' then ids else aux ids'
  in
    aux ids

let minimize_unused_hyps env ids =
  let all_ids = List.map pi1 (named_context env) in
  let deps_of =
    let cache =
      List.map (fun id -> id,really_needed env (Id.Set.singleton id)) all_ids in
    fun id -> List.assoc id cache in
  let inv_dep_of =
    let cache_sum cache id stuff =
      try Id.Map.add id (Id.Set.add stuff (Id.Map.find id cache)) cache
      with Not_found -> Id.Map.add id (Id.Set.singleton stuff) cache in
    let cache =
      List.fold_left (fun cache id ->
        Id.Set.fold (fun d cache -> cache_sum cache d id)
          (Id.Set.remove id (deps_of id)) cache)
        Id.Map.empty all_ids in
    fun id -> try Id.Map.find id cache with Not_found -> Id.Set.empty in
  let rec aux s =
    let s' =
      Id.Set.fold (fun id s ->
        if Id.Set.subset (inv_dep_of id) s then Id.Set.diff s (inv_dep_of id)
        else s)
      s s in
    if Id.Set.equal s s' then s else aux s' in
  aux ids

let suggest_Proof_using kn env vars ids_typ context_ids =
  let module S = Id.Set in
  let open Pp in
  let used = S.union vars ids_typ in
  let needed = minimize_hyps env used in
  let all_needed = really_needed env needed in
  let all = List.fold_right S.add context_ids S.empty in
  let unneeded = minimize_unused_hyps env (S.diff all needed) in
  let card_lt s1 s2 = S.cardinal s1 < S.cardinal s2 in
  let pr_set s =
    let wrap ppcmds =
      if S.cardinal s > 1 || S.equal s (S.singleton (Id.of_string "All"))
      then str "(" ++ ppcmds ++ str ")"
      else ppcmds in
    wrap (prlist_with_sep (fun _ -> str" ") Id.print (S.elements s)) in
  msg_info (
    str"The proof of "++
    Names.Constant.print kn ++ spc() ++ str "should start with:"++spc()++
    str"Proof using " ++
    if S.is_empty needed then str "."
    else if S.subset needed ids_typ then str "Type."
    else if S.equal all all_needed then str "All."
    else 
      let s1 = string_of_ppcmds (str "-" ++ pr_set unneeded ++ str".") in
      let s2 = string_of_ppcmds (pr_set needed ++ str".") in
      if String.length s1 < String.length s2 then str s1 else str s1)

let value = ref false

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "suggest Proof using";
      Goptions.optkey   = ["Suggest";"Proof";"Using"];
      Goptions.optread  = (fun () -> !value);
      Goptions.optwrite = (fun b ->
        value := b;
        if b then Term_typing.set_suggest_proof_using suggest_Proof_using
        else Term_typing.set_suggest_proof_using (fun _ _ _ _ _ -> ())
      ) }


