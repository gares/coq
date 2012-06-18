(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util

type 'a summary_declaration = {
  freeze_function : bool -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

let summaries =
  (Hashtbl.create 17 : (string, Dyn.t summary_declaration) Hashtbl.t)

let internal_declare_summary sumname sdecl =
  let (infun,outfun) = Dyn.create sumname in
  let dyn_freeze b = infun (sdecl.freeze_function b)
  and dyn_unfreeze sum = sdecl.unfreeze_function (outfun sum)
  and dyn_init = sdecl.init_function in
  let ddecl = {
    freeze_function = dyn_freeze;
    unfreeze_function = dyn_unfreeze;
    init_function = dyn_init }
  in
  if Hashtbl.mem summaries sumname then
    anomalylabstrm "Summary.declare_summary"
      (str "Cannot declare a summary twice: " ++ str sumname);
  Hashtbl.add summaries sumname ddecl

let declare_summary sumname decl =
  internal_declare_summary (sumname^"-SUMMARY") decl

type frozen = Dyn.t Stringmap.t

let freeze_summaries ~marshallable =
  let m = ref Stringmap.empty in
  Hashtbl.iter
    (fun id decl -> 
       (* to debug missing Lazy.force 
       if marshallable then begin
         prerr_endline ("begin marshalling " ^ id);
         ignore(Marshal.to_string (decl.freeze_function marshallable) []);
         prerr_endline ("end marshalling " ^ id);
       end;
        /debug *)
       m := Stringmap.add id (decl.freeze_function marshallable) !m)
    summaries;
  !m


let unfreeze_summaries fs =
  Hashtbl.iter
    (fun id decl ->
       try decl.unfreeze_function (Stringmap.find id fs)
       with Not_found -> decl.init_function())
    summaries

let init_summaries () =
  Hashtbl.iter (fun _ decl -> decl.init_function()) summaries

type data = (string * Dyn.t) list

let mangle id = id ^ "-SUMMARY"

let find_summary id =
  try Some (Hashtbl.find summaries (mangle id))
  with Not_found -> None

let freeze_summary ?(complement=false) ids =
  if not complement then
    Util.list_map_filter (fun id ->
      Option.map (fun x ->
         mangle id, x.freeze_function false) (find_summary id)) ids
  else
    let ids = List.map mangle ids in
    let l = ref [] in 
    Hashtbl.iter (fun id decl -> 
      if List.mem id ids then ()
      else l := (id, decl.freeze_function false) :: !l) summaries;
    !l

let unfreeze_summary data = 
  List.iter (fun (id,data) -> 
    (fun x -> x.unfreeze_function data) 
      (Hashtbl.find summaries id)) data
