(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Decl_kinds
open Vernacexpr
open Errors

(** * Managing locality *)
let syntax_checking_error loc s = user_err_loc (loc,"",Pp.str s)

let local_of_bool = function true -> Local | false -> Global
let bool_of_local = function Local -> true | Global -> false

let check_locality = function
  | VernacLocality ((loc,true), _) -> 
      syntax_checking_error loc
	"This command does not support the \"Local\" prefix.";
  | VernacLocality ((loc,false), _) -> 
      syntax_checking_error loc
	"This command does not support the \"Global\" prefix."
  | _ -> ()

(** Extracting the locality flag *)

(* Commands which supported an inlined Local flag *)

let enforce_locality_full ast local =
  match ast with
  | Some false when local ->
      error "Cannot be simultaneously Local and Global."
  | Some true when local ->
      error "Use only prefix \"Local\"."
  | Some _ as x -> x
  | _ ->
      if local then begin
        Flags.if_warn
         Pp.msg_warning (Pp.str"Obsolete syntax: use \"Local\" as a prefix.");
        Some true
      end else
      ast

(* Commands which did not supported an inlined Local flag (synonym of
   [enforce_locality_full false]) *)

(** Positioning locality for commands supporting discharging and export
     outside of modules *)

(* For commands whose default is to discharge and export:
   Global is the default and is neutral;
   Local in a section deactivates discharge, 
   Local not in a section deactivates export *)

let make_locality = function Some true -> true | _ -> false 

let use_locality x = make_locality x

let use_locality_exp x = local_of_bool (use_locality x)

let use_definition_locality local def_kind =
  match local, def_kind with
  | Some true,_ -> Local
  | Some false,_ -> Global
  | _, Definition -> Global
  | _, CanonicalStructure -> Global
  | _, Example -> Local
  | _, SubClass -> Global
  | _, (Coercion|IdentityCoercion) -> Global
  | _, Instance -> Local
  | _, (StructureComponent|Scheme|CoFixpoint|Fixpoint|Method)
      -> Errors.anomaly "Internal definition kind"

let enforce_locality x local = make_locality (enforce_locality_full x local)

let enforce_locality_exp x local = local_of_bool (enforce_locality x local)

(* For commands whose default is not to discharge and not to export:
   Global forces discharge and export;
   Local is the default and is neutral *)

let use_non_locality = function Some false -> false | _ -> true

(* For commands whose default is to not discharge but to export:
   Global in sections forces discharge, Global not in section is the default;
   Local in sections is the default, Local not in section forces non-export *)

let make_section_locality = function Some b -> b | _ ->Lib.sections_are_opened()

let use_section_locality x = make_section_locality x

let enforce_section_locality x local =
  make_section_locality (enforce_locality_full x local)

(** Positioning locality for commands supporting export but not discharge *)

(* For commands whose default is to export (if not in section):
   Global in sections is forbidden, Global not in section is neutral;
   Local in sections is the default, Local not in section forces non-export *)

let make_module_locality = function
  | Some false ->
      if Lib.sections_are_opened () then
	error "This command does not support the Global option in sections.";
      false
  | Some true -> true
  | _ -> false

let use_module_locality x = make_module_locality x

let enforce_module_locality x local =
  make_module_locality (enforce_locality_full x local)

