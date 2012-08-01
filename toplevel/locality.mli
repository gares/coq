(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Decl_kinds

(** * Managing locality *)

val check_locality : Vernacexpr.vernac_expr -> unit

(** * Extracting the locality flag *)

(** Commands which supported an inlined Local flag *)

val enforce_locality_full : bool option -> bool -> bool option

(** Commands which did not supported an inlined Local flag
    (synonym of [enforce_locality_full false]) *)

(* val use_locality_full : unit -> bool option *)

(** * Positioning locality for commands supporting discharging and export
    outside of modules *)

(** For commands whose default is to discharge and export:
    Global is the default and is neutral;
    Local in a section deactivates discharge,
    Local not in a section deactivates export *)

val make_locality : bool option -> bool
val use_locality : bool option -> bool
val use_locality_exp : bool option -> locality
val enforce_locality : bool option -> bool -> bool
val enforce_locality_exp : bool option -> bool -> locality
val use_definition_locality : bool option -> definition_object_kind -> locality

(** For commands whose default is not to discharge and not to export:
    Global forces discharge and export;
    Local is the default and is neutral *)

val use_non_locality : bool option -> bool

(** For commands whose default is to not discharge but to export:
    Global in sections forces discharge, Global not in section is the default;
    Local in sections is the default, Local not in section forces non-export *)

val make_section_locality : bool option -> bool
val use_section_locality : bool option -> bool
val enforce_section_locality : bool option -> bool -> bool

(** * Positioning locality for commands supporting export but not discharge *)

(** For commands whose default is to export (if not in section):
    Global in sections is forbidden, Global not in section is neutral;
    Local in sections is the default, Local not in section forces non-export *)

val make_module_locality : bool option -> bool
val use_module_locality : bool option -> bool
val enforce_module_locality : bool option -> bool -> bool

val local_of_bool : bool -> locality
val bool_of_local : locality -> bool
