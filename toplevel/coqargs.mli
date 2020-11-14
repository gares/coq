(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [`ON | `AUTO | `EMACS | `OFF]

val default_toplevel : Names.DirPath.t

type native_compiler = NativeOff | NativeOn of { ondemand : bool }

type coqargs_logic_config = {
  impredicative_set : Declarations.set_predicativity;
  indices_matter    : bool;
  toplevel_name     : Vernac_document.interactive_top;
}

type 'dm_flags coqargs_config = {
  logic       : coqargs_logic_config;
  rcfile      : string option;
  coqlib      : string option;
  color       : color;
  enable_VM   : bool;
  native_compiler : native_compiler;
  native_output_dir : CUnix.physical_path;
  native_include_dirs : CUnix.physical_path list;
  dm_flags   : 'dm_flags;
  debug       : bool;
  time        : bool;
  print_emacs : bool;
}

type coqargs_pre = {
  boot        : bool;
  load_init   : bool;
  load_rcfile : bool;

  ml_includes : CUnix.physical_path list;
  vo_includes : Loadpath.vo_path list;

  load_vernacular_list : (string * bool) list;
  injections  : Vernac_document.injection_command list;

  inputstate  : string option;
}

type coqargs_query =
  | PrintWhere | PrintConfig
  | PrintVersion | PrintMachineReadableVersion
  | PrintHelp of Usage.specific_usage

type coqargs_main =
  | Queries of coqargs_query list
  | Run

type coqargs_post = {
  memory_stat : bool;
  output_context : bool;
}

type 'dm_flags t = {
  config : 'dm_flags coqargs_config;
  pre : coqargs_pre;
  main : coqargs_main;
  post : coqargs_post;
}

(* Default options *)
val default : 'dm_flags -> 'dm_flags t

val parse_args : help:Usage.specific_usage -> init:'dm_flags t -> parse_dm_flags:(init:'dm_flags -> string list -> 'dm_flags * string list) -> string list -> 'dm_flags t * string list
val error_wrong_arg : string -> unit

val injection_commands : 'dm_flags t -> Vernac_document.injection_command list
val build_load_path : 'dm_flags t -> CUnix.physical_path list * Loadpath.vo_path list
