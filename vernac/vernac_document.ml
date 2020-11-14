(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type interactive_top = TopLogical of Names.DirPath.t | TopPhysical of string

type doc_type =
  | VoDoc       of string
  | VioDoc      of string
  | Interactive of interactive_top

type option_command = OptionSet of string option | OptionUnset

type injection_command =
  | OptionInjection of (Goptions.option_name * option_command)
  | RequireInjection of (string * string option * bool option)

type 'manager_opts doc_init_options =
  { doc_type : doc_type
  ; ml_load_path : CUnix.physical_path list
  ; vo_load_path   : Loadpath.vo_path list
  ; injections : injection_command list
  ; document_manager_options  : 'manager_opts
  }

let init_document { ml_load_path; vo_load_path; injections; doc_type } =

   let dirpath_of_file f =
   let ldir0 =
      try
         let lp = Loadpath.find_load_path (Filename.dirname f) in
         Loadpath.logical lp
      with Not_found -> Libnames.default_root_prefix
   in
   let f = try Filename.chop_extension (Filename.basename f) with Invalid_argument _ -> f in
   let id = Names.Id.of_string f in
   Libnames.add_dirpath_suffix ldir0 id in

  let require_file (dir, from, exp) =
    let mp = Libnames.qualid_of_string dir in
    let mfrom = Option.map Libnames.qualid_of_string from in
    Flags.silently (Vernacentries.vernac_require mfrom exp) [mp] in

  let interp_set_option opt v old =
    let open Goptions in
    let err expect =
      let opt = String.concat " " opt in
      let got = v in (* avoid colliding with Pp.v *)
      CErrors.user_err
        Pp.(str "-set: " ++ str opt ++
            str" expects " ++ str expect ++
            str" but got " ++ str got)
    in
    match old with
    | BoolValue _ ->
      let v = match String.trim v with
        | "true" -> true
        | "false" | "" -> false
        | _ -> err "a boolean"
      in
      BoolValue v
    | IntValue _ ->
      let v = String.trim v in
      let v = match int_of_string_opt v with
        | Some _ as v -> v
        | None -> if v = "" then None else err "an int"
      in
      IntValue v
    | StringValue _ -> StringValue v
    | StringOptValue _ -> StringOptValue (Some v) in

  let set_option = let open Goptions in function
      | opt, OptionUnset -> unset_option_value_gen ~locality:OptLocal opt
      | opt, OptionSet None -> set_bool_option_value_gen ~locality:OptLocal opt true
      | opt, OptionSet (Some v) -> set_option_value ~locality:OptLocal (interp_set_option opt) opt v in

  let handle_injection = function
    | RequireInjection r -> require_file r
    (* | LoadInjection l -> *)
    | OptionInjection o -> set_option o in

  (* Set load path; important, this has to happen before we declare
     the library below as [Declaremods/Library] will infer the module
     name by looking at the load path! *)
  List.iter Mltop.add_ml_dir ml_load_path;
  List.iter Loadpath.add_vo_path vo_load_path;

  let ldir = match doc_type with
    | Interactive (TopLogical ldir) -> ldir
    | Interactive (TopPhysical f) -> dirpath_of_file f
    | VoDoc f -> dirpath_of_file f
    | VioDoc f -> dirpath_of_file f
  in

  let () = Flags.verbosely Declaremods.start_library ldir in

  (* Import initial libraries. *)
  List.iter handle_injection injections;

  ldir
