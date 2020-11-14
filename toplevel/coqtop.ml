(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs
open Coq_toplevel

(** This file provides generic support for Coq executables + specific
    support for the coqtop executable *)

let () = at_exit flush_all

let ( / ) = Filename.concat

let get_version_date () =
  try
    let ch = open_in (Envars.coqlib () / "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    (ver,rev)
  with e when CErrors.noncritical e ->
    (Coq_config.version,Coq_config.date)

let print_header () =
  let (ver,rev) = get_version_date () in
  Feedback.msg_info (str "Welcome to Coq " ++ str ver ++ str " (" ++ str rev ++ str ")");
  flush_all ()

(******************************************************************************)
(* Color Options                                                              *)
(******************************************************************************)
let init_color opts =
  let has_color = match opts.color with
  | `OFF -> false
  | `EMACS -> false
  | `ON -> true
  | `AUTO ->
    Terminal.has_style Unix.stdout &&
    Terminal.has_style Unix.stderr &&
    (* emacs compilation buffer does not support colors by default,
       its TERM variable is set to "dumb". *)
    try Sys.getenv "TERM" <> "dumb" with Not_found -> false
  in
  let term_color =
    if has_color then begin
      let colors = try Some (Sys.getenv "COQ_COLORS") with Not_found -> None in
      match colors with
      | None -> Topfmt.default_styles (); true        (* Default colors *)
      | Some "" -> false                              (* No color output *)
      | Some s -> Topfmt.parse_color_config s; true   (* Overwrite all colors *)
    end
    else begin
      Topfmt.default_styles (); false                 (* textual markers, no color *)
    end
  in
  if opts.color = `EMACS then
    Topfmt.set_emacs_print_strings ()
  else if not term_color then begin
      Proof_diffs.write_color_enabled term_color;
    if Proof_diffs.show_diffs () then
      (prerr_endline "Error: -diffs requires enabling -color"; exit 1)
  end;
  Topfmt.init_terminal_output ~color:term_color

let print_style_tags opts =
  let () = init_color opts in
  let tags = Topfmt.dump_tags () in
  let iter (t, st) =
    let opt = Terminal.eval st ^ t ^ Terminal.reset ^ "\n" in
    print_string opt
  in
  let make (t, st) =
    let tags = List.map string_of_int (Terminal.repr st) in
    (t ^ "=" ^ String.concat ";" tags)
  in
  let repr = List.map make tags in
  let () = Printf.printf "COQ_COLORS=\"%s\"\n" (String.concat ":" repr) in
  let () = List.iter iter tags in
  flush_all ()

let init_document opts =
  (* Coq init process, phase 3: Stm initialization, backtracking state.

     It is essential that the module system is in a consistent
     state before we take the first snapshot. This was not
     guaranteed in the past, but now is thanks to the STM API.
  *)
  (* Next line allows loading .vos files when in interactive mode *)
  Flags.load_vos_libraries := true;
  let ml_load_path, vo_load_path = build_load_path opts in
  let injections = injection_commands opts in
  let document_manager_options = opts.config.dm_flags in
  let open Vernac.State in
  let doc, sid =
    Stm.(new_doc
           { Vernac_document.doc_type = Vernac_document.Interactive opts.config.logic.toplevel_name;
             ml_load_path; vo_load_path; injections; document_manager_options;
           }) in
  { doc; sid; proof = None; time = opts.config.time }

(** ****************************************)
(** Specific support for coqtop executable *)

type query = PrintTags
type run_mode = Interactive | Query of query | Batch

let init_toploop opts =
  let state = init_document opts in
  let state = Ccompile.load_init_vernaculars opts ~state in
  state

let coqtop_init run_mode ~opts =
  if run_mode = Batch then Flags.quiet := true;
  init_color opts.config;
  Flags.if_verbose print_header ();
  init_toploop opts

let coqtop_parse_extra ~opts extras =
  let rec parse_extra run_mode = function
  | "-batch" :: rest -> parse_extra Batch rest
  | "-list-tags" :: rest -> parse_extra (Query PrintTags) rest
  | x :: rest ->
    let run_mode, rest = parse_extra run_mode rest in run_mode, x :: rest
  | [] -> run_mode, [] in
  let run_mode, extras = parse_extra Interactive extras in
  run_mode, extras

let coqtop_run run_mode ~opts state =
  match run_mode with
  | Interactive -> Coqloop.loop ~opts ~state
  | Query PrintTags -> print_style_tags opts.config; exit 0
  | Batch -> exit 0

let coqtop_specific_usage = Usage.{
  executable_name = "coqtop";
  extra_args = "";
  extra_options = "\n\
coqtop specific options:\n\
\n  -batch                 batch mode (exits after interpretation of command line)\
\n"
}

let coqtop_toplevel =
  { parse_extra = coqtop_parse_extra
  ; help = coqtop_specific_usage
  ; init = coqtop_init
  ; run = coqtop_run
  ; opts = Coqargs.default Stm.AsyncOpts.default_opts
  ; parse_dm_flags = Stm.AsyncOpts.parse
  ; init_dm = Stm.init_core
  ; rcfile_loader = Vernac.rcfile_loader
  }
