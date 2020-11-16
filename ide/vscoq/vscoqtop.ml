(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

let vscoqtop_loop run_mode ~opts:_ state =
  LspManager.init ();
  let rec vscoqtop_loop (events : LspManager.events) =
    log @@ "[T] looking for next step";
    flush_all ();
    let (ready, remaining) = Sel.wait events in
    let nremaining = List.length remaining in
    log @@ "Main vscoqtop_loop events ready: " ^ Pp.string_of_ppcmds Pp.(prlist_with_sep spc LspManager.pr_event ready) ^ " , " ^ string_of_int nremaining ^ " events waiting";
    vscoqtop_loop (remaining @ CList.map_append LspManager.handle_event ready)
  in
  try vscoqtop_loop [LspManager.lsp]
  with exn ->
    let bt = Printexc.get_backtrace () in
    log Printexc.(to_string exn);
    log bt;
    flush_all ()

let vscoqtop_specific_usage = {
  Usage.executable_name = "vscoqtop";
  extra_args = "";
  extra_options = "";
}

type vscoqtop_specific_options = unit

let vscoqtop_parse_extra_flags ~opts extra_args =
  (() : vscoqtop_specific_options), []


let vscoqtop_init (document_manager_options : vscoqtop_specific_options) ~opts =
  let ml_load_path, vo_load_path = Coqargs.build_load_path opts in
  let injections = Coqargs.injection_commands opts in
  let _lp = Vernac_document.init_document Vernac_document.{
    document_manager_options; ml_load_path; vo_load_path; injections; doc_type = Interactive (TopPhysical "top.v") } in
  opts

type dm_options = unit

let parse_dm_flags ~init l = init, l

let opts =
  log @@ "Looking for _CoqProject file in: " ^ Unix.getcwd ();
  match CoqProject_file.find_project_file ~from:(Unix.getcwd ()) ~projfile_name:"_CoqProject" with
  | None -> Coqargs.default ()
  | Some f ->
    let project = CoqProject_file.read_project_file ~warning_fn:(fun _ -> ()) f in
    let args = CoqProject_file.coqtop_args_from_project project in
    log @@ "Args from project file: " ^ String.concat " " args;
    fst @@ Coqargs.parse_args ~parse_dm_flags ~help:vscoqtop_specific_usage ~init:(Coqargs.default ()) args

let vscoqtop = Coq_toplevel.{
  parse_extra = vscoqtop_parse_extra_flags;
  help = vscoqtop_specific_usage;
  init = vscoqtop_init;
  run = vscoqtop_loop;
  opts;
  parse_dm_flags = (fun ~init l -> init, l);
  init_dm = (fun _ -> ());
  rcfile_loader = (fun ~state _ -> state); (* we don't care, do we? *)
}

let _ =
  Sys.(set_signal sigint Signal_ignore);
  let () = Coq_toplevel.start_coq ~initialization_feeder:(fun _ -> ()) vscoqtop in
  exit 0
