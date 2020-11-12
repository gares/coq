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

let loop run_mode ~opts:_ state =
  LspManager.init ();
  let rec loop (events : LspManager.events) =
    log @@ "[T] looking for next step";
    flush_all ();
    let (ready, remaining) = Sel.wait events in
    let nremaining = List.length remaining in
    log @@ "Main loop events ready: " ^ Pp.string_of_ppcmds Pp.(prlist_with_sep spc LspManager.pr_event ready) ^ " , " ^ string_of_int nremaining ^ " events waiting";
    loop (remaining @ CList.map_append LspManager.handle_event ready)
  in
  try loop [LspManager.lsp]
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

let islave_parse ~opts extra_args =
  let open Coqtop in
  let run_mode, extra_args = coqtop_toplevel.parse_extra ~opts extra_args in
  run_mode, []

let islave_default_opts flags =
  Coqargs.{ flags with
    config = { default.config with
      stm_flags = { default.config.stm_flags with
         Stm.AsyncOpts.async_proofs_worker_priority = CoqworkmgrApi.High }}}

let islave_init run_mode ~opts =
  Coqtop.init_toploop opts

let main () =
  log @@ "Looking for _CoqProject file in: " ^ Unix.getcwd ();
  let opts =
    match CoqProject_file.find_project_file ~from:(Unix.getcwd ()) ~projfile_name:"_CoqProject" with
    | None -> islave_default_opts Coqargs.default
    | Some f ->
      let project = CoqProject_file.read_project_file ~warning_fn:(fun _ -> ()) f in
      let args = CoqProject_file.coqtop_args_from_project project in
      log @@ "Args from project file: " ^ String.concat " " args;
      fst @@ Coqargs.parse_args ~help:vscoqtop_specific_usage ~init:Coqargs.default args
  in
  let custom = Coqtop.{
      parse_extra = islave_parse;
      help = vscoqtop_specific_usage;
      init = islave_init;
      run = loop;
      opts } in
  Coqtop.start_coq custom

let _ =
  Sys.(set_signal sigint Signal_ignore);
  main ()