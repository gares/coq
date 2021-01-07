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

let loop injections =
  LspManager.init injections;
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

let _ =
  Coqinit.init_ocaml ();
  let initial_args =
    match CoqProject_file.find_project_file ~from:(Unix.getcwd ()) ~projfile_name:"_CoqProject" with
    | None -> Coqargs.default
    | Some f ->
      let project = CoqProject_file.read_project_file ~warning_fn:(fun _ -> ()) f in
      let args = CoqProject_file.coqtop_args_from_project project in
      log @@ "Args from project file: " ^ String.concat " " args;
      fst @@ Coqargs.parse_args ~usage:vscoqtop_specific_usage ~init:Coqargs.default args in
  let opts, () = Coqinit.parse_arguments ~usage:vscoqtop_specific_usage ~initial_args ~parse_extra:(fun x -> (), x) () in
  let injections = Coqinit.init_runtime opts in
  Sys.(set_signal sigint Signal_ignore);
  loop injections
