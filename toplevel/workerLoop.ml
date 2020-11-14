(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let rec parse = function
  | "--xml_format=Ppcmds" :: rest -> parse rest
  | x :: rest -> x :: parse rest
  | [] -> []

let worker_parse_extra ~opts extra_args =
  (), parse extra_args

let worker_init init () ~opts =
  Flags.quiet := true;
  init ();
  Coqtop.init_toploop opts

let worker_specific_usage name = Usage.{
  executable_name = name;
  extra_args = "";
  extra_options = ("\n" ^ name ^ " specific options:\
\n  --xml_format=Ppcmds    serialize pretty printing messages using the std_ppcmds format\n");
}

let start ~init ~loop name =
  let open Coq_toplevel in
  let custom = {
    parse_extra = worker_parse_extra;
    help = worker_specific_usage name;
    opts = Coqargs.default Stm.AsyncOpts.default_opts;
    init = worker_init init;
    run = (fun () ~opts:_ _state (* why is state not used *) -> loop ());
    parse_dm_flags = Stm.AsyncOpts.parse;
    init_dm = Stm.init_core;
    rcfile_loader = Vernac.rcfile_loader
  } in
  start_coq ~initialization_feeder:Coqloop.coqloop_feed custom
