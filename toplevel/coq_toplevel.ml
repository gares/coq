(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqargs

type ('a,'dm) extra_args_fn = opts:'dm Coqargs.t -> string list -> 'a * string list

type ('a,'b,'dm) custom_toplevel =
  { parse_extra : ('a,'dm) extra_args_fn
  ; help : Usage.specific_usage
  ; init : 'a -> opts:'dm Coqargs.t -> 'b
  ; run : 'a -> opts:'dm Coqargs.t -> 'b -> unit
  ; opts : 'dm Coqargs.t
  ; parse_dm_flags : init:'dm -> string list -> 'dm * string list
  ; init_dm : 'dm -> unit
  ; rcfile_loader : state:'b -> string -> 'b
  }

(******************************************************************************)
(* Fatal Errors                                                               *)
(******************************************************************************)

(** Prints info which is either an error or an anomaly and then exits
    with the appropriate error code *)
let fatal_error_exn exn =
  Topfmt.(in_phase ~phase:Initialization print_err_exn exn);
  flush_all ();
  let exit_code =
    if (CErrors.is_anomaly exn) then 129 else 1
  in
  exit exit_code

(******************************************************************************)
(* Input/Output State                                                         *)
(******************************************************************************)
let inputstate opts =
  Option.iter (fun istate_file ->
    let fname = Loadpath.locate_file (CUnix.make_suffix istate_file ".coq") in
    Vernacstate.System.load fname) opts.Coqargs.inputstate

(** GC tweaking *)

(** Coq is a heavy user of persistent data structures and symbolic ASTs, so the
    minor heap is heavily solicited. Unfortunately, the default size is far too
    small, so we enlarge it a lot (128 times larger).

    To better handle huge memory consumers, we also augment the default major
    heap increment and the GC pressure coefficient.
*)

let init_gc () =
  try
    (* OCAMLRUNPARAM environment variable is set.
     * In that case, we let ocamlrun to use the values provided by the user.
     *)
    ignore (Sys.getenv "OCAMLRUNPARAM")

  with Not_found ->
    (* OCAMLRUNPARAM environment variable is not set.
     * In this case, we put in place our preferred configuration.
     *)
    Gc.set { (Gc.get ()) with
             Gc.minor_heap_size = 32*1024*1024; (* 32Mwords x 8 bytes/word = 256Mb *)
             Gc.space_overhead = 120}

let print_memory_stat () =
  (* -m|--memory from the command-line *)
  Feedback.msg_notice
    Pp.(str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes" ++ fnl ());
  (* operf-macro interface:
     https://github.com/OCamlPro/operf-macro *)
  try
    let fn = Sys.getenv "OCAML_GC_STATS" in
    let oc = open_out fn in
    Gc.print_stat oc;
    close_out oc
  with _ -> ()

let init_process () =
  (* Coq's init process, phase 1:
     OCaml parameters, basic structures, and IO
   *)
  CProfile.init_profile ();
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init ()

let init_parse parse_extra parse_dm_flags help init_opts =
  let opts, extras =
    Coqargs.parse_args ~help:help ~init:init_opts ~parse_dm_flags
      (List.tl (Array.to_list Sys.argv)) in
  let customopts, extras = parse_extra ~opts extras in
  if not (CList.is_empty extras) then begin
    prerr_endline ("Don't know what to do with "^String.concat " " extras);
    prerr_endline "See -help for the list of supported options";
    exit 1
    end;
  opts, customopts

(** Coq's init process, phase 2: Basic Coq environment, plugins. *)
let init_execution opts dm_init custom_init =
  let open Coqargs in
  if opts.post.memory_stat then at_exit print_memory_stat;
  Mltop.init_known_plugins ();
  (* Configuration *)
  Global.set_engagement opts.config.logic.impredicative_set;
  Global.set_indices_matter opts.config.logic.indices_matter;
  Global.set_VM opts.config.enable_VM;
  Flags.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);
  Global.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);

  (* Native output dir *)
  Nativelib.output_dir := opts.config.native_output_dir;
  Nativelib.include_dirs := opts.config.native_include_dirs;

  (* Allow the user to load an arbitrary state here *)
  inputstate opts.pre;

  (* This state will be shared by all the documents *)
  dm_init opts.config.dm_flags;
  custom_init ~opts

let init_coqlib opts = match opts.config.coqlib with
  | None when opts.pre.boot -> ()
  | None ->
    Envars.set_coqlib ~fail:(fun msg -> CErrors.user_err Pp.(str msg));
  | Some s ->
    Envars.set_user_coqlib s

let print_query opts = function
  | PrintVersion -> Usage.version ()
  | PrintMachineReadableVersion -> Usage.machine_readable_version ()
  | PrintWhere ->
    let () = init_coqlib opts in
    print_endline (Envars.coqlib ())
  | PrintHelp h -> Usage.print_usage stderr h
  | PrintConfig ->
    let () = init_coqlib opts in
    Envars.print_config stdout Coq_config.all_src_dirs

(** Main init routine *)
let init_toplevel custom =
  let () = init_process () in
  let opts, customopts =
    init_parse custom.parse_extra custom.parse_dm_flags custom.help custom.opts
  in
  (* Querying or running? *)
  match opts.Coqargs.main with
  | Coqargs.Queries q -> List.iter (print_query opts) q; exit 0
  | Coqargs.Run ->
    let () = init_coqlib opts in
    let customstate = init_execution opts custom.init_dm (custom.init customopts) in
    opts, customopts, customstate

let start_coq ~initialization_feeder custom =
  let init_feeder = Feedback.add_feeder initialization_feeder in
  (* Init phase *)
  let opts, custom_opts, state =
    try init_toplevel custom
    with any ->
      flush_all();
      fatal_error_exn any in
  Feedback.del_feeder init_feeder;
  (* Run phase *)
  let () = custom.run ~opts custom_opts state in
  exit 0
