(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Definition of custom toplevels.
    [init] is used to do custom command line argument parsing.
    [run] launches a custom toplevel.
*)

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

(** The generic Coq main module. [start custom] will parse the command line,
   print the banner, initialize the load path, load the input state,
   load the files given on the command line, load the resource file,
   produce the output state if any, and finally will launch
   [custom.run]. *)
val start_coq : initialization_feeder:(Feedback.feedback -> unit) -> ('a,'b,'c) custom_toplevel -> unit
