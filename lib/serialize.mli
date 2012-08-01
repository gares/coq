(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Applicative part of the interface of CoqIde calls to Coq *)

open Interface

type xml =
  | Element of (string * (string * string) list * xml list)
  | PCData of string

type 'a call

(** Running a command (given as a string).
    - The 1st flag indicates whether to use "raw" mode
      (less sanity checks, no impact on the undo stack).
      Suitable e.g. for queries, or for the Set/Unset
      of display options that coqide performs all the time.
    - The 2nd flag controls the verbosity.
    - The returned string contains the messages produced
      by this command, but not the updated goals (they are
      to be fetch by a separated [current_goals]). *)
val interp : interp_sty -> interp_rty call

(** Backtracking to a given state *)
val backto : backto_sty -> backto_rty call

(** Fetching the list of current goals. Return [None] if no proof is in 
    progress, [Some gl] otherwise. *)
val goals : goals_sty -> goals_rty call

(** Retrieving the tactics applicable to the current goal. [None] if there is 
    no proof in progress. *)
val hints : hints_sty -> hints_rty call

(** The status, for instance "Ready in SomeSection, proving Foo" *)
val status : status_sty -> status_rty call

(** Is a directory part of Coq's loadpath ? *)
val inloadpath : inloadpath_sty -> inloadpath_rty call

(** Create a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables. *)
val mkcases : mkcases_sty -> mkcases_rty call

(** Retrieve the list of unintantiated evars in the current proof. [None] if no
    proof is in progress. *)
val evars : evars_sty -> evars_rty call

(** Search for objects satisfying the given search flags. *)
val search : search_sty -> search_rty call

(** About coq. *)
val about : about_sty -> about_rty call

(** Retrieve the list of options of the current toplevel, together with their 
    state. *)
val get_options : get_options_sty -> get_options_rty call

(** Set the options to the given value. Warning: this is not atomic, so whenever
    the call fails, the option state can be messed up... This is the caller duty
    to check that everything is correct. *)
val set_options : set_options_sty -> set_options_rty call

(** Quit gracefully the interpreter. *)
val quit : quit_sty -> quit_rty call

(** The structure that coqtop should implement *)

val abstract_eval_call : handler -> 'a call -> 'a value

(** * Protocol version *)

val protocol_version : string

(** * XML data marshalling *)

exception Marshal_error

val of_value : ('a -> xml) -> 'a value -> xml
val to_value : (xml -> 'a) -> xml -> 'a value

val of_call : 'a call -> xml
val to_call : xml -> 'a call

(* Out Of Band message *)
val of_oob_message : message -> xml
val to_oob_message : xml -> message
val is_oob_message : xml -> bool

val of_answer : 'a call -> 'a value -> xml
val to_answer : xml -> 'a value

(** * Debug printing *)

val pr_call : 'a call -> string
val pr_value : 'a value -> string
val pr_full_value : 'a call -> 'a value -> string
