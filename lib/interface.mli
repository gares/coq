(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Declarative part of the interface of CoqIde calls to Coq *)

(** * Generic structures *)

type raw = bool
type verbose = bool

(** The type of coqtop goals *)
type goal = {
  goal_id : string;
  (** Unique goal identifier *)
  goal_hyp : string list;
  (** List of hypotheses *)
  goal_ccl : string;
  (** Goal conclusion *)
}

type evar = {
  evar_info : string;
  (** A string describing an evar: type, number, environment *)
}

type status = {
  status_path : string list;
  (** Module path of the current proof *)
  status_proofname : string option;
  (** Current proof name. [None] if no focussed proof is in progress *)
  status_allproofs : string list;
  (** List of all pending proofs. Order is not significant *)
  status_statenum : int;
  (** A unique id describing the state of coqtop *)
  status_proofnum : int;
  (** An id describing the state of the current proof. *)
}

type goals = {
  fg_goals : goal list;
  (** List of the focussed goals *)
  bg_goals : (goal list * goal list) list;
  (** Zipper representing the unfocussed background goals *)
}

type hint = (string * string) list
(** A list of tactics applicable and their appearance *)

type option_name = string list

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string

(** Summary of an option status *)
type option_state = {
  opt_sync  : bool;
  (** Whether an option is synchronous *)
  opt_depr  : bool;
  (** Wheter an option is deprecated *)
  opt_name  : string;
  (** A short string that is displayed when using [Test] *)
  opt_value : option_value;
  (** The current value of the option *)
}

type search_constraint =
(** Whether the name satisfies a regexp (uses Ocaml Str syntax) *)
| Name_Pattern of string
(** Whether the object type satisfies a pattern *)
| Type_Pattern of string
(** Whether some subtype of object type satisfies a pattern *)
| SubType_Pattern of string
(** Whether the object pertains to a module *)
| In_Module of string list
(** Bypass the Search blacklist *)
| Include_Blacklist

(** A list of search constraints; the boolean flag is set to [false] whenever
    the flag should be negated. *)
type search_flags = (search_constraint * bool) list

type search_answer = {
  search_answer_full_path : string list;
  search_answer_base_name : string;
  search_answer_type : string;
}

type coq_info = {
  coqtop_version : string;
  protocol_version : string;
  release_date : string;
  compile_date : string;
}

(** * Coq answers to CoqIde *)

type message_level =
| Debug of string
| Info
| Notice
| Warning
| Error

type message = {
  message_level : message_level;
  message_content : string;
}

(* span, start and end of the error *)
type location =
  Stategraph.state_id * (int * int) option

type 'a success = Stategraph.state_id list * (* good states *)
                  'a                         (* the result  *)
type failure    = Stategraph.state_id list * (* good states *)
                  Stategraph.state_id list * (* bad states  *)
                  location * string          (* the error   *)

type 'a value =
  | Good of 'a success
  | Fail of failure

(** * The structure that coqtop should implement *)

type interp_rty      = Stategraph.state_id
type backto_rty      = unit
type goals_rty       = goals option
type evars_rty       = evar list option
type hints_rty       = (hint list * hint) option
type status_rty      = status
type get_options_rty = (option_name * option_state) list
type set_options_rty = unit
type inloadpath_rty  = bool
type mkcases_rty     = string list list 
type search_rty      = search_answer list
type quit_rty        = unit
type about_rty       = coq_info

type interp_sty      = raw * verbose * string
type backto_sty      = Stategraph.state_id
type goals_sty       = unit
type evars_sty       = unit
type hints_sty       = unit
type status_sty      = bool
type set_options_sty = (option_name * option_value) list
type get_options_sty = unit
type inloadpath_sty  = string
type mkcases_sty     = string
type search_sty      = (search_constraint * bool) list
type quit_sty        = unit
type about_sty       = unit

type handler = {
  interp      : interp_sty      ->      interp_rty success;
  backto      : backto_sty      ->      backto_rty success;
  goals       : goals_sty       ->       goals_rty success;
  evars       : evars_sty       ->       evars_rty success;
  hints       : hints_sty       ->       hints_rty success;
  status      : status_sty      ->      status_rty success;
  get_options : get_options_sty -> get_options_rty success;
  set_options : set_options_sty -> set_options_rty success;
  inloadpath  : inloadpath_sty  ->  inloadpath_rty success;
  mkcases     : mkcases_sty     ->     mkcases_rty success;
  search      : search_sty      ->      search_rty success;
  quit        : quit_sty        ->        quit_rty success;
  about       : about_sty       ->       about_rty success;
  handle_exn  : exn             ->                 failure;
}
