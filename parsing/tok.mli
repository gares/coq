(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

(* A token carries its kind, its location in the input file, all the
   blanks (including comments) that come before it and finally its
   position in the input character stream *)

module Blank : sig
  type t = {
    loc : Loc.t;
    v : kind;
  }
  and kind =
  | Blanks of string
  | Comment of string
end

type t = {
  v : kind;
  loc : Loc.t;
  blanks_before : Blank.t list;
  pos : int
}
and kind =
  | KEYWORD of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | INT of string
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | EOI

val mk_token : loc:Loc.t -> pos:int -> ?blanks_rev:Blank.t list -> kind -> t

val equal : t -> t -> bool
(* pass true for diff_mode *)
val extract_string : bool -> t -> string
val to_string : t -> string
val to_string_kind : kind -> string
(* Needed to fit Camlp5 signature *)
val print : Format.formatter -> t -> unit
val match_keyword : string -> t -> bool

(** for camlp5,
    eg GRAMMAR EXTEND ..... [ IDENT "x" -> .... END
    is a pattern ("IDENT", Some "x")
*)
type pattern = string * string option (* = Plexing.pattern *)

val is_keyword : pattern -> string option
val pattern_for_EOI : pattern
val pattern_for_KEYWORD : string -> pattern
val match_pattern : pattern -> t -> string
