(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This should be functional but it is not due to the interface *)
val add_keyword : string -> unit
val remove_keyword : string -> unit
val is_keyword : string -> bool
val keywords : unit -> CString.Set.t

type keyword_state
val set_keyword_state : keyword_state -> unit
val get_keyword_state : unit -> keyword_state

val check_ident : string -> unit
val is_ident : string -> bool
val check_keyword : string -> unit
val terminal : string -> Tok.pattern

(** The lexer of Coq: *)

include Gramlib.Grammar.GLexerType with type te = Tok.t

module Error : sig
  type t
  exception E of t
  val to_string : t -> string
end

(** Create a lexer.  diff_mode:true enables alternate handling for computing
   diffs.  It ensures that, ignoring white space, the concatenated tokens
   equal the input string.  Specifically:
   - for strings, return the enclosing quotes as tokens and treat the quoted
     value as if it was unquoted, possibly becoming multiple tokens
   - for comments, return the ( * as a token and treat the contents of the
     comment as if it was not in a comment, possibly becoming multiple tokens
   - return any unrecognized Ascii or UTF-8 character as a string

   The companion getter returns the list of token lexed so far (if
   log_tokens:true). This is used by the beautifier.
*)
val make_lexer_func :
  diff_mode:bool -> log_tokens:bool -> Loc.source ->
    Tok.t Gramlib.Plexing.lexer_func * (unit -> Tok.t list)

val lexer : Tok.t Gramlib.Plexing.lexer
