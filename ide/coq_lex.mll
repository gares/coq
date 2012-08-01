(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

{
  exception Unterminated
}

let space =
  [' ' '\n' '\r' '\t' '\012'] (* '\012' is form-feed *)

let undotted_sep = [ '{' '}' '-' '+' '*' ]

let dot_sep = '.' (space | eof)

let begin_comment = '(' '*'
let end_comment   = '*' ')'

rule coq_string = parse
  | "\\\"" { coq_string lexbuf }
  | "\\\\" { coq_string lexbuf }
  | "\"" { () }
  | eof { () }
  | _ { coq_string lexbuf }

and comment = parse
  | begin_comment { ignore (comment lexbuf); comment lexbuf }
  | "\"" { let () = coq_string lexbuf in comment lexbuf }
  | end_comment { (true, Lexing.lexeme_end lexbuf + 1) }
  | eof { (false, Lexing.lexeme_end lexbuf) }
  | _ { comment lexbuf }

and sentence initial soff = parse
  | begin_comment {
      let truly_terminated, comm_end = comment lexbuf in
      if not truly_terminated then raise Unterminated;
      (* A comment alone is a sentence.
	 A comment in a sentence doesn't terminate the sentence.
         Note: comm_end is the first position _after_ the comment,
	 as required when tagging a zone, hence the -1 to locate the
	 ")" terminating the comment.
      *)
      if initial then true, soff, comm_end - 1 else sentence false soff lexbuf
    }
  | "\"" {
      let () = coq_string lexbuf in
      sentence false soff lexbuf
    }
  | ".." {
      (* We must have a particular rule for parsing "..", where no dot
	 is a terminator, even if we have a blank afterwards
	 (cf. for instance the syntax for recursive notation).
	 This rule and the following one also allow to treat the "..."
	 special case, where the third dot is a terminator. *)
      sentence false soff lexbuf
    }
    (* The usual "." terminator *)
  | dot_sep { false, soff, Lexing.lexeme_end lexbuf }
  | undotted_sep {
      (* Separators like { or } and bullets * - + are only active
	 at the start of a sentence *)
      if initial then false, soff, Lexing.lexeme_end lexbuf
      else sentence false soff lexbuf
    }
  | space+ {
       (* Parsing spaces is the only situation preserving initiality *)
       sentence initial
         (if initial then Lexing.lexeme_end lexbuf else soff) lexbuf
    }
  | _ {
      (* Any other characters *)
      sentence false soff lexbuf
    }
  | eof { raise Unterminated }

{

  (** Parse a sentence in string [slice], tagging relevant parts with
      function [stamp], and returning the position of the first
      sentence delimitor (either "." or "{" or "}" or the end of a comment).
      It will raise [Unterminated] when no end of sentence is found.
  *)

  let delimit_sentence slice =
    sentence true 0 (Lexing.from_string slice)

}
