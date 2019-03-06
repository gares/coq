(* camlp5r *)
(* plexing.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pattern = string * string option

let to_string_pattern = function
  | k, None -> k^"(_)"
  | k, Some v -> k^"(\""^v^"\")"

type 'te lexer_func = char Stream.t -> 'te Stream.t

type 'te lexer =
  {
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : pattern -> 'te -> string;
    tok_text : pattern -> string;
  }

