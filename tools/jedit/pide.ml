(*** Property lists ***)

module type Properties =
sig
  type t = (string * string) list
  val defined: t -> string -> bool
  val get: t -> string -> string option
  val put: string * string -> t -> t
  val remove: string -> t -> t
end

module Properties: Properties =
struct

type t = (string * string) list

let defined (props: t) name = List.mem_assoc name props
let get (props: t) name = try Some (List.assoc name props) with Not_found -> None
let put ((name, _) as entry) (props: t) = entry :: List.remove_assoc name props
let remove name (props: t) = List.remove_assoc name props

end



(*** Markup elements ***)

module type Markup =
sig
  type t = string * Properties.t
  val empty: t
  val is_empty: t -> bool
  val properties: Properties.t -> t -> t
  val nameN: string
  val name: string -> t -> t
  val kindN: string
end

module Markup: Markup =
struct

(* basic markup *)

type t = string * Properties.t

let empty = ("", [])

let is_empty (elem, _) = elem = ""

let properties more_props ((elem, props): t) =
  (elem, List.fold_right Properties.put more_props props)


(* misc properties *)

let nameN = "name"
let name a = properties [(nameN, a)]

let kindN = "kind"

end



(*** Coq markup elements ***)

module type Coq_Markup =
sig
  val offsetN: string
  val end_offsetN: string
  val idN: string
  val comment: Markup.t
  val keyword: Markup.t
  val declaration: Markup.t
  val proof_declaration: Markup.t
  val qed: Markup.t
  val string: Markup.t
  val delimiter: Markup.t
  val report: Markup.t
  val functionN: string
  val ready: Properties.t
  val assign_execs: Properties.t
  val removed_versions: Properties.t
end


module Coq_Markup: Coq_Markup =
struct

(* markup elements *)

let markup_elem elem = ((elem, []): Markup.t)


(* position *)

let offsetN = "offset"
let end_offsetN = "end_offset"
let idN = "id"


(* outer syntax *)

let comment = markup_elem "comment"
let keyword = markup_elem "keyword"
let declaration = markup_elem "declaration"
let proof_declaration = markup_elem "proof_declaration"
let qed = markup_elem "qed"
let string = markup_elem "string"
let delimiter = markup_elem "delimiter"


(* messages *)

let report = markup_elem "report"


(* protocol message functions *)

let functionN = "function"

let ready = [(functionN, "ready")]

let assign_execs = [(functionN, "assign_execs")]
let removed_versions = [(functionN, "removed_versions")]

end


(*** Untyped XML trees and typed representation of ML values ***)

module type XML_Data_Ops =
sig
  type 'a a
  type 'a t
  type 'a v
  val int_atom: int a
  val bool_atom: bool a
  val unit_atom: unit a
  val properties: (string * string) list t
  val string: string t
  val int: int t
  val bool: bool t
  val unit: unit t
  val pair: 'a t -> 'b t -> ('a * 'b) t
  val triple: 'a t -> 'b t -> 'c t -> ('a * 'b * 'c) t
  val list: 'a t -> 'a list t
  val option: 'a t -> 'a option t
  val variant: 'a v list -> 'a t
end

module type XML =
sig
  type attributes = (string * string) list
  type tree = Elem of ((string * attributes) * tree list) | Text of string
  type body = tree list
  exception XML_Atom of string
  exception XML_Body of tree list
  module Encode: XML_Data_Ops with
    type 'a a = 'a -> string and
    type 'a t = 'a -> body and
    type 'a v = 'a -> string list * body
  module Decode: XML_Data_Ops with
    type 'a a = string -> 'a and
    type 'a t = body -> 'a and
    type 'a v = string list * body -> 'a
end

module XML: XML =
struct

type attributes = (string * string) list
type tree = Elem of ((string * attributes) * tree list) | Text of string
type body = tree list


let map_index f =
  let rec mapp i = function
    | [] -> []
    | x :: xs -> f (i, x) :: mapp (i + 1) xs
  in mapp 0

exception XML_Atom of string
exception XML_Body of tree list


module Encode =
struct

type 'a a = 'a -> string
type 'a t = 'a -> body
type 'a v = 'a -> string list * body


(* atomic values *)

let int_atom = string_of_int

let bool_atom = function false -> "0" | true -> "1"

let unit_atom () = ""


(* structural nodes *)

let node ts = Elem ((":", []), ts)

let vector = map_index (fun (i, x) -> (int_atom i, x))

let tagged (tag, (xs, ts)) = Elem ((int_atom tag, vector xs), ts)


(* representation of standard types *)

let properties props = [Elem ((":", props), [])]

let string = function "" -> [] | s -> [Text s]

let int i = string (int_atom i)

let bool b = string (bool_atom b)

let unit () = string (unit_atom ())

let pair f g (x, y) = [node (f x); node (g y)]

let triple f g h (x, y, z) = [node (f x); node (g y); node (h z)]

let list f xs = List.map (fun x -> node (f x)) xs

let option f = function None -> [] | Some x -> [node (f x)]

let variant fns x =
  let rec get_index i = function
    | [] -> raise (Failure "XML.Encode.variant")
    | f :: fs -> try (i, f x) with Match_failure _ -> get_index (i + 1) fs
  in [tagged (get_index 0 fns)]

end


module Decode =
struct

type 'a a = string -> 'a
type 'a t = body -> 'a
type 'a v = string list * body -> 'a


(* atomic values *)

let int_atom s =
  try int_of_string s
    with Invalid_argument _ -> raise (XML_Atom s)

let bool_atom = function
  | "0" -> false
  | "1" -> true
  | s -> raise (XML_Atom s)

let unit_atom s =
  if s = "" then () else raise (XML_Atom s)


(* structural nodes *)

let node = function
  | Elem ((":", []), ts) -> ts
  | t -> raise (XML_Body [t])

let vector =
  map_index (function (i, (a, x)) -> if int_atom a = i then x else raise (XML_Atom a))

let tagged = function
  | Elem ((name, atts), ts) -> (int_atom name, (vector atts, ts))
  | t -> raise (XML_Body [t])


(* representation of standard types *)

let properties = function
  | [Elem ((":", props), [])] -> props
  | ts -> raise (XML_Body ts)

let string = function
  | [] -> ""
  | [Text s] -> s
  | ts -> raise (XML_Body ts)

let int ts = int_atom (string ts)

let bool ts = bool_atom (string ts)

let unit ts = unit_atom (string ts)

let pair f g = function
  | [t1; t2] -> (f (node t1), g (node t2))
  | ts -> raise (XML_Body ts)

let triple f g h = function
  | [t1; t2; t3] -> (f (node t1), g (node t2), h (node t3))
  | ts -> raise (XML_Body ts)

let list f = List.map (fun t -> f (node t))

let option f = function
  | [] -> None
  | [t] -> Some (f (node t))
  | ts -> raise (XML_Body ts)

let variant fs = function
  | [t] ->
      let (tag, (xs, ts)) = tagged t in
      let f = try List.nth fs tag with Invalid_argument _ -> raise (XML_Body [t]) in
      f (xs, ts)
  | ts -> raise (XML_Body ts)

end

end



(*** YXML transfer syntax ***)

(*
Efficient text representation of XML trees using extra characters X
and Y -- no escaping, may nest marked text verbatim.  Suitable for
direct inlining into plain text.

Markup <elem att="val" ...>...body...</elem> is encoded as:

  X Y name Y att=val ... X
  ...
  body
  ...
  X Y X
*)

module type YXML =
sig
  val char_X: char
  val char_Y: char
  val implode: string list -> string
  val split: bool -> char -> string -> string list
  val no_output: string * string
  val output_markup: Markup.t -> string * string
  val markup: Markup.t -> string -> string
  val markup_only: Markup.t -> string
  val string_of_body: XML.body -> string
  val string_of: XML.tree -> string
  val parse_body: string -> XML.body
  val parse: string -> XML.tree
end

module YXML: YXML =
struct

(* markers *)

let char_X = '\005'
let char_Y = '\006'

let str_X = String.make 1 char_X
let str_Y = String.make 1 char_Y

let str_XY = str_X ^ str_Y
let str_XYX = str_XY ^ str_X

let detect s = String.contains s char_X || String.contains s char_Y


(* ML basics *)

let (|>) x f = f x
let (@>) f g x = g (f x)

let rec fold f list y =
  match list with
    [] -> y
  | x :: xs -> fold f xs (f x y)


(* output *)

let implode = String.concat ""
let content xs = implode (List.rev xs)
let add x xs = if x = "" then xs else x :: xs

let no_output = ("", "")

let output_markup (name, atts) =
  if name = "" then no_output
  else
    (str_XY ^ name ^ implode (List.map (fun (a, x) -> str_Y ^ a ^ "=" ^ x) atts) ^ str_X, str_XYX)

let markup m txt =
  let (bg, en) = output_markup m
  in bg ^ txt ^ en

let markup_only m = markup m ""

let string_of_body body =
  let attrib (a, x) = add str_Y @> add a @> add "=" @> add x in
  let rec tree = function
    | XML.Elem ((name, atts), ts) ->
        add str_XY @> add name @> fold attrib atts @> add str_X @>
        trees ts @>
        add str_XYX
    | XML.Text s -> add s
  and trees ts = fold tree ts
  in content (trees body [])

let string_of tree = string_of_body [tree]



(** parsing *)

(* split *)

let split fields sep str =
  let cons i n result =
    if i = 0 && n = String.length str && n > 0 then str :: result
    else if n > 0 then String.sub str i n :: result
    else if fields then "" :: result
    else result
  in
  let rec explode i result =
    let j = try String.index_from str i sep with Not_found -> -1 in
      if j >= 0 then explode (j + 1) (cons i (j - i) result)
      else List.rev (cons i (String.length str - i) result)
  in explode 0 []


(* parse *)

let err msg = raise (Failure ("Malformed YXML: " ^ msg))
let err_attribute () = err "bad attribute"
let err_element () = err "bad element"
let err_unbalanced name =
  if name = "" then err "unbalanced element"
  else err ("unbalanced element \"" ^ name ^ "\"")

let parse_attrib s =
  try
    let i = String.index s '=' in
    let _ = if i = 0 then err_attribute () in
    let j = i + 1 in
      (String.sub s 0 i, String.sub s j (String.length s - j))
  with Not_found -> err_attribute ()

let parse_body source =

  (* stack operations *)

  let add x = function
    | [] -> assert false
    | (elem, body) :: pending -> (elem, x :: body) :: pending
  in

  let push name atts pending =
    if name = "" then err_element ()
    else ((name, atts), []) :: pending
  in

  let pop = function 
    | [] -> assert false
    | (((name, _) as markup, body) :: pending) ->
        if name = "" then err_unbalanced ""
        else add (XML.Elem (markup, List.rev body)) pending
  in

  (* parse chunks *)

  let chunks = split false char_X source |> List.map (split true char_Y) in

  let parse_chunk = function
    | [""; ""] -> pop
    | ("" :: name :: atts) -> push name (List.map parse_attrib atts)
    | txts -> fold (fun s -> add (XML.Text s)) txts
  in
  match fold parse_chunk chunks [(("", []), [])] with
  | [] -> assert false
  | [(("", _), result)] -> List.rev result
  | ((name, _), _) :: _ -> err_unbalanced name

let parse source =
  match parse_body source with
  | [result] -> result
  | [] -> XML.Text ""
  | _ -> err "multiple results"

end



(*** Source positions ***)

module type Position =
sig
  type t
  val make_id: int -> int -> string -> t
  val make: int -> int -> t
  val none: t
  val id_only: string -> t
  val properties_of: t -> Properties.t
  val markup: t -> Markup.t -> Markup.t
  type report = t * Markup.t
  val reported_text: report -> string -> string
end

module Position: Position =
struct

type t = int * int * string  (*start/end offset counting from 1, id*)

let make_id i j id = (i, j, id)
let make i j = make_id i j ""

let none = make 0 0

let id_only id = make_id 0 0 id


(* properties *)

let valid i = i > 0

let value k i = if valid i then [(k, string_of_int i)] else []

let properties_of (i, j, id) =
  value Coq_Markup.offsetN i @
  value Coq_Markup.end_offsetN j @
  (if id = "" then [] else [(Coq_Markup.idN, id)])

let markup pos = Markup.properties (properties_of pos)


(* reports *)

type report = t * Markup.t

let is_reported (i, j, id) = valid i  (* FIXME id!? *)

let reported_text (pos, m) txt =
  if is_reported pos then YXML.markup (markup pos m) txt else "";

end


(*** Coq syntax ***)

module type Coq_Syntax =
sig
  type span = bool * string * Position.report list
  val parse_spans: string -> string -> span list
end

module Coq_Syntax: Coq_Syntax =
struct

type span = bool * string * Position.report list

(*
let token_markup tok =
  match tok with
  | Coq_lex.Comment -> Coq_Markup.comment
  | Coq_lex.Keyword -> Coq_Markup.keyword
  | Coq_lex.Declaration -> Coq_Markup.declaration
  | Coq_lex.ProofDeclaration -> Coq_Markup.proof_declaration
  | Coq_lex.Qed -> Coq_Markup.qed
  | Coq_lex.String -> Coq_Markup.string
*)

let is_delimiter c = c = '.' || c = '{' || c = '}' || c = '-' || c = '+' || c = '*'

let parse_spans id string =
  let result = ref ([]: span list) in
  let reports = ref ([]: Position.report list) in

  let push r = reports := r :: !reports in
  let flush ok source =
    if source = "" then ()
    else (result := (ok, source, List.rev !reports) :: !result; reports := [])
  in

  let rec parse offset str = () (*
    (* FIXME treatment of UTF-16 surrogates!? *)
    let char_offset i = Ideutils.byte_offset_to_char_offset str i + offset in
    let len = String.length str in

    let make_pos a b = Position.make_id (char_offset a + 1) (char_offset b + 1) id in
    let stamp a b m = push (make_pos a b, m) in
    let next =
      try
       (let n = Coq_lex.delimit_sentence (fun a b tok -> stamp a b (token_markup tok)) str in
        if is_delimiter (str.[n]) then stamp n (n + 1) Coq_Markup.delimiter;
        flush true (String.sub str 0 (n + 1));
        n + 1)
      with Coq_lex.Unterminated -> (flush false str; len)
    in
    if next < len then parse (char_offset next) (String.sub str next (len -
    next)); *)
  in
  parse 0 string;
  List.rev !result

end


(*** Document model ***)

module type Document =
sig
  type id = int
  type version_id = id
  type command_id = id
  type exec_id = id
  val no_id: id
  val new_id: unit -> id
  val parse_id: string -> id
  val print_id: id -> string
  type node_edit =
    Clear |
    Edits of (command_id option * command_id option) list
  type edit = string * node_edit
  type state
  val init_state: state
  val define_command: command_id -> string -> state -> state
  val remove_versions: version_id list -> state -> state
  val update: version_id -> version_id -> edit list -> state ->
    ((command_id * exec_id option) list * (exec_id * Position.report list) list) * state
  val state: unit -> state
  val change_state: (state -> state) -> unit
end

module Document: Document =
struct

(* ML basics *)

let (|>) x f = f x
let (@>) f g x = g (f x)

let rec fold f list y =
  match list with
    [] -> y
  | x :: xs -> fold f xs (f x y)


(* unique identifiers *)

type id = int
type version_id = id
type command_id = id
type exec_id = id

let no_id = 0


let new_id_counter = ref 0

let new_id () =
  let i = !new_id_counter + 1 in
  if (i > 0) then begin
    new_id_counter := i;
    i
  end else raise (Failure "Counter overflow")

let parse_id = int_of_string
let print_id = string_of_int



(** document structure **)

(* linear set of entries *)

type entries = (command_id * exec_id) list

let insert_here id2 (entries: entries) =
  if List.mem_assoc id2 entries then raise (Failure "Dup")
  else (id2, no_id) :: entries

let insert_after hook id2 (entries: entries) =
  match hook with
  | None -> insert_here id2 entries
  | Some id1 ->
      let rec insert list =
        match list with
        | [] -> raise (Failure "Undef")
        | (x, y) :: rest ->
            if x = id1 then (x, y) :: insert_here id2 rest
            else (x, y) :: insert rest
      in insert entries

let remove_here (entries: entries) =
  match entries with
  | [] -> raise (Failure "Undef")
  | [_] -> []
  | _ :: (x, _) :: rest -> (x, no_id) :: rest

let remove_after hook (entries: entries) =
  match hook with
  | None -> remove_here entries
  | Some id1 ->
      let rec remove list =
        match list with
        | [] -> raise (Failure "Undef")
        | (x, y) :: rest ->
            if x = id1 then (x, y) :: remove_here rest
            else (x, y) :: remove rest
      in remove entries


(* named nodes *)

type node = Node of entries
type version = Version of (string * node) list

let empty_node = Node []

let get_node nodes name =
  try List.assoc name nodes
  with Not_found -> empty_node

let default_node name nodes =
  if List.mem_assoc name nodes then nodes
  else (name, empty_node) :: nodes

let update_node name f nodes =
  List.map (function ((name', node) as pair) ->
    if name = name' then (name', f node) else pair) (default_node name nodes)


(* node edits *)

type node_edit =
  Clear |
  Edits of (command_id option * command_id option) list

type edit = string * node_edit

let edit_node edit (Node entries) =
  Node
    (match edit with
    | (hook, Some id2) -> insert_after hook id2 entries
    | (hook, None) -> remove_after hook entries)

let put_node (name, node) (Version nodes) =
  Version ((name, node) :: List.remove_assoc name nodes)


(* version operations *)

let empty_version = Version []

let edit_nodes (name, node_edit) (Version nodes) =
  Version
    (match node_edit with
     | Clear -> update_node name (fun _ -> empty_node) nodes
     | Edits edits -> update_node name (fold edit_node edits) nodes)



(** main state -- document structure and execution process **)

type state = State of (version_id * version) list * (command_id * string) list

let init_state = State ([(no_id, empty_version)], [])


(* document versions *)

let define_version (id: version_id) version (State (versions, commands)) =
  let versions' =
    if List.mem_assoc id versions then raise (Failure "Dup")
    else (id, version) :: versions
  in State (versions', commands)

let the_version (State (versions, _)) (id: version_id) =
  List.assoc id versions

let delete_version (id: version_id) versions =
  if List.mem_assoc id versions then List.remove_assoc id versions
  else raise (Failure "Undef")


(* commands *)

let define_command (id: command_id) text (State (versions, commands)) =
  let commands' =
    if List.mem_assoc id commands then raise (Failure "Dup")
    else (id, text) :: commands
  in State (versions, commands')

let the_command (State (_, commands)) (id: command_id) =
  List.assoc id commands

let remove_versions ids (State (versions, commands) as state) =
  let versions' = fold delete_version ids versions in
  let commands' =
    fold
      (fun (_, Version nodes) -> nodes |>
        fold (fun (_, Node entries) -> entries |>
          fold (fun (id, _) cmds ->
            if List.mem_assoc id cmds then cmds
            else (id, the_command state id) :: cmds)))
      versions' []
  in
  State (versions', commands')



(** document update **)

let rec chop_common (entries0: entries) (entries: entries) =
  match (entries0, entries) with
  | (x :: rest0, y :: rest) when x = y ->
      let (common', rests') = chop_common rest0 rest
      in (x :: common', rests')
  | _ -> ([], (entries0, entries))

let update (old_version_id: version_id) (version_id: version_id) edits state =
  let Version old_nodes as old_version = the_version state old_version_id in
  let Version new_nodes as new_version = fold edit_nodes edits old_version in
  let updated =
    new_nodes |> List.map (fun (name, Node entries) ->
      if List.mem_assoc name edits then
        let Node entries0 = get_node old_nodes name in
        let (common, (rest0, rest)) = chop_common entries0 entries in
        let rest' = List.map (fun (id, _) -> (id, new_id ())) rest in

        let command_execs =
          List.map (fun (id, _) -> (id, None)) rest0 @
          List.map (fun (id, exec_id) -> (id, Some exec_id)) rest' in

        let updated_node =
          match command_execs with
          | [] -> []
          | _ -> [(name, Node (common @ rest'))] in

        let reports =
          List.map (fun (id, exec_id) ->
            (exec_id,
              List.flatten (List.map (fun (_, _, reports) -> reports)
                (Coq_Syntax.parse_spans (print_id id) (the_command state id))))) rest' in

        (command_execs, updated_node, reports)
      else ([], [], []))
  in
  let command_execs = List.flatten (List.map (fun (x, _, _) -> x) updated) in
  let updated_nodes = List.flatten (List.map (fun (_, y, _) -> y) updated) in
  let reports = List.flatten (List.map (fun (_, _, z) -> z) updated) in
  let state' =
    define_version version_id (fold put_node updated_nodes new_version) state in
  ((command_execs, reports), state')



(** global state **)

let global_state = ref init_state

let state () = !global_state
let change_state f = global_state := f !global_state

end


(*** prover process with protocol loop ***)

(* odd emulations *)

let quote s = "\"" ^ s ^ "\""


(* protocol commands *)

let commands = ref ([]: (string * (string list -> unit)) list)

let protocol_command name cmd = commands := (name, cmd) :: !commands

let run_command name args =
  let cmd =
    try List.assoc name !commands
    with Not_found -> raise (Failure ("Undefined Coq process command " ^ quote name))
  in
    try cmd args
    with e -> raise (Failure
      ("Coq process protocol failure: " ^ quote name ^ "\n" ^ Printexc.to_string e))


(* message channels *)

type position = Position.t

let out_channel = ref stdout

let chunk s = string_of_int (String.length s) ^ "\n" ^ s

let message ch props body =
  let header = YXML.string_of (XML.Elem ((ch, props), [])) in
  output_string !out_channel (chunk header);
  output_string !out_channel (chunk body);
  flush !out_channel

let standard_message ch pos body =
  if body <> "" then
    message ch (Position.properties_of pos) body

let init_message = message "A" []
let status = standard_message "B" Position.none
let report = standard_message "C"
let writeln = standard_message "D" Position.none
let tracing = standard_message "E" Position.none
let warning = standard_message "F" Position.none
let error_msg = standard_message "G" Position.none
let protocol_message = message "H"


(* protocol loop *)

let in_channel = ref stdin

let read_chunk len =
  let n =
    try int_of_string len
    with Failure _ -> raise (Failure ("Coq process: malformed chunk header " ^ quote len))
  in
  let chunk = String.make n '\000' in
  really_input !in_channel chunk 0 n;
  chunk

let read_command () =
  try Some (List.map read_chunk (YXML.split true ',' (input_line !in_channel)))
  with End_of_file -> None

let rec protocol_loop () =
  match read_command () with
    None -> ()
  | Some [] -> error_msg "Coq process: no input"
  | Some (name :: args) ->
      (try run_command name args with e -> error_msg (Printexc.to_string e));
      protocol_loop ()


(* main entry point *)

let main () =
  (*indicate process startup and change of line-discipline*)
  output_string stderr "\002";
  flush stderr;

  (*system channel rendezvous*)
  let args = List.tl (Array.to_list Sys.argv) in
  let args =
    let rec aux acc = function
      | "-channel-fifo" :: fin :: fout :: args ->
            in_channel := open_in_bin fin;
            out_channel := open_out_bin fout;
            List.rev acc @ args
      | "-channel-socket" :: host :: port :: args ->
            let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
            let addr = (Unix.gethostbyname host).Unix.h_addr_list.(0) in
            Unix.connect s (Unix.ADDR_INET (addr, int_of_string port));
            in_channel := Unix.in_channel_of_descr s;
            out_channel := Unix.out_channel_of_descr s;
            List.rev acc @ args
      | x :: args -> aux (x :: acc) args
      | [] -> prerr_endline "No -channel-fifo or -channel-socket option to pide"; 
              exit 1
    in
      aux [] args in

  (*real startup*)
  Coqtop.init_toplevel args;
  init_message (Printf.sprintf
    "Welcome to Coq %s (%s)\n" Coq_config.version Coq_config.date);
  protocol_message Coq_Markup.ready "";

  (*finally the main loop*)
  protocol_loop ()
;;

(* concrete commands *)

let () =
  protocol_command "echo" (fun args -> List.iter writeln args);

  protocol_command "Coq.spans"
    (function [str] ->
      report Position.none
        (YXML.implode
          (List.map (fun (_, source, reports) ->
            YXML.implode (source :: List.map (fun r -> Position.reported_text r "") reports))
            (Coq_Syntax.parse_spans "" str)))
  | _ -> assert false);

  protocol_command "Document.define_command"
    (function [id; name; text] ->
      Document.change_state 
        (Document.define_command (Document.parse_id id) text)
    | _ -> assert false);

  protocol_command "Document.discontinue_execution" (fun _ -> ());

  protocol_command "Document.cancel_execution" (fun _ -> ());

  protocol_command "Document.update"
    (function [old_id_string; new_id_string; edits_yxml] ->
      Document.change_state (fun state ->
      let old_id = Document.parse_id old_id_string in
      let new_id = Document.parse_id new_id_string in
      let edits =
       (let string = XML.Decode.string in
        let int = XML.Decode.int in
        let pair = XML.Decode.pair in
        let list = XML.Decode.list in
        let option = XML.Decode.option in
        let variant = XML.Decode.variant in
        list (pair string
          (variant
           [(function ([], []) -> Document.Clear | _ -> assert false);
            (function ([], a) ->
               Document.Edits (list (pair (option int) (option int)) a)
             | _ -> assert false);
            (function ([], a) -> Document.Edits [] | _ -> assert false);
            (function ([a], []) -> Document.Edits [] | _ -> assert false);
            (function (a, []) -> Document.Edits [] | _ -> assert false)]))) 
          (YXML.parse_body edits_yxml)
      in
      let ((assignment, reports), state') = Document.update old_id new_id edits state in

      let _ =
        protocol_message Coq_Markup.assign_execs
          (YXML.string_of_body
            ((let int = XML.Encode.int in
              let pair = XML.Encode.pair in
              let list = XML.Encode.list in
              let option = XML.Encode.option in
              pair int (list (pair int (option int)))) (new_id, assignment))) in

      let _ = List.map (fun (exec_id, rs) ->
        report (Position.id_only (Document.print_id exec_id))
          (YXML.implode (List.map (fun r -> Position.reported_text r "") rs))) reports
      in state')
    | _ -> assert false);

  protocol_command "Document.remove_versions"
    (function [versions_yxml] ->
      Document.change_state (fun state ->
      let versions =
       (let int = XML.Decode.int in
        let list = XML.Decode.list in
        list int) (YXML.parse_body versions_yxml)
      in
      let state' = Document.remove_versions versions state in
      let _ = protocol_message Coq_Markup.removed_versions versions_yxml
      in state')
    | _ -> assert false)

let () = main ()
