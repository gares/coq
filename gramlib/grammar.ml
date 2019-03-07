(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)
open Gramlib
open Gramext
open Format

type ('a, 'b) eq = Refl : ('a, 'a) eq

(* Functorial interface *)

module type GLexerType = sig
  type te
  val loc_of : te -> Loc.t
  val loc_before : te -> Loc.t
  val pos_of : te -> int
  val lexer : te Plexing.lexer
end

module type S =
  sig
    type te
    type parsable
    val parsable : te Plexing.lexer_func -> char Stream.t -> parsable
    val tokens : string -> (string option * int) list
    module Entry :
      sig
        type 'a e
        val create : string -> 'a e
        val parse : 'a e -> parsable -> 'a
        val name : 'a e -> string
        val of_lookahead : string -> (te Stream.t -> unit) -> unit e
        type 'a parser_t =
          te option -> te Stream.t -> 'a * te option
        val of_parser : string -> 'a parser_t -> 'a e
        val parse_token_stream : 'a e -> te Stream.t -> 'a
        val print : Format.formatter -> 'a e -> unit
      end
    type ('self, 'a) ty_symbol
    type ('self, 'f, 'r) ty_rule
    type 'a ty_production
    val s_nterm : 'a Entry.e -> ('self, 'a) ty_symbol
    val s_nterml : 'a Entry.e -> string -> ('self, 'a) ty_symbol
    val s_list0 : ('self, 'a) ty_symbol -> ('self, 'a list) ty_symbol
    val s_list0sep :
      ('self, 'a) ty_symbol -> ('self, 'b) ty_symbol -> bool ->
        ('self, 'a list) ty_symbol
    val s_list1 : ('self, 'a) ty_symbol -> ('self, 'a list) ty_symbol
    val s_list1sep :
      ('self, 'a) ty_symbol -> ('self, 'b) ty_symbol -> bool ->
        ('self, 'a list) ty_symbol
    val s_opt : ('self, 'a) ty_symbol -> ('self, 'a option) ty_symbol
    val s_self : ('self, 'self) ty_symbol
    val s_next : ('self, 'self) ty_symbol
    val s_token : Plexing.pattern -> ('self, string) ty_symbol
    val s_rules : warning:(string -> unit) option -> 'a ty_production list -> ('self, 'a) ty_symbol
    val r_stop : ('self, 'r, 'r) ty_rule
    val r_next :
      ('self, 'a, 'r) ty_rule -> ('self, 'b) ty_symbol ->
        ('self, 'b -> 'a, 'r) ty_rule
    val production : ('a, 'f, Loc.t -> 'a) ty_rule * 'f -> 'a ty_production
    module Unsafe :
      sig
        val clear_entry : 'a Entry.e -> unit
      end
    val safe_extend : warning:(string -> unit) option ->
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option * 'a ty_production list)
          list ->
        unit
    val safe_delete_rule : 'a Entry.e -> ('a, 'r, 'f) ty_rule -> unit
  end

(* Implementation *)

module GMake (L : GLexerType) =
struct

type te = L.te

type 'a parser_t =
  L.te option -> L.te Stream.t -> 'a * L.te option (* last token parsed for this entry *)

type grammar =
  { gtokens : (Plexing.pattern, int ref) Hashtbl.t;
    glexer : L.te Plexing.lexer }

let egram =
  {gtokens = Hashtbl.create 301; glexer = L.lexer }

let tokens con =
  let list = ref [] in
  Hashtbl.iter
    (fun (p_con, p_prm) c -> if p_con = con then list := (p_prm, !c) :: !list)
    egram.gtokens;
  !list

type 'a ty_entry = {
  ename : string;
  mutable estart : int -> 'a parser_t;
  mutable econtinue : levn:int -> 'a -> 'a parser_t;
  mutable edesc : 'a ty_desc;
}

and 'a ty_desc =
| Dlevels of 'a ty_level list
| Dparser of 'a parser_t

and 'a ty_level = {
  assoc : g_assoc;
  lname : string option;
  lsuffix : ('a, 'a -> Loc.t -> 'a) ty_tree;
  lprefix : ('a, Loc.t -> 'a) ty_tree;
}

and ('self, 'a) ty_symbol =
| Stoken : Plexing.pattern -> ('self, string) ty_symbol
| Slist1 : ('self, 'a) ty_symbol -> ('self, 'a list) ty_symbol
| Slist1sep : ('self, 'a) ty_symbol * ('self, _) ty_symbol * bool -> ('self, 'a list) ty_symbol
| Slist0 : ('self, 'a) ty_symbol -> ('self, 'a list) ty_symbol
| Slist0sep : ('self, 'a) ty_symbol * ('self, _) ty_symbol * bool -> ('self, 'a list) ty_symbol
| Sopt : ('self, 'a) ty_symbol -> ('self, 'a option) ty_symbol
| Sself : ('self, 'self) ty_symbol
| Snext : ('self, 'self) ty_symbol
| Snterm : 'a ty_entry -> ('self, 'a) ty_symbol
| Snterml : 'a ty_entry * string -> ('self, 'a) ty_symbol
| Stree : ('self, Loc.t -> 'a) ty_tree -> ('self, 'a) ty_symbol

and ('self, _, 'r) ty_rule =
| TStop : ('self, 'r, 'r) ty_rule
| TNext : ('self, 'a, 'r) ty_rule * ('self, 'b) ty_symbol -> ('self, 'b -> 'a, 'r) ty_rule

and ('self, 'a) ty_tree =
| Node : ('self, 'b, 'a) ty_node -> ('self, 'a) ty_tree
| LocAct : 'k * 'k list -> ('self, 'k) ty_tree
| DeadEnd : ('self, 'k) ty_tree

and ('self, 'a, 'r) ty_node = {
  node : ('self, 'a) ty_symbol;
  son : ('self, 'a -> 'r) ty_tree;
  brother : ('self, 'r) ty_tree;
}

type 'a ty_production =
| TProd : ('a, 'act, Loc.t -> 'a) ty_rule * 'act -> 'a ty_production

let rec derive_eps : type s a. (s, a) ty_symbol -> bool =
  function
    Slist0 _ -> true
  | Slist0sep (_, _, _) -> true
  | Sopt _ -> true
  | Stree t -> tree_derive_eps t
  | Slist1 _ -> false
  | Slist1sep (_, _, _) -> false
  | Snterm _ | Snterml (_, _) -> false
  | Snext -> false
  | Sself -> false
  | Stoken _ -> false
and tree_derive_eps : type s a. (s, a) ty_tree -> bool =
  function
    LocAct (_, _) -> true
  | Node {node = s; brother = bro; son = son} ->
      derive_eps s && tree_derive_eps son || tree_derive_eps bro
  | DeadEnd -> false

(** FIXME: find a way to do that type-safely *)
let eq_entry : type a1 a2. a1 ty_entry -> a2 ty_entry -> (a1, a2) eq option = fun e1 e2 ->
  if (Obj.magic e1) == (Obj.magic e2) then Some (Obj.magic Refl)
  else None

let rec eq_symbol : type s a1 a2. (s, a1) ty_symbol -> (s, a2) ty_symbol -> (a1, a2) eq option = fun s1 s2 ->
  match s1, s2 with
    Snterm e1, Snterm e2 -> eq_entry e1 e2
  | Snterml (e1, l1), Snterml (e2, l2) ->
    if String.equal l1 l2 then eq_entry e1 e2 else None
  | Slist0 s1, Slist0 s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Slist0sep (s1, sep1, b1), Slist0sep (s2, sep2, b2) ->
    if b1 = b2 then match eq_symbol s1 s2 with
    | None -> None
    | Some Refl ->
      match eq_symbol sep1 sep2 with
      | None -> None
      | Some Refl -> Some Refl
    else None
  | Slist1 s1, Slist1 s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Slist1sep (s1, sep1, b1), Slist1sep (s2, sep2, b2) ->
    if b1 = b2 then match eq_symbol s1 s2 with
    | None -> None
    | Some Refl ->
      match eq_symbol sep1 sep2 with
      | None -> None
      | Some Refl -> Some Refl
    else None
  | Sopt s1, Sopt s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Stree _, Stree _ -> None
  | Sself, Sself -> Some Refl
  | Snext, Snext -> Some Refl
  | Stoken p1, Stoken p2 -> if p1 = p2 then Some Refl else None
  | _ -> None

let is_before : type s1 s2 a1 a2. (s1, a1) ty_symbol -> (s2, a2) ty_symbol -> bool = fun s1 s2 ->
  match s1, s2 with
    Stoken ("ANY", _), _ -> false
  | _, Stoken ("ANY", _) -> true
  | Stoken (_, Some _), Stoken (_, None) -> true
  | Stoken _, Stoken _ -> false
  | Stoken _, _ -> true
  | _ -> false

(** Ancilliary datatypes *)

type ('self, _) ty_symbols =
| TNil : ('self, unit) ty_symbols
| TCns : ('self, 'a) ty_symbol * ('self, 'b) ty_symbols -> ('self, 'a * 'b) ty_symbols

(** ('i, 'p, 'f, 'r) rel_prod0 ~
  ∃ α₁ ... αₙ.
    p ≡ αₙ * ... α₁ * 'i ∧
    f ≡ α₁ -> ... -> αₙ -> 'r
*)
type ('i, _, 'f, _) rel_prod0 =
| Rel0 : ('i, 'i, 'f, 'f) rel_prod0
| RelS : ('i, 'p, 'f, 'a -> 'r) rel_prod0 -> ('i, 'a * 'p, 'f, 'r) rel_prod0

type ('p, 'k, 'r) rel_prod = (unit, 'p, 'k, 'r) rel_prod0

type ('s, 'i, 'k, 'r) any_symbols =
| AnyS : ('s, 'p) ty_symbols * ('i, 'p, 'k, 'r) rel_prod0 -> ('s, 'i, 'k, 'r) any_symbols

(** FIXME *)
let rec symbols : type s p k r. (s, p) ty_symbols -> (s, k, r) ty_rule -> (s, unit, k, r) any_symbols =
  fun accu r -> match r with
  | TStop -> AnyS (Obj.magic accu, Rel0)
  | TNext (r, s) ->
    let AnyS (r, pf) = symbols (TCns (s, accu)) r in
    AnyS (Obj.magic r, RelS (Obj.magic pf))

let get_symbols : type s k r. (s, k, r) ty_rule -> (s, unit, k, r) any_symbols =
  fun r -> symbols TNil r

let insert_tree (type s p k a) ~warning entry_name (gsymbols : (s, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, a) ty_tree) =
  let rec insert : type p f k. (s, p) ty_symbols -> (p, k, f) rel_prod -> (s, f) ty_tree -> k -> (s, f) ty_tree  =
    fun symbols pf tree action ->
    match symbols, pf with
      TCns (s, sl), RelS pf -> insert_in_tree s sl pf tree action
    | TNil, Rel0 ->
        match tree with
          Node {node = s; son = son; brother = bro} ->
            Node {node = s; son = son; brother = insert TNil Rel0 bro action}
        | LocAct (old_action, action_list) ->
          begin match warning with
            | None -> ()
            | Some warn_fn ->
              let msg =
                "<W> Grammar extension: " ^
                (if entry_name <> "" then "" else "in ["^entry_name^"%s], ") ^
                "some rule has been masked" in
              warn_fn msg
          end;
          LocAct (action, old_action :: action_list)
        | DeadEnd -> LocAct (action, [])
  and insert_in_tree : type a p f k. (s, a) ty_symbol -> (s, p) ty_symbols -> (p, k, a -> f) rel_prod -> (s, f) ty_tree -> k -> (s, f) ty_tree =
    fun s sl pf tree action ->
    match try_insert s sl pf tree action with
      Some t -> t
    | None -> Node {node = s; son = insert sl pf DeadEnd action; brother = tree}
  and try_insert : type a p f k. (s, a) ty_symbol -> (s, p) ty_symbols -> (p, k, a -> f) rel_prod -> (s, f) ty_tree -> k -> (s, f) ty_tree option =
    fun s sl pf tree action ->
    match tree with
      Node {node = s1; son = son; brother = bro} ->
        begin match eq_symbol s s1 with
        | Some Refl ->
          let t = Node {node = s1; son = insert sl pf son action; brother = bro} in
          Some t
        | None ->
        if is_before s1 s || derive_eps s && not (derive_eps s1) then
          let bro =
            match try_insert s sl pf bro action with
              Some bro -> bro
            | None -> Node {node = s; son = insert sl pf DeadEnd action; brother = bro}
          in
          let t = Node {node = s1; son = son; brother = bro} in Some t
        else
          begin match try_insert s sl pf bro action with
            Some bro ->
              let t = Node {node = s1; son = son; brother = bro} in Some t
          | None -> None
          end
        end
    | LocAct (_, _) | DeadEnd -> None
  in
  insert gsymbols pf tree action

let srules (type self a) ~warning (rl : a ty_production list) =
  let t =
    List.fold_left
      (fun tree (TProd (symbols, action)) ->
        let AnyS (symbols, pf) = get_symbols symbols in
        insert_tree ~warning "" symbols pf action tree)
      DeadEnd rl
  in
  (* FIXME: use an universal self type to ensure well-typedness *)
  (Obj.magic (Stree t) : (self, a) ty_symbol)

let is_level_labelled n lev =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

let insert_level (type s p k) ~warning entry_name (symbols : (s, p) ty_symbols) (pf : (p, k, Loc.t -> s) rel_prod) (action : k) (slev : s ty_level) : s ty_level =
  match symbols with
  | TCns (Sself, symbols) ->
      let RelS pf = pf in
      {assoc = slev.assoc; lname = slev.lname;
       lsuffix = insert_tree ~warning entry_name symbols pf action slev.lsuffix;
       lprefix = slev.lprefix}
  | _ ->
      {assoc = slev.assoc; lname = slev.lname; lsuffix = slev.lsuffix;
       lprefix = insert_tree ~warning entry_name symbols pf action slev.lprefix}

let empty_lev lname assoc =
  let assoc =
    match assoc with
      Some a -> a
    | None -> LeftA
  in
  {assoc = assoc; lname = lname; lsuffix = DeadEnd; lprefix = DeadEnd}

let change_lev ~warning lev n lname assoc =
  let a =
    match assoc with
      None -> lev.assoc
    | Some a ->
      if a <> lev.assoc then
        begin
          match warning with
          | None -> ()
          | Some warn_fn ->
            warn_fn ("<W> Changing associativity of level \""^n^"\"")
        end;
        a
  in
  begin match lname with
    Some n ->
      if lname <> lev.lname then
        begin match warning with
          | None -> ()
          | Some warn_fn ->
            warn_fn ("<W> Level label \""^n^"\" ignored")
        end;
  | None -> ()
  end;
  {assoc = a; lname = lev.lname; lsuffix = lev.lsuffix; lprefix = lev.lprefix}

let get_level ~warning entry position levs =
  match position with
    Some First -> [], empty_lev, levs
  | Some Last -> levs, empty_lev, []
  | Some (Level n) ->
      let rec get =
        function
          [] ->
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if is_level_labelled n lev then [], change_lev ~warning lev n, levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | Some (Before n) ->
      let rec get =
        function
          [] ->
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if is_level_labelled n lev then [], empty_lev, lev :: levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | Some (After n) ->
      let rec get =
        function
          [] ->
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if is_level_labelled n lev then [lev], empty_lev, levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | None ->
      match levs with
        lev :: levs -> [], change_lev ~warning lev "<top>", levs
      | [] -> [], empty_lev, []

let change_to_self0 (type s) (type a) (entry : s ty_entry) : (s, a) ty_symbol -> (s, a) ty_symbol =
  function
  | Snterm e ->
      begin match eq_entry e entry with
      | None -> Snterm e
      | Some Refl -> Sself
      end
  | x -> x

let rec change_to_self : type s a r. s ty_entry -> (s, a, r) ty_rule -> (s, a, r) ty_rule = fun e r -> match r with
| TStop -> TStop
| TNext (r, t) -> TNext (change_to_self e r, change_to_self0 e t)

let insert_tokens gram symbols =
  let rec insert : type s a. (s, a) ty_symbol -> unit =
    function
    | Slist0 s -> insert s
    | Slist1 s -> insert s
    | Slist0sep (s, t, _) -> insert s; insert t
    | Slist1sep (s, t, _) -> insert s; insert t
    | Sopt s -> insert s
    | Stree t -> tinsert t
    | Stoken ("ANY", _) -> ()
    | Stoken tok ->
        gram.glexer.Plexing.tok_using tok;
        let r =
          try Hashtbl.find gram.gtokens tok with
            Not_found -> let r = ref 0 in Hashtbl.add gram.gtokens tok r; r
        in
        incr r
    | Snterm _ | Snterml (_, _) -> ()
    | Snext -> ()
    | Sself -> ()
  and tinsert : type s a. (s, a) ty_tree -> unit =
    function
      Node {node = s; brother = bro; son = son} ->
        insert s; tinsert bro; tinsert son
    | LocAct (_, _) | DeadEnd -> ()
  and linsert : type s p. (s, p) ty_symbols -> unit = function
  | TNil -> ()
  | TCns (s, r) -> insert s; linsert r
  in
  linsert symbols

let levels_of_rules ~warning entry position rules =
  let elev =
    match entry.edesc with
      Dlevels elev -> elev
    | Dparser _ ->
        eprintf "Error: entry not extensible: \"%s\"\n" entry.ename;
        flush stderr;
        failwith "Grammar.extend"
  in
  match rules with
  | [] -> elev
  | _ ->
    let (levs1, make_lev, levs2) = get_level ~warning entry position elev in
    let (levs, _) =
      List.fold_left
        (fun (levs, make_lev) (lname, assoc, level) ->
           let lev = make_lev lname assoc in
           let lev =
             List.fold_left
               (fun lev (TProd (symbols, action)) ->
                  let symbols = change_to_self entry symbols in
                  let AnyS (symbols, pf) = get_symbols symbols in
                  insert_tokens egram symbols;
                  insert_level ~warning entry.ename symbols pf action lev)
               lev level
           in
           lev :: levs, empty_lev)
        ([], make_lev) rules
    in
    levs1 @ List.rev levs @ levs2

let logically_eq_symbols entry =
  let rec eq_symbols : type s1 s2 a1 a2. (s1, a1) ty_symbol -> (s2, a2) ty_symbol -> bool = fun s1 s2 ->
    match s1, s2 with
      Snterm e1, Snterm e2 -> e1.ename = e2.ename
    | Snterm e1, Sself -> e1.ename = entry.ename
    | Sself, Snterm e2 -> entry.ename = e2.ename
    | Snterml (e1, l1), Snterml (e2, l2) -> e1.ename = e2.ename && l1 = l2
    | Slist0 s1, Slist0 s2 -> eq_symbols s1 s2
    | Slist0sep (s1, sep1, b1), Slist0sep (s2, sep2, b2) ->
        eq_symbols s1 s2 && eq_symbols sep1 sep2 && b1 = b2
    | Slist1 s1, Slist1 s2 -> eq_symbols s1 s2
    | Slist1sep (s1, sep1, b1), Slist1sep (s2, sep2, b2) ->
        eq_symbols s1 s2 && eq_symbols sep1 sep2 && b1 = b2
    | Sopt s1, Sopt s2 -> eq_symbols s1 s2
    | Stree t1, Stree t2 -> eq_trees t1 t2
    | Stoken p1, Stoken p2 -> p1 = p2
    | Sself, Sself -> true
    | Snext, Snext -> true
    | _ -> false
  and eq_trees : type s1 s2 a1 a2. (s1, a1) ty_tree -> (s2, a2) ty_tree -> bool = fun t1 t2 ->
    match t1, t2 with
      Node n1, Node n2 ->
        eq_symbols n1.node n2.node && eq_trees n1.son n2.son &&
        eq_trees n1.brother n2.brother
    | (LocAct (_, _) | DeadEnd), (LocAct (_, _) | DeadEnd) -> true
    | _ -> false
  in
  eq_symbols

(* [delete_rule_in_tree] returns
     [Some (dsl, t)] if success
        [dsl] =
           Some (list of deleted nodes) if branch deleted
           None if action replaced by previous version of action
        [t] = remaining tree
     [None] if failure *)

type 's ex_symbols =
| ExS : ('s, 'p) ty_symbols -> 's ex_symbols

let delete_rule_in_tree entry =
  let rec delete_in_tree :
    type s p r. (s, p) ty_symbols -> (s, r) ty_tree -> (s ex_symbols option * (s, r) ty_tree) option =
    fun symbols tree ->
    match symbols, tree with
    | TCns (s, sl), Node n ->
        if logically_eq_symbols entry s n.node then delete_son sl n
        else
          begin match delete_in_tree symbols n.brother with
            Some (dsl, t) ->
              Some (dsl, Node {node = n.node; son = n.son; brother = t})
          | None -> None
          end
    | TCns (s, sl), _ -> None
    | TNil, Node n ->
        begin match delete_in_tree TNil n.brother with
          Some (dsl, t) ->
            Some (dsl, Node {node = n.node; son = n.son; brother = t})
        | None -> None
        end
    | TNil, DeadEnd -> None
    | TNil, LocAct (_, []) -> Some (Some (ExS TNil), DeadEnd)
    | TNil, LocAct (_, action :: list) -> Some (None, LocAct (action, list))
  and delete_son :
    type s p a r. (s, p) ty_symbols -> (s, a, r) ty_node -> (s ex_symbols option * (s, r) ty_tree) option =
    fun sl n ->
    match delete_in_tree sl n.son with
      Some (Some (ExS dsl), DeadEnd) -> Some (Some (ExS (TCns (n.node, dsl))), n.brother)
    | Some (Some (ExS dsl), t) ->
        let t = Node {node = n.node; son = t; brother = n.brother} in
        Some (Some (ExS (TCns (n.node, dsl))), t)
    | Some (None, t) ->
        let t = Node {node = n.node; son = t; brother = n.brother} in
        Some (None, t)
    | None -> None
  in
  delete_in_tree

let rec decr_keyw_use : type s a. _ -> (s, a) ty_symbol -> unit = fun gram ->
  function
    Stoken tok ->
      let r = Hashtbl.find gram.gtokens tok in
      decr r;
      if !r == 0 then
        begin
          Hashtbl.remove gram.gtokens tok;
          gram.glexer.Plexing.tok_removing tok
        end
  | Slist0 s -> decr_keyw_use gram s
  | Slist1 s -> decr_keyw_use gram s
  | Slist0sep (s1, s2, _) -> decr_keyw_use gram s1; decr_keyw_use gram s2
  | Slist1sep (s1, s2, _) -> decr_keyw_use gram s1; decr_keyw_use gram s2
  | Sopt s -> decr_keyw_use gram s
  | Stree t -> decr_keyw_use_in_tree gram t
  | Sself -> ()
  | Snext -> ()
  | Snterm _ | Snterml (_, _) -> ()
and decr_keyw_use_in_tree : type s a. _ -> (s, a) ty_tree -> unit = fun gram ->
  function
    DeadEnd | LocAct (_, _) -> ()
  | Node n ->
      decr_keyw_use gram n.node;
      decr_keyw_use_in_tree gram n.son;
      decr_keyw_use_in_tree gram n.brother
and decr_keyw_use_in_list : type s p. _ -> (s, p) ty_symbols -> unit = fun gram ->
  function
  | TNil -> ()
  | TCns (s, l) -> decr_keyw_use gram s; decr_keyw_use_in_list gram l

let rec delete_rule_in_suffix entry symbols =
  function
    lev :: levs ->
      begin match delete_rule_in_tree entry symbols lev.lsuffix with
        Some (dsl, t) ->
          begin match dsl with
            Some (ExS dsl) -> decr_keyw_use_in_list egram dsl
          | None -> ()
          end;
          begin match t with
            DeadEnd when lev.lprefix == DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = t;
                 lprefix = lev.lprefix}
              in
              lev :: levs
          end
      | None ->
          let levs = delete_rule_in_suffix entry symbols levs in lev :: levs
      end
  | [] -> raise Not_found

let rec delete_rule_in_prefix entry symbols =
  function
    lev :: levs ->
      begin match delete_rule_in_tree entry symbols lev.lprefix with
        Some (dsl, t) ->
          begin match dsl with
            Some (ExS dsl) -> decr_keyw_use_in_list egram dsl
          | None -> ()
          end;
          begin match t with
            DeadEnd when lev.lsuffix == DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = lev.lsuffix;
                 lprefix = t}
              in
              lev :: levs
          end
      | None ->
          let levs = delete_rule_in_prefix entry symbols levs in lev :: levs
      end
  | [] -> raise Not_found

let delete_rule_in_level_list (type s p) (entry : s ty_entry) (symbols : (s, p) ty_symbols) levs =
  match symbols with
    TCns (Sself, symbols) -> delete_rule_in_suffix entry symbols levs
  | TCns (Snterm e, symbols') ->
    begin match eq_entry e entry with
    | None -> delete_rule_in_prefix entry symbols levs
    | Some Refl ->
      delete_rule_in_suffix entry symbols' levs
    end
  | _ -> delete_rule_in_prefix entry symbols levs

let rec flatten_tree : type s a. (s, a) ty_tree -> s ex_symbols list =
  function
    DeadEnd -> []
  | LocAct (_, _) -> [ExS TNil]
  | Node {node = n; brother = b; son = s} ->
      List.map (fun (ExS l) -> ExS (TCns (n, l))) (flatten_tree s) @ flatten_tree b

let utf8_print = ref true

let utf8_string_escaped s =
  let b = Buffer.create (String.length s) in
  let rec loop i =
    if i = String.length s then Buffer.contents b
    else
      begin
        begin match s.[i] with
          '"' -> Buffer.add_string b "\\\""
        | '\\' -> Buffer.add_string b "\\\\"
        | '\n' -> Buffer.add_string b "\\n"
        | '\t' -> Buffer.add_string b "\\t"
        | '\r' -> Buffer.add_string b "\\r"
        | '\b' -> Buffer.add_string b "\\b"
        | c -> Buffer.add_char b c
        end;
        loop (i + 1)
      end
  in
  loop 0

let string_escaped s =
  if !utf8_print then utf8_string_escaped s else String.escaped s

let print_str ppf s = fprintf ppf "\"%s\"" (string_escaped s)

let rec print_symbol : type s r. formatter -> (s, r) ty_symbol -> unit =
  fun ppf ->
  function
  | Slist0 s -> fprintf ppf "LIST0 %a" print_symbol1 s
  | Slist0sep (s, t, osep) ->
      fprintf ppf "LIST0 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Slist1 s -> fprintf ppf "LIST1 %a" print_symbol1 s
  | Slist1sep (s, t, osep) ->
      fprintf ppf "LIST1 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Sopt s -> fprintf ppf "OPT %a" print_symbol1 s
  | Stoken (con, Some prm) when con <> "" ->
      fprintf ppf "%s@ %a" con print_str prm
  | Snterml (e, l) ->
      fprintf ppf "%s%s@ LEVEL@ %a" e.ename ""
        print_str l
  | s -> print_symbol1 ppf s
and print_symbol1 : type s r. formatter -> (s, r) ty_symbol -> unit =
  fun ppf ->
  function
  | Snterm e -> fprintf ppf "%s%s" e.ename ""
  | Sself -> pp_print_string ppf "SELF"
  | Snext -> pp_print_string ppf "NEXT"
  | Stoken ("", Some s) -> print_str ppf s
  | Stoken (con, None) -> pp_print_string ppf con
  | Stree t -> print_level ppf pp_print_space (flatten_tree t)
  | s ->
      fprintf ppf "(%a)" print_symbol s
and print_rule : type s p. formatter -> (s, p) ty_symbols -> unit =
  fun ppf symbols ->
  fprintf ppf "@[<hov 0>";
  let rec fold : type s p. _ -> (s, p) ty_symbols -> unit =
    fun sep symbols -> match symbols with
    | TNil -> ()
    | TCns (symbol, symbols) ->
      fprintf ppf "%t%a" sep print_symbol symbol;
      fold (fun ppf -> fprintf ppf ";@ ") symbols
  in
  let () = fold (fun ppf -> ()) symbols in
  fprintf ppf "@]"
and print_level : type s. _ -> _ -> s ex_symbols list -> _ =
  fun ppf pp_print_space rules ->
  fprintf ppf "@[<hov 0>[ ";
  let _ =
    List.fold_left
      (fun sep (ExS rule) ->
         fprintf ppf "%t%a" sep print_rule rule;
         fun ppf -> fprintf ppf "%a| " pp_print_space ())
      (fun ppf -> ()) rules
  in
  fprintf ppf " ]@]"

let print_levels ppf elev =
  let _ =
    List.fold_left
      (fun sep lev ->
         let rules =
           List.map (fun (ExS t) -> ExS (TCns (Sself, t))) (flatten_tree lev.lsuffix) @
           flatten_tree lev.lprefix
         in
         fprintf ppf "%t@[<hov 2>" sep;
         begin match lev.lname with
           Some n -> fprintf ppf "%a@;<1 2>" print_str n
         | None -> ()
         end;
         begin match lev.assoc with
           LeftA -> fprintf ppf "LEFTA"
         | RightA -> fprintf ppf "RIGHTA"
         | NonA -> fprintf ppf "NONA"
         end;
         fprintf ppf "@]@;<1 2>";
         print_level ppf pp_force_newline rules;
         fun ppf -> fprintf ppf "@,| ")
      (fun ppf -> ()) elev
  in
  ()

let print_entry ppf e =
  fprintf ppf "@[<v 0>[ ";
  begin match e.edesc with
    Dlevels elev -> print_levels ppf elev
  | Dparser _ -> fprintf ppf "<parser>"
  end;
  fprintf ppf " ]@]"

let loc_of_token_interval first_token last_token =
  match first_token, last_token with
  | None, Some _ -> assert false
  | Some _, None -> assert false
  | None, None -> Ploc.dummy
  | Some first_token, Some last_token ->
      let bp = L.loc_of first_token in
      let ep = L.loc_of last_token in
      Loc.merge bp ep

let name_of_symbol : type s a. s ty_entry -> (s, a) ty_symbol -> string =
  fun entry ->
  function
    Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml (e, l) -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself -> "[" ^ entry.ename ^ "]"
  | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> egram.glexer.Plexing.tok_text tok
  | _ -> "???"

type ('r, 'f) tok_list =
| TokNil : ('f, 'f) tok_list
| TokCns : ('r, 'f) tok_list -> (string -> 'r, 'f) tok_list

type ('s, 'f) tok_tree = TokTree : ('s, string -> 'r) ty_tree * ('r, 'f) tok_list -> ('s, 'f) tok_tree

let rec get_token_list : type s r f.
  s ty_entry -> _ -> _ -> _ -> (r, f) tok_list -> (s, string -> r) ty_tree -> (_ * _ * _ * (s, f) tok_tree) option =
  fun entry first_tok rev_tokl last_tok pf tree ->
  match tree with
    Node {node = Stoken tok; son = son; brother = DeadEnd} ->
      get_token_list entry first_tok (last_tok :: rev_tokl) tok (TokCns pf) son
  | _ -> if rev_tokl = [] then None else Some (first_tok, rev_tokl, last_tok, TokTree (tree, pf))

let rec name_of_symbol_failed : type s a. s ty_entry -> (s, a) ty_symbol -> _ =
  fun entry ->
  function
  | Slist0 s -> name_of_symbol_failed entry s
  | Slist0sep (s, _, _) -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep (s, _, _) -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | s -> name_of_symbol entry s
and name_of_tree_failed : type s a. s ty_entry -> (s, a) ty_tree -> _ =
  fun entry ->
  function
    Node {node = s; brother = bro; son = son} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry tok [] tok TokNil son
        | _ -> None
      in
      begin match tokl with
        None ->
          let txt = name_of_symbol_failed entry s in
          let txt =
            match s, son with
              Sopt _, Node _ -> txt ^ " or " ^ name_of_tree_failed entry son
            | _ -> txt
          in
          let txt =
            match bro with
              DeadEnd | LocAct (_, _) -> txt
            | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro
          in
          txt
      | Some (_, rev_tokl, last_tok, _) ->
          List.fold_left
            (fun s tok ->
               (if s = "" then "" else s ^ " ") ^
               egram.glexer.Plexing.tok_text tok)
            "" (List.rev (last_tok :: rev_tokl))
      end
  | DeadEnd | LocAct (_, _) -> "???"

let tree_failed (type s a) (entry : s ty_entry) (prev_symb_result : a) (prev_symb : (s, a) ty_symbol) tree =
  let txt = name_of_tree_failed entry tree in
  let txt =
    match prev_symb with
      Slist0 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist1 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist0sep (s, sep, _) ->
        begin match prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Slist1sep (s, sep, _) ->
        begin match prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Sopt _ -> txt ^ " expected"
    | Stree _ -> txt ^ " expected"
    | _ -> txt ^ " expected after " ^ name_of_symbol_failed entry prev_symb
  in
  txt ^ " (in [" ^ entry.ename ^ "])"

let symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node {node = symb; brother = DeadEnd; son = DeadEnd} in
  tree_failed entry prev_symb_result prev_symb tree

let is_level_labelled n lev =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

let level_number entry lab =
  let rec lookup levn =
    function
      [] -> failwith ("unknown level " ^ lab)
    | lev :: levs ->
        if is_level_labelled lab lev then levn else lookup (succ levn) levs
  in
  match entry.edesc with
    Dlevels elev -> lookup 0 elev
  | Dparser _ -> raise Not_found

let rec top_symb : type s a. s ty_entry -> (s, a) ty_symbol -> (s, a) ty_symbol =
  fun entry ->
  function
    Sself -> Snterm entry
  | Snext -> Snterm entry
  | Snterml (e, _) -> Snterm e
  | Slist1sep (s, sep, b) -> Slist1sep (top_symb entry s, sep, b)
  | _ -> raise Stream.Failure

let entry_of_symb : type s a. s ty_entry -> (s, a) ty_symbol -> a ty_entry =
  fun entry ->
  function
    Sself -> entry
  | Snext -> entry
  | Snterm e -> e
  | Snterml (e, _) -> e
  | _ -> raise Stream.Failure

let top_tree : type s a. s ty_entry -> (s, a) ty_tree -> (s, a) ty_tree =
  fun entry ->
  function
    Node {node = s; brother = bro; son = son} ->
      Node {node = top_symb entry s; brother = bro; son = son}
  | LocAct (_, _) | DeadEnd -> raise Stream.Failure

let skip_if_empty bp p strm =
  (*XXX*) match bp with None -> raise Stream.Failure | Some bp ->
  if Stream.count strm == L.pos_of bp then fun a -> p strm
  else raise Stream.Failure

let continue entry a s son p1 first_token strm =
  let a, last_token =
    (entry_of_symb entry s).econtinue ~levn:0 a first_token strm in
  let act, last_token =
    try p1 last_token strm
    with Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
  in
  (fun _ -> act a), last_token

let do_recover parser_of_tree entry nlevn alevn a s son first_token strm =
  try parser_of_tree entry nlevn alevn (top_tree entry son) first_token strm
  with Stream.Failure ->
    continue entry a s son (parser_of_tree entry nlevn alevn son) first_token strm

let recover parser_of_tree entry nlevn alevn a s son first_token strm =
  do_recover parser_of_tree entry nlevn alevn a s son first_token strm

let token_count = ref 0

let peek_nth n strm =
  let list = Stream.npeek n strm in
  token_count := Stream.count strm + n;
  let rec loop list n =
    match list, n with
      x :: _, 1 -> Some x
    | _ :: l, n -> loop l (n - 1)
    | [], _ -> None
  in
  loop list n

let item_skipped = ref false

let call_and_push ps al first_token strm =
  item_skipped := false;
  let a, last_token = ps first_token strm in
  let al =
    if !item_skipped then al
    else a :: al in
  item_skipped := false;
  al, last_token

let token_ematch gram tok =
  let tematch = gram.glexer.Plexing.tok_match tok in
  fun tok -> tematch tok

let rec parser_of_tree : type s r. s ty_entry -> int -> int -> (s, r) ty_tree -> r parser_t =
  fun entry nlevn alevn ->
  function
  | DeadEnd -> (fun _first_token _strm -> raise Stream.Failure)
  | LocAct (act, _) -> (fun first_token _strm -> act, first_token)
  | Node {node = Sself; son = LocAct (act, _); brother = DeadEnd} ->
      (fun first_token strm ->
         let a, last_token = entry.estart alevn first_token strm in
         act a, last_token)
  | Node {node = Sself; son = LocAct (act, _); brother = bro} ->
      let p2 = parser_of_tree entry nlevn alevn bro in
      (fun first_token strm ->
         match
           try Some (entry.estart alevn first_token strm)
           with Stream.Failure -> None
         with
         | Some (a,last_token) -> act a, last_token
         | None -> p2 first_token strm)
  | Node {node = s; son = son; brother = DeadEnd} ->
      let tokl =
        match s with
        | Stoken tok -> get_token_list entry tok [] tok TokNil son
        | _ -> None
      in
      begin match tokl with
      | None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          (fun first_token strm ->
             let first_token = Stream.peek strm in
             let a, last_token = ps first_token strm in
             let act, last_token =
               try p1 a last_token strm
               with Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
             in
             act a, last_token)
      | Some (first_tok, rev_tokl, last_tok, TokTree (son, pf)) ->
          let s = Stoken first_tok in
          let lt = Stoken last_tok in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          parser_of_token_list entry s son pf p1
            (fun _ _ -> raise Stream.Failure) rev_tokl last_tok
      end
  | Node {node = s; son = son; brother = bro} ->
      let tokl =
        match s with
        | Stoken tok -> get_token_list entry tok [] tok TokNil son
        | _ -> None
      in
      match tokl with
        None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          (fun first_token strm ->
             let first_token = Stream.peek strm in
             match
               try Some (ps first_token strm)
               with Stream.Failure -> None
             with
             | Some (a,last_token) ->
                 begin match
                   try Some (p1 a last_token strm)
                   with Stream.Failure -> None
                 with
                   Some (act,last_token) -> act a, last_token
                 | None -> raise (Stream.Error (tree_failed entry a s son))
                 end
             | None -> p2 first_token strm)
      | Some (first_tok, rev_tokl, last_tok, TokTree (son, pf)) ->
          let lt = Stoken last_tok in
          let p2 = parser_of_tree entry nlevn alevn bro in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          let p1 =
            parser_of_token_list entry lt son pf p1 p2 rev_tokl last_tok
          in
          fun first_token strm ->
            try p1 first_token strm
            with Stream.Failure -> p2 first_token strm

and parser_cont : type s a r.
  (a -> r) parser_t -> s ty_entry -> int -> int -> (s, a) ty_symbol -> (s, a -> r) ty_tree -> a -> (a -> r) parser_t =
  fun p1 entry nlevn alevn s son a first_token strm ->
  try p1 first_token strm with
    Stream.Failure ->
      recover parser_of_tree entry nlevn alevn a s son first_token strm

and parser_of_token_list : type s r f.
  s ty_entry -> (s, string) ty_symbol -> (s, string -> r) ty_tree ->
    (r, f) tok_list -> (string -> (string -> r) parser_t) -> f parser_t -> _ -> _ -> f parser_t =
  fun entry s son pf p1 p2 rev_tokl last_tok ->
  let plast : r parser_t =
    let n = List.length rev_tokl + 1 in
    let tematch = token_ematch egram last_tok in
    let ps _first_token strm =
      match peek_nth n strm with
      | Some tok as last_token ->
          let r = tematch tok in
          for _i = 1 to n do Stream.junk strm done; r, last_token
      | None -> raise Stream.Failure
    in
    fun first_token strm ->
      let first_token = Stream.peek strm in
      let a, last_token = ps first_token strm in
      match
        try Some (p1 a last_token strm)
        with Stream.Failure -> None
      with
      | Some (act, last_token) -> act a, last_token
      | None -> raise (Stream.Error (tree_failed entry a s son))
  in
  match List.rev rev_tokl, pf with
  | [], TokNil -> (fun first_token strm -> plast first_token strm)
  | tok :: tokl, TokCns pf ->
      let tematch = token_ematch egram tok in
      let ps _first_token strm =
        match peek_nth 1 strm with
        | Some tok as last_token -> tematch tok, last_token
        | None -> raise Stream.Failure
      in
      let p1 =
        let rec loop : type s f. _ -> _ -> (s, f) tok_list -> (string -> s) parser_t -> (string -> f) parser_t =
          fun n tokl pf plast ->
          match tokl, pf with
            [], TokNil -> plast
          | tok :: tokl, TokCns pf ->
              let tematch = token_ematch egram tok in
              let ps _first_token strm =
                match peek_nth n strm with
                | Some tok as last_token -> tematch tok, last_token
                | None -> raise Stream.Failure
              in
              let p1 = loop (n + 1) tokl pf (Obj.magic plast) in (* FIXME *)
              fun first_token strm ->
                let a, last_token = ps first_token strm in
                let act, last_token = p1 last_token strm in
                (Obj.magic act a), last_token (* FIXME *)
          | _ -> assert false
        in
        loop 2 tokl pf plast
      in
      fun first_token strm ->
        let a, last_token = ps first_token strm in
        let act, last_token = p1 last_token strm in
        act a, last_token
  | _ -> assert false
and parser_of_symbol : type s a.
  s ty_entry -> int -> (s, a) ty_symbol -> a parser_t =
  fun entry nlevn ->
  function
  | Slist0 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al last_token strm =
        match
          try Some (ps al last_token strm)
          with Stream.Failure -> None
        with
        | Some (al,last_token) -> loop al last_token strm
        | _ -> al, last_token
      in
      (fun first_token strm ->
         let a, last_token = loop [] first_token strm in
         List.rev a, last_token)
  | Slist0sep (symb, sep, false) -> assert false (*
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      (fun first_token strm ->
         match
           try Some (ps [] first_token strm)
           with Stream.Failure -> None with
         | Some (_,last_token) -> [], last_token
         | _ -> [], first_token)
                                                    *)
  | Slist0sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al first_token strm =
        match
          try Some (pt first_token strm)
          with Stream.Failure -> None
        with
          Some (_, last_token) ->
            begin match
              try Some (ps al last_token strm)
              with Stream.Failure -> None
            with
              Some (al, last_token) -> kont al last_token strm
            | _ -> al, last_token
            end
        | None -> al, first_token
      in
      (fun first_token strm ->
         match
           try Some (ps [] first_token strm)
           with Stream.Failure -> None
         with
         | Some (al, last_token) ->
             let a, last_token = kont al last_token strm in
             List.rev a, last_token
         | None -> [], first_token)
  | Slist1 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al last_token strm =
        match
          try Some (ps al last_token strm)
          with Stream.Failure -> None
        with
        | Some (al, last_token) -> loop al last_token strm
        | _ -> al, last_token
      in
      (fun first_token strm ->
         let al, last_token = ps [] first_token strm in
         let a, last_token = loop al last_token strm in
         List.rev a, last_token)
  | Slist1sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al first_token strm =
        match
          try Some (pt first_token strm)
          with Stream.Failure -> None
        with
        | Some (v, last_token) ->
            let al, last_token =
              try ps al last_token strm
              with
                Stream.Failure ->
                  let a, last_token =
                    try parse_top_symb entry symb last_token strm
                    with Stream.Failure ->
                      raise (Stream.Error (symb_failed entry v sep symb))
                  in
                  a :: al, last_token
            in
            kont al last_token strm
        | None -> al, first_token
      in
      (fun first_token strm ->
         let al, last_token = ps [] first_token strm in
         let a, last_token = kont al last_token strm in
         List.rev a, last_token)
  | Slist1sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al first_token strm =
        match
          try Some (pt first_token strm)
          with Stream.Failure -> None with
        | Some (v, last_token) ->
            begin match
              try Some (ps al last_token strm)
              with Stream.Failure -> None
            with
            | Some (al,last_token) -> kont al last_token strm
            | None ->
                match
                  try Some (parse_top_symb entry symb last_token strm)
                  with Stream.Failure -> None
                with
                | Some (a,last_token) -> kont (a :: al) last_token strm
                | None -> al, last_token
            end
        | None -> al, first_token
      in
      (fun first_token strm ->
         let al, last_token = ps [] first_token strm in
         let a, last_token = kont al last_token strm in
         List.rev a, last_token)
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun first_token strm ->
         try let o, last_token = ps first_token strm in Some o, last_token
         with Stream.Failure -> None, first_token)
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      (fun first_token strm ->
         let first_token = Stream.peek strm in
         let a, last_token = pt first_token strm in
         let loc = loc_of_token_interval first_token last_token in
         a loc, last_token)
  | Snterm e -> (fun first_token strm -> e.estart 0 first_token strm)
  | Snterml (e, l) ->
      (fun first_token strm -> e.estart (level_number e l) first_token strm)
  | Sself -> (fun first_token strm -> entry.estart 0 first_token strm)
  | Snext -> (fun first_token strm -> entry.estart nlevn first_token strm)
  | Stoken tok -> parser_of_token entry tok

and parser_of_token : type s.
  s ty_entry -> Plexing.pattern -> string parser_t =
  fun entry tok ->
  let f = egram.glexer.Plexing.tok_match tok in
  fun first_token strm ->
    match Stream.peek strm with
    | Some tok -> let r = f tok in Stream.junk strm; r, first_token
    | None -> raise Stream.Failure

and parse_top_symb : type s a. s ty_entry -> (s, a) ty_symbol -> a parser_t =
  fun entry symb ->
  parser_of_symbol entry 0 (top_symb entry symb)

let rec start_parser_of_levels entry clevn =
  function
  | [] -> (fun _levn _first_token _strm -> raise Stream.Failure)
  | lev :: levs ->
      let p1 = start_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
      | DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          match levs with
            [] ->
              (fun levn first_token strm ->
                 (* this code should be there but is commented to preserve
                    compatibility with previous versions... with this code,
                    the grammar entry e: [[ "x"; a = e | "y" ]] should fail
                    because it should be: e: [RIGHTA[ "x"; a = e | "y" ]]...
                 if levn > clevn then match strm with parser []
                 else
                 *)
                 let first_token = Stream.peek strm in
                 let act, last_token = p2 first_token strm in
                 let a = act (loc_of_token_interval first_token last_token) in
                 entry.econtinue ~levn a last_token strm)
          | _ ->
              fun levn first_token strm ->
                if levn > clevn then p1 levn first_token strm
                else
                  let first_token = Stream.peek strm in
                  match
                    try Some (p2 first_token strm)
                    with Stream.Failure -> None
                  with
                  | Some (act, last_token) ->
                      let a = act (loc_of_token_interval first_token last_token) in
                      entry.econtinue ~levn a last_token strm
                  | _ -> p1 levn first_token strm

let rec continue_parser_of_levels entry clevn =
  function
  | [] -> (fun ~levn:_ _a _first_token _strm -> raise Stream.Failure)
  | lev :: levs ->
      let p1 = continue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
      | DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          fun ~levn a first_token strm ->
            if levn > clevn then p1 ~levn a first_token strm
            else
              try p1 ~levn a first_token strm with
                Stream.Failure ->
                  let act, last_token = p2 first_token strm in
                  let a = act a (loc_of_token_interval first_token last_token) in
                  entry.econtinue ~levn a last_token strm

let continue_parser_of_entry entry =
  match entry.edesc with
  | Dlevels elev ->
      let p = continue_parser_of_levels entry 0 elev in
      (fun ~levn a first_token strm ->
         try p ~levn a first_token strm
         with Stream.Failure -> a)
  | Dparser p ->
      fun ~levn:_ _a _first_token _strm -> raise Stream.Failure

let empty_entry ename _levn _first_token _strm =
  raise (Stream.Error ("entry [" ^ ename ^ "] is empty"))

let start_parser_of_entry entry =
  match entry.edesc with
    Dlevels [] -> empty_entry entry.ename
  | Dlevels elev -> start_parser_of_levels entry 0 elev
  | Dparser p -> fun _levn first_token strm -> p first_token strm

(* Extend syntax *)

let init_entry_functions entry =
  entry.estart <-
    (fun lev first_token strm ->
       let f = start_parser_of_entry entry in
       entry.estart <- f; f lev first_token strm);
  entry.econtinue <-
    (fun ~levn a first_token strm ->
       let f = continue_parser_of_entry entry in
       entry.econtinue <- f; f ~levn a first_token strm)

let extend_entry ~warning entry position rules =
    let elev = levels_of_rules ~warning entry position rules in
    entry.edesc <- Dlevels elev; init_entry_functions entry

(* Deleting a rule *)

let delete_rule entry sl =
  match entry.edesc with
  | Dlevels levs ->
      let levs = delete_rule_in_level_list entry sl levs in
      entry.edesc <- Dlevels levs;
      entry.estart <-
        (fun lev first_token strm ->
           let f = start_parser_of_entry entry in
           entry.estart <- f; f lev first_token strm);
      entry.econtinue <-
        (fun ~levn a first_token strm ->
           let f = continue_parser_of_entry entry in
           entry.econtinue <- f; f ~levn a first_token strm)
  | Dparser _ -> ()

(* Normal interface *)

type parsable = {
  pa_chr_strm : char Stream.t;
  pa_tok_strm : L.te Stream.t;
}

let parse_parsable entry p =
  let efun = entry.estart 0 None in
  let ts = p.pa_tok_strm in
  let cs = p.pa_chr_strm in
  let fun_loc = L.loc_of in
  let get_loc () =
    try
      match Stream.peek ts with
      | Some t -> fun_loc t
      | None -> Ploc.make_unlined (Stream.count cs, Stream.count cs + 1)
(*
      let cnt = Stream.count ts in
      let loc = fun_loc (Stream.peek ts) in
      if !token_count - 1 <= cnt then loc
      else Loc.merge loc (fun_loc (!token_count - 1))
*)
    with Failure _ -> Ploc.make_unlined (Stream.count cs, Stream.count cs + 1)
  in
  token_count := 0;
  try fst(efun ts) with
    Stream.Failure ->
      let loc = get_loc () in
      Ploc.raise loc (Stream.Error ("illegal begin of " ^ entry.ename))
  | Stream.Error _ as exc ->
      let loc = get_loc () in Ploc.raise loc exc
  | exc ->
      let loc = Stream.count cs, Stream.count cs + 1 in
      Ploc.raise (Ploc.make_unlined loc) exc

(* Unsafe *)

let clear_entry e =
  e.estart <- (fun _levn _first_token _strm -> raise Stream.Failure);
  e.econtinue <- (fun ~levn:_ _a _first_token _strm -> raise Stream.Failure);
  match e.edesc with
  | Dlevels _ -> e.edesc <- Dlevels []
  | Dparser _ -> ()

    let parsable tok_func cs =
      let ts = tok_func cs in
      { pa_chr_strm = cs; pa_tok_strm = ts }

module Entry =
  struct
    type 'a e = 'a ty_entry
    type nonrec 'a parser_t = 'a parser_t
    let create n =
      { ename = n; estart = empty_entry n;
       econtinue =
         (fun ~levn:_ _a _first_token _strm -> raise Stream.Failure);
       edesc = Dlevels [] }
    let parse (e : 'a e) p : 'a =
      parse_parsable e p
    let parse_token_stream (e : 'a e) ts : 'a =
      fst(e.estart 0 None ts)
    let name e = e.ename
    let of_lookahead n (p : te Stream.t -> unit) : 'a e =
      { ename = n;
       estart = (fun _levn first_token strm -> p strm, first_token);
       econtinue =
         (fun ~levn:_ _a _first_token _strm -> raise Stream.Failure);
       edesc = Dparser (fun first_token strm -> p strm, first_token) }
    let of_parser n (p : 'a parser_t) : 'a e =
      { ename = n;
       estart = (fun _levn -> p);
       econtinue =
         (fun ~levn:_ _a _first_token _strm -> raise Stream.Failure);
       edesc = Dparser p}
    let print ppf e = fprintf ppf "%a@." print_entry e
  end

let s_nterm e = Snterm e
let s_nterml e l = Snterml (e, l)
let s_list0 s = Slist0 s
let s_list0sep s sep b = Slist0sep (s, sep, b)
let s_list1 s = Slist1 s
let s_list1sep s sep b = Slist1sep (s, sep, b)
let s_opt s = Sopt s
let s_self = Sself
let s_next = Snext
let s_token tok = Stoken tok
let s_rules ~warning (t : 'a ty_production list) = srules ~warning t
let r_stop = TStop
let r_next r s = TNext (r, s)
let production (p, act) = TProd (p, act)
module Unsafe =
  struct
    let clear_entry = clear_entry
  end
let safe_extend ~warning (e : 'a Entry.e) pos
    (r :
     (string option * Gramext.g_assoc option * 'a ty_production list)
       list) =
  extend_entry ~warning e pos r
let safe_delete_rule e r =
  let AnyS (symbols, _) = get_symbols r in
  delete_rule e symbols

end
