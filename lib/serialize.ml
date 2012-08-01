(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Protocol version of this file. This is the date of the last modification. *)

(** WARNING: TO BE UPDATED WHEN MODIFIED! *)

let protocol_version = "20120710"

(** * Interface of calls to Coq by CoqIde *)

open Interface

type xml =
  | Element of (string * (string * string) list * xml list)
  | PCData of string

(** We use phantom types and GADT to protect ourselves against wild casts *)

type 'a call =
  | Interp     of interp_sty
  | Backto     of backto_sty
  | Goals      of goals_sty
  | Evars      of evars_sty
  | Hints      of hints_sty
  | Status     of status_sty
  | GetOptions of get_options_sty
  | SetOptions of set_options_sty
  | InLoadPath of inloadpath_sty
  | MkCases    of mkcases_sty
  | Search     of search_sty
  | Quit       of quit_sty
  | About      of about_sty

(** The actual calls *)

let interp x      : interp_rty call      = Interp x
let backto x      : backto_rty call      = Backto x
let goals x       : goals_rty call       = Goals x
let evars x       : evars_rty call       = Evars x
let hints x       : hints_rty call       = Hints x
let status x      : status_rty call      = Status x
let get_options x : get_options_rty call = GetOptions x
let set_options x : set_options_rty call = SetOptions x
let inloadpath x  : inloadpath_rty call  = InLoadPath x
let mkcases x     : mkcases_rty call     = MkCases x
let search x      : search_rty call      = Search x
let quit x        : quit_rty call        = Quit x
let about x       : about_rty call       = About x

(** * Coq answers to CoqIde *)

let abstract_eval_call handler c =
  let mkGood (l,x) = Good (l, Obj.magic x) in
  try
    match c with
    | Interp x     -> mkGood (handler.interp x)
    | Backto x     -> mkGood (handler.backto x)
    | Goals x      -> mkGood (handler.goals x)
    | Evars x      -> mkGood (handler.evars x)
    | Hints x      -> mkGood (handler.hints x)
    | Status x     -> mkGood (handler.status x)
    | GetOptions x -> mkGood (handler.get_options x)
    | SetOptions x -> mkGood (handler.set_options x)
    | InLoadPath x -> mkGood (handler.inloadpath x)
    | MkCases x    -> mkGood (handler.mkcases x)
    | Search x     -> mkGood (handler.search x)
    | Quit x       -> mkGood (handler.quit x)
    | About x      -> mkGood (handler.about x)
  with e -> Fail (handler.handle_exn e)

(** * XML data marshalling *)

exception Marshal_error

(** Utility functions *)

let massoc x l =
  try List.assoc x l
  with Not_found -> raise Marshal_error

let constructor t c args = Element (t, ["val", c], args)

let do_match constr t mf = match constr with
| Element (s, attrs, args) ->
  if s = t then
    let c = massoc "val" attrs in
    mf c args
  else raise Marshal_error
| _ -> raise Marshal_error

let pcdata = function
| PCData s -> s
| _ -> raise Marshal_error

let singleton = function
| [x] -> x
| _ -> raise Marshal_error

let raw_string = function
| [] -> ""
| [PCData s] -> s
| _ -> raise Marshal_error

let bool_arg tag b = if b then [tag, ""] else []

(** Base types *)

let of_bool b =
  if b then constructor "bool" "true" []
  else constructor "bool" "false" []

let to_bool xml = do_match xml "bool"
  (fun s _ -> match s with
  | "true" -> true
  | "false" -> false
  | _ -> raise Marshal_error)

let of_list f l =
  Element ("list", [], List.map f l)

let to_list f = function
| Element ("list", [], l) ->
  List.map f l
| _ -> raise Marshal_error

let of_option f = function
| None -> Element ("option", ["val", "none"], [])
| Some x -> Element ("option", ["val", "some"], [f x])

let to_option f = function
| Element ("option", ["val", "none"], []) -> None
| Element ("option", ["val", "some"], [x]) -> Some (f x)
| _ -> raise Marshal_error

let of_string s = Element ("string", [], [PCData s])

let to_string = function
| Element ("string", [], l) -> raw_string l
| _ -> raise Marshal_error

let of_int i = Element ("int", [], [PCData (string_of_int i)])

let to_int = function
| Element ("int", [], [PCData s]) -> int_of_string s
| _ -> raise Marshal_error

let of_pair f g (x, y) = Element ("pair", [], [f x; g y])

let to_pair f g = function
| Element ("pair", [], [x; y]) -> (f x, g y)
| _ -> raise Marshal_error

(** More elaborate types *)

let of_option_value = function
| IntValue i ->
  constructor "option_value" "intvalue" [of_option of_int i]
| BoolValue b ->
  constructor "option_value" "boolvalue" [of_bool b]
| StringValue s ->
  constructor "option_value" "stringvalue" [of_string s]

let to_option_value xml = do_match xml "option_value"
  (fun s args -> match s with
  | "intvalue" -> IntValue (to_option to_int (singleton args))
  | "boolvalue" -> BoolValue (to_bool (singleton args))
  | "stringvalue" -> StringValue (to_string (singleton args))
  | _ -> raise Marshal_error
  )

let of_option_state s =
  Element ("option_state", [], [
    of_bool s.opt_sync;
    of_bool s.opt_depr;
    of_string s.opt_name;
    of_option_value s.opt_value]
  )

let to_option_state = function
| Element ("option_state", [], [sync; depr; name; value]) ->
  {
    opt_sync = to_bool sync;
    opt_depr = to_bool depr;
    opt_name = to_string name;
    opt_value = to_option_value value;
  }
| _ -> raise Marshal_error

let of_search_constraint = function
| Name_Pattern s ->
  constructor "search_constraint" "name_pattern" [of_string s]
| Type_Pattern s ->
  constructor "search_constraint" "type_pattern" [of_string s]
| SubType_Pattern s ->
  constructor "search_constraint" "subtype_pattern" [of_string s]
| In_Module m ->
  constructor "search_constraint" "in_module" [of_list of_string m]
| Include_Blacklist ->
  constructor "search_constraint" "include_blacklist" []

let to_search_constraint xml = do_match xml "search_constraint"
  (fun s args -> match s with
  | "name_pattern" -> Name_Pattern (to_string (singleton args))
  | "type_pattern" -> Type_Pattern (to_string (singleton args))
  | "subtype_pattern" -> SubType_Pattern (to_string (singleton args))
  | "in_module" -> In_Module (to_list to_string (singleton args))
  | "include_blacklist" -> Include_Blacklist
  | _ -> raise Marshal_error)

let of_search_answer ans =
  let path = of_list of_string ans.search_answer_full_path in
  let name = of_string ans.search_answer_base_name in
  let tpe = of_string ans.search_answer_type in
  Element ("search_answer", [], [path; name; tpe])

let to_search_answer = function
| Element ("search_answer", [], [path; name; tpe]) ->
  let path = to_list to_string path in
  let name = to_string name in
  let tpe = to_string tpe in {
    search_answer_full_path = path;
    search_answer_base_name = name;
    search_answer_type = tpe;
  }
| _ -> raise Marshal_error

let of_state_id x =
  Element ("state_id", [], [PCData (Stategraph.string_of_state_id x)])

let to_state_id = function
| Element ("state_id", [], [PCData x]) ->
    Stategraph.state_id_of_int (int_of_string x)
| _ -> raise Marshal_error

let of_value f = function
| Good (good_spans,x) -> 
    Element ("value", ["val", "good"], 
      [of_pair (of_list of_state_id) f (good_spans, x)])
| Fail (good_spans,bad_spans,(span,loc), msg) ->
  let loc = match loc with
  | None -> []
  | Some (s, e) -> [("loc_s", string_of_int s); ("loc_e", string_of_int e)]
  in
  Element ("value", 
    ["val", "fail"] @ ["span",Stategraph.string_of_state_id span] @ loc,
    [of_list of_state_id good_spans;
     of_list of_state_id bad_spans ;
     PCData msg])

let to_value f = function
| Element ("value", attrs, l) ->
  let ans = massoc "val" attrs in
  if ans = "good" then Good (to_pair (to_list to_state_id) f (singleton l))
  else if ans = "fail" then
    let loc =
      try
        let loc_s = int_of_string (List.assoc "loc_s" attrs) in
        let loc_e = int_of_string (List.assoc "loc_e" attrs) in
        Some (loc_s, loc_e)
      with _ -> None
    in
    let state =
      Stategraph.state_id_of_int (int_of_string (List.assoc "span" attrs)) in
    match l with
    | [good_spans; bad_spans; PCData msg] ->
        let good_spans = to_list to_state_id good_spans in
        let bad_spans = to_list to_state_id bad_spans in
        Fail (good_spans, bad_spans, (state,loc), msg)
    | _ -> raise Marshal_error
  else raise Marshal_error
| _ -> raise Marshal_error

let of_call = function
| Interp (raw, vrb, cmd) ->
  let flags = (bool_arg "raw" raw) @ (bool_arg "verbose" vrb) in
  Element ("call", ("val", "interp") :: flags, [PCData cmd])
| Backto id ->
  Element ("call", ["val", "backto"], [of_state_id id])
| Goals () ->
  Element ("call", ["val", "goal"], [])
| Evars () ->
  Element ("call", ["val", "evars"], [])
| Hints () ->
  Element ("call", ["val", "hints"], [])
| Search flags ->
  let args = List.map (of_pair of_search_constraint of_bool) flags in
  Element ("call", ["val", "search"], args)
| Status force ->
  Element ("call", ["val", "status"; "force", string_of_bool force], [])
| GetOptions () ->
  Element ("call", ["val", "getoptions"], [])
| SetOptions opts ->
  let args = List.map (of_pair (of_list of_string) of_option_value) opts in
  Element ("call", ["val", "setoptions"], args)
| InLoadPath file ->
  Element ("call", ["val", "inloadpath"], [PCData file])
| MkCases ind ->
  Element ("call", ["val", "mkcases"], [PCData ind])
| Quit () ->
  Element ("call", ["val", "quit"], [])
| About () ->
  Element ("call", ["val", "about"], [])

let to_call = function
| Element ("call", attrs, l) ->
  let ans = massoc "val" attrs in
  begin match ans with
  | "interp" ->
    let raw = List.mem_assoc "raw" attrs in
    let vrb = List.mem_assoc "verbose" attrs in
    Interp (raw, vrb, raw_string l)
  | "backto" ->
    Backto (to_state_id (singleton l))
  | "goal" -> Goals ()
  | "evars" -> Evars ()
  | "status" ->
    let force = bool_of_string (massoc "force" attrs) in
    Status force
  | "search" ->
    let args = List.map (to_pair to_search_constraint to_bool) l in
    Search args
  | "getoptions" -> GetOptions ()
  | "setoptions" ->
    let args = List.map (to_pair (to_list to_string) to_option_value) l in
    SetOptions args
  | "inloadpath" -> InLoadPath (raw_string l)
  | "mkcases" -> MkCases (raw_string l)
  | "quit" -> Quit ()
  | "about" -> About ()
  | _ -> raise Marshal_error
  end
| _ -> raise Marshal_error

let of_status s =
  let of_so = of_option of_string in
  let of_sl = of_list of_string in
  Element ("status", [],
    [
      of_sl s.status_path;
      of_so s.status_proofname;
      of_sl s.status_allproofs;
      of_int s.status_statenum;
      of_int s.status_proofnum;
    ]
  )

let to_status = function
| Element ("status", [], [path; name; prfs; snum; pnum]) ->
  {
    status_path = to_list to_string path;
    status_proofname = to_option to_string name;
    status_allproofs = to_list to_string prfs;
    status_statenum = to_int snum;
    status_proofnum = to_int pnum;
  }
| _ -> raise Marshal_error

let of_evar s =
  Element ("evar", [], [PCData s.evar_info])

let to_evar = function
| Element ("evar", [], data) -> { evar_info = raw_string data; }
| _ -> raise Marshal_error

let of_goal g =
  let hyp = of_list of_string g.goal_hyp in
  let ccl = of_string g.goal_ccl in
  let id = of_string g.goal_id in
  Element ("goal", [], [id; hyp; ccl])

let to_goal = function
| Element ("goal", [], [id; hyp; ccl]) ->
  let hyp = to_list to_string hyp in
  let ccl = to_string ccl in
  let id = to_string id in
  { goal_hyp = hyp; goal_ccl = ccl; goal_id = id; }
| _ -> raise Marshal_error

let of_goals g =
  let of_glist = of_list of_goal in
  let fg = of_list of_goal g.fg_goals in
  let bg = of_list (of_pair of_glist of_glist) g.bg_goals in
  Element ("goals", [], [fg; bg])

let to_goals = function
| Element ("goals", [], [fg; bg]) ->
  let to_glist = to_list to_goal in
  let fg = to_list to_goal fg in
  let bg = to_list (to_pair to_glist to_glist) bg in
  { fg_goals = fg; bg_goals = bg; }
| _ -> raise Marshal_error

let of_coq_info info =
  let version = of_string info.coqtop_version in
  let protocol = of_string info.protocol_version in
  let release = of_string info.release_date in
  let compile = of_string info.compile_date in
  Element ("coq_info", [], [version; protocol; release; compile])

let to_coq_info = function
| Element ("coq_info", [], [version; protocol; release; compile]) ->
  {
    coqtop_version = to_string version;
    protocol_version = to_string protocol;
    release_date = to_string release;
    compile_date = to_string compile;
  }
| _ -> raise Marshal_error

let of_message_level = function
| Debug s -> constructor "message_level" "debug" [PCData s]
| Info -> constructor "message_level" "info" []
| Notice -> constructor "message_level" "notice" []
| Warning -> constructor "message_level" "warning" []
| Error -> constructor "message_level" "error" []

let to_message_level xml = do_match xml "message_level"
  (fun s args -> match s with
  | "debug" -> Debug (raw_string args)
  | "info" -> Info
  | "notice" -> Notice
  | "warning" -> Warning
  | "error" -> Error
  | _ -> raise Marshal_error)

let of_oob_message msg =
  let lvl = of_message_level msg.message_level in
  let content = of_string msg.message_content in
  Element ("message", [], [lvl; content])

let to_oob_message xml = match xml with
| Element ("message", [], [lvl; content]) ->
  { message_level = to_message_level lvl; message_content = to_string content }
| _ -> raise Marshal_error

let of_hints =
  let of_hint = of_list (of_pair of_string of_string) in
  of_option (of_pair (of_list of_hint) of_hint)

let is_oob_message = function
| Element ("message", _, _) -> true
| _ -> false

let of_unit () = Element ("unit", [], [])

let of_interp_rty  : interp_rty -> xml = of_pair of_state_id of_string
let of_backto_rty  : backto_rty -> xml = of_unit
let of_goals_rty   : goals_rty -> xml  = of_pair (of_option of_goals) of_string
let of_evars_rty   : evars_rty -> xml  = of_option (of_list of_evar)
let of_hints_rty   : hints_rty -> xml  = of_hints
let of_status_rty  : status_rty -> xml = of_pair of_status of_string
let of_get_options_rty : get_options_rty -> xml =
  of_list (of_pair (of_list of_string) of_option_state)
let of_set_options_rty : set_options_rty -> xml = of_unit
let of_inloadpath_rty : inloadpath_rty -> xml = of_bool
let of_mkcases_rty : mkcases_rty -> xml = of_list (of_list of_string)
let of_search_rty  : search_rty -> xml = of_list of_search_answer
let of_about_rty   : about_rty -> xml  = of_coq_info
let of_quit_rty    : quit_rty -> xml   = of_unit

let of_answer (q : 'a call) (r : 'a value) = match q with
  | Interp _     -> of_value of_interp_rty      (Obj.magic r)
  | Backto _     -> of_value of_backto_rty      (Obj.magic r)
  | Goals _      -> of_value of_goals_rty       (Obj.magic r)
  | Evars _      -> of_value of_evars_rty       (Obj.magic r)
  | Hints _      -> of_value of_hints_rty       (Obj.magic r)
  | Status _     -> of_value of_status_rty      (Obj.magic r)
  | GetOptions _ -> of_value of_get_options_rty (Obj.magic r)
  | SetOptions _ -> of_value of_set_options_rty (Obj.magic r)
  | InLoadPath _ -> of_value of_inloadpath_rty  (Obj.magic r)
  | MkCases _    -> of_value of_mkcases_rty     (Obj.magic r)
  | Search _     -> of_value of_search_rty      (Obj.magic r)
  | Quit _       -> of_value of_quit_rty        (Obj.magic r)
  | About _      -> of_value of_about_rty       (Obj.magic r)

let to_answer xml =
  let rec convert elt = match elt with
  | Element (tpe, attrs, l) ->
    begin match tpe with
    | "unit"          -> Obj.magic ()
    | "string"        -> Obj.magic (to_string elt : string)
    | "int"           -> Obj.magic (to_int elt : int)
    | "status"        -> Obj.magic (to_status elt : status)
    | "bool"          -> Obj.magic (to_bool elt : bool)
    | "list"          -> Obj.magic (to_list convert elt : 'a list)
    | "option"        -> Obj.magic (to_option convert elt : 'a option)
    | "pair"          -> Obj.magic (to_pair convert convert elt : ('a * 'b))
    | "goals"         -> Obj.magic (to_goals elt : goals)
    | "evar"          -> Obj.magic (to_evar elt : evar)
    | "state_id"      -> Obj.magic (to_state_id elt : Stategraph.state_id)
    | "option_value"  -> Obj.magic (to_option_value elt : option_value)
    | "option_state"  -> Obj.magic (to_option_state elt : option_state)
    | "coq_info"      -> Obj.magic (to_coq_info elt : coq_info)
    | "search_answer" -> Obj.magic (to_search_answer elt : search_answer)
    | _ -> raise Marshal_error
    end
  | _ -> raise Marshal_error
  in
  to_value convert xml

(** * Debug printing *)

let pr_option_value = function
| IntValue None -> "none"
| IntValue (Some i) -> string_of_int i
| StringValue s -> s
| BoolValue b -> if b then "true" else "false"

let rec pr_setoptions opts =
  let map (key, v) =
    let key = String.concat " " key in
    key ^ " := " ^ (pr_option_value v)
  in
  String.concat "; " (List.map map opts)

let pr_getoptions opts =
  let map (key, s) =
    let key = String.concat " " key in
    Printf.sprintf "%s: sync := %b; depr := %b; name := %s; value := %s\n"
      key s.opt_sync s.opt_depr s.opt_name (pr_option_value s.opt_value)
  in
  "\n" ^ String.concat "" (List.map map opts)

let pr_call = function
  | Interp (r,b,s) ->
    let raw = if r then "RAW" else "" in
    let verb = if b then "" else "SILENT" in
    "INTERP"^raw^verb^" ["^s^"]"
  | Backto id -> "BACKTO "^(Stategraph.string_of_state_id id)
  | Goals () -> "GOALS"
  | Evars () -> "EVARS"
  | Hints () -> "HINTS"
  | Search _ -> "SEARCH"
  | Status force -> "STATUS " ^ string_of_bool force
  | GetOptions () -> "GETOPTIONS"
  | SetOptions l -> "SETOPTIONS" ^ " [" ^ pr_setoptions l ^ "]"
  | InLoadPath s -> "INLOADPATH "^s
  | MkCases s -> "MKCASES "^s
  | Quit () -> "QUIT"
  | About () -> "ABOUT"

let pr_value_gen pr = function
  | Good (l,v) -> "GOOD " ^ pr v ^ 
      " ["^String.concat ";" (List.map Stategraph.string_of_state_id l)^"]"
  | Fail (good_ids, bad_ids,(id,_),str) -> "FAIL (["^
      String.concat ";" (List.map Stategraph.string_of_state_id good_ids)^"],["^
      String.concat ";" (List.map Stategraph.string_of_state_id bad_ids) ^"],"^ 
      Stategraph.string_of_state_id id  ^") ["^str^"]"

let pr_value v = pr_value_gen (fun _ -> "") v

let pr_string s = "["^s^"]"
let pr_bool b = if b then "true" else "false"
let pr_unit () = "()"

let pr_state_id id = "(" ^ Stategraph.string_of_state_id id ^ ")"

let pr_status s =
  let path =
    let l = String.concat "." s.status_path in
    "path=" ^ l ^ ";"
  in
  let name = match s.status_proofname with
  | None -> "no proof;"
  | Some n -> "proof = " ^ n ^ ";"
  in
  "Status: " ^ path ^ name

let pr_mkcases l =
  let l = List.map (String.concat " ") l in
  "[" ^ String.concat " | " l ^ "]"

let pr_goals_aux g =
  if g.fg_goals = [] then
    if g.bg_goals = [] then "Proof completed."
    else
      let rec pr_focus _ = function
      | [] -> assert false
      | [lg, rg] -> Printf.sprintf "%i" (List.length lg + List.length rg)
      | (lg, rg) :: l ->
        Printf.sprintf "%i:%a" (List.length lg + List.length rg) pr_focus l
      in
      Printf.sprintf "Still focussed: [%a]." pr_focus g.bg_goals
  else
    let pr_menu s = s in
    let pr_goal { goal_hyp = hyps; goal_ccl = goal } =
      "[" ^ String.concat "; " (List.map pr_menu hyps) ^ " |- " ^ pr_menu goal ^ "]"
    in
    String.concat " " (List.map pr_goal g.fg_goals)

let pr_goals = function
| None -> "No proof in progress."
| Some g -> pr_goals_aux g

let pr_evar ev = "[" ^ ev.evar_info ^ "]"

let pr_evars = function
| None -> "No proof in progress."
| Some evars -> String.concat " " (List.map pr_evar evars)

let pr_pair f g (a,b) = f a ^ " " ^ g b

let pr_full_value call value = match call with
  | Interp _ -> 
      pr_value_gen (pr_pair pr_state_id pr_string)
        (Obj.magic value : interp_rty value)
  | Backto _ -> 
      pr_value_gen pr_unit (Obj.magic value : backto_rty value)
  | Goals _ -> 
      pr_value_gen (pr_pair pr_goals pr_string)
        (Obj.magic value : goals_rty value)
  | Evars _ -> pr_value_gen pr_evars (Obj.magic value : evars_rty value)
  | Hints _ -> pr_value value
  | Status _ -> 
      pr_value_gen (pr_pair pr_status pr_string)
        (Obj.magic value : status_rty value)
  | GetOptions _ ->
      pr_value_gen pr_getoptions (Obj.magic value : get_options_rty value)
  | SetOptions _ -> pr_value value
  | InLoadPath s ->
      pr_value_gen pr_bool (Obj.magic value : inloadpath_rty value)
  | MkCases _ -> pr_value_gen pr_mkcases (Obj.magic value : mkcases_rty value)
  | Search _ -> pr_value value
  | Quit _ -> pr_value_gen pr_unit (Obj.magic value : quit_rty value)
  | About _ -> pr_value value
