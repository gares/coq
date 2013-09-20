(*
type xml =
        | Element of (string * (string * string) list * xml list)
        | PCData of string
*)

open Xml_datatype
open Vernacexpr
open Constrexpr
open Names
open Misctypes

let unlock loc =
  let start, stop = Loc.unloc loc in
  (string_of_int start, string_of_int stop)

let xmlThm typ name loc xml =
  let start, stop = unlock loc in
  Element("theorem", [
    "type", typ;
    "name", name;
    "begin", start;
    "end", stop ], xml)

let xmlCst name ?(attr=[]) loc =
  let start, stop = unlock loc in
  Element("constant", attr @ [
    "name", name;
    "begin", start;
    "end", stop ], [])

let xmlOperator name ?(attr=[]) loc =
  let start, stop = unlock loc in
  Element("operator", attr @ [
    "name", name;
    "begin", start;
    "end", stop ], [])

let xmlApply loc ?(attr=[]) xml =
  let start, stop = unlock loc in
  Element("apply", attr @ [
    "begin", start;
    "end", stop ], xml)

let xmlTyped xml =
  Element("typed", [], xml)

let string_of_name n =
  match n with
  | Anonymous -> "_"
  | Name id -> Id.to_string id

let string_of_glob_sort s =
  match s with
  | GProp -> "Prop"
  | GSet -> "Set"
  | GType _ -> "Type"

let string_of_cast_sort c =
  match c with
  | CastConv _ -> "CastConv"
  | CastVM _ -> "CastVM"
  | _ -> assert false

let op_of_cast_sort c =
  match c with
  | CastConv _ -> ":"
  | CastVM _ -> "<:"
  | _ -> assert false

let rec pp_expr ?(attr=[]) e =
  let unbind_expr bindlist =
    let tlist =
      List.flatten
        (List.map
          (fun (locl, _, e) ->
            let names =
              (List.map
                (fun (loc, name) ->
                  xmlCst (string_of_name name) loc) locl) in
              match e with
              | CHole (_,_) -> names
              | _ -> names @ [pp_expr e])
          bindlist) in
    match tlist with
    | [e] -> e
    | l -> xmlTyped l in
  match e with
  | CRef r ->
      xmlCst ~attr
        (Libnames.string_of_reference r) (Libnames.loc_of_reference r)
  | CProdN (loc, lb, e) ->
      xmlApply loc
        (xmlOperator "forall" loc :: [unbind_expr lb] @ [pp_expr e])
  | CApp (loc, (_, hd), args) ->
       xmlApply ~attr loc (pp_expr hd :: List.map (fun (e,_) -> pp_expr e) args)
  | CAppExpl (loc, (_, r), args) ->
       xmlApply ~attr loc (xmlCst (Libnames.string_of_reference r) (Libnames.loc_of_reference r) :: List.map pp_expr args)
  | CNotation (loc, notation,  ([],_,_)) ->
       xmlOperator notation loc
  | CNotation (loc, notation,  (args,_,_)) ->
       xmlApply loc (xmlOperator notation loc :: List.map pp_expr args)
  | CSort(loc, s) ->
       xmlOperator (string_of_glob_sort s) loc
  | CDelimiters (_, _, _) -> assert false
  | CPrim (_, _) -> assert false
  | CGeneralization (_, _, _, _) -> assert false
  | CCast (loc, e, tc) ->
      (match tc with
       | CastConv t | CastVM t -> xmlApply loc (xmlOperator (string_of_cast_sort tc) loc ~attr:["kind", (op_of_cast_sort tc)] :: [pp_expr e; pp_expr t])
       | CastCoerce   -> pp_expr e
       | CastNative _ -> assert false)
  | CEvar (_, _, _) -> assert false
  | CPatVar (_, _) -> assert false
  | CHole (loc, _) -> xmlCst ~attr  "_" loc
  | CIf (_, _, _, _, _) -> assert false
  | CLetTuple (_, _, _, _, _) -> assert false
  | CCases (_, _, _, _, _) -> assert false
  | CRecord (_, _, _) -> assert false
  | CLetIn (loc, (varloc, var), value, body) ->
      xmlApply loc (xmlOperator "let" loc :: [xmlCst (string_of_name var) varloc; pp_expr value; pp_expr body])
  | CLambdaN (loc, lb, e) ->
      xmlApply loc
        (xmlOperator "lambda" loc :: [unbind_expr lb] @ [pp_expr e])
  | CCoFix (_, _, _) -> assert false
  | CFix (_, _, _) -> assert false

  (* | CAppExpl of Loc.t * (proj_flag * reference) * constr_expr list *)
(*
  | CFix of Loc.t * Id.t located * fix_expr list
  | CCoFix of Loc.t * Id.t located * cofix_expr list
  | CLambdaN of Loc.t * binder_expr list * constr_expr
  | CLetIn of Loc.t * Name.t located * constr_expr * constr_expr
  | CRecord of Loc.t * constr_expr option * (reference * constr_expr) list
  | CCases of Loc.t * case_style * constr_expr option *
      case_expr list * branch_expr list
  | CLetTuple of Loc.t * Name.t located list * (Name.t located option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of Loc.t * constr_expr * (Name.t located option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of Loc.t * Evar_kinds.t option
  | CPatVar of Loc.t * (bool * patvar)
  | CEvar of Loc.t * existential_key * constr_expr list option
  | CSort of Loc.t * glob_sort
  | CCast of Loc.t * constr_expr * constr_expr cast_type
  | CGeneralization of Loc.t * binding_kind * abstraction_kind option * constr_expr
  | CPrim of Loc.t * prim_token
  | CDelimiters of Loc.t * string * constr_expr
*)

let tmpp v loc =
  match v with
  | VernacStartTheoremProof (tk, [ Some (_,id), ([], statement, None) ], b) ->
      let str_tk = Kindops.string_of_theorem_kind tk in
      let str_id = Id.to_string id in
      (xmlThm str_tk str_id loc [pp_expr statement])
  | _ -> assert false
  (*
  (* Control *)
  | VernacList of located_vernac_expr list
  | VernacLoad of verbose_flag * string
  | VernacTime of vernac_expr
  | VernacTimeout of int * vernac_expr
  | VernacFail of vernac_expr

  (* Syntax *)
  | VernacTacticNotation of
      int * grammar_tactic_prod_item_expr list * raw_tactic_expr
  | VernacSyntaxExtension of
      obsolete_locality * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of obsolete_locality * (bool * scope_name)
  | VernacDelimiters of scope_name * string
  | VernacBindScope of scope_name * reference or_by_notation list
  | VernacInfix of obsolete_locality * (lstring * syntax_modifier list) *
      constr_expr * scope_name option
  | VernacNotation of
      obsolete_locality * constr_expr * (lstring * syntax_modifier list) *
      scope_name option

  (* Gallina *)
  | VernacDefinition of
      (locality option * definition_object_kind) * lident * definition_expr
  | VernacStartTheoremProof of theorem_kind *
      (lident option * (local_binder list * constr_expr * (lident option * recursion_order_expr) option)) list *
        bool
  | VernacEndProof of proof_end
  | VernacExactProof of constr_expr
  | VernacAssumption of (locality option * assumption_object_kind) *
      inline * simple_binder with_coercion list
  | VernacInductive of inductive_flag * infer_flag * (inductive_expr * decl_notation list) list
  | VernacFixpoint of
      locality option * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of
      locality option * (cofixpoint_expr * decl_notation list) list
  | VernacScheme of (lident option * scheme) list
  | VernacCombinedScheme of lident * lident list

  (* Gallina extensions *)
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      export_flag option * lreference list
  | VernacImport of export_flag * lreference list
  | VernacCanonical of reference or_by_notation
  | VernacCoercion of obsolete_locality * reference or_by_notation *
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of obsolete_locality * lident *
      class_rawexpr * class_rawexpr

  (* Type classes *)
  | VernacInstance of
      bool * (* abstract instance *)
      local_binder list * (* super *)
	typeclass_constraint * (* instance name, class name, params *)
	constr_expr option * (* props *)
	int option (* Priority *)

  | VernacContext of local_binder list

  | VernacDeclareInstances of reference list (* instance names *)

  | VernacDeclareClass of reference (* inductive or definition name *)

  (* Modules and Module Types *)
  | VernacDeclareModule of bool option * lident *
      module_binder list * module_ast_inl
  | VernacDefineModule of bool option * lident * module_binder list *
      module_ast_inl module_signature * module_ast_inl list
  | VernacDeclareModuleType of lident *
      module_binder list * module_ast_inl list * module_ast_inl list
  | VernacInclude of module_ast_inl list

  (* Solving *)

  | VernacSolve of int * raw_tactic_expr * bool
  | VernacSolveExistential of int * constr_expr

  (* Auxiliary file and library management *)
  | VernacRequireFrom of export_flag option * string
  | VernacAddLoadPath of rec_flag * string * DirPath.t option
  | VernacRemoveLoadPath of string
  | VernacAddMLPath of rec_flag * string
  | VernacDeclareMLModule of string list
  | VernacChdir of string option

  (* State management *)
  | VernacWriteState of string
  | VernacRestoreState of string

  (* Resetting *)
  | VernacResetName of lident
  | VernacResetInitial
  | VernacBack of int
  | VernacBackTo of int

  (* Commands *)
  | VernacDeclareTacticDefinition of
      (rec_flag * (reference * bool * raw_tactic_expr) list)
  | VernacCreateHintDb of string * bool
  | VernacRemoveHints of string list * reference list
  | VernacHints of obsolete_locality * string list * hints_expr
  | VernacSyntacticDefinition of Id.t located * (Id.t list * constr_expr) *
      obsolete_locality * onlyparsing_flag
  | VernacDeclareImplicits of reference or_by_notation *
      (explicitation * bool * bool) list list
  | VernacArguments of reference or_by_notation *
      ((Name.t * bool * (Loc.t * string) option * bool * bool) list) list *
      int * [ `SimplDontExposeCase | `SimplNeverUnfold | `Rename | `ExtraScopes
            | `ClearImplicits | `ClearScopes | `DefaultImplicits ] list
  | VernacArgumentsScope of reference or_by_notation *
      scope_name option list
  | VernacReserve of simple_binder list
  | VernacGeneralizable of (lident list) option
  | VernacSetOpacity of (Conv_oracle.level * reference or_by_notation list)
  | VernacSetStrategy of
      (Conv_oracle.level * reference or_by_notation list) list
  | VernacUnsetOption of Goptions.option_name
  | VernacSetOption of Goptions.option_name * option_value
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of raw_red_expr option * int option * constr_expr
  | VernacGlobalCheck of constr_expr
  | VernacDeclareReduction of string * raw_red_expr
  | VernacPrint of printable
  | VernacSearch of searchable * search_restriction
  | VernacLocate of locatable
  | VernacComments of comment list
  | VernacNop

  (* Stm backdoor *)
  | VernacStm of vernac_expr stm_vernac

  (* Proof management *)
  | VernacGoal of constr_expr
  | VernacAbort of lident option
  | VernacAbortAll
  | VernacRestart
  | VernacUndo of int
  | VernacUndoTo of int
  | VernacBacktrack of int*int*int
  | VernacFocus of int option
  | VernacUnfocus
  | VernacUnfocused
  | VernacBullet of bullet
  | VernacSubproof of int option
  | VernacEndSubproof
  | VernacShow of showable
  | VernacCheckGuard
  | VernacProof of raw_tactic_expr option * lident list option
  | VernacProofMode of string
  (* Toplevel control *)
  | VernacToplevelControl of exn

  (* For extension *)
  | VernacExtend of string * raw_generic_argument list

  (* Flags *)
  | VernacProgram of vernac_expr
  | VernacLocal of bool * vernac_expr
  *)
