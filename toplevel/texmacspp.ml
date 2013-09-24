open Xml_datatype
open Vernacexpr
open Constrexpr
open Names
open Misctypes
open Bigint
open Decl_kinds

let unlock loc =
  let start, stop = Loc.unloc loc in
  (string_of_int start, string_of_int stop)

let xmlNoop = (* almost noop  *)
  PCData ""

let xmlBeginSection loc name =
  let start, stop = unlock loc in
  Element("beginsection", [
    "name", name;
    "begin", start;
    "end", stop ], [])

let xmlEndSegment loc name =
  let start, stop = unlock loc in
  Element("endsegment", [
    "name", name;
    "begin", start;
    "end", stop ], [])

let xmlThm typ name loc xml =
  let start, stop = unlock loc in
  Element("theorem", [
    "type", typ;
    "name", name;
    "begin", start;
    "end", stop ], xml)

let xmlDef typ name loc xml =
  let start, stop = unlock loc in
  Element("definition", [
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

let xmlToken loc ?(attr=[]) xml =
  let start, stop = unlock loc in
  Element("token", attr @ [
    "begin", start;
    "end", stop ], xml)

let xmlTyped xml =
  Element("typed", [], xml)

let xmlReturn xml =
  Element("return", [], xml)

let xmlCase xml =
  Element("case", [], xml)

let xmlMatch xml =
  Element("match", [], xml)

let xmlWith xml =
  Element("with", [], xml)

let xmlComment loc xml =
  let start, stop = unlock loc in
  Element("comment", [
    "begin", start;
    "end", stop ], xml)

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

let string_of_case_style s =
  match s with
  | LetStyle -> "Let"
  | IfStyle -> "If"
  | LetPatternStyle -> "LetPattern"
  | MatchStyle -> "Match"
  | RegularStyle -> "Regular"

(* For debuging purpose *)
let string_of_cases_pattern_expr cpe =
  match cpe with
  | CPatAlias _ -> "CPatAlias"
  | CPatCstr _ -> "CPatCstr"
  | CPatAtom _ -> "CPatAtom"
  | CPatOr _ -> "CPatOr"
  | CPatNotation _ -> "CPatNotation"
  | CPatPrim _ -> "CPatPrim"
  | CPatRecord _ -> "CPatRecord"
  | CPatDelimiters _ -> "CPatDelimiters"

let rec pp_bindlist bl =
  let tlist =
    List.flatten
        (List.map
          (fun (loc_names, _, e) ->
            let names =
              (List.map
                (fun (loc, name) ->
                  xmlCst (string_of_name name) loc) loc_names) in
            match e with
              | CHole (_,_) -> names
              | _ -> names @ [pp_expr e])
          bl) in
  match tlist with
    | [e] -> e
    | l -> xmlTyped l

and pp_cases_pattern_expr cpe =
  (* TODO: To be finished. cases_pattern_expr are quite complex*)
  let str= string_of_cases_pattern_expr cpe in
  Element ("pp_cases_pattern_expr", [("case", str)], [])
and pp_case_expr (e,_) =
  (* TODO: To be finished. cases_pattern_expr are not handled *)
  xmlMatch [pp_expr e]
and pp_branch_expr_list bel =
  (* TODO: To be thought. How to prettyprint well the pattern / branch list *)
  xmlWith
    (List.map
      (fun (_, cpel, e) ->
        let ppcepl =
          (List.map pp_cases_pattern_expr (List.flatten (List.map snd cpel))) in
        let ppe = [pp_expr e] in
        xmlCase (ppcepl @ ppe))
     bel)
and pp_token loc tok =
  let tokstr =
    match tok with
    | String s -> PCData s
    | Numeral n -> PCData (to_string n) in
  xmlToken loc [tokstr]
and pp_expr ?(attr=[]) e =
  match e with
  | CRef r ->
      xmlCst ~attr
        (Libnames.string_of_reference r) (Libnames.loc_of_reference r)
  | CProdN (loc, bl, e) ->
      xmlApply loc
        (xmlOperator "forall" loc :: [pp_bindlist bl] @ [pp_expr e])
  | CApp (loc, (_, hd), args) ->
       xmlApply ~attr loc (pp_expr hd :: List.map (fun (e,_) -> pp_expr e) args)
  | CAppExpl (loc, (_, r), args) ->
       xmlApply ~attr loc
         (xmlCst (Libnames.string_of_reference r)
                 (Libnames.loc_of_reference r) :: List.map pp_expr args)
  | CNotation (loc, notation,  ([],_,_)) ->
       xmlOperator notation loc
  | CNotation (loc, notation,  (args,_,_)) ->
       xmlApply loc (xmlOperator notation loc :: List.map pp_expr args)
  | CSort(loc, s) ->
       xmlOperator (string_of_glob_sort s) loc
  | CDelimiters (_, _, _) -> assert false
  | CPrim (loc, tok) -> pp_token loc tok
  | CGeneralization (_, _, _, _) -> assert false
  | CCast (loc, e, tc) ->
      begin match tc with
      | CastConv t | CastVM t ->
          xmlApply loc
            (xmlOperator ":" loc ~attr:["kind", (string_of_cast_sort tc)] ::
             [pp_expr e; pp_expr t])
      | CastCoerce   -> pp_expr e
      | CastNative _ -> assert false
      end
  | CEvar (_, _, _) -> assert false
  | CPatVar (_, _) -> assert false
  | CHole (loc, _) -> xmlCst ~attr  "_" loc
  | CIf (_, _, _, _, _) -> assert false
  | CLetTuple (_, _, _, _, _) -> assert false
  | CCases (loc, sty, None, cel, bel) ->
      xmlApply loc
        (xmlOperator "match" loc ~attr:["style", (string_of_case_style sty)] ::
          (List.map pp_case_expr cel) @ [pp_branch_expr_list bel])
  | CCases (loc, sty, Some e, cel, bel) ->
      xmlApply loc
        (xmlOperator "match" loc  ~attr:["style", (string_of_case_style sty)] ::
          [xmlReturn [pp_expr e]] @ (List.map pp_case_expr cel) @
          [pp_branch_expr_list bel])
  | CRecord (_, _, _) -> assert false
  | CLetIn (loc, (varloc, var), value, body) ->
      xmlApply loc
        (xmlOperator "let" loc ::
         [xmlCst (string_of_name var) varloc; pp_expr value; pp_expr body])
  | CLambdaN (loc, bl, e) ->
      xmlApply loc
        (xmlOperator "lambda" loc :: [pp_bindlist bl] @ [pp_expr e])
  | CCoFix (_, _, _) -> assert false
  | CFix (_, _, _) -> assert false

let pp_comment (c) =
  match c with
  | CommentConstr e -> [pp_expr e]
  | CommentString s -> [Element ("string", [], [PCData s])]
  | CommentInt i -> [PCData (string_of_int i)]

let rec tmpp v loc =
  match v with
  (* Control *)
  | VernacList _ -> assert false
  | VernacLoad _ -> assert false
  | VernacTime _ -> assert false
  | VernacTimeout _ -> assert false
  | VernacFail _ -> assert false

  (* Syntax *)
  | VernacTacticNotation _ -> assert false
  | VernacSyntaxExtension _ -> assert false
  | VernacOpenCloseScope _ -> assert false
  | VernacDelimiters _ -> assert false
  | VernacBindScope _ -> assert false
  | VernacInfix _ -> assert false
  | VernacNotation _ -> assert false

  (* Gallina *)
  | VernacDefinition (ldk, (_,id), de) ->
      let l, dk =
        match ldk with
        | Some l, dk -> (l, dk)
        | None, dk -> (Discharge, dk) in  (* FIXME: optional locality
        * I don't have any idea of what should be done. But it's needed for
        * string_of_definition_kind. *)
      let e =
        match de with
        | ProveBody (_, ce) -> ce 
        | DefineBody (_, Some _, ce, None) -> ce
        | DefineBody (_, None  , ce, None) -> ce
        | DefineBody (_, Some _, ce, Some _) -> ce
        | DefineBody (_, None  , ce, Some _) -> ce in
      let str_dk = Kindops.string_of_definition_kind (l, dk) in
      let str_id = Id.to_string id in
      (xmlDef str_dk str_id loc [pp_expr e])
  | VernacStartTheoremProof (tk, [ Some (_,id), ([], statement, None) ], b) ->
      let str_tk = Kindops.string_of_theorem_kind tk in
      let str_id = Id.to_string id in
      (xmlThm str_tk str_id loc [pp_expr statement])
  | VernacEndProof _ -> assert false
  | VernacExactProof _ -> assert false
  | VernacAssumption _ -> assert false
  | VernacInductive _ -> assert false
  | VernacFixpoint _ -> assert false
  | VernacCoFixpoint _ -> assert false
  | VernacScheme _ -> assert false
  | VernacCombinedScheme _ -> assert false

  (* Gallina extensions *)
  | VernacBeginSection (_, id) -> xmlBeginSection loc (Id.to_string id)
  | VernacEndSegment (_, id) -> xmlEndSegment loc (Id.to_string id)
  | VernacRequire _ -> assert false
  | VernacImport _ -> assert false
  | VernacCanonical _ -> assert false
  | VernacCoercion _ -> assert false
  | VernacIdentityCoercion _ -> assert false

  (* Type classes *)
  | VernacInstance _ -> assert false

  | VernacContext _ -> assert false

  | VernacDeclareInstances _ -> assert false

  | VernacDeclareClass _ -> assert false

  (* Modules and Module Types *)
  | VernacDeclareModule _ -> assert false
  | VernacDefineModule _ -> assert false
  | VernacDeclareModuleType _ -> assert false
  | VernacInclude _ -> assert false

  (* Solving *)

  | VernacSolve _ -> PCData "VernacSolve"
  | VernacSolveExistential _ -> assert false

  (* Auxiliary file and library management *)
  | VernacRequireFrom _ -> assert false
  | VernacAddLoadPath _ -> PCData "VernacAddLoadPath"
  | VernacRemoveLoadPath _ -> assert false
  | VernacAddMLPath _ -> assert false
  | VernacDeclareMLModule _ -> assert false
  | VernacChdir _ -> assert false

  (* State management *)
  | VernacWriteState _ -> assert false
  | VernacRestoreState _ -> assert false

  (* Resetting *)
  | VernacResetName _ -> assert false
  | VernacResetInitial -> assert false
  | VernacBack _ -> assert false
  | VernacBackTo _ -> PCData "VernacBackTo"

  (* Commands *)
  | VernacDeclareTacticDefinition _ -> assert false
  | VernacCreateHintDb _ -> assert false
  | VernacRemoveHints _ -> assert false
  | VernacHints _ -> assert false
  | VernacSyntacticDefinition _ -> assert false
  | VernacDeclareImplicits _ -> assert false
  | VernacArguments _ -> assert false
  | VernacArgumentsScope _ -> assert false
  | VernacReserve _ -> assert false
  | VernacGeneralizable _ -> assert false
  | VernacSetOpacity _ -> assert false
  | VernacSetStrategy _ -> assert false
  | VernacUnsetOption _ -> assert false
  | VernacSetOption _ -> assert false
  | VernacAddOption _ -> assert false
  | VernacRemoveOption _ -> assert false
  | VernacMemOption _ -> assert false
  | VernacPrintOption _ -> assert false
  | VernacCheckMayEval _ -> assert false
  | VernacGlobalCheck _ -> assert false
  | VernacDeclareReduction _ -> assert false
  | VernacPrint _ -> assert false
  | VernacSearch _ -> assert false
  | VernacLocate _ -> assert false
  | VernacRegister _ -> assert false
  | VernacComments (cl) ->
      xmlComment loc (List.flatten (List.map pp_comment cl))
  | VernacNop -> assert false

  (* Stm backdoor *)
  | VernacStm s ->
      begin match s with
      | JoinDocument -> assert false
      | Finish -> assert false
      | Observe _ -> assert false
      | Command v -> tmpp v Loc.ghost (* note: loc might be optionnal*)
      | PGLast _ -> assert false
      end

  (* Proof management *)
  | VernacGoal _ -> assert false
  | VernacAbort _ -> assert false
  | VernacAbortAll -> PCData "VernacAbortAll"
  | VernacRestart -> assert false
  | VernacUndo _ -> assert false
  | VernacUndoTo _ -> assert false
  | VernacBacktrack _ -> assert false
  | VernacFocus _ -> assert false
  | VernacUnfocus -> assert false
  | VernacUnfocused -> assert false
  | VernacBullet _ -> assert false
  | VernacSubproof _ -> assert false
  | VernacEndSubproof -> assert false
  | VernacShow _ -> assert false
  | VernacCheckGuard -> assert false
  | VernacProof _ -> assert false
  | VernacProofMode _ -> assert false
  (* Toplevel control *)
  | VernacToplevelControl _ -> assert false

  (* For extension *)
  | VernacExtend _ -> assert false

  (* Flags *)
  | VernacProgram _ -> assert false
  | VernacLocal _ -> assert false
