open Xml_datatype
open Vernacexpr
open Constrexpr
open Names
open Misctypes
open Bigint
open Decl_kinds
open Extend
open Libnames
open Flags

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

let xmlNotation attr name loc xml =
  let start, stop = unlock loc in
  Element("notation", attr @ [
    "name", name;
    "begin", start;
    "end", stop ], xml)

let xmlReservedNotation attr name loc =
  let start, stop = unlock loc in
  Element("reservednotation", attr @ [
    "name", name;
    "begin", start;
    "end", stop ], [])

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

let xmlReturn ?(attr=[]) xml =
  Element("return", attr, xml)

let xmlCase xml =
  Element("case", [], xml)

let xmlScrutinee ?(attr=[]) xml =
  Element("scrutinee", attr, xml)

let xmlWith xml =
  Element("with", [], xml)

let xmlInductive kind loc xml =
  let start, stop = unlock loc in
  Element("inductive", [
    "kind", kind;
    "begin", start;
    "end", stop ], xml)

let xmlCheck loc xml =
  let start, stop = unlock loc in
  Element("check", [
    "begin", start;
    "end", stop ], xml)

let xmlAssumption kind loc xml =
  let start, stop = unlock loc in
  Element("assumption", [
    "kind", kind;
    "begin", start;
    "end", stop ], xml)

let xmlComment loc xml =
  let start, stop = unlock loc in
  Element("comment", [
    "begin", start;
    "end", stop ], xml)

let xmlCanonicalStructure attr loc =
  let start, stop = unlock loc in
  Element("canonicalstructure", attr @ [
    "begin", start;
    "end", stop ], [])

let xmlQed ?(attr=[]) loc =
  let start, stop = unlock loc in
  Element("qed", attr @ [
    "begin", start;
    "end", stop ], [])

let xmlPatvar id loc =
  let start, stop = unlock loc in
  Element("patvar", [
    "id", id;
    "begin", start;
    "end", stop ], [])

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
  | CastNative _ -> "CastNative"
  | _ -> assert false

let string_of_case_style s =
  match s with
  | LetStyle -> "Let"
  | IfStyle -> "If"
  | LetPatternStyle -> "LetPattern"
  | MatchStyle -> "Match"
  | RegularStyle -> "Regular"

let attribute_of_syntax_modifier sm =
match sm with
  | SetItemLevel (sl, NumLevel n) ->
      List.map (fun s -> ("itemlevel", s)) sl @ ["level", string_of_int n]
  | SetItemLevel (sl, NextLevel) ->
      List.map (fun s -> ("itemlevel", s)) sl @ ["level", "next"]
  | SetLevel i -> ["level", string_of_int i]
  | SetAssoc a ->
      begin match a with
      | NonA -> ["",""]
      | RightA -> ["associativity", "right"]
      | LeftA -> ["associativity", "left"]
      end
  | SetEntryType (s, _) -> ["entrytype", s]
  | SetOnlyParsing v -> ["compat", Flags.pr_version v]
  | SetFormat (loc, s) ->
      let start, stop= unlock loc in
      ["format", s; "begin", start; "end", stop]

let string_of_assumption_kind l a many =
  match l, a, many with
  | (Discharge, Logical,      true)  -> "Hypotheses"
  | (Discharge, Logical,      false) -> "Hypothesis"
  | (Discharge, Definitional, true)  -> "Variables"
  | (Discharge, Definitional, false) -> "Variable"
  | (Global,    Logical,      true)  -> "Axioms"
  | (Global,    Logical,      false) -> "Axiom"
  | (Global,    Definitional, true)  -> "Parameters"
  | (Global,    Definitional, false) -> "Parameter"
  | (Local,     Logical,      true)  -> "Local Axioms"
  | (Local,     Logical,      false) -> "Local Axiom"
  | (Local,     Definitional, true)  -> "Local Parameters"
  | (Local,     Definitional, false) -> "Local Parameter"
  | (Global,    Conjectural, _)      -> "Conjecture"
  | ((Discharge | Local), Conjectural, _) -> assert false

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
              | CHole _ -> names
              | _ -> names @ [pp_expr e])
          bl) in
  match tlist with
    | [e] -> e
    | l -> xmlTyped l
and pp_decl_notation ((_, s), ce, sc) = (* don't know what it is for now *)
  Element ("decl_notation", ["name", s], [pp_expr ce])
and pp_local_binder lb = (* don't know what it is for now *)
  match lb with
  | LocalRawDef ((_, nam), ce) ->
      let attrs = ["name", string_of_name nam] in
      pp_expr ~attr:attrs ce
  | LocalRawAssum (namll, _, ce) ->
      let attrs =
        List.map (fun (_, nam) -> ("name", string_of_name nam)) namll in
      pp_expr ~attr:attrs ce
and pp_local_decl_expr lde = (* don't know what it is for now *)
  match lde with
  | AssumExpr (_, ce) -> pp_expr ce
  | DefExpr (_, ce, _) -> pp_expr ce
and pp_inductive_expr ((_, (_, id)), lbl, ceo, _, cl_or_rdexpr) = (* inductive_expr *)
  [Element ("lident", ["name", Id.to_string id], [])] @ (* don't know what it is for now *)
  begin match cl_or_rdexpr with
  | Constructors coel -> List.map (fun (_, (_, ce)) -> pp_expr ce) coel
  | RecordDecl (_, ldewwwl) ->
      List.map (fun (((_, x), _), _) -> pp_local_decl_expr x) ldewwwl
  end @
  begin match ceo with (* don't know what it is for now *)
  | Some ce -> [pp_expr ce]
  | None -> []
  end @
  (List.map pp_local_binder lbl)
and pp_lident (loc, id) = xmlCst (Id.to_string id) loc
and pp_simple_binder (idl, ce) =
  (List.map pp_lident idl) @ [pp_expr ce]
and pp_cases_pattern_expr cpe =
  match cpe with
  | CPatAlias (loc, cpe, id) ->
      xmlApply loc
        (xmlOperator "alias" ~attr:["name", string_of_id id] loc ::
          [pp_cases_pattern_expr cpe])
  | CPatCstr (loc, ref, cpel1, cpel2) ->
      xmlApply loc
        (xmlOperator "reference"
           ~attr:["name", Libnames.string_of_reference ref] loc ::
         [Element ("impargs", [], (List.map pp_cases_pattern_expr cpel1));
          Element ("args", [], (List.map pp_cases_pattern_expr cpel2))])
  | CPatAtom (loc, None) -> xmlApply loc (xmlOperator "atom" loc :: [])
  | CPatAtom (loc, Some r) ->
      xmlApply loc
        (xmlOperator "atom"
          ~attr:["name", Libnames.string_of_reference r] loc :: [])
  | CPatOr (loc, cpel) ->
      xmlApply loc
        (xmlOperator "or" loc :: (List.map pp_cases_pattern_expr cpel))
  | CPatNotation (loc, n, (subst_constr, subst_rec), cpel) ->
      xmlApply loc
        (xmlOperator "notation" loc ::
          [xmlOperator n loc;
           Element ("subst", [],
             [Element ("subterms", [],
                List.map pp_cases_pattern_expr subst_constr);
              Element ("recsubterms", [],
                List.map
                  (fun (cpel) ->
                     Element ("recsubterm", [],
                       List.map pp_cases_pattern_expr cpel))
                subst_rec)]);
           Element ("args", [], (List.map pp_cases_pattern_expr cpel))])
  | CPatPrim (loc, tok) -> pp_token loc tok
  | CPatRecord (loc, rcl) ->
      xmlApply loc
        (xmlOperator "record" loc ::
           List.map (fun (r, cpe) ->
             Element ("field",
               ["reference", Libnames.string_of_reference r],
               [pp_cases_pattern_expr cpe]))
           rcl)
  | CPatDelimiters (loc, delim, cpe) ->
      xmlApply loc
        (xmlOperator "delimiter" ~attr:["name", delim] loc ::
          [pp_cases_pattern_expr cpe])
and pp_case_expr (e, (name, pat)) =
  match name, pat with
  | None, None -> xmlScrutinee [pp_expr e]
  | Some (loc, name), None ->
      let start, stop= unlock loc in
      xmlScrutinee ~attr:["name", string_of_name name;
                          "begin", start; "end", stop] [pp_expr e]
  | Some (loc, name), Some p ->
      let start, stop= unlock loc in
      xmlScrutinee ~attr:["name", string_of_name name;
                          "begin", start; "end", stop]
        [Element ("in", [], [pp_cases_pattern_expr p]) ; pp_expr e]
  | None, Some p ->
      xmlScrutinee [Element ("in", [], [pp_cases_pattern_expr p]) ; pp_expr e]
and pp_branch_expr_list bel =
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
  | CDelimiters (loc, scope, ce) ->
      xmlApply loc (xmlOperator "delimiter" ~attr:["name", scope] loc ::
        [pp_expr ce])
  | CPrim (loc, tok) -> pp_token loc tok
  | CGeneralization (loc, Implicit, _, e) ->
      xmlApply loc
        (xmlOperator "generalization" ~attr:["type", "implicit"] loc ::
          [pp_expr e])
  | CGeneralization (loc, Explicit, _, e) ->
      xmlApply loc
        (xmlOperator "generalization" ~attr:["type", "explicit"] loc ::
          [pp_expr e])
  | CCast (loc, e, tc) ->
      begin match tc with
      | CastConv t | CastVM t |CastNative t ->
          xmlApply loc
            (xmlOperator ":" loc ~attr:["kind", (string_of_cast_sort tc)] ::
             [pp_expr e; pp_expr t])
      | CastCoerce   ->
          xmlApply loc
            (xmlOperator ":" loc ~attr:["kind", "CastCoerce"] ::
             [pp_expr e])
      end
  | CEvar (loc, ek, None) ->
      xmlApply loc
        (xmlOperator "evar" loc ~attr:["id", string_of_int (Evar.repr ek)] ::
          [])
  | CEvar (loc, ek, Some cel) ->
      xmlApply loc
        (xmlOperator "evar" loc ~attr:["id", string_of_int (Evar.repr ek)] ::
          List.map pp_expr cel)
  | CPatVar (loc, (_, id)) -> xmlPatvar (string_of_id id) loc
  | CHole (loc, _, _) -> xmlCst ~attr  "_" loc
  | CIf (loc, test, (_, ret), th, el) ->
      let return = match ret with
      | None -> []
      | Some r -> [xmlReturn [pp_expr r]] in
      xmlApply loc
        (xmlOperator "if" loc ::
          return @ [pp_expr th] @ [pp_expr el])
  | CLetTuple (loc, names, (_, ret), value, body) ->
      let return = match ret with
      | None -> []
      | Some r -> [xmlReturn [pp_expr r]] in
      xmlApply loc
        (xmlOperator "lettuple" loc ::
          return @
          (List.map (fun (loc, var) -> xmlCst (string_of_name var) loc) names) @
          [pp_expr value; pp_expr body])
  | CCases (loc, sty, None, cel, bel) ->
      xmlApply loc
        (xmlOperator "match" loc ~attr:["style", (string_of_case_style sty)] ::
          ([Element ("scrutinees", [], List.map pp_case_expr cel)] @
           [pp_branch_expr_list bel]))
  | CCases (loc, sty, Some e, cel, bel) ->
      xmlApply loc
        (xmlOperator "match" loc  ~attr:["style", (string_of_case_style sty)] ::
          ([xmlReturn [pp_expr e]] @
           [Element ("scrutinees", [], List.map pp_case_expr cel)] @
           [pp_branch_expr_list bel]))
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
  | VernacError _ -> assert false

  (* Syntax *)
  | VernacTacticNotation _ -> assert false
  | VernacSyntaxExtension (_, ((_, name), sml)) ->
      let attrs = List.flatten (List.map attribute_of_syntax_modifier sml) in
      xmlReservedNotation attrs name loc

  | VernacOpenCloseScope _ -> assert false
  | VernacDelimiters _ -> assert false
  | VernacBindScope _ -> assert false
  | VernacInfix _ -> assert false
  | VernacNotation (_, ce, (lstr, sml), sn) ->
      let name = snd lstr in
      let attrs = List.flatten (List.map attribute_of_syntax_modifier sml) in
      let sc_attr =
        match sn with
        | Some scope -> ["scope", scope]
        | None -> [] in
      xmlNotation (sc_attr @ attrs) name loc [pp_expr ce]

  (* Gallina *)
  | VernacDefinition (ldk, (_,id), de) ->
      let l, dk =
        match ldk with
        | Some l, dk -> (l, dk)
        | None, dk -> (Global, dk) in (* Like in ppvernac.ml, l 585 *)
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
  | VernacStartTheoremProof _ -> assert false
  | VernacEndProof pe ->
      begin
        match pe with
        | Admitted -> xmlQed loc
        | Proved (_, Some ((_, id), Some tk)) ->
            let nam = Id.to_string id in
            let typ = Kindops.string_of_theorem_kind tk in
            xmlQed ~attr:["name", nam; "type", typ] loc
        | Proved (_, Some ((_, id), None)) ->
            let nam = Id.to_string id in
            xmlQed ~attr:["name", nam] loc
        | Proved _ -> xmlQed loc
      end
  | VernacExactProof _ -> assert false
  | VernacAssumption ((l, a), _, sbwcl) ->
      let many =
        List.length (List.flatten (List.map fst (List.map snd sbwcl))) > 1 in
      let exprs =
        List.flatten (List.map pp_simple_binder (List.map snd sbwcl)) in
      let l = match l with Some x -> x | None -> Decl_kinds.Global in
      let kind = string_of_assumption_kind l a many in
      xmlAssumption kind loc exprs
  | VernacInductive (_, _, iednll) ->
      let kind =
        let (_, _, _, k, _),_ = List.hd iednll in
	  begin
            match k with
            | Record -> "Record"
            | Structure -> "Structure"
            | Inductive_kw -> "Inductive"
            | CoInductive -> "CoInductive"
            | Class _ -> "Class"
          end in
      let exprs =
        List.flatten
          (List.map
            (fun (ie, dnl) -> (pp_inductive_expr ie) @
                              (List.map pp_decl_notation dnl)) iednll) in
      xmlInductive kind loc exprs
  | VernacFixpoint _ -> assert false
  | VernacCoFixpoint _ -> assert false
  | VernacScheme _ -> assert false
  | VernacCombinedScheme _ -> assert false

  (* Gallina extensions *)
  | VernacBeginSection (_, id) -> xmlBeginSection loc (Id.to_string id)
  | VernacEndSegment (_, id) -> xmlEndSegment loc (Id.to_string id)
  | VernacRequire _ -> assert false
  | VernacImport _ -> assert false
  | VernacCanonical r ->
      let attr =
        match r with
        | AN (Qualid (_, q)) -> ["qualid", string_of_qualid q]
        | AN (Ident (_, id)) -> ["id", Id.to_string id]
        | ByNotation (_, s, _) -> ["notation", s] in
      xmlCanonicalStructure attr loc
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
  | VernacSyntacticDefinition ((_, name), (idl, ce), _, _) ->
      let name = Id.to_string name in
      let attrs = List.map (fun id -> ("id", Id.to_string id)) idl in
      xmlNotation attrs name loc [pp_expr ce]
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
  | VernacCheckMayEval (_,_,e) -> xmlCheck loc [pp_expr e]
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
      | PrintDag _ -> assert false
      | Wait _ -> assert false
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
