(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

open DocumentManager
open Printer
open Lwt.Infix
open Lwt_err.Infix

module CompactedDecl = Context.Compacted.Declaration

let init_state : Vernacstate.t option ref = ref None
let get_init_state () =
  match !init_state with
  | Some st -> st
  | None -> CErrors.anomaly Pp.(str "Initial state not available")

let documents : (string, document) Hashtbl.t = Hashtbl.create 39

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

(*let string_field name obj = Yojson.Basic.to_string (List.assoc name obj)*)

let read_request ic : Yojson.Basic.t Lwt.t =
  Lwt_io.read_line ic >!= fun header ->
  let scan_header = Scanf.Scanning.from_string header in
  Scanf.bscanf scan_header "Content-Length: %d" (fun size ->
      let buf = Bytes.create size in
      (* Discard a second newline *)
      Lwt_io.read_line ic >!= fun _ ->
      Lwt_io.read_into_exactly ic buf 0 size >!= fun () ->
      Lwt.return @@ Bytes.to_string buf
    ) >>= fun obj_str ->
  log @@ "received: " ^ obj_str;
  Lwt.return @@ Yojson.Basic.from_string obj_str

let output_json obj : unit Lwt.t =
  let msg  = Yojson.Basic.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  (*log @@ "replied: " ^ msg;*)
  Lwt_io.write Lwt_io.stdout s >!= fun () -> Lwt.return ()

let mk_notification ~event ~params = `Assoc ["jsonrpc", `String "2.0"; "method", `String event; "params", params]
let mk_response ~id ~result = `Assoc ["jsonrpc", `String "2.0"; "id", `Int id; "result", result]

let do_initialize ~id : unit Lwt.t =
  let capabilities = `Assoc [
    "textDocumentSync", `Int 2 (* Incremental *)
  ]
  in
  let result = `Assoc ["capabilities", capabilities] in
  output_json @@ mk_response ~id ~result

let parse_loc json =
  let open Yojson.Basic.Util in
  let line = json |> member "line" |> to_int in
  let char = json |> member "character" |> to_int in
  DocumentManager.{ line ; char }

let mk_loc loc =
  `Assoc [
    "line", `Int loc.line;
    "character", `Int loc.char;
  ]

let mk_range range =
  `Assoc [
    "start", mk_loc range.range_start;
    "end", mk_loc range.range_end;
  ]

let publish_diagnostics uri doc : unit Lwt.t =
  let mk_diagnostic d =
    `Assoc [
      "range", mk_range d.range;
      "severity", `Int (match d.severity with Error -> 1 | Warning -> 2);
      "message", `String d.message;
    ]
  in
  let diagnostics = List.map mk_diagnostic @@ DocumentManager.diagnostics doc in
  let params = `Assoc [
    "uri", `String uri;
    "diagnostics", `List diagnostics;
  ]
  in
  output_json @@ mk_notification ~event:"textDocument/publishDiagnostics" ~params

let send_highlights uri doc : unit Lwt.t =
  let executed_ranges, incomplete_ranges = DocumentManager.executed_ranges doc in
  let executed_ranges = List.map mk_range executed_ranges in
  let incomplete_ranges = List.map mk_range incomplete_ranges in
  let params = `Assoc [
    "uri", `String uri;
    "stateErrorRange", `List [];
    "parsingRange", `List [];
    "processingRange", `List [];
    "incompleteRange", `List incomplete_ranges;
    "axiomRange", `List [];
    "processedRange", `List executed_ranges;
  ]
  in
  output_json @@ mk_notification ~event:"coqtop/updateHighlights" ~params

let textDocumentDidOpen params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let text = textDocument |> member "text" |> to_string in
  create_document (get_init_state ()) text >>= fun document ->
  Hashtbl.add documents uri document;
  send_highlights uri document >>= fun () ->
  publish_diagnostics uri document


let textDocumentDidChange params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let contentChanges = params |> member "contentChanges" |> to_list in
  let read_edit edit =
    let text = edit |> member "text" |> to_string in
    let range = edit |> member "range" in
    let range_start = range |> member "start" |> parse_loc in
    let range_end = range |> member "end" |> parse_loc in
    DocumentManager.({ range_start; range_end }, text)
  in
  let textEdits = List.map read_edit contentChanges in
  let document = Hashtbl.find documents uri in
  let new_doc = DocumentManager.apply_text_edits document textEdits in
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc

let textDocumentDidSave params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let document = Hashtbl.find documents uri in
  DocumentManager.validate_document document >>= fun new_doc ->
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc

let mk_goal sigma g =
  let env = Goal.V82.env sigma g in
  let min_env = Environ.reset_context env in
  let id = Goal.uid g in
  let ccl =
    pr_letype_env ~goal_concl_style:true env sigma (Goal.V82.concl sigma g)
  in
  let mk_hyp d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right Environ.push_named d' env in
    let ids, body, typ = match d with
    | CompactedDecl.LocalAssum (ids, typ) ->
       ids, None, typ
    | CompactedDecl.LocalDef (ids,c,typ) ->
      ids, Some c, typ
    in
  let ids = List.map (fun id -> `String (Names.Id.to_string id.Context.binder_name)) ids in
  let typ = pr_ltype_env env sigma typ in
    let hyp = `Assoc ([
      "identifiers", `List ids;
      "type", `String (Pp.string_of_ppcmds typ);
      "diff", `String "None";
    ] @ Option.cata (fun body -> ["body", `String (Pp.string_of_ppcmds @@ pr_lconstr_env ~inctx:true env sigma body)]) [] body) in
    (env', hyp :: l)
  in
  let (_env, hyps) =
    Context.Compacted.fold mk_hyp
      (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
  `Assoc [
    "id", `Int (int_of_string id);
    "hypotheses", `List (List.rev hyps);
    "goal", `String (Pp.string_of_ppcmds ccl)
  ]

let mk_proofview loc Proof.{ goals; shelf; given_up; sigma } =
  let goals = List.map (mk_goal sigma) goals in
  let shelved = List.map (mk_goal sigma) shelf in
  let given_up = List.map (mk_goal sigma) given_up in
  `Assoc [
    "type", `String "proof-view";
    "goals", `List goals;
    "shelvedGoals", `List shelved;
    "abandonedGoals", `List given_up;
    "focus", mk_loc loc
  ]

let progress_hook uri doc : unit Lwt.t =
  let doc =
    match doc with
    | None -> Hashtbl.find documents uri
    | Some x -> x in
  send_highlights uri doc >>= fun () ->
  publish_diagnostics uri doc

let coqtopInterpretToPoint ~id params : ExecutionManager.events Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let loc = params |> member "location" |> parse_loc in
  let document = Hashtbl.find documents uri in
  let progress_hook = progress_hook uri in
  DocumentManager.interpret_to_position ~progress_hook document loc >>= fun (new_doc, proof, events) ->
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc >>= fun () ->
  match proof with
  | None -> Lwt.return events
  | Some (proofview, pos) ->
    let result = mk_proofview pos proofview in
    output_json @@ mk_response ~id ~result >>= fun () ->
    Lwt.return events

let coqtopStepBackward ~id params : ExecutionManager.events Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let document = Hashtbl.find documents uri in
  DocumentManager.interpret_to_previous document >>= fun (new_doc, proof, events) ->
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc >>= fun () ->
  match proof with
  | None -> Lwt.return events
  | Some (proofview, pos) ->
    let result = mk_proofview pos proofview in
    output_json @@ mk_response ~id ~result >>= fun () ->
    Lwt.return events

let coqtopStepForward ~id params : ExecutionManager.events Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let document = Hashtbl.find documents uri in
  DocumentManager.interpret_to_next document >>= fun (new_doc, proof, events) ->
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc >>= fun () ->
  match proof with
  | None -> Lwt.return events
  | Some (proofview, pos) ->
    let result = mk_proofview pos proofview in
    output_json @@ mk_response ~id ~result >>= fun () ->
    Lwt.return events

let coqtopResetCoq ~id params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let document = Hashtbl.find documents uri in
  DocumentManager.reset (get_init_state ()) document >>= fun new_doc ->
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc

let coqtopInterpretToEnd ~id params : ExecutionManager.events Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let document = Hashtbl.find documents uri in
  let progress_hook = progress_hook uri in
  DocumentManager.interpret_to_end ~progress_hook document >>= fun (new_doc, proof, events) ->
  Hashtbl.replace documents uri new_doc;
  send_highlights uri new_doc >>= fun () ->
  publish_diagnostics uri new_doc >>= fun () ->
  match proof with
  | None -> Lwt.return events
  | Some (proofview, pos) ->
    let result = mk_proofview pos proofview in
    output_json @@ mk_response ~id ~result >>= fun () ->
    Lwt.return events

type lsp_event = Request of Yojson.Basic.t

type event =
 | LspManager of lsp_event
 | ExecutionManager of ExecutionManager.event

type events = event Lwt.t list

let inject_em_event x : event Lwt.t =
  x >>= fun x -> Lwt.return @@ ExecutionManager x

let inject_em_events l =
  Lwt.return @@ List.map inject_em_event l

let dispatch_method ~id method_name params : events Lwt.t =
  let open Lwt.Infix in
  match method_name with
  | "initialize" -> do_initialize ~id >>= fun () -> Lwt.return []
  | "initialized" -> Lwt.return []
  | "textDocument/didOpen" -> textDocumentDidOpen params >>= fun () -> Lwt.return []
  | "textDocument/didChange" -> textDocumentDidChange params >>= fun () -> Lwt.return []
  | "textDocument/didSave" -> textDocumentDidSave params >>= fun () -> Lwt.return []
  | "coqtop/interpretToPoint" -> coqtopInterpretToPoint ~id params >>= inject_em_events
  | "coqtop/stepBackward" -> coqtopStepBackward ~id params  >>= inject_em_events
  | "coqtop/stepForward" -> coqtopStepForward ~id params  >>= inject_em_events
  | "coqtop/resetCoq" -> coqtopResetCoq ~id params >>= fun () -> Lwt.return []
  | "coqtop/interpretToEnd" -> coqtopInterpretToEnd ~id params >>= inject_em_events
  | _ -> log @@ "Ignoring call to unknown method: " ^ method_name; Lwt.return []

let lsp () = [
  read_request Lwt_io.stdin >!= fun req ->
  log "[T] UI req ready";
  Lwt.return @@ LspManager (Request req)
]

let handle_lsp_event = function
  | Request req ->
      let open Yojson.Basic.Util in
      let id = Option.default 0 (req |> member "id" |> to_int_option) in
      let method_name = req |> member "method" |> to_string in
      let params = req |> member "params" in
      log @@ "[T] ui step: " ^ method_name;
      dispatch_method ~id method_name params >>= fun more_events ->
      Lwt.return @@ more_events @ lsp()

let handle_event = function
  | LspManager e -> handle_lsp_event e
  | ExecutionManager e -> ExecutionManager.handle_event e >>= inject_em_events

let init () =
  init_state := Some (Vernacstate.freeze_interp_state ~marshallable:false)


