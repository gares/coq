(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
   Document Manager independent notion of document and its initialization.

   Initialization is still by side effect, hence a multi document toplevel
   needs to save/restore the system state before/after calling this API.
 *)

type interactive_top = TopLogical of Names.DirPath.t | TopPhysical of string

(** The kind of document we are dealing with. Note that a document manager can
   only deal with a subset, eg only interactive *)
type doc_type =
  | VoDoc       of string       (* file path *)
  | VioDoc      of string       (* file path *)
  | Interactive of interactive_top    (* module path | file path *)

type option_command = OptionSet of string option | OptionUnset

type injection_command =
  | OptionInjection of (Goptions.option_name * option_command)
  (** Set flags or options before the initial state is ready. *)
  | RequireInjection of (string * string option * bool option)
  (** Require libraries before the initial state is
     ready. Parameters follow [Library], that is to say,
     [lib,prefix,import_export] means require library [lib] from
     optional [prefix] and [import_export] if [Some false/Some true]
     is used.  *)
  (* -load-vernac-source interleaving is not supported yet *)
  (* | LoadInjection of (string * bool) *)

(** document initialization options: *)
type 'manager_opts doc_init_options =
  { doc_type : doc_type
  (** The document type *)

  ; ml_load_path : CUnix.physical_path list
  (** OCaml load paths for the document. *)

  ; vo_load_path   : Loadpath.vo_path list
  (** [vo] load paths for the document. Usually extracted from -R
     options / _CoqProject *)

  ; injections : injection_command list
  (** Injects Require and Set/Unset commands before the initial
     state is ready *)

  ; document_manager_options  : 'manager_opts
  (** Low-level document manager options *)
  }

(** Starts the current libary (as in [Declaremods.start_library]), handling
    options [-set ...], [-R], [-I] and [-R] and loding the prelude. Returns
    the logical path of the current document *)
val init_document : 'a doc_init_options -> Names.DirPath.t
