(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coq_toplevel

(** Initializer color for output *)

val init_color : Stm.AsyncOpts.stm_opt Coqargs.coqargs_config -> unit

(** Prepare state for interactive loop *)

val init_toploop : Stm.AsyncOpts.stm_opt Coqargs.t -> Vernac.State.t

(** The specific characterization of the coqtop_toplevel *)

type query = PrintTags
type run_mode = Interactive | Query of query | Batch

val coqtop_toplevel : (run_mode,Vernac.State.t,Stm.AsyncOpts.stm_opt) custom_toplevel
