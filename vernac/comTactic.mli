(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Entry point for toplevel tactic expression execution *)
val solve :
  pstate:Declare.Proof.t ->
  Goal_select.t ->
  info:int option ->
  unit Proofview.tactic ->
  with_end_tac:bool ->
  Declare.Proof.t

(** Entry point when the goal selector is par:
    Since Proofview.tactic is not marshalable we also pass the AST *)
val solve_parallel :
  pstate:Declare.Proof.t ->
  info:int option ->
  ast:Vernacexpr.vernac_expr ->
  unit Proofview.tactic ->
  solve:bool ->
  abstract:bool ->
  with_end_tac:bool ->
  (Declare.Proof.t * Declare.Proof.events) CLwt.t

(** By default par: is implemented with all: (sequential).
    The STM and LSP document manager provide "more parallel" implementations *)
val par_implementation : (
  pstate:Declare.Proof.t ->
  info:int option ->
  ast:Vernacexpr.vernac_expr ->
  unit Proofview.tactic ->
  solve:bool ->
  abstract:bool ->
  with_end_tac:bool ->
  (Declare.Proof.t * Declare.Proof.events) CLwt.t
  ) ref
