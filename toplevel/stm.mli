(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* XXX this function should be a ref set by vernacentries *)
type perform =
  ?proof:Proof_global.closed_proof -> Vernacexpr.vernac_expr -> unit

val process_transaction : perform -> Vernacexpr.vernac_expr -> unit
val finish : perform -> unit
val observe : perform -> Stategraph.state_id -> unit
val join : unit -> unit

val get_checked_states : unit -> Stategraph.state_id list
val get_current_state : unit -> Stategraph.state_id
val current_proof_depth : unit -> int
val get_all_proof_names : unit -> Names.identifier list
val get_current_proof_name : unit -> Names.identifier option

val get_script : Names.identifier -> (Vernacexpr.vernac_expr * int) list


