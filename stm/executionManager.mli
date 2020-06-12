(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The execution manager is in charge of the actual execution of tasks (as
    defined by the scheduler), caching execution states and invalidating
    them. *)

open Scheduler

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

type state
(** Execution state, includes the cache *)

val init : Vernacstate.t -> state

type updater = f:(state -> state Lwt.t) -> unit Lwt.t

val observe : hack:(sentence_id -> ast option) -> update_state:updater -> schedule -> sentence_id -> state -> Proof.data option Lwt.t
val query : sentence_id -> state -> ast -> state

val invalidate : schedule -> sentence_id -> state -> state

val errors : state -> (sentence_id * Loc.t option * string) list
val shift_locs : state -> int -> int -> state
val executed_ids : state -> sentence_id list
val is_executed : state -> sentence_id -> bool

val get_parsing_state_after : state -> sentence_id -> Vernacstate.Parser.state option
