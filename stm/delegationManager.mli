(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type sentence_id = Stateid.t
type link
(* Coqtop module not in scope *)
type ('a,'b) coqtop_extra_args_fn = opts:'b -> string list -> 'a * string list
val write_value : link -> 'a -> unit

module type Job = sig
  type t
  val name : string
  val binary_name : string
  val pool_size : int
end

type execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

type job_id
val cancel_job : job_id -> unit
val mk_job_id : unit -> job_id

module MakeWorker (Job : Job) : sig

(* Event for the main loop *)
type dm
type events = dm Sel.event list

(* handling an even may require an update to a sentence in the exec state *)
val handle_event : dm -> ((sentence_id * execution_status) option * events)
val pr_event : dm -> Pp.t

(* When a worker is available [job] is called and when it returns the
   event becomes ready; in turn the event triggers the action.
   If we can fork, job is passed to fork_action. Things are automatically
   wired up so that all the promises in the mapping are remotely fullfilled.

   Otherwise we create a new process. That process must be a Coq toplevel (see
   Coqtop module) parsing extra argument using [parse_options] then sets up
   a link with master via [setup_plumbing] and finally calls
   [new_process_workers] to setup remote promise fullfillment.
   See ExecutionManager.init_worker *)
val worker_available :
  jobs:((job_id * Job.t) Queue.t) ->
  fork_action:(Job.t -> link -> unit) ->
  events

(* for worker toplevels *)
type options
val parse_options : (options,'b) coqtop_extra_args_fn
(* the sentence ids of the remote_mapping being delegated *)
val setup_plumbing : options -> (link * Job.t)

end
