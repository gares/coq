(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type state_id
val initial_state_id : state_id
val dummy_state_id : state_id
val fresh_state_id : unit -> state_id
val string_of_state_id : state_id -> string
val state_id_of_int : int -> state_id

module StateidMap : Map.S with type key = state_id
module StateidSet : Set.S with type elt = state_id

exception ErrorReachingState of state_id list * state_id * exn

module Dag : sig

   type 't graph
   type cluster_id
   val string_of_cluster_id : cluster_id -> string
   val empty : 't graph
   val add_edge : state_id -> 't -> state_id -> 't graph -> 't graph
   val remove_node : state_id -> 't graph -> 't graph
   val create_cluster : state_id list -> 't graph -> 't graph
   val from_node : state_id -> 't graph -> (state_id * 't) list
   val mem : state_id -> 't graph -> bool
   val iter : 
     (state_id -> cluster_id option -> int ->
       (state_id * 't) list -> unit) -> 't graph -> unit
   val cluster_of : state_id -> 't graph -> cluster_id option
   val n_reached : state_id -> 't graph -> int
   val reach : state_id -> bool -> 't graph -> 't graph
   val reached : 't graph -> state_id list
   val pointing_to : state_id -> 't graph -> StateidSet.t

end
