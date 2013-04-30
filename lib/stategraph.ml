(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type state_id = int
let initial_state_id = 1
let dummy_state_id = 0
let fresh_state_id, in_range =
  let cur = ref initial_state_id in
  (fun () -> incr cur; !cur), (fun id -> id >= 0 && id <= !cur)
let string_of_state_id = string_of_int
let state_id_of_int id = assert(in_range id); id
let int_of_state_id id = id

let to_state_id = function
  | Element ("state_id",["val",i],[]) ->
      let id = int_of_string i in
(* If we use this module on both sides, we can't assert that
   assert(in_range id); *)
      id
  | _ -> raise (Invalid_argument "to_state_id")

let of_state_id i = Element ("state_id",["val",string_of_int i],[])

module StateidOrderedType = struct type t = state_id let compare = compare end
module StateidSet : Set.S with type elt = state_id =
  Set.Make(StateidOrderedType)
module StateidMap : Map.S with type key = state_id =
  Map.Make(StateidOrderedType)

exception ErrorReachingState of state_id option * state_id * exn

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

end = struct

   type cluster_id = int
   let string_of_cluster_id = string_of_int

   type 'a graph = 
     (state_id * 'a) list StateidMap.t * (* graph    *)
     (cluster_id) StateidMap.t *         (* clusters *)
     (int) StateidMap.t                  (* reach    *)

   let empty = StateidMap.empty, StateidMap.empty, StateidMap.empty

   let reached (_,_,reached) =
     StateidMap.fold (fun x v l -> if v > 0 then x :: l else l) reached []

   let mem id (graph,_,_) = StateidMap.mem id graph

   let add_edge from trans dest (graph,clusters,reach) =
     let extra = [dest, trans] in
     (try StateidMap.add from (extra @ StateidMap.find from graph) graph
     with Not_found -> StateidMap.add from extra graph),
     clusters,
     reach

   let from_node id (graph,_,_) =
     try StateidMap.find id graph 
     with Not_found -> []

   let remove_node id (graph,clusters,reach) =
     StateidMap.remove id graph,
     (try 
       let clid = StateidMap.find id clusters in
       let nodes = 
         StateidMap.fold (fun k v acc -> if v = clid then k::acc else acc)
         clusters [] in
       List.fold_right StateidMap.remove nodes clusters 
     with Not_found -> clusters),
     StateidMap.remove id reach

   let clid = ref 1
   let create_cluster l (graph,clusters,reach) =
     incr clid;
     graph,
     List.fold_right (fun x -> StateidMap.add x !clid) l clusters,
     reach

   let cluster_of id (_,clusters,_) =
     try Some (StateidMap.find id clusters)
     with Not_found -> None

   let n_reached id (_, _, reach) =
     try StateidMap.find id reach with Not_found -> 0

   let reach id b (graph, clusters, reach as dag) =
     graph,
     clusters,
     (if b then StateidMap.add id (n_reached id dag + 1) reach
     else StateidMap.add id ~-1 reach)

   let iter f (graph, clusters, reach as dag) =
     StateidMap.iter (fun k v ->
        f k (cluster_of k dag) (n_reached k dag) v) graph

   (* very naive *)
   let pointing_to id (graph, _, _) =
     let rec fix s =
       let red = ref s in
       StateidMap.iter (fun id l ->
         if List.exists (fun (tgt,_) -> StateidSet.mem tgt !red) l then
           red := StateidSet.add id !red) graph;
       if StateidSet.equal !red s then s else fix !red
     in
       fix (StateidSet.singleton id)

end

