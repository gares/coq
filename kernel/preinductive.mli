(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Sorts
open Declarations
open Environ

(** {6 Extracting an inductive type from a construction } *)

(** [find_m*type env sigma c] coerce [c] to an recursive type (I args).
   [find_rectype], [find_inductive] and [find_coinductive]
   respectively accepts any recursive type, only an inductive type and
   only a coinductive type.
   They raise [Not_found] if not convertible to a recursive type. *)

val find_rectype     : env -> types -> pinductive * constr list
val find_inductive   : env -> types -> pinductive * constr list
val find_coinductive : env -> types -> pinductive * constr list

type mind_specif = mutual_inductive_body * one_inductive_body

val inductive_params : mind_specif -> int

val inductive_paramdecls : mutual_inductive_body puniverses -> Context.Rel.t

(** {6 ... } *)
(** Fetching information in the environment about an inductive type.
    Raises [Not_found] if the inductive type is not found. *)
val lookup_mind_specif : env -> inductive -> mind_specif

val instantiate_universes : env -> Context.Rel.t ->
  template_arity -> constr Lazy.t array -> Context.Rel.t * sorts


exception SingletonInductiveBecomesProp of Id.t

val instantiate_inductive_constraints : 
  mutual_inductive_body -> sort_instance -> constraints

val constrained_type_of_inductive : env -> mind_specif puniverses -> types constrained
val constrained_type_of_inductive_knowing_parameters : 
  env -> mind_specif puniverses -> types Lazy.t array -> types constrained

val type_of_inductive : env -> mind_specif puniverses -> types

val type_of_inductive_knowing_parameters : 
  env -> ?polyprop:bool -> mind_specif puniverses -> types Lazy.t array -> types

(** Return type as quoted by the user *)

val constrained_type_of_constructor : pconstructor -> mind_specif -> types constrained
val type_of_constructor : pconstructor -> mind_specif -> types

(** Return constructor types in normal form *)
val arities_of_constructors : pinductive -> mind_specif -> types array

(** Return constructor types in user form *)
val type_of_constructors : pinductive -> mind_specif -> types array

(** Transforms inductive specification into types (in nf) *)
val arities_of_specif : mutual_inductive puniverses -> mind_specif -> types array

(** [type_of_case env (I,args) p c] computes the type
   of the following Cases expression:
      <p>Cases (c :: (I args)) of b1..bn end
 *)
val type_of_case :
  env -> pinductive * constr list -> constr -> constr
    -> types

