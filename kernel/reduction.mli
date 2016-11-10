(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Environ

(***********************************************************************
  s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int

type 'a kernel_conversion_function = env -> 'a -> 'a -> unit
type 'a extended_conversion_function = 
  ?l2r:bool -> ?reds:Names.transparent_state -> env ->
  ?evars:(evar_closures * UGraph.t) ->
  'a -> 'a -> unit

type conv_pb = CONV | CUMUL

type 'a universe_compare = 
  { (* Might raise NotConvertible or UnivInconsistency *)
    compare : env -> conv_pb -> sorts -> sorts -> 'a -> 'a;
    compare_instances: flex:bool -> 
		       Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a;
  } 

type 'a universe_state = 'a * 'a universe_compare

type ('a,'b) generic_conversion_function = env -> 'b universe_state -> 'a -> 'a -> 'b

type 'a infer_conversion_function = env -> UGraph.t -> 'a -> 'a -> Univ.constraints

val sort_cmp_universes : env -> conv_pb -> sorts -> sorts ->
  'a * 'a universe_compare -> 'a * 'a universe_compare

(* [flex] should be true for constants, false for inductive types and
constructors. *)
val convert_instances : flex:bool -> Univ.Instance.t -> Univ.Instance.t ->
  'a * 'a universe_compare -> 'a * 'a universe_compare

(** These two never raise UnivInconsistency, inferred_universes
    just gathers the constraints. *)
val checked_universes : UGraph.t universe_compare
val inferred_universes : (UGraph.t * Univ.Constraint.t) universe_compare

(** These two functions can only raise NotConvertible *)
val conv : constr extended_conversion_function

val conv_leq : types extended_conversion_function

(** These conversion functions are used by module subtyping, which needs to infer
    universe constraints inside the kernel *)
val infer_conv : ?l2r:bool -> ?evars:evar_closures -> 
  ?ts:Names.transparent_state -> constr infer_conversion_function
val infer_conv_leq : ?l2r:bool -> ?evars:evar_closures -> 
  ?ts:Names.transparent_state -> types infer_conversion_function

(** Depending on the universe state functions, this might raise
  [UniverseInconsistency] in addition to [NotConvertible] (for better error
  messages). *)
val generic_conv : conv_pb -> l2r:bool -> evar_closures ->
  Names.transparent_state -> (constr,'a) generic_conversion_function

(** option for conversion *)
val set_vm_conv : (conv_pb -> types kernel_conversion_function) -> unit
val vm_conv : conv_pb -> types kernel_conversion_function

val default_conv     : conv_pb -> ?l2r:bool -> types kernel_conversion_function
val default_conv_leq : ?l2r:bool -> types kernel_conversion_function

val warn_bytecode_compiler_failed : ?loc:Loc.t -> unit -> unit
