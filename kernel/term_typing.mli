(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Univ
open Declarations
open Inductive
open Environ
open Entries
open Typeops

val translate_local_def : env -> identifier -> definition_entry ->
  constant_def * types * constant_constraints

val translate_local_assum : env -> types ->
  types * Univ.constraints

(* returns the same definition_entry but with side effects turned into
 * let-ins or beta redexes. it is meant to get a term out of a not yet
 * type checked proof *)
val handle_side_effects : env -> definition_entry -> definition_entry

val translate_constant : env -> constant -> constant_entry -> constant_body

val translate_mind :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : env -> constant -> Cooking.recipe -> constant_body
