(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Loc
open Names
open Term
open Sign
open Environ

type evar = existential_key

type evar_body =
  | Evar_empty
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context_val;
  evar_body : evar_body;
  evar_filter : bool list;
  evar_source : Evar_kinds.t located;
  evar_candidates : constr list option;
  evar_extra : Store.t }

type conv_pb = CONV | CUMUL

type evar_constraint = conv_pb * env * constr * constr

module EvarMap : sig
  type t
  val empty : t
  val is_empty : t -> bool
  val has_undefined : t -> bool
  val add : t -> evar -> evar_info -> t
  val add_undefined : t -> evar -> evar_info -> t
  val find : t -> evar -> evar_info
  val find_undefined : t -> evar -> evar_info
  val remove : t -> evar -> t
  val mem : t -> evar -> bool
  val to_list : t -> (evar * evar_info) list
  val undefined_list :  t -> (evar * evar_info) list
  val undefined_evars : t -> t
  val defined_evars : t -> t
  val fold : t -> (evar -> evar_info -> 'a -> 'a) -> 'a -> 'a
  val fold_undefined : t -> (evar -> evar_info -> 'a -> 'a) -> 'a -> 'a
  val map : t -> (evar_info -> evar_info) -> t
  val define : t -> evar -> constr -> t
  val is_evar : t -> evar -> bool
  val is_defined : t -> evar -> bool
  val is_undefined : t -> evar -> bool
  val existential_value : t -> evar * Term.constr array -> Term.constr
  val existential_type : t -> evar * Term.constr array -> Term.constr
  val existential_opt_value : t -> evar * Term.constr array -> Term.constr option
  val progress_evar_map : t -> t -> bool
  val merge : t -> t -> t
  val add_constraints : t -> Univ.constraints -> t
  val universes : t -> Univ.universes
  val universe_level : t -> Univ.UniverseLSet.t
  val set_universe_level : t -> Univ.UniverseLSet.t -> t
end

module ExistentialMap : Map.S with type key = existential_key
module ExistentialSet : Set.S with type elt = existential_key

module Metamap : Map.S with type key = metavariable
module Metaset : Set.S with type elt = metavariable
exception NotInstantiatedEvar

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }
type instance_constraint = IsSuperType | IsSubType | Conv
type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed
type instance_status = instance_constraint * instance_typing_status
type clbinding =
  | Cltyp of name * constr freelisted
  | Clval of name * (constr freelisted * instance_status) * constr freelisted

type evar_map = { evars : EvarMap.t;
      conv_pbs : evar_constraint list;
      last_mods : ExistentialSet.t;
      metas : clbinding Metamap.t }

val empty_evar_map : evar_map

val instantiate_evar : named_context -> constr -> constr list -> constr
