(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CSig
open Names
open Constr
open Context

type t
(** Type of incomplete terms. Essentially a wrapper around {!Constr.t} ensuring
    that {!Constr.kind} does not observe defined evars. *)

type types = t
type constr = t
type existential = t pexistential
type fixpoint = (t, t) pfixpoint
type cofixpoint = (t, t) pcofixpoint
type unsafe_judgment = (constr, types) Environ.punsafe_judgment
type unsafe_type_judgment = types Environ.punsafe_type_judgment

(** {5 Destructors} *)

val kind : Evd.evar_map -> t -> (t, t) Constr.kind_of_term
(** Same as {!Constr.kind} except that it expands evars and normalizes
    universes on the fly. *)

val to_constr : Evd.evar_map -> t -> Constr.t
(** Returns the evar-normal form of the argument. See {!Evarutil.nf_evar}. *)

(** {5 Constructors} *)

val of_kind : (t, t) Constr.kind_of_term -> t
(** Construct a term from a view. *)

val of_constr : Constr.t -> t
(** Translate a kernel term into an incomplete term in O(1). *)

(** {5 Insensitive primitives}

  Evar-insensitive versions of the corresponding functions. See the {!Constr}
  module for more information.

*)

(** {6 Constructors} *)

val mkRel : int -> t
val mkVar : Id.t -> t
val mkMeta : metavariable -> t
val mkEvar : t pexistential -> t
val mkSort : Sorts.t -> t
val mkProp : t
val mkSet  : t
val mkType : Univ.universe -> t
val mkCast : t * cast_kind * t -> t
val mkProd : Name.t * t * t -> t
val mkLambda : Name.t * t * t -> t
val mkLetIn : Name.t * t * t * t -> t
val mkApp : t * t array -> t
val mkConst : constant -> t
val mkConstU : pconstant -> t
val mkProj : (projection * t) -> t
val mkInd : inductive -> t
val mkIndU : pinductive -> t
val mkConstruct : constructor -> t
val mkConstructU : pconstructor -> t
(* val mkConstructUi : pinductive * int -> t *)
val mkCase : case_info * t * t * t array -> t
val mkFix : (t, t) pfixpoint -> t
val mkCoFix : (t, t) pcofixpoint -> t
val mkArrow : t -> t -> t

val applist : t * t list -> t

val mkProd_or_LetIn : Rel.Declaration.t -> t -> t
val mkLambda_or_LetIn : Rel.Declaration.t -> t -> t
val it_mkProd_or_LetIn : t -> Rel.t -> t
val it_mkLambda_or_LetIn : t -> Rel.t -> t

val mkNamedLambda : Id.t -> types -> constr -> constr
val mkNamedLetIn : Id.t -> constr -> types -> constr -> constr
val mkNamedProd : Id.t -> types -> types -> types
val mkNamedLambda_or_LetIn : Named.Declaration.t -> types -> types
val mkNamedProd_or_LetIn : Named.Declaration.t -> types -> types

(** {6 Simple case analysis} *)

val isRel  : Evd.evar_map -> t -> bool
val isVar  : Evd.evar_map -> t -> bool
val isInd  : Evd.evar_map -> t -> bool
val isEvar : Evd.evar_map -> t -> bool
val isMeta : Evd.evar_map -> t -> bool
val isSort : Evd.evar_map -> t -> bool
val isCast : Evd.evar_map -> t -> bool
val isApp : Evd.evar_map -> t -> bool
val isLambda : Evd.evar_map -> t -> bool
val isLetIn : Evd.evar_map -> t -> bool
val isProd : Evd.evar_map -> t -> bool
val isConst : Evd.evar_map -> t -> bool
val isConstruct : Evd.evar_map -> t -> bool
val isFix : Evd.evar_map -> t -> bool
val isCoFix : Evd.evar_map -> t -> bool
val isCase : Evd.evar_map -> t -> bool
val isProj : Evd.evar_map -> t -> bool
val isArity : Evd.evar_map -> t -> bool
val isVarId  : Evd.evar_map -> Id.t -> t -> bool

val destRel : Evd.evar_map -> t -> int
val destMeta : Evd.evar_map -> t -> metavariable
val destVar : Evd.evar_map -> t -> Id.t
val destSort : Evd.evar_map -> t -> Sorts.t
val destCast : Evd.evar_map -> t -> t * cast_kind * t
val destProd : Evd.evar_map -> t -> Name.t * types * types
val destLambda : Evd.evar_map -> t -> Name.t * types * t
val destLetIn : Evd.evar_map -> t -> Name.t * t * types * t
val destApp : Evd.evar_map -> t -> t * t array
val destConst : Evd.evar_map -> t -> constant puniverses
val destEvar : Evd.evar_map -> t -> t pexistential
val destInd : Evd.evar_map -> t -> inductive puniverses
val destConstruct : Evd.evar_map -> t -> constructor puniverses
val destCase : Evd.evar_map -> t -> case_info * t * t * t array
val destProj : Evd.evar_map -> t -> projection * t
val destFix : Evd.evar_map -> t -> (t, t) pfixpoint
val destCoFix : Evd.evar_map -> t -> (t, t) pcofixpoint

val decompose_app : Evd.evar_map -> t -> t * t list

val decompose_lam : Evd.evar_map -> t -> (Name.t * t) list * t
val decompose_lam_assum : Evd.evar_map -> t -> Context.Rel.t * t
val decompose_lam_n_assum : Evd.evar_map -> int -> t -> Context.Rel.t * t
val decompose_lam_n_decls : Evd.evar_map -> int -> t -> Context.Rel.t * t

val decompose_prod : Evd.evar_map -> t -> (Name.t * t) list * t
val decompose_prod_assum : Evd.evar_map -> t -> Context.Rel.t * t
val decompose_prod_n_assum : Evd.evar_map -> int -> t -> Context.Rel.t * t

val existential_type : Evd.evar_map -> existential -> types

(** {6 Equality} *)

val eq_constr : Evd.evar_map -> t -> t -> bool
val eq_constr_nounivs : Evd.evar_map -> t -> t -> bool
val eq_constr_universes : Evd.evar_map -> t -> t -> Universes.universe_constraints option
val leq_constr_universes : Evd.evar_map -> t -> t -> Universes.universe_constraints option
val eq_constr_universes_proj : Environ.env -> Evd.evar_map -> t -> t -> Universes.universe_constraints option
val compare_constr : Evd.evar_map -> (t -> t -> bool) -> t -> t -> bool

(** {6 Iterators} *)

val map : Evd.evar_map -> (t -> t) -> t -> t
val map_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> t) -> 'a -> t -> t
val iter : Evd.evar_map -> (t -> unit) -> t -> unit
val iter_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> unit) -> 'a -> t -> unit
val iter_with_full_binders : Evd.evar_map -> (Rel.Declaration.t -> 'a -> 'a) -> ('a -> t -> unit) -> 'a -> t -> unit
val fold : Evd.evar_map -> ('a -> t -> 'a) -> 'a -> t -> 'a

(** {6 Substitutions} *)

module Vars :
sig
val lift : int -> t -> t
val liftn : int -> int -> t -> t
val substnl : t list -> int -> t -> t
val substl : t list -> t -> t
val subst1 : t -> t -> t

val replace_vars : (Id.t * t) list -> t -> t
val substn_vars : int -> Id.t list -> t -> t
val subst_vars : Id.t list -> t -> t
val subst_var : Id.t -> t -> t

val noccurn : Evd.evar_map -> int -> t -> bool
val noccur_between : Evd.evar_map -> int -> int -> t -> bool

val closedn : Evd.evar_map -> int -> t -> bool
val closed0 : Evd.evar_map -> t -> bool

val subst_univs_level_constr : Univ.universe_level_subst -> t -> t

end

(** {5 Unsafe operations} *)

module Unsafe :
sig
  val to_constr : t -> Constr.t
  (** Physical identity. Does not care for defined evars. *)

  val eq : (t, Constr.t) eq
  (** Use for transparent cast between types. *)
end