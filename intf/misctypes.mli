(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** Basic types used both in [constr_expr] and in [glob_constr] *)

(** Cases pattern variables *)

type patvar = Id.t

(** Introduction patterns *)

type 'constr intro_pattern_expr =
  | IntroForthcoming of bool
  | IntroNaming of intro_pattern_naming_expr
  | IntroAction of 'constr intro_pattern_action_expr
and intro_pattern_naming_expr =
  | IntroIdentifier of Id.t
  | IntroFresh of Id.t
  | IntroAnonymous
and 'constr intro_pattern_action_expr =
  | IntroWildcard
  | IntroOrAndPattern of 'constr or_and_intro_pattern_expr
  | IntroInjection of (Loc.t * 'constr intro_pattern_expr) list
  | IntroApplyOn of 'constr * (Loc.t * 'constr intro_pattern_expr)
  | IntroRewrite of bool
and 'constr or_and_intro_pattern_expr =
  | IntroOrPattern of (Loc.t * 'constr intro_pattern_expr) list list
  | IntroAndPattern of (Loc.t * 'constr intro_pattern_expr) list

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

(** Sorts *)

type univ_info = string Loc.located list
type trunc_info = string Loc.located list
type level_info = string Loc.located option
type tlevel_info = string Loc.located option

type glob_univ =
  | GUSet
  | GUAnon
  | GUniv of univ_info

type glob_trunc =
  | GHProp
  | GHSet
  | GHInf
  | GTrunc of trunc_info

type glob_sort =
  | GProp
  | GSet
  | GType of glob_univ * glob_trunc

type glob_instance_univ =
  | GISet
  | GILevel of level_info

type glob_instance_trunc =
  | GIHSet
  | GIHInf
  | GITLevel of tlevel_info

type glob_instance = glob_instance_univ list * glob_instance_trunc list

(** A synonym of [Evar.t], also defined in Term *)

type existential_key = Evar.t

(** Case style, shared with Term *)

type case_style = Term.case_style =
  | LetStyle
  | IfStyle
  | LetPatternStyle
  | MatchStyle
  | RegularStyle (** infer printing form from number of constructor *)

(** Casts *)

type 'a cast_type =
  | CastConv of 'a
  | CastVM of 'a
  | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)
  | CastNative of 'a

(** Bindings *)

type quantified_hypothesis = AnonHyp of int | NamedHyp of Id.t

type 'a explicit_bindings = (Loc.t * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings


(** Some utility types for parsing *)

type 'a or_var =
  | ArgArg of 'a
  | ArgVar of Names.Id.t Loc.located

type 'a and_short_name = 'a * Id.t Loc.located option

type 'a or_by_notation =
  | AN of 'a
  | ByNotation of (Loc.t * string * string option)

(* NB: the last string in [ByNotation] is actually a [Notation.delimiters],
   but this formulation avoids a useless dependency. *)


(** Kinds of modules *)

type module_kind = Module | ModType | ModAny

(** Various flags *)

type direction_flag = bool (* true = Left-to-right    false = right-to-right *)
type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type letin_flag = bool     (* true = use local def    false = use Leibniz *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

type multi =
  | Precisely of int
  | UpTo of int
  | RepeatStar
  | RepeatPlus

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of Id.t Loc.located
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

type inversion_kind =
  | SimpleInversion
  | FullInversion
  | FullInversionClear
