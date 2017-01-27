(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type GraphIn =
  sig
    module Level : sig
      type t

      val equal : t -> t -> bool

      (* val compare : t -> t -> int *)

      val is_litteral : t -> bool

      val min : t
      val is_min : t -> bool

      (** Polymorphic universes need to be entered >= Set
          Trunc levels are entered >= HSet *)
      val var_min : t
      val is_var_min : t -> bool

      (** HInf is global max of truncations *)
      val max : t option
      val is_max : t -> bool

      val of_path : Names.DirPath.t -> int -> t

      val to_string : t -> string
      val pr : t -> Pp.std_ppcmds
    end

    module LSet : CSig.SetS with type elt = Level.t
    module LMap : CMap.ExtS with type key = Level.t and module Set := LSet

    type constraint_type = Lt | Le | Eq
    type level_constraint = Level.t * constraint_type * Level.t

    module Constraints : Set.S with type elt = level_constraint

    type explanation = (constraint_type * Level.t) list
    val error_inconsistency : constraint_type -> Level.t -> Level.t -> explanation option -> 'a
  end


module type GraphS =
  sig
    module Input : GraphIn
    open Input

    type t

    val empty : t

    (** [initial] contains the litteral levels. *)
    val initial : t
    val is_initial : t -> bool

    val sort_universes : t -> t

    exception AlreadyDeclared
    val add_level : Level.t -> bool -> t -> t

    val check_constraint : t -> level_constraint -> bool
    val check_constraints : Constraints.t -> t -> bool

    val constraints_of_universes : t -> Constraints.t

    val merge_constraints : Constraints.t -> t -> t
    val enforce_constraint : level_constraint -> t -> t

    val pr : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds

    val dump_universes :
      (constraint_type -> string -> string -> unit) ->
      t -> unit
  end

module Make (Input : GraphIn) : GraphS with module Input := Input
