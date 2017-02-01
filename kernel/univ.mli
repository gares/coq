(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universes. *)

module Level :
sig
  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. *)

  val set : t
  val prop : t
  (** The set and prop universe levels. *)

  val is_small : t -> bool
  (** Is the universe set or prop? *)

  val apart : t -> t -> bool
  (** Are the universes different litterals? *)
		       
  val is_prop : t -> bool
  val is_set : t -> bool
  (** Is it specifically Prop or Set *)
		       
  val compare : t -> t -> int
  (** Comparison function *)
  val natural_compare : t -> t -> int
  (** For sorting in [ContextSet.to_context] *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int
  val hcons : t -> t

  val make : Names.DirPath.t -> int -> t
  (** Create a new universe level from a unique identifier and an associated
      module path. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option
end

type universe_level = Level.t
(** Alias name. *)

(** Sets of universe levels *)
module USet :
sig 
  include CSig.SetS with type elt = universe_level
	      
  val pr : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val of_array : Level.t array -> t
end

type universe_set = USet.t

module Universe :
sig
  module Expr : sig
    type t = Level.t * int
    val equal : t -> t -> bool
    val leq : t -> t -> bool
  end

  type t
  (** Type of universes. A universe is defined as a set of level expressions.
      A level expression is built from levels and successors of level expressions, i.e.:
      le ::= l + n, n \in N.

      A universe is said atomic if it consists of a single level expression with
      no increment, and algebraic otherwise (think the least upper bound of a set of
      level expressions).
  *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function on formal universes *)

  val hash : t -> int
  (** Hash function *)

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val pr_with : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds

  val is_level : t -> bool
  (** Test if the universe is a level or an algebraic universe. *)

  val is_levels : t -> bool
  (** Test if the universe is a lub of levels or contains +n's. *)

  val level : t -> Level.t option
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  val levels : t -> USet.t
  (** Get the levels inside the universe, forgetting about increments *)

  val super : t -> t
  (** The universe strictly above *)
    
  val sup   : t -> t -> t
  (** The l.u.b. of 2 universes *)

  val type0m : t  
  (** image of Prop in the universes hierarchy *)
  
  val type0 : t  
  (** image of Set in the universes hierarchy *)
  
  val type1 : t 
  (** the universe of the type of Prop/Set *)

  val fold : (Expr.t -> 'a -> 'a) -> t -> 'a -> 'a

  val exists : (Expr.t -> bool) -> t -> bool
  val for_all : (Expr.t -> bool) -> t -> bool
end

type universe = Universe.t

(** Alias name. *)

val pr_uni : universe -> Pp.std_ppcmds
	      
(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ... 
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)
val type0m_univ : universe
val type0_univ : universe
val type1_univ : universe

val is_type0_univ : universe -> bool
val is_type0m_univ : universe -> bool
val is_univ_variable : universe -> bool
val is_small_univ : universe -> bool

val sup : universe -> universe -> universe
val super : universe -> universe

val universe_level : universe -> universe_level option

(** [univ_level_mem l u] Is l is mentionned in u ? *)

val univ_level_mem : universe_level -> universe -> bool

(** [univ_level_rem u v min] removes [u] from [v], resulting in [min]
    if [v] was exactly [u]. *)

val univ_level_rem : universe_level -> universe -> universe -> universe

(** {6 Support for universe polymorphism } *)

(** Polymorphic maps from universe levels to 'a *)
module UMap :
sig
  include CMap.ExtS with type key = universe_level and module Set := USet

  val union : 'a t -> 'a t -> 'a t
  (** [union x y] favors the bindings in the first map. *)

  val diff : 'a t -> 'a t -> 'a t
  (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

  val subst_union : 'a option t -> 'a option t -> 'a option t
  (** [subst_union x y] favors the bindings of the first map that are [Some],
      otherwise takes y's bindings. *)

  val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
  (** Pretty-printing *)
end

type 'a universe_map = 'a UMap.t

(** {6 Substitution} *)

type universe_subst_fn = universe_level -> universe
type universe_level_subst_fn = universe_level -> universe_level

(** A full substitution, might involve algebraic universes *)
type universe_subst = universe universe_map
type universe_level_subst = universe_level universe_map

val univ_level_subst_of : universe_subst_fn -> universe_level_subst_fn

val empty_univ_level_subst : universe_level_subst
val is_empty_univ_level_subst : universe_level_subst -> bool

(** Substitution of universes. *)
val subst_univs_level_level : universe_level_subst -> universe_level -> universe_level
val subst_univs_level_universe : universe_level_subst -> universe -> universe
val subst_univs_level_universe_fn : universe_level_subst_fn -> universe -> universe

(** Level to universe substitutions. *)

val empty_univ_subst : universe_subst
val is_empty_univ_subst : universe_subst -> bool
val make_univ_subst : universe_subst -> universe_subst_fn

val subst_univs_universe : universe_subst_fn -> universe -> universe

(** {6 Pretty-printing of universes. } *)

val pr_universe_level_subst : universe_level_subst -> Pp.std_ppcmds
val pr_universe_subst : universe_subst -> Pp.std_ppcmds

(** {6 Hash-consing } *)

val hcons_univ : universe -> universe
val hcons_universe_set : universe_set -> universe_set
