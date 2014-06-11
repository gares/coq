(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** These are the notations whose level and associativity are imposed by Coq *)

(** Notations for propositional connectives *)

Reserved Notation "x -> y"  (at level 99, right associativity, y at level 200, format "tex" "#1 \rightarrow\ #2").
Reserved Notation "x <-> y" (at level 95, no associativity,    format "tex" "#1 \leftrightarrow\ #2").
Reserved Notation "x /\ y"  (at level 80, right associativity, format "tex" "#1 \wedge\ #2").
Reserved Notation "x \/ y"  (at level 85, right associativity, format "tex" "#1 \vee\ #2").
Reserved Notation "~ x"     (at level 75, right associativity, format "tex" "\neg\ #1").

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity, format "tex" "#1 = #2").
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level, format "tex" "#1 = #2 = #3").

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity, format "tex" "#1 \ne #2").

Reserved Notation "x <= y" (at level 70, no associativity, format "tex" "#1 \le #2").
Reserved Notation "x < y"  (at level 70, no associativity, format "tex" "#1  <  #2").
Reserved Notation "x >= y" (at level 70, no associativity, format "tex" "#1 \ge #2").
Reserved Notation "x > y"  (at level 70, no associativity, format "tex" "#1  >  #2").

Reserved Notation "x <= y <= z" (at level 70, y at next level, format "tex" "#1  \le #2 \le #3").
Reserved Notation "x <= y < z"  (at level 70, y at next level, format "tex" "#1  \le #2  <  #3").
Reserved Notation "x < y < z"   (at level 70, y at next level, format "tex" "#1   <  #2  <  #3").
Reserved Notation "x < y <= z"  (at level 70, y at next level, format "tex" "#1   <  #2 \le #3").

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity,  format "tex" "#1 + #2").
Reserved Notation "x - y" (at level 50, left associativity,  format "tex" "#1 - #2").
Reserved Notation "x * y" (at level 40, left associativity,  format "tex" "#1 * #2").
Reserved Notation "x / y" (at level 40, left associativity,  format "tex" "#1 / #2").
Reserved Notation "- x"   (at level 35, right associativity, format "tex"    "- #1").
Reserved Notation "/ x"   (at level 35, right associativity, format "tex"    "/ #1").
Reserved Notation "x ^ y" (at level 30, right associativity, format "tex" "#1 ^ #2").

(** Notations for booleans *)

Reserved Notation "x || y" (at level 50, left associativity, format "tex" "#1 || #2").
Reserved Notation "x && y" (at level 40, left associativity, format "tex" "#1 \&\& #2").

(** Notations for pairs *)

Reserved Notation "( x , y , .. , z )" (at level 0, format "tex" "\left(#1, #2,  .. , #3\right)").

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level than "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ x  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P  & Q }" (at level 0, x at level 99).

Delimit Scope type_scope with type.
Delimit Scope core_scope with core.

Open Scope core_scope.
Open Scope type_scope.

(** ML Tactic Notations *)

Declare ML Module "coretactics".
Declare ML Module "extratactics".
Declare ML Module "eauto".
Declare ML Module "g_class".
Declare ML Module "g_eqdecide".
Declare ML Module "g_rewrite".
Declare ML Module "tauto".
