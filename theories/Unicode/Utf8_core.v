(* -*- coding:utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)



(* Logic *)
Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "tex" "\forall #1,  .. , #2, #3") : type_scope.
Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "tex" "\exists #1,  .. , #2, #3") : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85,
  right associativity, format "tex" "#1 \vee\ #2") : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80,
  right associativity, format "tex" "#1 \wedge\ #2") : type_scope.
Notation "x → y" := (x -> y) (at level 99, y at level 200,
  right associativity, format "tex" "#1 \rightarrow\ #2"): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95,
  no associativity, format "tex" "#1 \leftrightarrow\ #2"): type_scope.
Notation "¬ x" := (~x) (at level 75,
  right associativity, format "tex" "\neg\ #1") : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70,
  format "tex" "#1 \ne #2") : type_scope.

(* Abstraction *)
Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
   format "tex" "\lambda #1\; .. \;#2.#3").
