From Coq.ssr Require Import ssreflect.
From Coq Require Import RelationClasses Relation_Definitions Setoid.

Parameter P : nat -> Prop.
Parameter f : nat -> nat.
Parameter foo_eq : forall x, P x -> x = f x.

Goal 0 = f 0.
Proof.
  rewrite -(foo_eq 0); [ | reflexivity].
Abort.


Parameter R : relation nat.
Parameter R_equivalence : Equivalence R.
#[global] Existing Instance R_equivalence.

Parameter foo_R : forall x, P x -> R x (f x).

Goal R 0 (f 0).
Proof.
  rewrite -(foo_R 0); [ | apply: Equivalence_Reflexive ].
Abort.
