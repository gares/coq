Require Import Init.Logic.
Import Logic.

Delimit Scope foo with f.
Bind Scope nat_scope with nat.

(* CProdN *)
Lemma toto1 : forall (n m : list nat), forall (b : bool), n = m.
idtac.
Lemma toto2 : forall (n m : list nat) (b : bool), True.
Lemma toto2 : forall (n : nat) (f : nat -> Prop), f n.
Lemma fail : forall x, x + x = x * x.


(* CCast *)
Lemma toto : (True : Prop).
Lemma toto : (True <: Prop).

(* CLetIn *)
Lemma toto : forall y : nat, let x := y in x = y.

(* CLambda *)
Lemma toto : forall x : nat,
    let f := (fun y : nat => y) in f x = x.

Lemma toto : forall x : nat,
    let f := (fun y => y:nat) in f x = x.

Lemma toto : forall (i j : list nat) (x : nat),
    let f := (fun (n m : list nat) (y : nat) => y) in f i j x = x.

(* CCases *)
Lemma toto : forall x : nat,
    match x as toto return nat with S y => y | O => x end = x - (S O).

Lemma toto : forall x : nat,
    match x with S y | O as y => y end = x - (S O).

Lemma toto : forall x : nat,
    match x return nat with S y => y | O => x end = x - (S O).

Lemma toto : forall x z : nat,
    match x,z with
    | S a, S b => a
    | S c, 0 => c
    | 0, S d => d
    | O, 0 => z
    end = x - (S O).
