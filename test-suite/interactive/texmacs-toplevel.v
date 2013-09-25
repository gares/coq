Check (1:nat).

Comments 3 (2 + 2) "ciao".

Lemma toto1 : True.

Theorem toto2 : True.

Definition toto3 := 5.

Definition toto4 : nat := 5.

Definition toto5 : nat. exact 3. (* VernacExtend *) Defined.

Fact toto6 : True. exact I. Qed.

Corollary toto7 : True.

Abort All.

Section Toto.

  Variable n : nat.
  Variables m s : nat.

  Hypothesis npos : n > 0.

End Toto.

Notation "a ++ b" := (a + b).

Notation "a +- b" := (a + b) (at level 42).

Notation "a -- b" := (a + b) (at level 42, format "'[v' a -- b ']'").

Notation "a -+- b" := (a + b) (at level 42, right associativity).

Notation mynat := nat.

Reserved Notation "a ** b" (at level 30).

Inductive vect (A : Type) : Type :=
 | Vnil : vect A
 | Vcons : A -> vect A -> vect A.

Record two : Type := BuilTwo { a : nat; b : vect nat }.

Canonical Structure two_example := BuilTwo 3 (Vnil nat).

Definition xxx := BuilTwo 3 (Vnil nat).

Canonical Structure xxx.
