Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.
Ltac sleep n :=
  try (assert (fib n = S (fib n)) by reflexivity).
(* Tune that depending on your PC *)
Let time := 19.

Axiom P : nat -> Prop.
Axiom P_triv : Type -> forall x, P x.
Ltac solve_P :=
  match goal with |- P (S ?X) =>
    sleep time; exact (P_triv Type _)
  end.

Lemma test_old x : P (S x) /\ P (S x) /\ P (S x) /\ P (S x).
Proof.
repeat split.
Time all: solve_P.
Qed.

Lemma test_ok x : P (S x) /\ P (S x) /\ P (S x) /\ P (S x).
Proof.
repeat split.
Time all |3| : solve_P.
Qed.

Lemma test_fail x : P (S x) /\ P x /\ P (S x) /\ P (S x).
Proof.
repeat split.
Fail Time all |2| : solve_P.
all: apply (P_triv Type).
Qed.
