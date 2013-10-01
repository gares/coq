
Lemma toto1 : forall (n m : list nat), forall (b : bool), n = m.
Lemma toto2 : forall (n m : list nat) (b : bool), True.
Lemma toto2 : forall (n : nat) (f : nat -> Prop), f n.
Lemma fail : forall x, x + x = x * x.