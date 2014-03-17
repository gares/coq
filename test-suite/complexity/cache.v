
Fixpoint fact n :=
  match n with
  | O => O
  | S m => n * fact m
  end.

Definition m := 600.
Definition n := m * 18.

(* Tests type checking *)
Lemma test1 x : fact n - fact n = 0 * x.
Proof.
check_and_cache (vm_cast_no_check (eq_refl 0)).
Timeout 1 Qed.

(* Tests vlosure.ml reduction *)
Lemma test2 x : fact m - fact m = 0 * x.
Proof.
lazy.
reflexivity.
Timeout 1 Qed.

(* Tests vnorm.ml reduction *)
Lemma test3 x : fact n - fact n = 0 * x.
Proof.
vm_compute.
reflexivity.
Timeout 1 Qed.

(* Tests with some env pollution *)
Lemma test4 x (y : bool) :
  fact n - fact n = 0 * x /\
  fact m - fact m = 0 * x /\
  False.
Proof.
pose (T := Type).
pose (w := 0).
split.
  clear y.
  check_and_cache (vm_cast_no_check (eq_refl 0)).
split.
  lazy.
  clear y.
  reflexivity.
admit.
Timeout 1 Qed.
