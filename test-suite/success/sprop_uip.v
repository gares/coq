(* -*- mode: coq; coq-prog-args: ("-allow-sprop" "-uip") -*- *)

Set Warnings "+bad-relevance".

(** Case inversion, conversion and universe polymorphism. *)
Set Universe Polymorphism.
Inductive IsTy@{i j} : Type@{j} -> SProp :=
  isty : IsTy Type@{i}.

Definition IsTy_rec_red@{i j+} (P:forall T : Type@{j}, IsTy@{i j} T -> Set)
           v (e:IsTy@{i j} Type@{i})
  : IsTy_rec P v _ e = v
  := eq_refl.


(** Identity! Currently we have UIP. *)
Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.

Definition transport {A} (P:A -> Type) {x y} (e:seq x y) (v:P x) : P y :=
  match e with
    srefl _ => v
  end.

Definition transport_refl {A} (P:A -> Type) {x} (e:seq x x) v
  : transport P e v = v
  := @eq_refl (P x) v.

Definition id_unit (x : unit) := x.
Definition transport_refl_id {A} (P : A -> Type) {x : A} (u : P x)
  : P (transport (fun _ => A) (srefl _ : seq (id_unit tt) tt) x)
  := u.

(** We don't ALWAYS reduce (this uses a constant transport so that the
    equation is well-typed) *)
Fail Definition transport_block A B (x y:A) (e:seq x y) v
  : transport (fun _ => B) e v = v
  := @eq_refl B v.

Inductive sBox (A:SProp) : Prop
  := sbox : A -> sBox A.

Definition transport_refl_box (A:SProp) P (x y:A) (e:seq (sbox A x) (sbox A y)) v
  : transport P e v = v
  := eq_refl.

(** TODO add tests for binders which aren't lambda. *)
Definition transport_box :=
  Eval lazy in (fun (A:SProp) P (x y:A) (e:seq (sbox A x) (sbox A y)) v =>
                  transport P e v).

Lemma transport_box_ok : transport_box = fun A P x y e v => v.
Proof.
  unfold transport_box.
  match goal with |- ?x = ?x => reflexivity end.
Qed.

(** Play with UIP *)
Lemma of_seq {A:Type} {x y:A} (p:seq x y) : x = y.
Proof.
  destruct p. reflexivity.
Defined.

Lemma to_seq {A:Type} {x y:A} (p: x = y) : seq x y.
Proof.
  destruct p. reflexivity.
Defined.

Lemma eq_srec (A:Type) (x y:A) (P:x=y->Type) : (forall e : seq x y, P (of_seq e)) -> forall e, P e.
Proof.
  intros H e. destruct e.
  apply (H (srefl _)).
Defined.

Lemma K : forall {A x} (p:x=x:>A), p = eq_refl.
Proof.
  intros A x. apply eq_srec. intros;reflexivity.
Defined.

Definition K_refl : forall {A x}, @K A x eq_refl = eq_refl
  := fun A x => eq_refl.

Section funext.

  Variable sfunext : forall {A B} (f g : A -> B), (forall x, seq (f x) (g x)) -> seq f g.

  Lemma funext {A B} (f g : A -> B) (H:forall x, (f x) = (g x)) : f = g.
  Proof.
    apply of_seq,sfunext;intros x;apply to_seq,H.
  Defined.

  Definition funext_refl A B (f : A -> B) : funext f f (fun x => eq_refl) = eq_refl
    := eq_refl.
End funext.
