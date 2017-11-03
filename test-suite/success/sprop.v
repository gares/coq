(* -*- mode: coq; coq-prog-args: ("-allow-sprop") -*- *)

Check SProp.

Definition iUnit : SProp := forall A : SProp, A -> A.
Definition itt : iUnit := fun A a => a.

Definition iSquash (A:Type) : SProp
  := forall P : SProp, (A -> P) -> P.
Definition isquash A : A -> iSquash A
  := fun a P f => f a.

Fail Check (fun A : SProp => A : Type).

Lemma foo : Prop.
Proof. pose (fun A : SProp => A : Type). Abort.

(* define evar as product *)
Check (fun (f:(_:SProp)) => f _).

Inductive sBox (A:SProp) : Prop
  := sbox : A -> sBox A.

Set Primitive Projections.
(* Primitive record with all fields in SProp has the eta property of SProp so must be SProp. *)
Record rBox (A:SProp) : Prop
  := rmkbox { runbox : A }.

(* Check that defining as an emulated record worked *)
Check runbox.

(* Check that it doesn't have eta *)
Fail Check (fun (A : SProp) (x : rBox A) => eq_refl : x = @rmkbox _ (@runbox _ x)).
