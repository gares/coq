(* -*- mode: coq; coq-prog-args: ("-allow-sprop" "-no-uip") -*- *)

Inductive Istrue : bool -> SProp := istrue : Istrue true.
Check Istrue_rect.

Inductive eqb (b:bool) : bool -> SProp := reflb : eqb b b.
Fail Check eqb_ind. Fail Check eqb_rec. Check eqb_sind.


(* anomaly for stupid reasons *)
(* Fail Inductive paths {A:Type} (a:A) : A -> Set := idpath : paths a a. *)
