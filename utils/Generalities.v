From Stdlib Require Import Utf8 List.
From Stdlib Require Export Morphisms Relations.

Import ListNotations.

Definition eq1 {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (eq1 f g) (at level 75).

Definition eq2 {A B C} : relation (A -> B -> C) := pointwise_relation _ (pointwise_relation _ eq).
Notation "f =₂ g" := (eq2 f g) (at level 75).

Fixpoint comp_n {X : Type} (f : X -> X) (n : nat) (x : X) := match n with
| 0 => x
| S n => f (comp_n f n x)
end.

Lemma fold_impl_iff (Ps : list Prop) (C : Prop) :
  (Forall (λ P, P) Ps → C) ↔ fold_right (λ P Q, P → Q) C Ps.
Proof.
  split.
  - intros h. induction Ps as [| P Ps ih] in h |- *.
    + cbn. eauto using Forall.
    + cbn. eauto using Forall.
  - intros h hF. induction Ps as [| P Ps ih] in h, hF |- *.
    + cbn in h. assumption.
    + cbn in h. inversion hF. eauto.
Qed.
