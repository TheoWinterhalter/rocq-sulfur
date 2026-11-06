From Stdlib Require Import Utf8 List Lia.
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

Lemma nth_map_seq {X} (f : nat → X) n k d :
  k < n →
  nth k (map f (seq 0 n)) d = f k.
Proof.
  intros h.
  rewrite nth_indep with (d' := f 0). 2: rewrite length_map, length_seq. 2: lia.
  rewrite map_nth, seq_nth. 2: lia. reflexivity.
Qed.

Fixpoint Forall_rec [A : Type] (P : A → Prop) l :=
  match l with
  | [] => True
  | [ a ] => P a
  | a :: l => P a ∧ Forall_rec P l
  end.

Fixpoint Forall_rec_alt [A : Type] (P : A → Prop) l :=
  match l with
  | [] => True
  | a :: l => P a ∧ Forall_rec_alt P l
  end.

Lemma Forall_rec_alt_iff A P l :
  @Forall_rec A P l ↔ Forall_rec_alt P l.
Proof.
  split.
  - intros h. induction l as [| a [|b l] ih].
    + constructor.
    + cbn in *. intuition auto.
    + cbn in *. intuition auto.
  - intros h. induction l as [| a [|b l] ih].
    + constructor.
    + cbn in *. intuition auto.
    + cbn in *. intuition auto.
Qed.

Lemma Forall_rec_iff A P l :
  @Forall_rec A P l ↔ Forall P l.
Proof.
  rewrite Forall_rec_alt_iff.
  split.
  - intros h. induction l as [| a l ih].
    + constructor.
    + cbn in h. constructor. all: intuition auto.
  - induction 1 as [| a l ha hl ih].
    + constructor.
    + cbn. intuition auto.
Qed.

(** n-ary (non-dependent) functions

  A pattern we reuse several times in this file.
  [nary n A B] is [A → … → A → B] with [n] times [A].

*)
Fixpoint nary n A B :=
  match n with
  | 0 => B
  | S n => A → nary n A B
  end.

(** n-ary application *)
Fixpoint napply {A B} (f : nat → A) n i : nary n A B → B :=
  match n with
  | 0 => λ b, b
  | S n => λ g, napply f n (S i) (g (f i))
  end.
