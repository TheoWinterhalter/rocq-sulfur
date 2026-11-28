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

Fixpoint length_acc [A : Type] (l : list A) n :=
  match l with
  | [] => n
  | _ :: l => length_acc l (S n)
  end.

Lemma length_acc_length A (l : list A) n :
  length_acc l n = n + length l.
Proof.
  induction l as [| a l ih] in n |- *.
  - cbn. lia.
  - cbn. rewrite ih. lia.
Qed.

(** Variant of [Forall_rec] which behaves better with respect to [constructor] *)
Definition Forall_idx [A : Type] (P : nat → A → Prop) (l : list A) :=
  Forall_rec
    (λ k, match nth_error l k with Some a => P k a | None => True end)
    (seq 0 (length_acc l 0)).

Lemma Forall_idx_nth A P (l : list A) k a :
  Forall_idx P l →
  nth_error l k = Some a →
  P k a.
Proof.
  intros h e.
  unfold Forall_idx in h. rewrite Forall_rec_iff, Forall_forall in h.
  specialize (h k). rewrite e in h. apply h.
  rewrite length_acc_length. apply in_seq. cbn.
  split. 1: lia.
  apply nth_error_Some. rewrite e. discriminate.
Qed.

Lemma nth_error_Some_length [A : Type] (l : list A) n a :
  nth_error l n = Some a →
  n < length l.
Proof.
  rewrite <- nth_error_Some.
  congruence.
Qed.

Lemma nth_error_None_eq [A : Type] (l : list A) n :
  length l ≤ n →
  nth_error l n = None.
Proof.
  apply nth_error_None.
Qed.

Lemma in_ext A (a : A) l l' :
  In a l →
  l = l' →
  In a l'.
Proof.
  congruence.
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
