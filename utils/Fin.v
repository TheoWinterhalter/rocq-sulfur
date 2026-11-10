(** This file defines finite sets [fin n] which can be thought of
    as sets [{ 0, 1, 2, ..., n-1 }]. *)

From Equations Require Import Equations.
From Stdlib Require Import Utf8 Bool List.
From Utils Require Import Generalities.

(** Enable reducing constants defined using [Equations]. *)
Set Equations Transparent.

(*********************************************************************************)
(** *** Finite sets. *)
(*********************************************************************************)

(** [fin n] represents the finite set with [n] elements [0], [1], ..., [n-1]. *)
Inductive fin : nat → Type :=
| (** [0] is in [fin n] whenever [n > 0]. *)
  finO {n} : fin (S n)
| (** Injection from [fin n] to [fin (S n)], which maps [i] to [i+1]. *)
  finS {n} : fin n → fin (S n).

Derive Signature NoConfusion NoConfusionHom for fin.

(*********************************************************************************)
(** *** Operations on finite sets. *)
(*********************************************************************************)

(** Coercion from [fin n] to [nat]. *)
Equations fin_to_nat {n} : fin n → nat :=
  fin_to_nat finO := 0 ;
  fin_to_nat (finS i) := S (fin_to_nat i).

(** Boolean equality test on [fin n]. *)
Equations eqb_fin {n} : fin n → fin n → bool :=
  eqb_fin finO finO := true ;
  eqb_fin (finS i) (finS i') := eqb_fin i i' ;
  eqb_fin _ _ := false.

Lemma eqb_fin_spec {n} (i i' : fin n) :
  reflect (i = i') (eqb_fin i i').
Proof.
  funelim (eqb_fin i i').
  - now left.
  - right. intros H. depelim H.
  - right. intros H. depelim H.
  - destruct H. all: subst.
    + now left.
    + right. intros H. apply n. now depelim H.
Qed.

(** Decidable equality on [fin n]. *)
#[export] Instance fin_EqDec n : EqDec (fin n).
Proof.
  intros i i'.
  destruct (eqb_fin_spec i i') ; constructor ; assumption.
Defined.

Lemma eqb_fin_eq {n} (i i' : fin n) :
  eqb_fin i i' = true ↔ i = i'.
Proof.
  symmetry. apply reflect_iff. apply eqb_fin_spec.
Qed.

(*********************************************************************************)
(** *** Enumeration. *)
(*********************************************************************************)

(** [fin_all n] lists the elements of [fin n] in order. *)
Equations fin_all (n : nat) : list (fin n) :=
  fin_all 0 := nil ;
  fin_all (S n) := finO :: map finS (fin_all n).

Lemma In_fin_all {n} (i : fin n) :
  In i (fin_all n).
Proof.
  induction i as [| n i ih].
  - now left.
  - right. now apply in_map.
Qed.

(** A conjunction over every index holds at each. *)
Lemma Forall_rec_fin_all {n} (P : fin n → Prop) :
  Forall_rec P (fin_all n) →
  ∀ i, P i.
Proof.
  intros h i.
  rewrite Forall_rec_iff, Forall_forall in h.
  apply h. apply In_fin_all.
Qed.
