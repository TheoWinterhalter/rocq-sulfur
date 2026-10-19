From Sulfur Require Import Prelude.

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** A renaming on terms is a function [nat -> nat] which is applied
    to all free variables. *)
Definition ren := nat -> nat.

(** The identity renaming. *)
Definition rid : ren := fun i => i.

(** [rshift] shifts indices by one. *)
Definition rshift : ren := fun i => S i.

(** Cons an index with a renaming. *)
Equations rcons (i0 : nat) (r : ren) : ren :=
rcons i0 _ 0 := i0 ;
rcons i0 r (S i) := r i.

(** Compose two renamings (left to right composition). *)
Equations rcomp (r1 r2 : ren) : ren :=
rcomp r1 r2 i := r2 (r1 i).

(** Lift a renaming through a binder. *)
Equations up_ren (r : ren) : ren :=
up_ren r := rcons 0 (rcomp r rshift).

Lemma up_ren_proper (r1 r2 : ren) :
  r1 =₁ r2 -> up_ren r1 =₁ up_ren r2.
Proof.
  intros Hr [|i]; simpl. reflexivity.
  unfold rcomp, rshift. f_equal. apply Hr.
Qed.

(* Eval compute in (fun ρ => up_ren ρ 1). *)

Equations up_rens (k : nat) (ρ : ren) : ren :=
up_rens 0 ρ := ρ ;
up_rens (S k) ρ := up_ren (up_rens k ρ).

Lemma up_rens_lt (i k : nat) (ρ : ren) :
  i < k -> up_rens k ρ i = i.
Proof.
  intro. induction k in i, H |- *; simpl.
  - lia.
  - destruct i as [|i]. simpl. reflexivity.
    simpl. unfold rcomp, rshift. f_equal. apply IHk. lia.
Qed.

Lemma up_rens_gt (i k : nat) (ρ : ren) :
  i >= k -> up_rens k ρ i = (ρ (i - k)) + k.
Proof.
  induction k in i |- *; intros; simpl.
  - transitivity (ρ (i - 0)). 2: lia. assert (i = i - 0) by lia. rewrite H0 at 1. reflexivity.
  - destruct i as [|i]; simpl. lia.
    unfold rcomp, rshift. rewrite IHk; lia.
Qed.

Lemma up_rens_add n m ρ :
  up_rens n (up_rens m ρ) =₁ up_rens (n + m) ρ.
Proof.
  induction n; simpl. reflexivity.
  apply up_ren_proper. assumption.
Qed.
(*********************************************************************************)
(** *** Trivial properties of renamings. *)
(*********************************************************************************)

(** Pointwise equality for functions. *)
(* Definition eq1 {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (eq1 f g) (at level 75). *)

Lemma eq1_refl {A B} {x : A -> B} : x =₁ x.
Proof. reflexivity. Qed.

Lemma eq1_sym {A B} {x y : A -> B} : x =₁ y -> y =₁ x.
Proof. now intros ->. Qed.

Lemma eq1_trans {A B} {x y z : A -> B} : x =₁ y -> y =₁ z -> x =₁ z.
Proof. now intros -> ->. Qed.

Lemma congr_rcons i {r r'} :
  r =₁ r' -> rcons i r =₁ rcons i r'.
Proof. intros H [|i'] ; [reflexivity|]. now simp rcons. Qed.

Lemma congr_rcomp {r1 r1' r2 r2'} :
  r1 =₁ r1' -> r2 =₁ r2' -> rcomp r1 r2 =₁ rcomp r1' r2'.
Proof. intros H1 H2 i. simp rcomp. now rewrite H1, H2. Qed.

Lemma congr_up_ren {r r'} :
  r =₁ r' -> up_ren r =₁ up_ren r'.
Proof. intros H. simp up_ren. apply congr_rcons. now apply congr_rcomp. Qed.

Lemma up_ren_comp r1 r2 :
  rcomp (up_ren r1) (up_ren r2) =₁ up_ren (rcomp r1 r2).
Proof.
  intros [|n]; unfold rcomp; reflexivity.
Qed.

Lemma up_rens_comp k r1 r2 :
  rcomp (up_rens k r1) (up_rens k r2) =₁ up_rens k (rcomp r1 r2).
Proof.
  induction k in r1, r2 |- *; intro n; simpl.
  - reflexivity.
  - rewrite up_ren_comp. apply congr_up_ren.
    apply IHk.
Qed.