(** MLTT with "conversion explosion": in an inconsistent 
    context, all terms become convertible to an untyped 
    term tDummy. This is an example that couldn't be 
    handled by the old setup, in which every judgement 
    had its own notion of substitution, as this required 
    showing that conv t t A implied typing t A for all t,A *)

From Stdlib Require Import Utf8.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Sulfur Require Import ConcreteSyntax JdgDesc.

Sulfur Syntax tm :=
| tDummy : tm
| tFalse : tm
| tTy : nat → tm
| tPi : tm → (tm → tm) → tm
| tlam : tm → (tm → tm) → tm
| tapp : tm → tm → tm.

Sulfur Judgment conv : tm → tm → tm → Prop
  with context Γ of tm
  and variable x A ↦ conv x x A
:=
| explosion t a A : 
    typing t tFalse ;
    typing a A
    ────────────────────────────────────
    conv a tDummy A

| beta A (B b : tm → tm) u :
    ────────────────────────────────────
    conv (tapp (tlam A b) u) (b u) (B u)

| cong_Pi (i j : nat) A A' (B B' : tm → tm) :
    conv A A' (tTy i) ;
    ⟨ x ↦ A ⊢ conv (B x) (B' x) (tTy j) ⟩
    ──────────────────────────────────────────
    conv (tPi A B) (tPi A' B') (tTy (max i j))

| cong_lam (n : nat) A A' (B b b' : tm → tm) :
    conv A A' (tTy n) ;
    ⟨ x ↦ A ⊢ conv (b x) (b' x) (B x) ⟩
    ─────────────────────────────────────
    conv (tlam A b) (tlam A' b') (tPi A B)

| cong_app A (B : tm → tm) f f' u u' :
    conv f f' (tPi A B) ;
    conv u u' A
    ─────────────────────────────────────
    conv (tapp f u) (tapp f' u') (B u)

| conv_refl u A :
    typing u A
    ─────────────────────────────────────
    conv u u A

| conv_sym u v A :
    conv u v A
    ─────────────────────────────────────
    conv v u A

| conv_trans u v w A :
    conv u v A ;
    conv v w A
    ─────────────────────────────────────
    conv u w A

with typing : tm → tm → Prop
  with context Γ
  and variable x A ↦ typing x A
:=
| type_False :
    ─────────────────────────────────────
    typing tFalse (tTy 0)

| type_Ty (i : nat) :
    ─────────────────────────────────────
    typing (tTy i) (tTy (S i))

| type_Pi (i j : nat) A (B : tm → tm) :
    typing A (tTy i) ;
    ⟨ x ↦ A ⊢ typing (B x) (tTy j) ⟩
    ─────────────────────────────────────
    typing (tPi A B) (tTy (max i j))

| type_lam (i j : nat) A (B t : tm → tm) :
    typing A (tTy i) ;
    ⟨ x ↦ A ⊢ typing (B x) (tTy j) ⟩ ;
    ⟨ x ↦ A ⊢ typing (t x) (B x) ⟩
    ─────────────────────────────────────
    typing (tlam A t) (tPi A B)

| type_app A (B : tm → tm) f u :
    typing f (tPi A B) ;
    typing u A
    ─────────────────────────────────────
    typing (tapp f u) (B u)

| type_conv (i : nat) A A' t :
    typing t A ;
    conv A A' (tTy i)
    ─────────────────────────────────────
    typing t A'.

Abbreviation ctx := (list tm).

(* Equivalent typing of substitution *)
Inductive styping (Δ : ctx) | (σ : nat → tm) : ctx → Prop :=
| styping_nil : styping σ []
| styping_cons Γ A :
    styping (λ k, σ (S k)) Γ →
    typing Δ (σ 0) (csubstitute (λ k, σ (S k)) A) →
    styping σ (A :: Γ).

Lemma styping_iff Δ σ Γ :
  styping Δ σ Γ ↔ cstyping (conv, (typing, tt)) Δ σ Γ.
Proof.
  split.
  - induction 1. 1: constructor.
    econstructor. 1: eauto.
    cbn. split. 1: constructor. all: auto.
  - induction 1. 1: constructor.
    econstructor. 1: eauto.
    cbn in *. intuition eauto.
Qed.
