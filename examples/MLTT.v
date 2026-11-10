(** MLTT with typed conversion (mutual judgments) *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Sulfur Require Import ConcreteSyntax JdgDesc.

Sulfur Syntax tm :=
| tTy : nat → tm
| tPi : tm → (tm → tm) → tm
| tlam : tm → (tm → tm) → tm
| tapp : tm → tm → tm.

Existing Instance sign.

Sulfur Judgment conv : tm → tm → tm → Prop
  with Γ : tm, Variable x A : conv x x A
:=
| beta A (B b : tm → tm) u :
    ────────────────────────────────────
    conv (tapp (tlam A b) u) (b u) (B u)

| cong_Pi (i j : nat) A A' (B B' : tm → tm) :
    conv A A' (tTy i) ;
    ⟨ x : A ⊢ conv (B x) (B' x) (tTy j) ⟩
    ──────────────────────────────────────────
    conv (tPi A B) (tPi A' B') (tTy (max i j))

| cong_lam (n : nat) A A' (B b b' : tm → tm) :
    conv A A' (tTy n) ;
    ⟨ x : A ⊢ conv (b x) (b' x) (B x) ⟩
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
  with Γ : tm, Variable x A : typing x A
:=
| type_Ty (i : nat) :
    ─────────────────────────────────────
    typing (tTy i) (tTy (S i))

| type_Pi (i j : nat) A (B : tm → tm) :
    typing A (tTy i) ;
    ⟨ x : A ⊢ typing (B x) (tTy j) ⟩
    ─────────────────────────────────────
    typing (tPi A B) (tTy (max i j))

| type_lam (i j : nat) A (B t : tm → tm) :
    typing A (tTy i) ;
    ⟨ x : A ⊢ typing (B x) (tTy j) ⟩ ;
    ⟨ x : A ⊢ typing (t x) (B x) ⟩
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

Instance: conv_obligations.
Proof.
  red.
Admitted.
