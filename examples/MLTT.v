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
| refl u A :
    (* typing u A *)
    ─────────────────────────────────────
    conv u u A

| beta A (B b : tm → tm) u :
    ─────────────────────────────────────
    conv (tapp (tlam A b) u) (b u) (B u)
| congr_lam (n : nat) A A' (B b b' : tm → tm) :
    conv A A' (tTy n) ;
    ⟨ x : A ⊢ conv (b x) (b' x) (B x) ⟩
    ─────────────────────────────────────
    conv (tlam A b) (tlam A' b') (tPi A B)

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

| type_conv A A' t :
    typing t A ;
    {{ conv (map (λ _, tt) Γ) A A' }}
    ─────────────────────────────────────
    typing t A'.
