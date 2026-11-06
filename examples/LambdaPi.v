(** λΠ-calculus (sorta) *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Sulfur Require Import ConcreteSyntax JdgDesc.

Sulfur Syntax {{
  tm : Type

  | tTy : nat → tm
  | tPi : tm → (tm → tm) → tm
  | tlam : tm → (tm → tm) → tm
  | tapp : tm → tm → tm
}}.

Existing Instance sign.

Sulfur Judgment conv : tm → tm → Prop
  with Γ : unit, Variable x A : conv x x
{{
| beta A (b : tm → tm) u :
    ⟹ conv (tapp (tlam A b) u) (b u)
| congr_lam A A' (b b' : tm → tm) :
    conv A A' ;
    ⟨ x : tt ⊢ conv (b x) (b' x) ⟩
    ⟹ conv (tlam A b) (tlam A' b')
}}.

Sulfur Judgment typing : tm → tm → Prop
  with Γ : tm, Variable x A : typing x A
{{
| type_Ty (i : nat) :
    ⟹ typing (tTy i) (tTy (S i))

| type_Pi (i j : nat) A (B : tm → tm) :
    typing A (tTy i) ;
    ⟨ x : A ⊢ typing (B x) (tTy j) ⟩
    ⟹ typing (tPi A B) (tTy (max i j))

| type_lam (i j : nat) A (B t : tm → tm) :
    typing A (tTy i) ;
    ⟨ x : A ⊢ typing (B x) (tTy j) ⟩ ;
    ⟨ x : A ⊢ typing (t x) (B x) ⟩
    ⟹ typing (tlam A t) (tPi A B)

| type_app A (B : tm → tm) f u :
    typing f (tPi A B) ;
    typing u A
    ⟹ typing (tapp f u) (B u)

| type_conv A A' t :
    typing t A ;
    {{ conv (map (λ _, tt) Γ) A A' }}
    ⟹ typing t A'
}}.

(* Needed for the substitution lemma, currently false *)
#[local] Instance: typing_obligations.
Proof.
  red.
  intros A A' t Γ Δ σ hs hA.
  eapply conv_subst. 1: eassumption.
  clear - hs. induction hs.
  - constructor.
  - constructor. 1: auto.
    cbn. (* Would need conv_refl but that's ok *)
Admitted.
