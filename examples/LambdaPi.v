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

Sulfur Judgment conv {{
| beta A (b : tm → tm) u :
    ⟹ conv (tapp (tlam A b) u) (b u)
| congr_lam A A' (b b' : tm → tm) :
    conv A A' ;
    ⟨ x : A ⊢ conv (b x) (b' x) ⟩
    ⟹ conv (tlam A b) (tlam A' b')
}}.

Sulfur Judgment typing {{
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
    {{ conv Γ A A' }}
    ⟹ typing t A'
}}.

Print typing_desc.
Print typing.

Check typing_wf : wf_desc typing_desc.
Check typing_rules : rules_type typing_desc typing.
Check typing_sound : sound_jdg typing_desc typing.
Check typing_complete : complete_jdg typing_desc typing.
Check typing_subst.

Print Assumptions typing_subst.
