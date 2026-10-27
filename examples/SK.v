(** Test on combinatory logic *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped ConcreteSyntax JdgDesc.
From Utils Require Import Functor.

Sulfur Syntax {{
  term : Type

  tK : term
  tS : term
  tarr : term -> term -> term
  tapp : term -> term -> term
}}.

(* Exports the signature for combinatory calculus *)
Existing Instance sign.

Definition hK := hctor CtK.
Definition hS := hctor CtS.
Definition harrow := hctor Ctarr.
Definition happ := hctor Ctapp.

Definition r_K :=
  hrule "type_K" 2 (λ A B, []) (λ A B, (hK, harrow A (harrow B A))).

Definition r_S :=
  hrule "type_S" 3
    (λ A B C, [])
    (λ A B C, (hS, harrow (harrow A (harrow B C)) (harrow (harrow A B) (harrow A C)))).

Definition r_app :=
  hrule "ty_app" 4
    (λ A B t u, [(t, harrow A B); (u, A)])
    (λ A B t u, (happ t u, B)).

Definition SK_desc : jdg_desc := [
  r_K ;
  r_S ;
  r_app
].

Sulfur Judgment typing SK_desc.

(* The generated inductive, with the variable rule first *)

Print typing.

(* The generated lemmas *)

Check typing_var : var_rule_type typing.
Check type_K : ∀ Γ, rule_desc_type typing r_K Γ.
Check type_S : ∀ Γ, rule_desc_type typing r_S Γ.
Check ty_app : ∀ Γ, rule_desc_type typing r_app Γ.

Check typing_wf : wf_desc SK_desc.
Check typing_rules : rules_type SK_desc typing.
Check typing_sound : sound_jdg SK_desc typing.
Check typing_complete : complete_jdg SK_desc typing.
Check typing_subst :
  ∀ Γ Δ σ t A,
    typing Γ t A →
    cstyping typing Δ σ Γ →
    typing Δ (substitute σ t) (substitute σ A).

Print Assumptions typing_subst.
