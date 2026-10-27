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

Arguments r_K /.
Arguments r_S /.
Arguments r_app /.
Arguments SK_desc /.
Eval cbn in SK_desc.

(* Actual implementation we want to reach *)

Definition varty := @cinctx term (rename rshift).

Inductive typing Γ : term → term → Prop :=
| ty_var n A :
  varty Γ n A →
  typing Γ (Var n) A

| ty_K A B :
  typing Γ tK (tarr A (tarr B A))

| ty_S A B C :
  typing Γ tS (tarr (tarr A (tarr B C)) (tarr (tarr A B) (tarr A C)))

| ty_app A B t u :
  typing Γ t (tarr A B) → typing Γ u A → typing Γ (tapp t u) B.

(* We can check the rules have the expected types *)

Check (ty_var : var_rule_type typing).
Check (ty_K : ∀ Γ, rule_desc_type typing r_K Γ).
Check (ty_S : ∀ Γ, rule_desc_type typing r_S Γ).
Check (ty_app : ∀ Γ, rule_desc_type typing r_app Γ).

Arguments conc_jdg /.
Arguments nvar /.
Arguments hmvar /.
Eval cbn in (∀ Γ, rule_desc_type typing r_app Γ).

(* We prove the judgments are the same (for now on this specific case) *)

Lemma typing_sound : sound_jdg SK_desc typing.
Proof.
  intros Γ t A h.
  unfold J, Pf. induction h. all: cbn.
  - exact (sound_var SK_desc Γ n A H).
  - exact (sound_step SK_desc r_K Γ ltac:(cbn; auto) eq_refl A B).
  - exact (sound_step SK_desc r_S Γ ltac:(cbn; auto) eq_refl A B C).
  - eapply (sound_step SK_desc r_app Γ ltac:(cbn; auto) eq_refl A B t u).
    all: assumption.
Qed.

Lemma typing_complete : complete_jdg SK_desc typing.
Proof.
  eapply jdg_complete.
  - exact _.
  - exact ty_var.
  - repeat eapply Forall_cons + eapply Forall_nil.
    + exact ty_K.
    + exact ty_S.
    + exact ty_app.
  - reflexivity.
Qed.

Lemma cpreserve_subst Γ Δ t A σ :
  typing Γ t A →
  cstyping typing Δ σ Γ →
  typing Δ (substitute σ t) (substitute σ A).
Proof.
  intros ht hs.
  eapply gen_preserve_subst with (1 := concrete_syntax_laws).
  - eapply typing_sound.
  - eapply typing_complete.
  - eassumption.
  - assumption.
Qed.
