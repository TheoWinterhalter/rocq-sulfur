(** Concrete syntax corresponding to a signature *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Utils Require Import Functor.

Set Default Goal Selector "!".

Section ConcreteSyntax.

  Context (sig : signature) (T : Type).

  Fixpoint carg (a : arg_ty) : Type :=
    match a with
    | AT_base b => eval_base b
    | AT_term => T
    | AT_bind a => carg a
    end.

  Fixpoint cargs (l : list arg_ty) : Type :=
    match l with
    | [] => unit
    | a :: l => carg a * cargs l
    end.

  Definition ckind (k : kind) : Type :=
    match k with
    | Kt => T
    | Ka a => carg a
    | Kal l => cargs l
    end.

  Class ConcreteSyntax := {
    cvar : nat → T ;
    crename : ren → T → T ;
    ceval : expr Kt → T ;
    creify : T → expr Kt ;
    csubstitute : (nat → T) → T → T ;
    cctor : ∀ c, cargs (ctor_type c) → T
  }.

End ConcreteSyntax.

Arguments carg {sig}.
Arguments cargs {sig}.
Arguments ckind {sig}.

Arguments cvar {sig T _}.
Arguments ceval {sig T _}.
Arguments creify {sig T _}.
Arguments crename {sig T _}.
Arguments csubstitute {sig T _}.
Arguments cctor {sig T _}.

Abbreviation ctx_rf Γ := (map creify Γ).
Abbreviation jdg_rf j := (creify (fst j), creify (snd j)).

(** Reification and lemmas *)

Section Rf.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  Fixpoint rf_arg (a : arg_ty) : carg T a → expr (Ka a) :=
    match a with
    | AT_base b => λ x, E_abase b x
    | AT_term => λ t, E_aterm (creify t)
    | AT_bind a => λ x, E_abind (rf_arg a x)
    end.

  Fixpoint rf_args (l : list arg_ty) : cargs T l → expr (Kal l) :=
    match l with
    | [] => λ _, E_al_nil
    | a :: l => λ '(x, xs), E_al_cons (rf_arg a x) (rf_args l xs)
    end.

  Definition rf (k : kind) : ckind T k → expr k :=
    match k with
    | Kt => creify
    | Ka a => rf_arg a
    | Kal l => rf_args l
    end.

  Class ConcreteSyntaxLaws := {
    rf_var : ∀ n, creify (cvar n) = E_var n ;
    rf_rename : ∀ r t, creify (crename r t) = rename r (creify t) ;
    rf_cctor :
      ∀ c args, creify (cctor c args) = E_ctor c (rf_args (ctor_type c) args) ;
    ev_rf : ∀ t, ceval (creify t) = t ;
    rf_ev : ∀ e, creify (ceval e) = e ;
    ev_substitute :
      ∀ s e, ceval (substitute s e) = csubstitute (λ i, ceval (s i)) (ceval e) ;
    csubstitute_ext : ∀ s s' t, s =₁ s' → csubstitute s t = csubstitute s' t
  }.

  (** Well-formed meta expression

    Meta-variables below [m], applied to no substitution (which [cinst] drops)

  *)
  Fixpoint wf_mexpr (m : nat) {k s} (e : mexpr k s) {struct e} : bool :=
    match e with
    | M_var _ _ _ => true
    | M_ctor _ _ al => wf_mexpr m al
    | M_al_nil _ => true
    | M_al_cons _ a al => wf_mexpr m a && wf_mexpr m al
    | M_abase _ _ _ => true
    | M_aterm _ t => wf_mexpr m t
    | M_abind _ a => wf_mexpr m a
    | M_mvar s k σ =>
      (k <? m) && (s =? 0) && match σ with [] => true | _ => false end
    end.

End Rf.

Arguments ConcreteSyntaxLaws {sig T} CS.
