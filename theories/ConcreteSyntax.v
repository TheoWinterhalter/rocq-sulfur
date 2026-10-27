(** Concrete syntax corresponding to a signature *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings.
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

  Class ConcreteSyntax := mkCS {
    cvar : nat → T ;
    crename : ren → T → T ;
    csubstitute : (nat → T) → T → T ;
    ceval : expr Kt → T ;
    creify : T → expr Kt ;
    cctor : ∀ c, cargs (ctor_type c) → T
  }.

End ConcreteSyntax.

Arguments carg {sig}.
Arguments cargs {sig}.
Arguments ckind {sig}.

Arguments cvar {sig T _}.
Arguments crename {sig T _}.
Arguments csubstitute {sig T _}.
Arguments ceval {sig T _}.
Arguments creify {sig T _}.
Arguments cctor {sig T _}.

Abbreviation ctx_rf Γ := (map creify Γ).
Abbreviation jdg_rf j := (creify (fst j), creify (snd j)).

(** Reification and lemmas *)

Section Rf.

  Context {sig : signature} {T : Type} (rf : T → expr Kt).

  Fixpoint rf_arg (a : arg_ty) : carg T a → expr (Ka a) :=
    match a with
    | AT_base b => λ x, E_abase b x
    | AT_term => λ t, E_aterm (rf t)
    | AT_bind a => λ x, E_abind (rf_arg a x)
    end.

  Fixpoint rf_args (l : list arg_ty) : cargs T l → expr (Kal l) :=
    match l with
    | [] => λ _, E_al_nil
    | a :: l => λ '(x, xs), E_al_cons (rf_arg a x) (rf_args l xs)
    end.

  Definition rfk (k : kind) : ckind T k → expr k :=
    match k with
    | Kt => rf
    | Ka a => rf_arg a
    | Kal l => rf_args l
    end.

End Rf.

Section Laws.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  Class ConcreteSyntaxLaws := {
    rf_var : ∀ n, creify (cvar n) = E_var n ;
    rf_rename : ∀ r t, creify (crename r t) = rename r (creify t) ;
    rf_cctor :
      ∀ c args, creify (cctor c args) = E_ctor c (rf_args creify (ctor_type c) args) ;
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

End Laws.

Arguments ConcreteSyntaxLaws {sig T} CS.

Lemma rf_rename_of_ev {sig : signature} {T : Type}
  (rf : T → expr Kt) (ev : expr Kt → T) (ren : ren → T → T)
  (ev_rf : ∀ t, ev (rf t) = t) (rf_ev : ∀ e, rf (ev e) = e)
  (ev_rename : ∀ r e, ev (rename r e) = ren r (ev e)) :
  ∀ r t, rf (ren r t) = rename r (rf t).
Proof.
  intros r t.
  erewrite <- rf_ev. rewrite ev_rename, ev_rf.
  reflexivity.
Qed.

(** Tactics run by [Sulfur Syntax] to derive the instances. *)

Ltac destruct_params :=
  repeat match goal with
  | q : (_ * _)%type |- _ => destruct q
  | q : unit |- _ => destruct q
  end.

(**
  Prove [forall e, reify (eval Kt e) = e], by induction on [e] at every kind.
  [ec] is the generated [eval_ctor].
*)
Ltac derive_rf_ev ec :=
  lazymatch goal with
  | [ |- forall e : @expr ?sg _, ?rf (?ev _ e) = e ] =>
    let H := fresh "H" in
    assert (H : forall c v, rf (ec c v) = @E_ctor sg c (rf_args rf _ v))
      by (let c := fresh "c" in let v := fresh "v" in
          intros c v; destruct c; cbn in v; destruct_params; reflexivity);
    let HH := fresh "HH" in
    enough (forall k (e : @expr sg k), rfk rf k (ev k e) = e) as HH
      by (intro e; exact (HH Kt e));
    let k := fresh "k" in let e := fresh "e" in
    intros k e; induction e; cbn; try rewrite H;
    solve [ reflexivity | f_equal; assumption ]
  end.

(** [ConcreteSyntaxLaws cs] from the generated lemmas. *)
Ltac derive_cs_laws rf_ev ev_rf ev_rename ev_substitute congr_substitute :=
  constructor;
  [ intro; reflexivity
  | exact (rf_rename_of_ev _ _ _ ev_rf rf_ev ev_rename)
  | let c := fresh "c" in let a := fresh "a" in
    intros c a; destruct c; cbn in a; destruct_params; reflexivity
  | exact ev_rf
  | exact rf_ev
  | exact ev_substitute
  | let h := fresh "h" in
    intros ? ? ? h ; apply congr_substitute; [ exact h | reflexivity ]
  ].
