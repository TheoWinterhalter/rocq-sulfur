(** Judgment description

  The purpose is to describe a family of judgments that can be turned into
  a judgment signature.
  A description is the output of the [Sulfur Judgment] command and thus refers
  to concrete syntax rather than only the syntax signature like judgment
  signatures.
  This justifies this intermediary module.

*)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Utils Require Import Functor.

(** Judgment description over a signature *)

Section Desc.

  Context {sig : signature}.

  (* For now, judgments involve two terms and that's it *)
  Definition mjdgd sc : Type :=
    (mexpr Kt sc * mexpr Kt sc).

  Record rule_desc := {
    rd_name : string ;
    rd_mvars : nat ;
    rd_premises : list (mjdgd 0) ;
    rd_conclusion : mjdgd 0
  }.

  Definition jdg_desc :=
    list rule_desc.

End Desc.

(** Judgment signature from a description *)

Section ToSig.

  Context {sig : signature}.

  (* For now we assume only one judgment *)
  Definition I := unit.

  (* Contexts only store terms *)
  #[local] Instance: IDecl I :=
    λ _ X, X.

  (* Context judgment has to be typing *)
  #[local] Instance: IJdg I :=
    λ _ X, (X * X)%type.

  Definition to_rule (rd : rule_desc) : rule tt := {|
    param  := unit ;
    premises := λ _, map (λ j, prem_ind tt (λ X x, x) mnil j) rd.(rd_premises) ;
    conclusion := λ _, rd.(rd_conclusion)
  |}.

  (* Somehow, universe issues prevent using List.map directly *)
  Fixpoint to_rules (rs : list rule_desc) : list (rule tt) :=
    match rs with
    | [] => []
    | rd :: rs => to_rule rd :: to_rules rs
    end.

  Definition to_jdg_sig (d : jdg_desc) : jdg_sig := {|
    rules := λ 'tt, to_rules d
  |}.

  Lemma in_to_rules r rs :
    In r (to_rules rs) →
    ∃ rd, In rd rs ∧ r = to_rule rd.
  Proof.
    intros h.
    induction rs as [| rd rs ih] in h |- *.
    1: contradiction.
    cbn in h. destruct h as [h | h].
    - exists rd. cbn. intuition auto.
    - destruct (ih h) as [rd' ihd].
      exists rd'. cbn. intuition auto.
  Qed.

  Lemma in_to_rules_intro rd rs :
    In rd rs →
    In (to_rule rd) (to_rules rs).
  Proof.
    induction rs as [| rd' rs ih]. 1: contradiction.
    intros [-> | h]. all: cbn. all: auto.
  Qed.

End ToSig.

#[local] Instance Sig_IDecl : IDecl I := λ _ X, X.
#[local] Instance Sig_IJdg : IJdg I := λ _ X, (X * X)%type.
#[local] Instance Sig_FMapDecl : ∀ i : I, FMap (declF i) := λ _, FMapId.
#[local] Instance Sig_FMapJdg : ∀ i : I, FMap (jdgF i) := λ _, FMapProd _ _.
#[local] Instance Sig_FuncDecl : ∀ i : I, Eq1Functor (declF i) := λ _, FId.
#[local] Instance Sig_FuncJdg : ∀ i : I, Eq1Functor (jdgF i) := λ _, Eq1FProd _ _.
#[local] Instance Sig_IMakeJdg : IMakeJdg I := λ _ X d x, (x, d).
#[local] Instance Sig_NatMake : ∀ i : I, NatFromProd (make_jdg i).
Proof. intro i. constructor. reflexivity. Qed.

(** Higher-order presentation of rules

  Meta-variables are abstracted as functions.

*)

Section HOAS.

  Context {sig : signature}.

  (* When adding support for binders, make it ∀ s, mexpr Kt s *)
  Definition hterm := mexpr Kt 0.

  (* Meta-variable [k], arity [0] *)
  Definition hmvar (k : mvar) := M_mvar 0 k [].

  (* For now not supporting binders *)
  Definition harg (a : arg_ty) :=
    match a with
    | AT_base b => eval_base b
    | AT_term => hterm
    | AT_bind a => (* harg a *) False
    end.

  Fixpoint curry (l : list arg_ty) :=
    match l with
    | [] => hterm
    | a :: l => harg a → curry l
    end.

  Definition harg_inst (a : arg_ty) : harg a → mexpr (Ka a) 0 :=
    match a with
    | AT_base b => λ x, M_abase _ _ x
    | AT_term => λ t, M_aterm _ t
    | AT_bind a => False_rect _ (* λ x, M_abind _ (harg_inst a x) *)
    end.

  Fixpoint hctor_aux (l : list arg_ty) : (mexpr (Kal l) 0 → hterm) → curry l :=
    match l with
    | [] => λ f, f (M_al_nil _)
    | a :: l => λ f x, hctor_aux l (λ al, f (M_al_cons _ (harg_inst _ x) al))
    end.

  (* Constructor applied to its arguments *)
  Definition hctor (c : ctor) : curry (ctor_type c) :=
    hctor_aux _ (M_ctor _ c).

  Fixpoint hfun n R :=
    match n with
    | 0 => R
    | S n => hterm → hfun n R
    end.

  (* Apply an [hfun] to meta-variables starting from [k] *)
  Fixpoint happly {R} n (k : mvar) : hfun n R → R :=
    match n with
    | 0 => λ x, x
    | S n => λ f, happly n (S k) (f (hmvar k))
    end.

  Definition hrule name n pr concl : rule_desc := {|
    rd_name := name ;
    rd_mvars := n ;
    rd_premises := happly n 0 pr ;
    rd_conclusion := happly n 0 concl
  |}.

End HOAS.

(** Concrete syntax corresponding to a signature *)

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
Arguments cctor {sig T _}.

Abbreviation ctx_rf Γ := (map creify Γ).
Abbreviation jdg_rf j := (creify (fst j), creify (snd j)).

(** Generic lemmas *)

Section Lemmas.

  Context {sig : signature}.

  (* [inst m (M_mvar 0 k [])] unfolds to a substitution by this identity. *)
  Lemma subst_nil_id (t : expr Kt) :
    ParamSyntax.substitute
      (λ i, match nth_error [] i with Some t => t | None => E_var (i - 0 + 0) end)
      t
    = t.
  Proof.
    etransitivity. 2: apply subst_sid.
    apply substitute_proper. 2: reflexivity.
    intro i. unfold ParamSyntax.sid.
    destruct i. all: cbn. all: f_equal.
    lia.
  Qed.

End Lemmas.

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
    rf_rename : ∀ r t, creify (crename r t) = ParamSyntax.rename r (creify t) ;
    rf_cctor :
      ∀ c args, creify (cctor c args) = E_ctor c (rf_args (ctor_type c) args)
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
      Nat.ltb k m && Nat.eqb s 0 && match σ with [] => true | _ => false end
    end.

End Rf.

Arguments ConcreteSyntaxLaws {sig T} CS.

(** Instantiate mexpr to concrete syntax *)

Section Inst.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  Context (ι : mvar → T).

  Fixpoint cinst {k s} (e : mexpr k s) {struct e} : ckind T k :=
    match e with
    | M_var _ i h => cvar i
    | M_ctor _ c args => cctor c (cinst args)
    | M_al_nil _ => tt
    | M_al_cons _ ty tys => (cinst ty, cinst tys)
    | M_abase _ b x => x
    | M_aterm _ t => cinst t
    | M_abind _ a => cinst a
    | M_mvar s k σ => ι k (* TODO Fix σ which is dropped *)
    end.

End Inst.

(** Computing the types of concrete constructors *)

Section ConcreteJdg.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  (* The concrete judgment being defined (specialised to binary case) *)
  Context (J : list T → T → T → Prop).

  Definition conc_jdg (Γ : list T) (ι : mvar → T) (j : mjdgd 0) : Prop :=
    J Γ (cinst ι (fst j)) (cinst ι (snd j)).

  (** [∀ x1 ... xn, K [x1; ...; xn]]. *)
  Fixpoint under (n : nat) (ms : list T) (K : list T → Prop) : Prop :=
    match n with
    | 0 => K (rev ms)
    | S n => ∀ x, under n (x :: ms) K
    end.

  Definition dummy : T :=
    cvar 0.

  Definition nvar (vs : list T) :=
    λ i, nth i vs dummy.

  Definition rule_desc_type (rd : rule_desc) (Γ : list T) : Prop :=
    under rd.(rd_mvars) [] (λ vs,
      fold_right
        (λ P Q, P → Q)
        (conc_jdg Γ (nvar vs) rd.(rd_conclusion))
        (map (conc_jdg Γ (nvar vs)) rd.(rd_premises))
    ).

  Inductive cinctx (sh : T → T) : list T → nat → T → Prop :=
  | cin_head d Γ : cinctx sh (d :: Γ) 0 (sh d)
  | cin_tail d d' Γ n : cinctx sh Γ n d → cinctx sh (d' :: Γ) (S n) (sh d).

  Definition var_rule_type :=
    ∀ Γ n A, cinctx (crename rshift) Γ n A → J Γ (cvar n) A.

  Lemma under_intro n ms K :
    (∀ vs, List.length vs = n → K (rev ms ++ vs)) →
    under n ms K.
  Proof.
    intros h.
    induction n as [| n ih] in ms, K, h |- *.
    - cbn.
      specialize h with (vs := []) (1 := eq_refl).
      rewrite app_nil_r in h. assumption.
    - cbn. intros x.
      apply ih. intros vs hvs.
      cbn. rewrite <- app_assoc. cbn. apply h.
      cbn. lia.
  Qed.

End ConcreteJdg.

(** Deriving theorems for concrete syntax and judgments *)

Section ConcreteFacts.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.
  Context (desc : jdg_desc).

  Lemma subst_sig : SubstJSig (to_jdg_sig desc).
  Proof.
    constructor.
    - intros [] r x P hr hP. cbn in hr.
      apply in_to_rules in hr as [rd [hr ->]].
      cbn in hP. rewrite in_map_iff in hP.
      destruct hP as (j & hj & ?). discriminate.
    - intros [] r x P hr hP. cbn in hr.
      apply in_to_rules in hr as [rd [hr ->]].
      cbn in hP. rewrite in_map_iff in hP.
      destruct hP as (j & hj & ?). discriminate.
    - intros [] r x hr n i' conv Δ j hP. cbn in hr.
      apply in_to_rules in hr as [rd [hr ->]].
      cbn in hP. rewrite in_map_iff in hP.
      destruct hP as (j' & hj' & ?). noconf hj'.
      intros X Y f d. reflexivity.
    - intros [] r x hr n i' conv Δ j hP. cbn in hr.
      apply in_to_rules in hr as [rd [hr ->]].
      cbn in hP. rewrite in_map_iff in hP.
      destruct hP as (j' & hj & ?). noconf hj.
      intros Γ d t h.
      rewrite map_id. assumption.
  Qed.

  (* Soundness of rules *)

  Definition Pf Γ j :=
    proof (jsig := to_jdg_sig desc) tt (ctx_rf Γ) (jdg_rf j).

  Definition J Γ t A :=
    Pf Γ (t, A).

  Context {CL : ConcreteSyntaxLaws CS}.

  Lemma rf_cinst ι m k s (e : mexpr k s) :
    wf_mexpr m e = true →
    rf k (cinst ι e) = inst (λ k _, creify (ι k)) e.
  Proof.
    revert k s e.
    apply (
      mexpr_ind (λ k s e,
        wf_mexpr m e = true → rf k (cinst ι e) = inst (λ k _, creify (ι k)) e
      )
    ).
    - intros. apply rf_var.
    - intros. cbn. rewrite rf_cctor. f_equal. auto.
    - intros. reflexivity.
    - intros s ty tys a al ha hal h.
      cbn in h. rewrite andb_true_iff in h. destruct h as [ea eal].
      cbn. f_equal. all: eauto.
    - reflexivity.
    - cbn. intros s t ht h. rewrite ht. all: eauto.
    - cbn. intros s ty a hty h. rewrite hty. all: eauto.
    - intros s k σ hσ h. cbn - [Nat.ltb] in h.
      rewrite andb_true_iff in h. destruct h as [h eσ].
      destruct σ. 2: discriminate.
      rewrite andb_true_iff in h. destruct h as [hkm e].
      rewrite PeanoNat.Nat.ltb_lt in hkm.
      rewrite PeanoNat.Nat.eqb_eq in e. subst.
      cbn. rewrite subst_nil_id.
      reflexivity.
  Qed.

  Lemma rf_cinst_t ι m s (e : mexpr Kt s) :
    wf_mexpr m e = true →
    creify (cinst ι e) = inst (λ k _, creify (ι k)) e.
  Proof.
    apply rf_cinst.
  Qed.

  Lemma cinctx_inctx Γ n A :
    cinctx (crename rshift) Γ n A →
    @inctx sig (declF tt) _ (map creify Γ) n (creify A).
  Proof.
    induction 1 as [d Γ | d d' Γ n h ih].
    - cbn. eapply conv_in_d. 1: econstructor.
      rewrite rf_rename. reflexivity.
    - cbn. eapply conv_in_d. 1:{ econstructor. eassumption. }
      rewrite rf_rename. reflexivity.
  Qed.

  Lemma sound_var : var_rule_type J.
  Proof.
    intros Γ n a h.
    unfold J, Pf. cbn. rewrite rf_var.
    eapply conv_proof_j.
    + eapply tvar. eapply cinctx_inctx. eassumption.
    + reflexivity.
  Qed.

  Definition wf_jdg m (j : mjdgd 0) :=
    wf_mexpr m (fst j) && wf_mexpr m (snd j).

  Definition wf_rule rd :=
    forallb (wf_jdg rd.(rd_mvars)) rd.(rd_premises) &&
    wf_jdg rd.(rd_mvars) rd.(rd_conclusion)
    = true.

  Lemma sound_step rd Γ :
    In rd desc →
    wf_rule rd →
    rule_desc_type J rd Γ.
  Proof.
    intros h hwf.
    red in hwf. unfold wf_jdg in hwf. rewrite !andb_true_iff in hwf.
    destruct hwf as (hwp & hwt & hwA).
    apply under_intro. intros vs hvs. cbn.
    rewrite <- fold_impl_iff. intros hF.
    rewrite Forall_map in hF.
    unfold conc_jdg, J, Pf. cbn.
    erewrite 2!rf_cinst_t. 2,3: eassumption.
    eapply conv_proof_j.
    - eapply step with (r := to_rule rd) (m := λ k _, creify (nvar vs k)) (x := tt).
      + apply in_to_rules_intro. assumption.
      + intros i' n Δ j conv hin. cbn in hin.
        rewrite in_map_iff in hin. destruct hin as [[t A] [hj hj']]. noconf hj.
        cbn. rewrite map_id.
        rewrite Forall_forall in hF. specialize (hF _ hj').
        rewrite forallb_forall in hwp. specialize (hwp _ hj').
        apply andb_prop in hwp as [].
        unfold conc_jdg, J, Pf in hF. cbn in hF.
        erewrite 2!rf_cinst_t in hF. 2,3: eassumption.
        exact hF.
      + intros P hin. cbn in hin.
        rewrite in_map_iff in hin. destruct hin as [j' [hj _]].
        discriminate hj.
    - cbn. destruct (rd_conclusion rd). reflexivity.
  Qed.

End ConcreteFacts.

(** Test on combinatory logic *)

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

#[local] Instance term_cs : ConcreteSyntax sign term := {|
  cvar := Var ;
  crename := rename ;
  ceval := eval Kt ;
  creify := reify ;
  cctor := λ c,
    match c return cargs term (ctor_type c) → term with
    | CtK => λ _, tK
    | CtS => λ _, tS
    | Ctarr => λ '(A, (B, tt)), tarr A B
    | Ctapp => λ '(t, (u, tt)), tapp t u
    end
|}.

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

Definition PfSK := Pf SK_desc.

Lemma reify_rename r t :
  reify (rename r t) = ParamSyntax.rename r (reify t).
Proof.
  induction t in r |- *.
  all: cbn. all: try reflexivity.
  all: congruence.
Qed.

#[local] Instance term_cl : ConcreteSyntaxLaws term_cs.
Proof.
  constructor.
  - reflexivity.
  - apply reify_rename.
  - intros c args. destruct c. all: cbn in args.
    all:
      repeat match type of args with
      | (_ * _)%type => destruct args as [? args]
      | unit => destruct args
      end.
    all: reflexivity.
Qed.

Definition to_menv l : menv :=
  λ k _, nth k (map reify l) (E_var 0).

Lemma typing_sound Γ t A :
  typing Γ t A →
  PfSK Γ (t, A).
Proof.
  unfold Pf. induction 1. all: cbn.
  - exact (sound_var SK_desc Γ n A H).
  - exact (sound_step SK_desc r_K Γ ltac:(cbn; auto) eq_refl A B).
  - exact (sound_step SK_desc r_S Γ ltac:(cbn; auto) eq_refl A B C).
  - eapply (sound_step SK_desc r_app Γ ltac:(cbn; auto) eq_refl A B t u).
    all: assumption.
Qed.

Lemma inctx_cinctx Γ n d :
  @inctx sign (declF tt) _ Γ n d →
  cinctx (crename rshift) (map (eval Kt) Γ) n (eval Kt d).
Proof.
  induction 1 as [d Γ | d d' Γ n h ih].
  all: cbn. all: unfold fmap, Sig_FMapDecl, FMapId.
  all: rewrite eval_rename.
  - constructor.
  - constructor. assumption.
Qed.

Lemma typing_complete Γ j :
  proof (jsig := to_jdg_sig SK_desc) tt Γ j →
  typing (map (eval Kt) Γ) (eval Kt (fst j)) (eval Kt (snd j)).
Proof.
  induction 1 as [ [] m Γ r x hin hind ihind hpred | [] Γ n d hd].
  - cbn in hin. destruct hin as [ <- | [ <- | [ <- | [] ] ] ].
    all: cbn. all: rewrite !(subst_nil_id (sig := sign)).
    1,2: econstructor.
    cbn in ihind.
    pose proof (ihind tt 0 mnil _ (λ X x, x) (or_introl eq_refl)) as h1.
    pose proof (ihind tt 0 mnil _ (λ X x, x) (or_intror (or_introl eq_refl))) as h2.
    cbn in h1, h2.
    rewrite !(subst_nil_id (sig := sign)) in h1.
    rewrite !(subst_nil_id (sig := sign)) in h2.
    rewrite map_id in h1, h2.
    econstructor ; eassumption.
  - cbn. econstructor.
    apply inctx_cinctx.
    assumption.
Qed.

Lemma reify_substitute σ t :
  reify (substitute σ t) = ParamSyntax.substitute (λ i, reify (σ i)) (reify t).
Proof.
  induction t in σ |- *.
  all: cbn. all: try reflexivity.
  all: rewrite IHt1, IHt2. all: reflexivity.
Qed.

Inductive cstyping : list term → (nat → term) → list term → Prop :=
| cstyping_nil Δ σ : cstyping Δ σ []
| cstyping_cons Δ σ Γ d :
    cstyping Δ (λ k, σ (S k)) Γ →
    typing Δ (σ 0) (substitute (λ k, σ (S k)) d) →
    cstyping Δ σ (d :: Γ).

Lemma cstyping_styping Δ σ Γ :
  cstyping Δ σ Γ →
  styping (jsig := to_jdg_sig SK_desc) tt (map reify Δ) (λ k, reify (σ k)) (map reify Γ).
Proof.
  induction 1 as [Δ σ | Δ σ Γ d h ih hd]. all: cbn.
  - constructor.
  - constructor. 1: exact ih.
    apply typing_sound in hd. unfold PfSK, Pf in hd. cbn in hd.
    rewrite reify_substitute in hd. exact hd.
Qed.

Lemma subst_sig_SK : SubstJSig (to_jdg_sig SK_desc).
Proof.
  apply subst_sig.
Qed.

Lemma cpreserve_subst Γ Δ t A σ :
  typing Γ t A →
  cstyping Δ σ Γ →
  typing Δ (substitute σ t) (substitute σ A).
Proof.
  intros ht hs.
  apply typing_sound in ht.
  apply cstyping_styping in hs.
  eapply (preserve_subst (HSubstSig := subst_sig_SK)) in ht. 2: eassumption.
  apply typing_complete in ht.
  rewrite map_map in ht.
  erewrite map_ext, map_id in ht. 2: apply eval_reify_inv.
  cbv beta iota delta [substitute_jdg fmap Sig_FMapJdg FMapProd FMapId fst snd] in ht.
  rewrite !eval_substitute, !eval_reify_inv in ht.
  erewrite 2!(congr_substitute (seval (λ k, reify (σ k))) σ) in ht.
  1: exact ht.
  all: try reflexivity.
  all: intro i. all: unfold seval. all: apply eval_reify_inv.
Qed.
