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
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped ConcreteSyntax.
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

  Lemma under_iff n ms K :
    (∀ vs, List.length vs = n → K (rev ms ++ vs)) ↔ under n ms K.
  Proof.
    split.
    - intros h.
      induction n as [| n ih] in ms, K, h |- *.
      + cbn.
        specialize h with (vs := []) (1 := eq_refl).
        rewrite app_nil_r in h. assumption.
      + cbn. intros x.
        apply ih. intros vs hvs.
        cbn. rewrite <- app_assoc. cbn. apply h.
        cbn. lia.
    - intros h vs hl.
      induction n as [| n ih] in ms, K, h, vs, hl |- *.
      + cbn in h. destruct vs. 2: discriminate.
        rewrite app_nil_r. assumption.
      + cbn in h. destruct vs as [| v vs]. 1: discriminate.
        cbn in hl. injection hl as e.
        specialize (h v). eapply ih in h. 2: eassumption.
        cbn in h. rewrite <- app_assoc in h. assumption.
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
    rfk creify k (cinst ι e) = inst (λ k _, creify (ι k)) e.
  Proof.
    revert k s e.
    apply (
      mexpr_ind (λ k s e,
        wf_mexpr m e = true → rfk creify k (cinst ι e) = inst (λ k _, creify (ι k)) e
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
    wf_jdg rd.(rd_mvars) rd.(rd_conclusion).

  Definition wf_desc :=
    forallb wf_rule desc.

  Lemma wf_desc_rule rd :
    wf_desc →
    In rd desc →
    wf_rule rd.
  Proof.
    intros h hin.
    unfold wf_desc in h. unfold is_true in h.
    rewrite forallb_forall in h. auto.
  Qed.

  Lemma sound_step rd Γ :
    In rd desc →
    wf_rule rd →
    rule_desc_type J rd Γ.
  Proof.
    intros h hwf.
    red in hwf. unfold wf_rule, wf_jdg in hwf. rewrite !andb_true_iff in hwf.
    destruct hwf as (hwp & hwt & hwA).
    red. rewrite <- under_iff. intros vs hvs. cbn.
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

  (** Statements about a concrete judgment *)

  Section Statements.

    Context (R : list T → T → T → Prop).

    Definition rules_type :=
      var_rule_type R ∧
      ∀ rd, In rd desc → ∀ Γ, rule_desc_type R rd Γ.

    Definition sound_jdg :=
      ∀ Γ t A, R Γ t A → J Γ t A.

    Definition complete_jdg :=
      ∀ Γ j,
        proof (jsig := to_jdg_sig desc) tt Γ j →
        R (map ceval Γ) (ceval (fst j)) (ceval (snd j)).

    (* [σ] is a well-typed substitution from [Δ] to [Γ] *)
    Inductive cstyping : list T → (nat → T) → list T → Prop :=
    | cstyping_nil Δ σ : cstyping Δ σ []
    | cstyping_cons Δ σ Γ d :
        cstyping Δ (λ k, σ (S k)) Γ →
        R Δ (σ 0) (csubstitute (λ k, σ (S k)) d) →
        cstyping Δ σ (d :: Γ).

    Definition preserve_subst_jdg :=
      ∀ Γ Δ σ t A,
        R Γ t A → cstyping Δ σ Γ → R Δ (csubstitute σ t) (csubstitute σ A).

  End Statements.

  (** Completeness against an abstract "concrete" judgment *)

  Lemma ev_var n : ceval (E_var n) = cvar n.
  Proof.
    rewrite <- rf_var. apply ev_rf.
  Qed.

  Lemma ev_rename r e : ceval (ParamSyntax.rename r e) = crename r (ceval e).
  Proof.
    rewrite <- (rf_ev e) at 1. rewrite <- rf_rename. apply ev_rf.
  Qed.

  Lemma rf_substitute σ t :
    creify (csubstitute σ t) = substitute (λ i, creify (σ i)) (creify t).
  Proof.
    erewrite <- rf_ev.
    rewrite ev_substitute, ev_rf. f_equal.
    apply csubstitute_ext. intro i. rewrite ev_rf. reflexivity.
  Qed.

  Lemma inst_ext_wf m (me me' : menv) k s (e : mexpr k s) :
    (∀ k, k < m → me k 0 = me' k 0) →
    wf_mexpr m e = true →
    inst me e = inst me' e.
  Proof.
    intros hme. revert k s e.
    apply (mexpr_ind (λ k s e, wf_mexpr m e = true → inst me e = inst me' e)).
    - intros. reflexivity.
    - intros s c al ih h. cbn in h. cbn. f_equal. auto.
    - intros. reflexivity.
    - intros s ty tys a al ha hal h.
      cbn in h. rewrite andb_true_iff in h. destruct h as [ea eal].
      cbn. f_equal. all: auto.
    - intros. reflexivity.
    - intros s t ih h. cbn in h. cbn. f_equal. auto.
    - intros s ty a ih h. cbn in h. cbn. f_equal. auto.
    - intros s k σ ih h. cbn - ["<?"] in h.
      destruct σ. 2: rewrite andb_false_r in h. 2: discriminate.
      rewrite !andb_true_iff in h. destruct h as [[hk _] _].
      rewrite PeanoNat.Nat.ltb_lt in hk.
      cbn. rewrite hme. 2: assumption.
      reflexivity.
  Qed.

  Definition ev_vs m (me : menv) : list T :=
    map (λ k, ceval (me k 0)) (seq 0 m).

  Lemma ev_vs_length m me :
    List.length (ev_vs m me) = m.
  Proof.
    unfold ev_vs.
    rewrite length_map, length_seq.
    reflexivity.
  Qed.

  Definition ev_vals m me :=
    nvar (ev_vs m me).

  Lemma ev_inst m me s (e : mexpr Kt s) :
    wf_mexpr m e = true →
    ceval (inst me e) = cinst (ev_vals m me) e.
  Proof.
    intros h.
    rewrite <- ev_rf.
    erewrite rf_cinst_t. 2: eassumption.
    f_equal. eapply inst_ext_wf. 2: eassumption.
    intros k hk.
    unfold ev_vals, ev_vs, nvar.
    rewrite nth_map_seq. 2: assumption.
    rewrite rf_ev. reflexivity.
  Qed.

  Lemma inctx_cinctx Γ n d :
    @inctx sig (declF tt) _ Γ n d →
    cinctx (crename rshift) (map ceval Γ) n (ceval d).
  Proof.
    induction 1 as [d Γ | d d' Γ n h ih].
    all: cbn. all: unfold fmap, Sig_FMapDecl, FMapId.
    all: rewrite ev_rename.
    - constructor.
    - constructor. assumption.
  Qed.

  Section Completeness.

    Context (R : list T → T → T → Prop).
    Context (hvar : var_rule_type R).
    Context (hrules : ∀ rd, In rd desc → ∀ Γ, rule_desc_type R rd Γ).
    Context (hwf : wf_desc).

    Theorem jdg_complete : complete_jdg R.
    Proof.
      intros Γ j.
      induction 1 as [[] me Γ r x hin hind ih hpred | [] Γ n d hd].
      - cbn in hin. apply in_to_rules in hin as (rd & hin & ->).
        eapply wf_desc_rule in hwf. 2: exact hin.
        specialize (hrules _ hin (map ceval Γ)).
        unfold is_true, wf_rule, wf_jdg in hwf. rewrite !andb_true_iff in hwf.
        destruct hwf as (hwp & hwt & hwA).
        destruct rd as [name m prems [t A]]. cbn in *.
        rewrite <- under_iff in hrules.
        specialize hrules with (1 := ev_vs_length m me).
        rewrite <- fold_impl_iff in hrules. cbn in hrules.
        unfold conc_jdg in hrules. cbn in hrules.
        unfold fmap, FMapId.
        erewrite !ev_inst. 2,3: eassumption.
        apply hrules.
        rewrite Forall_map, Forall_forall.
        intros [t' A'] hj'. cbn.
        rewrite forallb_forall in hwp. specialize (hwp _ hj'). cbn in hwp.
        rewrite andb_true_iff in hwp. destruct hwp as [hwt' hwA'].
        specialize (ih tt 0 mnil (t', A') (λ X x, x)).
        specialize ih with (1 := in_map (λ j, prem_ind tt (λ X x, x) mnil j) _ _ hj').
        cbn in ih. unfold fmap, FMapId in ih. rewrite map_id in ih.
        rewrite 2!(ev_inst m me) in ih. 2,3: assumption.
        exact ih.
      - cbn. rewrite ev_var.
        apply hvar. apply inctx_cinctx. assumption.
    Qed.

  End Completeness.

  (** Preservation of substitution from soundness and completeness *)

  Section Preservation.

    Context (R : list T → T → T → Prop).
    Context (hsound : sound_jdg R).
    Context (hcomplete : complete_jdg R).

    Lemma cstyping_styping Δ σ Γ :
      cstyping R Δ σ Γ →
      styping (jsig := to_jdg_sig desc) tt (ctx_rf Δ) (λ k, creify (σ k)) (ctx_rf Γ).
    Proof.
      induction 1 as [Δ σ | Δ σ Γ d h ih hd].
      - constructor.
      - cbn. constructor. 1: exact ih.
        apply hsound in hd. unfold J, Pf in hd. cbn in hd.
        rewrite rf_substitute in hd. exact hd.
    Qed.

    Theorem gen_preserve_subst : preserve_subst_jdg R.
    Proof.
      intros Γ Δ σ t A ht hs.
      apply hsound in ht. unfold J, Pf in ht.
      apply cstyping_styping in hs.
      eapply (preserve_subst (HSubstSig := subst_sig)) in ht. 2: eassumption.
      apply hcomplete in ht.
      rewrite map_map in ht.
      erewrite map_ext, map_id in ht. 2: apply ev_rf.
      cbv beta iota delta [substitute_jdg fmap Sig_FMapJdg FMapProd FMapId fst snd] in ht.
      rewrite !ev_substitute, !ev_rf in ht.
      erewrite 2!(csubstitute_ext (λ i, ceval (creify (σ i))) σ) in ht.
      1: exact ht.
      all: intro i. all: apply ev_rf.
    Qed.

  End Preservation.

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
  - intros rd hin. cbn in hin. destruct hin as [<- | [<- | [<- | []]]].
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
