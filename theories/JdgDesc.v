(** Judgment description

  The purpose is to describe a family of judgments that can be turned into
  a judgment signature.
  A description is the output of the [Sulfur Judgment] command and thus refers
  to concrete syntax rather than only the syntax signature like judgment
  signatures.
  This justifies this intermediary module.

*)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped ConcreteSyntax.
From Utils Require Import Functor.

(** n-ary (non-dependent) functions

  A pattern we reuse several times in this file.
  [nary n A B] is [A → … → A → B] with [n] times [A].

*)
Fixpoint nary n A B :=
  match n with
  | 0 => B
  | S n => A → nary n A B
  end.

(** n-ary application *)
Fixpoint napply {A B} (f : nat → A) n i : nary n A B → B :=
  match n with
  | 0 => λ b, b
  | S n => λ g, napply f n (S i) (g (f i))
  end.

(** Judgment description over a signature *)

Section Desc.

  Context {sig : signature}.

  (* For now, judgments involve two terms and that's it *)
  Definition mjdgd sc : Type :=
    (mexpr Kt sc * mexpr Kt sc).

  (** Rule parameter: a meta-variable of arity [n] or a true parameter *)
  Inductive rule_param :=
  | rp_term (n : nat)
  | rp_param (A : Type).

  (** Conjunction of true parameters *)
  Fixpoint params ps : Type :=
    match ps with
    | [] => unit
    | rp_term _ :: ps => params ps
    | rp_param A :: ps => A * params ps
    end.

  (** For now, contexts store terms (hence [λ X, X]) *)
  Definition hctx n := mctx (λ X, X) 0 n.

  (** Premise description: judgment under an extension *)
  Record premise_desc := {
    pd_n : nat ;
    pd_ctx : hctx pd_n ;
    pd_jdg : mjdgd pd_n
  }.

  Record rule_desc := {
    rd_name : string ;
    rd_params : list rule_param ;
    rd_premises : params rd_params → list premise_desc ;
    rd_conclusion : params rd_params → mjdgd 0
  }.

  Definition jdg_desc :=
    list rule_desc.

End Desc.

(** Judgment signature from a description *)

Section ToSig.

  Context {sig : signature}.

  (* For now we assume only one judgment *)
  Definition Idx := unit.

  (* Contexts only store terms *)
  #[local] Instance: IDecl Idx :=
    λ _ X, X.

  (* Context judgment has to be typing *)
  #[local] Instance: IJdg Idx :=
    λ _ X, (X * X)%type.

  Definition to_premise (pd : premise_desc) : premise tt :=
    prem_ind tt (λ X x, x) pd.(pd_ctx) pd.(pd_jdg).

  Definition to_rule (rd : rule_desc) : rule tt := {|
    param  := params rd.(rd_params) ;
    premises := λ x, map to_premise (rd.(rd_premises) x) ;
    conclusion := rd.(rd_conclusion)
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

#[local] Instance Sig_IDecl : IDecl Idx := λ _ X, X.
#[local] Instance Sig_IJdg : IJdg Idx := λ _ X, (X * X)%type.
#[local] Instance Sig_FMapDecl : ∀ i, FMap (declF i) := λ _, FMapId.
#[local] Instance Sig_FMapJdg : ∀ i, FMap (jdgF i) := λ _, FMapProd _ _.
#[local] Instance Sig_FuncDecl : ∀ i, Eq1Functor (declF i) := λ _, FId.
#[local] Instance Sig_FuncJdg : ∀ i, Eq1Functor (jdgF i) := λ _, Eq1FProd _ _.
#[local] Instance Sig_IMakeJdg : IMakeJdg Idx := λ _ X d x, (x, d).
#[local] Instance Sig_NatMake : ∀ i, NatFromProd (make_jdg i).
Proof. intro i. constructor. reflexivity. Qed.

(** Higher-order presentation of rules

  Meta-variables are abstracted as functions.

*)

Section HOAS.

  Context {sig : signature}.

  (* Term in any scope *)
  Definition hterm := ∀ s, mexpr Kt s.

  (* [n]-ary [hterm] *)
  Definition hterm_n n :=
    nary n hterm hterm.

  Fixpoint hmvar_aux (k : mvar) n (l : list hterm) : hterm_n n :=
    match n with
    | 0 => λ s, M_mvar s k (map (λ t, t s) l)
    | S n => λ x, hmvar_aux k n (x :: l)
    end.

  (* Meta-variable [k], arity [n] *)
  Definition hmvar (k : mvar) n : hterm_n n :=
    hmvar_aux k n [].

  Fixpoint harg (a : arg_ty) :=
    match a with
    | AT_base b => eval_base b
    | AT_term => hterm
    | AT_bind a => hterm → harg a
    end.

  Fixpoint curry (l : list arg_ty) :=
    match l with
    | [] => hterm
    | a :: l => harg a → curry l
    end.

  (** [hvar_idx d s] is [Some (s - S d)] when [d < s]: the index, at scope
    [s], of the variable bound at depth [d]. By recursion rather than
    [Nat.sub], which the plugin keeps folded (see [csub]).
  *)
  Fixpoint hvar_idx (d s : nat) : option nat :=
    match s with
    | 0 => None
    | S s =>
      match d with
      | 0 => Some s
      | S d => hvar_idx d s
      end
    end.

  Lemma hvar_idx_lt {d s i} :
    hvar_idx d s = Some i →
    i < s.
  Proof.
    induction d as [| d ih] in s, i |- *.
    all: destruct s as [| s]. all: cbn. all: intro h.
    all: try discriminate.
    - injection h as <-. lia.
    - apply ih in h. lia.
  Qed.

  Definition hdummy {s} : mexpr Kt s :=
    M_mvar s 0 [].

  (** The variable bound at depth [d], as a term: index [s - S d] at any
    scope [s > d], a dummy below (well-scoped HOAS never gets there).
    A binder entered at scope [s] binds the variable of depth [s].
  *)
  Definition hvar (d : nat) : hterm :=
    λ s,
      match hvar_idx d s as o return hvar_idx d s = o → mexpr Kt s with
      | Some i => λ h, M_var s i (hvar_idx_lt h)
      | None => λ _, hdummy
      end eq_refl.

  Fixpoint harg_inst s (a : arg_ty) : harg a → mexpr (Ka a) s :=
    match a with
    | AT_base b => λ x, M_abase _ _ x
    | AT_term => λ t, M_aterm _ (t s)
    | AT_bind a => λ b, M_abind _ (harg_inst _ a (b (hvar s)))
    end.

  Fixpoint hctor_aux (l : list arg_ty) : ((∀ s, mexpr (Kal l) s) → hterm) → curry l :=
    match l with
    | [] => λ f, f (λ s, M_al_nil _)
    | a :: l =>
      λ f x, hctor_aux l (λ al, f (λ s, M_al_cons _ (harg_inst _ _ x) (al s)))
    end.

  (* Constructor applied to its arguments *)
  Definition hctor (c : ctor) : curry (ctor_type c) :=
    hctor_aux _ (λ f s, M_ctor _ c (f s)).

  Definition rp_ty p :=
    match p with
    | rp_term n => hterm_n n
    | rp_param A => A
    end.

  Fixpoint hfun ps R :=
    match ps with
    | [] => R
    | p :: ps => rp_ty p → hfun ps R
    end.

  (* Apply an [hfun] to meta-variables starting from [k] *)
  Fixpoint happly {R} ps (k : mvar) : hfun ps R → params ps → R :=
    match ps with
    | [] => λ x _, x
    | rp_term n :: ps => λ f, happly ps (S k) (f (hmvar k n))
    | rp_param A :: ps => λ f x, happly ps k (f (fst x)) (snd x)
    end.

  Definition hjdg_ty : Type :=
    hterm * hterm.

  Definition hjdg (t A : hterm) : hjdg_ty :=
    (t, A).

  Definition hprem :=
    ∀ s, hctx s → premise_desc.

  Definition hjp (j : hjdg_ty) : hprem :=
    λ s Δ, {|
      pd_n := s ;
      pd_ctx := Δ ;
      pd_jdg := (fst j s, snd j s)
    |}.

  Definition hext (A : hterm) (P : hterm → hprem) : hprem :=
    λ s Δ, P (hvar s) (S s) (mcons (A (s + 0)) Δ).

  Definition hrule name ps (pr_cl : hfun ps (list hprem * hjdg_ty)) : rule_desc := {|
    rd_name := name ;
    rd_params := ps ;
    rd_premises := λ x, map (λ p, p 0 mnil) (fst (happly ps 0 pr_cl x)) ;
    rd_conclusion :=
      λ x,
        let j := snd (happly ps 0 pr_cl x) in
        (fst j 0, snd j 0)
  |}.

End HOAS.

Coercion hjp : hjdg_ty >-> hprem.

Notation "⟨ x : A ⊢ P ⟩" :=
  (hext A (λ x, P))
  (at level 0, x name, A at level 200, P at level 200).

(** Instantiate mexpr to concrete syntax *)

Section Inst.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  Context (ι : mvar → T).

  (* Fast path: do not substitute by the identity.

    We thus detect whether [σ] is [ var i ; … ; var (i + n - 1) ].

  *)
  Fixpoint is_id {s} n i (σ : list (mexpr Kt s)) : bool :=
    match n, σ with
    | 0, [] => true
    | S n, M_var _ j _ :: σ => (i =? j) && is_id n (S i) σ
    | _, _ => false
    end.

  (* Turn a list into a substitution, lifting outside by [s]

    Note: The plugin keeps "-" opaque to avoid pollution.

  *)
  Definition csub s (σ : list T) (i : nat) : T :=
    nth i σ (cvar (s + (i - List.length σ))).

  (* [s] shifts; [rshift] itself when [s = 1] *)
  Fixpoint rshifts (s : nat) : ren :=
    match s with
    | 0 => rid
    | S s =>
      match s with
      | 0 => rshift
      | S _ => rcomp (rshifts s) rshift
      end
    end.

  Fixpoint cinst {k s} (e : mexpr k s) {struct e} : ckind T k :=
    match e with
    | M_var _ i h => cvar i
    | M_ctor _ c args => cctor c (cinst args)
    | M_al_nil _ => tt
    | M_al_cons _ ty tys => (cinst ty, cinst tys)
    | M_abase _ b x => x
    | M_aterm _ t => cinst t
    | M_abind _ a => cinst a
    | M_mvar s k σ =>
      if is_id s 0 σ then ι k
      else
        match σ with
        | [] => crename (rshifts s) (ι k)
        | _ => csubstitute (csub s (map cinst σ)) (ι k)
        end
    end.

  Fixpoint cinst_ctx {n} (Δ : hctx n) : list T :=
    match Δ with
    | mnil => []
    | mcons d Δ => cinst d :: cinst_ctx Δ
    end.

End Inst.

(** Computing the types of concrete constructors *)

Section ConcreteJdg.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  (* The concrete judgment being defined (specialised to binary case) *)
  Context (J : list T → T → T → Prop).

  Definition conc_jdg {s} (Γ : list T) (ι : mvar → T) (j : mjdgd s) : Prop :=
    J Γ (cinst ι (fst j)) (cinst ι (snd j)).

  Definition conc_prem (Γ : list T) (ι : mvar → T) (pd : premise_desc) :=
    conc_jdg (cinst_ctx ι pd.(pd_ctx) ++ Γ) ι pd.(pd_jdg).

  (** [∀ x1 ... xn, K [x1; ...; xn]]. *)
  Fixpoint under ps (ms : list T) : (list T → params ps → Prop) → Prop :=
    match ps with
    | [] => λ K, K (rev ms) tt
    | rp_term _ :: ps => λ K, ∀ x, under ps (x :: ms) K
    | rp_param A :: ps => λ K, ∀ (a : A), under ps ms (λ l p, K l (a, p))
    end.

  Definition dummy : T :=
    cvar 0.

  Definition nvar (vs : list T) :=
    λ i, nth i vs dummy.

  Definition rule_desc_type (rd : rule_desc) (Γ : list T) : Prop :=
    under rd.(rd_params) [] (λ vs x,
      fold_right
        (λ P Q, P → Q)
        (conc_jdg Γ (nvar vs) (rd.(rd_conclusion) x))
        (map (conc_prem Γ (nvar vs)) (rd.(rd_premises) x))
    ).

  Inductive cinctx (sh : T → T) : list T → nat → T → Prop :=
  | cin_head d Γ : cinctx sh (d :: Γ) 0 (sh d)
  | cin_tail d d' Γ n : cinctx sh Γ n d → cinctx sh (d' :: Γ) (S n) (sh d).

  Definition var_rule_type :=
    ∀ Γ n A, cinctx (crename rshift) Γ n A → J Γ (cvar n) A.

  Fixpoint nterms ps : nat :=
    match ps with
    | [] => 0
    | rp_term _ :: ps => S (nterms ps)
    | rp_param _ :: ps => nterms ps
    end.

  (* Arity of the [k]-th meta-variable *)
  Fixpoint arity ps (k : mvar) : nat :=
    match ps with
    | [] => 0
    | rp_term n :: ps =>
      match k with
      | 0 => n
      | S k => arity ps k
      end
    | rp_param _ :: ps => arity ps k
    end.

  Lemma under_iff ps ms K :
    (∀ vs x, List.length vs = nterms ps → K (rev ms ++ vs) x) ↔ under ps ms K.
  Proof.
    split.
    - intros h.
      induction ps as [| [| A] ps ih] in ms, K, h |- *.
      + cbn.
        specialize h with (vs := []) (x := tt) (1 := eq_refl).
        rewrite app_nil_r in h. assumption.
      + cbn. intros x.
        apply ih. intros vs y hvs.
        cbn. rewrite <- app_assoc. cbn. apply h.
        cbn. lia.
      + cbn. intros a.
        apply ih. intros vs x e.
        apply h. cbn. assumption.
    - intros h vs x hl.
      induction ps as [| [| A] ps ih] in x, ms, K, h, vs, hl |- *.
      + cbn in h. destruct x.
        destruct vs. 2: discriminate.
        rewrite app_nil_r. assumption.
      + cbn in h.
        destruct vs as [| v vs]. 1: discriminate.
        cbn in hl. injection hl as e.
        specialize (h v). eapply ih in h. 2: eassumption.
        cbn in h. rewrite <- app_assoc in h. eassumption.
      + cbn in h, x.
        destruct x as [a x]. specialize (h a).
        cbn in hl.
        eapply ih in h. 2: eassumption.
        eassumption.
  Qed.

End ConcreteJdg.

(** Induction principle for a concrete judgment *)

Section Ind.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.
  Context (desc : jdg_desc).
  Context (J : list T → T → T → Prop).

  (* Like [rule_desc_type] but collecting induction hypotheses *)
  Definition rule_ind_case P (rd : rule_desc) (Γ : list T) : Prop :=
    under rd.(rd_params) [] (λ vs x,
      fold_right
        (λ pd K, conc_prem J Γ (nvar vs) pd → conc_prem P Γ (nvar vs) pd → K)
        (conc_jdg P Γ (nvar vs) (rd.(rd_conclusion) x))
        (rd.(rd_premises) x)
    ).

  Definition ind_type :=
    ∀ P,
      var_rule_type P →
      fold_right
        (λ rd K, (∀ Γ, rule_ind_case P rd Γ) → K)
        (∀ Γ t A, J Γ t A → P Γ t A)
        desc.

End Ind.

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

  (** Well-formed meta expression

    Meta-variables [k] below [m], applied to a substitution of arity [ar k].

  *)
  Section WExpr.

    Context (ar : mvar → nat) (m : nat).

    Fixpoint wf_mexpr {k s} (e : mexpr k s) {struct e} : bool :=
      match e with
      | M_var _ _ _ => true
      | M_ctor _ _ al => wf_mexpr al
      | M_al_nil _ => true
      | M_al_cons _ a al => wf_mexpr a && wf_mexpr al
      | M_abase _ _ _ => true
      | M_aterm _ t => wf_mexpr t
      | M_abind _ a => wf_mexpr a
      | M_mvar s k σ =>
        (k <? m) && (List.length σ =? ar k) && forallb wf_mexpr σ
      end.

  End WExpr.

  (* The substitution [inst me (M_mvar s k σ)] applies *)
  Definition inst_sub {s'} s (σ : list (mexpr Kt s')) me i : expr Kt :=
    match nth_error (map (inst me) σ) i with
    | Some t => t
    | None => E_var (i - List.length σ + s)
    end.

  Lemma inst_sub_S s' s t σ me i :
    inst_sub (s' := s') s (t :: σ) me (S i) =
    inst_sub s σ me i.
  Proof.
    reflexivity.
  Qed.

  Derive Signature for mexpr.

  Lemma is_id_sub s n i (σ : list (mexpr Kt s)) me j :
    is_id n i σ = true →
    s = i + n →
    inst_sub s σ me j = E_var (i + j).
  Proof.
    intros h e.
    induction σ as [| t σ ih] in n, i, j, h, e |- *.
    - destruct n. 2: discriminate.
      unfold inst_sub. destruct j. all: cbn. all: f_equal. all: lia.
    - destruct n as [| n]. 1: discriminate.
      depelim t. all: try discriminate.
      cbn in h. rewrite andb_true_iff in h. destruct h as [hi h].
      rewrite PeanoNat.Nat.eqb_eq in hi. symmetry in hi. subst.
      destruct j as [| j].
      + cbn. f_equal. lia.
      + rewrite inst_sub_S. erewrite ih. 2: eassumption. 2: lia.
        f_equal. lia.
  Qed.

  Lemma rf_substitute σ t :
    creify (csubstitute σ t) = substitute (λ i, creify (σ i)) (creify t).
  Proof.
    erewrite <- rf_ev.
    rewrite ev_substitute, ev_rf. f_equal.
    apply csubstitute_ext. intro i. rewrite ev_rf. reflexivity.
  Qed.

  Lemma rshifts_add s i :
    rshifts s i = s + i.
  Proof.
    induction s as [| s ih] in i |- *.
    - reflexivity.
    - destruct s as [| s].
      + reflexivity.
      + cbn. unfold rcomp, rshift. rewrite ih. reflexivity.
  Qed.

  Lemma rf_csub ι s (σ : list (mexpr Kt s)) me i :
    Forall (λ t, creify (cinst ι t) = inst me t) σ →
    creify (csub s (map (cinst ι) σ) i) = inst_sub s σ me i.
  Proof.
    intros h.
    induction h as [| t σ ht hσ ih] in i |- *.
    - unfold inst_sub. destruct i.
      all: cbn. all: rewrite rf_var. all: f_equal. all: lia.
    - destruct i as [| i].
      + assumption.
      + rewrite inst_sub_S. apply ih.
  Qed.

  Lemma rf_cinst ι k s (e : mexpr k s) :
    rfk creify k (cinst ι e) = inst (λ k _, creify (ι k)) e.
  Proof.
    revert k s e.
    apply (
      mexpr_ind (λ k s e,
        rfk creify k (cinst ι e) = inst (λ k _, creify (ι k)) e
      )
    ).
    - intros. apply rf_var.
    - intros. cbn. rewrite rf_cctor. f_equal. auto.
    - intros. reflexivity.
    - intros s ty tys a al ha hal.
      cbn. f_equal. all: eauto.
    - reflexivity.
    - cbn. intros s t ht. rewrite ht. all: eauto.
    - cbn. intros s ty a hty. rewrite hty. all: eauto.
    - intros s k σ hσ.
      cbn. destruct is_id eqn:e.
      + symmetry. etransitivity. 2: apply subst_sid.
        apply substitute_proper. 2: reflexivity.
        intros i.
        eapply is_id_sub with (j := i) in e. 2: reflexivity.
        eassumption.
      + destruct σ as [| t σ].
        * rewrite rf_rename, ren_is_subst.
          apply substitute_proper. 2: reflexivity.
          intro i. unfold rscomp, ren_to_subst. cbn.
          rewrite rshifts_add. replace (i - 0 + s) with (s + i) by lia.
          destruct i. all: reflexivity.
        * rewrite rf_substitute.
          apply substitute_proper. 2: reflexivity.
          intro i. apply rf_csub. assumption.
  Qed.

  Lemma rf_cinst_t ι s (e : mexpr Kt s) :
    creify (cinst ι e) = inst (λ k _, creify (ι k)) e.
  Proof.
    apply rf_cinst.
  Qed.

  Lemma rf_cinst_ctx ι n (Δ : hctx n) :
    map creify (cinst_ctx ι Δ) = inst_ctx (λ k _, creify (ι k)) Δ.
  Proof.
    induction Δ as [| n d Δ ih].
    - reflexivity.
    - cbn. unfold fmap, FMapId. rewrite rf_cinst_t. f_equal. apply ih.
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

  Definition wf_jdg {s} ar m (j : mjdgd s) :=
    wf_mexpr ar m (fst j) && wf_mexpr ar m (snd j).

  Fixpoint wf_ctx ar m {n} (Δ : hctx n) : bool :=
    match Δ with
    | mnil => true
    | mcons d Δ => wf_mexpr ar m d && wf_ctx ar m Δ
    end.

  Definition wf_prem ar m (pd : premise_desc) :=
    wf_ctx ar m pd.(pd_ctx) && wf_jdg ar m pd.(pd_jdg).

  Definition wf_rule_at rd x :=
    let ar := arity rd.(rd_params) in
    let m := nterms rd.(rd_params) in
    forallb (wf_prem ar m) (rd.(rd_premises) x) &&
    wf_jdg ar m (rd.(rd_conclusion) x).

  Definition wf_rule rd :=
    ∀ x, wf_rule_at rd x = true.

  Definition wf_desc :=
    Forall wf_rule desc.

  Lemma wf_desc_rule rd :
    wf_desc →
    In rd desc →
    wf_rule rd.
  Proof.
    intros h hin.
    unfold wf_desc in h. rewrite Forall_forall in h.
    apply h. assumption.
  Qed.

  Lemma sound_step rd Γ :
    In rd desc →
    rule_desc_type J rd Γ.
  Proof.
    intros h.
    red. rewrite <- under_iff. intros vs x hvs. cbn.
    rewrite <- fold_impl_iff. intros hF.
    rewrite Forall_map in hF.
    unfold conc_jdg, J, Pf. cbn.
    erewrite 2!rf_cinst_t.
    eapply conv_proof_j.
    - eapply step with (r := to_rule rd) (m := λ k _, creify (nvar vs k)) (x := x).
      + apply in_to_rules_intro. assumption.
      + intros i' n Δ j conv hin. cbn in hin.
        rewrite in_map_iff in hin. destruct hin as [pd [hp hp']].
        destruct pd as [n' Δ' [t A]]. noconf hp.
        cbn. rewrite map_id.
        rewrite Forall_forall in hF. specialize (hF _ hp').
        unfold conc_prem, conc_jdg, J, Pf in hF. cbn in hF.
        rewrite map_app, rf_cinst_ctx in hF.
        erewrite 2!rf_cinst_t in hF.
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
      Forall (λ rd, ∀ Γ, rule_desc_type R rd Γ) desc.

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

  (** Proving soundness from induction principle *)

  Lemma fold_cases_elim {X} (C : X → Prop) (B : Prop) (l : list X) :
    Forall C l →
    fold_right (λ x K, C x → K) B l →
    B.
  Proof.
    intros hF h. induction hF as [| x l hx hl ih]. 1: exact h.
    cbn in h. auto.
  Qed.

  Lemma rule_ind_case_of_type R P rd Γ :
    rule_desc_type P rd Γ →
    rule_ind_case R P rd Γ.
  Proof.
    unfold rule_desc_type, rule_ind_case.
    rewrite <- !under_iff. intros h vs x hl. specialize (h vs x hl).
    cbn in *.
    induction (rd_premises rd) as [| j l ih] in h |- *.
    - exact h.
    - cbn in *. intros _ hj. apply ih. apply h. exact hj.
  Qed.

  Lemma sound_of_ind R :
    ind_type desc R →
    sound_jdg R.
  Proof.
    intros hind.
    specialize (hind J sound_var).
    eapply fold_cases_elim in hind. 1: exact hind.
    rewrite Forall_forall. intros rd hin Γ.
    apply rule_ind_case_of_type.
    apply sound_step. assumption.
  Qed.

  (** Completeness against an abstract "concrete" judgment *)

  Lemma ev_var n : ceval (E_var n) = cvar n.
  Proof.
    rewrite <- rf_var. apply ev_rf.
  Qed.

  Lemma ev_rename r e : ceval (ParamSyntax.rename r e) = crename r (ceval e).
  Proof.
    rewrite <- (rf_ev e) at 1. rewrite <- rf_rename. apply ev_rf.
  Qed.

  Lemma inst_ext_wf ar m (me me' : menv) k s (e : mexpr k s) :
    (∀ k, k < m → me k (ar k) = me' k (ar k)) →
    wf_mexpr ar m e = true →
    inst me e = inst me' e.
  Proof.
    intros hme. revert k s e.
    apply (mexpr_ind (λ k s e, wf_mexpr ar m e = true → inst me e = inst me' e)).
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
      rewrite !andb_true_iff in h. destruct h as [[hk hl] hσ].
      rewrite PeanoNat.Nat.ltb_lt in hk.
      rewrite PeanoNat.Nat.eqb_eq in hl.
      cbn. rewrite hl. rewrite hme. 2: assumption.
      erewrite map_ext_Forall. 1: reflexivity.
      rewrite forallb_forall in hσ.
      rewrite Forall_forall in *.
      intros t ht. apply ih. all: auto.
  Qed.

  Definition ev_vs ar m (me : menv) : list T :=
    map (λ k, ceval (me k (ar k))) (seq 0 m).

  Lemma ev_vs_length ar m me :
    List.length (ev_vs ar m me) = m.
  Proof.
    unfold ev_vs.
    rewrite length_map, length_seq.
    reflexivity.
  Qed.

  Definition ev_vals ar m me :=
    nvar (ev_vs ar m me).

  Lemma ev_inst ar m me s (e : mexpr Kt s) :
    wf_mexpr ar m e = true →
    ceval (inst me e) = cinst (ev_vals ar m me) e.
  Proof.
    intros h.
    rewrite <- ev_rf.
    rewrite rf_cinst_t.
    f_equal. eapply inst_ext_wf. 2: eassumption.
    intros k hk.
    unfold ev_vals, ev_vs, nvar.
    rewrite nth_map_seq. 2: assumption.
    rewrite rf_ev. reflexivity.
  Qed.

  Lemma ev_inst_ctx ar m me n (Δ : hctx n) :
    wf_ctx ar m Δ = true →
    map ceval (inst_ctx me Δ) = cinst_ctx (ev_vals ar m me) Δ.
  Proof.
    intros h.
    induction Δ as [| n d Δ ih].
    - reflexivity.
    - cbn in h. rewrite andb_true_iff in h. destruct h as [hd hΔ].
      cbn. unfold fmap, FMapId. erewrite ev_inst. 2: exact hd.
      f_equal. apply ih. assumption.
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
    Context (hrules : rules_type R).
    Context (hwf : wf_desc).

    Theorem jdg_complete : complete_jdg R.
    Proof.
      intros Γ j.
      induction 1 as [[] me Γ r x hin hind ih hpred | [] Γ n d hd].
      - cbn in hin. apply in_to_rules in hin as (rd & hin & ->).
        eapply wf_desc_rule in hwf. 2: exact hin.
        unfold rules_type in hrules. rewrite Forall_forall in hrules.
        specialize (hrules _ hin (map ceval Γ)).
        specialize (hwf x). unfold wf_rule, wf_rule_at, wf_jdg in hwf.
        rewrite !andb_true_iff in hwf.
        destruct hwf as (hwp & hwt & hwA).
        destruct rd as [name ps prems concl]. cbn in *.
        rewrite <- under_iff in hrules.
        specialize hrules
        with (x := x) (1 := ev_vs_length (arity ps) (nterms ps) me).
        rewrite <- fold_impl_iff in hrules. cbn in hrules.
        destruct (concl x) as [t A]. cbn.
        unfold conc_jdg in hrules. cbn in hrules.
        unfold fmap, FMapId.
        erewrite !ev_inst. 2,3: eassumption.
        apply hrules.
        rewrite Forall_map, Forall_forall.
        intros [n Δ [t' A']] hp.
        rewrite forallb_forall in hwp. specialize (hwp _ hp).
        unfold wf_prem, wf_jdg in hwp. cbn in hwp.
        rewrite !andb_true_iff in hwp. destruct hwp as (hΔ & hwt' & hwA').
        specialize (ih tt _ Δ (t', A') (λ X x, x)).
        specialize ih with (1 := in_map _ _ _ hp).
        cbn in ih. unfold fmap, FMapId in ih. rewrite map_id in ih.
        rewrite map_app in ih.
        erewrite ev_inst_ctx in ih. 2: eassumption.
        rewrite 2!(ev_inst (arity ps) (nterms ps) me) in ih. 2,3: assumption.
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

(** Tactics for the plugin *)

(** Prove [wf_desc] *)
Ltac wf_desc_tac :=
  repeat constructor ;
  intro ; reflexivity.
