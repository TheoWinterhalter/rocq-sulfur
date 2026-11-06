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

(** Judgment description over a signature *)

Section Desc.

  Context {sig : signature}.

  (** The type of concrete terms mentioned by predicate premises *)
  Context {T : Type}.

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

  (** For now, contexts store terms (hence [λ X, X]) *)
  Definition hctx n := mctx (λ X, X) 0 n.

  (** Premise description:
    - a judgment under an extension;
    - or a predicate over the context and values of the meta-variables
  *)
  Inductive premise_desc :=
  | pd_jdg {n} (Δ : hctx n) (j : mjdgd n)
  | pd_pred n (P : nary n T (list T → Prop)).

  Record rule_desc := {
    rd_name : string ;
    rd_params : list rule_param ;
    rd_premises : params rd_params → list premise_desc ;
    rd_conclusion : params rd_params → mjdgd 0
  }.

  Definition jdg_desc :=
    list rule_desc.

End Desc.

Abbreviation rd_arity rd := (arity rd.(rd_params)).
Abbreviation rd_nterms rd := (nterms rd.(rd_params)).

(** List of values of meta-variables *)

Section Val.

  Context {sig : signature} {T} {CS : ConcreteSyntax sig T}.

  Definition dummy : T :=
    cvar 0.

  Definition nvar (vs : list T) :=
    λ i, nth i vs dummy.

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

End Val.

(** Judgment signature from a description *)

Section ToSig.

  Context {sig : signature} {T} {CS : ConcreteSyntax sig T}.

  (* For now we assume only one judgment *)
  Definition Idx := unit.

  (* Contexts only store terms *)
  #[local] Instance: IDecl Idx :=
    λ _ X, X.

  (* Context judgment has to be typing *)
  #[local] Instance: IJdg Idx :=
    λ _ X, (X * X)%type.

  Definition to_premise ar m (pd : premise_desc (T := T)) : premise tt :=
    match pd with
    | pd_jdg Δ j => prem_ind tt (λ X x, x) Δ j
    | pd_pred n P =>
      prem_pred tt (λ Γ me, napply (ev_vals ar m me) _ 0 P (map ceval Γ))
    end.

  Definition to_rule (rd : rule_desc) : rule tt := {|
    param := params rd.(rd_params) ;
    premises :=
      λ x, map (to_premise (rd_arity rd) (rd_nterms rd)) (rd.(rd_premises) x) ;
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

  Context {sig : signature} {T : Type}.

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
    ∀ s, hctx s → premise_desc (T := T).

  Definition hjp (j : hjdg_ty) : hprem :=
    λ s Δ, pd_jdg Δ (fst j s, snd j s).

  Definition hext (A : hterm) (P : hterm → hprem) : hprem :=
    λ s Δ, P (hvar s) (S s) (mcons (A (s + 0)) Δ).

  Definition hpred n (P : nary n T (list T → Prop)) : hprem :=
    λ _ _, pd_pred n P.

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

(** Lifting a concrete substitution under [k] binders, as [up_substs] *)

Section Up.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  Definition cup_subst (σ : nat → T) (i : nat) : T :=
    match i with
    | 0 => cvar 0
    | S i => crename rshift (σ i)
    end.

  Fixpoint cups_subst k (σ : nat → T) : nat → T :=
    match k with
    | 0 => σ
    | S k => cup_subst (cups_subst k σ)
    end.

End Up.

(** Computing the types of concrete constructors *)

Section ConcreteJdg.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  (* The concrete judgment being defined (specialised to binary case) *)
  Context (J : list T → T → T → Prop).

  Definition conc_jdg {s} (Γ : list T) (ι : mvar → T) (j : mjdgd s) : Prop :=
    J Γ (cinst ι (fst j)) (cinst ι (snd j)).

  Definition conc_prem (Γ : list T) (ι : mvar → T) (pd : premise_desc (T := T)) :=
    match pd with
    | pd_jdg Δ j => conc_jdg (cinst_ctx ι Δ ++ Γ) ι j
    | pd_pred n P => napply ι n 0 P Γ
    end.

  (** [∀ x1 ... xn, K [x1; ...; xn]]. *)
  Fixpoint under ps (ms : list T) : (list T → params ps → Prop) → Prop :=
    match ps with
    | [] => λ K, K (rev ms) tt
    | rp_term _ :: ps => λ K, ∀ x, under ps (x :: ms) K
    | rp_param A :: ps => λ K, ∀ (a : A), under ps ms (λ l p, K l (a, p))
    end.

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
  Context (desc : jdg_desc (T := T)).
  Context (J : list T → T → T → Prop).

  (* Induction hyopthesis only for [pd_jdg] *)
  Definition ind_prem P Γ ι pd K : Prop :=
    match pd with
    | pd_jdg _ _ => conc_prem J Γ ι pd → conc_prem P Γ ι pd → K
    | pd_pred _ _ => conc_prem J Γ ι pd → K
    end.

  (* Like [rule_desc_type] but collecting induction hypotheses *)
  Definition rule_ind_case P (rd : rule_desc) (Γ : list T) : Prop :=
    under rd.(rd_params) [] (λ vs x,
      fold_right
        (ind_prem P Γ (nvar vs))
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
  Context (desc : jdg_desc (T := T)).

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

  Definition wf_prem ar m (pd : premise_desc (T := T)) :=
    match pd with
    | pd_jdg Δ j => wf_ctx ar m Δ && wf_jdg ar m j
    | pd_pred n P => true
    end.

  Definition wf_rule_at rd x :=
    let ar := rd_arity rd in
    let m := rd_nterms rd in
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

  Lemma map_nvar_seq (vs : list T) :
    map (nvar vs) (seq 0 (List.length vs)) = vs.
  Proof.
    unfold nvar.
    induction vs as [| v vs ih].
    - reflexivity.
    - cbn. f_equal.
      rewrite <- seq_shift, map_map.
      apply ih.
  Qed.

  Lemma ev_ctx_rf (Γ : list T) :
    map ceval (ctx_rf Γ) = Γ.
  Proof.
    induction Γ as [| A Γ ih].
    - reflexivity.
    - cbn. rewrite ev_rf. f_equal. assumption.
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
        destruct pd as [n' Δ' [t A] | ]. 2: discriminate.
        noconf hp.
        cbn. rewrite map_id.
        rewrite Forall_forall in hF. specialize (hF _ hp').
        unfold conc_prem, conc_jdg, J, Pf in hF. cbn in hF.
        rewrite map_app, rf_cinst_ctx in hF.
        erewrite 2!rf_cinst_t in hF.
        exact hF.
      + intros P hin. cbn in hin.
        rewrite in_map_iff in hin. destruct hin as [pd [hpd hin]].
        destruct pd as [| n' P']. 1: discriminate.
        noconf hpd.
        rewrite Forall_forall in hF. specialize (hF _ hin).
        unfold conc_prem in hF.
        rewrite ev_ctx_rf. unfold ev_vals, ev_vs.
        erewrite map_ext.
        2:{ intro. rewrite ev_rf. reflexivity. }
        rewrite <- hvs, map_nvar_seq.
        exact hF.
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

    (** Obligations for [preserve_subst_jdg]

      Every predicate premise must be stable under well-typed substitutions.

    *)

    Definition subst_vals ar nt (σ : nat → T) (vs : list T) : list T :=
      map (λ k, csubstitute (cups_subst (ar k) σ) (nvar vs k)) (seq 0 nt).

    Definition pred_stable ar nt Γ Δ σ vs (pd : premise_desc (T := T)) :=
      match pd with
      | pd_jdg _ _ => True
      | pd_pred n P =>
        napply (nvar vs) n 0 P Γ →
        napply (nvar (subst_vals ar nt σ vs)) n 0 P Δ
      end.

    Fixpoint stable_at ar nt Γ Δ σ vs (l : list (premise_desc (T := T))) i :=
      match l with
      | [] => True
      | pd :: l =>
        match i with
        | 0 => pred_stable ar nt Γ Δ σ vs pd
        | S i => stable_at ar nt Γ Δ σ vs l i
        end
      end.

    Lemma stable_at_nth_error ar nt Γ Δ σ vs l i pd :
      nth_error l i = Some pd →
      stable_at ar nt Γ Δ σ vs l i = pred_stable ar nt Γ Δ σ vs pd.
    Proof.
      induction l as [| pd' l ih] in i |- *.
      - destruct i. all: discriminate.
      - destruct i as [| i].
        + cbn. intro e. injection e as ->. reflexivity.
        + cbn. apply ih.
    Qed.

    (* Obligation for the [i]-th premise of a rule *)
    Definition pred_obl (rd : rule_desc) i : Prop :=
      let ar := rd_arity rd in
      let nt := rd_nterms rd in
      under rd.(rd_params) [] (λ vs x,
        ∀ Γ Δ σ,
          cstyping Δ σ Γ →
          stable_at ar nt Γ Δ σ vs (rd.(rd_premises) x) i
      ).

    (** Obligations as stated by the command are identified by
      - the index of its rule in the description and
      - the position of the premise.
      They are therefore reprenseted as [nat * nat].
    *)

    Definition obl_at r i : Prop :=
      match nth_error desc r with
      | Some rd => pred_obl rd i
      | None => True
      end.

    Definition obligations (ps : list (nat * nat)) :=
      Forall_rec (λ '(r, i), obl_at r i) ps.

    Definition is_pred (pd : premise_desc (T := T)) :=
      match pd with
      | pd_pred _ _ => true
      | pd_jdg _ _ => false
      end.

    Definition mem (r i : nat) (ps : list (nat * nat)) :=
      existsb (λ '(r', i'), (r =? r') && (i =? i')) ps.

    (* The predicate premises of a rule, from position [i], are listed *)
    Fixpoint pos_ok r i (prems : list (premise_desc (T := T))) ps :=
      match prems with
      | [] => true
      | pd :: prems =>
        (negb (is_pred pd) || mem r i ps) && pos_ok r (S i) prems ps
      end.

    Fixpoint obls_ok_from r (d : list rule_desc) ps : Prop :=
      match d with
      | [] => True
      | rd :: d =>
        (∀ x, pos_ok r 0 (rd.(rd_premises) x) ps = true) ∧
        obls_ok_from (S r) d ps
      end.

    Definition obls_ok ps : Prop :=
      obls_ok_from 0 desc ps.

    Lemma mem_in r i ps :
      mem r i ps = true →
      In (r, i) ps.
    Proof.
      unfold mem. intros h.
      apply existsb_exists in h as ([r' i'] & hin & e).
      rewrite andb_true_iff, !PeanoNat.Nat.eqb_eq in e.
      destruct e as [-> ->]. assumption.
    Qed.

    Lemma pos_ok_nth r i prems ps k pd :
      pos_ok r i prems ps = true →
      nth_error prems k = Some pd →
      is_pred pd = true →
      mem r (i + k) ps = true.
    Proof.
      induction prems as [| pd' prems ih] in i, k |- *.
      - destruct k. all: discriminate.
      - cbn. intros h e hp.
        rewrite andb_true_iff in h. destruct h as [h1 h2].
        destruct k as [| k].
        + injection e as ->. rewrite hp in h1. cbn in h1.
          rewrite PeanoNat.Nat.add_0_r. assumption.
        + rewrite <- PeanoNat.Nat.add_succ_comm.
          eapply ih. all: eassumption.
    Qed.

    Lemma obls_ok_nth r d ps k rd :
      obls_ok_from r d ps →
      nth_error d k = Some rd →
      ∀ x, pos_ok (r + k) 0 (rd.(rd_premises) x) ps = true.
    Proof.
      induction d as [| rd' d ih] in r, k |- *.
      - destruct k. all: discriminate.
      - intros [h1 h2] e. destruct k as [| k].
        + injection e as ->. rewrite <- plus_n_O. assumption.
        + rewrite <- PeanoNat.Nat.add_succ_comm. eapply ih. all: eassumption.
    Qed.

    (* The obligation of the predicate premise [k] of rule [r] *)
    Lemma obligation_at ps r rd x k n P :
      obls_ok ps →
      obligations ps →
      nth_error desc r = Some rd →
      nth_error (rd.(rd_premises) x) k = Some (pd_pred n P) →
      pred_obl rd k.
    Proof.
      intros hok ho hr hk.
      eapply obls_ok_nth in hok. 2: exact hr. cbn in hok.
      eapply pos_ok_nth in hok. 2: exact hk. 2: reflexivity.
      cbn in hok. apply mem_in in hok.
      unfold obligations in ho. rewrite Forall_rec_iff, Forall_forall in ho.
      specialize (ho _ hok). unfold obl_at in ho. rewrite hr in ho.
      exact ho.
    Qed.

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
    induction (rd_premises rd) as [| pd l ih] in h |- *.
    - exact h.
    - cbn in *. destruct pd as [n Δ j | n Q].
      + cbn. intros _ hj. apply ih. apply h. exact hj.
      + cbn in *. eauto.
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

  Lemma ev_vs_ext ar m (me me' : menv) :
    me =₂ me' →
    ev_vs ar m me = ev_vs ar m me'.
  Proof.
    intros h. unfold ev_vs. apply map_ext.
    intro k. f_equal. apply h.
  Qed.

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
        with (x := x) (1 := ev_vs_length (CS := CS) (arity ps) (nterms ps) me).
        rewrite <- fold_impl_iff in hrules. cbn in hrules.
        destruct (concl x) as [t A]. cbn.
        unfold conc_jdg in hrules. cbn in hrules.
        unfold fmap, FMapId.
        erewrite !ev_inst. 2,3: eassumption.
        apply hrules.
        rewrite Forall_map, Forall_forall.
        intros pd hp.
        rewrite forallb_forall in hwp. specialize (hwp _ hp).
        destruct pd as [n Δ [t' A'] | n P].
        + unfold wf_prem, wf_jdg in hwp. cbn in hwp.
          rewrite !andb_true_iff in hwp. destruct hwp as (hΔ & hwt' & hwA').
          specialize (ih tt _ Δ (t', A') (λ X x, x)).
          specialize ih with (1 := in_map _ _ _ hp).
          cbn in ih. unfold fmap, FMapId in ih. rewrite map_id in ih.
          rewrite map_app in ih.
          erewrite ev_inst_ctx in ih. 2: eassumption.
          rewrite 2!(ev_inst (arity ps) (nterms ps) me) in ih. 2,3: assumption.
          exact ih.
        + eapply in_map in hp. specialize (hpred _ hp). assumption.
      - cbn. rewrite ev_var.
        apply hvar. apply inctx_cinctx. assumption.
    Qed.

  End Completeness.

  (** Preservation of substitution from soundness and completeness *)

  Lemma ev_up_substs k σ i :
    ceval (up_substs k σ i) = cups_subst k (λ i, ceval (σ i)) i.
  Proof.
    induction k as [| k ih] in i |- *.
    - reflexivity.
    - cbn. destruct i as [| i].
      + cbn. apply ev_var.
      + cbn. unfold srcomp. rewrite ev_rename, ih. reflexivity.
  Qed.

  (* The values of the meta-variables after a substitution *)
  Lemma ev_vs_subst ar nt me σ :
    ev_vs ar nt (λ k s, substitute (up_substs s σ) (me k s)) =
    subst_vals ar nt (λ i, ceval (σ i)) (ev_vs ar nt me).
  Proof.
    unfold subst_vals, ev_vs.
    apply map_ext_in. intros k hk. rewrite in_seq in hk.
    unfold nvar. rewrite nth_map_seq. 2: lia.
    rewrite ev_substitute. apply csubstitute_ext.
    intro i. apply ev_up_substs.
  Qed.

  Section Preservation.

    Context (R : list T → T → T → Prop).
    Context (hsound : sound_jdg R).
    Context (hcomplete : complete_jdg R).
    Context ps (hok : obls_ok ps) (hobls : obligations R ps).

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

    Lemma styping_cstyping Δ σ Γ :
      styping (jsig := to_jdg_sig desc) tt Δ σ Γ →
      cstyping R (map ceval Δ) (λ i, ceval (σ i)) (map ceval Γ).
    Proof.
      induction 1 as [[] Δ σ | [] Δ σ Γ d h ih hd].
      - constructor.
      - cbn. constructor. 1: exact ih.
        apply hcomplete in hd. cbn in hd.
        unfold fmap, Sig_FMapDecl, FMapId in hd.
        rewrite ev_substitute in hd. exact hd.
    Qed.

    Lemma subst_sig : SubstJSig (to_jdg_sig desc).
    Proof.
      constructor.
      - intros [] r x P hr hP. cbn in hr.
        apply in_to_rules in hr as [rd [hr ->]].
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (pd & hpd & hin).
        destruct pd as [| n Q]. 1: discriminate.
        noconf hpd.
        intros Γ σ Δ m hs h.
        apply In_nth_error in hin as [i hi].
        apply In_nth_error in hr as [ri hr].
        eapply obligation_at in hok as ho. 2-4: eassumption.
        unfold pred_obl in ho. rewrite <- under_iff in ho.
        specialize ho with (x := x) (1 :=
          ev_vs_length (CS := CS) (rd_arity rd) (rd_nterms rd) m
        ).
        cbn in ho.
        apply styping_cstyping in hs.
        specialize ho with (1 := hs).
        erewrite stable_at_nth_error in ho. 2: eassumption.
        cbn in ho. specialize (ho h).
        unfold ev_vals. rewrite ev_vs_subst. exact ho.
      - intros [] r x P hr hP. cbn in hr.
        apply in_to_rules in hr as [rd [hr ->]].
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (pd & e & hin).
        destruct pd as [| n Q]. 1: discriminate.
        noconf e.
        intros Γ m m' h hm.
        unfold ev_vals in *. erewrite <- ev_vs_ext. all: eassumption.
      - intros [] r x hr n i' conv Δ j hP. cbn in hr.
        apply in_to_rules in hr as [rd [hr ->]].
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (j' & hj' & ?).
        destruct j'. 2: discriminate.
        noconf hj'.
        intros X Y f d. reflexivity.
      - intros [] r x hr n i' conv Δ j hP. cbn in hr.
        apply in_to_rules in hr as [rd [hr ->]].
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (j' & hj & ?).
        destruct j'. 2: discriminate.
        noconf hj.
        intros Γ d t h.
        rewrite map_id. assumption.
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
