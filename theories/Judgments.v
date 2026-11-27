From Stdlib Require Import Utf8.
From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require Import ParamSyntax.
Module P := ParamSyntax.

Set Default Goal Selector "!".

Section WithSignature.
  Context {sig : signature}.

  (** Notations for expressions with known kinds. *)
  #[local] Reserved Notation "'mterm'" (at level 0).

  (* Reuse the notations from [ParamSyntax.v] *)
  #[local] Notation "'term'" := (P.expr Kt) (at level 0).

  Unset Elimination Schemes.

  (* Meta variables *)
  (* Record mvar := {
    (* Meta variables do not have binders, so we can use names easily. We use natural numbers for names *)
    name : nat;

    (* Local scope of a mvar, i.e. the number of terms that will be able to be substituted in this mvar *)
    lscope : nat
  }. *)
  (* NOTE : two meta variables with the same name but with different lscope are different meta variables. It is not problematic, but one need to keep that in mind when doing things *)
  Definition mvar := nat.


  (** Terms over an abstract signature.
      Terms are indexed by a kind.
      Terms are also intrinsically scoped *)
  Inductive mexpr : kind → nat → Type :=
  | (** Term variable. *)
    M_var scope : ∀ i, i < scope → mterm scope
  | (** Non-variable expr constructor, applied to a list of arguments. *)
    M_ctor scope : ∀ c, mexpr (Kal (ctor_type c)) scope → mterm scope
  | (** Empty argument list. *)
    M_al_nil scope : mexpr (Kal []) scope
  | (** Non-empty argument list. *)
    M_al_cons scope {ty tys} :
    mexpr (Ka ty) scope →
    mexpr (Kal tys) scope →
    mexpr (Kal (ty :: tys)) scope
  | (** Base argument (e.g. bool or string). *)
    M_abase scope : ∀ b, eval_base b → mexpr (Ka (AT_base b)) scope
  | (** Term argument. *)
    M_aterm scope : mterm scope → mexpr (Ka AT_term) scope
  | (** Bind a term in an argument. *)
    M_abind scope {ty} : mexpr (Ka ty) (S scope) → mexpr (Ka (AT_bind ty)) scope
  | (**
    Meta variable applyed to a substitution
    A substitution is a list of terms
    **)
    M_mvar scope (k : mvar) (σ : list (mterm scope)) :
      mterm scope

  where "'mterm'" := (mexpr Kt).

  Set Elimination Schemes.
  Derive NoConfusion for mexpr.

  (** Better induction scheme for [mexpr] **)
  Section MExprInd.

    Context (P : ∀ k s, mexpr k s → Prop).

    Context (H_var : ∀ s i (Hsi : i < s), P _ _ (M_var s i Hsi)).
    Context (H_ctor : ∀ s c al, P _ _ al → P _ _ (M_ctor s c al)).
    Context (H_al_nil : ∀ s, P _ _ (M_al_nil s)).
    Context (H_al_cons :
      ∀ s ty tys (a : mexpr (Ka ty) _) (al : mexpr (Kal tys) _),
        P _ _ a → P _ _ al → P _ _ (M_al_cons s a al)
    ).
    Context (H_abase : ∀ s b x, P _ _ (M_abase s b x)).
    Context (H_aterm : ∀ s t, P _ _ t → P _ _ (M_aterm s t)).
    Context (H_abind :
      ∀ s ty (a : mexpr (Ka ty) _), P _ _ a → P _ _ (M_abind s a)
    ).
    Context (H_mvar : ∀ s k σ,
      Forall (P _ s) σ →
      P _ _ (M_mvar s k σ)
    ).

    Fixpoint mexpr_ind k s (t : mexpr k s) {struct t} : P k s t.
    Proof.
      destruct t.
      - apply H_var.
      - apply H_ctor. apply mexpr_ind.
      - apply H_al_nil.
      - apply H_al_cons ; apply mexpr_ind.
      - apply H_abase.
      - apply H_aterm. apply mexpr_ind.
      - apply H_abind. apply mexpr_ind.
      - apply H_mvar.
        induction σ.
        + apply Forall_nil.
        + apply Forall_cons.
          * apply mexpr_ind.
          * assumption.
    Qed.

  End MExprInd.

  Register Scheme mexpr_ind as ind_dep for mexpr.

  (** Utils for meta variables **)
  Section UtilsMvar.

    #[refine] Definition var n : mterm (S n) := M_var _ n _.
    Proof. lia. Defined.

  End UtilsMvar.

  (** Instantiation of expressions with meta variables into ones without **)
  Section Instantiation.

    Definition menv := mvar → nat → P.expr Kt.
    Definition default_menv : menv := λ k _, E_var k.

    Equations inst {s k} (m : menv) (t : mexpr k s) : P.expr k :=
      inst m (M_var _ i _) := E_var i ;
      inst m (M_ctor _ c al) := E_ctor c (inst m al) ;
      inst m (M_al_nil _) := E_al_nil ;
      inst m (M_al_cons _ a al) := E_al_cons (inst m a) (inst m al) ;
      inst m (M_abase _ b x) := E_abase b x ;
      inst m (M_aterm _ t) := E_aterm (inst m t) ;

      inst m (M_abind _ a) :=
        (* We don't shift anything ;
          it is dealt with when instantiating a meta variable *)
        E_abind (inst m a);
      inst m (M_mvar _ k σ) :=
        (* Again, I need this so that Rocq knows that the recursive call is
          made on elements of σ *)
        let ev_σ := map (inst m) σ in
        substitute
          (λ i,
            match nth_error ev_σ i with
            | Some t => t
            (* [- List.length σ] shifts the indexes to take into account the
              substitution *)
              (* [+ s] takes into account the scope,
                "the number of lambdas we are under" *)
            | None => E_var (i - List.length σ + s)
            end
          )
          (m k (List.length σ)).

    Lemma map_proper X Y (l : list X) (f g : X → Y) :
      (Forall (λ t : X, f t = g t) l) →
      map f l = map g l.
    Proof.
      intros h.
      induction h.
      - reflexivity.
      - simpl. congruence.
    Qed.

    #[export] Instance inst_proper_instance {k s} :
      Proper (eq2 ==> eq ==> eq) (@inst s k).
    Proof.
      intros m m' Hm t' t Ht. subst.
      induction t in m, m', Hm |- *. all: simpl in *.
      all: try congruence.
      all: try firstorder congruence.
      all: try solve [ f_equal ; firstorder congruence ].
      rewrite Hm.
      apply substitute_proper. 2: reflexivity.
      intro i.
      erewrite map_proper.
      2:{
        eapply Forall_impl. 2: eassumption.
        intros a e. simpl in e. apply e. apply Hm.
      }
      reflexivity.
    Qed.

    Lemma inst_proper m m' {k s} (t : mexpr k s) :
      m =₂ m' →
      inst m t = inst m' t.
    Proof.
      intros Hm.
      rewrite Hm. reflexivity.
    Qed.

  End Instantiation.

  Notation "f =₂ g" := (eq2 f g) (at level 75).

  (** Definitions of contexts **)
  (* Functor of declarations that will be stored in contexts *)
  Section Contexts.

    Context (declF : Type → Type).
    Context `{HFmapDecl : FMap declF}.
    Context `{Hdecl : !Eq1Functor declF}.

    Definition mdecl (s : nat) := declF (mterm s).

    Inductive mctx (scope : nat) | : nat → Type :=
    | mnil : mctx 0
    | mcons {n : nat} (d : mdecl (n+scope)) (Γ : mctx n) : mctx (S n).

    Arguments mnil {scope}.
    Arguments mcons {scope}.

    Definition ctx := list (declF term).

    Equations inst_ctx {s n} (m : menv) (Γ : mctx s n) : ctx :=
      inst_ctx m mnil := [] ;
      inst_ctx m (mcons d Γ) := (fmap declF (inst m) d) :: (inst_ctx m Γ).

    (** Instantiation preserves length **)
    Lemma inst_length {s n} (Γ : mctx s n) m :
      n = Datatypes.length (inst_ctx m Γ).
    Proof.
      induction Γ as [| n d Γ ih] in m |- *. all: simpl.
      - reflexivity.
      - f_equal. apply ih.
    Qed.

    Equations rename_ctx (ρ : ren) (Γ : ctx) : ctx :=
      rename_ctx ρ [] => [] ;
      rename_ctx ρ (d::Γ) =>
        fmap _ (rename (up_rens (Datatypes.length Γ) ρ)) d ::
        rename_ctx ρ Γ.

    (* TODO : should be moved in ParamSyntax *)
    Equations up_substs (k : nat) (σ : subst) : subst :=
      up_substs 0 σ := σ ;
      up_substs (S k) σ := up_subst (up_substs k σ).

    Lemma up_substs_lt (i k : nat) (σ : subst) :
      i < k →
      up_substs k σ i = E_var i.
    Proof.
      intros hik.
      induction k as [| k ih] in i, hik |- *. all: simpl.
      - lia.
      - destruct i as [|i].
        + simpl. reflexivity.
        + simpl. unfold srcomp, rshift.
          rewrite ih. 2: lia.
          reflexivity.
    Qed.

    Lemma up_substs_gt (i k : nat) (σ : subst) :
      i ≥ k →
      up_substs k σ i = rename (λ i, i + k) (σ (i - k)).
    Proof.
      intros h.
      induction k as [| k ih] in i, h |- *. all: simpl.
      - erewrite <- ren_rid at 1.
        apply rename_proper.
        + unfold rid. intro. lia.
        + f_equal. lia.
      - destruct i as [|i]. 1: lia.
        cbn. unfold srcomp, rshift. rewrite ih. 2: lia.
        rewrite ren_ren. apply rename_proper. 2: reflexivity.
        unfold rcomp. intro. lia.
    Qed.

    Lemma up_substs_add n m σ :
      up_substs n (up_substs m σ) =₁ up_substs (n + m) σ.
    Proof.
      induction n.
      - reflexivity.
      - cbn. apply up_subst_proper. assumption.
    Qed.

    Equations subst_ctx (σ : subst) (Γ : ctx) : ctx :=
      subst_ctx σ [] => [] ;
      subst_ctx σ (d :: Γ) =>
        fmap _ (substitute (up_substs (Datatypes.length Γ) σ)) d ::
        subst_ctx σ Γ.

    (* Belonging to a context *)
    Reserved Notation "Γ ∋ n : d" (at level 70, n at level 50).

    Inductive inctx : ctx → nat → declF term → Prop :=
    | in_head d Γ :
      (d::Γ) ∋ 0 : fmap _ (rename rshift) d
    | in_tail d d' Γ n :
      Γ ∋ n : d →
      d'::Γ ∋ S n : fmap _ (rename rshift) d
    where "Γ ∋ n : A" := (inctx Γ n A).

    (* Allows to use existential variables easily *)
    Lemma conv_in_d Γ n d d' :
      Γ ∋ n : d →
      d = d' →
      Γ ∋ n : d'.
    Proof.
      intros. subst. assumption.
    Qed.

    Lemma conv_in_n Γ n m d :
      Γ ∋ n : d →
      n = m →
      Γ ∋ m : d.
    Proof.
      intros. subst. assumption.
    Qed.

  End Contexts.

  Arguments mnil {_ scope}.
  Arguments mcons {_ scope}.
  Arguments inctx [_] {_}.
  Arguments inst_ctx [_] {_ _ _}.
  Arguments rename_ctx [_] {_}.
  Arguments subst_ctx [_] {_}.

  Notation "Γ ∋ n : d" := (inctx Γ n d) (at level 70, n at level 50).

  (** Definition of judgments **)
  Section Jdg.

    Context (jdgF : Type → Type).
    Context `{HFmapJdg : FMap jdgF}.
    Context `{Hjdg : !Eq1Functor jdgF}.

    Definition mjdg (s : nat) := jdgF (mterm s).
    Definition jdg := jdgF term.

    (** Instantiating and renaming a judgment is much more straightforward **)
    Definition inst_jdg {s} m : mjdg s → jdg := fmap jdgF (inst m).
    Definition rename_jdg ρ : jdg → jdg := fmap jdgF (rename ρ).
    Definition substitute_jdg σ : jdg → jdg := fmap jdgF (substitute σ).

  End Jdg.

  Arguments inst_jdg [_] {_ _}.
  Arguments rename_jdg [_] {_}.
  Arguments substitute_jdg [_] {_}.

  (** Definition of a signature of rules **)
  Class IDecl := declF : Type → Type.

  Class IJdg (I : Type) := jdgF : I → Type → Type.

  Context {I : Type} {HEqDecI : EqDec I}.
  Context {InstIDecl : IDecl} `{InstIJdg : IJdg I}.
  Context {FMapDeclF : FMap declF}.
  Context {FuncDeclF : Eq1Functor declF}.
  Context {FMapJdgF : ∀ i, FMap (jdgF i)}.
  Context {FuncJdgF : ∀ i, Eq1Functor (jdgF i)}.

  Section RulesSignature.

    (* Contexts in premises must be closed, and judgments must be scoped by the
      context *)
    Variant premise (i : I) :=
    | prem_pred (P : ctx declF → menv → Prop)
    | prem_ind i' {n} (Δ : mctx declF 0 n) (j : mjdg (jdgF i') n).

    Derive NoConfusion for premise.

    (* The judgment of the conclusion must be closed *)
    (* A rule is parametrized by a type, e.g. a rule for any natural number *)
    Record rule (i : I) := {
      param : Type ;
      premises : param → list (premise i) ;
      conclusion : param → mjdg (jdgF i) 0
    }.

    Record jdg_sig := {
      rules : ∀ i : I, list (rule i)
    }.

  End RulesSignature.

  Arguments param {_}.
  Arguments premises {_}.
  Arguments conclusion {_}.

  Context {jsig : jdg_sig}.

  Class IMakeJdg :=
    make_jdg : ∀ i : I, ∀ X, declF X → X → jdgF i X.

  Context {InstIMakeJdg : IMakeJdg}.
  Context `{NatMakeJdg : ∀ i : I, NatFromProd (make_jdg i)}.

  (* make_jdg is a natural transformation from (declF * Id) to jdgF *)

  (** Derivation with the rules of the signature **)
  Section Derivation.

    Reserved Notation "Γ ⊢( i ) j" (at level 70, format "Γ  ⊢(  i  )  j").

    Inductive proof : ∀ i, ctx declF → jdg (jdgF i) → Prop :=
    (*
      We need a context, a rule and an instanciation of this rule, that will
      give the conclusion
    *)
    | step i (m : menv) (Γ : ctx declF) (r : rule i) (x : r.(param)) :
      (* The rule must be in the signature *)
      In r (jsig.(rules) i) →
      (* Satisfy all inductive premises *)
      (
        ∀ i' {n} (Δ : mctx declF 0 n) (j : mjdg (jdgF i') n),
          In (prem_ind i i' Δ j) (r.(premises) x) →
          (inst_ctx m Δ ++ Γ) ⊢(i') inst_jdg m j
      ) →
      (* Satisfy all predicate premise, depending on Γ and m *)
      (
        ∀ P,
          In (prem_pred i P) (r.(premises) x) →
          P Γ m
      ) →
      Γ ⊢(i) inst_jdg m (r.(conclusion) x)

    | tvar i (Γ : ctx declF) (n : nat) (d : declF term) :
      Γ ∋ n : d →
      Γ ⊢(i) make_jdg i term d (E_var n)

    where "Γ ⊢( i ) j" := (proof i Γ j).

    Lemma conv_proof_j i Γ j j' :
      Γ ⊢(i) j →
      j = j' →
      Γ ⊢(i) j'.
    Proof.
      intros. subst. assumption.
    Qed.

    Lemma conv_proof_c i Γ Γ' j :
      Γ ⊢(i) j →
      Γ = Γ' →
      Γ' ⊢(i) j.
    Proof.
      intros. subst. assumption.
    Qed.

  End Derivation.

  Notation "Γ ⊢( i ) j" := (proof i Γ j) (at level 70).

  (** Behaviour of renamings **)
  Section Renamings.

    (** Commutation between renaming and instantiation lemma **)
    Lemma scoped_rename_inst {k} (n : nat) (t : mexpr k n) m ρ :
      rename (up_rens n ρ) (inst m t) =
      inst (λ k s, rename (up_rens s ρ) (m k s)) t.
    Proof.
      induction t in m, ρ |- *.
      all: simpl in *.
      all: try (rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity).
      - f_equal. apply up_rens_lt. assumption.
      - rewrite ren_subst, subst_ren.
        unfold srcomp, rscomp.
        apply substitute_proper. 2: reflexivity.
        intro i.
        rewrite !nth_error_map.
        destruct (nth_error σ i) as [t|] eqn: e.
        + cbn. rewrite up_rens_lt.
          2:{ apply nth_error_Some. congruence. }
          rewrite e. cbn.
          rewrite Forall_forall in H.
          apply nth_error_In in e. eauto.
        + cbn.
          apply nth_error_None in e as h.
          rewrite !up_rens_gt. 2,3: lia.
          erewrite nth_error_None_eq. 2: lia.
          cbn. f_equal. f_equal.
          replace (i - List.length σ + s - s) with (i - List.length σ) by lia.
          lia.
    Qed.

    Corollary closed_rename_inst {k} (t : mexpr k 0) m ρ :
      rename ρ (inst m t) =
      inst (λ k s, rename (up_rens s ρ) (m k s)) t.
    Proof.
      apply (scoped_rename_inst 0).
    Qed.

    Lemma scoped_ctx_rename_inst {s n} (Γ : mctx declF s n) m ρ :
      rename_ctx (up_rens s ρ) (inst_ctx m Γ) =
      inst_ctx (λ k s, rename (up_rens s ρ) (m k s)) Γ.
    Proof.
      induction Γ as [| n d Γ ih] in m, ρ |- *.
      - reflexivity.
      - cbn. rewrite ih. f_equal.
        rewrite <- inst_length.
        rewrite func_comp.
        apply rew_eq1. intro t.
        rewrite <- scoped_rename_inst.
        apply rename_proper. 2: reflexivity.
        apply up_rens_add.
    Qed.

    Lemma scoped_jdg_rename_inst {i s} (j : mjdg (jdgF i) s) m ρ :
      rename_jdg (up_rens s ρ) (inst_jdg m j) =
      inst_jdg (λ k s, rename (up_rens s ρ) (m k s)) j.
    Proof.
      unfold rename_jdg, inst_jdg.
      rewrite func_comp. apply (rew_eq1 (F := jdgF i)).
      intro t. apply scoped_rename_inst.
    Qed.

    Corollary closed_jdg_rename_inst {i} (j : mjdg (jdgF i) 0) m ρ :
      rename_jdg ρ (inst_jdg m j) =
      inst_jdg (λ k s, rename (up_rens s ρ) (m k s)) j.
    Proof.
      apply (@scoped_jdg_rename_inst i 0).
    Qed.

    (** Typing of a renaming **)
    Reserved Notation "Δ ⊢r ρ : Γ" (at level 70, ρ at level 50).

    Inductive rtyping : ctx declF → ren → ctx declF → Prop :=
    | rtyping_empty Δ ρ :
      Δ ⊢r ρ : []
    | rtyping_cons Δ ρ Γ d :
      Δ ⊢r rcomp rshift ρ : Γ →
      Δ ∋ (ρ 0) : fmap _ (rename (rcomp rshift ρ)) d →
      Δ ⊢r ρ : d::Γ
    where "Δ ⊢r ρ : Γ " := (rtyping Δ ρ Γ).

    Lemma conv_rtyping Δ ρ ρ' Γ :
      Δ ⊢r ρ : Γ →
      ρ = ρ' →
      Δ ⊢r ρ' : Γ.
    Proof.
      intros. subst. assumption.
    Qed.

    Derive Signature for rtyping.

    Class RenJSig := {
      prem_ren :
        ∀ (i : I) (r : rule i) x P,
          In r (jsig.(rules) i) →
          In (prem_pred i P) (r.(premises) x) →
          ∀ Γ ρ Δ m,
            Δ ⊢r ρ : Γ →
            P Γ m →
            P Δ (λ k s, rename (up_rens s ρ) (m k s))
    }.

    (** Renaming lemmas **)
    #[export] Instance rtyping_proper :
      Proper (eq ==> eq1 ==> eq ==> Basics.impl) rtyping.
    Proof.
      intros Δ' Δ HΔ ρ ρ' Hρ Γ' Γ HΓ H. subst.
      induction H in ρ', Hρ |- *. 1: constructor.
      constructor.
      - firstorder eauto using congr_rcomp.
      - rewrite <- Hρ. eapply conv_in_d. 1: eassumption.
        apply rew_eq1. intro t.
        apply rename_proper. 2: reflexivity.
        unfold rcomp, rshift. intro. apply Hρ.
    Qed.

    Lemma conv_rtype_r Δ ρ ρ' Γ :
      Δ ⊢r ρ : Γ →
      ρ =₁ ρ' →
      Δ ⊢r ρ' : Γ.
    Proof.
      intros Hρ Heq. rewrite <- Heq. assumption.
    Qed.

    Lemma rename_in Δ Γ ρ n d :
      Γ ∋ n : d →
      Δ ⊢r ρ : Γ →
      Δ ∋ ρ n : fmap _ (rename ρ) d.
    Proof.
      intros HΓ Hρ.
      induction HΓ as [| ????? ih] in Δ, ρ, Hρ |- *.
      all: depelim Hρ.
      - rewrite func_comp.
        eapply conv_in_d. 1: eassumption.
        apply rew_eq1. intro t. rewrite ren_ren. reflexivity.
      - eapply conv_in_d.
        + eapply conv_in_n.
          * apply ih. apply Hρ.
          * reflexivity.
        + rewrite func_comp. apply rew_eq1.
          intro t. rewrite ren_ren. reflexivity.
    Qed.

    Lemma rtyping_comp Γ Δ Θ ρ ρ' :
      Δ ⊢r ρ : Γ →
      Θ ⊢r ρ' : Δ →
      Θ ⊢r rcomp ρ ρ' : Γ.
    Proof.
      intros Hρ Hρ'.
      induction Hρ in Θ, ρ', Hρ' |- *. 1: constructor.
      constructor.
      - eapply rtyping_proper. 1,3: reflexivity.
        + apply rcomp_assoc.
        + eauto.
      - eapply conv_in_d.
        + unfold rcomp. eapply rename_in. 1: eassumption.
          assumption.
        + rewrite func_comp. apply rew_eq1. intro.
          rewrite ren_ren, rcomp_assoc. reflexivity.
    Qed.

    Lemma weaken_rtyping Γ ρ Δ A :
      Δ ⊢r ρ : Γ →
      A :: Δ ⊢r rcomp ρ S : Γ.
    Proof.
      intros Hρ.
      induction Hρ in A |- *. 1: constructor.
      constructor.
      - eauto.
      - eapply conv_in_d.
        + constructor. eassumption.
        + rewrite func_comp. apply rew_eq1. intro.
          rewrite ren_ren, rcomp_assoc. reflexivity.
    Qed.

    Lemma up_rtyping Γ ρ Δ d :
      Δ ⊢r ρ : Γ →
      fmap _ (rename ρ) d :: Δ ⊢r up_ren ρ : d :: Γ.
    Proof.
      intros Hρ. constructor.
      - apply weaken_rtyping. assumption.
      - eapply conv_in_d.
        + simpl. constructor.
        + rewrite func_comp. apply rew_eq1. intro.
          rewrite ren_ren. reflexivity.
    Qed.

    Corollary up_rtyping_n Γ ρ Δ Θ :
      Δ ⊢r ρ : Γ →
      (rename_ctx ρ Θ) ++ Δ ⊢r up_rens (Datatypes.length Θ) ρ : Θ ++ Γ.
    Proof.
      intros h.
      induction Θ in Γ, ρ, Δ, h |- *. all: cbn in *.
      - assumption.
      - apply up_rtyping. eauto.
    Qed.

    Lemma id_rtyping Γ :
      Γ ⊢r rid : Γ.
    Proof.
      induction Γ as [| a Γ ih]. 1: constructor.
      replace a with (fmap _ (rename rid) a) at 1.
      2:{
        rewrite <- func_id. apply rew_eq1. intro. apply ren_rid.
      }
      rewrite <- up_ren_rid at 2. apply up_rtyping. assumption.
    Qed.

    Context {HRenSig : RenJSig}.

    Theorem preserve_renaming i Γ j Δ ρ :
      Γ ⊢(i) j →
      Δ ⊢r ρ : Γ →
      Δ ⊢(i) rename_jdg ρ j.
    Proof.
      intros Hj Hρ.
      induction Hj as [i m Γ r x H H0 H1 H2 | ] in Δ, ρ, Hρ |- *.
      (* Case of an inductive/predicate premise *)
      - (* We apply rule [r x] *)
        eapply conv_proof_j.
        { unshelve econstructor. 1: shelve.
          - exact r.
          - exact x.
          - assumption.
          - (* Inductive premise *)
            intros.
            rewrite <- scoped_jdg_rename_inst. eapply H1. 1: eassumption.
            rewrite <- scoped_ctx_rename_inst. simpl.
            eapply conv_rtyping.
            + eapply up_rtyping_n. eassumption.
            + rewrite <- inst_length. reflexivity.
          - (* Predicate premise *)
            intros.
            eapply HRenSig. all: eauto.
            apply H2. apply H3.
        }
        rewrite closed_jdg_rename_inst. reflexivity.
      (* Case of a variable *)
      - unfold rename_jdg.
        rewrite naturality_prod.
        constructor. eapply rename_in. all: eassumption.
    Qed.

    Corollary weaken_typing i Γ j A :
      Γ ⊢(i) j →
      A :: Γ ⊢(i) rename_jdg rshift j.
    Proof.
      intros h.
      eapply preserve_renaming. 1: eassumption.
      apply weaken_rtyping. apply id_rtyping.
    Qed.

  End Renamings.

  Notation "Δ ⊢r ρ : Γ" :=
    (rtyping Δ ρ Γ) (at level 70, ρ at level 50).

  (** Behaviour of substitutions **)
  Section Substitutions.

    (* TODO : should be in ParamSyntax *)

    Definition ren_to_subst (r : ren) : subst :=
      λ i, E_var (r i).

    Lemma ren_is_subst {k} r (t : expr k) :
      rename r t = substitute (ren_to_subst r) t.
    Proof.
      induction t in r |- *.
      all: simpl.
      all: try (rewrite ?IHt, ?IHt1, ?IHt2; reflexivity).
      cbn. rewrite IHt. f_equal. apply substitute_proper. 2: reflexivity.
      intros [|n]. all: reflexivity.
    Qed.

    Corollary ren_is_subst_jdg {i} r (t : jdg (jdgF i)) :
      rename_jdg r t = substitute_jdg (ren_to_subst r) t.
    Proof.
      unfold rename_jdg, substitute_jdg.
      apply (rew_eq1 (F := jdgF i)).
      intro. apply ren_is_subst.
    Qed.

    Lemma ren_to_subst_up_rens n ρ :
      ren_to_subst (up_rens n ρ) =₁ up_substs n (ren_to_subst ρ).
    Proof.
      intro k.
      induction n in ρ, k |- *. 1: reflexivity.
      cbn. unfold ren_to_subst, up_subst. unfold scons. destruct k as [|k].
      - reflexivity.
      - cbn. unfold srcomp, rshift.
        etransitivity. 2:{ eapply rename_proper. 1: reflexivity. eauto. }
        reflexivity.
    Qed.

    (** Commutation lemmas between substitution and instantiation **)
    Lemma scoped_substitute_inst {k} (n : nat) (t : mexpr k n) m σ :
      substitute (up_substs n σ) (inst m t) =
      inst (λ k s, substitute (up_substs s σ) (m k s)) t.
    Proof.
      induction t in m, σ |- *.
      all: simpl in *.
      all: rewrite ?IHt, ?IHt1, ?IHt2 ; try reflexivity.
      - apply up_substs_lt. assumption.
      - rewrite 2!subst_subst.
        unfold scomp. apply substitute_proper. 2: reflexivity.
        intro i.
        destruct (i <? List.length σ0) eqn: Hi.
        + rewrite up_substs_lt.
          2:{ apply PeanoNat.Nat.ltb_lt. assumption. }
          cbn. rewrite 2!nth_error_map.
          apply PeanoNat.Nat.ltb_lt in Hi.
          rewrite <- nth_error_Some in Hi.
          destruct (nth_error σ0 i) as [t|] eqn:Hσ.
          2:{ exfalso. apply Hi. reflexivity. }
          cbn. apply nth_error_In in Hσ. rewrite Forall_forall in H.
          specialize (H _ Hσ).
          apply H.
        + rewrite PeanoNat.Nat.ltb_ge in Hi.
          pose (Hσ := Hi).
          rewrite up_substs_gt. 2: lia.
          rewrite subst_ren.
          unfold rscomp.
          etransitivity.
          2:{
            apply substitute_proper. 2: reflexivity.
            intro i0. assert (List.length σ0 ≤ i0 + List.length σ0) by lia.
            apply nth_error_None in H0.
            rewrite nth_error_map.
            rewrite H0. simpl. reflexivity.
          }
          apply nth_error_None in Hσ. rewrite nth_error_map. rewrite Hσ. simpl.
          rewrite up_substs_gt. 2: lia.
          rewrite ren_is_subst. apply substitute_proper.
          2:{ f_equal. lia. }
          intro i0. unfold ren_to_subst. f_equal. lia.
    Qed.

    Corollary closed_substitute_inst {k} (t : mexpr k 0) m σ :
      substitute σ (inst m t) =
      inst (λ k s, substitute (up_substs s σ) (m k s)) t.
    Proof.
      apply (@scoped_substitute_inst _ 0).
    Qed.

    Lemma scoped_ctx_substitute_inst {s n} (Γ : mctx declF s n) m σ :
      subst_ctx (up_substs s σ) (inst_ctx m Γ) =
      inst_ctx (λ k s, substitute (up_substs s σ) (m k s)) Γ.
    Proof.
      induction Γ as [| n d Γ ih] in m, σ |- *.
      - reflexivity.
      - cbn. rewrite ih. f_equal.
        rewrite <- inst_length.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite <- scoped_substitute_inst.
        apply substitute_proper. 2: reflexivity.
        apply up_substs_add.
    Qed.

    Lemma scoped_jdg_substitute_inst {i s} (j : mjdg (jdgF i) s) m σ :
      substitute_jdg (up_substs s σ) (inst_jdg m j) =
      inst_jdg (λ k s, substitute (up_substs s σ) (m k s)) j.
    Proof.
      unfold substitute_jdg, inst_jdg.
      rewrite func_comp. apply (rew_eq1 (F := jdgF i)).
      intro t.
      apply scoped_substitute_inst.
    Qed.

    Corollary closed_jdg_substitute_inst {i} (j : mjdg (jdgF i) 0) m σ :
      substitute_jdg σ (inst_jdg m j) =
      inst_jdg (λ k s, substitute (up_substs s σ) (m k s)) j.
    Proof.
      apply (@scoped_jdg_substitute_inst i 0).
    Qed.

    (** Typing of a substitution **)
    Reserved Notation "Δ ⊢s σ : Γ" (at level 70, σ at level 50).

    Inductive styping : ctx declF → subst → ctx declF → Prop :=
    | styping_empty Δ σ :
      Δ ⊢s σ : []
    | styping_cons Δ σ Γ d :
      Δ ⊢s rscomp rshift σ : Γ →
      (∀ i,
        Δ ⊢(i) make_jdg i term (fmap _ (substitute (rscomp rshift σ)) d) (σ 0)
      ) →
      Δ ⊢s σ : d::Γ
    where "Δ ⊢s σ : Γ " := (styping Δ σ Γ).

    Lemma conv_styping Δ ρ ρ' Γ :
      Δ ⊢s ρ : Γ →
      ρ = ρ' →
      Δ ⊢s ρ' : Γ.
    Proof.
      intros. subst. assumption.
    Qed.

    Derive Signature for styping.

    Lemma ren_to_subst_typing Γ ρ Δ :
      Δ ⊢r ρ : Γ →
      Δ ⊢s ren_to_subst ρ : Γ.
    Proof.
      intro Hρ. induction Hρ as [| Δ ρ Γ d h ih hρ].
      - constructor.
      - constructor. 1: eauto.
        intros. constructor. eapply conv_in_d. 1: eauto.
        apply rew_eq1. intro. apply ren_is_subst.
    Qed.

    Class SubstJSig := {
      prem_subst :
        ∀ i (r : rule i) x P,
        In r (jsig.(rules) i) →
        In (prem_pred i P) (r.(premises) x) →
        ∀ Γ σ Δ m,
        Δ ⊢s σ : Γ →
        P Γ m →
        P Δ (λ k s, substitute (up_substs s σ) (m k s));

      prem_pred_ext :
        ∀ i (r : rule i) x P,
        In r (jsig.(rules) i) →
        In (prem_pred i P) (r.(premises) x) →
        ∀ Γ m m',
        P Γ m → m =₂ m' → P Γ m'
    }.

    (* Preserving substitutions implies preserving renamings via ren_is_subst *)
    #[export] Instance SubstJdg_RenJdg : SubstJSig → RenJSig.
    Proof.
      intro H.
      constructor.
      intros i r x P hr hp Γ ρ Δ m hρ hm.
      eapply prem_pred_ext.
      1,2: eassumption.
      2:{ intros k s. rewrite <- ren_is_subst. reflexivity. }
      eapply prem_pred_ext. 1,2: eassumption.
      2:{
        intros k s. etransitivity.
        2:{ rewrite ren_to_subst_up_rens. reflexivity. }
        reflexivity.
      }
      eapply prem_subst. 1,2,4: eassumption.
      apply ren_to_subst_typing. assumption.
    Qed.

    (** Substitution lemmas **)
    #[export] Instance styping_proper :
      Proper (eq ==> eq1 ==> eq ==> Basics.impl) styping.
    Proof.
      intros Δ' Δ HΔ σ σ' Hσ Γ' Γ HΓ H. subst.
      induction H as [| Δ σ Γ d H ih H0] in σ', Hσ |- *. 1: constructor.
      constructor.
      - apply ih. apply rscomp_proper. 1: reflexivity. assumption.
      - intros i. eapply conv_proof_j.
        + apply H0.
        + f_equal. 2: apply Hσ.
          apply rew_eq1. intros. intro.
          apply substitute_proper. 2: reflexivity.
          intro. apply Hσ.
    Qed.

    Lemma conv_stype_s Δ σ σ' Γ :
      Δ ⊢s σ : Γ →
      σ =₁ σ' →
      Δ ⊢s σ' : Γ.
    Proof.
      intros Hσ Heq. rewrite <- Heq. assumption.
    Qed.

    Lemma substitute_in i Δ Γ σ n d :
      Γ ∋ n : d →
      Δ ⊢s σ : Γ →
      Δ ⊢(i) make_jdg i term (fmap _ (substitute σ) d) (σ n).
    Proof.
      intros HΓ Hσ.
      induction HΓ as [| ????? ih] in Δ, σ, Hσ |- *.
      all: depelim Hσ.
      - rewrite func_comp.
        eapply conv_proof_j. 1: apply H.
        f_equal. apply rew_eq1. intro.
        rewrite subst_ren. reflexivity.
      - eapply conv_proof_j.
        + apply ih. apply Hσ.
        + rewrite func_comp. f_equal. apply rew_eq1. intro.
          rewrite subst_ren. reflexivity.
    Qed.

    Context `{HSubstSig : SubstJSig}.

    Lemma weaken_styping Γ σ Δ d :
      Δ ⊢s σ : Γ →
      d::Δ ⊢s srcomp σ S : Γ.
    Proof.
      intros Hσ.
      induction Hσ as [| ????? ih ?] in d |- *. 1: constructor.
      constructor.
      - apply ih.
      - intros i. eapply conv_proof_j.
        + apply weaken_typing. eauto.
        + simpl. unfold rename_jdg.
          rewrite naturality_prod. f_equal.
          rewrite func_comp. apply rew_eq1. intro.
          rewrite ren_subst. reflexivity.
    Qed.

    Lemma up_styping Γ σ Δ d :
      Δ ⊢s σ : Γ →
      (fmap _ (substitute σ) d)::Δ ⊢s up_subst σ : d::Γ.
    Proof.
      intros Hσ. constructor.
      - apply weaken_styping. assumption.
      - simpl. constructor.
        eapply conv_in_d.
        + constructor.
        + rewrite func_comp.
          apply rew_eq1. intro. rewrite ren_subst. reflexivity.
    Qed.

    Corollary up_styping_n Γ σ Δ Θ :
      Δ ⊢s σ : Γ →
      (subst_ctx σ Θ) ++ Δ ⊢s up_substs (Datatypes.length Θ) σ : Θ ++ Γ.
    Proof.
      induction Θ in Γ, σ, Δ |- *; intros; simpl in *.
      - assumption.
      - apply up_styping. eauto.
    Qed.

    Lemma id_styping Γ :
      Γ ⊢s sid : Γ.
    Proof.
      induction Γ as [| a Γ ih]. 1: constructor.
      replace a with (fmap _ (substitute sid) a) at 1.
      2: {
        rewrite <- func_id. apply rew_eq1. intro. apply subst_sid.
      }
      rewrite <- up_subst_sid at 2. apply up_styping. assumption.
    Qed.

    Theorem preserve_subst i Γ j Δ σ :
      Γ ⊢(i) j →
      Δ ⊢s σ : Γ →
      Δ ⊢(i) substitute_jdg σ j.
    Proof.
      intros Hj Hσ.
      induction Hj as [i m Γ r x H H0 H1 H2 | ] in Δ, σ, Hσ |- *.
      (* Case of an inductive/predicate premise *)
      - (* We apply rule [r x] *)
        eapply conv_proof_j.
        1: unshelve econstructor.
        1: shelve.
        1: exact r. 1: exact x.
        1: assumption.
        3: {symmetry. apply closed_jdg_substitute_inst. }
        + (* Inductive premise *)
          intros.
          rewrite <- scoped_jdg_substitute_inst. eapply H1. 1: apply H3.
          rewrite <- scoped_ctx_substitute_inst. simpl.
          eapply conv_styping.
          * eapply up_styping_n. assumption.
          * f_equal. symmetry. apply inst_length.
        + (* Predicate premise *)
          intros.
          eapply HSubstSig. 1: apply H. 1: apply H3. 1: apply Hσ.
          apply H2. assumption.
      (* Case of a variable *)
      - unfold substitute_jdg.
        rewrite naturality_prod.
        eapply substitute_in. 1: apply H.
        assumption.
    Qed.

  End Substitutions.

  Notation "Δ ⊢s σ : Γ" :=
    (styping Δ σ Γ) (at level 70, σ at level 50).

End WithSignature.

Arguments mnil {_ _ scope}.
Arguments mcons {_ _ scope _}.
Arguments inctx {_} [_] {_}.

Notation "Γ ∋ n : d" := (inctx Γ n d) (at level 70, n at level 50).

Arguments inst_ctx {_} [_] {_ _ _}.
Arguments rename_ctx {_} [_] {_}.
Arguments subst_ctx {_} [_] {_}.

Arguments prem_ind {_ _ _ _ _} _ {_}.

Notation "Γ ⊢( i ) j" := (proof i Γ j) (at level 70).

Notation "Δ ⊢r ρ : Γ" := (rtyping Δ ρ Γ) (at level 70, ρ at level 50).
Notation "Δ ⊢s σ : Γ" := (styping Δ σ Γ) (at level 70, σ at level 50).

Arguments IMakeJdg (_) {_ _}.

Arguments RenJSig {_ _ _ _ _} (_).
Arguments SubstJSig {_ _ _ _ _ _} (_) {_}.
