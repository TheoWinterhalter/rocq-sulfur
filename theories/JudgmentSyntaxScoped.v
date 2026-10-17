From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require Import ParamSyntax.
Module P := ParamSyntax.

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
  Inductive mexpr : kind -> nat -> Type :=
  | (** Term variable. *)
    M_var scope : forall i, i < scope -> mterm scope
  | (** Non-variable expr constructor, applied to a list of arguments. *)
    M_ctor scope : forall c, mexpr (Kal (ctor_type c)) scope -> mterm scope
  | (** Empty argument list. *)
    M_al_nil scope : mexpr (Kal []) scope
  | (** Non-empty argument list. *)
    M_al_cons scope {ty tys} : mexpr (Ka ty) scope -> mexpr (Kal tys) scope -> mexpr (Kal (ty :: tys)) scope
  | (** Base argument (e.g. bool or string). *)
    M_abase scope : forall b, eval_base b -> mexpr (Ka (AT_base b)) scope
  | (** Term argument. *)
    M_aterm scope : mterm scope -> mexpr (Ka AT_term) scope
  | (** Bind a term in an argument. *)
    M_abind scope {ty} : mexpr (Ka ty) (S scope) -> mexpr (Ka (AT_bind ty)) scope
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
    Context (P : forall k s, mexpr k s -> Prop).

    Context (H_var : forall s i (Hsi : i < s), P _ _ (M_var s i Hsi)).
    Context (H_ctor : forall s c al, P _ _ al -> P _ _ (M_ctor s c al)).
    Context (H_al_nil : forall s, P _ _ (M_al_nil s)).
    Context (H_al_cons : forall s ty tys (a : mexpr (Ka ty) _) (al : mexpr (Kal tys) _),
      P _ _ a -> P _ _ al -> P _ _ (M_al_cons s a al)).
    Context (H_abase : forall s b x, P _ _ (M_abase s b x)).
    Context (H_aterm : forall s t, P _ _ t -> P _ _ (M_aterm s t)).
    Context (H_abind : forall s ty (a : mexpr (Ka ty) _), P _ _ a -> P _ _ (M_abind s a)).
    Context (H_mvar : forall s k σ,
      Forall (P _ s) σ ->
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
      (* I have to make an induction on σ, otherwise the Guard condition does not work. With the induction on σ, we are sure that the recursive calls are made on elements of σ, i.e. subterms *)
      induction σ.
      + apply Forall_nil.
      + apply Forall_cons. apply mexpr_ind. apply IHσ.
    Qed.

  End MExprInd.

  Register Scheme mexpr_ind as ind_dep for mexpr.

  (** Utils for meta variables **)
  Section UtilsMvar.
    #[refine] Definition var n : mterm (S n) := M_var _ n _.
    Proof. lia. Defined.
  End UtilsMvar.

  (** Instantiation of an expression with meta variables into expressions without **)
  Section Instantiation.
    Definition menv := mvar -> nat -> P.expr Kt.
    Definition default_menv : menv := fun k _ => E_var k.

    Equations inst {s k} (m : menv) (t : mexpr k s) : P.expr k :=
    inst m (M_var _ i _) := E_var i ;
    inst m (M_ctor _ c al) := E_ctor c (inst m al) ;
    inst m (M_al_nil _) := E_al_nil ;
    inst m (M_al_cons _ a al) := E_al_cons (inst m a) (inst m al) ;
    inst m (M_abase _ b x) := E_abase b x ;
    inst m (M_aterm _ t) := E_aterm (inst m t) ;

    inst m (M_abind _ a) :=
      (* We don't shift anything ; it is dealt with when instantiating a meta variable *)
      E_abind (inst m a);
    inst m (M_mvar _ k σ) :=
      (* Again, I need this so that Rocq knows that the recursive call is made on elements of σ *)
      let ev_σ := map (inst m) σ in
      substitute
        (fun i =>
          match nth_error ev_σ i with
          | Some t => t
          (* [- List.length σ] shifts the indexes to take into account the substitution *)
            (* [+ s] takes into account the scope, "the number of lambdas we are under" *)
          | None => E_var (i - List.length σ + s)
          end
        )
        (m k (List.length σ)).

    Lemma map_proper :
      forall X Y (l : list X) (f g : X -> Y), (Forall (fun t : X => f t = g t) l) ->
      map f l = map g l.
    Proof.
      intros X Y l. induction l; intros.
      - reflexivity.
      - simpl. erewrite IHl. 2: {apply (Forall_inv_tail H). }
        apply Forall_inv in H. rewrite H. reflexivity.
    Qed.

    #[export] Instance inst_proper_instance {k s} :
      Proper (eq2 ==> eq ==> eq) (@inst s k).
    Proof.
      intros m m' Hm t' t Ht. subst.
      induction t in m, m', Hm |- *; simpl in *; intros.
      - reflexivity.
      - erewrite IHt. reflexivity. assumption.
      - reflexivity.
      - erewrite IHt1, IHt2. reflexivity. assumption. assumption.
      - reflexivity.
      - erewrite IHt. reflexivity. assumption.
      - f_equal. apply IHt. setoid_rewrite Hm. reflexivity.
      - rewrite Hm.
        apply substitute_proper. 2: reflexivity.
        intro i.
        erewrite map_proper.
        2: {
          eapply Forall_impl. 2: apply H.
          intros. simpl in H0. apply H0. apply Hm.
        } reflexivity.
    Qed.

    Lemma inst_proper m m' :
      m =₂ m' -> forall {k s} (t : mexpr k s),
      inst m t = inst m' t.
    Proof.
      intros Hm k s t.
      rewrite Hm. reflexivity.
    Qed.
  End Instantiation.
  Notation "f =₂ g" := (eq2 f g) (at level 75).

  (** Definitions of contexts **)
  (* Functor of declarations that will be stored in contexts *)
  Section Contexts.
    Context (declF : Type -> Type)
    `{HFmapDecl : FMap declF}
    `{Hdecl : !Eq1Functor declF}.
    Definition mdecl (s : nat) := declF (mterm s).

    Inductive mctx (scope : nat) | : nat -> Type :=
    | mnil : mctx 0
    | mcons {n : nat}
      (d : mdecl (n+scope)) (Γ : mctx n) :
      mctx (S n).
    Arguments mnil {scope}.
    Arguments mcons {scope}.

    Definition ctx := list (declF term).

    Equations inst_ctx {s n} (m : menv) (Γ : mctx s n) : ctx :=
    inst_ctx m mnil := [] ;
    inst_ctx m (mcons d Γ) := (fmap declF (inst m) d)::(inst_ctx m Γ).

    (** Instantiation preserves length **)
    Lemma inst_length {s n} (Γ : mctx s n) :
      forall m, n = Datatypes.length (inst_ctx m Γ).
    Proof.
      induction Γ; intros; simpl. reflexivity. f_equal. apply IHΓ.
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
      i < k -> up_substs k σ i = E_var i.
    Proof.
      intro. induction k in i, H |- *; simpl.
      - lia.
      - destruct i as [|i]. simpl. reflexivity.
        simpl. unfold srcomp, rshift. rewrite IHk. reflexivity. lia.
    Qed.

    Lemma up_substs_gt (i k : nat) (σ : subst) :
      i >= k -> up_substs k σ i = rename (fun i => i + k) (σ (i - k)).
    Proof.
      induction k in i |- *; intros; simpl.
      - transitivity (σ (i - 0)).
        assert (i = i - 0) by lia. rewrite H0 at 1. reflexivity.
        etransitivity. symmetry. apply ren_rid.
        apply rename_proper. 2: reflexivity. intro. unfold rid. lia.
      - destruct i as [|i]; simpl. lia.
        unfold srcomp, rshift. rewrite IHk. 2: lia.
        rewrite ren_ren. apply rename_proper. 2: reflexivity.
        unfold rcomp. intro. lia.
    Qed.

    Lemma up_substs_add n m σ :
      up_substs n (up_substs m σ) =₁ up_substs (n + m) σ.
    Proof.
      induction n; simpl. reflexivity.
      apply up_subst_proper. assumption.
    Qed.

    Equations subst_ctx (σ : subst) (Γ : ctx) : ctx :=
    subst_ctx σ [] => [] ;
    subst_ctx σ (d :: Γ) =>
      fmap _ (substitute (up_substs (Datatypes.length Γ) σ)) d ::
      subst_ctx σ Γ.

    (* Belonging to a context *)
    Reserved Notation "Γ ∋ n : d" (at level 70, n at level 50).
    Inductive inctx : ctx -> nat -> declF term -> Prop :=
    | in_head d Γ :
      (d::Γ) ∋ 0 : fmap _ (rename rshift) d
    | in_tail d d' Γ n :
      Γ ∋ n : d ->
      d'::Γ ∋ S n : fmap _ (rename rshift) d
    where "Γ ∋ n : A" := (inctx Γ n A).

    (* Allows to use existential variables easily *)
    Lemma conv_in_d Γ n d d' :
      Γ ∋ n : d ->
      d = d' ->
      Γ ∋ n : d'.
    Proof. intros; subst; assumption. Qed.
    Lemma conv_in_n Γ n m d :
      Γ ∋ n : d ->
      n = m ->
      Γ ∋ m : d.
    Proof. intros; subst; assumption. Qed.
  End Contexts.
  Arguments mnil {_ scope}.
  Arguments mcons {_ scope}.
  Arguments inctx [_] {_}.
  Notation "Γ ∋ n : d" := (inctx Γ n d) (at level 70, n at level 50).
  Arguments inst_ctx [_] {_ _ _}.
  Arguments rename_ctx [_] {_}.
  Arguments subst_ctx [_] {_}.

  (** Definition of judgments **)
  Section Judgments.
    Context (jdgF : Type -> Type)
    `{HFmapJdg : FMap jdgF}
    `{Hjdg : !Eq1Functor jdgF}.
    Definition mjdg (s : nat) := jdgF (mterm s).
    Definition jdg  := jdgF term.

    (** Instantiating and renaming a judgment is much more straightforward **)
    Definition inst_jdg {s} m : mjdg s -> jdg := fmap jdgF (inst m).
    Definition rename_jdg ρ : jdg -> jdg := fmap jdgF (rename ρ).
    Definition substitute_jdg σ : jdg -> jdg := fmap jdgF (substitute σ).
  End Judgments.
  Arguments inst_jdg [_] {_ _}.
  Arguments rename_jdg [_] {_}.
  Arguments substitute_jdg [_] {_}.

  (** Definition of a signature of rules **)
  Class IDecl (I : Type) := declF : I -> Type -> Type.
  Class IJdg (I : Type) := jdgF : I -> Type -> Type.
  Context {I : Type} {HEqDecI : EqDec I}
    `{InstIDecl : IDecl I} `{InstIJdg : IJdg I}
    `{FMapDeclF : forall i, FMap (declF i)}
    `{FuncDeclF : forall i, Eq1Functor (declF i)}
    `{FMapJdgF : forall i, FMap (jdgF i)}
    `{FuncJdgF : forall i, Eq1Functor (jdgF i)}.
  Section RulesSignature.
    (* Contexts in premises must be closed, and judgments must be scoped by the context *)
    Variant premise (i : I) :=
    | prem_pred (P : ctx (declF i) -> menv -> Prop)
    | prem_ind i' (conv : forall X, declF i X -> declF i' X) {n} (Δ : mctx (declF i') 0 n) (j : mjdg (jdgF i') n).
    Derive NoConfusion for premise.

    (* The judgment of the conclusion must be closed *)
    Record rule (i : I) := {
      param : Type; (* A rule is parametrized by a type, e.g. a rule for any natural number *)
      premises : param -> list (premise i);
      conclusion : param -> mjdg (jdgF i) 0;
    }.

    Record jdg_sig := {
      rules : forall i : I, list (rule i)
    }.
    (* Other solution, maybe more heavy to write:
      [rules : list {param : Type & param -> rule}]
      and remove [param] from [rule]
    *)
  End RulesSignature.
  Arguments param {_}.
  Arguments premises {_}.
  Arguments conclusion {_}.
  Context {jsig : jdg_sig}.

  Class IMakeJdg := make_jdg : forall i : I,
    forall X, declF i X -> X -> jdgF i X.

  Context {InstIMakeJdg : IMakeJdg}
  `{NatMakeJdg : forall i : I, NatFromProd (make_jdg i)}.
  (* Theoretically, make_jdg is a natural transformation from (declF * Id) to jdgF *)

  (** Derivation with the rules of the signature **)
  Section Derivation.
    Reserved Notation "Γ ⊢( i ) j" (at level 70).
    Inductive proof : forall i, ctx (declF i) -> jdg (jdgF i) -> Prop :=
    (*
      We need a context, a rule and an instanciation of this rule, that will give the conclusion
    *)
    | step i (m : menv) (Γ : ctx (declF i)) (r : rule i) (x : r.(param)) :
      (* The rule must be in the signature *)
      In r (jsig.(rules) i) ->
      (* Satisfy all inductive premises *)
      (
        forall i' {n} (Δ : mctx (declF i') 0 n) (j : mjdg (jdgF i') n) conv,
        In (prem_ind i i' conv Δ j) (r.(premises) x) ->
        (inst_ctx m Δ ++ map (conv term) Γ) ⊢(i') inst_jdg m j
      ) ->
      (* Satisfy all predicate premise, depending on Γ and m *)
      (
        forall P, In (prem_pred i P) (r.(premises) x) ->
        P Γ m
      ) ->
      Γ ⊢(i) inst_jdg m (r.(conclusion) x)
    | tvar i (Γ : ctx (declF i)) (n : nat) (d : declF i term) :
      Γ ∋ n : d ->
      Γ ⊢(i) make_jdg i term d (E_var n)
    where "Γ ⊢( i ) j" := (proof i Γ j).

    Lemma conv_proof_j i Γ j j' :
      Γ ⊢(i) j ->
      j = j' ->
      Γ ⊢(i) j'.
    Proof. intros; subst; assumption. Qed.
    Lemma conv_proof_c i Γ Γ' j :
      Γ ⊢(i) j ->
      Γ = Γ' ->
      Γ' ⊢(i) j.
    Proof. intros; subst; assumption. Qed.
  End Derivation.
  Notation "Γ ⊢( i ) j" := (proof i Γ j) (at level 70).

  (** Behaviour of renamings **)
  Section Renamings.
    (** Commutation between renaming and instantiation lemma **)
    Lemma scoped_rename_inst {k} (n : nat) (t : mexpr k n) :
      forall m ρ,
      rename (up_rens n ρ) (inst m t) =
      inst (fun k s => rename (up_rens s ρ) (m k s)) t.
    Proof.
      intros.
      induction t in m, ρ |- *;
      simpl in *;
      rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
      - f_equal.
        apply up_rens_lt. assumption.
      - rewrite ren_subst, subst_ren.
        unfold srcomp, rscomp. apply substitute_proper. 2: reflexivity.
        intro i.
        destruct (i<? List.length σ) eqn: Hi.
        + rewrite up_rens_lt. 2: apply PeanoNat.Nat.ltb_lt; assumption.
          rewrite 2!nth_error_map.
          apply PeanoNat.Nat.ltb_lt in Hi.
          rewrite <- nth_error_Some in Hi.
          destruct (nth_error σ i) as [t|] eqn:Hσ; simpl.
          2: {exfalso. apply Hi. reflexivity. }
          apply nth_error_In in Hσ. rewrite Forall_forall in H.
          specialize (H _ Hσ).
          apply H.
        + rewrite PeanoNat.Nat.ltb_ge in Hi.
          pose (Hσ := Hi).
          apply nth_error_None in Hσ.
          (* rewrite up_rens_gt. 2: lia. *)
          rewrite 2!nth_error_map. rewrite Hσ. simpl.
          assert (List.length σ <= up_rens (List.length σ) ρ i).
          {rewrite up_rens_gt. 2: lia. lia. }
          rewrite <- nth_error_None in H0. rewrite H0. simpl.
          f_equal. rewrite up_rens_gt. 2: lia. rewrite up_rens_gt. 2: lia.
          replace (i - List.length σ + s - s) with (i - List.length σ) by lia. lia.
    Qed.
    Corollary closed_rename_inst {k} (t : mexpr k 0) :
      forall m ρ,
      rename ρ (inst m t) =
      inst (fun k s => rename (up_rens s ρ) (m k s)) t.
    Proof. apply (scoped_rename_inst 0). Qed.

    Lemma scoped_ctx_rename_inst {i s n} (Γ : mctx (declF i) s n) :
      forall m ρ,
      rename_ctx (up_rens s ρ) (inst_ctx m Γ) =
      inst_ctx (fun k s => rename (up_rens s ρ) (m k s)) Γ.
    Proof.
      induction Γ; intros; simpl.
      - reflexivity.
      - rewrite IHΓ. f_equal.
        rewrite <- inst_length.
        rewrite func_comp.
        apply rew_eq1. intro t.
        rewrite <- scoped_rename_inst.
        apply rename_proper. 2: reflexivity.
        apply up_rens_add.
    Qed.

    Lemma scoped_jdg_rename_inst {i s} (j : mjdg (jdgF i) s) :
      forall m ρ,
      rename_jdg (up_rens s ρ) (inst_jdg m j) =
      inst_jdg (fun k s => rename (up_rens s ρ) (m k s)) j.
    Proof.
      intros m ρ. unfold rename_jdg, inst_jdg.
      rewrite func_comp. apply (rew_eq1(F:=jdgF i)).
      intro t. apply scoped_rename_inst.
    Qed.
    Corollary closed_jdg_rename_inst {i} (j : mjdg (jdgF i) 0) :
      forall m ρ,
      rename_jdg ρ (inst_jdg m j) =
      inst_jdg (fun k s => rename (up_rens s ρ) (m k s)) j.
    Proof. apply (@scoped_jdg_rename_inst i 0). Qed.

    (** Typing of a renaming **)
    Reserved Notation "Δ ⊢r( i ) ρ : Γ" (at level 70, ρ at level 50, i at level 50).
    Inductive rtyping : forall i, ctx (declF i) -> ren -> ctx (declF i) -> Prop :=
    | rtyping_empty i Δ ρ :
      Δ ⊢r(i) ρ : []
    | rtyping_cons i Δ ρ Γ d :
      Δ ⊢r( i ) rcomp rshift ρ : Γ ->
      Δ ∋ (ρ 0) : fmap _ (rename (rcomp rshift ρ)) d ->
      Δ ⊢r(i) ρ : d::Γ
    where "Δ ⊢r( i ) ρ : Γ " := (rtyping i Δ ρ Γ).
    Lemma conv_rtyping i Δ ρ ρ' Γ :
      Δ ⊢r(i) ρ : Γ ->
      ρ = ρ' ->
      Δ ⊢r(i) ρ' : Γ.
    Proof. intros; subst; assumption. Qed.
    Derive Signature for rtyping.

    (* Hypothesis to add to signatures for them to preserve renaming *)
    Class IsNat {i i'} (conv : forall X, declF i X -> declF i' X) := natural :
    forall {X Y} (f : X -> Y) (d : declF i X),
    fmap (declF i') f (conv _ d) = conv Y (fmap (declF i) f d).

    Class RenJSig := {
      prem_ren :
        forall (i : I) (r : rule i) x P,
        In r (jsig.(rules) i) ->
        In (prem_pred i P) (r.(premises) x) ->
        forall Γ ρ Δ m,
        Δ ⊢r(i) ρ : Γ ->
        P Γ m ->
        P Δ (fun k s => rename (up_rens s ρ) (m k s)) ;

      conv_nat_ren :
        forall (i : I) (r : rule i) x,
        In r (jsig.(rules) i) ->
        forall n i' conv Δ j,
        In (prem_ind(n:=n) i i' conv Δ j) (r.(premises) x) ->
        IsNat conv
    }.

    (** Renaming lemmas **)
    #[export] Instance rtyping_proper i :
      Proper (eq ==> eq1 ==> eq ==> Basics.impl) (rtyping i).
    Proof.
      intros Δ' Δ HΔ ρ ρ' Hρ Γ' Γ HΓ H; subst.
      induction H in ρ', Hρ |- *; intros; constructor.
      - apply IHrtyping. apply congr_rcomp. reflexivity. assumption.
      - rewrite <- Hρ. eapply conv_in_d. apply H0.
        apply rew_eq1. intro t.
        apply rename_proper. 2: reflexivity.
        unfold rcomp, rshift. intro. apply Hρ.
    Qed.
    Lemma conv_rtype_r i Δ ρ ρ' Γ :
      Δ ⊢r(i) ρ : Γ ->
      ρ =₁ ρ' ->
      Δ ⊢r(i) ρ' : Γ.
    Proof. intros Hρ Heq. rewrite <- Heq. assumption. Qed.

    Lemma rename_in i Δ Γ ρ n d :
      Γ ∋ n : d ->
      Δ ⊢r(i) ρ : Γ ->
      Δ ∋ ρ n : fmap _ (rename ρ) d.
    Proof.
      intros HΓ Hρ. induction HΓ in Δ, ρ, Hρ |- *; intros;
      depelim Hρ.
      - rewrite func_comp.
        eapply conv_in_d. apply H.
        apply rew_eq1. intro t. rewrite ren_ren. reflexivity.
      - eapply conv_in_d. eapply conv_in_n.
        apply IHHΓ. apply Hρ. reflexivity.
        rewrite func_comp. apply rew_eq1.
        intro t. rewrite ren_ren. reflexivity.
    Qed.

    Lemma rtyping_comp i Γ Δ Θ ρ ρ' :
      Δ ⊢r(i) ρ : Γ ->
      Θ ⊢r(i) ρ' : Δ ->
      Θ ⊢r(i) rcomp ρ ρ' : Γ.
    Proof.
      intros Hρ Hρ'. induction Hρ in Θ, ρ', Hρ' |- *; intros; constructor.
      - eapply rtyping_proper. reflexivity. 2: reflexivity.
        apply rcomp_assoc. apply IHHρ. assumption.
      - eapply conv_in_d.
        unfold rcomp. eapply rename_in. apply H. assumption.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_ren, rcomp_assoc. reflexivity.
    Qed.

    Lemma weaken_rtyping i Γ ρ Δ A :
      Δ ⊢r(i) ρ : Γ ->
      A::Δ ⊢r(i) rcomp ρ S : Γ.
    Proof.
      intros Hρ. induction Hρ in A |- *; intros; constructor.
      - apply IHHρ.
      - eapply conv_in_d. constructor. apply H.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_ren, rcomp_assoc. reflexivity.
    Qed.

    Lemma up_rtyping i Γ ρ Δ d :
      Δ ⊢r(i) ρ : Γ ->
      fmap _ (rename ρ) d::Δ ⊢r(i) up_ren ρ : d::Γ.
    Proof.
      intros Hρ. constructor.
      - apply weaken_rtyping. assumption.
      - eapply conv_in_d. simpl. constructor.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_ren. reflexivity.
    Qed.

    Corollary up_rtyping_n i Γ ρ Δ Θ :
      Δ ⊢r(i) ρ : Γ ->
      (rename_ctx ρ Θ) ++ Δ ⊢r(i) up_rens (Datatypes.length Θ) ρ : Θ ++ Γ.
    Proof.
      induction Θ in Γ, ρ, Δ |- *; intros; simpl in *.
      - assumption.
      - apply up_rtyping.
        apply IHΘ. assumption.
    Qed.

    Lemma id_rtyping i Γ :
      Γ ⊢r(i) rid : Γ.
    Proof.
      induction Γ. constructor.
      replace a with (fmap _ (rename rid) a) at 1.
      2: {
        rewrite <- func_id. apply rew_eq1. intro. apply ren_rid.
      }
      rewrite <- up_ren_rid at 2. apply up_rtyping. assumption.
    Qed.

    Context {HRenSig : RenJSig}.

    Lemma inctx_conv {i i'} (conv : forall X, declF i X -> declF i' X) {Hconv : IsNat conv} Γ n d :
      Γ ∋ n : d ->
      map (conv _) Γ ∋ n : conv _ d.
    Proof.
      intros Hn. induction Hn in Hconv, conv |- *.
      - simpl. rewrite <- Hconv. constructor.
      - simpl. rewrite <- Hconv. constructor.
        apply IHHn. assumption.
    Qed.

    Lemma rtyping_conv {i i'} conv {Hconv : IsNat conv} Δ ρ Γ :
      Δ ⊢r(i) ρ : Γ ->
      map (conv _) Δ ⊢r(i') ρ : map (conv _) Γ.
    Proof.
      intros Hi. induction Hi in conv, Hconv |- *.
      - constructor.
      - simpl. constructor. apply IHHi. assumption.
        rewrite Hconv.
        apply inctx_conv; assumption.
    Qed.

    Theorem preserve_renaming i Γ j Δ ρ :
      Γ ⊢(i) j ->
      Δ ⊢r(i) ρ : Γ ->
      Δ ⊢(i) rename_jdg ρ j.
    Proof.
      intros Hj Hρ.
      induction Hj in Δ, ρ, Hρ |- *.
      (* Case of an inductive/predicate premise *)
      - (* We apply rule [r x] *)
        eapply conv_proof_j.
        unshelve econstructor.
        shelve.
        exact r. exact x.
        assumption.
        3: {symmetry. apply closed_jdg_rename_inst. }
        + (* Inductive premise *)
          intros.
          rewrite <- scoped_jdg_rename_inst. eapply H1. apply H3.
          rewrite <- scoped_ctx_rename_inst. simpl.
          eapply conv_rtyping.
          eapply up_rtyping_n.
          apply rtyping_conv. eapply conv_nat_ren.
          apply H. apply H3. assumption.
          f_equal. symmetry. apply inst_length.
        + (* Predicate premise *)
          intros.
          eapply HRenSig. apply H. apply H3. apply Hρ. apply H2. apply H3.
      (* Case of a variable *)
      - unfold rename_jdg.
        rewrite naturality_prod.
        constructor. eapply rename_in. apply H. assumption.
    Qed.

    Corollary weaken_typing i Γ j A :
      Γ ⊢(i) j ->
      A::Γ ⊢(i) rename_jdg rshift j.
    Proof.
      intro.
      eapply preserve_renaming. apply H.
      apply weaken_rtyping. apply id_rtyping.
    Qed.
  End Renamings.
  Notation "Δ ⊢r( i ) ρ : Γ" := (rtyping i Δ ρ Γ) (at level 70, ρ at level 50, i at level 50).

  (** Behaviour of substitutions **)
  Section Substitutions.

    (* TODO : should be in ParamSyntax *)

    Definition ren_to_subst (r : ren) : subst := fun i =>
    E_var (r i).

    Lemma ren_is_subst {k} r (t : expr k) :
      rename r t = substitute (ren_to_subst r) t.
    Proof.
      induction t in r |- *; simpl;
      rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
      f_equal. apply substitute_proper. 2: reflexivity.
      intros [|n]; simpl. reflexivity.
      unfold rcomp, rshift, srcomp. simpl. reflexivity.
    Qed.
    Corollary ren_is_subst_jdg {i} r (t : jdg (jdgF i)) :
      rename_jdg r t = substitute_jdg (ren_to_subst r) t.
    Proof.
      unfold rename_jdg, substitute_jdg. apply (rew_eq1(F:=jdgF i)).
      intro. apply ren_is_subst.
    Qed.
    Lemma ren_to_subst_up_rens n ρ :
      ren_to_subst (up_rens n ρ) =₁ up_substs n (ren_to_subst ρ).
    Proof.
      intro k. induction n in ρ, k |- *; simpl.
      reflexivity.
      unfold ren_to_subst, up_subst. unfold scons. destruct k as [|k].
      simpl. reflexivity. simpl. unfold srcomp, rshift.
      etransitivity. 2: {eapply rename_proper. reflexivity. apply IHn. }
      reflexivity.
    Qed.

    (** Commutation lemmas between substitution and instantiation **)
    Lemma scoped_substitute_inst {k} (n : nat) (t : mexpr k n) :
      forall m σ,
      substitute (up_substs n σ) (inst m t) =
      inst (fun k s => substitute (up_substs s σ) (m k s)) t.
    Proof.
      intros.
      induction t in m, σ |- *;
      simpl in *;
      rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
      - apply up_substs_lt. assumption.
      - rewrite 2!subst_subst.
        unfold scomp. apply substitute_proper. 2: reflexivity.
        intro i.
        destruct (i<? List.length σ0) eqn: Hi.
        + rewrite up_substs_lt. 2: apply PeanoNat.Nat.ltb_lt; assumption. simpl.
          rewrite 2!nth_error_map.
          apply PeanoNat.Nat.ltb_lt in Hi.
          rewrite <- nth_error_Some in Hi.
          destruct (nth_error σ0 i) as [t|] eqn:Hσ; simpl.
          2: {exfalso. apply Hi. reflexivity. }
          apply nth_error_In in Hσ. rewrite Forall_forall in H.
          specialize (H _ Hσ).
          apply H.
        + rewrite PeanoNat.Nat.ltb_ge in Hi.
          pose (Hσ := Hi).
          rewrite up_substs_gt. 2: lia.
          (* apply nth_error_None in Hσ. *)
          (* rewrite !up_substs_gt. 2: lia. *)
          rewrite subst_ren.
          unfold rscomp.
          etransitivity. 2: {apply substitute_proper. 2: reflexivity.
            intro i0. assert (List.length σ0 <= i0 + List.length σ0) by lia.
            apply nth_error_None in H0.
            rewrite nth_error_map.
            rewrite H0. simpl. reflexivity.
          }
          apply nth_error_None in Hσ. rewrite nth_error_map. rewrite Hσ. simpl.
          rewrite up_substs_gt. 2: lia.
          rewrite ren_is_subst. apply substitute_proper.
          2: f_equal; lia.
          intro i0. unfold ren_to_subst. f_equal. lia.
    Qed.
    Corollary closed_substitute_inst {k} (t : mexpr k 0) :
      forall m σ,
      substitute σ (inst m t) =
      inst (fun k s => substitute (up_substs s σ) (m k s)) t.
    Proof. apply (@scoped_substitute_inst _ 0). Qed.

    Lemma scoped_ctx_substitute_inst {i s n} (Γ : mctx (declF i) s n) :
      forall m σ,
      subst_ctx (up_substs s σ) (inst_ctx m Γ) =
      inst_ctx (fun k s => substitute (up_substs s σ) (m k s)) Γ.
    Proof.
      induction Γ; intros; simpl.
      - reflexivity.
      - rewrite IHΓ. f_equal.
        rewrite <- inst_length.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite <- scoped_substitute_inst.
        apply substitute_proper. 2: reflexivity.
        apply up_substs_add.
    Qed.

    Lemma scoped_jdg_substitute_inst {i s} (j : mjdg (jdgF i) s) :
      forall m σ,
      substitute_jdg (up_substs s σ) (inst_jdg m j) =
      inst_jdg (fun k s => substitute (up_substs s σ) (m k s)) j.
    Proof.
      intros m ρ. unfold substitute_jdg, inst_jdg.
      rewrite func_comp. apply (rew_eq1(F:=jdgF i)).
      intro t.
      apply scoped_substitute_inst.
    Qed.
    Corollary closed_jdg_substitute_inst {i} (j : mjdg (jdgF i) 0) :
      forall m σ,
      substitute_jdg σ (inst_jdg m j) =
      inst_jdg (fun k s => substitute (up_substs s σ) (m k s)) j.
    Proof. apply (@scoped_jdg_substitute_inst i 0). Qed.

    (** Typing of a substitution **)
    Reserved Notation "Δ ⊢s( i ) σ : Γ" (at level 70, σ at level 50).
    Inductive styping : forall i, ctx (declF i) -> subst -> ctx (declF i) -> Prop :=
    | styping_empty i Δ σ :
      Δ ⊢s(i) σ : []
    | styping_cons i Δ σ Γ d :
      Δ ⊢s(i) rscomp rshift σ : Γ ->
      Δ ⊢(i) make_jdg i term
        (fmap _ (substitute (rscomp rshift σ)) d)
        (σ 0) ->
      Δ ⊢s(i) σ : d::Γ
    where "Δ ⊢s( i ) σ : Γ " := (styping i Δ σ Γ).
    Lemma conv_styping i Δ ρ ρ' Γ :
      Δ ⊢s( i ) ρ : Γ ->
      ρ = ρ' ->
      Δ ⊢s( i ) ρ' : Γ.
    Proof. intros; subst; assumption. Qed.
    Derive Signature for styping.

    Lemma ren_to_subst_typing i Γ ρ Δ :
      Δ ⊢r(i) ρ : Γ ->
      Δ ⊢s(i) ren_to_subst ρ : Γ.
    Proof.
      intro Hρ. induction Hρ.
      - constructor.
      - constructor. apply IHHρ.
        constructor. eapply conv_in_d. apply H.
        apply rew_eq1. intro. apply ren_is_subst.
    Qed.

    (* Hypothesis to add to signatures for them to preserve substitution *)
    Class ConvMakeJdg {i i'} (conv : forall X, declF i X -> declF i' X) :=
    conv_pres_makke_jdg :
      forall Γ (d : declF i term) t,
      Γ ⊢(i) make_jdg i term d t ->
      map (conv _) Γ ⊢(i') make_jdg i' term (conv _ d) t.
    Class SubstJSig := {
      prem_subst :
        forall i (r : rule i) x P,
        In r (jsig.(rules) i) ->
        In (prem_pred i P) (r.(premises) x) ->
        forall Γ σ Δ m,
        Δ ⊢s(i) σ : Γ ->
        P Γ m ->
        P Δ (fun k s => substitute (up_substs s σ) (m k s));

      prem_pred_ext :
        forall i (r : rule i) x P,
        In r (jsig.(rules) i) ->
        In (prem_pred i P) (r.(premises) x) ->
        forall Γ m m',
        P Γ m -> m =₂ m' -> P Γ m';

      conv_nat_subst :
        forall (i : I) (r : rule i) x,
        In r (jsig.(rules) i) ->
        forall n i' conv Δ j,
        In (prem_ind(n:=n) i i' conv Δ j) (r.(premises) x) ->
        IsNat conv;

      conv_make_jdg :
        forall (i : I) (r : rule i) x,
        In r (jsig.(rules) i) ->
        forall n i' conv Δ j,
        In (prem_ind(n:=n) i i' conv Δ j) (r.(premises) x) ->
        (* [conv] preserves typing of [make_jdg] *)
        ConvMakeJdg conv
    }.
    (* Preserving substitutions implies preserving renamings via ren_is_subst *)
    #[export] Instance SubstJdg_RenJdg : SubstJSig -> RenJSig.
    Proof.
      intro H.
      constructor.
      2: apply H.
      intros.
      eapply prem_pred_ext. apply H0. apply H1.
      2: {intros k s. rewrite <- ren_is_subst. reflexivity. }
      eapply prem_pred_ext. apply H0. apply H1.
      2: {intros k s. etransitivity. 2: rewrite ren_to_subst_up_rens; reflexivity. reflexivity. }
      eapply prem_subst. apply H0. apply H1. 2: apply H3.
      apply ren_to_subst_typing. assumption.
    Qed.

    (** Substitution lemmas **)
    #[export] Instance styping_proper i :
      Proper (eq ==> eq1 ==> eq ==> Basics.impl) (styping i).
    Proof.
      intros Δ' Δ HΔ σ σ' Hσ Γ' Γ HΓ H; subst.
      induction H in σ', Hσ |- *; intros; constructor.
      - apply IHstyping. apply rscomp_proper. reflexivity. assumption.
      - eapply conv_proof_j.
        apply H0.
        f_equal. 2: apply Hσ.
        apply rew_eq1. intros. intro. apply substitute_proper. 2: reflexivity.
        intro. apply Hσ.
    Qed.
    Lemma conv_stype_s i Δ σ σ' Γ :
      Δ ⊢s(i) σ : Γ ->
      σ =₁ σ' ->
      Δ ⊢s(i) σ' : Γ.
    Proof.
      intros Hσ Heq. rewrite <- Heq. assumption.
    Qed.

    Lemma substitute_in i Δ Γ σ n d :
      Γ ∋ n : d ->
      Δ ⊢s(i) σ : Γ ->
      Δ ⊢(i) make_jdg i term (fmap _ (substitute σ) d) (σ n).
    Proof.
      intros HΓ Hσ. induction HΓ in Δ, σ, Hσ |- *; intros;
      depelim Hσ; subst.
      - rewrite func_comp.
        eapply conv_proof_j. apply H.
        f_equal. apply rew_eq1. intro.
        rewrite subst_ren. reflexivity.
      - eapply conv_proof_j. apply IHHΓ. apply Hσ.
        rewrite func_comp. f_equal. apply rew_eq1. intro.
        rewrite subst_ren. reflexivity.
    Qed.

    Context `{HSubstSig : SubstJSig}.

    Lemma weaken_styping i Γ σ Δ d :
      Δ ⊢s(i) σ : Γ ->
      d::Δ ⊢s(i) srcomp σ S : Γ.
    Proof.
      intros Hσ. induction Hσ in d |- *; intros; constructor.
      - apply IHHσ.
      - eapply conv_proof_j. apply weaken_typing. apply H.
        simpl. unfold rename_jdg.
        rewrite naturality_prod. f_equal.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_subst. reflexivity.
    Qed.

    Lemma up_styping i Γ σ Δ d :
      Δ ⊢s(i) σ : Γ ->
      (fmap _ (substitute σ) d)::Δ ⊢s(i) up_subst σ : d::Γ.
    Proof.
      intros Hσ. constructor.
      - apply weaken_styping. assumption.
      - simpl. constructor.
        eapply conv_in_d. constructor.
        rewrite func_comp.
        apply rew_eq1. intro. rewrite ren_subst. reflexivity.
    Qed.

    Corollary up_styping_n i Γ σ Δ Θ :
      Δ ⊢s(i) σ : Γ ->
      (subst_ctx σ Θ) ++ Δ ⊢s(i) up_substs (Datatypes.length Θ) σ : Θ ++ Γ.
    Proof.
      induction Θ in Γ, σ, Δ |- *; intros; simpl in *.
      - assumption.
      - apply up_styping.
        apply IHΘ. assumption.
    Qed.

    Lemma id_styping i Γ :
      Γ ⊢s(i) sid : Γ.
    Proof.
      induction Γ. constructor.
      replace a with (fmap _ (substitute sid) a) at 1.
      2: {
        rewrite <- func_id. apply rew_eq1. intro. apply subst_sid.
      }
      rewrite <- up_subst_sid at 2. apply up_styping. assumption.
    Qed.

    Lemma styping_subst i i' Γ σ Δ conv {Hconv : IsNat conv} :
      ConvMakeJdg conv ->
      Δ ⊢s(i) σ : Γ ->
      map (conv _) Δ ⊢s(i') σ : map (conv _) Γ.
    Proof.
      intros Hconv_make Hi. induction Hi in Hconv_make, Hconv, conv |- *.
      - constructor.
      - simpl. constructor.
        apply IHHi; try assumption.
        rewrite Hconv.
        apply Hconv_make. assumption.
    Qed.

    Theorem preserve_subst i Γ j Δ σ :
      Γ ⊢(i) j ->
      Δ ⊢s(i) σ : Γ ->
      Δ ⊢(i) substitute_jdg σ j.
    Proof.
      intros Hj Hσ.
      induction Hj in Δ, σ, Hσ |- *.
      (* Case of an inductive/predicate premise *)
      - (* We apply rule [r x] *)
        eapply conv_proof_j.
        unshelve econstructor.
        shelve.
        exact r. exact x.
        assumption.
        3: {symmetry. apply closed_jdg_substitute_inst. }
        + (* Inductive premise *)
          intros.
          rewrite <- scoped_jdg_substitute_inst. eapply H1. apply H3.
          rewrite <- scoped_ctx_substitute_inst. simpl.
          eapply conv_styping.
          eapply up_styping_n.
          apply styping_subst.
          eapply conv_nat_subst. apply H. apply H3.
          eapply conv_make_jdg. apply H. apply H3.
          assumption.
          f_equal. symmetry. apply inst_length.
        + (* Predicate premise *)
          intros.
          eapply HSubstSig. apply H. apply H3. apply Hσ. apply H2. assumption.
      (* Case of a variable *)
      - unfold substitute_jdg.
        rewrite naturality_prod.
        eapply substitute_in. apply H. assumption.
    Qed.
  End Substitutions.
  Notation "Δ ⊢s( i ) σ : Γ" := (styping i Δ σ Γ) (at level 70, σ at level 50, i at level 50).
End WithSignature.
Arguments mnil {_ _ scope}.
Arguments mcons {_ _ scope _}.
Arguments inctx {_} [_] {_}.
Notation "Γ ∋ n : d" := (inctx Γ n d) (at level 70, n at level 50).
Arguments inst_ctx {_} [_] {_ _ _}.
Arguments rename_ctx {_} [_] {_}.
Arguments subst_ctx {_} [_] {_}.

Arguments prem_ind {_ _ _ _ _} (_ _) {_}.

Notation "Γ ⊢( i ) j" := (proof i Γ j) (at level 70).

Notation "Δ ⊢r( i ) ρ : Γ" := (rtyping i Δ ρ Γ) (at level 70, ρ at level 50).
Notation "Δ ⊢s( i ) σ : Γ" := (styping i Δ σ Γ) (at level 70, σ at level 50).

Arguments IMakeJdg (_) {_ _}.

Arguments RenJSig {_ _ _ _ _} (_).
Arguments SubstJSig {_ _ _ _ _ _} (_) {_}.

#[export] Instance IdIsNat
  `{signature}
  `{IDecl unit} `{forall i : unit, FMap (declF i)} :
  IsNat(I:=unit)(i':=tt) (fun _ d => d).
Proof. constructor. Qed.

#[export] Instance IdPresMakeJdg
  `{signature}
  `{IDecl unit} `{forall i : unit, FMap (declF i)}
  `{IJdg unit} `{forall i : unit, FMap (jdgF i)}
  `{!IMakeJdg unit}
  `{jsig : !jdg_sig} :
  @ConvMakeJdg _ unit _ _ _ _ jsig _ tt tt (fun _ d => d).
Proof.
  unfold ConvMakeJdg. intros.
  rewrite map_id. assumption.
Qed.

(** Example module of conversion in lambda pi **)
Module LPConv.
  (* Syntax of lambda pi *)
  Variant EBase := Nat.
  Variant CLamPi := CType | CApp | CLam | CPi.

  Derive NoConfusion for EBase.
  Derive EqDec for EBase.
  Derive NoConfusion for CLamPi.
  Derive EqDec for CLamPi.

  #[refine] Definition sig_lp : signature := {|
    base := EBase;
    eval_base := fun _ => nat;
    ctor := CLamPi;
    ctor_type := fun c => match c with
    | CType => [AT_base Nat]
    | CApp => [AT_term; AT_term]
    | CLam => [AT_bind AT_term]
    | CPi => [AT_term; AT_bind AT_term]
    end
  |}.
  Defined.

  Notation "'mterm'" := (@mexpr sig_lp Kt) (at level 0).

  (* λΠ constructors, written in a more accessible way *)
  Definition T {s} (n : nat) : mterm s :=
  @M_ctor sig_lp s CType (
    M_al_cons s (@M_abase sig_lp s Nat n) (M_al_nil s)
  ).

  Definition lambda {s} (t : mterm (S s)) : mterm s :=
  @M_ctor sig_lp s CLam (
    M_al_cons s (M_abind s (M_aterm  (S s) t)) (M_al_nil s)
  ).

  Definition Pi {s} (A : mterm s) (B : mterm (S s)) : mterm s :=
  @M_ctor sig_lp s CPi (
    M_al_cons s (M_aterm s A) (M_al_cons s (M_abind s (M_aterm (S s) B)) (M_al_nil s))
  ).

  Definition App {s} (f u : mterm s) : mterm s :=
  @M_ctor sig_lp s CApp (
    M_al_cons s (M_aterm s f) (M_al_cons s (M_aterm s u) (M_al_nil s))
  ).

  Definition Var {s} (n : nat) (Hs : n < s) : mterm s :=
  @M_var sig_lp s n Hs.

  Definition elambda (t : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).
  Definition ePi (A B : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CPi (
    E_al_cons (E_aterm A) (E_al_cons (E_abind (E_aterm B)) E_al_nil)
  ).
  Definition eT (u : nat) : P.expr Kt :=
  @E_ctor sig_lp CType (
    E_al_cons (@E_abase sig_lp Nat u) E_al_nil
  ).
  Definition eApp (f u : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CApp (
    E_al_cons (E_aterm f) (E_al_cons (E_aterm u) E_al_nil)
  ).

  (* Typing rules *)
  Instance ConvDeclF : IDecl unit := fun _ X => unit.
  Instance ConvJdgF : IJdg unit := fun _ X => (X*X)%type.
  Instance ConvMakeJdg : IMakeJdg unit := fun _ _ _ t => (t, t).
  Instance LpConvNatMakeJdg (i : unit) : NatFromProd (make_jdg(IMakeJdg:=ConvMakeJdg) i).
  Proof.
    constructor. reflexivity.
  Qed.

  Definition nA := 0.
  Definition nB := 1.
  Definition nA' := 2.
  Definition nB' := 3.
  Definition nt := 4.
  Definition nu := 5.
  Definition nv := 6.
  Definition nt' := 7.
  Definition nu' := 8.
  Definition nv' := 9.
  Definition nb := 10.
  Definition nb' := 11.

  Definition A {s} := M_mvar(sig:=sig_lp) s nA.
  Definition B {s} := M_mvar(sig:=sig_lp) s nB.
  Definition A' {s} := M_mvar(sig:=sig_lp) s nA'.
  Definition B' {s} := M_mvar(sig:=sig_lp) s nB'.
  Definition t {s} := M_mvar(sig:=sig_lp) s nt.
  Definition u {s} := M_mvar(sig:=sig_lp) s nu.
  Definition v {s} := M_mvar(sig:=sig_lp) s nv.
  Definition t' {s} := M_mvar(sig:=sig_lp) s nt'.
  Definition u' {s} := M_mvar(sig:=sig_lp) s nu'.
  Definition v' {s} := M_mvar(sig:=sig_lp) s nv'.
  Definition b {s} := M_mvar(sig:=sig_lp) s nb.
  Definition b' {s} := M_mvar(sig:=sig_lp) s nb'.

  Definition tRefl : rule(sig:=sig_lp) tt :=
  {|
    premises := fun (_ : unit) => [];
    conclusion := fun _ => (t[], t[])
  |}.
  Definition tSym : rule(sig:=sig_lp) tt :=
  {|
    premises := fun (_ : unit) => [
      prem_ind tt (fun _ u => u)
        mnil
        (t[], u[])
    ];
    conclusion := fun _ => (u [], t [])
  |}.
  Definition tTrans : rule(sig:=sig_lp) tt :=
  {|
    premises := fun (_ : unit) => [
      prem_ind tt (fun _ u => u)
        mnil
        (t[], u[]) ;
      prem_ind tt (fun _ u => u)
        mnil
        (u[], v[])
    ];
    conclusion := fun _ => (t [], v [])
  |}.

  Definition tCongrApp : rule tt :=
  {|
    premises := fun (_ : unit) => [
      prem_ind tt (fun _ u => u)
        mnil
        (t[], t'[]) ;
      prem_ind tt (fun _ u => u)
        mnil
        (u[], u'[])
    ];
    conclusion := fun _ =>
      (App (t[]) (u[]), App (t'[]) (u'[]))
  |}.
  (* In this rule, B and B' will be instanciated to terms with one variable ; the substitution has to take this into account *)
  Definition tCongrPi : rule tt :=
  {|
    premises := fun (_ : unit) => [
      prem_ind tt (fun _ u => u)
        mnil
        (A[], A'[]);
      prem_ind tt (fun _ u => u)
        (mcons tt mnil)
        (B[var 0], B'[var 0])
    ];
    conclusion := fun _ =>
      (Pi (A[]) (B[var 0]), Pi (A'[]) (B'[var 0]))
  |}.
  Definition tCongrLam : rule tt :=
  {|
    premises := fun (_ : unit) => [
      prem_ind tt (fun _ u => u)
        (mcons tt mnil)
        (b[var 0], b'[var 0])
    ];
    conclusion := fun _ =>
      (lambda (b[var 0]), lambda (b'[var 0]))
  |}.

  Definition tBeta : rule tt :=
  {|
    premises := fun (_ : unit) => [];
    conclusion := fun _ =>
    (App (lambda (b[var 0])) (u[]), b[u[]])
  |}.

  Definition typ_conv_lampi : jdg_sig := {|rules:=
  fun u => match u with
    tt => [
      tRefl; tSym; tTrans;
      tCongrApp; tCongrPi; tCongrLam;
      tBeta
    ]
  end|}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ j" := (proof(jsig:=typ_conv_lampi) tt Γ j) (at level 70).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lp) tt Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_conv_lampi) tt Δ σ Γ) (at level 70, σ at level 50).

  Notation "Γ ⊢ A ≡ B" := (proof(jsig:=typ_conv_lampi) tt Γ (A, B)) (at level 70).

  (* Sanity check *)
  Lemma beta_rev n :
    [] ⊢ eT n ≡ eApp (elambda (E_var 0)) (eT n).
  Proof.
    (* Apply symmetry *)
    (* The instansiation msym only depends on the name of the meta-variables. This is OK because we did everything correctly when we defined our signature. *)
    pose (msym := fun k s =>
      if (k=?nu) then (eT n)
      else if (k=?nt) then (eApp (elambda (E_var 0)) (eT n))
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact msym. exact tSym. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: {intros. destruct_n H. inversion H. }
    intros. destruct_n H.
    noconf H. simpl.
    (* Just to avoid unfolding too much *)
    unshelve eapply conv_proof_j.
    exact ((eApp (elambda (E_var 0)) (eT n)), eT n).
    2: reflexivity.

    (* Apply beta *)
    pose (mbeta := fun k s =>
      if (k=?nb) then (E_var 0)
      else if (k=?nu) then (eT n)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact mbeta. exact tBeta. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H.
  Qed.

  Instance LPConvSubst : SubstJSig typ_conv_lampi.
  Proof.
    constructor; intros; destruct i;
    destruct_n H; subst; destruct_n H0;
    try now inversion H0; try typeclasses eauto.
  Qed.
End LPConv.

(** Example module of typing of Lambda Pi **)
Module LambdaPi.
  #[warnings="-notation-overridden"] Import LPConv.

  Definition nA := 0.
  Definition nB := 1.
  Definition nf := 2.
  Definition nu := 3.
  Definition nb := 4.
  Definition nt := 5.
  Definition nA' := 6.

  Definition A {s} := M_mvar(sig:=sig_lp) s nA.
  Definition B {s} := M_mvar(sig:=sig_lp) s nB.
  Definition f {s} := M_mvar(sig:=sig_lp) s nf.
  Definition u {s} := M_mvar(sig:=sig_lp) s nu.
  Definition b {s} := M_mvar(sig:=sig_lp) s nb.
  Definition t {s} := M_mvar(sig:=sig_lp) s nt.
  Definition A' {s} := M_mvar(sig:=sig_lp) s nA'.

  (* Typing rules *)
  Instance LpDecl : IDecl unit := fun _ X => X.
  Instance LpJdg : IJdg unit := fun _ X => (X*X)%type.
  Instance LpMakeJdg : IMakeJdg(InstIDecl:=LpDecl)(InstIJdg:=LpJdg) unit := fun _ X A t => (t, A).
  Instance LpNatMakeJdg (i : unit) : NatFromProd (make_jdg(IMakeJdg:=LpMakeJdg) i).
  Proof.
    constructor. reflexivity.
  Qed.


  Definition tType : rule tt :=
  {|
    premises := fun _ => [];
    conclusion := fun n => (T(s:=0) n, T (S n))
  |}.

  Definition tPi : rule tt :=
  {|
    premises := fun '(n, m) =>
    [
      prem_ind tt (fun _ A => A)
        mnil
        (A[], T n) ;
      prem_ind tt (fun _ A => A)
        (mcons(n:=0) (A[]) mnil)
        (B[var 0], T m)
    ] ;
    conclusion := fun '(n, m) =>
      (Pi (A[]) (B[var 0]), T (Nat.max n m))
  |}.
  Definition tApp : rule tt :=
  {|
    premises := fun (_ : unit) =>
    [
      prem_ind tt (fun _ A => A)
        mnil
        (f[], Pi (A[]) (B[var 0]));
      prem_ind tt (fun _ A => A)
        mnil
        (u[], A[])
    ];
    conclusion := fun _ =>
      (App (f[]) (u[]), B[u[]])
  |}.


  Definition tLam : rule tt :=
  {|
    premises := fun (_ : unit) =>
    [
      prem_ind tt (fun _ A => A)
        (mcons(n:=0) (A[]) mnil)
        (b[var 0], B[var 0])
    ];
    conclusion := fun _ =>
      (lambda (b[var 0]), Pi (A[]) (B[var 0]))
  |}.

  Definition tConv : rule tt :=
  {|
    premises := fun (_ : unit) =>
    [
      prem_ind tt (fun _ A => A)
        (mnil)
        (t[], A[]);
      prem_pred tt (fun Γ m =>
        map (fun _ => tt) Γ ⊢ inst m (@A 0[]) ≡ inst m (@A' 0[])
      )
    ];
    conclusion := fun _ =>
      (t[], A'[])
  |}.

  Definition typ_lampi : jdg_sig := {|rules:=
  fun u => match u with
    tt =>[
      tType; tPi; tApp; tLam; tConv
    ]
  end|}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ j" := (proof(jsig:=typ_lampi) tt Γ j) (at level 70).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lp) tt Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_lampi) tt Δ σ Γ) (at level 70, σ at level 50).

  (* Something that appears multiple times, so making it a lemma might be useful *)
  Lemma subst_minus_plus_zero :
    (fun i => E_var(sig:=sig_lp) (i - 0 + 0)) =₁ sid.
  Proof. intro; unfold sid; f_equal; lia. Qed.

  Lemma refl Γ t :
    Γ ⊢ t ≡ t.
  Proof.
    pose (m := fun k s =>
      if k =? LPConv.nt then t else
      default_menv k s
    ).
    eapply conv_proof_j.
    unshelve econstructor. exact m. exact tRefl. exact tt. repeat (try (left; reflexivity); right).
    3: {cbn. setoid_rewrite nth_error_nil.
      rewrite subst_minus_plus_zero. rewrite subst_sid. reflexivity.
    }
    - intros. noconf H.
    - intros. noconf H.
  Qed.

  Lemma styping_to_unit Δ σ Γ :
    Δ ⊢s σ : Γ ->
    styping(jsig:=typ_conv_lampi) tt (map (fun _ => tt) Δ) σ (map (fun _ => tt) Γ).
  Proof.
    intro Hσ. induction Hσ.
    - constructor.
    - simpl. constructor.
      + apply IHHσ.
      + unfold make_jdg, LpMakeJdg, ConvMakeJdg, fmap, FMapId in *.
        destruct i.
        apply refl.
  Qed.

  (* This is the instance we need if we want to use preservation by substitution and renaming *)
  Instance LPTypSubst : SubstJSig typ_lampi.
  Proof.
    constructor; intros; destruct i; destruct_n H; subst; try destruct x; destruct_n H0; try now inversion H0; try typeclasses eauto.
    - inversion H0. subst.
      (* Clean the context a bit *)
      clear H0.
      remember (m nA 0) as tA.
      remember (m nA' 0) as tA'.
      simpl.
      setoid_rewrite nth_error_nil. setoid_rewrite nth_error_nil in H2.
      rewrite subst_minus_plus_zero in *.
      rewrite 2!subst_sid in *.
      (* Apply the theorem of preservation by substitution because the predicate is an inductive predicate that we already built *)
      pose (preserve_subst(jsig:=typ_conv_lampi) tt (map (fun _ => tt) Γ) (tA, tA')).
      apply p; clear p.
      apply H2.
      (* We still need to show that :
        [map (fun u => u) Γ ⊢s map (fun u => u) Δ]
        This is a part that is more specific to the theory we built. We even [Admitted] a part of this proof that is not comfortable in this framework, and that is not useful for the example
      *)
      apply styping_to_unit. assumption.
    - inversion H0. clear H0.
      setoid_rewrite nth_error_nil. subst. setoid_rewrite nth_error_nil in H1.
      rewrite subst_minus_plus_zero in *.
      rewrite !subst_sid in *. rewrite !H2 in H1. assumption.
  Qed.

  Lemma proof_type_id n :
    [] ⊢ (elambda (E_var 0), ePi (eT n) (eT n)).
  Proof.
    pose (m := fun k s =>
      if (k=?nb) then (E_var 0)
      else if (k=?nA) then (eT n)
      else if (k=?nB) then (eT n)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. exact tLam. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: intros; destruct_n H; noconf H.
    intros. destruct_n H.
    noconf H. simpl.
    eapply conv_proof_j. apply tvar. constructor.
    reflexivity.
  Qed.

  Lemma proof_type_id_app n :
    [eT n] ⊢ (eApp (elambda (E_var 0)) (E_var 0), (eT n)).
  Proof.
    pose (m := fun k s =>
      if (k=?nf) then (elambda (E_var 0))
      else if (k=?nu) then (E_var 0)
      else if (k=?nA) then (eT n)
      else if (k=?nB) then (eT n)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tApp. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: intros; destruct_n H; noconf H.
    intros. destruct_n H.
    - noconf H.
      simpl. unfold fmap, FMapId. simpl.
      eapply conv_proof_j.
      eapply (weaken_typing (jsig:=typ_lampi)).
      apply (proof_type_id n).
      reflexivity.
      Unshelve.
      + intro. typeclasses eauto.
      + intro. eapply Eq1FProd; typeclasses eauto.
      + typeclasses eauto.
      + apply SubstJdg_RenJdg; typeclasses eauto.
    - noconf H. simpl.
      eapply conv_proof_j. apply tvar. constructor.
      reflexivity.
  Qed.

  Lemma proof_typee_id_app_lam n :
    [eT n] ⊢ (eApp (elambda (E_var 0)) (E_var 0),
    eApp (elambda (E_var 0)) (eT n)).
  Proof.
    (* Use the conversion rule *)
    pose (m := fun k s =>
      if (k=?nt) then (eApp (elambda (E_var 0)) (E_var 0))
      else if (k=?nA) then (eT n)
      else if (k=?nA') then (eApp (elambda (E_var 0)) (eT n))
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tConv. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    - (* Inductive premise *)
      intros. destruct_n H; noconf H.
      unfold inst_jdg, inst_ctx, fmap, FMapProd, fmap, FMapId. simpl. apply proof_type_id_app.
    - (* Predicate premise *)
      intros. destruct_n H; noconf H.
      setoid_rewrite nth_error_nil.
      rewrite subst_minus_plus_zero. rewrite 2! subst_sid.
      simpl. unfold m. simpl.
      (* Need to weaken the context *)
      eapply conv_proof_j.
      eapply (weaken_typing(jsig:=typ_conv_lampi)).
      (* Here Rocq finds the typeclasses *)
      apply (beta_rev n). reflexivity.
  Qed.

End LambdaPi.

(** Example section of simply typed lambda calculus **)
Module SimplLambda.
  Variant EBase :=.
  Variant CLamCalc := CApp | CLam.

  Derive NoConfusion for EBase.
  Derive EqDec for EBase.
  Derive NoConfusion for CLamCalc.
  Derive EqDec for CLamCalc.

  #[refine] Definition sig_lam : signature := {|
    base := EBase;
    eval_base := fun _ => False;
    ctor := CLamCalc;
    ctor_type := fun c => match c with
    | CApp => [AT_term; AT_term]
    | CLam => [AT_bind AT_term]
    end
  |}.
  Defined.

  #[local] Notation "'mterm'" := (@mexpr sig_lam Kt) (at level 0).

  (* λΠ constructors, written in a more accessible way *)
  Definition lambda {s} (t : mterm (S s)) : mterm s :=
  @M_ctor sig_lam s CLam (
    M_al_cons s (M_abind s (M_aterm  (S s) t)) (M_al_nil s)
  ).

  Definition App {s} (f u : mterm s) : mterm s :=
  @M_ctor sig_lam s CApp (
    M_al_cons s (M_aterm s f) (M_al_cons s (M_aterm s u) (M_al_nil s))
  ).

  Definition Var {s} (n : nat) (Hs : n < s) : mterm s :=
  @M_var sig_lam s n Hs.

  Inductive sType :=
  | sIota
  | sArrow (A B : sType).

  (* Definition of contexts and judments *)
  Instance LamDecl : IDecl unit := fun _ _ => sType.
  Instance LamJdg : IJdg unit := fun _ X => (X*sType)%type.
  Instance LamMakeJdg : IMakeJdg unit := fun _ X A t => (t, A).
  Instance LamMakeJdgNat (i : unit) : NatFromProd (make_jdg(IMakeJdg:=LamMakeJdg) i).
  Proof.
    constructor. reflexivity.
  Qed.

  (* Typing rules *)
  Definition nf := 0.
  Definition nu := 1.
  Definition nb := 2.

  Definition f {s} := M_mvar(sig:=sig_lam) s nf.
  Definition u {s} := M_mvar(sig:=sig_lam) s nu.
  Definition b {s} := M_mvar(sig:=sig_lam) s nb.

  Definition tApp : rule tt :=
  {|
    premises := fun '(A, B) =>
    [
      prem_ind tt (fun _ A => A)
        mnil
        (f[], sArrow A B);
      prem_ind tt (fun _ A => A)
        mnil
        (u[], A)
    ];
    conclusion := fun '(_, B) =>
      (App (f[]) (u[]), B)
  |}.

  Definition tLam : rule tt :=
  {|
    premises := fun '(A, B) =>
    [
      prem_ind tt (fun _ A => A)
        (mcons(n:=0) A mnil)
        (b[var 0], B)
    ];
    conclusion := fun '(A, B) =>
      (lambda (b[var 0]), sArrow A B)
  |}.

  Definition typ_lam : jdg_sig := {|rules:=
  fun u => match u with
    tt =>[tApp; tLam]
  end|}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lam Γ n A) (at level 70, n at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ j" := (proof(jsig:=typ_lam) tt Γ j) (at level 70).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lam) tt Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_lam) tt Δ σ Γ) (at level 70, σ at level 50).

  (* Sanity check *)

  Definition elambda (t : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lam CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).
  Definition eApp (f u : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lam CApp (
    E_al_cons (E_aterm f) (E_al_cons (E_aterm u) E_al_nil)
  ).

  Lemma proof_type_id :
    [] ⊢ ((elambda (E_var 0), sArrow sIota sIota)).
  Proof.
    pose (m := fun k s =>
      if (k=?nb) then (E_var(sig:=sig_lam) 0)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. exact tLam. exact (sIota, sIota). repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H; noconf H.
    simpl. unfold inst_jdg, fmap, FMapProd, fmap, FMapId.
    eapply conv_proof_j. apply tvar. constructor.
    reflexivity.
  Qed.

  Instance LambdaSubst : SubstJSig typ_lam.
  Proof.
    constructor; intros; destruct i; destruct_n H;
    subst; try destruct x; destruct_n H0;
    try now inversion H0; try typeclasses eauto.
  Qed.

  Lemma proof_type_id_app :
    [sIota] ⊢ (eApp (elambda (E_var 0)) (E_var 0), (sIota)).
  Proof.
    pose (m := fun k s =>
      if (k=?nf) then (elambda (E_var 0))
      else if (k=?nu) then (E_var 0)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tApp. exact (sIota, sIota). repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H; noconf H.
    - simpl.
      eapply conv_proof_j.
      eapply (weaken_typing (jsig:=typ_lam)).
      apply (proof_type_id).
      reflexivity.
    - simpl.
      eapply conv_proof_j. apply tvar. constructor.
      reflexivity.
  Qed.
End SimplLambda.

(** Lambda pi modulo typed conversion with eta rule **)
Module LPEta.
  (* Syntax of lambda pi *)
  Variant EBase := Nat.
  Variant CLamPi := CType | CApp | CLam | CPi.

  Derive NoConfusion for EBase.
  Derive EqDec for EBase.
  Derive NoConfusion for CLamPi.
  Derive EqDec for CLamPi.

  #[refine] Definition sig_lp : signature := {|
    base := EBase;
    eval_base := fun _ => nat;
    ctor := CLamPi;
    ctor_type := fun c => match c with
    | CType => [AT_base Nat]
    | CApp => [AT_term; AT_term]
    | CLam => [AT_bind AT_term]
    | CPi => [AT_term; AT_bind AT_term]
    end
  |}.
  Defined.

  Notation "'mterm'" := (@mexpr sig_lp Kt) (at level 0).

  (* λΠ constructors, written in a more accessible way *)
  Definition T {s} (n : nat) : mterm s :=
  @M_ctor sig_lp s CType (
    M_al_cons s (@M_abase sig_lp s Nat n) (M_al_nil s)
  ).

  Definition lambda {s} (t : mterm (S s)) : mterm s :=
  @M_ctor sig_lp s CLam (
    M_al_cons s (M_abind s (M_aterm  (S s) t)) (M_al_nil s)
  ).

  Definition Pi {s} (A : mterm s) (B : mterm (S s)) : mterm s :=
  @M_ctor sig_lp s CPi (
    M_al_cons s (M_aterm s A) (M_al_cons s (M_abind s (M_aterm (S s) B)) (M_al_nil s))
  ).

  Definition App {s} (f u : mterm s) : mterm s :=
  @M_ctor sig_lp s CApp (
    M_al_cons s (M_aterm s f) (M_al_cons s (M_aterm s u) (M_al_nil s))
  ).

  Definition Var {s} (n : nat) (Hs : n < s) : mterm s :=
  @M_var sig_lp s n Hs.

  Definition elambda (t : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).
  Definition ePi (A B : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CPi (
    E_al_cons (E_aterm A) (E_al_cons (E_abind (E_aterm B)) E_al_nil)
  ).
  Definition eT (u : nat) : P.expr Kt :=
  @E_ctor sig_lp CType (
    E_al_cons (@E_abase sig_lp Nat u) E_al_nil
  ).
  Definition eApp (f u : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CApp (
    E_al_cons (E_aterm f) (E_al_cons (E_aterm u) E_al_nil)
  ).

  (* Typing rules *)
  Variant ILP := | Typing | Conversion.

  Instance LpDecl : IDecl ILP := fun _ X => X.
  Instance LpJdg : IJdg ILP := fun i => match i with
  | Typing => fun X => (X*X)%type
  | Conversion => fun X => (X*X*X)%type
  end.
  Instance FMapLpJdg (i : ILP) : FMap (jdgF i).
  Proof.
    destruct i; typeclasses eauto.
  Defined.
  Instance FuncLpJdg (i : ILP) : Eq1Functor (jdgF i).
  Proof.
    destruct i; typeclasses eauto.
  Defined.

  Instance LpMakeJdg : IMakeJdg ILP := fun i => match i with
  | Typing => fun _ A t => (t, A)
  | Conversion => fun _ A t => (t, t, A)
  end.

  Instance LamMakeJdgNat (i : ILP) : NatFromProd (make_jdg(IMakeJdg:=LpMakeJdg) i).
  Proof.
    destruct i; constructor; reflexivity.
  Qed.

  Definition nA := 0.
  Definition nB := 1.
  Definition nA' := 2.
  Definition nB' := 3.
  Definition nt := 4.
  Definition nu := 5.
  Definition nv := 6.
  Definition nt' := 7.
  Definition nu' := 8.
  Definition nv' := 9.
  Definition nb := 10.
  Definition nb' := 11.
  Definition nf := 12.

  Definition A {s} := M_mvar(sig:=sig_lp) s nA.
  Definition B {s} := M_mvar(sig:=sig_lp) s nB.
  Definition A' {s} := M_mvar(sig:=sig_lp) s nA'.
  Definition B' {s} := M_mvar(sig:=sig_lp) s nB'.
  Definition t {s} := M_mvar(sig:=sig_lp) s nt.
  Definition u {s} := M_mvar(sig:=sig_lp) s nu.
  Definition v {s} := M_mvar(sig:=sig_lp) s nv.
  Definition t' {s} := M_mvar(sig:=sig_lp) s nt'.
  Definition u' {s} := M_mvar(sig:=sig_lp) s nu'.
  Definition v' {s} := M_mvar(sig:=sig_lp) s nv'.
  Definition b {s} := M_mvar(sig:=sig_lp) s nb.
  Definition b' {s} := M_mvar(sig:=sig_lp) s nb'.
  Definition f {s} := M_mvar(sig:=sig_lp) s nf.

  (* Conversion rules *)
  #[refine] Definition tRefl : rule(sig:=sig_lp) Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Typing _
          mnil
          (t[], A[])
      ];
      conclusion := _
    |}.
  Proof.
  exact (fun _ u => u).
  exact (fun _ => (t[], t[], A[])).
  Defined.

  Definition tSym : rule(sig:=sig_lp) Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Conversion (fun _ u => u)
          mnil
          (t[], u[], A[])
      ];
      conclusion := fun _ => (u[], t[], A[])
    |}.

  Definition tTrans : rule(sig:=sig_lp) Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Conversion (fun _ u => u)
          mnil
          (t[], u[], A[]) ;
        prem_ind Conversion (fun _ u => u)
          mnil
          (u[], v[], A[])
      ];
      conclusion := fun _ => (t[], v[], A[])
    |}.

  Definition tCongrApp : rule Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Conversion (fun _ u => u)
          mnil
          (t[], t'[], Pi (A[]) (B[var 0])) ;
        prem_ind Conversion (fun _ u => u)
          mnil
          (u[], u'[], A[])
      ];
      conclusion := fun _ =>
        (App (t[]) (u[]), App (t'[]) (u'[]), B[u[]])
    |}.

  Definition tCongrPi : rule Conversion :=
    {|
      premises := fun '(n, m) => [
        prem_ind Conversion (fun _ u => u)
          mnil
          (A[], A'[], T n) ;
        prem_ind Conversion (fun _ u => u)
          (mcons (T n) mnil)
          (B[var 0], B'[var 0], T m)
      ];
      conclusion := fun '(n, m) =>
        (Pi (A[]) (B[var 0]), Pi (A'[]) (B'[var 0]), T (Nat.max n m))
    |}.

  Definition tCongrLam : rule Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Conversion (fun _ u => u)
          (mcons (A[]) mnil)
          (b[var 0], b'[var 0], B[var 0])
      ];
      conclusion := fun _ =>
        (lambda (b[var 0]), lambda (b'[var 0]), Pi (A[]) (B[var 0]))
    |}.

  #[refine] Definition tBeta : rule(sig:=sig_lp) Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Typing _
          (mcons (A[]) mnil)
          (b[var 0], B[var 0]) ;
        prem_ind Typing _
          mnil
          (u[], A[])
      ];
      conclusion := fun (t : unit) => _
    |}.
  Proof.
    - exact (fun _ u => u).
    - exact (fun _ u => u).
    - exact (App (lambda (b[var 0])) (u[]), b[u[]], B[u[]]).
  Defined.

  #[refine] Definition tEta : rule Conversion :=
    {|
      premises := fun (_ : unit) => [
        prem_ind Typing _
          mnil
          (f[], Pi (A[]) (B[var 0]))
      ];
      conclusion := fun _ => _
    |}.
  Proof.
    - exact (fun _ u => u).
    - exact (f[], lambda (App (f[]) (var 0)), Pi (A[]) (B[var 0])).
  Defined.

  (* Typing rules *)
  #[refine] Definition tType : rule(sig:=sig_lp) Typing :=
    {|
      premises := fun _ => [];
      conclusion := fun n : nat => _
    |}.
  Proof.
    exact (T n, T (S n)).
  Defined.

  Definition tPi : rule Typing :=
    {|
      premises := fun '(n, m) =>
      [
        prem_ind Typing (fun _ A => A)
          mnil
          (A[], T n) ;
        prem_ind Typing (fun _ A => A)
          (mcons(n:=0) (A[]) mnil)
          (B[var 0], T m)
      ] ;
      conclusion := fun '(n, m) =>
        (Pi (A[]) (B[var 0]), T (Nat.max n m))
    |}.

  Definition tApp : rule Typing :=
    {|
      premises := fun (_ : unit) =>
      [
        prem_ind Typing (fun _ A => A)
          mnil
          (f[], Pi (A[]) (B[var 0]));
        prem_ind Typing (fun _ A => A)
          mnil
          (u[], A[])
      ];
      conclusion := fun _ =>
        (App (f[]) (u[]), B[u[]])
    |}.

  Definition tLam : rule Typing :=
    {|
      premises := fun (_ : unit) =>
      [
        prem_ind Typing (fun _ A => A)
          (mcons(n:=0) (A[]) mnil)
          (b[var 0], B[var 0])
      ];
      conclusion := fun _ =>
        (lambda (b[var 0]), Pi (A[]) (B[var 0]))
    |}.

  #[refine] Definition tConv : rule(sig:=sig_lp) Typing :=
    {|
      premises := fun (n : nat) =>
      [
        prem_ind Typing (fun _ A => A)
          (mnil)
          (t[], A[]);
        prem_ind Conversion _
          mnil
          (A[], A'[], T n)
      ];
      conclusion := fun _ =>
        (t[], A'[])
    |}.
  Proof.
    exact (fun _ u => u).
  Defined.

  Definition typ_lampi : jdg_sig := {| rules :=
    fun u => match u with
      | Conversion => [
        tRefl; tSym; tTrans;
        tCongrApp; tCongrPi; tCongrLam;
        tBeta ; tEta
      ]
      | Typing => [
        tType ; tPi ; tApp ; tLam ; tConv
      ]
    end
  |}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).
  (* #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lp) tt Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_conv_lampi) tt Δ σ Γ) (at level 70, σ at level 50). *)

  Notation "Γ ⊢ u ≡ v : A" := (proof(jsig:=typ_lampi) Conversion Γ (u, v, A)) (at level 70, u at level 50, v at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ t : A" := (proof(jsig:=typ_lampi) Typing Γ (t, A)) (at level 70, t at level 50).

  Lemma subst_minus_plus_zero :
    (fun i => E_var(sig:=sig_lp) (i - 0 + 0)) =₁ sid.
  Proof. intro; unfold sid; f_equal; lia. Qed.

  Lemma typed_refl Γ t A :
    Γ ⊢ t : A ->
    Γ ⊢ t ≡ t : A.
  Proof.
    intro.
    pose (m := fun k s =>
      if k =? nt then t else
      if k =? nA then A else
      default_menv k s
    ).
    eapply conv_proof_j.
    unshelve econstructor. exact m. exact tRefl. exact tt. repeat (try (left; reflexivity); right).
    3: {cbn. setoid_rewrite nth_error_nil.
      rewrite subst_minus_plus_zero. rewrite !subst_sid. reflexivity.
    }
    - intros. destruct_n H0. noconf H0.
      rewrite map_id. simpl. cbn.
      setoid_rewrite nth_error_nil. rewrite subst_minus_plus_zero.
      rewrite !subst_sid.
      assumption.
    - intros. destruct_n H0. noconf H0.
  Qed.

  Lemma conv_typed Γ s t A :
    Γ ⊢ t ≡ s : A ->
    Γ ⊢ t : A.
  Proof.
    (* We do not want to do the proof in this framework: indeed, we need an induction on [Γ ⊢ t ≡ s : A], which will be very heavy here. We would prefer to do the proof in the "nice" Rocq inductive of the relation, then transfer it to the parametric world *)
  Admitted.

  Instance LPSubst : SubstJSig typ_lampi.
  Proof.
    constructor; intros; destruct i; destruct_n H; subst; try destruct x; destruct_n H0; try now inversion H0; try typeclasses eauto.
    all: noconf H0;
    unfold ConvMakeJdg; intros; rewrite map_id; try assumption;
    unfold make_jdg, LpMakeJdg in *.
    all: try apply typed_refl; try assumption.
    all: eapply conv_typed; apply H.
  Qed.

  (* Sanity check *)
  Lemma beta_rev n :
    [] ⊢ eT n ≡ eApp (elambda (E_var 0)) (eT n) : eT (S n).
  Proof.
    (* Apply symmetry *)
    pose (msym := fun k s =>
      if (k=?nu) then (eT n)
      else if (k=?nt) then (eApp (elambda (E_var 0)) (eT n))
      else if (k=?nA) then (eT (S n))
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact msym. exact tSym. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: {intros. destruct_n H. inversion H. }
    intros. destruct_n H.
    noconf H. simpl.
    (* Just to avoid unfolding too much *)
    unshelve eapply conv_proof_j.
    exact ((eApp (elambda (E_var 0)) (eT n)), eT n, eT (S n)).
    2: reflexivity.

    (* Apply beta *)
    pose (mbeta := fun k s =>
      if (k=?nb) then (E_var 0)
      else if (k=?nu) then (eT n)
      else if (k=?nA) then (eT (S n))
      else if (k=?nB) then (eT (S n))
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact mbeta. exact tBeta. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H; noconf H.
    - simpl. unfold inst_jdg, fmap, FMapProd, fmap, FMapId.
      unshelve eapply conv_proof_j. exact (make_jdg Typing _ (eT (S n)) (E_var 0)).
      2: reflexivity.
      apply tvar. constructor.
    - simpl. unfold inst_jdg, fmap, FMapProd, fmap, FMapId.
      unshelve eapply (conv_proof_j). exact (eT n, eT (S n)).
      2: reflexivity.
      eapply conv_proof_j.
      unshelve econstructor. exact default_menv. exact tType.
      exact n. repeat (try (left; reflexivity); right).
      3: reflexivity.
      2: {intros. destruct_n H. }
      intros. noconf H.
  Qed.

  Lemma proof_type_id n :
    [] ⊢ elambda (E_var 0) : ePi (eT n) (eT n).
  Proof.
    pose (m := fun k s =>
      if (k=?nb) then (E_var 0)
      else if (k=?nA) then (eT n)
      else if (k=?nB) then (eT n)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. exact tLam. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: intros; destruct_n H; noconf H.
    intros. destruct_n H.
    noconf H. simpl.
    eapply conv_proof_j. apply tvar. constructor.
    reflexivity.
  Qed.

  Lemma proof_type_id_app n :
    [eT n] ⊢ eApp (elambda (E_var 0)) (E_var 0) : (eT n).
  Proof.
    pose (m := fun k s =>
      if (k=?nf) then (elambda (E_var 0))
      else if (k=?nu) then (E_var 0)
      else if (k=?nA) then (eT n)
      else if (k=?nB) then (eT n)
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tApp. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: intros; destruct_n H; noconf H.
    intros. destruct_n H.
    - noconf H.
      simpl. unfold fmap, FMapId. simpl.
      eapply conv_proof_j.
      eapply (weaken_typing (jsig:=typ_lampi)).
      apply (proof_type_id n).
      reflexivity.
      Unshelve.
      apply SubstJdg_RenJdg. typeclasses eauto.
    - noconf H. simpl.
      eapply conv_proof_j. apply tvar. constructor.
      reflexivity.
  Qed.

  Lemma proof_typee_id_app_lam n :
    [eT n] ⊢ eApp (elambda (E_var 0)) (E_var 0) :
    eApp (elambda (E_var 0)) (eT n).
  Proof.
    (* Use the conversion rule *)
    pose (m := fun k s =>
      if (k=?nt) then (eApp (elambda (E_var 0)) (E_var 0))
      else if (k=?nA) then (eT n)
      else if (k=?nA') then (eApp (elambda (E_var 0)) (eT n))
      else (default_menv k s)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tConv. exact (S n). repeat (try (left; reflexivity); right).
    3: reflexivity.
    - (* Inductive premise *)
      intros. destruct_n H; noconf H.
      + unfold inst_jdg, inst_ctx, fmap, FMapProd, fmap, FMapId.
        simpl. unfold fmap, FMapId.
        unshelve eapply conv_proof_j. exact (eApp (elambda (E_var 0)) (E_var 0), eT n). 2: reflexivity.
        apply proof_type_id_app.
      + simpl.
        eapply (conv_proof_j).
        eapply (weaken_typing(jsig:=typ_lampi)).
        Unshelve.
        3: exact (eT n, eApp (elambda (E_var 0)) (eT n), eT (S n)).
        2: reflexivity.
        apply beta_rev.
    - (* Predicate premise *)
      intros. destruct_n H; noconf H.
  Qed.
End LPEta.
