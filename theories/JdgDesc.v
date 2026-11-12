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
From Sulfur Require Import JdgShape.
From Utils Require Import Functor.

(** Judgments and declarations are built on shapes *)

Record jshape (decl : shape) := jshape_of {
  js_jdg : shape ;
  js_var : sel decl js_jdg
}.

Arguments js_jdg {decl}.
Arguments js_var {decl}.

Class Shapes := shapes {
  sh_decl : shape ;
  sh_jdgs : list (jshape sh_decl)
}.

#[local]
Abbreviation ctx T := (list (tuple sh_decl T)).

#[local]
Abbreviation dmap f := (tuple_map sh_decl f).

#[local]
Abbreviation cmap f := (List.map (dmap f)).

Section Shaped.

  Context {sh : Shapes}.

  (** The judgments of the block *)
  Definition Idx := fin (List.length sh_jdgs).

  Definition sh_vec := vec_of_list sh_jdgs.
  Definition sh_at (i : Idx) := vec_nth sh_vec i.
  Definition sh_jdg (i : Idx) := js_jdg (sh_at i).
  Definition sh_var (i : Idx) := js_var (sh_at i).

  (** Type of the concrete judgment [i] *)
  Definition jdg_type (T : Type) (i : Idx) : Type :=
    ctx T → cfun (X := T) (sh_jdg i) Prop.

  (** The concrete judgments packed together *)
  Definition jdg_types T :=
    hvec (λ js, ctx T → cfun (X := T) (js_jdg js) Prop) sh_vec.

  Definition jdg_at {T} (R : jdg_types T) : ∀ i, jdg_type T i :=
    hvec_nth _ sh_vec R.

End Shaped.

#[local]
Abbreviation jmap f := (tuple_map (sh_jdg _) f).

(** Judgment description over a signature *)

Section Desc.

  Context {sig : signature}.

  (** The type of concrete terms mentioned by predicate premises *)
  Context {T : Type}.

  (** The shape of the judgment *)
  Context {sh : Shapes}.

  (** Meta-judgments (built from the shape of judgment [i]) *)
  Definition mjdgd (i : Idx) sc : Type :=
    tuple (sh_jdg i) (mexpr Kt sc).

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

  (** Contexts of meta-declarations *)
  Definition hctx n := mctx (tuple sh_decl) 0 n.

  (** Premise description:
    - a judgment under an extension;
    - or a predicate over the context and values of the meta-variables
  *)
  Inductive premise_desc :=
  | pd_jdg i {n} (Δ : hctx n) (j : mjdgd i n)
  | pd_pred n (P : nary n T (ctx T → Prop)).

  Record rule_desc (js : jshape sh_decl) := {
    rd_name : string ;
    rd_params : list rule_param ;
    rd_premises : params rd_params → list premise_desc ;
    rd_conclusion : params rd_params → tuple (js_jdg js) (mexpr Kt 0)
  }.

  Definition jdg_desc :=
    hvec (λ js, list (rule_desc js)) sh_vec.

  Definition desc_rules (d : jdg_desc) (i : Idx) : list (rule_desc (sh_at i)) :=
    hvec_nth _ sh_vec d i.

End Desc.

Arguments rd_name {sig T sh js}.
Arguments rd_params {sig T sh js}.
Arguments rd_premises {sig T sh js}.
Arguments rd_conclusion {sig T sh js}.

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

  Context {sig T} {CS : ConcreteSyntax sig T}.
  Context {sh : Shapes}.

  #[local] Instance: IDecl Idx :=
    λ _, tuple sh_decl.

  #[local] Instance: IJdg Idx :=
    λ i, tuple (sh_jdg i).

  Definition to_premise {i} ar m (pd : premise_desc (T := T)) : premise i :=
    match pd with
    | pd_jdg ix Δ j => prem_ind (i := i) ix (λ X x, x) Δ j
    | pd_pred n P =>
      prem_pred i (λ Γ me, napply (ev_vals ar m me) _ 0 P (cmap ceval Γ))
    end.

  Definition to_rule {i} (rd : rule_desc (sh_at i)) : rule i := {|
    param := params rd.(rd_params) ;
    premises :=
      λ x, map (to_premise (rd_arity rd) (rd_nterms rd)) (rd.(rd_premises) x) ;
    conclusion := rd.(rd_conclusion)
  |}.

  (* Somehow, universe issues prevent using List.map directly *)
  Fixpoint to_rules {i} (rs : list (rule_desc (sh_at i))) : list (rule i) :=
    match rs with
    | [] => []
    | rd :: rs => to_rule rd :: to_rules rs
    end.

  Definition to_jdg_sig (d : jdg_desc) : jdg_sig := {|
    rules := λ i, to_rules (i := i) (desc_rules d i)
  |}.

  Lemma in_to_rules i rd rs :
    In rd rs →
    In (to_rule rd) (to_rules (i := i) rs).
  Proof.
    induction rs as [| rd' rs ih]. 1: contradiction.
    intros [-> | h]. all: cbn. all: auto.
  Qed.

  Lemma in_to_rules_inv i r rs :
    In r (to_rules (i := i) rs) →
    ∃ rd, In rd rs ∧ r = to_rule rd.
  Proof.
    induction rs as [| rd rs ih]. 1: contradiction.
    intros [<- | h]. all: cbn.
    - exists rd. auto.
    - destruct (ih h) as (rd' & hin & e). exists rd'. auto.
  Qed.

End ToSig.

(** Higher-order presentation of rules

  Meta-variables are abstracted as functions.

*)

Section HOAS.

  Context {sig : signature} {T : Type} {sh : Shapes}.

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

  Definition hjdg_ty i : Type :=
    tuple (sh_jdg i) hterm.

  Definition hdecl : Type :=
    tuple sh_decl hterm.

  Definition hjdg {i} : cfun (sh_jdg i) (hjdg_ty i) :=
    JdgShape.curry id.

  Definition hprem :=
    ∀ s, hctx s → premise_desc (T := T).

  Definition hjp {i} (j : hjdg_ty i) : hprem :=
    λ s Δ, pd_jdg i Δ (jmap (λ t, t s) j).

  Definition hext (d : hdecl) (P : hterm → hprem) : hprem :=
    λ s Δ, P (hvar s) (S s) (mcons (dmap (λ t, t (s + 0)) d) Δ).

  Definition hpred n (P : nary n T (ctx T → Prop)) : hprem :=
    λ _ _, pd_pred n P.

  Definition hrule {i} name ps (pr_cl : hfun ps (list hprem * hjdg_ty i))
  : rule_desc (sh_at i) := {|
    rd_name := name ;
    rd_params := ps ;
    rd_premises := λ x, map (λ p, p 0 mnil) (fst (happly ps 0 pr_cl x)) ;
    rd_conclusion := λ x, jmap (λ t, t 0) (snd (happly ps 0 pr_cl x))
  |}.

End HOAS.

Coercion hjp : hjdg_ty >-> hprem.

Notation "⟨ x ↦ A ⊢ P ⟩" :=
  (hext A (λ x, P))
  (at level 0, x name, A at level 69, P at level 200).

(** Instantiate mexpr to concrete syntax *)

Section Inst.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.
  Context {sh : Shapes}.

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

  Fixpoint cinst_ctx {n} (Δ : hctx n) : ctx T :=
    match Δ with
    | mnil => []
    | mcons d Δ => dmap cinst d :: cinst_ctx Δ
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

  Context {sig T} {CS : ConcreteSyntax sig T}.
  Context {sh : Shapes}.

  (* The concrete judgments being defined *)
  Context (J : ∀ i, jdg_type T i).

  Definition conc_jdg {i s} (Γ : ctx T) (ι : mvar → T) (j : mjdgd i s) : Prop :=
    capply (J i Γ) (jmap (cinst ι) j).

  Definition conc_prem (Γ : ctx T) (ι : mvar → T) (pd : premise_desc) :=
    match pd with
    | pd_jdg i Δ j => conc_jdg (cinst_ctx ι Δ ++ Γ) ι j
    | pd_pred n P => napply ι n 0 P Γ
    end.

  (** [∀ x1 ... xn, K [x1; ...; xn]]. *)
  Fixpoint under ps (ms : list T) : (list T → params ps → Prop) → Prop :=
    match ps with
    | [] => λ K, K (rev ms) tt
    | rp_term _ :: ps => λ K, ∀ x, under ps (x :: ms) K
    | rp_param A :: ps => λ K, ∀ (a : A), under ps ms (λ l p, K l (a, p))
    end.

  Definition rule_desc_type {i} (rd : rule_desc (sh_at i)) (Γ : ctx T) : Prop :=
    under rd.(rd_params) [] (λ vs x,
      fold_right
        (λ P Q, P → Q)
        (conc_jdg Γ (nvar vs) (rd.(rd_conclusion) x))
        (map (conc_prem Γ (nvar vs)) (rd.(rd_premises) x))
    ).

  (* Lookup declarations in a context, shifted by [f] *)
  Inductive cinctx {D} (f : D → D) : list D → nat → D → Prop :=
  | cin_head d Γ : cinctx f (d :: Γ) 0 (f d)
  | cin_tail d d' Γ n : cinctx f Γ n d → cinctx f (d' :: Γ) (S n) (f d).

  Definition var_rule_type i :=
    ∀ Γ n d,
      cinctx (dmap (crename rshift)) Γ n d →
      capply (J i Γ) (make (sh_var i) d (cvar n)).

  (* The variable rules of every judgment, as the command proves them *)
  Definition var_rules :=
    Forall_rec var_rule_type (fin_all _).

  Lemma var_rules_all :
    var_rules →
    ∀ i, var_rule_type i.
  Proof.
    intros h i.
    unfold var_rules in h.
    rewrite Forall_rec_iff, Forall_forall in h.
    apply h. apply In_fin_all.
  Qed.

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

  Context {sig T} {CS : ConcreteSyntax sig T}.
  Context {sh : Shapes}.
  Context (desc : jdg_desc (T := T)).
  Context (J : ∀ i, jdg_type T i).

  (* Induction hyopthesis only for [pd_jdg] *)
  Definition ind_prem P Γ ι pd K : Prop :=
    match pd with
    | pd_jdg _ _ _ => conc_prem J Γ ι pd → conc_prem P Γ ι pd → K
    | pd_pred _ _ => conc_prem J Γ ι pd → K
    end.

  (* Like [rule_desc_type] but collecting induction hypotheses *)
  Definition rule_ind_case {i} P (rd : rule_desc (sh_at i)) (Γ : ctx T) : Prop :=
    under rd.(rd_params) [] (λ vs x,
      fold_right
        (ind_prem P Γ (nvar vs))
        (conc_jdg P Γ (nvar vs) (rd.(rd_conclusion) x))
        (rd.(rd_premises) x)
    ).

  Definition ind_type :=
    ∀ (P : ∀ i, jdg_type T i),
      fold_right
        (λ i K,
          var_rule_type P i →
          fold_right
            (λ rd K, (∀ Γ, rule_ind_case P rd Γ) → K)
            K
            (desc_rules desc i)
        )
        (Forall_rec
          (λ i, ∀ Γ,
            under_tuple (λ j,
              capply (J i Γ) j → capply (P i Γ) j
            )
          )
          (fin_all _)
        )
        (fin_all _).

End Ind.

(** Deriving theorems for concrete syntax and judgments *)

Section ConcreteFacts.

  Context {sig T} {CS : ConcreteSyntax sig T} {sh : Shapes}.
  Context (desc : jdg_desc (T := T)).

  #[local] Instance Sig_IDecl : IDecl Idx := λ _, tuple sh_decl.
  #[local] Instance Sig_IJdg : IJdg Idx := λ i, tuple (sh_jdg i).
  #[local] Instance Sig_FMapDecl : ∀ i : Idx, FMap (declF i) :=
    λ _, FMap_tuple _.
  #[local] Instance Sig_FMapJdg : ∀ i : Idx, FMap (jdgF i) :=
    λ _, FMap_tuple _.
  #[local] Instance Sig_FuncDecl : ∀ i : Idx, Eq1Functor (declF i) :=
    λ _, Eq1Functor_tuple _.
  #[local] Instance Sig_FuncJdg : ∀ i : Idx, Eq1Functor (jdgF i) :=
    λ _, Eq1Functor_tuple _.
  #[local] Instance Sig_IMakeJdg : IMakeJdg Idx :=
    λ i X d x, make (sh_var i) d x.
  #[local] Instance Sig_NatMake : ∀ i : Idx, NatFromProd (make_jdg i).
  Proof. intro i. constructor. intros. apply make_nat. Qed.

  (* Soundness of rules *)

  Definition ctx_rf (Γ : ctx T) :=
    cmap creify Γ.

  Definition Pf i Γ j :=
    proof (jsig := to_jdg_sig desc) i (ctx_rf Γ) (jmap creify j).

  Definition J i : jdg_type T i :=
    λ Γ, JdgShape.curry (Pf i Γ).

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

  Lemma rf_cinst_tuple ι l s (j : tuple l (mexpr Kt s)) :
    tuple_map l creify (tuple_map l (cinst ι) j) =
    tuple_map l (inst (λ k _, creify (ι k))) j.
  Proof.
    apply tuple_map_comp_ext.
    intro t. apply rf_cinst_t.
  Qed.

  Lemma rf_cinst_ctx ι n (Δ : hctx n) :
    ctx_rf (cinst_ctx ι Δ) = inst_ctx (λ k _, creify (ι k)) Δ.
  Proof.
    induction Δ as [| n d Δ ih].
    - reflexivity.
    - cbn. unfold fmap, FMap_tuple.
      rewrite rf_cinst_tuple. f_equal. apply ih.
  Qed.

  Lemma rf_shift d :
    dmap creify (dmap (crename rshift) d) =
    dmap (rename rshift) (dmap creify d).
  Proof.
    rewrite 2!tuple_map_comp. apply tuple_map_ext.
    intro t. apply rf_rename.
  Qed.

  Lemma cinctx_inctx i Γ n d :
    cinctx (dmap (crename rshift)) Γ n d →
    @inctx sig (declF i) _ (ctx_rf Γ) n (dmap creify d).
  Proof.
    induction 1 as [d Γ | d d' Γ n h ih].
    - cbn. eapply conv_in_d. 1: econstructor.
      rewrite rf_shift. reflexivity.
    - cbn. eapply conv_in_d. 1:{ econstructor. eassumption. }
      rewrite rf_shift. reflexivity.
  Qed.

  Lemma sound_var i : var_rule_type J i.
  Proof.
    intros Γ n d h.
    unfold J. rewrite capply_curry.
    unfold Pf.
    rewrite make_nat. rewrite rf_var.
    eapply conv_proof_j.
    - eapply tvar. eapply cinctx_inctx. eassumption.
    - reflexivity.
  Qed.

  Definition wf_jdg {i s} ar m (j : mjdgd i s) :=
    tuple_allb (wf_mexpr ar m) j.

  Fixpoint wf_ctx ar m {n} (Δ : hctx n) : bool :=
    match Δ with
    | mnil => true
    | mcons d Δ => tuple_allb (wf_mexpr ar m) d && wf_ctx ar m Δ
    end.

  Definition wf_prem ar m (pd : premise_desc (T := T)) :=
    match pd with
    | pd_jdg _ Δ j => wf_ctx ar m Δ && wf_jdg ar m j
    | pd_pred _ _ => true
    end.

  Definition wf_rule_at {i} (rd : rule_desc (sh_at i)) x :=
    let ar := rd_arity rd in
    let m := rd_nterms rd in
    forallb (wf_prem ar m) (rd.(rd_premises) x) &&
    wf_jdg ar m (rd.(rd_conclusion) x).

  Definition wf_rule {i} rd :=
    ∀ x, wf_rule_at (i := i) rd x = true.

  Definition wf_desc :=
    Forall_rec (λ i, Forall wf_rule (desc_rules desc i)) (fin_all _).

  Lemma wf_desc_rule i rd :
    wf_desc →
    In rd (desc_rules desc i) →
    wf_rule rd.
  Proof.
    intros h hin.
    unfold wf_desc in h. rewrite Forall_rec_iff in h.
    rewrite Forall_forall in h.
    specialize (h i (In_fin_all i)). rewrite Forall_forall in h.
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

  Lemma ev_ctx_rf (Γ : ctx T) :
    cmap ceval (ctx_rf Γ) = Γ.
  Proof.
    unfold ctx_rf. rewrite map_map.
    erewrite map_ext. 1: apply map_id.
    intros d. rewrite tuple_map_comp.
    erewrite tuple_map_ext. 1: apply tuple_map_id.
    intros t. apply ev_rf.
  Qed.

  Lemma sound_step i rd Γ :
    In rd (desc_rules desc i) →
    rule_desc_type J rd Γ.
  Proof.
    intros h.
    red. rewrite <- under_iff. intros vs x hvs. cbn.
    rewrite <- fold_impl_iff. intros hF.
    rewrite Forall_map in hF.
    unfold conc_jdg, J.
    rewrite capply_curry. unfold Pf.
    rewrite rf_cinst_tuple.
    eapply conv_proof_j.
    - eapply step
      with (r := to_rule rd) (m := λ k _, creify (nvar vs k)) (x := x).
      + apply in_to_rules. assumption.
      + intros i' n Δ j conv hin. cbn in hin.
        rewrite in_map_iff in hin. destruct hin as [pd [hp hp']].
        destruct pd as [n' Δ' j' | ]. 2: discriminate.
        noconf hp.
        cbn. rewrite map_id.
        rewrite Forall_forall in hF. specialize (hF _ hp').
        unfold conc_prem, conc_jdg, J in hF. rewrite capply_curry in hF.
        unfold Pf, ctx_rf in hF.
        rewrite map_app, rf_cinst_ctx in hF.
        rewrite rf_cinst_tuple in hF.
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
    - reflexivity.
  Qed.

  (** Statements about a concrete judgment *)

  (* [σ] is a well-typed substitution from [Δ] to [Γ] for judgment [i] *)
  Inductive cstyping i (Ri : jdg_type T i) : ctx T → (nat → T) → ctx T → Prop :=
  | cstyping_nil Δ σ : cstyping i Ri Δ σ []
  | cstyping_cons Δ σ Γ d :
      cstyping i Ri Δ (λ k, σ (S k)) Γ →
      capply (Ri Δ) (
        make (sh_var i) (dmap (csubstitute (λ k, σ (S k))) d) (σ 0)
      ) →
      cstyping i Ri Δ σ (d :: Γ).

  Section Statements.

    Context (R : ∀ i, jdg_type T i).

    Definition rules_type :=
      Forall_rec (λ i,
        Forall (λ rd, ∀ Γ, rule_desc_type R rd Γ) (desc_rules desc i)
      ) (fin_all _).

    Lemma rules_type_rule i rd Γ :
      rules_type →
      In rd (desc_rules desc i) →
      rule_desc_type R rd Γ.
    Proof.
      intros h hin.
      unfold rules_type in h. rewrite Forall_rec_iff, Forall_forall in h.
      specialize (h i (In_fin_all i)). rewrite Forall_forall in h.
      apply h. assumption.
    Qed.

    Definition sound_jdg :=
      ∀ i Γ, under_tuple (λ j, capply (R i Γ) j → capply (J i Γ) j).

    Definition complete_jdg :=
      ∀ i Γ j,
        proof (jsig := to_jdg_sig desc) i Γ j →
        capply (R i (cmap ceval Γ)) (jmap ceval j).

    Definition preserve_subst_jdg i :=
      ∀ Γ Δ σ,
        under_tuple (λ j,
          capply (R i Γ) j →
          cstyping i (R i) Δ σ Γ →
          capply (R i Δ) (jmap (csubstitute σ) j)
        ).

    (** Obligations for [preserve_subst_jdg]

      Every predicate premise must be stable under well-typed substitutions.

    *)

    Definition subst_vals ar nt (σ : nat → T) (vs : list T) : list T :=
      map (λ k, csubstitute (cups_subst (ar k) σ) (nvar vs k)) (seq 0 nt).

    Definition pred_stable ar nt Γ Δ σ vs (pd : premise_desc (T := T)) :=
      match pd with
      | pd_jdg _ _ _ => True
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

    (* Obligation for the [k]-th premise of a rule *)
    Definition pred_obl {i} (rd : rule_desc (sh_at i)) k : Prop :=
      let ar := rd_arity rd in
      let nt := rd_nterms rd in
      under rd.(rd_params) [] (λ vs x,
        ∀ Γ Δ σ,
          cstyping i (R i) Δ σ Γ →
          stable_at ar nt Γ Δ σ vs (rd.(rd_premises) x) k
      ).

    (* Obligation related to [make] *)
    Definition make_obl i i' : Prop :=
      ∀ Γ d t,
        capply (R i Γ) (make (sh_var i) d t) →
        capply (R i' Γ) (make (sh_var i') d t).

    (** Obligation references for the plugin *)
    Inductive ob :=
    | ob_pred (j : Idx) (r i : nat)
    | ob_make (i i' : Idx).

    Definition obligation (o : ob) : Prop :=
      match o with
      | ob_pred j r i =>
        match nth_error (desc_rules desc j) r with
        | Some rd => pred_obl rd i
        | None => True
        end
      | ob_make i i' => make_obl i i'
      end.

    Definition obligations (l : list ob) :=
      Forall_rec obligation l.

    Definition mem_pred (j : Idx) (r i : nat) (l : list ob) :=
      existsb (λ o,
        match o with
        | ob_pred j' r' i' => eqb_fin j j' && (r =? r') && (i =? i')
        | _ => false
        end
      ) l.

    Definition mem_make (i i' : Idx) (l : list ob) :=
      existsb (λ o,
        match o with
        | ob_make j j' => eqb_fin i j && eqb_fin i' j'
        | _ => false
        end
      ) l.

    Definition prem_ok i r k (pd : premise_desc (T := T)) l :=
      match pd with
      | pd_pred _ _ => mem_pred i r k l
      | pd_jdg i' _ _ => eqb_fin i i' || mem_make i i' l
      end.

    Fixpoint pos_ok i r k (prems : list (premise_desc (T := T))) l :=
      match prems with
      | [] => true
      | pd :: prems => prem_ok i r k pd l && pos_ok i r (S k) prems l
      end.

    Fixpoint obls_ok_from i r (d : list (rule_desc (sh_at i))) l : Prop :=
      match d with
      | [] => True
      | rd :: d =>
        (∀ x, pos_ok i r 0 (rd.(rd_premises) x) l = true) ∧
        obls_ok_from i (S r) d l
      end.

    Definition obls_ok l : Prop :=
      Forall_rec (λ i, obls_ok_from i 0 (desc_rules desc i) l) (fin_all _).

    Lemma mem_pred_in j r i l :
      mem_pred j r i l = true →
      In (ob_pred j r i) l.
    Proof.
      unfold mem_pred. intros h.
      apply existsb_exists in h as (o & hin & e).
      destruct o as [j' r' i' |]. 2: discriminate.
      rewrite !andb_true_iff, eqb_fin_eq, !PeanoNat.Nat.eqb_eq in e.
      destruct e as [[-> ->] ->]. assumption.
    Qed.

    Lemma mem_make_in i i' l :
      mem_make i i' l = true →
      In (ob_make i i') l.
    Proof.
      unfold mem_make. intros h.
      apply existsb_exists in h as (o & hin & e).
      destruct o as [| j j']. 1: discriminate.
      rewrite andb_true_iff, !eqb_fin_eq in e.
      destruct e as [-> ->]. assumption.
    Qed.

    Lemma pos_ok_nth i r k prems l j pd :
      pos_ok i r k prems l = true →
      nth_error prems j = Some pd →
      prem_ok i r (k + j) pd l = true.
    Proof.
      induction prems as [| pd' prems ih] in k, j |- *.
      - destruct j. all: discriminate.
      - cbn. intros h e. rewrite andb_true_iff in h.
        destruct h as [h1 h2].
        destruct j as [| j].
        + injection e as ->. rewrite PeanoNat.Nat.add_0_r. assumption.
        + rewrite <- PeanoNat.Nat.add_succ_comm. eapply ih. all: eassumption.
    Qed.

    Lemma obls_ok_nth i r d l k rd x :
      obls_ok_from i r d l →
      nth_error d k = Some rd →
      pos_ok i (r + k) 0 (rd.(rd_premises) x) l = true.
    Proof.
      induction d as [| rd' d ih] in r, k, x |- *.
      - destruct k. all: discriminate.
      - intros [h1 h2] e. destruct k as [| k].
        + injection e as ->. rewrite PeanoNat.Nat.add_0_r. auto.
        + rewrite <- PeanoNat.Nat.add_succ_comm. eapply ih. all: eassumption.
    Qed.

    Lemma obls_ok_at l j :
      obls_ok l →
      obls_ok_from j 0 (desc_rules desc j) l.
    Proof.
      intros h. unfold obls_ok in h.
      rewrite Forall_rec_iff, Forall_forall in h.
      apply h. apply In_fin_all.
    Qed.

    Lemma obligation_at l j r rd x k n P :
      obls_ok l →
      obligations l →
      nth_error (desc_rules desc j) r = Some rd →
      nth_error (rd.(rd_premises) x) k = Some (pd_pred n P) →
      pred_obl rd k.
    Proof.
      intros hok ho hr hk. apply obls_ok_at with (j := j) in hok.
      eapply obls_ok_nth in hok. 2: exact hr. cbn in hok.
      eapply pos_ok_nth in hok. 2: exact hk. cbn in hok.
      apply mem_pred_in in hok.
      unfold obligations in ho. rewrite Forall_rec_iff, Forall_forall in ho.
      specialize (ho _ hok). cbn in ho. rewrite hr in ho.
      exact ho.
    Qed.

    Lemma make_obligation_at l i r rd x k i' n Δ j :
      obls_ok l →
      obligations l →
      nth_error (desc_rules desc i) r = Some rd →
      nth_error (rd.(rd_premises) x) k = Some (pd_jdg i' (n := n) Δ j) →
      make_obl i i'.
    Proof.
      intros hok ho hr hk. apply obls_ok_at with (j := i) in hok.
      eapply obls_ok_nth in hok. 2: exact hr. cbn in hok.
      eapply pos_ok_nth in hok. 2: exact hk. cbn in hok.
      rewrite orb_true_iff in hok. destruct hok as [e | hin].
      - apply eqb_fin_eq in e. subst i'. intros Γ d t h. exact h.
      - apply mem_make_in in hin.
        unfold obligations in ho. rewrite Forall_rec_iff, Forall_forall in ho.
        exact (ho _ hin).
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

  Lemma rule_ind_case_of_type {i} R P rd Γ :
    rule_desc_type P rd Γ →
    rule_ind_case (i := i) R P rd Γ.
  Proof.
    unfold rule_desc_type, rule_ind_case.
    rewrite <- !under_iff. intros h vs x hl. specialize (h vs x hl).
    cbn in *.
    induction (rd_premises rd) as [| pd l ih] in h |- *.
    - exact h.
    - cbn in *. destruct pd as [i' n Δ j | n Q].
      + cbn. intros _ hj. apply ih. apply h. exact hj.
      + cbn in *. eauto.
  Qed.

  Lemma ind_cases_elim R P (B : Prop) l :
    (∀ i, var_rule_type P i) →
    (∀ i rd, In rd (desc_rules desc i) → ∀ Γ, rule_ind_case R P rd Γ) →
    fold_right (λ i K,
      var_rule_type P i →
      fold_right
        (λ rd K, (∀ Γ, rule_ind_case R P rd Γ) → K) K
        (desc_rules desc i)
    ) B l →
    B.
  Proof.
    intros hv hr h.
    induction l as [| i l ih] in h |- *.
    - exact h.
    - cbn in h. specialize (h (hv i)).
      apply ih. eapply fold_cases_elim. 2: exact h.
      rewrite Forall_forall. intros rd hin.
      apply hr. assumption.
  Qed.

  Lemma sound_of_ind R :
    ind_type desc R →
    sound_jdg R.
  Proof.
    intros hind.
    specialize (hind J).
    eapply ind_cases_elim in hind. 2: exact sound_var.
    2:{
      intros i rd hin Γ.
      apply rule_ind_case_of_type. apply sound_step.
      assumption.
    }
    intros i Γ.
    rewrite Forall_rec_iff, Forall_forall in hind.
    apply hind. apply In_fin_all.
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

  Lemma ev_inst_tuple ar m me l s (j : tuple l (mexpr Kt s)) :
    tuple_allb (wf_mexpr ar m) j = true →
    tuple_map l ceval (tuple_map l (inst me) j) =
    tuple_map l (cinst (ev_vals ar m me)) j.
  Proof.
    intros h. rewrite tuple_map_comp.
    eapply tuple_map_ext_all. 2: eassumption.
    intros t ht. apply ev_inst. assumption.
  Qed.

  Lemma ev_inst_ctx ar m me n (Δ : hctx n) :
    wf_ctx ar m Δ = true →
    cmap ceval (inst_ctx me Δ) = cinst_ctx (ev_vals ar m me) Δ.
  Proof.
    intros h.
    induction Δ as [| n d Δ ih].
    - reflexivity.
    - cbn in h. rewrite andb_true_iff in h. destruct h as [hd hΔ].
      cbn. unfold fmap, FMap_tuple.
      erewrite ev_inst_tuple. 2: eassumption.
      f_equal. apply ih. assumption.
  Qed.

  Lemma ev_shift d :
    dmap ceval (dmap (rename rshift) d) =
    dmap (crename rshift) (dmap ceval d).
  Proof.
    rewrite 2!tuple_map_comp. apply tuple_map_ext.
    intro t. apply ev_rename.
  Qed.

  Lemma inctx_cinctx i Γ n d :
    @inctx sig (declF i) _ Γ n d →
    cinctx (dmap (crename rshift)) (cmap ceval Γ) n (dmap ceval d).
  Proof.
    induction 1 as [d Γ | d d' Γ n h ih].
    all: cbn. all: unfold fmap, Sig_FMapDecl, FMap_tuple.
    all: rewrite ev_shift.
    - constructor.
    - constructor. assumption.
  Qed.

  Section Completeness.

    Context (R : ∀ i, jdg_type T i).
    Context (hvar : var_rules R).
    Context (hrules : rules_type R).
    Context (hwf : wf_desc).

    Theorem jdg_complete : complete_jdg R.
    Proof.
      intros i Γ j.
      induction 1 as [i me Γ r x hin hind ih hpred | i Γ n d hd].
      - cbn in hin. apply in_to_rules_inv in hin as (rd & hin & ->). cbn.
        eapply wf_desc_rule in hwf. 2: exact hin.
        eapply rules_type_rule with (Γ := cmap ceval Γ) in hrules.
        2: eassumption.
        specialize (hwf x). unfold wf_rule, wf_rule_at, wf_jdg in hwf.
        rewrite !andb_true_iff in hwf.
        destruct hwf as (hwp & hwc).
        destruct rd as [name ps prems concl]. cbn in *.
        rewrite <- under_iff in hrules.
        specialize hrules
        with (x := x) (1 := ev_vs_length (CS := CS) (arity ps) (nterms ps) me).
        rewrite <- fold_impl_iff in hrules. cbn in hrules.
        unfold conc_jdg in hrules.
        unfold inst_jdg, fmap, Sig_FMapJdg, FMap_tuple.
        erewrite ev_inst_tuple. 2: eassumption.
        apply hrules.
        rewrite Forall_map, Forall_forall.
        intros pd hp.
        rewrite forallb_forall in hwp. specialize (hwp _ hp).
        destruct pd as [i' n Δ j | n P].
        + unfold wf_prem, wf_jdg in hwp. cbn in hwp.
          rewrite !andb_true_iff in hwp. destruct hwp as (hΔ & hwj).
          specialize (ih i' _ Δ j (λ X x, x)).
          specialize ih with (1 := in_map _ _ _ hp).
          cbn in ih. unfold inst_jdg, fmap, Sig_FMapJdg, FMap_tuple in ih.
          rewrite map_id in ih.
          rewrite map_app in ih.
          erewrite ev_inst_ctx in ih. 2: eassumption.
          erewrite ev_inst_tuple in ih. 2: eassumption.
          exact ih.
        + eapply in_map in hp. specialize (hpred _ hp). assumption.
      - unfold make_jdg, Sig_IMakeJdg. rewrite make_nat. rewrite ev_var.
        apply var_rules_all. 1: exact hvar.
        apply inctx_cinctx. assumption.
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

    Context (R : ∀ i, jdg_type T i).
    Context (hsound : sound_jdg R).
    Context (hcomplete : complete_jdg R).
    Context obs (hok : obls_ok obs) (hobls : obligations R obs).

    Lemma rf_subst_tuple σ l (j : tuple l T) :
      tuple_map l creify (tuple_map l (csubstitute σ) j) =
      tuple_map l (substitute (λ i, creify (σ i))) (tuple_map l creify j).
    Proof.
      rewrite 2!tuple_map_comp. apply tuple_map_ext.
      intro t. apply rf_substitute.
    Qed.

    Lemma cstyping_styping i Δ σ Γ :
      cstyping i (R i) Δ σ Γ →
      styping (jsig := to_jdg_sig desc) i (ctx_rf Δ) (λ k, creify (σ k)) (ctx_rf Γ).
    Proof.
      induction 1 as [Δ σ | Δ σ Γ d h ih hd].
      - constructor.
      - cbn. constructor. 1: exact ih.
        pose proof (hsound i Δ) as hs. rewrite under_tuple_iff in hs.
        apply hs in hd. unfold J in hd. rewrite capply_curry in hd.
        unfold Pf in hd. rewrite make_nat, rf_subst_tuple in hd.
        exact hd.
    Qed.

    Lemma styping_cstyping i Δ σ Γ :
      styping (jsig := to_jdg_sig desc) i Δ σ Γ →
      cstyping i (R i) (cmap ceval Δ) (λ i, ceval (σ i)) (cmap ceval Γ).
    Proof.
      induction 1 as [i Δ σ | i Δ σ Γ d h ih hd].
      - constructor.
      - cbn. constructor. 1: exact ih.
        apply hcomplete in hd.
        unfold fmap, Sig_FMapDecl, FMap_tuple in hd.
        unfold make_jdg, Sig_IMakeJdg in hd.
        rewrite make_nat in hd. rewrite tuple_map_comp in hd.
        rewrite tuple_map_comp. erewrite tuple_map_ext. 1: apply hd.
        intro t. rewrite ev_substitute. apply csubstitute_ext.
        intro k. reflexivity.
    Qed.

    Lemma rf_ev_ctx Γ :
      ctx_rf (cmap ceval Γ) = Γ.
    Proof.
      unfold ctx_rf. rewrite map_map.
      erewrite map_ext. 1: apply map_id.
      intro d. erewrite tuple_map_comp_ext. 1: apply tuple_map_id.
      intro t. apply rf_ev.
    Qed.

    Lemma subst_sig : SubstJSig (to_jdg_sig desc).
    Proof.
      constructor.
      - intros i r x P hr hP. cbn in hr.
        apply in_to_rules_inv in hr as (rd & hr & ->).
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (pd & e & hin).
        destruct pd as [| n Q]. 1: discriminate.
        noconf e.
        intros Γ σ Δ m hs h.
        apply In_nth_error in hin as [k hi].
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
      - intros i r x P hr hP. cbn in hr.
        apply in_to_rules_inv in hr as (rd & hr & ->).
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (pd & e & hin).
        destruct pd as [| n Q]. 1: discriminate.
        noconf e.
        intros Γ m m' h hm.
        unfold ev_vals in *. erewrite <- ev_vs_ext. 1: exact h.
        apply hm.
      - intros i r x hr n i' conv Δ j hP. cbn in hr.
        apply in_to_rules_inv in hr as (rd & hr & ->).
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (pd & e & ?).
        destruct pd as [i'' n' Δ' j' |]. 2: discriminate.
        noconf e.
        intros X Y f d. reflexivity.
      - intros i r x hr n i' conv Δ j hP. cbn in hr.
        apply in_to_rules_inv in hr as (rd & hr & ->).
        cbn in hP. rewrite in_map_iff in hP.
        destruct hP as (pd & e & hin).
        destruct pd as [i'' n' Δ' j' |]. 2: discriminate.
        noconf e.
        intros Γ d t h. rewrite map_id.
        apply In_nth_error in hin as [k hk].
        apply In_nth_error in hr as [ri hr].
        pose proof (make_obligation_at _ _ _ _ _ _ _ _ _ _ _ hok hobls hr hk)
        as ho.
        apply hcomplete in h.
        unfold fmap, Sig_FMapJdg, FMap_tuple, make_jdg, Sig_IMakeJdg in h.
        rewrite make_nat in h. apply ho in h.
        pose proof (hsound i' (cmap ceval Γ)) as hs.
        rewrite under_tuple_iff in hs. apply hs in h.
        unfold J in h. rewrite capply_curry in h. unfold Pf in h.
        rewrite rf_ev_ctx, make_nat, rf_ev in h.
        erewrite tuple_map_comp_ext in h. 2:{ intro. apply rf_ev. }
        rewrite tuple_map_id in h. exact h.
    Qed.

    Theorem gen_preserve_subst i : preserve_subst_jdg R i.
    Proof.
      intros Γ Δ σ.
      rewrite under_tuple_iff. intros j hj hs.
      pose proof (hsound i Γ) as hsΓ. rewrite under_tuple_iff in hsΓ.
      apply hsΓ in hj. unfold J in hj. rewrite capply_curry in hj.
      unfold Pf in hj.
      apply cstyping_styping in hs.
      eapply (preserve_subst (HSubstSig := subst_sig)) in hj. 2: eassumption.
      apply hcomplete in hj.
      rewrite ev_ctx_rf in hj.
      unfold substitute_jdg in hj.
      unfold fmap, Sig_FMapJdg, FMap_tuple in hj.
      rewrite 2!tuple_map_comp in hj.
      erewrite tuple_map_ext in hj. 1: exact hj.
      intro t. cbn. rewrite ev_substitute, ev_rf.
      apply csubstitute_ext. intro k. apply ev_rf.
    Qed.

  End Preservation.

End ConcreteFacts.

(** Tactics for the plugin *)

(** Prove [wf_desc] *)
Ltac wf_desc_tac :=
  repeat constructor ;
  intro ; reflexivity.

(** Split [var_rules], a [Forall_rec], into the variable rules of the
  judgments *)
Ltac split_forall_rec :=
  hnf ;
  lazymatch goal with
  | |- _ ∧ _ => split ; [ | split_forall_rec ]
  | _ => idtac
  end.
