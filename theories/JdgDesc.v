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

End ToSig.

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
    crename : ren -> T -> T ;
    cctor : ∀ c, cargs (ctor_type c) → T
  }.

End ConcreteSyntax.

Arguments carg {sig}.
Arguments cargs {sig}.
Arguments ckind {sig}.

Arguments cvar {sig T _}.
Arguments crename {sig T _}.
Arguments cctor {sig T _}.

(** Instantiate mexpr to concrete syntax *)

Section Inst.

  Context {sig : signature} {T : Type} {CS : ConcreteSyntax sig T}.

  Context (ι : mvar → T).

  (* TODO scope should be a param in mexpr *)

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

End ConcreteJdg.

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

From Utils Require Import Functor.

#[local] Instance Sig_IDecl : IDecl I := λ _ X, X.
#[local] Instance Sig_IJdg : IJdg I := λ _ X, (X * X)%type.
#[local] Instance Sig_FMapDecl : ∀ i : I, FMap (declF i) := λ _, FMapId.
#[local] Instance Sig_FMapJdg : ∀ i : I, FMap (jdgF i) := λ _, FMapProd _ _.
#[local] Instance Sig_FuncDecl : ∀ i : I, Eq1Functor (declF i) := λ _, FId.
#[local] Instance Sig_FuncJdg : ∀ i : I, Eq1Functor (jdgF i) := λ _, Eq1FProd _ _.
#[local] Instance Sig_IMakeJdg : IMakeJdg I := λ _ X d x, (x, d).
#[local] Instance Sig_NatMake : ∀ i : I, NatFromProd (make_jdg i).
Proof. intro i. constructor. reflexivity. Qed.

Definition Pf (Γ : list term) (j : term * term) : Prop :=
  proof (jsig := to_jdg_sig SK_desc) tt (map reify Γ) (reify (fst j), reify (snd j)).

Lemma reify_rename r t :
  reify (rename r t) = ParamSyntax.rename r (reify t).
Proof.
  induction t in r |- *.
  all: cbn. all: try reflexivity.
  all: congruence.
Qed.

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

Lemma cinctx_inctx Γ n A :
  cinctx (crename rshift) Γ n A →
  @inctx sign (declF tt) _ (map reify Γ) n (reify A).
Proof.
  induction 1 as [d Γ | d d' Γ n h ih].
  - cbn. eapply conv_in_d. 1: econstructor.
    rewrite reify_rename. reflexivity.
  - cbn. eapply conv_in_d. 1:{ econstructor. eassumption. }
    rewrite reify_rename. reflexivity.
Qed.

Definition to_menv l : menv :=
  λ k _, nth k (map reify l) (E_var 0).

Lemma typing_sound Γ t A :
  typing Γ t A →
  Pf Γ (t, A).
Proof.
  unfold Pf. induction 1. all: cbn.
  - eapply conv_proof_j.
    + eapply tvar. eapply cinctx_inctx. eassumption.
    + reflexivity.
  - eapply conv_proof_j.
    + eapply step with (r := to_rule r_K) (m := to_menv [ A ; B ]) (x := tt).
      * cbn. auto.
      * cbn. contradiction.
      * cbn. contradiction.
    + cbn. rewrite !subst_nil_id. reflexivity.
  - eapply conv_proof_j.
    + eapply step with (r := to_rule r_S) (m := to_menv [ A ; B ; C ]) (x := tt).
      * cbn. auto.
      * cbn. contradiction.
      * cbn. contradiction.
    + cbn. rewrite !subst_nil_id. reflexivity.
  - eapply conv_proof_j.
    + eapply step with (r := to_rule r_app) (m := to_menv [ A ; B ; t ; u ]) (x := tt).
      * cbn. auto.
      * cbn. intros i' n Δ j conv hp.
        destruct hp as [ hp | [ hp | [] ] ].
        all: noconf hp.
        all: cbn; rewrite !subst_nil_id, map_id.
        all: assumption.
      * cbn. intros P hp.
        destruct hp as [ hp | [ hp | [] ] ].
        all: discriminate hp.
    + cbn. rewrite !subst_nil_id. reflexivity.
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
    all: cbn. all: rewrite !subst_nil_id.
    1,2: econstructor.
    cbn in ihind.
    pose proof (ihind tt 0 mnil _ (λ X x, x) (or_introl eq_refl)) as h1.
    pose proof (ihind tt 0 mnil _ (λ X x, x) (or_intror (or_introl eq_refl))) as h2.
    cbn in h1, h2.
    rewrite !subst_nil_id in h1. rewrite !subst_nil_id in h2.
    rewrite map_id in h1, h2.
    econstructor ; eassumption.
  - cbn. econstructor.
    apply inctx_cinctx.
    assumption.
Qed.

Check preserve_subst.
