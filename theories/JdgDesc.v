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
    cctor : ∀ c, cargs (ctor_type c) → T
  }.

End ConcreteSyntax.

Arguments carg {sig}.
Arguments cargs {sig}.
Arguments ckind {sig}.

Arguments cvar {sig T _}.
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

  #[refine]
  Definition rule_desc_type (rd : rule_desc) (Γ : list T) : Prop :=
    (* TODO something for the premise *)
    conc_jdg Γ _ rd.(rd_conclusion).
  Proof.
  Admitted.

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

Definition SK_desc : jdg_desc := [
  hrule "type_K" 2 (λ A B, []) (λ A B, (hK, harrow A (harrow B A))) ;
  hrule "type_S" 3
    (λ A B C, [])
    (λ A B C, (hS, harrow (harrow A (harrow B C)) (harrow (harrow A B) (harrow A C)))) ;
  hrule "ty_app" 4 (λ A B t u, [(t, harrow A B); (u, A)]) (λ A B t u, (happ t u, B))
].

Arguments SK_desc /.
Eval cbn in SK_desc.

(* Actual implementation we want to reach *)

Inductive cinctx {T} (sh : T → T) : list T → nat → T → Prop :=
| cin_head d Γ : cinctx sh (d :: Γ) 0 (sh d)
| cin_tail d d' Γ n : cinctx sh Γ n d → cinctx sh (d' :: Γ) (S n) (sh d).

Definition inctx := @cinctx term (rename rshift).

Inductive typing Γ : term → term → Prop :=
| ty_var n A :
  inctx Γ n A →
  typing Γ (Var n) A

| ty_K A B :
  typing Γ tK (tarr A (tarr B A))

| ty_S A B C :
  typing Γ tS (tarr (tarr A (tarr B C)) (tarr (tarr A B) (tarr A C)))

| ty_app A B t u :
  typing Γ t (tarr A B) → typing Γ u A → typing Γ (tapp t u) B.

Check preserve_subst.
