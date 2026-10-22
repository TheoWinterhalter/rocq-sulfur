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

  Definition hterm := mexpr Kt 0.

  (* Meta-variable [k], arity [0] *)
  Definition hmvar (k : mvar) := M_mvar 0 k [].

  Fixpoint harg (a : arg_ty) :=
    match a with
    | AT_base b => eval_base b
    | AT_term => hterm
    | AT_bind a => harg a
    end.

  Fixpoint curry (l : list arg_ty) :=
    match l with
    | [] => hterm
    | a :: l => harg a → curry l
    end.

  #[refine]
  Fixpoint harg_inst (a : arg_ty) : harg a → mexpr (Ka a) 0 :=
    match a with
    | AT_base b => λ x, M_abase _ _ x
    | AT_term => λ t, M_aterm _ t
    | AT_bind a => λ x, M_abind _ _ (* λ x, M_abind _ (harg_inst a x) *)
    end.
  Proof.
  Admitted.

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

(** Test on combinatory logic *)

Sulfur Syntax {{
  term : Type

  K : term
  S : term
  arrow : term -> term -> term
  app : term -> term -> term
}}.

(* Exports the signature for combinatory calculus *)
Existing Instance sign.

Definition hK := hctor CK.
Definition hS := hctor CS.
Definition harrow := hctor Carrow.
Definition happ := hctor Capp.

Definition SK_desc : jdg_desc := [
  hrule "type_K" 2 (λ A B, []) (λ A B, (hK, harrow A (harrow B A))) ;
  hrule "type_S" 3
    (λ A B C, [])
    (λ A B C, (hS, harrow (harrow A (harrow B C)) (harrow (harrow A B) (harrow A C)))) ;
  hrule "ty_app" 4 (λ A B t u, [(t, harrow A B); (u, A)]) (λ A B t u, (happ t u, B))
].

Eval cbv in SK_desc.

Check preserve_subst.
