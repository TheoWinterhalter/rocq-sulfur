(** Combinatory logic *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Sulfur Require Import ConcreteSyntax JdgDesc.

Sulfur Syntax term : Type :=
| tK : term
| tS : term
| tarr : term → term → term
| tapp : term → term → term.

Existing Instance sign.

Sulfur Judgment typing : term → term → Prop
  with context Γ of term
  and variable x A ↦ typing x A :=
| type_K (A B : term) :
    ⟹ typing tK (tarr A (tarr B A))
| type_S (A B C : term) :
    ⟹ typing tS (tarr (tarr A (tarr B C)) (tarr (tarr A B) (tarr A C)))
| ty_app (A B t u : term) :
    typing t (tarr A B) ;
    typing u A
    ⟹ typing (tapp t u) B.
