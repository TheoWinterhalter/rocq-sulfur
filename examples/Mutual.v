(** Testing mutual judgments *)

From Stdlib Require Import Utf8.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Sulfur Require Import ConcreteSyntax JdgDesc.

Sulfur Syntax tm :=
| tTy : nat → tm
| tPi : tm → (tm → tm) → tm
| tlam : tm → (tm → tm) → tm
| tapp : tm → tm → tm
| tax : tm → tm.

Existing Instance sign.

Sulfur Judgment j1 : tm → tm → Prop
  with context Γ of tm
  and variable x A ↦ j1 x A
:=
| from2 t A :
  j2 t t A
  ────────
  j1 t A

| ax1 t A (i : nat) :
  j1 A (tTy i) ;
  {{ Γ = [] }}
  ──────────────
  j1 t A

with j2 : tm → tm → tm → Prop
  with context Δ of tm
  and variable x A ↦ j2 x x A
:=
| from1 t A :
  j1 t A ;
  {{ List.length Δ = 1 }}
  ──────────────────
  j2 t t A.
