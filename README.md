<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="img/sulfur-logo-dark.svg">
    <img alt="Sulfur" src="img/sulfur-logo.svg" width="340">
  </picture>
</p>

<p align="center">
  <b>Su</b>bstitution <b>L</b>ogical <b>F</b>ramework <b>U</b>sing <b>R</b>eflection
</p>

Sulfur is a plugin for Rocq which lets you generate syntaxes with binders,
generating renaming and substitution lemmas automatically.
It also provides a `ssimpl` tactic for simplifying expressions featuring
renamings and substitutions.

`ssimpl` is a *proof-by-reflection* tactic, so it is quite fast.
The whole spirit of Sulfur is to derive properties once and for all by devising
a notion of signature for syntaxes and proving theorems about them generically.
The plugin then generates syntaxes as inductive types that are more palatable to
humans, and formally connect with the corresponding signature to leverage the
generic theorems.

## Usage

### Syntax

One can generate a syntax from a Rocq file using the following command which
mimics an inductive type declaration.

```rocq
From Sulfur Require Import All.

Sulfur Syntax tm :=
| tTy : nat → tm
| tPi : tm → (tm → tm) → tm
| tlam : tm → (tm → tm) → tm
| tapp : tm → tm → tm.
```

Here we generate a syntax for the λΠ-calculus using higher-order abstract
syntax (HOAS) so `(term -> term)` indicates a `term` where another `term` is
bound.
This builds on Rocq's parser and elaborator, so one can use notations and
existing types such as `nat` above.

### Judgments

One can generate judgments from Sulfur as well.
Currently, one can do the following.

```rocq
Sulfur Judgment conv : tm → tm → Prop
  with Γ : unit, Variable x A : conv x x
{{
| beta A (b : tm → tm) u :
    ⟹ conv (tapp (tlam A b) u) (b u)
| congr_lam A A' (b b' : tm → tm) :
    conv A A' ;
    ⟨ x : tt ⊢ conv (b x) (b' x) ⟩
    ⟹ conv (tlam A b) (tlam A' b')
}}.
```

This defines a new inductive type `conv` which quantifies explicitly over a
notion of contexts (here said to be holding `unit` values):
```rocq
conv : list unit → tm → tm → Prop
```

The `Variable` bit tells Sulfur how to generate the variable rule (as well
as the substitution judgment):
```rocq
conv_var : ∀ (Γ : list unit) (n : nat) (d : unit),
  cinctx (λ x : unit, x) Γ n d →
  conv Γ (var n) (var n)
```

This also generates a substitution lemma for free:
```rocq
conv_subst :
  ∀ (Γ Δ : list unit) (σ : nat → tm) (x x0 : tm),
    conv Γ x x0 →
    cstyping conv Δ σ Γ →
    conv Δ (substitute σ x) (substitute σ x0)
```

New judgments can refer to older judgments (they don't even have to be generated
by Sulfur).

```rocq
Sulfur Judgment typing : tm → tm → Prop
  with Γ : tm, Variable x A : typing x A
{{
(* other rules ommited *)

| type_conv A A' t :
    typing t A ;
    {{ conv (map (λ _, tt) Γ) A A' }}
    ⟹ typing t A'
}}.
```

This will generate obligations that can be discharged with:
```rocq
Instance: typing_obligations.
```

This instance will be picked up by `typing_subst`.

## Install

Sulfur is available on `opam` for Rocq 9.3.
You need to have `rocq-released` available in your `opam`.

Then you can simply install with:
```
opam install rocq-sulfur
```

## Build from sources

Create a local opam switch with the required packages:
```
opam switch create . 4.14.2 --repos=default,rocq-released='https://rocq-prover.org/opam/released' -y
```

Optionally install development packages, e.g. for VS Code:
```
opam install ocaml-lsp-server user-setup ocamlformat vsrocq-language-server
opam user-setup install
```

Build and install with:
```
dune build && dune install
```

## Simplification

Sulfur offers a substitution simplification tactic, called `ssimpl` (for
Sulfur simplifier). It works on any expression featuring terms with renamings
or substitutions that can be simplified. It fails otherwise.
