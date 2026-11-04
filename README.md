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

One can generate a syntax from a Rocq file using the following commands.

```rocq
From Sulfur Require Import All.

Sulfur Syntax {{
  tm : Type

  | tTy : nat → tm
  | tPi : tm → (tm → tm) → tm
  | tlam : tm → (tm → tm) → tm
  | tapp : tm → tm → tm
}}.
```

Here we generate a syntax for the λΠ-calculus using higher-order abstract
syntax (HOAS) so `(term -> term)` indicates a `term` where another `term` is
bound.
This builds on Rocq's parser and elaborator, so one can use notations and
existing types such as `nat` above.

### Judgments

One can generate judgments from Sulfur as well.
The syntax is work-in-progress. Currently one can do the following.

```rocq
Sulfur Judgment conv {{
| beta A (b : tm → tm) u :
    ⟹ conv (tapp (tlam A b) u) (b u)
| congr_lam A A' (b b' : tm → tm) :
    conv A A' ;
    ⟨ x : A ⊢ conv (b x) (b' x) ⟩
    ⟹ conv (tlam A b) (tlam A' b')
}}.
```

This defines a new inductive type `conv` which quantifies explicitly over a
notion of contexts:
```rocq
conv : list tm → tm → tm → Prop
```

This also generates a substitution lemma for free:
```rocq
conv_subst :
  ∀ (Γ Δ : list tm) (σ : nat → tm) (t A : tm),
    conv Γ t A →
    cstyping conv Δ σ Γ →
    conv Δ (substitute σ t) (substitute σ A)
```

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

## Signatures

Here is the grammar of signatures. Non-terminals are surrounded with square brackets,
and [ident] stands for valid Rocq identifiers.

```
[signature] ::= {{ [decl] ( | [decl] )* }}  (* The first declaration is the sort. *)

[decl] ::= [ident] : Type                (* Declare the sort. *)
         | [ident] ( [ident] ) : Type    (* Declare the sort, specifying the name of
                                            the variable constructor between parentheses
                                            ([var] by default). *)
         | [ident] : [constr]            (* Declare a constructor with the given type,
                                            [constr] being any Rocq type of the form
                                            [arg] -> ... -> [arg] -> [sort]. *)

[arg] ::= [sort]                         (* A term. *)
        | [sort] -> ... -> [sort] -> [arg] (* Bind that many variables in an argument. *)
        | [constr]                       (* Any other Rocq type: a base type. Universe
                                            polymorphic types are instantiated with new
                                            monomorphic (global) universes. *)
```

## Simplification

Sulfur offers a substitution simplification tactic, called `ssimpl` (for
Sulfur simplifier). It works on any expression featuring terms with renamings
or substitutions that can be simplified. It fails otherwise.
