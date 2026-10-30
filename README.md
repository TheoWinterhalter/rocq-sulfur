# Sulfur: Substitution Logical Framework Using Reflection

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="img/sulfur-logo-dark.svg">
  <img alt="Sulfur" src="img/sulfur-logo.svg" width="300">
</picture>

Sulfur is a plugin for Rocq which lets you generate syntaxes with binders,
generating renaming and substitution lemmas automatically.
It also provides a `ssimpl` tactic for simplifying expressions featuring
renamings and substitutions.

`ssimpl` is a *proof-by-reflection* tactic, so it is quite fast.
The whole spirit of Sulfur is to derive properties once and for all by devising
a notion of signature for syntaxes and proving theorems about them generically.
The plugin the generates syntaxes as inductive types that are more palatable to
humans, and formally connect with the corresponding signature to leverage the
generic theorems.

## Usage

One can generate a syntax from a Rocq file using the following commands.

```rocq
From Sulfur Require Import All.

Sulfur Syntax
{{
  term : Type

  Ty : {{nat}} → term
  Pi : term → (bind term in term) → term
  lam : (bind term in term) → term
  app : term → term → term
}}.
```

Here we generate a syntax for the λΠ-calculus.

The `{{ _ }}` syntax inside the global `{{ _ }}` lets you include proper Rocq
terms.
`bind` is used to indicate the presence of a binder.

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
[signature] ::= {{ [sort_decl] [ctor_decl]* }} (* There must be exactly one sort declaration. *)

[sort_decl] ::= [ident] : Type              (* Declare a sort. *)
              | [ident] ( [ident] ) : Type  (* Declare a sort, specifying the name of
                                               the variable constructor between parentheses. *)

[ctor_decl] ::= [ident] : [ctor_type]       (* Declare a constructor with the given type. )

[ctor_type] ::= [ident]
              | [arg_typ] → [ctor_type]

[arg_type] ::= [ident]                      (* Just a sort. )
             | ( bind [ident]+ in [ident] ) (* Bind a list of sorts (from left to right) in a sort. *)
             | {{ [constr] }}               (* [constr] is any Rocq term of type [Set], [Prop], or [Type].
                                               Universe polymorphic terms will be instantiated with
                                               new monomorphic (global) universes. *)
```

## Simplification

Sulfur offers a substitution simplification tactic, called `ssimpl` (for
Sulfur simplifier). It works on any expression featuring terms with renamings
or substitutions that can be simplified. It fails otherwise.
