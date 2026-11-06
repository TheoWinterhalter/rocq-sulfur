From Stdlib Require Import Utf8 List.
From SulfurExamples Require Import GAST.

Set Primitive Projections.

(** Contexts store for each variable its type and mode.

  The mode is redundant information already contained in the type, but we only
  establish that later. Storing this information is useful to perform syntactic
  transformations: typically conversion and the syntactic model.

**)

Abbreviation decl := (mode * term)%type.

Abbreviation context := (list decl).

Abbreviation scope := (list mode).

Definition sc (Γ : context) : scope :=
  map fst Γ.

Notation "'∙'" :=
  (@nil decl).

Notation "Γ ,, d" :=
  (@cons decl d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@app decl Δ Γ) (at level 25, Δ at next level, left associativity).
