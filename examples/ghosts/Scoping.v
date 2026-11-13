(** Scoping

  Stating that all variables are in a given scope, and in a given mode.

**)

From Stdlib Require Import Utf8 List.
From SulfurGhostExample
Require Import GAST SubstNotations ContextDecl CastRemoval.

Import ListNotations.

Set Default Goal Selector "!".

Sulfur Judgment scoping : term → mode → Prop
  with context Γ of mode
  and variable x m ↦ scoping x m :=
| scope_sort (m : mode) (i : level) :
    ─────────────────────────────────────
    scoping (Sort m i) mKind

| scope_pi (i j : level) (mx m : mode) A (B : term → term) :
    scoping A mKind ;
    ⟨ x ↦ mx ⊢ scoping (B x) mKind ⟩
    ─────────────────────────────────────
    scoping (Pi i j m mx A B) mKind

| scope_lam (mx m : mode) A (t : term → term) :
    scoping A mKind ;
    ⟨ x ↦ mx ⊢ scoping (t x) m ⟩
    ─────────────────────────────────────
    scoping (lam mx A t) m

| scope_app (mx m : mode) t u :
    scoping t m ;
    scoping u mx
    ─────────────────────────────────────
    scoping (app t u) m

| scope_erased A :
    scoping A mKind
    ─────────────────────────────────────
    scoping (Erased A) mKind

| scope_hide t :
    scoping t mType
    ─────────────────────────────────────
    scoping (hide t) mGhost

| scope_reveal (m : mode) t P p :
    {{ In m [ mProp ; mGhost ] }} ;
    scoping t mGhost ;
    scoping P mKind ;
    scoping p m
    ─────────────────────────────────────
    scoping (reveal t P p) m

| scope_Reveal t p :
    scoping t mGhost ;
    scoping p mKind
    ─────────────────────────────────────
    scoping (Reveal t p) mKind

| scope_toRev t p u :
    scoping t mType ;
    scoping p mKind ;
    scoping u mProp
    ─────────────────────────────────────
    scoping (toRev t p u) mProp

| scope_fromRev t p u :
    scoping t mType ;
    scoping p mKind ;
    scoping u mProp
    ─────────────────────────────────────
    scoping (fromRev t p u) mProp

| scope_gheq A u v :
    scoping A mKind ;
    scoping u mGhost ;
    scoping v mGhost
    ─────────────────────────────────────
    scoping (gheq A u v) mKind

| scope_ghrefl A u :
    scoping A mKind ;
    scoping u mGhost
    ─────────────────────────────────────
    scoping (ghrefl A u) mProp

| scope_ghcast (m : mode) A u v e P t :
    {{ m ≠ mKind }} ;
    scoping A mKind ;
    scoping u mGhost ;
    scoping v mGhost ;
    scoping e mProp ;
    scoping P mKind ;
    scoping t m
    ─────────────────────────────────────
    scoping (ghcast A u v e P t) m

| scope_bool :
    ─────────────────────────────────────
    scoping tbool mKind

| scope_true :
    ─────────────────────────────────────
    scoping ttrue mType

| scope_false :
    ─────────────────────────────────────
    scoping tfalse mType

| scope_if (m : mode) b P t f :
    scoping b mType ;
    scoping P mKind ;
    scoping t m ;
    scoping f m
    ─────────────────────────────────────
    scoping (tif m b P t f) m

| scope_nat :
    ─────────────────────────────────────
    scoping tnat mKind

| scope_zero :
    ─────────────────────────────────────
    scoping tzero mType

| scope_succ n :
    scoping n mType
    ─────────────────────────────────────
    scoping (tsucc n) mType

| scope_nat_elim (m : mode) n P z s :
    {{ m ≠ mKind }} ;
    scoping n mType ;
    scoping P mKind ;
    scoping z m ;
    scoping s m
    ─────────────────────────────────────
    scoping (tnat_elim m n P z s) m

| scope_vec A n :
    scoping A mKind ;
    scoping n mGhost
    ─────────────────────────────────────
    scoping (tvec A n) mKind

| scope_vnil A :
    scoping A mKind
    ─────────────────────────────────────
    scoping (tvnil A) mType

| scope_vcons a n v :
    scoping a mType ;
    scoping n mGhost ;
    scoping v mType
    ─────────────────────────────────────
    scoping (tvcons a n v) mType

| scope_vec_elim (m : mode) A n v P z s :
    {{ m ≠ mKind }} ;
    scoping A mKind ;
    scoping n mGhost ;
    scoping v mType ;
    scoping P mKind ;
    scoping z m ;
    scoping s m
    ─────────────────────────────────────
    scoping (tvec_elim m A n v P z s) m

| scope_bot :
    ─────────────────────────────────────
    scoping bot mKind

| scope_bot_elim (m : mode) A p :
    scoping A mKind ;
    scoping p mProp
    ─────────────────────────────────────
    scoping (bot_elim m A p) m.

Abbreviation cscoping Γ := (scoping (sc Γ)).

Create HintDb gtt_scope discriminated.

Hint Constructors scoping : gtt_scope.

Ltac gscope :=
  unshelve typeclasses eauto with gtt_scope shelvedb ; shelve_unifiable.

Instance: scoping_obligations.
Proof.
  red. intuition auto.
Qed.
