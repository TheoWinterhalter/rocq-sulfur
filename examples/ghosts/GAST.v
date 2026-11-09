From Stdlib Require Import Utf8.
From Sulfur Require Export All JdgDesc.

Definition level := nat.

Inductive mode := mKind | mType | mGhost | mProp.

Inductive mark := Any | WasKind | WasType | WasGhost.

Time Sulfur Syntax term(Var) :=
| Sort : mode -> level -> term

| Pi : level -> level -> mode -> mode -> term -> (term -> term) -> term
| lam : mode -> term -> (term -> term) -> term
| app : term -> term -> term

| Erased : term -> term
| hide : term -> term
| reveal : term -> term -> term -> term
| Reveal : term -> term -> term
| toRev : term -> term -> term -> term
| fromRev : term -> term -> term -> term

| gheq : term -> term -> term -> term
| ghrefl : term -> term -> term
| ghcast : term -> term -> term -> term -> term -> term -> term

| tbool : term
| ttrue : term
| tfalse : term
| tif : mode -> term -> term -> term -> term -> term

| tnat : term
| tzero : term
| tsucc : term -> term
| tnat_elim : mode -> term -> term -> term -> term -> term

| tvec : term -> term -> term
| tvnil : term -> term
| tvcons : term -> term -> term -> term
| tvec_elim : mode -> term -> term -> term -> term -> term -> term -> term

| bot : term
| bot_elim : mode -> term -> term -> term.

Existing Instance sign.

(* FIXME (should be automatic) *)
Ltac2 Set sunfold_list as old :=
  fun () => List.append (constants up_ren, up_subst) (old ()).

From Ltac2 Require Import Rewrite.

Ltac2 Set ssimpl_matches :=
  fun () =>
    Strategy.choice
      (Strategy.matches pat:(rename _ _))
      (Strategy.matches pat:(substitute _ _)).
