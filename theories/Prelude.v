From Stdlib Require Export Bool Nat List String Morphisms Relations Program.Equality Lia.
From Stdlib Require Import Utf8.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
From Utils Require Export Fin Vector Functor Generalities.
Export ListNotations VectorNotations.
Require Export Stdlib.Logic.ProofIrrelevance.


#[export] Set Equations Transparent.

(** Just to make sure. *)
#[export] Unset Equations With UIP.

(** Ltac2 is still missing many basic Ltac1 tactics,
    so we use Ltac1 for proofs. *)
#[export] Set Default Proof Mode "Classic".

(** Coercion to view booleans as propositions. *)
Coercion is_true : bool >-> Sortclass.

(*********************************************************************************)
(** *** Convenience tactics. *)
(*********************************************************************************)

(** Split n-ary conjunctions. *)
Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].

(** Destruct n-ary disjunctions.  *)
Ltac destruct_n H :=
simpl in H;
match type of H with
| False => destruct H
| or _ _ => destruct H as [H|H]; [destruct_n H|destruct_n H]
| _ => idtac
end.

(** On a hypothesis of the form [H : A -> B], this generates two goals:
    - the first asks to prove [A].
    - the second asks to prove the original goal in a context where [H : A]. *)
Ltac feed H :=
  match type of H with
  | ?A -> ?B =>
    let HA := fresh "H" in
    assert (HA : A) ; [| specialize (H HA)]
  end.

Ltac feed2 H := feed H ; [| feed H].
Ltac feed3 H := feed H ; [| feed2 H].
Ltac feed4 H := feed H ; [| feed3 H].


Create Rewrite HintDb red.
Create Rewrite HintDb seval.
Create Rewrite HintDb ssimpl_topdown.
Create Rewrite HintDb ssimpl_outermost.
Create Rewrite HintDb ssimpl_unfold.

(** Decidable equality for enumerable types *)

Class Enum (A : Type) := {
  to_nat : A → nat ;
  of_nat : nat → option A ;
  is_enum : ∀ x, of_nat (to_nat x) = Some x
}.

#[export] Instance enum_eqdec {A} `{Enum A} : EqDec A.
Proof.
  intros x y.
  destruct (nat_eqdec (to_nat x) (to_nat y)) as [e|ne].
  - left. apply (f_equal of_nat) in e. rewrite 2!is_enum in e. noconf e.
    reflexivity.
  - right. intros <-. apply ne. reflexivity.
Qed.
