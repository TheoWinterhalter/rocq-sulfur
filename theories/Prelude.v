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

Definition enum_all_in A (l : list A) i :=
  ∀ a, nth_error l (i a) = Some a.

Class Enum (A : Type) := mkenum {
  enum : list A ;
  index_of : A → nat ;
  enum_all : enum_all_in A enum index_of
}.

#[export] Instance enum_eqdec {A} `{Enum A} : EqDec A.
Proof.
  intros x y.
  destruct (nat_eqdec (index_of x) (index_of y)) as [e|ne].
  - left. apply (f_equal (nth_error enum)) in e.
    rewrite 2!enum_all in e. noconf e.
    reflexivity.
  - right. intros <-. apply ne. reflexivity.
Qed.

(** Prove goals of the form [enum_all_in] *)
Ltac sulfur_is_enum :=
  intros [] ; reflexivity.
