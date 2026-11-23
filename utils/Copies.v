(** Copies of functions from the standard library

  The point is to be able to simplify expressons in the plugin a bit agressively
  without worrying about user input: they will use List.map and the plugin
  will use its copy from here.

*)

From Stdlib Require Import Utf8 Bool List.
Import ListNotations.

Section Lists.

  Context [A B : Type].
  Context (f : A → B).

  Fixpoint lmap (l : list A) : list B :=
    match l with
    | [] => []
    | x :: l => f x :: lmap l
    end.

  Fixpoint llength (l : list A) : nat :=
    match l with
    | [] => 0
    | _ :: l => S (llength l)
    end.

End Lists.

Lemma lmap_map :
  lmap = map.
Proof.
  reflexivity.
Qed.

Lemma llength_length :
  llength = List.length.
Proof.
  reflexivity.
Qed.
