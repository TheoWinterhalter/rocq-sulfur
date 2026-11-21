(** Copies of functions from the standard library

  The point is to be able to simplify expressons in the plugin a bit agressively
  without worrying about user input: they will use List.map and the plugin
  will use its copy from here.

*)

From Stdlib Require Import Utf8 Bool List.
Import ListNotations.

(** Copy of List.map *)
Fixpoint lmap {A B} (f : A → B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l => f x :: lmap f l
  end.

Lemma lmap_map {A B} (f : A → B) l :
  lmap f l = map f l.
Proof.
  induction l as [| x l ih]. 1: reflexivity.
  cbn. f_equal. assumption.
Qed.
