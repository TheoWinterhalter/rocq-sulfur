From Stdlib Require Export Morphisms Relations.

Definition eq1 {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (eq1 f g) (at level 75).

Definition eq2 {A B C} : relation (A -> B -> C) := pointwise_relation _ (pointwise_relation _ eq).
Notation "f =₂ g" := (eq2 f g) (at level 75).

Fixpoint comp_n {X : Type} (f : X -> X) (n : nat) (x : X) := match n with
| 0 => x
| S n => f (comp_n f n x)
end.