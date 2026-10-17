(** Utility for the OCaml generation *)

From Stdlib Require Import Utf8 Lia.
From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require ParamSyntax.

(** Decidable equality for enumerable types *)

Section Enum.

  Context (A : Type).
  Context (to_nat : A → nat).
  Context (of_nat : nat → option A).

  Definition is_enum :=
    ∀ x, of_nat (to_nat x) = Some x.

  Context (h : is_enum).

  Lemma enum_eqdec : EqDec A.
  Proof.
    intros x y.
    destruct (nat_eqdec (to_nat x) (to_nat y)) as [e|ne].
    - left. apply (f_equal of_nat) in e. rewrite 2!h in e. noconf e.
      reflexivity.
    - right. intros <-. apply ne. reflexivity.
  Qed.

End Enum.

(** Helper to build the [of_nat] function from a list of constructors. *)

Definition enum_of_nat {A} (l : list A) : nat → option A :=
  nth_error l.

(**
  Proves goals of the form is_enum _ to_nat (enum_of_nat l)
  where to_nat is sending constructor i to i and l is the list of constructors.
*)
Ltac sulfur_is_enum :=
  hnf ;
  let x := fresh "x" in
  intro x ; destruct x ; reflexivity.
