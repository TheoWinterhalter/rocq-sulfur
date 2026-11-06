(** Shapes of judgments and declarations

  Judgments and context declarations are a combination of terms and base values.
  These are recorded in shapes.

  They can be used to build [declF] and [jdgF] functors.

*)

From Stdlib Require Import Utf8 List Bool.
From Utils Require Import Functor Generalities.
Import ListNotations.

Set Default Goal Selector "!".

(** Shapes as tuples of terms and base types *)


Inductive type :=
| t_term
| t_base (B : Type).

Abbreviation shape := (list type).

(* Order is there to make a functor over [Type] *)
Definition El (t : type) tm : Type :=
  match t with
  | t_term => tm
  | t_base B => B
  end.

Fixpoint tuple1 (t : type) (sh : shape) tm : Type :=
  match sh with
  | [] => El t tm
  | u :: sh => El t tm * tuple1 u sh tm
  end.

(* The argument [tm] is at the end for the [FMap] class *)
Definition tuple (sh : shape) tm : Type :=
  match sh with
  | [] => unit
  | t :: sh => tuple1 t sh tm
  end.

Definition Elmap {X Y} t (f : X → Y) : El t X → El t Y :=
  match t with
  | t_term => f
  | t_base B => id
  end.

Fixpoint tuple1_map {X Y} t sh (f : X → Y) : tuple1 t sh X → tuple1 t sh Y :=
  match sh with
  | [] => Elmap t f
  | u :: sh => λ '(x,xs), (Elmap t f x, tuple1_map u sh f xs)
  end.

Definition tuple_map {X Y} sh (f : X → Y) : tuple sh X → tuple sh Y :=
  match sh with
  | [] => id
  | t :: sh => tuple1_map t sh f
  end.

#[export]
Instance FMap_tuple sh : FMap (tuple sh) :=
  λ X Y, tuple_map sh.

Lemma Elmap_id t X (x : El t X) :
  Elmap t (λ x, x) x = x.
Proof.
  destruct t. all: reflexivity.
Qed.

Lemma Elmap_comp a X Y Z (f : X → Y) (g : Y → Z) (x : El a X) :
  Elmap a g (Elmap a f x) = Elmap a (λ x, g (f x)) x.
Proof.
  destruct a. all: reflexivity.
Qed.

Lemma Elmap_ext a X Y (f g : X → Y) (x : El a X) :
  f =₁ g →
  Elmap a f x = Elmap a g x.
Proof.
  destruct a. all: cbn. all: auto.
Qed.

Lemma tuple1_map_id a l X (x : tuple1 a l X) :
  tuple1_map a l (λ x, x) x = x.
Proof.
  induction l as [| b l ih] in a, x |- *. all: cbn.
  - apply Elmap_id.
  - destruct x as [x xs]. rewrite Elmap_id, ih. reflexivity.
Qed.

Lemma tuple1_map_comp a l X Y Z (f : X → Y) (g : Y → Z) (x : tuple1 a l X) :
  tuple1_map a l g (tuple1_map a l f x) = tuple1_map a l (λ x, g (f x)) x.
Proof.
  induction l as [| b l ih] in a, x |- *. all: cbn.
  - apply Elmap_comp.
  - destruct x as [x xs]. rewrite Elmap_comp, ih. reflexivity.
Qed.

Lemma tuple1_map_ext a l X Y (f g : X → Y) (x : tuple1 a l X) :
  f =₁ g →
  tuple1_map a l f x = tuple1_map a l g x.
Proof.
  intro h. induction l as [| b l ih] in a, x |- *. all: cbn.
  - apply Elmap_ext. assumption.
  - destruct x as [x xs]. rewrite ih. erewrite Elmap_ext. all: eauto.
Qed.

Lemma tuple_map_id sh X (x : tuple sh X) :
  tuple_map sh (λ x, x) x = x.
Proof.
  destruct sh.
  - reflexivity.
  - apply tuple1_map_id.
Qed.

Lemma tuple_map_comp sh X Y Z (f : X → Y) (g : Y → Z) (x : tuple sh X) :
  tuple_map sh g (tuple_map sh f x) = tuple_map sh (λ x, g (f x)) x.
Proof.
  destruct sh.
  - reflexivity.
  - apply tuple1_map_comp.
Qed.

Lemma tuple_map_ext sh X Y (f g : X → Y) (x : tuple sh X) :
  f =₁ g →
  tuple_map sh f x = tuple_map sh g x.
Proof.
  intro h. destruct sh.
  - reflexivity.
  - apply tuple1_map_ext. assumption.
Qed.

Lemma tuple_map_comp_ext sh X Y Z (f : X → Y) (g : Y → Z) (h : X → Z)
  (x : tuple sh X) :
  (∀ x, g (f x) = h x) →
  tuple_map sh g (tuple_map sh f x) = tuple_map sh h x.
Proof.
  intro e. rewrite tuple_map_comp. apply tuple_map_ext. exact e.
Qed.

#[export]
Instance Functor_tuple sh : Functor (tuple sh).
Proof.
  constructor.
  - intros X x. apply tuple_map_id.
  - intros X Y Z f g x. apply tuple_map_comp.
Qed.

#[export]
Instance Eq1Functor_tuple sh : Eq1Functor (tuple sh).
Proof.
  constructor.
  - apply Functor_tuple.
  - intros X Y f g h x. apply tuple_map_ext. assumption.
Defined.

(** A Boolean predicate holds on all members of a tuple *)

Definition onEl {t X} (p : X → bool) : El t X → bool :=
  match t with
  | t_term => p
  | t_base _ => λ _, true
  end.

Fixpoint tuple1_allb (a : type) (sh : shape) {X} (p : X → bool) :
  tuple1 a sh X → bool :=
  match sh with
  | [] => onEl p
  | b :: sh => λ '(x, xs), onEl p x && tuple1_allb b sh p xs
  end.

Definition tuple_allb (sh : shape) {X} (p : X → bool) : tuple sh X → bool :=
  match sh with
  | [] => λ _, true
  | a :: sh => tuple1_allb a sh p
  end.

Lemma Elmap_ext_all a X Y (p : X → bool) (f g : X → Y) (x : El a X) :
  (∀ x, p x = true → f x = g x) →
  onEl p x = true →
  Elmap a f x = Elmap a g x.
Proof.
  destruct a. all: cbn. all: auto.
Qed.

Lemma tuple1_map_ext_all a sh X Y (p : X → bool) (f g : X → Y)
  (x : tuple1 a sh X) :
  (∀ x, p x = true → f x = g x) →
  tuple1_allb a sh p x = true →
  tuple1_map a sh f x = tuple1_map a sh g x.
Proof.
  intros h. induction sh as [| b sh ih] in a, x |- *. all: cbn.
  - destruct a. all: cbn. all: auto.
  - destruct x as [x xs]. intro e.
    rewrite andb_true_iff in e. destruct e as [hx hxs].
    erewrite Elmap_ext_all with (p := p). 2,3: eassumption.
    rewrite ih. 2: assumption.
    reflexivity.
Qed.

Lemma tuple_map_ext_all sh X Y (p : X → bool) (f g : X → Y) (x : tuple sh X) :
  (∀ x, p x = true → f x = g x) →
  tuple_allb sh p x = true →
  tuple_map sh f x = tuple_map sh g x.
Proof.
  intros h e. destruct sh. all: cbn.
  - reflexivity.
  - eapply tuple1_map_ext_all. all: eassumption.
Qed.
