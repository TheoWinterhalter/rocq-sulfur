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

Definition tuple_allb {sh : shape} {X} (p : X → bool) : tuple sh X → bool :=
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
  tuple_allb p x = true →
  tuple_map sh f x = tuple_map sh g x.
Proof.
  intros h e. destruct sh. all: cbn.
  - reflexivity.
  - eapply tuple1_map_ext_all. all: eassumption.
Qed.

(** Curried functions over tuples *)

Section Curried.

  Context {X : Type}.

  Fixpoint cfun1 (a : type) (sh : shape) (R : Type) : Type :=
    match sh with
    | [] => El a X → R
    | b :: sh => El a X → cfun1 b sh R
    end.

  Definition cfun (sh : shape) (R : Type) : Type :=
    match sh with
    | [] => R
    | a :: sh => cfun1 a sh R
    end.

  Fixpoint capply1 {R} a sh : cfun1 a sh R → tuple1 a sh X → R :=
    match sh with
    | [] => λ f x, f x
    | b :: sh => λ f '(x, xs), capply1 b sh (f x) xs
    end.

  Definition capply {R sh} : cfun sh R → tuple sh X → R :=
    match sh with
    | [] => λ r _, r
    | a :: sh => capply1 a sh
    end.

  Fixpoint curry1 {R} a sh : (tuple1 a sh X → R) → cfun1 a sh R :=
    match sh with
    | [] => λ f x, f x
    | b :: sh => λ f x, curry1 b sh (λ xs, f (x, xs))
    end.

  Definition curry {R sh} : (tuple sh X → R) → cfun sh R :=
    match sh with
    | [] => λ f, f tt
    | a :: sh => curry1 a sh
    end.

  Lemma capply1_curry1 {R} a sh (f : tuple1 a sh X → R) x :
    capply1 a sh (curry1 a sh f) x = f x.
  Proof.
    induction sh as [| b sh ih] in a, f, x |- *.
    - reflexivity.
    - cbn in *. destruct x as [x xs]. apply ih.
  Qed.

  Lemma capply_curry {R} sh (f : tuple sh X → R) x :
    capply (curry f) x = f x.
  Proof.
    destruct sh.
    - destruct x. reflexivity.
    - cbn. apply capply1_curry1.
  Qed.

  (** [∀ x1 ... xn, K (x1, ..., xn)] *)
  Fixpoint under_tuple1 a sh : (tuple1 a sh X → Prop) → Prop :=
    match sh with
    | [] => λ K, ∀ x, K x
    | b :: sh => λ K, ∀ x, under_tuple1 b sh (λ xs, K (x, xs))
    end.

  Definition under_tuple {sh} : (tuple sh X → Prop) → Prop :=
    match sh with
    | [] => λ K, K tt
    | a :: sh => under_tuple1 a sh
    end.

  Lemma under_tuple1_iff a sh K :
    under_tuple1 a sh K ↔ ∀ x, K x.
  Proof.
    induction sh as [| b sh ih] in a, K |- *. all: cbn.
    - reflexivity.
    - split.
      + intros h [x xs]. specialize (h x). rewrite ih in h. apply h.
      + intros h x. apply ih. auto.
  Qed.

  Lemma under_tuple_iff sh K :
    under_tuple (sh := sh) K ↔ ∀ x, K x.
  Proof.
    destruct sh. all: cbn.
    - split.
      + intros h []. exact h.
      + auto.
    - apply under_tuple1_iff.
  Qed.

End Curried.

(** Operations on tuples *)

Definition tcons (a : type) (sh : shape) {X} :
  El a X → tuple sh X → tuple (a :: sh) X :=
  match sh with
  | [] => λ x _, x
  | b :: sh => λ x xs, (x, xs)
  end.

Definition thead (a : type) (sh : shape) {X} : tuple (a :: sh) X → El a X :=
  match sh with
  | [] => λ x, x
  | b :: sh => fst
  end.

Definition ttail (a : type) (sh : shape) {X} :
  tuple (a :: sh) X → tuple sh X :=
  match sh with
  | [] => λ _, tt
  | b :: sh => snd
  end.

Lemma tuple_map_tcons a sh X Y (f : X → Y) (x : El a X) (xs : tuple sh X) :
  tuple_map (a :: sh) f (tcons a sh x xs) =
  tcons a sh (Elmap a f x) (tuple_map sh f xs).
Proof.
  destruct sh. all: reflexivity.
Qed.

Lemma thead_tuple_map a sh X Y (f : X → Y) (d : tuple (a :: sh) X) :
  thead a sh (tuple_map (a :: sh) f d) = Elmap a f (thead a sh d).
Proof.
  destruct sh.
  - reflexivity.
  - cbn in *. destruct d. reflexivity.
Qed.

Lemma ttail_tuple_map a sh X Y (f : X → Y) (d : tuple (a :: sh) X) :
  ttail a sh (tuple_map (a :: sh) f d) = tuple_map sh f (ttail a sh d).
Proof.
  destruct sh.
  - reflexivity.
  - destruct d. reflexivity.
Qed.

(** Positions in a shape, recording the type *)
Inductive pos : shape → type → Type :=
| pos0 {a sh} : pos (a :: sh) a
| posS {a b sh} : pos sh b → pos (a :: sh) b.

Fixpoint tget {sh a} (p : pos sh a) {X} : tuple sh X → El a X :=
  match p in pos sh a return tuple sh X → El a X with
  | @pos0 a sh => thead a sh
  | @posS a b sh p => λ d, tget p (ttail a sh d)
  end.

Lemma tget_tuple_map sh a (p : pos sh a) X Y (f : X → Y) (d : tuple sh X) :
  tget p (tuple_map sh f d) = Elmap a f (tget p d).
Proof.
  induction p as [a sh | a b sh p ih] in d |- *.
  - cbn. apply thead_tuple_map.
  - cbn [tget]. rewrite ttail_tuple_map. apply ih.
Qed.

(** [sel decl jdg] gives a natural map [tuple decl X → X → tuple jdg X]

  It does so by selecting elements from the tuple [decl] and [X] for each
  element of [jdg].

*)

Inductive sel (decl : shape) : shape → Type :=
| sel_nil : sel decl []
| sel_var {jdg} : sel decl jdg → sel decl (t_term :: jdg)
| sel_pos {a jdg} : pos decl a → sel decl jdg → sel decl (a :: jdg).

Fixpoint make {decl jdg} (s : sel decl jdg) {X} (d : tuple decl X) (x : X) :
  tuple jdg X :=
  match s with
  | sel_nil _ => tt
  | @sel_var _ l s => tcons t_term l x (make s d x)
  | @sel_pos _ a l p s => tcons a l (tget p d) (make s d x)
  end.

Arguments sel_nil {decl}.
Arguments sel_var {decl jdg}.
Arguments sel_pos {decl a jdg}.

Lemma make_nat decl jdg (s : sel decl jdg) X Y (f : X → Y) d x :
  tuple_map jdg f (make s d x) = make s (tuple_map decl f d) (f x).
Proof.
  induction s as [| jdg s ih | a jdg p s ih]. all: cbn [make].
  - reflexivity.
  - rewrite tuple_map_tcons, ih. reflexivity.
  - rewrite tuple_map_tcons, ih, tget_tuple_map. reflexivity.
Qed.
