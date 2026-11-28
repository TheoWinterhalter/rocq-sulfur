From SulfurUtils Require Import Generalities.
From Stdlib Require Import Utf8 List.
Import ListNotations.

Set Default Goal Selector "!".

(* This files defines utils about functors *)
Class FMap (F : Type → Type) := fmap : forall {X Y : Type}, (X → Y) → (F X → F Y).
Arguments fmap (F) {_ _ _}.

Class Functor (F : Type → Type) `{FMap F} := {
  func_id : ∀ {X}, fmap F (λ (x : X), x) =₁ (λ x, x) ;

  func_comp :
    ∀ {X Y Z} (f : X → Y) (g : Y → Z),
      (λ x, fmap F g (fmap F f x)) =₁ fmap F (λ x, g (f x))
}.

Class Eq1Functor (F : Type → Type) `{FMap F} := {
  is_func :: Functor F;
  rew_eq1 {X Y} :: Proper (@eq1 X Y ==> eq1) (fmap F)
}.

(** Examples of functors **)
(* Identity functor *)
#[export] Instance FMapId : FMap (fun X : Type => X) :=
  λ _ _ f, f.

#[export] Instance FId : Eq1Functor (fun X => X).
Proof.
  constructor.
  - constructor. all: cbv. all: auto.
  - cbv. auto.
Qed.

(* Constant functor *)
#[export] Instance FMapConst (C : Type) : FMap (λ _, C) :=
  λ _ _ _ c, c.

#[export] Instance FConst (C : Type) : Eq1Functor (λ _, C).
Proof.
  constructor.
  - constructor. all: cbv. all: auto.
  - cbv. auto.
Qed.

(* Composition of functors *)
#[export] Instance FMapComp {F G} `{Functor F} `{Functor G} :
  FMap (λ X, F (G X)) :=
  λ X Y f x, fmap F (fmap G f) x.

#[export] Instance FComp {F G} `{Eq1Functor F} `{Eq1Functor G} :
  Eq1Functor (λ X, F (G X)).
Proof.
  constructor.
  - constructor.
    + intros X x. unfold fmap, FMapComp.
      erewrite rew_eq1. 2: apply func_id.
      apply func_id.
    + intros X Y Z f g x. unfold fmap, FMapComp.
      rewrite func_comp. apply rew_eq1. intros y.
      apply func_comp.
  - intros X Y f g e x. unfold fmap, FMapComp.
    apply rew_eq1. apply rew_eq1. assumption.
Qed.

(* At one point, we need a natural transformation but from a product functor,
  which makes everything not curryfied. We express what is a natural
  transformation from a product functor but with a curryfied version
*)
Class NatFromProd {F G H : Type → Type}
  `{Functor F} `{Functor G} `{Functor H}
  (η : forall X, F X → G X → H X) :=
{
  naturality_prod : ∀ {X Y} (f : X → Y) (xF : F X) (xG :  G X),
    fmap H f (η X xF xG) = η Y (fmap F f xF) (fmap G f xG)
}.

(* Maybe at some point it will be interesting to make the general definition of
  a natural transformation and say that this is a particular case?
*)

(* Lists *)
#[export] Instance FMapList : FMap list := map.
#[export] Instance Flist : Eq1Functor list.
Proof.
  constructor. 1: constructor.
  all: cbv - [ List.map ].
  - apply map_id.
  - apply map_map.
  - apply map_ext.
Qed.

(* Product of functors *)
#[export] Instance FMapProd F G `{FMap F} `{FMap G} :
  FMap (λ X, (F X * G X)%type) :=
  λ X Y (f : X → Y) '(xf, xg), (fmap F f xf, fmap G f xg).

#[export] Instance FProd F G `{Functor F} `{Functor G} :
  Functor (λ X, (F X * G X)%type).
Proof.
  constructor. all: unfold fmap, FMapProd.
  - intros X [x y]. rewrite 2!func_id. reflexivity.
  - intros X Y Z f g [x y]. rewrite 2!func_comp. reflexivity.
Qed.

#[export] Instance Eq1FProd F G `{Eq1Functor F} `{Eq1Functor G} :
  Eq1Functor (λ X, (F X * G X)%type).
Proof.
  constructor. 1: typeclasses eauto.
  intros X Y f g e [x y].
  unfold fmap, FMapProd.
  f_equal. all: apply rew_eq1. all: assumption.
Qed.

(* Sanity check *)
Goal Eq1Functor (λ X, (X * nat * X)%type).
Proof.
  typeclasses eauto.
Qed.


(** Lifting of a predicate to a functor **)
(* Class Lift (F : Type → Type) := lift : forall X, (X → Prop) → (F X → Prop).
Arguments lift (F) {_ _}.

(* We will see what axioms we need *)
Class Predicator (F : Type → Type) `{Lift F}
:= {}.

#[export] Instance LiftList : Lift list := Forall.
#[export] Instance PList : Predicator list.
Qed.

#[export] Instance LiftId : Lift (fun X => X) := fun _ P => P.
#[export] Instance PId : Predicator (fun X => X).
Qed.

#[export] Instance LiftProd F G `{Lift F} `{Lift G} : Lift (fun X => (F X * G X)%type) :=
fun _ P '(xf, xg) => (lift F P xf) /\ (lift G P xg).
#[export] Instance PProd F G `{Predicator F} `{Predicator G} : Predicator (fun X => (F X * G X)%type).
Qed. *)
