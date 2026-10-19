From Utils Require Import Generalities.
From Stdlib Require Import List. Import ListNotations.

(* This files defines utils about functors *)
Class FMap (F : Type -> Type) := fmap : forall {X Y : Type}, (X -> Y) -> (F X -> F Y).
Arguments fmap (F) {_ _ _}.

Class Functor (F : Type -> Type) `{FMap F} := {
  func_id : forall {X : Type},
    fmap F (fun x : X => x) =₁ (fun x => x);

  func_comp : forall {X Y Z : Type} (f : X -> Y) (g : Y -> Z),
    (fun x => fmap F g (fmap F f x)) =₁ fmap F (fun x => g (f x))
}.

Class Eq1Functor (F : Type -> Type) `{FMap F} := {
  is_func :: Functor F;
  rew_eq1 {X Y} :: Proper (@eq1 X Y ==> eq1) (fmap F)
}.

(** Examples of functors **)
(* Identity functor *)
#[export] Instance FMapId : FMap (fun X : Type => X) :=
  fun _ _ f => f.
#[export] Instance FId : Eq1Functor (fun X => X).
Proof.
  constructor.
  constructor; unfold fmap; repeat intro; reflexivity.
  repeat intro. unfold fmap. apply H.
Qed.

(* Constant functor *)
#[export] Instance FMapConst (C : Type) : FMap (fun _ => C) :=
  fun _ _ _ => (fun c => c).
#[export] Instance FConst (C : Type) : Eq1Functor (fun _ => C).
Proof.
  constructor.
  constructor; unfold fmap; repeat intro; reflexivity.
  repeat intro. reflexivity.
Qed.

(* At one point, we need a natural transformation but from a product functor, which makes everything not curryfied. We express what is a natural transformation from a product functor but with a curryfied version *)
Class NatFromProd {F G H : Type -> Type}
  `{Functor F} `{Functor G} `{Functor H}
  (η : forall X, F X -> G X -> H X) :=
{
  naturality_prod: forall {X Y} (f : X -> Y) (xF : F X) (xG :  G X),
  fmap H f (η X xF xG) =
  η Y (fmap F f xF) (fmap G f xG)
}.
(* Maybe at some point it will be interesting to make the general definition of a natural transformation and say that this is a particular case? *)

(* Lists *)
#[export] Instance FMapList : FMap list := map.
#[export] Instance Flist : Eq1Functor list.
Proof.
  constructor.
  constructor; unfold fmap, FMapList; repeat intro.
  - apply map_id.
  - induction a; simpl.
    reflexivity.
    rewrite IHa. reflexivity.
  - repeat intro. induction a.
    + reflexivity.
    + unfold fmap. simpl. rewrite H. reflexivity.
Qed.

(* Product of functors *)
#[export] Instance FMapProd F G `{FMap F} `{FMap G} : FMap (fun X => (F X * G X)%type) :=
  fun X Y (f : X -> Y) '(xf, xg) => (fmap F f xf, fmap G f xg).
#[export] Instance FProd F G `{Functor F} `{Functor G} : Functor (fun X => (F X * G X)%type).
Proof.
  constructor; unfold fmap, FMapProd; repeat intro; destruct a as [xf xg].
  - rewrite 2!func_id. reflexivity.
  - rewrite 2!func_comp. reflexivity.
Qed.
#[export] Instance Eq1FProd F G `{Eq1Functor F} `{Eq1Functor G} : Eq1Functor (fun X => (F X * G X)%type).
Proof.
  constructor. typeclasses eauto.
  repeat intro. unfold fmap. rename x into f, y into g.
  destruct a as [fx gx]. simpl.
  f_equal; (erewrite rew_eq1; [reflexivity|apply H3]).
Qed.

(* Sanity check *)
Goal Eq1Functor (fun X => (X*nat*X)%type).
Proof.
  typeclasses eauto.
Qed.


(** Lifting of a predicate to a functor **)
(* Class Lift (F : Type -> Type) := lift : forall X, (X -> Prop) -> (F X -> Prop).
Arguments lift (F) {_ _}.

(* We will see what axioms we need *)
Class Predicator (F : Type -> Type) `{Lift F}
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
