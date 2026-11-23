(** Copies of functions from the standard library

  The point is to be able to simplify expressons in the plugin a bit agressively
  without worrying about user input: they will use List.map and the plugin
  will use its copy from here.

  This is a bit silly, so maybe there is way to do this better?

*)

From Stdlib Require Import Utf8 Nat Bool List.
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

  Fixpoint lnth n (l : list A) default {struct l} :=
    match n, l with
    | 0, x :: _ => x
    | S n, _ :: l => lnth n l default
    | _, _ => default
    end.

  Fixpoint lapp (l m : list A) :=
    match l with
    | [] => m
    | a :: l => a :: lapp l m
    end.

  (* TODO Maybe we take this opportunity to use a smarter rev? *)
  Fixpoint lrev (l : list A) :=
    match l with
    | [] => []
    | a :: l => lapp (lrev l) [ a ]
    end.

  Context (g : B → A → A) (a : A).

  Fixpoint lfold_right (l : list B) : A :=
    match l with
    | [] => a
    | b :: l => g b (lfold_right l)
    end.

  Fixpoint lseq start len {struct len} :=
    match len with
    | 0 => []
    | S len => start :: lseq (S start) len
    end.

  Fixpoint lnth_error (l : list A) n {struct n} :=
    match n, l with
    | 0, a :: _ => Some a
    | S n, _ :: l => lnth_error l n
    | _, _ => None
    end.

End Lists.

Notation "a ++' b" :=
  (lapp a b)
  (at level 60, b at next level, right associativity).

Lemma lmap_map :
  lmap = map.
Proof.
  reflexivity.
Qed.

Lemma llength_length :
  llength = length.
Proof.
  reflexivity.
Qed.

Lemma lnth_nth :
  lnth = nth.
Proof.
  reflexivity.
Qed.

Lemma lapp_app :
  lapp = app.
Proof.
  reflexivity.
Qed.

Lemma lrev_rev :
  lrev = rev.
Proof.
  reflexivity.
Qed.

Lemma lfold_right_def :
  lfold_right = fold_right.
Proof.
  reflexivity.
Qed.

Lemma lseq_seq :
  lseq = seq.
Proof.
  reflexivity.
Qed.

Lemma lnth_error_def :
  lnth_error = nth_error.
Proof.
  reflexivity.
Qed.

Section Pairs.

  Context {A B : Type}.

  Definition pfst (p : A * B) :=
    let (a,_) := p in a.

  Definition psnd (p : A * B) :=
    let (_,b) := p in b.

End Pairs.

Lemma pfst_fst :
  @pfst = @fst.
Proof.
  reflexivity.
Qed.

Lemma psnd_snd :
  @psnd = @snd.
Proof.
  reflexivity.
Qed.

Definition idfun {A} (x : A) := x.

Lemma idfun_id :
  @idfun = @id.
Proof.
  reflexivity.
Qed.

Fixpoint nadd n m :=
  match n with
  | 0 => m
  | S n => S (nadd n m)
  end.

Notation "n +' m" :=
  (nadd n m)
  (at level 50, m at next level, left associativity).

Lemma nadd_add :
  nadd = add.
Proof.
  reflexivity.
Qed.

Fixpoint neqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => neqb n m
  | _, _ => false
  end.

Lemma neqb_eqb :
  neqb = Nat.eqb.
Proof.
  reflexivity.
Qed.

Infix "=?'" := neqb (at level 70) : nat_scope.

Definition bandb (x y : bool) :=
  if x then y else false.

Notation "x &&' y" :=
  (bandb x y)
  (at level 40, y at next level, left associativity).

Lemma bandb_andb :
  bandb = andb.
Proof.
  reflexivity.
Qed.

Definition bnegb (b : bool) :=
  if b then false else true.

Notation "~' b" :=
  (bnegb b)
  (at level 75, right associativity).

Lemma bnegb_negb :
  bnegb = negb.
Proof.
  reflexivity.
Qed.
