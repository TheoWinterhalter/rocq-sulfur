From Stdlib Require Import Utf8 List.
From SulfurGhostExample Require Import Util GAST SubstNotations ContextDecl
  CastRemoval TermMode Scoping.
From SulfurGhostExample Require Export Univ TermNotations.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(** Before we define typing for vectors we need to define the gS function **)
Definition gS n :=
  reveal n (lam mGhost (Erased tnat) (Erased tnat))
    (lam mType tnat (hide (tsucc (Var 0)))).

(** We also need something which is essentially the length function
  but whose main idea is to recompute the index of a vector.
**)
Definition glength A n v :=
  tvec_elim mGhost A n v
    (* return *) (lam mGhost (Erased tnat) (
      lam mType (tvec (S ⋅ A) (Var 0)) (Erased tnat)
    )
    )
    (* vnil => *) (hide tzero)
    (* vcons => *) (lam mType A (
      lam mGhost (Erased tnat) (
        lam mType (tvec (S ⋅ S ⋅ A) (Var 0)) (
          lam mGhost (Erased tnat) (gS (Var 0))
        )
      )
    )).

Sulfur Judgment conversion : term → term → Prop
  with context Γ of (mode * term) and variable x m _ ↦ conversion x x :=
(** Computation rules **)

| conv_beta (m mx : mode) A (t : term → term) u :
    {{ cscoping Γ A mKind }} ;
    {{ scoping (mx :: sc Γ) t m }} ;
    {{ cscoping Γ u mx }}
    ⟹ conversion (app (lam mx A t) u) (t u)

| reveal_hide (mp : mode) t P p :
    {{ cscoping Γ t mType }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ p mp }} ;
    {{ In mp [ mProp ; mGhost ] }}
    ⟹ conversion (reveal (hide t) P p) (app p t)

| conv_if_true (m : mode) P t f :
    {{ cscoping Γ t m }}
    ⟹ conversion (tif m ttrue P t f) t

| conv_if_false (m : mode) P t f :
    {{ cscoping Γ f m }}
    ⟹ conversion (tif m tfalse P t f) f

| conv_nat_elim_zero (m : mode) P z s :
    {{ m ≠ mKind }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ z m }} ;
    {{ cscoping Γ s m }}
    ⟹ conversion (tnat_elim m tzero P z s) z

| conv_nat_elim_succ (m : mode) P z s n :
    {{ m ≠ mKind }} ;
    {{ cscoping Γ n mType }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ z m }} ;
    {{ cscoping Γ s m }}
    ⟹ conversion (tnat_elim m (tsucc n) P z s)
      (app (app s n) (tnat_elim m n P z s))

| conv_vec_elim_nil (m : mode) A P z s :
    {{ m ≠ mKind }} ;
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ z m }} ;
    {{ cscoping Γ s m }}
    ⟹ conversion (tvec_elim m A (hide tzero) (tvnil A) P z s) z

| conv_vec_elim_cons (m : mode) A a n n' v P z s :
    {{ m ≠ mKind }} ;
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ a mType }} ;
    {{ cscoping Γ n mGhost }} ;
    {{ cscoping Γ n' mGhost }} ;
    {{ cscoping Γ v mType }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ z m }} ;
    {{ cscoping Γ s m }}
    ⟹ conversion (tvec_elim m A n' (tvcons a n v) P z s)
      (app
        (app
          (app (app s a)
            (* glength A n v *)
            (tvec_elim mGhost A n v
              (lam mGhost (Erased tnat) (λ n0,
                lam mType (tvec A n0) (λ _, Erased tnat)))
              (hide tzero)
              (lam mType A (λ _,
                lam mGhost (Erased tnat) (λ n0,
                  lam mType (tvec A n0) (λ _,
                    lam mGhost (Erased tnat) (λ l,
                      (* gS l *)
                      reveal l (lam mGhost (Erased tnat) (λ _, Erased tnat))
                        (lam mType tnat (λ x, hide (tsucc x))))))))))
          v)
        (tvec_elim m A n v P z s))

(** Congruence rules **)

(** A rule to quotient away all levels of Prop, making it impredicative **)
| cong_Prop (i j : level) :
    ⟹ conversion (Sort mProp i) (Sort mProp j)

| cong_Pi (i i' j j' : level) (m mx : mode) A A' (B B' : term → term) :
    conversion A A' ;
    ⟨ x ↦ (mx, A) ⊢ conversion (B x) (B' x) ⟩ ;
    {{ ueq mx i i' }} ;
    {{ ueq m j j' }}
    ⟹ conversion (Pi i j m mx A B) (Pi i' j' m mx A' B')

| cong_lam (mx : mode) A A' (t t' : term → term) :
    conversion A A' ;
    ⟨ x ↦ (mx, A) ⊢ conversion (t x) (t' x) ⟩
    ⟹ conversion (lam mx A t) (lam mx A' t')

| cong_app u u' v v' :
    conversion u u' ;
    conversion v v'
    ⟹ conversion (app u v) (app u' v')

| cong_Erased A A' :
    conversion A A'
    ⟹ conversion (Erased A) (Erased A')

| cong_hide u u' :
    conversion u u'
    ⟹ conversion (hide u) (hide u')

| cong_reveal t t' P P' p p' :
    conversion t t' ;
    conversion P P' ;
    conversion p p'
    ⟹ conversion (reveal t P p) (reveal t' P' p')

| cong_Reveal t t' p p' :
    conversion t t' ;
    conversion p p'
    ⟹ conversion (Reveal t p) (Reveal t' p')

| cong_gheq A A' u u' v v' :
    conversion A A' ;
    conversion u u' ;
    conversion v v'
    ⟹ conversion (gheq A u v) (gheq A' u' v')

| cong_if (m : mode) b P t f b' P' t' f' :
    conversion b b' ;
    conversion P P' ;
    conversion t t' ;
    conversion f f'
    ⟹ conversion (tif m b P t f) (tif m b' P' t' f')

| cong_succ n n' :
    conversion n n'
    ⟹ conversion (tsucc n) (tsucc n')

| cong_nat_elim (m : mode) n P z s n' P' z' s' :
    conversion n n' ;
    conversion P P' ;
    conversion z z' ;
    conversion s s'
    ⟹ conversion (tnat_elim m n P z s) (tnat_elim m n' P' z' s')

| cong_vec A A' n n' :
    conversion A A' ;
    conversion n n'
    ⟹ conversion (tvec A n) (tvec A' n')

| cong_vnil A A' :
    conversion A A'
    ⟹ conversion (tvnil A) (tvnil A')

| cong_vcons a n v a' n' v' :
    conversion a a' ;
    conversion n n' ;
    conversion v v'
    ⟹ conversion (tvcons a n v) (tvcons a' n' v')

| cong_vec_elim (m : mode) A n v P z s A' n' v' P' z' s' :
    conversion A A' ;
    conversion n n' ;
    conversion v v' ;
    conversion P P' ;
    conversion z z' ;
    conversion s s'
    ⟹ conversion (tvec_elim m A n v P z s) (tvec_elim m A' n' v' P' z' s')

| cong_bot_elim (m : mode) A A' p p' :
    conversion A A' ;
    conversion p p'
    ⟹ conversion (bot_elim m A p) (bot_elim m A' p')

(** Structural rules **)

| conv_refl u :
    ⟹ conversion u u

| conv_sym u v :
    conversion u v
    ⟹ conversion v u

| conv_trans u v w :
    conversion u v ;
    conversion v w
    ⟹ conversion u w

(** Proof irrelevance **)

| conv_irr p q :
    {{ cscoping Γ p mProp }} ;
    {{ cscoping Γ q mProp }}
    ⟹ conversion p q.

Notation "Γ ⊢ u ≡ v" :=
  (conversion Γ u v)
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≡  v").

Lemma cstyping_conversion_scoping Δ Γ σ :
  cstyping Fin.finO conversion Δ σ Γ →
  cstyping (sh := scoping_shapes) Fin.finO scoping (sc Δ) σ (sc Γ).
Proof.
  intros h. cbn in *.
  induction h as [| Δ σ Γ d hd h0 ih]. 1: constructor.
  cbn in *. constructor.
  - auto.
  - cbn. unfold id.
    (* It seems we want something stronger *)
Admitted.

Instance: conversion_obligations.
Proof.
  red.
  intuition (try (eapply scoping_subst ; eauto using cstyping_conversion_scoping)).
Admitted.

Sulfur Judgment typing : term → term → Prop
  with context Γ of (mode * term)
  and variable x m A ↦ typing x A :=
| type_sort (m : mode) (i : level) :
    ⟹ typing (Sort m i) (Sort mKind (usup m i))

| type_pi (i j : level) (mx m : mode) A (B : term → term) :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping (Γ ,, (mx, A)) B mKind }} ;
    typing A (Sort mx i) ;
    ⟨ x ↦ (mx, A) ⊢ typing (B x) (Sort m j) ⟩
    ⟹ typing (Pi i j m mx A B) (Sort m (umax mx m i j))

| type_lam (mx m : mode) (i j : level) A (B t : term → term) :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping (Γ ,, (mx, A)) B mKind }} ;
    {{ cscoping (Γ ,, (mx, A)) t m }} ;
    typing A (Sort mx i) ;
    ⟨ x ↦ (mx, A) ⊢ typing (B x) (Sort m j) ⟩ ;
    ⟨ x ↦ (mx, A) ⊢ typing (t x) (B x) ⟩
    ⟹ typing (lam mx A t) (Pi i j m mx A B)

| type_app (i j : level) (mx m : mode) A (B : term → term) t u :
    {{ cscoping (Γ ,, (mx, A)) B mKind }} ;
    {{ cscoping Γ t m }} ;
    {{ cscoping Γ u mx }} ;
    {{ cscoping Γ A mKind }} ;
    typing t (Pi i j m mx A B) ;
    typing u A ;
    typing A (Sort mx i) ;
    ⟨ x ↦ (mx, A) ⊢ typing (B x) (Sort m j) ⟩
    ⟹ typing (app t u) (B u)

| type_erased (i : level) A :
    {{ cscoping Γ A mKind }} ;
    typing A (Sort mType i)
    ⟹ typing (Erased A) (Sort mGhost i)

| type_hide (i : level) A t :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ t mType }} ;
    typing A (Sort mType i) ;
    typing t A
    ⟹ typing (hide t) (Erased A)

| type_reveal (i j : level) (m : mode) A t P p :
    {{ cscoping Γ p m }} ;
    {{ cscoping Γ t mGhost }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ A mKind }} ;
    {{ In m [ mProp ; mGhost ] }} ;
    typing t (Erased A) ;
    typing P (Pi i (usup m j) mKind mGhost (Erased A) (λ _, Sort m j)) ;
    typing p (Pi i j m mType A (λ x, app P (hide x))) ;
    typing A (Sort mType i)
    ⟹ typing (reveal t P p) (app P t)

| type_Reveal (i : level) A t p :
    {{ cscoping Γ t mGhost }} ;
    {{ cscoping Γ p mKind }} ;
    typing t (Erased A) ;
    typing p (Pi i 0 mKind mType A (λ _, Sort mProp 0)) ;
    typing A (Sort mType i) ;
    {{ cscoping Γ A mKind }}
    ⟹ typing (Reveal t p) (Sort mProp 0)

| type_toRev (i : level) A t p u :
    {{ cscoping Γ t mType }} ;
    {{ cscoping Γ p mKind }} ;
    {{ cscoping Γ u mProp }} ;
    typing t A ;
    typing p (Pi i 0 mKind mType A (λ _, Sort mProp 0)) ;
    typing u (app p t)
    ⟹ typing (toRev t p u) (Reveal (hide t) p)

| type_fromRev (i : level) A t p u :
    {{ cscoping Γ t mType }} ;
    {{ cscoping Γ p mKind }} ;
    {{ cscoping Γ u mProp }} ;
    typing t A ;
    typing p (Pi i 0 mKind mType A (λ _, Sort mProp 0)) ;
    typing u (Reveal (hide t) p)
    ⟹ typing (fromRev t p u) (app p t)

| type_gheq (i : level) A u v :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ u mGhost }} ;
    {{ cscoping Γ v mGhost }} ;
    typing A (Sort mGhost i) ;
    typing u A ;
    typing v A
    ⟹ typing (gheq A u v) (Sort mProp 0)

| type_ghrefl (i : level) A u :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ u mGhost }} ;
    typing A (Sort mGhost i) ;
    typing u A
    ⟹ typing (ghrefl A u) (gheq A u u)

| type_ghcast (i : level) (m : mode) A u v e P t :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ u mGhost }} ;
    {{ cscoping Γ v mGhost }} ;
    {{ cscoping Γ t m }} ;
    {{ cscoping Γ e mProp }} ;
    {{ m ≠ mKind }} ;
    typing A (Sort mGhost i) ;
    typing u A ;
    typing v A ;
    typing e (gheq A u v) ;
    typing P (Pi i (usup m i) mKind mGhost A (λ _, Sort m i)) ;
    typing t (app P u)
    ⟹ typing (ghcast A u v e P t) (app P v)

| type_bool :
    ⟹ typing tbool (Sort mType 0)

| type_true :
    ⟹ typing ttrue tbool

| type_false :
    ⟹ typing tfalse tbool

| type_if (i : level) (m : mode) b P t f :
    {{ cscoping Γ b mType }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ t m }} ;
    {{ cscoping Γ f m }} ;
    typing b tbool ;
    typing P (Pi 0 (usup m i) mKind mType tbool (λ _, Sort m i)) ;
    typing t (app P ttrue) ;
    typing f (app P tfalse)
    ⟹ typing (tif m b P t f) (app P b)

| type_nat :
    ⟹ typing tnat (Sort mType 0)

| type_zero :
    ⟹ typing tzero tnat

| type_succ n :
    {{ cscoping Γ n mType }} ;
    typing n tnat
    ⟹ typing (tsucc n) tnat

| type_nat_elim (i : level) (m : mode) n P z s :
    {{ m ≠ mKind }} ;
    {{ cscoping Γ n mType }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ z m }} ;
    {{ cscoping Γ s m }} ;
    typing n tnat ;
    typing P (Pi 0 (usup m i) mKind mType tnat (λ _, Sort m i)) ;
    typing z (app P tzero) ;
    typing s (Pi 0 i m mType tnat (λ x,
      Pi i i m m (app P x) (λ _, app P (tsucc x))))
    ⟹ typing (tnat_elim m n P z s) (app P n)

| type_vec (i : level) A n :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ n mGhost }} ;
    typing A (Sort mType i) ;
    typing n (Erased tnat)
    ⟹ typing (tvec A n) (Sort mType i)

| type_vnil (i : level) A :
    {{ cscoping Γ A mKind }} ;
    typing A (Sort mType i)
    ⟹ typing (tvnil A) (tvec A (hide tzero))

| type_vcons (i : level) A a n v :
    {{ cscoping Γ a mType }} ;
    {{ cscoping Γ n mGhost }} ;
    {{ cscoping Γ v mType }} ;
    typing a A ;
    typing n (Erased tnat) ;
    typing v (tvec A n) ;
    typing A (Sort mType i) ;
    {{ cscoping Γ A mKind }}
    ⟹ typing (tvcons a n v)
      (tvec A
        (* gS n *)
        (reveal n (lam mGhost (Erased tnat) (λ _, Erased tnat))
          (lam mType tnat (λ x, hide (tsucc x)))))

| type_vec_elim (i j : level) (m : mode) A n v P z s :
    {{ m ≠ mKind }} ;
    {{ cscoping Γ v mType }} ;
    {{ cscoping Γ P mKind }} ;
    {{ cscoping Γ z m }} ;
    {{ cscoping Γ s m }} ;
    typing v (tvec A n) ;
    typing P (Pi 0 (umax mType mKind i (usup m j)) mKind mGhost (Erased tnat)
      (λ n0, Pi i (usup m j) mKind mType (tvec A n0) (λ _, Sort m j))) ;
    typing z (app (app P (hide tzero)) (tvnil A)) ;
    typing s (Pi i (umax mGhost m 0 (umax mType m i (umax m m j j))) m mType A
      (λ a, Pi 0 (umax mType m i (umax m m j j)) m mGhost (Erased tnat)
        (λ n0, Pi i (umax m m j j) m mType (tvec A n0)
          (λ v0, Pi j j m m (app (app P n0) v0)
            (λ _, app
              (app P
                (* gS n0 *)
                (reveal n0 (lam mGhost (Erased tnat) (λ _, Erased tnat))
                  (lam mType tnat (λ x, hide (tsucc x)))))
              (tvcons a n0 v0)))))) ;
    {{ cscoping Γ n mGhost }} ;
    {{ cscoping Γ A mKind }} ;
    typing n (Erased tnat) ;
    typing A (Sort mType i)
    ⟹ typing (tvec_elim m A n v P z s) (app (app P n) v)

| type_bot :
    ⟹ typing bot (Sort mProp 0)

| type_bot_elim (i : level) (m : mode) A p :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ p mProp }} ;
    typing A (Sort m i) ;
    typing p bot
    ⟹ typing (bot_elim m A p) A

| type_conv (i : level) (m : mode) A B t :
    {{ cscoping Γ A mKind }} ;
    {{ cscoping Γ B mKind }} ;
    {{ cscoping Γ t m }} ;
    typing t A ;
    {{ Γ ⊢ ε|A| ≡ ε|B| }} ;
    typing B (Sort m i)
    ⟹ typing t B.

Notation "Γ ⊢ t : A" :=
  (typing Γ t A)
  (at level 80, t, A at next level, format "Γ  ⊢  t  :  A").

Lemma cstyping_typing_scoping Δ Γ σ :
  cstyping Fin.finO typing Δ σ Γ →
  cstyping (sh := scoping_shapes) Fin.finO scoping (sc Δ) σ (sc Γ).
Proof.
  intros h. cbn in *.
  induction h as [| Δ σ Γ d hd ih h0]. 1: constructor.
  cbn in *. constructor.
  - auto.
  - cbn. unfold id.
    destruct d as [m t]. cbn in *.
    (* Might be ok *)
Admitted.

Instance: typing_obligations.
Proof.
  (* red. intuition eauto.
  - eapply scoping_subst. 1: eauto. *)
Admitted.

(** Context formation **)

Inductive wf : context → Prop :=
| wf_nil : wf nil
| wf_cons :
    ∀ Γ m i A,
      wf Γ →
      cscoping Γ A mKind →
      Γ ⊢ A : Sort m i →
      wf (Γ ,, (m, A)).

Create HintDb gtt_conv discriminated.
Create HintDb gtt_type discriminated.

Hint Resolve conv_beta reveal_hide conv_if_true conv_if_false conv_nat_elim_zero
  conv_nat_elim_succ conv_vec_elim_nil conv_vec_elim_cons cong_Prop cong_Pi
  cong_lam cong_app cong_Erased cong_hide cong_reveal cong_Reveal cong_gheq
  cong_if cong_succ cong_nat_elim cong_vec cong_vnil cong_vcons cong_vec_elim
  cong_bot_elim conv_refl
: gtt_conv.

Hint Resolve typing_var type_sort type_pi type_lam type_app type_erased
  type_hide type_reveal type_Reveal type_toRev type_fromRev type_gheq
  type_ghrefl type_ghcast type_bool type_true type_false type_if type_nat
  type_zero type_succ type_nat_elim type_vec type_vnil type_vcons type_vec_elim
  type_bot type_bot_elim
: gtt_type.

Ltac gconv :=
  unshelve typeclasses eauto with gtt_scope gtt_conv shelvedb ;
  shelve_unifiable.

Ltac gtype :=
  unshelve typeclasses eauto with gtt_scope gtt_type shelvedb ;
  shelve_unifiable.
