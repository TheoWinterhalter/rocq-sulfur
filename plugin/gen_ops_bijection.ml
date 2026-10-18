(** This file generates the proof that [eval] and [reify] form a bijection between level
    zero terms and level one terms (actully, currently only one direction is needed). To
    prove this we also need to generate a custom induction principle on level one terms.
*)

open Prelude
open Signature
module C = Constants

module Make (P : sig
  val sign : signature
  val ops_conc : ops_concrete
  val ops_sign : ops_sign
  val re : ops_reify_eval
  val congr : ops_congr
end) =
struct
  (**************************************************************************************)
  (** *** Build the lemmas. *)
  (**************************************************************************************)

  (** Build [forall t, eval (reify t) = t]. *)
  let build_eval_reify () : EConstr.t m =
    prod "t" (mkind P.ops_conc.term) @@ fun t ->
    let t' =
      apps (mkconst P.re.eval)
        [| app (mkglob' C.k_t) @@ mkind P.ops_sign.base
         ; app (mkconst P.re.reify) @@ EConstr.mkVar t
        |]
    in
    ret @@ apps (mkglob' C.eq) [| mkind P.ops_conc.term; t'; EConstr.mkVar t |]

  (** Build [forall t, seval (sreify s) =₁ s]. *)
  let build_seval_sreify () : EConstr.t m =
    prod "s" (mkconst P.ops_conc.subst) @@ fun s ->
    let s' = app (mkconst P.re.seval) @@ app (mkconst P.re.sreify) @@ EConstr.mkVar s in
    ret
    @@ apps (mkglob' C.eq1)
         [| mkglob' C.nat; mkind P.ops_conc.term; s'; EConstr.mkVar s |]

  (**************************************************************************************)
  (** *** Prove the lemmas. *)
  (**************************************************************************************)

  (** Prove [forall t, eval (reify t) = t]. *)
  let prove_eval_reify () : unit Proofview.tactic =
    let open PVMonad in
    let* t = intro_fresh "t" in
    let* _ = induction @@ EConstr.mkVar t in
    let* _ = Tactics.simpl_in_concl in
    dispatch @@ function
    (* Solve the variable constructor with [reflexivity]. *)
    | 0 -> Tactics.reflexivity
    (* Solve the non-variable constructors by applying the appropriate congruence lemma
     and finishing with [auto]. *)
    | i -> Tactics.apply (mkconst P.congr.congr_ctors.(i - 1)) >> auto ()

  (** Prove [forall s, seval (sreify s) =₁ s]. *)
  let prove_seval_sreify (eval_reify : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_fresh "s" in
    let* _ = intro_fresh "i" in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.re.seval) in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.re.sreify) in
    Tactics.apply (mkconst eval_reify)

  (** Call the tactic [lia]. *)
  let lia () : unit Proofview.tactic =
    let open Ltac_plugin in
    let kname = mk_kername [ "Stdlib"; "micromega"; "Lia" ] "lia" in
    Tacinterp.eval_tactic (Tacenv.interp_ltac kname)
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(**
  Generate the bijection proof and the custom induction principle on the
  parametrised syntax (to match the one of the concrete syntax).
*)
let generate (s : signature) (ops_conc : ops_concrete) (ops_sign : ops_sign)
    (re : ops_reify_eval) (congr : ops_congr) : ops_bijection =
  let module M = Make (struct
    let sign = s
    let ops_conc = ops_conc
    let ops_sign = ops_sign
    let re = re
    let congr = congr
  end) in
  let eval_reify_inv =
    lemma "eval_reify_inv" (M.build_eval_reify ()) @@ M.prove_eval_reify ()
  in
  let seval_sreify_inv =
    lemma "seval_sreify_inv" (M.build_seval_sreify ())
    @@ M.prove_seval_sreify eval_reify_inv
  in
  let sign = mkconst ops_sign.sign in
  let term_ind =
    lemma "term_ind'"
      (Gen_ops_concrete.eval_cbn (app (mkglob' C.P.sig_ind_t) sign))
      (Tactics.exact_check (app (mkglob' C.P.sig_ind) sign))
  in
  { eval_reify_inv; seval_sreify_inv; term_ind }
