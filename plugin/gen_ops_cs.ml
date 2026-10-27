(** [ConcreteSyntax] generation

  This file produces an instance of the [ConcreteSyntax] class, as well as the
  laws of [ConcreteSyntaxLaws], both defined in [theories/ConcreteSyntax.v].

*)

open Prelude
open Signature
module C = Constants

(** Declare a constant as a typeclass instance. *)
let declare_instance (c : Names.Constant.t) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Classes.declare_instance ~warn:true env sigma None Hints.Export
    (Names.GlobRef.ConstRef c)

(** Build [forall e : expr Kt, reify (eval Kt e) = e]. *)
let build_reify_eval (osign : ops_sign) (re : ops_reify_eval) : EConstr.t m =
  prod "e" (term1 osign) @@ fun e ->
  let e' =
    app (mkconst re.reify) @@
    apps (mkconst re.eval) [| kt osign; EConstr.mkVar e |]
  in
  ret @@ apps (mkglob' C.eq) [| term1 osign; e'; EConstr.mkVar e |]

let generate (sign : signature) (ops : ops_all) : unit =
  let osign = ops.ops_si and oconc = ops.ops_conc and re = ops.ops_re in
  let sg = mkconst osign.sign in
  let term = mkind oconc.term in
  let cref c = Names.GlobRef.ConstRef c in
  (* [reify (eval Kt e) = e]. *)
  let reify_eval_inv =
    lemma "reify_eval_inv" (build_reify_eval osign re) @@
    run_ltac "ConcreteSyntax" "derive_rf_ev" [ cref re.eval_ctor ]
  in
  (* The instance of [ConcreteSyntax]. *)
  let cs =
    def "concrete_syntax" @@
    ret @@
    apps (mkglob' C.CS.build) [|
      sg ;
      term ;
      mkctor (oconc.term, 1) ;
      mkconst oconc.rename ;
      mkconst oconc.substitute ;
      app (mkconst re.eval) (kt osign) ;
      mkconst re.reify ;
      mkconst re.eval_ctor
    |]
  in
  declare_instance cs;
  (* The instance of [ConcreteSyntaxLaws]. *)
  let cs_laws =
    lemma "concrete_syntax_laws"
      (ret @@ apps (mkglob' C.CS.laws) [| sg; term; mkconst cs |]) @@
      run_ltac "ConcreteSyntax" "derive_cs_laws" [
        cref reify_eval_inv ;
        cref ops.ops_bij.eval_reify_inv ;
        cref ops.ops_pe.eval_rename ;
        cref ops.ops_pe.eval_substitute ;
        cref ops.ops_congr.congr_substitute
      ]
  in
  declare_instance cs_laws
