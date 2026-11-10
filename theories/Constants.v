(** This module exposes various constants to the OCaml plugin.
    Constants are accessed in the plugin from [plugin/constants.ml]. *)

From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require ParamSyntax ConcreteSyntax JdgDesc JdgShape.

(*********************************************************************************)
(** *** Basic constants. *)
(*********************************************************************************)

Register unit as sulfur.unit.type.
Register tt as sulfur.unit.tt.

Register prod as sulfur.prod.type.
Register pair as sulfur.prod.pair.

Register nat as sulfur.nat.type.
Register O as sulfur.nat.zero.
Register S as sulfur.nat.succ.
Register Nat.sub as sulfur.nat.sub.

Register list as sulfur.list.type.
Register nil as sulfur.list.nil.
Register cons as sulfur.list.cons.
Register Datatypes.app as sulfur.list.app.
Register List.map as sulfur.list.map.

Register string as sulfur.string.type.

Register eq as sulfur.eq.type.
Register eq_refl as sulfur.eq.refl.
Register eq_sym as sulfur.eq.sym.
Register eq_trans as sulfur.eq.trans.

Register eq1 as sulfur.eq1.type.
Register eq1_refl as sulfur.eq1.refl.
Register eq1_sym as sulfur.eq1.sym.
Register eq1_trans as sulfur.eq1.trans.

(** Prelude *)

Register mkenum as sulfur.enum.make.
Register enum_all_in as sulfur.enum.all_in.

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

Register ren as sulfur.ren.type.

Register rid as sulfur.ren.rid.
Register rshift as sulfur.ren.rshift.
Register rcons as sulfur.ren.rcons.
Register rcomp as sulfur.ren.rcomp.
Register up_ren as sulfur.ren.up_ren.

Register congr_rcons as sulfur.ren.congr_rcons.
Register congr_rcomp as sulfur.ren.congr_rcomp.
Register congr_up_ren as sulfur.ren.congr_up_ren.

(*********************************************************************************)
(** *** Signatures. *)
(*********************************************************************************)

Register arg_ty  as sulfur.arg_ty.type.
Register AT_base as sulfur.arg_ty.base.
Register AT_term as sulfur.arg_ty.term.
Register AT_bind as sulfur.arg_ty.bind.

Register kind as sulfur.kind.type.
Register Kt as sulfur.kind.t.
Register Ka as sulfur.kind.a.
Register Kal as sulfur.kind.al.

Register signature as sulfur.signature.type.
Register Build_signature as sulfur.signature.ctor.

(*********************************************************************************)
(** *** Parameterized syntax. *)
(*********************************************************************************)

Register ParamSyntax.expr as sulfur.param.expr.type.
Register ParamSyntax.E_var as sulfur.param.expr.var.
Register ParamSyntax.E_ctor as sulfur.param.expr.ctor.
Register ParamSyntax.E_al_nil as sulfur.param.expr.al_nil.
Register ParamSyntax.E_al_cons as sulfur.param.expr.al_cons.
Register ParamSyntax.E_abase as sulfur.param.expr.abase.
Register ParamSyntax.E_aterm as sulfur.param.expr.aterm.
Register ParamSyntax.E_abind as sulfur.param.expr.abind.
Register ParamSyntax.subst as sulfur.param.subst.

Register ParamSyntax.rename as sulfur.param.rename.
Register ParamSyntax.substitute as sulfur.param.substitute.
Register ParamSyntax.sid as sulfur.param.sid.
Register ParamSyntax.sshift as sulfur.param.sshift.
Register ParamSyntax.scons as sulfur.param.scons.
Register ParamSyntax.up_subst as sulfur.param.up_subst.
Register ParamSyntax.scomp as sulfur.param.scomp.
Register ParamSyntax.rscomp as sulfur.param.rscomp.
Register ParamSyntax.srcomp as sulfur.param.srcomp.

Register ParamSyntax.inv_Kal_nil as sulfur.param.inv_Kal_nil.
Register ParamSyntax.inv_Kal_cons as sulfur.param.inv_Kal_cons.
Register ParamSyntax.inv_Ka_term as sulfur.param.inv_Ka_term.
Register ParamSyntax.inv_Ka_base as sulfur.param.inv_Ka_base.
Register ParamSyntax.inv_Ka_bind as sulfur.param.inv_Ka_bind.

Register ParamSyntax.sig_ind_t as sulfur.param.sig_ind_t.
Register ParamSyntax.sig_ind as sulfur.param.sig_ind.

(** ConcreteSyntax *)

Register ConcreteSyntax.carg as sulfur.cs.carg.
Register ConcreteSyntax.cargs as sulfur.cs.cargs.
Register ConcreteSyntax.ckind as sulfur.cs.ckind.
Register ConcreteSyntax.mkCS as sulfur.cs.build.
Register ConcreteSyntax.ConcreteSyntaxLaws as sulfur.cs.laws.
Register ConcreteSyntax.csubstitute as sulfur.cs.csubstitute.
Register ConcreteSyntax.ConcreteSyntax as sulfur.cs.type.

(** JdgDesc *)

Register JdgDesc.rp_term as sulfur.jdg.rp_term.
Register JdgDesc.rp_param as sulfur.jdg.rp_param.
Register JdgDesc.rule_desc as sulfur.jdg.rule_desc.
Register JdgDesc.jdg_desc as sulfur.jdg.jdg_desc.
Register JdgDesc.hterm as sulfur.jdg.hterm.
Register JdgDesc.hctor as sulfur.jdg.hctor.
Register JdgDesc.hjdg as sulfur.jdg.hjdg.
Register JdgDesc.hext as sulfur.jdg.hext.
Register JdgDesc.hjp as sulfur.jdg.hjp.
Register JdgDesc.hprem as sulfur.jdg.hprem.
Register JdgDesc.hpred as sulfur.jdg.hpred.
Register JdgDesc.cup_subst as sulfur.jdg.cup_subst.
Register JdgDesc.pred_obl as sulfur.jdg.pred_obl.
Register JdgDesc.ob as sulfur.jdg.ob.
Register JdgDesc.ob_pred as sulfur.jdg.ob_pred.
Register JdgDesc.ob_make as sulfur.jdg.ob_make.
Register JdgDesc.obligations as sulfur.jdg.obligations.
Register JdgDesc.obls_ok as sulfur.jdg.obls_ok.
Register JdgDesc.shapes as sulfur.jdg.shapes.
Register JdgDesc.jshape_of as sulfur.jdg.jshape_of.
Register JdgDesc.jdg_type as sulfur.jdg.jdg_type.
Register JdgDesc.sh_at as sulfur.jdg.sh_at.
Register JdgDesc.Idx as sulfur.jdg.jidx.
Register JdgDesc.jdg_at as sulfur.jdg.jdg_at.
Register JdgDesc.var_rules as sulfur.jdg.var_rules.
Register JdgDesc.make_obl as sulfur.jdg.make_obl.
Register finO as sulfur.fin.finO.
Register finS as sulfur.fin.finS.
Register JdgShape.t_term as sulfur.jdg.t_term.
Register JdgShape.t_base as sulfur.jdg.t_base.
Register JdgShape.sel_nil as sulfur.jdg.sel_nil.
Register JdgShape.sel_var as sulfur.jdg.sel_var.
Register JdgShape.sel_pos as sulfur.jdg.sel_pos.
Register JdgShape.pos0 as sulfur.jdg.pos0.
Register JdgShape.posS as sulfur.jdg.posS.
Register JdgDesc.hrule as sulfur.jdg.hrule.
Register JdgDesc.rule_desc_type as sulfur.jdg.rule_desc_type.
Register JdgDesc.var_rule_type as sulfur.jdg.var_rule_type.
Register JdgDesc.J as sulfur.jdg.J.
Register JdgDesc.wf_desc as sulfur.jdg.wf_desc.
Register JdgDesc.rules_type as sulfur.jdg.rules_type.
Register JdgDesc.sound_jdg as sulfur.jdg.sound_jdg.
Register JdgDesc.complete_jdg as sulfur.jdg.complete_jdg.
Register JdgDesc.preserve_subst_jdg as sulfur.jdg.preserve_subst_jdg.
Register JdgDesc.sound_of_ind as sulfur.jdg.sound_of_ind.
Register JdgDesc.jdg_complete as sulfur.jdg.jdg_complete.
Register JdgDesc.gen_preserve_subst as sulfur.jdg.gen_preserve_subst.
Register Stdlib.Lists.List.Forall_nil as sulfur.list.forall_nil.
Register Stdlib.Lists.List.Forall_cons as sulfur.list.forall_cons.
