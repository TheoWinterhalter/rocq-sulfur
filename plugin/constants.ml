(** This module defines Rocq constants we need to access from OCaml. Rocq constants are
    registered in [theories/Constants.v] using the command [Register ... as ...]. *)

(** We have to wait until Rocq is initialized before calling [Rocqlib.lib_ref], hence the
    use of [Lazy.t]. *)
let resolve (ref : string) : Names.GlobRef.t Lazy.t = lazy (Rocqlib.lib_ref ref)

(**************************************************************************************)
(** *** Basic constants. *)
(**************************************************************************************)

let unit = resolve "sulfur.unit.type"
let tt = resolve "sulfur.unit.tt"
let prod = resolve "sulfur.prod.type"
let pair = resolve "sulfur.prod.pair"
let nat = resolve "sulfur.nat.type"
let zero = resolve "sulfur.nat.zero"
let succ = resolve "sulfur.nat.succ"
let list = resolve "sulfur.list.type"
let nil = resolve "sulfur.list.nil"
let cons = resolve "sulfur.list.cons"
let app = resolve "sulfur.list.app"
let string = resolve "sulfur.string.type"
let eq = resolve "sulfur.eq.type"
let eq_refl = resolve "sulfur.eq.refl"
let eq_sym = resolve "sulfur.eq.sym"
let eq_trans = resolve "sulfur.eq.trans"
let eq1 = resolve "sulfur.eq1.type"
let eq1_refl = resolve "sulfur.eq1.refl"
let eq1_sym = resolve "sulfur.eq1.sym"
let eq1_trans = resolve "sulfur.eq1.trans"

(** Prelude  *)

let mkenum = resolve "sulfur.enum.make"
let enum_all_in = resolve "sulfur.enum.all_in"

(**************************************************************************************)
(** *** Renamings. *)
(**************************************************************************************)

let ren = resolve "sulfur.ren.type"
let rid = resolve "sulfur.ren.rid"
let rshift = resolve "sulfur.ren.rshift"
let rcons = resolve "sulfur.ren.rcons"
let rcomp = resolve "sulfur.ren.rcomp"
let up_ren = resolve "sulfur.ren.up_ren"
let congr_rcons = resolve "sulfur.ren.congr_rcons"
let congr_rcomp = resolve "sulfur.ren.congr_rcomp"
let congr_up_ren = resolve "sulfur.ren.congr_up_ren"

(**************************************************************************************)
(** *** Signatures. *)
(**************************************************************************************)

let arg_ty = resolve "sulfur.arg_ty.type"
let at_base = resolve "sulfur.arg_ty.base"
let at_term = resolve "sulfur.arg_ty.term"
let at_bind = resolve "sulfur.arg_ty.bind"
let kind = resolve "sulfur.kind.type"
let k_t = resolve "sulfur.kind.t"
let k_a = resolve "sulfur.kind.a"
let k_al = resolve "sulfur.kind.al"
let signature = resolve "sulfur.signature.type"
let build_signature = resolve "sulfur.signature.ctor"

(**************************************************************************************)
(** *** Parameterized syntax. *)
(**************************************************************************************)

module P = struct
  let expr = resolve "sulfur.param.expr.type"
  let e_var = resolve "sulfur.param.expr.var"
  let e_ctor = resolve "sulfur.param.expr.ctor"
  let e_al_nil = resolve "sulfur.param.expr.al_nil"
  let e_al_cons = resolve "sulfur.param.expr.al_cons"
  let e_abase = resolve "sulfur.param.expr.abase"
  let e_aterm = resolve "sulfur.param.expr.aterm"
  let e_abind = resolve "sulfur.param.expr.abind"
  let subst = resolve "sulfur.param.subst"
  let rename = resolve "sulfur.param.rename"
  let substitute = resolve "sulfur.param.substitute"
  let sid = resolve "sulfur.param.sid"
  let sshift = resolve "sulfur.param.sshift"
  let scons = resolve "sulfur.param.scons"
  let up_subst = resolve "sulfur.param.up_subst"
  let scomp = resolve "sulfur.param.scomp"
  let rscomp = resolve "sulfur.param.rscomp"
  let srcomp = resolve "sulfur.param.srcomp"
  let inv_Kal_nil = resolve "sulfur.param.inv_Kal_nil"
  let inv_Kal_cons = resolve "sulfur.param.inv_Kal_cons"
  let inv_Ka_term = resolve "sulfur.param.inv_Ka_term"
  let inv_Ka_base = resolve "sulfur.param.inv_Ka_base"
  let inv_Ka_bind = resolve "sulfur.param.inv_Ka_bind"
  let sig_ind_t = resolve "sulfur.param.sig_ind_t"
  let sig_ind = resolve "sulfur.param.sig_ind"
end

(**************************************************************************************)
(** *** ConcreteSyntax class. *)
(**************************************************************************************)

module CS = struct
  let carg = resolve "sulfur.cs.carg"
  let cargs = resolve "sulfur.cs.cargs"
  let ckind = resolve "sulfur.cs.ckind"
  let build = resolve "sulfur.cs.build"
  let laws = resolve "sulfur.cs.laws"
  let csubstitute = resolve "sulfur.cs.csubstitute"
  let typ = resolve "sulfur.cs.type"
end

(**************************************************************************************)
(** *** Judgment descriptions (theories/JdgDesc.v). *)
(**************************************************************************************)

module Jdg = struct
  let rule_desc = resolve "sulfur.jdg.rule_desc"
  let build_rule_desc = resolve "sulfur.jdg.build_rule_desc"
  let jdg_desc = resolve "sulfur.jdg.jdg_desc"
  let happly = resolve "sulfur.jdg.happly"
  let hterm = resolve "sulfur.jdg.hterm"
  let hctor = resolve "sulfur.jdg.hctor"
  let hjdg = resolve "sulfur.jdg.hjdg"
  let hrule = resolve "sulfur.jdg.hrule"
  let rule_desc_type = resolve "sulfur.jdg.rule_desc_type"
  let var_rule_type = resolve "sulfur.jdg.var_rule_type"
  let j = resolve "sulfur.jdg.J"
  let wf_desc = resolve "sulfur.jdg.wf_desc"
  let rules_type = resolve "sulfur.jdg.rules_type"
  let sound_jdg = resolve "sulfur.jdg.sound_jdg"
  let complete_jdg = resolve "sulfur.jdg.complete_jdg"
  let preserve_subst_jdg = resolve "sulfur.jdg.preserve_subst_jdg"
  let sound_of_ind = resolve "sulfur.jdg.sound_of_ind"
  let jdg_complete = resolve "sulfur.jdg.jdg_complete"
  let gen_preserve_subst = resolve "sulfur.jdg.gen_preserve_subst"
  let forall_nil = resolve "sulfur.list.forall_nil"
  let forall_cons = resolve "sulfur.list.forall_cons"
end
