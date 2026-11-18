(** Data parsed by the [Sulfur Judgment] command.

  See [g_plugin.mlg] for the grammar of the command.
*)

open Prelude
module C = Constants

type pheader = {
  ph_name : Names.Id.t ;
  ph_type : Constrexpr.constr_expr ;
  ph_ctx : Names.Id.t ;
  ph_decl : Constrexpr.constr_expr option ;
  ph_var : Names.Id.t ;
  ph_decls : Names.lname list ;
  ph_jdg : Names.Id.t ;
  ph_args : Names.Id.t list
}

type prem =
| PJdg of Constrexpr.constr_expr
| PPred of Constrexpr.constr_expr

type prule = {
  pr_name : Names.Id.t ;
  pr_binders : Constrexpr.local_binder_expr list ;
  pr_prems : prem list ;
  pr_concl : Constrexpr.constr_expr
}

type pblock = {
  pb_header : pheader ;
  pb_rules : prule list
}

type pjdg = pblock list
