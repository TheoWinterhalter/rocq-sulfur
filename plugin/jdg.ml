(** Implementation of the [Sulfur Judgment] command

  [Sulfur Judgment J d] expects [J] to be a new identifier and
  [d : JdgDesc.jdg_desc] to be a judgment description over a syntax generated
  from [Sulfur Syntax].

  It declared [J] as an inductive type and prove it equivalent with respect to
  the corresponding signature (also derived from [d]).

  This file mostly reassembles stuff from [JdgDesc].

*)

open Prelude

module C = Constants

(** The command *)

let generate (name : Names.Id.t) (desc_expr : Constrexpr.constr_expr) : unit =
  ()
