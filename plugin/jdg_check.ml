(** Data obtained from [Jdg_parse] after validation, and the validation phase

  For now, it only extracts the context declarations hidden in the headers,
  putting it at the top-level.
  It contains redundant information, but computes it only once.

*)

open Prelude
open Jdg_parse
module C = Constants

type jdg = {
  j_blocks : pblock list ;
  j_decl : Constrexpr.constr_expr ;
  j_headers : pheader list ;
  j_name : Names.Id.t
}

(** Context declaration for a block of judgments.

  It comes from the [with context Γ of d] of the first judgment, for which it
  is mandatory. Subsequent judgments may mention it again, but only with
  syntactically equal declarations.
*)
let block_decl (hs : pheader list) : Constrexpr.constr_expr =
  let d =
    match (List.hd hs).ph_decl with
    | Some d -> d
    | None ->
      Log.error "Sulfur Judgment: the first judgment declares the context, \
                 [with context Γ of d]."
  in
  List.iter (fun h ->
    match h.ph_decl with
    | Some d' when not (Constrexpr_ops.constr_expr_eq d d') ->
      Log.error ?loc:d'.CAst.loc
        "Sulfur Judgment: the judgments of a block must all use the same \
         context declarations."
    | _ -> ()
  ) hs ;
  d

let of_pjdg (pj : pjdg) : jdg =
  let j_headers = List.map (fun b -> b.pb_header) pj in
  let j_decl = block_decl j_headers in
  let j_name = (List.hd j_headers).ph_name in
  { j_blocks = pj ; j_decl ; j_headers ; j_name }
