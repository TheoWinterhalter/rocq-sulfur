(** Data obtained from [Jdg_parse] after validation, and the validation phase

  For instance, it extracts the context declarations hidden in the headers,
  putting it at the top-level.

  The idea is that most error messages should come from this module.

  TODO: prem_kinds, prem_jdg, …

*)

open Prelude
open Jdg_parse

type sel =
| SelVar
| SelPos of int

(* Single judgment *)
type sjdg = {
  sj_name : Names.Id.t ;
  sj_ctx : Names.Id.t ;
  sj_sel : sel list ;
  sj_type : Constrexpr.constr_expr
}

type jdg = {
  j_blocks : pblock list ; (* TODO REMOVE *)
  j_decl_comp : Constrexpr.constr_expr list ;
  j_name : Names.Id.t ;
  j_headers : pheader list ; (* TODO REMOVE *)
  j_jdgs : sjdg list
}

(** Which components of a declaration are selected to form the variable
  judgment *)
let selection (h : pheader) ncomp =
  let sel a =
    if Names.Id.equal a h.ph_var then SelVar
    else
      let ds = List.map (fun d -> d.CAst.v) h.ph_decls in
      match CList.index0 Names.Name.equal (Names.Name a) ds with
      | k -> SelPos k
      | exception Not_found ->
        Log.error
          "Sulfur Judgment: %s is neither the variable nor a declaration."
          (Names.Id.to_string a)
  in
  if not (Names.Id.equal h.ph_jdg h.ph_name) then
    Log.error "Sulfur Judgment: the variable rule must conclude %s."
      (Names.Id.to_string h.ph_name) ;
  if List.length h.ph_decls <> ncomp then begin
    let loc = Option.bind h.ph_decl (fun x -> x.CAst.loc) in
    Log.error ?loc
      "Sulfur Judgment: context %s of judgment %s declares %d component(s), \
       variable x d1 ... dn must name as many after the variable. \
       (Note: unit counts as no components.)"
      (Names.Id.to_string h.ph_ctx) (Names.Id.to_string h.ph_name) ncomp
  end ;
  List.map sel h.ph_args

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

(** The components of a declaration [Γ : d]: the factors of a product, none for
  [unit]. The context is a list of the library's tuples, [decl_type d]. *)
let decl_components (d : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  if Cexpr.is_ident (Names.Id.of_string "unit") d then [] else Cexpr.products d

let of_pblock ncomp (pb : pblock) =
  let sj_name = pb.pb_header.ph_name in
  let sj_ctx = pb.pb_header.ph_ctx in
  let sj_sel = selection pb.pb_header ncomp in
  let sj_type = pb.pb_header.ph_type in
  { sj_name ; sj_ctx ; sj_sel ; sj_type }

let of_pjdg (pj : pjdg) : jdg =
  let j_headers = List.map (fun b -> b.pb_header) pj in
  let decl = block_decl j_headers in
  let j_decl_comp = decl_components decl in
  let ncomp = List.length j_decl_comp in
  let j_name = (List.hd j_headers).ph_name in
  let j_jdgs = List.map (of_pblock ncomp) pj in
  { j_blocks = pj ; j_decl_comp ; j_headers ; j_name ; j_jdgs }
