(** Data obtained from [Jdg_parse] after validation, and the validation phase

  For instance, it extracts the context declarations hidden in the headers,
  putting it at the top-level.

  The idea is that most error messages should come from this module.

*)

open Prelude
open Jdg_parse

type binder =
| BMeta of Names.lname * int
| BParam of Names.lname * Constrexpr.constr_expr

type prem =
| Jdg of int * Constrexpr.constr_expr
| Pred of Constrexpr.constr_expr

type rule = {
  r_name : Names.Id.t ;
  r_binders : binder list ;
  r_prems : prem list ;
  r_concl : Constrexpr.constr_expr
}

type sel =
| SelVar
| SelPos of int

type arg =
| Term
| Base of Constrexpr.constr_expr

(* Single judgment *)
type sjdg = {
  sj_name : Names.Id.t ;
  sj_ctx : Names.Id.t ;
  sj_sel : sel list ;
  sj_args : arg list ;
  sj_rules : rule list
}

type jdg = {
  j_decl : Constrexpr.constr_expr ;
  j_decl_comp : arg list ;
  j_name : Names.Id.t ;
  j_jdgs : sjdg list ;
  j_names : Names.Id.t list
}

(** The arity of a meta-variable type [sort → ... → sort], if it is one *)
let arity (sort : Names.Id.t) (ty : Constrexpr.constr_expr) : int option =
  let ds, c = Cexpr.arrows ty in
  if Cexpr.is_ident sort c && List.for_all (Cexpr.is_ident sort) ds
  then Some (List.length ds)
  else None

let to_binders sort (pb : Constrexpr.local_binder_expr) : binder list =
  match pb with
  (* Holes are converted to the sort *)
  | Constrexpr.CLocalAssum (xs, _, _, { CAst.v = Constrexpr.CHole _ ; _ }) ->
    List.map (fun x -> BMeta (x, 0)) xs
  | Constrexpr.CLocalAssum (xs, _, _, ty) ->
    begin match arity sort ty with
    | Some n -> List.map (fun x -> BMeta (x, n)) xs
    | None when Constrexpr_ops.occur_var_constr_expr sort ty ->
      Log.error ?loc:ty.CAst.loc
        "A parameter type cannot mention the sort %s."
        (Names.Id.to_string sort)
    | None -> List.map (fun x -> BParam (x, ty)) xs
    end
  | Constrexpr.CLocalDef ({ CAst.loc ; _ }, _, _, _)
  | Constrexpr.CLocalPattern { CAst.loc ; _ } ->
    Log.error ?loc "Rule binders must be assumptions (x : A)."

(** The judgment of a premise [R t u] or [⟨ x ↦ A ⊢ R t u ⟩], by its head,
  among the judgments [names] of the block *)
let rec prem_jdg (names : Names.Id.t list) (e : Constrexpr.constr_expr) : int =
  match e.CAst.v with
  | Constrexpr.CNotation (_, (_, "⟨ _ ↦ _ ⊢ _ ⟩"), ([ _ ; p ], _, _, _)) ->
    prem_jdg names p
  | _ ->
    let head = match e.CAst.v with Constrexpr.CApp (f, _) -> f | _ -> e in
    let rec index k = function
      | [] ->
        Log.error ?loc:e.CAst.loc
          "Sulfur Judgment: a premise is a judgment of the block, or {{ P }}."
      | n :: ns -> if Cexpr.is_ident n head then k else index (k + 1) ns
    in
    index 0 names

let of_pprem names (p : pprem) : prem =
  match p with
  | PPred e -> Pred e
  | PJdg e -> Jdg (prem_jdg names e, e)

(** A rule of the [k]th judgment of the block, which it must conclude *)
let of_prule sort names k (pr : prule) : rule =
  if prem_jdg names pr.pr_concl <> k then begin
    let s = Names.Id.to_string (List.nth names k) in
    Log.error ?loc:pr.pr_concl.CAst.loc
      "Sulfur Judgment: a rule of %s must conclude %s." s s
  end ;
  let r_binders = List.concat_map (to_binders sort) pr.pr_binders in
  let r_prems = List.map (of_pprem names) pr.pr_prems in
  { r_name = pr.pr_name ; r_binders ; r_prems ; r_concl = pr.pr_concl }

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

let to_arg sort ty =
  if Cexpr.is_ident sort ty then Term
  else Base ty

let to_args sort ty =
  let (args, st) = Cexpr.arrows ty in
  begin match st.CAst.v with
  | Constrexpr.CSort s
    when Constrexpr_ops.sort_expr_eq s Constrexpr_ops.expr_Prop_sort -> ()
  | _ ->
    Log.error ?loc:st.CAst.loc
      "Sulfur Judgment: a judgment is a relation, its type must end in Prop."
  end ;
  List.map (to_arg sort) args

let of_pblock sort names ncomp k (pb : pblock) =
  let sj_name = pb.pb_header.ph_name in
  let sj_ctx = pb.pb_header.ph_ctx in
  let sj_sel = selection pb.pb_header ncomp in
  let sj_args = to_args sort pb.pb_header.ph_type in
  let sj_rules = List.map (of_prule sort names k) pb.pb_rules in
  { sj_name ; sj_ctx ; sj_sel ; sj_args ; sj_rules }

let saved_ops () =
  match !Main.saved_ops with
  | Some x -> x
  | None -> Log.error "Sulfur Judgment: no syntax was generated beforehand."

let of_pjdg (pj : pjdg) : jdg =
  let sign, _ = saved_ops () in
  let sort = sign.Signature.sort_name in
  let j_headers = List.map (fun b -> b.pb_header) pj in
  let j_names = List.map (fun h -> h.ph_name) j_headers in
  let j_decl = block_decl j_headers in
  let comp = decl_components j_decl in
  let j_decl_comp = List.map (to_arg sort) comp in
  let ncomp = List.length comp in
  let j_name = (List.hd j_headers).ph_name in
  let j_jdgs = List.mapi (of_pblock sort j_names ncomp) pj in
  { j_decl ; j_decl_comp ; j_name ; j_jdgs ; j_names }
