open Constrexpr
open Constrexpr_ops

let qid (g : Names.GlobRef.t) : Libnames.qualid =
  Nametab.shortest_qualid_of_global Names.Id.Set.empty g

let gref (g : Names.GlobRef.t) : constr_expr = mkRefC (qid g)

let gref' (g : Names.GlobRef.t Lazy.t) : constr_expr = gref (Lazy.force g)

let hole : constr_expr = CAst.make (CHole None)

let app_expl (g : Names.GlobRef.t Lazy.t) (args : constr_expr list) : constr_expr =
  CAst.make (CAppExpl ((qid (Lazy.force g), None), args))

let lib (name : string) : constr_expr = gref (Rocqlib.lib_ref name)

(** A literal in scope [scope]. *)
let prim (scope : string) (p : prim_token) : constr_expr =
  CAst.make (CDelimiters (DelimUnboundedScope, scope, CAst.make (CPrim p)))

let nat (n : int) : constr_expr =
  prim "nat" (Number (NumTok.Signed.of_int_string (string_of_int n)))

let bool b =
  lib (if b then "core.bool.true" else "core.bool.false")

let ascii c =
  let n = Char.code c in
  mkAppC (
    lib "core.ascii.ascii",
    List.init 8 (fun i -> bool (n land (1 lsl i) <> 0))
  )

(* With the constructors rather than a literal: a literal needs [string_scope]
  open or delimited, i.e. [String] imported where the command runs. *)
let string (s : string) : constr_expr =
  String.fold_right
    (fun c acc -> mkAppC (lib "core.string.string", [ ascii c ; acc ]))
    s (lib "core.string.empty")

let list (xs : constr_expr list) : constr_expr =
  List.fold_right (fun x l ->
    mkAppC (lib "core.list.cons", [ x ; l ])
  ) xs (lib "core.list.nil")

let pair (a : constr_expr) (b : constr_expr) : constr_expr =
  mkAppC (lib "core.prod.intro", [ a ; b ])

let assum (xs : Names.lname list) (ty : constr_expr) : local_binder_expr =
  CLocalAssum (xs, None, Default Glob_term.Explicit, ty)

let is_ident (x : Names.Id.t) (e : constr_expr) : bool =
  match e.CAst.v with
  | CRef (q, None) ->
    Libnames.qualid_is_ident q && Names.Id.equal (Libnames.qualid_basename q) x
  | _ -> false

let rec arrows (ty : constr_expr) : constr_expr list * constr_expr =
  match ty.CAst.v with
  | CProdN (bs, c) ->
    let dom b =
      match b with
      | CLocalAssum (xs, _, _, d) -> List.map (fun _ -> d) xs
      | _ -> []
    in
    let ds, c = arrows c in
    (List.concat_map dom bs @ ds, c)
  | CNotation (_, (_, "_ → _"), ([ d ; c ], _, _, _)) ->
    let ds, c = arrows c in
    (d :: ds, c)
  | _ -> ([], ty)

let rec products (ty : constr_expr) : constr_expr list =
  match ty.CAst.v with
  | CNotation (_, (_, "_ * _"), ([ a ; b ], _, _, _)) -> products a @ products b
  | _ -> [ ty ]

let prod (tys : constr_expr list) : constr_expr =
  match List.rev tys with
  | [] -> lib "core.unit.type"
  | ty :: tys ->
    List.fold_left (fun acc ty ->
      mkAppC (lib "core.prod.type", [ ty ; acc ])
    ) ty tys
