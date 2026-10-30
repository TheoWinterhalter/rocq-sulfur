(** This file defines the OCaml representation of signatures, as well utilities
  for parsing and validating signatures written by the user. *)

open Prelude
module C = Constants

(**************************************************************************************)
(** *** Pre-signature. *)
(**************************************************************************************)

(** A pre-signature is the parse tree of a user-written signature: declarations
  [name : ty], the first one being the sort [term (Var) : Type]. Types are Rocq
  terms, elaborated by [check_psignature] with the sort as a local variable,
  once the global environment is available. *)

(** Declaration.

  Either a sort declaration eg, [term (Var) : Type], or a constructor
  [app : term -> term -> term].

*)
type decl_r = {
  name : Names.lident ;
  var_ctor : Names.lident option ;
  ty : Constrexpr.constr_expr
}

and decl = decl_r CAst.t

(** Pre-signature. *)
type psignature_r = { decls : decl list }

and psignature = psignature_r CAst.t

(**************************************************************************************)
(** *** Signature. *)
(**************************************************************************************)

(** Argument type.
    - [AT_base] contains the index of the base type in the [base_types] array. *)
type arg_ty = AT_base of int | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [sort] is the name of the (unique) sort of terms.
    - [var_ctor] is the name of the variable constructor.
    - [base_types] contains the list of base types.
    - [n_ctors] is the number of _non-variable_ constructors.
    - [ctor_names] (of length [n_ctors]) contains the name of each constructor.
    - [ctor_sig] (of length [n_ctors]) contains the argument types of each constructor. *)
type signature =
  { sort_name : Names.Id.t
  ; var_ctor_name : Names.Id.t
  ; base_types : EConstr.t array
  ; n_ctors : int
  ; ctor_names : Names.Id.t array
  ; ctor_types : arg_ty list array
  }

(** [arg_ty_constr sign ty ind] builds the [EConstr.t] corresponding to [ty]. We use [ind]
    as a placeholder for the inductive type of terms. *)
let rec arg_ty_constr (sign : signature) (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with
  | AT_base i -> sign.base_types.(i)
  | AT_term -> ind
  | AT_bind ty -> arg_ty_constr sign ty ind

(** [ctor_ty_constr sign tys ind] builds the type of a constructor as a [EConstr.t]. We
    use [ind] as a placeholder for the inductive type of terms. *)
let ctor_ty_constr (sign : signature) (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr sign ty ind) tys) ind

(**************************************************************************************)
(** *** Checking a pre-signature. *)
(**************************************************************************************)

(** Check a pre-signature is well formed. Checking a pre-signature is done when evaluating
    the command [Sulfur Syntax ...]. We can't check a signature during parsing because
    we need access to the global environment. *)

type checked_sort = { sname : Names.Id.t; var_ctor : Names.Id.t }
type checked_ctor = { cname : Names.Id.t; arg_tys : arg_ty list }

(** State we maintain while validating a pre-signature. *)
type state = {
  (* The (unique) sort, or [None] if we haven't encountered it yet. *)
  sort : checked_sort option ;
  (* The list of declared constructors, most recent last. *)
  ctors : checked_ctor list ;
  (* The list of base types, most recent last. *)
  base_types : EConstr.t list
}

(** Check a name is fresh, i.e. it is not already present in the state. *)
let check_fresh (st : state) (name : Names.lident) : unit =
  let b1 = List.exists (fun c -> Names.Id.equal name.v c.cname) st.ctors in
  let b2 =
    match st.sort with
    | None -> false
    | Some s -> Names.Id.equal name.v s.sname || Names.Id.equal name.v s.var_ctor
  in
  (* TODO: check in the global env as well. *)
  if b1 || b2
  then Log.error ?loc:name.loc "%s is already declared." (Names.Id.to_string name.v)

(** Read an argument type from the domain [d] of a constructor type, where
  [sort] is the local variable standing for the sort: the sort itself, a binder
  [sort -> .. -> ty], or any other (closed) type, which is a base type.
  [invalid ()] reports an error. *)
let rec check_arg (sort : Names.Id.t) (invalid : unit -> state * arg_ty)
    (st : state) (d : EConstr.t) : (state * arg_ty) m =
  let* env = get_env in
  let* sigma = get_sigma in
  let is_sort t = EConstr.isVarId sigma sort t in
  let binders, body = EConstr.decompose_prod sigma d in
  if is_sort d
  then ret (st, AT_term)
  else if binders <> [] && List.for_all (fun (_, t) -> is_sort t) binders
  then
    let* st, ty = check_arg sort invalid st body in
    ret (st, List.fold_left (fun ty _ -> AT_bind ty) ty binders)
  else if EConstr.Vars.closed0 sigma d && not (Termops.occur_var env sigma sort d)
  then
    let idx = List.length st.base_types in
    ret ({ st with base_types = d :: st.base_types }, AT_base idx)
  else ret (invalid ())

(** Check a declaration. *)
let check_decl (st : state) (d : decl) : state m =
  check_fresh st d.v.name ;
  match st.sort, d.v.ty.CAst.v with
  (* The first declaration is the sort. *)
  | None, Constrexpr.CSort _ ->
      let var_ctor =
        match d.v.var_ctor with
        | None -> Names.Id.of_string_soft "var"
        | Some var -> var.v
      in
      ret { st with sort = Some { sname = d.v.name.v ; var_ctor } }
  | None, _ -> Log.error ?loc:d.loc "The sort must be declared first."
  | Some _, Constrexpr.CSort _ ->
      Log.error ?loc:d.loc "Only one sort can be declared."
  (* Constructor declaration: elaborate its type with the sort as a local
    variable. *)
  | Some sort, _ ->
      let* univ = fresh_type in
      let name = Names.Name sort.sname in
      let annot = Context.make_annot name EConstr.ERelevance.relevant in
      with_local_decl (Context.Rel.Declaration.LocalAssum (annot, univ)) @@ fun sort ->
      let* ty = pretype_type d.v.ty in
      let* env = get_env in
      let* sigma = get_sigma in
      let invalid () =
        Log.error ?loc:d.loc
          "Invalid constructor type %s: it must be [a1 -> .. -> an -> %s] where \
           each argument is the sort, a binder [%s -> .. -> a] or a base type \
           that does not depend on the other arguments."
          (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma ty))
          (Names.Id.to_string sort) (Names.Id.to_string sort)
      in
      let binders, body = EConstr.decompose_prod sigma ty in
      if not (EConstr.isVarId sigma sort body) then ignore (invalid ()) ;
      let* st, tys =
        List.monad_fold_left
          (fun (st, tys) (_, dom) ->
            let* st, ty = check_arg sort invalid st dom in
            ret (st, ty :: tys))
          (st, []) (List.rev binders)
      in
      let ctor = { cname = d.v.name.v ; arg_tys = List.rev tys } in
      ret { st with ctors = ctor :: st.ctors }

(** Check a pre-signature. Raises an error (using Rocq's error reporting
  mechanism) if the pre-signature is not valid. *)
let check_psignature (s : psignature) : signature m =
  let st = { sort = None ; ctors = [] ; base_types = [] } in
  let* st = List.monad_fold_left check_decl st s.v.decls in
  (* The lists were built most recent first. *)
  let ctors = List.rev st.ctors in
  let base_types = List.rev st.base_types in
  let sort =
    match st.sort with
    | Some s -> s
    | None -> Log.error ?loc:s.loc "At least one sort must be declared."
  in
  ret {
    sort_name = sort.sname ;
    var_ctor_name = sort.var_ctor ;
    n_ctors = List.length ctors ;
    base_types = Array.of_list base_types ;
    ctor_names = ctors |> List.map (fun c -> c.cname) |> Array.of_list ;
    ctor_types = ctors |> List.map (fun c -> c.arg_tys) |> Array.of_list
  }
