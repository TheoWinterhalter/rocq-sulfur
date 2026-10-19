open Prelude

(* Errors *)
exception Rel_gen_bug of string

(* Pre-checking structures *)
type pprem_r =
  | PPremInd of {
    pind : (* Name of the inductive we call *)
      Names.lident;
    pargs : (* Arguments of the inductive we call *)
      Constrexpr.constr_expr list ;
    pextension : (* Context extension *)
      Constrexpr.constr_expr list option ;
  }
  | PPremPred of {
    ppred : (* Predicate *)
      Constrexpr.constr_expr
  }
and pprem = pprem_r CAst.t

type parity_decl_r = {
  prel_name : (* Name of the relation we build *)
    Names.lident ;
  pdecl : (* Type of declarations stored in contexts *)
    Constrexpr.constr_expr ;
  parity : (* Arity of the relation we build *)
    Constrexpr.constr_expr list ;
  pctx_name : (* Name of contexts for the relation we build *)
    Names.lident ;
}
and parity_decl = parity_decl_r CAst.t

type prule_decl_r = {
  prule_name : (* Name of the rule we declare *)
    Names.lident ;
  pvars : (* Variables by which we abstract, of the form [(x : t)] *)
    (Names.lident * Constrexpr.constr_expr) list ;
    (* TODO : allow Constrexpr option *)
  pconclusion : (* Conclusion of the rule, as a name of an inductive with arguments *)
    Names.lident * Constrexpr.constr_expr list ;
  ppremises : (* List of premises of the rule *)
    pprem list
}
and prule_decl = prule_decl_r CAst.t

type rel_psignature_r = {
  parity_decls : (* All arities *)
    parity_decl list ;
  prule_decls : (* All rules *)
    prule_decl list
}
and rel_psignature = rel_psignature_r CAst.t

(* Post-checking structures ; the structure is similar to the one above *)
type prem =
  | PremInd of {
    ind : Names.variable;
    args : Evd.econstr list;
    extension : Evd.econstr option ;
  }
  | PremPred of {
    pred : Evd.econstr
  }

type arity_decl = {
  rel_name : Names.variable ;
  decl : Evd.econstr ;
  arity : Evd.econstr list ;
  ctx_name : Names.variable ;
}

type rule_decl = {
  rule_name : Names.variable ;
  decl : Evd.econstr ;
  vars : (Names.lident * Evd.econstr) list ;
  conclusion : Names.variable * Evd.econstr list ;
  premises : prem list ;
  ctx_name : Names.variable ;
}

type rel_signature = { arity_decls : arity_decl list ; rule_decls : rule_decl list }


(* Checking functions *)

(* Check that a variable is fresh in a signature ; TODO : also check in the environment *)
let check_fresh ?is_ctx_name:(is_ctx_name=false) (signature : rel_signature) (name : Names.lident) : unit =
  (* Check that we did not define a relation or a rule *)
  let b_rel = List.mem name.v (List.map (fun d -> d.rel_name) signature.arity_decls) in
  let b_rule = List.mem name.v (List.map (fun d -> d.rule_name) signature.rule_decls) in
  (* If we are not a context, checks that we do not have the same name as a context. Allows multiple contexts for different relations to have the same names *)
  let b_ctx = (not is_ctx_name) && List.mem name.v (List.map (fun (d : arity_decl) -> d.ctx_name) signature.arity_decls) in
  (* TODO : check in the global environment *)
  if b_rel || b_rule || b_ctx then
    Log.error ?loc:name.loc "%s is already declared." (Names.Id.to_string name.v);
  ()

(* Check an arity declaration and add its checked version to the current signature *)
let check_arity_decl (signature : rel_signature) (d : parity_decl) : rel_signature m =
  (* Check that the name is fresh *)
  check_fresh signature d.v.prel_name;
  (* Check that the context name is fresh *)
  check_fresh ~is_ctx_name:true signature d.v.pctx_name;
  (* Check that the context name is different than the name *)
  if (d.v.prel_name = d.v.pctx_name) then Log.error ?loc:d.v.pctx_name.loc "%s is the name of the relation." (Names.Id.to_string d.v.pctx_name.v);

  (* Typecheck the type of declarations *)
  let* tdecl = pretype d.v.pdecl in

  (* Typecheck all arities *)
  let* arity = List.monad_map pretype d.v.parity in

  (* Build the arity declaration *)
  let ad : arity_decl = {
    rel_name = d.v.prel_name.v ;
    decl = tdecl ;
    arity = arity ;
    ctx_name = d.v.pctx_name.v
  } in
  ret {
    arity_decls = ad::signature.arity_decls;
    rule_decls = signature.rule_decls
  }

(* Check something of the form [name arg1 ... argn], either a conclusion or a premise, and returns the the list of checked arguments *)
let check_app (signature : rel_signature) (ind : Names.lident) (args : Constrexpr.constr_expr list) : Evd.econstr list m =
  (* Check that the name of the inductive is something we defined *)
  let ad = List.find_opt (fun (d : arity_decl) -> d.rel_name = ind.v) signature.arity_decls in
  match ad with
  | None -> Log.error ?loc:ind.loc "%s is not a declared relation." (Names.Id.to_string ind.v)
  | Some _ -> ();
  let ad = Option.get ad in

  (* Check the arguments *)
  let* args = List.monad_map pretype args in

  (* Check that the arguments are indeed the right ones *)
  let* arg_types = List.monad_map retype args in
  (if arg_types <> ad.arity then Log.error ?loc:ind.loc "Bad arguments" ());
  ret args

let check_rule_decls (signature : rel_signature) (d : prule_decl) : rel_signature m =
  (* Check that the name is fresh *)
  check_fresh signature d.v.prule_name;

  (* Check that the conclusion is a declared relation and get the corresponding arity declaration *)
  let ad = List.find_opt (fun (ad : arity_decl) -> ad.rel_name = (fst d.v.pconclusion).v) signature.arity_decls in
  match ad with
  | None -> Log.error ?loc:(fst (d.v.pconclusion)).loc "%s is not a declared relation." (Names.Id.to_string (fst d.v.pconclusion).v)
  | Some _ -> ();
  let ad = Option.get ad in

  (* Get the type of declarations *)
  let tdecl = ad.decl in

  (* Check the variables and get the new environment *)
  let names = List.map fst d.v.pvars in

  let rec monad_map_with_env (l : (Names.lident * Constrexpr.constr_expr) list) : (Evd.econstr list * Constr.named_declaration list) m = match l with
  (* Redefine monad_map but slightly different since we change the local environment at each step *)
  | [] -> ret ([], [])
  | (x, t)::l ->
    let* t = pretype t in
    let annot = Context.make_annot x.v Sorts.Relevant in
    let* constr_t = (fun env sigma -> sigma, EConstr.to_constr sigma t) in
    let decl = Context.Named.Declaration.LocalAssum (annot, constr_t) in
    let* l, decls = with_env' (fun env -> Environ.push_named Environ.ProofVar decl env) @@ monad_map_with_env l in
    ret (t::l, decl::decls)
  in
  let* tvars, decls = monad_map_with_env d.v.pvars in
  let vars = List.combine names tvars in

  (* Add the new local environment *)
  with_env' (
  let rec aux ds env = match ds with
    | [] -> env
    | d::ds -> aux ds (Environ.push_named Environ.ProofVar d env)
    in aux decls
  ) @@
  (* Check the conclusion *)
  let* args_ccl = check_app signature (fst d.v.pconclusion) (snd (d.v.pconclusion)) in
  let ccl = (fst d.v.pconclusion).v in

  (* Check all premises *)
  let c_list = mkglob' Constants.list in
  let c_nil = mkglob' Constants.nil in
  let c_cons = mkglob' Constants.cons in

  let* premises = List.monad_map (fun (p : pprem) -> match p.v with
    | PPremPred p ->
      (* Abstract the context by adding it to the local environment *)
      let annot = Context.make_annot ad.ctx_name Sorts.Relevant in
      let* constr = fun env sigma -> sigma, EConstr.to_constr sigma (app c_list ad.decl) in
      let decl = Context.Named.Declaration.LocalAssum (annot, constr) in
      with_env' (fun env -> Environ.push_named Environ.ProofVar decl env) @@
      (* Typecheck the predicate *)
      let* p = pretype p.ppred in
      ret (PremPred {pred = p})
    | PPremInd p_ind ->
      (* Check the arguments *)
      let* args = check_app signature p_ind.pind p_ind.pargs in
      (* Check the extension *)
      let* ext = match p_ind.pextension with
      | None -> ret None
      | Some e ->
        (* Builds a Rocq list from the OCaml list [e] *)
        let* e = List.monad_fold_left (fun (e : Evd.econstr) (d : Constrexpr.constr_expr) ->
          (* Check d *)
          let* d = pretype d in
          let* type_d = retype d in
          if type_d <> tdecl then Log.error ?loc:p.loc "Wrong extension type" ();
          (* Adds it to the Rocq list *)
          ret (apps c_cons [|tdecl ; d ; e|])
        ) (app c_nil tdecl) e in
        ret (Some e)
      in
      ret (PremInd {ind = p_ind.pind.v ; args = args ; extension = ext})
  ) (d.v.ppremises) in

  (* Build the rule declaration *)
  let r : rule_decl = {
    rule_name = d.v.prule_name.v ;
    decl = tdecl ;
    vars = vars ;
    conclusion = (ccl, args_ccl) ;
    premises = premises ;
    ctx_name = ad.ctx_name ;
  } in
  ret {
    arity_decls = signature.arity_decls ;
    rule_decls = r::signature.rule_decls
  }

(* Check the whole signature *)
let check_psig (s : rel_psignature) : rel_signature m =
  (* Initial empty signature *)
  let signature = {
    arity_decls = [] ;
    rule_decls = []
  } in
  (* Check arities *)
  let* signature = List.monad_fold_left check_arity_decl signature (s.v.parity_decls) in
  (* Check rules *)
  let* signature = List.monad_fold_left check_rule_decls signature (s.v.prule_decls) in
  ret {
    (* The order is reversed *)
    arity_decls = List.rev signature.arity_decls ;
    rule_decls = signature.rule_decls
  }

(* Building the inductive *)

(* Creates the type of a rule, with the right format for [declare_mut_ind] *)
let make_rule_type (name_assoc : (Names.variable * int) list) (ctx_type : Evd.econstr) (d : rule_decl) : Names.variable list -> Evd.econstr m = fun inds ->
  (* Build the conclusion type *)
  let concl_name = List.nth inds (List.assoc (fst d.conclusion) name_assoc) in
  let args = Array.of_list (
    (EConstr.mkVar d.ctx_name):: (snd d.conclusion)
  ) in
  let conclusion = apps (EConstr.mkVar concl_name) args in

  (* Build the list of arrows *)
  let c_app = mkglob' Constants.app in
  let hyps = List.map (fun (p : prem) -> match p with
    | PremPred p -> p.pred
    | PremInd p ->
      (* Finds the element of the list [ind] that correspond to the name of the inductive in the premise *)
      let ind = List.nth inds (List.assoc p.ind name_assoc) in
      (* Create the extended context and adds it to the arguments *)
      let new_ctx = match p.extension with
      | None -> EConstr.mkVar d.ctx_name
      | Some e -> apps c_app [|d.decl ; e ; EConstr.mkVar d.ctx_name|]
      in
      let args = Array.of_list (new_ctx :: p.args) in
      apps (EConstr.mkVar ind) args
  ) d.premises in
  let free_arrow = arrows hyps conclusion in

  (* Build the product *)
  (* Add the context to variables *)
  let vars = (CAst.make d.ctx_name, ctx_type)::(d.vars) in
  let rule_type = List.fold_right (fun (x, t : Names.lident * Evd.econstr) (rt : Evd.econstr) ->
    let x_annot = Context.make_annot x.v EConstr.ERelevance.relevant in
    EConstr.mkNamedProd (Evd.from_env (Global.env ())) x_annot t rt
  ) vars free_arrow in
  ret rule_type

(* For every [d : rule_decl] in [l], puts [f d] in the list at the place in [a] that corresponds to the conclusion of [d] *)
let rec sort_by_conclusion (assoc : (Names.variable * int) list) (a : 'a list array) (f : rule_decl -> 'a) (l : rule_decl list) : unit = match l with
| [] -> ()
| d::l ->
  let i = List.assoc (fst d.conclusion) assoc in
  Array.set a i ((f d) :: a.(i));
  sort_by_conclusion assoc a f l

(* Main function to build the inductive relation *)
let build_inductive (signature : rel_signature) : Names.MutInd.t m =
  (* Build all relation names *)
  let rel_names = List.map (fun d -> d.rel_name) signature.arity_decls in

  (* Build all relation arities *)
  let c_list = mkglob' Constants.list in
  let rel_arities = List.map (fun (d : arity_decl) ->
    arrows ((app c_list d.decl)::d.arity) EConstr.mkProp
  ) signature.arity_decls in

  (* Rules *)
  let rel_names_assoc = List.mapi (fun i n -> n, i) rel_names in
  let rule_names_arr : Names.variable list array = Array.make (List.length rel_names) [] in
  let rule_types_arr : (Names.variable list -> Evd.econstr m) list array = Array.make (List.length rel_names) [] in

  sort_by_conclusion rel_names_assoc rule_types_arr (fun (d : rule_decl) ->
    make_rule_type rel_names_assoc (app c_list d.decl) d
  ) (signature.rule_decls);
  sort_by_conclusion rel_names_assoc rule_names_arr (fun (d : rule_decl) -> d.rule_name) (signature.rule_decls);

  let rule_names = Array.to_list rule_names_arr in
  let rule_types = Array.to_list rule_types_arr in

  declare_mut_ind rel_names rel_arities rule_names rule_types

(* Main function *)
let main (s : rel_psignature) : unit =
  (* Check the signature *)
  let signature = monad_run @@ check_psig s in
  (* Build the inductive *)
  let _ = monad_run @@ build_inductive signature in
  ()