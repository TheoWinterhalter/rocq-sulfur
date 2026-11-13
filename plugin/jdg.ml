(** Implementation of the [Sulfur Judgment] command.

  See [g_plugin.mlg] for the grammar of the command.

  Everything is stated and proven in [theories/JdgDesc.v]:
  this file only computes the constructor types by reduction, and instantiates
  the generic lemmas.
*)

open Prelude
module C = Constants

(** The header of a judgment, see [g_plugin.mlg]. *)
type header = {
  ph_name : Names.Id.t ;
  ph_type : Constrexpr.constr_expr ;
  ph_ctx : Names.Id.t ;
  ph_decl : Constrexpr.constr_expr ;
  ph_var : Names.Id.t ;
  ph_decls : Names.lname list ;
  ph_jdg : Names.Id.t ;
  ph_args : Names.Id.t list
}

(** A premise as written: a judgment, or [{{ P }}]. *)
type prem =
| PJdg of Constrexpr.constr_expr
| PPred of Constrexpr.constr_expr

(** A rule as written in the command:
  [| name (x1 ... : t1) ... : p1 ; ... ; pn ⟹ c].
*)
type prule = {
  pr_name : Names.Id.t ;
  pr_binders : Constrexpr.local_binder_expr list ;
  pr_prems : prem list ;
  pr_concl : Constrexpr.constr_expr
}

(** A rule for the generation:
  its term in the description, its name, its judgment, the names of its binders
  and for each premise its judgment ([None] for a predicate). *)
type rule = {
  r_term : EConstr.t ;
  r_name : string ;
  r_jdg : int ;
  r_binders : string list ;
  r_prems : int option list
}

let binder_names (bs : Constrexpr.local_binder_expr list) : string list =
  bs |> List.concat_map @@ fun b ->
    match b with
    | Constrexpr.CLocalAssum (xs, _, _, _) ->
      List.map (fun x ->
        match x.CAst.v with
        | Names.Name id -> Names.Id.to_string id
        | Names.Anonymous -> "x"
      ) xs
    | _ -> []

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

let prem_kinds (names : Names.Id.t list) (ps : prem list) : int option list =
  List.map (fun p ->
    match p with PPred _ -> None | PJdg e -> Some (prem_jdg names e)
  ) ps

(** The rule [r] of the [k]th judgment, with its term [t] *)
let rule_of (names : Names.Id.t list) (k : int) (t : EConstr.t) (r : prule) = {
  r_term = t ;
  r_name = Names.Id.to_string r.pr_name ;
  r_jdg = k ;
  r_binders = binder_names r.pr_binders ;
  r_prems = prem_kinds names r.pr_prems
}

(** The signature, term type and shapes of a description, from its type
  [jdg_desc sg T sh]. *)
let decode_sig (desc_ty : EConstr.t) : (EConstr.t * EConstr.t * EConstr.t) m =
  let what = "a judgment description" in
  decode what
    [
      C.prod, fun a ->
        decode what
          [
            C.list, fun a ->
              decode what
                [ C.Jdg.rule_desc, fun a -> ret (a.(0), a.(1), a.(2)) ]
                a.(0)
          ]
          a.(0)
    ]
    desc_ty

(** The rule terms of a description [(l1, (l2, ... tt))], judgment by
  judgment. *)
let rec decode_desc (t : EConstr.t) : EConstr.t list list m =
  decode "a judgment description"
    [
      C.pair, (fun a ->
        let* l = decode_list a.(2) in
        let* ls = decode_desc a.(3) in
        ret (l :: ls)) ;
      C.tt, (fun _ -> ret [])
    ]
    t

(** The values of the fields of a [ConcreteSyntax] instance, except [cctor]. *)
let decode_cs_ops (cs : EConstr.t) : EConstr.t list m =
  decode "a ConcreteSyntax instance"
    [ C.CS.build, fun a -> ret [ a.(2) ; a.(3) ; a.(4) ; a.(5) ; a.(6) ] ]
    cs

(** The index [k] of a judgment among [n], as a term of [fin n]. *)
let fin (n : int) (k : int) : EConstr.t =
  let rec go m k =
    if k = 0 then app (mkglob' C.Jdg.finO) (mknat m)
    else apps (mkglob' C.Jdg.finS) [| mknat m ; go (m - 1) (k - 1) |]
  in
  go (n - 1) k

(** [(x1, (x2, ... tt))] for the terms [xs], given with their types. *)
let tuple (xs : (EConstr.t * EConstr.t) list) : EConstr.t =
  let rec go = function
    | [] -> (mkglob' C.tt, mkglob' C.unit)
    | (x, ty) :: rest ->
      let r, rty = go rest in
      apps (mkglob' C.pair) [| ty ; rty ; x ; r |],
      apps (mkglob' C.prod) [| ty ; rty |]
  in
  fst (go xs)

(** The judgments of [blocks], described by [desc]: the inductives, then the
  lemmas. The shared lemmas are named after the first judgment. *)
let generate_desc (blocks : (header * prule list) list) (desc : EConstr.t) :
  unit =
  let names = List.map (fun (h, _) -> h.ph_name) blocks in
  (* The rules as written, with the index of their judgment *)
  let prs =
    List.mapi (fun k (_, rs) -> List.map (fun r -> (k, r)) rs) blocks
    |> List.concat
  in
  let mkj name s = Names.Id.of_string_soft (Names.Id.to_string name ^ s) in
  let mk = mkj (List.hd names) in
  let sname = Names.Id.to_string (List.hd names) in
  let locate id = Nametab.locate_constant (Libnames.qualid_of_ident id) in
  (* [map] over a variable context, in a predicate, keeps its name *)
  let reduce_only = reduce_only ~refold:[ const_of_ref (Lazy.force C.map) ] in
  let n = List.length names in
  let ks = List.init n (fun k -> k) in
  let fin = fin n in
  (* The signature of the description, the term type, the shapes, the instance
     and its laws, the rules. *)
  let sg, ty, sh, cs, cl, rules =
    monad_run begin
      let* desc_ty = typecheck desc None in
      let* sg, ty, sh = decode_sig desc_ty in
      let* cs = resolve_tc (apps (mkglob' C.CS.typ) [| sg ; ty |]) in
      let* cl = resolve_tc (apps (mkglob' C.CS.laws) [| sg ; ty ; cs |]) in
      let* terms = decode_desc desc in
      let terms = List.concat terms in
      let rules = List.map2 (fun (k, r) t -> rule_of names k t r) prs terms in
      ret (sg, ty, sh, cs, cl, rules)
    end
  in
  let jdg s = apps (mkglob' s) [| sg ; ty ; cs ; sh |] in
  let jdg_type = apps (mkglob' C.Jdg.jdg_type) [| sh ; ty |] in
  (* The type of the rules of judgment [k] *)
  let rule_desc_ty k =
    let sh_at = apps (mkglob' C.Jdg.sh_at) [| sh ; fin k |] in
    apps (mkglob' C.Jdg.rule_desc) [| sg ; ty ; sh ; sh_at |]
  in
  (* The constants the statements may unfold, the types of the relations (from
    the shapes) and of their contexts. *)
  let transparent, arities, ctx_ty =
    monad_run begin
      (* The constants which stay folded in the statements: the description, the
        operations of the syntax, the renamings, the lifting of substitutions,
        the generic judgment [J], and [Nat.sub] which would otherwise pollute
        [csub]. *)
      let* ops = decode_cs_ops cs in
      let* opaque = List.monad_map head_const (desc :: ops) in
      let opaque =
        List.filter_map (fun c -> c) opaque @
        List.map (fun g -> const_of_ref (Lazy.force g)) [
          C.rid ; C.rshift ; C.rcons ; C.rcomp ; C.up_ren ; C.Jdg.cup_subst ;
          C.Jdg.j ; C.sub
        ]
      in
      (* Those reachable from the library's definitions and the instance, but
        not those of the user's parameters. *)
      let* transparent =
        constants_closure (
          jdg C.Jdg.rule_desc_type :: jdg C.Jdg.var_rule_type ::
          jdg C.Jdg.pred_obl :: apps (mkglob' C.Jdg.make_obl) [| ty ; sh |] ::
          jdg C.Jdg.obligations ::
          jdg C.Jdg.preserve_subst_jdg :: jdg_type ::
          List.map mkglob' [
            C.Jdg.hrule ; C.Jdg.hctor ; C.Jdg.hjdg ; C.Jdg.hjp ; C.Jdg.hext ;
            C.Jdg.hpred ; C.Jdg.jdg_at
          ]
        )
      in
      let transparent =
        List.filter (fun c -> not (List.mem c opaque)) transparent
      in
      let* arities =
        List.monad_map (fun k -> reduce_only transparent (app jdg_type (fin k)))
          ks
      in
      let* sigma = get_sigma in
      let _, ctx_ty, _ = EConstr.destProd sigma (List.hd arities) in
      ret (transparent, arities, ctx_ty)
    end
  in
  (* The family of relations [rs] (the inductives, or the variables standing
    for them in their constructor types) *)
  let family (rs : EConstr.t list) : EConstr.t =
    apps (mkglob' C.Jdg.jdg_at) [| sh ; ty ; tuple (List.combine rs arities) |]
  in
  let rules_of k = List.filter (fun rd -> rd.r_jdg = k) rules in
  (* The constructor types of judgment [k] of the family [r]: the reduced
    [var_rule_type] and [rule_desc_type], with the meta-variables named as in
    the description. *)
  let var_type (r : EConstr.t) (k : int) : EConstr.t m =
    reduce_only transparent (apps (jdg C.Jdg.var_rule_type) [| r ; fin k |])
  in
  let rule_type (r : EConstr.t) (rd : rule) : EConstr.t m =
    let* t =
      prod "Γ" ctx_ty @@ fun g ->
        ret @@
        apps (jdg C.Jdg.rule_desc_type)
          [| r ; fin rd.r_jdg ; rd.r_term ; EConstr.mkVar g |]
    in
    let* t = reduce_only transparent t in
    rename_binders (None :: List.map (fun x -> Some x) rd.r_binders) t
  in
  (* The inductives, mutual. *)
  let ctor_names =
    List.map2 (fun name k ->
      mkj name "_var" ::
      List.map (fun rd -> Names.Id.of_string_soft rd.r_name) (rules_of k)
    ) names ks
  in
  let ctor_types =
    List.map (fun k ->
      let on_family f inds = f (family (List.map EConstr.mkVar inds)) in
      on_family (fun r -> var_type r k) ::
      List.map (fun rd -> on_family (fun r -> rule_type r rd)) (rules_of k)
    ) ks
  in
  let mind = monad_run @@ declare_mut_ind names arities ctor_names ctor_types in
  let r = family (List.map (fun k -> mkind (mind, k)) ks) in
  let ctor k i = mkctor ((mind, k), i) in
  let stmt s = ret @@ apps (jdg s) [| desc ; r |] in
  (* [R_wf : wf_desc d], using tactic [JdgDesc.wf_desc_tac]. *)
  let wf =
    lemma (sname ^ "_wf")
      (ret @@ apps (mkglob' C.Jdg.wf_desc) [| sg ; ty ; sh ; desc |])
      (run_ltac "JdgDesc" "wf_desc_tac" [])
  in
  (* [R_rules : rules_type d R]: for each judgment, the [Forall] built from
    its constructors (after the variable rule). *)
  let rules_lemma =
    let forall k =
      let pred =
        monad_run begin
          lambda "rd" (rule_desc_ty k) @@ fun rd ->
          prod "Γ" ctx_ty @@ fun g ->
          ret @@
          apps (jdg C.Jdg.rule_desc_type)
            [| r ; fin k ; EConstr.mkVar rd ; EConstr.mkVar g |]
        end
      in
      let rec build i = function
        | [] -> apps (mkglob' C.Jdg.forall_nil) [| rule_desc_ty k ; pred |]
        | rd :: rest ->
          apps (mkglob' C.Jdg.forall_cons) [|
            rule_desc_ty k ;
            pred ;
            rd.r_term ;
            mklist (rule_desc_ty k) (List.map (fun rd -> rd.r_term) rest) ;
            ctor k i ;
            build (i + 1) rest
          |]
      in
      build 2 (rules_of k)
    in
    let foralls = List.map forall ks in
    lemma (sname ^ "_rules")
      (stmt C.Jdg.rules_type)
      (Tacticals.tclTHEN
        (run_ltac "JdgDesc" "split_forall_rec" [])
        (dispatch (fun k -> Tactics.exact_check (List.nth foralls k))))
  in
  (* [R_vars : var_rules d R], the conjunction of the variable constructors. *)
  let vars =
    lemma (sname ^ "_vars")
      (ret @@ app (jdg C.Jdg.var_rules) r)
      (Tacticals.tclTHEN
        (run_ltac "JdgDesc" "split_forall_rec" [])
        (dispatch (fun k -> Tactics.exact_check (ctor k 1))))
  in
  (* [R_sound : sound_jdg d R], from the induction principle of the block: the
    combined scheme over the motives [P i], whose type is then convertible to
    [ind_type d R]. The own scheme of a single inductive does. *)
  let sound =
    let scheme =
      if n = 1 then locate (mk "_ind")
      else begin
        let schemes = List.map (fun name -> mkj name "_mut") names in
        let prop = UnivGen.QualityOrSet.Qual Sorts.Quality.(QConstant QProp) in
        Indschemes.do_mutual_induction_scheme ~register:false (Global.env ())
          (List.map2 (fun id k -> (CAst.make id, false, (mind, k), prop))
            schemes ks) ;
        Indschemes.do_combined_scheme (CAst.make (mk "_mutind"))
          (List.map locate schemes) ;
        locate (mk "_mutind")
      end
    in
    let motives =
      monad_run begin
        let* p_ty =
          prod "i" (app (mkglob' C.Jdg.jidx) sh) @@ fun i ->
            ret (app jdg_type (EConstr.mkVar i))
        in
        lambda "P" p_ty @@ fun p ->
          ret (apps (mkconst scheme)
            (Array.of_list (List.map (fun k -> app (EConstr.mkVar p) (fin k)) ks)))
      end
    in
    lemma (sname ^ "_sound")
      (stmt C.Jdg.sound_jdg)
      (Tactics.exact_check (
        apps (jdg C.Jdg.sound_of_ind) [| desc ; cl ; r ; motives |]
      ))
  in
  (* [R_complete : complete_jdg d R]. *)
  let complete =
    lemma (sname ^ "_complete")
      (stmt C.Jdg.complete_jdg)
      (Tactics.exact_check (
        apps (jdg C.Jdg.jdg_complete) [|
          desc ; cl ; r ; mkconst vars ; mkconst rules_lemma ; mkconst wf
        |]
      ))
  in
  (* The obligations, located in the description: [ob_pred j r i] for the
    predicate premise [i] of rule [r], [ob_make i i'] for a pair of judgments
    where a rule of [i] has a premise in [i']; [R_obls_wf] checks the list
    by computation. [R_obligations : Prop] is their conjunction, reduced
    (with the description unfolded), declared as a class so that the user
    proves it once as an instance, and each [R_subst : ∀ {H : R_obligations},
    preserve_subst_jdg R i] finds it by resolution. No class when there is no
    obligation. *)
  let _subst =
    let preds =
      List.concat_map (fun j ->
        List.concat (List.mapi (fun r rd ->
          List.concat (List.mapi (fun i p ->
            match p with None -> [ (j, r, rd, i) ] | Some _ -> []) rd.r_prems)
        ) (rules_of j))
      ) ks
    in
    let pairs =
      List.sort_uniq compare (List.concat_map (fun rd ->
        List.filter_map (fun p ->
          match p with
          | Some i when i <> rd.r_jdg -> Some (rd.r_jdg, i)
          | _ -> None) rd.r_prems
      ) rules)
    in
    (* [ob] only depends on the shapes *)
    let obs =
      List.map (fun (j, r, _, i) ->
        apps (mkglob' C.Jdg.ob_pred) [| sh ; fin j ; mknat r ; mknat i |])
        preds @
      List.map (fun (i, i') ->
        apps (mkglob' C.Jdg.ob_make) [| sh ; fin i ; fin i' |]) pairs
    in
    let obs_term = mklist (app (mkglob' C.Jdg.ob) sh) obs in
    let ok =
      lemma (sname ^ "_obls_wf")
        (ret @@ apps (mkglob' C.Jdg.obls_ok) [| sg ; ty ; sh ; desc ; obs_term |])
        (run_ltac "JdgDesc" "wf_desc_tac" [])
    in
    let stmt k =
      let* cs_const = head_const cs in
      let transp = List.map (fun g -> const_of_ref (Lazy.force g)) [
        C.Jdg.preserve_subst_jdg ;
        C.CS.csubstitute
      ] in
      let transp = match cs_const with Some c -> c :: transp | None -> transp in
      reduce_only (transp @ transparent)
        (apps (jdg C.Jdg.preserve_subst_jdg) [| r ; fin k |])
    in
    let proof h k =
      apps (jdg C.Jdg.gen_preserve_subst) [|
        desc ; cl ; r ; mkconst sound ; mkconst complete ; obs_term ;
        mkconst ok ; h ; fin k
      |]
    in
    (* The conjunction of the obligations, those of a predicate premise with
      the binders of their rule *)
    let rename_obls (t : EConstr.t) : EConstr.t m =
      let* sigma = get_sigma in
      let rename bs t =
        match bs with
        | Some bs -> rename_binders (List.map (fun x -> Some x) bs) t
        | None -> ret t
      in
      let rec go t = function
        | [] -> ret t
        | [ bs ] -> rename bs t
        | bs :: rest ->
          match EConstr.decompose_app sigma t with
          | h, [| a ; b |] ->
            let* a = rename bs a in
            let* b = go b rest in
            ret (apps h [| a ; b |])
          | _ -> ret t
      in
      go t (
        List.map (fun (_, _, rd, _) -> Some rd.r_binders) preds @
        List.map (fun _ -> None) pairs
      )
    in
    let cls =
      if obs = [] then None
      else begin
        let cls =
          def (sname ^ "_obligations") begin
            let* desc_const = head_const desc in
            let transparent =
              match desc_const with Some c -> c :: transparent | None -> transparent
            in
            let* t =
              reduce_only transparent
                (apps (jdg C.Jdg.obligations) [| desc ; r ; obs_term |])
            in
            rename_obls t
          end
        in
        Record.declare_existing_class (Names.GlobRef.ConstRef cls) ;
        Some cls
      end
    in
    List.iter2 (fun name k ->
      let name = Names.Id.to_string name ^ "_subst" in
      match cls with
      | None ->
        ignore (lemma name (stmt k)
          (Tactics.exact_check (proof (mkglob (Rocqlib.lib_ref "core.True.I")) k)))
      | Some cls ->
        let subst =
          lemma name
            (let* concl = stmt k in
              prod "H" (mkconst cls) (fun _ -> ret concl))
            (Tactics.exact_check
              (monad_run (lambda "H" (mkconst cls) (fun h ->
                ret (proof (EConstr.mkVar h) k)))))
        in
        Impargs.declare_manual_implicits false (Names.GlobRef.ConstRef subst)
          [ CAst.make (Some (Names.Name (Names.Id.of_string "H"), true)) ]
    ) names ks
  in
  ()

(******************************************************************************)
(** *** Judgments written as rules. *)
(******************************************************************************)

let saved_ops () =
  match !Main.saved_ops with
  | Some x -> x
  | None -> Log.error "Sulfur Judgment: no syntax was generated beforehand."

(** The components of a declaration [Γ : d]: the factors of a product, none for
  [unit]. The context is a list of the library's tuples, [decl_type d]. *)
let decl_components (d : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  if Cexpr.is_ident (Names.Id.of_string "unit") d then [] else Cexpr.products d

let decl_type (d : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  Cexpr.prod (decl_components d)

(** The description written by the user, as the Gallina expression

    [ ([ hrule k "name" ps (λ binders, ([p1 ; ... ; pn], c)) ; ... ],
       (..., tt)) : jdg_desc term ]

  with one list of rules per judgment [k], where [ps] are the parameters, and
  every judgment [pi] or [c] is wrapped as

    [ let R := hjdg in let c := hctor Cc in ... pi ]

  with [R] the judgment and [c] ranging over the constructors, so that
  elaboration resolves them to their HOAS versions.
  A binder [(x : term)] is a meta-variable, typed [hterm] in the lambda
  ([hterm → ... → hterm] for an arity), any other type is a parameter.
  A premise [{{ P }}] is first-order:

    [ hpred n (λ (x1 ... xn : term) (Γ : list term), P) ]

  with [x1 ... xn] the meta-variables of the rule.

  The shapes instance [shapes] is given explicitly wherever the command emits a
  constant that depends on it, so that the types of the predicates reduce during
  elaboration; the bracket and the coercion of judgments find it by unification.
*)
let desc_expr (blocks : (header * prule list) list)
  (shapes : Names.Constant.t) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
  let hs = List.map fst blocks in
  let h = List.hd hs in
  let sign, ops = saved_ops () in
  let sort = sign.Signature.sort_name in
  let shc = Cexpr.gref (Names.GlobRef.ConstRef shapes) in
  (* A constant of [JdgDesc] whose implicit arguments are the signature, the
    term type and the shapes *)
  let shaped g args =
    Cexpr.app_expl g (Cexpr.hole :: Cexpr.hole :: shc :: args)
  in
  (* The judgment and the constructors as their HOAS versions *)
  let hctor i =
    let c = Names.GlobRef.ConstructRef (ops.ops_si.ctor, i + 1) in
    mkAppC (Cexpr.gref' C.Jdg.hctor, [ Cexpr.gref c ])
  in
  (* The index [k] of a judgment *)
  let rec fin k =
    if k = 0 then Cexpr.gref' C.Jdg.finO
    else mkAppC (Cexpr.gref' C.Jdg.finS, [ fin (k - 1) ])
  in
  let defs =
    (* [hjdg] does not depend on the term type *)
    List.mapi (fun k h ->
      (h.ph_name, Cexpr.app_expl C.Jdg.hjdg [ Cexpr.hole ; shc ; fin k ])
    ) hs @
    List.mapi (fun i c -> (c, hctor i)) (Array.to_list sign.Signature.ctor_names)
  in
  let hoas e =
    List.fold_right
      (fun (x, v) body -> mkLetInC (CAst.make (Names.Name x), v, None, body))
      defs e
  in
  (* Force annotation-free binders to be the sort *)
  let typed b =
    match b with
    | Constrexpr.CLocalAssum (xs, r, k, { CAst.v = Constrexpr.CHole _ ; _ }) ->
      Constrexpr.CLocalAssum (xs, r, k, mkIdentC sort)
    | b -> b
  in
  (* The arity of a meta-variable type [term → ... → term], if it is one *)
  let arity (ty : Constrexpr.constr_expr) : int option =
    let ds, c = Cexpr.arrows ty in
    if Cexpr.is_ident sort c && List.for_all (Cexpr.is_ident sort) ds
    then Some (List.length ds)
    else None
  in
  let param (ty : Constrexpr.constr_expr) =
    match arity ty with
    | Some n -> mkAppC (Cexpr.gref' C.Jdg.rp_term, [ Cexpr.nat n ])
    | None when Constrexpr_ops.occur_var_constr_expr sort ty ->
      Log.error ?loc:ty.CAst.loc
        "A parameter type cannot mention the sort %s." (Names.Id.to_string sort)
    | None -> mkAppC (Cexpr.gref' C.Jdg.rp_param, [ ty ])
  in
  (* The binders of the lambda: a meta-variable of arity [n] is an [n]-ary
    function on [hterm] *)
  let rec hterm_n n =
    if n = 0 then Cexpr.gref' C.Jdg.hterm
    else
      mkCProdN [
        Cexpr.assum [ CAst.make Names.Anonymous ] (Cexpr.gref' C.Jdg.hterm)
      ] (hterm_n (n - 1))
  in
  let hbinder b =
    match b with
    | Constrexpr.CLocalAssum (xs, r, k, ty) when arity ty <> None ->
      Constrexpr.CLocalAssum (xs, r, k, hterm_n (Option.get (arity ty)))
    | b -> b
  in
  let params bs =
    bs |> List.concat_map @@ fun b ->
      match b with
      | Constrexpr.CLocalAssum (xs, _, _, ty) ->
        List.map (fun _ -> param ty) xs
      | Constrexpr.CLocalDef ({ CAst.loc ; _ }, _, _, _)
      | Constrexpr.CLocalPattern { CAst.loc ; _ } ->
        Log.error ?loc "Rule binders must be assumptions (x : A)."
  in
  (* The meta-variables among the binders *)
  let metas bs =
    bs |> List.concat_map @@ fun b ->
      match b with
      | Constrexpr.CLocalAssum (xs, _, _, ty) when arity ty <> None -> xs
      | _ -> []
  in
  (* [{{ P }}] with meta-variables [xs] (see above); the context is named
    and typed as in the header *)
  let pred xs e =
    let gamma = CAst.make (Names.Name h.ph_ctx) in
    let bs =
      [
        Cexpr.assum [ gamma ]
          (mkAppC (Cexpr.gref' C.list, [ decl_type h.ph_decl ]))
      ]
    in
    let bs = if xs = [] then bs else Cexpr.assum xs (mkIdentC sort) :: bs in
    shaped C.Jdg.hpred [ Cexpr.nat (List.length xs) ; mkCLambdaN bs e ]
  in
  (* The premises, as [@cons hprem p l]: with the type explicit.
    A judgment [p] is checked against [hprem] and coerced;
    [cons p l] alone would infer the type from [p] first.
  *)
  let prems xs l =
    let prem p =
      match p with
      | PJdg e -> hoas e
      | PPred e -> pred xs e
    in
    let cons p l =
      Cexpr.app_expl C.cons [ shaped C.Jdg.hprem [] ; prem p ; l ]
    in
    List.fold_right cons l (Cexpr.gref' C.nil)
  in
  (* A rule of the [k]th judgment *)
  let rule k r =
    let bs = List.map typed r.pr_binders in
    shaped C.Jdg.hrule [
      fin k ;
      Cexpr.string (Names.Id.to_string r.pr_name) ;
      Cexpr.list (params bs) ;
      (* [hfun [] R] is [R]: no lambda for a rule without binders *)
      (if bs = [] then Fun.id else mkCLambdaN (List.map hbinder bs))
        (Cexpr.pair (prems (metas bs) r.pr_prems) (hoas r.pr_concl))
    ]
  in
  (* The rules of each block as a list, the blocks as a tuple *)
  let block k (_, rs) = Cexpr.list (List.map (rule k) rs) in
  mkCastC (
    List.fold_right Cexpr.pair (List.mapi block blocks) (Cexpr.gref' C.tt),
    Some Constr.DEFAULTcast,
    Cexpr.app_expl C.Jdg.jdg_desc [ Cexpr.hole ; mkIdentC sort ; shc ]
  )

(** The shapes of the headers, as the Gallina expression
  [shapes [d] [jshape_of [a1 ; ... ; am] (sel of the variable rule) ; ...]]:
  the sort is [t_term], any other type [t_base], a product of those is taken
  ([unit] for the empty product).
  The judgments of a block declare the same thing. *)
let shapes_expr (hs : header list) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
  let sign, _ = saved_ops () in
  let sort = sign.Signature.sort_name in
  let shape_of ty =
    if Cexpr.is_ident sort ty then Cexpr.gref' C.Jdg.t_term
    else mkAppC (Cexpr.gref' C.Jdg.t_base, [ ty ])
  in
  let h0 = List.hd hs in
  let dsh = Cexpr.list (List.map shape_of (decl_components h0.ph_decl)) in
  let jshape (h : header) =
    if not (Constrexpr_ops.constr_expr_eq h.ph_decl h0.ph_decl) then
      Log.error ?loc:h.ph_decl.CAst.loc
        "Sulfur Judgment: the judgments of a block declare the same thing." ;
    if not (Names.Id.equal h.ph_jdg h.ph_name) then
      Log.error "Sulfur Judgment: the variable rule must conclude %s."
        (Names.Id.to_string h.ph_name) ;
    let jsh = Cexpr.list (List.map shape_of (fst (Cexpr.arrows h.ph_type))) in
    (* The judgment of a variable: each argument is the variable or one of the
      declarations [d1 ... dn], picked by position. *)
    let rec pos k =
      if k = 0 then Cexpr.gref' C.Jdg.pos0
      else mkAppC (Cexpr.gref' C.Jdg.posS, [ pos (k - 1) ])
    in
    let sel a s =
      let rec index k = function
        | [] -> None
        | d :: ds ->
          if Names.Name.equal (Names.Name a) d.CAst.v
          then Some k
          else index (k + 1) ds
      in
      if Names.Id.equal a h.ph_var then mkAppC (Cexpr.gref' C.Jdg.sel_var, [ s ])
      else
        match index 0 h.ph_decls with
        | Some k -> mkAppC (Cexpr.gref' C.Jdg.sel_pos, [ pos k ; s ])
        | None ->
          Log.error
            "Sulfur Judgment: %s is neither the variable nor a declaration."
            (Names.Id.to_string a)
    in
    let sel = List.fold_right sel h.ph_args (Cexpr.gref' C.Jdg.sel_nil) in
    mkAppC (Cexpr.gref' C.Jdg.jshape_of, [ Cexpr.hole ; jsh ; sel ])
  in
  mkAppC (Cexpr.gref' C.Jdg.shapes, [ dsh ; Cexpr.list (List.map jshape hs) ])

(** [Sulfur Judgment header {{ rules }}]: the shapes are declared as the
  instance [R_shapes], the description as [R_desc] (with the local
  definitions substituted), then handled as above.
*)
let generate_rules (blocks : (header * prule list) list) : unit =
  let hs = List.map fst blocks in
  let name = Names.Id.to_string (List.hd hs).ph_name in
  let shapes = def (name ^ "_shapes") (pretype (shapes_expr hs)) in
  Classes.declare_instance (Global.env ()) (Evd.from_env (Global.env ()))
    None Hints.Export (Names.GlobRef.ConstRef shapes) ;
  let desc =
    def (name ^ "_desc") begin
      let* d = pretype (desc_expr blocks shapes) in
      (* Substitute the local definitions *)
      reduce_only [] d
    end
  in
  generate_desc blocks (mkconst desc)
