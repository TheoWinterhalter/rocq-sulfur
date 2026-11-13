(** Implementation of the [Sulfur Judgment] command.

  See [g_plugin.mlg] for the grammar of the command.

  Everything is stated and proven in [theories/JdgDesc.v]:
  this file only computes the constructor types by reduction, and instantiates
  the generic lemmas.
*)

open Prelude
module C = Constants

(** Parsed data *)

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

(** A description:
  the names of its judgments, its signature, term type, shapes, instance and
  laws, and its rules.
*)
type desc = {
  d_term : EConstr.t ;
  d_names : Names.Id.t list ;
  d_sg : EConstr.t ;
  d_ty : EConstr.t ;
  d_sh : EConstr.t ;
  d_cs : EConstr.t ;
  d_cl : EConstr.t ;
  d_rules : rule list
}

(** The family of relations generated from a description: the constants its
  statements may unfold, the type of its contexts, the mutual inductive, and
  [jdg_at (R1, (R2, ... tt))] which the statements are about. *)
type family = {
  f_transparent : Names.Constant.t list ;
  f_ctx_ty : EConstr.t ;
  f_mind : Names.MutInd.t ;
  f_r : EConstr.t
}

(** The indices of the judgments, as integers and as terms *)
let indices (d : desc) : int list = List.init (List.length d.d_names) Fun.id
let idx (d : desc) (k : int) : EConstr.t = fin (List.length d.d_names) k

(** The rules of judgment [k], in order *)
let rules_of (d : desc) (k : int) : rule list =
  List.filter (fun rd -> rd.r_jdg = k) d.d_rules

let suffix (name : Names.Id.t) (s : string) : Names.Id.t =
  Names.Id.of_string_soft (Names.Id.to_string name ^ s)

(** The shared lemmas are named after the first judgment *)
let shared (d : desc) (s : string) : string =
  Names.Id.to_string (List.hd d.d_names) ^ s

(** A constant of [JdgDesc] applied to the signature, term type, instance and
  shapes of [d] *)
let jdg (d : desc) (s : Names.GlobRef.t Lazy.t) : EConstr.t =
  apps (mkglob' s) [| d.d_sg ; d.d_ty ; d.d_cs ; d.d_sh |]

let jdg_type (d : desc) : EConstr.t =
  apps (mkglob' C.Jdg.jdg_type) [| d.d_sh ; d.d_ty |]

(** The type of the rules of judgment [k] *)
let rule_desc_ty (d : desc) (k : int) : EConstr.t =
  let sh_at = apps (mkglob' C.Jdg.sh_at) [| d.d_sh ; idx d k |] in
  apps (mkglob' C.Jdg.rule_desc) [| d.d_sg ; d.d_ty ; d.d_sh ; sh_at |]

(** The statement [s d R] about the family *)
let stmt (d : desc) (f : family) (s : Names.GlobRef.t Lazy.t) : EConstr.t m =
  ret (apps (jdg d s) [| d.d_term ; f.f_r |])

(** The constructor [i] of judgment [k]; the variable rule is [1] *)
let ctor (f : family) (k : int) (i : int) : EConstr.t =
  mkctor ((f.f_mind, k), i)

(** Reduce a statement, unfolding only [transparent]; [map] over a variable
  context, in a predicate, keeps its name. *)
let reduce (transparent : Names.Constant.t list) (t : EConstr.t) : EConstr.t m =
  reduce_only ~refold:[ const_of_ref (Lazy.force C.map) ] transparent t

(** The description [desc] of the judgments of [blocks], read *)
let read_desc (blocks : (header * prule list) list) (desc : EConstr.t) : desc =
  let d_names = List.map (fun (h, _) -> h.ph_name) blocks in
  (* The rules as written, with the index of their judgment *)
  let prs =
    List.mapi (fun k (_, rs) -> List.map (fun r -> (k, r)) rs) blocks
    |> List.concat
  in
  monad_run begin
    let* desc_ty = typecheck desc None in
    let* d_sg, d_ty, d_sh = decode_sig desc_ty in
    let* d_cs = resolve_tc (apps (mkglob' C.CS.typ) [| d_sg ; d_ty |]) in
    let* d_cl = resolve_tc (apps (mkglob' C.CS.laws) [| d_sg ; d_ty ; d_cs |]) in
    let* terms = decode_desc desc in
    let terms = List.concat terms in
    let d_rules = List.map2 (fun (k, r) t -> rule_of d_names k t r) prs terms in
    ret { d_term = desc ; d_names ; d_sg ; d_ty ; d_sh ; d_cs ; d_cl ; d_rules }
  end

(** The constants the statements may unfold: those reachable from the library's
  definitions and the instance, but not those of the user's parameters, nor
  the ones which stay folded in the statements: the description, the
  operations of the syntax, the renamings, the lifting of substitutions, the
  generic judgment [J], and [Nat.sub] which would otherwise pollute [csub]. *)
let transparent_constants (d : desc) : Names.Constant.t list m =
  let* ops = decode_cs_ops d.d_cs in
  let* opaque = List.monad_map head_const (d.d_term :: ops) in
  let opaque =
    List.filter_map Fun.id opaque @
    List.map (fun g -> const_of_ref (Lazy.force g)) [
      C.rid ; C.rshift ; C.rcons ; C.rcomp ; C.up_ren ; C.Jdg.cup_subst ;
      C.Jdg.j ; C.sub
    ]
  in
  let* transparent =
    constants_closure (
      jdg d C.Jdg.rule_desc_type :: jdg d C.Jdg.var_rule_type ::
      jdg d C.Jdg.pred_obl :: apps (mkglob' C.Jdg.make_obl) [| d.d_ty ; d.d_sh |] ::
      jdg d C.Jdg.obligations ::
      jdg d C.Jdg.preserve_subst_jdg :: jdg_type d ::
      List.map mkglob' [
        C.Jdg.hrule ; C.Jdg.hctor ; C.Jdg.hjdg ; C.Jdg.hjp ; C.Jdg.hext ;
        C.Jdg.hpred ; C.Jdg.jdg_at
      ]
    )
  in
  ret (List.filter (fun c -> not (List.mem c opaque)) transparent)

(** The inductives, mutual, each with its variable rule as first constructor.
  Their types come from the shapes, their constructor types are the reduced
  [var_rule_type] and [rule_desc_type], with the meta-variables named as in
  the description. *)
let declare_inductives (d : desc) : family =
  let transparent, arities, ctx_ty =
    monad_run begin
      let* transparent = transparent_constants d in
      let* arities =
        List.monad_map (fun k ->
          reduce transparent (app (jdg_type d) (idx d k))
        ) (indices d)
      in
      let* sigma = get_sigma in
      let _, ctx_ty, _ = EConstr.destProd sigma (List.hd arities) in
      ret (transparent, arities, ctx_ty)
    end
  in
  (* The family of relations [rs] (the inductives, or the variables standing
    for them in their constructor types) *)
  let family (rs : EConstr.t list) : EConstr.t =
    apps (mkglob' C.Jdg.jdg_at)
      [| d.d_sh ; d.d_ty ; tuple (List.combine rs arities) |]
  in
  let var_type (r : EConstr.t) (k : int) : EConstr.t m =
    reduce transparent (apps (jdg d C.Jdg.var_rule_type) [| r ; idx d k |])
  in
  let rule_type (r : EConstr.t) (rd : rule) : EConstr.t m =
    let* t =
      prod "Γ" ctx_ty @@ fun g ->
        ret (apps (jdg d C.Jdg.rule_desc_type)
          [| r ; idx d rd.r_jdg ; rd.r_term ; EConstr.mkVar g |])
    in
    let* t = reduce transparent t in
    rename_binders (None :: List.map (fun x -> Some x) rd.r_binders) t
  in
  let ctor_names =
    List.map2 (fun name k ->
      suffix name "_var" ::
      List.map (fun rd -> Names.Id.of_string_soft rd.r_name) (rules_of d k)
    ) d.d_names (indices d)
  in
  let ctor_types =
    List.map (fun k ->
      let on_family f inds = f (family (List.map EConstr.mkVar inds)) in
      on_family (fun r -> var_type r k) ::
      List.map (fun rd -> on_family (fun r -> rule_type r rd)) (rules_of d k)
    ) (indices d)
  in
  let mind =
    monad_run (declare_mut_ind d.d_names arities ctor_names ctor_types)
  in
  {
    f_transparent = transparent ;
    f_ctx_ty = ctx_ty ;
    f_mind = mind ;
    f_r = family (List.map (fun k -> mkind (mind, k)) (indices d))
  }

(** [R_wf : wf_desc d], using tactic [JdgDesc.wf_desc_tac]. *)
let wf_lemma (d : desc) : Names.Constant.t =
  lemma (shared d "_wf")
    (ret (apps (mkglob' C.Jdg.wf_desc) [| d.d_sg ; d.d_ty ; d.d_sh ; d.d_term |]))
    (run_ltac "JdgDesc" "wf_desc_tac" [])

(** [R_rules : rules_type d R]: for each judgment, the [Forall] built from
  its constructors (after the variable rule). *)
let rules_lemma (d : desc) (f : family) : Names.Constant.t =
  let forall k =
    let pred =
      monad_run begin
        lambda "rd" (rule_desc_ty d k) @@ fun rd ->
        prod "Γ" f.f_ctx_ty @@ fun g ->
        ret (apps (jdg d C.Jdg.rule_desc_type)
          [| f.f_r ; idx d k ; EConstr.mkVar rd ; EConstr.mkVar g |])
      end
    in
    let rec build i = function
      | [] -> apps (mkglob' C.Jdg.forall_nil) [| rule_desc_ty d k ; pred |]
      | rd :: rest ->
        apps (mkglob' C.Jdg.forall_cons) [|
          rule_desc_ty d k ;
          pred ;
          rd.r_term ;
          mklist (rule_desc_ty d k) (List.map (fun rd -> rd.r_term) rest) ;
          ctor f k i ;
          build (i + 1) rest
        |]
    in
    build 2 (rules_of d k)
  in
  let foralls = List.map forall (indices d) in
  lemma (shared d "_rules")
    (stmt d f C.Jdg.rules_type)
    (Tacticals.tclTHEN
      (run_ltac "JdgDesc" "split_forall_rec" [])
      (dispatch (fun k -> Tactics.exact_check (List.nth foralls k))))

(** [R_vars : var_rules d R], the conjunction of the variable constructors. *)
let vars_lemma (d : desc) (f : family) : Names.Constant.t =
  lemma (shared d "_vars")
    (ret (app (jdg d C.Jdg.var_rules) f.f_r))
    (Tacticals.tclTHEN
      (run_ltac "JdgDesc" "split_forall_rec" [])
      (dispatch (fun k -> Tactics.exact_check (ctor f k 1))))

(** The induction principle of the family, over a family of motives [P i]: the
  combined scheme of the mutual inductive applied to [P finO], [P (finS
  finO)], ..., whose type is then convertible to [ind_type d R]. The own
  scheme of a single inductive does. *)
let induction_scheme (d : desc) (f : family) : EConstr.t =
  let locate id = Nametab.locate_constant (Libnames.qualid_of_ident id) in
  let scheme =
    match d.d_names with
    | [ name ] -> locate (suffix name "_ind")
    | names ->
      let schemes = List.map (fun name -> suffix name "_mut") names in
      let prop = UnivGen.QualityOrSet.Qual Sorts.Quality.(QConstant QProp) in
      Indschemes.do_mutual_induction_scheme ~register:false (Global.env ())
        (List.map2 (fun id k -> (CAst.make id, false, (f.f_mind, k), prop))
          schemes (indices d)) ;
      let combined = suffix (List.hd names) "_mutind" in
      Indschemes.do_combined_scheme (CAst.make combined) (List.map locate schemes) ;
      locate combined
  in
  monad_run begin
    let* p_ty =
      prod "i" (app (mkglob' C.Jdg.jidx) d.d_sh) @@ fun i ->
        ret (app (jdg_type d) (EConstr.mkVar i))
    in
    lambda "P" p_ty @@ fun p ->
      let motives = List.map (fun k -> app (EConstr.mkVar p) (idx d k)) (indices d) in
      ret (apps (mkconst scheme) (Array.of_list motives))
  end

(** [R_sound : sound_jdg d R], from the induction principle. *)
let sound_lemma (d : desc) (f : family) : Names.Constant.t =
  lemma (shared d "_sound")
    (stmt d f C.Jdg.sound_jdg)
    (Tactics.exact_check (
      apps (jdg d C.Jdg.sound_of_ind)
        [| d.d_term ; d.d_cl ; f.f_r ; induction_scheme d f |]
    ))

(** [R_complete : complete_jdg d R]. *)
let complete_lemma (d : desc) (f : family) ~vars ~rules ~wf : Names.Constant.t =
  lemma (shared d "_complete")
    (stmt d f C.Jdg.complete_jdg)
    (Tactics.exact_check (
      apps (jdg d C.Jdg.jdg_complete)
        [| d.d_term ; d.d_cl ; f.f_r ; mkconst vars ; mkconst rules ; mkconst wf |]
    ))

(** The obligations, located in the description: [ob_pred j r i] for the
  predicate premise [i] of rule [r] of judgment [j], [ob_make i i'] for a
  pair of judgments where a rule of [i] has a premise in [i']; and their list
  as a term, which only depends on the shapes. *)
type obligations = {
  o_preds : (int * int * rule * int) list ;
  o_pairs : (int * int) list ;
  o_term : EConstr.t
}

let obligations (d : desc) : obligations =
  let o_preds =
    List.concat_map (fun j ->
      List.concat (List.mapi (fun r rd ->
        List.concat (List.mapi (fun i p ->
          match p with None -> [ (j, r, rd, i) ] | Some _ -> []) rd.r_prems)
      ) (rules_of d j))
    ) (indices d)
  in
  let o_pairs =
    List.sort_uniq compare (List.concat_map (fun rd ->
      List.filter_map (fun p ->
        match p with
        | Some i when i <> rd.r_jdg -> Some (rd.r_jdg, i)
        | _ -> None) rd.r_prems
    ) d.d_rules)
  in
  let obs =
    List.map (fun (j, r, _, i) ->
      apps (mkglob' C.Jdg.ob_pred) [| d.d_sh ; idx d j ; mknat r ; mknat i |])
      o_preds @
    List.map (fun (i, i') ->
      apps (mkglob' C.Jdg.ob_make) [| d.d_sh ; idx d i ; idx d i' |]) o_pairs
  in
  { o_preds ; o_pairs ; o_term = mklist (app (mkglob' C.Jdg.ob) d.d_sh) obs }

(** [R_obligations : Prop], the conjunction of the obligations, reduced (with
  the description unfolded), the obligation of a predicate premise under the
  binders of its rule; declared as a class so that the user proves it once as
  an instance. None when there is no obligation. *)
let obligations_class (d : desc) (f : family) (o : obligations) :
  Names.Constant.t option =
  if o.o_preds = [] && o.o_pairs = [] then None
  else begin
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
        List.map (fun (_, _, rd, _) -> Some rd.r_binders) o.o_preds @
        List.map (fun _ -> None) o.o_pairs
      )
    in
    let cls =
      def (shared d "_obligations") begin
        let* desc_const = head_const d.d_term in
        let* t =
          reduce (Option.List.cons desc_const f.f_transparent)
            (apps (jdg d C.Jdg.obligations) [| d.d_term ; f.f_r ; o.o_term |])
        in
        rename_obls t
      end
    in
    Record.declare_existing_class (Names.GlobRef.ConstRef cls) ;
    Some cls
  end

(** [R_obls_wf] checks the list of obligations by computation, then
  [R_subst : ∀ {H : R_obligations}, preserve_subst_jdg R i] for every
  judgment, which finds the instance by resolution. *)
let subst_lemmas (d : desc) (f : family) ~sound ~complete : unit =
  let o = obligations d in
  let ok =
    lemma (shared d "_obls_wf")
      (ret (apps (mkglob' C.Jdg.obls_ok)
        [| d.d_sg ; d.d_ty ; d.d_sh ; d.d_term ; o.o_term |]))
      (run_ltac "JdgDesc" "wf_desc_tac" [])
  in
  let cls = obligations_class d f o in
  let stmt k =
    let* cs_const = head_const d.d_cs in
    let extra =
      Option.List.cons cs_const
        (List.map (fun g -> const_of_ref (Lazy.force g))
          [ C.Jdg.preserve_subst_jdg ; C.CS.csubstitute ])
    in
    reduce (extra @ f.f_transparent)
      (apps (jdg d C.Jdg.preserve_subst_jdg) [| f.f_r ; idx d k |])
  in
  let proof h k =
    apps (jdg d C.Jdg.gen_preserve_subst) [|
      d.d_term ; d.d_cl ; f.f_r ; mkconst sound ; mkconst complete ; o.o_term ;
      mkconst ok ; h ; idx d k
    |]
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
  ) d.d_names (indices d)

(** The judgments of [blocks], described by [desc]: the inductives, then the
  lemmas. *)
let generate_desc (blocks : (header * prule list) list) (desc : EConstr.t) :
  unit =
  let d = read_desc blocks desc in
  let f = declare_inductives d in
  let wf = wf_lemma d in
  let rules = rules_lemma d f in
  let vars = vars_lemma d f in
  let sound = sound_lemma d f in
  let complete = complete_lemma d f ~vars ~rules ~wf in
  subst_lemmas d f ~sound ~complete

(******************************************************************************)
(** *** Judgments written as rules. *)
(******************************************************************************)

let saved_ops () =
  match !Main.saved_ops with
  | Some x -> x
  | None -> Log.error "Sulfur Judgment: no syntax was generated beforehand."

(** The index [k] of a judgment, as an expression *)
let rec idx_expr (k : int) : Constrexpr.constr_expr =
  if k = 0 then Cexpr.gref' C.Jdg.finO
  else Constrexpr_ops.mkAppC (Cexpr.gref' C.Jdg.finS, [ idx_expr (k - 1) ])

(** The components of a declaration [Γ : d]: the factors of a product, none for
  [unit]. The context is a list of the library's tuples, [decl_type d]. *)
let decl_components (d : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  if Cexpr.is_ident (Names.Id.of_string "unit") d then [] else Cexpr.products d

let decl_type (d : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  Cexpr.prod (decl_components d)

(** Binders of a rule, over the sort of the syntax *)

(** The arity of a meta-variable type [term → ... → term], if it is one *)
let arity (sort : Names.Id.t) (ty : Constrexpr.constr_expr) : int option =
  let ds, c = Cexpr.arrows ty in
  if Cexpr.is_ident sort c && List.for_all (Cexpr.is_ident sort) ds
  then Some (List.length ds)
  else None

(** A rule parameter: a meta-variable of arity [n], or a true parameter, whose
  type cannot mention the sort *)
let param (sort : Names.Id.t) (ty : Constrexpr.constr_expr) :
  Constrexpr.constr_expr =
  let open Constrexpr_ops in
  match arity sort ty with
  | Some n -> mkAppC (Cexpr.gref' C.Jdg.rp_term, [ Cexpr.nat n ])
  | None when occur_var_constr_expr sort ty ->
    Log.error ?loc:ty.CAst.loc
      "A parameter type cannot mention the sort %s." (Names.Id.to_string sort)
  | None -> mkAppC (Cexpr.gref' C.Jdg.rp_param, [ ty ])

(** [hterm → ... → hterm], the type of a meta-variable of arity [n] *)
let rec hterm_n (n : int) : Constrexpr.constr_expr =
  if n = 0 then Cexpr.gref' C.Jdg.hterm
  else
    Constrexpr_ops.mkCProdN
      [ Cexpr.assum [ CAst.make Names.Anonymous ] (Cexpr.gref' C.Jdg.hterm) ]
      (hterm_n (n - 1))

(** An annotation-free binder is of the sort *)
let typed (sort : Names.Id.t) (b : Constrexpr.local_binder_expr) :
  Constrexpr.local_binder_expr =
  match b with
  | Constrexpr.CLocalAssum (xs, r, k, { CAst.v = Constrexpr.CHole _ ; _ }) ->
    Constrexpr.CLocalAssum (xs, r, k, Constrexpr_ops.mkIdentC sort)
  | b -> b

(** A binder of the lambda of a rule: a meta-variable of arity [n] is an
  [n]-ary function on [hterm] *)
let hbinder (sort : Names.Id.t) (b : Constrexpr.local_binder_expr) :
  Constrexpr.local_binder_expr =
  match b with
  | Constrexpr.CLocalAssum (xs, r, k, ty) when arity sort ty <> None ->
    Constrexpr.CLocalAssum (xs, r, k, hterm_n (Option.get (arity sort ty)))
  | b -> b

(** The parameters of the binders of a rule, which must be assumptions *)
let params (sort : Names.Id.t) (bs : Constrexpr.local_binder_expr list) :
  Constrexpr.constr_expr list =
  bs |> List.concat_map @@ fun b ->
    match b with
    | Constrexpr.CLocalAssum (xs, _, _, ty) -> List.map (fun _ -> param sort ty) xs
    | Constrexpr.CLocalDef ({ CAst.loc ; _ }, _, _, _)
    | Constrexpr.CLocalPattern { CAst.loc ; _ } ->
      Log.error ?loc "Rule binders must be assumptions (x : A)."

(** The meta-variables among the binders of a rule *)
let metas (sort : Names.Id.t) (bs : Constrexpr.local_binder_expr list) :
  Names.lname list =
  bs |> List.concat_map @@ fun b ->
    match b with
    | Constrexpr.CLocalAssum (xs, _, _, ty) when arity sort ty <> None -> xs
    | _ -> []

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
  (* The judgments and the constructors as their HOAS versions; [hjdg] does
    not depend on the term type *)
  let hctor i =
    let c = Names.GlobRef.ConstructRef (ops.ops_si.ctor, i + 1) in
    mkAppC (Cexpr.gref' C.Jdg.hctor, [ Cexpr.gref c ])
  in
  let defs =
    List.mapi (fun k h ->
      (h.ph_name, Cexpr.app_expl C.Jdg.hjdg [ Cexpr.hole ; shc ; idx_expr k ])
    ) hs @
    List.mapi (fun i c -> (c, hctor i)) (Array.to_list sign.Signature.ctor_names)
  in
  let hoas e =
    List.fold_right
      (fun (x, v) body -> mkLetInC (CAst.make (Names.Name x), v, None, body))
      defs e
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
    let bs = List.map (typed sort) r.pr_binders in
    shaped C.Jdg.hrule [
      idx_expr k ;
      Cexpr.string (Names.Id.to_string r.pr_name) ;
      Cexpr.list (params sort bs) ;
      (* [hfun [] R] is [R]: no lambda for a rule without binders *)
      (if bs = [] then Fun.id else mkCLambdaN (List.map (hbinder sort) bs))
        (Cexpr.pair (prems (metas sort bs) r.pr_prems) (hoas r.pr_concl))
    ]
  in
  (* The rules of each block as a list, the blocks as a tuple *)
  let block k (_, rs) = Cexpr.list (List.map (rule k) rs) in
  mkCastC (
    List.fold_right Cexpr.pair (List.mapi block blocks) (Cexpr.gref' C.tt),
    Some Constr.DEFAULTcast,
    Cexpr.app_expl C.Jdg.jdg_desc [ Cexpr.hole ; mkIdentC sort ; shc ]
  )

(** The shape of an argument type: the sort is [t_term], any other type
  [t_base] *)
let shape_of (sort : Names.Id.t) (ty : Constrexpr.constr_expr) :
  Constrexpr.constr_expr =
  if Cexpr.is_ident sort ty then Cexpr.gref' C.Jdg.t_term
  else Constrexpr_ops.mkAppC (Cexpr.gref' C.Jdg.t_base, [ ty ])

(** The judgment of a variable, from the header: each argument is the variable
  or one of the declarations [d1 ... dn], picked by position; [_] names none. *)
let selection (h : header) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
  let rec pos k =
    if k = 0 then Cexpr.gref' C.Jdg.pos0
    else mkAppC (Cexpr.gref' C.Jdg.posS, [ pos (k - 1) ])
  in
  let sel a s =
    let rec index k = function
      | [] -> None
      | d :: ds ->
        if Names.Name.equal (Names.Name a) d.CAst.v then Some k
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
  if not (Names.Id.equal h.ph_jdg h.ph_name) then
    Log.error "Sulfur Judgment: the variable rule must conclude %s."
      (Names.Id.to_string h.ph_name) ;
  List.fold_right sel h.ph_args (Cexpr.gref' C.Jdg.sel_nil)

(** The shapes of the headers, as the Gallina expression
  [shapes [d] [jshape_of [a1 ; ... ; am] (sel of the variable rule) ; ...]]:
  a declaration is a product of shapes ([unit] for none). The judgments of a
  block declare the same thing. *)
let shapes_expr (hs : header list) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
  let sign, _ = saved_ops () in
  let sort = sign.Signature.sort_name in
  let h0 = List.hd hs in
  let dsh =
    Cexpr.list (List.map (shape_of sort) (decl_components h0.ph_decl))
  in
  let jshape (h : header) =
    if not (constr_expr_eq h.ph_decl h0.ph_decl) then
      Log.error ?loc:h.ph_decl.CAst.loc
        "Sulfur Judgment: the judgments of a block declare the same thing." ;
    let jsh =
      Cexpr.list (List.map (shape_of sort) (fst (Cexpr.arrows h.ph_type)))
    in
    mkAppC (Cexpr.gref' C.Jdg.jshape_of, [ Cexpr.hole ; jsh ; selection h ])
  in
  mkAppC (Cexpr.gref' C.Jdg.shapes, [ dsh ; Cexpr.list (List.map jshape hs) ])

(** [Sulfur Judgment header := rules with ...]: the shapes are declared as the
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
