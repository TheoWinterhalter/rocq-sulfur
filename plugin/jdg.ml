(** Implementation of the [Sulfur Judgment] command.

  See [g_plugin.mlg] for the grammar of the command.

  Everything is stated and proven in [theories/JdgDesc.v]:
  this file only computes the constructor types by reduction, and instantiates
  the generic lemmas.
*)

open Prelude
open Jdg_parse
open Jdg_check
module C = Constants

(** A rule for the generation:
  its term in the description, its name, the names of its binders and for each
  premise its judgment ([None] for a predicate). *)
type grule = {
  gr_term : EConstr.t ;
  gr_name : string ;
  gr_binders : string list ;
  gr_prems : int option list
}

let of_prem (p : prem) =
  match p with
  | Jdg (k, _) -> Some k
  | Pred _ -> None

let of_binder (b : binder) =
  match b with
  | BMeta ({ CAst.v = Names.Name x ; _ }, _)
  | BParam ({ CAst.v = Names.Name x ; _ }, _) -> Names.Id.to_string x
  | BMeta _ | BParam _ -> "x"

(** The rule [r] with its term [t] *)
let of_rule (t : EConstr.t) (r : rule) = {
  gr_term = t ;
  gr_name = Names.Id.to_string r.r_name ;
  gr_binders = List.map of_binder r.r_binders ;
  gr_prems = List.map of_prem r.r_prems
}

(** The signature, term type and shapes of a description, from its type
  [jdg_desc sg T sh]. *)
let decode_sig (desc_ty : EConstr.t) : (EConstr.t * EConstr.t * EConstr.t) m =
  let what = "a judgment description" in
  decode ~whd:false
    what
    [ C.Jdg.jdg_desc, fun a -> ret (a.(0), a.(1), a.(2)) ]
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
  the global judgment name (in practice the head of [d_names]),
  the names of its judgments, its signature, term type, shapes, instance and
  laws, and its rules (one list for each judgment).
*)
type desc = {
  d_name : Names.Id.t ;
  d_term : EConstr.t ;
  d_names : Names.Id.t list ;
  d_sg : EConstr.t ;
  d_ty : EConstr.t ;
  d_sh : EConstr.t ;
  d_cs : EConstr.t ;
  d_cl : EConstr.t ;
  d_rules : grule list list
}

(** The family of relations generated from a description: the constants its
  statements may unfold, the mutual inductive, and [jdg_at (R1, (R2, ... tt))]
  which the statements are about. *)
type family = {
  f_transparent : Names.Constant.t list ;
  f_mind : Names.MutInd.t ;
  f_r : EConstr.t ; (* [R] *)
  f_rs : EConstr.t (* [Rs], the packed version *)
}

(** The indices of the judgments, as integers and as terms *)
let indices (d : desc) : int list = List.init (List.length d.d_names) Fun.id
let idx (d : desc) (k : int) : EConstr.t = fin (List.length d.d_names) k

let suffix (name : Names.Id.t) (s : string) : Names.Id.t =
  Names.Id.of_string_soft (Names.Id.to_string name ^ s)

(** The shared lemmas are named after the first judgment *)
let shared (d : desc) (s : string) : string =
  Names.Id.to_string d.d_name ^ s

(** A constant of [JdgDesc] applied to the signature, term type, instance and
  shapes of [d] *)
let jdg (d : desc) (s : Names.GlobRef.t Lazy.t) : EConstr.t =
  apps (mkglob' s) [| d.d_sg ; d.d_ty ; d.d_cs ; d.d_sh |]

let jdg_type (d : desc) : EConstr.t =
  apps (mkglob' C.Jdg.jdg_type) [| d.d_sh ; d.d_ty |]

(** The statement [s d R] about the family *)
let stmt (d : desc) (f : family) (s : Names.GlobRef.t Lazy.t) : EConstr.t m =
  ret (apps (jdg d s) [| d.d_term ; f.f_r |])

(** The constructor [i] of judgment [k]; the variable rule is [1] *)
let ctor (f : family) (k : int) (i : int) : EConstr.t =
  mkctor ((f.f_mind, k), i)

(** Reduce a statement, unfolding only [transparent] *)
let reduce (transparent : Names.Constant.t list) (t : EConstr.t) : EConstr.t m =
  reduce_only transparent t

(** The description [desc] of the judgments [jdg], read *)
let read_desc (jdg : jdg) (d_term : EConstr.t) : desc =
  monad_run begin
    let* desc_ty = typecheck d_term None in
    let* d_sg, d_ty, d_sh = decode_sig desc_ty in
    let* d_cs = resolve_tc (apps (mkglob' C.CS.typ) [| d_sg ; d_ty |]) in
    let* d_cl = resolve_tc (apps (mkglob' C.CS.laws) [| d_sg ; d_ty ; d_cs |]) in
    let* terms = decode_desc d_term in
    let d_rules =
      List.map2 (fun sj ts ->
        List.map2 of_rule ts sj.sj_rules
      ) jdg.j_jdgs terms
    in
    let d_name = jdg.j_name in
    let d_names = jdg.j_names in
    ret @@
    { d_name ; d_term ; d_names ; d_sg ; d_ty ; d_sh ; d_cs ; d_cl ; d_rules }
  end

(** The constants the statements may unfold

  We assume the user does not use the names from Sulfur itself and that those
  are safe to unfold always.

*)
let transparent_constants (d : desc) : Names.Constant.t list m =
  let* ops = decode_cs_ops d.d_cs in
  let* opaque = List.monad_map head_const (d.d_term :: ops) in
  let opaque =
    List.filter_map Fun.id opaque @
    List.map (fun g -> const_of_ref (Lazy.force g)) [
      C.rid ; C.rshift ; C.rcons ; C.rcomp ; C.up_ren ; C.Jdg.cup_subst
    ]
  in
  let library c =
    let file = Names.ModPath.dp (Names.Constant.modpath c) in
    let root = Names.Id.to_string (CList.last (Names.DirPath.repr file)) in
    List.mem root [ "Sulfur" ; "SulfurUtils" ; "Equations" ] ||
    List.mem (Names.Constant.to_string c) [
      "Corelib.Init.Logic.eq_rect" ; "Corelib.Init.Logic.eq_sym" ;
      "Corelib.Init.Logic.False_rect"
    ]
  in
  let is_transp c =
    library c || Names.Cset_env.mem c !generated_consts
  in
  let* env = get_env in
  let transparent =
    (* Might be expensive when the environment is big *)
    Environ.fold_constants (fun c _ cs ->
      if is_transp c then c :: cs else cs
    ) env []
  in
  ret (CList.subtract Names.Constant.CanOrd.equal transparent opaque)

(** The inductives, mutual, each with its variable rule as first constructor.
  Their types come from the shapes, their constructor types are the reduced
  [var_rule_type] and [rule_type], with the meta-variables named as in the
  description. *)
let declare_inductives (d : desc) : family =
  let transparent, arities =
    monad_run begin
      let* transparent = transparent_constants d in
      let* arities =
        List.monad_map (fun k ->
          reduce transparent (app (jdg_type d) (idx d k))
        ) (indices d)
      in
      ret (transparent, arities)
    end
  in
  (* The family of relations [rs] (the inductives, or the variables standing
    for them in their constructor types) *)
  let family (rs : EConstr.t list) : EConstr.t =
    apps (mkglob' C.Jdg.jdg_at)
      [| d.d_sh ; d.d_ty ; tuple (List.combine rs arities) |]
  in
  let on_family f inds = f (family (List.map EConstr.mkVar inds)) in
  let var_type (r : EConstr.t) (k : int) : EConstr.t m =
    reduce transparent (apps (jdg d C.Jdg.var_rule_type) [| r ; idx d k |])
  in
  let rule_type (r : EConstr.t) k (rd : grule) : EConstr.t m =
    let* t =
      reduce transparent (
        apps (jdg d C.Jdg.rule_type) [| r ; idx d k ; rd.gr_term |]
      )
    in
    rename_binders (None :: List.map (fun x -> Some x) rd.gr_binders) t
  in
  let ctor_names =
    List.map2 (fun name rs ->
      suffix name "_var" ::
      List.map (fun rd -> Names.Id.of_string_soft rd.gr_name) rs
    ) d.d_names d.d_rules
  in
  let ctor_types =
    List.mapi (fun k rs ->
      on_family (fun r -> var_type r k) ::
      List.map (fun rd -> on_family (fun r -> rule_type r k rd)) rs
    ) d.d_rules
  in
  let mind =
    monad_run (declare_mut_ind d.d_names arities ctor_names ctor_types)
  in
  let r = List.map (fun k -> mkind (mind, k)) (indices d) in
  {
    f_transparent = transparent ;
    f_mind = mind ;
    f_r = family r ;
    f_rs = tuple (List.combine r arities)
  }

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
      let rschemes =
        List.mapi (fun k id ->
          (CAst.make id, false, (f.f_mind, k), prop)
        ) schemes
      in
      let env = Global.env () in
      Indschemes.do_mutual_induction_scheme ~register:false env rschemes ;
      let combined = suffix d.d_name "_mutind" in
      Indschemes.do_combined_scheme
        (CAst.make combined) (List.map locate schemes) ;
      locate combined
  in
  monad_run begin
    let* p_ty =
      prod "i" (app (mkglob' C.Jdg.jidx) d.d_sh) @@ fun i ->
        ret (app (jdg_type d) (EConstr.mkVar i))
    in
    lambda "P" p_ty @@ fun p ->
      let motives =
        List.map (fun k -> app (EConstr.mkVar p) (idx d k)) (indices d)
      in
      ret (apps (mkconst scheme) (Array.of_list motives))
  end

(** Prove [facts] *)
let facts_lemma (d : desc) (f : family) : Names.Constant.t =
  let vars = List.map (fun k -> ctor f k 1) (indices d) in
  let rules =
    d.d_rules
    |> List.mapi (fun k rs -> List.mapi (fun i _ -> ctor f k (i + 2)) rs)
    |> List.concat
  in
  let leaves = vars @ rules @ [ induction_scheme d f ] in
  lemma (shared d "_facts") (stmt d f C.Jdg.facts) (
    Tacticals.tclTHEN
      (run_ltac "JdgDesc" "facts_tac" [])
      (dispatch (fun k -> Tactics.exact_no_check (List.nth leaves k)))
  )

(** The obligations, located in the description: [ob_pred j r i] for the
  predicate premise [i] of rule [r] of judgment [j], [ob_make i i'] for a
  pair of judgments where a rule of [i] has a premise in [i']; and their list
  as a term, which only depends on the shapes. *)
type obligations = {
  o_preds : (int * int * grule * int) list ;
  o_pairs : (int * int) list ;
  o_term : EConstr.t
}

let obligations (d : desc) : obligations =
  let o_preds =
    List.mapi (fun j rs ->
      List.concat (List.mapi (fun r rd ->
        CList.map_filter_i (fun i p ->
          match p with
          | None -> Some (j, r, rd, i)
          | Some _ -> None
        ) rd.gr_prems
      ) rs)
    ) d.d_rules
    |> List.concat
  in
  let o_pairs =
    List.mapi (fun j rs ->
      List.concat_map (fun rd ->
        List.filter_map (fun p ->
          match p with
          | Some i when i <> j -> Some (j,i)
          | _ -> None
        ) rd.gr_prems
      ) rs
    ) d.d_rules
    |> List.concat
    |> List.sort_uniq compare
  in
  let obs =
    List.map (fun (j, r, _, i) ->
      apps (mkglob' C.Jdg.ob_pred) [| d.d_sh ; idx d j ; mknat r ; mknat i |])
      o_preds
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
        List.map (fun (_, _, rd, _) -> Some rd.gr_binders) o.o_preds @
        List.map (fun _ -> None) o.o_pairs
      )
    in
    let cls =
      def (shared d "_obligations") begin
        let* desc_const = head_const d.d_term in
        let* t =
          reduce (Option.List.cons desc_const f.f_transparent)
            (apps (jdg d C.Jdg.obligations) [| d.d_term ; f.f_rs ; o.o_term |])
        in
        rename_obls t
      end
    in
    Record.declare_existing_class (Names.GlobRef.ConstRef cls) ;
    Some cls
  end

(** [R_obls_wf] checks the list of obligations by computation, then
  [R_subst : ∀ {H : R_obligations}, preserve_subst_jdg Rs i] for every
  judgment, which finds the instance by resolution. *)
let subst_lemmas (d : desc) (f : family) ~facts : unit =
  let o = obligations d in
  let obs = mkconst (def (shared d "_obls") (ret o.o_term)) in
  let ok =
    lemma (shared d "_obls_wf")
      (ret (apps (mkglob' C.Jdg.obls_ok)
        [| d.d_sg ; d.d_ty ; d.d_sh ; d.d_term ; obs |]))
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
      (apps (jdg d C.Jdg.preserve_subst_jdg) [| f.f_rs ; idx d k |])
  in
  let proof h k =
    apps (jdg d C.Jdg.gen_preserve_subst) [|
      d.d_term ; d.d_cl ; f.f_rs ; mkconst facts ; obs ;
      mkconst ok ; h ; idx d k
    |]
  in
  List.iteri (fun k name ->
    let name = Names.Id.to_string name ^ "_subst" in
    match cls with
    | None ->
      ignore @@
      lemma name (stmt k) (
        Tactics.exact_no_check @@
        proof (mkglob (Rocqlib.lib_ref "core.True.I")) k
      )
    | Some cls ->
      let subst =
        lemma name
          (let* concl = stmt k in
            prod "H" (mkconst cls) (fun _ -> ret concl))
          (Tactics.exact_no_check
            (monad_run (lambda "H" (mkconst cls) (fun h ->
              ret (proof (EConstr.mkVar h) k)))))
      in
      Impargs.declare_manual_implicits false (Names.GlobRef.ConstRef subst)
        [ CAst.make (Some (Names.Name (Names.Id.of_string "H"), true)) ]
  ) d.d_names

(** The judgments of [blocks], described by [desc]: the inductives, then the
  lemmas. *)
let generate_desc (jdg : jdg) (desc : EConstr.t) :
  unit =
  let d = read_desc jdg desc in
  let f = declare_inductives d in
  let facts = facts_lemma d f in
  subst_lemmas d f ~facts

(******************************************************************************)
(** *** Judgments written as rules. *)
(******************************************************************************)

let rec ce_iter n f x =
  if n <= 0 then x
  else Constrexpr_ops.mkAppC (f, [ ce_iter (n - 1) f x ])

(** The index [k] of a judgment, as an expression *)
let idx_expr (k : int) : Constrexpr.constr_expr =
  ce_iter k (Cexpr.gref' C.Jdg.finS) (Cexpr.gref' C.Jdg.finO)

(** Binders of a rule *)

(** [hterm → ... → hterm], the type of a meta-variable of arity [n] *)
let rec hterm_n (n : int) : Constrexpr.constr_expr =
  if n = 0 then Cexpr.gref' C.Jdg.hterm
  else
    Constrexpr_ops.mkCProdN
      [ Cexpr.assum [ CAst.make Names.Anonymous ] (Cexpr.gref' C.Jdg.hterm) ]
      (hterm_n (n - 1))

(** The parameters of the rule: a meta-variable of arity [n], or a true
  parameter *)
let params (bs : binder list) : Constrexpr.constr_expr list =
  let open Constrexpr_ops in
  List.map (fun b ->
    match b with
    | BMeta (_, n) -> mkAppC (Cexpr.gref' C.Jdg.rp_term, [ Cexpr.nat n ])
    | BParam (_, ty) -> mkAppC (Cexpr.gref' C.Jdg.rp_param, [ ty ])
  ) bs

(** The binders of the lambda of a rule: a meta-variable of arity [n] is an
  [n]-ary function on [hterm] *)
let hbinders (bs : binder list) : Constrexpr.local_binder_expr list =
  List.map (fun b ->
    match b with
    | BMeta (x, n) -> Cexpr.assum [ x ] (hterm_n n)
    | BParam (x, ty) -> Cexpr.assum [ x ] ty
  ) bs

(** The meta-variables among the binders of a rule *)
let metas (bs : binder list) : Names.lname list =
  List.filter_map (fun b ->
    match b with BMeta (x, _) -> Some x | BParam _ -> None
  ) bs

(** The description written by the user, as the Gallina expression

    [ ([ hrule k "name" ps (λ binders, ([p1 ; ... ; pn], c)) ; ... ],
       (..., tt)) : jdg_desc term ]

  with one list of rules per judgment [k], where [ps] are the parameters, and
  every judgment [pi] or [c] is wrapped as

    [ let R := hjdg in let c := hctor Cc in ... pi ]

  with [R] the judgment and [c] ranging over the constructors that [pi]
  mentiones, so that elaboration resolves them to their HOAS versions.
  A binder [(x : term)] is a meta-variable, typed [hterm] in the lambda
  ([hterm → ... → hterm] for an arity), any other type is a parameter.
  A premise [{{ P }}] is first-order:

    [ hpred n (λ (x1 ... xn : term) (Γ : list term), P) ]

  with [x1 ... xn] the meta-variables of the rule.

  The shapes instance [shapes] is given explicitly wherever the command emits a
  constant that depends on it, so that the types of the predicates reduce during
  elaboration; the bracket and the coercion of judgments find it by unification.
*)
let desc_expr (jdg : jdg) (shapes : Names.Constant.t) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
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
    List.mapi (fun k sj ->
      (sj.sj_name, Cexpr.app_expl C.Jdg.hjdg [ Cexpr.hole ; shc ; idx_expr k ])
    ) jdg.j_jdgs @
    List.mapi (fun i c ->
      (c, hctor i)
    ) (Array.to_list sign.Signature.ctor_names)
  in
  let hoas e =
    let fv = free_vars_of_constr_expr e in
    List.fold_right
      (fun (x, v) body -> mkLetInC (CAst.make (Names.Name x), v, None, body))
      (List.filter (fun (x, _) -> Names.Id.Set.mem x fv) defs) e
  in
  (* [{{ P }}] with meta-variables [xs] (see above); the context is named
    as in the header of the judgment [sj] and typed by the declaration *)
  let pred sj xs e =
    let gamma = CAst.make (Names.Name sj.sj_ctx) in
    let bs =
      [
        Cexpr.assum [ gamma ]
          (mkAppC (Cexpr.gref' C.list, [ jdg.j_decl ]))
      ]
    in
    let bs = if xs = [] then bs else Cexpr.assum xs (mkIdentC sort) :: bs in
    shaped C.Jdg.hpred [ Cexpr.nat (List.length xs) ; mkCLambdaN bs e ]
  in
  (* The premises, as [@cons hprem p l]: with the type explicit.
    A judgment [p] is checked against [hprem] and coerced;
    [cons p l] alone would infer the type from [p] first.
  *)
  let prems sj xs l =
    let prem p =
      match p with
      | Jdg (_, e) -> hoas e
      | Pred e -> pred sj xs e
    in
    let cons p l =
      Cexpr.app_expl C.cons [ shaped C.Jdg.hprem [] ; prem p ; l ]
    in
    List.fold_right cons l (Cexpr.gref' C.nil)
  in
  (* A rule of the [k]th judgment [sj] *)
  let rule k sj r =
    let bs = r.r_binders in
    shaped C.Jdg.hrule [
      idx_expr k ;
      Cexpr.string (Names.Id.to_string r.r_name) ;
      Cexpr.list (params bs) ;
      (* [hfun [] R] is [R]: no lambda for a rule without binders *)
      (if bs = [] then Fun.id else mkCLambdaN (hbinders bs))
        (Cexpr.pair (prems sj (metas bs) r.r_prems) (hoas r.r_concl))
    ]
  in
  (* The rules of each judgment as a list, the judgments as a tuple *)
  let block k sj = Cexpr.list (List.map (rule k sj) sj.sj_rules) in
  mkCastC (
    List.fold_right Cexpr.pair (List.mapi block jdg.j_jdgs) (Cexpr.gref' C.tt),
    Some Constr.DEFAULTcast,
    Cexpr.app_expl C.Jdg.jdg_desc [ Cexpr.hole ; mkIdentC sort ; shc ]
  )

(** The shape of an argument type: the sort is [t_term], any other type
  [t_base] *)
let shape_of arg : Constrexpr.constr_expr =
  match arg with
  | Term -> Cexpr.gref' C.Jdg.t_term
  | Base ty -> Constrexpr_ops.mkAppC (Cexpr.gref' C.Jdg.t_base, [ ty ])

let build_sel (s : sel list) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
  let pos k = ce_iter k (Cexpr.gref' C.Jdg.posS) (Cexpr.gref' C.Jdg.pos0) in
  let mk a s =
    match a with
    | SelVar -> mkAppC (Cexpr.gref' C.Jdg.sel_var, [ s ])
    | SelPos k -> mkAppC (Cexpr.gref' C.Jdg.sel_pos, [ pos k ; s ])
  in
  List.fold_right mk s (Cexpr.gref' C.Jdg.sel_nil)

(** The shapes of the headers, as the Gallina expression
  [shapes [d] [jshape_of [a1 ; ... ; am] (sel of the variable rule) ; ...]]:
  a declaration is a product of shapes ([unit] for none). *)
let shapes_expr (jdg : jdg) : Constrexpr.constr_expr =
  let open Constrexpr_ops in
  let dsh =
    Cexpr.list (List.map shape_of jdg.j_decl_comp)
  in
  let jshape (sj : sjdg) =
    let jsh =
      Cexpr.list (List.map shape_of sj.sj_args)
    in
    mkAppC
      (Cexpr.gref' C.Jdg.jshape_of, [ Cexpr.hole ; jsh ; build_sel sj.sj_sel ])
  in
  let shapes = List.map jshape jdg.j_jdgs in
  mkAppC (Cexpr.gref' C.Jdg.shapes, [ dsh ; Cexpr.list shapes ])

(** [Sulfur Judgment header := rules with ...]: the shapes are declared as the
  instance [R_shapes], the description as [R_desc] (with the local
  definitions substituted), then handled as above.
*)
let generate_rules (pj : pjdg) : unit =
  let jdg = of_pjdg pj in
  let name = Names.Id.to_string jdg.j_name in
  let shapes = def (name ^ "_shapes") (pretype (shapes_expr jdg)) in
  declare_instance shapes ;
  let desc =
    def_typed (name ^ "_desc") begin
      let* d = pretype (desc_expr jdg shapes) in
      let* sigma = get_sigma in
      let d, _, ty = EConstr.destCast sigma d in
      (* Substitute the local definitions *)
      let* d = reduce_only [] d in
      ret (d, Some ty)
    end
  in
  generate_desc jdg (mkconst desc)
