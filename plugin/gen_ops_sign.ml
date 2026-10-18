open Prelude
open Signature
module C = Constants

module Make (P : sig
  val sign : signature
  val ops_conc : ops_concrete
end) =
struct
  (**************************************************************************************)
  (** *** Build the signature. *)
  (**************************************************************************************)

  (** Build the inductive [Inductive base := B0 | B1 | ...] which indexes base types. *)
  let build_base () : Names.Ind.t m =
    let names =
      List.init (Array.length P.sign.base_types) @@ fun i ->
      Names.Id.of_string_soft ("B" ^ string_of_int i)
    in
    let types =
      List.init (Array.length P.sign.base_types) @@ fun _ ind -> ret @@ EConstr.mkVar ind
    in
    declare_ind (Names.Id.of_string_soft "base") EConstr.mkSet names types

  (** Build the function [eval_base : base -> Type]. *)
  let build_eval_base (base : Names.Ind.t) : EConstr.t m =
    lambda "b" (mkind base) @@ fun b ->
    (* If there are no base types, Rocq can't infer the return type of the pattern match. *)
    let return _ _ : EConstr.t m =
      if Array.length P.sign.base_types = 0 then ret EConstr.mkSet else fresh_evar None
    in
    case (EConstr.mkVar b) ~return @@ fun i _ -> ret P.sign.base_types.(i)

  (** Build the inductive [Inductive ctor := CApp | CLam | ...] which indexes non-variable
      constructors. *)
  let build_ctor () : Names.Ind.t m =
    let names =
      List.init P.sign.n_ctors @@ fun i ->
      Names.Id.of_string_soft ("C" ^ Names.Id.to_string P.sign.ctor_names.(i))
    in
    let types = List.init P.sign.n_ctors @@ fun _ ind -> ret @@ EConstr.mkVar ind in
    declare_ind (Names.Id.of_string_soft "ctor") EConstr.mkSet names types

  (** Helper function to make a Rocq list with elements [xs]. Each element must be of type
      [ty]. *)
  let rec mklist (ty : EConstr.t) (xs : EConstr.t list) : EConstr.t =
    match xs with
    | [] -> app (mkglob' C.nil) ty
    | x :: xs -> apps (mkglob' C.cons) [| ty; x; mklist ty xs |]

  (** Build the function [ctor_type : ctor -> list (@arg_ty base)]. *)
  let build_ctor_type (ctor : Names.Ind.t) (base : Names.Ind.t) : EConstr.t m =
    let rec on_arg_ty (ty : arg_ty) : EConstr.t =
      match ty with
      | AT_base i -> apps (mkglob' C.at_base) [| mkind base; mkctor (base, i + 1) |]
      | AT_term -> apps (mkglob' C.at_term) [| mkind base |]
      | AT_bind ty -> apps (mkglob' C.at_bind) [| mkind base; on_arg_ty ty |]
    in
    lambda "c" (mkind ctor) @@ fun c ->
    (* When [ctor] is empty, Rocq can't infer the return type of the pattern match. *)
    let return _ _ : EConstr.t m =
      ret @@ app (mkglob' C.list) @@ apps (mkglob' C.arg_ty) [| mkind base |]
    in
    case (EConstr.mkVar c) ~return @@ fun i _ ->
    ret
    @@ mklist (apps (mkglob' C.arg_ty) [| mkind base |])
    @@ List.map on_arg_ty P.sign.ctor_types.(i)
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Derive [Enum] for an inductive type of the right shape (enumeration).
  [name] is used to give a name to the proof.
  [nctors] is the number of constructors.
*)
let derive_enum (name : string) (ind : Names.Ind.t) nctors :
    Names.Constant.t =
  let t = mkind ind in
  let ctors =
    List.init nctors (fun i -> mkctor (ind, i + 1))
  in
  let nat = mkglob' C.nat in
  let rec nat_lit i =
    if i = 0 then mkglob' C.zero
    else app (mkglob' C.succ) (nat_lit (i - 1))
  in
  let index_of =
    def (name ^ "_index_of") @@
    lambda "x" t @@
    fun x -> case (EConstr.mkVar x) ~return:(fun _ _ -> ret nat) @@
    fun i _ -> ret (nat_lit i)
  in
  let index_of = mkconst index_of in
  let enum =
    List.fold_right (fun c l ->
      apps (mkglob' C.cons) [| t ; c ; l |]
    ) ctors (app (mkglob' C.nil) t)
  in
  let inv =
    lemma (name ^ "_enum_all_in")
      (ret @@ apps (mkglob (pre_ref "enum_all_in")) [| t ; enum ; index_of |])
      (pre_ltac "sulfur_is_enum" [])
  in
  let inv = mkconst inv in
  let enum =
    def ~kind:Decls.Instance (name ^ "_Enum") @@ ret @@
    apps (mkglob (pre_ref "mkenum")) [| t ; enum ; index_of ; inv |]
  in
  Classes.existing_instance Hints.Export (Names.GlobRef.ConstRef enum) None ;
  enum

(** Generate the level one signature. *)
let generate (sign : signature) (ops_conc : ops_concrete) : ops_sign =
  let module M = Make (struct
    let sign = sign
    let ops_conc = ops_conc
  end) in
  (* Build the signature. *)
  let base = monad_run @@ M.build_base () in
  let base_enum = derive_enum "base" base (Array.length sign.base_types) in
  let eval_base = def "eval_base" @@ M.build_eval_base base in
  let ctor = monad_run @@ M.build_ctor () in
  let ctor_enum = derive_enum "ctor" ctor sign.n_ctors in
  let ctor_type = def "ctor_type" @@ M.build_ctor_type ctor base in
  let sign =
    def "sign" @@ ret
    @@ apps (mkglob' C.build_signature)
         [| mkind base
          ; mkconst base_enum
          ; mkconst eval_base
          ; mkind ctor
          ; mkconst ctor_enum
          ; mkconst ctor_type
         |]
  in
  (* Assemble everything. *)
  { base; base_enum; eval_base; ctor; ctor_enum; ctor_type; sign }
