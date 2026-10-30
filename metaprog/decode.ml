(** Decoding Gallina values into OCaml values. *)

open Monad

let lib (name : string) : Names.GlobRef.t Lazy.t = lazy (Rocqlib.lib_ref name)

let decode ?(whd = true) (what : string)
  (cases : (Names.GlobRef.t Lazy.t * (EConstr.t array -> 'a m)) list)
  (t : EConstr.t) : 'a m =
  let* env = get_env in
  let* sigma = get_sigma in
  let t = if whd then Reductionops.whd_all env sigma t else t in
  let f, args = EConstr.decompose_app sigma t in
  let is g = EConstr.isRefX env sigma (Lazy.force g) f in
  match List.find_opt (fun (g, _) -> is g) cases with
  | Some (_, k) -> k args
  | None ->
    CErrors.user_err Pp.(
      str "Expected " ++ str what ++ str " but got " ++
      Printer.pr_econstr_env env sigma t
    )

let decode_bool : EConstr.t -> bool m =
  decode "a boolean" [
    lib "core.bool.true", (fun _ -> ret true) ;
    lib "core.bool.false", (fun _ -> ret false)
  ]

let rec decode_nat (t : EConstr.t) : int m =
  decode "a natural number" [
    lib "num.nat.O", (fun _ -> ret 0) ;
    lib "num.nat.S", (fun a -> let* n = decode_nat a.(0) in ret (n + 1))
  ] t

let rec decode_list (t : EConstr.t) : EConstr.t list m =
  decode "a list" [
    lib "core.list.nil", (fun _ -> ret []) ;
    lib "core.list.cons", fun a ->
      let* l = decode_list a.(2) in
      ret (a.(1) :: l)
  ] t

(** The bits of an [Ascii] are given least significant first. *)
let decode_ascii : EConstr.t -> char m =
  decode "a character" [
    lib "core.ascii.ascii", fun bits ->
      let* bits = List.monad_map decode_bool (Array.to_list bits) in
      let bit b n = 2 * n + if b then 1 else 0 in
      ret @@ Char.chr @@ List.fold_right bit bits 0
  ]

let rec decode_string (t : EConstr.t) : string m =
  decode "a string" [
    lib "core.string.empty", (fun _ -> ret "") ;
    lib "core.string.string", fun a ->
      let* c = decode_ascii a.(0) in
      let* s = decode_string a.(1) in
      ret (String.make 1 c ^ s)
  ] t
