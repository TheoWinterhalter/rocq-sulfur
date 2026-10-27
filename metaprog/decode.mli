(** This module provides functions to decode Gallina values
  (closed terms which reduce to literals) into OCaml values.
*)

open Monad

(**
  [decode ?whd what cases t] weak head normalizes [t] (unless [whd] is [false])
  and dispatches on its head: [cases] associates global references to
  continuations, which receive the arguments of the head. It fails with a
  message mentioning [what] if the head matches no case.
*)
val decode :
  ?whd:bool ->
  string ->
  (Names.GlobRef.t Lazy.t * (EConstr.t array -> 'a m)) list ->
  EConstr.t ->
  'a m

(** Decoders for the basic literals of the standard library. *)

val decode_bool : EConstr.t -> bool m
val decode_nat : EConstr.t -> int m
val decode_list : EConstr.t -> EConstr.t list m
val decode_ascii : EConstr.t -> char m
val decode_string : EConstr.t -> string m
