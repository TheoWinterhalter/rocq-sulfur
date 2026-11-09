(** Building and reading Gallina expressions ([Constrexpr.constr_expr]), the
  input of pretyping.
  A command can thus build a term from what the user wrote and let elaboration
  resolve names, implicit arguments and coercions.
*)

(** [gref g] refers to the global [g] by its shortest name. *)
val gref : Names.GlobRef.t -> Constrexpr.constr_expr

(** Same as [gref] but with a lazy global reference. *)
val gref' : Names.GlobRef.t Lazy.t -> Constrexpr.constr_expr

(** A hole [_], to be inferred. *)
val hole : Constrexpr.constr_expr

(** [app_expl g args] is [@g args]: every argument of [g] given explicitly. *)
val app_expl :
  Names.GlobRef.t Lazy.t ->
  Constrexpr.constr_expr list ->
  Constrexpr.constr_expr

(** [nat n] is the literal [n%nat]. *)
val nat : int -> Constrexpr.constr_expr

(** [string s] is the string [s], built with its constructors. *)
val string : string -> Constrexpr.constr_expr

(** [list xs] is the list [xs], written with [cons] and [nil]. *)
val list : Constrexpr.constr_expr list -> Constrexpr.constr_expr

(** [pair a b] is [(a, b)]. *)
val pair :
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr

(** [assum xs ty] is the binder [(x1 ... xn : ty)]. *)
val assum :
  Names.lname list ->
  Constrexpr.constr_expr ->
  Constrexpr.local_binder_expr

(** [is_ident x e] tells whether [e] is the identifier [x]. *)
val is_ident : Names.Id.t -> Constrexpr.constr_expr -> bool

(** [arrows ty] is the domains and the codomain of [A1 → ... → An → B]:
  [->] parses as a product, [→] as the notation of [Utf8_core]. *)
val arrows :
  Constrexpr.constr_expr -> Constrexpr.constr_expr list * Constrexpr.constr_expr

(** [products ty] is the factors of a product [A1 * ... * An] (however nested),
  [[ty]] when [ty] is not one. *)
val products : Constrexpr.constr_expr -> Constrexpr.constr_expr list

(** [prod [A1 ; ... ; An]] is the right-nested product [A1 * (... * An)], [unit]
  when empty. *)
val prod : Constrexpr.constr_expr list -> Constrexpr.constr_expr
