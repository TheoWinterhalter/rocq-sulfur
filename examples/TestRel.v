From Sulfur Require Export All.

Sulfur Syntax
{{
  term : Type

  Ty : {{nat}} -> term
  Pi : term -> (bind term in term) -> term
  lam : (bind term in term) -> term
  app : term -> term -> term
}}.

Ren Generate {{
  Relation uconv : term -> term -> Prop, Declaring unit in Γ;

  Rule my_urefl :
    Variables : (t : term)
    Premises :
    Conclusion : uconv t t
  ;
  Rule my_usym :
    Variables : (s t : term)
    Premises :
      Ind(uconv s t)
    Conclusion : uconv s t
  ;
  Rule my_utrans :
    Variables : (s t u : term)
    Premises :
      Ind (uconv s t)
      Ind (uconv t u)
    Conclusion : uconv s u
  ;

  Rule my_ucongr_app :
    Variables : (t u t' u' : term)
    Premises :
      Ind (uconv t t')
      Ind (uconv u u')
    Conclusion :
      uconv (app t u) (app t' u')
  ;
  Rule my_ucongr_Pi :
    Variables : (A B A' B' : term)
    Premises :
      Ind (uconv A A')
      Ind (uconv B B')
    Conclusion :
      uconv (Pi A B) (Pi A' B')
  ;
  Rule my_ucongr_lam :
    Variables : (b b' : term)
    Premises :
      Ind (uconv b b')
    Conclusion :
      uconv (lam b) (lam b')
  ;

  Rule my_ubeta :
    Variables : (b u : term)
    Premises :
    Conclusion :
      uconv (app (lam b) u) (substitute (scons u sid) b)
  ;
}}.

Print uconv.

Ren Generate {{
  Relation type : term -> term -> Prop, Declaring term in Γ;

  Rule my_type_Ty :
    Variables : (n : nat)
    Premises :
    Conclusion :
      type (Ty n) (Ty (S n))
  ;
  Rule my_type_Pi :
    Variables :(n m : nat) (A B : term)
    Premises :
      Ind (type A (Ty n))
      Ind (type B (Ty m))
    Conclusion :
      type (Pi A B) (Ty (Nat.max n m))
  ;

  Rule my_type_app :
    Variables : (A B t u : term)
    Premises :
      Ind (type t (Pi A B))
      Ind (type u A)
    Conclusion :
      type (app t u) (substitute (scons u sid) B)
  ;
  Rule my_type_conv :
    Variables : (A A' t : term)
    Premises :
      Ind (type t A)
      Pred (uconv (List.map (fun _ => tt) Γ) A A')
    Conclusion :
      type t A'
  ;
  Rule my_type_lam :
    Variables : (A B b : term)
    Premises :
      Ind (extend A in type b B)
    Conclusion :
      type (lam b) (Pi A B)
  ;
}}.

Print type.

Ren Generate {{
  Relation conv : term -> term -> term -> Prop, Declaring term in Γ;
  Relation typ : term -> term -> Prop, Declaring term in Γ;

  (* Conversion rules *)
  Rule my_refl :
    Variables : (t A : term)
    Premises :
      Ind (typ t A)
    Conclusion : conv t t A
  ;
  Rule my_sym :
    Variables : (s t A : term)
    Premises :
      Ind(conv s t A)
    Conclusion : conv s t A
  ;
  Rule my_trans :
    Variables : (s t u A : term)
    Premises :
      Ind (conv s t A)
      Ind (conv t u A)
    Conclusion : conv s u A
  ;

  Rule my_congr_app :
    Variables : (t u t' u' A B : term)
    Premises :
      Ind (conv t t' (Pi A B))
      Ind (conv u u' A)
    Conclusion :
      conv (app t u) (app t' u') (substitute (scons u sid) B)
  ;
  Rule my_congr_Pi :
    Variables : (A B A' B' : term) (n m : nat)
    Premises :
      Ind (conv A A' (Ty n))
      Ind (conv B B' (Ty m))
    Conclusion :
      conv (Pi A B) (Pi A' B') (Ty (Nat.max n m))
  ;
  Rule my_congr_lam :
    Variables : (b b' A B : term)
    Premises :
      Ind (extend A in conv b b' B)
    Conclusion :
      conv (lam b) (lam b') (Pi A B)
  ;

  Rule my_beta :
    Variables : (b u A B : term)
    Premises :
      Ind (extend A in typ b B)
      Ind (typ u A)
    Conclusion :
      conv (app (lam b) u) (substitute (scons u sid) b) (substitute (scons u sid) B)
  ;

  (* Typing rules *)
  Rule my_typ_Ty :
    Variables : (n : nat)
    Premises :
    Conclusion :
      typ (Ty n) (Ty (S n))
  ;
  Rule my_typ_Pi :
    Variables : (n m : nat) (A B : term)
    Premises :
      Ind (typ A (Ty n))
      Ind (typ B (Ty m))
    Conclusion :
      typ (Pi A B) (Ty (Nat.max n m))
  ;

  Rule my_typ_app :
    Variables : (A B t u : term)
    Premises :
      Ind (typ t (Pi A B))
      Ind (typ u A)
    Conclusion :
      typ (app t u) (substitute (scons u sid) B)
  ;
  Rule my_typ_lam :
    Variables : (A B b : term)
    Premises :
      Ind (extend A in typ b B)
    Conclusion :
      typ (lam b) (Pi A B)
  ;

  Rule my_typ_conv :
    Variables : (A A' t : term) (n : nat)
    Premises :
      Ind (typ t A)
      Ind (conv A A' (Ty n))
    Conclusion :
      typ t A'
  ;
}}.

Print conv.
