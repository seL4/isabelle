signature USyntax_sig =
sig
  structure Utils : Utils_sig

  type Type
  type Term
  type Preterm
  type 'a binding

  datatype lambda = VAR   of {Name : string, Ty : Type}
                  | CONST of {Name : string, Ty : Type}
                  | COMB  of {Rator: Preterm, Rand : Preterm}
                  | LAMB  of {Bvar : Preterm, Body : Preterm}

  val alpha : Type
  val bool  : Type
  val mk_preterm : Term -> Preterm
  val drop_Trueprop : Preterm -> Preterm

  (* Types *)
  val type_vars  : Type -> Type list
  val type_varsl : Type list -> Type list
  val mk_type    : {Tyop: string, Args:Type list} -> Type
  val dest_type  : Type -> {Tyop : string, Args : Type list}
  val mk_vartype : string -> Type
  val is_vartype : Type -> bool
  val -->        : Type * Type -> Type
  val strip_type : Type -> Type list * Type
  val strip_prod_type : Type -> Type list
  val match_type: Type -> Type -> Type binding list

  (* Terms *)
  val free_vars  : Preterm -> Preterm list
  val free_varsl : Preterm list -> Preterm list
  val free_vars_lr : Preterm -> Preterm list
  val all_vars   : Preterm -> Preterm list
  val all_varsl  : Preterm list -> Preterm list
  val variant    : Preterm list -> Preterm -> Preterm
  val type_of    : Preterm -> Type
  val type_vars_in_term : Preterm -> Type list
  val dest_term  : Preterm -> lambda
  
  (* Prelogic *)
  val aconv     : Preterm -> Preterm -> bool
  val subst     : Preterm binding list -> Preterm -> Preterm
  val inst      : Type binding list -> Preterm -> Preterm
  val beta_conv : Preterm -> Preterm

  (* Construction routines *)
  val mk_prop   :Preterm -> Preterm
  val mk_var    :{Name : string, Ty : Type} -> Preterm
  val mk_const  :{Name : string, Ty : Type} -> Preterm
  val mk_comb   :{Rator : Preterm, Rand : Preterm} -> Preterm
  val mk_abs    :{Bvar  : Preterm, Body : Preterm} -> Preterm

  val mk_eq     :{lhs : Preterm, rhs : Preterm} -> Preterm
  val mk_imp    :{ant : Preterm, conseq :  Preterm} -> Preterm
  val mk_select :{Bvar : Preterm, Body : Preterm} -> Preterm
  val mk_forall :{Bvar : Preterm, Body : Preterm} -> Preterm
  val mk_exists :{Bvar : Preterm, Body : Preterm} -> Preterm
  val mk_conj   :{conj1 : Preterm, conj2 : Preterm} -> Preterm
  val mk_disj   :{disj1 : Preterm, disj2 : Preterm} -> Preterm
  val mk_pabs   :{varstruct : Preterm, body : Preterm} -> Preterm

  (* Destruction routines *)
  val dest_var  : Preterm -> {Name : string, Ty : Type}
  val dest_const: Preterm -> {Name : string, Ty : Type}
  val dest_comb : Preterm -> {Rator : Preterm, Rand : Preterm}
  val dest_abs  : Preterm -> {Bvar : Preterm, Body : Preterm}
  val dest_eq     : Preterm -> {lhs : Preterm, rhs : Preterm}
  val dest_imp    : Preterm -> {ant : Preterm, conseq : Preterm}
  val dest_select : Preterm -> {Bvar : Preterm, Body : Preterm}
  val dest_forall : Preterm -> {Bvar : Preterm, Body : Preterm}
  val dest_exists : Preterm -> {Bvar : Preterm, Body : Preterm}
  val dest_neg    : Preterm -> Preterm
  val dest_conj   : Preterm -> {conj1 : Preterm, conj2 : Preterm}
  val dest_disj   : Preterm -> {disj1 : Preterm, disj2 : Preterm}
  val dest_pair   : Preterm -> {fst : Preterm, snd : Preterm}
  val dest_pabs   : Preterm -> {varstruct : Preterm, body : Preterm}

  val lhs   : Preterm -> Preterm
  val rhs   : Preterm -> Preterm
  val rator : Preterm -> Preterm
  val rand  : Preterm -> Preterm
  val bvar  : Preterm -> Preterm
  val body  : Preterm -> Preterm
  

  (* Query routines *)
  val is_var  : Preterm -> bool
  val is_const: Preterm -> bool
  val is_comb : Preterm -> bool
  val is_abs  : Preterm -> bool
  val is_eq     : Preterm -> bool
  val is_imp    : Preterm -> bool
  val is_forall : Preterm -> bool 
  val is_exists : Preterm -> bool 
  val is_neg    : Preterm -> bool
  val is_conj   : Preterm -> bool
  val is_disj   : Preterm -> bool
  val is_pair   : Preterm -> bool
  val is_pabs   : Preterm -> bool

  (* Construction of a Preterm from a list of Preterms *)
  val list_mk_comb   : (Preterm * Preterm list) -> Preterm
  val list_mk_abs    : (Preterm list * Preterm) -> Preterm
  val list_mk_imp    : (Preterm list * Preterm) -> Preterm
  val list_mk_forall : (Preterm list * Preterm) -> Preterm
  val list_mk_exists : (Preterm list * Preterm) -> Preterm
  val list_mk_conj   : Preterm list -> Preterm
  val list_mk_disj   : Preterm list -> Preterm

  (* Destructing a Preterm to a list of Preterms *)
  val strip_comb     : Preterm -> (Preterm * Preterm list)
  val strip_abs      : Preterm -> (Preterm list * Preterm)
  val strip_imp      : Preterm -> (Preterm list * Preterm)
  val strip_forall   : Preterm -> (Preterm list * Preterm)
  val strip_exists   : Preterm -> (Preterm list * Preterm)
  val strip_conj     : Preterm -> Preterm list
  val strip_disj     : Preterm -> Preterm list
  val strip_pair     : Preterm -> Preterm list

  (* Miscellaneous *)
  val mk_vstruct : Type -> Preterm list -> Preterm
  val gen_all    : Preterm -> Preterm
  val find_term  : (Preterm -> bool) -> Preterm -> Preterm
  val find_terms : (Preterm -> bool) -> Preterm -> Preterm list
  val dest_relation : Preterm -> Preterm * Preterm * Preterm
  val is_WFR : Preterm -> bool
  val ARB : Type -> Preterm

  (* Prettyprinting *)
  val Term_to_string : Term -> string
end;
