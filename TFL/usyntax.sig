(*  Title:      TFL/usyntax
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Emulation of HOL's abstract syntax functions
*)

signature USyntax_sig =
sig
  structure Utils : Utils_sig

  datatype lambda = VAR   of {Name : string, Ty : typ}
                  | CONST of {Name : string, Ty : typ}
                  | COMB  of {Rator: term, Rand : term}
                  | LAMB  of {Bvar : term, Body : term}

  val alpha : typ

  (* Types *)
  val type_vars  : typ -> typ list
  val type_varsl : typ list -> typ list
  val mk_vartype : string -> typ
  val is_vartype : typ -> bool
  val strip_prod_type : typ -> typ list

  (* Terms *)
  val free_vars_lr : term -> term list
  val type_vars_in_term : term -> typ list
  val dest_term  : term -> lambda
  
  (* Prelogic *)
  val inst      : (typ*typ) list -> term -> term

  (* Construction routines *)
  val mk_abs    :{Bvar  : term, Body : term} -> term

  val mk_imp    :{ant : term, conseq :  term} -> term
  val mk_select :{Bvar : term, Body : term} -> term
  val mk_forall :{Bvar : term, Body : term} -> term
  val mk_exists :{Bvar : term, Body : term} -> term
  val mk_conj   :{conj1 : term, conj2 : term} -> term
  val mk_disj   :{disj1 : term, disj2 : term} -> term
  val mk_pabs   :{varstruct : term, body : term} -> term

  (* Destruction routines *)
  val dest_const: term -> {Name : string, Ty : typ}
  val dest_comb : term -> {Rator : term, Rand : term}
  val dest_abs  : term -> {Bvar : term, Body : term}
  val dest_eq     : term -> {lhs : term, rhs : term}
  val dest_imp    : term -> {ant : term, conseq : term}
  val dest_forall : term -> {Bvar : term, Body : term}
  val dest_exists : term -> {Bvar : term, Body : term}
  val dest_neg    : term -> term
  val dest_conj   : term -> {conj1 : term, conj2 : term}
  val dest_disj   : term -> {disj1 : term, disj2 : term}
  val dest_pair   : term -> {fst : term, snd : term}
  val dest_pabs   : term -> {varstruct : term, body : term}

  val lhs   : term -> term
  val rhs   : term -> term
  val rand  : term -> term

  (* Query routines *)
  val is_imp    : term -> bool
  val is_forall : term -> bool 
  val is_exists : term -> bool 
  val is_neg    : term -> bool
  val is_conj   : term -> bool
  val is_disj   : term -> bool
  val is_pair   : term -> bool
  val is_pabs   : term -> bool

  (* Construction of a term from a list of Preterms *)
  val list_mk_abs    : (term list * term) -> term
  val list_mk_imp    : (term list * term) -> term
  val list_mk_forall : (term list * term) -> term
  val list_mk_conj   : term list -> term

  (* Destructing a term to a list of Preterms *)
  val strip_comb     : term -> (term * term list)
  val strip_abs      : term -> (term list * term)
  val strip_imp      : term -> (term list * term)
  val strip_forall   : term -> (term list * term)
  val strip_exists   : term -> (term list * term)
  val strip_disj     : term -> term list

  (* Miscellaneous *)
  val mk_vstruct : typ -> term list -> term
  val gen_all    : term -> term
  val find_term  : (term -> bool) -> term -> term option
  val dest_relation : term -> term * term * term
  val is_WFR : term -> bool
  val ARB : typ -> term
end;
