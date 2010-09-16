(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)
(* ========================================================================= *)

signature Formula =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic formulas.                                     *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    True
  | False
  | Atom of Atom.atom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of Term.var * formula
  | Exists of Term.var * formula

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Booleans *)

val mkBoolean : bool -> formula

val destBoolean : formula -> bool

val isBoolean : formula -> bool

val isTrue : formula -> bool

val isFalse : formula -> bool

(* Functions *)

val functions : formula -> NameAritySet.set

val functionNames : formula -> NameSet.set

(* Relations *)

val relations : formula -> NameAritySet.set

val relationNames : formula -> NameSet.set

(* Atoms *)

val destAtom : formula -> Atom.atom

val isAtom : formula -> bool

(* Negations *)

val destNeg : formula -> formula

val isNeg : formula -> bool

val stripNeg : formula -> int * formula

(* Conjunctions *)

val listMkConj : formula list -> formula

val stripConj : formula -> formula list

val flattenConj : formula -> formula list

(* Disjunctions *)

val listMkDisj : formula list -> formula

val stripDisj : formula -> formula list

val flattenDisj : formula -> formula list

(* Equivalences *)

val listMkEquiv : formula list -> formula

val stripEquiv : formula -> formula list

val flattenEquiv : formula -> formula list

(* Universal quantification *)

val destForall : formula -> Term.var * formula

val isForall : formula -> bool

val listMkForall : Term.var list * formula -> formula

val setMkForall : NameSet.set * formula -> formula

val stripForall : formula -> Term.var list * formula

(* Existential quantification *)

val destExists : formula -> Term.var * formula

val isExists : formula -> bool

val listMkExists : Term.var list * formula -> formula

val setMkExists : NameSet.set * formula -> formula

val stripExists : formula -> Term.var list * formula

(* ------------------------------------------------------------------------- *)
(* The size of a formula in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

val symbols : formula -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for formulas.                                 *)
(* ------------------------------------------------------------------------- *)

val compare : formula * formula -> order

val equal : formula -> formula -> bool

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Term.var -> formula -> bool

val freeVars : formula -> NameSet.set

val freeVarsList : formula list -> NameSet.set

val specialize : formula -> formula

val generalize : formula -> formula

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

val subst : Subst.subst -> formula -> formula

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val mkEq : Term.term * Term.term -> formula

val destEq : formula -> Term.term * Term.term

val isEq : formula -> bool

val mkNeq : Term.term * Term.term -> formula

val destNeq : formula -> Term.term * Term.term

val isNeq : formula -> bool

val mkRefl : Term.term -> formula

val destRefl : formula -> Term.term

val isRefl : formula -> bool

val sym : formula -> formula  (* raises Error if given a refl *)

val lhs : formula -> Term.term

val rhs : formula -> Term.term

(* ------------------------------------------------------------------------- *)
(* Splitting goals.                                                          *)
(* ------------------------------------------------------------------------- *)

val splitGoal : formula -> formula list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

type quotation = formula Parse.quotation

val pp : formula Print.pp

val toString : formula -> string

val fromString : string -> formula

val parse : quotation -> formula

end
