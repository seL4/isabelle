(* ========================================================================= *)
(* FIRST ORDER LOGIC LITERALS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Literal =
sig

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic literals.                            *)
(* ------------------------------------------------------------------------- *)

type polarity = bool

type literal = polarity * Atom.atom

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

val polarity : literal -> polarity

val atom : literal -> Atom.atom

val name : literal -> Atom.relationName

val arguments : literal -> Term.term list

val arity : literal -> int

val positive : literal -> bool

val negative : literal -> bool

val negate : literal -> literal

val relation : literal -> Atom.relation

val functions : literal -> NameAritySet.set

val functionNames : literal -> NameSet.set

(* Binary relations *)

val mkBinop : Atom.relationName -> polarity * Term.term * Term.term -> literal

val destBinop : Atom.relationName -> literal -> polarity * Term.term * Term.term

val isBinop : Atom.relationName -> literal -> bool

(* Formulas *)

val toFormula : literal -> Formula.formula

val fromFormula : Formula.formula -> literal

(* ------------------------------------------------------------------------- *)
(* The size of a literal in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

val symbols : literal -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for literals.                                 *)
(* ------------------------------------------------------------------------- *)

val compare : literal * literal -> order  (* negative < positive *)

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

val subterm : literal -> Term.path -> Term.term

val subterms : literal -> (Term.path * Term.term) list

val replace : literal -> Term.path * Term.term -> literal

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Term.var -> literal -> bool

val freeVars : literal -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

val subst : Subst.subst -> literal -> literal

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

val match :  (* raises Error *)
    Subst.subst -> literal -> literal -> Subst.subst

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

val unify :  (* raises Error *)
    Subst.subst -> literal -> literal -> Subst.subst

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val mkEq : Term.term * Term.term -> literal

val destEq : literal -> Term.term * Term.term

val isEq : literal -> bool

val mkNeq : Term.term * Term.term -> literal

val destNeq : literal -> Term.term * Term.term

val isNeq : literal -> bool

val mkRefl : Term.term -> literal

val destRefl : literal -> Term.term

val isRefl : literal -> bool

val mkIrrefl : Term.term -> literal

val destIrrefl : literal -> Term.term

val isIrrefl : literal -> bool

(* The following work with both equalities and disequalities *)

val sym : literal -> literal  (* raises Error if given a refl or irrefl *)

val lhs : literal -> Term.term

val rhs : literal -> Term.term

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val typedSymbols : literal -> int

val nonVarTypedSubterms : literal -> (Term.path * Term.term) list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp : literal Parser.pp

val toString : literal -> string

val fromString : string -> literal

val parse : Term.term Parser.quotation -> literal

end
