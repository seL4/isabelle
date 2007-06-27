(* ========================================================================= *)
(* FIRST ORDER LOGIC ATOMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Atom =
sig

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic atoms.                               *)
(* ------------------------------------------------------------------------- *)

type relationName = Name.name

type relation = relationName * int

type atom = relationName * Term.term list

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

val name : atom -> relationName

val arguments : atom -> Term.term list

val arity : atom -> int

val relation : atom -> relation

val functions : atom -> NameAritySet.set

val functionNames : atom -> NameSet.set

(* Binary relations *)

val mkBinop : relationName -> Term.term * Term.term -> atom

val destBinop : relationName -> atom -> Term.term * Term.term

val isBinop : relationName -> atom -> bool

(* ------------------------------------------------------------------------- *)
(* The size of an atom in symbols.                                           *)
(* ------------------------------------------------------------------------- *)

val symbols : atom -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for atoms.                                    *)
(* ------------------------------------------------------------------------- *)

val compare : atom * atom -> order

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

val subterm : atom -> Term.path -> Term.term

val subterms : atom -> (Term.path * Term.term) list

val replace : atom -> Term.path * Term.term -> atom

val find : (Term.term -> bool) -> atom -> Term.path option

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Term.var -> atom -> bool

val freeVars : atom -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

val subst : Subst.subst -> atom -> atom

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

val match : Subst.subst -> atom -> atom -> Subst.subst  (* raises Error *)

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

val unify : Subst.subst -> atom -> atom -> Subst.subst  (* raises Error *)

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val eqRelation : relation

val mkEq : Term.term * Term.term -> atom

val destEq : atom -> Term.term * Term.term

val isEq : atom -> bool

val mkRefl : Term.term -> atom

val destRefl : atom -> Term.term

val isRefl : atom -> bool

val sym : atom -> atom  (* raises Error if given a refl *)

val lhs : atom -> Term.term

val rhs : atom -> Term.term

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val typedSymbols : atom -> int

val nonVarTypedSubterms : atom -> (Term.path * Term.term) list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp : atom Parser.pp

val toString : atom -> string

val fromString : string -> atom

val parse : Term.term Parser.quotation -> atom

end
