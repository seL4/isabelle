(* ========================================================================= *)
(* CLAUSE = ID + THEOREM                                                     *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Clause =
sig

(* ------------------------------------------------------------------------- *)
(* A type of clause.                                                         *)
(* ------------------------------------------------------------------------- *)

datatype literalOrder =
    NoLiteralOrder
  | UnsignedLiteralOrder
  | PositiveLiteralOrder

type parameters =
     {ordering : KnuthBendixOrder.kbo,
      orderLiterals : literalOrder,
      orderTerms : bool}

type clauseId = int

type clauseInfo = {parameters : parameters, id : clauseId, thm : Thm.thm}

type clause

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val newId : unit -> clauseId

val mk : clauseInfo -> clause

val dest : clause -> clauseInfo

val id : clause -> clauseId

val thm : clause -> Thm.thm

val equalThms : clause -> clause -> bool

val literals : clause -> Thm.clause

val isTautology : clause -> bool

val isContradiction : clause -> bool

(* ------------------------------------------------------------------------- *)
(* The term ordering is used to cut down inferences.                         *)
(* ------------------------------------------------------------------------- *)

val largestLiterals : clause -> LiteralSet.set

val largestEquations :
    clause -> (Literal.literal * Rewrite.orient * Term.term) list

val largestSubterms :
    clause -> (Literal.literal * Term.path * Term.term) list

val allSubterms : clause -> (Literal.literal * Term.path * Term.term) list

(* ------------------------------------------------------------------------- *)
(* Subsumption.                                                              *)
(* ------------------------------------------------------------------------- *)

val subsumes : clause Subsume.subsume -> clause -> bool

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id.                          *)
(* ------------------------------------------------------------------------- *)

val freshVars : clause -> clause

val simplify : clause -> clause option

val reduce : Units.units -> clause -> clause

val rewrite : Rewrite.rewrite -> clause -> clause

(* ------------------------------------------------------------------------- *)
(* Inference rules: these generate new clause ids.                           *)
(* ------------------------------------------------------------------------- *)

val factor : clause -> clause list

val resolve : clause * Literal.literal -> clause * Literal.literal -> clause

val paramodulate :
    clause * Literal.literal * Rewrite.orient * Term.term ->
    clause * Literal.literal * Term.path * Term.term -> clause

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val showId : bool ref

val pp : clause Parser.pp

end
