(* ========================================================================= *)
(* INTERFACE TO TPTP PROBLEM FILES                                           *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Tptp =
sig

(* ------------------------------------------------------------------------- *)
(* Mapping TPTP functions and relations to different names.                  *)
(* ------------------------------------------------------------------------- *)

val functionMapping : {name : string, arity : int, tptp : string} list ref

val relationMapping : {name : string, arity : int, tptp : string} list ref

(* ------------------------------------------------------------------------- *)
(* TPTP literals.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype literal =
    Boolean of bool
  | Literal of Literal.literal

val negate : literal -> literal

val literalFunctions : literal -> NameAritySet.set

val literalRelation : literal -> Atom.relation option

val literalFreeVars : literal -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* TPTP formulas.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    CnfFormula of {name : string, role : string, clause : literal list}
  | FofFormula of {name : string, role : string, formula : Formula.formula}

val formulaFunctions : formula -> NameAritySet.set

val formulaRelations : formula -> NameAritySet.set

val formulaFreeVars : formula -> NameSet.set

val formulaIsConjecture : formula -> bool

val ppFormula : formula Parser.pp

val parseFormula : char Stream.stream -> formula Stream.stream

val formulaToString : formula -> string

val formulaFromString : string -> formula

(* ------------------------------------------------------------------------- *)
(* TPTP problems.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype goal =
    Cnf of Problem.problem
  | Fof of Formula.formula

type problem = {comments : string list, formulas : formula list}

val read : {filename : string} -> problem

val write : {filename : string} -> problem -> unit

val hasConjecture : problem -> bool

val toGoal : problem -> goal

val fromProblem : Problem.problem -> problem

val prove : {filename : string} -> bool

end
