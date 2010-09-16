(* ========================================================================= *)
(* THE TPTP PROBLEM FILE FORMAT                                              *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)
(* ========================================================================= *)

signature Tptp =
sig

(* ------------------------------------------------------------------------- *)
(* Mapping to and from TPTP variable, function and relation names.           *)
(* ------------------------------------------------------------------------- *)

type mapping

val defaultMapping : mapping

val mkMapping :
    {functionMapping : {name : Name.name, arity : int, tptp : string} list,
     relationMapping : {name : Name.name, arity : int, tptp : string} list} ->
    mapping

val addVarSetMapping : mapping -> NameSet.set -> mapping

(* ------------------------------------------------------------------------- *)
(* Interpreting TPTP functions and relations in a finite model.              *)
(* ------------------------------------------------------------------------- *)

val defaultFixedMap : Model.fixedMap

val defaultModel : Model.parameters

val ppFixedMap : mapping -> Model.fixedMap Print.pp

(* ------------------------------------------------------------------------- *)
(* TPTP roles.                                                               *)
(* ------------------------------------------------------------------------- *)

datatype role =
    AxiomRole
  | ConjectureRole
  | DefinitionRole
  | NegatedConjectureRole
  | PlainRole
  | TheoremRole
  | OtherRole of string;

val isCnfConjectureRole : role -> bool

val isFofConjectureRole : role -> bool

val toStringRole : role -> string

val fromStringRole : string -> role

val ppRole : role Print.pp

(* ------------------------------------------------------------------------- *)
(* SZS statuses.                                                             *)
(* ------------------------------------------------------------------------- *)

datatype status =
    CounterSatisfiableStatus
  | TheoremStatus
  | SatisfiableStatus
  | UnknownStatus
  | UnsatisfiableStatus

val toStringStatus : status -> string

val ppStatus : status Print.pp

(* ------------------------------------------------------------------------- *)
(* TPTP literals.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype literal =
    Boolean of bool
  | Literal of Literal.literal

val negateLiteral : literal -> literal

val functionsLiteral : literal -> NameAritySet.set

val relationLiteral : literal -> Atom.relation option

val freeVarsLiteral : literal -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* TPTP formula names.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype formulaName =
    FormulaName of string

val ppFormulaName : formulaName Print.pp

(* ------------------------------------------------------------------------- *)
(* TPTP formula bodies.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype formulaBody =
    CnfFormulaBody of literal list
  | FofFormulaBody of Formula.formula

(* ------------------------------------------------------------------------- *)
(* TPTP formula sources.                                                     *)
(* ------------------------------------------------------------------------- *)

datatype formulaSource =
    NoFormulaSource
  | StripFormulaSource of
      {inference : string,
       parents : formulaName list}
  | NormalizeFormulaSource of
      {inference : Normalize.inference,
       parents : formulaName list}
  | ProofFormulaSource of
      {inference : Proof.inference,
       parents : formulaName list}

(* ------------------------------------------------------------------------- *)
(* TPTP formulas.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    Formula of
      {name : formulaName,
       role : role,
       body : formulaBody,
       source : formulaSource}

val nameFormula : formula -> formulaName

val roleFormula : formula -> role

val bodyFormula : formula -> formulaBody

val sourceFormula : formula -> formulaSource

val functionsFormula : formula -> NameAritySet.set

val relationsFormula : formula -> NameAritySet.set

val freeVarsFormula : formula -> NameSet.set

val freeVarsListFormula : formula list -> NameSet.set

val isCnfConjectureFormula : formula -> bool
val isFofConjectureFormula : formula -> bool
val isConjectureFormula : formula -> bool

(* ------------------------------------------------------------------------- *)
(* Clause information.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype clauseSource =
    CnfClauseSource of formulaName * literal list
  | FofClauseSource of Normalize.thm

type 'a clauseInfo = 'a LiteralSetMap.map

type clauseNames = formulaName clauseInfo

type clauseRoles = role clauseInfo

type clauseSources = clauseSource clauseInfo

val noClauseNames : clauseNames

val noClauseRoles : clauseRoles

val noClauseSources : clauseSources

(* ------------------------------------------------------------------------- *)
(* TPTP problems.                                                            *)
(* ------------------------------------------------------------------------- *)

type comments = string list

type includes = string list

datatype problem =
    Problem of
      {comments : comments,
       includes : includes,
       formulas : formula list}

val hasCnfConjecture : problem -> bool
val hasFofConjecture : problem -> bool
val hasConjecture : problem -> bool

val freeVars : problem -> NameSet.set

val mkProblem :
    {comments : comments,
     includes : includes,
     names : clauseNames,
     roles : clauseRoles,
     problem : Problem.problem} -> problem

val normalize :
    problem ->
    {subgoal : Formula.formula * formulaName list,
     problem : Problem.problem,
     sources : clauseSources} list

val goal : problem -> Formula.formula

val read : {mapping : mapping, filename : string} -> problem

val write :
    {problem : problem,
     mapping : mapping,
     filename : string} -> unit

val prove : {filename : string, mapping : mapping} -> bool

(* ------------------------------------------------------------------------- *)
(* TSTP proofs.                                                              *)
(* ------------------------------------------------------------------------- *)

val fromProof :
    {problem : problem,
     proofs : {subgoal : Formula.formula * formulaName list,
               sources : clauseSources,
               refutation : Thm.thm} list} -> formula list

end
