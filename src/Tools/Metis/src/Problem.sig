(* ========================================================================= *)
(* CNF PROBLEMS                                                              *)
(* Copyright (c) 2001-2008 Joe Hurd, distributed under the BSD License       *)
(* ========================================================================= *)

signature Problem =
sig

(* ------------------------------------------------------------------------- *)
(* Problems.                                                                 *)
(* ------------------------------------------------------------------------- *)

type problem =
     {axioms : Thm.clause list,
      conjecture : Thm.clause list}

val size : problem -> {clauses : int,
                       literals : int,
                       symbols : int,
                       typedSymbols : int}

val freeVars : problem -> NameSet.set

val toClauses : problem -> Thm.clause list

val toFormula : problem -> Formula.formula

val toGoal : problem -> Formula.formula

val toString : problem -> string

(* ------------------------------------------------------------------------- *)
(* Categorizing problems.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype propositional =
    Propositional
  | EffectivelyPropositional
  | NonPropositional

datatype equality =
    NonEquality
  | Equality
  | PureEquality

datatype horn =
    Trivial
  | Unit
  | DoubleHorn
  | Horn
  | NegativeHorn
  | NonHorn

type category =
     {propositional : propositional,
      equality : equality,
      horn : horn}

val categorize : problem -> category

val categoryToString : category -> string

end
