(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Problem =
sig

(* ------------------------------------------------------------------------- *)
(* Problems.                                                                 *)
(* ------------------------------------------------------------------------- *)

type problem = Thm.clause list

val size : problem -> {clauses : int,
                       literals : int,
                       symbols : int,
                       typedSymbols : int}

val fromGoal : Formula.formula -> problem list

val toClauses : problem -> Formula.formula

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
