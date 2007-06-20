(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* Copyright (c) 2003-2007 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Model =
sig

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* Note: a model of size N has integer elements 0...N-1.                     *)
(* ------------------------------------------------------------------------- *)

type fixed =
     {size : int} ->
     {functions : (Term.functionName * int list) -> int option,
      relations : (Atom.relationName * int list) -> bool option}

val fixedMerge : fixed -> fixed -> fixed  (* Prefers the second fixed *)

val fixedMergeList : fixed list -> fixed

val fixedPure : fixed  (* : = *)

val fixedBasic : fixed  (* id fst snd #1 #2 #3 <> *)

val fixedModulo : fixed  (* <numerals> suc pre ~ + - * exp div mod *)
                         (* is_0 divides even odd *)

val fixedOverflowNum : fixed  (* <numerals> suc pre + - * exp div mod *)
                              (* is_0 <= < >= > divides even odd *)

val fixedOverflowInt : fixed  (* <numerals> suc pre + - * exp div mod *)
                              (* is_0 <= < >= > divides even odd *)

val fixedSet : fixed  (* empty univ union intersect compl card in subset *)

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fixed : fixed}

type model

val new : parameters -> model

val size : model -> int

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = int NameMap.map

val valuationEmpty : valuation

val valuationRandom : {size : int} -> NameSet.set -> valuation

val valuationFold :
    {size : int} -> NameSet.set -> (valuation * 'a -> 'a) -> 'a -> 'a

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

val interpretTerm : model -> valuation -> Term.term -> int

val interpretAtom : model -> valuation -> Atom.atom -> bool

val interpretFormula : model -> valuation -> Formula.formula -> bool

val interpretLiteral : model -> valuation -> Literal.literal -> bool

val interpretClause : model -> valuation -> Thm.clause -> bool

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

val checkAtom :
    {maxChecks : int} -> model -> Atom.atom -> {T : int, F : int}

val checkFormula :
    {maxChecks : int} -> model -> Formula.formula -> {T : int, F : int}

val checkLiteral :
    {maxChecks : int} -> model -> Literal.literal -> {T : int, F : int}

val checkClause :
    {maxChecks : int} -> model -> Thm.clause -> {T : int, F : int}

end
