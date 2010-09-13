(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* Copyright (c) 2003 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

signature Model =
sig

(* ------------------------------------------------------------------------- *)
(* Model size.                                                               *)
(* ------------------------------------------------------------------------- *)

type size = {size : int}

(* ------------------------------------------------------------------------- *)
(* A model of size N has integer elements 0...N-1.                           *)
(* ------------------------------------------------------------------------- *)

type element = int

val zeroElement : element

val incrementElement : size -> element -> element option

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* ------------------------------------------------------------------------- *)

type fixedFunction = size -> element list -> element option

type fixedRelation = size -> element list -> bool option

datatype fixed =
    Fixed of
      {functions : fixedFunction NameArityMap.map,
       relations : fixedRelation NameArityMap.map}

val emptyFixed : fixed

val unionFixed : fixed -> fixed -> fixed

val getFunctionFixed : fixed -> NameArity.nameArity -> fixedFunction

val getRelationFixed : fixed -> NameArity.nameArity -> fixedRelation

val insertFunctionFixed : fixed -> NameArity.nameArity * fixedFunction -> fixed

val insertRelationFixed : fixed -> NameArity.nameArity * fixedRelation -> fixed

val unionListFixed : fixed list -> fixed

val basicFixed : fixed  (* interprets equality and hasType *)

(* ------------------------------------------------------------------------- *)
(* Renaming fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

type fixedMap =
     {functionMap : Name.name NameArityMap.map,
      relationMap : Name.name NameArityMap.map}

val mapFixed : fixedMap -> fixed -> fixed

val ppFixedMap : fixedMap Print.pp

(* ------------------------------------------------------------------------- *)
(* Standard fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

(* Projections *)

val projectionMin : int

val projectionMax : int

val projectionName : int -> Name.name

val projectionFixed : fixed

(* Arithmetic *)

val numeralMin : int

val numeralMax : int

val numeralName : int -> Name.name

val addName : Name.name

val divName : Name.name

val dividesName : Name.name

val evenName : Name.name

val expName : Name.name

val geName : Name.name

val gtName : Name.name

val isZeroName : Name.name

val leName : Name.name

val ltName : Name.name

val modName : Name.name

val multName : Name.name

val negName : Name.name

val oddName : Name.name

val preName : Name.name

val subName : Name.name

val sucName : Name.name

val modularFixed : fixed

val overflowFixed : fixed

(* Sets *)

val cardName : Name.name

val complementName : Name.name

val differenceName : Name.name

val emptyName : Name.name

val memberName : Name.name

val insertName : Name.name

val intersectName : Name.name

val singletonName : Name.name

val subsetName : Name.name

val symmetricDifferenceName : Name.name

val unionName : Name.name

val universeName : Name.name

val setFixed : fixed

(* Lists *)

val appendName : Name.name

val consName : Name.name

val lengthName : Name.name

val nilName : Name.name

val nullName : Name.name

val tailName : Name.name

val listFixed : fixed

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation

val emptyValuation : valuation

val zeroValuation : NameSet.set -> valuation

val constantValuation : element -> NameSet.set -> valuation

val peekValuation : valuation -> Name.name -> element option

val getValuation : valuation -> Name.name -> element

val insertValuation : valuation -> Name.name * element -> valuation

val randomValuation : {size : int} -> NameSet.set -> valuation

val incrementValuation :
    {size : int} -> NameSet.set -> valuation -> valuation option

val foldValuation :
    {size : int} -> NameSet.set -> (valuation * 'a -> 'a) -> 'a -> 'a

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fixed : fixed}

type model

val default : parameters

val new : parameters -> model

val size : model -> int

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

val interpretFunction : model -> Term.functionName * element list -> element

val interpretRelation : model -> Atom.relationName * element list -> bool

val interpretTerm : model -> valuation -> Term.term -> element

val interpretAtom : model -> valuation -> Atom.atom -> bool

val interpretFormula : model -> valuation -> Formula.formula -> bool

val interpretLiteral : model -> valuation -> Literal.literal -> bool

val interpretClause : model -> valuation -> Thm.clause -> bool

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

val check :
    (model -> valuation -> 'a -> bool) -> {maxChecks : int option} -> model ->
    NameSet.set -> 'a -> {T : int, F : int}

val checkAtom :
    {maxChecks : int option} -> model -> Atom.atom -> {T : int, F : int}

val checkFormula :
    {maxChecks : int option} -> model -> Formula.formula -> {T : int, F : int}

val checkLiteral :
    {maxChecks : int option} -> model -> Literal.literal -> {T : int, F : int}

val checkClause :
    {maxChecks : int option} -> model -> Thm.clause -> {T : int, F : int}

(* ------------------------------------------------------------------------- *)
(* Updating the model.                                                       *)
(* ------------------------------------------------------------------------- *)

val updateFunction :
    model -> (Term.functionName * element list) * element -> unit

val updateRelation :
    model -> (Atom.relationName * element list) * bool -> unit

(* ------------------------------------------------------------------------- *)
(* Choosing a random perturbation to make a formula true in the model.       *)
(* ------------------------------------------------------------------------- *)

val perturbTerm : model -> valuation -> Term.term * element list -> unit

val perturbAtom : model -> valuation -> Atom.atom * bool -> unit

val perturbLiteral : model -> valuation -> Literal.literal -> unit

val perturbClause : model -> valuation -> Thm.clause -> unit

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp : model Print.pp

end
