(* ========================================================================= *)
(* CNF PROBLEMS                                                              *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)
(* ========================================================================= *)

structure Problem :> Problem =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Problems.                                                                 *)
(* ------------------------------------------------------------------------- *)

type problem =
     {axioms : Thm.clause list,
      conjecture : Thm.clause list};

fun toClauses {axioms,conjecture} = axioms @ conjecture;

fun size prob =
    let
      fun lits (cl,n) = n + LiteralSet.size cl

      fun syms (cl,n) = n + LiteralSet.symbols cl

      fun typedSyms (cl,n) = n + LiteralSet.typedSymbols cl

      val cls = toClauses prob
    in
      {clauses = length cls,
       literals = List.foldl lits 0 cls,
       symbols = List.foldl syms 0 cls,
       typedSymbols = List.foldl typedSyms 0 cls}
    end;

fun freeVars {axioms,conjecture} =
    NameSet.union
      (LiteralSet.freeVarsList axioms)
      (LiteralSet.freeVarsList conjecture);

local
  fun clauseToFormula cl =
      Formula.listMkDisj (LiteralSet.transform Literal.toFormula cl);
in
  fun toFormula prob =
      Formula.listMkConj (map clauseToFormula (toClauses prob));

  fun toGoal {axioms,conjecture} =
      let
        val clToFm = Formula.generalize o clauseToFormula
        val clsToFm = Formula.listMkConj o map clToFm

        val fm = Formula.False
        val fm =
            if null conjecture then fm
            else Formula.Imp (clsToFm conjecture, fm)
        val fm = Formula.Imp (clsToFm axioms, fm)
      in
        fm
      end;
end;

fun toString prob = Formula.toString (toFormula prob);

(* ------------------------------------------------------------------------- *)
(* Categorizing problems.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype propositional =
    Propositional
  | EffectivelyPropositional
  | NonPropositional;

datatype equality =
    NonEquality
  | Equality
  | PureEquality;

datatype horn =
    Trivial
  | Unit
  | DoubleHorn
  | Horn
  | NegativeHorn
  | NonHorn;

type category =
     {propositional : propositional,
      equality : equality,
      horn : horn};

fun categorize prob =
    let
      val cls = toClauses prob

      val rels =
          let
            fun f (cl,set) = NameAritySet.union set (LiteralSet.relations cl)
          in
            List.foldl f NameAritySet.empty cls
          end

      val funs =
          let
            fun f (cl,set) = NameAritySet.union set (LiteralSet.functions cl)
          in
            List.foldl f NameAritySet.empty cls
          end

      val propositional =
          if NameAritySet.allNullary rels then Propositional
          else if NameAritySet.allNullary funs then EffectivelyPropositional
          else NonPropositional

      val equality =
          if not (NameAritySet.member Atom.eqRelation rels) then NonEquality
          else if NameAritySet.size rels = 1 then PureEquality
          else Equality

      val horn =
          if List.exists LiteralSet.null cls then Trivial
          else if List.all (fn cl => LiteralSet.size cl = 1) cls then Unit
          else 
            let
              fun pos cl = LiteralSet.count Literal.positive cl <= 1
              fun neg cl = LiteralSet.count Literal.negative cl <= 1
            in
              case (List.all pos cls, List.all neg cls) of
                (true,true) => DoubleHorn
              | (true,false) => Horn
              | (false,true) => NegativeHorn
              | (false,false) => NonHorn
            end
    in
      {propositional = propositional,
       equality = equality,
       horn = horn}
    end;

fun categoryToString {propositional,equality,horn} =
    (case propositional of
       Propositional => "propositional"
     | EffectivelyPropositional => "effectively propositional"
     | NonPropositional => "non-propositional") ^
    ", " ^
    (case equality of
       NonEquality => "non-equality"
     | Equality => "equality"
     | PureEquality => "pure equality") ^
    ", " ^
    (case horn of
       Trivial => "trivial"
     | Unit => "unit"
     | DoubleHorn => "horn (and negative horn)"
     | Horn => "horn"
     | NegativeHorn => "negative horn"
     | NonHorn => "non-horn");

end
