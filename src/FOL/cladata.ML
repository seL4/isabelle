(*  Title:      FOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner.
*)

section "Classical Reasoner";

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val mp        = mp
  val not_elim  = notE
  val classical = thm "classical"
  val sizef     = size_of_thm
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Cla = ClassicalFun(Classical_Data);
structure BasicClassical: BASIC_CLASSICAL = Cla; open BasicClassical;



(*Propositional rules*)
val prop_cs = empty_cs
  addSIs [refl, TrueI, conjI, thm "disjCI", impI, notI, iffI]
  addSEs [conjE, disjE, thm "impCE", FalseE, thm "iffCE"];

(*Quantifier rules*)
val FOL_cs = prop_cs addSIs [allI, thm "ex_ex1I"] addIs [exI]
                     addSEs [exE, thm "alt_ex1E"] addEs [allE];

val cla_setup = (fn thy => (change_claset_of thy (fn _ => FOL_cs); thy));

val case_setup =
 (Method.add_methods
    [("case_tac", Method.goal_args Args.name case_tac,
      "case_tac emulation (dynamic instantiation!)")]);
