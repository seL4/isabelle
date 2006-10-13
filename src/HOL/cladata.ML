(*  Title:      HOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner.
*)

structure Hypsubst_Data =
struct
  structure Simplifier = Simplifier
  val dest_eq = HOLogic.dest_eq_typ
  val dest_Trueprop = HOLogic.dest_Trueprop
  val dest_imp = HOLogic.dest_imp
  val eq_reflection = HOL.eq_reflection
  val rev_eq_reflection = HOL.def_imp_eq
  val imp_intr = HOL.impI
  val rev_mp = HOL.rev_mp
  val subst = HOL.subst
  val sym = HOL.sym
  val thin_refl = thm "thin_refl";
end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);

structure Classical_Data = 
struct
  val mp = HOL.mp
  val not_elim = HOL.notE
  val classical = HOL.classical
  val sizef = Drule.size_of_thm
  val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]
end;

structure Classical = ClassicalFun(Classical_Data);
structure BasicClassical: BASIC_CLASSICAL = Classical; 
