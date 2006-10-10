(*  Title:      HOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner.
*)

structure Hypsubst_Data =
struct
  structure Simplifier = Simplifier
  fun dest_eq (Const ("op =", T) $ t $ u) = (t, u, domain_type T)
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

structure HOL =
struct

open HOL;
open Hypsubst;
open BasicClassical;

(*prevent substitution on bool*)
fun hyp_subst_tac' i thm = if i <= Thm.nprems_of thm andalso
  Term.exists_Const (fn ("op =", Type (_, [T, _])) => T <> Type ("bool", []) | _ => false)
    (nth (Thm.prems_of thm) (i - 1)) then hyp_subst_tac i thm else no_tac thm;

(*Propositional rules*)
val prop_cs = empty_cs addSIs [HOL.refl, HOL.TrueI, HOL.conjI, HOL.disjCI, HOL.impI, HOL.notI, HOL.iffI]
                       addSEs [HOL.conjE, HOL.disjE, HOL.impCE, HOL.FalseE, HOL.iffCE];

(*Quantifier rules*)
val cs = prop_cs addSIs [HOL.allI, HOL.ex_ex1I] addIs [HOL.exI, HOL.the_equality] 
                     addSEs [HOL.exE] addEs [HOL.allE];

end;
