(*  Title:      HOLCF/HOLCF.thy
    Author:     Franz Regensburger

HOLCF -- a semantic extension of HOL by the LCF logic.
*)

theory HOLCF
imports
  Domain ConvexPD Algebraic Universal Sum_Cpo Main
uses
  "holcf_logic.ML"
  "Tools/cont_consts.ML"
  "Tools/cont_proc.ML"
  "Tools/domain/domain_library.ML"
  "Tools/domain/domain_syntax.ML"
  "Tools/domain/domain_axioms.ML"
  "Tools/domain/domain_theorems.ML"
  "Tools/domain/domain_extender.ML"
  "Tools/adm_tac.ML"
begin

defaultsort pcpo

declaration {* fn _ =>
  Simplifier.map_ss (fn simpset => simpset addSolver
    (mk_solver' "adm_tac" (fn ss =>
      Adm.adm_tac (Simplifier.the_context ss)
        (cut_facts_tac (Simplifier.prems_of_ss ss) THEN' cont_tacRs ss))));
*}

end
