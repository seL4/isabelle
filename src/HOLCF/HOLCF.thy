(*  Title:      HOLCF/HOLCF.thy
    ID:         $Id$
    Author:     Franz Regensburger

HOLCF -- a semantic extension of HOL by the LCF logic.
*)

theory HOLCF
imports Sprod Ssum Up Lift Discrete One Tr Domain
uses
  "holcf_logic.ML"
  "cont_consts.ML"
  "domain/library.ML"
  "domain/syntax.ML"
  "domain/axioms.ML"
  "domain/theorems.ML"
  "domain/extender.ML"
  "adm_tac.ML"

begin

ML_setup {*
  change_simpset (fn simpset => simpset addSolver
    (mk_solver' "adm_tac" (fn ss =>
      adm_tac (cut_facts_tac (Simplifier.prems_of_ss ss) THEN' cont_tacRs ss))));
*}

end
