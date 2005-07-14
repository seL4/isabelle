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
  "domain/interface.ML"
  "adm_tac.ML"

begin

ML_setup {*
  simpset_ref() := simpset() addSolver
     (mk_solver "adm_tac" (fn thms => (adm_tac (cut_facts_tac thms THEN' cont_tacRs))));
*}

end
