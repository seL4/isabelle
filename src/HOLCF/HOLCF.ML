(*  Title:      HOLCF/HOLCF.ML
    ID:         $Id$
    Author:     Franz Regensburger
*)

use"adm.ML";

simpset_ref() := simpset() addSolver
   (mk_solver "adm_tac" (fn thms => (adm_tac (cut_facts_tac thms THEN' cont_tacRs))));

val HOLCF_ss = simpset();
