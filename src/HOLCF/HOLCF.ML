(*  Title:      HOLCF/HOLCF.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open HOLCF;

use"adm.ML";

simpset := !simpset addSolver(fn thms =>
            (adm_tac (cut_facts_tac thms THEN' cont_tacRs)));

val HOLCF_ss = !simpset;
