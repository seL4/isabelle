(*  Title:      HOLCF/HOLCF.ML
    ID:         $Id$
    Author:     Franz Regensburger
*)

structure HOLCF =
struct
  val thy = the_context ();
end;

use "adm_tac.ML";

simpset_ref() := simpset() addSolver
   (mk_solver "adm_tac" (fn thms => (adm_tac (cut_facts_tac thms THEN' cont_tacRs))));

val HOLCF_ss = simpset();
