(*  Title:      HOLCF/Fun3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

(* for compatibility with old HOLCF-Version *)
val prems = goal thy "UU = (%x. UU)";
by (simp_tac (HOL_ss addsimps [UU_def,UU_fun_def]) 1);
qed "inst_fun_pcpo";
