(*  Title:      HOLCF/fun3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open Fun3;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_fun_pcpo" thy "UU = (%x. UU)"
 (fn prems => 
        [
        (simp_tac (HOL_ss addsimps [UU_def,UU_fun_def]) 1)
        ]);
