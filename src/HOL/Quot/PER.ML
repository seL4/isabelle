(*  Title:      HOL/Quot/PER.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open PER;

goalw thy [fun_per_def,per_def] "f===g=(!x y.x:D&y:D&x===y-->f x===g y)";
br refl 1;
qed "inst_fun_per";

(* Witness that quot is not empty *)
goal thy "?z:{s.? r.!y.y:s=y===r}";
fr CollectI;
by (res_inst_tac [("x","x")] exI 1);
br allI 1;
br mem_Collect_eq 1;
qed "quotNE";
