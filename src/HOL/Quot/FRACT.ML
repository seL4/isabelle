(*  Title:      HOL/Quot/FRACT.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open FRACT;

goalw thy [per_def,per_NP_def]
"(op ===)=(%x y.fst(rep_NP x)*snd(rep_NP y)=fst(rep_NP y)*snd(rep_NP x))";
fr refl;
qed "inst_NP_per";


goalw thy [half_def] "half = <[abs_NP(n,2*n)]>";
fr per_class_eqI;
by (simp_tac (!simpset addsimps [inst_NP_per]) 1);
qed "test";
