(*  Title:      HOL/Quot/FRACT.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)

Goalw [per_def,per_NP_def]
"(op ===)=(%x y. fst(rep_NP x)*snd(rep_NP y)=fst(rep_NP y)*snd(rep_NP x))";
by (rtac refl 1);
qed "inst_NP_per";


Goalw [half_def] "half = <[abs_NP(n,2*n)]>";
by (rtac per_class_eqI 1);
by (simp_tac (simpset() addsimps [inst_NP_per]) 1);
qed "test";
