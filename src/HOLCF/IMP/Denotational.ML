(*  Title:      HOLCF/IMP/Denotational.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner
    Copyright   1996 TUM

Equivalence of Denotational Semantics in HOLCF and Evaluation Semantics in HOL
*)

goalw thy [dlift_def] "dlift f`(Def x) = f`(Discr x)";
by (Simp_tac 1);
qed "dlift_Def";
Addsimps [dlift_Def];

goalw thy [dlift_def] "cont(%f. dlift f)";
by (Simp_tac 1);
qed "cont_dlift";
AddIffs [cont_dlift];

goalw thy [dlift_def]
 "(dlift f`l = Def y) = (? x. l = Def x & f`(Discr x) = Def y)";
by (simp_tac (simpset() addsplits [split_lift_case]) 1);
qed "dlift_is_Def";
Addsimps [dlift_is_Def];

goal thy "!!c. <c,s> -c-> t ==> D c`(Discr s) = (Def t)";
by (etac evalc.induct 1);
      by (ALLGOALS Asm_simp_tac);
 by (ALLGOALS (stac fix_eq THEN' Asm_full_simp_tac));
qed_spec_mp "eval_implies_D";

goal thy "!s t. D c`(Discr s) = (Def t) --> <c,s> -c-> t";
by (com.induct_tac "c" 1);
    by (fast_tac ((HOL_cs addSIs evalc.intrs) addss simpset()) 1);
   by (fast_tac ((HOL_cs addSIs evalc.intrs) addss simpset()) 1);
  by (fast_tac ((HOL_cs addSIs evalc.intrs) addss simpset()) 1);
 by (Simp_tac 1);
 by (fast_tac ((HOL_cs addIs evalc.intrs) addss simpset()) 1);
by (Simp_tac 1);
by (rtac fix_ind 1);
  by (fast_tac (HOL_cs addSIs (adm_lemmas@[adm_chfindom,ax_flat_lift])) 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (safe_tac HOL_cs);
  by (fast_tac (HOL_cs addIs evalc.intrs) 1);
 by (fast_tac ((HOL_cs addSIs evalc.intrs) addss simpset()) 1);
qed_spec_mp "D_implies_eval";


goal thy "(D c`(Discr s) = (Def t)) = (<c,s> -c-> t)";
by (fast_tac (HOL_cs addSEs [D_implies_eval,eval_implies_D]) 1);
qed "D_is_eval";
