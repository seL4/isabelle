(*  Title:      HOLCF/IMP/Denotational.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner
    Copyright   1996 TUM

Equivalence of Denotational Semantics in HOLCF and Evaluation Semantics in HOL
*)

Goalw [dlift_def] "dlift f$(Def x) = f$(Discr x)";
by (Simp_tac 1);
qed "dlift_Def";
Addsimps [dlift_Def];

Goalw [dlift_def] "cont(%f. dlift f)";
by (Simp_tac 1);
qed "cont_dlift";
AddIffs [cont_dlift];

Goalw [dlift_def]
 "(dlift f$l = Def y) = (? x. l = Def x & f$(Discr x) = Def y)";
by (simp_tac (simpset() addsplits [lift.split]) 1);
qed "dlift_is_Def";
Addsimps [dlift_is_Def];

Goal "<c,s> -c-> t ==> D c$(Discr s) = (Def t)";
by (etac evalc.induct 1);
      by (ALLGOALS Asm_simp_tac);
 by (ALLGOALS (stac fix_eq THEN' Asm_full_simp_tac));
qed_spec_mp "eval_implies_D";

Goal "!s t. D c$(Discr s) = (Def t) --> <c,s> -c-> t";
by (induct_tac "c" 1);
    by (Force_tac 1);
   by (Force_tac 1);
  by (Force_tac 1);
 by (Simp_tac 1);
 by (Force_tac 1);
by (Simp_tac 1);
by (rtac fix_ind 1);
  by (fast_tac (claset() addSIs adm_lemmas @ [adm_chfindom, ax_flat]) 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by Safe_tac;
  by (Fast_tac 1);
 by (Force_tac 1);
qed_spec_mp "D_implies_eval";


Goal "(D c$(Discr s) = (Def t)) = (<c,s> -c-> t)";
by (fast_tac (claset() addSEs [D_implies_eval,eval_implies_D]) 1);
qed "D_is_eval";
