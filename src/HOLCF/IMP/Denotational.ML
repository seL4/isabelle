(*  Title:      HOLCF/IMP/Denotational.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner
    Copyright   1996 TUM

Equivalence of Denotational Semantics in HOLCF and Evaluation Semantics in HOL
*)

Addsimps [flift1_def];

val prems = goal Lift.thy "[| f`UU = UU; f`x = Def b |] ==> EX a. x = Def a";
by (cut_facts_tac prems 1);
by (res_inst_tac [("x","x")] Lift_cases 1);
 by (fast_tac (HOL_cs addSEs [DefE2]) 1);
by (fast_tac HOL_cs 1);
qed "strict_Def";


goal thy "D(WHILE b DO c) = D(IF b THEN c;WHILE b DO c ELSE SKIP)";
by(Simp_tac 1);
by(EVERY[stac fix_eq 1, Simp_tac 1, IF_UNSOLVED	no_tac]);
qed "D_While_If";


goal thy "D c`UU =UU";
by (com.induct_tac "c" 1);
    by (ALLGOALS Asm_simp_tac);
by (stac fix_eq 1);
by (Asm_simp_tac 1);
qed "D_strict";


goal thy "!!c. <c,s> -c-> t ==> D c`(Def s) = (Def t)";
be evalc.induct 1;
      by (ALLGOALS Asm_simp_tac);
 by (ALLGOALS (rtac (fix_eq RS ssubst) THEN' Asm_full_simp_tac));
qed_spec_mp "eval_implies_D";

goal thy "!s t. D c`(Def s) = (Def t) --> <c,s> -c-> t";
by (com.induct_tac "c" 1);
    by (fast_tac ((HOL_cs addSIs evalc.intrs) addss !simpset) 1);
   by (fast_tac ((HOL_cs addSIs evalc.intrs) addss !simpset) 1);
  by (Simp_tac 1);
  by (strip_tac 1);
  by (forward_tac [D_strict RS strict_Def] 1);
  be exE 1;
  by (rotate_tac ~1 1);
  by (Asm_full_simp_tac 1);
  by (fast_tac (HOL_cs addSIs evalc.intrs) 1);
 by (REPEAT (rtac allI 1));
 by (case_tac "bexp s" 1);
  by (fast_tac ((HOL_cs addSIs evalc.intrs) unsafe_addss !simpset) 1);
 by (fast_tac ((HOL_cs addIs evalc.intrs) unsafe_addss !simpset) 1);
by(res_inst_tac [("Q","D (WHILE bexp DO com)`UU = UU")] conjunct1 1);
by (Simp_tac 1);
br fix_ind 1;
  by(fast_tac (HOL_cs addSIs (adm_lemmas@[adm_flatdom,flat_lift])) 1);
 by (Simp_tac 1);
br conjI 1;
 by (REPEAT (rtac allI 1));
 by (case_tac "bexp s" 1);
  (* case bexp s *)
  by (Asm_simp_tac 1);
  by (strip_tac 1);
  be conjE 1;
  bd strict_Def 1;
   ba 1;
  be exE 1;
  by (rotate_tac ~1 1);
  by (Asm_full_simp_tac 1);
  by (fast_tac (HOL_cs addIs evalc.intrs) 1);
 (* case ~bexp s *)
 by (fast_tac ((HOL_cs addSIs evalc.intrs) unsafe_addss !simpset) 1);
(* induction step for strictness *)
by (Asm_full_simp_tac 1);
qed_spec_mp "D_implies_eval";


goal thy "(D c`(Def s) = (Def t)) = (<c,s> -c-> t)";
by (fast_tac (HOL_cs addSEs [D_implies_eval,eval_implies_D]) 1);
qed "D_is_eval";
