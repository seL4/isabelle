(*  Title:      HOL/IMP/VC.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TUM

Soundness and completeness of vc
*)

open VC;

AddIs hoare.intrs;

val lemma = prove_goal HOL.thy "!s. P s --> P s" (K[Fast_tac 1]);

goal VC.thy "!Q. (!s. vc c Q s) --> |- {awp c Q} astrip c {Q}";
by (acom.induct_tac "c" 1);
    by (ALLGOALS Simp_tac);
    by (Fast_tac 1);
   by (Fast_tac 1);
  by (Fast_tac 1);
 (* if *)
 by (Deepen_tac 4 1);
(* while *)
by (safe_tac HOL_cs);
by (resolve_tac hoare.intrs 1);
  by (rtac lemma 1);
 by (resolve_tac hoare.intrs 1);
 by (resolve_tac hoare.intrs 1);
   by (ALLGOALS(fast_tac HOL_cs));
qed "vc_sound";

goal VC.thy "!P Q. (!s. P s --> Q s) --> (!s. awp c P s --> awp c Q s)";
by (acom.induct_tac "c" 1);
    by (ALLGOALS Asm_simp_tac);
by (EVERY1[rtac allI, rtac allI, rtac impI]);
by (EVERY1[etac allE, etac allE, etac mp]);
by (EVERY1[etac allE, etac allE, etac mp, atac]);
qed_spec_mp "awp_mono";

goal VC.thy "!P Q. (!s. P s --> Q s) --> (!s. vc c P s --> vc c Q s)";
by (acom.induct_tac "c" 1);
    by (ALLGOALS Asm_simp_tac);
by (safe_tac HOL_cs);
by (EVERY[etac allE 1,etac allE 1,etac impE 1,etac allE 2,etac mp 2,atac 2]);
by (fast_tac (HOL_cs addEs [awp_mono]) 1);
qed_spec_mp "vc_mono";

goal VC.thy
  "!!P c Q. |- {P}c{Q} ==> \
\          (? ac. astrip ac = c & (!s. vc ac Q s) & (!s. P s --> awp ac Q s))";
by (etac hoare.induct 1);
     by (res_inst_tac [("x","Askip")] exI 1);
     by (Simp_tac 1);
    by (res_inst_tac [("x","Aass x a")] exI 1);
    by (Simp_tac 1);
   by (SELECT_GOAL(safe_tac HOL_cs)1);
   by (res_inst_tac [("x","Asemi ac aca")] exI 1);
   by (Asm_simp_tac 1);
   by (fast_tac (HOL_cs addSEs [awp_mono,vc_mono]) 1);
  by (SELECT_GOAL(safe_tac HOL_cs)1);
  by (res_inst_tac [("x","Aif b ac aca")] exI 1);
  by (Asm_simp_tac 1);
 by (SELECT_GOAL(safe_tac HOL_cs)1);
 by (res_inst_tac [("x","Awhile b Pa ac")] exI 1);
 by (Asm_simp_tac 1);
by (safe_tac HOL_cs);
by (res_inst_tac [("x","ac")] exI 1);
by (Asm_simp_tac 1);
by (fast_tac (HOL_cs addSEs [awp_mono,vc_mono]) 1);
qed "vc_complete";

goal VC.thy "!Q. vcawp c Q = (vc c Q, awp c Q)";
by (acom.induct_tac "c" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Let_def])));
qed "vcawp_vc_awp";
