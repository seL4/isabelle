(*  Title:      HOL/IMP/Hoare.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM

Soundness (and part of) relative completeness of Hoare rules
wrt denotational semantics
*)

open Hoare;

goalw Hoare.thy [hoare_valid_def] "!!P c Q. |- {P}c{Q} ==> |= {P}c{Q}";
by (etac hoare.induct 1);
    by(ALLGOALS Asm_simp_tac);
  by (Fast_tac 1);
 by (Fast_tac 1);
by (rtac allI 1);
by (rtac allI 1);
by (rtac impI 1);
by (etac induct2 1);
 br Gamma_mono 1;
by (rewtac Gamma_def);  
by (Fast_tac 1);
qed "hoare_sound";

goalw Hoare.thy [swp_def] "swp SKIP Q = Q";
by(Simp_tac 1);
br ext 1;
by (Fast_tac 1);
qed "swp_SKIP";

goalw Hoare.thy [swp_def] "swp (x:=a) Q = (%s.Q(s[a s/x]))";
by(Simp_tac 1);
qed "swp_Ass";

goalw Hoare.thy [swp_def] "swp (c;d) Q = swp c (swp d Q)";
by(Simp_tac 1);
br ext 1;
by (Fast_tac 1);
qed "swp_Semi";

goalw Hoare.thy [swp_def]
  "swp (IF b THEN c ELSE d) Q = (%s. (b s --> swp c Q s) & \
\                                    (~b s --> swp d Q s))";
by(Simp_tac 1);
br ext 1;
by (Fast_tac 1);
qed "swp_If";

goalw Hoare.thy [swp_def]
  "!!s. b s ==> swp (WHILE b DO c) Q s = swp (c;WHILE b DO c) Q s";
by(stac C_While_If 1);
by(Asm_simp_tac 1);
qed "swp_While_True";

goalw Hoare.thy [swp_def] "!!s. ~b s ==> swp (WHILE b DO c) Q s = Q s";
by(stac C_While_If 1);
by(Asm_simp_tac 1);
by (Fast_tac 1);
qed "swp_While_False";

Addsimps [swp_SKIP,swp_Ass,swp_Semi,swp_If,swp_While_True,swp_While_False];

(*Not suitable for rewriting: LOOPS!*)
goal Hoare.thy "swp (WHILE b DO c) Q s = \
\                 (if b s then swp (c;WHILE b DO c) Q s else Q s)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
qed "swp_While_if";


Delsimps [C_while];

AddSIs [hoare.skip, hoare.ass, hoare.semi, hoare.If];

goal Hoare.thy "!Q. |- {swp c Q} c {Q}";
by(com.induct_tac "c" 1);
by(ALLGOALS Simp_tac);
by (REPEAT_FIRST Fast_tac);
by (deepen_tac (!claset addIs [hoare.conseq]) 0 1);
by (Step_tac 1);
br hoare.conseq 1;
  be thin_rl 1;
  by (Fast_tac 1);
 br hoare.While 1;
 br hoare.conseq 1;
   be thin_rl 3;
   br allI 3;
   br impI 3;
   ba 3;
  by (Fast_tac 2);
 by(safe_tac HOL_cs);
 by(rotate_tac ~1 1);
 by(Asm_full_simp_tac 1);
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
qed_spec_mp "swp_is_pre";

goal Hoare.thy "!!c. |= {P}c{Q} ==> |- {P}c{Q}";
br (swp_is_pre RSN (2,hoare.conseq)) 1;
 by (Fast_tac 2);
by(rewrite_goals_tac [hoare_valid_def,swp_def]);
by (Fast_tac 1);
qed "hoare_relative_complete";
