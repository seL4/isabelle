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
    by (ALLGOALS Asm_simp_tac);
  by (Fast_tac 1);
 by (Fast_tac 1);
by (rtac allI 1);
by (rtac allI 1);
by (rtac impI 1);
by (etac induct2 1);
 by (rtac Gamma_mono 1);
by (rewtac Gamma_def);  
by (Fast_tac 1);
qed "hoare_sound";

goalw Hoare.thy [wp_def] "wp SKIP Q = Q";
by (Simp_tac 1);
qed "wp_SKIP";

goalw Hoare.thy [wp_def] "wp (x:=a) Q = (%s.Q(s[a s/x]))";
by (Simp_tac 1);
qed "wp_Ass";

goalw Hoare.thy [wp_def] "wp (c;d) Q = wp c (wp d Q)";
by (Simp_tac 1);
by (rtac ext 1);
by (Fast_tac 1);
qed "wp_Semi";

goalw Hoare.thy [wp_def]
  "wp (IF b THEN c ELSE d) Q = (%s. (b s --> wp c Q s) & \
\                                    (~b s --> wp d Q s))";
by (Simp_tac 1);
by (rtac ext 1);
by (Fast_tac 1);
qed "wp_If";

goalw Hoare.thy [wp_def]
  "!!s. b s ==> wp (WHILE b DO c) Q s = wp (c;WHILE b DO c) Q s";
by (stac C_While_If 1);
by (Asm_simp_tac 1);
qed "wp_While_True";

goalw Hoare.thy [wp_def] "!!s. ~b s ==> wp (WHILE b DO c) Q s = Q s";
by (stac C_While_If 1);
by (Asm_simp_tac 1);
qed "wp_While_False";

Addsimps [wp_SKIP,wp_Ass,wp_Semi,wp_If,wp_While_True,wp_While_False];

(*Not suitable for rewriting: LOOPS!*)
goal Hoare.thy "wp (WHILE b DO c) Q s = \
\                 (if b s then wp (c;WHILE b DO c) Q s else Q s)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
qed "wp_While_if";

goal thy
  "wp (WHILE b DO c) Q s = \
\  (s : gfp(%S.{s.if b s then wp c (%s.s:S) s else Q s}))";
by(simp_tac (!simpset setloop(split_tac[expand_if])) 1);
br iffI 1;
 br weak_coinduct 1;
  by(etac CollectI 1);
 by(safe_tac (!claset));
  by(rotate_tac ~1 1);
  by(Asm_full_simp_tac 1);
 by(rotate_tac ~1 1);
 by(Asm_full_simp_tac 1);
by(asm_full_simp_tac (!simpset addsimps [wp_def,Gamma_def]) 1);
by(strip_tac 1);
br mp 1;
 ba 2;
be induct2 1;
by(fast_tac (!claset addSIs [monoI]) 1);
by(stac gfp_Tarski 1);
 by(fast_tac (!claset addSIs [monoI]) 1);
by(Fast_tac 1);
qed "wp_While";

Delsimps [C_while];

AddSIs [hoare.skip, hoare.ass, hoare.semi, hoare.If];

goal Hoare.thy "!Q. |- {wp c Q} c {Q}";
by (com.induct_tac "c" 1);
by (ALLGOALS Simp_tac);
by (REPEAT_FIRST Fast_tac);
by (deepen_tac (!claset addIs [hoare.conseq]) 0 1);
by (Step_tac 1);
by (rtac hoare.conseq 1);
  by (etac thin_rl 1);
  by (Fast_tac 1);
 by (rtac hoare.While 1);
 by (rtac hoare.conseq 1);
   by (etac thin_rl 3);
   by (rtac allI 3);
   by (rtac impI 3);
   by (assume_tac 3);
  by (Fast_tac 2);
 by (safe_tac HOL_cs);
 by (rotate_tac ~1 1);
 by (Asm_full_simp_tac 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "wp_is_pre";

goal Hoare.thy "!!c. |= {P}c{Q} ==> |- {P}c{Q}";
by (rtac (wp_is_pre RSN (2,hoare.conseq)) 1);
 by (Fast_tac 2);
by (rewrite_goals_tac [hoare_valid_def,wp_def]);
by (Fast_tac 1);
qed "hoare_relative_complete";
