(*  Title:      HOL/BCV/DFAandWTI.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Goalw [wti_is_stable_topless_def]
 "[| wti_is_stable_topless r T step wti succs n A; \
\    ss : list n A; !p<n. ss!p ~= T; p < n |] ==> \
\ wti ss p = stable r step succs ss p";
by (Asm_simp_tac 1);
qed "wti_is_stable_toplessD";

Goalw [is_dfa_def]
 "[| is_dfa r dfa step succs n A; ss : list n A |] ==> \
\ dfa ss:list n A & stables r step succs (dfa ss) & ss <=[r] dfa ss & \
\ (!ts: list n A. stables r step succs ts & ss <=[r] ts \
\       --> dfa ss <=[r] ts)";
by (Asm_full_simp_tac 1);
qed "is_dfaD";

Goalw [is_bcv_def,welltyping_def,stables_def]
 "[| order r; top r T; \
\    wti_is_stable_topless r T step wti succs n A; \
\    is_dfa r dfa step succs n A |] ==> is_bcv r T wti n A dfa";
by(Clarify_tac 1);
by (dtac is_dfaD 1);
by (assume_tac 1);
by(Clarify_tac 1);
br iffI 1;
 br bexI 1;
  br conjI 1;
   ba 1;
  by (asm_full_simp_tac
        (simpset() addsimps[wti_is_stable_toplessD,stables_def]) 1);
 ba 1;
by(Clarify_tac 1);
by(asm_full_simp_tac
    (simpset() addsimps [imp_conjR,all_conj_distrib,wti_is_stable_toplessD,
                         stables_def] addcongs [conj_cong]) 1);
by(dres_inst_tac [("x","ts")] bspec 1);
 ba 1;
by (force_tac (claset()addDs [le_listD],simpset()) 1);
qed "is_bcv_dfa";

(*
Goal
 "x:M ==> replicate n x : list n M";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [in_list_Suc_iff,Bex_def]) 1);
qed "replicate_in_list";
Addsimps [replicate_in_list];

Goal "!ys. replicate n x <= ys = (length ys = n & (!y:set ys. x <= y))";
by (induct_tac "n" 1);
 by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_le_iff,length_Suc_conv]) 1);
by (Force_tac 1);
qed_spec_mp "replicate_le_conv";
AddIffs [replicate_le_conv];

Goal
 "[| wti_is_stable_topless step wti succs n A; is_dfa dfa step succs n A; \
\    0 < n; init : (option A) |] ==> \
\ dfa (init # replicate (n-1) None) = \
\ (? tos : list n (option A). init <= tos!0 & welltyping wti tos)";
by (subgoal_tac "? m. n = m+1" 1);
 by (res_inst_tac [("x","n-1")] exI 2);
 by (arith_tac 2);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (dtac dfa_iff_welltyping 1);
  by (assume_tac 1);
 by (etac trans 2);
 by (asm_simp_tac (simpset() addsimps [in_list_Suc_iff,Bex_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_le_iff]) 1);
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (rtac bexI 1);
  by (rtac conjI 1);
   by (assume_tac 2);
  by (assume_tac 2);
 by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff,Bex_def]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps []) 1);
by (rtac exI 1);
by (rtac conjI 1);
 by (rtac conjI 2);
  by (assume_tac 3);
 by (Blast_tac 1);
by (Force_tac 1);
qed "dfa_iff_welltyping0";
*)
