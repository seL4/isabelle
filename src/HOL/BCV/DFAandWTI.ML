(*  Title:      HOL/BCV/DFAandWTI.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

Goalw [wti_is_fix_step_def]
 "[| wti_is_fix_step step wti succs n L; \
\    sos : listsn n (option L); p < n |] ==> \
\ wti p sos = stable step succs p sos";
by (Asm_simp_tac 1);
qed "wti_is_fix_stepD";

Goalw [is_dfa_def]
 "[| is_dfa dfa step succs n L; sos : listsn n (option L) |] ==> \
\ dfa sos = (? tos : listsn (size sos) (option L). \
\             sos <= tos & (!p < size tos. stable step succs p tos))";
by (Asm_simp_tac 1);
qed "is_dfaD";

Goalw [welltyping_def]
 "[| wti_is_fix_step step wti succs n L; is_dfa dfa step succs n L; \
\    sos : listsn n (option L) |] ==> \
\ dfa sos = (? tos : listsn n (option L). sos <= tos & welltyping wti tos)";
by (dtac is_dfaD 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addDs [wti_is_fix_stepD]) 1);
qed "dfa_iff_welltyping";

Goal
 "x:M ==> replicate n x : listsn n M";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [in_listsn_Suc_iff,Bex_def]) 1);
qed "replicate_in_listsn";
Addsimps [replicate_in_listsn];

Goal "!ys. replicate n x <= ys = (length ys = n & (!y:set ys. x <= y))";
by (induct_tac "n" 1);
 by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_le_iff,length_Suc_conv]) 1);
by (Force_tac 1);
qed_spec_mp "replicate_le_conv";
AddIffs [replicate_le_conv];

Goal
 "[| wti_is_fix_step step wti succs n L; is_dfa dfa step succs n L; \
\    0 < n; init : (option L) |] ==> \
\ dfa (init # replicate (n-1) None) = \
\ (? tos : listsn n (option L). init <= tos!0 & welltyping wti tos)";
by (subgoal_tac "? m. n = m+1" 1);
 by (res_inst_tac [("x","n-1")] exI 2);
 by (arith_tac 2);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (dtac dfa_iff_welltyping 1);
  by (assume_tac 1);
 by (etac trans 2);
 by (asm_simp_tac (simpset() addsimps [in_listsn_Suc_iff,Bex_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_le_iff]) 1);
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (rtac bexI 1);
  by (rtac conjI 1);
   by (assume_tac 2);
  by (assume_tac 2);
 by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_listsn_Suc_iff,Bex_def]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps []) 1);
by (rtac exI 1);
by (rtac conjI 1);
 by (rtac conjI 2);
  by (assume_tac 3);
 by (Blast_tac 1);
by (Force_tac 1);
qed "dfa_iff_welltyping0";
