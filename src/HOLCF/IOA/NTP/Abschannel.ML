(*  Title:      HOL/IOA/NTP/Abschannel.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1994  TU Muenchen

Derived rules
*)

open Abschannel;

val unfold_renaming = 
 [srch_asig_def, rsch_asig_def, rsch_ioa_def, srch_ioa_def, ch_ioa_def, 
   ch_asig_def, srch_actions_def, rsch_actions_def, rename_def, rename_set_def, asig_of_def, 
   actions_def, srch_trans_def, rsch_trans_def, ch_trans_def,starts_of_def, 
   trans_of_def] @ asig_projections;

goal Abschannel.thy
     "S_msg(m) ~: actions(srch_asig)        &    \
     \ R_msg(m) ~: actions(srch_asig)        &    \
     \ S_pkt(pkt) : actions(srch_asig)    &    \
     \ R_pkt(pkt) : actions(srch_asig)    &    \
     \ S_ack(b) ~: actions(srch_asig)     &    \
     \ R_ack(b) ~: actions(srch_asig)     &    \
     \ C_m_s ~: actions(srch_asig)           &    \
     \ C_m_r ~: actions(srch_asig)           &    \
     \ C_r_s ~: actions(srch_asig)  & C_r_r(m) ~: actions(srch_asig)";

by (simp_tac (simpset() addsimps unfold_renaming) 1);
qed"in_srch_asig";

goal Abschannel.thy
      "S_msg(m) ~: actions(rsch_asig)         & \
     \ R_msg(m) ~: actions(rsch_asig)         & \
     \ S_pkt(pkt) ~: actions(rsch_asig)    & \
     \ R_pkt(pkt) ~: actions(rsch_asig)    & \
     \ S_ack(b) : actions(rsch_asig)       & \
     \ R_ack(b) : actions(rsch_asig)       & \
     \ C_m_s ~: actions(rsch_asig)            & \
     \ C_m_r ~: actions(rsch_asig)            & \
     \ C_r_s ~: actions(rsch_asig)            & \
     \ C_r_r(m) ~: actions(rsch_asig)";

by (simp_tac (simpset() addsimps unfold_renaming) 1);
qed"in_rsch_asig";

goal Abschannel.thy "srch_ioa = \
\   (srch_asig, {{|}}, srch_trans,srch_wfair,srch_sfair)";
by (simp_tac (simpset() addsimps [srch_asig_def,srch_trans_def, asig_of_def, trans_of_def,
              wfair_of_def, sfair_of_def,srch_wfair_def,srch_sfair_def]) 1);
by (simp_tac (simpset() addsimps unfold_renaming) 1);
qed"srch_ioa_thm";

goal Abschannel.thy "rsch_ioa = \
\    (rsch_asig, {{|}}, rsch_trans,rsch_wfair,rsch_sfair)";
by (simp_tac (simpset() addsimps [rsch_asig_def,rsch_trans_def, asig_of_def, trans_of_def,
              wfair_of_def, sfair_of_def,rsch_wfair_def,rsch_sfair_def]) 1);
by (simp_tac (simpset() addsimps unfold_renaming) 1);
qed"rsch_ioa_thm";

