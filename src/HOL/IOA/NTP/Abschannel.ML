(*  Title:      HOL/IOA/NTP/Abschannel.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Olaf Mueller
    Copyright   1994  TU Muenchen

Derived rules
*)

open Abschannel;

Addsimps 
 ([srch_asig_def, rsch_asig_def, rsch_ioa_def, srch_ioa_def, ch_ioa_def, 
   ch_asig_def, srch_actions_def, rsch_actions_def, rename_def, asig_of_def, 
   actions_def, srch_trans_def, rsch_trans_def, ch_trans_def,starts_of_def, 
   trans_of_def] @ asig_projections @ set_lemmas);

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

by(Simp_tac 1);
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

by(Simp_tac 1);
qed"in_rsch_asig";

goal Abschannel.thy "srch_ioa = (srch_asig, {{|}}, srch_trans)";
by (Simp_tac 1);
qed"srch_ioa_thm";

goal Abschannel.thy "rsch_ioa = (rsch_asig, {{|}}, rsch_trans)";
by (Simp_tac 1);
qed"rsch_ioa_thm";

