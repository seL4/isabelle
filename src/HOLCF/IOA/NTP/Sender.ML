(*  Title:      HOL/IOA/NTP/Sender.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

Goal
 "S_msg(m) : actions(sender_asig)       &   \
\ R_msg(m) ~: actions(sender_asig)      &   \
\ S_pkt(pkt) : actions(sender_asig)  &   \
\ R_pkt(pkt) ~: actions(sender_asig) &   \
\ S_ack(b) ~: actions(sender_asig)   &   \
\ R_ack(b) : actions(sender_asig)    &   \
\ C_m_s : actions(sender_asig)          &   \
\ C_m_r ~: actions(sender_asig)         &   \
\ C_r_s : actions(sender_asig)          &   \
\ C_r_r(m) ~: actions(sender_asig)";
by (simp_tac (simpset() addsimps 
             (sender_asig_def :: actions_def :: 
              asig_projections)) 1);
qed "in_sender_asig";

val sender_projections = 
   [sq_def,ssent_def,srcvd_def,
    sbit_def,ssending_def];
