(*  Title:      HOL/IOA/NTP/Sender.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen
*)

goal Sender.thy
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
by(simp_tac (!simpset addsimps 
             (Sender.sender_asig_def :: actions_def :: 
              asig_projections @ set_lemmas)) 1);
qed "in_sender_asig";

val sender_projections = 
   [Sender.sq_def,Sender.ssent_def,Sender.srcvd_def,
    Sender.sbit_def,Sender.ssending_def];
