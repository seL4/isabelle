(*  Title:      HOL/IOA/NTP/Receiver.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

Goal
 "S_msg(m) ~: actions(receiver_asig)      &   \
\ R_msg(m) : actions(receiver_asig)       &   \
\ S_pkt(pkt) ~: actions(receiver_asig) &   \
\ R_pkt(pkt) : actions(receiver_asig)  &   \
\ S_ack(b) : actions(receiver_asig)    &   \
\ R_ack(b) ~: actions(receiver_asig)   &   \
\ C_m_s ~: actions(receiver_asig)         &   \
\ C_m_r : actions(receiver_asig)          &   \
\ C_r_s ~: actions(receiver_asig)         &   \
\ C_r_r(m) : actions(receiver_asig)";
  by (simp_tac (simpset() addsimps (Receiver.receiver_asig_def :: actions_def :: 
                                  asig_projections)) 1);
qed "in_receiver_asig";

val receiver_projections = 
   [Receiver.rq_def,
    Receiver.rsent_def,
    Receiver.rrcvd_def,
    Receiver.rbit_def,
    Receiver.rsending_def];


