(*  Title:      HOL/IOA/NTP/Receiver.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

header {* The implementation: receiver *}

theory Receiver
imports IOA Action
begin

types

'm receiver_state
= "'m list * bool multiset * 'm packet multiset * bool * bool"
(* messages  #replies        #received            header mode *)

definition rq :: "'m receiver_state => 'm list" where "rq == fst"
definition rsent :: "'m receiver_state => bool multiset" where "rsent == fst o snd"
definition rrcvd :: "'m receiver_state => 'm packet multiset" where "rrcvd == fst o snd o snd"
definition rbit :: "'m receiver_state => bool" where "rbit == fst o snd o snd o snd"
definition rsending :: "'m receiver_state => bool" where "rsending == snd o snd o snd o snd"

definition
  receiver_asig :: "'m action signature" where
  "receiver_asig =
   (UN pkt. {R_pkt(pkt)},
    (UN m. {R_msg(m)}) Un (UN b. {S_ack(b)}),
    insert C_m_r (UN m. {C_r_r(m)}))"

definition
  receiver_trans:: "('m action, 'm receiver_state)transition set" where
"receiver_trans =
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in
      case fst(snd(tr))
      of
      S_msg(m) => False |
      R_msg(m) => rq(s) = (m # rq(t))   &
                  rsent(t)=rsent(s)     &
                  rrcvd(t)=rrcvd(s)     &
                  rbit(t)=rbit(s)       &
                  rsending(t)=rsending(s) |
      S_pkt(pkt) => False |
      R_pkt(pkt) => rq(t) = rq(s)                        &
                       rsent(t) = rsent(s)                  &
                       rrcvd(t) = addm (rrcvd s) pkt        &
                       rbit(t) = rbit(s)                    &
                       rsending(t) = rsending(s) |
      S_ack(b) => b = rbit(s)                        &
                     rq(t) = rq(s)                      &
                     rsent(t) = addm (rsent s) (rbit s) &
                     rrcvd(t) = rrcvd(s)                &
                     rbit(t)=rbit(s)                    &
                     rsending(s)                        &
                     rsending(t) |
      R_ack(b) => False |
      C_m_s => False |
 C_m_r => count (rsent s) (~rbit s) < countm (rrcvd s) (%y. hdr(y)=rbit(s)) &
             rq(t) = rq(s)                        &
             rsent(t)=rsent(s)                    &
             rrcvd(t)=rrcvd(s)                    &
             rbit(t)=rbit(s)                      &
             rsending(s)                          &
             ~rsending(t) |
    C_r_s => False |
 C_r_r(m) => count (rsent s) (rbit s) <= countm (rrcvd s) (%y. hdr(y)=rbit(s)) &
             count (rsent s) (~rbit s) < count (rrcvd s) (rbit(s),m) &
             rq(t) = rq(s)@[m]                         &
             rsent(t)=rsent(s)                         &
             rrcvd(t)=rrcvd(s)                         &
             rbit(t) = (~rbit(s))                      &
             ~rsending(s)                              &
             rsending(t)}"

definition
  receiver_ioa  :: "('m action, 'm receiver_state)ioa" where
  "receiver_ioa =
    (receiver_asig, {([],{|},{|},False,False)}, receiver_trans,{},{})"

lemma in_receiver_asig:
  "S_msg(m) ~: actions(receiver_asig)"
  "R_msg(m) : actions(receiver_asig)"
  "S_pkt(pkt) ~: actions(receiver_asig)"
  "R_pkt(pkt) : actions(receiver_asig)"
  "S_ack(b) : actions(receiver_asig)"
  "R_ack(b) ~: actions(receiver_asig)"
  "C_m_s ~: actions(receiver_asig)"
  "C_m_r : actions(receiver_asig)"
  "C_r_s ~: actions(receiver_asig)"
  "C_r_r(m) : actions(receiver_asig)"
  by (simp_all add: receiver_asig_def actions_def asig_projections)

lemmas receiver_projections = rq_def rsent_def rrcvd_def rbit_def rsending_def

end
