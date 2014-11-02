(*  Title:      HOL/HOLCF/IOA/NTP/Sender.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

section {* The implementation: sender *}

theory Sender
imports IOA Action
begin

type_synonym
'm sender_state = "'m list * bool multiset * bool multiset * bool * bool"
(*                messages   #sent           #received      header  mode *)

definition sq :: "'m sender_state => 'm list" where "sq = fst"
definition ssent :: "'m sender_state => bool multiset" where "ssent = fst o snd"
definition srcvd :: "'m sender_state => bool multiset" where "srcvd = fst o snd o snd"
definition sbit :: "'m sender_state => bool" where "sbit = fst o snd o snd o snd"
definition ssending :: "'m sender_state => bool" where "ssending = snd o snd o snd o snd"

definition
  sender_asig :: "'m action signature" where
  "sender_asig = ((UN m. {S_msg(m)}) Un (UN b. {R_ack(b)}),
                   UN pkt. {S_pkt(pkt)},
                   {C_m_s,C_r_s})"

definition
  sender_trans :: "('m action, 'm sender_state)transition set" where
  "sender_trans =
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in case fst(snd(tr))
      of
      S_msg(m) => sq(t)=sq(s)@[m]   &
                  ssent(t)=ssent(s) &
                  srcvd(t)=srcvd(s) &
                  sbit(t)=sbit(s)   &
                  ssending(t)=ssending(s) |
      R_msg(m) => False |
      S_pkt(pkt) => hdr(pkt) = sbit(s)      &
                       (? Q. sq(s) = (msg(pkt)#Q))  &
                       sq(t) = sq(s)           &
                       ssent(t) = addm (ssent s) (sbit s) &
                       srcvd(t) = srcvd(s) &
                       sbit(t) = sbit(s)   &
                       ssending(s)         &
                       ssending(t) |
    R_pkt(pkt) => False |
    S_ack(b)   => False |
      R_ack(b) => sq(t)=sq(s)                  &
                     ssent(t)=ssent(s)            &
                     srcvd(t) = addm (srcvd s) b  &
                     sbit(t)=sbit(s)              &
                     ssending(t)=ssending(s) |
      C_m_s => count (ssent s) (~sbit s) < count (srcvd s) (~sbit s) &
               sq(t)=sq(s)       &
               ssent(t)=ssent(s) &
               srcvd(t)=srcvd(s) &
               sbit(t)=sbit(s)   &
               ssending(s)       &
               ~ssending(t) |
      C_m_r => False |
      C_r_s => count (ssent s) (sbit s) <= count (srcvd s) (~sbit s) &
               sq(t)=tl(sq(s))      &
               ssent(t)=ssent(s)    &
               srcvd(t)=srcvd(s)    &
               sbit(t) = (~sbit(s)) &
               ~ssending(s)         &
               ssending(t) |
      C_r_r(m) => False}"

definition
  sender_ioa :: "('m action, 'm sender_state)ioa" where
  "sender_ioa =
   (sender_asig, {([],{|},{|},False,True)}, sender_trans,{},{})"

lemma in_sender_asig: 
  "S_msg(m) : actions(sender_asig)"
  "R_msg(m) ~: actions(sender_asig)"
  "S_pkt(pkt) : actions(sender_asig)"
  "R_pkt(pkt) ~: actions(sender_asig)"
  "S_ack(b) ~: actions(sender_asig)"
  "R_ack(b) : actions(sender_asig)"
  "C_m_s : actions(sender_asig)"
  "C_m_r ~: actions(sender_asig)"
  "C_r_s : actions(sender_asig)"
  "C_r_r(m) ~: actions(sender_asig)"
  by (simp_all add: sender_asig_def actions_def asig_projections)

lemmas sender_projections = sq_def ssent_def srcvd_def sbit_def ssending_def

end
