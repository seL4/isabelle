(*  Title:      HOL/IOA/example/Receiver.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation: receiver
*)

Receiver = List + IOA + Action + Lemmas +

types 

'm receiver_state
= "'m list * bool"
(* messages  mode *)

consts

  receiver_asig :: "'m action signature"
  receiver_trans:: "('m action, 'm receiver_state)transition set"
  receiver_ioa  :: "('m action, 'm receiver_state)ioa"
  rq            :: "'m receiver_state => 'm list"
  rbit          :: "'m receiver_state => bool"

defs

rq_def       "rq == fst"
rbit_def     "rbit == snd"

receiver_asig_def "receiver_asig ==            \
\ (UN pkt. {R_pkt(pkt)},                       \
\  (UN m. {R_msg(m)}) Un (UN b. {S_ack(b)}),   \
\  {})"

receiver_trans_def "receiver_trans ==                                    \
\ {tr. let s = fst(tr);                                                  \
\          t = snd(snd(tr))                                              \
\      in                                                                \
\      case fst(snd(tr))                                                 \
\      of   \
\      Next    =>  False |     \
\      S_msg(m) => False |                                               \
\      R_msg(m) => (rq(s) ~= [])  &                                     \
\		   m = hd(rq(s))  &                             \
\		   rq(t) = tl(rq(s))   &                              \
\                  rbit(t)=rbit(s)  |                                 \
\      S_pkt(pkt) => False |                                          \
\      R_pkt(pkt) => if (hdr(pkt) ~= rbit(s))&rq(s)=[] then            \
\		         rq(t) = (rq(s)@[msg(pkt)]) &rbit(t) = (~rbit(s)) else  \
\		         rq(t) =rq(s) & rbit(t)=rbit(s)  |   \
\      S_ack(b) => b = rbit(s)                        &               \
\                      rq(t) = rq(s)                    &             \
\                      rbit(t)=rbit(s) |                              \
\      R_ack(b) => False}"

receiver_ioa_def "receiver_ioa == \
\ (receiver_asig, {([],False)}, receiver_trans)"

end
