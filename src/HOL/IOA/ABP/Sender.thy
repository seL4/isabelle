(*  Title:      HOL/IOA/example/Sender.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation: sender
*)

Sender = IOA + Action + List + Lemmas +

types

'm sender_state = "'m list  *  bool"
(*                messages     Alternating Bit   *)

consts

sender_asig   :: "'m action signature"
sender_trans  :: "('m action, 'm sender_state)transition set"
sender_ioa    :: "('m action, 'm sender_state)ioa"
sq            :: "'m sender_state => 'm list"
sbit          :: "'m sender_state => bool"

defs

sq_def       "sq == fst"
sbit_def     "sbit == snd"

sender_asig_def
  "sender_asig == ((UN m. {S_msg(m)}) Un (UN b. {R_ack(b)}),       \
\                  UN pkt. {S_pkt(pkt)},                   \
\                  {})"

sender_trans_def "sender_trans ==                                     \
\ {tr. let s = fst(tr);                                               \
\          t = snd(snd(tr))                                           \
\      in case fst(snd(tr))                                           \
\      of   \
\      Next     => if sq(s)=[] then t=s else False |                \
\      S_msg(m) => sq(t)=sq(s)@[m]   &                                \
\                  sbit(t)=sbit(s)  |                                 \
\      R_msg(m) => False |                                            \
\      S_pkt(pkt) => sq(s) ~= []  &                                   \
\		     hdr(pkt) = sbit(s)      &                        \
\                    msg(pkt) = hd(sq(s))    &                   \
\                    sq(t) = sq(s)           &                        \
\                    sbit(t) = sbit(s) |                              \
\      R_pkt(pkt) => False |                                          \
\      S_ack(b)   => False |                                          \
\      R_ack(b)   => if b = sbit(s) then                              \
\		     sq(t)=tl(sq(s)) & sbit(t)=(~sbit(s)) else   \
\		     sq(t)=sq(s) & sbit(t)=sbit(s)}"

sender_ioa_def "sender_ioa == \
\ (sender_asig, {([],True)}, sender_trans)"

end
