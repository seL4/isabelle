(*  Title:      HOLCF/IOA/ABP/Receiver.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The implementation: receiver *}

theory Receiver
imports IOA Action Lemmas
begin

types
  'm receiver_state = "'m list * bool"  -- {* messages, mode *}

constdefs
  rq            :: "'m receiver_state => 'm list"
  "rq == fst"

  rbit          :: "'m receiver_state => bool"
  "rbit == snd"

receiver_asig :: "'m action signature"
"receiver_asig ==
  (UN pkt. {R_pkt(pkt)},
  (UN m. {R_msg(m)}) Un (UN b. {S_ack(b)}),
  {})"

receiver_trans :: "('m action, 'm receiver_state)transition set"
"receiver_trans ==
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in
      case fst(snd(tr))
      of
      Next    =>  False |
      S_msg(m) => False |
      R_msg(m) => (rq(s) ~= [])  &
                   m = hd(rq(s))  &
                   rq(t) = tl(rq(s))   &
                  rbit(t)=rbit(s)  |
      S_pkt(pkt) => False |
      R_pkt(pkt) => if (hdr(pkt) ~= rbit(s))&rq(s)=[] then
                         rq(t) = (rq(s)@[msg(pkt)]) &rbit(t) = (~rbit(s)) else
                         rq(t) =rq(s) & rbit(t)=rbit(s)  |
      S_ack(b) => b = rbit(s)                        &
                      rq(t) = rq(s)                    &
                      rbit(t)=rbit(s) |
      R_ack(b) => False}"

receiver_ioa :: "('m action, 'm receiver_state)ioa"
"receiver_ioa ==
 (receiver_asig, {([],False)}, receiver_trans,{},{})"

ML {* use_legacy_bindings (the_context ()) *}

end
