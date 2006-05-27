(*  Title:      HOLCF/IOA/ABP/Impl.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The environment *}

theory Env
imports IOA Action
begin

types
  'm env_state = bool   -- {* give next bit to system *}

constdefs
env_asig   :: "'m action signature"
"env_asig == ({Next},
               UN m. {S_msg(m)},
               {})"

env_trans  :: "('m action, 'm env_state)transition set"
"env_trans ==
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in case fst(snd(tr))
      of
      Next       => t=True |
      S_msg(m)   => s=True & t=False |
      R_msg(m)   => False |
      S_pkt(pkt) => False |
      R_pkt(pkt) => False |
      S_ack(b)   => False |
      R_ack(b)   => False}"

env_ioa    :: "('m action, 'm env_state)ioa"
"env_ioa == (env_asig, {True}, env_trans,{},{})"

consts
  "next"     :: "'m env_state => bool"

end
