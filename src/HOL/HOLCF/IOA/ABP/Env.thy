(*  Title:      HOL/HOLCF/IOA/ABP/Env.thy
    Author:     Olaf Müller
*)

section {* The environment *}

theory Env
imports IOA Action
begin

type_synonym
  'm env_state = bool   -- {* give next bit to system *}

definition
  env_asig :: "'m action signature" where
  "env_asig == ({Next},
                 UN m. {S_msg(m)},
                 {})"

definition
  env_trans :: "('m action, 'm env_state)transition set" where
  "env_trans =
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

definition
  env_ioa :: "('m action, 'm env_state)ioa" where
  "env_ioa = (env_asig, {True}, env_trans,{},{})"

axiomatization
  "next" :: "'m env_state => bool"

end
