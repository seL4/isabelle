(*  Title:      HOL/HOLCF/IOA/ABP/Impl.thy
    Author:     Olaf Müller
*)

section {* The implementation *}

theory Impl
imports Sender Receiver Abschannel
begin

type_synonym
  'm impl_state = "'m sender_state * 'm receiver_state * 'm packet list * bool list"
  (*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)

definition
 impl_ioa :: "('m action, 'm impl_state)ioa" where
 "impl_ioa = (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)"

definition
 sen :: "'m impl_state => 'm sender_state" where
 "sen = fst"

definition
 rec :: "'m impl_state => 'm receiver_state" where
 "rec = fst o snd"

definition
 srch :: "'m impl_state => 'm packet list" where
 "srch = fst o snd o snd"

definition
 rsch :: "'m impl_state => bool list" where
 "rsch = snd o snd o snd"

end
