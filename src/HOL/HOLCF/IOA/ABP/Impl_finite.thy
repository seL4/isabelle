(*  Title:      HOL/HOLCF/IOA/ABP/Impl_finite.thy
    Author:     Olaf Müller
*)

section {* The implementation *}

theory Impl_finite
imports Sender Receiver Abschannel_finite
begin

type_synonym
  'm impl_fin_state
    = "'m sender_state * 'm receiver_state * 'm packet list * bool list"
(*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)

definition
  impl_fin_ioa :: "('m action, 'm impl_fin_state)ioa" where
  "impl_fin_ioa = (sender_ioa || receiver_ioa || srch_fin_ioa ||
                  rsch_fin_ioa)"

definition
  sen_fin :: "'m impl_fin_state => 'm sender_state" where
  "sen_fin = fst"

definition
  rec_fin :: "'m impl_fin_state => 'm receiver_state" where
  "rec_fin = fst o snd"

definition
  srch_fin :: "'m impl_fin_state => 'm packet list" where
  "srch_fin = fst o snd o snd"

definition
  rsch_fin :: "'m impl_fin_state => bool list" where
  "rsch_fin = snd o snd o snd"

end
