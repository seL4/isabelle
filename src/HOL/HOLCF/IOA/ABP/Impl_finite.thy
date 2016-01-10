(*  Title:      HOL/HOLCF/IOA/ABP/Impl_finite.thy
    Author:     Olaf Müller
*)

section \<open>The implementation\<close>

theory Impl_finite
imports Sender Receiver Abschannel_finite
begin

type_synonym
  'm impl_fin_state
    = "'m sender_state * 'm receiver_state * 'm packet list * bool list"
(*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)

definition
  impl_fin_ioa :: "('m action, 'm impl_fin_state)ioa" where
  "impl_fin_ioa = (sender_ioa \<parallel> receiver_ioa \<parallel> srch_fin_ioa \<parallel>
                  rsch_fin_ioa)"

definition
  sen_fin :: "'m impl_fin_state => 'm sender_state" where
  "sen_fin = fst"

definition
  rec_fin :: "'m impl_fin_state => 'm receiver_state" where
  "rec_fin = fst \<circ> snd"

definition
  srch_fin :: "'m impl_fin_state => 'm packet list" where
  "srch_fin = fst \<circ> snd \<circ> snd"

definition
  rsch_fin :: "'m impl_fin_state => bool list" where
  "rsch_fin = snd \<circ> snd \<circ> snd"

end
