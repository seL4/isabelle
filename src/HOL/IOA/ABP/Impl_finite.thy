(*  Title:      HOL/IOA/ABP/Impl_finite.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Olaf Mueller
    Copyright   1995  TU Muenchen

The finite implementation
*)

Impl_finite = Sender + Receiver +  Abschannel_finite +
  
types 

'm impl_fin_state 
= "'m sender_state * 'm receiver_state * 'm packet list * bool list"
(*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)

consts

 impl_fin_ioa    :: "('m action, 'm impl_fin_state)ioa"
 sen_fin         :: "'m impl_fin_state => 'm sender_state"
 rec_fin         :: "'m impl_fin_state => 'm receiver_state"
 srch_fin        :: "'m impl_fin_state => 'm packet list"
 rsch_fin        :: "'m impl_fin_state => bool list"

defs

 impl_fin_def
  "impl_fin_ioa == (sender_ioa || receiver_ioa || srch_fin_ioa || rsch_fin_ioa)"
 sen_fin_def   "sen_fin == fst"
 rec_fin_def   "rec_fin == fst o snd"
 srch_fin_def "srch_fin == fst o snd o snd"
 rsch_fin_def "rsch_fin == snd o snd o snd"

end

