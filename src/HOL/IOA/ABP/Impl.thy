(*  Title:      HOL/IOA/example/Impl.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation
*)

Impl = Sender + Receiver +  Abschannel +

types 

'm impl_state 
= "'m sender_state * 'm receiver_state * 'm packet list * bool list"
(*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)


consts
 impl_ioa    :: "('m action, 'm impl_state)ioa"
 sen         :: "'m impl_state => 'm sender_state"
 rec         :: "'m impl_state => 'm receiver_state"
 srch        :: "'m impl_state => 'm packet list"
 rsch        :: "'m impl_state => bool list"

defs

 impl_def
  "impl_ioa == (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)"

 sen_def   "sen == fst"
 rec_def   "rec == fst o snd"
 srch_def "srch == fst o snd o snd"
 rsch_def "rsch == snd o snd o snd"

end
