(*  Title:      HOLCF/IOA/ABP/Impl.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The implementation.
*)

Impl = Sender + Receiver +  Abschannel +

types 

'm impl_state 
= "'m sender_state * 'm receiver_state * 'm packet list * bool list"
(*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)


constdefs

 impl_ioa    :: ('m action, 'm impl_state)ioa
 "impl_ioa == (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)"

 sen         :: 'm impl_state => 'm sender_state
 "sen == fst"

 rec         :: 'm impl_state => 'm receiver_state
 "rec == fst o snd"

 srch        :: 'm impl_state => 'm packet list
 "srch == fst o snd o snd"

 rsch        :: 'm impl_state => bool list
 "rsch == snd o snd o snd"

end
