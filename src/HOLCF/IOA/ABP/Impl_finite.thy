(*  Title:      HOLCF/IOA/ABP/Impl.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1995  TU Muenchen

The implementation
*)

Impl_finite = Sender + Receiver +  Abschannel_finite +
  
types 

'm impl_fin_state 
= "'m sender_state * 'm receiver_state * 'm packet list * bool list"
(*  sender_state   *  receiver_state   *    srch_state  * rsch_state *)

constdefs

 impl_fin_ioa    :: ('m action, 'm impl_fin_state)ioa
 "impl_fin_ioa == (sender_ioa || receiver_ioa || srch_fin_ioa ||
                   rsch_fin_ioa)"

 sen_fin         :: 'm impl_fin_state => 'm sender_state
 "sen_fin == fst"

 rec_fin         :: 'm impl_fin_state => 'm receiver_state
 "rec_fin == fst o snd"

 srch_fin        :: 'm impl_fin_state => 'm packet list
 "srch_fin == fst o snd o snd"

 rsch_fin        :: 'm impl_fin_state => bool list
 "rsch_fin == snd o snd o snd"

end

