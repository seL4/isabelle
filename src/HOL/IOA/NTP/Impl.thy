(*  Title:      HOL/IOA/NTP/Impl.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation
*)

Impl = Sender + Receiver + Abschannel +

types 

'm impl_state 
= "'m sender_state * 'm receiver_state * 'm packet multiset * bool multiset"
(*  sender_state   *  receiver_state   *    srch_state      * rsch_state *)


consts
 impl_ioa    :: ('m action, 'm impl_state)ioa
 sen         :: 'm impl_state => 'm sender_state
 rec         :: 'm impl_state => 'm receiver_state
 srch        :: 'm impl_state => 'm packet multiset
 rsch        :: 'm impl_state => bool multiset
 inv1, inv2, 
 inv3, inv4  :: 'm impl_state => bool
 hdr_sum     :: 'm packet multiset => bool => nat

defs

 impl_def
  "impl_ioa == (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)"

 sen_def   "sen == fst"
 rec_def   "rec == fst o snd"
 srch_def "srch == fst o snd o snd"
 rsch_def "rsch == snd o snd o snd"

hdr_sum_def
   "hdr_sum M b == countm M (%pkt.hdr(pkt) = b)"

(* Lemma 5.1 *)
inv1_def 
  "inv1(s) ==                                                                 
     (!b. count (rsent(rec s)) b = count (srcvd(sen s)) b + count (rsch s) b) 
   & (!b. count (ssent(sen s)) b                                              
          = hdr_sum (rrcvd(rec s)) b + hdr_sum (srch s) b)"

(* Lemma 5.2 *)
 inv2_def "inv2(s) ==                                                   
  (rbit(rec(s)) = sbit(sen(s)) &                                       
   ssending(sen(s)) &                                                  
   count (rsent(rec s)) (~sbit(sen s)) <= count (ssent(sen s)) (~sbit(sen s)) &
   count (ssent(sen s)) (~sbit(sen s)) <= count (rsent(rec s)) (sbit(sen s)))  
   |                                                                   
  (rbit(rec(s)) = (~sbit(sen(s))) &                                    
   rsending(rec(s)) &                                                  
   count (ssent(sen s)) (~sbit(sen s)) <= count (rsent(rec s)) (sbit(sen s)) &
   count (rsent(rec s)) (sbit(sen s)) <= count (ssent(sen s)) (sbit(sen s)))"

(* Lemma 5.3 *)
 inv3_def "inv3(s) ==                                                   
   rbit(rec(s)) = sbit(sen(s))                                         
   --> (!m. sq(sen(s))=[] | m ~= hd(sq(sen(s)))                        
        -->  count (rrcvd(rec s)) (sbit(sen(s)),m)                     
             + count (srch s) (sbit(sen(s)),m)                         
            <= count (rsent(rec s)) (~sbit(sen s)))"

(* Lemma 5.4 *)
 inv4_def "inv4(s) == rbit(rec(s)) = (~sbit(sen(s))) --> sq(sen(s)) ~= []"

end
