(*  Title:      HOL/IOA/NTP/Receiver.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation: receiver
*)

Receiver = List + IOA + Action + 

types 

'm receiver_state
= "'m list * bool multiset * 'm packet multiset * bool * bool"
(* messages  #replies        #received            header mode *)

consts

  receiver_asig :: 'm action signature
  receiver_trans:: ('m action, 'm receiver_state)transition set
  receiver_ioa  :: ('m action, 'm receiver_state)ioa
  rq            :: 'm receiver_state => 'm list
  rsent         :: 'm receiver_state => bool multiset
  rrcvd         :: 'm receiver_state => 'm packet multiset
  rbit          :: 'm receiver_state => bool
  rsending      :: 'm receiver_state => bool

defs

rq_def       "rq == fst"
rsent_def    "rsent == fst o snd"
rrcvd_def    "rrcvd == fst o snd o snd"
rbit_def     "rbit == fst o snd o snd o snd"
rsending_def "rsending == snd o snd o snd o snd"

receiver_asig_def "receiver_asig ==            
 (UN pkt. {R_pkt(pkt)},                       
  (UN m. {R_msg(m)}) Un (UN b. {S_ack(b)}),   
  insert C_m_r (UN m. {C_r_r(m)}))"

receiver_trans_def "receiver_trans ==                                    
 {tr. let s = fst(tr);                                                  
          t = snd(snd(tr))                                              
      in                                                                
      case fst(snd(tr))                                                 
      of                                                                
      S_msg(m) => False |                                               
      R_msg(m) => rq(s) = (m # rq(t))   &                               
                  rsent(t)=rsent(s)     &                               
                  rrcvd(t)=rrcvd(s)     &                               
                  rbit(t)=rbit(s)       &                               
                  rsending(t)=rsending(s) |                             
      S_pkt(pkt) => False |                                          
      R_pkt(pkt) => rq(t) = rq(s)                        &           
                       rsent(t) = rsent(s)                  &           
                       rrcvd(t) = addm (rrcvd s) pkt        &           
                       rbit(t) = rbit(s)                    &           
                       rsending(t) = rsending(s) |                      
      S_ack(b) => b = rbit(s)                        &               
                     rq(t) = rq(s)                      &               
                     rsent(t) = addm (rsent s) (rbit s) &               
                     rrcvd(t) = rrcvd(s)                &               
                     rbit(t)=rbit(s)                    &               
                     rsending(s)                        &               
                     rsending(t) |                                      
      R_ack(b) => False |                                               
      C_m_s => False |                                                  
 C_m_r => count (rsent s) (~rbit s) < countm (rrcvd s) (%y.hdr(y)=rbit(s)) & 
             rq(t) = rq(s)                        &                     
             rsent(t)=rsent(s)                    &                     
             rrcvd(t)=rrcvd(s)                    &                     
             rbit(t)=rbit(s)                      &                     
             rsending(s)                          &                     
             ~rsending(t) |                                             
    C_r_s => False |                                                    
 C_r_r(m) => count (rsent s) (rbit s) <= countm (rrcvd s) (%y.hdr(y)=rbit(s)) & 
             count (rsent s) (~rbit s) < count (rrcvd s) (rbit(s),m) &  
             rq(t) = rq(s)@[m]                         &                
             rsent(t)=rsent(s)                         &                
             rrcvd(t)=rrcvd(s)                         &                
             rbit(t) = (~rbit(s))                      &                
             ~rsending(s)                              &                
             rsending(t)}"


receiver_ioa_def "receiver_ioa == 
 (receiver_asig, {([],{|},{|},False,False)}, receiver_trans,{},{})"

end
