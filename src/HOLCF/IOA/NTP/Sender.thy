(*  Title:      HOL/IOA/NTP/Sender.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation: sender
*)

Sender = IOA + Action + List +

types

'm sender_state = "'m list * bool multiset * bool multiset * bool * bool"
(*                messages   #sent           #received      header  mode *)

consts

sender_asig   :: 'm action signature
sender_trans  :: ('m action, 'm sender_state)transition set
sender_ioa    :: ('m action, 'm sender_state)ioa
sq            :: 'm sender_state => 'm list
ssent,srcvd   :: 'm sender_state => bool multiset
sbit          :: 'm sender_state => bool
ssending      :: 'm sender_state => bool

defs

sq_def       "sq == fst"
ssent_def    "ssent == fst o snd"
srcvd_def    "srcvd == fst o snd o snd"
sbit_def     "sbit == fst o snd o snd o snd"
ssending_def "ssending == snd o snd o snd o snd"

sender_asig_def
  "sender_asig == ((UN m. {S_msg(m)}) Un (UN b. {R_ack(b)}),       
                  UN pkt. {S_pkt(pkt)},                           
                  {C_m_s,C_r_s})"

sender_trans_def "sender_trans ==                                     
 {tr. let s = fst(tr);                                               
          t = snd(snd(tr))                                           
      in case fst(snd(tr))                                           
      of                                                             
      S_msg(m) => sq(t)=sq(s)@[m]   &                                
                  ssent(t)=ssent(s) &                                
                  srcvd(t)=srcvd(s) &                                
                  sbit(t)=sbit(s)   &                                
                  ssending(t)=ssending(s) |                          
      R_msg(m) => False |                                            
      S_pkt(pkt) => hdr(pkt) = sbit(s)      &                        
                       (? Q. sq(s) = (msg(pkt)#Q))  &                
                       sq(t) = sq(s)           &                     
                       ssent(t) = addm (ssent s) (sbit s) &          
                       srcvd(t) = srcvd(s) &                         
                       sbit(t) = sbit(s)   &                         
                       ssending(s)         &                         
                       ssending(t) |                                 
    R_pkt(pkt) => False |                                            
    S_ack(b)   => False |                                            
      R_ack(b) => sq(t)=sq(s)                  &                     
                     ssent(t)=ssent(s)            &                  
                     srcvd(t) = addm (srcvd s) b  &                  
                     sbit(t)=sbit(s)              &                  
                     ssending(t)=ssending(s) |                       
      C_m_s => count (ssent s) (~sbit s) < count (srcvd s) (~sbit s) & 
               sq(t)=sq(s)       &                                   
               ssent(t)=ssent(s) &                                   
               srcvd(t)=srcvd(s) &                                   
               sbit(t)=sbit(s)   &                                   
               ssending(s)       &                                   
               ~ssending(t) |                                        
      C_m_r => False |                                               
      C_r_s => count (ssent s) (sbit s) <= count (srcvd s) (~sbit s) & 
               sq(t)=tl(sq(s))      &                                
               ssent(t)=ssent(s)    &                                
               srcvd(t)=srcvd(s)    &                                
               sbit(t) = (~sbit(s)) &                                
               ~ssending(s)         &                                
               ssending(t) |                                         
      C_r_r(m) => False}"

sender_ioa_def "sender_ioa == 
 (sender_asig, {([],{|},{|},False,True)}, sender_trans,{},{})"

end
