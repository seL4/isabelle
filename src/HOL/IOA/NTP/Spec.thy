(*  Title:      HOL/IOA/NTP/Spec.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The specification of reliable transmission
*)

Spec = List + IOA + Action +

consts

spec_sig   :: "'m action signature"
spec_trans :: "('m action, 'm list)transition set"
spec_ioa   :: "('m action, 'm list)ioa"

defs

sig_def "spec_sig == (UN m.{S_msg(m)}, 
                     UN m.{R_msg(m)}, 
                     {})"

trans_def "spec_trans ==                           
 {tr. let s = fst(tr);                            
          t = snd(snd(tr))                        
      in                                          
      case fst(snd(tr))                           
      of                                          
      S_msg(m) => t = s@[m]  |                    
      R_msg(m) => s = (m#t)  |                    
      S_pkt(pkt) => False |                    
      R_pkt(pkt) => False |                    
      S_ack(b) => False |                      
      R_ack(b) => False |                      
      C_m_s => False |                            
      C_m_r => False |                            
      C_r_s => False |                            
      C_r_r(m) => False}"

ioa_def "spec_ioa == (spec_sig, {[]}, spec_trans)"

end
