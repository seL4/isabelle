(*  Title:      HOL/IOA/NTP/Abschannel.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The (faulty) transmission channel (both directions).
*)

Abschannel = IOA + Action + 
 
datatype ('a)abs_action =   S('a) | R('a)

consts
 
ch_asig  :: "'a abs_action signature"

ch_trans :: ('a abs_action, 'a multiset)transition set

ch_ioa   :: ('a abs_action, 'a multiset)ioa

rsch_actions  :: 'm action => bool abs_action option
srch_actions  :: "'m action =>(bool * 'm) abs_action option"

srch_asig, 
rsch_asig  :: "'m action signature"

srch_wfair, srch_sfair, rsch_sfair,
rsch_wfair ::('m action)set set

srch_trans :: ('m action, 'm packet multiset)transition set
rsch_trans :: ('m action, bool multiset)transition set

srch_ioa   :: ('m action, 'm packet multiset)ioa
rsch_ioa   :: ('m action, bool multiset)ioa   


defs

srch_asig_def "srch_asig == asig_of(srch_ioa)"
rsch_asig_def "rsch_asig == asig_of(rsch_ioa)"

srch_trans_def "srch_trans == trans_of(srch_ioa)"  
rsch_trans_def "rsch_trans == trans_of(rsch_ioa)"

srch_wfair_def "srch_wfair == wfair_of(srch_ioa)"  
rsch_wfair_def "rsch_wfair == wfair_of(rsch_ioa)"

srch_sfair_def "srch_sfair == sfair_of(srch_ioa)"  
rsch_sfair_def "rsch_sfair == sfair_of(rsch_ioa)"

srch_ioa_def "srch_ioa == rename ch_ioa srch_actions"
rsch_ioa_def "rsch_ioa == rename ch_ioa rsch_actions"


ch_asig_def "ch_asig == (UN b. {S(b)}, UN b. {R(b)}, {})"

ch_trans_def "ch_trans ==                                       
 {tr. let s = fst(tr);                                         
          t = snd(snd(tr))                                     
      in                                                       
      case fst(snd(tr))                                        
        of S(b) => t = addm s b |                            
           R(b) => count s b ~= 0 & t = delm s b}"

ch_ioa_def "ch_ioa == (ch_asig, {{|}}, ch_trans,{},{})"


rsch_actions_def "rsch_actions (akt) ==        
            case akt of                
           S_msg(m) => None |         
            R_msg(m) => None |         
           S_pkt(packet) => None |    
            R_pkt(packet) => None |    
            S_ack(b) => Some(S(b)) |   
            R_ack(b) => Some(R(b)) |   
           C_m_s =>  None  |          
           C_m_r =>  None |           
           C_r_s =>  None  |          
           C_r_r(m) => None"

srch_actions_def "srch_actions (akt) ==         
            case akt of                
           S_msg(m) => None |         
            R_msg(m) => None |         
           S_pkt(p) => Some(S(p)) |   
            R_pkt(p) => Some(R(p)) |   
            S_ack(b) => None |         
            R_ack(b) => None |         
           C_m_s => None |            
           C_m_r => None |            
           C_r_s => None |            
           C_r_r(m) => None"

end  


















