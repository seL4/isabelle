(*  Title:      HOLCF/IOA/ABP/Abschannel.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The transmission channel.
*)

Abschannel = IOA + Action + Lemmas + List +


datatype ('a)abs_action =   S('a) | R('a)


consts
 
ch_asig  :: "'a abs_action signature"
ch_trans :: ('a abs_action, 'a list)transition set
ch_ioa   :: ('a abs_action, 'a list)ioa

rsch_actions  :: 'm action => bool abs_action option
srch_actions  :: "'m action =>(bool * 'm) abs_action option"

srch_asig, 
rsch_asig  :: "'m action signature"
 
srch_trans :: ('m action, 'm packet list)transition set
rsch_trans :: ('m action, bool list)transition set

srch_ioa   :: ('m action, 'm packet list)ioa
rsch_ioa   :: ('m action, bool list)ioa   


defs

srch_asig_def "srch_asig == asig_of(srch_ioa)"
rsch_asig_def "rsch_asig == asig_of(rsch_ioa)"

srch_trans_def "srch_trans == trans_of(srch_ioa)"  
rsch_trans_def "rsch_trans == trans_of(rsch_ioa)"

srch_ioa_def "srch_ioa == rename ch_ioa srch_actions"
rsch_ioa_def "rsch_ioa == rename ch_ioa rsch_actions"

  
(**********************************************************
       G e n e r i c   C h a n n e l
 *********************************************************)
  
ch_asig_def "ch_asig == (UN b. {S(b)}, UN b. {R(b)}, {})"

ch_trans_def "ch_trans ==                                       
 {tr. let s = fst(tr);                                         
          t = snd(snd(tr))                                     
      in                                                       
      case fst(snd(tr))                                        
        of S(b) => ((t = s) | (t = s @ [b]))  |                
           R(b) => s ~= [] &                                   
                    b = hd(s) &                                 
                    ((t = s) | (t = tl(s)))    }"
  
ch_ioa_def "ch_ioa == (ch_asig, {[]}, ch_trans,{},{})"

(**********************************************************
  C o n c r e t e  C h a n n e l s  b y   R e n a m i n g 
 *********************************************************)
  
rsch_actions_def "rsch_actions (akt) ==                      
            case akt of   
           Next    =>  None |          
           S_msg(m) => None |         
            R_msg(m) => None |         
           S_pkt(packet) => None |    
            R_pkt(packet) => None |    
            S_ack(b) => Some(S(b)) |   
            R_ack(b) => Some(R(b))"

srch_actions_def "srch_actions (akt) ==                      
            case akt of   
            Next    =>  None |          
           S_msg(m) => None |         
            R_msg(m) => None |         
           S_pkt(p) => Some(S(p)) |   
            R_pkt(p) => Some(R(p)) |   
            S_ack(b) => None |         
            R_ack(b) => None"


end  


















