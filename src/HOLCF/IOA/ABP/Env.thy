(*  Title:      HOLCF/IOA/ABP/Impl.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1995  TU Muenchen

The environment
*)

Env = IOA + Action +

types

'm env_state = "bool"
(*              give next bit to system  *)

consts

env_asig   :: 'm action signature
env_trans  :: ('m action, 'm env_state)transition set
env_ioa    :: ('m action, 'm env_state)ioa
next       :: 'm env_state => bool

defs

env_asig_def
  "env_asig == ({Next},                 
               UN m. {S_msg(m)},       
               {})"

env_trans_def "env_trans ==                                           
 {tr. let s = fst(tr);                                               
          t = snd(snd(tr))                                           
      in case fst(snd(tr))                                           
      of                                                             
      Next       => t=True |                                         
      S_msg(m)   => s=True & t=False |                               
      R_msg(m)   => False |                                          
      S_pkt(pkt) => False |                                          
      R_pkt(pkt) => False |                                          
      S_ack(b)   => False |                                          
      R_ack(b)   => False}"

env_ioa_def "env_ioa == 
 (env_asig, {True}, env_trans,{},{})"

end

