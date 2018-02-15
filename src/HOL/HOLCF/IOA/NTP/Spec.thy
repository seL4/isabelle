(*  Title:      HOL/HOLCF/IOA/NTP/Spec.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

section \<open>The specification of reliable transmission\<close>

theory Spec
imports IOA.IOA Action
begin

definition
  spec_sig :: "'m action signature" where
  sig_def: "spec_sig = (\<Union>m.{S_msg(m)}, 
                        \<Union>m.{R_msg(m)}, 
                        {})"

definition
  spec_trans :: "('m action, 'm list)transition set" where
  trans_def: "spec_trans =
   {tr. let s = fst(tr);                            
            t = snd(snd(tr))                        
        in                                          
        case fst(snd(tr))                           
        of                                          
        S_msg(m) \<Rightarrow> t = s@[m]  |                    
        R_msg(m) \<Rightarrow> s = (m#t)  |                    
        S_pkt(pkt) \<Rightarrow> False |                    
        R_pkt(pkt) \<Rightarrow> False |                    
        S_ack(b) \<Rightarrow> False |                      
        R_ack(b) \<Rightarrow> False |                      
        C_m_s \<Rightarrow> False |                            
        C_m_r \<Rightarrow> False |                            
        C_r_s \<Rightarrow> False |                            
        C_r_r(m) \<Rightarrow> False}"

definition
  spec_ioa :: "('m action, 'm list)ioa" where
  ioa_def: "spec_ioa = (spec_sig, {[]}, spec_trans,{},{})"

end
