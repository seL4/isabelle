(*  Title:      HOL/HOLCF/IOA/NTP/Abschannel.thy
    Author:     Olaf Müller
*)

section {* The (faulty) transmission channel (both directions) *}

theory Abschannel
imports IOA Action
begin

datatype 'a abs_action = S 'a | R 'a

definition
  ch_asig :: "'a abs_action signature" where
  "ch_asig = (UN b. {S(b)}, UN b. {R(b)}, {})"

definition
  ch_trans :: "('a abs_action, 'a multiset)transition set" where
  "ch_trans =
    {tr. let s = fst(tr);
             t = snd(snd(tr))
         in
         case fst(snd(tr))
           of S(b) => t = addm s b |
              R(b) => count s b ~= 0 & t = delm s b}"

definition
  ch_ioa :: "('a abs_action, 'a multiset)ioa" where
  "ch_ioa = (ch_asig, {{|}}, ch_trans,{},{})"

definition
  rsch_actions :: "'m action => bool abs_action option" where
  "rsch_actions (akt) =
          (case akt of
           S_msg(m) => None |
            R_msg(m) => None |
           S_pkt(packet) => None |
            R_pkt(packet) => None |
            S_ack(b) => Some(S(b)) |
            R_ack(b) => Some(R(b)) |
           C_m_s =>  None  |
           C_m_r =>  None |
           C_r_s =>  None  |
           C_r_r(m) => None)"

definition
  srch_actions :: "'m action =>(bool * 'm) abs_action option" where
  "srch_actions (akt) =
          (case akt of
           S_msg(m) => None |
            R_msg(m) => None |
           S_pkt(p) => Some(S(p)) |
            R_pkt(p) => Some(R(p)) |
            S_ack(b) => None |
            R_ack(b) => None |
           C_m_s => None |
           C_m_r => None |
           C_r_s => None |
           C_r_r(m) => None)"

definition
  srch_ioa :: "('m action, 'm packet multiset)ioa" where
  "srch_ioa = rename ch_ioa srch_actions"

definition
  rsch_ioa :: "('m action, bool multiset)ioa" where
  "rsch_ioa = rename ch_ioa rsch_actions"

definition
  srch_asig :: "'m action signature" where
  "srch_asig = asig_of(srch_ioa)"

definition
  rsch_asig :: "'m action signature" where
  "rsch_asig = asig_of(rsch_ioa)"

definition
  srch_wfair :: "('m action)set set" where
  "srch_wfair = wfair_of(srch_ioa)"
definition
  srch_sfair :: "('m action)set set" where
  "srch_sfair = sfair_of(srch_ioa)"
definition
  rsch_sfair :: "('m action)set set" where
  "rsch_sfair = sfair_of(rsch_ioa)"
definition
  rsch_wfair :: "('m action)set set" where
  "rsch_wfair = wfair_of(rsch_ioa)"

definition
  srch_trans :: "('m action, 'm packet multiset)transition set" where
  "srch_trans = trans_of(srch_ioa)"
definition
  rsch_trans :: "('m action, bool multiset)transition set" where
  "rsch_trans = trans_of(rsch_ioa)"


lemmas unfold_renaming =
  srch_asig_def rsch_asig_def rsch_ioa_def srch_ioa_def ch_ioa_def
  ch_asig_def srch_actions_def rsch_actions_def rename_def rename_set_def asig_of_def
  actions_def srch_trans_def rsch_trans_def ch_trans_def starts_of_def
  trans_of_def asig_projections

lemma in_srch_asig: 
     "S_msg(m) ~: actions(srch_asig)        &     
       R_msg(m) ~: actions(srch_asig)        &     
       S_pkt(pkt) : actions(srch_asig)    &     
       R_pkt(pkt) : actions(srch_asig)    &     
       S_ack(b) ~: actions(srch_asig)     &     
       R_ack(b) ~: actions(srch_asig)     &     
       C_m_s ~: actions(srch_asig)           &     
       C_m_r ~: actions(srch_asig)           &     
       C_r_s ~: actions(srch_asig)  & C_r_r(m) ~: actions(srch_asig)"
  by (simp add: unfold_renaming)

lemma in_rsch_asig: 
      "S_msg(m) ~: actions(rsch_asig)         &  
       R_msg(m) ~: actions(rsch_asig)         &  
       S_pkt(pkt) ~: actions(rsch_asig)    &  
       R_pkt(pkt) ~: actions(rsch_asig)    &  
       S_ack(b) : actions(rsch_asig)       &  
       R_ack(b) : actions(rsch_asig)       &  
       C_m_s ~: actions(rsch_asig)            &  
       C_m_r ~: actions(rsch_asig)            &  
       C_r_s ~: actions(rsch_asig)            &  
       C_r_r(m) ~: actions(rsch_asig)"
  by (simp add: unfold_renaming)

lemma srch_ioa_thm: "srch_ioa =  
    (srch_asig, {{|}}, srch_trans,srch_wfair,srch_sfair)"
apply (simp (no_asm) add: srch_asig_def srch_trans_def asig_of_def trans_of_def wfair_of_def sfair_of_def srch_wfair_def srch_sfair_def)
apply (simp (no_asm) add: unfold_renaming)
done

lemma rsch_ioa_thm: "rsch_ioa =  
     (rsch_asig, {{|}}, rsch_trans,rsch_wfair,rsch_sfair)"
apply (simp (no_asm) add: rsch_asig_def rsch_trans_def asig_of_def trans_of_def wfair_of_def sfair_of_def rsch_wfair_def rsch_sfair_def)
apply (simp (no_asm) add: unfold_renaming)
done

end
