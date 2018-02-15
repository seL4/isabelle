(*  Title:      HOL/HOLCF/IOA/NTP/Correctness.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

section \<open>The main correctness proof: Impl implements Spec\<close>

theory Correctness
imports Impl Spec
begin

definition
  hom :: "'m impl_state => 'm list" where
  "hom s = rq(rec(s)) @ (if rbit(rec s) = sbit(sen s) then sq(sen s)
                         else tl(sq(sen s)))"

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

lemmas hom_ioas = Spec.ioa_def Spec.trans_def sender_trans_def receiver_trans_def impl_ioas
  and impl_asigs = sender_asig_def receiver_asig_def srch_asig_def rsch_asig_def

declare split_paired_All [simp del]


text \<open>
  A lemma about restricting the action signature of the implementation
  to that of the specification.
\<close>

lemma externals_lemma: 
 "a\<in>externals(asig_of(Automata.restrict impl_ioa (externals spec_sig))) =  
  (case a of                   
      S_msg(m) \<Rightarrow> True         
    | R_msg(m) \<Rightarrow> True         
    | S_pkt(pkt) \<Rightarrow> False   
    | R_pkt(pkt) \<Rightarrow> False   
    | S_ack(b) \<Rightarrow> False     
    | R_ack(b) \<Rightarrow> False     
    | C_m_s \<Rightarrow> False           
    | C_m_r \<Rightarrow> False           
    | C_r_s \<Rightarrow> False           
    | C_r_r(m) \<Rightarrow> False)"
 apply (simp (no_asm) add: externals_def restrict_def restrict_asig_def Spec.sig_def asig_projections)

  apply (induct_tac "a")
  apply (simp_all (no_asm) add: actions_def asig_projections)
  txt \<open>2\<close>
  apply (simp (no_asm) add: impl_ioas)
  apply (simp (no_asm) add: impl_asigs)
  apply (simp (no_asm) add: asig_of_par asig_comp_def asig_projections)
  apply (simp (no_asm) add: "transitions"(1) unfold_renaming)
  txt \<open>1\<close>
  apply (simp (no_asm) add: impl_ioas)
  apply (simp (no_asm) add: impl_asigs)
  apply (simp (no_asm) add: asig_of_par asig_comp_def asig_projections)
  done

lemmas sels = sbit_def sq_def ssending_def rbit_def rq_def rsending_def


text \<open>Proof of correctness\<close>
lemma ntp_correct:
  "is_weak_ref_map hom (Automata.restrict impl_ioa (externals spec_sig)) spec_ioa"
apply (unfold Spec.ioa_def is_weak_ref_map_def)
apply (simp (no_asm) cong del: if_weak_cong split del: if_split add: Correctness.hom_def
  cancel_restrict externals_lemma)
apply (rule conjI)
 apply (simp (no_asm) add: hom_ioas)
 apply (simp (no_asm_simp) add: sels)
apply (rule allI)+
apply (rule imp_conj_lemma)

apply (induct_tac "a")
apply (simp_all (no_asm_simp) add: hom_ioas)
apply (frule inv4)
apply force

apply (frule inv4)
apply (frule inv2)
apply (erule disjE)
apply (simp (no_asm_simp))
apply force

apply (frule inv2)
apply (erule disjE)

apply (frule inv3)
apply (case_tac "sq (sen (s))=[]")

apply (simp add: hom_ioas)
apply (blast dest!: add_leD1 [THEN leD])

apply (rename_tac m, case_tac "m = hd (sq (sen (s)))")

apply force

apply simp
apply (blast dest!: add_leD1 [THEN leD])

apply simp
done

end
