(*  Title:      HOL/IOA/NTP/Correctness.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

header {* The main correctness proof: Impl implements Spec *}

theory Correctness
imports Impl Spec
begin

constdefs
  hom :: "'m impl_state => 'm list"
  "hom(s) == rq(rec(s)) @ (if rbit(rec s) = sbit(sen s) then sq(sen s)
                           else tl(sq(sen s)))"

ML_setup {*
(* repeated from Traces.ML *)
change_claset (fn cs => cs delSWrapper "split_all_tac")
*}

lemmas hom_ioas = Spec.ioa_def Spec.trans_def sender_trans_def receiver_trans_def impl_ioas
  and impl_asigs = sender_asig_def receiver_asig_def srch_asig_def rsch_asig_def

declare split_paired_All [simp del]


text {*
  A lemma about restricting the action signature of the implementation
  to that of the specification.
*}

lemma externals_lemma: 
 "a:externals(asig_of(Automata.restrict impl_ioa (externals spec_sig))) =  
  (case a of                   
      S_msg(m) => True         
    | R_msg(m) => True         
    | S_pkt(pkt) => False   
    | R_pkt(pkt) => False   
    | S_ack(b) => False     
    | R_ack(b) => False     
    | C_m_s => False           
    | C_m_r => False           
    | C_r_s => False           
    | C_r_r(m) => False)"
 apply (simp (no_asm) add: externals_def restrict_def restrict_asig_def Spec.sig_def asig_projections)

  apply (induct_tac "a")
  apply (simp_all (no_asm) add: actions_def asig_projections)
  txt {* 2 *}
  apply (simp (no_asm) add: impl_ioas)
  apply (simp (no_asm) add: impl_asigs)
  apply (simp (no_asm) add: asig_of_par asig_comp_def asig_projections)
  apply (simp (no_asm) add: "transitions" unfold_renaming)
  txt {* 1 *}
  apply (simp (no_asm) add: impl_ioas)
  apply (simp (no_asm) add: impl_asigs)
  apply (simp (no_asm) add: asig_of_par asig_comp_def asig_projections)
  done

lemmas sels = sbit_def sq_def ssending_def rbit_def rq_def rsending_def


text {* Proof of correctness *}
lemma ntp_correct:
  "is_weak_ref_map hom (Automata.restrict impl_ioa (externals spec_sig)) spec_ioa"
apply (unfold Spec.ioa_def is_weak_ref_map_def)
apply (simp (no_asm) cong del: if_weak_cong split del: split_if add: Correctness.hom_def
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

apply (case_tac "m = hd (sq (sen (s)))")

apply force

apply simp
apply (blast dest!: add_leD1 [THEN leD])

apply simp
done

end
