(*  Title:      HOL/IOA/NTP/Correctness.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The main correctness proof: Impl implements Spec.
*)

(* repeated from Traces.ML *)
claset_ref() := claset() delSWrapper "split_all_tac";


val hom_ioas = [Spec.ioa_def, Spec.trans_def,
                Sender.sender_trans_def,Receiver.receiver_trans_def]
               @ impl_ioas;

val impl_asigs = [Sender.sender_asig_def,Receiver.receiver_asig_def,
                  Abschannel.srch_asig_def,Abschannel.rsch_asig_def];

(* Two simpsets: - simpset() is basic, ss' unfolds hom_ioas *)

Delsimps [split_paired_All];

val ss' = (simpset() addsimps hom_ioas);


(* A lemma about restricting the action signature of the implementation
 * to that of the specification.
 ****************************)
Goal
 "a:externals(asig_of(Automata.restrict impl_ioa (externals spec_sig))) = \
\ (case a of                  \
\     S_msg(m) => True        \
\   | R_msg(m) => True        \
\   | S_pkt(pkt) => False  \
\   | R_pkt(pkt) => False  \
\   | S_ack(b) => False    \
\   | R_ack(b) => False    \
\   | C_m_s => False          \
\   | C_m_r => False          \
\   | C_r_s => False          \
\   | C_r_r(m) => False)";
 by (simp_tac (simpset() addsimps ([externals_def, restrict_def,
                            restrict_asig_def, Spec.sig_def]
                            @asig_projections)) 1);

  by (induct_tac "a" 1);
  by (ALLGOALS(simp_tac (simpset() addsimps [actions_def]@asig_projections)));
 (* 2 *)
  by (simp_tac (simpset() addsimps impl_ioas) 1);
  by (simp_tac (simpset() addsimps impl_asigs) 1);
  by (simp_tac (simpset() addsimps 
             [asig_of_par, asig_comp_def]@asig_projections) 1);
  by (simp_tac rename_ss 1); 
 (* 1 *)
  by (simp_tac (simpset() addsimps impl_ioas) 1);
  by (simp_tac (simpset() addsimps impl_asigs) 1);
  by (simp_tac (simpset() addsimps 
             [asig_of_par, asig_comp_def]@asig_projections) 1);
qed "externals_lemma"; 


val sels = [Sender.sbit_def, Sender.sq_def, Sender.ssending_def,
            Receiver.rbit_def, Receiver.rq_def, Receiver.rsending_def];


(* Proof of correctness *)
Goalw [Spec.ioa_def, is_weak_ref_map_def]
  "is_weak_ref_map hom (Automata.restrict impl_ioa (externals spec_sig))  \
\                  spec_ioa";
by (simp_tac (simpset() delcongs [if_weak_cong] delsplits [split_if] 
 	                addsimps [Correctness.hom_def, cancel_restrict, 
				  externals_lemma]) 1);
by (rtac conjI 1);
 by (simp_tac ss' 1);
 by (asm_simp_tac (simpset() addsimps sels) 1);
by (REPEAT(rtac allI 1));
by (rtac imp_conj_lemma 1);   (* from lemmas.ML *)

by (induct_tac "a"  1);
by (ALLGOALS (asm_simp_tac ss'));
by (ftac inv4 1);
by (Force_tac 1);

by (ftac inv4 1);
by (ftac inv2 1);
by (etac disjE 1);
by (Asm_simp_tac 1);
by (Force_tac 1);

by (ftac inv2 1);
by (etac disjE 1);

by (ftac inv3 1);
by (case_tac "sq(sen(s))=[]" 1);

by (asm_full_simp_tac ss' 1);
by (blast_tac (claset() addSDs [add_leD1 RS leD]) 1);

by (case_tac "m = hd(sq(sen(s)))" 1);

by (Force_tac 1);

by (Asm_full_simp_tac 1);
by (blast_tac (claset() addSDs [add_leD1 RS leD]) 1);

by (Asm_full_simp_tac 1);
qed"ntp_correct";
