(*  Title:      HOL/IOA/NTP/Correctness.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The main correctness proof: Impl implements Spec
*)



val hom_ioas = [Spec.ioa_def, Spec.trans_def,
                Sender.sender_trans_def,Receiver.receiver_trans_def]
               @ impl_ioas;

val impl_asigs = [Sender.sender_asig_def,Receiver.receiver_asig_def,
                  Abschannel.srch_asig_def,Abschannel.rsch_asig_def];

(* Two simpsets: - !simpset is basic, ss' unfolds hom_ioas *)

Delsimps [split_paired_All];

val ss' = (!simpset addsimps hom_ioas);


(* A lemma about restricting the action signature of the implementation
 * to that of the specification.
 ****************************)
goal Correctness.thy
 "a:externals(asig_of(restrict impl_ioa (externals spec_sig))) = \
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
 by (simp_tac (!simpset addsimps ([externals_def, restrict_def,
                            restrict_asig_def, Spec.sig_def]
                            @asig_projections)) 1);

  by (Action.action.induct_tac "a" 1);
  by (ALLGOALS(simp_tac (!simpset addsimps [actions_def]@asig_projections)));
 (* 2 *)
  by (simp_tac (!simpset addsimps impl_ioas) 1);
  by (simp_tac (!simpset addsimps impl_asigs) 1);
  by (simp_tac (!simpset addsimps 
             [asig_of_par, asig_comp_def]@asig_projections) 1);
  by (simp_tac rename_ss 1); 
 (* 1 *)
  by (simp_tac (!simpset addsimps impl_ioas) 1);
  by (simp_tac (!simpset addsimps impl_asigs) 1);
  by (simp_tac (!simpset addsimps 
             [asig_of_par, asig_comp_def]@asig_projections) 1);
qed "externals_lemma"; 


val sels = [Sender.sbit_def, Sender.sq_def, Sender.ssending_def,
            Receiver.rbit_def, Receiver.rq_def, Receiver.rsending_def];



(* Proof of correctness *)
goalw Correctness.thy [Spec.ioa_def, is_weak_ref_map_def]
  "is_weak_ref_map hom (restrict impl_ioa (externals spec_sig)) spec_ioa";
by (simp_tac (!simpset addsimps 
    [Correctness.hom_def, cancel_restrict, externals_lemma]) 1);
by (rtac conjI 1);
by (simp_tac ss' 1);
by (asm_simp_tac (!simpset addsimps sels) 1);
by (REPEAT(rtac allI 1));
by (rtac imp_conj_lemma 1);   (* from lemmas.ML *)

by (Action.action.induct_tac "a"  1);
by (asm_simp_tac (ss' setloop (split_tac [expand_if])) 1);
by (forward_tac [inv4] 1);
by (fast_tac (!claset addss (!simpset addsimps [neq_Nil_conv])) 1);
by (simp_tac ss' 1);
by (simp_tac ss' 1);
by (simp_tac ss' 1);
by (simp_tac ss' 1);
by (simp_tac ss' 1);
by (simp_tac ss' 1);
by (simp_tac ss' 1);

by (asm_simp_tac ss' 1);
by (forward_tac [inv4] 1);
by (forward_tac [inv2] 1);
by (etac disjE 1);
by (Asm_simp_tac 1);
by (fast_tac (!claset addss (!simpset addsimps [neq_Nil_conv])) 1);

by (asm_simp_tac ss' 1);
by (forward_tac [inv2] 1);
by (etac disjE 1);

by (forward_tac [inv3] 1);
by (case_tac "sq(sen(s))=[]" 1);

by (asm_full_simp_tac ss' 1);
by (fast_tac (!claset addSDs [add_leD1 RS leD]) 1);

by (case_tac "m = hd(sq(sen(s)))" 1);

by (fast_tac (!claset addss (!simpset addsimps [neq_Nil_conv])) 1);

by (Asm_full_simp_tac 1);
by (fast_tac (!claset addSDs [add_leD1 RS leD]) 1);

by (Asm_full_simp_tac 1);
qed"ntp_correct";
