(*  Title:      HOL/IOA/NTP/Correctness.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The main correctness proof: Impl implements Spec
*)

open Impl;
open Spec;

val hom_ioas = [Spec.ioa_def, Spec.trans_def,
                Sender.sender_trans_def,Receiver.receiver_trans_def]
               @ impl_ioas;

Addsimps hom_ioas;

val impl_asigs = [Sender.sender_asig_def,Receiver.receiver_asig_def,
                   Abschannel.srch_asig_def,Abschannel.rsch_asig_def];

val ss =
  !simpset delsimps ([trans_of_def, starts_of_def, srch_asig_def,rsch_asig_def,
                      asig_of_def, actions_def, srch_trans_def, rsch_trans_def,
                      impl_def, srch_ioa_thm, rsch_ioa_thm, srch_ioa_def,
                      rsch_ioa_def, Sender.sender_trans_def,
                      Receiver.receiver_trans_def] @ set_lemmas);

val ss' = !simpset delsimps [trans_of_def, srch_asig_def, rsch_asig_def,
                             srch_trans_def, rsch_trans_def, asig_of_def,
                             actions_def]
                   addcongs [let_weak_cong];


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
 by(simp_tac (ss addcongs [if_weak_cong] 
                 addsimps ([externals_def, restrict_def,
                            restrict_asig_def, Spec.sig_def])) 1);

  by(Action.action.induct_tac "a" 1);
  by(ALLGOALS(simp_tac (ss addsimps (actions_def :: set_lemmas))));
 (* 2 *)
  by (simp_tac (ss addsimps impl_ioas) 1);
  by (simp_tac (ss addsimps impl_asigs) 1);
  by (simp_tac (ss addsimps ([asig_of_par, asig_comp_def])) 1);
  by (simp_tac (!simpset delsimps [srch_ioa_thm, rsch_ioa_thm, Let_def]) 1); 
 (* 1 *)
  by (simp_tac (ss addsimps impl_ioas) 1);
  by (simp_tac (ss addsimps impl_asigs) 1); 
  by (simp_tac (ss addsimps ([asig_of_par, asig_comp_def])) 1);
  by (simp_tac (!simpset delsimps [srch_ioa_thm, rsch_ioa_thm, Let_def]) 1); 
qed "externals_lemma"; 


val sels = [Sender.sbit_def, Sender.sq_def, Sender.ssending_def,
            Receiver.rbit_def, Receiver.rq_def, Receiver.rsending_def];

(* Proof of correctness *)
goalw Correctness.thy [Spec.ioa_def, Solve.is_weak_pmap_def]
  "is_weak_pmap hom (restrict impl_ioa (externals spec_sig)) spec_ioa";
by(simp_tac (ss delsimps [trans_def] addsimps 
             (Correctness.hom_def::[cancel_restrict,externals_lemma])) 1);
br conjI 1;
by(simp_tac (ss addsimps impl_ioas) 1);
br ballI 1;
bd CollectD 1;
by(asm_simp_tac (!simpset addsimps sels) 1);
by(REPEAT(rtac allI 1));
br imp_conj_lemma 1;   (* from lemmas.ML *)
by(Action.action.induct_tac "a"  1);
by(asm_simp_tac (ss' setloop (split_tac [expand_if])) 1);
by(forward_tac [inv4] 1);
by(asm_full_simp_tac (ss addsimps [imp_ex_equiv,neq_Nil_conv,ex_all_equiv]) 1);
by(simp_tac ss' 1);
by(simp_tac ss' 1);
by(simp_tac ss' 1);
by(simp_tac ss' 1);
by(simp_tac ss' 1);
by(simp_tac ss' 1);
by(simp_tac ss' 1);

by(asm_simp_tac ss' 1);
by(forward_tac [inv4] 1);
by(forward_tac [inv2] 1);
be disjE 1;
by(asm_simp_tac ss 1);
by(asm_full_simp_tac (ss addsimps [imp_ex_equiv,neq_Nil_conv,ex_all_equiv]) 1);

by(asm_simp_tac ss' 1);
by(forward_tac [inv2] 1);
be disjE 1;

by(forward_tac [inv3] 1);
by(case_tac "sq(sen(s))=[]" 1);

by(asm_full_simp_tac ss' 1);
by(fast_tac (HOL_cs addSDs [add_leD1 RS leD]) 1);

by(case_tac "m = hd(sq(sen(s)))" 1);

by(asm_full_simp_tac (ss addsimps 
                     [imp_ex_equiv,neq_Nil_conv,ex_all_equiv]) 1);

by(asm_full_simp_tac ss 1);
by(fast_tac (HOL_cs addSDs [add_leD1 RS leD]) 1);

by(asm_full_simp_tac ss 1);
result();
