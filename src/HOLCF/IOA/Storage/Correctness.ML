(*  Title:      HOL/IOA/example/Correctness.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997  TU Muenchen

Correctness Proof
*)


Addsimps [split_paired_All];
Delsimps [split_paired_Ex];


(* Idea: instead of impl_con_lemma do not rewrite impl_ioa, but derive
         simple lemmas asig_of impl_ioa = impl_sig, trans_of impl_ioa = impl_trans 
   Idea: ?ex. move .. should be generally replaced by a step via a subst tac if desired,
         as this can be done globally *)

Goal 
      "is_simulation sim_relation impl_ioa spec_ioa";
by (simp_tac (simpset() addsimps [is_simulation_def]) 1);
by (rtac conjI 1);
(* --------------  start states ----------------- *)
by (SELECT_GOAL (safe_tac set_cs) 1);
by (res_inst_tac [("x","({},False)")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [sim_relation_def,starts_of_def,
        Spec.ioa_def,Impl.ioa_def]) 1);
(* ---------------- main-part ------------------- *)

by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
ren "k b used c k' b' a" 1;
by (induct_tac "a" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [sim_relation_def,
      Impl.ioa_def,Impl.trans_def,trans_of_def])));
by (safe_tac set_cs);
(* NEW *)
by (res_inst_tac [("x","(used,True)")] exI 1);
by (Asm_full_simp_tac 1);
by (rtac transition_is_ex 1);
by (simp_tac (simpset() addsimps [
      Spec.ioa_def,Spec.trans_def,trans_of_def])1);
(* LOC *)
by (res_inst_tac [("x","(used Un {k},False)")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [less_SucI]) 1);
by (rtac transition_is_ex 1);
by (simp_tac (simpset() addsimps [
      Spec.ioa_def,Spec.trans_def,trans_of_def])1);
by (Fast_tac 1);
(* FREE *)
by (res_inst_tac [("x","(used - {nat},c)")] exI 1);
by (Asm_full_simp_tac 1);
by (SELECT_GOAL (safe_tac set_cs) 1);
by Auto_tac;
by (rtac transition_is_ex 1);
by (simp_tac (simpset() addsimps [
      Spec.ioa_def,Spec.trans_def,trans_of_def])1);
qed"issimulation";



Goalw [ioa_implements_def] 
"impl_ioa =<| spec_ioa";
by (rtac conjI 1);
by (simp_tac (simpset() addsimps [Impl.sig_def,Spec.sig_def,
    Impl.ioa_def,Spec.ioa_def, asig_outputs_def,asig_of_def,
    asig_inputs_def]) 1);
by (rtac trace_inclusion_for_simulations 1);
by (simp_tac (simpset() addsimps [Impl.sig_def,Spec.sig_def,
    Impl.ioa_def,Spec.ioa_def, externals_def,asig_outputs_def,asig_of_def,
    asig_inputs_def]) 1);
by (rtac issimulation 1);
qed"implementation";

