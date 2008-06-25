(*  Title:      HOL/IOA/example/Correctness.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Correctness Proof *}

theory Correctness
imports SimCorrectness Spec Impl
begin

defaultsort type

definition
  sim_relation :: "((nat * bool) * (nat set * bool)) set" where
  "sim_relation = {qua. let c = fst qua; a = snd qua ;
                            k = fst c;   b = snd c;
                            used = fst a; c = snd a
                        in
                        (! l:used. l < k) & b=c}"

declare split_paired_All [simp]
declare split_paired_Ex [simp del]


(* Idea: instead of impl_con_lemma do not rewrite impl_ioa, but derive
         simple lemmas asig_of impl_ioa = impl_sig, trans_of impl_ioa = impl_trans
   Idea: ?ex. move .. should be generally replaced by a step via a subst tac if desired,
         as this can be done globally *)

lemma issimulation:
      "is_simulation sim_relation impl_ioa spec_ioa"
apply (simp (no_asm) add: is_simulation_def)
apply (rule conjI)
txt {* start states *}
apply (auto)[1]
apply (rule_tac x = " ({},False) " in exI)
apply (simp add: sim_relation_def starts_of_def spec_ioa_def impl_ioa_def)
txt {* main-part *}
apply (rule allI)+
apply (rule imp_conj_lemma)
apply (rename_tac k b used c k' b' a)
apply (induct_tac "a")
apply (simp_all (no_asm) add: sim_relation_def impl_ioa_def impl_trans_def trans_of_def)
apply auto
txt {* NEW *}
apply (rule_tac x = "(used,True)" in exI)
apply simp
apply (rule transition_is_ex)
apply (simp (no_asm) add: spec_ioa_def spec_trans_def trans_of_def)
txt {* LOC *}
apply (rule_tac x = " (used Un {k},False) " in exI)
apply (simp add: less_SucI)
apply (rule transition_is_ex)
apply (simp (no_asm) add: spec_ioa_def spec_trans_def trans_of_def)
apply fast
txt {* FREE *}
apply (rule_tac x = " (used - {nat},c) " in exI)
apply simp
apply (rule transition_is_ex)
apply (simp (no_asm) add: spec_ioa_def spec_trans_def trans_of_def)
done


lemma implementation:
"impl_ioa =<| spec_ioa"
apply (unfold ioa_implements_def)
apply (rule conjI)
apply (simp (no_asm) add: impl_sig_def spec_sig_def impl_ioa_def spec_ioa_def
  asig_outputs_def asig_of_def asig_inputs_def)
apply (rule trace_inclusion_for_simulations)
apply (simp (no_asm) add: impl_sig_def spec_sig_def impl_ioa_def spec_ioa_def
  externals_def asig_outputs_def asig_of_def asig_inputs_def)
apply (rule issimulation)
done

end
