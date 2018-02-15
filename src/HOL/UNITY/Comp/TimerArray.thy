(*  Title:      HOL/UNITY/Comp/TimerArray.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A trivial example of reasoning about an array of processes
*)

theory TimerArray imports "../UNITY_Main" begin

type_synonym 'a state = "nat * 'a"   (*second component allows new variables*)

definition count :: "'a state => nat"
  where "count s = fst s"
  
definition decr  :: "('a state * 'a state) set"
  where "decr = (UN n uu. {((Suc n, uu), (n,uu))})"
  
definition Timer :: "'a state program"
  where "Timer = mk_total_program (UNIV, {decr}, UNIV)"


declare Timer_def [THEN def_prg_Init, simp]

declare count_def [simp] decr_def [simp]

(*Demonstrates induction, but not used in the following proof*)
lemma Timer_leadsTo_zero: "Timer \<in> UNIV leadsTo {s. count s = 0}"
apply (rule_tac f = count in lessThan_induct, simp)
apply (case_tac "m")
 apply (force intro!: subset_imp_leadsTo)
apply (unfold Timer_def, ensures_tac "decr")
done

lemma Timer_preserves_snd [iff]: "Timer \<in> preserves snd"
apply (rule preservesI)
apply (unfold Timer_def, safety)
done


declare PLam_stable [simp]

lemma TimerArray_leadsTo_zero:
     "finite I  
      \<Longrightarrow> (plam i: I. Timer) \<in> UNIV leadsTo {(s,uu). \<forall>i\<in>I. s i = 0}"
apply (erule_tac A'1 = "\<lambda>i. lift_set i ({0} \<times> UNIV)" 
       in finite_stable_completion [THEN leadsTo_weaken])
apply auto
(*Safety property, already reduced to the single Timer case*)
 prefer 2
 apply (simp add: Timer_def, safety) 
(*Progress property for the array of Timers*)
apply (rule_tac f = "sub i o fst" in lessThan_induct)
apply (case_tac "m")
(*Annoying need to massage the conditions to have the form (... \<times> UNIV)*)
apply (auto intro: subset_imp_leadsTo 
        simp add: insert_absorb 
                  lift_set_Un_distrib [symmetric] lessThan_Suc [symmetric] 
               Times_Un_distrib1 [symmetric] Times_Diff_distrib1 [symmetric])
apply (rename_tac "n")
apply (rule PLam_leadsTo_Basis)
apply (auto simp add: lessThan_Suc [symmetric])
apply (unfold Timer_def mk_total_program_def, safety) 
apply (rule_tac act = decr in totalize_transientI, auto)
done

end
