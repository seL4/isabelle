(*  Title:      HOL/UNITY/TimerArray.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A trivial example of reasoning about an array of processes
*)

theory TimerArray = UNITY_Main:

types 'a state = "nat * 'a"   (*second component allows new variables*)

constdefs
  count  :: "'a state => nat"
    "count s == fst s"
  
  decr  :: "('a state * 'a state) set"
    "decr == UN n uu. {((Suc n, uu), (n,uu))}"
  
  Timer :: "'a state program"
    "Timer == mk_program (UNIV, {decr}, UNIV)"


declare Timer_def [THEN def_prg_Init, simp]

declare count_def [simp] decr_def [simp]

(*Demonstrates induction, but not used in the following proof*)
lemma Timer_leadsTo_zero: "Timer : UNIV leadsTo {s. count s = 0}"
apply (rule_tac f = count in lessThan_induct, simp)
apply (case_tac "m")
 apply (force intro!: subset_imp_leadsTo)
apply (unfold Timer_def, ensures_tac "decr")
done

lemma Timer_preserves_snd [iff]: "Timer : preserves snd"
apply (rule preservesI)
apply (unfold Timer_def, constrains)
done


declare PLam_stable [simp]

lemma TimerArray_leadsTo_zero:
     "finite I  
      ==> (plam i: I. Timer) : UNIV leadsTo {(s,uu). ALL i:I. s i = 0}"
apply (erule_tac A'1 = "%i. lift_set i ({0} <*> UNIV)" 
       in finite_stable_completion [THEN leadsTo_weaken])
apply auto
(*Safety property, already reduced to the single Timer case*)
 prefer 2
 apply (simp add: Timer_def, constrains) 
(*Progress property for the array of Timers*)
apply (rule_tac f = "sub i o fst" in lessThan_induct)
apply (case_tac "m")
(*Annoying need to massage the conditions to have the form (... <*> UNIV)*)
apply (auto intro: subset_imp_leadsTo 
        simp add: insert_absorb 
                  lift_set_Un_distrib [symmetric] lessThan_Suc [symmetric] 
               Times_Un_distrib1 [symmetric] Times_Diff_distrib1 [symmetric])
apply (rename_tac "n")
apply (rule PLam_leadsTo_Basis)
apply (auto simp add: lessThan_Suc [symmetric])
apply (unfold Timer_def, constrains) 
apply (rule_tac act = decr in transientI, auto)
done

end
