(*  Title:      HOL/UNITY/Counterc
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

A family of similar counters, version with a full use of "compatibility "

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

header{*A Family of Similar Counters: Version with Compatibility*}

theory Counterc =  UNITY_Main:

typedecl state
arities state :: type

consts
  C :: "state=>int"
  c :: "state=>nat=>int"

consts  
  sum  :: "[nat,state]=>int"
  sumj :: "[nat, nat, state]=>int"

primrec (* sum I s = sigma_{i<I}. c s i *)
  "sum 0 s = 0"
  "sum (Suc i) s = (c s) i + sum i s"

primrec
  "sumj 0 i s = 0"
  "sumj (Suc n) i s = (if n=i then sum n s else (c s) n + sumj n i s)"
  
types command = "(state*state)set"

constdefs
  a :: "nat=>command"
 "a i == {(s, s'). (c s') i = (c s) i + 1 & (C s') = (C s) + 1}"
 
  Component :: "nat => state program"
  "Component i == mk_total_program({s. C s = 0 & (c s) i = 0},
				   {a i},
 	                           \<Union>G \<in> preserves (%s. (c s) i). Acts G)"


declare Component_def [THEN def_prg_Init, simp]
declare Component_def [THEN def_prg_AllowedActs, simp]
declare a_def [THEN def_act_simp, simp]

(* Theorems about sum and sumj *)
lemma sum_sumj_eq1 [rule_format]: "\<forall>i. I<i--> (sum I s = sumj I i s)"
by (induct_tac "I", auto)

lemma sum_sumj_eq2 [rule_format]: "i<I --> sum I s  = c s i + sumj I i s"
apply (induct_tac "I")
apply (auto simp add: linorder_neq_iff sum_sumj_eq1)
done

lemma sum_ext [rule_format]:
     "(\<forall>i. i<I --> c s' i = c s i) --> (sum I s' = sum I s)"
by (induct_tac "I", auto)

lemma sumj_ext [rule_format]:
     "(\<forall>j. j<I & j\<noteq>i --> c s' j =  c s j) --> (sumj I i s' = sumj I i s)"
apply (induct_tac "I", safe)
apply (auto intro!: sum_ext)
done


lemma sum0 [rule_format]: "(\<forall>i. i<I --> c s i = 0) -->  sum I s = 0"
by (induct_tac "I", auto)


(* Safety properties for Components *)

lemma Component_ok_iff:
     "(Component i ok G) =  
      (G \<in> preserves (%s. c s i) & Component i \<in> Allowed G)"
apply (auto simp add: ok_iff_Allowed Component_def [THEN def_total_prg_Allowed])
done
declare Component_ok_iff [iff]
declare OK_iff_ok [iff]
declare preserves_def [simp]


lemma p2: "Component i \<in> stable {s. C s = (c s) i + k}"
by (simp add: Component_def, constrains)

lemma p3:
     "[| OK I Component; i\<in>I |]   
      ==> Component i \<in> stable {s. \<forall>j\<in>I. j\<noteq>i --> c s j = c k j}"
apply simp
apply (unfold Component_def mk_total_program_def)
apply (simp (no_asm_use) add: stable_def constrains_def)
apply blast
done


lemma p2_p3_lemma1: 
     "[| OK {i. i<I} Component; i<I |] ==>  
      \<forall>k. Component i \<in> stable ({s. C s = c s i + sumj I i k} Int  
	 	                {s. \<forall>j\<in>{i. i<I}. j\<noteq>i --> c s j = c k j})"
by (blast intro: stable_Int [OF p2 p3])

lemma p2_p3_lemma2:
     "(\<forall>k. F \<in> stable ({s. C s = (c s) i + sumj I i k} Int  
                        {s. \<forall>j\<in>{i. i<I}. j\<noteq>i --> c s j = c k j}))   
      ==> (F \<in> stable {s. C s = c s i + sumj I i s})"
apply (simp add: constrains_def stable_def)
apply (force intro!: sumj_ext)
done


lemma p2_p3:
     "[| OK {i. i<I} Component; i<I |]  
      ==> Component i \<in> stable {s. C s = c s i + sumj I i s}"
by (blast intro: p2_p3_lemma1 [THEN p2_p3_lemma2])


(* Compositional correctness *)
lemma safety: 
     "[| 0<I; OK {i. i<I} Component |]   
      ==> (\<Squnion>i\<in>{i. i<I}. (Component i)) \<in> invariant {s. C s = sum I s}"
apply (simp (no_asm) add: invariant_def JN_stable sum_sumj_eq2)
apply (auto intro!: sum0 p2_p3)
done

end  
