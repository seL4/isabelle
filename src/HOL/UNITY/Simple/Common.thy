(*  Title:      HOL/UNITY/Common
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Common Meeting Time example from Misra (1994)

The state is identified with the one variable in existence.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.1 and 13.1.
*)

theory Common = UNITY_Main:

consts
  ftime :: "nat=>nat"
  gtime :: "nat=>nat"

axioms
  fmono: "m \<le> n ==> ftime m \<le> ftime n"
  gmono: "m \<le> n ==> gtime m \<le> gtime n"

  fasc:  "m \<le> ftime n"
  gasc:  "m \<le> gtime n"

constdefs
  common :: "nat set"
    "common == {n. ftime n = n & gtime n = n}"

  maxfg :: "nat => nat set"
    "maxfg m == {t. t \<le> max (ftime m) (gtime m)}"


(*Misra's property CMT4: t exceeds no common meeting time*)
lemma common_stable:
     "[| \<forall>m. F \<in> {m} Co (maxfg m); n \<in> common |]  
      ==> F \<in> Stable (atMost n)"
apply (drule_tac M = "{t. t \<le> n}" in Elimination_sing)
apply (simp add: atMost_def Stable_def common_def maxfg_def le_max_iff_disj)
apply (erule Constrains_weaken_R)
apply (blast intro: order_eq_refl fmono gmono le_trans)
done

lemma common_safety:
     "[| Init F \<subseteq> atMost n;   
         \<forall>m. F \<in> {m} Co (maxfg m); n \<in> common |]  
      ==> F \<in> Always (atMost n)"
by (simp add: AlwaysI common_stable)


(*** Some programs that implement the safety property above ***)

lemma "SKIP \<in> {m} co (maxfg m)"
by (simp add: constrains_def maxfg_def le_max_iff_disj fasc)

(*This one is  t := ftime t || t := gtime t*)
lemma "mk_program (UNIV, {range(%t.(t,ftime t)), range(%t.(t,gtime t))}, UNIV)
       \<in> {m} co (maxfg m)"
by (simp add: constrains_def maxfg_def le_max_iff_disj fasc)

(*This one is  t := max (ftime t) (gtime t)*)
lemma  "mk_program (UNIV, {range(%t.(t, max (ftime t) (gtime t)))}, UNIV)  
       \<in> {m} co (maxfg m)"
by (simp add: constrains_def maxfg_def max_def gasc)

(*This one is  t := t+1 if t <max (ftime t) (gtime t) *)
lemma  "mk_program   
          (UNIV, { {(t, Suc t) | t. t < max (ftime t) (gtime t)} }, UNIV)   
       \<in> {m} co (maxfg m)"
by (simp add: constrains_def maxfg_def max_def gasc)


(*It remans to prove that they satisfy CMT3': t does not decrease,
  and that CMT3' implies that t stops changing once common(t) holds.*)


(*** Progress under weak fairness ***)

declare atMost_Int_atLeast [simp]

lemma leadsTo_common_lemma:
     "[| \<forall>m. F \<in> {m} Co (maxfg m);  
         \<forall>m \<in> lessThan n. F \<in> {m} LeadsTo (greaterThan m);  
         n \<in> common |]   
      ==> F \<in> (atMost n) LeadsTo common"
apply (rule LeadsTo_weaken_R)
apply (rule_tac f = id and l = n in GreaterThan_bounded_induct)
apply (simp_all (no_asm_simp))
apply (rule_tac [2] subset_refl)
apply (blast dest: PSP_Stable2 intro: common_stable LeadsTo_weaken_R)
done

(*The "\<forall>m \<in> -common" form echoes CMT6.*)
lemma leadsTo_common:
     "[| \<forall>m. F \<in> {m} Co (maxfg m);  
         \<forall>m \<in> -common. F \<in> {m} LeadsTo (greaterThan m);  
         n \<in> common |]   
      ==> F \<in> (atMost (LEAST n. n \<in> common)) LeadsTo common"
apply (rule leadsTo_common_lemma)
apply (simp_all (no_asm_simp))
apply (erule_tac [2] LeastI)
apply (blast dest!: not_less_Least)
done

end
