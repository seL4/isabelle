(*  Title:      HOL/UNITY/Simple/Deadlock.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Deadlock examples from section 5.6 of 
    Misra, "A Logic for Concurrent Programming", 1994
*)

theory Deadlock imports "../UNITY" begin

(*Trivial, two-process case*)
lemma "[| F \<in> (A \<inter> B) co A;  F \<in> (B \<inter> A) co B |] ==> F \<in> stable (A \<inter> B)"
  unfolding constrains_def stable_def by blast


(*a simplification step*)
lemma Collect_le_Int_equals:
     "(\<Inter>i \<in> atMost n. A(Suc i) \<inter> A i) = (\<Inter>i \<in> atMost (Suc n). A i)"
  by (induct n) (auto simp add: atMost_Suc)

(*Dual of the required property.  Converse inclusion fails.*)
lemma UN_Int_Compl_subset:
     "(\<Union>i \<in> lessThan n. A i) \<inter> (- A n) \<subseteq>   
      (\<Union>i \<in> lessThan n. (A i) \<inter> (- A (Suc i)))"
  by (induct n) (auto simp: lessThan_Suc)


(*Converse inclusion fails.*)
lemma INT_Un_Compl_subset:
     "(\<Inter>i \<in> lessThan n. -A i \<union> A (Suc i))  \<subseteq>  
      (\<Inter>i \<in> lessThan n. -A i) \<union> A n"
  by (induct n) (auto simp: lessThan_Suc)


(*Specialized rewriting*)
lemma INT_le_equals_Int_lemma:
     "A 0 \<inter> (-(A n) \<inter> (\<Inter>i \<in> lessThan n. -A i \<union> A (Suc i))) = {}"
by (blast intro: gr0I dest: INT_Un_Compl_subset [THEN subsetD])

(*Reverse direction makes it harder to invoke the ind hyp*)
lemma INT_le_equals_Int:
     "(\<Inter>i \<in> atMost n. A i) =  
      A 0 \<inter> (\<Inter>i \<in> lessThan n. -A i \<union> A(Suc i))"
  by (induct n)
    (simp_all add: Int_ac Int_Un_distrib Int_Un_distrib2
      INT_le_equals_Int_lemma lessThan_Suc atMost_Suc)

lemma INT_le_Suc_equals_Int:
     "(\<Inter>i \<in> atMost (Suc n). A i) =  
      A 0 \<inter> (\<Inter>i \<in> atMost n. -A i \<union> A(Suc i))"
by (simp add: lessThan_Suc_atMost INT_le_equals_Int)


(*The final deadlock example*)
lemma
  assumes zeroprem: "F \<in> (A 0 \<inter> A (Suc n)) co (A 0)"
      and allprem:
            "!!i. i \<in> atMost n ==> F \<in> (A(Suc i) \<inter> A i) co (-A i \<union> A(Suc i))"
  shows "F \<in> stable (\<Inter>i \<in> atMost (Suc n). A i)"
apply (unfold stable_def) 
apply (rule constrains_Int [THEN constrains_weaken])
   apply (rule zeroprem) 
  apply (rule constrains_INT) 
  apply (erule allprem)
 apply (simp add: Collect_le_Int_equals Int_assoc INT_absorb)
apply (simp add: INT_le_Suc_equals_Int)
done

end
