(*  Title:      HOL/UNITY/Comp/AllocBase.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

section\<open>Common Declarations for Chandy and Charpentier's Allocator\<close>

theory AllocBase imports "../UNITY_Main" "HOL-Library.Multiset_Order" begin

consts Nclients :: nat  (*Number of clients*)

axiomatization NbT :: nat  (*Number of tokens in system*)
  where NbT_pos: "0 < NbT"

abbreviation (input) tokens :: "nat list \<Rightarrow> nat"
where
  "tokens \<equiv> sum_list"

abbreviation (input)
  "bag_of \<equiv> mset"

lemma sum_fun_mono:
  fixes f :: "nat \<Rightarrow> nat"
  shows "(\<And>i. i < n \<Longrightarrow> f i \<le> g i) \<Longrightarrow> sum f {..<n} \<le> sum g {..<n}"
  by (induct n) (auto simp add: lessThan_Suc add_le_mono)

lemma tokens_mono_prefix: "xs \<le> ys \<Longrightarrow> tokens xs \<le> tokens ys"
  by (induct ys arbitrary: xs) (auto simp add: prefix_Cons)

lemma mono_tokens: "mono tokens"
  using tokens_mono_prefix by (rule monoI)


(** bag_of **)

lemma bag_of_append [simp]: "bag_of (l@l') = bag_of l + bag_of l'"
  by (fact mset_append)

lemma mono_bag_of: "mono (bag_of :: 'a list => ('a::order) multiset)"
apply (rule monoI)
apply (unfold prefix_def)
apply (erule genPrefix.induct, simp_all add: add_right_mono)
apply (erule order_trans)
apply simp
done

(** sum **)

declare sum.cong [cong]

lemma bag_of_nths_lemma:
     "(\<Sum>i\<in> A Int lessThan k. {#if i<k then f i else g i#}) =  
      (\<Sum>i\<in> A Int lessThan k. {#f i#})"
by (rule sum.cong, auto)

lemma bag_of_nths:
     "bag_of (nths l A) =  
      (\<Sum>i\<in> A Int lessThan (length l). {# l!i #})"
  by (rule_tac xs = l in rev_induct)
     (simp_all add: nths_append Int_insert_right lessThan_Suc nth_append 
                    bag_of_nths_lemma ac_simps)


lemma bag_of_nths_Un_Int:
     "bag_of (nths l (A Un B)) + bag_of (nths l (A Int B)) =  
      bag_of (nths l A) + bag_of (nths l B)"
apply (subgoal_tac "A Int B Int {..<length l} =
                    (A Int {..<length l}) Int (B Int {..<length l}) ")
apply (simp add: bag_of_nths Int_Un_distrib2 sum.union_inter, blast)
done

lemma bag_of_nths_Un_disjoint:
     "A Int B = {}  
      ==> bag_of (nths l (A Un B)) =  
          bag_of (nths l A) + bag_of (nths l B)"
by (simp add: bag_of_nths_Un_Int [symmetric])

lemma bag_of_nths_UN_disjoint [rule_format]:
     "[| finite I; \<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j \<longrightarrow> A i Int A j = {} |]  
      ==> bag_of (nths l (\<Union>(A ` I))) =   
          (\<Sum>i\<in>I. bag_of (nths l (A i)))"
apply (auto simp add: bag_of_nths)
unfolding UN_simps [symmetric]
apply (subst sum.UNION_disjoint)
apply auto
done

end
