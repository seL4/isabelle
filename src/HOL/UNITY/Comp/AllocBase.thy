(*  Title:      HOL/UNITY/Comp/AllocBase.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

section\<open>Common Declarations for Chandy and Charpentier's Allocator\<close>

theory AllocBase imports "../UNITY_Main" "~~/src/HOL/Library/Multiset_Order" begin

consts Nclients :: nat  (*Number of clients*)

axiomatization NbT :: nat  (*Number of tokens in system*)
  where NbT_pos: "0 < NbT"

abbreviation (input) tokens :: "nat list \<Rightarrow> nat"
where
  "tokens \<equiv> listsum"

abbreviation (input)
  "bag_of \<equiv> mset"

lemma setsum_fun_mono:
  fixes f :: "nat \<Rightarrow> nat"
  shows "(\<And>i. i < n \<Longrightarrow> f i \<le> g i) \<Longrightarrow> setsum f {..<n} \<le> setsum g {..<n}"
  by (induct n) (auto simp add: lessThan_Suc add_le_mono)

lemma tokens_mono_prefix: "xs \<le> ys \<Longrightarrow> tokens xs \<le> tokens ys"
  by (induct ys arbitrary: xs) (auto simp add: prefix_Cons)

lemma mono_tokens: "mono tokens"
  using tokens_mono_prefix by (rule monoI)


(** bag_of **)

lemma bag_of_append [simp]: "bag_of (l@l') = bag_of l + bag_of l'"
  by (fact mset_append)

lemma subseteq_le_multiset: "(A :: 'a::order multiset) \<le> A + B"
unfolding less_eq_multiset_def apply (cases B; simp)
apply (rule union_le_mono2[of "{#}" "_ + {#_#}" A, simplified])
apply (simp add: less_multiset\<^sub>H\<^sub>O)
done

lemma mono_bag_of: "mono (bag_of :: 'a list => ('a::order) multiset)"
apply (rule monoI)
apply (unfold prefix_def)
apply (erule genPrefix.induct, simp_all add: add_right_mono)
apply (erule order_trans)
apply (simp add: subseteq_le_multiset)
done

(** setsum **)

declare setsum.cong [cong]

lemma bag_of_sublist_lemma:
     "(\<Sum>i\<in> A Int lessThan k. {#if i<k then f i else g i#}) =  
      (\<Sum>i\<in> A Int lessThan k. {#f i#})"
by (rule setsum.cong, auto)

lemma bag_of_sublist:
     "bag_of (sublist l A) =  
      (\<Sum>i\<in> A Int lessThan (length l). {# l!i #})"
apply (rule_tac xs = l in rev_induct, simp)
apply (simp add: sublist_append Int_insert_right lessThan_Suc nth_append 
                 bag_of_sublist_lemma ac_simps)
done


lemma bag_of_sublist_Un_Int:
     "bag_of (sublist l (A Un B)) + bag_of (sublist l (A Int B)) =  
      bag_of (sublist l A) + bag_of (sublist l B)"
apply (subgoal_tac "A Int B Int {..<length l} =
                    (A Int {..<length l}) Int (B Int {..<length l}) ")
apply (simp add: bag_of_sublist Int_Un_distrib2 setsum.union_inter, blast)
done

lemma bag_of_sublist_Un_disjoint:
     "A Int B = {}  
      ==> bag_of (sublist l (A Un B)) =  
          bag_of (sublist l A) + bag_of (sublist l B)"
by (simp add: bag_of_sublist_Un_Int [symmetric])

lemma bag_of_sublist_UN_disjoint [rule_format]:
     "[| finite I; ALL i:I. ALL j:I. i~=j --> A i Int A j = {} |]  
      ==> bag_of (sublist l (UNION I A)) =   
          (\<Sum>i\<in>I. bag_of (sublist l (A i)))"
apply (auto simp add: bag_of_sublist)
unfolding UN_simps [symmetric]
apply (subst setsum.UNION_disjoint)
apply auto
done

end
