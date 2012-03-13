(*  Title:      HOL/UNITY/Comp/AllocBase.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*Common Declarations for Chandy and Charpentier's Allocator*}

theory AllocBase imports "../UNITY_Main" begin

consts Nclients :: nat  (*Number of clients*)

axiomatization NbT :: nat  (*Number of tokens in system*)
  where NbT_pos: "0 < NbT"

(*This function merely sums the elements of a list*)
primrec tokens :: "nat list => nat" where
  "tokens [] = 0"
| "tokens (x#xs) = x + tokens xs"

abbreviation (input) "bag_of \<equiv> multiset_of"

lemma setsum_fun_mono [rule_format]:
     "!!f :: nat=>nat.  
      (ALL i. i<n --> f i <= g i) -->  
      setsum f (lessThan n) <= setsum g (lessThan n)"
apply (induct_tac "n")
apply (auto simp add: lessThan_Suc)
done

lemma tokens_mono_prefix: "xs <= ys ==> tokens xs <= tokens ys"
  by (induct ys arbitrary: xs) (auto simp add: prefix_Cons)

lemma mono_tokens: "mono tokens"
apply (unfold mono_def)
apply (blast intro: tokens_mono_prefix)
done


(** bag_of **)

lemma bag_of_append [simp]: "bag_of (l@l') = bag_of l + bag_of l'"
  by (induct l) (simp_all add: add_ac)

lemma mono_bag_of: "mono (bag_of :: 'a list => ('a::order) multiset)"
apply (rule monoI)
apply (unfold prefix_def)
apply (erule genPrefix.induct, auto)
apply (erule order_trans)
apply simp
done

(** setsum **)

declare setsum_cong [cong]

lemma bag_of_sublist_lemma:
     "(\<Sum>i\<in> A Int lessThan k. {#if i<k then f i else g i#}) =  
      (\<Sum>i\<in> A Int lessThan k. {#f i#})"
by (rule setsum_cong, auto)

lemma bag_of_sublist:
     "bag_of (sublist l A) =  
      (\<Sum>i\<in> A Int lessThan (length l). {# l!i #})"
apply (rule_tac xs = l in rev_induct, simp)
apply (simp add: sublist_append Int_insert_right lessThan_Suc nth_append 
                 bag_of_sublist_lemma add_ac)
done


lemma bag_of_sublist_Un_Int:
     "bag_of (sublist l (A Un B)) + bag_of (sublist l (A Int B)) =  
      bag_of (sublist l A) + bag_of (sublist l B)"
apply (subgoal_tac "A Int B Int {..<length l} =
                    (A Int {..<length l}) Int (B Int {..<length l}) ")
apply (simp add: bag_of_sublist Int_Un_distrib2 setsum_Un_Int, blast)
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
apply (simp del: UN_simps 
            add: UN_simps [symmetric] add: bag_of_sublist)
apply (subst setsum_UN_disjoint, auto)
done

end
