(*  Title:      HOL/UNITY/AllocBase.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

*)

header{*Common Declarations for Chandy and Charpentier's Allocator*}

theory AllocBase = UNITY_Main:

consts
  NbT      :: nat       (*Number of tokens in system*)
  Nclients :: nat       (*Number of clients*)

axioms
  NbT_pos:  "0 < NbT"

(*This function merely sums the elements of a list*)
consts tokens     :: "nat list => nat"
primrec 
  "tokens [] = 0"
  "tokens (x#xs) = x + tokens xs"

consts
  bag_of :: "'a list => 'a multiset"

primrec
  "bag_of []     = {#}"
  "bag_of (x#xs) = {#x#} + bag_of xs"

lemma setsum_fun_mono [rule_format]:
     "!!f :: nat=>nat.  
      (ALL i. i<n --> f i <= g i) -->  
      setsum f (lessThan n) <= setsum g (lessThan n)"
apply (induct_tac "n")
apply (auto simp add: lessThan_Suc)
apply (drule_tac x = n in spec, arith)
done

lemma tokens_mono_prefix [rule_format]:
     "ALL xs. xs <= ys --> tokens xs <= tokens ys"
apply (induct_tac "ys")
apply (auto simp add: prefix_Cons)
done

lemma mono_tokens: "mono tokens"
apply (unfold mono_def)
apply (blast intro: tokens_mono_prefix)
done


(** bag_of **)

lemma bag_of_append [simp]: "bag_of (l@l') = bag_of l + bag_of l'"
apply (induct_tac "l", simp)
 apply (simp add: plus_ac0)
done

lemma mono_bag_of: "mono (bag_of :: 'a list => ('a::order) multiset)"
apply (rule monoI)
apply (unfold prefix_def)
apply (erule genPrefix.induct, auto)
apply (simp add: union_le_mono)
apply (erule order_trans)
apply (rule union_upper1)
done

(** setsum **)

declare setsum_cong [cong]

lemma bag_of_sublist_lemma:
     "(\<Sum>i: A Int lessThan k. {#if i<k then f i else g i#}) =  
      (\<Sum>i: A Int lessThan k. {#f i#})"
apply (rule setsum_cong, auto)
done

lemma bag_of_sublist:
     "bag_of (sublist l A) =  
      (\<Sum>i: A Int lessThan (length l). {# l!i #})"
apply (rule_tac xs = l in rev_induct, simp)
apply (simp add: sublist_append Int_insert_right lessThan_Suc nth_append 
                 bag_of_sublist_lemma plus_ac0)
done


lemma bag_of_sublist_Un_Int:
     "bag_of (sublist l (A Un B)) + bag_of (sublist l (A Int B)) =  
      bag_of (sublist l A) + bag_of (sublist l B)"
apply (subgoal_tac "A Int B Int {..length l (} = (A Int {..length l (}) Int (B Int {..length l (}) ")
apply (simp add: bag_of_sublist Int_Un_distrib2 setsum_Un_Int, blast)
done

lemma bag_of_sublist_Un_disjoint:
     "A Int B = {}  
      ==> bag_of (sublist l (A Un B)) =  
          bag_of (sublist l A) + bag_of (sublist l B)"
apply (simp add: bag_of_sublist_Un_Int [symmetric])
done

lemma bag_of_sublist_UN_disjoint [rule_format]:
     "[| finite I; ALL i:I. ALL j:I. i~=j --> A i Int A j = {} |]  
      ==> bag_of (sublist l (UNION I A)) =   
          (\<Sum>i:I. bag_of (sublist l (A i)))"
apply (simp del: UN_simps 
            add: UN_simps [symmetric] add: bag_of_sublist)
apply (subst setsum_UN_disjoint, auto)
done

ML
{*
val NbT_pos = thm "NbT_pos";
val setsum_fun_mono = thm "setsum_fun_mono";
val tokens_mono_prefix = thm "tokens_mono_prefix";
val mono_tokens = thm "mono_tokens";
val bag_of_append = thm "bag_of_append";
val mono_bag_of = thm "mono_bag_of";
val bag_of_sublist_lemma = thm "bag_of_sublist_lemma";
val bag_of_sublist = thm "bag_of_sublist";
val bag_of_sublist_Un_Int = thm "bag_of_sublist_Un_Int";
val bag_of_sublist_Un_disjoint = thm "bag_of_sublist_Un_disjoint";
val bag_of_sublist_UN_disjoint = thm "bag_of_sublist_UN_disjoint";
*}

end
