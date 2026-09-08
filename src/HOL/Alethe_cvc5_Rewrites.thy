(*  Title:      HOL/Alethe_cvc5_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_cvc5_Rewrites
  imports "Alethe_Rare_Nary_Ops"
begin

(*
Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in
Alethe_Rare_Interface.thy and register the rules using the cvc5_rare command.
*)

named_theorems rewrite_ite_eq \<open>cvc5 specific\<close>
(* (define-rule ite_eq ((C bool) (t1 ?) (t2 ?)) (ite C (= (C?t1:t2) t1) (= (C?t1:t2) t2)) true)*)

lemma [rewrite_ite_eq]:
  fixes C::"bool" and t1::"'a::type" and t2::"'a::type"
  shows "NO_MATCH cvc_a (undefined C t1 t2) \<Longrightarrow>
  (if C then ((if C then t1 else t2) = t1) else ((if C then t1 else t2) = t2)) = True"
  by simp

named_theorems rewrite_or_not_refl \<open>added in postprocessing\<close>
(*(define-rule or-not-refl ((t ?) (xs Bool :list)) (or (not (= t t)) xs) (or xs))*)

lemma [rewrite_or_not_refl]:
  fixes t::'a and xs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined t xs) \<Longrightarrow>
   ((cvc_list_right (\<or>) (\<not>(t = t)) xs)) = (cvc_list_both (\<or>) False xs (ListVar []))"
  unfolding cvc_list_both_def cvc_list_right_def
  apply (cases xs)
  subgoal for xs'
    apply (induction xs')
     apply simp_all
    done
  done

named_theorems rewrite_distinct_binary_elim \<open>added in postprocessing\<close>
(*(define-rule bool-not-eq-false ((t Bool)) (not (= t t)) false)*)

lemma [rewrite_distinct_binary_elim]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow>
  \<not>(t = t) = False"
  by simp

end
