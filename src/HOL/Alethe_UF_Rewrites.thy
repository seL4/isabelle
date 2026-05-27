(*  Title:      HOL/Alethe_UF_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_UF_Rewrites
  imports "Alethe_Rare_Nary_Ops"
begin

(*
Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in
Alethe_Rare_Interface.thy and register the rules using the cvc5_rare command.
*)

named_theorems rewrite_eq_refl \<open>automatically_generated\<close>

lemma [rewrite_eq_refl]:
  fixes t::"'a::type"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = t) = True"
  by auto

named_theorems rewrite_eq_symm \<open>automatically_generated\<close>

lemma [rewrite_eq_symm]:
  fixes t::"'a::type" and s::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t = s) = (s = t)"
  by auto

named_theorems rewrite_eq_cond_deq \<open>automatically_generated\<close>

lemma [rewrite_eq_cond_deq]:
  fixes t::"'a::type" and s::"'a::type" and r::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s r) \<Longrightarrow> ((s = r) = False) \<Longrightarrow> ((t = s) = (t = r)) = ((\<not>(t = s)) \<and> (\<not>(t = r)))"
  by auto

named_theorems rewrite_eq_ite_lift \<open>automatically_generated\<close>

lemma [rewrite_eq_ite_lift]:
  fixes C::bool and t::"'a::type" and s::"'a::type" and r::"'a::type"
  shows "NO_MATCH cvc_a (undefined C t s r) \<Longrightarrow> ((if C then t else s) = r) = (if C then (t = r) else (s = r))"
  by auto

named_theorems rewrite_distinct_binary_elim \<open>automatically_generated\<close>

lemma [rewrite_distinct_binary_elim]:
  fixes t::"'a::type" and s::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<noteq> s) = (\<not> (t = s))"
  by auto

end
