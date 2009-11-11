(*  Title:      HOL/SMT/Z3.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Binding to the SMT solver Z3, with proof reconstruction *}

theory Z3
imports SMT_Base
uses
  "Tools/z3_proof_terms.ML"
  "Tools/z3_proof_rules.ML"
  "Tools/z3_proof.ML"
  "Tools/z3_model.ML"
  "Tools/z3_interface.ML"
  "Tools/z3_solver.ML"
begin

setup {* Z3_Proof_Rules.setup #> Z3_Solver.setup *}

lemmas [z3_rewrite] =
  refl eq_commute conj_commute disj_commute simp_thms nnf_simps
  ring_distribs field_eq_simps if_True if_False

lemma [z3_rewrite]: "(P \<noteq> Q) = (Q = (\<not>P))" by fast

lemma [z3_rewrite]: "(\<not>False \<longrightarrow> P) = P" by fast
lemma [z3_rewrite]: "(P \<longrightarrow> Q) = (Q \<or> \<not>P)" by fast
lemma [z3_rewrite]: "(\<not>P \<longrightarrow> Q) = (P \<or> Q)" by fast
lemma [z3_rewrite]: "(\<not>P \<longrightarrow> Q) = (Q \<or> P)" by fast

lemma [z3_rewrite]: "(if P then True else False) = P" by simp
lemma [z3_rewrite]: "(if P then False else True) = (\<not>P)" by simp

lemma [z3_rewrite]:
  "0 + (x::int) = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

lemma [z3_rewrite]:
  "0 + (x::real) = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

end
