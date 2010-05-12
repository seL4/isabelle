(*  Title:      HOL/SMT/Z3.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Binding to the SMT solver Z3, with proof reconstruction *}

theory Z3
imports SMT_Base "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
uses
  "Tools/z3_proof_parser.ML"
  "Tools/z3_proof_tools.ML"
  "Tools/z3_proof_literals.ML"
  "Tools/z3_proof_reconstruction.ML"
  "Tools/z3_model.ML"
  "Tools/z3_interface.ML"
  "Tools/z3_solver.ML"
begin

setup {*
  Z3_Proof_Reconstruction.setup #>
  Z3_Solver.setup #>
  Arith_Data.add_tactic "Ferrante-Rackoff" (K FerranteRackoff.dlo_tac)
*}

lemmas [z3_rule] =
  refl eq_commute conj_commute disj_commute simp_thms nnf_simps
  ring_distribs field_simps times_divide_eq_right times_divide_eq_left
  if_True if_False not_not

lemma [z3_rule]:
  "(P \<longrightarrow> Q) = (Q \<or> \<not>P)"
  "(\<not>P \<longrightarrow> Q) = (P \<or> Q)"
  "(\<not>P \<longrightarrow> Q) = (Q \<or> P)"
  by auto

lemma [z3_rule]:
  "((P = Q) \<longrightarrow> R) = (R | (Q = (\<not>P)))"
  by auto

lemma [z3_rule]:
  "((\<not>P) = P) = False"
  "(P = (\<not>P)) = False"
  "(P \<noteq> Q) = (Q = (\<not>P))"
  "(P = Q) = ((\<not>P \<or> Q) \<and> (P \<or> \<not>Q))"
  "(P \<noteq> Q) = ((\<not>P \<or> \<not>Q) \<and> (P \<or> Q))"
  by auto

lemma [z3_rule]:
  "(if P then P else \<not>P) = True"
  "(if \<not>P then \<not>P else P) = True"
  "(if P then True else False) = P"
  "(if P then False else True) = (\<not>P)"
  "(if \<not>P then x else y) = (if P then y else x)"
  by auto

lemma [z3_rule]:
  "P = Q \<or> P \<or> Q"
  "P = Q \<or> \<not>P \<or> \<not>Q"
  "(\<not>P) = Q \<or> \<not>P \<or> Q"
  "(\<not>P) = Q \<or> P \<or> \<not>Q"
  "P = (\<not>Q) \<or> \<not>P \<or> Q"
  "P = (\<not>Q) \<or> P \<or> \<not>Q"
  "P \<noteq> Q \<or> P \<or> \<not>Q"
  "P \<noteq> Q \<or> \<not>P \<or> Q"
  "P \<noteq> (\<not>Q) \<or> P \<or> Q"
  "(\<not>P) \<noteq> Q \<or> P \<or> Q"
  "P \<or> Q \<or> P \<noteq> (\<not>Q)"
  "P \<or> Q \<or> (\<not>P) \<noteq> Q"
  "P \<or> \<not>Q \<or> P \<noteq> Q"
  "\<not>P \<or> Q \<or> P \<noteq> Q"
  by auto

lemma [z3_rule]:
  "0 + (x::int) = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

lemma [z3_rule]:
  "0 + (x::real) = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

end
