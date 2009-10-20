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
  ring_distribs field_eq_simps

end
