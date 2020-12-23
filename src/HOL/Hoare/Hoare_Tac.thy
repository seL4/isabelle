(*  Title:      HOL/Hoare/Hoare_Tac.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Author:     Walter Guttmann (extension to total-correctness proofs)

Derivation of the proof rules and, most importantly, the VCG tactic.
*)

theory Hoare_Tac
  imports Main
begin

context
begin

qualified named_theorems BasicRule
qualified named_theorems SkipRule
qualified named_theorems AbortRule
qualified named_theorems SeqRule
qualified named_theorems CondRule
qualified named_theorems WhileRule

qualified named_theorems BasicRuleTC
qualified named_theorems SkipRuleTC
qualified named_theorems SeqRuleTC
qualified named_theorems CondRuleTC
qualified named_theorems WhileRuleTC

lemma Compl_Collect: "-(Collect b) = {x. \<not>(b x)}"
  by blast

ML_file \<open>hoare_tac.ML\<close>

end

end
