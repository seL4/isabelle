(*  Title:      FOL/ex/Propositional_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: propositional examples (intuitionistic version)\<close>

theory Propositional_Int
imports IFOL
begin

text \<open>commutative laws of @{text "\<and>"} and @{text "\<or>"}\<close>

lemma "P \<and> Q \<longrightarrow> Q \<and> P"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "P \<or> Q \<longrightarrow> Q \<or> P"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>associative laws of @{text "\<and>"} and @{text "\<or>"}\<close>
lemma "(P \<and> Q) \<and> R \<longrightarrow> P \<and> (Q \<and> R)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<or> Q) \<or> R \<longrightarrow> P \<or> (Q \<or> R)"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>distributive laws of @{text "\<and>"} and @{text "\<or>"}\<close>
lemma "(P \<and> Q) \<or> R \<longrightarrow> (P \<or> R) \<and> (Q \<or> R)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<or> R) \<and> (Q \<or> R) \<longrightarrow> (P \<and> Q) \<or> R"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<or> Q) \<and> R \<longrightarrow> (P \<and> R) \<or> (Q \<and> R)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<and> R) \<or> (Q \<and> R) \<longrightarrow> (P \<or> Q) \<and> R"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>Laws involving implication\<close>

lemma "(P \<longrightarrow> R) \<and> (Q \<longrightarrow> R) \<longleftrightarrow> (P \<or> Q \<longrightarrow> R)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<and> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> (Q \<longrightarrow> R))"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "((P \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> ((Q \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> (P \<and> Q \<longrightarrow> R) \<longrightarrow> R"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "\<not> (P \<longrightarrow> R) \<longrightarrow> \<not> (Q \<longrightarrow> R) \<longrightarrow> \<not> (P \<and> Q \<longrightarrow> R)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<longrightarrow> Q \<and> R) \<longleftrightarrow> (P \<longrightarrow> Q) \<and> (P \<longrightarrow> R)"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>Propositions-as-types\<close>

-- \<open>The combinator K\<close>
lemma "P \<longrightarrow> (Q \<longrightarrow> P)"
  by (tactic "IntPr.fast_tac @{context} 1")

-- \<open>The combinator S\<close>
lemma "(P \<longrightarrow> Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R)"
  by (tactic "IntPr.fast_tac @{context} 1")


-- \<open>Converse is classical\<close>
lemma "(P \<longrightarrow> Q) \<or> (P \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<or> R)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>Schwichtenberg's examples (via T. Nipkow)\<close>

lemma stab_imp: "(((Q \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> Q) \<longrightarrow> (((P \<longrightarrow> Q) \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> P \<longrightarrow> Q"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma stab_to_peirce:
  "(((P \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> P) \<longrightarrow> (((Q \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> Q)
    \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma peirce_imp1:
  "(((Q \<longrightarrow> R) \<longrightarrow> Q) \<longrightarrow> Q)
    \<longrightarrow> (((P \<longrightarrow> Q) \<longrightarrow> R) \<longrightarrow> P \<longrightarrow> Q) \<longrightarrow> P \<longrightarrow> Q"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma peirce_imp2: "(((P \<longrightarrow> R) \<longrightarrow> P) \<longrightarrow> P) \<longrightarrow> ((P \<longrightarrow> Q \<longrightarrow> R) \<longrightarrow> P) \<longrightarrow> P"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma mints: "((((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P) \<longrightarrow> Q) \<longrightarrow> Q"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma mints_solovev: "(P \<longrightarrow> (Q \<longrightarrow> R) \<longrightarrow> Q) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> R) \<longrightarrow> R"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma tatsuta:
  "(((P7 \<longrightarrow> P1) \<longrightarrow> P10) \<longrightarrow> P4 \<longrightarrow> P5)
  \<longrightarrow> (((P8 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P3 \<longrightarrow> P10)
  \<longrightarrow> (P1 \<longrightarrow> P8) \<longrightarrow> P6 \<longrightarrow> P7
  \<longrightarrow> (((P3 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P4)
  \<longrightarrow> (P1 \<longrightarrow> P3) \<longrightarrow> (((P6 \<longrightarrow> P1) \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P5"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma tatsuta1:
  "(((P8 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P3 \<longrightarrow> P10)
  \<longrightarrow> (((P3 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P4)
  \<longrightarrow> (((P6 \<longrightarrow> P1) \<longrightarrow> P2) \<longrightarrow> P9)
  \<longrightarrow> (((P7 \<longrightarrow> P1) \<longrightarrow> P10) \<longrightarrow> P4 \<longrightarrow> P5)
  \<longrightarrow> (P1 \<longrightarrow> P3) \<longrightarrow> (P1 \<longrightarrow> P8) \<longrightarrow> P6 \<longrightarrow> P7 \<longrightarrow> P5"
  by (tactic "IntPr.fast_tac @{context} 1")

end
