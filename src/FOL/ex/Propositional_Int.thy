(*  Title:      FOL/ex/Propositional_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: propositional examples (intuitionistic version)\<close>

theory Propositional_Int
imports IFOL
begin

text \<open>commutative laws of \<open>\<and>\<close> and \<open>\<or>\<close>\<close>

lemma \<open>P \<and> Q \<longrightarrow> Q \<and> P\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>P \<or> Q \<longrightarrow> Q \<or> P\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")


text \<open>associative laws of \<open>\<and>\<close> and \<open>\<or>\<close>\<close>
lemma \<open>(P \<and> Q) \<and> R \<longrightarrow> P \<and> (Q \<and> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<or> Q) \<or> R \<longrightarrow> P \<or> (Q \<or> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")


text \<open>distributive laws of \<open>\<and>\<close> and \<open>\<or>\<close>\<close>
lemma \<open>(P \<and> Q) \<or> R \<longrightarrow> (P \<or> R) \<and> (Q \<or> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<or> R) \<and> (Q \<or> R) \<longrightarrow> (P \<and> Q) \<or> R\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<or> Q) \<and> R \<longrightarrow> (P \<and> R) \<or> (Q \<and> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<and> R) \<or> (Q \<and> R) \<longrightarrow> (P \<or> Q) \<and> R\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")


text \<open>Laws involving implication\<close>

lemma \<open>(P \<longrightarrow> R) \<and> (Q \<longrightarrow> R) \<longleftrightarrow> (P \<or> Q \<longrightarrow> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<and> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> (Q \<longrightarrow> R))\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>((P \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> ((Q \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> (P \<and> Q \<longrightarrow> R) \<longrightarrow> R\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>\<not> (P \<longrightarrow> R) \<longrightarrow> \<not> (Q \<longrightarrow> R) \<longrightarrow> \<not> (P \<and> Q \<longrightarrow> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<longrightarrow> Q \<and> R) \<longleftrightarrow> (P \<longrightarrow> Q) \<and> (P \<longrightarrow> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")


text \<open>Propositions-as-types\<close>

\<comment> \<open>The combinator K\<close>
lemma \<open>P \<longrightarrow> (Q \<longrightarrow> P)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

\<comment> \<open>The combinator S\<close>
lemma \<open>(P \<longrightarrow> Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")


\<comment> \<open>Converse is classical\<close>
lemma \<open>(P \<longrightarrow> Q) \<or> (P \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<or> R)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma \<open>(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")


text \<open>Schwichtenberg's examples (via T. Nipkow)\<close>

lemma stab_imp: \<open>(((Q \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> Q) \<longrightarrow> (((P \<longrightarrow> Q) \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> P \<longrightarrow> Q\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma stab_to_peirce:
  \<open>(((P \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> P) \<longrightarrow> (((Q \<longrightarrow> R) \<longrightarrow> R) \<longrightarrow> Q)
    \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma peirce_imp1:
  \<open>(((Q \<longrightarrow> R) \<longrightarrow> Q) \<longrightarrow> Q)
    \<longrightarrow> (((P \<longrightarrow> Q) \<longrightarrow> R) \<longrightarrow> P \<longrightarrow> Q) \<longrightarrow> P \<longrightarrow> Q\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma peirce_imp2: \<open>(((P \<longrightarrow> R) \<longrightarrow> P) \<longrightarrow> P) \<longrightarrow> ((P \<longrightarrow> Q \<longrightarrow> R) \<longrightarrow> P) \<longrightarrow> P\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma mints: \<open>((((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P) \<longrightarrow> Q) \<longrightarrow> Q\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma mints_solovev: \<open>(P \<longrightarrow> (Q \<longrightarrow> R) \<longrightarrow> Q) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> R) \<longrightarrow> R\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma tatsuta:
  \<open>(((P7 \<longrightarrow> P1) \<longrightarrow> P10) \<longrightarrow> P4 \<longrightarrow> P5)
  \<longrightarrow> (((P8 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P3 \<longrightarrow> P10)
  \<longrightarrow> (P1 \<longrightarrow> P8) \<longrightarrow> P6 \<longrightarrow> P7
  \<longrightarrow> (((P3 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P4)
  \<longrightarrow> (P1 \<longrightarrow> P3) \<longrightarrow> (((P6 \<longrightarrow> P1) \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P5\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

lemma tatsuta1:
  \<open>(((P8 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P3 \<longrightarrow> P10)
  \<longrightarrow> (((P3 \<longrightarrow> P2) \<longrightarrow> P9) \<longrightarrow> P4)
  \<longrightarrow> (((P6 \<longrightarrow> P1) \<longrightarrow> P2) \<longrightarrow> P9)
  \<longrightarrow> (((P7 \<longrightarrow> P1) \<longrightarrow> P10) \<longrightarrow> P4 \<longrightarrow> P5)
  \<longrightarrow> (P1 \<longrightarrow> P3) \<longrightarrow> (P1 \<longrightarrow> P8) \<longrightarrow> P6 \<longrightarrow> P7 \<longrightarrow> P5\<close>
  by (tactic "IntPr.fast_tac \<^context> 1")

end
