(*  Title:      FOL/ex/Miniscope.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Classical First-Order Logic.
Conversion to nnf/miniscope format: pushing quantifiers in.
Demonstration of formula rewriting by proof.
*)

theory Miniscope
imports FOL
begin

lemmas ccontr = FalseE [THEN classical]

subsection \<open>Negation Normal Form\<close>

subsubsection \<open>de Morgan laws\<close>

lemma demorgans1:
  \<open>\<not> (P \<and> Q) \<longleftrightarrow> \<not> P \<or> \<not> Q\<close>
  \<open>\<not> (P \<or> Q) \<longleftrightarrow> \<not> P \<and> \<not> Q\<close>
  \<open>\<not> \<not> P \<longleftrightarrow> P\<close>
  by blast+

lemma demorgans2:
  \<open>\<And>P. \<not> (\<forall>x. P(x)) \<longleftrightarrow> (\<exists>x. \<not> P(x))\<close>
  \<open>\<And>P. \<not> (\<exists>x. P(x)) \<longleftrightarrow> (\<forall>x. \<not> P(x))\<close>
  by blast+

lemmas demorgans = demorgans1 demorgans2

(*** Removal of --> and <-> (positive and negative occurrences) ***)
(*Last one is important for computing a compact CNF*)
lemma nnf_simps:
  \<open>(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)\<close>
  \<open>\<not> (P \<longrightarrow> Q) \<longleftrightarrow> (P \<and> \<not> Q)\<close>
  \<open>(P \<longleftrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q) \<and> (\<not> Q \<or> P)\<close>
  \<open>\<not> (P \<longleftrightarrow> Q) \<longleftrightarrow> (P \<or> Q) \<and> (\<not> P \<or> \<not> Q)\<close>
  by blast+


(* BEWARE: rewrite rules for <-> can confuse the simplifier!! *)

subsubsection \<open>Pushing in the existential quantifiers\<close>

lemma ex_simps:
  \<open>(\<exists>x. P) \<longleftrightarrow> P\<close>
  \<open>\<And>P Q. (\<exists>x. P(x) \<and> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<and> Q\<close>
  \<open>\<And>P Q. (\<exists>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<exists>x. Q(x))\<close>
  \<open>\<And>P Q. (\<exists>x. P(x) \<or> Q(x)) \<longleftrightarrow> (\<exists>x. P(x)) \<or> (\<exists>x. Q(x))\<close>
  \<open>\<And>P Q. (\<exists>x. P(x) \<or> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<or> Q\<close>
  \<open>\<And>P Q. (\<exists>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<exists>x. Q(x))\<close>
  by blast+


subsubsection \<open>Pushing in the universal quantifiers\<close>

lemma all_simps:
  \<open>(\<forall>x. P) \<longleftrightarrow> P\<close>
  \<open>\<And>P Q. (\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> (\<forall>x. P(x)) \<and> (\<forall>x. Q(x))\<close>
  \<open>\<And>P Q. (\<forall>x. P(x) \<and> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<and> Q\<close>
  \<open>\<And>P Q. (\<forall>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<forall>x. Q(x))\<close>
  \<open>\<And>P Q. (\<forall>x. P(x) \<or> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<or> Q\<close>
  \<open>\<And>P Q. (\<forall>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<forall>x. Q(x))\<close>
  by blast+

lemmas mini_simps = demorgans nnf_simps ex_simps all_simps

ML \<open>
val mini_ss = simpset_of (\<^context> |> Simplifier.add_simps @{thms mini_simps});
fun mini_tac ctxt =
  resolve_tac ctxt @{thms ccontr} THEN' asm_full_simp_tac (put_simpset mini_ss ctxt);
\<close>

end
