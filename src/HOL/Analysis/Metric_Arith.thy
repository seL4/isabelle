(*  Title:      HOL/Analysis/Metric_Arith.thy
    Author:     Maximilian Schäffeler (port from HOL Light)
*)

chapter \<open>Functional Analysis\<close>

section\<^marker>\<open>tag unimportant\<close> \<open>A decision procedure for metric spaces\<close>

theory Metric_Arith
  imports HOL.Real_Vector_Spaces
begin

text\<^marker>\<open>tag unimportant\<close> \<open>
A port of the decision procedure ``Formalization of metric spaces in HOL Light''
@{cite "DBLP:journals/jar/Maggesi18"} for the type class @{class metric_space},
with the \<open>Argo\<close> solver as backend.
\<close>

named_theorems metric_prenex
named_theorems metric_nnf
named_theorems metric_unfold
named_theorems metric_pre_arith

lemmas pre_arith_simps =
  max.bounded_iff max_less_iff_conj
  le_max_iff_disj less_max_iff_disj
  simp_thms HOL.eq_commute
declare pre_arith_simps [metric_pre_arith]

lemmas unfold_simps =
  Un_iff subset_iff disjoint_iff_not_equal
  Ball_def Bex_def
declare unfold_simps [metric_unfold]

declare HOL.nnf_simps(4) [metric_prenex]

lemma imp_prenex [metric_prenex]:
  "\<And>P Q. (\<exists>x. P x) \<longrightarrow> Q \<equiv> \<forall>x. (P x \<longrightarrow> Q)"
  "\<And>P Q. P \<longrightarrow> (\<exists>x. Q x) \<equiv> \<exists>x. (P \<longrightarrow> Q x)"
  "\<And>P Q. (\<forall>x. P x) \<longrightarrow> Q \<equiv> \<exists>x. (P x \<longrightarrow> Q)"
  "\<And>P Q. P \<longrightarrow> (\<forall>x. Q x) \<equiv> \<forall>x. (P \<longrightarrow> Q x)"
  by simp_all

lemma ex_prenex [metric_prenex]:
  "\<And>P Q. (\<exists>x. P x) \<and> Q \<equiv> \<exists>x. (P x \<and> Q)"
  "\<And>P Q. P \<and> (\<exists>x. Q x) \<equiv> \<exists>x. (P \<and> Q x)"
  "\<And>P Q. (\<exists>x. P x) \<or> Q \<equiv> \<exists>x. (P x \<or> Q)"
  "\<And>P Q. P \<or> (\<exists>x. Q x) \<equiv> \<exists>x. (P \<or> Q x)"
  "\<And>P. \<not>(\<exists>x. P x) \<equiv> \<forall>x. \<not>P x"
  by simp_all

lemma all_prenex [metric_prenex]:
  "\<And>P Q. (\<forall>x. P x) \<and> Q \<equiv> \<forall>x. (P x \<and> Q)"
  "\<And>P Q. P \<and> (\<forall>x. Q x) \<equiv> \<forall>x. (P \<and> Q x)"
  "\<And>P Q. (\<forall>x. P x) \<or> Q \<equiv> \<forall>x. (P x \<or> Q)"
  "\<And>P Q. P \<or> (\<forall>x. Q x) \<equiv> \<forall>x. (P \<or> Q x)"
  "\<And>P. \<not>(\<forall>x. P x) \<equiv> \<exists>x. \<not>P x"
  by simp_all

lemma nnf_thms [metric_nnf]:
  "(\<not> (P \<and> Q)) = (\<not> P \<or> \<not> Q)"
  "(\<not> (P \<or> Q)) = (\<not> P \<and> \<not> Q)"
  "(P \<longrightarrow> Q) = (\<not> P \<or> Q)"
  "(P = Q) \<longleftrightarrow> (P \<or> \<not> Q) \<and> (\<not> P \<or> Q)"
  "(\<not> (P = Q)) \<longleftrightarrow> (\<not> P \<or> \<not> Q) \<and> (P \<or> Q)"
  "(\<not> \<not> P) = P"
  by blast+

lemmas nnf_simps = nnf_thms linorder_not_less linorder_not_le
declare nnf_simps[metric_nnf]

lemma ball_insert: "(\<forall>x\<in>insert a B. P x) = (P a \<and> (\<forall>x\<in>B. P x))"
  by blast

lemma Sup_insert_insert:
  fixes a::real
  shows "Sup (insert a (insert b s)) = Sup (insert (max a b) s)"
  by (simp add: Sup_real_def)

lemma real_abs_dist: "\<bar>dist x y\<bar> = dist x y"
  by simp

lemma maxdist_thm [THEN HOL.eq_reflection]:
  assumes "finite s" "x \<in> s" "y \<in> s"
  defines "\<And>a. f a \<equiv> \<bar>dist x a - dist a y\<bar>"
  shows "dist x y = Sup (f ` s)"
proof -
  have "dist x y \<le> Sup (f ` s)"
  proof -
    have "finite (f ` s)"
      by (simp add: \<open>finite s\<close>)
    moreover have "\<bar>dist x y - dist y y\<bar> \<in> f ` s"
      by (metis \<open>y \<in> s\<close> f_def imageI)
    ultimately show ?thesis
      using le_cSup_finite by simp
  qed
  also have "Sup (f ` s) \<le> dist x y"
    using \<open>x \<in> s\<close> cSUP_least[of s f] abs_dist_diff_le
    unfolding f_def
    by blast
  finally show ?thesis .
qed

theorem metric_eq_thm [THEN HOL.eq_reflection]:
  "x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x = y \<longleftrightarrow> (\<forall>a\<in>s. dist x a = dist y a)"
  by auto

ML_file "metric_arith.ML"

method_setup metric = \<open>
  Scan.succeed (SIMPLE_METHOD' o Metric_Arith.metric_arith_tac)
\<close> "prove simple linear statements in metric spaces (\<forall>\<exists>\<^sub>p fragment)"

end
