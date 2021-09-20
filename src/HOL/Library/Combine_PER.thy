(*  Author:     Florian Haftmann, TU Muenchen *)

section \<open>A combinator to build partial equivalence relations from a predicate and an equivalence relation\<close>

theory Combine_PER
  imports Main
begin

unbundle lattice_syntax

definition combine_per :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "combine_per P R = (\<lambda>x y. P x \<and> P y) \<sqinter> R"

lemma combine_per_simp [simp]:
  "combine_per P R x y \<longleftrightarrow> P x \<and> P y \<and> x \<approx> y" for R (infixl "\<approx>" 50)
  by (simp add: combine_per_def)

lemma combine_per_top [simp]: "combine_per \<top> R = R"
  by (simp add: fun_eq_iff)

lemma combine_per_eq [simp]: "combine_per P HOL.eq = HOL.eq \<sqinter> (\<lambda>x y. P x)"
  by (auto simp add: fun_eq_iff)

lemma symp_combine_per: "symp R \<Longrightarrow> symp (combine_per P R)"
  by (auto simp add: symp_def sym_def combine_per_def)

lemma transp_combine_per: "transp R \<Longrightarrow> transp (combine_per P R)"
  by (auto simp add: transp_def trans_def combine_per_def)

lemma combine_perI: "P x \<Longrightarrow> P y \<Longrightarrow> x \<approx> y \<Longrightarrow> combine_per P R x y" for R (infixl "\<approx>" 50)
  by (simp add: combine_per_def)

lemma symp_combine_per_symp: "symp R \<Longrightarrow> symp (combine_per P R)"
  by (auto intro!: sympI elim: sympE)

lemma transp_combine_per_transp: "transp R \<Longrightarrow> transp (combine_per P R)"
  by (auto intro!: transpI elim: transpE)

lemma equivp_combine_per_part_equivp [intro?]:
  fixes R (infixl "\<approx>" 50)
  assumes "\<exists>x. P x" and "equivp R"
  shows "part_equivp (combine_per P R)"
proof -
  from \<open>\<exists>x. P x\<close> obtain x where "P x" ..
  moreover from \<open>equivp R\<close> have "x \<approx> x"
    by (rule equivp_reflp)
  ultimately have "\<exists>x. P x \<and> x \<approx> x"
    by blast
  with \<open>equivp R\<close> show ?thesis
    by (auto intro!: part_equivpI symp_combine_per_symp transp_combine_per_transp
      elim: equivpE)
qed

end
