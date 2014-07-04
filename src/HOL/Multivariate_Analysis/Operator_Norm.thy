(*  Title:      HOL/Multivariate_Analysis/Operator_Norm.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Brian Huffman
*)

header {* Operator Norm *}

theory Operator_Norm
imports Complex_Main
begin

text {* This formulation yields zero if @{text 'a} is the trivial vector space. *}

definition onorm :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> real"
  where "onorm f = (SUP x. norm (f x) / norm x)"

lemma onorm_bound:
  assumes "0 \<le> b" and "\<And>x. norm (f x) \<le> b * norm x"
  shows "onorm f \<le> b"
  unfolding onorm_def
proof (rule cSUP_least)
  fix x
  show "norm (f x) / norm x \<le> b"
    using assms by (cases "x = 0") (simp_all add: pos_divide_le_eq)
qed simp

text {* In non-trivial vector spaces, the first assumption is redundant. *}

lemma onorm_le:
  fixes f :: "'a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>x. norm (f x) \<le> b * norm x"
  shows "onorm f \<le> b"
proof (rule onorm_bound [OF _ assms])
  have "{0::'a} \<noteq> UNIV" by (metis not_open_singleton open_UNIV)
  then obtain a :: 'a where "a \<noteq> 0" by fast
  have "0 \<le> b * norm a"
    by (rule order_trans [OF norm_ge_zero assms])
  with `a \<noteq> 0` show "0 \<le> b"
    by (simp add: zero_le_mult_iff)
qed

lemma le_onorm:
  assumes "bounded_linear f"
  shows "norm (f x) / norm x \<le> onorm f"
proof -
  interpret f: bounded_linear f by fact
  obtain b where "0 \<le> b" and "\<forall>x. norm (f x) \<le> norm x * b"
    using f.nonneg_bounded by auto
  then have "\<forall>x. norm (f x) / norm x \<le> b"
    by (clarify, case_tac "x = 0",
      simp_all add: f.zero pos_divide_le_eq mult.commute)
  then have "bdd_above (range (\<lambda>x. norm (f x) / norm x))"
    unfolding bdd_above_def by fast
  with UNIV_I show ?thesis
    unfolding onorm_def by (rule cSUP_upper)
qed

lemma onorm:
  assumes "bounded_linear f"
  shows "norm (f x) \<le> onorm f * norm x"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis
  proof (cases)
    assume "x = 0"
    then show ?thesis by (simp add: f.zero)
  next
    assume "x \<noteq> 0"
    have "norm (f x) / norm x \<le> onorm f"
      by (rule le_onorm [OF assms])
    then show "norm (f x) \<le> onorm f * norm x"
      by (simp add: pos_divide_le_eq `x \<noteq> 0`)
  qed
qed

lemma onorm_pos_le:
  assumes f: "bounded_linear f"
  shows "0 \<le> onorm f"
  using le_onorm [OF f, where x=0] by simp

lemma onorm_zero: "onorm (\<lambda>x. 0) = 0"
proof (rule order_antisym)
  show "onorm (\<lambda>x. 0) \<le> 0"
    by (simp add: onorm_bound)
  show "0 \<le> onorm (\<lambda>x. 0)"
    using bounded_linear_zero by (rule onorm_pos_le)
qed

lemma onorm_eq_0:
  assumes f: "bounded_linear f"
  shows "onorm f = 0 \<longleftrightarrow> (\<forall>x. f x = 0)"
  using onorm [OF f] by (auto simp: fun_eq_iff [symmetric] onorm_zero)

lemma onorm_pos_lt:
  assumes f: "bounded_linear f"
  shows "0 < onorm f \<longleftrightarrow> \<not> (\<forall>x. f x = 0)"
  by (simp add: less_le onorm_pos_le [OF f] onorm_eq_0 [OF f])

lemma onorm_compose:
  assumes f: "bounded_linear f"
  assumes g: "bounded_linear g"
  shows "onorm (f \<circ> g) \<le> onorm f * onorm g"
proof (rule onorm_bound)
  show "0 \<le> onorm f * onorm g"
    by (intro mult_nonneg_nonneg onorm_pos_le f g)
next
  fix x
  have "norm (f (g x)) \<le> onorm f * norm (g x)"
    by (rule onorm [OF f])
  also have "onorm f * norm (g x) \<le> onorm f * (onorm g * norm x)"
    by (rule mult_left_mono [OF onorm [OF g] onorm_pos_le [OF f]])
  finally show "norm ((f \<circ> g) x) \<le> onorm f * onorm g * norm x"
    by (simp add: mult.assoc)
qed

lemma onorm_scaleR_lemma:
  assumes f: "bounded_linear f"
  shows "onorm (\<lambda>x. r *\<^sub>R f x) \<le> \<bar>r\<bar> * onorm f"
proof (rule onorm_bound)
  show "0 \<le> \<bar>r\<bar> * onorm f"
    by (intro mult_nonneg_nonneg onorm_pos_le abs_ge_zero f)
next
  fix x
  have "\<bar>r\<bar> * norm (f x) \<le> \<bar>r\<bar> * (onorm f * norm x)"
    by (intro mult_left_mono onorm abs_ge_zero f)
  then show "norm (r *\<^sub>R f x) \<le> \<bar>r\<bar> * onorm f * norm x"
    by (simp only: norm_scaleR mult.assoc)
qed

lemma onorm_scaleR:
  assumes f: "bounded_linear f"
  shows "onorm (\<lambda>x. r *\<^sub>R f x) = \<bar>r\<bar> * onorm f"
proof (cases "r = 0")
  assume "r \<noteq> 0"
  show ?thesis
  proof (rule order_antisym)
    show "onorm (\<lambda>x. r *\<^sub>R f x) \<le> \<bar>r\<bar> * onorm f"
      using f by (rule onorm_scaleR_lemma)
  next
    have "bounded_linear (\<lambda>x. r *\<^sub>R f x)"
      using bounded_linear_scaleR_right f by (rule bounded_linear_compose)
    then have "onorm (\<lambda>x. inverse r *\<^sub>R r *\<^sub>R f x) \<le> \<bar>inverse r\<bar> * onorm (\<lambda>x. r *\<^sub>R f x)"
      by (rule onorm_scaleR_lemma)
    with `r \<noteq> 0` show "\<bar>r\<bar> * onorm f \<le> onorm (\<lambda>x. r *\<^sub>R f x)"
      by (simp add: inverse_eq_divide pos_le_divide_eq mult.commute)
  qed
qed (simp add: onorm_zero)

lemma onorm_neg:
  shows "onorm (\<lambda>x. - f x) = onorm f"
  unfolding onorm_def by simp

lemma onorm_triangle:
  assumes f: "bounded_linear f"
  assumes g: "bounded_linear g"
  shows "onorm (\<lambda>x. f x + g x) \<le> onorm f + onorm g"
proof (rule onorm_bound)
  show "0 \<le> onorm f + onorm g"
    by (intro add_nonneg_nonneg onorm_pos_le f g)
next
  fix x
  have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
    by (rule norm_triangle_ineq)
  also have "norm (f x) + norm (g x) \<le> onorm f * norm x + onorm g * norm x"
    by (intro add_mono onorm f g)
  finally show "norm (f x + g x) \<le> (onorm f + onorm g) * norm x"
    by (simp only: distrib_right)
qed

lemma onorm_triangle_le:
  assumes "bounded_linear f"
  assumes "bounded_linear g"
  assumes "onorm f + onorm g \<le> e"
  shows "onorm (\<lambda>x. f x + g x) \<le> e"
  using assms by (rule onorm_triangle [THEN order_trans])

lemma onorm_triangle_lt:
  assumes "bounded_linear f"
  assumes "bounded_linear g"
  assumes "onorm f + onorm g < e"
  shows "onorm (\<lambda>x. f x + g x) < e"
  using assms by (rule onorm_triangle [THEN order_le_less_trans])

end
