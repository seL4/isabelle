(*  Title:      HOL/Multivariate_Analysis/L2_Norm.thy
    Author:     Brian Huffman, Portland State University
*)

header {* Square root of sum of squares *}

theory L2_Norm
imports NthRoot
begin

definition
  "setL2 f A = sqrt (\<Sum>i\<in>A. (f i)\<twosuperior>)"

lemma setL2_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> setL2 f A = setL2 g B"
  unfolding setL2_def by simp

lemma strong_setL2_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B =simp=> f x = g x\<rbrakk> \<Longrightarrow> setL2 f A = setL2 g B"
  unfolding setL2_def simp_implies_def by simp

lemma setL2_infinite [simp]: "\<not> finite A \<Longrightarrow> setL2 f A = 0"
  unfolding setL2_def by simp

lemma setL2_empty [simp]: "setL2 f {} = 0"
  unfolding setL2_def by simp

lemma setL2_insert [simp]:
  "\<lbrakk>finite F; a \<notin> F\<rbrakk> \<Longrightarrow>
    setL2 f (insert a F) = sqrt ((f a)\<twosuperior> + (setL2 f F)\<twosuperior>)"
  unfolding setL2_def by (simp add: setsum_nonneg)

lemma setL2_nonneg [simp]: "0 \<le> setL2 f A"
  unfolding setL2_def by (simp add: setsum_nonneg)

lemma setL2_0': "\<forall>a\<in>A. f a = 0 \<Longrightarrow> setL2 f A = 0"
  unfolding setL2_def by simp

lemma setL2_constant: "setL2 (\<lambda>x. y) A = sqrt (of_nat (card A)) * \<bar>y\<bar>"
  unfolding setL2_def by (simp add: real_sqrt_mult)

lemma setL2_mono:
  assumes "\<And>i. i \<in> K \<Longrightarrow> f i \<le> g i"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 \<le> f i"
  shows "setL2 f K \<le> setL2 g K"
  unfolding setL2_def
  by (simp add: setsum_nonneg setsum_mono power_mono assms)

lemma setL2_strict_mono:
  assumes "finite K" and "K \<noteq> {}"
  assumes "\<And>i. i \<in> K \<Longrightarrow> f i < g i"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 \<le> f i"
  shows "setL2 f K < setL2 g K"
  unfolding setL2_def
  by (simp add: setsum_strict_mono power_strict_mono assms)

lemma setL2_right_distrib:
  "0 \<le> r \<Longrightarrow> r * setL2 f A = setL2 (\<lambda>x. r * f x) A"
  unfolding setL2_def
  apply (simp add: power_mult_distrib)
  apply (simp add: setsum_right_distrib [symmetric])
  apply (simp add: real_sqrt_mult setsum_nonneg)
  done

lemma setL2_left_distrib:
  "0 \<le> r \<Longrightarrow> setL2 f A * r = setL2 (\<lambda>x. f x * r) A"
  unfolding setL2_def
  apply (simp add: power_mult_distrib)
  apply (simp add: setsum_left_distrib [symmetric])
  apply (simp add: real_sqrt_mult setsum_nonneg)
  done

lemma setsum_nonneg_eq_0_iff:
  fixes f :: "'a \<Rightarrow> 'b::ordered_ab_group_add"
  shows "\<lbrakk>finite A; \<forall>x\<in>A. 0 \<le> f x\<rbrakk> \<Longrightarrow> setsum f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  apply (induct set: finite, simp)
  apply (simp add: add_nonneg_eq_0_iff setsum_nonneg)
  done

lemma setL2_eq_0_iff: "finite A \<Longrightarrow> setL2 f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  unfolding setL2_def
  by (simp add: setsum_nonneg setsum_nonneg_eq_0_iff)

lemma setL2_triangle_ineq:
  shows "setL2 (\<lambda>i. f i + g i) A \<le> setL2 f A + setL2 g A"
proof (cases "finite A")
  case False
  thus ?thesis by simp
next
  case True
  thus ?thesis
  proof (induct set: finite)
    case empty
    show ?case by simp
  next
    case (insert x F)
    hence "sqrt ((f x + g x)\<twosuperior> + (setL2 (\<lambda>i. f i + g i) F)\<twosuperior>) \<le>
           sqrt ((f x + g x)\<twosuperior> + (setL2 f F + setL2 g F)\<twosuperior>)"
      by (intro real_sqrt_le_mono add_left_mono power_mono insert
                setL2_nonneg add_increasing zero_le_power2)
    also have
      "\<dots> \<le> sqrt ((f x)\<twosuperior> + (setL2 f F)\<twosuperior>) + sqrt ((g x)\<twosuperior> + (setL2 g F)\<twosuperior>)"
      by (rule real_sqrt_sum_squares_triangle_ineq)
    finally show ?case
      using insert by simp
  qed
qed

lemma sqrt_sum_squares_le_sum:
  "\<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> sqrt (x\<twosuperior> + y\<twosuperior>) \<le> x + y"
  apply (rule power2_le_imp_le)
  apply (simp add: power2_sum mult_nonneg_nonneg)
  apply simp
  done

lemma setL2_le_setsum [rule_format]:
  "(\<forall>i\<in>A. 0 \<le> f i) \<longrightarrow> setL2 f A \<le> setsum f A"
  apply (cases "finite A")
  apply (induct set: finite)
  apply simp
  apply clarsimp
  apply (erule order_trans [OF sqrt_sum_squares_le_sum])
  apply simp
  apply simp
  apply simp
  done

lemma sqrt_sum_squares_le_sum_abs: "sqrt (x\<twosuperior> + y\<twosuperior>) \<le> \<bar>x\<bar> + \<bar>y\<bar>"
  apply (rule power2_le_imp_le)
  apply (simp add: power2_sum mult_nonneg_nonneg)
  apply simp
  done

lemma setL2_le_setsum_abs: "setL2 f A \<le> (\<Sum>i\<in>A. \<bar>f i\<bar>)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply simp
  apply simp
  apply (rule order_trans [OF sqrt_sum_squares_le_sum_abs])
  apply simp
  apply simp
  done

lemma setL2_mult_ineq_lemma:
  fixes a b c d :: real
  shows "2 * (a * c) * (b * d) \<le> a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior>"
proof -
  have "0 \<le> (a * d - b * c)\<twosuperior>" by simp
  also have "\<dots> = a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior> - 2 * (a * d) * (b * c)"
    by (simp only: power2_diff power_mult_distrib)
  also have "\<dots> = a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior> - 2 * (a * c) * (b * d)"
    by simp
  finally show "2 * (a * c) * (b * d) \<le> a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior>"
    by simp
qed

lemma setL2_mult_ineq: "(\<Sum>i\<in>A. \<bar>f i\<bar> * \<bar>g i\<bar>) \<le> setL2 f A * setL2 g A"
  apply (cases "finite A")
  apply (induct set: finite)
  apply simp
  apply (rule power2_le_imp_le, simp)
  apply (rule order_trans)
  apply (rule power_mono)
  apply (erule add_left_mono)
  apply (simp add: mult_nonneg_nonneg setsum_nonneg)
  apply (simp add: power2_sum)
  apply (simp add: power_mult_distrib)
  apply (simp add: distrib_left distrib_right)
  apply (rule ord_le_eq_trans)
  apply (rule setL2_mult_ineq_lemma)
  apply simp
  apply (intro mult_nonneg_nonneg setL2_nonneg)
  apply simp
  done

lemma member_le_setL2: "\<lbrakk>finite A; i \<in> A\<rbrakk> \<Longrightarrow> f i \<le> setL2 f A"
  apply (rule_tac s="insert i (A - {i})" and t="A" in subst)
  apply fast
  apply (subst setL2_insert)
  apply simp
  apply simp
  apply simp
  done

end
