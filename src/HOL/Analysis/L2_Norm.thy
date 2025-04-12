(*  Title:      HOL/Analysis/L2_Norm.thy
    Author:     Brian Huffman, Portland State University
*)

chapter \<open>Linear Algebra\<close>

theory L2_Norm
imports Complex_Main
begin

section \<open>L2 Norm\<close>

definition\<^marker>\<open>tag important\<close> L2_set :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
"L2_set f A = sqrt (\<Sum>i\<in>A. (f i)\<^sup>2)"

lemma L2_set_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> L2_set f A = L2_set g B"
  unfolding L2_set_def by simp

lemma L2_set_cong_simp:
  "\<lbrakk>A = B; \<And>x. x \<in> B =simp=> f x = g x\<rbrakk> \<Longrightarrow> L2_set f A = L2_set g B"
  unfolding L2_set_def simp_implies_def by simp

lemma L2_set_infinite [simp]: "\<not> finite A \<Longrightarrow> L2_set f A = 0"
  unfolding L2_set_def by simp

lemma L2_set_empty [simp]: "L2_set f {} = 0"
  unfolding L2_set_def by simp

lemma L2_set_insert [simp]:
  "\<lbrakk>finite F; a \<notin> F\<rbrakk> \<Longrightarrow>
    L2_set f (insert a F) = sqrt ((f a)\<^sup>2 + (L2_set f F)\<^sup>2)"
  unfolding L2_set_def by (simp add: sum_nonneg)

lemma L2_set_nonneg [simp]: "0 \<le> L2_set f A"
  unfolding L2_set_def by (simp add: sum_nonneg)

lemma L2_set_0': "\<forall>a\<in>A. f a = 0 \<Longrightarrow> L2_set f A = 0"
  unfolding L2_set_def by simp

lemma L2_set_constant: "L2_set (\<lambda>x. y) A = sqrt (of_nat (card A)) * \<bar>y\<bar>"
  unfolding L2_set_def by (simp add: real_sqrt_mult)

lemma L2_set_mono:
  assumes "\<And>i. i \<in> K \<Longrightarrow> f i \<le> g i"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 \<le> f i"
  shows "L2_set f K \<le> L2_set g K"
  unfolding L2_set_def
  by (simp add: sum_nonneg sum_mono power_mono assms)

lemma L2_set_strict_mono:
  assumes "finite K" and "K \<noteq> {}"
  assumes "\<And>i. i \<in> K \<Longrightarrow> f i < g i"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 \<le> f i"
  shows "L2_set f K < L2_set g K"
  unfolding L2_set_def
  by (simp add: sum_strict_mono power_strict_mono assms)

lemma L2_set_right_distrib:
  "0 \<le> r \<Longrightarrow> r * L2_set f A = L2_set (\<lambda>x. r * f x) A"
  unfolding L2_set_def
  apply (simp add: power_mult_distrib)
  apply (simp add: sum_distrib_left [symmetric])
  apply (simp add: real_sqrt_mult sum_nonneg)
  done

lemma L2_set_left_distrib:
  "0 \<le> r \<Longrightarrow> L2_set f A * r = L2_set (\<lambda>x. f x * r) A"
  unfolding L2_set_def power_mult_distrib
  by (simp add: real_sqrt_mult sum_nonneg flip: sum_distrib_right)

lemma L2_set_eq_0_iff: "finite A \<Longrightarrow> L2_set f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  unfolding L2_set_def
  by (simp add: sum_nonneg sum_nonneg_eq_0_iff)

proposition L2_set_triangle_ineq:
  "L2_set (\<lambda>i. f i + g i) A \<le> L2_set f A + L2_set g A"
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
    hence "sqrt ((f x + g x)\<^sup>2 + (L2_set (\<lambda>i. f i + g i) F)\<^sup>2) \<le>
           sqrt ((f x + g x)\<^sup>2 + (L2_set f F + L2_set g F)\<^sup>2)"
      by (intro real_sqrt_le_mono add_left_mono power_mono insert
                L2_set_nonneg add_increasing zero_le_power2)
    also have
      "\<dots> \<le> sqrt ((f x)\<^sup>2 + (L2_set f F)\<^sup>2) + sqrt ((g x)\<^sup>2 + (L2_set g F)\<^sup>2)"
      by (rule real_sqrt_sum_squares_triangle_ineq)
    finally show ?case
      using insert by simp
  qed
qed

lemma L2_set_le_sum:
  "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> L2_set f A \<le> sum f A"
proof (induction A rule: infinite_finite_induct)
  case (insert a A)
  with order_trans [OF sqrt_sum_squares_le_sum] show ?case by force
qed auto

lemma L2_set_le_sum_abs: "L2_set f A \<le> (\<Sum>i\<in>A. \<bar>f i\<bar>)"
proof (induction A rule: infinite_finite_induct)
  case (insert a A)
  with order_trans [OF sqrt_sum_squares_le_sum_abs] show ?case by force
qed auto

lemma L2_set_mult_ineq: "(\<Sum>i\<in>A. \<bar>f i\<bar> * \<bar>g i\<bar>) \<le> L2_set f A * L2_set g A"
proof (induction A rule: infinite_finite_induct)
  case (insert a A)
  have "(\<bar>f a\<bar> * \<bar>g a\<bar> + (\<Sum>i\<in>A. \<bar>f i\<bar> * \<bar>g i\<bar>))\<^sup>2
      \<le> (\<bar>f a\<bar> * \<bar>g a\<bar> + L2_set f A * L2_set g A)\<^sup>2"
    by (simp add: insert.IH sum_nonneg)
  also have "... \<le> ((f a)\<^sup>2 + (L2_set f A)\<^sup>2) * ((g a)\<^sup>2 + (L2_set g A)\<^sup>2)"
    using L2_set_mult_ineq_lemma [of "L2_set f A" "L2_set g A" "\<bar>f a\<bar>" "\<bar>g a\<bar>"]
    by (simp add: power2_eq_square algebra_simps)
  also have "... = (sqrt ((f a)\<^sup>2 + (L2_set f A)\<^sup>2) * sqrt ((g a)\<^sup>2 + (L2_set g A)\<^sup>2))\<^sup>2"
    using real_sqrt_mult real_sqrt_sum_squares_mult_squared_eq by presburger
  finally have "(\<bar>f a\<bar> * \<bar>g a\<bar> + (\<Sum>i\<in>A. \<bar>f i\<bar> * \<bar>g i\<bar>))\<^sup>2
              \<le> (sqrt ((f a)\<^sup>2 + (L2_set f A)\<^sup>2) * sqrt ((g a)\<^sup>2 + (L2_set g A)\<^sup>2))\<^sup>2" .
  then
  show ?case
    using power2_le_imp_le insert.hyps by fastforce
qed auto

lemma member_le_L2_set: "\<lbrakk>finite A; i \<in> A\<rbrakk> \<Longrightarrow> f i \<le> L2_set f A"
  unfolding L2_set_def
  by (auto intro!: member_le_sum real_le_rsqrt)

end
