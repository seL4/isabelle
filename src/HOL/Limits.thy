(*  Title       : Limits.thy
    Author      : Brian Huffman
*)

header {* Filters and Limits *}

theory Limits
imports RealVector RComplete
begin

subsection {* Filters *}

typedef (open) 'a filter =
  "{f :: ('a \<Rightarrow> bool) \<Rightarrow> bool. f (\<lambda>x. True)
    \<and> (\<forall>P Q. (\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> f P \<longrightarrow> f Q)
    \<and> (\<forall>P Q. f P \<longrightarrow> f Q \<longrightarrow> f (\<lambda>x. P x \<and> Q x))}"
proof
  show "(\<lambda>P. True) \<in> ?filter" by simp
qed

definition
  eventually :: "('a \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "eventually P F \<longleftrightarrow> Rep_filter F P"

lemma eventually_True [simp]: "eventually (\<lambda>x. True) F"
unfolding eventually_def using Rep_filter [of F] by blast

lemma eventually_mono:
  "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> eventually P F \<Longrightarrow> eventually Q F"
unfolding eventually_def using Rep_filter [of F] by blast

lemma eventually_conj:
  "\<lbrakk>eventually (\<lambda>x. P x) F; eventually (\<lambda>x. Q x) F\<rbrakk>
    \<Longrightarrow> eventually (\<lambda>x. P x \<and> Q x) F"
unfolding eventually_def using Rep_filter [of F] by blast

lemma eventually_mp:
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  assumes "eventually (\<lambda>x. P x) F"
  shows "eventually (\<lambda>x. Q x) F"
proof (rule eventually_mono)
  show "\<forall>x. (P x \<longrightarrow> Q x) \<and> P x \<longrightarrow> Q x" by simp
  show "eventually (\<lambda>x. (P x \<longrightarrow> Q x) \<and> P x) F"
    using assms by (rule eventually_conj)
qed

lemma eventually_rev_mp:
  assumes "eventually (\<lambda>x. P x) F"
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  shows "eventually (\<lambda>x. Q x) F"
using assms(2) assms(1) by (rule eventually_mp)

lemma eventually_conj_iff:
  "eventually (\<lambda>x. P x \<and> Q x) net \<longleftrightarrow> eventually P net \<and> eventually Q net"
by (auto intro: eventually_conj elim: eventually_rev_mp)

lemma eventually_Abs_filter:
  assumes "f (\<lambda>x. True)"
  assumes "\<And>P Q. (\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> f P \<Longrightarrow> f Q"
  assumes "\<And>P Q. f P \<Longrightarrow> f Q \<Longrightarrow> f (\<lambda>x. P x \<and> Q x)"
  shows "eventually P (Abs_filter f) \<longleftrightarrow> f P"
unfolding eventually_def using assms
by (subst Abs_filter_inverse, auto)

lemma filter_ext:
  "(\<And>P. eventually P F \<longleftrightarrow> eventually P F') \<Longrightarrow> F = F'"
unfolding eventually_def
by (simp add: Rep_filter_inject [THEN iffD1] ext)

lemma eventually_elim1:
  assumes "eventually (\<lambda>i. P i) F"
  assumes "\<And>i. P i \<Longrightarrow> Q i"
  shows "eventually (\<lambda>i. Q i) F"
using assms by (auto elim!: eventually_rev_mp)

lemma eventually_elim2:
  assumes "eventually (\<lambda>i. P i) F"
  assumes "eventually (\<lambda>i. Q i) F"
  assumes "\<And>i. P i \<Longrightarrow> Q i \<Longrightarrow> R i"
  shows "eventually (\<lambda>i. R i) F"
using assms by (auto elim!: eventually_rev_mp)


subsection {* Convergence to Zero *}

definition
  Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "Zfun S F = (\<forall>r>0. eventually (\<lambda>i. norm (S i) < r) F)"

lemma ZfunI:
  "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>i. norm (S i) < r) F) \<Longrightarrow> Zfun S F"
unfolding Zfun_def by simp

lemma ZfunD:
  "\<lbrakk>Zfun S F; 0 < r\<rbrakk> \<Longrightarrow> eventually (\<lambda>i. norm (S i) < r) F"
unfolding Zfun_def by simp

lemma Zfun_zero: "Zfun (\<lambda>i. 0) F"
unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>i. norm (S i)) F = Zfun (\<lambda>i. S i) F"
unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes X: "Zfun X F"
  assumes Y: "\<And>n. norm (Y n) \<le> norm (X n) * K"
  shows "Zfun (\<lambda>n. Y n) F"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZfunI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then have "eventually (\<lambda>i. norm (X i) < r / K) F"
      using ZfunD [OF X] by fast
    then show "eventually (\<lambda>i. norm (Y i) < r) F"
    proof (rule eventually_elim1)
      fix i assume "norm (X i) < r / K"
      hence "norm (X i) * K < r"
        by (simp add: pos_less_divide_eq K)
      thus "norm (Y i) < r"
        by (simp add: order_le_less_trans [OF Y])
    qed
  qed
next
  assume "\<not> 0 < K"
  hence K: "K \<le> 0" by (simp only: not_less)
  {
    fix i
    have "norm (Y i) \<le> norm (X i) * K" by (rule Y)
    also have "\<dots> \<le> norm (X i) * 0"
      using K norm_ge_zero by (rule mult_left_mono)
    finally have "norm (Y i) = 0" by simp
  }
  thus ?thesis by (simp add: Zfun_zero)
qed

lemma Zfun_le: "\<lbrakk>Zfun Y F; \<forall>n. norm (X n) \<le> norm (Y n)\<rbrakk> \<Longrightarrow> Zfun X F"
by (erule_tac K="1" in Zfun_imp_Zfun, simp)

lemma Zfun_add:
  assumes X: "Zfun X F" and Y: "Zfun Y F"
  shows "Zfun (\<lambda>n. X n + Y n) F"
proof (rule ZfunI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  have "eventually (\<lambda>i. norm (X i) < r/2) F"
    using X r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>i. norm (Y i) < r/2) F"
    using Y r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>i. norm (X i + Y i) < r) F"
  proof (rule eventually_elim2)
    fix i
    assume *: "norm (X i) < r/2" "norm (Y i) < r/2"
    have "norm (X i + Y i) \<le> norm (X i) + norm (Y i)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using * by (rule add_strict_mono)
    finally show "norm (X i + Y i) < r"
      by simp
  qed
qed

lemma Zfun_minus: "Zfun X F \<Longrightarrow> Zfun (\<lambda>i. - X i) F"
unfolding Zfun_def by simp

lemma Zfun_diff: "\<lbrakk>Zfun X F; Zfun Y F\<rbrakk> \<Longrightarrow> Zfun (\<lambda>i. X i - Y i) F"
by (simp only: diff_minus Zfun_add Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes X: "Zfun X F"
  shows "Zfun (\<lambda>n. f (X n)) F"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  with X show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes X: "Zfun X F"
  assumes Y: "Zfun Y F"
  shows "Zfun (\<lambda>n. X n ** Y n) F"
proof (rule ZfunI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>i. norm (X i) < r) F"
    using X r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>i. norm (Y i) < inverse K) F"
    using Y K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>i. norm (X i ** Y i) < r) F"
  proof (rule eventually_elim2)
    fix i
    assume *: "norm (X i) < r" "norm (Y i) < inverse K"
    have "norm (X i ** Y i) \<le> norm (X i) * norm (Y i) * K"
      by (rule norm_le)
    also have "norm (X i) * norm (Y i) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero * K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show "norm (X i ** Y i) < r" .
  qed
qed

lemma (in bounded_bilinear) Zfun_left:
  "Zfun X F \<Longrightarrow> Zfun (\<lambda>n. X n ** a) F"
by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right:
  "Zfun X F \<Longrightarrow> Zfun (\<lambda>n. a ** X n) F"
by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = mult.Zfun
lemmas Zfun_mult_right = mult.Zfun_right
lemmas Zfun_mult_left = mult.Zfun_left


subsection{* Limits *}

definition
  tendsto :: "('a \<Rightarrow> 'b::metric_space) \<Rightarrow> 'b \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "tendsto f l net \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"

lemma tendstoI:
  "(\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) net)
    \<Longrightarrow> tendsto f l net"
  unfolding tendsto_def by auto

lemma tendstoD:
  "tendsto f l net \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) net"
  unfolding tendsto_def by auto

lemma tendsto_Zfun_iff: "tendsto (\<lambda>n. X n) L F = Zfun (\<lambda>n. X n - L) F"
by (simp only: tendsto_def Zfun_def dist_norm)

lemma tendsto_const: "tendsto (\<lambda>n. k) k F"
by (simp add: tendsto_def)

lemma tendsto_norm:
  fixes a :: "'a::real_normed_vector"
  shows "tendsto X a F \<Longrightarrow> tendsto (\<lambda>n. norm (X n)) (norm a) F"
apply (simp add: tendsto_def dist_norm, safe)
apply (drule_tac x="e" in spec, safe)
apply (erule eventually_elim1)
apply (erule order_le_less_trans [OF norm_triangle_ineq3])
done

lemma add_diff_add:
  fixes a b c d :: "'a::ab_group_add"
  shows "(a + c) - (b + d) = (a - b) + (c - d)"
by simp

lemma minus_diff_minus:
  fixes a b :: "'a::ab_group_add"
  shows "(- a) - (- b) = - (a - b)"
by simp

lemma tendsto_add:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>tendsto X a F; tendsto Y b F\<rbrakk> \<Longrightarrow> tendsto (\<lambda>n. X n + Y n) (a + b) F"
by (simp only: tendsto_Zfun_iff add_diff_add Zfun_add)

lemma tendsto_minus:
  fixes a :: "'a::real_normed_vector"
  shows "tendsto X a F \<Longrightarrow> tendsto (\<lambda>n. - X n) (- a) F"
by (simp only: tendsto_Zfun_iff minus_diff_minus Zfun_minus)

lemma tendsto_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "tendsto (\<lambda>n. - X n) (- a) F \<Longrightarrow> tendsto X a F"
by (drule tendsto_minus, simp)

lemma tendsto_diff:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>tendsto X a F; tendsto Y b F\<rbrakk> \<Longrightarrow> tendsto (\<lambda>n. X n - Y n) (a - b) F"
by (simp add: diff_minus tendsto_add tendsto_minus)

lemma (in bounded_linear) tendsto:
  "tendsto X a F \<Longrightarrow> tendsto (\<lambda>n. f (X n)) (f a) F"
by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_bilinear) tendsto:
  "\<lbrakk>tendsto X a F; tendsto Y b F\<rbrakk> \<Longrightarrow> tendsto (\<lambda>n. X n ** Y n) (a ** b) F"
by (simp only: tendsto_Zfun_iff prod_diff_prod
               Zfun_add Zfun Zfun_left Zfun_right)

end
