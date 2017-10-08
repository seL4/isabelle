(*  Title:     HOL/Inequalities.thy
    Author:    Tobias Nipkow
    Author:    Johannes Hölzl
*)

theory Inequalities
  imports Real_Vector_Spaces
begin

lemma Sum_Icc_int: "(m::int) \<le> n \<Longrightarrow> \<Sum> {m..n} = (n*(n+1) - m*(m-1)) div 2"
proof(induct i == "nat(n-m)" arbitrary: m n)
  case 0
  hence "m = n" by arith
  thus ?case by (simp add: algebra_simps)
next
  case (Suc i)
  have 0: "i = nat((n-1) - m)" "m \<le> n-1" using Suc(2,3) by arith+
  have "\<Sum> {m..n} = \<Sum> {m..1+(n-1)}" by simp
  also have "\<dots> = \<Sum> {m..n-1} + n" using \<open>m \<le> n\<close>
    by(subst atLeastAtMostPlus1_int_conv) simp_all
  also have "\<dots> = ((n-1)*(n-1+1) - m*(m-1)) div 2 + n"
    by(simp add: Suc(1)[OF 0])
  also have "\<dots> = ((n-1)*(n-1+1) - m*(m-1) + 2*n) div 2" by simp
  also have "\<dots> = (n*(n+1) - m*(m-1)) div 2" by(simp add: algebra_simps)
  finally show ?case .
qed

lemma Sum_Icc_nat: assumes "(m::nat) \<le> n"
shows "\<Sum> {m..n} = (n*(n+1) - m*(m-1)) div 2"
proof -
  have "m*(m-1) \<le> n*(n + 1)"
   using assms by (meson diff_le_self order_trans le_add1 mult_le_mono)
  hence "int(\<Sum> {m..n}) = int((n*(n+1) - m*(m-1)) div 2)" using assms
    by (auto simp: Sum_Icc_int[transferred, OF assms] zdiv_int of_nat_mult simp del: of_nat_sum
          split: zdiff_int_split)
  thus ?thesis
    using of_nat_eq_iff by blast
qed

lemma Sum_Ico_nat: assumes "(m::nat) \<le> n"
shows "\<Sum> {m..<n} = (n*(n-1) - m*(m-1)) div 2"
proof cases
  assume "m < n"
  hence "{m..<n} = {m..n-1}" by auto
  hence "\<Sum>{m..<n} = \<Sum>{m..n-1}" by simp
  also have "\<dots> = (n*(n-1) - m*(m-1)) div 2"
    using assms \<open>m < n\<close> by (simp add: Sum_Icc_nat mult.commute)
  finally show ?thesis .
next
  assume "\<not> m < n" with assms show ?thesis by simp
qed

lemma Chebyshev_sum_upper:
  fixes a b::"nat \<Rightarrow> 'a::linordered_idom"
  assumes "\<And>i j. i \<le> j \<Longrightarrow> j < n \<Longrightarrow> a i \<le> a j"
  assumes "\<And>i j. i \<le> j \<Longrightarrow> j < n \<Longrightarrow> b i \<ge> b j"
  shows "of_nat n * (\<Sum>k=0..<n. a k * b k) \<le> (\<Sum>k=0..<n. a k) * (\<Sum>k=0..<n. b k)"
proof -
  let ?S = "(\<Sum>j=0..<n. (\<Sum>k=0..<n. (a j - a k) * (b j - b k)))"
  have "2 * (of_nat n * (\<Sum>j=0..<n. (a j * b j)) - (\<Sum>j=0..<n. b j) * (\<Sum>k=0..<n. a k)) = ?S"
    by (simp only: one_add_one[symmetric] algebra_simps)
      (simp add: algebra_simps sum_subtractf sum.distrib sum.swap[of "\<lambda>i j. a i * b j"] sum_distrib_left)
  also
  { fix i j::nat assume "i<n" "j<n"
    hence "a i - a j \<le> 0 \<and> b i - b j \<ge> 0 \<or> a i - a j \<ge> 0 \<and> b i - b j \<le> 0"
      using assms by (cases "i \<le> j") (auto simp: algebra_simps)
  } then have "?S \<le> 0"
    by (auto intro!: sum_nonpos simp: mult_le_0_iff)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma Chebyshev_sum_upper_nat:
  fixes a b :: "nat \<Rightarrow> nat"
  shows "(\<And>i j. \<lbrakk> i\<le>j; j<n \<rbrakk> \<Longrightarrow> a i \<le> a j) \<Longrightarrow>
         (\<And>i j. \<lbrakk> i\<le>j; j<n \<rbrakk> \<Longrightarrow> b i \<ge> b j) \<Longrightarrow>
    n * (\<Sum>i=0..<n. a i * b i) \<le> (\<Sum>i=0..<n. a i) * (\<Sum>i=0..<n. b i)"
using Chebyshev_sum_upper[where 'a=real, of n a b]
by (simp del: of_nat_mult of_nat_sum  add: of_nat_mult[symmetric] of_nat_sum[symmetric])

end
