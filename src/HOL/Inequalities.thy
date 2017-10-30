(*  Title:     HOL/Inequalities.thy
    Author:    Tobias Nipkow
    Author:    Johannes Hölzl
*)

theory Inequalities
  imports Real_Vector_Spaces
begin

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
