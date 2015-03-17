(*  Title:     HOL/Inequalities.thy
    Author:    Tobias Nipkow
    Author:    Johannes Hölzl
*)

theory Inequalities
  imports Real_Vector_Spaces
begin

lemma setsum_triangle_reindex:
  fixes n :: nat
  shows "(\<Sum>(i,j)\<in>{(i,j). i+j < n}. f i j) = (\<Sum>k<n. \<Sum>i\<le>k. f i (k - i))"
  apply (simp add: setsum.Sigma)
  apply (rule setsum.reindex_bij_witness[where j="\<lambda>(i, j). (i+j, i)" and i="\<lambda>(k, i). (i, k - i)"])
  apply auto
  done

lemma gauss_sum_div2: "(2::'a::semiring_div) \<noteq> 0 \<Longrightarrow>
  setsum of_nat {1..n} = of_nat n * (of_nat n + 1) div (2::'a)"
using gauss_sum[where n=n and 'a = 'a,symmetric] by auto

lemma Setsum_Icc_int: assumes "0 \<le> m" and "(m::int) \<le> n"
shows "\<Sum> {m..n} = (n*(n+1) - m*(m-1)) div 2"
proof-
  { fix k::int assume "k\<ge>0"
    hence "\<Sum> {1..k::int} = k * (k+1) div 2"
      by (rule gauss_sum_div2[where 'a = int, transferred]) simp
  } note 1 = this
  have "{m..n} = {0..n} - {0..m-1}" using `m\<ge>0` by auto
  hence "\<Sum>{m..n} = \<Sum>{0..n} - \<Sum>{0..m-1}" using assms
    by (force intro!: setsum_diff)
  also have "{0..n} = {0} Un {1..n}" using assms by auto
  also have "\<Sum>({0} \<union> {1..n}) = \<Sum>{1..n}" by(simp add: setsum.union_disjoint)
  also have "\<dots> = n * (n+1) div 2" by(rule 1[OF order_trans[OF assms]])
  also have "{0..m-1} = (if m=0 then {} else {0} Un {1..m-1})"
    using assms by auto
  also have "\<Sum> \<dots> = m*(m-1) div 2" using `m\<ge>0` by(simp add: 1 mult.commute)
  also have "n*(n+1) div 2 - m*(m-1) div 2 = (n*(n+1) - m*(m-1)) div 2"
    apply(subgoal_tac "even(n*(n+1)) \<and> even(m*(m-1))")
    by (auto (*simp: even_def[symmetric]*))
  finally show ?thesis .
qed

lemma Setsum_Icc_nat: assumes "(m::nat) \<le> n"
shows "\<Sum> {m..n} = (n*(n+1) - m*(m-1)) div 2"
proof -
  have "m*(m-1) \<le> n*(n + 1)"
   using assms by (meson diff_le_self order_trans le_add1 mult_le_mono)
  hence "int(\<Sum> {m..n}) = int((n*(n+1) - m*(m-1)) div 2)" using assms
    by (auto simp add: Setsum_Icc_int[transferred, OF _ assms] zdiv_int int_mult
      split: zdiff_int_split)
  thus ?thesis by simp
qed

lemma Setsum_Ico_nat: assumes "(m::nat) \<le> n"
shows "\<Sum> {m..<n} = (n*(n-1) - m*(m-1)) div 2"
proof cases
  assume "m < n"
  hence "{m..<n} = {m..n-1}" by auto
  hence "\<Sum>{m..<n} = \<Sum>{m..n-1}" by simp
  also have "\<dots> = (n*(n-1) - m*(m-1)) div 2"
    using assms `m < n` by (simp add: Setsum_Icc_nat mult.commute)
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
    unfolding one_add_one[symmetric] algebra_simps
    by (simp add: algebra_simps setsum_subtractf setsum.distrib setsum.commute[of "\<lambda>i j. a i * b j"] setsum_right_distrib)
  also
  { fix i j::nat assume "i<n" "j<n"
    hence "a i - a j \<le> 0 \<and> b i - b j \<ge> 0 \<or> a i - a j \<ge> 0 \<and> b i - b j \<le> 0"
      using assms by (cases "i \<le> j") (auto simp: algebra_simps)
  } hence "?S \<le> 0"
    by (auto intro!: setsum_nonpos simp: mult_le_0_iff)
       (auto simp: field_simps)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma Chebyshev_sum_upper_nat:
  fixes a b :: "nat \<Rightarrow> nat"
  shows "(\<And>i j. \<lbrakk> i\<le>j; j<n \<rbrakk> \<Longrightarrow> a i \<le> a j) \<Longrightarrow>
         (\<And>i j. \<lbrakk> i\<le>j; j<n \<rbrakk> \<Longrightarrow> b i \<ge> b j) \<Longrightarrow>
    n * (\<Sum>i=0..<n. a i * b i) \<le> (\<Sum>i=0..<n. a i) * (\<Sum>i=0..<n. b i)"
using Chebyshev_sum_upper[where 'a=real, of n a b]
by (simp del: real_of_nat_mult real_of_nat_setsum
  add: real_of_nat_mult[symmetric] real_of_nat_setsum[symmetric] real_of_nat_def[symmetric])

end
