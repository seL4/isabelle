theory NthRoot_Limits
  imports Complex_Main
begin

lemma LIMSEQ_root: "(\<lambda>n. root n n) ----> 1"
proof -
  def x \<equiv> "\<lambda>n. root n n - 1"
  have "x ----> sqrt 0"
  proof (rule tendsto_sandwich[OF _ _ tendsto_const])
    show "(\<lambda>x. sqrt (2 / x)) ----> sqrt 0"
      by (intro tendsto_intros tendsto_divide_0[OF tendsto_const] filterlim_mono[OF filterlim_real_sequentially])
         (simp_all add: at_infinity_eq_at_top_bot)
    { fix n :: nat assume "2 < n"
      have "1 + (real (n - 1) * n) / 2 * x n^2 = 1 + of_nat (n choose 2) * x n^2"
        using `2 < n` unfolding gbinomial_def binomial_gbinomial
        by (simp add: atLeast0AtMost atMost_Suc field_simps real_of_nat_diff numeral_2_eq_2 real_eq_of_nat[symmetric])
      also have "\<dots> \<le> (\<Sum>k\<in>{0, 2}. of_nat (n choose k) * x n^k)"
        by (simp add: x_def)
      also have "\<dots> \<le> (\<Sum>k=0..n. of_nat (n choose k) * x n^k)"
        using `2 < n` by (intro setsum_mono2) (auto intro!: mult_nonneg_nonneg zero_le_power simp: x_def le_diff_eq)
      also have "\<dots> = (x n + 1) ^ n"
        by (simp add: binomial_ring)
      also have "\<dots> = n"
        using `2 < n` by (simp add: x_def)
      finally have "real (n - 1) * (real n / 2 * (x n)\<^sup>2) \<le> real (n - 1) * 1"
        by simp
      then have "(x n)\<^sup>2 \<le> 2 / real n"
        using `2 < n` unfolding mult_le_cancel_left by (simp add: field_simps)
      from real_sqrt_le_mono[OF this] have "x n \<le> sqrt (2 / real n)"
        by simp }
    then show "eventually (\<lambda>n. x n \<le> sqrt (2 / real n)) sequentially"
      by (auto intro!: exI[of _ 3] simp: eventually_sequentially)
    show "eventually (\<lambda>n. sqrt 0 \<le> x n) sequentially"
      by (auto intro!: exI[of _ 1] simp: eventually_sequentially le_diff_eq x_def)
  qed
  from tendsto_add[OF this tendsto_const[of 1]] show ?thesis
    by (simp add: x_def)
qed

lemma LIMSEQ_root_const:
  assumes "0 < c"
  shows "(\<lambda>n. root n c) ----> 1"
proof -
  { fix c :: real assume "1 \<le> c"
    def x \<equiv> "\<lambda>n. root n c - 1"
    have "x ----> 0"
    proof (rule tendsto_sandwich[OF _ _ tendsto_const])
      show "(\<lambda>n. c / n) ----> 0"
        by (intro tendsto_divide_0[OF tendsto_const] filterlim_mono[OF filterlim_real_sequentially])
           (simp_all add: at_infinity_eq_at_top_bot)
      { fix n :: nat assume "1 < n"
        have "1 + x n * n = 1 + of_nat (n choose 1) * x n^1"
          using `1 < n` unfolding gbinomial_def binomial_gbinomial by (simp add: real_eq_of_nat[symmetric])
        also have "\<dots> \<le> (\<Sum>k\<in>{0, 1}. of_nat (n choose k) * x n^k)"
          by (simp add: x_def)
        also have "\<dots> \<le> (\<Sum>k=0..n. of_nat (n choose k) * x n^k)"
          using `1 < n` `1 \<le> c` by (intro setsum_mono2) (auto intro!: mult_nonneg_nonneg zero_le_power simp: x_def le_diff_eq)
        also have "\<dots> = (x n + 1) ^ n"
          by (simp add: binomial_ring)
        also have "\<dots> = c"
          using `1 < n` `1 \<le> c` by (simp add: x_def)
        finally have "x n \<le> c / n"
          using `1 \<le> c` `1 < n` by (simp add: field_simps) }
      then show "eventually (\<lambda>n. x n \<le> c / n) sequentially"
        by (auto intro!: exI[of _ 3] simp: eventually_sequentially)
      show "eventually (\<lambda>n. 0 \<le> x n) sequentially"
        using `1 \<le> c` by (auto intro!: exI[of _ 1] simp: eventually_sequentially le_diff_eq x_def)
    qed
    from tendsto_add[OF this tendsto_const[of 1]] have "(\<lambda>n. root n c) ----> 1"
      by (simp add: x_def) }
  note ge_1 = this

  show ?thesis
  proof cases
    assume "1 \<le> c" with ge_1 show ?thesis by blast
  next
    assume "\<not> 1 \<le> c"
    with `0 < c` have "1 \<le> 1 / c"
      by simp
    then have "(\<lambda>n. 1 / root n (1 / c)) ----> 1 / 1"
      by (intro tendsto_divide tendsto_const ge_1 `1 \<le> 1 / c` one_neq_zero)
    then show ?thesis
      by (rule filterlim_cong[THEN iffD1, rotated 3])
         (auto intro!: exI[of _ 1] simp: eventually_sequentially real_root_divide)
  qed
qed

end
