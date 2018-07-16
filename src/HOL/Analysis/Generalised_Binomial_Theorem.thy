(*  Title:    HOL/Analysis/Generalised_Binomial_Theorem.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Generalised Binomial Theorem\<close>

text \<open>
  The proof of the Generalised Binomial Theorem and related results.
  We prove the generalised binomial theorem for complex numbers, following the proof at:
  \url{https://proofwiki.org/wiki/Binomial_Theorem/General_Binomial_Theorem}
\<close>

theory Generalised_Binomial_Theorem
imports
  Complex_Main
  Complex_Transcendental
  Summation_Tests
begin

lemma gbinomial_ratio_limit:
  fixes a :: "'a :: real_normed_field"
  assumes "a \<notin> \<nat>"
  shows "(\<lambda>n. (a gchoose n) / (a gchoose Suc n)) \<longlonglongrightarrow> -1"
proof (rule Lim_transform_eventually)
  let ?f = "\<lambda>n. inverse (a / of_nat (Suc n) - of_nat n / of_nat (Suc n))"
  from eventually_gt_at_top[of "0::nat"]
    show "eventually (\<lambda>n. ?f n = (a gchoose n) /(a gchoose Suc n)) sequentially"
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    then obtain q where q: "n = Suc q" by (cases n) blast
    let ?P = "\<Prod>i=0..<n. a - of_nat i"
    from n have "(a gchoose n) / (a gchoose Suc n) = (of_nat (Suc n) :: 'a) *
                   (?P / (\<Prod>i=0..n. a - of_nat i))"
      by (simp add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)
    also from q have "(\<Prod>i=0..n. a - of_nat i) = ?P * (a - of_nat n)"
      by (simp add: prod.atLeast0_atMost_Suc atLeastLessThanSuc_atLeastAtMost)
    also have "?P / \<dots> = (?P / ?P) / (a - of_nat n)" by (rule divide_divide_eq_left[symmetric])
    also from assms have "?P / ?P = 1" by auto
    also have "of_nat (Suc n) * (1 / (a - of_nat n)) =
                   inverse (inverse (of_nat (Suc n)) * (a - of_nat n))" by (simp add: field_simps)
    also have "inverse (of_nat (Suc n)) * (a - of_nat n) = a / of_nat (Suc n) - of_nat n / of_nat (Suc n)"
      by (simp add: field_simps del: of_nat_Suc)
    finally show "?f n = (a gchoose n) / (a gchoose Suc n)" by simp
  qed

  have "(\<lambda>n. norm a / (of_nat (Suc n))) \<longlonglongrightarrow> 0"
    unfolding divide_inverse
    by (intro tendsto_mult_right_zero LIMSEQ_inverse_real_of_nat)
  hence "(\<lambda>n. a / of_nat (Suc n)) \<longlonglongrightarrow> 0"
    by (subst tendsto_norm_zero_iff[symmetric]) (simp add: norm_divide del: of_nat_Suc)
  hence "?f \<longlonglongrightarrow> inverse (0 - 1)"
    by (intro tendsto_inverse tendsto_diff LIMSEQ_n_over_Suc_n) simp_all
  thus "?f \<longlonglongrightarrow> -1" by simp
qed

lemma conv_radius_gchoose:
  fixes a :: "'a :: {real_normed_field,banach}"
  shows "conv_radius (\<lambda>n. a gchoose n) = (if a \<in> \<nat> then \<infinity> else 1)"
proof (cases "a \<in> \<nat>")
  assume a: "a \<in> \<nat>"
  have "eventually (\<lambda>n. (a gchoose n) = 0) sequentially"
    using eventually_gt_at_top[of "nat \<lfloor>norm a\<rfloor>"]
    by eventually_elim (insert a, auto elim!: Nats_cases simp: binomial_gbinomial[symmetric])
  from conv_radius_cong'[OF this] a show ?thesis by simp
next
  assume a: "a \<notin> \<nat>"
  from tendsto_norm[OF gbinomial_ratio_limit[OF this]]
    have "conv_radius (\<lambda>n. a gchoose n) = 1"
    by (intro conv_radius_ratio_limit_nonzero[of _ 1]) (simp_all add: norm_divide)
  with a show ?thesis by simp
qed

theorem gen_binomial_complex:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "(\<lambda>n. (a gchoose n) * z^n) sums (1 + z) powr a"
proof -
  define K where "K = 1 - (1 - norm z) / 2"
  from assms have K: "K > 0" "K < 1" "norm z < K"
     unfolding K_def by (auto simp: field_simps intro!: add_pos_nonneg)
  let ?f = "\<lambda>n. a gchoose n" and ?f' = "diffs (\<lambda>n. a gchoose n)"
  have summable_strong: "summable (\<lambda>n. ?f n * z ^ n)" if "norm z < 1" for z using that
    by (intro summable_in_conv_radius) (simp_all add: conv_radius_gchoose)
  with K have summable: "summable (\<lambda>n. ?f n * z ^ n)" if "norm z < K" for z using that by auto
  hence summable': "summable (\<lambda>n. ?f' n * z ^ n)" if "norm z < K" for z using that
    by (intro termdiff_converges[of _ K]) simp_all

  define f f' where [abs_def]: "f z = (\<Sum>n. ?f n * z ^ n)" "f' z = (\<Sum>n. ?f' n * z ^ n)" for z
  {
    fix z :: complex assume z: "norm z < K"
    from summable_mult2[OF summable'[OF z], of z]
      have summable1: "summable (\<lambda>n. ?f' n * z ^ Suc n)" by (simp add: mult_ac)
    hence summable2: "summable (\<lambda>n. of_nat n * ?f n * z^n)"
      unfolding diffs_def by (subst (asm) summable_Suc_iff)

    have "(1 + z) * f' z = (\<Sum>n. ?f' n * z^n) + (\<Sum>n. ?f' n * z^Suc n)"
      unfolding f_f'_def using summable' z by (simp add: algebra_simps suminf_mult)
    also have "(\<Sum>n. ?f' n * z^n) = (\<Sum>n. of_nat (Suc n) * ?f (Suc n) * z^n)"
      by (intro suminf_cong) (simp add: diffs_def)
    also have "(\<Sum>n. ?f' n * z^Suc n) = (\<Sum>n. of_nat n * ?f n * z ^ n)"
      using summable1 suminf_split_initial_segment[OF summable1] unfolding diffs_def
      by (subst suminf_split_head, subst (asm) summable_Suc_iff) simp_all
    also have "(\<Sum>n. of_nat (Suc n) * ?f (Suc n) * z^n) + (\<Sum>n. of_nat n * ?f n * z^n) =
                 (\<Sum>n. a * ?f n * z^n)"
      by (subst gbinomial_mult_1, subst suminf_add)
         (insert summable'[OF z] summable2,
          simp_all add: summable_powser_split_head algebra_simps diffs_def)
    also have "\<dots> = a * f z" unfolding f_f'_def
      by (subst suminf_mult[symmetric]) (simp_all add: summable[OF z] mult_ac)
    finally have "a * f z = (1 + z) * f' z" by simp
  } note deriv = this

  have [derivative_intros]: "(f has_field_derivative f' z) (at z)" if "norm z < of_real K" for z
    unfolding f_f'_def using K that
    by (intro termdiffs_strong[of "?f" K z] summable_strong) simp_all
  have "f 0 = (\<Sum>n. if n = 0 then 1 else 0)" unfolding f_f'_def by (intro suminf_cong) simp
  also have "\<dots> = 1" using sums_single[of 0 "\<lambda>_. 1::complex"] unfolding sums_iff by simp
  finally have [simp]: "f 0 = 1" .

  have "\<exists>c. \<forall>z\<in>ball 0 K. f z * (1 + z) powr (-a) = c"
  proof (rule has_field_derivative_zero_constant)
    fix z :: complex assume z': "z \<in> ball 0 K"
    hence z: "norm z < K" by simp
    with K have nz: "1 + z \<noteq> 0" by (auto dest!: minus_unique)
    from z K have "norm z < 1" by simp
    hence "(1 + z) \<notin> \<real>\<^sub>\<le>\<^sub>0" by (cases z) (auto simp: Complex_eq complex_nonpos_Reals_iff)
    hence "((\<lambda>z. f z * (1 + z) powr (-a)) has_field_derivative
              f' z * (1 + z) powr (-a) - a * f z * (1 + z) powr (-a-1)) (at z)" using z
      by (auto intro!: derivative_eq_intros)
    also from z have "a * f z = (1 + z) * f' z" by (rule deriv)
    finally show "((\<lambda>z. f z * (1 + z) powr (-a)) has_field_derivative 0) (at z within ball 0 K)"
      using nz by (simp add: field_simps powr_diff at_within_open[OF z'])
  qed simp_all
  then obtain c where c: "\<And>z. z \<in> ball 0 K \<Longrightarrow> f z * (1 + z) powr (-a) = c" by blast
  from c[of 0] and K have "c = 1" by simp
  with c[of z] have "f z = (1 + z) powr a" using K
    by (simp add: powr_minus field_simps dist_complex_def)
  with summable K show ?thesis unfolding f_f'_def by (simp add: sums_iff)
qed

lemma gen_binomial_complex':
  fixes x y :: real and a :: complex
  assumes "\<bar>x\<bar> < \<bar>y\<bar>"
  shows   "(\<lambda>n. (a gchoose n) * of_real x^n * of_real y powr (a - of_nat n)) sums
               of_real (x + y) powr a" (is "?P x y")
proof -
  {
    fix x y :: real assume xy: "\<bar>x\<bar> < \<bar>y\<bar>" "y \<ge> 0"
    hence "y > 0" by simp
    note xy = xy this
    from xy have "(\<lambda>n. (a gchoose n) * of_real (x / y) ^ n) sums (1 + of_real (x / y)) powr a"
        by (intro gen_binomial_complex) (simp add: norm_divide)
    hence "(\<lambda>n. (a gchoose n) * of_real (x / y) ^ n * y powr a) sums
               ((1 + of_real (x / y)) powr a * y powr a)"
      by (rule sums_mult2)
    also have "(1 + complex_of_real (x / y)) = complex_of_real (1 + x/y)" by simp
    also from xy have "\<dots> powr a * of_real y powr a = (\<dots> * y) powr a"
      by (subst powr_times_real[symmetric]) (simp_all add: field_simps)
    also from xy have "complex_of_real (1 + x / y) * complex_of_real y = of_real (x + y)"
      by (simp add: field_simps)
    finally have "?P x y" using xy by (simp add: field_simps powr_diff powr_nat)
  } note A = this

  show ?thesis
  proof (cases "y < 0")
    assume y: "y < 0"
    with assms have xy: "x + y < 0" by simp
    with assms have "\<bar>-x\<bar> < \<bar>-y\<bar>" "-y \<ge> 0" by simp_all
    note A[OF this]
    also have "complex_of_real (-x + -y) = - complex_of_real (x + y)" by simp
    also from xy assms have "... powr a = (-1) powr -a * of_real (x + y) powr a"
      by (subst powr_neg_real_complex) (simp add: abs_real_def split: if_split_asm)
    also {
      fix n :: nat
      from y have "(a gchoose n) * of_real (-x) ^ n * of_real (-y) powr (a - of_nat n) =
                       (a gchoose n) * (-of_real x / -of_real y) ^ n * (- of_real y) powr a"
        by (subst power_divide) (simp add: powr_diff powr_nat)
      also from y have "(- of_real y) powr a = (-1) powr -a * of_real y powr a"
        by (subst powr_neg_real_complex) simp
      also have "-complex_of_real x / -complex_of_real y = complex_of_real x / complex_of_real y"
        by simp
      also have "... ^ n = of_real x ^ n / of_real y ^ n" by (simp add: power_divide)
      also have "(a gchoose n) * ... * ((-1) powr -a * of_real y powr a) =
                   (-1) powr -a * ((a gchoose n) * of_real x ^ n * of_real y powr (a - n))"
        by (simp add: algebra_simps powr_diff powr_nat)
      finally have "(a gchoose n) * of_real (- x) ^ n * of_real (- y) powr (a - of_nat n) =
                      (-1) powr -a * ((a gchoose n) * of_real x ^ n * of_real y powr (a - of_nat n))" .
    }
    note sums_cong[OF this]
    finally show ?thesis by (simp add: sums_mult_iff)
  qed (insert A[of x y] assms, simp_all add: not_less)
qed

lemma gen_binomial_complex'':
  fixes x y :: real and a :: complex
  assumes "\<bar>y\<bar> < \<bar>x\<bar>"
  shows   "(\<lambda>n. (a gchoose n) * of_real x powr (a - of_nat n) * of_real y ^ n) sums
               of_real (x + y) powr a"
  using gen_binomial_complex'[OF assms] by (simp add: mult_ac add.commute)

lemma gen_binomial_real:
  fixes z :: real
  assumes "\<bar>z\<bar> < 1"
  shows   "(\<lambda>n. (a gchoose n) * z^n) sums (1 + z) powr a"
proof -
  from assms have "norm (of_real z :: complex) < 1" by simp
  from gen_binomial_complex[OF this]
    have "(\<lambda>n. (of_real a gchoose n :: complex) * of_real z ^ n) sums
              (of_real (1 + z)) powr (of_real a)" by simp
  also have "(of_real (1 + z) :: complex) powr (of_real a) = of_real ((1 + z) powr a)"
    using assms by (subst powr_of_real) simp_all
  also have "(of_real a gchoose n :: complex) = of_real (a gchoose n)" for n
    by (simp add: gbinomial_prod_rev)
  hence "(\<lambda>n. (of_real a gchoose n :: complex) * of_real z ^ n) =
           (\<lambda>n. of_real ((a gchoose n) * z ^ n))" by (intro ext) simp
  finally show ?thesis by (simp only: sums_of_real_iff)
qed

lemma gen_binomial_real':
  fixes x y a :: real
  assumes "\<bar>x\<bar> < y"
  shows   "(\<lambda>n. (a gchoose n) * x^n * y powr (a - of_nat n)) sums (x + y) powr a"
proof -
  from assms have "y > 0" by simp
  note xy = this assms
  from assms have "\<bar>x / y\<bar> < 1" by simp
  hence "(\<lambda>n. (a gchoose n) * (x / y) ^ n) sums (1 + x / y) powr a"
    by (rule gen_binomial_real)
  hence "(\<lambda>n. (a gchoose n) * (x / y) ^ n * y powr a) sums ((1 + x / y) powr a * y powr a)"
    by (rule sums_mult2)
  with xy show ?thesis
    by (simp add: field_simps powr_divide powr_diff powr_realpow)
qed

lemma one_plus_neg_powr_powser:
  fixes z s :: complex
  assumes "norm (z :: complex) < 1"
  shows "(\<lambda>n. (-1)^n * ((s + n - 1) gchoose n) * z^n) sums (1 + z) powr (-s)"
    using gen_binomial_complex[OF assms, of "-s"] by (simp add: gbinomial_minus)

lemma gen_binomial_real'':
  fixes x y a :: real
  assumes "\<bar>y\<bar> < x"
  shows   "(\<lambda>n. (a gchoose n) * x powr (a - of_nat n) * y^n) sums (x + y) powr a"
  using gen_binomial_real'[OF assms] by (simp add: mult_ac add.commute)

lemma sqrt_series':
  "\<bar>z\<bar> < a \<Longrightarrow> (\<lambda>n. ((1/2) gchoose n) * a powr (1/2 - real_of_nat n) * z ^ n) sums
                  sqrt (a + z :: real)"
  using gen_binomial_real''[of z a "1/2"] by (simp add: powr_half_sqrt)

lemma sqrt_series:
  "\<bar>z\<bar> < 1 \<Longrightarrow> (\<lambda>n. ((1/2) gchoose n) * z ^ n) sums sqrt (1 + z)"
  using gen_binomial_real[of z "1/2"] by (simp add: powr_half_sqrt)

end
