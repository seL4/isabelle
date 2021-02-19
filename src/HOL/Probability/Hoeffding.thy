(*
  File:    Hoeffding.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Hoeffding's Lemma and Hoeffding's Inequality\<close>
theory Hoeffding
  imports Product_PMF Independent_Family
begin

text \<open>
  Hoeffding's inequality shows that a sum of bounded independent random variables is concentrated
  around its mean, with an exponential decay of the tail probabilities.
\<close>

subsection \<open>Hoeffding's Lemma\<close>

lemma convex_on_exp: 
  fixes l :: real
  assumes "l \<ge> 0"
  shows   "convex_on UNIV (\<lambda>x. exp(l*x))"
  using assms
  by (intro convex_on_realI[where f' = "\<lambda>x. l * exp (l * x)"])
     (auto intro!: derivative_eq_intros mult_left_mono)

lemma mult_const_minus_self_real_le:
  fixes x :: real
  shows "x * (c - x) \<le> c\<^sup>2 / 4"
proof -
  have "x * (c - x) = -(x - c / 2)\<^sup>2 + c\<^sup>2 / 4"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> 0 + c\<^sup>2 / 4"
    by (intro add_mono) auto
  finally show ?thesis by simp
qed

lemma Hoeffdings_lemma_aux:
  fixes h p :: real
  assumes "h \<ge> 0" and "p \<ge> 0"
  defines "L \<equiv> (\<lambda>h. -h * p + ln (1 + p * (exp h - 1)))"
  shows   "L h \<le> h\<^sup>2 / 8"
proof (cases "h = 0")
  case False
  hence h: "h > 0"
    using \<open>h \<ge> 0\<close> by simp
  define L' where "L' = (\<lambda>h. -p + p * exp h / (1 + p * (exp h - 1)))"
  define L'' where "L'' = (\<lambda>h. -(p\<^sup>2) * exp h * exp h / (1 + p * (exp h - 1))\<^sup>2 +
                              p * exp h / (1 + p * (exp h - 1)))"
  define Ls where "Ls = (\<lambda>n. [L, L', L''] ! n)"

  have [simp]: "L 0 = 0" "L' 0 = 0"
    by (auto simp: L_def L'_def)

  have L': "(L has_real_derivative L' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have "1 + p * (exp x - 1) > 0"
      using \<open>p \<ge> 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    thus ?thesis
      unfolding L_def L'_def by (auto intro!: derivative_eq_intros)
  qed

  have L'': "(L' has_real_derivative L'' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have *: "1 + p * (exp x - 1) > 0"
      using \<open>p \<ge> 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    show ?thesis
      unfolding L'_def L''_def
      by (insert *, (rule derivative_eq_intros refl | simp)+) (auto simp: divide_simps; algebra)
  qed

  have diff: "\<forall>m t. m < 2 \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> (Ls m has_real_derivative Ls (Suc m) t) (at t)"
    using L' L'' by (auto simp: Ls_def nth_Cons split: nat.splits)
  from Taylor[of 2 Ls L 0 h 0 h, OF _ _ diff]
    obtain t where t: "t \<in> {0<..<h}" "L h = L'' t * h\<^sup>2 / 2"
      using \<open>h > 0\<close> by (auto simp: Ls_def lessThan_nat_numeral)
  define u where "u = p * exp t / (1 + p * (exp t - 1))"

  have "L'' t = u * (1 - u)"
    by (simp add: L''_def u_def divide_simps; algebra)
  also have "\<dots> \<le> 1 / 4"
    using mult_const_minus_self_real_le[of u 1] by simp
  finally have "L'' t \<le> 1 / 4" .

  note t(2)
  also have "L'' t * h\<^sup>2 / 2 \<le> (1 / 4) * h\<^sup>2 / 2"
    using \<open>L'' t \<le> 1 / 4\<close> by (intro mult_right_mono divide_right_mono) auto
  finally show "L h \<le> h\<^sup>2 / 8" by simp
qed (auto simp: L_def)


locale interval_bounded_random_variable = prob_space +
  fixes f :: "'a \<Rightarrow> real" and a b :: real
  assumes random_variable [measurable]: "random_variable borel f"
  assumes AE_in_interval: "AE x in M. f x \<in> {a..b}"
begin

lemma integrable [intro]: "integrable M f"
proof (rule integrable_const_bound)
  show "AE x in M. norm (f x) \<le> max \<bar>a\<bar> \<bar>b\<bar>"
    by (intro eventually_mono[OF AE_in_interval]) auto
qed (fact random_variable)

text \<open>
  We first show Hoeffding's lemma for distributions whose expectation is 0. The general
  case will easily follow from this later.
\<close>
lemma Hoeffdings_lemma_nn_integral_0:
  assumes "l > 0" and E0: "expectation f = 0"
  shows   "nn_integral M (\<lambda>x. exp (l * f x)) \<le> ennreal (exp (l\<^sup>2 * (b - a)\<^sup>2 / 8))"
proof (cases "AE x in M. f x = 0")
  case True
  hence "nn_integral M (\<lambda>x. exp (l * f x)) = nn_integral M (\<lambda>x. ennreal 1)"
    by (intro nn_integral_cong_AE) auto
  also have "\<dots> = ennreal (expectation (\<lambda>_. 1))"
    by (intro nn_integral_eq_integral) auto
  finally show ?thesis by (simp add: prob_space)
next
  case False
  have "a < 0"
  proof (rule ccontr)
    assume a: "\<not>(a < 0)"
    have "AE x in M. f x = 0"
    proof (subst integral_nonneg_eq_0_iff_AE [symmetric])
      show "AE x in M. f x \<ge> 0"
        using AE_in_interval by eventually_elim (use a in auto)
    qed (use E0 in \<open>auto simp: id_def integrable\<close>)
    with False show False by contradiction
  qed

  have "b > 0"
  proof (rule ccontr)
    assume b: "\<not>(b > 0)"
    have "AE x in M. -f x = 0"
    proof (subst integral_nonneg_eq_0_iff_AE [symmetric])
      show "AE x in M. -f x \<ge> 0"
        using AE_in_interval by eventually_elim (use b in auto)
    qed (use E0 in \<open>auto simp: id_def integrable\<close>)
    with False show False by simp
  qed
    
  have "a < b"
    using \<open>a < 0\<close> \<open>b > 0\<close> by linarith

  define p where "p = -a / (b - a)"
  define L where "L = (\<lambda>t. -t* p + ln (1 - p + p * exp t))"
  define z where "z = l * (b - a)"
  have "z > 0"
    unfolding z_def using \<open>a < b\<close> \<open>l > 0\<close> by auto
  have "p > 0"
    using \<open>a < 0\<close> \<open>a < b\<close> unfolding p_def by (intro divide_pos_pos) auto

  have "(\<integral>\<^sup>+x. exp (l * f x) \<partial>M) \<le>
        (\<integral>\<^sup>+x. (b - f x) / (b - a) * exp (l * a) + (f x - a) / (b - a) * exp (l * b) \<partial>M)"
  proof (intro nn_integral_mono_AE eventually_mono[OF AE_in_interval] ennreal_leI)
    fix x assume x: "f x \<in> {a..b}"
    define y where "y = (b - f x) / (b-a)"
    have y: "y \<in> {0..1}"
      using x \<open>a < b\<close> by (auto simp: y_def)
    have conv: "convex_on UNIV (\<lambda>x. exp(l*x))"
      using \<open>l > 0\<close> by (intro convex_on_exp) auto
    have "exp (l * ((1 - y) *\<^sub>R b + y *\<^sub>R a)) \<le> (1 - y) * exp (l * b) + y * exp (l * a)"
      using y \<open>l > 0\<close> by (intro convex_onD[OF convex_on_exp]) auto
    also have "(1 - y) *\<^sub>R b + y *\<^sub>R a = f x"
      using \<open>a < b\<close> by (simp add: y_def divide_simps) (simp add: algebra_simps)?
    also have "1 - y = (f x - a) / (b - a)"
      using \<open>a < b\<close> by (simp add: field_simps y_def)
    finally show "exp (l * f x) \<le> (b - f x) / (b - a) * exp (l*a) + (f x - a)/(b-a) * exp (l*b)"
      by (simp add: y_def)
  qed
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (b - f x) * exp (l * a) / (b - a) +
                        ennreal (f x - a) * exp (l * b) / (b - a) \<partial>M)"
    using \<open>a < 0\<close> \<open>b > 0\<close>
    by (intro nn_integral_cong_AE eventually_mono[OF AE_in_interval])
       (simp add: ennreal_plus ennreal_mult flip: divide_ennreal)
  also have "\<dots> = ((\<integral>\<^sup>+ x. ennreal (b - f x) \<partial>M) * ennreal (exp (l * a)) +
                   (\<integral>\<^sup>+ x. ennreal (f x - a) \<partial>M) * ennreal (exp (l * b))) / ennreal (b - a)"
    by (simp add: nn_integral_add nn_integral_divide nn_integral_multc add_divide_distrib_ennreal)
  also have "(\<integral>\<^sup>+ x. ennreal (b - f x) \<partial>M) = ennreal (expectation (\<lambda>x. b - f x))"
    by (intro nn_integral_eq_integral Bochner_Integration.integrable_diff
              eventually_mono[OF AE_in_interval] integrable_const integrable) auto
  also have "expectation (\<lambda>x. b - f x) = b"
    using assms by (subst Bochner_Integration.integral_diff) (auto simp: prob_space)
  also have "(\<integral>\<^sup>+ x. ennreal (f x - a) \<partial>M) = ennreal (expectation (\<lambda>x. f x - a))"
    by (intro nn_integral_eq_integral Bochner_Integration.integrable_diff
              eventually_mono[OF AE_in_interval] integrable_const integrable) auto
  also have "expectation (\<lambda>x. f x - a) = (-a)"
    using assms by (subst Bochner_Integration.integral_diff) (auto simp: prob_space)
  also have "(ennreal b * (exp (l * a)) + ennreal (-a) * (exp (l * b))) / (b - a) =
             ennreal (b * exp (l * a) - a * exp (l * b)) / ennreal (b - a)"
    using \<open>a < 0\<close> \<open>b > 0\<close>
    by (simp flip: ennreal_mult ennreal_plus add: mult_nonpos_nonneg divide_ennreal mult_mono)
  also have "b * exp (l * a) - a * exp (l * b) = exp (L z) * (b - a)"
  proof -
    have pos: "1 - p + p * exp z > 0"
    proof -
      have "exp z > 1" using \<open>l > 0\<close> and \<open>a < b\<close>
        by (subst one_less_exp_iff) (auto simp: z_def intro!: mult_pos_pos)
      hence "(exp z - 1) * p \<ge> 0"
        unfolding p_def using \<open>a < 0\<close> and \<open>a < b\<close>
        by (intro mult_nonneg_nonneg divide_nonneg_pos) auto
      thus ?thesis
        by (simp add: algebra_simps)
    qed

    have "exp (L z) * (b - a) = exp (-z * p) * (1 - p + p * exp z) * (b - a)"
      using pos by (simp add: exp_add L_def exp_diff exp_minus divide_simps)
    also have "\<dots> = b * exp (l * a) - a * exp (l * b)" using \<open>a < b\<close>
      by (simp add: p_def z_def divide_simps) (simp add:  exp_diff algebra_simps)?
    finally show ?thesis by simp
  qed
  also have "ennreal (exp (L z) * (b - a)) / ennreal (b - a) = ennreal (exp (L z))"
    using \<open>a < b\<close> by (simp add: divide_ennreal)
  also have "L z = -z * p + ln (1 + p * (exp z - 1))"
    by (simp add: L_def algebra_simps)
  also have "\<dots> \<le> z\<^sup>2 / 8"
    unfolding L_def by (rule Hoeffdings_lemma_aux[where p = p]) (use \<open>z > 0\<close> \<open>p > 0\<close> in simp_all)
  hence "ennreal (exp (-z * p + ln (1 + p * (exp z - 1)))) \<le> ennreal (exp (z\<^sup>2 / 8))"
    by (intro ennreal_leI) auto
  finally show ?thesis
    by (simp add: z_def power_mult_distrib)
qed

context
begin

interpretation shift: interval_bounded_random_variable M "\<lambda>x. f x - \<mu>" "a - \<mu>" "b - \<mu>"
  rewrites "b - \<mu> - (a - \<mu>) \<equiv> b - a"
  by unfold_locales (auto intro!: eventually_mono[OF AE_in_interval])

lemma expectation_shift: "expectation (\<lambda>x. f x - expectation f) = 0"
  by (subst Bochner_Integration.integral_diff) (auto simp: integrable prob_space)

lemmas Hoeffdings_lemma_nn_integral = shift.Hoeffdings_lemma_nn_integral_0[OF _ expectation_shift]

end

end



subsection \<open>Hoeffding's Inequality\<close>

text \<open>
  Consider \<open>n\<close> independent real random variables $X_1, \ldots, X_n$ that each almost surely lie
  in a compact interval $[a_i, b_i]$. Hoeffding's inequality states that the distribution of the
  sum of the $X_i$ is tightly concentrated around the sum of the expected values: the probability
  of it being above or below the sum of the expected values by more than some \<open>\<epsilon>\<close> decreases
  exponentially with \<open>\<epsilon>\<close>.
\<close>

locale indep_interval_bounded_random_variables = prob_space +
  fixes I :: "'b set" and X :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  fixes a b :: "'b \<Rightarrow> real"
  assumes fin: "finite I"
  assumes indep: "indep_vars (\<lambda>_. borel) X I"
  assumes AE_in_interval: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<in> {a i..b i}"
begin

lemma random_variable [measurable]:
  assumes i: "i \<in> I"
  shows "random_variable borel (X i)"
  using i indep unfolding indep_vars_def by blast

lemma bounded_random_variable [intro]:
  assumes i: "i \<in> I"
  shows   "interval_bounded_random_variable M (X i) (a i) (b i)"
  by unfold_locales (use AE_in_interval[OF i] i in auto)

end


locale Hoeffding_ineq = indep_interval_bounded_random_variables +
  fixes \<mu> :: real
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i))"
begin

theorem%important Hoeffding_ineq_ge:
  assumes "\<epsilon> \<ge> 0"
  assumes "(\<Sum>i\<in>I. (b i - a i)\<^sup>2) > 0"
  shows   "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof (cases "\<epsilon> = 0")
  case [simp]: True
  have "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} \<le> 1"
    by simp
  thus ?thesis by simp
next
  case False
  with \<open>\<epsilon> \<ge> 0\<close> have \<epsilon>: "\<epsilon> > 0"
    by auto

  define d where "d = (\<Sum>i\<in>I. (b i - a i)\<^sup>2)"
  define l :: real where "l = 4 * \<epsilon> / d"
  have d: "d > 0"
    using assms by (simp add: d_def)
  have l: "l > 0"
    using \<epsilon> d by (simp add: l_def)
  define \<mu>' where "\<mu>' = (\<lambda>i. expectation (X i))"

  have "{x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} = {x\<in>space M. (\<Sum>i\<in>I. X i x) - \<mu> \<ge> \<epsilon>}"
    by (simp add: algebra_simps)
  hence "ennreal (prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>}) = emeasure M \<dots>"
    by (simp add: emeasure_eq_measure)
  also have "\<dots> \<le> ennreal (exp (-l*\<epsilon>)) * (\<integral>\<^sup>+x\<in>space M. exp (l * ((\<Sum>i\<in>I. X i x) - \<mu>)) \<partial>M)"
    by (intro Chernoff_ineq_nn_integral_ge l) auto
  also have "(\<lambda>x. (\<Sum>i\<in>I. X i x) - \<mu>) = (\<lambda>x. (\<Sum>i\<in>I. X i x - \<mu>' i))"
    by (simp add: \<mu>_def sum_subtractf \<mu>'_def)
  also have "(\<integral>\<^sup>+x\<in>space M. exp (l * ((\<Sum>i\<in>I. X i x - \<mu>' i))) \<partial>M) =
             (\<integral>\<^sup>+x. (\<Prod>i\<in>I. ennreal (exp (l * (X i x - \<mu>' i)))) \<partial>M)"
    by (intro nn_integral_cong)
       (simp_all add: sum_distrib_left ring_distribs exp_diff exp_sum fin prod_ennreal)
  also have "\<dots> = (\<Prod>i\<in>I. \<integral>\<^sup>+x. ennreal (exp (l * (X i x - \<mu>' i))) \<partial>M)"
    by (intro indep_vars_nn_integral fin indep_vars_compose2[OF indep]) auto
  also have "ennreal (exp (-l * \<epsilon>)) * \<dots> \<le>
               ennreal (exp (-l * \<epsilon>)) * (\<Prod>i\<in>I. ennreal (exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8)))"
  proof (intro mult_left_mono prod_mono_ennreal)
    fix i assume i: "i \<in> I"
    from i interpret interval_bounded_random_variable M "X i" "a i" "b i" ..
    show "(\<integral>\<^sup>+x. ennreal (exp (l * (X i x - \<mu>' i))) \<partial>M) \<le> ennreal (exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8))"
      unfolding \<mu>'_def by (rule Hoeffdings_lemma_nn_integral) fact+
  qed auto
  also have "\<dots> = ennreal (exp (-l*\<epsilon>) * (\<Prod>i\<in>I. exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8)))"
    by (simp add: prod_ennreal prod_nonneg flip: ennreal_mult)
  also have "exp (-l*\<epsilon>) * (\<Prod>i\<in>I. exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8)) = exp (d * l\<^sup>2 / 8 - l * \<epsilon>)"
    by (simp add: exp_diff exp_minus sum_divide_distrib sum_distrib_left
                  sum_distrib_right exp_sum fin divide_simps mult_ac d_def)
  also have "d * l\<^sup>2 / 8 - l * \<epsilon> = -2 * \<epsilon>\<^sup>2 / d"
    using d by (simp add: l_def field_simps power2_eq_square)
  finally show ?thesis
    by (subst (asm) ennreal_le_iff) (simp_all add: d_def)
qed

corollary Hoeffding_ineq_le:
  assumes \<epsilon>: "\<epsilon> \<ge> 0"
  assumes "(\<Sum>i\<in>I. (b i - a i)\<^sup>2) > 0"
  shows   "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  interpret flip: Hoeffding_ineq M I "\<lambda>i x. -X i x" "\<lambda>i. -b i" "\<lambda>i. -a i" "-\<mu>"
  proof unfold_locales
    fix i assume "i \<in> I"
    then interpret interval_bounded_random_variable M "X i" "a i" "b i" ..
    show "AE x in M. - X i x \<in> {- b i..- a i}"
      by (intro eventually_mono[OF AE_in_interval]) auto
  qed (auto simp: fin \<mu>_def sum_negf intro: indep_vars_compose2[OF indep])

  have "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>} = prob {x\<in>space M. (\<Sum>i\<in>I. -X i x) \<ge> -\<mu> + \<epsilon>}"
    by (simp add: sum_negf algebra_simps)
  also have "\<dots> \<le> exp (- 2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
    using flip.Hoeffding_ineq_ge[OF \<epsilon>] assms(2) by simp
  finally show ?thesis .
qed

corollary Hoeffding_ineq_abs_ge:
  assumes \<epsilon>: "\<epsilon> \<ge> 0"
  assumes "(\<Sum>i\<in>I. (b i - a i)\<^sup>2) > 0"
  shows   "prob {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - \<mu>\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  have "{x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - \<mu>\<bar> \<ge> \<epsilon>} =
        {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} \<union> {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>}"
    by auto
  also have "prob \<dots> \<le> prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} +
                       prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>}"
    by (intro measure_Un_le) auto
  also have "\<dots> \<le> exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2)) + exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
    by (intro add_mono Hoeffding_ineq_ge Hoeffding_ineq_le assms)
  finally show ?thesis by simp
qed

end


subsection \<open>Hoeffding's inequality for i.i.d. bounded random variables\<close>

text \<open>
  If we have \<open>n\<close> even identically-distributed random variables, the statement of Hoeffding's
  lemma simplifies a bit more: it shows that the probability that the average of the $X_i$
  is more than \<open>\<epsilon>\<close> above the expected value is no greater than $e^{\frac{-2ny^2}{(b-a)^2}}$.

  This essentially gives us a more concrete version of the weak law of large numbers: the law
  states that the probability vanishes for \<open>n \<rightarrow> \<infinity>\<close> for any \<open>\<epsilon> > 0\<close>. Unlike Hoeffding's inequality,
  it does not assume the variables to have bounded support, but it does not provide concrete bounds.
\<close>

locale iid_interval_bounded_random_variables = prob_space +
  fixes I :: "'b set" and X :: "'b \<Rightarrow> 'a \<Rightarrow> real" and Y :: "'a \<Rightarrow> real"
  fixes a b :: real
  assumes fin: "finite I"
  assumes indep: "indep_vars (\<lambda>_. borel) X I"
  assumes distr_X: "i \<in> I \<Longrightarrow> distr M borel (X i) = distr M borel Y"
  assumes rv_Y [measurable]: "random_variable borel Y"
  assumes AE_in_interval: "AE x in M. Y x \<in> {a..b}"
begin

lemma random_variable [measurable]:
  assumes i: "i \<in> I"
  shows "random_variable borel (X i)"
  using i indep unfolding indep_vars_def by blast

sublocale X: indep_interval_bounded_random_variables M I X "\<lambda>_. a" "\<lambda>_. b"
proof
  fix i assume i: "i \<in> I"
  have "AE x in M. Y x \<in> {a..b}"
    by (fact AE_in_interval)
  also have "?this \<longleftrightarrow> (AE x in distr M borel Y. x \<in> {a..b})"
    by (subst AE_distr_iff) auto
  also have "distr M borel Y = distr M borel (X i)"
    using i by (simp add: distr_X)
  also have "(AE x in \<dots>. x \<in> {a..b}) \<longleftrightarrow> (AE x in M. X i x \<in> {a..b})"
    using i by (subst AE_distr_iff) auto
  finally show "AE x in M. X i x \<in> {a..b}" .
qed (simp_all add: fin indep)

lemma expectation_X [simp]:
  assumes i: "i \<in> I"
  shows "expectation (X i) = expectation Y"
proof -
  have "expectation (X i) = lebesgue_integral (distr M borel (X i)) (\<lambda>x. x)"
    using i by (intro integral_distr [symmetric]) auto
  also have "distr M borel (X i) = distr M borel Y"
    using i by (rule distr_X)
  also have "lebesgue_integral \<dots> (\<lambda>x. x) = expectation Y"
    by (rule integral_distr) auto
  finally show "expectation (X i) = expectation Y" .
qed

end


locale Hoeffding_ineq_iid = iid_interval_bounded_random_variables +
  fixes \<mu> :: real
  defines "\<mu> \<equiv> expectation Y"
begin

sublocale X: Hoeffding_ineq M I X "\<lambda>_. a" "\<lambda>_. b" "real (card I) * \<mu>"
  by unfold_locales (simp_all add: \<mu>_def)

corollary
  assumes \<epsilon>: "\<epsilon> \<ge> 0"
  assumes "a < b" "I \<noteq> {}"
  defines "n \<equiv> card I"
  shows   Hoeffding_ineq_ge:
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> n * \<mu> + \<epsilon>} \<le>
               exp (-2 * \<epsilon>\<^sup>2 / (n * (b - a)\<^sup>2))" (is ?le)
    and   Hoeffding_ineq_le:
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> n * \<mu> - \<epsilon>} \<le>
               exp (-2 * \<epsilon>\<^sup>2 / (n * (b - a)\<^sup>2))" (is ?ge)
    and   Hoeffding_ineq_abs_ge:
            "prob {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - n * \<mu>\<bar> \<ge> \<epsilon>} \<le>
               2 * exp (-2 * \<epsilon>\<^sup>2 / (n * (b - a)\<^sup>2))" (is ?abs_ge)
proof -
  have pos: "(\<Sum>i\<in>I. (b - a)\<^sup>2) > 0"
    using \<open>a < b\<close> \<open>I \<noteq> {}\<close> fin by (intro sum_pos) auto
  show ?le
    using X.Hoeffding_ineq_ge[OF \<epsilon> pos] by (simp add: n_def)
  show ?ge
    using X.Hoeffding_ineq_le[OF \<epsilon> pos] by (simp add: n_def)
  show ?abs_ge
    using X.Hoeffding_ineq_abs_ge[OF \<epsilon> pos] by (simp add: n_def)
qed

lemma 
  assumes \<epsilon>: "\<epsilon> \<ge> 0"
  assumes "a < b" "I \<noteq> {}"
  defines "n \<equiv> card I"
  shows   Hoeffding_ineq_ge':
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<ge> \<mu> + \<epsilon>} \<le>
               exp (-2 * n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" (is ?ge)
    and   Hoeffding_ineq_le':
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<le> \<mu> - \<epsilon>} \<le>
               exp (-2 * n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" (is ?le)
    and   Hoeffding_ineq_abs_ge':
            "prob {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) / n - \<mu>\<bar> \<ge> \<epsilon>} \<le>
               2 * exp (-2 * n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" (is ?abs_ge)
proof -
  have "n > 0"
    using assms fin by (auto simp: field_simps)
  have \<epsilon>': "\<epsilon> * n \<ge> 0"
    using \<open>n > 0\<close> \<open>\<epsilon> \<ge> 0\<close> by auto
  have eq: "- (2 * (\<epsilon> * real n)\<^sup>2 / (real (card I) * (b - a)\<^sup>2)) =
            - (2 * real n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)"
    using \<open>n > 0\<close> by (simp add: power2_eq_square divide_simps n_def)

  have "{x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<ge> \<mu> + \<epsilon>} =
        {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> * n + \<epsilon> * n}"
    using \<open>n > 0\<close> by (intro Collect_cong conj_cong refl) (auto simp: field_simps)
  with Hoeffding_ineq_ge[OF \<epsilon>' \<open>a < b\<close> \<open>I \<noteq> {}\<close>] \<open>n > 0\<close> eq show ?ge
    by (simp add: n_def mult_ac)

  have "{x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<le> \<mu> - \<epsilon>} =
        {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> * n - \<epsilon> * n}"
    using \<open>n > 0\<close> by (intro Collect_cong conj_cong refl) (auto simp: field_simps)
  with Hoeffding_ineq_le[OF \<epsilon>' \<open>a < b\<close> \<open>I \<noteq> {}\<close>] \<open>n > 0\<close> eq show ?le
    by (simp add: n_def mult_ac)

  have "{x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) / n - \<mu>\<bar> \<ge> \<epsilon>} =
        {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - \<mu> * n\<bar> \<ge> \<epsilon> * n}"
    using \<open>n > 0\<close> by (intro Collect_cong conj_cong refl) (auto simp: field_simps)
  with Hoeffding_ineq_abs_ge[OF \<epsilon>' \<open>a < b\<close> \<open>I \<noteq> {}\<close>] \<open>n > 0\<close> eq show ?abs_ge
    by (simp add: n_def mult_ac)
qed

end


subsection \<open>Hoeffding's Inequality for the Binomial distribution\<close>

text \<open>
  We can now apply Hoeffding's inequality to the Binomial distribution, which can be seen
  as the sum of \<open>n\<close> i.i.d. coin flips (the support of each of which is contained in $[0,1]$).
\<close>

locale binomial_distribution =
  fixes n :: nat and p :: real
  assumes p: "p \<in> {0..1}"
begin

context
  fixes coins :: "(nat \<Rightarrow> bool) pmf" and \<mu>
  assumes n: "n > 0"
  defines "coins \<equiv> Pi_pmf {..<n} False (\<lambda>_. bernoulli_pmf p)"
begin

lemma coins_component:
  assumes i: "i < n"
  shows   "distr (measure_pmf coins) borel (\<lambda>f. if f i then 1 else 0) =
             distr (measure_pmf (bernoulli_pmf p)) borel (\<lambda>b. if b then 1 else 0)"
proof -
  have "distr (measure_pmf coins) borel (\<lambda>f. if f i then 1 else 0) =
        distr (measure_pmf (map_pmf (\<lambda>f. f i) coins)) borel (\<lambda>b. if b then 1 else 0)"
    unfolding map_pmf_rep_eq by (subst distr_distr) (auto simp: o_def)
  also have "map_pmf (\<lambda>f. f i) coins = bernoulli_pmf p"
    unfolding coins_def using i by (subst Pi_pmf_component) auto
  finally show ?thesis
    unfolding map_pmf_rep_eq .
qed

lemma prob_binomial_pmf_conv_coins:
  "measure_pmf.prob (binomial_pmf n p) {x. P (real x)} = 
   measure_pmf.prob coins {x. P (\<Sum>i<n. if x i then 1 else 0)}"
proof -
  have eq1: "(\<Sum>i<n. if x i then 1 else 0) = real (card {i\<in>{..<n}. x i})" for x
  proof -
    have "(\<Sum>i<n. if x i then 1 else (0::real)) = (\<Sum>i\<in>{i\<in>{..<n}. x i}. 1)"
      by (intro sum.mono_neutral_cong_right) auto
    thus ?thesis by simp
  qed
  have eq2: "binomial_pmf n p = map_pmf (\<lambda>v. card {i\<in>{..<n}. v i}) coins"
    unfolding coins_def by (rule binomial_pmf_altdef') (use p in auto)
  show ?thesis
    by (subst eq2) (simp_all add: eq1)
qed

interpretation Hoeffding_ineq_iid
  coins "{..<n}" "\<lambda>i f. if f i then 1 else 0" "\<lambda>f. if f 0 then 1 else 0" 0 1 p
proof unfold_locales
  show "prob_space.indep_vars (measure_pmf coins) (\<lambda>_. borel) (\<lambda>i f. if f i then 1 else 0) {..<n}"
    unfolding coins_def
    by (intro prob_space.indep_vars_compose2[OF _ indep_vars_Pi_pmf])
       (auto simp: measure_pmf.prob_space_axioms)
next
  have "measure_pmf.expectation coins (\<lambda>f. if f 0 then 1 else 0 :: real) =
        measure_pmf.expectation (map_pmf (\<lambda>f. f 0) coins) (\<lambda>b. if b then 1 else 0 :: real)"
    by (simp add: coins_def)
  also have "map_pmf (\<lambda>f. f 0) coins = bernoulli_pmf p"
    using n by (simp add: coins_def Pi_pmf_component)
  also have "measure_pmf.expectation \<dots> (\<lambda>b. if b then 1 else 0) = p"
    using p by simp
  finally show "p \<equiv> measure_pmf.expectation coins (\<lambda>f. if f 0 then 1 else 0)" by simp
qed (auto simp: coins_component)

corollary
  fixes \<epsilon> :: real
  assumes \<epsilon>: "\<epsilon> \<ge> 0"
  shows prob_ge: "measure_pmf.prob (binomial_pmf n p) {x. x \<ge> n * p + \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    and prob_le: "measure_pmf.prob (binomial_pmf n p) {x. x \<le> n * p - \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    and prob_abs_ge:
          "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x - n * p\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * \<epsilon>\<^sup>2 / n)"
proof -
  have [simp]: "{..<n} \<noteq> {}"
    using n by auto
  show "measure_pmf.prob (binomial_pmf n p) {x. x \<ge> n * p + \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    using Hoeffding_ineq_ge[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. x \<le> n * p - \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    using Hoeffding_ineq_le[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x - n * p\<bar> \<ge> \<epsilon>} \<le> 2 *  exp (-2 * \<epsilon>\<^sup>2 / n)"
    using Hoeffding_ineq_abs_ge[of \<epsilon>]
    by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
qed

corollary
  fixes \<epsilon> :: real
  assumes \<epsilon>: "\<epsilon> \<ge> 0"
  shows prob_ge': "measure_pmf.prob (binomial_pmf n p) {x. x / n \<ge> p + \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    and prob_le': "measure_pmf.prob (binomial_pmf n p) {x. x / n \<le> p - \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    and prob_abs_ge':
          "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x / n - p\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * n * \<epsilon>\<^sup>2)"
proof -
  have [simp]: "{..<n} \<noteq> {}"
    using n by auto
  show "measure_pmf.prob (binomial_pmf n p) {x. x / n \<ge> p + \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    using Hoeffding_ineq_ge'[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. x / n \<le> p - \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    using Hoeffding_ineq_le'[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x / n - p\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * n * \<epsilon>\<^sup>2)"
    using Hoeffding_ineq_abs_ge'[of \<epsilon>]
    by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
qed

end

end


subsection \<open>Tail bounds for the negative binomial distribution\<close>

text \<open>
  Since the tail probabilities of a negative Binomial distribution are equal to the
  tail probabilities of some Binomial distribution, we can obtain tail bounds for the
  negative Binomial distribution through the Hoeffding tail bounds for the Binomial
  distribution.
\<close>

context
  fixes p q :: real
  assumes p: "p \<in> {0<..<1}"
  defines "q \<equiv> 1 - p"
begin

lemma prob_neg_binomial_pmf_ge_bound:
  fixes n :: nat and k :: real
  defines "\<mu> \<equiv> real n * q / p"
  assumes k: "k \<ge> 0"
  shows "measure_pmf.prob (neg_binomial_pmf n p) {x. real x \<ge> \<mu> + k}
         \<le> exp (- 2 * p ^ 3 * k\<^sup>2 / (n + p * k))"
proof -
  consider "n = 0" | "p = 1" | "n > 0" "p \<noteq> 1"
    by blast
  thus ?thesis
  proof cases
    assume [simp]: "n = 0"
    show ?thesis using k
      by (simp add: indicator_def \<mu>_def)
  next
    assume [simp]: "p = 1"
    show ?thesis using k
      by (auto simp add: indicator_def \<mu>_def q_def)
  next
    assume n: "n > 0" and "p \<noteq> 1"
    from \<open>p \<noteq> 1\<close> and p have p: "p \<in> {0<..<1}"
      by auto
    from p have q: "q \<in> {0<..<1}"
      by (auto simp: q_def)

    define k1 where "k1 = \<mu> + k"
    have k1: "k1 \<ge> \<mu>"
      using k by (simp add: k1_def)
    have "k1 > 0"
      by (rule less_le_trans[OF _ k1]) (use p n in \<open>auto simp: q_def \<mu>_def\<close>)
  
    define k1' where "k1' = nat (ceiling k1)"
    have "\<mu> \<ge> 0" using p
      by (auto simp: \<mu>_def q_def)
    have "\<not>(x < k1') \<longleftrightarrow> real x \<ge> k1" for x
      unfolding k1'_def by linarith
    hence eq: "UNIV - {..<k1'} = {x. x \<ge> k1}"
      by auto
    hence "measure_pmf.prob (neg_binomial_pmf n p) {n. n \<ge> k1} =
          1 - measure_pmf.prob (neg_binomial_pmf n p) {..<k1'}"
      using measure_pmf.prob_compl[of "{..<k1'}" "neg_binomial_pmf n p"] by simp
    also have "measure_pmf.prob (neg_binomial_pmf n p) {..<k1'} =
               measure_pmf.prob (binomial_pmf (n + k1' - 1) q) {..<k1'}"
      unfolding q_def using p by (intro prob_neg_binomial_pmf_lessThan) auto
    also have "1 - \<dots> = measure_pmf.prob (binomial_pmf (n + k1' - 1) q) {n. n \<ge> k1}"
      using measure_pmf.prob_compl[of "{..<k1'}" "binomial_pmf (n + k1' - 1) q"] eq by simp
    also have "{x. real x \<ge> k1} = {x. x \<ge> real (n + k1' - 1) * q + (k1 - real (n + k1' - 1) * q)}"
      by simp
    also have "measure_pmf.prob (binomial_pmf (n + k1' - 1) q) \<dots> \<le>
                 exp (-2 * (k1 - real (n + k1' - 1) * q)\<^sup>2 / real (n + k1' - 1))"
    proof (rule binomial_distribution.prob_ge)
      show "binomial_distribution q"
        by unfold_locales (use q in auto)
    next
      show "n + k1' - 1 > 0"
        using \<open>k1 > 0\<close> n unfolding k1'_def by linarith
    next
      have "real (n + nat \<lceil>k1\<rceil> - 1) \<le> real n + k1"
        using \<open>k1 > 0\<close> by linarith
      hence "real (n + k1' - 1) * q  \<le> (real n + k1) * q"
        unfolding k1'_def by (intro mult_right_mono) (use p in \<open>simp_all add: q_def\<close>)
      also have "\<dots> \<le> k1"
        using k1 p by (simp add: q_def field_simps \<mu>_def)
      finally show "0 \<le> k1 - real (n + k1' - 1) * q"
        by simp
    qed
    also have "{x. real (n + k1' - 1) * q + (k1 - real (n + k1' - 1) * q) \<le> real x} = {x. real x \<ge> k1}"
      by simp
    also have "exp (-2 * (k1 - real (n + k1' - 1) * q)\<^sup>2 / real (n + k1' - 1)) \<le>
               exp (-2 * (k1 - (n + k1) * q)\<^sup>2 / (n + k1))"
    proof -
      have "real (n + k1' - Suc 0) \<le> real n + k1"
        unfolding k1'_def using \<open>k1 > 0\<close> by linarith
      moreover have "(real n + k1) * q \<le> k1"
        using k1 p by (auto simp: q_def field_simps \<mu>_def)
      moreover have "1 < n + k1'"
        using n \<open>k1 > 0\<close> unfolding k1'_def by linarith
      ultimately have "2 * (k1 - real (n + k1' - 1) * q)\<^sup>2 / real (n + k1' - 1) \<ge>
                       2 * (k1 - (n + k1) * q)\<^sup>2 / (n + k1)"
        by (intro frac_le mult_left_mono power_mono mult_nonneg_nonneg mult_right_mono diff_mono)
           (use q in simp_all)
      thus ?thesis
        by simp
    qed
    also have "\<dots> = exp (-2 * (p * k1 - q * n)\<^sup>2 / (k1 + n))"
      by (simp add: q_def algebra_simps)
    also have "-2 * (p * k1 - q * n)\<^sup>2 = -2 * p\<^sup>2 * (k1 - \<mu>)\<^sup>2"
      using p by (auto simp: field_simps \<mu>_def)
    also have "k1 - \<mu> = k"
      by (simp add: k1_def \<mu>_def)
    also note k1_def
    also have "\<mu> + k + real n = real n / p + k"
      using p by (simp add: \<mu>_def q_def field_simps)
    also have "- 2 * p\<^sup>2 * k\<^sup>2 / (real n / p + k) = - 2 * p ^ 3 * k\<^sup>2 / (p * k + n)"
      using p by (simp add: field_simps power3_eq_cube power2_eq_square)
    finally show ?thesis by (simp add: add_ac)
  qed
qed

lemma prob_neg_binomial_pmf_le_bound:
  fixes n :: nat and k :: real
  defines "\<mu> \<equiv> real n * q / p"
  assumes k: "k \<ge> 0"
  shows "measure_pmf.prob (neg_binomial_pmf n p) {x. real x \<le> \<mu> - k}
         \<le> exp (-2 * p ^ 3 * k\<^sup>2 / (n - p * k))"
proof -
  consider "n = 0" | "p = 1" | "k > \<mu>" | "n > 0" "p \<noteq> 1" "k \<le> \<mu>"
    by force
  thus ?thesis
  proof cases
    assume [simp]: "n = 0"
    show ?thesis using k
      by (simp add: indicator_def \<mu>_def)
  next
    assume [simp]: "p = 1"
    show ?thesis using k
      by (auto simp add: indicator_def \<mu>_def q_def)
  next
    assume "k > \<mu>"
    hence "{x. real x \<le> \<mu> - k} = {}"
      by auto
    thus ?thesis by simp
  next
    assume n: "n > 0" and "p \<noteq> 1" and "k \<le> \<mu>"
    from \<open>p \<noteq> 1\<close> and p have p: "p \<in> {0<..<1}"
      by auto
    from p have q: "q \<in> {0<..<1}"
      by (auto simp: q_def)

    define f :: "real \<Rightarrow> real" where "f = (\<lambda>x. (p * x - q * n)\<^sup>2 / (x + n))"
    have f_mono: "f x \<ge> f y" if "x \<ge> 0" "y \<le> n * q / p" "x \<le> y" for x y :: real
      using that(3)
    proof (rule DERIV_nonpos_imp_nonincreasing)
      fix t assume t: "t \<ge> x" "t \<le> y"
      have "x > -n"
        using n \<open>x \<ge> 0\<close> by linarith
      hence "(f has_field_derivative ((p * t - q * n) * (n * (1 + p) + p * t) / (n + t) ^ 2)) (at t)"
        unfolding f_def using t
        by (auto intro!: derivative_eq_intros simp: algebra_simps q_def power2_eq_square)
      moreover {
        have "p * t \<le> p * y"
          using p by (intro mult_left_mono t) auto
        also have "p * y \<le> q * n"
          using \<open>y \<le> n * q / p\<close> p by (simp add: field_simps)
        finally have "p * t \<le> q * n" .
      }
      hence "(p * t - q * n) * (n * (1 + p) + p * t) / (n + t) ^ 2 \<le> 0"
        using p \<open>x \<ge> 0\<close> t
        by (intro mult_nonpos_nonneg divide_nonpos_nonneg add_nonneg_nonneg mult_nonneg_nonneg) auto
      ultimately show "\<exists>y. (f has_real_derivative y) (at t) \<and> y \<le> 0"
        by blast
    qed

    define k1 where "k1 = \<mu> - k"
    have k1: "k1 \<le> real n * q / p"
      using assms by (simp add: \<mu>_def k1_def)
    have "k1 \<ge> 0"
      using k \<open>k \<le> \<mu>\<close> by (simp add: \<mu>_def k1_def)
  
    define k1' where "k1' = nat (floor k1)"
    have "\<mu> \<ge> 0" using p
      by (auto simp: \<mu>_def q_def)
    have "(x \<le> k1') \<longleftrightarrow> real x \<le> k1" for x
      unfolding k1'_def not_less using \<open>k1 \<ge> 0\<close> by linarith
    hence eq: "{n. n \<le> k1}  = {..k1'}"
      by auto
    hence "measure_pmf.prob (neg_binomial_pmf n p) {n. n \<le> k1} =
           measure_pmf.prob (neg_binomial_pmf n p) {..k1'}"
      by simp
    also have "measure_pmf.prob (neg_binomial_pmf n p) {..k1'} =
               measure_pmf.prob (binomial_pmf (n + k1') q) {..k1'}"
      unfolding q_def using p by (intro prob_neg_binomial_pmf_atMost) auto
    also note eq [symmetric]
    also have "{x. real x \<le> k1} = {x. x \<le> real (n + k1') * q - (real (n + k1') * q - real k1')}"
      using eq by auto
    also have "measure_pmf.prob (binomial_pmf (n + k1') q) \<dots> \<le>
                 exp (-2 * (real (n + k1') * q - real k1')\<^sup>2 / real (n + k1'))"
    proof (rule binomial_distribution.prob_le)
      show "binomial_distribution q"
        by unfold_locales (use q in auto)
    next
      show "n + k1' > 0"
        using \<open>k1 \<ge> 0\<close> n unfolding k1'_def by linarith
    next
      have "p * k1' \<le> p * k1"
        using p \<open>k1 \<ge> 0\<close> by (intro mult_left_mono) (auto simp: k1'_def)
      also have "\<dots> \<le> q * n"
        using k1 p by (simp add: field_simps)
      finally show "0 \<le> real (n + k1') * q - real k1'"
        by (simp add: algebra_simps q_def)
    qed
    also have "{x. real x \<le> real (n + k1') * q - (real (n + k1') * q - k1')} = {..k1'}"
      by auto
    also have "real (n + k1') * q - k1' = -(p * k1' - q * n)"
      by (simp add: q_def algebra_simps)
    also have "\<dots> ^ 2 = (p * k1' - q * n) ^ 2"
      by algebra
    also have "- 2 * (p * real k1' - q * real n)\<^sup>2 / real (n + k1') = -2 * f (real k1')"
      by (simp add: f_def)
    also have "f (real k1') \<ge> f k1"
      by (rule f_mono) (use \<open>k1 \<ge> 0\<close> k1 in \<open>auto simp: k1'_def\<close>)
    hence "exp (-2 * f (real k1')) \<le> exp (-2 * f k1)"
      by simp
    also have "\<dots> = exp (-2 * (p * k1 - q * n)\<^sup>2 / (k1 + n))"
      by (simp add: f_def)

    also have "-2 * (p * k1 - q * n)\<^sup>2 = -2 * p\<^sup>2 * (k1 - \<mu>)\<^sup>2"
      using p by (auto simp: field_simps \<mu>_def)
    also have "(k1 - \<mu>) ^ 2 = k ^ 2"
      by (simp add: k1_def \<mu>_def)
    also note k1_def
    also have "\<mu> - k + real n = real n / p - k"
      using p by (simp add: \<mu>_def q_def field_simps)
    also have "- 2 * p\<^sup>2 * k\<^sup>2 / (real n / p - k) = - 2 * p ^ 3 * k\<^sup>2 / (n - p * k)"
      using p by (simp add: field_simps power3_eq_cube power2_eq_square)
    also have "{..k1'} = {x. real x \<le> \<mu> - k}"
      using eq by (simp add: k1_def)
    finally show ?thesis .
  qed
qed

text \<open>
  Due to the function $exp(-l/x)$ being concave for $x \geq \frac{l}{2}$, the above two
  bounds can be combined into the following one for moderate values of \<open>k\<close>.
  (cf. \<^url>\<open>https://math.stackexchange.com/questions/1565559\<close>)
\<close>
lemma prob_neg_binomial_pmf_abs_ge_bound:
  fixes n :: nat and k :: real
  defines "\<mu> \<equiv> real n * q / p"
  assumes "k \<ge> 0" and n_ge: "n \<ge> p * k * (p\<^sup>2 * k + 1)"
  shows "measure_pmf.prob (neg_binomial_pmf n p) {x. \<bar>real x - \<mu>\<bar> \<ge> k} \<le>
           2 * exp (-2 * p ^ 3 * k ^ 2 / n)"
proof (cases "k = 0")
  case False
  with \<open>k \<ge> 0\<close> have k: "k > 0"
    by auto
  define l :: real where "l = 2 * p ^ 3 * k ^ 2"
  have l: "l > 0"
    using p k by (auto simp: l_def)
  define f :: "real \<Rightarrow> real" where "f = (\<lambda>x. exp (-l / x))"
  define f' where "f' = (\<lambda>x. -l * exp (-l / x) / x ^ 2)"

  have f'_mono: "f' x \<le> f' y" if "x \<ge> l / 2" "x \<le> y" for x y :: real
    using that(2)
  proof (rule DERIV_nonneg_imp_nondecreasing)
    fix t assume t: "x \<le> t" "t \<le> y"
    have "t > 0"
      using that l t by auto
    have "(f' has_field_derivative (l * (2 * t - l) / (exp (l / t) * t ^ 4))) (at t)"
      unfolding f'_def using t that \<open>t > 0\<close>
      by (auto intro!: derivative_eq_intros simp: field_simps exp_minus simp flip: power_Suc)
    moreover have "l * (2 * t - l) / (exp (l / t) * t ^ 4) \<ge> 0"
      using that t l by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
    ultimately show "\<exists>y. (f' has_real_derivative y) (at t) \<and> 0 \<le> y" by blast
  qed

  have convex: "convex_on {l/2..} (\<lambda>x. -f x)" unfolding f_def
  proof (intro convex_on_realI[where f' = f'])
    show "((\<lambda>x. - exp (- l / x)) has_real_derivative f' x) (at x)" if "x \<in> {l/2..}" for x
      using that l
      by (auto intro!: derivative_eq_intros simp: f'_def power2_eq_square algebra_simps)
  qed (use l in \<open>auto intro!: f'_mono\<close>)

  have eq: "{x. \<bar>real x - \<mu>\<bar> \<ge> k} = {x. real x \<le> \<mu> - k} \<union> {x. real x \<ge> \<mu> + k}"
    by auto
  have "measure_pmf.prob (neg_binomial_pmf n p) {x. \<bar>real x - \<mu>\<bar> \<ge> k} \<le>
        measure_pmf.prob (neg_binomial_pmf n p) {x. real x \<le> \<mu> - k} +
        measure_pmf.prob (neg_binomial_pmf n p) {x. real x \<ge> \<mu> + k}"
    by (subst eq, rule measure_Un_le) auto
  also have "\<dots> \<le> exp (-2 * p ^ 3 * k\<^sup>2 / (n - p * k)) + exp (-2 * p ^ 3 * k\<^sup>2 / (n + p * k))"
    unfolding \<mu>_def
    by (intro prob_neg_binomial_pmf_le_bound prob_neg_binomial_pmf_ge_bound add_mono \<open>k \<ge> 0\<close>)
  also have "\<dots> = 2 * (1/2 * f (n - p * k) + 1/2 * f (n + p * k))"
    by (simp add: f_def l_def)
  also have "1/2 * f (n - p * k) + 1/2 * f (n + p * k) \<le> f (1/2 * (n - p * k) + 1/2 * (n + p * k))"
  proof -
    let ?x = "n - p * k" and ?y = "n + p * k"
    have le1: "l / 2 \<le> ?x" using n_ge
      by (simp add: l_def power2_eq_square power3_eq_cube algebra_simps)
    also have "\<dots> \<le> ?y"
      using p k by simp
    finally have le2: "l / 2 \<le> ?y" .
    have "-f ((1 - 1 / 2) *\<^sub>R ?x + (1 / 2) *\<^sub>R ?y) \<le> (1 - 1 / 2) * - f ?x + 1 / 2 * - f ?y"
      using le1 le2 by (intro convex_onD[OF convex]) auto
    thus ?thesis by simp
  qed
  also have "1/2 * (n - p * k) + 1/2 * (n + p * k) = n"
    by (simp add: algebra_simps)
  also have "2 * f n = 2 * exp (-l / n)"
    by (simp add: f_def)
  finally show ?thesis
    by (simp add: l_def)
qed auto

end

end
