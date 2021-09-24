(*  Title:     HOL/Probability/Levy.thy
    Authors:   Jeremy Avigad (CMU)
*)

section \<open>The Levy inversion theorem, and the Levy continuity theorem.\<close>

theory Levy
  imports Characteristic_Functions Helly_Selection Sinc_Integral
begin

subsection \<open>The Levy inversion theorem\<close>

(* Actually, this is not needed for us -- but it is useful for other purposes. (See Billingsley.) *)
lemma Levy_Inversion_aux1:
  fixes a b :: real
  assumes "a \<le> b"
  shows "((\<lambda>t. (iexp (-(t * a)) - iexp (-(t * b))) / (\<i> * t)) \<longlongrightarrow> b - a) (at 0)"
    (is "(?F \<longlongrightarrow> _) (at _)")
proof -
  have 1: "cmod (?F t - (b - a)) \<le> a^2 / 2 * abs t + b^2 / 2 * abs t" if "t \<noteq> 0" for t
  proof -
    have "cmod (?F t - (b - a)) = cmod (
        (iexp (-(t * a)) - (1 + \<i> * -(t * a))) / (\<i> * t) -
        (iexp (-(t * b)) - (1 + \<i> * -(t * b))) / (\<i> * t))"
           (is "_ = cmod (?one / (\<i> * t) - ?two / (\<i> * t))")
      using \<open>t \<noteq> 0\<close> by (intro arg_cong[where f=norm]) (simp add: field_simps)
    also have "\<dots> \<le> cmod (?one / (\<i> * t)) + cmod (?two / (\<i> * t))"
      by (rule norm_triangle_ineq4)
    also have "cmod (?one / (\<i> * t)) = cmod ?one / abs t"
      by (simp add: norm_divide norm_mult)
    also have "cmod (?two / (\<i> * t)) = cmod ?two / abs t"
      by (simp add: norm_divide norm_mult)
    also have "cmod ?one / abs t + cmod ?two / abs t \<le>
        ((- (a * t))^2 / 2) / abs t + ((- (b * t))^2 / 2) / abs t"
      apply (rule add_mono)
      apply (rule divide_right_mono)
      using iexp_approx1 [of "-(t * a)" 1] apply (simp add: field_simps eval_nat_numeral)
      apply force
      apply (rule divide_right_mono)
      using iexp_approx1 [of "-(t * b)" 1] apply (simp add: field_simps eval_nat_numeral)
      by force
    also have "\<dots> = a^2 / 2 * abs t + b^2 / 2 * abs t"
      using \<open>t \<noteq> 0\<close> apply (case_tac "t \<ge> 0", simp add: field_simps power2_eq_square)
      using \<open>t \<noteq> 0\<close> by (subst (1 2) abs_of_neg, auto simp add: field_simps power2_eq_square)
    finally show "cmod (?F t - (b - a)) \<le> a^2 / 2 * abs t + b^2 / 2 * abs t" .
  qed
  show ?thesis
    apply (rule LIM_zero_cancel)
    apply (rule tendsto_norm_zero_cancel)
    apply (rule real_LIM_sandwich_zero [OF _ _ 1])
    apply (auto intro!: tendsto_eq_intros)
    done
qed

lemma Levy_Inversion_aux2:
  fixes a b t :: real
  assumes "a \<le> b" and "t \<noteq> 0"
  shows "cmod ((iexp (t * b) - iexp (t * a)) / (\<i> * t)) \<le> b - a" (is "?F \<le> _")
proof -
  have "?F = cmod (iexp (t * a) * (iexp (t * (b - a)) - 1) / (\<i> * t))"
    using \<open>t \<noteq> 0\<close> by (intro arg_cong[where f=norm]) (simp add: field_simps exp_diff exp_minus)
  also have "\<dots> = cmod (iexp (t * (b - a)) - 1) / abs t"
    unfolding norm_divide norm_mult norm_exp_i_times using \<open>t \<noteq> 0\<close>
    by (simp add: complex_eq_iff norm_mult)
  also have "\<dots> \<le> abs (t * (b - a)) / abs t"
    using iexp_approx1 [of "t * (b - a)" 0]
    by (intro divide_right_mono) (auto simp add: field_simps eval_nat_numeral)
  also have "\<dots> = b - a"
    using assms by (auto simp add: abs_mult)
  finally show ?thesis .
qed

(* TODO: refactor! *)
theorem (in real_distribution) Levy_Inversion:
  fixes a b :: real
  assumes "a \<le> b"
  defines "\<mu> \<equiv> measure M" and "\<phi> \<equiv> char M"
  assumes "\<mu> {a} = 0" and "\<mu> {b} = 0"
  shows "(\<lambda>T. 1 / (2 * pi) * (CLBINT t=-T..T. (iexp (-(t * a)) - iexp (-(t * b))) / (\<i> * t) * \<phi> t))
    \<longlonglongrightarrow> \<mu> {a<..b}"
    (is "(\<lambda>T. 1 / (2 * pi) * (CLBINT t=-T..T. ?F t * \<phi> t)) \<longlonglongrightarrow> of_real (\<mu> {a<..b})")
proof -
  interpret P: pair_sigma_finite lborel M ..
  from bounded_Si obtain B where Bprop: "\<And>T. abs (Si T) \<le> B" by auto
  from Bprop [of 0] have [simp]: "B \<ge> 0" by auto
  let ?f = "\<lambda>t x :: real. (iexp (t * (x - a)) - iexp(t * (x - b))) / (\<i> * t)"
  { fix T :: real
    assume "T \<ge> 0"
    let ?f' = "\<lambda>(t, x). indicator {-T<..<T} t *\<^sub>R ?f t x"
    { fix x
      have 1: "complex_interval_lebesgue_integrable lborel u v (\<lambda>t. ?f t x)" for u v :: real
        using Levy_Inversion_aux2[of "x - b" "x - a"]
        apply (simp add: interval_lebesgue_integrable_def set_integrable_def del: times_divide_eq_left)
        apply (intro integrableI_bounded_set_indicator[where B="b - a"] conjI impI)
        apply (auto intro!: AE_I [of _ _ "{0}"] simp: assms)
        done
      have "(CLBINT t. ?f' (t, x)) = (CLBINT t=-T..T. ?f t x)"
        using \<open>T \<ge> 0\<close> by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def)
      also have "\<dots> = (CLBINT t=-T..(0 :: real). ?f t x) + (CLBINT t=(0 :: real)..T. ?f t x)"
          (is "_ = _ + ?t")
        using 1 by (intro interval_integral_sum[symmetric]) (simp add: min_absorb1 max_absorb2 \<open>T \<ge> 0\<close>)
      also have "(CLBINT t=-T..(0 :: real). ?f t x) = (CLBINT t=(0::real)..T. ?f (-t) x)"
        by (subst interval_integral_reflect) auto
      also have "\<dots> + ?t = (CLBINT t=(0::real)..T. ?f (-t) x + ?f t x)"
        using 1
        by (intro interval_lebesgue_integral_add(2) [symmetric] interval_integrable_mirror[THEN iffD2]) simp_all
      also have "\<dots> = (CLBINT t=(0::real)..T. ((iexp(t * (x - a)) - iexp (-(t * (x - a)))) -
          (iexp(t * (x - b)) - iexp (-(t * (x - b))))) / (\<i> * t))"
        using \<open>T \<ge> 0\<close> by (intro interval_integral_cong) (auto simp add: field_split_simps)
      also have "\<dots> = (CLBINT t=(0::real)..T. complex_of_real(
          2 * (sin (t * (x - a)) / t) - 2 * (sin (t * (x - b)) / t)))"
        using \<open>T \<ge> 0\<close>
        apply (intro interval_integral_cong)
        apply (simp add: field_simps cis.ctr Im_divide Re_divide Im_exp Re_exp complex_eq_iff)
        unfolding minus_diff_eq[symmetric, of "y * x" "y * a" for y a] sin_minus cos_minus
        apply (simp add: field_simps power2_eq_square)
        done
      also have "\<dots> = complex_of_real (LBINT t=(0::real)..T.
          2 * (sin (t * (x - a)) / t) - 2 * (sin (t * (x - b)) / t))"
        by (rule interval_lebesgue_integral_of_real)
      also have "\<dots> = complex_of_real (2 * (sgn (x - a) * Si (T * abs (x - a)) -
          sgn (x - b) * Si (T * abs (x - b))))"
        apply (subst interval_lebesgue_integral_diff)
        apply (rule interval_lebesgue_integrable_mult_right, rule integrable_sinc')+
        apply (subst interval_lebesgue_integral_mult_right)+
        apply (simp add: zero_ereal_def[symmetric] LBINT_I0c_sin_scale_divide[OF \<open>T \<ge> 0\<close>])
        done
      finally have "(CLBINT t. ?f' (t, x)) =
          2 * (sgn (x - a) * Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))" .
    } note main_eq = this
    have "(CLBINT t=-T..T. ?F t * \<phi> t) =
      (CLBINT t. (CLINT x | M. ?F t * iexp (t * x) * indicator {-T<..<T} t))"
      using \<open>T \<ge> 0\<close> unfolding \<phi>_def char_def interval_lebesgue_integral_def set_lebesgue_integral_def
      by (auto split: split_indicator intro!: Bochner_Integration.integral_cong)
    also have "\<dots> = (CLBINT t. (CLINT x | M. ?f' (t, x)))"
      by (auto intro!: Bochner_Integration.integral_cong simp: field_simps exp_diff exp_minus split: split_indicator)
    also have "\<dots> = (CLINT x | M. (CLBINT t. ?f' (t, x)))"
    proof (intro P.Fubini_integral [symmetric] integrableI_bounded_set [where B="b - a"])
      show "emeasure (lborel \<Otimes>\<^sub>M M) ({- T<..<T} \<times> space M) < \<infinity>"
        using \<open>T \<ge> 0\<close>
        by (subst emeasure_pair_measure_Times)
           (auto simp: ennreal_mult_less_top not_less top_unique)
      show "AE x\<in>{- T<..<T} \<times> space M in lborel \<Otimes>\<^sub>M M. cmod (case x of (t, x) \<Rightarrow> ?f' (t, x)) \<le> b - a"
        using Levy_Inversion_aux2[of "x - b" "x - a" for x] \<open>a \<le> b\<close>
        by (intro AE_I [of _ _ "{0} \<times> UNIV"]) (force simp: emeasure_pair_measure_Times)+
    qed (auto split: split_indicator split_indicator_asm)
    also have "\<dots> = (CLINT x | M. (complex_of_real (2 * (sgn (x - a) *
         Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))))"
       using main_eq by (intro Bochner_Integration.integral_cong, auto)
    also have "\<dots> = complex_of_real (LINT x | M. (2 * (sgn (x - a) *
         Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))))"
       by (rule integral_complex_of_real)
    finally have "(CLBINT t=-T..T. ?F t * \<phi> t) =
        complex_of_real (LINT x | M. (2 * (sgn (x - a) *
         Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))))" .
  } note main_eq2 = this

  have "(\<lambda>T :: nat. LINT x | M. (2 * (sgn (x - a) *
         Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))) \<longlonglongrightarrow>
       (LINT x | M. 2 * pi * indicator {a<..b} x)"
  proof (rule integral_dominated_convergence [where w="\<lambda>x. 4 * B"])
    show "integrable M (\<lambda>x. 4 * B)"
      by (rule integrable_const_bound [of _ "4 * B"]) auto
  next
    let ?S = "\<lambda>n::nat. \<lambda>x. sgn (x - a) * Si (n * \<bar>x - a\<bar>) - sgn (x - b) * Si (n * \<bar>x - b\<bar>)"
    { fix n x
      have "norm (?S n x) \<le> norm (sgn (x - a) * Si (n * \<bar>x - a\<bar>)) + norm (sgn (x - b) * Si (n * \<bar>x - b\<bar>))"
        by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> B + B"
        using Bprop by (intro add_mono) (auto simp: abs_mult abs_sgn_eq)
      finally have "norm (2 * ?S n x) \<le> 4 * B"
        by simp }
    then show "\<And>n. AE x in M. norm (2 * ?S n x) \<le> 4 * B"
      by auto
    have "AE x in M. x \<noteq> a" "AE x in M. x \<noteq> b"
      using prob_eq_0[of "{a}"] prob_eq_0[of "{b}"] \<open>\<mu> {a} = 0\<close> \<open>\<mu> {b} = 0\<close> by (auto simp: \<mu>_def)
    then show "AE x in M. (\<lambda>n. 2 * ?S n x) \<longlonglongrightarrow> 2 * pi * indicator {a<..b} x"
    proof eventually_elim
      fix x assume x: "x \<noteq> a" "x \<noteq> b"
      then have "(\<lambda>n. 2 * (sgn (x - a) * Si (\<bar>x - a\<bar> * n) - sgn (x - b) * Si (\<bar>x - b\<bar> * n)))
          \<longlonglongrightarrow> 2 * (sgn (x - a) * (pi / 2) - sgn (x - b) * (pi / 2))"
        by (intro tendsto_intros filterlim_compose[OF Si_at_top]
            filterlim_tendsto_pos_mult_at_top[OF tendsto_const] filterlim_real_sequentially)
           auto
      also have "(\<lambda>n. 2 * (sgn (x - a) * Si (\<bar>x - a\<bar> * n) - sgn (x - b) * Si (\<bar>x - b\<bar> * n))) = (\<lambda>n. 2 * ?S n x)"
        by (auto simp: ac_simps)
      also have "2 * (sgn (x - a) * (pi / 2) - sgn (x - b) * (pi / 2)) = 2 * pi * indicator {a<..b} x"
        using x \<open>a \<le> b\<close> by (auto split: split_indicator)
      finally show "(\<lambda>n. 2 * ?S n x) \<longlonglongrightarrow> 2 * pi * indicator {a<..b} x" .
    qed
  qed simp_all
  also have "(LINT x | M. 2 * pi * indicator {a<..b} x) = 2 * pi * \<mu> {a<..b}"
    by (simp add: \<mu>_def)
  finally have "(\<lambda>T. LINT x | M. (2 * (sgn (x - a) *
         Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))) \<longlonglongrightarrow>
       2 * pi * \<mu> {a<..b}" .
  with main_eq2 show ?thesis
    by (auto intro!: tendsto_eq_intros)
qed

theorem Levy_uniqueness:
  fixes M1 M2 :: "real measure"
  assumes "real_distribution M1" "real_distribution M2" and
    "char M1 = char M2"
  shows "M1 = M2"
proof -
  interpret M1: real_distribution M1 by (rule assms)
  interpret M2: real_distribution M2 by (rule assms)
  have "countable ({x. measure M1 {x} \<noteq> 0} \<union> {x. measure M2 {x} \<noteq> 0})"
    by (intro countable_Un M2.countable_support M1.countable_support)
  then have count: "countable {x. measure M1 {x} \<noteq> 0 \<or> measure M2 {x} \<noteq> 0}"
    by (simp add: Un_def)

  have "cdf M1 = cdf M2"
  proof (rule ext)
    fix x
    let ?D = "\<lambda>x. \<bar>cdf M1 x - cdf M2 x\<bar>"

    { fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      have "(?D \<longlongrightarrow> 0) at_bot"
        using M1.cdf_lim_at_bot M2.cdf_lim_at_bot by (intro tendsto_eq_intros) auto
      then have "eventually (\<lambda>y. ?D y < \<epsilon> / 2 \<and> y \<le> x) at_bot"
        using \<open>\<epsilon> > 0\<close> by (simp only: tendsto_iff dist_real_def diff_0_right eventually_conj eventually_le_at_bot abs_idempotent)
      then obtain M where "\<And>y. y \<le> M \<Longrightarrow> ?D y < \<epsilon> / 2" "M \<le> x"
        unfolding eventually_at_bot_linorder by auto
      with open_minus_countable[OF count, of "{..< M}"] obtain a where
        "measure M1 {a} = 0" "measure M2 {a} = 0" "a < M" "a \<le> x" and 1: "?D a < \<epsilon> / 2"
        by auto

      have "(?D \<longlongrightarrow> ?D x) (at_right x)"
        using M1.cdf_is_right_cont [of x] M2.cdf_is_right_cont [of x]
        by (intro tendsto_intros) (auto simp add: continuous_within)
      then have "eventually (\<lambda>y. \<bar>?D y - ?D x\<bar> < \<epsilon> / 2) (at_right x)"
        using \<open>\<epsilon> > 0\<close> by (simp only: tendsto_iff dist_real_def eventually_conj eventually_at_right_less)
      then obtain N where "N > x" "\<And>y. x < y \<Longrightarrow> y < N \<Longrightarrow> \<bar>?D y - ?D x\<bar> < \<epsilon> / 2"
        by (auto simp add: eventually_at_right[OF less_add_one])
      with open_minus_countable[OF count, of "{x <..< N}"] obtain b where "x < b" "b < N"
          "measure M1 {b} = 0" "measure M2 {b} = 0" and 2: "\<bar>?D b - ?D x\<bar> < \<epsilon> / 2"
        by (auto simp: abs_minus_commute)
      from \<open>a \<le> x\<close> \<open>x < b\<close> have "a < b" "a \<le> b" by auto

      from \<open>char M1 = char M2\<close>
        M1.Levy_Inversion [OF \<open>a \<le> b\<close> \<open>measure M1 {a} = 0\<close> \<open>measure M1 {b} = 0\<close>]
        M2.Levy_Inversion [OF \<open>a \<le> b\<close> \<open>measure M2 {a} = 0\<close> \<open>measure M2 {b} = 0\<close>]
      have "complex_of_real (measure M1 {a<..b}) = complex_of_real (measure M2 {a<..b})"
        by (intro LIMSEQ_unique) auto
      then have "?D a = ?D b"
        unfolding of_real_eq_iff M1.cdf_diff_eq [OF \<open>a < b\<close>, symmetric] M2.cdf_diff_eq [OF \<open>a < b\<close>, symmetric] by simp
      then have "?D x = \<bar>(?D b - ?D x) - ?D a\<bar>"
        by simp
      also have "\<dots> \<le> \<bar>?D b - ?D x\<bar> + \<bar>?D a\<bar>"
        by (rule abs_triangle_ineq4)
      also have "\<dots> \<le> \<epsilon> / 2 + \<epsilon> / 2"
        using 1 2 by (intro add_mono) auto
      finally have "?D x \<le> \<epsilon>" by simp }
    then show "cdf M1 x = cdf M2 x"
      by (metis abs_le_zero_iff dense_ge eq_iff_diff_eq_0)
  qed
  thus ?thesis
    by (rule cdf_unique [OF \<open>real_distribution M1\<close> \<open>real_distribution M2\<close>])
qed


subsection \<open>The Levy continuity theorem\<close>

theorem levy_continuity1:
  fixes M :: "nat \<Rightarrow> real measure" and M' :: "real measure"
  assumes "\<And>n. real_distribution (M n)" "real_distribution M'" "weak_conv_m M M'"
  shows "(\<lambda>n. char (M n) t) \<longlonglongrightarrow> char M' t"
  unfolding char_def using assms by (rule weak_conv_imp_integral_bdd_continuous_conv) auto

theorem levy_continuity:
  fixes M :: "nat \<Rightarrow> real measure" and M' :: "real measure"
  assumes real_distr_M : "\<And>n. real_distribution (M n)"
    and real_distr_M': "real_distribution M'"
    and char_conv: "\<And>t. (\<lambda>n. char (M n) t) \<longlonglongrightarrow> char M' t"
  shows "weak_conv_m M M'"
proof -
  interpret Mn: real_distribution "M n" for n by fact
  interpret M': real_distribution M' by fact

  have *: "\<And>u x. u > 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (CLBINT t:{-u..u}. 1 - iexp (t * x)) =
      2 * (u  - sin (u * x) / x)"
  proof -
    fix u :: real and x :: real
    assume "u > 0" and "x \<noteq> 0"
    hence "(CLBINT t:{-u..u}. 1 - iexp (t * x)) = (CLBINT t=-u..u. 1 - iexp (t * x))"
      by (subst interval_integral_Icc, auto)
    also have "\<dots> = (CLBINT t=-u..0. 1 - iexp (t * x)) + (CLBINT t=0..u. 1 - iexp (t * x))"
      using \<open>u > 0\<close>
      apply (subst interval_integral_sum)
      apply (simp add: min_absorb1 min_absorb2 max_absorb1 max_absorb2)
      apply (rule interval_integrable_isCont)
      apply auto
      done
    also have "\<dots> = (CLBINT t=ereal 0..u. 1 - iexp (t * -x)) + (CLBINT t=ereal 0..u. 1 - iexp (t * x))"
      apply (subgoal_tac "0 = ereal 0", erule ssubst)
      by (subst interval_integral_reflect, auto)
    also have "\<dots> = (LBINT t=ereal 0..u. 2 - 2 * cos (t * x))"
      apply (subst interval_lebesgue_integral_add (2) [symmetric])
      apply ((rule interval_integrable_isCont, auto)+) [2]
      unfolding exp_Euler cos_of_real
      apply (simp add: of_real_mult interval_lebesgue_integral_of_real[symmetric])
      done
    also have "\<dots> = 2 * u - 2 * sin (u * x) / x"
      by (subst interval_lebesgue_integral_diff)
         (auto intro!: interval_integrable_isCont
               simp: interval_lebesgue_integral_of_real integral_cos [OF \<open>x \<noteq> 0\<close>] mult.commute[of _ x])
    finally show "(CLBINT t:{-u..u}. 1 - iexp (t * x)) = 2 * (u  - sin (u * x) / x)"
      by (simp add: field_simps)
  qed
  have main_bound: "\<And>u n. u > 0 \<Longrightarrow> Re (CLBINT t:{-u..u}. 1 - char (M n) t) \<ge>
    u * measure (M n) {x. abs x \<ge> 2 / u}"
  proof -
    fix u :: real and n
    assume "u > 0"
    interpret P: pair_sigma_finite "M n" lborel ..
    (* TODO: put this in the real_distribution locale as a simp rule? *)
    have Mn1 [simp]: "measure (M n) UNIV = 1" by (metis Mn.prob_space Mn.space_eq_univ)
    (* TODO: make this automatic somehow? *)
    have Mn2 [simp]: "\<And>x. complex_integrable (M n) (\<lambda>t. exp (\<i> * complex_of_real (x * t)))"
      by (rule Mn.integrable_const_bound [where B = 1], auto)
    have Mn3: "set_integrable (M n \<Otimes>\<^sub>M lborel) (UNIV \<times> {- u..u}) (\<lambda>a. 1 - exp (\<i> * complex_of_real (snd a * fst a)))"
      using \<open>0 < u\<close>
      unfolding set_integrable_def
      by (intro integrableI_bounded_set_indicator [where B="2"])
         (auto simp: lborel.emeasure_pair_measure_Times ennreal_mult_less_top not_less top_unique
               split: split_indicator
               intro!: order_trans [OF norm_triangle_ineq4])
    have "(CLBINT t:{-u..u}. 1 - char (M n) t) =
        (CLBINT t:{-u..u}. (CLINT x | M n. 1 - iexp (t * x)))"
      unfolding char_def by (rule set_lebesgue_integral_cong, auto simp del: of_real_mult)
    also have "\<dots> = (CLBINT t. (CLINT x | M n. indicator {-u..u} t *\<^sub>R (1 - iexp (t * x))))"
      unfolding set_lebesgue_integral_def
      by (rule Bochner_Integration.integral_cong) (auto split: split_indicator)
    also have "\<dots> = (CLINT x | M n. (CLBINT t:{-u..u}. 1 - iexp (t * x)))"
      using Mn3 by (subst P.Fubini_integral) (auto simp: indicator_times split_beta' set_integrable_def set_lebesgue_integral_def)
    also have "\<dots> = (CLINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))"
      using \<open>u > 0\<close> by (intro Bochner_Integration.integral_cong, auto simp add: * simp del: of_real_mult)
    also have "\<dots> = (LINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))"
      by (rule integral_complex_of_real)
    finally have "Re (CLBINT t:{-u..u}. 1 - char (M n) t) =
       (LINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))" by simp
    also have "\<dots> \<ge> (LINT x : {x. abs x \<ge> 2 / u} | M n. u)"
    proof -
      have "complex_integrable (M n) (\<lambda>x. CLBINT t:{-u..u}. 1 - iexp (snd (x, t) * fst (x, t)))"
        using Mn3 unfolding set_integrable_def set_lebesgue_integral_def
        by (intro P.integrable_fst) (simp add: indicator_times split_beta')
      hence "complex_integrable (M n) (\<lambda>x. if x = 0 then 0 else 2 * (u  - sin (u * x) / x))"
        using \<open>u > 0\<close>
        unfolding set_integrable_def
        by (subst integrable_cong) (auto simp add: * simp del: of_real_mult)
      hence **: "integrable (M n) (\<lambda>x. if x = 0 then 0 else 2 * (u  - sin (u * x) / x))"
        unfolding complex_of_real_integrable_eq .
      have "2 * sin x \<le> x" if "2 \<le> x" for x :: real
        by (rule order_trans[OF _ \<open>2 \<le> x\<close>]) auto
      moreover have "x \<le> 2 * sin x" if "x \<le> - 2" for x :: real
        by (rule order_trans[OF \<open>x \<le> - 2\<close>]) auto
      moreover have "x < 0 \<Longrightarrow> x \<le> sin x" for x :: real
        using sin_x_le_x[of "-x"] by simp
      ultimately show ?thesis
        using \<open>u > 0\<close> unfolding set_lebesgue_integral_def
        by (intro integral_mono [OF _ **])
           (auto simp: divide_simps sin_x_le_x mult.commute[of u] mult_neg_pos top_unique less_top[symmetric]
                 split: split_indicator)
    qed
    also (xtrans) have "(LINT x : {x. abs x \<ge> 2 / u} | M n. u) = u * measure (M n) {x. abs x \<ge> 2 / u}"
      unfolding set_lebesgue_integral_def
      by (simp add: Mn.emeasure_eq_measure)
    finally show "Re (CLBINT t:{-u..u}. 1 - char (M n) t) \<ge> u * measure (M n) {x. abs x \<ge> 2 / u}" .
  qed

  have tight_aux: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>a b. a < b \<and> (\<forall>n. 1 - \<epsilon> < measure (M n) {a<..b})"
  proof -
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    note M'.isCont_char [of 0]
    hence "\<exists>d>0. \<forall>t. abs t < d \<longrightarrow> cmod (char M' t - 1) < \<epsilon> / 4"
      apply (subst (asm) continuous_at_eps_delta)
      apply (drule_tac x = "\<epsilon> / 4" in spec)
      using \<open>\<epsilon> > 0\<close> by (auto simp add: dist_real_def dist_complex_def M'.char_zero)
    then obtain d where "d > 0 \<and> (\<forall>t. (abs t < d \<longrightarrow> cmod (char M' t - 1) < \<epsilon> / 4))" ..
    hence d0: "d > 0" and d1: "\<And>t. abs t < d \<Longrightarrow> cmod (char M' t - 1) < \<epsilon> / 4" by auto
    have 1: "\<And>x. cmod (1 - char M' x) \<le> 2"
      by (rule order_trans [OF norm_triangle_ineq4], auto simp add: M'.cmod_char_le_1)
    then have 2: "\<And>u v. complex_set_integrable lborel {u..v} (\<lambda>x. 1 - char M' x)"
      unfolding set_integrable_def
      by (intro integrableI_bounded_set_indicator[where B=2]) (auto simp: emeasure_lborel_Icc_eq)
    have 3: "\<And>u v. integrable lborel (\<lambda>x. indicat_real {u..v} x *\<^sub>R cmod (1 - char M' x))"
      by (intro borel_integrable_compact[OF compact_Icc] continuous_at_imp_continuous_on
                continuous_intros ballI M'.isCont_char continuous_intros)
    have "cmod (CLBINT t:{-d/2..d/2}. 1 - char M' t) \<le> LBINT t:{-d/2..d/2}. cmod (1 - char M' t)"
      unfolding set_lebesgue_integral_def
      using integral_norm_bound[of _ "\<lambda>x. indicator {u..v} x *\<^sub>R (1 - char M' x)" for u v] by simp
    also have 4: "\<dots> \<le> LBINT t:{-d/2..d/2}. \<epsilon> / 4"
      unfolding set_lebesgue_integral_def
      apply (rule integral_mono [OF 3])
       apply (simp add: emeasure_lborel_Icc_eq)
      apply (case_tac "x \<in> {-d/2..d/2}")
       apply auto
      apply (subst norm_minus_commute)
      apply (rule less_imp_le)
      apply (rule d1 [simplified])
      using d0 apply auto
      done
    also from d0 4 have "\<dots> = d * \<epsilon> / 4"
      unfolding set_lebesgue_integral_def by simp
    finally have bound: "cmod (CLBINT t:{-d/2..d/2}. 1 - char M' t) \<le> d * \<epsilon> / 4" .
    have "cmod (1 - char (M n) x) \<le> 2" for n x
      by (rule order_trans [OF norm_triangle_ineq4], auto simp add: Mn.cmod_char_le_1)
    then have "(\<lambda>n. CLBINT t:{-d/2..d/2}. 1 - char (M n) t) \<longlonglongrightarrow> (CLBINT t:{-d/2..d/2}. 1 - char M' t)"
      unfolding set_lebesgue_integral_def
      apply (intro integral_dominated_convergence[where w="\<lambda>x. indicator {-d/2..d/2} x *\<^sub>R 2"])
      apply (auto intro!: char_conv tendsto_intros
                  simp: emeasure_lborel_Icc_eq
                  split: split_indicator)
      done
    hence "eventually (\<lambda>n. cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
        (CLBINT t:{-d/2..d/2}. 1 - char M' t)) < d * \<epsilon> / 4) sequentially"
      using d0 \<open>\<epsilon> > 0\<close> apply (subst (asm) tendsto_iff)
      by (subst (asm) dist_complex_def, drule spec, erule mp, auto)
    hence "\<exists>N. \<forall>n \<ge> N. cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
        (CLBINT t:{-d/2..d/2}. 1 - char M' t)) < d * \<epsilon> / 4" by (simp add: eventually_sequentially)
    then obtain N
      where "\<forall>n\<ge>N. cmod ((CLBINT t:{- d / 2..d / 2}. 1 - char (M n) t) -
        (CLBINT t:{- d / 2..d / 2}. 1 - char M' t)) < d * \<epsilon> / 4" ..
    hence N: "\<And>n. n \<ge> N \<Longrightarrow> cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
        (CLBINT t:{-d/2..d/2}. 1 - char M' t)) < d * \<epsilon> / 4" by auto
    { fix n
      assume "n \<ge> N"
      have "cmod (CLBINT t:{-d/2..d/2}. 1 - char (M n) t) =
        cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) - (CLBINT t:{-d/2..d/2}. 1 - char M' t)
          + (CLBINT t:{-d/2..d/2}. 1 - char M' t))" by simp
      also have "\<dots> \<le> cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
          (CLBINT t:{-d/2..d/2}. 1 - char M' t)) + cmod(CLBINT t:{-d/2..d/2}. 1 - char M' t)"
        by (rule norm_triangle_ineq)
      also have "\<dots> < d * \<epsilon> / 4 + d * \<epsilon> / 4"
        by (rule add_less_le_mono [OF N [OF \<open>n \<ge> N\<close>] bound])
      also have "\<dots> = d * \<epsilon> / 2" by auto
      finally have "cmod (CLBINT t:{-d/2..d/2}. 1 - char (M n) t) < d * \<epsilon> / 2" .
      hence "d * \<epsilon> / 2 > Re (CLBINT t:{-d/2..d/2}. 1 - char (M n) t)"
        by (rule order_le_less_trans [OF complex_Re_le_cmod])
      hence "d * \<epsilon> / 2 > Re (CLBINT t:{-(d/2)..d/2}. 1 - char (M n) t)" (is "_ > ?lhs") by simp
      also have "?lhs \<ge> (d / 2) * measure (M n) {x. abs x \<ge> 2 / (d / 2)}"
        using d0 by (intro main_bound, simp)
      finally (xtrans) have "d * \<epsilon> / 2 > (d / 2) * measure (M n) {x. abs x \<ge> 2 / (d / 2)}" .
      with d0 \<open>\<epsilon> > 0\<close> have "\<epsilon> > measure (M n) {x. abs x \<ge> 2 / (d / 2)}" by (simp add: field_simps)
      hence "\<epsilon> > 1 - measure (M n) (UNIV - {x. abs x \<ge> 2 / (d / 2)})"
        apply (subst Mn.borel_UNIV [symmetric])
        by (subst Mn.prob_compl, auto)
      also have "UNIV - {x. abs x \<ge> 2 / (d / 2)} = {x. -(4 / d) < x \<and> x < (4 / d)}"
        using d0 apply (auto simp add: field_simps)
        (* very annoying -- this should be automatic *)
        apply (case_tac "x \<ge> 0", auto simp add: field_simps)
        apply (subgoal_tac "0 \<le> x * d", arith, rule mult_nonneg_nonneg, auto)
        apply (case_tac "x \<ge> 0", auto simp add: field_simps)
        apply (subgoal_tac "x * d \<le> 0", arith)
        apply (rule mult_nonpos_nonneg, auto)
        by (case_tac "x \<ge> 0", auto simp add: field_simps)
      finally have "measure (M n) {x. -(4 / d) < x \<and> x < (4 / d)} > 1 - \<epsilon>"
        by auto
    } note 6 = this
    { fix n :: nat
      have *: "(UN (k :: nat). {- real k<..real k}) = UNIV"
        by (auto, metis leI le_less_trans less_imp_le minus_less_iff reals_Archimedean2)
      have "(\<lambda>k. measure (M n) {- real k<..real k}) \<longlonglongrightarrow>
          measure (M n) (UN (k :: nat). {- real k<..real k})"
        by (rule Mn.finite_Lim_measure_incseq, auto simp add: incseq_def)
      hence "(\<lambda>k. measure (M n) {- real k<..real k}) \<longlonglongrightarrow> 1"
        using Mn.prob_space unfolding * Mn.borel_UNIV by simp
      hence "eventually (\<lambda>k. measure (M n) {- real k<..real k} > 1 - \<epsilon>) sequentially"
        apply (elim order_tendstoD (1))
        using \<open>\<epsilon> > 0\<close> by auto
    } note 7 = this
    { fix n :: nat
      have "eventually (\<lambda>k. \<forall>m < n. measure (M m) {- real k<..real k} > 1 - \<epsilon>) sequentially"
        (is "?P n")
      proof (induct n)
        case (Suc n) with 7[of n] show ?case
          by eventually_elim (auto simp add: less_Suc_eq)
      qed simp
    } note 8 = this
    from 8 [of N] have "\<exists>K :: nat. \<forall>k \<ge> K. \<forall>m<N. 1 - \<epsilon> <
        Sigma_Algebra.measure (M m) {- real k<..real k}"
      by (auto simp add: eventually_sequentially)
    hence "\<exists>K :: nat. \<forall>m<N. 1 - \<epsilon> < Sigma_Algebra.measure (M m) {- real K<..real K}" by auto
    then obtain K :: nat where
      "\<forall>m<N. 1 - \<epsilon> < Sigma_Algebra.measure (M m) {- real K<..real K}" ..
    hence K: "\<And>m. m < N \<Longrightarrow> 1 - \<epsilon> < Sigma_Algebra.measure (M m) {- real K<..real K}"
      by auto
    let ?K' = "max K (4 / d)"
    have "-?K' < ?K' \<and> (\<forall>n. 1 - \<epsilon> < measure (M n) {-?K'<..?K'})"
      using d0 apply auto
      apply (rule max.strict_coboundedI2, auto)
    proof -
      fix n
      show " 1 - \<epsilon> < measure (M n) {- max (real K) (4 / d)<..max (real K) (4 / d)}"
        apply (case_tac "n < N")
        apply (rule order_less_le_trans)
        apply (erule K)
        apply (rule Mn.finite_measure_mono, auto)
        apply (rule order_less_le_trans)
        apply (rule 6, erule leI)
        by (rule Mn.finite_measure_mono, auto)
    qed
    thus "\<exists>a b. a < b \<and> (\<forall>n. 1 - \<epsilon> < measure (M n) {a<..b})" by (intro exI)
  qed
  have tight: "tight M"
    by (auto simp: tight_def intro: assms tight_aux)
  show ?thesis
  proof (rule tight_subseq_weak_converge [OF real_distr_M real_distr_M' tight])
    fix s \<nu>
    assume s: "strict_mono (s :: nat \<Rightarrow> nat)"
    assume nu: "weak_conv_m (M \<circ> s) \<nu>"
    assume *: "real_distribution \<nu>"
    have 2: "\<And>n. real_distribution ((M \<circ> s) n)" unfolding comp_def by (rule assms)
    have 3: "\<And>t. (\<lambda>n. char ((M \<circ> s) n) t) \<longlonglongrightarrow> char \<nu> t" by (intro levy_continuity1 [OF 2 * nu])
    have 4: "\<And>t. (\<lambda>n. char ((M \<circ> s) n) t) = ((\<lambda>n. char (M n) t) \<circ> s)" by (rule ext, simp)
    have 5: "\<And>t. (\<lambda>n. char ((M \<circ> s) n) t) \<longlonglongrightarrow> char M' t"
      by (subst 4, rule LIMSEQ_subseq_LIMSEQ [OF _ s], rule assms)
    hence "char \<nu> = char M'" by (intro ext, intro LIMSEQ_unique [OF 3 5])
    hence "\<nu> = M'" by (rule Levy_uniqueness [OF * \<open>real_distribution M'\<close>])
    thus "weak_conv_m (M \<circ> s) M'"
      by (elim subst) (rule nu)
  qed
qed

end
