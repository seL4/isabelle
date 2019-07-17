(*  Title:     HOL/Probability/Characteristic_Functions.thy
    Authors:   Jeremy Avigad (CMU), Luke Serafin (CMU), Johannes Hölzl (TUM)
*)

section \<open>Characteristic Functions\<close>

theory Characteristic_Functions
  imports Weak_Convergence Independent_Family Distributions
begin

lemma mult_min_right: "a \<ge> 0 \<Longrightarrow> (a :: real) * min b c = min (a * b) (a * c)"
  by (metis min.absorb_iff2 min_def mult_left_mono)

lemma sequentially_even_odd:
  assumes E: "eventually (\<lambda>n. P (2 * n)) sequentially" and O: "eventually (\<lambda>n. P (2 * n + 1)) sequentially"
  shows "eventually P sequentially"
proof -
  from E obtain n_e where [intro]: "\<And>n. n \<ge> n_e \<Longrightarrow> P (2 * n)"
    by (auto simp: eventually_sequentially)
  moreover
  from O obtain n_o where [intro]: "\<And>n. n \<ge> n_o \<Longrightarrow> P (Suc (2 * n))"
    by (auto simp: eventually_sequentially)
  show ?thesis
    unfolding eventually_sequentially
  proof (intro exI allI impI)
    fix n assume "max (2 * n_e) (2 * n_o + 1) \<le> n" then show "P n"
      by (cases "even n") (auto elim!: evenE oddE )
  qed
qed

lemma limseq_even_odd:
  assumes "(\<lambda>n. f (2 * n)) \<longlonglongrightarrow> (l :: 'a :: topological_space)"
      and "(\<lambda>n. f (2 * n + 1)) \<longlonglongrightarrow> l"
  shows "f \<longlonglongrightarrow> l"
  using assms by (auto simp: filterlim_iff intro: sequentially_even_odd)

subsection \<open>Application of the FTC: integrating $e^ix$\<close>

abbreviation iexp :: "real \<Rightarrow> complex" where
  "iexp \<equiv> (\<lambda>x. exp (\<i> * complex_of_real x))"

lemma isCont_iexp [simp]: "isCont iexp x"
  by (intro continuous_intros)

lemma has_vector_derivative_iexp[derivative_intros]:
  "(iexp has_vector_derivative \<i> * iexp x) (at x within s)"
  by (auto intro!: derivative_eq_intros simp: Re_exp Im_exp has_vector_derivative_complex_iff)

lemma interval_integral_iexp:
  fixes a b :: real
  shows "(CLBINT x=a..b. iexp x) = \<i> * iexp a - \<i> * iexp b"
  by (subst interval_integral_FTC_finite [where F = "\<lambda>x. -\<i> * iexp x"])
     (auto intro!: derivative_eq_intros continuous_intros)

subsection \<open>The Characteristic Function of a Real Measure.\<close>

definition
  char :: "real measure \<Rightarrow> real \<Rightarrow> complex"
where
  "char M t = CLINT x|M. iexp (t * x)"

lemma (in real_distribution) char_zero: "char M 0 = 1"
  unfolding char_def by (simp del: space_eq_univ add: prob_space)

lemma (in prob_space) integrable_iexp:
  assumes f: "f \<in> borel_measurable M" "\<And>x. Im (f x) = 0"
  shows "integrable M (\<lambda>x. exp (\<i> * (f x)))"
proof (intro integrable_const_bound [of _ 1])
  from f have "\<And>x. of_real (Re (f x)) = f x"
    by (simp add: complex_eq_iff)
  then show "AE x in M. cmod (exp (\<i> * f x)) \<le> 1"
    using norm_exp_i_times[of "Re (f x)" for x] by simp
qed (insert f, simp)

lemma (in real_distribution) cmod_char_le_1: "norm (char M t) \<le> 1"
proof -
  have "norm (char M t) \<le> (\<integral>x. norm (iexp (t * x)) \<partial>M)"
    unfolding char_def by (intro integral_norm_bound)
  also have "\<dots> \<le> 1"
    by (simp del: of_real_mult)
  finally show ?thesis .
qed

lemma (in real_distribution) isCont_char: "isCont (char M) t"
  unfolding continuous_at_sequentially
proof safe
  fix X assume X: "X \<longlonglongrightarrow> t"
  show "(char M \<circ> X) \<longlonglongrightarrow> char M t"
    unfolding comp_def char_def
    by (rule integral_dominated_convergence[where w="\<lambda>_. 1"]) (auto intro!: tendsto_intros X)
qed

lemma (in real_distribution) char_measurable [measurable]: "char M \<in> borel_measurable borel"
  by (auto intro!: borel_measurable_continuous_onI continuous_at_imp_continuous_on isCont_char)

subsection \<open>Independence\<close>

(* the automation can probably be improved *)
lemma (in prob_space) char_distr_add:
  fixes X1 X2 :: "'a \<Rightarrow> real" and t :: real
  assumes "indep_var borel X1 borel X2"
  shows "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t =
    char (distr M borel X1) t * char (distr M borel X2) t"
proof -
  from assms have [measurable]: "random_variable borel X1" by (elim indep_var_rv1)
  from assms have [measurable]: "random_variable borel X2" by (elim indep_var_rv2)

  have "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t = (CLINT x|M. iexp (t * (X1 x + X2 x)))"
    by (simp add: char_def integral_distr)
  also have "\<dots> = (CLINT x|M. iexp (t * (X1 x)) * iexp (t * (X2 x))) "
    by (simp add: field_simps exp_add)
  also have "\<dots> = (CLINT x|M. iexp (t * (X1 x))) * (CLINT x|M. iexp (t * (X2 x)))"
    by (intro indep_var_lebesgue_integral indep_var_compose[unfolded comp_def, OF assms])
       (auto intro!: integrable_iexp)
  also have "\<dots> = char (distr M borel X1) t * char (distr M borel X2) t"
    by (simp add: char_def integral_distr)
  finally show ?thesis .
qed

lemma (in prob_space) char_distr_sum:
  "indep_vars (\<lambda>i. borel) X A \<Longrightarrow>
    char (distr M borel (\<lambda>\<omega>. \<Sum>i\<in>A. X i \<omega>)) t = (\<Prod>i\<in>A. char (distr M borel (X i)) t)"
proof (induct A rule: infinite_finite_induct)
  case (insert x F) with indep_vars_subset[of "\<lambda>_. borel" X "insert x F" F] show ?case
    by (auto simp add: char_distr_add indep_vars_sum)
qed (simp_all add: char_def integral_distr prob_space del: distr_const)

subsection \<open>Approximations to $e^{ix}$\<close>

text \<open>Proofs from Billingsley, page 343.\<close>

lemma CLBINT_I0c_power_mirror_iexp:
  fixes x :: real and n :: nat
  defines "f s m \<equiv> complex_of_real ((x - s) ^ m)"
  shows "(CLBINT s=0..x. f s n * iexp s) =
    x^Suc n / Suc n + (\<i> / Suc n) * (CLBINT s=0..x. f s (Suc n) * iexp s)"
proof -
  have 1:
    "((\<lambda>s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * iexp s)
      has_vector_derivative complex_of_real((x - s)^n) * iexp s + (\<i> * iexp s) * complex_of_real(-((x - s) ^ (Suc n) / (Suc n))))
      (at s within A)" for s A
    by (intro derivative_eq_intros) auto

  let ?F = "\<lambda>s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * iexp s"
  have "x^(Suc n) / (Suc n) = (CLBINT s=0..x. (f s n * iexp s + (\<i> * iexp s) * -(f s (Suc n) / (Suc n))))" (is "?LHS = ?RHS")
  proof -
    have "?RHS = (CLBINT s=0..x. (f s n * iexp s + (\<i> * iexp s) *
      complex_of_real(-((x - s) ^ (Suc n) / (Suc n)))))"
      by (cases "0 \<le> x") (auto intro!: simp: f_def[abs_def])
    also have "... = ?F x - ?F 0"
      unfolding zero_ereal_def using 1
      by (intro interval_integral_FTC_finite)
         (auto simp: f_def add_nonneg_eq_0_iff complex_eq_iff
               intro!: continuous_at_imp_continuous_on continuous_intros)
    finally show ?thesis
      by auto
  qed
  show ?thesis
    unfolding \<open>?LHS = ?RHS\<close> f_def interval_lebesgue_integral_mult_right [symmetric]
    by (subst interval_lebesgue_integral_add(2) [symmetric])
       (auto intro!: interval_integrable_isCont continuous_intros simp: zero_ereal_def complex_eq_iff)
qed

lemma iexp_eq1:
  fixes x :: real
  defines "f s m \<equiv> complex_of_real ((x - s) ^ m)"
  shows "iexp x =
    (\<Sum>k \<le> n. (\<i> * x)^k / (fact k)) + ((\<i> ^ (Suc n)) / (fact n)) * (CLBINT s=0..x. (f s n) * (iexp s))" (is "?P n")
proof (induction n)
  show "?P 0"
    by (auto simp add: field_simps interval_integral_iexp f_def zero_ereal_def)
next
  fix n assume ih: "?P n"
  have **: "\<And>a b :: real. a = -b \<longleftrightarrow> a + b = 0"
    by linarith
  have *: "of_nat n * of_nat (fact n) \<noteq> - (of_nat (fact n)::complex)"
    unfolding of_nat_mult[symmetric]
    by (simp add: complex_eq_iff ** of_nat_add[symmetric] del: of_nat_mult of_nat_fact of_nat_add)
  show "?P (Suc n)"
    unfolding sum.atMost_Suc ih f_def CLBINT_I0c_power_mirror_iexp[of _ n]
    by (simp add: divide_simps add_eq_0_iff *) (simp add: field_simps)
qed

lemma iexp_eq2:
  fixes x :: real
  defines "f s m \<equiv> complex_of_real ((x - s) ^ m)"
  shows "iexp x = (\<Sum>k\<le>Suc n. (\<i>*x)^k/fact k) + \<i>^Suc n/fact n * (CLBINT s=0..x. f s n*(iexp s - 1))"
proof -
  have isCont_f: "isCont (\<lambda>s. f s n) x" for n x
    by (auto simp: f_def)
  let ?F = "\<lambda>s. complex_of_real (-((x - s) ^ (Suc n) / real (Suc n)))"
  have calc1: "(CLBINT s=0..x. f s n * (iexp s - 1)) =
    (CLBINT s=0..x. f s n * iexp s) - (CLBINT s=0..x. f s n)"
    unfolding zero_ereal_def
    by (subst interval_lebesgue_integral_diff(2) [symmetric])
       (simp_all add: interval_integrable_isCont isCont_f field_simps)

  have calc2: "(CLBINT s=0..x. f s n) = x^Suc n / Suc n"
    unfolding zero_ereal_def
  proof (subst interval_integral_FTC_finite [where a = 0 and b = x and f = "\<lambda>s. f s n" and F = ?F])
    show "(?F has_vector_derivative f y n) (at y within {min 0 x..max 0 x})" for y
      unfolding f_def
      by (intro has_vector_derivative_of_real)
         (auto intro!: derivative_eq_intros simp del: power_Suc simp add: add_nonneg_eq_0_iff)
  qed (auto intro: continuous_at_imp_continuous_on isCont_f)

  have calc3: "\<i> ^ (Suc (Suc n)) / (fact (Suc n)) = (\<i> ^ (Suc n) / (fact n)) * (\<i> / (Suc n))"
    by (simp add: field_simps)

  show ?thesis
    unfolding iexp_eq1 [where n = "Suc n" and x=x] calc1 calc2 calc3 unfolding f_def
    by (subst CLBINT_I0c_power_mirror_iexp [where n = n]) auto
qed

lemma abs_LBINT_I0c_abs_power_diff:
  "\<bar>LBINT s=0..x. \<bar>(x - s)^n\<bar>\<bar> = \<bar>x ^ (Suc n) / (Suc n)\<bar>"
proof -
 have "\<bar>LBINT s=0..x. \<bar>(x - s)^n\<bar>\<bar> = \<bar>LBINT s=0..x. (x - s)^n\<bar>"
  proof cases
    assume "0 \<le> x \<or> even n"
    then have "(LBINT s=0..x. \<bar>(x - s)^n\<bar>) = LBINT s=0..x. (x - s)^n"
      by (auto simp add: zero_ereal_def power_even_abs power_abs min_absorb1 max_absorb2
               intro!: interval_integral_cong)
    then show ?thesis by simp
  next
    assume "\<not> (0 \<le> x \<or> even n)"
    then have "(LBINT s=0..x. \<bar>(x - s)^n\<bar>) = LBINT s=0..x. -((x - s)^n)"
      by (auto simp add: zero_ereal_def power_abs min_absorb1 max_absorb2
                         ereal_min[symmetric] ereal_max[symmetric] power_minus_odd[symmetric]
               simp del: ereal_min ereal_max intro!: interval_integral_cong)
    also have "\<dots> = - (LBINT s=0..x. (x - s)^n)"
      by (subst interval_lebesgue_integral_uminus, rule refl)
    finally show ?thesis by simp
  qed
  also have "LBINT s=0..x. (x - s)^n = x^Suc n / Suc n"
  proof -
    let ?F = "\<lambda>t. - ((x - t)^(Suc n) / Suc n)"
    have "LBINT s=0..x. (x - s)^n = ?F x - ?F 0"
      unfolding zero_ereal_def
      by (intro interval_integral_FTC_finite continuous_at_imp_continuous_on
                has_field_derivative_iff_has_vector_derivative[THEN iffD1])
         (auto simp del: power_Suc intro!: derivative_eq_intros simp add: add_nonneg_eq_0_iff)
    also have "\<dots> = x ^ (Suc n) / (Suc n)" by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma iexp_approx1: "cmod (iexp x - (\<Sum>k \<le> n. (\<i> * x)^k / fact k)) \<le> \<bar>x\<bar>^(Suc n) / fact (Suc n)"
proof -
  have "iexp x - (\<Sum>k \<le> n. (\<i> * x)^k / fact k) =
      ((\<i> ^ (Suc n)) / (fact n)) * (CLBINT s=0..x. (x - s)^n * (iexp s))" (is "?t1 = ?t2")
    by (subst iexp_eq1 [of _ n], simp add: field_simps)
  then have "cmod (?t1) = cmod (?t2)"
    by simp
  also have "\<dots> =  (1 / of_nat (fact n)) * cmod (CLBINT s=0..x. (x - s)^n * (iexp s))"
    by (simp add: norm_mult norm_divide norm_power)
  also have "\<dots> \<le> (1 / of_nat (fact n)) * \<bar>LBINT s=0..x. cmod ((x - s)^n * (iexp s))\<bar>"
    by (intro mult_left_mono interval_integral_norm2)
       (auto simp: zero_ereal_def intro: interval_integrable_isCont)
  also have "\<dots> \<le> (1 / of_nat (fact n)) * \<bar>LBINT s=0..x. \<bar>(x - s)^n\<bar>\<bar>"
    by (simp add: norm_mult del: of_real_diff of_real_power)
  also have "\<dots> \<le> (1 / of_nat (fact n)) * \<bar>x ^ (Suc n) / (Suc n)\<bar>"
    by (simp add: abs_LBINT_I0c_abs_power_diff)
  also have "1 / real_of_nat (fact n::nat) * \<bar>x ^ Suc n / real (Suc n)\<bar> =
      \<bar>x\<bar> ^ Suc n / fact (Suc n)"
    by (simp add: abs_mult power_abs)
  finally show ?thesis .
qed

lemma iexp_approx2: "cmod (iexp x - (\<Sum>k \<le> n. (\<i> * x)^k / fact k)) \<le> 2 * \<bar>x\<bar>^n / fact n"
proof (induction n) \<comment> \<open>really cases\<close>
  case (Suc n)
  have *: "\<And>a b. interval_lebesgue_integrable lborel a b f \<Longrightarrow> interval_lebesgue_integrable lborel a b g \<Longrightarrow>
      \<bar>LBINT s=a..b. f s\<bar> \<le> \<bar>LBINT s=a..b. g s\<bar>"
    if f: "\<And>s. 0 \<le> f s" and g: "\<And>s. f s \<le> g s" for f g :: "_ \<Rightarrow> real"
    using order_trans[OF f g] f g 
    unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def set_lebesgue_integral_def set_integrable_def
    by (auto simp: integral_nonneg_AE[OF AE_I2] intro!: integral_mono mult_mono)

  have "iexp x - (\<Sum>k \<le> Suc n. (\<i> * x)^k / fact k) =
      ((\<i> ^ (Suc n)) / (fact n)) * (CLBINT s=0..x. (x - s)^n * (iexp s - 1))" (is "?t1 = ?t2")
    unfolding iexp_eq2 [of x n] by (simp add: field_simps)
  then have "cmod (?t1) = cmod (?t2)"
    by simp
  also have "\<dots> =  (1 / (fact n)) * cmod (CLBINT s=0..x. (x - s)^n * (iexp s - 1))"
    by (simp add: norm_mult norm_divide norm_power)
  also have "\<dots> \<le> (1 / (fact n)) * \<bar>LBINT s=0..x. cmod ((x - s)^n * (iexp s - 1))\<bar>"
    by (intro mult_left_mono interval_integral_norm2)
       (auto intro!: interval_integrable_isCont simp: zero_ereal_def)
  also have "\<dots> = (1 / (fact n)) * \<bar>LBINT s=0..x. abs ((x - s)^n) * cmod((iexp s - 1))\<bar>"
    by (simp add: norm_mult del: of_real_diff of_real_power)
  also have "\<dots> \<le> (1 / (fact n)) * \<bar>LBINT s=0..x. abs ((x - s)^n) * 2\<bar>"
    by (intro mult_left_mono * order_trans [OF norm_triangle_ineq4])
       (auto simp: mult_ac zero_ereal_def intro!: interval_integrable_isCont)
  also have "\<dots> = (2 / (fact n)) * \<bar>x ^ (Suc n) / (Suc n)\<bar>"
   by (simp add: abs_LBINT_I0c_abs_power_diff abs_mult)
  also have "2 / fact n * \<bar>x ^ Suc n / real (Suc n)\<bar> = 2 * \<bar>x\<bar> ^ Suc n / (fact (Suc n))"
    by (simp add: abs_mult power_abs)
  finally show ?case .
qed (insert norm_triangle_ineq4[of "iexp x" 1], simp)

lemma (in real_distribution) char_approx1:
  assumes integrable_moments: "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x. x^k)"
  shows "cmod (char M t - (\<Sum>k \<le> n. ((\<i> * t)^k / fact k) * expectation (\<lambda>x. x^k))) \<le>
    (2*\<bar>t\<bar>^n / fact n) * expectation (\<lambda>x. \<bar>x\<bar>^n)" (is "cmod (char M t - ?t1) \<le> _")
proof -
  have integ_iexp: "integrable M (\<lambda>x. iexp (t * x))"
    by (intro integrable_const_bound) auto

  define c where [abs_def]: "c k x = (\<i> * t)^k / fact k * complex_of_real (x^k)" for k x
  have integ_c: "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x. c k x)"
    unfolding c_def by (intro integrable_mult_right integrable_of_real integrable_moments)

  have "k \<le> n \<Longrightarrow> expectation (c k) = (\<i>*t) ^ k * (expectation (\<lambda>x. x ^ k)) / fact k" for k
    unfolding c_def integral_mult_right_zero integral_complex_of_real by simp
  then have "norm (char M t - ?t1) = norm (char M t - (CLINT x | M. (\<Sum>k \<le> n. c k x)))"
    by (simp add: integ_c)
  also have "\<dots> = norm ((CLINT x | M. iexp (t * x) - (\<Sum>k \<le> n. c k x)))"
    unfolding char_def by (subst Bochner_Integration.integral_diff[OF integ_iexp]) (auto intro!: integ_c)
  also have "\<dots> \<le> expectation (\<lambda>x. cmod (iexp (t * x) - (\<Sum>k \<le> n. c k x)))"
    by (intro integral_norm_bound)
  also have "\<dots> \<le> expectation (\<lambda>x. 2 * \<bar>t\<bar> ^ n / fact n * \<bar>x\<bar> ^ n)"
  proof (rule integral_mono)
    show "integrable M (\<lambda>x. cmod (iexp (t * x) - (\<Sum>k\<le>n. c k x)))"
      by (intro integrable_norm Bochner_Integration.integrable_diff integ_iexp Bochner_Integration.integrable_sum integ_c) simp
    show "integrable M (\<lambda>x. 2 * \<bar>t\<bar> ^ n / fact n * \<bar>x\<bar> ^ n)"
      unfolding power_abs[symmetric]
      by (intro integrable_mult_right integrable_abs integrable_moments) simp
    show "cmod (iexp (t * x) - (\<Sum>k\<le>n. c k x)) \<le> 2 * \<bar>t\<bar> ^ n / fact n * \<bar>x\<bar> ^ n" for x
      using iexp_approx2[of "t * x" n] by (auto simp add: abs_mult field_simps c_def)
  qed
  finally show ?thesis
    unfolding integral_mult_right_zero .
qed

lemma (in real_distribution) char_approx2:
  assumes integrable_moments: "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x. x ^ k)"
  shows "cmod (char M t - (\<Sum>k \<le> n. ((\<i> * t)^k / fact k) * expectation (\<lambda>x. x^k))) \<le>
    (\<bar>t\<bar>^n / fact (Suc n)) * expectation (\<lambda>x. min (2 * \<bar>x\<bar>^n * Suc n) (\<bar>t\<bar> * \<bar>x\<bar>^Suc n))"
    (is "cmod (char M t - ?t1) \<le> _")
proof -
  have integ_iexp: "integrable M (\<lambda>x. iexp (t * x))"
    by (intro integrable_const_bound) auto

  define c where [abs_def]: "c k x = (\<i> * t)^k / fact k * complex_of_real (x^k)" for k x
  have integ_c: "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x. c k x)"
    unfolding c_def by (intro integrable_mult_right integrable_of_real integrable_moments)

  have *: "min (2 * \<bar>t * x\<bar>^n / fact n) (\<bar>t * x\<bar>^Suc n / fact (Suc n)) =
      \<bar>t\<bar>^n / fact (Suc n) * min (2 * \<bar>x\<bar>^n * real (Suc n)) (\<bar>t\<bar> * \<bar>x\<bar>^(Suc n))" for x
    apply (subst mult_min_right)
    apply simp
    apply (rule arg_cong2[where f=min])
    apply (simp_all add: field_simps abs_mult del: fact_Suc)
    apply (simp_all add: field_simps)
    done

  have "k \<le> n \<Longrightarrow> expectation (c k) = (\<i>*t) ^ k * (expectation (\<lambda>x. x ^ k)) / fact k" for k
    unfolding c_def integral_mult_right_zero integral_complex_of_real by simp
  then have "norm (char M t - ?t1) = norm (char M t - (CLINT x | M. (\<Sum>k \<le> n. c k x)))"
    by (simp add: integ_c)
  also have "\<dots> = norm ((CLINT x | M. iexp (t * x) - (\<Sum>k \<le> n. c k x)))"
    unfolding char_def by (subst Bochner_Integration.integral_diff[OF integ_iexp]) (auto intro!: integ_c)
  also have "\<dots> \<le> expectation (\<lambda>x. cmod (iexp (t * x) - (\<Sum>k \<le> n. c k x)))"
    by (rule integral_norm_bound)
  also have "\<dots> \<le> expectation (\<lambda>x. min (2 * \<bar>t * x\<bar>^n / fact n) (\<bar>t * x\<bar>^(Suc n) / fact (Suc n)))"
    (is "_ \<le> expectation ?f")
  proof (rule integral_mono)
    show "integrable M (\<lambda>x. cmod (iexp (t * x) - (\<Sum>k\<le>n. c k x)))"
      by (intro integrable_norm Bochner_Integration.integrable_diff integ_iexp Bochner_Integration.integrable_sum integ_c) simp
    show "integrable M ?f"
      by (rule Bochner_Integration.integrable_bound[where f="\<lambda>x. 2 * \<bar>t * x\<bar> ^ n / fact n"])
         (auto simp: integrable_moments power_abs[symmetric] power_mult_distrib)
    show "cmod (iexp (t * x) - (\<Sum>k\<le>n. c k x)) \<le> ?f x" for x
      using iexp_approx1[of "t * x" n] iexp_approx2[of "t * x" n]
      by (auto simp add: abs_mult field_simps c_def intro!: min.boundedI)
  qed
  also have "\<dots> = (\<bar>t\<bar>^n / fact (Suc n)) * expectation (\<lambda>x. min (2 * \<bar>x\<bar>^n * Suc n) (\<bar>t\<bar> * \<bar>x\<bar>^Suc n))"
    unfolding *
  proof (rule Bochner_Integration.integral_mult_right)
    show "integrable M (\<lambda>x. min (2 * \<bar>x\<bar> ^ n * real (Suc n)) (\<bar>t\<bar> * \<bar>x\<bar> ^ Suc n))"
      by (rule Bochner_Integration.integrable_bound[where f="\<lambda>x. 2 * \<bar>x\<bar> ^ n * real (Suc n)"])
         (auto simp: integrable_moments power_abs[symmetric] power_mult_distrib)
  qed
  finally show ?thesis
    unfolding integral_mult_right_zero .
qed

lemma (in real_distribution) char_approx3:
  fixes t
  assumes
    integrable_1: "integrable M (\<lambda>x. x)" and
    integral_1: "expectation (\<lambda>x. x) = 0" and
    integrable_2: "integrable M (\<lambda>x. x^2)" and
    integral_2: "variance (\<lambda>x. x) = \<sigma>2"
  shows "cmod (char M t - (1 - t^2 * \<sigma>2 / 2)) \<le>
    (t^2 / 6) * expectation (\<lambda>x. min (6 * x^2) (abs t * (abs x)^3) )"
proof -
  note real_distribution.char_approx2 [of M 2 t, simplified]
  have [simp]: "prob UNIV = 1" by (metis prob_space space_eq_univ)
  from integral_2 have [simp]: "expectation (\<lambda>x. x * x) = \<sigma>2"
    by (simp add: integral_1 numeral_eq_Suc)
  have 1: "k \<le> 2 \<Longrightarrow> integrable M (\<lambda>x. x^k)" for k
    using assms by (auto simp: eval_nat_numeral le_Suc_eq)
  note char_approx1
  note 2 = char_approx1 [of 2 t, OF 1, simplified]
  have "cmod (char M t - (\<Sum>k\<le>2. (\<i> * t) ^ k * (expectation (\<lambda>x. x ^ k)) / (fact k))) \<le>
      t\<^sup>2 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3)) / fact (3::nat)"
    using char_approx2 [of 2 t, OF 1] by simp
  also have "(\<Sum>k\<le>2. (\<i> * t) ^ k * expectation (\<lambda>x. x ^ k) / (fact k)) = 1 - t^2 * \<sigma>2 / 2"
    by (simp add: complex_eq_iff numeral_eq_Suc integral_1 Re_divide Im_divide)
  also have "fact 3 = 6" by (simp add: eval_nat_numeral)
  also have "t\<^sup>2 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3)) / 6 =
     t\<^sup>2 / 6 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3))" by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>
  This is a more familiar textbook formulation in terms of random variables, but
  we will use the previous version for the CLT.
\<close>

lemma (in prob_space) char_approx3':
  fixes \<mu> :: "real measure" and X
  assumes rv_X [simp]: "random_variable borel X"
    and [simp]: "integrable M X" "integrable M (\<lambda>x. (X x)^2)" "expectation X = 0"
    and var_X: "variance X = \<sigma>2"
    and \<mu>_def: "\<mu> = distr M borel X"
  shows "cmod (char \<mu> t - (1 - t^2 * \<sigma>2 / 2)) \<le>
    (t^2 / 6) * expectation (\<lambda>x. min (6 * (X x)^2) (\<bar>t\<bar> * \<bar>X x\<bar>^3))"
  using var_X unfolding \<mu>_def
  apply (subst integral_distr [symmetric, OF rv_X], simp)
  apply (intro real_distribution.char_approx3)
  apply (auto simp add: integrable_distr_eq integral_distr)
  done

text \<open>
  this is the formulation in the book -- in terms of a random variable *with* the distribution,
  rather the distribution itself. I don't know which is more useful, though in principal we can
  go back and forth between them.
\<close>

lemma (in prob_space) char_approx1':
  fixes \<mu> :: "real measure" and X
  assumes integrable_moments : "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x. X x ^ k)"
    and rv_X[measurable]: "random_variable borel X"
    and \<mu>_distr : "distr M borel X = \<mu>"
  shows "cmod (char \<mu> t - (\<Sum>k \<le> n. ((\<i> * t)^k / fact k) * expectation (\<lambda>x. (X x)^k))) \<le>
    (2 * \<bar>t\<bar>^n / fact n) * expectation (\<lambda>x. \<bar>X x\<bar>^n)"
  unfolding \<mu>_distr[symmetric]
  apply (subst (1 2) integral_distr [symmetric, OF rv_X], simp, simp)
  apply (intro real_distribution.char_approx1[of "distr M borel X" n t] real_distribution_distr rv_X)
  apply (auto simp: integrable_distr_eq integrable_moments)
  done

subsection \<open>Calculation of the Characteristic Function of the Standard Distribution\<close>

abbreviation
  "std_normal_distribution \<equiv> density lborel std_normal_density"

(* TODO: should this be an instance statement? *)
lemma real_dist_normal_dist: "real_distribution std_normal_distribution"
  using prob_space_normal_density by (auto simp: real_distribution_def real_distribution_axioms_def)

lemma std_normal_distribution_even_moments:
  fixes k :: nat
  shows "(LINT x|std_normal_distribution. x^(2 * k)) = fact (2 * k) / (2^k * fact k)"
    and "integrable std_normal_distribution (\<lambda>x. x^(2 * k))"
  using integral_std_normal_moment_even[of k]
  by (subst integral_density)
     (auto simp: normal_density_nonneg integrable_density
           intro: integrable.intros std_normal_moment_even)

lemma integrable_std_normal_distribution_moment: "integrable std_normal_distribution (\<lambda>x. x^k)"
  by (auto simp: normal_density_nonneg integrable_std_normal_moment integrable_density)

lemma integral_std_normal_distribution_moment_odd:
  "odd k \<Longrightarrow> integral\<^sup>L std_normal_distribution (\<lambda>x. x^k) = 0"
  using integral_std_normal_moment_odd[of "(k - 1) div 2"]
  by (auto simp: integral_density normal_density_nonneg elim: oddE)

lemma std_normal_distribution_even_moments_abs:
  fixes k :: nat
  shows "(LINT x|std_normal_distribution. \<bar>x\<bar>^(2 * k)) = fact (2 * k) / (2^k * fact k)"
  using integral_std_normal_moment_even[of k]
  by (subst integral_density) (auto simp: normal_density_nonneg power_even_abs)

lemma std_normal_distribution_odd_moments_abs:
  fixes k :: nat
  shows "(LINT x|std_normal_distribution. \<bar>x\<bar>^(2 * k + 1)) = sqrt (2 / pi) * 2 ^ k * fact k"
  using integral_std_normal_moment_abs_odd[of k]
  by (subst integral_density) (auto simp: normal_density_nonneg)

theorem char_std_normal_distribution:
  "char std_normal_distribution = (\<lambda>t. complex_of_real (exp (- (t^2) / 2)))"
proof (intro ext LIMSEQ_unique)
  fix t :: real
  let ?f' = "\<lambda>k. (\<i> * t)^k / fact k * (LINT x | std_normal_distribution. x^k)"
  let ?f = "\<lambda>n. (\<Sum>k \<le> n. ?f' k)"
  show "?f \<longlonglongrightarrow> exp (-(t^2) / 2)"
  proof (rule limseq_even_odd)
    have "(\<i> * complex_of_real t) ^ (2 * a) / (2 ^ a * fact a) = (- ((complex_of_real t)\<^sup>2 / 2)) ^ a / fact a" for a
      by (subst power_mult) (simp add: field_simps uminus_power_if power_mult)
    then have *: "?f (2 * n) = complex_of_real (\<Sum>k < Suc n. (1 / fact k) * (- (t^2) / 2)^k)" for n :: nat
      unfolding of_real_sum
      by (intro sum.reindex_bij_witness_not_neutral[symmetric, where
           i="\<lambda>n. n div 2" and j="\<lambda>n. 2 * n" and T'="{i. i \<le> 2 * n \<and> odd i}" and S'="{}"])
         (auto simp: integral_std_normal_distribution_moment_odd std_normal_distribution_even_moments)
    show "(\<lambda>n. ?f (2 * n)) \<longlonglongrightarrow> exp (-(t^2) / 2)"
      unfolding * using exp_converges[where 'a=real]
      by (intro tendsto_of_real LIMSEQ_Suc) (auto simp: inverse_eq_divide sums_def [symmetric])
    have **: "?f (2 * n + 1) = ?f (2 * n)" for n
    proof -
      have "?f (2 * n + 1) = ?f (2 * n) + ?f' (2 * n + 1)"
        by simp
      also have "?f' (2 * n + 1) = 0"
        by (subst integral_std_normal_distribution_moment_odd) simp_all
      finally show "?f (2 * n + 1) = ?f (2 * n)"
        by simp
    qed
    show "(\<lambda>n. ?f (2 * n + 1)) \<longlonglongrightarrow> exp (-(t^2) / 2)"
      unfolding ** by fact
  qed

  have **: "(\<lambda>n. x ^ n / fact n) \<longlonglongrightarrow> 0" for x :: real
    using summable_LIMSEQ_zero [OF summable_exp] by (auto simp add: inverse_eq_divide)

  let ?F = "\<lambda>n. 2 * \<bar>t\<bar> ^ n / fact n * (LINT x|std_normal_distribution. \<bar>x\<bar> ^ n)"

  show "?f \<longlonglongrightarrow> char std_normal_distribution t"
  proof (rule metric_tendsto_imp_tendsto[OF limseq_even_odd])
    show "(\<lambda>n. ?F (2 * n)) \<longlonglongrightarrow> 0"
    proof (rule Lim_transform_eventually)
      show "\<forall>\<^sub>F n in sequentially. 2 * ((t^2 / 2)^n / fact n) = ?F (2 * n)"
        unfolding std_normal_distribution_even_moments_abs by (simp add: power_mult power_divide)
    qed (intro tendsto_mult_right_zero **)

    have *: "?F (2 * n + 1) = (2 * \<bar>t\<bar> * sqrt (2 / pi)) * ((2 * t^2)^n * fact n / fact (2 * n + 1))" for n
      unfolding std_normal_distribution_odd_moments_abs
      by (simp add: field_simps power_mult[symmetric] power_even_abs)
    have "norm ((2 * t\<^sup>2) ^ n * fact n / fact (2 * n + 1)) \<le> (2 * t\<^sup>2) ^ n / fact n" for n
      using mult_mono[OF _ square_fact_le_2_fact, of 1 "1 + 2 * real n" n]
      by (auto simp add: divide_simps intro!: mult_left_mono)
    then show "(\<lambda>n. ?F (2 * n + 1)) \<longlonglongrightarrow> 0"
      unfolding * by (intro tendsto_mult_right_zero Lim_null_comparison [OF _ ** [of "2 * t\<^sup>2"]]) auto

    show "\<forall>\<^sub>F n in sequentially. dist (?f n) (char std_normal_distribution t) \<le> dist (?F n) 0"
      using real_distribution.char_approx1[OF real_dist_normal_dist integrable_std_normal_distribution_moment]
      by (auto simp: dist_norm integral_nonneg_AE norm_minus_commute)
  qed
qed

end
