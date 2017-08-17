(*  Title:    HOL/Analysis/Harmonic_Numbers.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Harmonic Numbers\<close>

theory Harmonic_Numbers
imports
  Complex_Transcendental
  Summation_Tests
  Integral_Test
begin

text \<open>
  The definition of the Harmonic Numbers and the Euler-Mascheroni constant.
  Also provides a reasonably accurate approximation of @{term "ln 2 :: real"}
  and the Euler-Mascheroni constant.
\<close>

subsection \<open>The Harmonic numbers\<close>

definition harm :: "nat \<Rightarrow> 'a :: real_normed_field" where
  "harm n = (\<Sum>k=1..n. inverse (of_nat k))"

lemma harm_altdef: "harm n = (\<Sum>k<n. inverse (of_nat (Suc k)))"
  unfolding harm_def by (induction n) simp_all

lemma harm_Suc: "harm (Suc n) = harm n + inverse (of_nat (Suc n))"
  by (simp add: harm_def)

lemma harm_nonneg: "harm n \<ge> (0 :: 'a :: {real_normed_field,linordered_field})"
  unfolding harm_def by (intro sum_nonneg) simp_all

lemma harm_pos: "n > 0 \<Longrightarrow> harm n > (0 :: 'a :: {real_normed_field,linordered_field})"
  unfolding harm_def by (intro sum_pos) simp_all

lemma of_real_harm: "of_real (harm n) = harm n"
  unfolding harm_def by simp

lemma abs_harm [simp]: "(abs (harm n) :: real) = harm n"
  using harm_nonneg[of n] by (rule abs_of_nonneg)    

lemma norm_harm: "norm (harm n) = harm n"
  by (subst of_real_harm [symmetric]) (simp add: harm_nonneg)

lemma harm_expand:
  "harm 0 = 0"
  "harm (Suc 0) = 1"
  "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)"
proof -
  have "numeral n = Suc (pred_numeral n)" by simp
  also have "harm \<dots> = harm (pred_numeral n) + inverse (numeral n)"
    by (subst harm_Suc, subst numeral_eq_Suc[symmetric]) simp
  finally show "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)" .
qed (simp_all add: harm_def)

lemma not_convergent_harm: "\<not>convergent (harm :: nat \<Rightarrow> 'a :: real_normed_field)"
proof -
  have "convergent (\<lambda>n. norm (harm n :: 'a)) \<longleftrightarrow>
            convergent (harm :: nat \<Rightarrow> real)" by (simp add: norm_harm)
  also have "\<dots> \<longleftrightarrow> convergent (\<lambda>n. \<Sum>k=Suc 0..Suc n. inverse (of_nat k) :: real)"
    unfolding harm_def[abs_def] by (subst convergent_Suc_iff) simp_all
  also have "... \<longleftrightarrow> convergent (\<lambda>n. \<Sum>k\<le>n. inverse (of_nat (Suc k)) :: real)"
    by (subst sum_shift_bounds_cl_Suc_ivl) (simp add: atLeast0AtMost)
  also have "... \<longleftrightarrow> summable (\<lambda>n. inverse (of_nat n) :: real)"
    by (subst summable_Suc_iff [symmetric]) (simp add: summable_iff_convergent')
  also have "\<not>..." by (rule not_summable_harmonic)
  finally show ?thesis by (blast dest: convergent_norm)
qed

lemma harm_pos_iff [simp]: "harm n > (0 :: 'a :: {real_normed_field,linordered_field}) \<longleftrightarrow> n > 0"
  by (rule iffI, cases n, simp add: harm_expand, simp, rule harm_pos)

lemma ln_diff_le_inverse:
  assumes "x \<ge> (1::real)"
  shows   "ln (x + 1) - ln x < 1 / x"
proof -
  from assms have "\<exists>z>x. z < x + 1 \<and> ln (x + 1) - ln x = (x + 1 - x) * inverse z"
    by (intro MVT2) (auto intro!: derivative_eq_intros simp: field_simps)
  then obtain z where z: "z > x" "z < x + 1" "ln (x + 1) - ln x = inverse z" by auto
  have "ln (x + 1) - ln x = inverse z" by fact
  also from z(1,2) assms have "\<dots> < 1 / x" by (simp add: field_simps)
  finally show ?thesis .
qed

lemma ln_le_harm: "ln (real n + 1) \<le> (harm n :: real)"
proof (induction n)
  fix n assume IH: "ln (real n + 1) \<le> harm n"
  have "ln (real (Suc n) + 1) = ln (real n + 1) + (ln (real n + 2) - ln (real n + 1))" by simp
  also have "(ln (real n + 2) - ln (real n + 1)) \<le> 1 / real (Suc n)"
    using ln_diff_le_inverse[of "real n + 1"] by (simp add: add_ac)
  also note IH
  also have "harm n + 1 / real (Suc n) = harm (Suc n)" by (simp add: harm_Suc field_simps)
  finally show "ln (real (Suc n) + 1) \<le> harm (Suc n)" by - simp
qed (simp_all add: harm_def)

lemma harm_at_top: "filterlim (harm :: nat \<Rightarrow> real) at_top sequentially"
proof (rule filterlim_at_top_mono)
  show "eventually (\<lambda>n. harm n \<ge> ln (real (Suc n))) at_top"
    using ln_le_harm by (intro always_eventually allI) (simp_all add: add_ac)
  show "filterlim (\<lambda>n. ln (real (Suc n))) at_top sequentially"
    by (intro filterlim_compose[OF ln_at_top] filterlim_compose[OF filterlim_real_sequentially] 
              filterlim_Suc)
qed


subsection \<open>The Euler--Mascheroni constant\<close>

text \<open>
  The limit of the difference between the partial harmonic sum and the natural logarithm
  (approximately 0.577216). This value occurs e.g. in the definition of the Gamma function.
 \<close>
definition euler_mascheroni :: "'a :: real_normed_algebra_1" where
  "euler_mascheroni = of_real (lim (\<lambda>n. harm n - ln (of_nat n)))"

lemma of_real_euler_mascheroni [simp]: "of_real euler_mascheroni = euler_mascheroni"
  by (simp add: euler_mascheroni_def)

interpretation euler_mascheroni: antimono_fun_sum_integral_diff "\<lambda>x. inverse (x + 1)"
  by unfold_locales (auto intro!: continuous_intros)

lemma euler_mascheroni_sum_integral_diff_series:
  "euler_mascheroni.sum_integral_diff_series n = harm (Suc n) - ln (of_nat (Suc n))"
proof -
  have "harm (Suc n) = (\<Sum>k=0..n. inverse (of_nat k + 1) :: real)" unfolding harm_def
    unfolding One_nat_def by (subst sum_shift_bounds_cl_Suc_ivl) (simp add: add_ac)
  moreover have "((\<lambda>x. inverse (x + 1) :: real) has_integral ln (of_nat n + 1) - ln (0 + 1))
                   {0..of_nat n}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros simp: divide_inverse
           has_field_derivative_iff_has_vector_derivative[symmetric])
  hence "integral {0..of_nat n} (\<lambda>x. inverse (x + 1) :: real) = ln (of_nat (Suc n))"
    by (auto dest!: integral_unique)
  ultimately show ?thesis
    by (simp add: euler_mascheroni.sum_integral_diff_series_def atLeast0AtMost)
qed

lemma euler_mascheroni_sequence_decreasing:
  "m > 0 \<Longrightarrow> m \<le> n \<Longrightarrow> harm n - ln (of_nat n) \<le> harm m - ln (of_nat m :: real)"
  by (cases m, simp, cases n, simp, hypsubst,
      subst (1 2) euler_mascheroni_sum_integral_diff_series [symmetric],
      rule euler_mascheroni.sum_integral_diff_series_antimono, simp)

lemma euler_mascheroni_sequence_nonneg:
  "n > 0 \<Longrightarrow> harm n - ln (of_nat n) \<ge> (0::real)"
  by (cases n, simp, hypsubst, subst euler_mascheroni_sum_integral_diff_series [symmetric],
      rule euler_mascheroni.sum_integral_diff_series_nonneg)

lemma euler_mascheroni_convergent: "convergent (\<lambda>n. harm n - ln (of_nat n) :: real)"
proof -
  have A: "(\<lambda>n. harm (Suc n) - ln (of_nat (Suc n))) =
             euler_mascheroni.sum_integral_diff_series"
    by (subst euler_mascheroni_sum_integral_diff_series [symmetric]) (rule refl)
  have "convergent (\<lambda>n. harm (Suc n) - ln (of_nat (Suc n) :: real))"
    by (subst A) (fact euler_mascheroni.sum_integral_diff_series_convergent)
  thus ?thesis by (subst (asm) convergent_Suc_iff)
qed

lemma euler_mascheroni_LIMSEQ:
  "(\<lambda>n. harm n - ln (of_nat n) :: real) \<longlonglongrightarrow> euler_mascheroni"
  unfolding euler_mascheroni_def
  by (simp add: convergent_LIMSEQ_iff [symmetric] euler_mascheroni_convergent)

lemma euler_mascheroni_LIMSEQ_of_real:
  "(\<lambda>n. of_real (harm n - ln (of_nat n))) \<longlonglongrightarrow>
      (euler_mascheroni :: 'a :: {real_normed_algebra_1, topological_space})"
proof -
  have "(\<lambda>n. of_real (harm n - ln (of_nat n))) \<longlonglongrightarrow> (of_real (euler_mascheroni) :: 'a)"
    by (intro tendsto_of_real euler_mascheroni_LIMSEQ)
  thus ?thesis by simp
qed

lemma euler_mascheroni_sum_real:
  "(\<lambda>n. inverse (of_nat (n+1)) + ln (of_nat (n+1)) - ln (of_nat (n+2)) :: real)
       sums euler_mascheroni"
 using sums_add[OF telescope_sums[OF LIMSEQ_Suc[OF euler_mascheroni_LIMSEQ]]
                   telescope_sums'[OF LIMSEQ_inverse_real_of_nat]]
  by (simp_all add: harm_def algebra_simps)

lemma euler_mascheroni_sum:
  "(\<lambda>n. inverse (of_nat (n+1)) + of_real (ln (of_nat (n+1))) - of_real (ln (of_nat (n+2))))
       sums (euler_mascheroni :: 'a :: {banach, real_normed_field})"
proof -
  have "(\<lambda>n. of_real (inverse (of_nat (n+1)) + ln (of_nat (n+1)) - ln (of_nat (n+2))))
       sums (of_real euler_mascheroni :: 'a :: {banach, real_normed_field})"
    by (subst sums_of_real_iff) (rule euler_mascheroni_sum_real)
  thus ?thesis by simp
qed

lemma alternating_harmonic_series_sums: "(\<lambda>k. (-1)^k / real_of_nat (Suc k)) sums ln 2"
proof -
  let ?f = "\<lambda>n. harm n - ln (real_of_nat n)"
  let ?g = "\<lambda>n. if even n then 0 else (2::real)"
  let ?em = "\<lambda>n. harm n - ln (real_of_nat n)"
  have "eventually (\<lambda>n. ?em (2*n) - ?em n + ln 2 = (\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k))) at_top"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    have "(\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k)) =
              (\<Sum>k<2*n. ((-1)^k + ?g k) / of_nat (Suc k)) - (\<Sum>k<2*n. ?g k / of_nat (Suc k))"
      by (simp add: sum.distrib algebra_simps divide_inverse)
    also have "(\<Sum>k<2*n. ((-1)^k + ?g k) / real_of_nat (Suc k)) = harm (2*n)"
      unfolding harm_altdef by (intro sum.cong) (auto simp: field_simps)
    also have "(\<Sum>k<2*n. ?g k / real_of_nat (Suc k)) = (\<Sum>k|k<2*n \<and> odd k. ?g k / of_nat (Suc k))"
      by (intro sum.mono_neutral_right) auto
    also have "\<dots> = (\<Sum>k|k<2*n \<and> odd k. 2 / (real_of_nat (Suc k)))"
      by (intro sum.cong) auto
    also have "(\<Sum>k|k<2*n \<and> odd k. 2 / (real_of_nat (Suc k))) = harm n"
      unfolding harm_altdef
      by (intro sum.reindex_cong[of "\<lambda>n. 2*n+1"]) (auto simp: inj_on_def field_simps elim!: oddE)
    also have "harm (2*n) - harm n = ?em (2*n) - ?em n + ln 2" using n
      by (simp_all add: algebra_simps ln_mult)
    finally show "?em (2*n) - ?em n + ln 2 = (\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k))" ..
  qed
  moreover have "(\<lambda>n. ?em (2*n) - ?em n + ln (2::real))
                     \<longlonglongrightarrow> euler_mascheroni - euler_mascheroni + ln 2"
    by (intro tendsto_intros euler_mascheroni_LIMSEQ filterlim_compose[OF euler_mascheroni_LIMSEQ]
              filterlim_subseq) (auto simp: strict_mono_def)
  hence "(\<lambda>n. ?em (2*n) - ?em n + ln (2::real)) \<longlonglongrightarrow> ln 2" by simp
  ultimately have "(\<lambda>n. (\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k))) \<longlonglongrightarrow> ln 2"
    by (rule Lim_transform_eventually)

  moreover have "summable (\<lambda>k. (-1)^k * inverse (real_of_nat (Suc k)))"
    using LIMSEQ_inverse_real_of_nat
    by (intro summable_Leibniz(1) decseq_imp_monoseq decseq_SucI) simp_all
  hence A: "(\<lambda>n. \<Sum>k<n. (-1)^k / real_of_nat (Suc k)) \<longlonglongrightarrow> (\<Sum>k. (-1)^k / real_of_nat (Suc k))"
    by (simp add: summable_sums_iff divide_inverse sums_def)
  from filterlim_compose[OF this filterlim_subseq[of "op * (2::nat)"]]
    have "(\<lambda>n. \<Sum>k<2*n. (-1)^k / real_of_nat (Suc k)) \<longlonglongrightarrow> (\<Sum>k. (-1)^k / real_of_nat (Suc k))"
    by (simp add: strict_mono_def)
  ultimately have "(\<Sum>k. (- 1) ^ k / real_of_nat (Suc k)) = ln 2" by (intro LIMSEQ_unique)
  with A show ?thesis by (simp add: sums_def)
qed

lemma alternating_harmonic_series_sums':
  "(\<lambda>k. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2))) sums ln 2"
unfolding sums_def
proof (rule Lim_transform_eventually)
  show "(\<lambda>n. \<Sum>k<2*n. (-1)^k / (real_of_nat (Suc k))) \<longlonglongrightarrow> ln 2"
    using alternating_harmonic_series_sums unfolding sums_def
    by (rule filterlim_compose) (rule mult_nat_left_at_top, simp)
  show "eventually (\<lambda>n. (\<Sum>k<2*n. (-1)^k / (real_of_nat (Suc k))) =
            (\<Sum>k<n. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2)))) sequentially"
  proof (intro always_eventually allI)
    fix n :: nat
    show "(\<Sum>k<2*n. (-1)^k / (real_of_nat (Suc k))) =
              (\<Sum>k<n. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2)))"
      by (induction n) (simp_all add: inverse_eq_divide)
  qed
qed


subsection \<open>Bounds on the Euler--Mascheroni constant\<close>

(* TODO: Move? *)
lemma ln_inverse_approx_le:
  assumes "(x::real) > 0" "a > 0"
  shows   "ln (x + a) - ln x \<le> a * (inverse x + inverse (x + a))/2" (is "_ \<le> ?A")
proof -
  define f' where "f' = (inverse (x + a) - inverse x)/a"
  have f'_nonpos: "f' \<le> 0" using assms by (simp add: f'_def divide_simps)
  let ?f = "\<lambda>t. (t - x) * f' + inverse x"
  let ?F = "\<lambda>t. (t - x)^2 * f' / 2 + t * inverse x"
  have diff: "\<forall>t\<in>{x..x+a}. (?F has_vector_derivative ?f t)
                               (at t within {x..x+a})" using assms
    by (auto intro!: derivative_eq_intros
             simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  from assms have "(?f has_integral (?F (x+a) - ?F x)) {x..x+a}"
    by (intro fundamental_theorem_of_calculus[OF _ diff])
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] field_simps
             intro!: derivative_eq_intros)
  also have "?F (x+a) - ?F x = (a*2 + f'*a\<^sup>2*x) / (2*x)" using assms by (simp add: field_simps)
  also have "f'*a^2 = - (a^2) / (x*(x + a))" using assms
    by (simp add: divide_simps f'_def power2_eq_square)
  also have "(a*2 + - a\<^sup>2/(x*(x+a))*x) / (2*x) = ?A" using assms
    by (simp add: divide_simps power2_eq_square) (simp add: algebra_simps)
  finally have int1: "((\<lambda>t. (t - x) * f' + inverse x) has_integral ?A) {x..x + a}" .

  from assms have int2: "(inverse has_integral (ln (x + a) - ln x)) {x..x+a}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] divide_simps
             intro!: derivative_eq_intros)
  hence "ln (x + a) - ln x = integral {x..x+a} inverse" by (simp add: integral_unique)
  also have ineq: "\<forall>xa\<in>{x..x + a}. inverse xa \<le> (xa - x) * f' + inverse x"
  proof
    fix t assume t': "t \<in> {x..x+a}"
    with assms have t: "0 \<le> (t - x) / a" "(t - x) / a \<le> 1" by simp_all
    have "inverse t = inverse ((1 - (t - x) / a) *\<^sub>R x + ((t - x) / a) *\<^sub>R (x + a))" (is "_ = ?A")
      using assms t' by (simp add: field_simps)
    also from assms have "convex_on {x..x+a} inverse" by (intro convex_on_inverse) auto
    from convex_onD_Icc[OF this _ t] assms
      have "?A \<le> (1 - (t - x) / a) * inverse x + (t - x) / a * inverse (x + a)" by simp
    also have "\<dots> = (t - x) * f' + inverse x" using assms
      by (simp add: f'_def divide_simps) (simp add: f'_def field_simps)
    finally show "inverse t \<le> (t - x) * f' + inverse x" .
  qed
  hence "integral {x..x+a} inverse \<le> integral {x..x+a} ?f" using f'_nonpos assms
    by (intro integral_le has_integral_integrable[OF int1] has_integral_integrable[OF int2] ineq)
  also have "\<dots> = ?A" using int1 by (rule integral_unique)
  finally show ?thesis .
qed

lemma ln_inverse_approx_ge:
  assumes "(x::real) > 0" "x < y"
  shows   "ln y - ln x \<ge> 2 * (y - x) / (x + y)" (is "_ \<ge> ?A")
proof -
  define m where "m = (x+y)/2"
  define f' where "f' = -inverse (m^2)"
  from assms have m: "m > 0" by (simp add: m_def)
  let ?F = "\<lambda>t. (t - m)^2 * f' / 2 + t / m"
  from assms have "((\<lambda>t. (t - m) * f' + inverse m) has_integral (?F y - ?F x)) {x..y}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] divide_simps
             intro!: derivative_eq_intros)
  also from m have "?F y - ?F x = ((y - m)^2 - (x - m)^2) * f' / 2 + (y - x) / m"
    by (simp add: field_simps)
  also have "((y - m)^2 - (x - m)^2) = 0" by (simp add: m_def power2_eq_square field_simps)
  also have "0 * f' / 2 + (y - x) / m = ?A" by (simp add: m_def)
  finally have int1: "((\<lambda>t. (t - m) * f' + inverse m) has_integral ?A) {x..y}" .

  from assms have int2: "(inverse has_integral (ln y - ln x)) {x..y}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] divide_simps
             intro!: derivative_eq_intros)
  hence "ln y - ln x = integral {x..y} inverse" by (simp add: integral_unique)
  also have ineq: "\<forall>xa\<in>{x..y}. inverse xa \<ge> (xa - m) * f' + inverse m"
  proof
    fix t assume t: "t \<in> {x..y}"
    from t assms have "inverse t - inverse m \<ge> f' * (t - m)"
      by (intro convex_on_imp_above_tangent[of "{0<..}"] convex_on_inverse)
         (auto simp: m_def interior_open f'_def power2_eq_square intro!: derivative_eq_intros)
    thus "(t - m) * f' + inverse m \<le> inverse t" by (simp add: algebra_simps)
  qed
  hence "integral {x..y} inverse \<ge> integral {x..y} (\<lambda>t. (t - m) * f' + inverse m)"
    using int1 int2 by (intro integral_le has_integral_integrable)
  also have "integral {x..y} (\<lambda>t. (t - m) * f' + inverse m) = ?A"
    using integral_unique[OF int1] by simp
  finally show ?thesis .
qed


lemma euler_mascheroni_lower:
        "euler_mascheroni \<ge> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 2))"
  and euler_mascheroni_upper:
        "euler_mascheroni \<le> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 1))"
proof -
  define D :: "_ \<Rightarrow> real"
    where "D n = inverse (of_nat (n+1)) + ln (of_nat (n+1)) - ln (of_nat (n+2))" for n
  let ?g = "\<lambda>n. ln (of_nat (n+2)) - ln (of_nat (n+1)) - inverse (of_nat (n+1)) :: real"
  define inv where [abs_def]: "inv n = inverse (real_of_nat n)" for n
  fix n :: nat
  note summable = sums_summable[OF euler_mascheroni_sum_real, folded D_def]
  have sums: "(\<lambda>k. (inv (Suc (k + (n+1))) - inv (Suc (Suc k + (n+1))))/2) sums ((inv (Suc (0 + (n+1))) - 0)/2)"
    unfolding inv_def
    by (intro sums_divide telescope_sums' LIMSEQ_ignore_initial_segment LIMSEQ_inverse_real_of_nat)
  have sums': "(\<lambda>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2) sums ((inv (Suc (0 + n)) - 0)/2)"
    unfolding inv_def
    by (intro sums_divide telescope_sums' LIMSEQ_ignore_initial_segment LIMSEQ_inverse_real_of_nat)
  from euler_mascheroni_sum_real have "euler_mascheroni = (\<Sum>k. D k)"
    by (simp add: sums_iff D_def)
  also have "\<dots> = (\<Sum>k. D (k + Suc n)) + (\<Sum>k\<le>n. D k)"
    by (subst suminf_split_initial_segment[OF summable, of "Suc n"], 
        subst lessThan_Suc_atMost) simp
  finally have sum: "(\<Sum>k\<le>n. D k) - euler_mascheroni = -(\<Sum>k. D (k + Suc n))" by simp

  note sum
  also have "\<dots> \<le> -(\<Sum>k. (inv (k + Suc n + 1) - inv (k + Suc n + 2)) / 2)"
  proof (intro le_imp_neg_le suminf_le allI summable_ignore_initial_segment[OF summable])
    fix k' :: nat
    define k where "k = k' + Suc n"
    hence k: "k > 0" by (simp add: k_def)
    have "real_of_nat (k+1) > 0" by (simp add: k_def)
    with ln_inverse_approx_le[OF this zero_less_one]
      have "ln (of_nat k + 2) - ln (of_nat k + 1) \<le> (inv (k+1) + inv (k+2))/2"
      by (simp add: inv_def add_ac)
    hence "(inv (k+1) - inv (k+2))/2 \<le> inv (k+1) + ln (of_nat (k+1)) - ln (of_nat (k+2))"
      by (simp add: field_simps)
    also have "\<dots> = D k" unfolding D_def inv_def ..
    finally show "D (k' + Suc n) \<ge> (inv (k' + Suc n + 1) - inv (k' + Suc n + 2)) / 2"
      by (simp add: k_def)
    from sums_summable[OF sums]
      show "summable (\<lambda>k. (inv (k + Suc n + 1) - inv (k + Suc n + 2))/2)" by simp
  qed
  also from sums have "\<dots> = -inv (n+2) / 2" by (simp add: sums_iff)
  finally have "euler_mascheroni \<ge> (\<Sum>k\<le>n. D k) + 1 / (of_nat (2 * (n+2)))"
    by (simp add: inv_def field_simps)
  also have "(\<Sum>k\<le>n. D k) = harm (Suc n) - (\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1)))"
    unfolding harm_altdef D_def by (subst lessThan_Suc_atMost) (simp add:  sum.distrib sum_subtractf)
  also have "(\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1))) = ln (of_nat (n+2))"
    by (subst atLeast0AtMost [symmetric], subst sum_Suc_diff) simp_all
  finally show "euler_mascheroni \<ge> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 2))"
    by simp

  note sum
  also have "-(\<Sum>k. D (k + Suc n)) \<ge> -(\<Sum>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2)"
  proof (intro le_imp_neg_le suminf_le allI summable_ignore_initial_segment[OF summable])
    fix k' :: nat
    define k where "k = k' + Suc n"
    hence k: "k > 0" by (simp add: k_def)
    have "real_of_nat (k+1) > 0" by (simp add: k_def)
    from ln_inverse_approx_ge[of "of_nat k + 1" "of_nat k + 2"]
      have "2 / (2 * real_of_nat k + 3) \<le> ln (of_nat (k+2)) - ln (real_of_nat (k+1))"
      by (simp add: add_ac)
    hence "D k \<le> 1 / real_of_nat (k+1) - 2 / (2 * real_of_nat k + 3)"
      by (simp add: D_def inverse_eq_divide inv_def)
    also have "\<dots> = inv ((k+1)*(2*k+3))" unfolding inv_def by (simp add: field_simps)
    also have "\<dots> \<le> inv (2*k*(k+1))" unfolding inv_def using k
      by (intro le_imp_inverse_le)
         (simp add: algebra_simps, simp del: of_nat_add)
    also have "\<dots> = (inv k - inv (k+1))/2" unfolding inv_def using k
      by (simp add: divide_simps del: of_nat_mult) (simp add: algebra_simps)
    finally show "D k \<le> (inv (Suc (k' + n)) - inv (Suc (Suc k' + n)))/2" unfolding k_def by simp
  next
    from sums_summable[OF sums']
      show "summable (\<lambda>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2)" by simp
  qed
  also from sums' have "(\<Sum>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2) = inv (n+1)/2"
    by (simp add: sums_iff)
  finally have "euler_mascheroni \<le> (\<Sum>k\<le>n. D k) + 1 / of_nat (2 * (n+1))"
    by (simp add: inv_def field_simps)
  also have "(\<Sum>k\<le>n. D k) = harm (Suc n) - (\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1)))"
    unfolding harm_altdef D_def by (subst lessThan_Suc_atMost) (simp add:  sum.distrib sum_subtractf)
  also have "(\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1))) = ln (of_nat (n+2))"
    by (subst atLeast0AtMost [symmetric], subst sum_Suc_diff) simp_all
  finally show "euler_mascheroni \<le> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 1))"
    by simp
qed

lemma euler_mascheroni_pos: "euler_mascheroni > (0::real)"
  using euler_mascheroni_lower[of 0] ln_2_less_1 by (simp add: harm_def)

context
begin

private lemma ln_approx_aux:
  fixes n :: nat and x :: real
  defines "y \<equiv> (x-1)/(x+1)"
  assumes x: "x > 0" "x \<noteq> 1"
  shows "inverse (2*y^(2*n+1)) * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) \<in>
            {0..(1 / (1 - y^2) / of_nat (2*n+1))}"
proof -
  from x have norm_y: "norm y < 1" unfolding y_def by simp
  from power_strict_mono[OF this, of 2] have norm_y': "norm y^2 < 1" by simp

  let ?f = "\<lambda>k. 2 * y ^ (2*k+1) / of_nat (2*k+1)"
  note sums = ln_series_quadratic[OF x(1)]
  define c where "c = inverse (2*y^(2*n+1))"
  let ?d = "c * (ln x - (\<Sum>k<n. ?f k))"
  have "\<forall>k. y\<^sup>2^k / of_nat (2*(k+n)+1) \<le> y\<^sup>2 ^ k / of_nat (2*n+1)"
    by (intro allI divide_left_mono mult_right_mono mult_pos_pos zero_le_power[of "y^2"]) simp_all
  moreover {
    have "(\<lambda>k. ?f (k + n)) sums (ln x - (\<Sum>k<n. ?f k))"
      using sums_split_initial_segment[OF sums] by (simp add: y_def)
    hence "(\<lambda>k. c * ?f (k + n)) sums ?d" by (rule sums_mult)
    also have "(\<lambda>k. c * (2*y^(2*(k+n)+1) / of_nat (2*(k+n)+1))) =
                   (\<lambda>k. (c * (2*y^(2*n+1))) * ((y^2)^k / of_nat (2*(k+n)+1)))"
      by (simp only: ring_distribs power_add power_mult) (simp add: mult_ac)
    also from x have "c * (2*y^(2*n+1)) = 1" by (simp add: c_def y_def)
    finally have "(\<lambda>k. (y^2)^k / of_nat (2*(k+n)+1)) sums ?d" by simp
  } note sums' = this
  moreover from norm_y' have "(\<lambda>k. (y^2)^k / of_nat (2*n+1)) sums (1 / (1 - y^2) / of_nat (2*n+1))"
    by (intro sums_divide geometric_sums) (simp_all add: norm_power)
  ultimately have "?d \<le> (1 / (1 - y^2) / of_nat (2*n+1))" by (rule sums_le)
  moreover have "c * (ln x - (\<Sum>k<n. 2 * y ^ (2 * k + 1) / real_of_nat (2 * k + 1))) \<ge> 0"
    by (intro sums_le[OF _ sums_zero sums']) simp_all
  ultimately show ?thesis unfolding c_def by simp
qed

lemma
  fixes n :: nat and x :: real
  defines "y \<equiv> (x-1)/(x+1)"
  defines "approx \<equiv> (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))"
  defines "d \<equiv> y^(2*n+1) / (1 - y^2) / of_nat (2*n+1)"
  assumes x: "x > 1"
  shows   ln_approx_bounds: "ln x \<in> {approx..approx + 2*d}"
  and     ln_approx_abs:    "abs (ln x - (approx + d)) \<le> d"
proof -
  define c where "c = 2*y^(2*n+1)"
  from x have c_pos: "c > 0" unfolding c_def y_def
    by (intro mult_pos_pos zero_less_power) simp_all
  have A: "inverse c * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) \<in>
              {0.. (1 / (1 - y^2) / of_nat (2*n+1))}" using assms unfolding y_def c_def
    by (intro ln_approx_aux) simp_all
  hence "inverse c * (ln x - (\<Sum>k<n. 2*y^(2*k+1)/of_nat (2*k+1))) \<le> (1 / (1-y^2) / of_nat (2*n+1))"
    by simp
  hence "(ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) / c \<le> (1 / (1 - y^2) / of_nat (2*n+1))"
    by (auto simp add: divide_simps)
  with c_pos have "ln x \<le> c / (1 - y^2) / of_nat (2*n+1) + approx"
    by (subst (asm) pos_divide_le_eq) (simp_all add: mult_ac approx_def)
  moreover {
    from A c_pos have "0 \<le> c * (inverse c * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))))"
      by (intro mult_nonneg_nonneg[of c]) simp_all
    also have "\<dots> = (c * inverse c) * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1)))"
      by (simp add: mult_ac)
    also from c_pos have "c * inverse c = 1" by simp
    finally have "ln x \<ge> approx" by (simp add: approx_def)
  }
  ultimately show "ln x \<in> {approx..approx + 2*d}" by (simp add: c_def d_def)
  thus "abs (ln x - (approx + d)) \<le> d" by auto
qed

end

lemma euler_mascheroni_bounds:
  fixes n :: nat assumes "n \<ge> 1" defines "t \<equiv> harm n - ln (of_nat (Suc n)) :: real"
  shows "euler_mascheroni \<in> {t + inverse (of_nat (2*(n+1)))..t + inverse (of_nat (2*n))}"
  using assms euler_mascheroni_upper[of "n-1"] euler_mascheroni_lower[of "n-1"]
  unfolding t_def by (cases n) (simp_all add: harm_Suc t_def inverse_eq_divide)

lemma euler_mascheroni_bounds':
  fixes n :: nat assumes "n \<ge> 1" "ln (real_of_nat (Suc n)) \<in> {l<..<u}"
  shows "euler_mascheroni \<in>
           {harm n - u + inverse (of_nat (2*(n+1)))<..<harm n - l + inverse (of_nat (2*n))}"
  using euler_mascheroni_bounds[OF assms(1)] assms(2) by auto


text \<open>
  Approximation of @{term "ln 2"}. The lower bound is accurate to about 0.03; the upper
  bound is accurate to about 0.0015.
\<close>
lemma ln2_ge_two_thirds: "2/3 \<le> ln (2::real)"
  and ln2_le_25_over_36: "ln (2::real) \<le> 25/36"
  using ln_approx_bounds[of 2 1, simplified, simplified eval_nat_numeral, simplified] by simp_all


text \<open>
  Approximation of the Euler--Mascheroni constant. The lower bound is accurate to about 0.0015;
  the upper bound is accurate to about 0.015.
\<close>
lemma euler_mascheroni_gt_19_over_33: "(euler_mascheroni :: real) > 19/33" (is ?th1)
  and euler_mascheroni_less_13_over_22: "(euler_mascheroni :: real) < 13/22" (is ?th2)
proof -
  have "ln (real (Suc 7)) = 3 * ln 2" by (simp add: ln_powr [symmetric])
  also from ln_approx_bounds[of 2 3] have "\<dots> \<in> {3*307/443<..<3*4615/6658}"
    by (simp add: eval_nat_numeral)
  finally have "ln (real (Suc 7)) \<in> \<dots>" .
  from euler_mascheroni_bounds'[OF _ this] have "?th1 \<and> ?th2" by (simp_all add: harm_expand)
  thus ?th1 ?th2 by blast+
qed

end
