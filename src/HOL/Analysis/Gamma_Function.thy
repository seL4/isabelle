(*  Title:    HOL/Analysis/Gamma_Function.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>The Gamma Function\<close>

theory Gamma_Function
  imports
  Equivalence_Lebesgue_Henstock_Integration
  Summation_Tests
  Harmonic_Numbers
  "HOL-Library.Nonpos_Ints"
  "HOL-Library.Periodic_Fun"
begin

text \<open>
  Several equivalent definitions of the Gamma function and its
  most important properties. Also contains the definition and some properties
  of the log-Gamma function and the Digamma function and the other Polygamma functions.

  Based on the Gamma function, we also prove the Weierstra{\ss} product form of the
  sin function and, based on this, the solution of the Basel problem (the
  sum over all \<^term>\<open>1 / (n::nat)^2\<close>.
\<close>

lemma pochhammer_eq_0_imp_nonpos_Int:
  "pochhammer (x::'a::field_char_0) n = 0 \<Longrightarrow> x \<in> \<int>\<^sub>\<le>\<^sub>0"
  by (auto simp: pochhammer_eq_0_iff)

lemma closed_nonpos_Ints [simp]: "closed (\<int>\<^sub>\<le>\<^sub>0 :: 'a :: real_normed_algebra_1 set)"
proof -
  have "\<int>\<^sub>\<le>\<^sub>0 = (of_int ` {n. n \<le> 0} :: 'a set)"
    by (auto elim!: nonpos_Ints_cases intro!: nonpos_Ints_of_int)
  also have "closed \<dots>" by (rule closed_of_int_image)
  finally show ?thesis .
qed

lemma plus_one_in_nonpos_Ints_imp: "z + 1 \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> z \<in> \<int>\<^sub>\<le>\<^sub>0"
  using nonpos_Ints_diff_Nats[of "z+1" "1"] by simp_all

lemma of_int_in_nonpos_Ints_iff:
  "(of_int n :: 'a :: ring_char_0) \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n \<le> 0"
  by (auto simp: nonpos_Ints_def)

lemma one_plus_of_int_in_nonpos_Ints_iff:
  "(1 + of_int n :: 'a :: ring_char_0) \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n \<le> -1"
proof -
  have "1 + of_int n = (of_int (n + 1) :: 'a)" by simp
  also have "\<dots> \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n + 1 \<le> 0" by (subst of_int_in_nonpos_Ints_iff) simp_all
  also have "\<dots> \<longleftrightarrow> n \<le> -1" by presburger
  finally show ?thesis .
qed

lemma one_minus_of_nat_in_nonpos_Ints_iff:
  "(1 - of_nat n :: 'a :: ring_char_0) \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n > 0"
proof -
  have "(1 - of_nat n :: 'a) = of_int (1 - int n)" by simp
  also have "\<dots> \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n > 0" by (subst of_int_in_nonpos_Ints_iff) presburger
  finally show ?thesis .
qed

lemma fraction_not_in_ints:
  assumes "\<not>(n dvd m)" "n \<noteq> 0"
  shows   "of_int m / of_int n \<notin> (\<int> :: 'a :: {division_ring,ring_char_0} set)"
proof
  assume "of_int m / (of_int n :: 'a) \<in> \<int>"
  then obtain k where "of_int m / of_int n = (of_int k :: 'a)" by (elim Ints_cases)
  with assms have "of_int m = (of_int (k * n) :: 'a)" by (auto simp add: field_split_simps)
  hence "m = k * n" by (subst (asm) of_int_eq_iff)
  hence "n dvd m" by simp
  with assms(1) show False by contradiction
qed

lemma fraction_not_in_nats:
  assumes "\<not>n dvd m" "n \<noteq> 0"
  shows   "of_int m / of_int n \<notin> (\<nat> :: 'a :: {division_ring,ring_char_0} set)"
proof
  assume "of_int m / of_int n \<in> (\<nat> :: 'a set)"
  also note Nats_subset_Ints
  finally have "of_int m / of_int n \<in> (\<int> :: 'a set)" .
  moreover have "of_int m / of_int n \<notin> (\<int> :: 'a set)"
    using assms by (intro fraction_not_in_ints)
  ultimately show False by contradiction
qed

lemma not_in_Ints_imp_not_in_nonpos_Ints: "z \<notin> \<int> \<Longrightarrow> z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  by (auto simp: Ints_def nonpos_Ints_def)

lemma double_in_nonpos_Ints_imp:
  assumes "2 * (z :: 'a :: field_char_0) \<in> \<int>\<^sub>\<le>\<^sub>0"
  shows   "z \<in> \<int>\<^sub>\<le>\<^sub>0 \<or> z + 1/2 \<in> \<int>\<^sub>\<le>\<^sub>0"
proof-
  from assms obtain k where k: "2 * z = - of_nat k" by (elim nonpos_Ints_cases')
  thus ?thesis by (cases "even k") (auto elim!: evenE oddE simp: field_simps)
qed


lemma sin_series: "(\<lambda>n. ((-1)^n / fact (2*n+1)) *\<^sub>R z^(2*n+1)) sums sin z"
proof -
  from sin_converges[of z] have "(\<lambda>n. sin_coeff n *\<^sub>R z^n) sums sin z" .
  also have "(\<lambda>n. sin_coeff n *\<^sub>R z^n) sums sin z \<longleftrightarrow>
                 (\<lambda>n. ((-1)^n / fact (2*n+1)) *\<^sub>R z^(2*n+1)) sums sin z"
    by (subst sums_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
       (auto simp: sin_coeff_def strict_mono_def ac_simps elim!: oddE)
  finally show ?thesis .
qed

lemma cos_series: "(\<lambda>n. ((-1)^n / fact (2*n)) *\<^sub>R z^(2*n)) sums cos z"
proof -
  from cos_converges[of z] have "(\<lambda>n. cos_coeff n *\<^sub>R z^n) sums cos z" .
  also have "(\<lambda>n. cos_coeff n *\<^sub>R z^n) sums cos z \<longleftrightarrow>
                 (\<lambda>n. ((-1)^n / fact (2*n)) *\<^sub>R z^(2*n)) sums cos z"
    by (subst sums_mono_reindex[of "\<lambda>n. 2*n", symmetric])
       (auto simp: cos_coeff_def strict_mono_def ac_simps elim!: evenE)
  finally show ?thesis .
qed

lemma sin_z_over_z_series:
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes "z \<noteq> 0"
  shows   "(\<lambda>n. (-1)^n / fact (2*n+1) * z^(2*n)) sums (sin z / z)"
proof -
  from sin_series[of z] have "(\<lambda>n. z * ((-1)^n / fact (2*n+1)) * z^(2*n)) sums sin z"
    by (simp add: field_simps scaleR_conv_of_real)
  from sums_mult[OF this, of "inverse z"] and assms show ?thesis
    by (simp add: field_simps)
qed

lemma sin_z_over_z_series':
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes "z \<noteq> 0"
  shows   "(\<lambda>n. sin_coeff (n+1) *\<^sub>R z^n) sums (sin z / z)"
proof -
  from sums_split_initial_segment[OF sin_converges[of z], of 1]
    have "(\<lambda>n. z * (sin_coeff (n+1) *\<^sub>R z ^ n)) sums sin z" by simp
  from sums_mult[OF this, of "inverse z"] assms show ?thesis by (simp add: field_simps)
qed

lemma has_field_derivative_sin_z_over_z:
  fixes A :: "'a :: {real_normed_field,banach} set"
  shows "((\<lambda>z. if z = 0 then 1 else sin z / z) has_field_derivative 0) (at 0 within A)"
      (is "(?f has_field_derivative ?f') _")
proof (rule has_field_derivative_at_within)
  have "((\<lambda>z::'a. \<Sum>n. of_real (sin_coeff (n+1)) * z^n)
            has_field_derivative (\<Sum>n. diffs (\<lambda>n. of_real (sin_coeff (n+1))) n * 0^n)) (at 0)"
  proof (rule termdiffs_strong)
    from summable_ignore_initial_segment[OF sums_summable[OF sin_converges[of "1::'a"]], of 1]
      show "summable (\<lambda>n. of_real (sin_coeff (n+1)) * (1::'a)^n)" by (simp add: of_real_def)
  qed simp
  also have "(\<lambda>z::'a. \<Sum>n. of_real (sin_coeff (n+1)) * z^n) = ?f"
  proof
    fix z
    show "(\<Sum>n. of_real (sin_coeff (n+1)) * z^n)  = ?f z"
      by (cases "z = 0") (insert sin_z_over_z_series'[of z],
            simp_all add: scaleR_conv_of_real sums_iff sin_coeff_def)
  qed
  also have "(\<Sum>n. diffs (\<lambda>n. of_real (sin_coeff (n + 1))) n * (0::'a) ^ n) =
                 diffs (\<lambda>n. of_real (sin_coeff (Suc n))) 0" by simp
  also have "\<dots> = 0" by (simp add: sin_coeff_def diffs_def)
  finally show "((\<lambda>z::'a. if z = 0 then 1 else sin z / z) has_field_derivative 0) (at 0)" .
qed

lemma round_Re_minimises_norm:
  "norm ((z::complex) - of_int m) \<ge> norm (z - of_int (round (Re z)))"
proof -
  let ?n = "round (Re z)"
  have "norm (z - of_int ?n) = sqrt ((Re z - of_int ?n)\<^sup>2 + (Im z)\<^sup>2)"
    by (simp add: cmod_def)
  also have "\<bar>Re z - of_int ?n\<bar> \<le> \<bar>Re z - of_int m\<bar>" by (rule round_diff_minimal)
  hence "sqrt ((Re z - of_int ?n)\<^sup>2 + (Im z)\<^sup>2) \<le> sqrt ((Re z - of_int m)\<^sup>2 + (Im z)\<^sup>2)"
    by (intro real_sqrt_le_mono add_mono) (simp_all add: abs_le_square_iff)
  also have "\<dots> = norm (z - of_int m)" by (simp add: cmod_def)
  finally show ?thesis .
qed

lemma Re_pos_in_ball:
  assumes "Re z > 0" "t \<in> ball z (Re z/2)"
  shows   "Re t > 0"
proof -
  have "Re (z - t) \<le> norm (z - t)" by (rule complex_Re_le_cmod)
  also from assms have "\<dots> < Re z / 2" by (simp add: dist_complex_def)
  finally show "Re t > 0" using assms by simp
qed

lemma no_nonpos_Int_in_ball_complex:
  assumes "Re z > 0" "t \<in> ball z (Re z/2)"
  shows   "t \<notin> \<int>\<^sub>\<le>\<^sub>0"
  using Re_pos_in_ball[OF assms] by (force elim!: nonpos_Ints_cases)

lemma no_nonpos_Int_in_ball:
  assumes "t \<in> ball z (dist z (round (Re z)))"
  shows   "t \<notin> \<int>\<^sub>\<le>\<^sub>0"
proof
  assume "t \<in> \<int>\<^sub>\<le>\<^sub>0"
  then obtain n where "t = of_int n" by (auto elim!: nonpos_Ints_cases)
  have "dist z (of_int n) \<le> dist z t + dist t (of_int n)" by (rule dist_triangle)
  also from assms have "dist z t < dist z (round (Re z))" by simp
  also have "\<dots> \<le> dist z (of_int n)"
    using round_Re_minimises_norm[of z] by (simp add: dist_complex_def)
  finally have "dist t (of_int n) > 0" by simp
  with \<open>t = of_int n\<close> show False by simp
qed

lemma no_nonpos_Int_in_ball':
  assumes "(z :: 'a :: {euclidean_space,real_normed_algebra_1}) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  obtains d where "d > 0" "\<And>t. t \<in> ball z d \<Longrightarrow> t \<notin> \<int>\<^sub>\<le>\<^sub>0"
proof (rule that)
  from assms show "setdist {z} \<int>\<^sub>\<le>\<^sub>0 > 0" by (subst setdist_gt_0_compact_closed) auto
next
  fix t assume "t \<in> ball z (setdist {z} \<int>\<^sub>\<le>\<^sub>0)"
  thus "t \<notin> \<int>\<^sub>\<le>\<^sub>0" using setdist_le_dist[of z "{z}" t "\<int>\<^sub>\<le>\<^sub>0"] by force
qed

lemma no_nonpos_Real_in_ball:
  assumes z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0" and t: "t \<in> ball z (if Im z = 0 then Re z / 2 else abs (Im z) / 2)"
  shows   "t \<notin> \<real>\<^sub>\<le>\<^sub>0"
using z
proof (cases "Im z = 0")
  assume A: "Im z = 0"
  with z have "Re z > 0" by (force simp add: complex_nonpos_Reals_iff)
  with t A Re_pos_in_ball[of z t] show ?thesis by (force simp add: complex_nonpos_Reals_iff)
next
  assume A: "Im z \<noteq> 0"
  have "abs (Im z) - abs (Im t) \<le> abs (Im z - Im t)" by linarith
  also have "\<dots> = abs (Im (z - t))" by simp
  also have "\<dots> \<le> norm (z - t)" by (rule abs_Im_le_cmod)
  also from A t have "\<dots> \<le> abs (Im z) / 2" by (simp add: dist_complex_def)
  finally have "abs (Im t) > 0" using A by simp
  thus ?thesis by (force simp add: complex_nonpos_Reals_iff)
qed


subsection \<open>The Euler form and the logarithmic Gamma function\<close>

text \<open>
  We define the Gamma function by first defining its multiplicative inverse \<open>rGamma\<close>.
  This is more convenient because \<open>rGamma\<close> is entire, which makes proofs of its
  properties more convenient because one does not have to watch out for discontinuities.
  (e.g. \<open>rGamma\<close> fulfils \<open>rGamma z = z * rGamma (z + 1)\<close> everywhere, whereas the \<open>\<Gamma>\<close> function
  does not fulfil the analogous equation on the non-positive integers)

  We define the \<open>\<Gamma>\<close> function (resp.\ its reciprocale) in the Euler form. This form has the advantage
  that it is a relatively simple limit that converges everywhere. The limit at the poles is 0
  (due to division by 0). The functional equation \<open>Gamma (z + 1) = z * Gamma z\<close> follows
  immediately from the definition.
\<close>

definition\<^marker>\<open>tag important\<close> Gamma_series :: "('a :: {banach,real_normed_field}) \<Rightarrow> nat \<Rightarrow> 'a" where
  "Gamma_series z n = fact n * exp (z * of_real (ln (of_nat n))) / pochhammer z (n+1)"

definition Gamma_series' :: "('a :: {banach,real_normed_field}) \<Rightarrow> nat \<Rightarrow> 'a" where
  "Gamma_series' z n = fact (n - 1) * exp (z * of_real (ln (of_nat n))) / pochhammer z n"

definition rGamma_series :: "('a :: {banach,real_normed_field}) \<Rightarrow> nat \<Rightarrow> 'a" where
  "rGamma_series z n = pochhammer z (n+1) / (fact n * exp (z * of_real (ln (of_nat n))))"

lemma Gamma_series_altdef: "Gamma_series z n = inverse (rGamma_series z n)"
  and rGamma_series_altdef: "rGamma_series z n = inverse (Gamma_series z n)"
  unfolding Gamma_series_def rGamma_series_def by simp_all

lemma rGamma_series_minus_of_nat:
  "eventually (\<lambda>n. rGamma_series (- of_nat k) n = 0) sequentially"
  using eventually_ge_at_top[of k]
  by eventually_elim (auto simp: rGamma_series_def pochhammer_of_nat_eq_0_iff)

lemma Gamma_series_minus_of_nat:
  "eventually (\<lambda>n. Gamma_series (- of_nat k) n = 0) sequentially"
  using eventually_ge_at_top[of k]
  by eventually_elim (auto simp: Gamma_series_def pochhammer_of_nat_eq_0_iff)

lemma Gamma_series'_minus_of_nat:
  "eventually (\<lambda>n. Gamma_series' (- of_nat k) n = 0) sequentially"
  using eventually_gt_at_top[of k]
  by eventually_elim (auto simp: Gamma_series'_def pochhammer_of_nat_eq_0_iff)

lemma rGamma_series_nonpos_Ints_LIMSEQ: "z \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> rGamma_series z \<longlonglongrightarrow> 0"
  by (elim nonpos_Ints_cases', hypsubst, subst tendsto_cong, rule rGamma_series_minus_of_nat, simp)

lemma Gamma_series_nonpos_Ints_LIMSEQ: "z \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Gamma_series z \<longlonglongrightarrow> 0"
  by (elim nonpos_Ints_cases', hypsubst, subst tendsto_cong, rule Gamma_series_minus_of_nat, simp)

lemma Gamma_series'_nonpos_Ints_LIMSEQ: "z \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Gamma_series' z \<longlonglongrightarrow> 0"
  by (elim nonpos_Ints_cases', hypsubst, subst tendsto_cong, rule Gamma_series'_minus_of_nat, simp)

lemma Gamma_series_Gamma_series':
  assumes z: "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>n. Gamma_series' z n / Gamma_series z n) \<longlonglongrightarrow> 1"
proof (rule Lim_transform_eventually)
  from eventually_gt_at_top[of "0::nat"]
    show "eventually (\<lambda>n. z / of_nat n + 1 = Gamma_series' z n / Gamma_series z n) sequentially"
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    from n z have "Gamma_series' z n / Gamma_series z n = (z + of_nat n) / of_nat n"
      by (cases n, simp)
         (auto simp add: Gamma_series_def Gamma_series'_def pochhammer_rec'
               dest: pochhammer_eq_0_imp_nonpos_Int plus_of_nat_eq_0_imp)
    also from n have "\<dots> = z / of_nat n + 1" by (simp add: field_split_simps)
    finally show "z / of_nat n + 1 = Gamma_series' z n / Gamma_series z n" ..
  qed
  have "(\<lambda>x. z / of_nat x) \<longlonglongrightarrow> 0"
    by (rule tendsto_norm_zero_cancel)
       (insert tendsto_mult[OF tendsto_const[of "norm z"] lim_inverse_n],
        simp add:  norm_divide inverse_eq_divide)
  from tendsto_add[OF this tendsto_const[of 1]] show "(\<lambda>n. z / of_nat n + 1) \<longlonglongrightarrow> 1" by simp
qed

text \<open>
  We now show that the series that defines the \<open>\<Gamma>\<close> function in the Euler form converges
  and that the function defined by it is continuous on the complex halfspace with positive
  real part.

  We do this by showing that the logarithm of the Euler series is continuous and converges
  locally uniformly, which means that the log-Gamma function defined by its limit is also
  continuous.

  This will later allow us to lift holomorphicity and continuity from the log-Gamma
  function to the inverse of the Gamma function, and from that to the Gamma function itself.
\<close>

definition\<^marker>\<open>tag important\<close> ln_Gamma_series :: "('a :: {banach,real_normed_field,ln}) \<Rightarrow> nat \<Rightarrow> 'a" where
  "ln_Gamma_series z n = z * ln (of_nat n) - ln z - (\<Sum>k=1..n. ln (z / of_nat k + 1))"

definition\<^marker>\<open>tag unimportant\<close> ln_Gamma_series' :: "('a :: {banach,real_normed_field,ln}) \<Rightarrow> nat \<Rightarrow> 'a" where
  "ln_Gamma_series' z n =
     - euler_mascheroni*z - ln z + (\<Sum>k=1..n. z / of_nat n - ln (z / of_nat k + 1))"

definition ln_Gamma :: "('a :: {banach,real_normed_field,ln}) \<Rightarrow> 'a" where
  "ln_Gamma z = lim (ln_Gamma_series z)"


text \<open>
  We now show that the log-Gamma series converges locally uniformly for all complex numbers except
  the non-positive integers. We do this by proving that the series is locally Cauchy.
\<close>

context
begin

private lemma ln_Gamma_series_complex_converges_aux:
  fixes z :: complex and k :: nat
  assumes z: "z \<noteq> 0" and k: "of_nat k \<ge> 2*norm z" "k \<ge> 2"
  shows "norm (z * ln (1 - 1/of_nat k) + ln (z/of_nat k + 1)) \<le> 2*(norm z + norm z^2) / of_nat k^2"
proof -
  let ?k = "of_nat k :: complex" and ?z = "norm z"
  have "z *ln (1 - 1/?k) + ln (z/?k+1) = z*(ln (1 - 1/?k :: complex) + 1/?k) + (ln (1+z/?k) - z/?k)"
    by (simp add: algebra_simps)
  also have "norm ... \<le> ?z * norm (ln (1-1/?k) + 1/?k :: complex) + norm (ln (1+z/?k) - z/?k)"
    by (subst norm_mult [symmetric], rule norm_triangle_ineq)
  also have "norm (Ln (1 + -1/?k) - (-1/?k)) \<le> (norm (-1/?k))\<^sup>2 / (1 - norm(-1/?k))"
    using k by (intro Ln_approx_linear) (simp add: norm_divide)
  hence "?z * norm (ln (1-1/?k) + 1/?k) \<le> ?z * ((norm (1/?k))^2 / (1 - norm (1/?k)))"
    by (intro mult_left_mono) simp_all
  also have "... \<le> (?z * (of_nat k / (of_nat k - 1))) / of_nat k^2" using k
    by (simp add: field_simps power2_eq_square norm_divide)
  also have "... \<le> (?z * 2) / of_nat k^2" using k
    by (intro divide_right_mono mult_left_mono) (simp_all add: field_simps)
  also have "norm (ln (1+z/?k) - z/?k) \<le> norm (z/?k)^2 / (1 - norm (z/?k))" using k
    by (intro Ln_approx_linear) (simp add: norm_divide)
  hence "norm (ln (1+z/?k) - z/?k) \<le> ?z^2 / of_nat k^2 / (1 - ?z / of_nat k)"
    by (simp add: field_simps norm_divide)
  also have "... \<le> (?z^2 * (of_nat k / (of_nat k - ?z))) / of_nat k^2" using k
    by (simp add: field_simps power2_eq_square)
  also have "... \<le> (?z^2 * 2) / of_nat k^2" using k
    by (intro divide_right_mono mult_left_mono) (simp_all add: field_simps)
  also note add_divide_distrib [symmetric]
  finally show ?thesis by (simp only: distrib_left mult.commute)
qed

lemma ln_Gamma_series_complex_converges:
  assumes z: "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  assumes d: "d > 0" "\<And>n. n \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> norm (z - of_int n) > d"
  shows "uniformly_convergent_on (ball z d) (\<lambda>n z. ln_Gamma_series z n :: complex)"
proof (intro Cauchy_uniformly_convergent uniformly_Cauchy_onI')
  fix e :: real assume e: "e > 0"
  define e'' where "e'' = (SUP t\<in>ball z d. norm t + norm t^2)"
  define e' where "e' = e / (2*e'')"
  have "bounded ((\<lambda>t. norm t + norm t^2) ` cball z d)"
    by (intro compact_imp_bounded compact_continuous_image) (auto intro!: continuous_intros)
  hence "bounded ((\<lambda>t. norm t + norm t^2) ` ball z d)" by (rule bounded_subset) auto
  hence bdd: "bdd_above ((\<lambda>t. norm t + norm t^2) ` ball z d)" by (rule bounded_imp_bdd_above)

  with z d(1) d(2)[of "-1"] have e''_pos: "e'' > 0" unfolding e''_def
    by (subst less_cSUP_iff) (auto intro!: add_pos_nonneg bexI[of _ z])
  have e'': "norm t + norm t^2 \<le> e''" if "t \<in> ball z d" for t unfolding e''_def using that
    by (rule cSUP_upper[OF _ bdd])
  from e z e''_pos have e': "e' > 0" unfolding e'_def
    by (intro divide_pos_pos mult_pos_pos add_pos_pos) (simp_all add: field_simps)

  have "summable (\<lambda>k. inverse ((real_of_nat k)^2))"
    by (rule inverse_power_summable) simp
  from summable_partial_sum_bound[OF this e'] guess M . note M = this

  define N where "N = max 2 (max (nat \<lceil>2 * (norm z + d)\<rceil>) M)"
  {
    from d have "\<lceil>2 * (cmod z + d)\<rceil> \<ge> \<lceil>0::real\<rceil>"
      by (intro ceiling_mono mult_nonneg_nonneg add_nonneg_nonneg) simp_all
    hence "2 * (norm z + d) \<le> of_nat (nat \<lceil>2 * (norm z + d)\<rceil>)" unfolding N_def
      by (simp_all)
    also have "... \<le> of_nat N" unfolding N_def
      by (subst of_nat_le_iff) (rule max.coboundedI2, rule max.cobounded1)
    finally have "of_nat N \<ge> 2 * (norm z + d)" .
    moreover have "N \<ge> 2" "N \<ge> M" unfolding N_def by simp_all
    moreover have "(\<Sum>k=m..n. 1/(of_nat k)\<^sup>2) < e'" if "m \<ge> N" for m n
      using M[OF order.trans[OF \<open>N \<ge> M\<close> that]] unfolding real_norm_def
      by (subst (asm) abs_of_nonneg) (auto intro: sum_nonneg simp: field_split_simps)
    moreover note calculation
  } note N = this

  show "\<exists>M. \<forall>t\<in>ball z d. \<forall>m\<ge>M. \<forall>n>m. dist (ln_Gamma_series t m) (ln_Gamma_series t n) < e"
    unfolding dist_complex_def
  proof (intro exI[of _ N] ballI allI impI)
    fix t m n assume t: "t \<in> ball z d" and mn: "m \<ge> N" "n > m"
    from d(2)[of 0] t have "0 < dist z 0 - dist z t" by (simp add: field_simps dist_complex_def)
    also have "dist z 0 - dist z t \<le> dist 0 t" using dist_triangle[of 0 z t]
      by (simp add: dist_commute)
    finally have t_nz: "t \<noteq> 0" by auto

    have "norm t \<le> norm z + norm (t - z)" by (rule norm_triangle_sub)
    also from t have "norm (t - z) < d" by (simp add: dist_complex_def norm_minus_commute)
    also have "2 * (norm z + d) \<le> of_nat N" by (rule N)
    also have "N \<le> m" by (rule mn)
    finally have norm_t: "2 * norm t < of_nat m" by simp

    have "ln_Gamma_series t m - ln_Gamma_series t n =
              (-(t * Ln (of_nat n)) - (-(t * Ln (of_nat m)))) +
              ((\<Sum>k=1..n. Ln (t / of_nat k + 1)) - (\<Sum>k=1..m. Ln (t / of_nat k + 1)))"
      by (simp add: ln_Gamma_series_def algebra_simps)
    also have "(\<Sum>k=1..n. Ln (t / of_nat k + 1)) - (\<Sum>k=1..m. Ln (t / of_nat k + 1)) =
                 (\<Sum>k\<in>{1..n}-{1..m}. Ln (t / of_nat k + 1))" using mn
      by (simp add: sum_diff)
    also from mn have "{1..n}-{1..m} = {Suc m..n}" by fastforce
    also have "-(t * Ln (of_nat n)) - (-(t * Ln (of_nat m))) =
                   (\<Sum>k = Suc m..n. t * Ln (of_nat (k - 1)) - t * Ln (of_nat k))" using mn
      by (subst sum_telescope'' [symmetric]) simp_all
    also have "... = (\<Sum>k = Suc m..n. t * Ln (of_nat (k - 1) / of_nat k))" using mn N
      by (intro sum_cong_Suc)
         (simp_all del: of_nat_Suc add: field_simps Ln_of_nat Ln_of_nat_over_of_nat)
    also have "of_nat (k - 1) / of_nat k = 1 - 1 / (of_nat k :: complex)" if "k \<in> {Suc m..n}" for k
      using that of_nat_eq_0_iff[of "Suc i" for i] by (cases k) (simp_all add: field_split_simps)
    hence "(\<Sum>k = Suc m..n. t * Ln (of_nat (k - 1) / of_nat k)) =
             (\<Sum>k = Suc m..n. t * Ln (1 - 1 / of_nat k))" using mn N
      by (intro sum.cong) simp_all
    also note sum.distrib [symmetric]
    also have "norm (\<Sum>k=Suc m..n. t * Ln (1 - 1/of_nat k) + Ln (t/of_nat k + 1)) \<le>
      (\<Sum>k=Suc m..n. 2 * (norm t + (norm t)\<^sup>2) / (real_of_nat k)\<^sup>2)" using t_nz N(2) mn norm_t
      by (intro order.trans[OF norm_sum sum_mono[OF ln_Gamma_series_complex_converges_aux]]) simp_all
    also have "... \<le> 2 * (norm t + norm t^2) * (\<Sum>k=Suc m..n. 1 / (of_nat k)\<^sup>2)"
      by (simp add: sum_distrib_left)
    also have "... < 2 * (norm t + norm t^2) * e'" using mn z t_nz
      by (intro mult_strict_left_mono N mult_pos_pos add_pos_pos) simp_all
    also from e''_pos have "... = e * ((cmod t + (cmod t)\<^sup>2) / e'')"
      by (simp add: e'_def field_simps power2_eq_square)
    also from e''[OF t] e''_pos e
      have "\<dots> \<le> e * 1" by (intro mult_left_mono) (simp_all add: field_simps)
    finally show "norm (ln_Gamma_series t m - ln_Gamma_series t n) < e" by simp
  qed
qed

end

lemma ln_Gamma_series_complex_converges':
  assumes z: "(z :: complex) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows "\<exists>d>0. uniformly_convergent_on (ball z d) (\<lambda>n z. ln_Gamma_series z n)"
proof -
  define d' where "d' = Re z"
  define d where "d = (if d' > 0 then d' / 2 else norm (z - of_int (round d')) / 2)"
  have "of_int (round d') \<in> \<int>\<^sub>\<le>\<^sub>0" if "d' \<le> 0" using that
    by (intro nonpos_Ints_of_int) (simp_all add: round_def)
  with assms have d_pos: "d > 0" unfolding d_def by (force simp: not_less)

  have "d < cmod (z - of_int n)" if "n \<in> \<int>\<^sub>\<le>\<^sub>0" for n
  proof (cases "Re z > 0")
    case True
    from nonpos_Ints_nonpos[OF that] have n: "n \<le> 0" by simp
    from True have "d = Re z/2" by (simp add: d_def d'_def)
    also from n True have "\<dots> < Re (z - of_int n)" by simp
    also have "\<dots> \<le> norm (z - of_int n)" by (rule complex_Re_le_cmod)
    finally show ?thesis .
  next
    case False
    with assms nonpos_Ints_of_int[of "round (Re z)"]
      have "z \<noteq> of_int (round d')" by (auto simp: not_less)
    with False have "d < norm (z - of_int (round d'))" by (simp add: d_def d'_def)
    also have "\<dots> \<le> norm (z - of_int n)" unfolding d'_def by (rule round_Re_minimises_norm)
    finally show ?thesis .
  qed
  hence conv: "uniformly_convergent_on (ball z d) (\<lambda>n z. ln_Gamma_series z n)"
    by (intro ln_Gamma_series_complex_converges d_pos z) simp_all
  from d_pos conv show ?thesis by blast
qed

lemma ln_Gamma_series_complex_converges'': "(z :: complex) \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> convergent (ln_Gamma_series z)"
  by (drule ln_Gamma_series_complex_converges') (auto intro: uniformly_convergent_imp_convergent)

theorem ln_Gamma_complex_LIMSEQ: "(z :: complex) \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> ln_Gamma_series z \<longlonglongrightarrow> ln_Gamma z"
  using ln_Gamma_series_complex_converges'' by (simp add: convergent_LIMSEQ_iff ln_Gamma_def)

lemma exp_ln_Gamma_series_complex:
  assumes "n > 0" "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "exp (ln_Gamma_series z n :: complex) = Gamma_series z n"
proof -
  from assms obtain m where m: "n = Suc m" by (cases n) blast
  from assms have "z \<noteq> 0" by (intro notI) auto
  with assms have "exp (ln_Gamma_series z n) =
          (of_nat n) powr z / (z * (\<Prod>k=1..n. exp (Ln (z / of_nat k + 1))))"
    unfolding ln_Gamma_series_def powr_def by (simp add: exp_diff exp_sum)
  also from assms have "(\<Prod>k=1..n. exp (Ln (z / of_nat k + 1))) = (\<Prod>k=1..n. z / of_nat k + 1)"
    by (intro prod.cong[OF refl], subst exp_Ln) (auto simp: field_simps plus_of_nat_eq_0_imp)
  also have "... = (\<Prod>k=1..n. z + k) / fact n"
    by (simp add: fact_prod)
    (subst prod_dividef [symmetric], simp_all add: field_simps)
  also from m have "z * ... = (\<Prod>k=0..n. z + k) / fact n"
    by (simp add: prod.atLeast0_atMost_Suc_shift prod.atLeast_Suc_atMost_Suc_shift del: prod.cl_ivl_Suc)
  also have "(\<Prod>k=0..n. z + k) = pochhammer z (Suc n)"
    unfolding pochhammer_prod
    by (simp add: prod.atLeast0_atMost_Suc atLeastLessThanSuc_atLeastAtMost)
  also have "of_nat n powr z / (pochhammer z (Suc n) / fact n) = Gamma_series z n"
    unfolding Gamma_series_def using assms by (simp add: field_split_simps powr_def)
  finally show ?thesis .
qed


lemma ln_Gamma_series'_aux:
  assumes "(z::complex) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>k. z / of_nat (Suc k) - ln (1 + z / of_nat (Suc k))) sums
              (ln_Gamma z + euler_mascheroni * z + ln z)" (is "?f sums ?s")
unfolding sums_def
proof (rule Lim_transform)
  show "(\<lambda>n. ln_Gamma_series z n + of_real (harm n - ln (of_nat n)) * z + ln z) \<longlonglongrightarrow> ?s"
    (is "?g \<longlonglongrightarrow> _")
    by (intro tendsto_intros ln_Gamma_complex_LIMSEQ euler_mascheroni_LIMSEQ_of_real assms)

  have A: "eventually (\<lambda>n. (\<Sum>k<n. ?f k) - ?g n = 0) sequentially"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    have "(\<Sum>k<n. ?f k) = (\<Sum>k=1..n. z / of_nat k - ln (1 + z / of_nat k))"
      by (subst atLeast0LessThan [symmetric], subst sum.shift_bounds_Suc_ivl [symmetric],
          subst atLeastLessThanSuc_atLeastAtMost) simp_all
    also have "\<dots> = z * of_real (harm n) - (\<Sum>k=1..n. ln (1 + z / of_nat k))"
      by (simp add: harm_def sum_subtractf sum_distrib_left divide_inverse)
    also from n have "\<dots> - ?g n = 0"
      by (simp add: ln_Gamma_series_def sum_subtractf algebra_simps)
    finally show "(\<Sum>k<n. ?f k) - ?g n = 0" .
  qed
  show "(\<lambda>n. (\<Sum>k<n. ?f k) - ?g n) \<longlonglongrightarrow> 0" by (subst tendsto_cong[OF A]) simp_all
qed


lemma uniformly_summable_deriv_ln_Gamma:
  assumes z: "(z :: 'a :: {real_normed_field,banach}) \<noteq> 0" and d: "d > 0" "d \<le> norm z/2"
  shows "uniformly_convergent_on (ball z d)
            (\<lambda>k z. \<Sum>i<k. inverse (of_nat (Suc i)) - inverse (z + of_nat (Suc i)))"
           (is "uniformly_convergent_on _ (\<lambda>k z. \<Sum>i<k. ?f i z)")
proof (rule Weierstrass_m_test'_ev)
  {
    fix t assume t: "t \<in> ball z d"
    have "norm z = norm (t + (z - t))" by simp
    have "norm (t + (z - t)) \<le> norm t + norm (z - t)" by (rule norm_triangle_ineq)
    also from t d have "norm (z - t) < norm z / 2" by (simp add: dist_norm)
    finally have A: "norm t > norm z / 2" using z by (simp add: field_simps)

    have "norm t = norm (z + (t - z))" by simp
    also have "\<dots> \<le> norm z + norm (t - z)" by (rule norm_triangle_ineq)
    also from t d have "norm (t - z) \<le> norm z / 2" by (simp add: dist_norm norm_minus_commute)
    also from z have "\<dots> < norm z" by simp
    finally have B: "norm t < 2 * norm z" by simp
    note A B
  } note ball = this

  show "eventually (\<lambda>n. \<forall>t\<in>ball z d. norm (?f n t) \<le> 4 * norm z * inverse (of_nat (Suc n)^2)) sequentially"
    using eventually_gt_at_top apply eventually_elim
  proof safe
    fix t :: 'a assume t: "t \<in> ball z d"
    from z ball[OF t] have t_nz: "t \<noteq> 0" by auto
    fix n :: nat assume n: "n > nat \<lceil>4 * norm z\<rceil>"
    from ball[OF t] t_nz have "4 * norm z > 2 * norm t" by simp
    also from n have "\<dots>  < of_nat n" by linarith
    finally have n: "of_nat n > 2 * norm t" .
    hence "of_nat n > norm t" by simp
    hence t': "t \<noteq> -of_nat (Suc n)" by (intro notI) (simp del: of_nat_Suc)

    with t_nz have "?f n t = 1 / (of_nat (Suc n) * (1 + of_nat (Suc n)/t))"
      by (simp add: field_split_simps eq_neg_iff_add_eq_0 del: of_nat_Suc)
    also have "norm \<dots> = inverse (of_nat (Suc n)) * inverse (norm (of_nat (Suc n)/t + 1))"
      by (simp add: norm_divide norm_mult field_split_simps del: of_nat_Suc)
    also {
      from z t_nz ball[OF t] have "of_nat (Suc n) / (4 * norm z) \<le> of_nat (Suc n) / (2 * norm t)"
        by (intro divide_left_mono mult_pos_pos) simp_all
      also have "\<dots> < norm (of_nat (Suc n) / t) - norm (1 :: 'a)"
        using t_nz n by (simp add: field_simps norm_divide del: of_nat_Suc)
      also have "\<dots> \<le> norm (of_nat (Suc n)/t + 1)" by (rule norm_diff_ineq)
      finally have "inverse (norm (of_nat (Suc n)/t + 1)) \<le> 4 * norm z / of_nat (Suc n)"
        using z by (simp add: field_split_simps norm_divide mult_ac del: of_nat_Suc)
    }
    also have "inverse (real_of_nat (Suc n)) * (4 * norm z / real_of_nat (Suc n)) =
                 4 * norm z * inverse (of_nat (Suc n)^2)"
                 by (simp add: field_split_simps power2_eq_square del: of_nat_Suc)
    finally show "norm (?f n t) \<le> 4 * norm z * inverse (of_nat (Suc n)^2)"
      by (simp del: of_nat_Suc)
  qed
next
  show "summable (\<lambda>n. 4 * norm z * inverse ((of_nat (Suc n))^2))"
    by (subst summable_Suc_iff) (simp add: summable_mult inverse_power_summable)
qed


subsection \<open>The Polygamma functions\<close>

lemma summable_deriv_ln_Gamma:
  "z \<noteq> (0 :: 'a :: {real_normed_field,banach}) \<Longrightarrow>
     summable (\<lambda>n. inverse (of_nat (Suc n)) - inverse (z + of_nat (Suc n)))"
  unfolding summable_iff_convergent
  by (rule uniformly_convergent_imp_convergent,
      rule uniformly_summable_deriv_ln_Gamma[of z "norm z/2"]) simp_all

definition\<^marker>\<open>tag important\<close> Polygamma :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a" where
  "Polygamma n z = (if n = 0 then
      (\<Sum>k. inverse (of_nat (Suc k)) - inverse (z + of_nat k)) - euler_mascheroni else
      (-1)^Suc n * fact n * (\<Sum>k. inverse ((z + of_nat k)^Suc n)))"

abbreviation\<^marker>\<open>tag important\<close> Digamma :: "('a :: {real_normed_field,banach}) \<Rightarrow> 'a" where
  "Digamma \<equiv> Polygamma 0"

lemma Digamma_def:
  "Digamma z = (\<Sum>k. inverse (of_nat (Suc k)) - inverse (z + of_nat k)) - euler_mascheroni"
  by (simp add: Polygamma_def)


lemma summable_Digamma:
  assumes "(z :: 'a :: {real_normed_field,banach}) \<noteq> 0"
  shows   "summable (\<lambda>n. inverse (of_nat (Suc n)) - inverse (z + of_nat n))"
proof -
  have sums: "(\<lambda>n. inverse (z + of_nat (Suc n)) - inverse (z + of_nat n)) sums
                       (0 - inverse (z + of_nat 0))"
    by (intro telescope_sums filterlim_compose[OF tendsto_inverse_0]
              tendsto_add_filterlim_at_infinity[OF tendsto_const] tendsto_of_nat)
  from summable_add[OF summable_deriv_ln_Gamma[OF assms] sums_summable[OF sums]]
    show "summable (\<lambda>n. inverse (of_nat (Suc n)) - inverse (z + of_nat n))" by simp
qed

lemma summable_offset:
  assumes "summable (\<lambda>n. f (n + k) :: 'a :: real_normed_vector)"
  shows   "summable f"
proof -
  from assms have "convergent (\<lambda>m. \<Sum>n<m. f (n + k))"
    using summable_iff_convergent by blast
  hence "convergent (\<lambda>m. (\<Sum>n<k. f n) + (\<Sum>n<m. f (n + k)))"
    by (intro convergent_add convergent_const)
  also have "(\<lambda>m. (\<Sum>n<k. f n) + (\<Sum>n<m. f (n + k))) = (\<lambda>m. \<Sum>n<m+k. f n)"
  proof
    fix m :: nat
    have "{..<m+k} = {..<k} \<union> {k..<m+k}" by auto
    also have "(\<Sum>n\<in>\<dots>. f n) = (\<Sum>n<k. f n) + (\<Sum>n=k..<m+k. f n)"
      by (rule sum.union_disjoint) auto
    also have "(\<Sum>n=k..<m+k. f n) = (\<Sum>n=0..<m+k-k. f (n + k))"
      using sum.shift_bounds_nat_ivl [of f 0 k m] by simp
    finally show "(\<Sum>n<k. f n) + (\<Sum>n<m. f (n + k)) = (\<Sum>n<m+k. f n)" by (simp add: atLeast0LessThan)
  qed
  finally have "(\<lambda>a. sum f {..<a}) \<longlonglongrightarrow> lim (\<lambda>m. sum f {..<m + k})"
    by (auto simp: convergent_LIMSEQ_iff dest: LIMSEQ_offset)
  thus ?thesis by (auto simp: summable_iff_convergent convergent_def)
qed

lemma Polygamma_converges:
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes z: "z \<noteq> 0" and n: "n \<ge> 2"
  shows "uniformly_convergent_on (ball z d) (\<lambda>k z. \<Sum>i<k. inverse ((z + of_nat i)^n))"
proof (rule Weierstrass_m_test'_ev)
  define e where "e = (1 + d / norm z)"
  define m where "m = nat \<lceil>norm z * e\<rceil>"
  {
    fix t assume t: "t \<in> ball z d"
    have "norm t = norm (z + (t - z))" by simp
    also have "\<dots> \<le> norm z + norm (t - z)" by (rule norm_triangle_ineq)
    also from t have "norm (t - z) < d" by (simp add: dist_norm norm_minus_commute)
    finally have "norm t < norm z * e" using z by (simp add: divide_simps e_def)
  } note ball = this

  show "eventually (\<lambda>k. \<forall>t\<in>ball z d. norm (inverse ((t + of_nat k)^n)) \<le>
            inverse (of_nat (k - m)^n)) sequentially"
    using eventually_gt_at_top[of m] apply eventually_elim
  proof (intro ballI)
    fix k :: nat and t :: 'a assume k: "k > m" and t: "t \<in> ball z d"
    from k have "real_of_nat (k - m) = of_nat k - of_nat m" by (simp add: of_nat_diff)
    also have "\<dots> \<le> norm (of_nat k :: 'a) - norm z * e"
      unfolding m_def by (subst norm_of_nat) linarith
    also from ball[OF t] have "\<dots> \<le> norm (of_nat k :: 'a) - norm t" by simp
    also have "\<dots> \<le> norm (of_nat k + t)" by (rule norm_diff_ineq)
    finally have "inverse ((norm (t + of_nat k))^n) \<le> inverse (real_of_nat (k - m)^n)" using k n
      by (intro le_imp_inverse_le power_mono) (simp_all add: add_ac del: of_nat_Suc)
    thus "norm (inverse ((t + of_nat k)^n)) \<le> inverse (of_nat (k - m)^n)"
      by (simp add: norm_inverse norm_power power_inverse)
  qed

  have "summable (\<lambda>k. inverse ((real_of_nat k)^n))"
    using inverse_power_summable[of n] n by simp
  hence "summable (\<lambda>k. inverse ((real_of_nat (k + m - m))^n))" by simp
  thus "summable (\<lambda>k. inverse ((real_of_nat (k - m))^n))" by (rule summable_offset)
qed

lemma Polygamma_converges':
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes z: "z \<noteq> 0" and n: "n \<ge> 2"
  shows "summable (\<lambda>k. inverse ((z + of_nat k)^n))"
  using uniformly_convergent_imp_convergent[OF Polygamma_converges[OF assms, of 1], of z]
  by (simp add: summable_iff_convergent)

theorem Digamma_LIMSEQ:
  fixes z :: "'a :: {banach,real_normed_field}"
  assumes z: "z \<noteq> 0"
  shows   "(\<lambda>m. of_real (ln (real m)) - (\<Sum>n<m. inverse (z + of_nat n))) \<longlonglongrightarrow> Digamma z"
proof -
  have "(\<lambda>n. of_real (ln (real n / (real (Suc n))))) \<longlonglongrightarrow> (of_real (ln 1) :: 'a)"
    by (intro tendsto_intros LIMSEQ_n_over_Suc_n) simp_all
  hence "(\<lambda>n. of_real (ln (real n / (real n + 1)))) \<longlonglongrightarrow> (0 :: 'a)" by (simp add: add_ac)
  hence lim: "(\<lambda>n. of_real (ln (real n)) - of_real (ln (real n + 1))) \<longlonglongrightarrow> (0::'a)"
  proof (rule Lim_transform_eventually)
    show "eventually (\<lambda>n. of_real (ln (real n / (real n + 1))) =
            of_real (ln (real n)) - (of_real (ln (real n + 1)) :: 'a)) at_top"
      using eventually_gt_at_top[of "0::nat"] by eventually_elim (simp add: ln_div)
  qed

  from summable_Digamma[OF z]
    have "(\<lambda>n. inverse (of_nat (n+1)) - inverse (z + of_nat n))
              sums (Digamma z + euler_mascheroni)"
    by (simp add: Digamma_def summable_sums)
  from sums_diff[OF this euler_mascheroni_sum]
    have "(\<lambda>n. of_real (ln (real (Suc n) + 1)) - of_real (ln (real n + 1)) - inverse (z + of_nat n))
            sums Digamma z" by (simp add: add_ac)
  hence "(\<lambda>m. (\<Sum>n<m. of_real (ln (real (Suc n) + 1)) - of_real (ln (real n + 1))) -
              (\<Sum>n<m. inverse (z + of_nat n))) \<longlonglongrightarrow> Digamma z"
    by (simp add: sums_def sum_subtractf)
  also have "(\<lambda>m. (\<Sum>n<m. of_real (ln (real (Suc n) + 1)) - of_real (ln (real n + 1)))) =
                 (\<lambda>m. of_real (ln (m + 1)) :: 'a)"
    by (subst sum_lessThan_telescope) simp_all
  finally show ?thesis by (rule Lim_transform) (insert lim, simp)
qed

theorem Polygamma_LIMSEQ:
  fixes z :: "'a :: {banach,real_normed_field}"
  assumes "z \<noteq> 0" and "n > 0"
  shows   "(\<lambda>k. inverse ((z + of_nat k)^Suc n)) sums ((-1) ^ Suc n * Polygamma n z / fact n)"
  using Polygamma_converges'[OF assms(1), of "Suc n"] assms(2)
  by (simp add: sums_iff Polygamma_def)

theorem has_field_derivative_ln_Gamma_complex [derivative_intros]:
  fixes z :: complex
  assumes z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(ln_Gamma has_field_derivative Digamma z) (at z)"
proof -
  have not_nonpos_Int [simp]: "t \<notin> \<int>\<^sub>\<le>\<^sub>0" if "Re t > 0" for t
    using that by (auto elim!: nonpos_Ints_cases')
  from z have z': "z \<notin> \<int>\<^sub>\<le>\<^sub>0" and z'': "z \<noteq> 0" using nonpos_Ints_subset_nonpos_Reals nonpos_Reals_zero_I
     by blast+
  let ?f' = "\<lambda>z k. inverse (of_nat (Suc k)) - inverse (z + of_nat (Suc k))"
  let ?f = "\<lambda>z k. z / of_nat (Suc k) - ln (1 + z / of_nat (Suc k))" and ?F' = "\<lambda>z. \<Sum>n. ?f' z n"
  define d where "d = min (norm z/2) (if Im z = 0 then Re z / 2 else abs (Im z) / 2)"
  from z have d: "d > 0" "norm z/2 \<ge> d" by (auto simp add: complex_nonpos_Reals_iff d_def)
  have ball: "Im t = 0 \<longrightarrow> Re t > 0" if "dist z t < d" for t
    using no_nonpos_Real_in_ball[OF z, of t] that unfolding d_def by (force simp add: complex_nonpos_Reals_iff)
  have sums: "(\<lambda>n. inverse (z + of_nat (Suc n)) - inverse (z + of_nat n)) sums
                       (0 - inverse (z + of_nat 0))"
    by (intro telescope_sums filterlim_compose[OF tendsto_inverse_0]
              tendsto_add_filterlim_at_infinity[OF tendsto_const] tendsto_of_nat)

  have "((\<lambda>z. \<Sum>n. ?f z n) has_field_derivative ?F' z) (at z)"
    using d z ln_Gamma_series'_aux[OF z']
    apply (intro has_field_derivative_series'(2)[of "ball z d" _ _ z] uniformly_summable_deriv_ln_Gamma)
    apply (auto intro!: derivative_eq_intros add_pos_pos mult_pos_pos dest!: ball
             simp: field_simps sums_iff nonpos_Reals_divide_of_nat_iff
             simp del: of_nat_Suc)
    apply (auto simp add: complex_nonpos_Reals_iff)
    done
  with z have "((\<lambda>z. (\<Sum>k. ?f z k) - euler_mascheroni * z - Ln z) has_field_derivative
                   ?F' z - euler_mascheroni - inverse z) (at z)"
    by (force intro!: derivative_eq_intros simp: Digamma_def)
  also have "?F' z - euler_mascheroni - inverse z = (?F' z + -inverse z) - euler_mascheroni" by simp
  also from sums have "-inverse z = (\<Sum>n. inverse (z + of_nat (Suc n)) - inverse (z + of_nat n))"
    by (simp add: sums_iff)
  also from sums summable_deriv_ln_Gamma[OF z'']
    have "?F' z + \<dots> =  (\<Sum>n. inverse (of_nat (Suc n)) - inverse (z + of_nat n))"
    by (subst suminf_add) (simp_all add: add_ac sums_iff)
  also have "\<dots> - euler_mascheroni = Digamma z" by (simp add: Digamma_def)
  finally have "((\<lambda>z. (\<Sum>k. ?f z k) - euler_mascheroni * z - Ln z)
                    has_field_derivative Digamma z) (at z)" .
  moreover from eventually_nhds_ball[OF d(1), of z]
    have "eventually (\<lambda>z. ln_Gamma z = (\<Sum>k. ?f z k) - euler_mascheroni * z - Ln z) (nhds z)"
  proof eventually_elim
    fix t assume "t \<in> ball z d"
    hence "t \<notin> \<int>\<^sub>\<le>\<^sub>0" by (auto dest!: ball elim!: nonpos_Ints_cases)
    from ln_Gamma_series'_aux[OF this]
      show "ln_Gamma t = (\<Sum>k. ?f t k) - euler_mascheroni * t - Ln t" by (simp add: sums_iff)
  qed
  ultimately show ?thesis by (subst DERIV_cong_ev[OF refl _ refl])
qed

declare has_field_derivative_ln_Gamma_complex[THEN DERIV_chain2, derivative_intros]


lemma Digamma_1 [simp]: "Digamma (1 :: 'a :: {real_normed_field,banach}) = - euler_mascheroni"
  by (simp add: Digamma_def)

lemma Digamma_plus1:
  assumes "z \<noteq> 0"
  shows   "Digamma (z+1) = Digamma z + 1/z"
proof -
  have sums: "(\<lambda>k. inverse (z + of_nat k) - inverse (z + of_nat (Suc k)))
                  sums (inverse (z + of_nat 0) - 0)"
    by (intro telescope_sums'[OF filterlim_compose[OF tendsto_inverse_0]]
              tendsto_add_filterlim_at_infinity[OF tendsto_const] tendsto_of_nat)
  have "Digamma (z+1) = (\<Sum>k. inverse (of_nat (Suc k)) - inverse (z + of_nat (Suc k))) -
          euler_mascheroni" (is "_ = suminf ?f - _") by (simp add: Digamma_def add_ac)
  also have "suminf ?f = (\<Sum>k. inverse (of_nat (Suc k)) - inverse (z + of_nat k)) +
                         (\<Sum>k. inverse (z + of_nat k) - inverse (z + of_nat (Suc k)))"
    using summable_Digamma[OF assms] sums by (subst suminf_add) (simp_all add: add_ac sums_iff)
  also have "(\<Sum>k. inverse (z + of_nat k) - inverse (z + of_nat (Suc k))) = 1/z"
    using sums by (simp add: sums_iff inverse_eq_divide)
  finally show ?thesis by (simp add: Digamma_def[of z])
qed

theorem Polygamma_plus1:
  assumes "z \<noteq> 0"
  shows   "Polygamma n (z + 1) = Polygamma n z + (-1)^n * fact n / (z ^ Suc n)"
proof (cases "n = 0")
  assume n: "n \<noteq> 0"
  let ?f = "\<lambda>k. inverse ((z + of_nat k) ^ Suc n)"
  have "Polygamma n (z + 1) = (-1) ^ Suc n * fact n * (\<Sum>k. ?f (k+1))"
    using n by (simp add: Polygamma_def add_ac)
  also have "(\<Sum>k. ?f (k+1)) + (\<Sum>k<1. ?f k) = (\<Sum>k. ?f k)"
    using Polygamma_converges'[OF assms, of "Suc n"] n
    by (subst suminf_split_initial_segment [symmetric]) simp_all
  hence "(\<Sum>k. ?f (k+1)) = (\<Sum>k. ?f k) - inverse (z ^ Suc n)" by (simp add: algebra_simps)
  also have "(-1) ^ Suc n * fact n * ((\<Sum>k. ?f k) - inverse (z ^ Suc n)) =
               Polygamma n z + (-1)^n * fact n / (z ^ Suc n)" using n
    by (simp add: inverse_eq_divide algebra_simps Polygamma_def)
  finally show ?thesis .
qed (insert assms, simp add: Digamma_plus1 inverse_eq_divide)

theorem Digamma_of_nat:
  "Digamma (of_nat (Suc n) :: 'a :: {real_normed_field,banach}) = harm n - euler_mascheroni"
proof (induction n)
  case (Suc n)
  have "Digamma (of_nat (Suc (Suc n)) :: 'a) = Digamma (of_nat (Suc n) + 1)" by simp
  also have "\<dots> = Digamma (of_nat (Suc n)) + inverse (of_nat (Suc n))"
    by (subst Digamma_plus1) (simp_all add: inverse_eq_divide del: of_nat_Suc)
  also have "Digamma (of_nat (Suc n) :: 'a) = harm n - euler_mascheroni " by (rule Suc)
  also have "\<dots> + inverse (of_nat (Suc n)) = harm (Suc n) - euler_mascheroni"
    by (simp add: harm_Suc)
  finally show ?case .
qed (simp add: harm_def)

lemma Digamma_numeral: "Digamma (numeral n) = harm (pred_numeral n) - euler_mascheroni"
  by (subst of_nat_numeral[symmetric], subst numeral_eq_Suc, subst Digamma_of_nat) (rule refl)

lemma Polygamma_of_real: "x \<noteq> 0 \<Longrightarrow> Polygamma n (of_real x) = of_real (Polygamma n x)"
  unfolding Polygamma_def using summable_Digamma[of x] Polygamma_converges'[of x "Suc n"]
  by (simp_all add: suminf_of_real)

lemma Polygamma_Real: "z \<in> \<real> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> Polygamma n z \<in> \<real>"
  by (elim Reals_cases, hypsubst, subst Polygamma_of_real) simp_all

lemma Digamma_half_integer:
  "Digamma (of_nat n + 1/2 :: 'a :: {real_normed_field,banach}) =
      (\<Sum>k<n. 2 / (of_nat (2*k+1))) - euler_mascheroni - of_real (2 * ln 2)"
proof (induction n)
  case 0
  have "Digamma (1/2 :: 'a) = of_real (Digamma (1/2))" by (simp add: Polygamma_of_real [symmetric])
  also have "Digamma (1/2::real) =
               (\<Sum>k. inverse (of_nat (Suc k)) - inverse (of_nat k + 1/2)) - euler_mascheroni"
    by (simp add: Digamma_def add_ac)
  also have "(\<Sum>k. inverse (of_nat (Suc k) :: real) - inverse (of_nat k + 1/2)) =
             (\<Sum>k. inverse (1/2) * (inverse (2 * of_nat (Suc k)) - inverse (2 * of_nat k + 1)))"
    by (simp_all add: add_ac inverse_mult_distrib[symmetric] ring_distribs del: inverse_divide)
  also have "\<dots> = - 2 * ln 2" using sums_minus[OF alternating_harmonic_series_sums']
    by (subst suminf_mult) (simp_all add: algebra_simps sums_iff)
  finally show ?case by simp
next
  case (Suc n)
  have nz: "2 * of_nat n + (1:: 'a) \<noteq> 0"
     using of_nat_neq_0[of "2*n"] by (simp only: of_nat_Suc) (simp add: add_ac)
  hence nz': "of_nat n + (1/2::'a) \<noteq> 0" by (simp add: field_simps)
  have "Digamma (of_nat (Suc n) + 1/2 :: 'a) = Digamma (of_nat n + 1/2 + 1)" by simp
  also from nz' have "\<dots> = Digamma (of_nat n + 1/2) + 1 / (of_nat n + 1/2)"
    by (rule Digamma_plus1)
  also from nz nz' have "1 / (of_nat n + 1/2 :: 'a) = 2 / (2 * of_nat n + 1)"
    by (subst divide_eq_eq) simp_all
  also note Suc
  finally show ?case by (simp add: add_ac)
qed

lemma Digamma_one_half: "Digamma (1/2) = - euler_mascheroni - of_real (2 * ln 2)"
  using Digamma_half_integer[of 0] by simp

lemma Digamma_real_three_halves_pos: "Digamma (3/2 :: real) > 0"
proof -
  have "-Digamma (3/2 :: real) = -Digamma (of_nat 1 + 1/2)" by simp
  also have "\<dots> = 2 * ln 2 + euler_mascheroni - 2" by (subst Digamma_half_integer) simp
  also note euler_mascheroni_less_13_over_22
  also note ln2_le_25_over_36
  finally show ?thesis by simp
qed


theorem has_field_derivative_Polygamma [derivative_intros]:
  fixes z :: "'a :: {real_normed_field,euclidean_space}"
  assumes z: "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows "(Polygamma n has_field_derivative Polygamma (Suc n) z) (at z within A)"
proof (rule has_field_derivative_at_within, cases "n = 0")
  assume n: "n = 0"
  let ?f = "\<lambda>k z. inverse (of_nat (Suc k)) - inverse (z + of_nat k)"
  let ?F = "\<lambda>z. \<Sum>k. ?f k z" and ?f' = "\<lambda>k z. inverse ((z + of_nat k)\<^sup>2)"
  from no_nonpos_Int_in_ball'[OF z] guess d . note d = this
  from z have summable: "summable (\<lambda>k. inverse (of_nat (Suc k)) - inverse (z + of_nat k))"
    by (intro summable_Digamma) force
  from z have conv: "uniformly_convergent_on (ball z d) (\<lambda>k z. \<Sum>i<k. inverse ((z + of_nat i)\<^sup>2))"
    by (intro Polygamma_converges) auto
  with d have "summable (\<lambda>k. inverse ((z + of_nat k)\<^sup>2))" unfolding summable_iff_convergent
    by (auto dest!: uniformly_convergent_imp_convergent simp: summable_iff_convergent )

  have "(?F has_field_derivative (\<Sum>k. ?f' k z)) (at z)"
  proof (rule has_field_derivative_series'[of "ball z d" _ _ z])
    fix k :: nat and t :: 'a assume t: "t \<in> ball z d"
    from t d(2)[of t] show "((\<lambda>z. ?f k z) has_field_derivative ?f' k t) (at t within ball z d)"
      by (auto intro!: derivative_eq_intros simp: power2_eq_square simp del: of_nat_Suc
               dest!: plus_of_nat_eq_0_imp elim!: nonpos_Ints_cases)
  qed (insert d(1) summable conv, (assumption|simp)+)
  with z show "(Polygamma n has_field_derivative Polygamma (Suc n) z) (at z)"
    unfolding Digamma_def [abs_def] Polygamma_def [abs_def] using n
    by (force simp: power2_eq_square intro!: derivative_eq_intros)
next
  assume n: "n \<noteq> 0"
  from z have z': "z \<noteq> 0" by auto
  from no_nonpos_Int_in_ball'[OF z] guess d . note d = this
  define n' where "n' = Suc n"
  from n have n': "n' \<ge> 2" by (simp add: n'_def)
  have "((\<lambda>z. \<Sum>k. inverse ((z + of_nat k) ^ n')) has_field_derivative
                (\<Sum>k. - of_nat n' * inverse ((z + of_nat k) ^ (n'+1)))) (at z)"
  proof (rule has_field_derivative_series'[of "ball z d" _ _ z])
    fix k :: nat and t :: 'a assume t: "t \<in> ball z d"
    with d have t': "t \<notin> \<int>\<^sub>\<le>\<^sub>0" "t \<noteq> 0" by auto
    show "((\<lambda>a. inverse ((a + of_nat k) ^ n')) has_field_derivative
                - of_nat n' * inverse ((t + of_nat k) ^ (n'+1))) (at t within ball z d)" using t'
      by (fastforce intro!: derivative_eq_intros simp: divide_simps power_diff dest: plus_of_nat_eq_0_imp)
  next
    have "uniformly_convergent_on (ball z d)
              (\<lambda>k z. (- of_nat n' :: 'a) * (\<Sum>i<k. inverse ((z + of_nat i) ^ (n'+1))))"
      using z' n by (intro uniformly_convergent_mult Polygamma_converges) (simp_all add: n'_def)
    thus "uniformly_convergent_on (ball z d)
              (\<lambda>k z. \<Sum>i<k. - of_nat n' * inverse ((z + of_nat i :: 'a) ^ (n'+1)))"
      by (subst (asm) sum_distrib_left) simp
  qed (insert Polygamma_converges'[OF z' n'] d, simp_all)
  also have "(\<Sum>k. - of_nat n' * inverse ((z + of_nat k) ^ (n' + 1))) =
               (- of_nat n') * (\<Sum>k. inverse ((z + of_nat k) ^ (n' + 1)))"
    using Polygamma_converges'[OF z', of "n'+1"] n' by (subst suminf_mult) simp_all
  finally have "((\<lambda>z. \<Sum>k. inverse ((z + of_nat k) ^ n')) has_field_derivative
                    - of_nat n' * (\<Sum>k. inverse ((z + of_nat k) ^ (n' + 1)))) (at z)" .
  from DERIV_cmult[OF this, of "(-1)^Suc n * fact n :: 'a"]
    show "(Polygamma n has_field_derivative Polygamma (Suc n) z) (at z)"
    unfolding n'_def Polygamma_def[abs_def] using n by (simp add: algebra_simps)
qed

declare has_field_derivative_Polygamma[THEN DERIV_chain2, derivative_intros]

lemma isCont_Polygamma [continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_field,euclidean_space}"
  shows "isCont f z \<Longrightarrow> f z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> isCont (\<lambda>x. Polygamma n (f x)) z"
  by (rule isCont_o2[OF _  DERIV_isCont[OF has_field_derivative_Polygamma]])

lemma continuous_on_Polygamma:
  "A \<inter> \<int>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> continuous_on A (Polygamma n :: _ \<Rightarrow> 'a :: {real_normed_field,euclidean_space})"
  by (intro continuous_at_imp_continuous_on isCont_Polygamma[OF continuous_ident] ballI) blast

lemma isCont_ln_Gamma_complex [continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> complex"
  shows "isCont f z \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> isCont (\<lambda>z. ln_Gamma (f z)) z"
  by (rule isCont_o2[OF _  DERIV_isCont[OF has_field_derivative_ln_Gamma_complex]])

lemma continuous_on_ln_Gamma_complex [continuous_intros]:
  fixes A :: "complex set"
  shows "A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> continuous_on A ln_Gamma"
  by (intro continuous_at_imp_continuous_on ballI isCont_ln_Gamma_complex[OF continuous_ident])
     fastforce

lemma deriv_Polygamma:
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "deriv (Polygamma m) z =
             Polygamma (Suc m) (z :: 'a :: {real_normed_field,euclidean_space})"
  by (intro DERIV_imp_deriv has_field_derivative_Polygamma assms)
    thm has_field_derivative_Polygamma

lemma higher_deriv_Polygamma:
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(deriv ^^ n) (Polygamma m) z =
             Polygamma (m + n) (z :: 'a :: {real_normed_field,euclidean_space})"
proof -
  have "eventually (\<lambda>u. (deriv ^^ n) (Polygamma m) u = Polygamma (m + n) u) (nhds z)"
  proof (induction n)
    case (Suc n)
    from Suc.IH have "eventually (\<lambda>z. eventually (\<lambda>u. (deriv ^^ n) (Polygamma m) u = Polygamma (m + n) u) (nhds z)) (nhds z)"
      by (simp add: eventually_eventually)
    hence "eventually (\<lambda>z. deriv ((deriv ^^ n) (Polygamma m)) z =
             deriv (Polygamma (m + n)) z) (nhds z)"
      by eventually_elim (intro deriv_cong_ev refl)
    moreover have "eventually (\<lambda>z. z \<in> UNIV - \<int>\<^sub>\<le>\<^sub>0) (nhds z)" using assms
      by (intro eventually_nhds_in_open open_Diff open_UNIV) auto
    ultimately show ?case by eventually_elim (simp_all add: deriv_Polygamma)
  qed simp_all
  thus ?thesis by (rule eventually_nhds_x_imp_x)
qed

lemma deriv_ln_Gamma_complex:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "deriv ln_Gamma z = Digamma (z :: complex)"
  by (intro DERIV_imp_deriv has_field_derivative_ln_Gamma_complex assms)


lemma higher_deriv_ln_Gamma_complex:
  assumes "(x::complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(deriv ^^ j) ln_Gamma x = (if j = 0 then ln_Gamma x else Polygamma (j - 1) x)"
proof (cases j)
  case (Suc j')
  have "(deriv ^^ j') (deriv ln_Gamma) x = (deriv ^^ j') Digamma x"
    using eventually_nhds_in_open[of "UNIV - \<real>\<^sub>\<le>\<^sub>0" x] assms
    by (intro higher_deriv_cong_ev refl)
       (auto elim!: eventually_mono simp: open_Diff deriv_ln_Gamma_complex)
  also have "\<dots> = Polygamma j' x" using assms
    by (subst higher_deriv_Polygamma)
       (auto elim!: nonpos_Ints_cases simp: complex_nonpos_Reals_iff)
  finally show ?thesis using Suc by (simp del: funpow.simps add: funpow_Suc_right)
qed simp_all


text \<open>
  We define a type class that captures all the fundamental properties of the inverse of the Gamma function
  and defines the Gamma function upon that. This allows us to instantiate the type class both for
  the reals and for the complex numbers with a minimal amount of proof duplication.
\<close>

class\<^marker>\<open>tag unimportant\<close> Gamma = real_normed_field + complete_space +
  fixes rGamma :: "'a \<Rightarrow> 'a"
  assumes rGamma_eq_zero_iff_aux: "rGamma z = 0 \<longleftrightarrow> (\<exists>n. z = - of_nat n)"
  assumes differentiable_rGamma_aux1:
    "(\<And>n. z \<noteq> - of_nat n) \<Longrightarrow>
     let d = (THE d. (\<lambda>n. \<Sum>k<n. inverse (of_nat (Suc k)) - inverse (z + of_nat k))
               \<longlonglongrightarrow> d) - scaleR euler_mascheroni 1
     in  filterlim (\<lambda>y. (rGamma y - rGamma z + rGamma z * d * (y - z)) /\<^sub>R
                        norm (y - z)) (nhds 0) (at z)"
  assumes differentiable_rGamma_aux2:
    "let z = - of_nat n
     in  filterlim (\<lambda>y. (rGamma y - rGamma z - (-1)^n * (prod of_nat {1..n}) * (y - z)) /\<^sub>R
                        norm (y - z)) (nhds 0) (at z)"
  assumes rGamma_series_aux: "(\<And>n. z \<noteq> - of_nat n) \<Longrightarrow>
             let fact' = (\<lambda>n. prod of_nat {1..n});
                 exp = (\<lambda>x. THE e. (\<lambda>n. \<Sum>k<n. x^k /\<^sub>R fact k) \<longlonglongrightarrow> e);
                 pochhammer' = (\<lambda>a n. (\<Prod>n = 0..n. a + of_nat n))
             in  filterlim (\<lambda>n. pochhammer' z n / (fact' n * exp (z * (ln (of_nat n) *\<^sub>R 1))))
                     (nhds (rGamma z)) sequentially"
begin
subclass banach ..
end

definition "Gamma z = inverse (rGamma z)"


subsection \<open>Basic properties\<close>

lemma Gamma_nonpos_Int: "z \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Gamma z = 0"
  and rGamma_nonpos_Int: "z \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> rGamma z = 0"
  using rGamma_eq_zero_iff_aux[of z] unfolding Gamma_def by (auto elim!: nonpos_Ints_cases')

lemma Gamma_nonzero: "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Gamma z \<noteq> 0"
  and rGamma_nonzero: "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> rGamma z \<noteq> 0"
  using rGamma_eq_zero_iff_aux[of z] unfolding Gamma_def by (auto elim!: nonpos_Ints_cases')

lemma Gamma_eq_zero_iff: "Gamma z = 0 \<longleftrightarrow> z \<in> \<int>\<^sub>\<le>\<^sub>0"
  and rGamma_eq_zero_iff: "rGamma z = 0 \<longleftrightarrow> z \<in> \<int>\<^sub>\<le>\<^sub>0"
  using rGamma_eq_zero_iff_aux[of z] unfolding Gamma_def by (auto elim!: nonpos_Ints_cases')

lemma rGamma_inverse_Gamma: "rGamma z = inverse (Gamma z)"
  unfolding Gamma_def by simp

lemma rGamma_series_LIMSEQ [tendsto_intros]:
  "rGamma_series z \<longlonglongrightarrow> rGamma z"
proof (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0")
  case False
  hence "z \<noteq> - of_nat n" for n by auto
  from rGamma_series_aux[OF this] show ?thesis
    by (simp add: rGamma_series_def[abs_def] fact_prod pochhammer_Suc_prod
                  exp_def of_real_def[symmetric] suminf_def sums_def[abs_def] atLeast0AtMost)
qed (insert rGamma_eq_zero_iff[of z], simp_all add: rGamma_series_nonpos_Ints_LIMSEQ)

theorem Gamma_series_LIMSEQ [tendsto_intros]:
  "Gamma_series z \<longlonglongrightarrow> Gamma z"
proof (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0")
  case False
  hence "(\<lambda>n. inverse (rGamma_series z n)) \<longlonglongrightarrow> inverse (rGamma z)"
    by (intro tendsto_intros) (simp_all add: rGamma_eq_zero_iff)
  also have "(\<lambda>n. inverse (rGamma_series z n)) = Gamma_series z"
    by (simp add: rGamma_series_def Gamma_series_def[abs_def])
  finally show ?thesis by (simp add: Gamma_def)
qed (insert Gamma_eq_zero_iff[of z], simp_all add: Gamma_series_nonpos_Ints_LIMSEQ)

lemma Gamma_altdef: "Gamma z = lim (Gamma_series z)"
  using Gamma_series_LIMSEQ[of z] by (simp add: limI)

lemma rGamma_1 [simp]: "rGamma 1 = 1"
proof -
  have A: "eventually (\<lambda>n. rGamma_series 1 n = of_nat (Suc n) / of_nat n) sequentially"
    using eventually_gt_at_top[of "0::nat"]
    by (force elim!: eventually_mono simp: rGamma_series_def exp_of_real pochhammer_fact
                    field_split_simps pochhammer_rec' dest!: pochhammer_eq_0_imp_nonpos_Int)
  have "rGamma_series 1 \<longlonglongrightarrow> 1" by (subst tendsto_cong[OF A]) (rule LIMSEQ_Suc_n_over_n)
  moreover have "rGamma_series 1 \<longlonglongrightarrow> rGamma 1" by (rule tendsto_intros)
  ultimately show ?thesis by (intro LIMSEQ_unique)
qed

lemma rGamma_plus1: "z * rGamma (z + 1) = rGamma z"
proof -
  let ?f = "\<lambda>n. (z + 1) * inverse (of_nat n) + 1"
  have "eventually (\<lambda>n. ?f n * rGamma_series z n = z * rGamma_series (z + 1) n) sequentially"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    hence "z * rGamma_series (z + 1) n = inverse (of_nat n) *
             pochhammer z (Suc (Suc n)) / (fact n * exp (z * of_real (ln (of_nat n))))"
      by (subst pochhammer_rec) (simp add: rGamma_series_def field_simps exp_add exp_of_real)
    also from n have "\<dots> = ?f n * rGamma_series z n"
      by (subst pochhammer_rec') (simp_all add: field_split_simps rGamma_series_def)
    finally show "?f n * rGamma_series z n = z * rGamma_series (z + 1) n" ..
  qed
  moreover have "(\<lambda>n. ?f n * rGamma_series z n) \<longlonglongrightarrow> ((z+1) * 0 + 1) * rGamma z"
    by (intro tendsto_intros lim_inverse_n)
  hence "(\<lambda>n. ?f n * rGamma_series z n) \<longlonglongrightarrow> rGamma z" by simp
  ultimately have "(\<lambda>n. z * rGamma_series (z + 1) n) \<longlonglongrightarrow> rGamma z"
    by (blast intro: Lim_transform_eventually)
  moreover have "(\<lambda>n. z * rGamma_series (z + 1) n) \<longlonglongrightarrow> z * rGamma (z + 1)"
    by (intro tendsto_intros)
  ultimately show "z * rGamma (z + 1) = rGamma z" using LIMSEQ_unique by blast
qed


lemma pochhammer_rGamma: "rGamma z = pochhammer z n * rGamma (z + of_nat n)"
proof (induction n arbitrary: z)
  case (Suc n z)
  have "rGamma z = pochhammer z n * rGamma (z + of_nat n)" by (rule Suc.IH)
  also note rGamma_plus1 [symmetric]
  finally show ?case by (simp add: add_ac pochhammer_rec')
qed simp_all

theorem Gamma_plus1: "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Gamma (z + 1) = z * Gamma z"
  using rGamma_plus1[of z] by (simp add: rGamma_inverse_Gamma field_simps Gamma_eq_zero_iff)

theorem pochhammer_Gamma: "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> pochhammer z n = Gamma (z + of_nat n) / Gamma z"
  using pochhammer_rGamma[of z]
  by (simp add: rGamma_inverse_Gamma Gamma_eq_zero_iff field_simps)

lemma Gamma_0 [simp]: "Gamma 0 = 0"
  and rGamma_0 [simp]: "rGamma 0 = 0"
  and Gamma_neg_1 [simp]: "Gamma (- 1) = 0"
  and rGamma_neg_1 [simp]: "rGamma (- 1) = 0"
  and Gamma_neg_numeral [simp]: "Gamma (- numeral n) = 0"
  and rGamma_neg_numeral [simp]: "rGamma (- numeral n) = 0"
  and Gamma_neg_of_nat [simp]: "Gamma (- of_nat m) = 0"
  and rGamma_neg_of_nat [simp]: "rGamma (- of_nat m) = 0"
  by (simp_all add: rGamma_eq_zero_iff Gamma_eq_zero_iff)

lemma Gamma_1 [simp]: "Gamma 1 = 1" unfolding Gamma_def by simp

theorem Gamma_fact: "Gamma (1 + of_nat n) = fact n"
  by (simp add: pochhammer_fact pochhammer_Gamma of_nat_in_nonpos_Ints_iff flip: of_nat_Suc)

lemma Gamma_numeral: "Gamma (numeral n) = fact (pred_numeral n)"
  by (subst of_nat_numeral[symmetric], subst numeral_eq_Suc,
      subst of_nat_Suc, subst Gamma_fact) (rule refl)

lemma Gamma_of_int: "Gamma (of_int n) = (if n > 0 then fact (nat (n - 1)) else 0)"
proof (cases "n > 0")
  case True
  hence "Gamma (of_int n) = Gamma (of_nat (Suc (nat (n - 1))))" by (subst of_nat_Suc) simp_all
  with True show ?thesis by (subst (asm) of_nat_Suc, subst (asm) Gamma_fact) simp
qed (simp_all add: Gamma_eq_zero_iff nonpos_Ints_of_int)

lemma rGamma_of_int: "rGamma (of_int n) = (if n > 0 then inverse (fact (nat (n - 1))) else 0)"
  by (simp add: Gamma_of_int rGamma_inverse_Gamma)

lemma Gamma_seriesI:
  assumes "(\<lambda>n. g n / Gamma_series z n) \<longlonglongrightarrow> 1"
  shows   "g \<longlonglongrightarrow> Gamma z"
proof (rule Lim_transform_eventually)
  have "1/2 > (0::real)" by simp
  from tendstoD[OF assms, OF this]
    show "eventually (\<lambda>n. g n / Gamma_series z n * Gamma_series z n = g n) sequentially"
    by (force elim!: eventually_mono simp: dist_real_def)
  from assms have "(\<lambda>n. g n / Gamma_series z n * Gamma_series z n) \<longlonglongrightarrow> 1 * Gamma z"
    by (intro tendsto_intros)
  thus "(\<lambda>n. g n / Gamma_series z n * Gamma_series z n) \<longlonglongrightarrow> Gamma z" by simp
qed

lemma Gamma_seriesI':
  assumes "f \<longlonglongrightarrow> rGamma z"
  assumes "(\<lambda>n. g n * f n) \<longlonglongrightarrow> 1"
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "g \<longlonglongrightarrow> Gamma z"
proof (rule Lim_transform_eventually)
  have "1/2 > (0::real)" by simp
  from tendstoD[OF assms(2), OF this] show "eventually (\<lambda>n. g n * f n / f n = g n) sequentially"
    by (force elim!: eventually_mono simp: dist_real_def)
  from assms have "(\<lambda>n. g n * f n / f n) \<longlonglongrightarrow> 1 / rGamma z"
    by (intro tendsto_divide assms) (simp_all add: rGamma_eq_zero_iff)
  thus "(\<lambda>n. g n * f n / f n) \<longlonglongrightarrow> Gamma z" by (simp add: Gamma_def divide_inverse)
qed

lemma Gamma_series'_LIMSEQ: "Gamma_series' z \<longlonglongrightarrow> Gamma z"
  by (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0") (simp_all add: Gamma_nonpos_Int Gamma_seriesI[OF Gamma_series_Gamma_series']
                                      Gamma_series'_nonpos_Ints_LIMSEQ[of z])


subsection \<open>Differentiability\<close>

lemma has_field_derivative_rGamma_no_nonpos_int:
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(rGamma has_field_derivative -rGamma z * Digamma z) (at z within A)"
proof (rule has_field_derivative_at_within)
  from assms have "z \<noteq> - of_nat n" for n by auto
  from differentiable_rGamma_aux1[OF this]
    show "(rGamma has_field_derivative -rGamma z * Digamma z) (at z)"
         unfolding Digamma_def suminf_def sums_def[abs_def]
                   has_field_derivative_def has_derivative_def netlimit_at
    by (simp add: Let_def bounded_linear_mult_right mult_ac of_real_def [symmetric])
qed

lemma has_field_derivative_rGamma_nonpos_int:
  "(rGamma has_field_derivative (-1)^n * fact n) (at (- of_nat n) within A)"
  apply (rule has_field_derivative_at_within)
  using differentiable_rGamma_aux2[of n]
  unfolding Let_def has_field_derivative_def has_derivative_def netlimit_at
  by (simp only: bounded_linear_mult_right mult_ac of_real_def [symmetric] fact_prod) simp

lemma has_field_derivative_rGamma [derivative_intros]:
  "(rGamma has_field_derivative (if z \<in> \<int>\<^sub>\<le>\<^sub>0 then (-1)^(nat \<lfloor>norm z\<rfloor>) * fact (nat \<lfloor>norm z\<rfloor>)
      else -rGamma z * Digamma z)) (at z within A)"
using has_field_derivative_rGamma_no_nonpos_int[of z A]
      has_field_derivative_rGamma_nonpos_int[of "nat \<lfloor>norm z\<rfloor>" A]
  by (auto elim!: nonpos_Ints_cases')

declare has_field_derivative_rGamma_no_nonpos_int [THEN DERIV_chain2, derivative_intros]
declare has_field_derivative_rGamma [THEN DERIV_chain2, derivative_intros]
declare has_field_derivative_rGamma_nonpos_int [derivative_intros]
declare has_field_derivative_rGamma_no_nonpos_int [derivative_intros]
declare has_field_derivative_rGamma [derivative_intros]

theorem has_field_derivative_Gamma [derivative_intros]:
  "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> (Gamma has_field_derivative Gamma z * Digamma z) (at z within A)"
  unfolding Gamma_def [abs_def]
  by (fastforce intro!: derivative_eq_intros simp: rGamma_eq_zero_iff)

declare has_field_derivative_Gamma[THEN DERIV_chain2, derivative_intros]

(* TODO: Hide ugly facts properly *)
hide_fact rGamma_eq_zero_iff_aux differentiable_rGamma_aux1 differentiable_rGamma_aux2
          differentiable_rGamma_aux2 rGamma_series_aux Gamma_class.rGamma_eq_zero_iff_aux

lemma continuous_on_rGamma [continuous_intros]: "continuous_on A rGamma"
  by (rule DERIV_continuous_on has_field_derivative_rGamma)+

lemma continuous_on_Gamma [continuous_intros]: "A \<inter> \<int>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> continuous_on A Gamma"
  by (rule DERIV_continuous_on has_field_derivative_Gamma)+ blast

lemma isCont_rGamma [continuous_intros]:
  "isCont f z \<Longrightarrow> isCont (\<lambda>x. rGamma (f x)) z"
  by (rule isCont_o2[OF _  DERIV_isCont[OF has_field_derivative_rGamma]])

lemma isCont_Gamma [continuous_intros]:
  "isCont f z \<Longrightarrow> f z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> isCont (\<lambda>x. Gamma (f x)) z"
  by (rule isCont_o2[OF _  DERIV_isCont[OF has_field_derivative_Gamma]])

subsection\<^marker>\<open>tag unimportant\<close> \<open>The complex Gamma function\<close>

instantiation\<^marker>\<open>tag unimportant\<close> complex :: Gamma
begin

definition\<^marker>\<open>tag unimportant\<close> rGamma_complex :: "complex \<Rightarrow> complex" where
  "rGamma_complex z = lim (rGamma_series z)"

lemma rGamma_series_complex_converges:
        "convergent (rGamma_series (z :: complex))" (is "?thesis1")
  and rGamma_complex_altdef:
        "rGamma z = (if z \<in> \<int>\<^sub>\<le>\<^sub>0 then 0 else exp (-ln_Gamma z))" (is "?thesis2")
proof -
  have "?thesis1 \<and> ?thesis2"
  proof (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0")
    case False
    have "rGamma_series z \<longlonglongrightarrow> exp (- ln_Gamma z)"
    proof (rule Lim_transform_eventually)
      from ln_Gamma_series_complex_converges'[OF False] guess d by (elim exE conjE)
      from this(1) uniformly_convergent_imp_convergent[OF this(2), of z]
        have "ln_Gamma_series z \<longlonglongrightarrow> lim (ln_Gamma_series z)" by (simp add: convergent_LIMSEQ_iff)
      thus "(\<lambda>n. exp (-ln_Gamma_series z n)) \<longlonglongrightarrow> exp (- ln_Gamma z)"
        unfolding convergent_def ln_Gamma_def by (intro tendsto_exp tendsto_minus)
      from eventually_gt_at_top[of "0::nat"] exp_ln_Gamma_series_complex False
        show "eventually (\<lambda>n. exp (-ln_Gamma_series z n) = rGamma_series z n) sequentially"
        by (force elim!: eventually_mono simp: exp_minus Gamma_series_def rGamma_series_def)
    qed
    with False show ?thesis
      by (auto simp: convergent_def rGamma_complex_def intro!: limI)
  next
    case True
    then obtain k where "z = - of_nat k" by (erule nonpos_Ints_cases')
    also have "rGamma_series \<dots> \<longlonglongrightarrow> 0"
      by (subst tendsto_cong[OF rGamma_series_minus_of_nat]) (simp_all add: convergent_const)
    finally show ?thesis using True
      by (auto simp: rGamma_complex_def convergent_def intro!: limI)
  qed
  thus "?thesis1" "?thesis2" by blast+
qed

context\<^marker>\<open>tag unimportant\<close>
begin

(* TODO: duplication *)
private lemma rGamma_complex_plus1: "z * rGamma (z + 1) = rGamma (z :: complex)"
proof -
  let ?f = "\<lambda>n. (z + 1) * inverse (of_nat n) + 1"
  have "eventually (\<lambda>n. ?f n * rGamma_series z n = z * rGamma_series (z + 1) n) sequentially"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    hence "z * rGamma_series (z + 1) n = inverse (of_nat n) *
             pochhammer z (Suc (Suc n)) / (fact n * exp (z * of_real (ln (of_nat n))))"
      by (subst pochhammer_rec) (simp add: rGamma_series_def field_simps exp_add exp_of_real)
    also from n have "\<dots> = ?f n * rGamma_series z n"
      by (subst pochhammer_rec') (simp_all add: field_split_simps rGamma_series_def add_ac)
    finally show "?f n * rGamma_series z n = z * rGamma_series (z + 1) n" ..
  qed
  moreover have "(\<lambda>n. ?f n * rGamma_series z n) \<longlonglongrightarrow> ((z+1) * 0 + 1) * rGamma z"
    using rGamma_series_complex_converges
    by (intro tendsto_intros lim_inverse_n)
       (simp_all add: convergent_LIMSEQ_iff rGamma_complex_def)
  hence "(\<lambda>n. ?f n * rGamma_series z n) \<longlonglongrightarrow> rGamma z" by simp
  ultimately have "(\<lambda>n. z * rGamma_series (z + 1) n) \<longlonglongrightarrow> rGamma z"
    by (blast intro: Lim_transform_eventually)
  moreover have "(\<lambda>n. z * rGamma_series (z + 1) n) \<longlonglongrightarrow> z * rGamma (z + 1)"
    using rGamma_series_complex_converges
    by (auto intro!: tendsto_mult simp: rGamma_complex_def convergent_LIMSEQ_iff)
  ultimately show "z * rGamma (z + 1) = rGamma z" using LIMSEQ_unique by blast
qed

private lemma has_field_derivative_rGamma_complex_no_nonpos_Int:
  assumes "(z :: complex) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(rGamma has_field_derivative - rGamma z * Digamma z) (at z)"
proof -
  have diff: "(rGamma has_field_derivative - rGamma z * Digamma z) (at z)" if "Re z > 0" for z
  proof (subst DERIV_cong_ev[OF refl _ refl])
    from that have "eventually (\<lambda>t. t \<in> ball z (Re z/2)) (nhds z)"
      by (intro eventually_nhds_in_nhd) simp_all
    thus "eventually (\<lambda>t. rGamma t = exp (- ln_Gamma t)) (nhds z)"
      using no_nonpos_Int_in_ball_complex[OF that]
      by (auto elim!: eventually_mono simp: rGamma_complex_altdef)
  next
    have "z \<notin> \<real>\<^sub>\<le>\<^sub>0" using that by (simp add: complex_nonpos_Reals_iff)
    with that show "((\<lambda>t. exp (- ln_Gamma t)) has_field_derivative (-rGamma z * Digamma z)) (at z)"
     by (force elim!: nonpos_Ints_cases intro!: derivative_eq_intros simp: rGamma_complex_altdef)
  qed

  from assms show "(rGamma has_field_derivative - rGamma z * Digamma z) (at z)"
  proof (induction "nat \<lfloor>1 - Re z\<rfloor>" arbitrary: z)
    case (Suc n z)
    from Suc.prems have z: "z \<noteq> 0" by auto
    from Suc.hyps have "n = nat \<lfloor>- Re z\<rfloor>" by linarith
    hence A: "n = nat \<lfloor>1 - Re (z + 1)\<rfloor>" by simp
    from Suc.prems have B: "z + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0" by (force dest: plus_one_in_nonpos_Ints_imp)

    have "((\<lambda>z. z * (rGamma \<circ> (\<lambda>z. z + 1)) z) has_field_derivative
      -rGamma (z + 1) * (Digamma (z + 1) * z - 1)) (at z)"
      by (rule derivative_eq_intros DERIV_chain Suc refl A B)+ (simp add: algebra_simps)
    also have "(\<lambda>z. z * (rGamma \<circ> (\<lambda>z. z + 1 :: complex)) z) = rGamma"
      by (simp add: rGamma_complex_plus1)
    also from z have "Digamma (z + 1) * z - 1 = z * Digamma z"
      by (subst Digamma_plus1) (simp_all add: field_simps)
    also have "-rGamma (z + 1) * (z * Digamma z) = -rGamma z * Digamma z"
      by (simp add: rGamma_complex_plus1[of z, symmetric])
    finally show ?case .
  qed (intro diff, simp)
qed

private lemma rGamma_complex_1: "rGamma (1 :: complex) = 1"
proof -
  have A: "eventually (\<lambda>n. rGamma_series 1 n = of_nat (Suc n) / of_nat n) sequentially"
    using eventually_gt_at_top[of "0::nat"]
    by (force elim!: eventually_mono simp: rGamma_series_def exp_of_real pochhammer_fact
                    field_split_simps pochhammer_rec' dest!: pochhammer_eq_0_imp_nonpos_Int)
  have "rGamma_series 1 \<longlonglongrightarrow> 1" by (subst tendsto_cong[OF A]) (rule LIMSEQ_Suc_n_over_n)
  thus "rGamma 1 = (1 :: complex)" unfolding rGamma_complex_def by (rule limI)
qed

private lemma has_field_derivative_rGamma_complex_nonpos_Int:
  "(rGamma has_field_derivative (-1)^n * fact n) (at (- of_nat n :: complex))"
proof (induction n)
  case 0
  have A: "(0::complex) + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0" by simp
  have "((\<lambda>z. z * (rGamma \<circ> (\<lambda>z. z + 1 :: complex)) z) has_field_derivative 1) (at 0)"
    by (rule derivative_eq_intros DERIV_chain refl
             has_field_derivative_rGamma_complex_no_nonpos_Int A)+ (simp add: rGamma_complex_1)
    thus ?case by (simp add: rGamma_complex_plus1)
next
  case (Suc n)
  hence A: "(rGamma has_field_derivative (-1)^n * fact n)
                (at (- of_nat (Suc n) + 1 :: complex))" by simp
   have "((\<lambda>z. z * (rGamma \<circ> (\<lambda>z. z + 1 :: complex)) z) has_field_derivative
             (- 1) ^ Suc n * fact (Suc n)) (at (- of_nat (Suc n)))"
     by (rule derivative_eq_intros refl A DERIV_chain)+
        (simp add: algebra_simps rGamma_complex_altdef)
  thus ?case by (simp add: rGamma_complex_plus1)
qed

instance proof
  fix z :: complex show "(rGamma z = 0) \<longleftrightarrow> (\<exists>n. z = - of_nat n)"
    by (auto simp: rGamma_complex_altdef elim!: nonpos_Ints_cases')
next
  fix z :: complex assume "\<And>n. z \<noteq> - of_nat n"
  hence "z \<notin> \<int>\<^sub>\<le>\<^sub>0" by (auto elim!: nonpos_Ints_cases')
  from has_field_derivative_rGamma_complex_no_nonpos_Int[OF this]
    show "let d = (THE d. (\<lambda>n. \<Sum>k<n. inverse (of_nat (Suc k)) - inverse (z + of_nat k))
                       \<longlonglongrightarrow> d) - euler_mascheroni *\<^sub>R 1 in  (\<lambda>y. (rGamma y - rGamma z +
              rGamma z * d * (y - z)) /\<^sub>R  cmod (y - z)) \<midarrow>z\<rightarrow> 0"
      by (simp add: has_field_derivative_def has_derivative_def Digamma_def sums_def [abs_def]
                    of_real_def[symmetric] suminf_def)
next
  fix n :: nat
  from has_field_derivative_rGamma_complex_nonpos_Int[of n]
  show "let z = - of_nat n in (\<lambda>y. (rGamma y - rGamma z - (- 1) ^ n * prod of_nat {1..n} *
                  (y - z)) /\<^sub>R cmod (y - z)) \<midarrow>z\<rightarrow> 0"
    by (simp add: has_field_derivative_def has_derivative_def fact_prod Let_def)
next
  fix z :: complex
  from rGamma_series_complex_converges[of z] have "rGamma_series z \<longlonglongrightarrow> rGamma z"
    by (simp add: convergent_LIMSEQ_iff rGamma_complex_def)
  thus "let fact' = \<lambda>n. prod of_nat {1..n};
            exp = \<lambda>x. THE e. (\<lambda>n. \<Sum>k<n. x ^ k /\<^sub>R fact k) \<longlonglongrightarrow> e;
            pochhammer' = \<lambda>a n. \<Prod>n = 0..n. a + of_nat n
        in  (\<lambda>n. pochhammer' z n / (fact' n * exp (z * ln (real_of_nat n) *\<^sub>R 1))) \<longlonglongrightarrow> rGamma z"
    by (simp add: fact_prod pochhammer_Suc_prod rGamma_series_def [abs_def] exp_def
                  of_real_def [symmetric] suminf_def sums_def [abs_def] atLeast0AtMost)
qed

end
end


lemma Gamma_complex_altdef:
  "Gamma z = (if z \<in> \<int>\<^sub>\<le>\<^sub>0 then 0 else exp (ln_Gamma (z :: complex)))"
  unfolding Gamma_def rGamma_complex_altdef by (simp add: exp_minus)

lemma cnj_rGamma: "cnj (rGamma z) = rGamma (cnj z)"
proof -
  have "rGamma_series (cnj z) = (\<lambda>n. cnj (rGamma_series z n))"
    by (intro ext) (simp_all add: rGamma_series_def exp_cnj)
  also have "... \<longlonglongrightarrow> cnj (rGamma z)" by (intro tendsto_cnj tendsto_intros)
  finally show ?thesis unfolding rGamma_complex_def by (intro sym[OF limI])
qed

lemma cnj_Gamma: "cnj (Gamma z) = Gamma (cnj z)"
  unfolding Gamma_def by (simp add: cnj_rGamma)

lemma Gamma_complex_real:
  "z \<in> \<real> \<Longrightarrow> Gamma z \<in> (\<real> :: complex set)" and rGamma_complex_real: "z \<in> \<real> \<Longrightarrow> rGamma z \<in> \<real>"
  by (simp_all add: Reals_cnj_iff cnj_Gamma cnj_rGamma)

lemma field_differentiable_rGamma: "rGamma field_differentiable (at z within A)"
  using has_field_derivative_rGamma[of z] unfolding field_differentiable_def by blast

lemma holomorphic_rGamma [holomorphic_intros]: "rGamma holomorphic_on A"
  unfolding holomorphic_on_def by (auto intro!: field_differentiable_rGamma)

lemma holomorphic_rGamma' [holomorphic_intros]: 
  assumes "f holomorphic_on A"
  shows   "(\<lambda>x. rGamma (f x)) holomorphic_on A"
proof -
  have "rGamma \<circ> f holomorphic_on A" using assms
    by (intro holomorphic_on_compose assms holomorphic_rGamma)
  thus ?thesis by (simp only: o_def)
qed

lemma analytic_rGamma: "rGamma analytic_on A"
  unfolding analytic_on_def by (auto intro!: exI[of _ 1] holomorphic_rGamma)


lemma field_differentiable_Gamma: "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Gamma field_differentiable (at z within A)"
  using has_field_derivative_Gamma[of z] unfolding field_differentiable_def by auto

lemma holomorphic_Gamma [holomorphic_intros]: "A \<inter> \<int>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> Gamma holomorphic_on A"
  unfolding holomorphic_on_def by (auto intro!: field_differentiable_Gamma)

lemma holomorphic_Gamma' [holomorphic_intros]: 
  assumes "f holomorphic_on A" and "\<And>x. x \<in> A \<Longrightarrow> f x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma (f x)) holomorphic_on A"
proof -
  have "Gamma \<circ> f holomorphic_on A" using assms
    by (intro holomorphic_on_compose assms holomorphic_Gamma) auto
  thus ?thesis by (simp only: o_def)
qed

lemma analytic_Gamma: "A \<inter> \<int>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> Gamma analytic_on A"
  by (rule analytic_on_subset[of _ "UNIV - \<int>\<^sub>\<le>\<^sub>0"], subst analytic_on_open)
     (auto intro!: holomorphic_Gamma)


lemma field_differentiable_ln_Gamma_complex:
  "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> ln_Gamma field_differentiable (at (z::complex) within A)"
  by (rule field_differentiable_within_subset[of _ _ UNIV])
     (force simp: field_differentiable_def intro!: derivative_intros)+

lemma holomorphic_ln_Gamma [holomorphic_intros]: "A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> ln_Gamma holomorphic_on A"
  unfolding holomorphic_on_def by (auto intro!: field_differentiable_ln_Gamma_complex)

lemma analytic_ln_Gamma: "A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> ln_Gamma analytic_on A"
  by (rule analytic_on_subset[of _ "UNIV - \<real>\<^sub>\<le>\<^sub>0"], subst analytic_on_open)
     (auto intro!: holomorphic_ln_Gamma)


lemma has_field_derivative_rGamma_complex' [derivative_intros]:
  "(rGamma has_field_derivative (if z \<in> \<int>\<^sub>\<le>\<^sub>0 then (-1)^(nat \<lfloor>-Re z\<rfloor>) * fact (nat \<lfloor>-Re z\<rfloor>) else
        -rGamma z * Digamma z)) (at z within A)"
  using has_field_derivative_rGamma[of z] by (auto elim!: nonpos_Ints_cases')

declare has_field_derivative_rGamma_complex'[THEN DERIV_chain2, derivative_intros]


lemma field_differentiable_Polygamma:
  fixes z :: complex
  shows
  "z \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Polygamma n field_differentiable (at z within A)"
  using has_field_derivative_Polygamma[of z n] unfolding field_differentiable_def by auto

lemma holomorphic_on_Polygamma [holomorphic_intros]: "A \<inter> \<int>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> Polygamma n holomorphic_on A"
  unfolding holomorphic_on_def by (auto intro!: field_differentiable_Polygamma)

lemma analytic_on_Polygamma: "A \<inter> \<int>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> Polygamma n analytic_on A"
  by (rule analytic_on_subset[of _ "UNIV - \<int>\<^sub>\<le>\<^sub>0"], subst analytic_on_open)
     (auto intro!: holomorphic_on_Polygamma)



subsection\<^marker>\<open>tag unimportant\<close> \<open>The real Gamma function\<close>

lemma rGamma_series_real:
  "eventually (\<lambda>n. rGamma_series x n = Re (rGamma_series (of_real x) n)) sequentially"
  using eventually_gt_at_top[of "0 :: nat"]
proof eventually_elim
  fix n :: nat assume n: "n > 0"
  have "Re (rGamma_series (of_real x) n) =
          Re (of_real (pochhammer x (Suc n)) / (fact n * exp (of_real (x * ln (real_of_nat n)))))"
    using n by (simp add: rGamma_series_def powr_def pochhammer_of_real)
  also from n have "\<dots> = Re (of_real ((pochhammer x (Suc n)) /
                              (fact n * (exp (x * ln (real_of_nat n))))))"
    by (subst exp_of_real) simp
  also from n have "\<dots> = rGamma_series x n"
    by (subst Re_complex_of_real) (simp add: rGamma_series_def powr_def)
  finally show "rGamma_series x n = Re (rGamma_series (of_real x) n)" ..
qed

instantiation\<^marker>\<open>tag unimportant\<close> real :: Gamma
begin

definition "rGamma_real x = Re (rGamma (of_real x :: complex))"

instance proof
  fix x :: real
  have "rGamma x = Re (rGamma (of_real x))" by (simp add: rGamma_real_def)
  also have "of_real \<dots> = rGamma (of_real x :: complex)"
    by (intro of_real_Re rGamma_complex_real) simp_all
  also have "\<dots> = 0 \<longleftrightarrow> x \<in> \<int>\<^sub>\<le>\<^sub>0" by (simp add: rGamma_eq_zero_iff of_real_in_nonpos_Ints_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists>n. x = - of_nat n)" by (auto elim!: nonpos_Ints_cases')
  finally show "(rGamma x) = 0 \<longleftrightarrow> (\<exists>n. x = - real_of_nat n)" by simp
next
  fix x :: real assume "\<And>n. x \<noteq> - of_nat n"
  hence x: "complex_of_real x \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (subst of_real_in_nonpos_Ints_iff) (auto elim!: nonpos_Ints_cases')
  then have "x \<noteq> 0" by auto
  with x have "(rGamma has_field_derivative - rGamma x * Digamma x) (at x)"
    by (fastforce intro!: derivative_eq_intros has_vector_derivative_real_field
                  simp: Polygamma_of_real rGamma_real_def [abs_def])
  thus "let d = (THE d. (\<lambda>n. \<Sum>k<n. inverse (of_nat (Suc k)) - inverse (x + of_nat k))
                       \<longlonglongrightarrow> d) - euler_mascheroni *\<^sub>R 1 in  (\<lambda>y. (rGamma y - rGamma x +
              rGamma x * d * (y - x)) /\<^sub>R  norm (y - x)) \<midarrow>x\<rightarrow> 0"
      by (simp add: has_field_derivative_def has_derivative_def Digamma_def sums_def [abs_def]
                    of_real_def[symmetric] suminf_def)
next
  fix n :: nat
  have "(rGamma has_field_derivative (-1)^n * fact n) (at (- of_nat n :: real))"
    by (fastforce intro!: derivative_eq_intros has_vector_derivative_real_field
                  simp: Polygamma_of_real rGamma_real_def [abs_def])
  thus "let x = - of_nat n in (\<lambda>y. (rGamma y - rGamma x - (- 1) ^ n * prod of_nat {1..n} *
                  (y - x)) /\<^sub>R norm (y - x)) \<midarrow>x::real\<rightarrow> 0"
    by (simp add: has_field_derivative_def has_derivative_def fact_prod Let_def)
next
  fix x :: real
  have "rGamma_series x \<longlonglongrightarrow> rGamma x"
  proof (rule Lim_transform_eventually)
    show "(\<lambda>n. Re (rGamma_series (of_real x) n)) \<longlonglongrightarrow> rGamma x" unfolding rGamma_real_def
      by (intro tendsto_intros)
  qed (insert rGamma_series_real, simp add: eq_commute)
  thus "let fact' = \<lambda>n. prod of_nat {1..n};
            exp = \<lambda>x. THE e. (\<lambda>n. \<Sum>k<n. x ^ k /\<^sub>R fact k) \<longlonglongrightarrow> e;
            pochhammer' = \<lambda>a n. \<Prod>n = 0..n. a + of_nat n
        in  (\<lambda>n. pochhammer' x n / (fact' n * exp (x * ln (real_of_nat n) *\<^sub>R 1))) \<longlonglongrightarrow> rGamma x"
    by (simp add: fact_prod pochhammer_Suc_prod rGamma_series_def [abs_def] exp_def
                  of_real_def [symmetric] suminf_def sums_def [abs_def] atLeast0AtMost)
qed

end


lemma rGamma_complex_of_real: "rGamma (complex_of_real x) = complex_of_real (rGamma x)"
  unfolding rGamma_real_def using rGamma_complex_real by simp

lemma Gamma_complex_of_real: "Gamma (complex_of_real x) = complex_of_real (Gamma x)"
  unfolding Gamma_def by (simp add: rGamma_complex_of_real)

lemma rGamma_real_altdef: "rGamma x = lim (rGamma_series (x :: real))"
  by (rule sym, rule limI, rule tendsto_intros)

lemma Gamma_real_altdef1: "Gamma x = lim (Gamma_series (x :: real))"
  by (rule sym, rule limI, rule tendsto_intros)

lemma Gamma_real_altdef2: "Gamma x = Re (Gamma (of_real x))"
  using rGamma_complex_real[OF Reals_of_real[of x]]
  by (elim Reals_cases)
     (simp only: Gamma_def rGamma_real_def of_real_inverse[symmetric] Re_complex_of_real)

lemma ln_Gamma_series_complex_of_real:
  "x > 0 \<Longrightarrow> n > 0 \<Longrightarrow> ln_Gamma_series (complex_of_real x) n = of_real (ln_Gamma_series x n)"
proof -
  assume xn: "x > 0" "n > 0"
  have "Ln (complex_of_real x / of_nat k + 1) = of_real (ln (x / of_nat k + 1))" if "k \<ge> 1" for k
    using that xn by (subst Ln_of_real [symmetric]) (auto intro!: add_nonneg_pos simp: field_simps)
  with xn show ?thesis by (simp add: ln_Gamma_series_def Ln_of_real)
qed

lemma ln_Gamma_real_converges:
  assumes "(x::real) > 0"
  shows   "convergent (ln_Gamma_series x)"
proof -
  have "(\<lambda>n. ln_Gamma_series (complex_of_real x) n) \<longlonglongrightarrow> ln_Gamma (of_real x)" using assms
    by (intro ln_Gamma_complex_LIMSEQ) (auto simp: of_real_in_nonpos_Ints_iff)
  moreover from eventually_gt_at_top[of "0::nat"]
    have "eventually (\<lambda>n. complex_of_real (ln_Gamma_series x n) =
            ln_Gamma_series (complex_of_real x) n) sequentially"
    by eventually_elim (simp add: ln_Gamma_series_complex_of_real assms)
  ultimately have "(\<lambda>n. complex_of_real (ln_Gamma_series x n)) \<longlonglongrightarrow> ln_Gamma (of_real x)"
    by (subst tendsto_cong) assumption+
  from tendsto_Re[OF this] show ?thesis by (auto simp: convergent_def)
qed

lemma ln_Gamma_real_LIMSEQ: "(x::real) > 0 \<Longrightarrow> ln_Gamma_series x \<longlonglongrightarrow> ln_Gamma x"
  using ln_Gamma_real_converges[of x] unfolding ln_Gamma_def by (simp add: convergent_LIMSEQ_iff)

lemma ln_Gamma_complex_of_real: "x > 0 \<Longrightarrow> ln_Gamma (complex_of_real x) = of_real (ln_Gamma x)"
proof (unfold ln_Gamma_def, rule limI, rule Lim_transform_eventually)
  assume x: "x > 0"
  show "eventually (\<lambda>n. of_real (ln_Gamma_series x n) =
            ln_Gamma_series (complex_of_real x) n) sequentially"
    using eventually_gt_at_top[of "0::nat"]
    by eventually_elim (simp add: ln_Gamma_series_complex_of_real x)
qed (intro tendsto_of_real, insert ln_Gamma_real_LIMSEQ[of x], simp add: ln_Gamma_def)

lemma Gamma_real_pos_exp: "x > (0 :: real) \<Longrightarrow> Gamma x = exp (ln_Gamma x)"
  by (auto simp: Gamma_real_altdef2 Gamma_complex_altdef of_real_in_nonpos_Ints_iff
                 ln_Gamma_complex_of_real exp_of_real)

lemma ln_Gamma_real_pos: "x > 0 \<Longrightarrow> ln_Gamma x = ln (Gamma x :: real)"
  unfolding Gamma_real_pos_exp by simp

lemma ln_Gamma_complex_conv_fact: "n > 0 \<Longrightarrow> ln_Gamma (of_nat n :: complex) = ln (fact (n - 1))"
  using ln_Gamma_complex_of_real[of "real n"] Gamma_fact[of "n - 1", where 'a = real]
  by (simp add: ln_Gamma_real_pos of_nat_diff Ln_of_real [symmetric])

lemma ln_Gamma_real_conv_fact: "n > 0 \<Longrightarrow> ln_Gamma (real n) = ln (fact (n - 1))"
  using Gamma_fact[of "n - 1", where 'a = real]
  by (simp add: ln_Gamma_real_pos of_nat_diff Ln_of_real [symmetric])

lemma Gamma_real_pos [simp, intro]: "x > (0::real) \<Longrightarrow> Gamma x > 0"
  by (simp add: Gamma_real_pos_exp)

lemma Gamma_real_nonneg [simp, intro]: "x > (0::real) \<Longrightarrow> Gamma x \<ge> 0"
  by (simp add: Gamma_real_pos_exp)

lemma has_field_derivative_ln_Gamma_real [derivative_intros]:
  assumes x: "x > (0::real)"
  shows "(ln_Gamma has_field_derivative Digamma x) (at x)"
proof (subst DERIV_cong_ev[OF refl _ refl])
  from assms show "((Re \<circ> ln_Gamma \<circ> complex_of_real) has_field_derivative Digamma x) (at x)"
    by (auto intro!: derivative_eq_intros has_vector_derivative_real_field
             simp: Polygamma_of_real o_def)
  from eventually_nhds_in_nhd[of x "{0<..}"] assms
    show "eventually (\<lambda>y. ln_Gamma y = (Re \<circ> ln_Gamma \<circ> of_real) y) (nhds x)"
    by (auto elim!: eventually_mono simp: ln_Gamma_complex_of_real interior_open)
qed

lemma field_differentiable_ln_Gamma_real:
  "x > 0 \<Longrightarrow> ln_Gamma field_differentiable (at (x::real) within A)"
  by (rule field_differentiable_within_subset[of _ _ UNIV])
     (auto simp: field_differentiable_def intro!: derivative_intros)+

declare has_field_derivative_ln_Gamma_real[THEN DERIV_chain2, derivative_intros]

lemma deriv_ln_Gamma_real:
  assumes "z > 0"
  shows   "deriv ln_Gamma z = Digamma (z :: real)"
  by (intro DERIV_imp_deriv has_field_derivative_ln_Gamma_real assms)

lemma higher_deriv_ln_Gamma_real:
  assumes "(x::real) > 0"
  shows   "(deriv ^^ j) ln_Gamma x = (if j = 0 then ln_Gamma x else Polygamma (j - 1) x)"
proof (cases j)
  case (Suc j')
  have "(deriv ^^ j') (deriv ln_Gamma) x = (deriv ^^ j') Digamma x"
    using eventually_nhds_in_open[of "{0<..}" x] assms
    by (intro higher_deriv_cong_ev refl)
       (auto elim!: eventually_mono simp: open_Diff deriv_ln_Gamma_real)
  also have "\<dots> = Polygamma j' x" using assms
    by (subst higher_deriv_Polygamma)
       (auto elim!: nonpos_Ints_cases simp: complex_nonpos_Reals_iff)
  finally show ?thesis using Suc by (simp del: funpow.simps add: funpow_Suc_right)
qed simp_all
  
lemma higher_deriv_ln_Gamma_complex_of_real:
  assumes "(x :: real) > 0"
  shows   "(deriv ^^ j) ln_Gamma (complex_of_real x) = of_real ((deriv ^^ j) ln_Gamma x)"
    using assms
    by (auto simp: higher_deriv_ln_Gamma_real higher_deriv_ln_Gamma_complex
                   ln_Gamma_complex_of_real Polygamma_of_real)

lemma has_field_derivative_rGamma_real' [derivative_intros]:
  "(rGamma has_field_derivative (if x \<in> \<int>\<^sub>\<le>\<^sub>0 then (-1)^(nat \<lfloor>-x\<rfloor>) * fact (nat \<lfloor>-x\<rfloor>) else
        -rGamma x * Digamma x)) (at x within A)"
  using has_field_derivative_rGamma[of x] by (force elim!: nonpos_Ints_cases')

declare has_field_derivative_rGamma_real'[THEN DERIV_chain2, derivative_intros]

lemma Polygamma_real_odd_pos:
  assumes "(x::real) \<notin> \<int>\<^sub>\<le>\<^sub>0" "odd n"
  shows   "Polygamma n x > 0"
proof -
  from assms have "x \<noteq> 0" by auto
  with assms show ?thesis
    unfolding Polygamma_def using Polygamma_converges'[of x "Suc n"]
    by (auto simp: zero_less_power_eq simp del: power_Suc
             dest: plus_of_nat_eq_0_imp intro!: mult_pos_pos suminf_pos)
qed

lemma Polygamma_real_even_neg:
  assumes "(x::real) > 0" "n > 0" "even n"
  shows   "Polygamma n x < 0"
  using assms unfolding Polygamma_def using Polygamma_converges'[of x "Suc n"]
  by (auto intro!: mult_pos_pos suminf_pos)

lemma Polygamma_real_strict_mono:
  assumes "x > 0" "x < (y::real)" "even n"
  shows   "Polygamma n x < Polygamma n y"
proof -
  have "\<exists>\<xi>. x < \<xi> \<and> \<xi> < y \<and> Polygamma n y - Polygamma n x = (y - x) * Polygamma (Suc n) \<xi>"
    using assms by (intro MVT2 derivative_intros impI allI) (auto elim!: nonpos_Ints_cases)
  then guess \<xi> by (elim exE conjE) note \<xi> = this
  note \<xi>(3)
  also from \<xi>(1,2) assms have "(y - x) * Polygamma (Suc n) \<xi> > 0"
    by (intro mult_pos_pos Polygamma_real_odd_pos) (auto elim!: nonpos_Ints_cases)
  finally show ?thesis by simp
qed

lemma Polygamma_real_strict_antimono:
  assumes "x > 0" "x < (y::real)" "odd n"
  shows   "Polygamma n x > Polygamma n y"
proof -
  have "\<exists>\<xi>. x < \<xi> \<and> \<xi> < y \<and> Polygamma n y - Polygamma n x = (y - x) * Polygamma (Suc n) \<xi>"
    using assms by (intro MVT2 derivative_intros impI allI) (auto elim!: nonpos_Ints_cases)
  then guess \<xi> by (elim exE conjE) note \<xi> = this
  note \<xi>(3)
  also from \<xi>(1,2) assms have "(y - x) * Polygamma (Suc n) \<xi> < 0"
    by (intro mult_pos_neg Polygamma_real_even_neg) simp_all
  finally show ?thesis by simp
qed

lemma Polygamma_real_mono:
  assumes "x > 0" "x \<le> (y::real)" "even n"
  shows   "Polygamma n x \<le> Polygamma n y"
  using Polygamma_real_strict_mono[OF assms(1) _ assms(3), of y] assms(2)
  by (cases "x = y") simp_all

lemma Digamma_real_strict_mono: "(0::real) < x \<Longrightarrow> x < y \<Longrightarrow> Digamma x < Digamma y"
  by (rule Polygamma_real_strict_mono) simp_all

lemma Digamma_real_mono: "(0::real) < x \<Longrightarrow> x \<le> y \<Longrightarrow> Digamma x \<le> Digamma y"
  by (rule Polygamma_real_mono) simp_all

lemma Digamma_real_ge_three_halves_pos:
  assumes "x \<ge> 3/2"
  shows   "Digamma (x :: real) > 0"
proof -
  have "0 < Digamma (3/2 :: real)" by (fact Digamma_real_three_halves_pos)
  also from assms have "\<dots> \<le> Digamma x" by (intro Polygamma_real_mono) simp_all
  finally show ?thesis .
qed

lemma ln_Gamma_real_strict_mono:
  assumes "x \<ge> 3/2" "x < y"
  shows   "ln_Gamma (x :: real) < ln_Gamma y"
proof -
  have "\<exists>\<xi>. x < \<xi> \<and> \<xi> < y \<and> ln_Gamma y - ln_Gamma x = (y - x) * Digamma \<xi>"
    using assms by (intro MVT2 derivative_intros impI allI) (auto elim!: nonpos_Ints_cases)
  then guess \<xi> by (elim exE conjE) note \<xi> = this
  note \<xi>(3)
  also from \<xi>(1,2) assms have "(y - x) * Digamma \<xi> > 0"
    by (intro mult_pos_pos Digamma_real_ge_three_halves_pos) simp_all
  finally show ?thesis by simp
qed

lemma Gamma_real_strict_mono:
  assumes "x \<ge> 3/2" "x < y"
  shows   "Gamma (x :: real) < Gamma y"
proof -
  from Gamma_real_pos_exp[of x] assms have "Gamma x = exp (ln_Gamma x)" by simp
  also have "\<dots> < exp (ln_Gamma y)" by (intro exp_less_mono ln_Gamma_real_strict_mono assms)
  also from Gamma_real_pos_exp[of y] assms have "\<dots> = Gamma y" by simp
  finally show ?thesis .
qed

theorem log_convex_Gamma_real: "convex_on {0<..} (ln \<circ> Gamma :: real \<Rightarrow> real)"
  by (rule convex_on_realI[of _ _ Digamma])
     (auto intro!: derivative_eq_intros Polygamma_real_mono Gamma_real_pos
           simp: o_def Gamma_eq_zero_iff elim!: nonpos_Ints_cases')


subsection \<open>The uniqueness of the real Gamma function\<close>

text \<open>
  The following is a proof of the Bohr--Mollerup theorem, which states that
  any log-convex function \<open>G\<close> on the positive reals that fulfils \<open>G(1) = 1\<close> and
  satisfies the functional equation \<open>G(x + 1) = x G(x)\<close> must be equal to the
  Gamma function.
  In principle, if \<open>G\<close> is a holomorphic complex function, one could then extend
  this from the positive reals to the entire complex plane (minus the non-positive
  integers, where the Gamma function is not defined).
\<close>

context\<^marker>\<open>tag unimportant\<close>
  fixes G :: "real \<Rightarrow> real"
  assumes G_1: "G 1 = 1"
  assumes G_plus1: "x > 0 \<Longrightarrow> G (x + 1) = x * G x"
  assumes G_pos: "x > 0 \<Longrightarrow> G x > 0"
  assumes log_convex_G: "convex_on {0<..} (ln \<circ> G)"
begin

private lemma G_fact: "G (of_nat n + 1) = fact n"
  using G_plus1[of "real n + 1" for n]
  by (induction n) (simp_all add: G_1 G_plus1)

private definition S :: "real \<Rightarrow> real \<Rightarrow> real" where
  "S x y = (ln (G y) - ln (G x)) / (y - x)"

private lemma S_eq:
  "n \<ge> 2 \<Longrightarrow> S (of_nat n) (of_nat n + x) = (ln (G (real n + x)) - ln (fact (n - 1))) / x"
  by (subst G_fact [symmetric]) (simp add: S_def add_ac of_nat_diff)

private lemma G_lower:
  assumes x: "x > 0" and n: "n \<ge> 1"
  shows  "Gamma_series x n \<le> G x"
proof -
  have "(ln \<circ> G) (real (Suc n)) \<le> ((ln \<circ> G) (real (Suc n) + x) -
          (ln \<circ> G) (real (Suc n) - 1)) / (real (Suc n) + x - (real (Suc n) - 1)) *
           (real (Suc n) - (real (Suc n) - 1)) + (ln \<circ> G) (real (Suc n) - 1)"
    using x n by (intro convex_onD_Icc' convex_on_subset[OF log_convex_G]) auto
  hence "S (of_nat n) (of_nat (Suc n)) \<le> S (of_nat (Suc n)) (of_nat (Suc n) + x)"
    unfolding S_def using x by (simp add: field_simps)
  also have "S (of_nat n) (of_nat (Suc n)) = ln (fact n) - ln (fact (n-1))"
    unfolding S_def using n
    by (subst (1 2) G_fact [symmetric]) (simp_all add: add_ac of_nat_diff)
  also have "\<dots> = ln (fact n / fact (n-1))" by (subst ln_div) simp_all
  also from n have "fact n / fact (n - 1) = n" by (cases n) simp_all
  finally have "x * ln (real n) + ln (fact n) \<le> ln (G (real (Suc n) + x))"
    using x n by (subst (asm) S_eq) (simp_all add: field_simps)
  also have "x * ln (real n) + ln (fact n) = ln (exp (x * ln (real n)) * fact n)"
    using x by (simp add: ln_mult)
  finally have "exp (x * ln (real n)) * fact n \<le> G (real (Suc n) + x)" using x
    by (subst (asm) ln_le_cancel_iff) (simp_all add: G_pos)
  also have "G (real (Suc n) + x) = pochhammer x (Suc n) * G x"
    using G_plus1[of "real (Suc n) + x" for n] G_plus1[of x] x
    by (induction n) (simp_all add: pochhammer_Suc add_ac)
  finally show "Gamma_series x n \<le> G x"
    using x by (simp add: field_simps pochhammer_pos Gamma_series_def)
qed

private lemma G_upper:
  assumes x: "x > 0" "x \<le> 1" and n: "n \<ge> 2"
  shows  "G x \<le> Gamma_series x n * (1 + x / real n)"
proof -
  have "(ln \<circ> G) (real n + x) \<le> ((ln \<circ> G) (real n + 1) -
          (ln \<circ> G) (real n)) / (real n + 1 - (real n)) *
           ((real n + x) - real n) + (ln \<circ> G) (real n)"
    using x n by (intro convex_onD_Icc' convex_on_subset[OF log_convex_G]) auto
  hence "S (of_nat n) (of_nat n + x) \<le> S (of_nat n) (of_nat n + 1)"
    unfolding S_def using x by (simp add: field_simps)
  also from n have "S (of_nat n) (of_nat n + 1) = ln (fact n) - ln (fact (n-1))"
    by (subst (1 2) G_fact [symmetric]) (simp add: S_def add_ac of_nat_diff)
  also have "\<dots> = ln (fact n / (fact (n-1)))" using n by (subst ln_div) simp_all
  also from n have "fact n / fact (n - 1) = n" by (cases n) simp_all
  finally have "ln (G (real n + x)) \<le> x * ln (real n) + ln (fact (n - 1))"
    using x n by (subst (asm) S_eq) (simp_all add: field_simps)
  also have "\<dots> = ln (exp (x * ln (real n)) * fact (n - 1))" using x
    by (simp add: ln_mult)
  finally have "G (real n + x) \<le> exp (x * ln (real n)) * fact (n - 1)" using x
    by (subst (asm) ln_le_cancel_iff) (simp_all add: G_pos)
  also have "G (real n + x) = pochhammer x n * G x"
    using G_plus1[of "real n + x" for n] x
    by (induction n) (simp_all add: pochhammer_Suc add_ac)
  finally have "G x \<le> exp (x * ln (real n)) * fact (n- 1) / pochhammer x n"
    using x by (simp add: field_simps pochhammer_pos)
  also from n have "fact (n - 1) = fact n / n" by (cases n) simp_all
  also have "exp (x * ln (real n)) * \<dots> / pochhammer x n =
               Gamma_series x n * (1 + x / real n)" using n x
    by (simp add: Gamma_series_def divide_simps pochhammer_Suc)
  finally show ?thesis .
qed

private lemma G_eq_Gamma_aux:
  assumes x: "x > 0" "x \<le> 1"
  shows   "G x = Gamma x"
proof (rule antisym)
  show "G x \<ge> Gamma x"
  proof (rule tendsto_upperbound)
    from G_lower[of x] show "eventually (\<lambda>n. Gamma_series x n \<le> G x) sequentially"
      using  x by (auto intro: eventually_mono[OF eventually_ge_at_top[of "1::nat"]])
  qed (simp_all add: Gamma_series_LIMSEQ)
next
  show "G x \<le> Gamma x"
  proof (rule tendsto_lowerbound)
    have "(\<lambda>n. Gamma_series x n * (1 + x / real n)) \<longlonglongrightarrow> Gamma x * (1 + 0)"
      by (rule tendsto_intros real_tendsto_divide_at_top
               Gamma_series_LIMSEQ filterlim_real_sequentially)+
    thus "(\<lambda>n. Gamma_series x n * (1 + x / real n)) \<longlonglongrightarrow> Gamma x" by simp
  next
    from G_upper[of x] show "eventually (\<lambda>n. Gamma_series x n * (1 + x / real n) \<ge> G x) sequentially"
      using x by (auto intro: eventually_mono[OF eventually_ge_at_top[of "2::nat"]])
  qed simp_all
qed

theorem Gamma_pos_real_unique:
  assumes x: "x > 0"
  shows   "G x = Gamma x"
proof -
  have G_eq: "G (real n + x) = Gamma (real n + x)" if "x \<in> {0<..1}" for n x using that
  proof (induction n)
    case (Suc n)
    from Suc have "x + real n > 0" by simp
    hence "x + real n \<notin> \<int>\<^sub>\<le>\<^sub>0" by auto
    with Suc show ?case using G_plus1[of "real n + x"] Gamma_plus1[of "real n + x"]
      by (auto simp: add_ac)
  qed (simp_all add: G_eq_Gamma_aux)

  show ?thesis
  proof (cases "frac x = 0")
    case True
    hence "x = of_int (floor x)" by (simp add: frac_def)
    with x have x_eq: "x = of_nat (nat (floor x) - 1) + 1" by simp
    show ?thesis by (subst (1 2) x_eq, rule G_eq) simp_all
  next
    case False
    from assms have x_eq: "x = of_nat (nat (floor x)) + frac x"
      by (simp add: frac_def)
    have frac_le_1: "frac x \<le> 1" unfolding frac_def by linarith
    show ?thesis
      by (subst (1 2) x_eq, rule G_eq, insert False frac_le_1) simp_all
  qed
qed

end


subsection \<open>The Beta function\<close>

definition Beta where "Beta a b = Gamma a * Gamma b / Gamma (a + b)"

lemma Beta_altdef: "Beta a b = Gamma a * Gamma b * rGamma (a + b)"
  by (simp add: inverse_eq_divide Beta_def Gamma_def)

lemma Beta_commute: "Beta a b = Beta b a"
  unfolding Beta_def by (simp add: ac_simps)

lemma has_field_derivative_Beta1 [derivative_intros]:
  assumes "x \<notin> \<int>\<^sub>\<le>\<^sub>0" "x + y \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Beta x y) has_field_derivative (Beta x y * (Digamma x - Digamma (x + y))))
               (at x within A)" unfolding Beta_altdef
  by (rule DERIV_cong, (rule derivative_intros assms)+) (simp add: algebra_simps)

lemma Beta_pole1: "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Beta x y = 0"
  by (auto simp add: Beta_def elim!: nonpos_Ints_cases')

lemma Beta_pole2: "y \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Beta x y = 0"
  by (auto simp add: Beta_def elim!: nonpos_Ints_cases')

lemma Beta_zero: "x + y \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Beta x y = 0"
  by (auto simp add: Beta_def elim!: nonpos_Ints_cases')

lemma has_field_derivative_Beta2 [derivative_intros]:
  assumes "y \<notin> \<int>\<^sub>\<le>\<^sub>0" "x + y \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>y. Beta x y) has_field_derivative (Beta x y * (Digamma y - Digamma (x + y))))
               (at y within A)"
  using has_field_derivative_Beta1[of y x A] assms by (simp add: Beta_commute add_ac)

theorem Beta_plus1_plus1:
  assumes "x \<notin> \<int>\<^sub>\<le>\<^sub>0" "y \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "Beta (x + 1) y + Beta x (y + 1) = Beta x y"
proof -
  have "Beta (x + 1) y + Beta x (y + 1) =
            (Gamma (x + 1) * Gamma y + Gamma x * Gamma (y + 1)) * rGamma ((x + y) + 1)"
    by (simp add: Beta_altdef add_divide_distrib algebra_simps)
  also have "\<dots> = (Gamma x * Gamma y) * ((x + y) * rGamma ((x + y) + 1))"
    by (subst assms[THEN Gamma_plus1])+ (simp add: algebra_simps)
  also from assms have "\<dots> = Beta x y" unfolding Beta_altdef by (subst rGamma_plus1) simp
  finally show ?thesis .
qed

theorem Beta_plus1_left:
  assumes "x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(x + y) * Beta (x + 1) y = x * Beta x y"
proof -
  have "(x + y) * Beta (x + 1) y = Gamma (x + 1) * Gamma y * ((x + y) * rGamma ((x + y) + 1))"
    unfolding Beta_altdef by (simp only: ac_simps)
  also have "\<dots> = x * Beta x y" unfolding Beta_altdef
     by (subst assms[THEN Gamma_plus1] rGamma_plus1)+ (simp only: ac_simps)
  finally show ?thesis .
qed

theorem Beta_plus1_right:
  assumes "y \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(x + y) * Beta x (y + 1) = y * Beta x y"
  using Beta_plus1_left[of y x] assms by (simp_all add: Beta_commute add.commute)

lemma Gamma_Gamma_Beta:
  assumes "x + y \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "Gamma x * Gamma y = Beta x y * Gamma (x + y)"
  unfolding Beta_altdef using assms Gamma_eq_zero_iff[of "x+y"]
  by (simp add: rGamma_inverse_Gamma)



subsection \<open>Legendre duplication theorem\<close>

context
begin

private lemma Gamma_legendre_duplication_aux:
  fixes z :: "'a :: Gamma"
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0" "z + 1/2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows "Gamma z * Gamma (z + 1/2) = exp ((1 - 2*z) * of_real (ln 2)) * Gamma (1/2) * Gamma (2*z)"
proof -
  let ?powr = "\<lambda>b a. exp (a * of_real (ln (of_nat b)))"
  let ?h = "\<lambda>n. (fact (n-1))\<^sup>2 / fact (2*n-1) * of_nat (2^(2*n)) *
                exp (1/2 * of_real (ln (real_of_nat n)))"
  {
    fix z :: 'a assume z: "z \<notin> \<int>\<^sub>\<le>\<^sub>0" "z + 1/2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
    let ?g = "\<lambda>n. ?powr 2 (2*z) * Gamma_series' z n * Gamma_series' (z + 1/2) n /
                      Gamma_series' (2*z) (2*n)"
    have "eventually (\<lambda>n. ?g n = ?h n) sequentially" using eventually_gt_at_top
    proof eventually_elim
      fix n :: nat assume n: "n > 0"
      let ?f = "fact (n - 1) :: 'a" and ?f' = "fact (2*n - 1) :: 'a"
      have A: "exp t * exp t = exp (2*t :: 'a)" for t by (subst exp_add [symmetric]) simp
      have A: "Gamma_series' z n * Gamma_series' (z + 1/2) n = ?f^2 * ?powr n (2*z + 1/2) /
                (pochhammer z n * pochhammer (z + 1/2) n)"
        by (simp add: Gamma_series'_def exp_add ring_distribs power2_eq_square A mult_ac)
      have B: "Gamma_series' (2*z) (2*n) =
                       ?f' * ?powr 2 (2*z) * ?powr n (2*z) /
                       (of_nat (2^(2*n)) * pochhammer z n * pochhammer (z+1/2) n)" using n
        by (simp add: Gamma_series'_def ln_mult exp_add ring_distribs pochhammer_double)
      from z have "pochhammer z n \<noteq> 0" by (auto dest: pochhammer_eq_0_imp_nonpos_Int)
      moreover from z have "pochhammer (z + 1/2) n \<noteq> 0" by (auto dest: pochhammer_eq_0_imp_nonpos_Int)
      ultimately have "?powr 2 (2*z) * (Gamma_series' z n * Gamma_series' (z + 1/2) n) / Gamma_series' (2*z) (2*n) =
         ?f^2 / ?f' * of_nat (2^(2*n)) * (?powr n ((4*z + 1)/2) * ?powr n (-2*z))"
        using n unfolding A B by (simp add: field_split_simps exp_minus)
      also have "?powr n ((4*z + 1)/2) * ?powr n (-2*z) = ?powr n (1/2)"
        by (simp add: algebra_simps exp_add[symmetric] add_divide_distrib)
      finally show "?g n = ?h n" by (simp only: mult_ac)
    qed

    moreover from z double_in_nonpos_Ints_imp[of z] have "2 * z \<notin> \<int>\<^sub>\<le>\<^sub>0" by auto
    hence "?g \<longlonglongrightarrow> ?powr 2 (2*z) * Gamma z * Gamma (z+1/2) / Gamma (2*z)"
      using LIMSEQ_subseq_LIMSEQ[OF Gamma_series'_LIMSEQ, of "(*)2" "2*z"]
      by (intro tendsto_intros Gamma_series'_LIMSEQ)
         (simp_all add: o_def strict_mono_def Gamma_eq_zero_iff)
    ultimately have "?h \<longlonglongrightarrow> ?powr 2 (2*z) * Gamma z * Gamma (z+1/2) / Gamma (2*z)"
      by (blast intro: Lim_transform_eventually)
  } note lim = this

  from assms double_in_nonpos_Ints_imp[of z] have z': "2 * z \<notin> \<int>\<^sub>\<le>\<^sub>0" by auto
  from fraction_not_in_ints[of 2 1] have "(1/2 :: 'a) \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (intro not_in_Ints_imp_not_in_nonpos_Ints) simp_all
  with lim[of "1/2 :: 'a"] have "?h \<longlonglongrightarrow> 2 * Gamma (1/2 :: 'a)" by (simp add: exp_of_real)
  from LIMSEQ_unique[OF this lim[OF assms]] z' show ?thesis
    by (simp add: field_split_simps Gamma_eq_zero_iff ring_distribs exp_diff exp_of_real)
qed

text \<open>
  The following lemma is somewhat annoying. With a little bit of complex analysis
  (Cauchy's integral theorem, to be exact), this would be completely trivial. However,
  we want to avoid depending on the complex analysis session at this point, so we prove it
  the hard way.
\<close>
private lemma Gamma_reflection_aux:
  defines "h \<equiv> \<lambda>z::complex. if z \<in> \<int> then 0 else
                 (of_real pi * cot (of_real pi*z) + Digamma z - Digamma (1 - z))"
  defines "a \<equiv> complex_of_real pi"
  obtains h' where "continuous_on UNIV h'" "\<And>z. (h has_field_derivative (h' z)) (at z)"
proof -
  define f where "f n = a * of_real (cos_coeff (n+1) - sin_coeff (n+2))" for n
  define F where "F z = (if z = 0 then 0 else (cos (a*z) - sin (a*z)/(a*z)) / z)" for z
  define g where "g n = complex_of_real (sin_coeff (n+1))" for n
  define G where "G z = (if z = 0 then 1 else sin (a*z)/(a*z))" for z
  have a_nz: "a \<noteq> 0" unfolding a_def by simp

  have "(\<lambda>n. f n * (a*z)^n) sums (F z) \<and> (\<lambda>n. g n * (a*z)^n) sums (G z)"
    if "abs (Re z) < 1" for z
  proof (cases "z = 0"; rule conjI)
    assume "z \<noteq> 0"
    note z = this that

    from z have sin_nz: "sin (a*z) \<noteq> 0" unfolding a_def by (auto simp: sin_eq_0)
    have "(\<lambda>n. of_real (sin_coeff n) * (a*z)^n) sums (sin (a*z))" using sin_converges[of "a*z"]
      by (simp add: scaleR_conv_of_real)
    from sums_split_initial_segment[OF this, of 1]
      have "(\<lambda>n. (a*z) * of_real (sin_coeff (n+1)) * (a*z)^n) sums (sin (a*z))" by (simp add: mult_ac)
    from sums_mult[OF this, of "inverse (a*z)"] z a_nz
      have A: "(\<lambda>n. g n * (a*z)^n) sums (sin (a*z)/(a*z))"
      by (simp add: field_simps g_def)
    with z show "(\<lambda>n. g n * (a*z)^n) sums (G z)" by (simp add: G_def)
    from A z a_nz sin_nz have g_nz: "(\<Sum>n. g n * (a*z)^n) \<noteq> 0" by (simp add: sums_iff g_def)

    have [simp]: "sin_coeff (Suc 0) = 1" by (simp add: sin_coeff_def)
    from sums_split_initial_segment[OF sums_diff[OF cos_converges[of "a*z"] A], of 1]
    have "(\<lambda>n. z * f n * (a*z)^n) sums (cos (a*z) - sin (a*z) / (a*z))"
      by (simp add: mult_ac scaleR_conv_of_real ring_distribs f_def g_def)
    from sums_mult[OF this, of "inverse z"] z assms
      show "(\<lambda>n. f n * (a*z)^n) sums (F z)" by (simp add: divide_simps mult_ac f_def F_def)
  next
    assume z: "z = 0"
    have "(\<lambda>n. f n * (a * z) ^ n) sums f 0" using powser_sums_zero[of f] z by simp
    with z show "(\<lambda>n. f n * (a * z) ^ n) sums (F z)"
      by (simp add: f_def F_def sin_coeff_def cos_coeff_def)
    have "(\<lambda>n. g n * (a * z) ^ n) sums g 0" using powser_sums_zero[of g] z by simp
    with z show "(\<lambda>n. g n * (a * z) ^ n) sums (G z)"
      by (simp add: g_def G_def sin_coeff_def cos_coeff_def)
  qed
  note sums = conjunct1[OF this] conjunct2[OF this]

  define h2 where [abs_def]:
    "h2 z = (\<Sum>n. f n * (a*z)^n) / (\<Sum>n. g n * (a*z)^n) + Digamma (1 + z) - Digamma (1 - z)" for z
  define POWSER where [abs_def]: "POWSER f z = (\<Sum>n. f n * (z^n :: complex))" for f z
  define POWSER' where [abs_def]: "POWSER' f z = (\<Sum>n. diffs f n * (z^n))" for f and z :: complex
  define h2' where [abs_def]:
    "h2' z = a * (POWSER g (a*z) * POWSER' f (a*z) - POWSER f (a*z) * POWSER' g (a*z)) /
      (POWSER g (a*z))^2 + Polygamma 1 (1 + z) + Polygamma 1 (1 - z)" for z

  have h_eq: "h t = h2 t" if "abs (Re t) < 1" for t
  proof -
    from that have t: "t \<in> \<int> \<longleftrightarrow> t = 0" by (auto elim!: Ints_cases)
    hence "h t = a*cot (a*t) - 1/t + Digamma (1 + t) - Digamma (1 - t)"
      unfolding h_def using Digamma_plus1[of t] by (force simp: field_simps a_def)
    also have "a*cot (a*t) - 1/t = (F t) / (G t)"
      using t by (auto simp add: divide_simps sin_eq_0 cot_def a_def F_def G_def)
    also have "\<dots> = (\<Sum>n. f n * (a*t)^n) / (\<Sum>n. g n * (a*t)^n)"
      using sums[of t] that by (simp add: sums_iff)
    finally show "h t = h2 t" by (simp only: h2_def)
  qed

  let ?A = "{z. abs (Re z) < 1}"
  have "open ({z. Re z < 1} \<inter> {z. Re z > -1})"
    using open_halfspace_Re_gt open_halfspace_Re_lt by auto
  also have "({z. Re z < 1} \<inter> {z. Re z > -1}) = {z. abs (Re z) < 1}" by auto
  finally have open_A: "open ?A" .
  hence [simp]: "interior ?A = ?A" by (simp add: interior_open)

  have summable_f: "summable (\<lambda>n. f n * z^n)" for z
    by (rule powser_inside, rule sums_summable, rule sums[of "\<i> * of_real (norm z + 1) / a"])
       (simp_all add: norm_mult a_def del: of_real_add)
  have summable_g: "summable (\<lambda>n. g n * z^n)" for z
    by (rule powser_inside, rule sums_summable, rule sums[of "\<i> * of_real (norm z + 1) / a"])
       (simp_all add: norm_mult a_def del: of_real_add)
  have summable_fg': "summable (\<lambda>n. diffs f n * z^n)" "summable (\<lambda>n. diffs g n * z^n)" for z
    by (intro termdiff_converges_all summable_f summable_g)+
  have "(POWSER f has_field_derivative (POWSER' f z)) (at z)"
               "(POWSER g has_field_derivative (POWSER' g z)) (at z)" for z
    unfolding POWSER_def POWSER'_def
    by (intro termdiffs_strong_converges_everywhere summable_f summable_g)+
  note derivs = this[THEN DERIV_chain2[OF _ DERIV_cmult[OF DERIV_ident]], unfolded POWSER_def]
  have "isCont (POWSER f) z" "isCont (POWSER g) z" "isCont (POWSER' f) z" "isCont (POWSER' g) z"
    for z unfolding POWSER_def POWSER'_def
    by (intro isCont_powser_converges_everywhere summable_f summable_g summable_fg')+
  note cont = this[THEN isCont_o2[rotated], unfolded POWSER_def POWSER'_def]

  {
    fix z :: complex assume z: "abs (Re z) < 1"
    define d where "d = \<i> * of_real (norm z + 1)"
    have d: "abs (Re d) < 1" "norm z < norm d" by (simp_all add: d_def norm_mult del: of_real_add)
    have "eventually (\<lambda>z. h z = h2 z) (nhds z)"
      using eventually_nhds_in_nhd[of z ?A] using h_eq z
      by (auto elim!: eventually_mono)

    moreover from sums(2)[OF z] z have nz: "(\<Sum>n. g n * (a * z) ^ n) \<noteq> 0"
      unfolding G_def by (auto simp: sums_iff sin_eq_0 a_def)
    have A: "z \<in> \<int> \<longleftrightarrow> z = 0" using z by (auto elim!: Ints_cases)
    have no_int: "1 + z \<in> \<int> \<longleftrightarrow> z = 0" using z Ints_diff[of "1+z" 1] A
      by (auto elim!: nonpos_Ints_cases)
    have no_int': "1 - z \<in> \<int> \<longleftrightarrow> z = 0" using z Ints_diff[of 1 "1-z"] A
      by (auto elim!: nonpos_Ints_cases)
    from no_int no_int' have no_int: "1 - z \<notin> \<int>\<^sub>\<le>\<^sub>0" "1 + z \<notin> \<int>\<^sub>\<le>\<^sub>0" by auto
    have "(h2 has_field_derivative h2' z) (at z)" unfolding h2_def
      by (rule DERIV_cong, (rule derivative_intros refl derivs[unfolded POWSER_def] nz no_int)+)
         (auto simp: h2'_def POWSER_def field_simps power2_eq_square)
    ultimately have deriv: "(h has_field_derivative h2' z) (at z)"
      by (subst DERIV_cong_ev[OF refl _ refl])

    from sums(2)[OF z] z have "(\<Sum>n. g n * (a * z) ^ n) \<noteq> 0"
      unfolding G_def by (auto simp: sums_iff a_def sin_eq_0)
    hence "isCont h2' z" using no_int unfolding h2'_def[abs_def] POWSER_def POWSER'_def
      by (intro continuous_intros cont
            continuous_on_compose2[OF _ continuous_on_Polygamma[of "{z. Re z > 0}"]]) auto
    note deriv and this
  } note A = this

  interpret h: periodic_fun_simple' h
  proof
    fix z :: complex
    show "h (z + 1) = h z"
    proof (cases "z \<in> \<int>")
      assume z: "z \<notin> \<int>"
      hence A: "z + 1 \<notin> \<int>" "z \<noteq> 0" using Ints_diff[of "z+1" 1] by auto
      hence "Digamma (z + 1) - Digamma (-z) = Digamma z - Digamma (-z + 1)"
        by (subst (1 2) Digamma_plus1) simp_all
      with A z show "h (z + 1) = h z"
        by (simp add: h_def sin_plus_pi cos_plus_pi ring_distribs cot_def)
    qed (simp add: h_def)
  qed

  have h2'_eq: "h2' (z - 1) = h2' z" if z: "Re z > 0" "Re z < 1" for z
  proof -
    have "((\<lambda>z. h (z - 1)) has_field_derivative h2' (z - 1)) (at z)"
      by (rule DERIV_cong, rule DERIV_chain'[OF _ A(1)])
         (insert z, auto intro!: derivative_eq_intros)
    hence "(h has_field_derivative h2' (z - 1)) (at z)" by (subst (asm) h.minus_1)
    moreover from z have "(h has_field_derivative h2' z) (at z)" by (intro A) simp_all
    ultimately show "h2' (z - 1) = h2' z" by (rule DERIV_unique)
  qed

  define h2'' where "h2'' z = h2' (z - of_int \<lfloor>Re z\<rfloor>)" for z
  have deriv: "(h has_field_derivative h2'' z) (at z)" for z
  proof -
    fix z :: complex
    have B: "\<bar>Re z - real_of_int \<lfloor>Re z\<rfloor>\<bar> < 1" by linarith
    have "((\<lambda>t. h (t - of_int \<lfloor>Re z\<rfloor>)) has_field_derivative h2'' z) (at z)"
      unfolding h2''_def by (rule DERIV_cong, rule DERIV_chain'[OF _ A(1)])
                            (insert B, auto intro!: derivative_intros)
    thus "(h has_field_derivative h2'' z) (at z)" by (simp add: h.minus_of_int)
  qed

  have cont: "continuous_on UNIV h2''"
  proof (intro continuous_at_imp_continuous_on ballI)
    fix z :: complex
    define r where "r = \<lfloor>Re z\<rfloor>"
    define A where "A = {t. of_int r - 1 < Re t \<and> Re t < of_int r + 1}"
    have "continuous_on A (\<lambda>t. h2' (t - of_int r))" unfolding A_def
      by (intro continuous_at_imp_continuous_on isCont_o2[OF _ A(2)] ballI continuous_intros)
         (simp_all add: abs_real_def)
    moreover have "h2'' t = h2' (t - of_int r)" if t: "t \<in> A" for t
    proof (cases "Re t \<ge> of_int r")
      case True
      from t have "of_int r - 1 < Re t" "Re t < of_int r + 1" by (simp_all add: A_def)
      with True have "\<lfloor>Re t\<rfloor> = \<lfloor>Re z\<rfloor>" unfolding r_def by linarith
      thus ?thesis by (auto simp: r_def h2''_def)
    next
      case False
      from t have t: "of_int r - 1 < Re t" "Re t < of_int r + 1" by (simp_all add: A_def)
      with False have t': "\<lfloor>Re t\<rfloor> = \<lfloor>Re z\<rfloor> - 1" unfolding r_def by linarith
      moreover from t False have "h2' (t - of_int r + 1 - 1) = h2' (t - of_int r + 1)"
        by (intro h2'_eq) simp_all
      ultimately show ?thesis by (auto simp: r_def h2''_def algebra_simps t')
    qed
    ultimately have "continuous_on A h2''" by (subst continuous_on_cong[OF refl])
    moreover {
      have "open ({t. of_int r - 1 < Re t} \<inter> {t. of_int r + 1 > Re t})"
        by (intro open_Int open_halfspace_Re_gt open_halfspace_Re_lt)
      also have "{t. of_int r - 1 < Re t} \<inter> {t. of_int r + 1 > Re t} = A"
        unfolding A_def by blast
      finally have "open A" .
    }
    ultimately have C: "isCont h2'' t" if "t \<in> A" for t using that
      by (subst (asm) continuous_on_eq_continuous_at) auto
    have "of_int r - 1 < Re z" "Re z  < of_int r + 1" unfolding r_def by linarith+
    thus "isCont h2'' z" by (intro C) (simp_all add: A_def)
  qed

  from that[OF cont deriv] show ?thesis .
qed

lemma Gamma_reflection_complex:
  fixes z :: complex
  shows "Gamma z * Gamma (1 - z) = of_real pi / sin (of_real pi * z)"
proof -
  let ?g = "\<lambda>z::complex. Gamma z * Gamma (1 - z) * sin (of_real pi * z)"
  define g where [abs_def]: "g z = (if z \<in> \<int> then of_real pi else ?g z)" for z :: complex
  let ?h = "\<lambda>z::complex. (of_real pi * cot (of_real pi*z) + Digamma z - Digamma (1 - z))"
  define h where [abs_def]: "h z = (if z \<in> \<int> then 0 else ?h z)" for z :: complex

  \<comment> \<open>@{term g} is periodic with period 1.\<close>
  interpret g: periodic_fun_simple' g
  proof
    fix z :: complex
    show "g (z + 1) = g z"
    proof (cases "z \<in> \<int>")
      case False
      hence "z * g z = z * Beta z (- z + 1) * sin (of_real pi * z)" by (simp add: g_def Beta_def)
      also have "z * Beta z (- z + 1) = (z + 1 + -z) * Beta (z + 1) (- z + 1)"
        using False Ints_diff[of 1 "1 - z"] nonpos_Ints_subset_Ints
        by (subst Beta_plus1_left [symmetric]) auto
      also have "\<dots> * sin (of_real pi * z) = z * (Beta (z + 1) (-z) * sin (of_real pi * (z + 1)))"
        using False Ints_diff[of "z+1" 1] Ints_minus[of "-z"] nonpos_Ints_subset_Ints
        by (subst Beta_plus1_right) (auto simp: ring_distribs sin_plus_pi)
      also from False have "Beta (z + 1) (-z) * sin (of_real pi * (z + 1)) = g (z + 1)"
        using Ints_diff[of "z+1" 1] by (auto simp: g_def Beta_def)
      finally show "g (z + 1) = g z" using False by (subst (asm) mult_left_cancel) auto
    qed (simp add: g_def)
  qed

  \<comment> \<open>@{term g} is entire.\<close>
  have g_g': "(g has_field_derivative (h z * g z)) (at z)" for z :: complex
  proof (cases "z \<in> \<int>")
    let ?h' = "\<lambda>z. Beta z (1 - z) * ((Digamma z - Digamma (1 - z)) * sin (z * of_real pi) +
                     of_real pi * cos (z * of_real pi))"
    case False
    from False have "eventually (\<lambda>t. t \<in> UNIV - \<int>) (nhds z)"
      by (intro eventually_nhds_in_open) (auto simp: open_Diff)
    hence "eventually (\<lambda>t. g t = ?g t) (nhds z)" by eventually_elim (simp add: g_def)
    moreover {
      from False Ints_diff[of 1 "1-z"] have "1 - z \<notin> \<int>" by auto
      hence "(?g has_field_derivative ?h' z) (at z)" using nonpos_Ints_subset_Ints
        by (auto intro!: derivative_eq_intros simp: algebra_simps Beta_def)
      also from False have "sin (of_real pi * z) \<noteq> 0" by (subst sin_eq_0) auto
      hence "?h' z = h z * g z"
        using False unfolding g_def h_def cot_def by (simp add: field_simps Beta_def)
      finally have "(?g has_field_derivative (h z * g z)) (at z)" .
    }
    ultimately show ?thesis by (subst DERIV_cong_ev[OF refl _ refl])
  next
    case True
    then obtain n where z: "z = of_int n" by (auto elim!: Ints_cases)
    let ?t = "(\<lambda>z::complex. if z = 0 then 1 else sin z / z) \<circ> (\<lambda>z. of_real pi * z)"
    have deriv_0: "(g has_field_derivative 0) (at 0)"
    proof (subst DERIV_cong_ev[OF refl _ refl])
      show "eventually (\<lambda>z. g z = of_real pi * Gamma (1 + z) * Gamma (1 - z) * ?t z) (nhds 0)"
        using eventually_nhds_ball[OF zero_less_one, of "0::complex"]
      proof eventually_elim
        fix z :: complex assume z: "z \<in> ball 0 1"
        show "g z = of_real pi * Gamma (1 + z) * Gamma (1 - z) * ?t z"
        proof (cases "z = 0")
          assume z': "z \<noteq> 0"
          with z have z'': "z \<notin> \<int>\<^sub>\<le>\<^sub>0" "z \<notin> \<int>" by (auto elim!: Ints_cases)
          from Gamma_plus1[OF this(1)] have "Gamma z = Gamma (z + 1) / z" by simp
          with z'' z' show ?thesis by (simp add: g_def ac_simps)
        qed (simp add: g_def)
      qed
      have "(?t has_field_derivative (0 * of_real pi)) (at 0)"
        using has_field_derivative_sin_z_over_z[of "UNIV :: complex set"]
        by (intro DERIV_chain) simp_all
      thus "((\<lambda>z. of_real pi * Gamma (1 + z) * Gamma (1 - z) * ?t z) has_field_derivative 0) (at 0)"
        by (auto intro!: derivative_eq_intros simp: o_def)
    qed

    have "((g \<circ> (\<lambda>x. x - of_int n)) has_field_derivative 0 * 1) (at (of_int n))"
      using deriv_0 by (intro DERIV_chain) (auto intro!: derivative_eq_intros)
    also have "g \<circ> (\<lambda>x. x - of_int n) = g" by (intro ext) (simp add: g.minus_of_int)
    finally show "(g has_field_derivative (h z * g z)) (at z)" by (simp add: z h_def)
  qed

  have g_eq: "g (z/2) * g ((z+1)/2) = Gamma (1/2)^2 * g z" if "Re z > -1" "Re z < 2" for z
  proof (cases "z \<in> \<int>")
    case True
    with that have "z = 0 \<or> z = 1" by (force elim!: Ints_cases)
    moreover have "g 0 * g (1/2) = Gamma (1/2)^2 * g 0"
      using fraction_not_in_ints[where 'a = complex, of 2 1] by (simp add: g_def power2_eq_square)
    moreover have "g (1/2) * g 1 = Gamma (1/2)^2 * g 1"
        using fraction_not_in_ints[where 'a = complex, of 2 1]
        by (simp add: g_def power2_eq_square Beta_def algebra_simps)
    ultimately show ?thesis by force
  next
    case False
    hence z: "z/2 \<notin> \<int>" "(z+1)/2 \<notin> \<int>" using Ints_diff[of "z+1" 1] by (auto elim!: Ints_cases)
    hence z': "z/2 \<notin> \<int>\<^sub>\<le>\<^sub>0" "(z+1)/2 \<notin> \<int>\<^sub>\<le>\<^sub>0" by (auto elim!: nonpos_Ints_cases)
    from z have "1-z/2 \<notin> \<int>" "1-((z+1)/2) \<notin> \<int>"
      using Ints_diff[of 1 "1-z/2"] Ints_diff[of 1 "1-((z+1)/2)"] by auto
    hence z'': "1-z/2 \<notin> \<int>\<^sub>\<le>\<^sub>0" "1-((z+1)/2) \<notin> \<int>\<^sub>\<le>\<^sub>0" by (auto elim!: nonpos_Ints_cases)
    from z have "g (z/2) * g ((z+1)/2) =
      (Gamma (z/2) * Gamma ((z+1)/2)) * (Gamma (1-z/2) * Gamma (1-((z+1)/2))) *
      (sin (of_real pi * z/2) * sin (of_real pi * (z+1)/2))"
      by (simp add: g_def)
    also from z' Gamma_legendre_duplication_aux[of "z/2"]
      have "Gamma (z/2) * Gamma ((z+1)/2) = exp ((1-z) * of_real (ln 2)) * Gamma (1/2) * Gamma z"
      by (simp add: add_divide_distrib)
    also from z'' Gamma_legendre_duplication_aux[of "1-(z+1)/2"]
      have "Gamma (1-z/2) * Gamma (1-(z+1)/2) =
              Gamma (1-z) * Gamma (1/2) * exp (z * of_real (ln 2))"
      by (simp add: add_divide_distrib ac_simps)
    finally have "g (z/2) * g ((z+1)/2) = Gamma (1/2)^2 * (Gamma z * Gamma (1-z) *
                    (2 * (sin (of_real pi*z/2) * sin (of_real pi*(z+1)/2))))"
      by (simp add: add_ac power2_eq_square exp_add ring_distribs exp_diff exp_of_real)
    also have "sin (of_real pi*(z+1)/2) = cos (of_real pi*z/2)"
      using cos_sin_eq[of "- of_real pi * z/2", symmetric]
      by (simp add: ring_distribs add_divide_distrib ac_simps)
    also have "2 * (sin (of_real pi*z/2) * cos (of_real pi*z/2)) = sin (of_real pi * z)"
      by (subst sin_times_cos) (simp add: field_simps)
    also have "Gamma z * Gamma (1 - z) * sin (complex_of_real pi * z) = g z"
      using \<open>z \<notin> \<int>\<close> by (simp add: g_def)
    finally show ?thesis .
  qed
  have g_eq: "g (z/2) * g ((z+1)/2) = Gamma (1/2)^2 * g z" for z
  proof -
    define r where "r = \<lfloor>Re z / 2\<rfloor>"
    have "Gamma (1/2)^2 * g z = Gamma (1/2)^2 * g (z - of_int (2*r))" by (simp only: g.minus_of_int)
    also have "of_int (2*r) = 2 * of_int r" by simp
    also have "Re z - 2 * of_int r > -1" "Re z - 2 * of_int r < 2" unfolding r_def by linarith+
    hence "Gamma (1/2)^2 * g (z - 2 * of_int r) =
                   g ((z - 2 * of_int r)/2) * g ((z - 2 * of_int r + 1)/2)"
      unfolding r_def by (intro g_eq[symmetric]) simp_all
    also have "(z - 2 * of_int r) / 2 = z/2 - of_int r" by simp
    also have "g \<dots> = g (z/2)" by (rule g.minus_of_int)
    also have "(z - 2 * of_int r + 1) / 2 = (z + 1)/2 - of_int r" by simp
    also have "g \<dots> = g ((z+1)/2)" by (rule g.minus_of_int)
    finally show ?thesis ..
  qed

  have g_nz [simp]: "g z \<noteq> 0" for z :: complex
  unfolding g_def using Ints_diff[of 1 "1 - z"]
    by (auto simp: Gamma_eq_zero_iff sin_eq_0 dest!: nonpos_Ints_Int)

  have h_eq: "h z = (h (z/2) + h ((z+1)/2)) / 2" for z
  proof -
    have "((\<lambda>t. g (t/2) * g ((t+1)/2)) has_field_derivative
                       (g (z/2) * g ((z+1)/2)) * ((h (z/2) + h ((z+1)/2)) / 2)) (at z)"
      by (auto intro!: derivative_eq_intros g_g'[THEN DERIV_chain2] simp: field_simps)
    hence "((\<lambda>t. Gamma (1/2)^2 * g t) has_field_derivative
              Gamma (1/2)^2 * g z * ((h (z/2) + h ((z+1)/2)) / 2)) (at z)"
      by (subst (1 2) g_eq[symmetric]) simp
    from DERIV_cmult[OF this, of "inverse ((Gamma (1/2))^2)"]
      have "(g has_field_derivative (g z * ((h (z/2) + h ((z+1)/2))/2))) (at z)"
      using fraction_not_in_ints[where 'a = complex, of 2 1]
      by (simp add: divide_simps Gamma_eq_zero_iff not_in_Ints_imp_not_in_nonpos_Ints)
    moreover have "(g has_field_derivative (g z * h z)) (at z)"
      using g_g'[of z] by (simp add: ac_simps)
    ultimately have "g z * h z = g z * ((h (z/2) + h ((z+1)/2))/2)"
      by (intro DERIV_unique)
    thus "h z = (h (z/2) + h ((z+1)/2)) / 2" by simp
  qed

  obtain h' where h'_cont: "continuous_on UNIV h'" and
                  h_h': "\<And>z. (h has_field_derivative h' z) (at z)"
     unfolding h_def by (erule Gamma_reflection_aux)

  have h'_eq: "h' z = (h' (z/2) + h' ((z+1)/2)) / 4" for z
  proof -
    have "((\<lambda>t. (h (t/2) + h ((t+1)/2)) / 2) has_field_derivative
                       ((h' (z/2) + h' ((z+1)/2)) / 4)) (at z)"
      by (fastforce intro!: derivative_eq_intros h_h'[THEN DERIV_chain2])
    hence "(h has_field_derivative ((h' (z/2) + h' ((z+1)/2))/4)) (at z)"
      by (subst (asm) h_eq[symmetric])
    from h_h' and this show "h' z = (h' (z/2) + h' ((z+1)/2)) / 4" by (rule DERIV_unique)
  qed

  have h'_zero: "h' z = 0" for z
  proof -
    define m where "m = max 1 \<bar>Re z\<bar>"
    define B where "B = {t. abs (Re t) \<le> m \<and> abs (Im t) \<le> abs (Im z)}"
    have "closed ({t. Re t \<ge> -m} \<inter> {t. Re t \<le> m} \<inter>
                  {t. Im t \<ge> -\<bar>Im z\<bar>} \<inter> {t. Im t \<le> \<bar>Im z\<bar>})"
      (is "closed ?B") by (intro closed_Int closed_halfspace_Re_ge closed_halfspace_Re_le
                                 closed_halfspace_Im_ge closed_halfspace_Im_le)
    also have "?B = B" unfolding B_def by fastforce
    finally have "closed B" .
    moreover have "bounded B" unfolding bounded_iff
    proof (intro ballI exI)
      fix t assume t: "t \<in> B"
      have "norm t \<le> \<bar>Re t\<bar> + \<bar>Im t\<bar>" by (rule cmod_le)
      also from t have "\<bar>Re t\<bar> \<le> m" unfolding B_def by blast
      also from t have "\<bar>Im t\<bar> \<le> \<bar>Im z\<bar>" unfolding B_def by blast
      finally show "norm t \<le> m + \<bar>Im z\<bar>" by - simp
    qed
    ultimately have compact: "compact B" by (subst compact_eq_bounded_closed) blast

    define M where "M = (SUP z\<in>B. norm (h' z))"
    have "compact (h' ` B)"
      by (intro compact_continuous_image continuous_on_subset[OF h'_cont] compact) blast+
    hence bdd: "bdd_above ((\<lambda>z. norm (h' z)) ` B)"
      using bdd_above_norm[of "h' ` B"] by (simp add: image_comp o_def compact_imp_bounded)
    have "norm (h' z) \<le> M" unfolding M_def by (intro cSUP_upper bdd) (simp_all add: B_def m_def)
    also have "M \<le> M/2"
    proof (subst M_def, subst cSUP_le_iff)
      have "z \<in> B" unfolding B_def m_def by simp
      thus "B \<noteq> {}" by auto
    next
      show "\<forall>z\<in>B. norm (h' z) \<le> M/2"
      proof
        fix t :: complex assume t: "t \<in> B"
        from h'_eq[of t] t have "h' t = (h' (t/2) + h' ((t+1)/2)) / 4" by (simp)
        also have "norm \<dots> = norm (h' (t/2) + h' ((t+1)/2)) / 4" by simp
        also have "norm (h' (t/2) + h' ((t+1)/2)) \<le> norm (h' (t/2)) + norm (h' ((t+1)/2))"
          by (rule norm_triangle_ineq)
        also from t have "abs (Re ((t + 1)/2)) \<le> m" unfolding m_def B_def by auto
        with t have "t/2 \<in> B" "(t+1)/2 \<in> B" unfolding B_def by auto
        hence "norm (h' (t/2)) + norm (h' ((t+1)/2)) \<le> M + M" unfolding M_def
          by (intro add_mono cSUP_upper bdd) (auto simp: B_def)
        also have "(M + M) / 4 = M / 2" by simp
        finally show "norm (h' t) \<le> M/2" by - simp_all
      qed
    qed (insert bdd, auto)
    hence "M \<le> 0" by simp
    finally show "h' z = 0" by simp
  qed
  have h_h'_2: "(h has_field_derivative 0) (at z)" for z
    using h_h'[of z] h'_zero[of z] by simp

  have g_real: "g z \<in> \<real>" if "z \<in> \<real>" for z
    unfolding g_def using that by (auto intro!: Reals_mult Gamma_complex_real)
  have h_real: "h z \<in> \<real>" if "z \<in> \<real>" for z
    unfolding h_def using that by (auto intro!: Reals_mult Reals_add Reals_diff Polygamma_Real)
  have g_nz: "g z \<noteq> 0" for z unfolding g_def using Ints_diff[of 1 "1-z"]
    by (auto simp: Gamma_eq_zero_iff sin_eq_0)

  from h'_zero h_h'_2 have "\<exists>c. \<forall>z\<in>UNIV. h z = c"
    by (intro has_field_derivative_zero_constant) (simp_all add: dist_0_norm)
  then obtain c where c: "\<And>z. h z = c" by auto
  have "\<exists>u. u \<in> closed_segment 0 1 \<and> Re (g 1) - Re (g 0) = Re (h u * g u * (1 - 0))"
    by (intro complex_mvt_line g_g')
  then obtain u where u: "u \<in> closed_segment 0 1" "Re (g 1) - Re (g 0) = Re (h u * g u)"
    by auto
  from u(1) have u': "u \<in> \<real>" unfolding closed_segment_def
    by (auto simp: scaleR_conv_of_real)
  from u' g_real[of u] g_nz[of u] have "Re (g u) \<noteq> 0" by (auto elim!: Reals_cases)
  with u(2) c[of u] g_real[of u] g_nz[of u] u'
    have "Re c = 0" by (simp add: complex_is_Real_iff g.of_1)
  with h_real[of 0] c[of 0] have "c = 0" by (auto elim!: Reals_cases)
  with c have A: "h z * g z = 0" for z by simp
  hence "(g has_field_derivative 0) (at z)" for z using g_g'[of z] by simp
  hence "\<exists>c'. \<forall>z\<in>UNIV. g z = c'" by (intro has_field_derivative_zero_constant) simp_all
  then obtain c' where c: "\<And>z. g z = c'" by (force)
  from this[of 0] have "c' = pi" unfolding g_def by simp
  with c have "g z = pi" by simp

  show ?thesis
  proof (cases "z \<in> \<int>")
    case False
    with \<open>g z = pi\<close> show ?thesis by (auto simp: g_def divide_simps)
  next
    case True
    then obtain n where n: "z = of_int n" by (elim Ints_cases)
    with sin_eq_0[of "of_real pi * z"] have "sin (of_real pi * z) = 0" by force
    moreover have "of_int (1 - n) \<in> \<int>\<^sub>\<le>\<^sub>0" if "n > 0" using that by (intro nonpos_Ints_of_int) simp
    ultimately show ?thesis using n
      by (cases "n \<le> 0") (auto simp: Gamma_eq_zero_iff nonpos_Ints_of_int)
  qed
qed

lemma rGamma_reflection_complex:
  "rGamma z * rGamma (1 - z :: complex) = sin (of_real pi * z) / of_real pi"
  using Gamma_reflection_complex[of z]
    by (simp add: Gamma_def field_split_simps split: if_split_asm)

lemma rGamma_reflection_complex':
  "rGamma z * rGamma (- z :: complex) = -z * sin (of_real pi * z) / of_real pi"
proof -
  have "rGamma z * rGamma (-z) = -z * (rGamma z * rGamma (1 - z))"
    using rGamma_plus1[of "-z", symmetric] by simp
  also have "rGamma z * rGamma (1 - z) = sin (of_real pi * z) / of_real pi"
    by (rule rGamma_reflection_complex)
  finally show ?thesis by simp
qed

lemma Gamma_reflection_complex':
  "Gamma z * Gamma (- z :: complex) = - of_real pi / (z * sin (of_real pi * z))"
  using rGamma_reflection_complex'[of z] by (force simp add: Gamma_def field_split_simps)



lemma Gamma_one_half_real: "Gamma (1/2 :: real) = sqrt pi"
proof -
  from Gamma_reflection_complex[of "1/2"] fraction_not_in_ints[where 'a = complex, of 2 1]
    have "Gamma (1/2 :: complex)^2 = of_real pi" by (simp add: power2_eq_square)
  hence "of_real pi = Gamma (complex_of_real (1/2))^2" by simp
  also have "\<dots> = of_real ((Gamma (1/2))^2)" by (subst Gamma_complex_of_real) simp_all
  finally have "Gamma (1/2)^2 = pi" by (subst (asm) of_real_eq_iff) simp_all
  moreover have "Gamma (1/2 :: real) \<ge> 0" using Gamma_real_pos[of "1/2"] by simp
  ultimately show ?thesis by (rule real_sqrt_unique [symmetric])
qed

lemma Gamma_one_half_complex: "Gamma (1/2 :: complex) = of_real (sqrt pi)"
proof -
  have "Gamma (1/2 :: complex) = Gamma (of_real (1/2))" by simp
  also have "\<dots> = of_real (sqrt pi)" by (simp only: Gamma_complex_of_real Gamma_one_half_real)
  finally show ?thesis .
qed

theorem Gamma_legendre_duplication:
  fixes z :: complex
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0" "z + 1/2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows "Gamma z * Gamma (z + 1/2) =
             exp ((1 - 2*z) * of_real (ln 2)) * of_real (sqrt pi) * Gamma (2*z)"
  using Gamma_legendre_duplication_aux[OF assms] by (simp add: Gamma_one_half_complex)

end


subsection\<^marker>\<open>tag unimportant\<close> \<open>Limits and residues\<close>

text \<open>
  The inverse of the Gamma function has simple zeros:
\<close>

lemma rGamma_zeros:
  "(\<lambda>z. rGamma z / (z + of_nat n)) \<midarrow> (- of_nat n) \<rightarrow> ((-1)^n * fact n :: 'a :: Gamma)"
proof (subst tendsto_cong)
  let ?f = "\<lambda>z. pochhammer z n * rGamma (z + of_nat (Suc n)) :: 'a"
  from eventually_at_ball'[OF zero_less_one, of "- of_nat n :: 'a" UNIV]
    show "eventually (\<lambda>z. rGamma z / (z + of_nat n) = ?f z) (at (- of_nat n))"
    by (subst pochhammer_rGamma[of _ "Suc n"])
       (auto elim!: eventually_mono simp: field_split_simps pochhammer_rec' eq_neg_iff_add_eq_0)
  have "isCont ?f (- of_nat n)" by (intro continuous_intros)
  thus "?f \<midarrow> (- of_nat n) \<rightarrow> (- 1) ^ n * fact n" unfolding isCont_def
    by (simp add: pochhammer_same)
qed


text \<open>
  The simple zeros of the inverse of the Gamma function correspond to simple poles of the Gamma function,
  and their residues can easily be computed from the limit we have just proven:
\<close>

lemma Gamma_poles: "filterlim Gamma at_infinity (at (- of_nat n :: 'a :: Gamma))"
proof -
  from eventually_at_ball'[OF zero_less_one, of "- of_nat n :: 'a" UNIV]
    have "eventually (\<lambda>z. rGamma z \<noteq> (0 :: 'a)) (at (- of_nat n))"
    by (auto elim!: eventually_mono nonpos_Ints_cases'
             simp: rGamma_eq_zero_iff dist_of_nat dist_minus)
  with isCont_rGamma[of "- of_nat n :: 'a", OF continuous_ident]
    have "filterlim (\<lambda>z. inverse (rGamma z) :: 'a) at_infinity (at (- of_nat n))"
    unfolding isCont_def by (intro filterlim_compose[OF filterlim_inverse_at_infinity])
                            (simp_all add: filterlim_at)
  moreover have "(\<lambda>z. inverse (rGamma z) :: 'a) = Gamma"
    by (intro ext) (simp add: rGamma_inverse_Gamma)
  ultimately show ?thesis by (simp only: )
qed

lemma Gamma_residues:
  "(\<lambda>z. Gamma z * (z + of_nat n)) \<midarrow> (- of_nat n) \<rightarrow> ((-1)^n / fact n :: 'a :: Gamma)"
proof (subst tendsto_cong)
  let ?c = "(- 1) ^ n / fact n :: 'a"
  from eventually_at_ball'[OF zero_less_one, of "- of_nat n :: 'a" UNIV]
    show "eventually (\<lambda>z. Gamma z * (z + of_nat n) = inverse (rGamma z / (z + of_nat n)))
            (at (- of_nat n))"
    by (auto elim!: eventually_mono simp: field_split_simps rGamma_inverse_Gamma)
  have "(\<lambda>z. inverse (rGamma z / (z + of_nat n))) \<midarrow> (- of_nat n) \<rightarrow>
          inverse ((- 1) ^ n * fact n :: 'a)"
    by (intro tendsto_intros rGamma_zeros) simp_all
  also have "inverse ((- 1) ^ n * fact n) = ?c"
    by (simp_all add: field_simps flip: power_mult_distrib)
  finally show "(\<lambda>z. inverse (rGamma z / (z + of_nat n))) \<midarrow> (- of_nat n) \<rightarrow> ?c" .
qed


subsection \<open>Alternative definitions\<close>


subsubsection \<open>Variant of the Euler form\<close>


definition Gamma_series_euler' where
  "Gamma_series_euler' z n =
     inverse z * (\<Prod>k=1..n. exp (z * of_real (ln (1 + inverse (of_nat k)))) / (1 + z / of_nat k))"

context
begin
private lemma Gamma_euler'_aux1:
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes n: "n > 0"
  shows "exp (z * of_real (ln (of_nat n + 1))) = (\<Prod>k=1..n. exp (z * of_real (ln (1 + 1 / of_nat k))))"
proof -
  have "(\<Prod>k=1..n. exp (z * of_real (ln (1 + 1 / of_nat k)))) =
          exp (z * of_real (\<Sum>k = 1..n. ln (1 + 1 / real_of_nat k)))"
    by (subst exp_sum [symmetric]) (simp_all add: sum_distrib_left)
  also have "(\<Sum>k=1..n. ln (1 + 1 / of_nat k) :: real) = ln (\<Prod>k=1..n. 1 + 1 / real_of_nat k)"
    by (subst ln_prod [symmetric]) (auto intro!: add_pos_nonneg)
  also have "(\<Prod>k=1..n. 1 + 1 / of_nat k :: real) = (\<Prod>k=1..n. (of_nat k + 1) / of_nat k)"
    by (intro prod.cong) (simp_all add: field_split_simps)
  also have "(\<Prod>k=1..n. (of_nat k + 1) / of_nat k :: real) = of_nat n + 1"
    by (induction n) (simp_all add: prod.nat_ivl_Suc' field_split_simps)
  finally show ?thesis ..
qed

theorem Gamma_series_euler':
  assumes z: "(z :: 'a :: Gamma) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows "(\<lambda>n. Gamma_series_euler' z n) \<longlonglongrightarrow> Gamma z"
proof (rule Gamma_seriesI, rule Lim_transform_eventually)
  let ?f = "\<lambda>n. fact n * exp (z * of_real (ln (of_nat n + 1))) / pochhammer z (n + 1)"
  let ?r = "\<lambda>n. ?f n / Gamma_series z n"
  let ?r' = "\<lambda>n. exp (z * of_real (ln (of_nat (Suc n) / of_nat n)))"
  from z have z': "z \<noteq> 0" by auto

  have "eventually (\<lambda>n. ?r' n = ?r n) sequentially"
    using z by (auto simp: field_split_simps Gamma_series_def ring_distribs exp_diff ln_div
                     intro: eventually_mono eventually_gt_at_top[of "0::nat"] dest: pochhammer_eq_0_imp_nonpos_Int)
  moreover have "?r' \<longlonglongrightarrow> exp (z * of_real (ln 1))"
    by (intro tendsto_intros LIMSEQ_Suc_n_over_n) simp_all
  ultimately show "?r \<longlonglongrightarrow> 1" by (force intro: Lim_transform_eventually)

  from eventually_gt_at_top[of "0::nat"]
    show "eventually (\<lambda>n. ?r n = Gamma_series_euler' z n / Gamma_series z n) sequentially"
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    from n z' have "Gamma_series_euler' z n =
      exp (z * of_real (ln (of_nat n + 1))) / (z * (\<Prod>k=1..n. (1 + z / of_nat k)))"
      by (subst Gamma_euler'_aux1)
         (simp_all add: Gamma_series_euler'_def prod.distrib
                        prod_inversef[symmetric] divide_inverse)
    also have "(\<Prod>k=1..n. (1 + z / of_nat k)) = pochhammer (z + 1) n / fact n"
    proof (cases n)
      case (Suc n')
      then show ?thesis
        unfolding pochhammer_prod fact_prod
        by (simp add:  atLeastLessThanSuc_atLeastAtMost field_simps prod_dividef 
                  prod.atLeast_Suc_atMost_Suc_shift del: prod.cl_ivl_Suc)
    qed auto
    also have "z * \<dots> = pochhammer z (Suc n) / fact n" by (simp add: pochhammer_rec)
    finally show "?r n = Gamma_series_euler' z n / Gamma_series z n" by simp
  qed
qed

end



subsubsection \<open>Weierstrass form\<close>

definition Gamma_series_Weierstrass :: "'a :: {banach,real_normed_field} \<Rightarrow> nat \<Rightarrow> 'a" where
  "Gamma_series_Weierstrass z n =
     exp (-euler_mascheroni * z) / z * (\<Prod>k=1..n. exp (z / of_nat k) / (1 + z / of_nat k))"

definition\<^marker>\<open>tag unimportant\<close>
  rGamma_series_Weierstrass :: "'a :: {banach,real_normed_field} \<Rightarrow> nat \<Rightarrow> 'a" where
  "rGamma_series_Weierstrass z n =
     exp (euler_mascheroni * z) * z * (\<Prod>k=1..n. (1 + z / of_nat k) * exp (-z / of_nat k))"

lemma Gamma_series_Weierstrass_nonpos_Ints:
  "eventually (\<lambda>k. Gamma_series_Weierstrass (- of_nat n) k = 0) sequentially"
  using eventually_ge_at_top[of n] by eventually_elim (auto simp: Gamma_series_Weierstrass_def)

lemma rGamma_series_Weierstrass_nonpos_Ints:
  "eventually (\<lambda>k. rGamma_series_Weierstrass (- of_nat n) k = 0) sequentially"
  using eventually_ge_at_top[of n] by eventually_elim (auto simp: rGamma_series_Weierstrass_def)

theorem Gamma_Weierstrass_complex: "Gamma_series_Weierstrass z \<longlonglongrightarrow> Gamma (z :: complex)"
proof (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0")
  case True
  then obtain n where "z = - of_nat n" by (elim nonpos_Ints_cases')
  also from True have "Gamma_series_Weierstrass \<dots> \<longlonglongrightarrow> Gamma z"
    by (simp add: tendsto_cong[OF Gamma_series_Weierstrass_nonpos_Ints] Gamma_nonpos_Int)
  finally show ?thesis .
next
  case False
  hence z: "z \<noteq> 0" by auto
  let ?f = "(\<lambda>x. \<Prod>x = Suc 0..x. exp (z / of_nat x) / (1 + z / of_nat x))"
  have A: "exp (ln (1 + z / of_nat n)) = (1 + z / of_nat n)" if "n \<ge> 1" for n :: nat
    using False that by (subst exp_Ln) (auto simp: field_simps dest!: plus_of_nat_eq_0_imp)
  have "(\<lambda>n. \<Sum>k=1..n. z / of_nat k - ln (1 + z / of_nat k)) \<longlonglongrightarrow> ln_Gamma z + euler_mascheroni * z + ln z"
    using ln_Gamma_series'_aux[OF False]
    by (simp only: atLeastLessThanSuc_atLeastAtMost [symmetric] One_nat_def
                   sum.shift_bounds_Suc_ivl sums_def atLeast0LessThan)
  from tendsto_exp[OF this] False z have "?f \<longlonglongrightarrow> z * exp (euler_mascheroni * z) * Gamma z"
    by (simp add: exp_add exp_sum exp_diff mult_ac Gamma_complex_altdef A)
  from tendsto_mult[OF tendsto_const[of "exp (-euler_mascheroni * z) / z"] this] z
    show "Gamma_series_Weierstrass z \<longlonglongrightarrow> Gamma z"
    by (simp add: exp_minus field_split_simps Gamma_series_Weierstrass_def [abs_def])
qed

lemma tendsto_complex_of_real_iff: "((\<lambda>x. complex_of_real (f x)) \<longlongrightarrow> of_real c) F = (f \<longlongrightarrow> c) F"
  by (rule tendsto_of_real_iff)

lemma Gamma_Weierstrass_real: "Gamma_series_Weierstrass x \<longlonglongrightarrow> Gamma (x :: real)"
  using Gamma_Weierstrass_complex[of "of_real x"] unfolding Gamma_series_Weierstrass_def[abs_def]
  by (subst tendsto_complex_of_real_iff [symmetric])
     (simp_all add: exp_of_real[symmetric] Gamma_complex_of_real)

lemma rGamma_Weierstrass_complex: "rGamma_series_Weierstrass z \<longlonglongrightarrow> rGamma (z :: complex)"
proof (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0")
  case True
  then obtain n where "z = - of_nat n" by (elim nonpos_Ints_cases')
  also from True have "rGamma_series_Weierstrass \<dots> \<longlonglongrightarrow> rGamma z"
    by (simp add: tendsto_cong[OF rGamma_series_Weierstrass_nonpos_Ints] rGamma_nonpos_Int)
  finally show ?thesis .
next
  case False
  have "rGamma_series_Weierstrass z = (\<lambda>n. inverse (Gamma_series_Weierstrass z n))"
    by (simp add: rGamma_series_Weierstrass_def[abs_def] Gamma_series_Weierstrass_def
                  exp_minus divide_inverse prod_inversef[symmetric] mult_ac)
  also from False have "\<dots> \<longlonglongrightarrow> inverse (Gamma z)"
    by (intro tendsto_intros Gamma_Weierstrass_complex) (simp add: Gamma_eq_zero_iff)
  finally show ?thesis by (simp add: Gamma_def)
qed

subsubsection \<open>Binomial coefficient form\<close>

lemma Gamma_gbinomial:
  "(\<lambda>n. ((z + of_nat n) gchoose n) * exp (-z * of_real (ln (of_nat n)))) \<longlonglongrightarrow> rGamma (z+1)"
proof (cases "z = 0")
  case False
  show ?thesis
  proof (rule Lim_transform_eventually)
    let ?powr = "\<lambda>a b. exp (b * of_real (ln (of_nat a)))"
    show "eventually (\<lambda>n. rGamma_series z n / z =
            ((z + of_nat n) gchoose n) * ?powr n (-z)) sequentially"
    proof (intro always_eventually allI)
      fix n :: nat
      from False have "((z + of_nat n) gchoose n) = pochhammer z (Suc n) / z / fact n"
        by (simp add: gbinomial_pochhammer' pochhammer_rec)
      also have "pochhammer z (Suc n) / z / fact n * ?powr n (-z) = rGamma_series z n / z"
        by (simp add: rGamma_series_def field_split_simps exp_minus)
      finally show "rGamma_series z n / z = ((z + of_nat n) gchoose n) * ?powr n (-z)" ..
    qed

    from False have "(\<lambda>n. rGamma_series z n / z) \<longlonglongrightarrow> rGamma z / z" by (intro tendsto_intros)
    also from False have "rGamma z / z = rGamma (z + 1)" using rGamma_plus1[of z]
      by (simp add: field_simps)
    finally show "(\<lambda>n. rGamma_series z n / z) \<longlonglongrightarrow> rGamma (z+1)" .
  qed
qed (simp_all add: binomial_gbinomial [symmetric])

lemma gbinomial_minus': "(a + of_nat b) gchoose b = (- 1) ^ b * (- (a + 1) gchoose b)"
  by (subst gbinomial_minus) (simp add: power_mult_distrib [symmetric])

lemma gbinomial_asymptotic:
  fixes z :: "'a :: Gamma"
  shows "(\<lambda>n. (z gchoose n) / ((-1)^n / exp ((z+1) * of_real (ln (real n))))) \<longlonglongrightarrow>
           inverse (Gamma (- z))"
  unfolding rGamma_inverse_Gamma [symmetric] using Gamma_gbinomial[of "-z-1"]
  by (subst (asm) gbinomial_minus')
     (simp add: add_ac mult_ac divide_inverse power_inverse [symmetric])

lemma fact_binomial_limit:
  "(\<lambda>n. of_nat ((k + n) choose n) / of_nat (n ^ k) :: 'a :: Gamma) \<longlonglongrightarrow> 1 / fact k"
proof (rule Lim_transform_eventually)
  have "(\<lambda>n. of_nat ((k + n) choose n) / of_real (exp (of_nat k * ln (real_of_nat n))))
            \<longlonglongrightarrow> 1 / Gamma (of_nat (Suc k) :: 'a)" (is "?f \<longlonglongrightarrow> _")
    using Gamma_gbinomial[of "of_nat k :: 'a"]
    by (simp add: binomial_gbinomial Gamma_def field_split_simps exp_of_real [symmetric] exp_minus)
  also have "Gamma (of_nat (Suc k)) = fact k" by (simp add: Gamma_fact)
  finally show "?f \<longlonglongrightarrow> 1 / fact k" .

  show "eventually (\<lambda>n. ?f n = of_nat ((k + n) choose n) / of_nat (n ^ k)) sequentially"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    from n have "exp (real_of_nat k * ln (real_of_nat n)) = real_of_nat (n^k)"
      by (simp add: exp_of_nat_mult)
    thus "?f n = of_nat ((k + n) choose n) / of_nat (n ^ k)" by simp
  qed
qed

lemma binomial_asymptotic':
  "(\<lambda>n. of_nat ((k + n) choose n) / (of_nat (n ^ k) / fact k) :: 'a :: Gamma) \<longlonglongrightarrow> 1"
  using tendsto_mult[OF fact_binomial_limit[of k] tendsto_const[of "fact k :: 'a"]] by simp

lemma gbinomial_Beta:
  assumes "z + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((z::'a::Gamma) gchoose n) = inverse ((z + 1) * Beta (z - of_nat n + 1) (of_nat n + 1))"
using assms
proof (induction n arbitrary: z)
  case 0
  hence "z + 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
    using plus_one_in_nonpos_Ints_imp[of "z+1"] by (auto simp: add.commute)
  with 0 show ?case
    by (auto simp: Beta_def Gamma_eq_zero_iff Gamma_plus1 [symmetric] add.commute)
next
  case (Suc n z)
  show ?case
  proof (cases "z \<in> \<int>\<^sub>\<le>\<^sub>0")
    case True
    with Suc.prems have "z = 0"
      by (auto elim!: nonpos_Ints_cases simp: algebra_simps one_plus_of_int_in_nonpos_Ints_iff)
    show ?thesis
    proof (cases "n = 0")
      case True
      with \<open>z = 0\<close> show ?thesis
        by (simp add: Beta_def Gamma_eq_zero_iff Gamma_plus1 [symmetric])
    next
      case False
      with \<open>z = 0\<close> show ?thesis
        by (simp_all add: Beta_pole1 one_minus_of_nat_in_nonpos_Ints_iff)
    qed
  next
    case False
    have "(z gchoose (Suc n)) = ((z - 1 + 1) gchoose (Suc n))" by simp
    also have "\<dots> = (z - 1 gchoose n) * ((z - 1) + 1) / of_nat (Suc n)"
      by (subst gbinomial_factors) (simp add: field_simps)
    also from False have "\<dots> = inverse (of_nat (Suc n) * Beta (z - of_nat n) (of_nat (Suc n)))"
      (is "_ = inverse ?x") by (subst Suc.IH) (simp_all add: field_simps Beta_pole1)
    also have "of_nat (Suc n) \<notin> (\<int>\<^sub>\<le>\<^sub>0 :: 'a set)" by (subst of_nat_in_nonpos_Ints_iff) simp_all
    hence "?x = (z + 1) * Beta (z - of_nat (Suc n) + 1) (of_nat (Suc n) + 1)"
      by (subst Beta_plus1_right [symmetric]) simp_all
    finally show ?thesis .
  qed
qed

theorem gbinomial_Gamma:
  assumes "z + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(z gchoose n) = Gamma (z + 1) / (fact n * Gamma (z - of_nat n + 1))"
proof -
  have "(z gchoose n) = Gamma (z + 2) / (z + 1) / (fact n * Gamma (z - of_nat n + 1))"
    by (subst gbinomial_Beta[OF assms]) (simp_all add: Beta_def Gamma_fact [symmetric] add_ac)
  also from assms have "Gamma (z + 2) / (z + 1) = Gamma (z + 1)"
    using Gamma_plus1[of "z+1"] by (auto simp add: field_split_simps)
  finally show ?thesis .
qed


subsubsection \<open>Integral form\<close>

lemma integrable_on_powr_from_0':
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "(\<lambda>x. x powr a) integrable_on {0<..c}"
proof -
  from c have *: "{0<..c} - {0..c} = {}" "{0..c} - {0<..c} = {0}" by auto
  show ?thesis
  by (rule integrable_spike_set [OF integrable_on_powr_from_0[OF a c]]) (simp_all add: *)
qed

lemma absolutely_integrable_Gamma_integral:
  assumes "Re z > 0" "a > 0"
  shows   "(\<lambda>t. complex_of_real t powr (z - 1) / of_real (exp (a * t))) 
             absolutely_integrable_on {0<..}" (is "?f absolutely_integrable_on _")
proof -
  have "((\<lambda>x. (Re z - 1) * (ln x / x)) \<longlongrightarrow> (Re z - 1) * 0) at_top"
    by (intro tendsto_intros ln_x_over_x_tendsto_0)
  hence "((\<lambda>x. ((Re z - 1) * ln x) / x) \<longlongrightarrow> 0) at_top" by simp
  from order_tendstoD(2)[OF this, of "a/2"] and \<open>a > 0\<close>
    have "eventually (\<lambda>x. (Re z - 1) * ln x / x < a/2) at_top" by simp
  from eventually_conj[OF this eventually_gt_at_top[of 0]]
    obtain x0 where "\<forall>x\<ge>x0. (Re z - 1) * ln x / x < a/2 \<and> x > 0"
      by (auto simp: eventually_at_top_linorder)
  hence "x0 > 0" by simp
  have "x powr (Re z - 1) / exp (a * x) < exp (-(a/2) * x)" if "x \<ge> x0" for x
  proof -
    from that and \<open>\<forall>x\<ge>x0. _\<close> have x: "(Re z - 1) * ln x / x < a / 2" "x > 0" by auto
    have "x powr (Re z - 1) = exp ((Re z - 1) * ln x)"
      using \<open>x > 0\<close> by (simp add: powr_def)
    also from x have "(Re z - 1) * ln x < (a * x) / 2" by (simp add: field_simps)
    finally show ?thesis by (simp add: field_simps exp_add [symmetric])
  qed
  note x0 = \<open>x0 > 0\<close> this

  have "?f absolutely_integrable_on ({0<..x0} \<union> {x0..})"
  proof (rule set_integrable_Un)
    show "?f absolutely_integrable_on {0<..x0}"
      unfolding set_integrable_def
    proof (rule Bochner_Integration.integrable_bound [OF _ _ AE_I2])
      show "integrable lebesgue (\<lambda>x. indicat_real {0<..x0} x *\<^sub>R x powr (Re z - 1))"         
        using x0(1) assms
        by (intro nonnegative_absolutely_integrable_1 [unfolded set_integrable_def] integrable_on_powr_from_0') auto
      show "(\<lambda>x. indicat_real {0<..x0} x *\<^sub>R (x powr (z - 1) / exp (a * x))) \<in> borel_measurable lebesgue"
        by (intro measurable_completion)
           (auto intro!: borel_measurable_continuous_on_indicator continuous_intros)
      fix x :: real 
      have "x powr (Re z - 1) / exp (a * x) \<le> x powr (Re z - 1) / 1" if "x \<ge> 0"
        using that assms by (intro divide_left_mono) auto
      thus "norm (indicator {0<..x0} x *\<^sub>R ?f x) \<le> 
               norm (indicator {0<..x0} x *\<^sub>R x powr (Re z - 1))"
        by (simp_all add: norm_divide norm_powr_real_powr indicator_def)
    qed
  next
    show "?f absolutely_integrable_on {x0..}"
      unfolding set_integrable_def
    proof (rule Bochner_Integration.integrable_bound [OF _ _ AE_I2])
      show "integrable lebesgue (\<lambda>x. indicat_real {x0..} x *\<^sub>R exp (- (a / 2) * x))" using assms
        by (intro nonnegative_absolutely_integrable_1 [unfolded set_integrable_def] integrable_on_exp_minus_to_infinity) auto
      show "(\<lambda>x. indicat_real {x0..} x *\<^sub>R (x powr (z - 1) / exp (a * x))) \<in> borel_measurable lebesgue" using x0(1)
        by (intro measurable_completion)
           (auto intro!: borel_measurable_continuous_on_indicator continuous_intros)
      fix x :: real 
      show "norm (indicator {x0..} x *\<^sub>R ?f x) \<le> 
               norm (indicator {x0..} x *\<^sub>R exp (-(a/2) * x))" using x0
        by (auto simp: norm_divide norm_powr_real_powr indicator_def less_imp_le)
    qed
  qed auto
  also have "{0<..x0} \<union> {x0..} = {0<..}" using x0(1) by auto
  finally show ?thesis .
qed

lemma integrable_Gamma_integral_bound:
  fixes a c :: real
  assumes a: "a > -1" and c: "c \<ge> 0"
  defines "f \<equiv> \<lambda>x. if x \<in> {0..c} then x powr a else exp (-x/2)"
  shows   "f integrable_on {0..}"
proof -
  have "f integrable_on {0..c}"
    by (rule integrable_spike_finite[of "{}", OF _ _ integrable_on_powr_from_0[of a c]])
       (insert a c, simp_all add: f_def)
  moreover have A: "(\<lambda>x. exp (-x/2)) integrable_on {c..}"
    using integrable_on_exp_minus_to_infinity[of "1/2"] by simp
  have "f integrable_on {c..}"
    by (rule integrable_spike_finite[of "{c}", OF _ _ A]) (simp_all add: f_def)
  ultimately show "f integrable_on {0..}"
    by (rule integrable_Un') (insert c, auto simp: max_def)
qed

theorem Gamma_integral_complex:
  assumes z: "Re z > 0"
  shows   "((\<lambda>t. of_real t powr (z - 1) / of_real (exp t)) has_integral Gamma z) {0..}"
proof -
  have A: "((\<lambda>t. (of_real t) powr (z - 1) * of_real ((1 - t) ^ n))
          has_integral (fact n / pochhammer z (n+1))) {0..1}"
    if "Re z > 0" for n z using that
  proof (induction n arbitrary: z)
    case 0
    have "((\<lambda>t. complex_of_real t powr (z - 1)) has_integral
            (of_real 1 powr z / z - of_real 0 powr z / z)) {0..1}" using 0
      by (intro fundamental_theorem_of_calculus_interior)
         (auto intro!: continuous_intros derivative_eq_intros has_vector_derivative_real_field)
    thus ?case by simp
  next
    case (Suc n)
    let ?f = "\<lambda>t. complex_of_real t powr z / z"
    let ?f' = "\<lambda>t. complex_of_real t powr (z - 1)"
    let ?g = "\<lambda>t. (1 - complex_of_real t) ^ Suc n"
    let ?g' = "\<lambda>t. - ((1 - complex_of_real t) ^ n) * of_nat (Suc n)"
    have "((\<lambda>t. ?f' t * ?g t) has_integral
            (of_nat (Suc n)) * fact n / pochhammer z (n+2)) {0..1}"
      (is "(_ has_integral ?I) _")
    proof (rule integration_by_parts_interior[where f' = ?f' and g = ?g])
      from Suc.prems show "continuous_on {0..1} ?f" "continuous_on {0..1} ?g"
        by (auto intro!: continuous_intros)
    next
      fix t :: real assume t: "t \<in> {0<..<1}"
      show "(?f has_vector_derivative ?f' t) (at t)" using t Suc.prems
        by (auto intro!: derivative_eq_intros has_vector_derivative_real_field)
      show "(?g has_vector_derivative ?g' t) (at t)"
        by (rule has_vector_derivative_real_field derivative_eq_intros refl)+ simp_all
    next
      from Suc.prems have [simp]: "z \<noteq> 0" by auto
      from Suc.prems have A: "Re (z + of_nat n) > 0" for n by simp
      have [simp]: "z + of_nat n \<noteq> 0" "z + 1 + of_nat n \<noteq> 0" for n
        using A[of n] A[of "Suc n"] by (auto simp add: add.assoc simp del: plus_complex.sel)
      have "((\<lambda>x. of_real x powr z * of_real ((1 - x) ^ n) * (- of_nat (Suc n) / z)) has_integral
              fact n / pochhammer (z+1) (n+1) * (- of_nat (Suc n) / z)) {0..1}"
        (is "(?A has_integral ?B) _")
        using Suc.IH[of "z+1"] Suc.prems by (intro has_integral_mult_left) (simp_all add: add_ac pochhammer_rec)
      also have "?A = (\<lambda>t. ?f t * ?g' t)" by (intro ext) (simp_all add: field_simps)
      also have "?B = - (of_nat (Suc n) * fact n / pochhammer z (n+2))"
        by (simp add: field_split_simps pochhammer_rec
              prod.shift_bounds_cl_Suc_ivl del: of_nat_Suc)
      finally show "((\<lambda>t. ?f t * ?g' t) has_integral (?f 1 * ?g 1 - ?f 0 * ?g 0 - ?I)) {0..1}"
        by simp
    qed (simp_all add: bounded_bilinear_mult)
    thus ?case by simp
  qed

  have B: "((\<lambda>t. if t \<in> {0..of_nat n} then
             of_real t powr (z - 1) * (1 - of_real t / of_nat n) ^ n else 0)
           has_integral (of_nat n powr z * fact n / pochhammer z (n+1))) {0..}" for n
  proof (cases "n > 0")
    case [simp]: True
    hence [simp]: "n \<noteq> 0" by auto
    with has_integral_affinity01[OF A[OF z, of n], of "inverse (of_nat n)" 0]
      have "((\<lambda>x. (of_nat n - of_real x) ^ n * (of_real x / of_nat n) powr (z - 1) / of_nat n ^ n)
              has_integral fact n * of_nat n / pochhammer z (n+1)) ((\<lambda>x. real n * x)`{0..1})"
      (is "(?f has_integral ?I) ?ivl") by (simp add: field_simps scaleR_conv_of_real)
    also from True have "((\<lambda>x. real n*x)`{0..1}) = {0..real n}"
      by (subst image_mult_atLeastAtMost) simp_all
    also have "?f = (\<lambda>x. (of_real x / of_nat n) powr (z - 1) * (1 - of_real x / of_nat n) ^ n)"
      using True by (intro ext) (simp add: field_simps)
    finally have "((\<lambda>x. (of_real x / of_nat n) powr (z - 1) * (1 - of_real x / of_nat n) ^ n)
                    has_integral ?I) {0..real n}" (is ?P) .
    also have "?P \<longleftrightarrow> ((\<lambda>x. exp ((z - 1) * of_real (ln (x / of_nat n))) * (1 - of_real x / of_nat n) ^ n)
                        has_integral ?I) {0..real n}"
      by (intro has_integral_spike_finite_eq[of "{0}"]) (auto simp: powr_def Ln_of_real [symmetric])
    also have "\<dots> \<longleftrightarrow> ((\<lambda>x. exp ((z - 1) * of_real (ln x - ln (of_nat n))) * (1 - of_real x / of_nat n) ^ n)
                        has_integral ?I) {0..real n}"
      by (intro has_integral_spike_finite_eq[of "{0}"]) (simp_all add: ln_div)
    finally have \<dots> .
    note B = has_integral_mult_right[OF this, of "exp ((z - 1) * ln (of_nat n))"]
    have "((\<lambda>x. exp ((z - 1) * of_real (ln x)) * (1 - of_real x / of_nat n) ^ n)
            has_integral (?I * exp ((z - 1) * ln (of_nat n)))) {0..real n}" (is ?P)
      by (insert B, subst (asm) mult.assoc [symmetric], subst (asm) exp_add [symmetric])
         (simp add: algebra_simps)
    also have "?P \<longleftrightarrow> ((\<lambda>x. of_real x powr (z - 1) * (1 - of_real x / of_nat n) ^ n)
            has_integral (?I * exp ((z - 1) * ln (of_nat n)))) {0..real n}"
      by (intro has_integral_spike_finite_eq[of "{0}"]) (simp_all add: powr_def Ln_of_real)
    also have "fact n * of_nat n / pochhammer z (n+1) * exp ((z - 1) * Ln (of_nat n)) =
                 (of_nat n powr z * fact n / pochhammer z (n+1))"
      by (auto simp add: powr_def algebra_simps exp_diff exp_of_real)
    finally show ?thesis by (subst has_integral_restrict) simp_all
  next
    case False
    thus ?thesis by (subst has_integral_restrict) (simp_all add: has_integral_refl)
  qed

  have "eventually (\<lambda>n. Gamma_series z n =
          of_nat n powr z * fact n / pochhammer z (n+1)) sequentially"
    using eventually_gt_at_top[of "0::nat"]
    by eventually_elim (simp add: powr_def algebra_simps Gamma_series_def)
  from this and Gamma_series_LIMSEQ[of z]
    have C: "(\<lambda>k. of_nat k powr z * fact k / pochhammer z (k+1)) \<longlonglongrightarrow> Gamma z"
    by (blast intro: Lim_transform_eventually)
  {
    fix x :: real assume x: "x \<ge> 0"
    have lim_exp: "(\<lambda>k. (1 - x / real k) ^ k) \<longlonglongrightarrow> exp (-x)"
      using tendsto_exp_limit_sequentially[of "-x"] by simp
    have "(\<lambda>k. of_real x powr (z - 1) * of_real ((1 - x / of_nat k) ^ k))
            \<longlonglongrightarrow> of_real x powr (z - 1) * of_real (exp (-x))" (is ?P)
      by (intro tendsto_intros lim_exp)
    also from eventually_gt_at_top[of "nat \<lceil>x\<rceil>"]
      have "eventually (\<lambda>k. of_nat k > x) sequentially" by eventually_elim linarith
    hence "?P \<longleftrightarrow> (\<lambda>k. if x \<le> of_nat k then
                 of_real x powr (z - 1) * of_real ((1 - x / of_nat k) ^ k) else 0)
                   \<longlonglongrightarrow> of_real x powr (z - 1) * of_real (exp (-x))"
      by (intro tendsto_cong) (auto elim!: eventually_mono)
    finally have \<dots> .
  }
  hence D: "\<forall>x\<in>{0..}. (\<lambda>k. if x \<in> {0..real k} then
              of_real x powr (z - 1) * (1 - of_real x / of_nat k) ^ k else 0)
             \<longlonglongrightarrow> of_real x powr (z - 1) / of_real (exp x)"
    by (simp add: exp_minus field_simps cong: if_cong)

  have "((\<lambda>x. (Re z - 1) * (ln x / x)) \<longlongrightarrow> (Re z - 1) * 0) at_top"
    by (intro tendsto_intros ln_x_over_x_tendsto_0)
  hence "((\<lambda>x. ((Re z - 1) * ln x) / x) \<longlongrightarrow> 0) at_top" by simp
  from order_tendstoD(2)[OF this, of "1/2"]
    have "eventually (\<lambda>x. (Re z - 1) * ln x / x < 1/2) at_top" by simp
  from eventually_conj[OF this eventually_gt_at_top[of 0]]
    obtain x0 where "\<forall>x\<ge>x0. (Re z - 1) * ln x / x < 1/2 \<and> x > 0"
    by (auto simp: eventually_at_top_linorder)
  hence x0: "x0 > 0" "\<And>x. x \<ge> x0 \<Longrightarrow> (Re z - 1) * ln x < x / 2" by auto

  define h where "h = (\<lambda>x. if x \<in> {0..x0} then x powr (Re z - 1) else exp (-x/2))"
  have le_h: "x powr (Re z - 1) * exp (-x) \<le> h x" if x: "x \<ge> 0" for x
  proof (cases "x > x0")
    case True
    from True x0(1) have "x powr (Re z - 1) * exp (-x) = exp ((Re z - 1) * ln x - x)"
      by (simp add: powr_def exp_diff exp_minus field_simps exp_add)
    also from x0(2)[of x] True have "\<dots> < exp (-x/2)"
      by (simp add: field_simps)
    finally show ?thesis using True by (auto simp add: h_def)
  next
    case False
    from x have "x powr (Re z - 1) * exp (- x) \<le> x powr (Re z - 1) * 1"
      by (intro mult_left_mono) simp_all
    with False show ?thesis by (auto simp add: h_def)
  qed

  have E: "\<forall>x\<in>{0..}. cmod (if x \<in> {0..real k} then of_real x powr (z - 1) *
                   (1 - complex_of_real x / of_nat k) ^ k else 0) \<le> h x"
    (is "\<forall>x\<in>_. ?f x \<le> _") for k
  proof safe
    fix x :: real assume x: "x \<ge> 0"
    {
      fix x :: real and n :: nat assume x: "x \<le> of_nat n"
      have "(1 - complex_of_real x / of_nat n) = complex_of_real ((1 - x / of_nat n))" by simp
      also have "norm \<dots> = \<bar>(1 - x / real n)\<bar>" by (subst norm_of_real) (rule refl)
      also from x have "\<dots> = (1 - x / real n)" by (intro abs_of_nonneg) (simp_all add: field_split_simps)
      finally have "cmod (1 - complex_of_real x / of_nat n) = 1 - x / real n" .
    } note D = this
    from D[of x k] x
      have "?f x \<le> (if of_nat k \<ge> x \<and> k > 0 then x powr (Re z - 1) * (1 - x / real k) ^ k else 0)"
      by (auto simp: norm_mult norm_powr_real_powr norm_power intro!: mult_nonneg_nonneg)
    also have "\<dots> \<le> x powr (Re z - 1) * exp  (-x)"
      by (auto intro!: mult_left_mono exp_ge_one_minus_x_over_n_power_n)
    also from x have "\<dots> \<le> h x" by (rule le_h)
    finally show "?f x \<le> h x" .
  qed

  have F: "h integrable_on {0..}" unfolding h_def
    by (rule integrable_Gamma_integral_bound) (insert assms x0(1), simp_all)
  show ?thesis
    by (rule has_integral_dominated_convergence[OF B F E D C])
qed

lemma Gamma_integral_real:
  assumes x: "x > (0 :: real)"
  shows   "((\<lambda>t. t powr (x - 1) / exp t) has_integral Gamma x) {0..}"
proof -
  have A: "((\<lambda>t. complex_of_real t powr (complex_of_real x - 1) /
          complex_of_real (exp t)) has_integral complex_of_real (Gamma x)) {0..}"
    using Gamma_integral_complex[of x] assms by (simp_all add: Gamma_complex_of_real powr_of_real)
  have "((\<lambda>t. complex_of_real (t powr (x - 1) / exp t)) has_integral of_real (Gamma x)) {0..}"
    by (rule has_integral_eq[OF _ A]) (simp_all add: powr_of_real [symmetric])
  from has_integral_linear[OF this bounded_linear_Re] show ?thesis by (simp add: o_def)
qed

lemma absolutely_integrable_Gamma_integral':
  assumes "Re z > 0"
  shows   "(\<lambda>t. complex_of_real t powr (z - 1) / of_real (exp t)) absolutely_integrable_on {0<..}"
  using absolutely_integrable_Gamma_integral [OF assms zero_less_one] by simp

lemma Gamma_integral_complex':
  assumes z: "Re z > 0"
  shows   "((\<lambda>t. of_real t powr (z - 1) / of_real (exp t)) has_integral Gamma z) {0<..}"
proof -
  have "((\<lambda>t. of_real t powr (z - 1) / of_real (exp t)) has_integral Gamma z) {0..}"
    by (rule Gamma_integral_complex) fact+
  hence "((\<lambda>t. if t \<in> {0<..} then of_real t powr (z - 1) / of_real (exp t) else 0) 
           has_integral Gamma z) {0..}"
    by (rule has_integral_spike [of "{0}", rotated 2]) auto
  also have "?this = ?thesis"
    by (subst has_integral_restrict) auto
  finally show ?thesis .
qed

lemma Gamma_conv_nn_integral_real:
  assumes "s > (0::real)"
  shows   "Gamma s = nn_integral lborel (\<lambda>t. ennreal (indicator {0..} t * t powr (s - 1) / exp t))"
  using nn_integral_has_integral_lebesgue[OF _ Gamma_integral_real[OF assms]] by simp

lemma integrable_Beta:
  assumes "a > 0" "b > (0::real)"
  shows   "set_integrable lborel {0..1} (\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1))"
proof -
  define C where "C = max 1 ((1/2) powr (b - 1))"
  define D where "D = max 1 ((1/2) powr (a - 1))"
  have C: "(1 - x) powr (b - 1) \<le> C" if "x \<in> {0..1/2}" for x
  proof (cases "b < 1")
    case False
    with that have "(1 - x) powr (b - 1) \<le> (1 powr (b - 1))" by (intro powr_mono2) auto
    thus ?thesis by (auto simp: C_def)
  qed (insert that, auto simp: max.coboundedI1 max.coboundedI2 powr_mono2' powr_mono2 C_def)
  have D: "x powr (a - 1) \<le> D" if "x \<in> {1/2..1}" for x
  proof (cases "a < 1")
    case False
    with that have "x powr (a - 1) \<le> (1 powr (a - 1))" by (intro powr_mono2) auto
    thus ?thesis by (auto simp: D_def)
  next
    case True
  qed (insert that, auto simp: max.coboundedI1 max.coboundedI2 powr_mono2' powr_mono2 D_def)
  have [simp]: "C \<ge> 0" "D \<ge> 0" by (simp_all add: C_def D_def)

  have I1: "set_integrable lborel {0..1/2} (\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1))"
    unfolding set_integrable_def
  proof (rule Bochner_Integration.integrable_bound[OF _ _ AE_I2])
    have "(\<lambda>t. t powr (a - 1)) integrable_on {0..1/2}"
      by (rule integrable_on_powr_from_0) (use assms in auto)
    hence "(\<lambda>t. t powr (a - 1)) absolutely_integrable_on {0..1/2}"
      by (subst absolutely_integrable_on_iff_nonneg) auto
    from integrable_mult_right[OF this [unfolded set_integrable_def], of C]
    show "integrable lborel (\<lambda>x. indicat_real {0..1/2} x *\<^sub>R (C * x powr (a - 1)))"
      by (subst (asm) integrable_completion) (auto simp: mult_ac)
  next
    fix x :: real
    have "x powr (a - 1) * (1 - x) powr (b - 1) \<le> x powr (a - 1) * C" if "x \<in> {0..1/2}"
      using that by (intro mult_left_mono powr_mono2 C) auto
    thus "norm (indicator {0..1/2} x *\<^sub>R (x powr (a - 1) * (1 - x) powr (b - 1))) \<le>
            norm (indicator {0..1/2} x *\<^sub>R (C * x powr (a - 1)))"
      by (auto simp: indicator_def abs_mult mult_ac)
  qed (auto intro!: AE_I2 simp: indicator_def)

  have I2: "set_integrable lborel {1/2..1} (\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1))"
    unfolding set_integrable_def
  proof (rule Bochner_Integration.integrable_bound[OF _ _ AE_I2])
    have "(\<lambda>t. t powr (b - 1)) integrable_on {0..1/2}"
      by (rule integrable_on_powr_from_0) (use assms in auto)
    hence "(\<lambda>t. t powr (b - 1)) integrable_on (cbox 0 (1/2))" by simp
    from integrable_affinity[OF this, of "-1" 1]
      have "(\<lambda>t. (1 - t) powr (b - 1)) integrable_on {1/2..1}" by simp
    hence "(\<lambda>t. (1 - t) powr (b - 1)) absolutely_integrable_on {1/2..1}"
      by (subst absolutely_integrable_on_iff_nonneg) auto
    from integrable_mult_right[OF this [unfolded set_integrable_def], of D]
    show "integrable lborel (\<lambda>x. indicat_real {1/2..1} x *\<^sub>R (D * (1 - x) powr (b - 1)))"
      by (subst (asm) integrable_completion) (auto simp: mult_ac)
  next
    fix x :: real
    have "x powr (a - 1) * (1 - x) powr (b - 1) \<le> D * (1 - x) powr (b - 1)" if "x \<in> {1/2..1}"
      using that by (intro mult_right_mono powr_mono2 D) auto
    thus "norm (indicator {1/2..1} x *\<^sub>R (x powr (a - 1) * (1 - x) powr (b - 1))) \<le>
            norm (indicator {1/2..1} x *\<^sub>R (D * (1 - x) powr (b - 1)))"
      by (auto simp: indicator_def abs_mult mult_ac)
  qed (auto intro!: AE_I2 simp: indicator_def)

  have "set_integrable lborel ({0..1/2} \<union> {1/2..1}) (\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1))"
    by (intro set_integrable_Un I1 I2) auto
  also have "{0..1/2} \<union> {1/2..1} = {0..(1::real)}" by auto
  finally show ?thesis .
qed

lemma integrable_Beta':
  assumes "a > 0" "b > (0::real)"
  shows   "(\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1)) integrable_on {0..1}"
  using integrable_Beta[OF assms] by (rule set_borel_integral_eq_integral)

theorem has_integral_Beta_real:
  assumes a: "a > 0" and b: "b > (0 :: real)"
  shows "((\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1)) has_integral Beta a b) {0..1}"
proof -
  define B where "B = integral {0..1} (\<lambda>x. x powr (a - 1) * (1 - x) powr (b - 1))"
  have [simp]: "B \<ge> 0" unfolding B_def using a b
    by (intro integral_nonneg integrable_Beta') auto
  from a b have "ennreal (Gamma a * Gamma b) =
    (\<integral>\<^sup>+ t. ennreal (indicator {0..} t * t powr (a - 1) / exp t) \<partial>lborel) *
    (\<integral>\<^sup>+ t. ennreal (indicator {0..} t * t powr (b - 1) / exp t) \<partial>lborel)"
    by (subst ennreal_mult') (simp_all add: Gamma_conv_nn_integral_real)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+u. ennreal (indicator {0..} t * t powr (a - 1) / exp t) *
                            ennreal (indicator {0..} u * u powr (b - 1) / exp u) \<partial>lborel \<partial>lborel)"
    by (simp add: nn_integral_cmult nn_integral_multc)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+u. ennreal (indicator ({0..}\<times>{0..}) (t,u) * t powr (a - 1) * u powr (b - 1)
                            / exp (t + u)) \<partial>lborel \<partial>lborel)"
    by (intro nn_integral_cong)
       (auto simp: indicator_def divide_ennreal ennreal_mult' [symmetric] exp_add)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+u. ennreal (indicator ({0..}\<times>{t..}) (t,u) * t powr (a - 1) * 
                              (u - t) powr (b - 1) / exp u) \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_cong, goal_cases)
    case (1 t)
    have "(\<integral>\<^sup>+u. ennreal (indicator ({0..}\<times>{0..}) (t,u) * t powr (a - 1) * 
                              u powr (b - 1) / exp (t + u)) \<partial>distr lborel borel ((+) (-t))) =
               (\<integral>\<^sup>+u. ennreal (indicator ({0..}\<times>{t..}) (t,u) * t powr (a - 1) * 
                              (u - t) powr (b - 1) / exp u) \<partial>lborel)"
      by (subst nn_integral_distr) (auto intro!: nn_integral_cong simp: indicator_def)
    thus ?case by (subst (asm) lborel_distr_plus)
  qed
  also have "\<dots> = (\<integral>\<^sup>+u. \<integral>\<^sup>+t. ennreal (indicator ({0..}\<times>{t..}) (t,u) * t powr (a - 1) * 
                              (u - t) powr (b - 1) / exp u) \<partial>lborel \<partial>lborel)"
    by (subst lborel_pair.Fubini')
       (auto simp: case_prod_unfold indicator_def cong: measurable_cong_sets)
  also have "\<dots> = (\<integral>\<^sup>+u. \<integral>\<^sup>+t. ennreal (indicator {0..u} t * t powr (a - 1) * (u - t) powr (b - 1)) *
                              ennreal (indicator {0..} u / exp u) \<partial>lborel \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: indicator_def ennreal_mult' [symmetric])
  also have "\<dots> = (\<integral>\<^sup>+u. (\<integral>\<^sup>+t. ennreal (indicator {0..u} t * t powr (a - 1) * (u - t) powr (b - 1)) 
                          \<partial>lborel) * ennreal (indicator {0..} u / exp u) \<partial>lborel)"
    by (subst nn_integral_multc [symmetric]) auto 
  also have "\<dots> = (\<integral>\<^sup>+u. (\<integral>\<^sup>+t. ennreal (indicator {0..u} t * t powr (a - 1) * (u - t) powr (b - 1)) 
                          \<partial>lborel) * ennreal (indicator {0<..} u / exp u) \<partial>lborel)"
    by (intro nn_integral_cong_AE eventually_mono[OF AE_lborel_singleton[of 0]]) 
       (auto simp: indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+u. ennreal B * ennreal (indicator {0..} u / exp u * u powr (a + b - 1)) \<partial>lborel)"
  proof (intro nn_integral_cong, goal_cases)
    case (1 u)
    show ?case
    proof (cases "u > 0")
      case True
      have "(\<integral>\<^sup>+t. ennreal (indicator {0..u} t * t powr (a - 1) * (u - t) powr (b - 1)) \<partial>lborel) = 
              (\<integral>\<^sup>+t. ennreal (indicator {0..1} t * (u * t) powr (a - 1) * (u - u * t) powr (b - 1)) 
                \<partial>distr lborel borel ((*) (1 / u)))" (is "_ = nn_integral _ ?f")
        using True
        by (subst nn_integral_distr) (auto simp: indicator_def field_simps intro!: nn_integral_cong)
      also have "distr lborel borel ((*) (1 / u)) = density lborel (\<lambda>_. u)"
        using \<open>u > 0\<close> by (subst lborel_distr_mult) auto
      also have "nn_integral \<dots> ?f = (\<integral>\<^sup>+x. ennreal (indicator {0..1} x * (u * (u * x) powr (a - 1) *
                                              (u * (1 - x)) powr (b - 1))) \<partial>lborel)" using \<open>u > 0\<close>
        by (subst nn_integral_density) (auto simp: ennreal_mult' [symmetric] algebra_simps)
      also have "\<dots> = (\<integral>\<^sup>+x. ennreal (u powr (a + b - 1)) * 
                            ennreal (indicator {0..1} x * x powr (a - 1) *
                                       (1 - x) powr (b - 1)) \<partial>lborel)" using \<open>u > 0\<close> a b
        by (intro nn_integral_cong)
           (auto simp: indicator_def powr_mult powr_add powr_diff mult_ac ennreal_mult' [symmetric])
      also have "\<dots> = ennreal (u powr (a + b - 1)) * 
                        (\<integral>\<^sup>+x. ennreal (indicator {0..1} x * x powr (a - 1) *
                                         (1 - x) powr (b - 1)) \<partial>lborel)"
        by (subst nn_integral_cmult) auto
      also have "((\<lambda>x. x powr (a - 1) * (1 - x) powr (b - 1)) has_integral 
                   integral {0..1} (\<lambda>x. x powr (a - 1) * (1 - x) powr (b - 1))) {0..1}"
        using a b by (intro integrable_integral integrable_Beta')
      from nn_integral_has_integral_lebesgue[OF _ this] a b
        have "(\<integral>\<^sup>+x. ennreal (indicator {0..1} x * x powr (a - 1) *
                         (1 - x) powr (b - 1)) \<partial>lborel) = B" by (simp add: mult_ac B_def)
      finally show ?thesis using \<open>u > 0\<close> by (simp add: ennreal_mult' [symmetric] mult_ac)
    qed auto
  qed
  also have "\<dots> = ennreal B * ennreal (Gamma (a + b))"
    using a b by (subst nn_integral_cmult) (auto simp: Gamma_conv_nn_integral_real)
  also have "\<dots> = ennreal (B * Gamma (a + b))"
    by (subst (1 2) mult.commute, intro ennreal_mult' [symmetric]) (use a b in auto)
  finally have "B = Beta a b" using a b Gamma_real_pos[of "a + b"]
    by (subst (asm) ennreal_inj) (auto simp: field_simps Beta_def Gamma_eq_zero_iff)
  moreover have "(\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1)) integrable_on {0..1}"
    by (intro integrable_Beta' a b)
  ultimately show ?thesis by (simp add: has_integral_iff B_def)
qed


subsection \<open>The Weierstra{\ss} product formula for the sine\<close>

theorem sin_product_formula_complex:
  fixes z :: complex
  shows "(\<lambda>n. of_real pi * z * (\<Prod>k=1..n. 1 - z^2 / of_nat k^2)) \<longlonglongrightarrow> sin (of_real pi * z)"
proof -
  let ?f = "rGamma_series_Weierstrass"
  have "(\<lambda>n. (- of_real pi * inverse z) * (?f z n * ?f (- z) n))
            \<longlonglongrightarrow> (- of_real pi * inverse z) * (rGamma z * rGamma (- z))"
    by (intro tendsto_intros rGamma_Weierstrass_complex)
  also have "(\<lambda>n. (- of_real pi * inverse z) * (?f z n * ?f (-z) n)) =
                    (\<lambda>n. of_real pi * z * (\<Prod>k=1..n. 1 - z^2 / of_nat k ^ 2))"
  proof
    fix n :: nat
    have "(- of_real pi * inverse z) * (?f z n * ?f (-z) n) =
              of_real pi * z * (\<Prod>k=1..n. (of_nat k - z) * (of_nat k + z) / of_nat k ^ 2)"
      by (simp add: rGamma_series_Weierstrass_def mult_ac exp_minus
                    divide_simps prod.distrib[symmetric] power2_eq_square)
    also have "(\<Prod>k=1..n. (of_nat k - z) * (of_nat k + z) / of_nat k ^ 2) =
                 (\<Prod>k=1..n. 1 - z^2 / of_nat k ^ 2)"
      by (intro prod.cong) (simp_all add: power2_eq_square field_simps)
    finally show "(- of_real pi * inverse z) * (?f z n * ?f (-z) n) = of_real pi * z * \<dots>"
      by (simp add: field_split_simps)
  qed
  also have "(- of_real pi * inverse z) * (rGamma z * rGamma (- z)) = sin (of_real pi * z)"
    by (subst rGamma_reflection_complex') (simp add: field_split_simps)
  finally show ?thesis .
qed

lemma sin_product_formula_real:
  "(\<lambda>n. pi * (x::real) * (\<Prod>k=1..n. 1 - x^2 / of_nat k^2)) \<longlonglongrightarrow> sin (pi * x)"
proof -
  from sin_product_formula_complex[of "of_real x"]
    have "(\<lambda>n. of_real pi * of_real x * (\<Prod>k=1..n. 1 - (of_real x)^2 / (of_nat k)^2))
              \<longlonglongrightarrow> sin (of_real pi * of_real x :: complex)" (is "?f \<longlonglongrightarrow> ?y") .
  also have "?f = (\<lambda>n. of_real (pi * x * (\<Prod>k=1..n. 1 - x^2 / (of_nat k^2))))" by simp
  also have "?y = of_real (sin (pi * x))" by (simp only: sin_of_real [symmetric] of_real_mult)
  finally show ?thesis by (subst (asm) tendsto_of_real_iff)
qed

lemma sin_product_formula_real':
  assumes "x \<noteq> (0::real)"
  shows   "(\<lambda>n. (\<Prod>k=1..n. 1 - x^2 / of_nat k^2)) \<longlonglongrightarrow> sin (pi * x) / (pi * x)"
  using tendsto_divide[OF sin_product_formula_real[of x] tendsto_const[of "pi * x"]] assms
  by simp

theorem wallis: "(\<lambda>n. \<Prod>k=1..n. (4*real k^2) / (4*real k^2 - 1)) \<longlonglongrightarrow> pi / 2"
proof -
  from tendsto_inverse[OF tendsto_mult[OF
         sin_product_formula_real[of "1/2"] tendsto_const[of "2/pi"]]]
    have "(\<lambda>n. (\<Prod>k=1..n. inverse (1 - (1/2)\<^sup>2 / (real k)\<^sup>2))) \<longlonglongrightarrow> pi/2"
    by (simp add: prod_inversef [symmetric])
  also have "(\<lambda>n. (\<Prod>k=1..n. inverse (1 - (1/2)\<^sup>2 / (real k)\<^sup>2))) =
               (\<lambda>n. (\<Prod>k=1..n. (4*real k^2)/(4*real k^2 - 1)))"
    by (intro ext prod.cong refl) (simp add: field_split_simps)
  finally show ?thesis .
qed


subsection \<open>The Solution to the Basel problem\<close>

theorem inverse_squares_sums: "(\<lambda>n. 1 / (n + 1)\<^sup>2) sums (pi\<^sup>2 / 6)"
proof -
  define P where "P x n = (\<Prod>k=1..n. 1 - x^2 / of_nat k^2)" for x :: real and n
  define K where "K = (\<Sum>n. inverse (real_of_nat (Suc n))^2)"
  define f where [abs_def]: "f x = (\<Sum>n. P x n / of_nat (Suc n)^2)" for x
  define g where [abs_def]: "g x = (1 - sin (pi * x) / (pi * x))" for x

  have sums: "(\<lambda>n. P x n / of_nat (Suc n)^2) sums (if x = 0 then K else g x / x^2)" for x
  proof (cases "x = 0")
    assume x: "x = 0"
    have "summable (\<lambda>n. inverse ((real_of_nat (Suc n))\<^sup>2))"
      using inverse_power_summable[of 2] by (subst summable_Suc_iff) simp
    thus ?thesis by (simp add: x g_def P_def K_def inverse_eq_divide power_divide summable_sums)
  next
    assume x: "x \<noteq> 0"
    have "(\<lambda>n. P x n - P x (Suc n)) sums (P x 0 - sin (pi * x) / (pi * x))"
      unfolding P_def using x by (intro telescope_sums' sin_product_formula_real')
    also have "(\<lambda>n. P x n - P x (Suc n)) = (\<lambda>n. (x^2 / of_nat (Suc n)^2) * P x n)"
      unfolding P_def by (simp add: prod.nat_ivl_Suc' algebra_simps)
    also have "P x 0 = 1" by (simp add: P_def)
    finally have "(\<lambda>n. x\<^sup>2 / (of_nat (Suc n))\<^sup>2 * P x n) sums (1 - sin (pi * x) / (pi * x))" .
    from sums_divide[OF this, of "x^2"] x show ?thesis unfolding g_def by simp
  qed

  have "continuous_on (ball 0 1) f"
  proof (rule uniform_limit_theorem; (intro always_eventually allI)?)
    show "uniform_limit (ball 0 1) (\<lambda>n x. \<Sum>k<n. P x k / of_nat (Suc k)^2) f sequentially"
    proof (unfold f_def, rule Weierstrass_m_test)
      fix n :: nat and x :: real assume x: "x \<in> ball 0 1"
      {
        fix k :: nat assume k: "k \<ge> 1"
        from x have "x^2 < 1" by (auto simp: abs_square_less_1)
        also from k have "\<dots> \<le> of_nat k^2" by simp
        finally have "(1 - x^2 / of_nat k^2) \<in> {0..1}" using k
          by (simp_all add: field_simps del: of_nat_Suc)
      }
      hence "(\<Prod>k=1..n. abs (1 - x^2 / of_nat k^2)) \<le> (\<Prod>k=1..n. 1)" by (intro prod_mono) simp
      thus "norm (P x n / (of_nat (Suc n)^2)) \<le> 1 / of_nat (Suc n)^2"
        unfolding P_def by (simp add: field_simps abs_prod del: of_nat_Suc)
    qed (subst summable_Suc_iff, insert inverse_power_summable[of 2], simp add: inverse_eq_divide)
  qed (auto simp: P_def intro!: continuous_intros)
  hence "isCont f 0" by (subst (asm) continuous_on_eq_continuous_at) simp_all
  hence "(f \<midarrow> 0 \<rightarrow> f 0)" by (simp add: isCont_def)
  also have "f 0 = K" unfolding f_def P_def K_def by (simp add: inverse_eq_divide power_divide)
  finally have "f \<midarrow> 0 \<rightarrow> K" .

  moreover have "f \<midarrow> 0 \<rightarrow> pi^2 / 6"
  proof (rule Lim_transform_eventually)
    define f' where [abs_def]: "f' x = (\<Sum>n. - sin_coeff (n+3) * pi ^ (n+2) * x^n)" for x
    have "eventually (\<lambda>x. x \<noteq> (0::real)) (at 0)"
      by (auto simp add: eventually_at intro!: exI[of _ 1])
    thus "eventually (\<lambda>x. f' x = f x) (at 0)"
    proof eventually_elim
      fix x :: real assume x: "x \<noteq> 0"
      have "sin_coeff 1 = (1 :: real)" "sin_coeff 2 = (0::real)" by (simp_all add: sin_coeff_def)
      with sums_split_initial_segment[OF sums_minus[OF sin_converges], of 3 "pi*x"]
      have "(\<lambda>n. - (sin_coeff (n+3) * (pi*x)^(n+3))) sums (pi * x - sin (pi*x))"
        by (simp add: eval_nat_numeral)
      from sums_divide[OF this, of "x^3 * pi"] x
        have "(\<lambda>n. - (sin_coeff (n+3) * pi^(n+2) * x^n)) sums ((1 - sin (pi*x) / (pi*x)) / x^2)"
        by (simp add: field_split_simps eval_nat_numeral)
      with x have "(\<lambda>n. - (sin_coeff (n+3) * pi^(n+2) * x^n)) sums (g x / x^2)"
        by (simp add: g_def)
      hence "f' x = g x / x^2" by (simp add: sums_iff f'_def)
      also have "\<dots> = f x" using sums[of x] x by (simp add: sums_iff g_def f_def)
      finally show "f' x = f x" .
    qed

    have "isCont f' 0" unfolding f'_def
    proof (intro isCont_powser_converges_everywhere)
      fix x :: real show "summable (\<lambda>n. -sin_coeff (n+3) * pi^(n+2) * x^n)"
      proof (cases "x = 0")
        assume x: "x \<noteq> 0"
        from summable_divide[OF sums_summable[OF sums_split_initial_segment[OF
               sin_converges[of "pi*x"]], of 3], of "-pi*x^3"] x
          show ?thesis by (simp add: field_split_simps eval_nat_numeral)
      qed (simp only: summable_0_powser)
    qed
    hence "f' \<midarrow> 0 \<rightarrow> f' 0" by (simp add: isCont_def)
    also have "f' 0 = pi * pi / fact 3" unfolding f'_def
      by (subst powser_zero) (simp add: sin_coeff_def)
    finally show "f' \<midarrow> 0 \<rightarrow> pi^2 / 6" by (simp add: eval_nat_numeral)
  qed

  ultimately have "K = pi^2 / 6" by (rule LIM_unique)
  moreover from inverse_power_summable[of 2]
    have "summable (\<lambda>n. (inverse (real_of_nat (Suc n)))\<^sup>2)"
    by (subst summable_Suc_iff) (simp add: power_inverse)
  ultimately show ?thesis unfolding K_def
    by (auto simp add: sums_iff power_divide inverse_eq_divide)
qed

end
