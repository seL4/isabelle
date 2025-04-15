section \<open>The Weierstra\ss\ Factorisation Theorem\<close>
theory Weierstrass_Factorization
  imports Meromorphic
begin 
                
subsection \<open>The elementary factors\<close>

text \<open>
  The Weierstra\ss\ elementary factors are the family of entire functions
  \[E_n(z) = (1-z) \exp\bigg(z + \frac{z^2}{2} + \ldots + \frac{z^n}{n}\bigg)\]
  with the key properties that they have a single zero at $z = 1$ and 
  satisfy $E_n(z) = 1 + O(z^{n+1})$ around the origin.
\<close>
definition weierstrass_factor :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "weierstrass_factor n z = (1 - z) * exp (\<Sum>k=1..n. z ^ k / of_nat k)"

lemma weierstrass_factor_continuous_on [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>z. weierstrass_factor n (f z))"
  by (auto simp: weierstrass_factor_def intro!: continuous_intros)

lemma weierstrass_factor_holomorphic [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>z. weierstrass_factor n (f z)) holomorphic_on A"
  by (auto simp: weierstrass_factor_def intro!: holomorphic_intros)

lemma weierstrass_factor_analytic [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>z. weierstrass_factor n (f z)) analytic_on A"
  by (auto simp: weierstrass_factor_def intro!: analytic_intros)

lemma weierstrass_factor_0 [simp]: "weierstrass_factor n 0 = 1"
  by (auto simp: weierstrass_factor_def power_0_left)

lemma weierstrass_factor_1 [simp]: "weierstrass_factor n 1 = 0"
  by (simp add: weierstrass_factor_def)

lemma weierstrass_factor_eq_0_iff [simp]: "weierstrass_factor n z = 0 \<longleftrightarrow> z = 1"
  by (simp add: weierstrass_factor_def)

lemma zorder_weierstrass_factor [simp]: "zorder (weierstrass_factor n) 1 = 1"
proof (rule zorder_eqI)
  show "(\<lambda>z. -exp (\<Sum>k=1..n. z ^ k / of_nat k)) holomorphic_on UNIV"
    by (intro holomorphic_intros) auto
qed (auto simp: weierstrass_factor_def algebra_simps)  

lemma
  fixes z :: "'a :: {banach, real_normed_field}"
  assumes "norm z \<le> 1 / 2"
  shows   norm_exp_bounds_lemma: "norm (exp z - 1 - z) \<le> norm z / 2"
    and   norm_exp_bounds: "norm (exp z - 1) \<ge> 1 / 2 * norm z"
                           "norm (exp z - 1) \<le> 3 / 2 * norm z"
proof -
  show *: "norm (exp z - 1 - z) \<le> norm z / 2"
  proof (cases "z = 0")
    case False
    have sums: "(\<lambda>k. z ^ (k + 2) /\<^sub>R fact (k + 2)) sums (exp z - (\<Sum>k<2. z ^ k /\<^sub>R fact k))"
      by (intro sums_split_initial_segment exp_converges)
  
    have "summable (\<lambda>k. norm z ^ (k + 2) /\<^sub>R fact (k + 2))"
      using summable_norm_exp[of z]
      by (intro summable_norm summable_ignore_initial_segment)
         (auto simp: norm_power norm_divide divide_simps)
    also have "?this \<longleftrightarrow> summable (\<lambda>k. norm z ^ 2 * (norm z ^ k / fact (k +2)))"
      by (simp add: power_add mult_ac divide_simps power2_eq_square del: of_nat_Suc of_nat_add)
    also have "\<dots> \<longleftrightarrow> summable (\<lambda>k. norm z ^ k / fact (k + 2))"
      by (subst summable_cmult_iff) (use \<open>z \<noteq> 0\<close> in auto)
    finally have summable: "summable (\<lambda>k. norm z ^ k / fact (k + 2))" .
  
    have "exp z - 1 - z = (\<Sum>k. z ^ (k + 2) / fact (k + 2))"
      using sums by (simp add: sums_iff scaleR_conv_of_real divide_simps eval_nat_numeral)
    also have "norm \<dots> \<le> (\<Sum>k. norm (z ^ (k + 2) / fact (k + 2)))"
      using summable_norm_exp[of z]
      by (intro summable_norm summable_ignore_initial_segment)
         (auto simp: norm_power norm_divide divide_simps)
    also have "\<dots> = (\<Sum>k. norm z ^ 2 * (norm z ^ k / fact (k + 2)))"
      by (simp add: power_add norm_power norm_divide mult_ac norm_mult power2_eq_square del: of_nat_Suc)
    also have "\<dots> = norm z ^ 2 * (\<Sum>k. norm z ^ k / fact (k + 2))"
      using summable by (rule suminf_mult)
    also have "\<dots> \<le> norm z ^ 2 * (1 / (1 - norm z) / 2)"
    proof (intro mult_left_mono, rule sums_le)
      show "(\<lambda>k. norm z ^ k / fact (k + 2)) sums (\<Sum>k. norm z ^ k / fact (k + 2))"
        using summable by blast
      show "(\<lambda>k. norm z ^ k / 2) sums (1 / (1 - norm z) / 2)"
        using assms by (intro geometric_sums sums_divide) auto
    next
      fix k :: nat
      have "norm z ^ k / fact (k + 2) \<le> norm z ^ k / fact 2"
        by (intro divide_left_mono fact_mono) auto
      thus "norm z ^ k / fact (k + 2) \<le> norm z ^ k / 2"
        by simp
    qed (auto simp: divide_simps)
    also have "\<dots> = norm z * (norm z / (1 - norm z)) / 2"
      by (simp add: power2_eq_square)
    also have "\<dots> \<le> norm z * ((1 / 2) / (1 - (1 / 2))) / 2"
      using assms by (intro mult_mono frac_le diff_mono) auto
    also have "\<dots> = norm z / 2"
      by simp
    finally show "norm (exp z - 1 - z) \<le> norm z / 2" .
  qed auto

  have "norm (exp z - 1) \<le> norm z + norm (exp z - 1 - z)"
    by (rule norm_triangle_sub)
  with * show "norm (exp z - 1) \<le> 3 / 2 * norm z"
    by simp

  have "norm z - norm (exp z - 1 - z) \<le> norm (exp z - 1)"
    using norm_triangle_ineq3[of "exp z - 1 - z" "-z"] by simp
  with * show "norm (exp z - 1) \<ge> 1 / 2 * norm z"
    by simp
qed 

lemma weierstrass_factor_bound:
  assumes "norm z \<le> 1 / 2"
  shows   "norm (weierstrass_factor n z - 1) \<le> 3 * norm z ^ Suc n"
proof (cases "n = 0 \<or> z = 0")
  case True
  thus ?thesis
  proof
    assume "n = 0"
    thus ?thesis by (auto simp: weierstrass_factor_def)
  qed auto
next
  case False
  with assms have "z \<noteq> 1" "n > 0" "z \<noteq> 0"
    by auto

  have "summable (\<lambda>k. cmod z ^ (k + Suc n) / real (k + Suc n))"
    using ln_series'[of "-norm z"] assms
    by (intro summable_norm summable_ignore_initial_segment)
       (simp_all add: sums_iff summable_minus_iff power_minus' norm_divide norm_power)
  also have "?this \<longleftrightarrow> summable (\<lambda>k. norm z ^ Suc n * (norm z ^ k / real (k + Suc n)))"
    by (simp add: power_add mult_ac)
  also have "\<dots> \<longleftrightarrow> summable (\<lambda>k. norm z ^ k / real (k + Suc n))"
    by (subst summable_cmult_iff) (use \<open>z \<noteq> 0\<close> in auto)
  finally have summable: "summable (\<lambda>k. norm z ^ k / real (k + Suc n))" .

  have "(\<lambda>k. z ^ k / of_nat k) sums - Ln (1 - z)"
    using sums_minus[OF Ln_series[of "-z"]] assms by (simp add: power_minus')
  hence "(\<lambda>k. z ^ (k + Suc n) / of_nat (k + Suc n)) sums (- Ln (1 - z) - (\<Sum>k<Suc n. z ^ k / of_nat k))"
    by (intro sums_split_initial_segment)
  also have "(\<Sum>k<Suc n. z ^ k / of_nat k) = (\<Sum>k=1..n. z ^ k / of_nat k)"
    by (intro sum.mono_neutral_right) auto
  finally have "norm (ln (1 - z) + (\<Sum>k=1..n. z ^ k / of_nat k)) =
                norm (\<Sum>k. z ^ (k + Suc n) / of_nat (k + Suc n))"
    by (simp add: sums_iff norm_uminus_minus)

  also have "\<dots> \<le> (\<Sum>k. norm (z ^ (k + Suc n) / of_nat (k + Suc n)))"
    using ln_series'[of "-norm z"] assms
    by (intro summable_norm summable_ignore_initial_segment)
       (simp_all add: sums_iff summable_minus_iff power_minus' norm_divide norm_power)
  also have "\<dots> = (\<Sum>k. norm z ^ Suc n * (norm z ^ k / real (k + Suc n)))"
    by (simp add: algebra_simps norm_mult norm_power norm_divide power_add del: of_nat_add of_nat_Suc)
  also have "\<dots> = norm z ^ Suc n * (\<Sum>k. norm z ^ k / real (k + Suc n))"
    by (intro suminf_mult summable)
  also have "\<dots> \<le> norm z ^ Suc n * (1 / (1 - norm z))"
  proof (intro mult_left_mono[OF sums_le])
    show "(\<lambda>k. norm z ^ k / real (k + Suc n)) sums (\<Sum>k. norm z ^ k / real (k + Suc n))"
      using summable by blast
    show "(\<lambda>k. norm z ^ k) sums (1 / (1 - norm z))"
      by (rule geometric_sums) (use assms in auto)
  qed (auto simp: field_simps)
  also have "norm z ^ Suc n * (1 / (1 - norm z)) \<le> norm z ^ Suc n * (1 / (1 - (1 / 2)))"
    using assms by (intro mult_mono power_mono divide_left_mono diff_mono mult_pos_pos) auto
  also have "\<dots> = 2 * norm z ^ Suc n"
    by simp
  finally have norm_le: "norm (ln (1 - z) + (\<Sum>k=1..n. z ^ k / of_nat k)) \<le> 2 * norm z ^ Suc n" .

  also have "\<dots> \<le> 2 * norm z ^ 2"
    using \<open>n > 0\<close> assms by (intro mult_left_mono power_decreasing) auto
  also have "\<dots> \<le> 2 * (1 / 2) ^ 2"
    by (intro mult_left_mono assms power_mono) auto
  finally have norm_le': "norm (ln (1 - z) + (\<Sum>k=1..n. z ^ k / of_nat k)) \<le> 1 / 2"
    by (simp add: power2_eq_square)

  have "weierstrass_factor n z = exp (ln (1 - z) + (\<Sum>k=1..n. z ^ k / of_nat k))"
    using \<open>z \<noteq> 1\<close> by (simp add: exp_add weierstrass_factor_def)
  also have "norm (\<dots> - 1) \<le> (3 / 2) * norm (ln (1 - z) + (\<Sum>k=1..n. z ^ k / of_nat k))"
    by (intro norm_exp_bounds norm_le')
  also have "\<dots> \<le> (3 / 2) * (2 * norm z ^ Suc n)"
    by (intro mult_left_mono norm_le) auto
  finally show ?thesis
    by simp
qed


subsection \<open>Infinite products of elementary factors\<close>

text \<open>
  We now show that the elementary factors can be used to construct an entire function
  with its zeros at a certain set of points (given by a sequence of non-zero numbers $a_n$ with no
  accumulation point).
\<close>

locale weierstrass_product =
  fixes a :: "nat \<Rightarrow> complex"
  fixes p :: "nat \<Rightarrow> nat"
  assumes a_nonzero: "\<And>n. a n \<noteq> 0"
  assumes filterlim_a: "filterlim a at_infinity at_top"
  assumes summable_a_p: "\<And>r. r > 0 \<Longrightarrow> summable (\<lambda>n. (r / norm (a n)) ^ Suc (p n))"
begin

definition f :: "complex \<Rightarrow> complex" where
  "f z = (\<Prod>n. weierstrass_factor (p n) (z / a n))"

lemma abs_convergent: "abs_convergent_prod (\<lambda>n. weierstrass_factor (p n) (z / a n))"
  unfolding abs_convergent_prod_conv_summable
proof (rule summable_comparison_test_ev)
  have "eventually (\<lambda>n. norm (a n) > 2 * norm z) at_top"
    using filterlim_a by (metis filterlim_at_infinity_imp_norm_at_top filterlim_at_top_dense)
  thus "eventually (\<lambda>n. norm (norm (weierstrass_factor (p n) (z / a n) - 1)) \<le>
          3 * norm (z / a n) ^ Suc (p n)) at_top"
  proof eventually_elim
    case (elim n)
    hence "norm (z / a n) \<le> 1 / 2"
      by (auto simp: norm_divide divide_simps)
    thus ?case using weierstrass_factor_bound[of "z / a n" "p n"]
      by simp
  qed
next
  show "summable (\<lambda>n. 3 * norm (z / a n) ^ Suc (p n))"
    using summable_mult[OF summable_a_p[of "norm z"], of 3]
    by (cases "z = 0") (auto simp: norm_divide)
qed

lemma convergent: "convergent_prod (\<lambda>n. weierstrass_factor (p n) (z / a n))"
  using abs_convergent[of z] abs_convergent_prod_imp_convergent_prod by blast

lemma has_prod: "(\<lambda>n. weierstrass_factor (p n) (z / a n)) has_prod f z"
  using convergent[of z] unfolding f_def by auto

lemma finite_occs_a: "finite (a -` {z})"
proof -
  have "eventually (\<lambda>n. norm (a n) > norm z) at_top"
    using filterlim_a by (metis filterlim_at_infinity_imp_norm_at_top filterlim_at_top_dense)
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm (a n) > norm z"
    by (auto simp: eventually_at_top_linorder)
  have "n < N" if "n \<in> a -` {z}" for n
    using N[of n] that by (cases "n < N") auto
  hence "a -` {z} \<subseteq> {..<N}" "finite {..<N}"
    by auto
  thus ?thesis
    using finite_subset by blast
qed

context
  fixes P
  defines "P \<equiv> (\<lambda>N z. \<Prod>n<N. weierstrass_factor (p n) (z / a n))"
begin 

lemma uniformly_convergent:
  assumes "R > 0"
  shows   "uniformly_convergent_on (cball 0 R) P"
  unfolding P_def
proof (rule uniformly_convergent_on_prod')
  show "uniformly_convergent_on (cball 0 R) (\<lambda>N z. \<Sum>n<N. norm (weierstrass_factor (p n) (z / a n) - 1))"
  proof (rule Weierstrass_m_test'_ev)
    have "eventually (\<lambda>n. norm (a n) \<ge> 2 * R) sequentially"
      using filterlim_a by (metis filterlim_at_infinity_imp_norm_at_top filterlim_at_top)
    thus "\<forall>\<^sub>F n in sequentially. \<forall>z\<in>cball 0 R. norm (norm (weierstrass_factor (p n) (z / a n) - 1)) \<le>
            3 * (R / norm (a n)) ^ Suc (p n)"
    proof eventually_elim
      case (elim n)
      show ?case
      proof safe
        fix z :: complex assume z: "z \<in> cball 0 R"
        have "2 * norm z \<le> 2 * R"
          using z by auto
        also have "\<dots> \<le> norm (a n)"
          using elim by simp
        finally have "norm (a n) \<ge> 2 * norm z" .
        hence "norm (weierstrass_factor (p n) (z / a n) - 1) \<le> 3 * norm (z / a n) ^ Suc (p n)"
          by (intro weierstrass_factor_bound) (auto simp: norm_divide divide_simps)
        also have "\<dots> = 3 * (norm z / norm (a n)) ^ Suc (p n)"
          by (simp add: norm_divide)
        also have "\<dots> \<le> 3 * (R / norm (a n)) ^ Suc (p n)"
          by (intro mult_left_mono power_mono divide_right_mono) (use z in auto)
        finally show "norm (norm (weierstrass_factor (p n) (z / a n) - 1)) \<le>
                        3 * (R / norm (a n)) ^ Suc (p n)" by simp
      qed
    qed
  next
    show "summable (\<lambda>n. 3 * (R / norm (a n)) ^ Suc (p n))"
      by (intro summable_mult summable_a_p assms)
  qed
qed (auto intro!: continuous_intros simp: a_nonzero)

lemma uniform_limit:
  assumes "R > 0"
  shows   "uniform_limit (cball 0 R) P f at_top"
proof -
  obtain g where g: "uniform_limit (cball 0 R) P g at_top"
    using uniformly_convergent[OF assms] by (auto simp: uniformly_convergent_on_def)
  also have "?this \<longleftrightarrow> uniform_limit (cball 0 R) P f at_top"
  proof (intro uniform_limit_cong)
    fix z :: complex assume "z \<in> cball 0 R"
    with g have "(\<lambda>n. P (Suc n) z) \<longlonglongrightarrow> g z"
      by (metis tendsto_uniform_limitI filterlim_sequentially_Suc)
    moreover have "(\<lambda>n. P (Suc n) z) \<longlonglongrightarrow> f z"
      using convergent_prod_LIMSEQ[OF convergent[of z]] unfolding P_def lessThan_Suc_atMost
      by (simp add: f_def)
    ultimately show "g z = f z"
      using tendsto_unique by force
  qed auto
  finally show ?thesis .
qed

lemma holomorphic [holomorphic_intros]: "f holomorphic_on A"
proof (rule holomorphic_on_subset)
  show "f holomorphic_on UNIV"
  proof (rule holomorphic_uniform_sequence)
    fix z :: complex
    have *: "uniform_limit (cball 0 (norm z + 1)) P f sequentially"
      by (rule uniform_limit) (auto intro: add_nonneg_pos)
    hence "uniform_limit (cball z 1) P f sequentially"
      by (rule uniform_limit_on_subset) (simp add: cball_subset_cball_iff)
    thus "\<exists>d>0. cball z d \<subseteq> UNIV \<and> uniform_limit (cball z d) P f sequentially"
      by (intro exI[of _ 1]) auto
  qed (auto intro!: holomorphic_intros simp: P_def)
qed auto

lemma analytic [analytic_intros]: "f analytic_on A"
  using holomorphic[of UNIV] analytic_on_holomorphic by blast

end


lemma zero: "f z = 0 \<longleftrightarrow> z \<in> range a"
  using has_prod_eq_0_iff[OF has_prod, of z] by (auto simp: a_nonzero)  

lemma not_islimpt_range_a: "\<not>z islimpt (range a)"
proof
  assume "z islimpt (range a)"
  then obtain r :: "nat \<Rightarrow> nat" where r: "strict_mono r" "(a \<circ> r) \<longlonglongrightarrow> z"
    using islimpt_range_imp_convergent_subsequence by metis
  moreover have "filterlim (a \<circ> r) at_infinity sequentially"
    unfolding o_def by (rule filterlim_compose[OF filterlim_a filterlim_subseq[OF r(1)]])
  ultimately show False
    by (meson not_tendsto_and_filterlim_at_infinity trivial_limit_sequentially)
qed

lemma isolated_zero:
  assumes "z \<in> range a"
  shows   "isolated_zero f z"
proof -
  have "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
    using not_islimpt_range_a[of z] by (auto simp: islimpt_iff_eventually zero)
  moreover have "f \<midarrow>z\<rightarrow> f z"
    by (intro isContD analytic_at_imp_isCont analytic)
  hence "f \<midarrow>z\<rightarrow> 0"
    using assms zero[of z] by auto
  ultimately show ?thesis
    by (auto simp: isolated_zero_def)
qed

lemma zorder: "zorder f z = card (a -` {z})"
proof -
  obtain N where N: "a -` {z} \<subseteq> {..N}"
    using finite_occs_a[of z] by (meson finite_nat_iff_bounded_le)
  define g where "g = (\<lambda>z n. weierstrass_factor (p n) (z / a n))"
  define h1 where "h1 = (\<lambda>w. (\<Prod>n\<in>{..N} - a-`{z}. g w n) * (\<Prod>n. g w (n + Suc N)))"
  define h2 where "h2 = (\<lambda>w. (\<Prod>n\<in>{..N} \<inter> a-`{z}. g w n))"

  have has_prod_h1': "(\<lambda>n. g w (n + Suc N)) has_prod (\<Prod>n. g w (n + Suc N))" for w
    unfolding g_def
    by (intro convergent_prod_has_prod convergent_prod_ignore_initial_segment convergent)

  have f_eq: "f w = h1 w * h2 w" for w
  proof -
    have "f w = (\<Prod>n<Suc N. g w n) * (\<Prod>n. g w (n + Suc N))"
    proof (rule has_prod_unique2)
      show "(\<lambda>n. g w n) has_prod ((\<Prod>n<Suc N. g w n) * (\<Prod>n. g w (n + Suc N)))"
        unfolding g_def by (intro has_prod_ignore_initial_segment' convergent)
      show "g w has_prod f w"
        unfolding g_def by (rule has_prod)
    qed 
    also have "{..<Suc N} = ({..N} - a-`{z}) \<union> ({..N} \<inter> a-`{z})"
      by auto
    also have "(\<Prod>k\<in>\<dots>. g w k) = (\<Prod>k\<in>{..N} - a-`{z}. g w k) * (\<Prod>k\<in>{..N} \<inter> a-`{z}. g w k)"
      by (intro prod.union_disjoint) auto
    finally show ?thesis
      by (simp add: h1_def h2_def mult_ac)
  qed    

  have ana_h1: "h1 analytic_on {z}"
  proof -
    interpret h1: weierstrass_product "\<lambda>n. a (n + Suc N)" "\<lambda>n. p (n + Suc N)"
    proof
      have "filterlim (\<lambda>n. n + Suc N) at_top at_top"
        by (rule filterlim_add_const_nat_at_top)
      thus "filterlim (\<lambda>n. a (n + Suc N)) at_infinity at_top"
        by (intro filterlim_compose[OF filterlim_a])
      show "summable (\<lambda>n. (r / cmod (a (n + Suc N))) ^ Suc (p (n + Suc N)))" if "r > 0" for r
        by (intro summable_ignore_initial_segment summable_a_p that)
    qed (auto simp: a_nonzero)

    show ?thesis using h1.analytic
      unfolding h1_def g_def h1.f_def by (intro analytic_intros) (auto simp: a_nonzero)
  qed

  have ana_h2: "h2 analytic_on {z}"
    unfolding h2_def g_def by (intro analytic_intros) (auto simp: a_nonzero)

  have "zorder f z = zorder (\<lambda>w. h1 w * h2 w) z"
    by (simp add: f_eq [abs_def])
  also have "\<dots> = zorder h1 z + zorder h2 z"
  proof (rule zorder_times_analytic)
    have "eventually (\<lambda>w. f w \<noteq> 0) (at z)"
      using not_islimpt_range_a[of z] by (auto simp: islimpt_conv_frequently_at frequently_def zero)
    thus "eventually (\<lambda>w. h1 w * h2 w \<noteq> 0) (at z)"
      by (simp add: f_eq)
  qed fact+
  also have "zorder h2 z = (\<Sum>n\<in>{..N} \<inter> a -` {z}. zorder (\<lambda>w. g w n) z)"
    unfolding h2_def
    by (intro zorder_prod_analytic)
       (auto simp: a_nonzero g_def eventually_at_filter intro!: analytic_intros)
  also have "h1 z \<noteq> 0" using N has_prod_eq_0_iff[OF has_prod_h1'[of z]]
    by (auto simp: h1_def g_def)
  hence "zorder h1 z = 0"
    by (intro zorder_eq_0I ana_h1)
  also have "(\<Sum>n\<in>{..N} \<inter> a -` {z}. zorder (\<lambda>w. g w n) z) = (\<Sum>n\<in>{..N} \<inter> a -` {z}. 1)"
  proof (intro sum.cong refl)
    fix n :: nat
    assume n: "n \<in> {..N} \<inter> a -` {z}"
    have "zorder (\<lambda>w. weierstrass_factor (p n) (1 / a n * w)) z =
          zorder (weierstrass_factor (p n)) (1 / a n * z)"
      using a_nonzero[of n] eventually_neq_at_within[of 1 "z / a n" UNIV]
      by (intro zorder_scale analytic_intros analytic_on_imp_meromorphic_on) auto
    hence "zorder (\<lambda>w. g w n) z = zorder (weierstrass_factor (p n)) 1"
      using n a_nonzero[of n] by (auto simp: g_def)
    thus "zorder (\<lambda>w. g w n) z = 1"
      by simp
  qed
  also have "\<dots> = card ({..N} \<inter> a -` {z})"
    by simp
  also have "{..N} \<inter> a -` {z} = a -` {z}"
    using N by blast
  finally show ?thesis
    by simp
qed

end (* weierstrass_product *)


text \<open>
  The following locale is the most common case of $p(n) = n$.
\<close>
locale weierstrass_product' =
  fixes a :: "nat \<Rightarrow> complex"
  assumes a_nonzero: "\<And>n. a n \<noteq> 0"
  assumes filterlim_a: "filterlim a at_infinity at_top"
  assumes finite_occs_a': "\<And>z. z \<in> range a \<Longrightarrow> finite (a -` {z})"
begin

lemma finite_occs_a: "finite (a -` {z})"
proof (cases "z \<in> range a")
  case False
  hence "a -` {z} = {}"
    by auto
  thus ?thesis by simp
qed (use finite_occs_a'[of z] in auto)

sublocale weierstrass_product a "\<lambda>n. n"
proof
  fix r :: real assume r: "r > 0"
  show "summable (\<lambda>n. (r / norm (a n)) ^ Suc n)"
  proof (rule summable_comparison_test_ev)
    have "eventually (\<lambda>n. norm (a n) > 2 * r) at_top"
      using filterlim_a by (metis filterlim_at_infinity_imp_norm_at_top filterlim_at_top_dense)
    thus "eventually (\<lambda>n. norm ((r / norm (a n)) ^ Suc n) \<le> (1 / 2) ^ Suc n) at_top"
    proof eventually_elim
      case (elim n)
      have "norm ((r / norm (a n)) ^ Suc n) = (r / norm (a n)) ^ Suc n"
        using \<open>r > 0\<close> by (simp add: abs_mult)
      also have "\<dots> \<le> (1 / 2) ^ Suc n"
        using \<open>r > 0\<close> elim by (intro power_mono) (auto simp: divide_simps)
      finally show ?case .
    qed
  next
    show "summable (\<lambda>n. (1 / 2) ^ Suc n :: real)"
      unfolding summable_Suc_iff by (intro summable_geometric) auto
  qed
qed (use a_nonzero filterlim_a finite_occs_a in auto)

end (* weierstrass_product' *)



subsection \<open>Writing a quotient as an exponential\<close>

text \<open>
  If two holomorphic functions \<open>f\<close> and \<open>g\<close> on a simply connected domain have the same zeros with
  the same multiplicities, they can be written as $g(x) = e^{h(x)} f(x)$ for some holomorphic
  function $h(x)$.
\<close>
lemma holomorphic_zorder_factorization:
  assumes "g holomorphic_on A" "open A" "connected A"
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z = 0 \<longleftrightarrow> g z = 0"
          "\<And>z. z \<in> A \<Longrightarrow> zorder f z = zorder g z"
  obtains h where "h holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> h z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> g z = h z * f z"
proof (cases "\<exists>z\<in>A. g z \<noteq> 0")
  case False
  show ?thesis
    by (rule that[of "\<lambda>_. 1"]) (use False assms in auto)
next
  case True
  define F where "F = fps_expansion f"
  define G where "G = fps_expansion g"
  define c where "c = (\<lambda>z. fps_nth (G z) (subdegree (G z)) / fps_nth (F z) (subdegree (F z)))"
  define h where "h = (\<lambda>z. if f z = 0 then c z else g z / f z)"

  have ev_nonzero: "eventually (\<lambda>w. g w \<noteq> 0 \<and> w \<in> A) (at z)" if "z \<in> A" for z
  proof -
    from True obtain z0 where z0: "z0 \<in> A" "g z0 \<noteq> 0"
      by auto
    show ?thesis
      by (rule non_zero_neighbour_alt[where ?\<beta> = z0])
         (use assms that z0 in \<open>auto intro: simply_connected_imp_connected\<close>)
  qed

  have g_ana: "g analytic_on {z}" if "z \<in> A" for z
    using assms \<open>open A\<close> analytic_at that by blast
  have f_ana: "f analytic_on {z}" if "z \<in> A" for z
    using assms \<open>open A\<close> analytic_at that by blast

  have F: "(\<lambda>w. f (z + w)) has_fps_expansion F z" if "z \<in> A" for z
    unfolding F_def by (rule analytic_at_imp_has_fps_expansion[OF f_ana[OF that]])
  have G: "(\<lambda>w. g (z + w)) has_fps_expansion G z" if "z \<in> A" for z
    unfolding G_def by (rule analytic_at_imp_has_fps_expansion[OF g_ana[OF that]])

  have [simp]: "G z \<noteq> 0" if "z \<in> A" for z
  proof
    assume "G z = 0"
    hence "eventually (\<lambda>w. g w = 0) (at z)" using G[OF that]
      by (auto simp: has_fps_expansion_0_iff at_to_0' eventually_filtermap add_ac
                     eventually_at_filter nhds_to_0' elim: eventually_mono)
    hence "eventually (\<lambda>_. False) (at z)"
      using ev_nonzero[OF that] unfolding eventually_at_filter by eventually_elim auto
    thus False
      by simp
  qed
  have [simp]: "F z \<noteq> 0" if "z \<in> A" for z
  proof
    assume "F z = 0"
    hence "eventually (\<lambda>w. f w = 0) (at z)" using F[of z] that
      by (auto simp: has_fps_expansion_0_iff at_to_0' eventually_filtermap add_ac
                     eventually_at_filter nhds_to_0' elim: eventually_mono)
    hence "eventually (\<lambda>_. False) (at z)"
      using ev_nonzero[OF that] unfolding eventually_at_filter
      by eventually_elim (use assms in auto)
    thus False
      by simp
  qed
  have [simp]: "c z \<noteq> 0" if "z \<in> A" for z
    using that by (simp add: c_def)

  have h: "h analytic_on {z} \<and> h z \<noteq> 0" if "z \<in> A" for z
  proof -
    show ?thesis
    proof (cases "f z = 0")
      case False
      from False that have "(\<lambda>z. g z / f z) analytic_on {z}"
        by (intro analytic_intros g_ana f_ana) auto
      also have "?this \<longleftrightarrow> h analytic_on {z}"
      proof (rule analytic_at_cong)
        have "eventually (\<lambda>w. f w \<noteq> 0) (nhds z)"
          using ev_nonzero[OF \<open>z \<in> A\<close>] unfolding eventually_at_filter
          by eventually_elim (use False \<open>z \<in> A\<close> assms in auto)
        thus "eventually (\<lambda>z. g z / f z = h z) (nhds z)"
          by eventually_elim (auto simp: h_def)
      qed auto
      finally have "h analytic_on {z}" .
      moreover have "h z \<noteq> 0"
        using that assms by (simp add: h_def)
      ultimately show ?thesis by blast
    next
      case True
      with that have z: "z \<in> A" "f z = 0"
        by auto
      have "zorder f z = int (subdegree (F z))"
        using F by (rule has_fps_expansion_zorder) (use z in auto)
      also have "zorder f z = zorder g z"
        using z assms by auto
      also have "zorder g z = subdegree (G z)"
        using G by (rule has_fps_expansion_zorder) (use z in auto)
      finally have subdegree_eq: "subdegree (F z) = subdegree (G z)"
        by simp
  
      have "(\<lambda>w. if w = 0 then c z else g (z + w) / f (z + w)) has_fps_expansion G z / F z" (is ?P)
        using subdegree_eq z by (intro has_fps_expansion_divide F G) (auto simp: c_def)
      also have "?this \<longleftrightarrow> (\<lambda>w. h (z + w)) has_fps_expansion G z / F z"
      proof (intro has_fps_expansion_cong)
        have "eventually (\<lambda>w. w \<noteq> z \<longrightarrow> f w \<noteq> 0) (nhds z)"
          using ev_nonzero[OF \<open>z \<in> A\<close>] unfolding eventually_at_filter
          by eventually_elim (use \<open>z \<in> A\<close> assms in auto)
        hence "eventually (\<lambda>w. w \<noteq> 0 \<longrightarrow> f (z + w) \<noteq> 0) (nhds 0)"
          by (simp add: nhds_to_0' eventually_filtermap)
        thus "eventually (\<lambda>w. (if w = 0 then c z else g (z + w) / f (z + w)) = h (z + w)) (nhds 0)"
          unfolding h_def by eventually_elim (use z in \<open>auto simp: c_def h_def\<close>)
      qed auto
      finally have "h analytic_on {z}"
        using has_fps_expansion_imp_analytic by blast
      moreover have "h z \<noteq> 0"
        using that z by (auto simp: h_def c_def)
      ultimately show ?thesis by blast
    qed
  qed

  from h have h_ana: "h analytic_on A" and h_nz: "\<forall>z\<in>A. h z \<noteq> 0"
    using analytic_on_analytic_at by blast+
  moreover have "g z = h z * f z" if "z \<in> A" for z
    using assms that by (auto simp: h_def)
  ultimately show ?thesis
    using \<open>open A\<close> by (intro that[of h]) (auto simp: analytic_on_open)
qed


subsection \<open>Constructing the sequence of zeros\<close>

text \<open>
  The form of the Weierstra\ss\ Factorisation Theorem that we derived above requires
  an explicit sequence of the zeros that tends to infinity. We will now show that under
  mild conditions, such a sequence always exists.

  More precisely: if \<open>A\<close> is an infinite closed set that is sparse in the sense that its
  intersection with any compact set is finite, then there exists an injective sequence \<open>f\<close>
  enumerating the values of \<open>A\<close> in ascending order by absolute value, and \<open>f\<close> tends to infinity
  for \<open>n \<rightarrow> \<infinity>\<close>.
\<close>
lemma sequence_of_sparse_set_exists:
  fixes A :: "complex set"
  assumes "infinite A" "closed A" "\<And>r. r \<ge> 0 \<Longrightarrow> finite (A \<inter> cball 0 r)"
  obtains f :: "nat \<Rightarrow> complex"
    where "mono (norm \<circ> f)" "inj f" "range f = A" "filterlim f at_infinity at_top"
proof -
  have "\<exists>f::nat \<Rightarrow> complex. \<forall>n.
         f n \<in> A \<and>
         f n \<notin> f ` {..<n} \<and>
         {z\<in>A. norm z < norm (f n)} \<subseteq> f ` {..<n} \<and>
         (\<forall>k<n. norm (f k) \<le> norm (f n))"
  proof (rule dependent_wf_choice[OF wf], goal_cases)
    case (1 f g n r)
    thus ?case by auto
  next
    case (2 n f)
    have f: "f k \<in> A" "{z \<in> A. norm z < norm (f k)} \<subseteq> f ` {..<k}" "\<forall>k'<k. cmod (f k') \<le> cmod (f k)"
      if "k < n" for k
      using 2[of k] that by simp_all
  
    have "infinite (A - f ` {..<n})"
      using assms(1) by (intro Diff_infinite_finite) auto
    then obtain z0 where z0: "z0 \<in> A - f ` {..<n}"
      by (meson finite.intros(1) finite_subset subsetI)
    have "finite (A \<inter> cball 0 (norm z0))"
      by (intro assms(3)) auto
    hence "finite (A \<inter> cball 0 (norm z0) - f ` {..<n})"
      using finite_subset by blast
    moreover from z0 have "A \<inter> cball 0 (norm z0) - f ` {..<n} \<noteq> {}"
      by auto
    ultimately obtain z where "is_arg_min norm (\<lambda>z. z \<in> A \<inter> cball 0 (norm z0) - f ` {..<n}) z"
      using ex_is_arg_min_if_finite by blast
    hence z: "z \<in> A" "norm z \<le> norm z0" "z \<notin> f ` {..<n}"
             "\<And>w. w \<in> A \<Longrightarrow> norm w \<le> norm z0 \<Longrightarrow> w \<notin> f ` {..<n} \<Longrightarrow> norm w \<ge> norm z"
      by (auto simp: is_arg_min_def)
  
    show ?case
    proof (rule exI[of _ z], safe)
      fix w assume w: "w \<in> A" "norm w < norm z"
      with z(4)[of w] z w show "w \<in> f ` {..<n}"
        by linarith
    next
      fix k assume k: "k < n"
      show "norm (f k) \<le> norm z"
        using f(2)[of k] z(1,3) k by auto
    qed (use z in auto)
  qed
  then obtain f :: "nat \<Rightarrow> complex" where f:
    "\<And>n. f n \<in> A"
    "\<And>n. f n \<notin> f ` {..<n}"
    "\<And>n. {z\<in>A. norm z < norm (f n)} \<subseteq> f ` {..<n}"
    "\<And>k n. k < n \<Longrightarrow> norm (f k) \<le> norm (f n)"
    by meson
  from f(2) have f_neq: "f n \<noteq> f k" if "k < n" for k n
    using that by blast

  have inj: "inj f"
  proof (rule injI)
    fix m n :: nat
    assume "f m = f n"
    thus "m = n"
      using f_neq[of m n] f_neq[of n m] by (cases m n rule: linorder_cases) auto
  qed      

  have range: "range f = A"
  proof safe
    fix z assume z: "z \<in> A"
    show "z \<in> range f"
    proof (rule ccontr)
      assume "z \<notin> range f"
      hence "norm (f n) \<le> norm z" for n
        using f(3)[of n] z by auto
      hence "range f \<subseteq> A \<inter> cball 0 (norm z)"
        using f(1) by auto
      moreover have "finite (A \<inter> cball 0 (norm z))"
        by (intro assms) auto
      ultimately have "finite (range f)"
        using finite_subset by blast
      moreover have "infinite (range f)"
        using inj by (subst finite_image_iff) auto
      ultimately show False by contradiction
    qed
  qed (use f(1) in auto)

  have mono: "mono (norm \<circ> f)"
  proof (rule monoI, unfold o_def)
    fix m n :: nat
    assume "m \<le> n"
    thus "norm (f m) \<le> norm (f n)"
      using f(4)[of m n] by (cases "m < n") auto
  qed

  have "\<not>bounded A"
  proof
    assume "bounded A"
    hence "bdd_above (norm ` A)"
      by (meson bdd_above_norm)
    hence "norm z \<le> Sup (norm ` A)" if "z \<in> A" for z
      using that by (meson cSUP_upper)
    hence "A \<subseteq> cball 0 (Sup (norm ` A))"
      by auto
    also have "\<dots> \<subseteq> cball 0 (max 1 (Sup (norm ` A)))"
      by auto
    finally have "A \<subseteq> A \<inter> cball 0 (max 1 (Sup (norm ` A)))"
      by blast
    moreover have "finite (A \<inter> cball 0 (max 1 (Sup (norm ` A))))"
      by (intro assms) auto
    ultimately have "finite A"
      using finite_subset by blast
    hence "finite (range f)"
      by (simp add: range)
    thus False
      using inj by (subst (asm) finite_image_iff) auto
  qed

  have lim: "filterlim f at_infinity at_top"
    unfolding filterlim_at_infinity_conv_norm_at_top filterlim_at_top
  proof
    fix C :: real
    from \<open>\<not>bounded A\<close> obtain z where "z \<in> A" "norm z > C"
      unfolding bounded_iff by (auto simp: not_le)
    obtain n where [simp]: "z = f n"
      using range \<open>z \<in> A\<close> by auto
    show "eventually (\<lambda>n. norm (f n) \<ge> C) at_top"
      using eventually_ge_at_top[of n]
    proof eventually_elim
      case (elim k)
      have "C \<le> norm (f n)"
        using \<open>norm z > C\<close> by simp
      also have "\<dots> \<le> norm (f k)"
        using monoD[OF \<open>mono (norm \<circ> f)\<close>, of n k] elim by auto
      finally show ?case .
    qed
  qed

  show ?thesis
    by (intro that[of f] inj range mono lim)
qed

(* TODO: of general interest? *)
lemma strict_mono_sequence_partition:
  assumes "strict_mono (f :: nat \<Rightarrow> 'a :: {linorder, no_top})"
  assumes "x \<ge> f 0"
  assumes "filterlim f at_top at_top"
  shows   "\<exists>k. x \<in> {f k..<f (Suc k)}"
proof -
  define k where "k = (LEAST k. f (Suc k) > x)"
  {
    obtain n where "x \<le> f n"
      using assms by (auto simp: filterlim_at_top eventually_at_top_linorder)
    also have "f n < f (Suc n)"
      using assms by (auto simp: strict_mono_Suc_iff)
    finally have "\<exists>n. f (Suc n) > x" by auto
  }
  from LeastI_ex[OF this] have "x < f (Suc k)"
    by (simp add: k_def)
  moreover have "f k \<le> x"
  proof (cases k)
    case (Suc k')
    have "k \<le> k'" if "f (Suc k') > x"
      using that unfolding k_def by (rule Least_le)
    with Suc show "f k \<le> x" by (cases "f k \<le> x") (auto simp: not_le)
  qed (use assms in auto)
  ultimately show ?thesis by auto
qed

(* TODO: of general interest? *)
lemma strict_mono_sequence_partition':
  assumes "strict_mono (f :: nat \<Rightarrow> 'a :: {linorder, no_top})"
  assumes "x \<ge> f 0"
  assumes "filterlim f at_top at_top"
  shows   "\<exists>!k. x \<in> {f k..<f (Suc k)}"
proof (rule ex_ex1I)
  show "\<exists>k. x \<in> {f k..<f (Suc k)}"
    using strict_mono_sequence_partition[OF assms] .
  fix k1 k2 assume "x \<in> {f k1..<f (Suc k1)}" "x \<in> {f k2..<f (Suc k2)}"
  thus "k1 = k2"
  proof (induction k1 k2 rule: linorder_wlog)
    case (le k1 k2)
    hence "f k2 < f (Suc k1)"
      by auto
    hence "k2 < Suc k1"
      using assms(1) strict_mono_less by blast
    with le show "k1 = k2"
      by linarith
  qed auto
qed

lemma sequence_of_sparse_set_exists':
  fixes A :: "complex set" and c :: "complex \<Rightarrow> nat"
  assumes "infinite A" "closed A" "\<And>r. r \<ge> 0 \<Longrightarrow> finite (A \<inter> cball 0 r)"
  assumes c_pos: "\<And>x. x \<in> A \<Longrightarrow> c x > 0"
  obtains f :: "nat \<Rightarrow> complex" where
    "mono (norm \<circ> f)" "range f = A" "filterlim f at_infinity at_top"
    "\<And>z. z \<in> A \<Longrightarrow> finite (f -` {z}) \<and> card (f -` {z}) = c z"
proof -
  obtain f :: "nat \<Rightarrow> complex" where f:
    "mono (norm \<circ> f)" "inj f" "range f = A" "filterlim f at_infinity at_top"
    using assms sequence_of_sparse_set_exists by blast
  have f_eq_iff [simp]: "f m = f n \<longleftrightarrow> m = n" for m n
    using \<open>inj f\<close> by (auto simp: inj_def)

  define h :: "nat \<Rightarrow> nat" where "h = (\<lambda>n. \<Sum>k<n. c (f k))"

  have [simp]: "h 0 = 0"
    by (simp add: h_def)
  have h_ge: "h n \<ge> n" for n
  proof -
    have "h n \<ge> (\<Sum>k<n. 1)"
      unfolding h_def by (intro sum_mono) (use c_pos f in \<open>auto simp: Suc_le_eq\<close>)
    thus ?thesis by simp
  qed

  have "strict_mono h"
    unfolding strict_mono_Suc_iff using f by (auto simp: h_def c_pos)
  moreover from this have "filterlim h at_top at_top"
    using filterlim_subseq by blast
  ultimately have Ex1: "\<exists>!k. n \<in> {h k..<h (Suc k)}" for n
    by (intro strict_mono_sequence_partition') auto

  define g :: "nat \<Rightarrow> nat" where "g = (\<lambda>n. THE k. n \<in> {h k..<h (Suc k)})"
  have g: "n \<in> {h (g n)..<h (Suc (g n))}" for n
    using theI'[OF Ex1[of n]] by (simp add: g_def)
  have g_eqI: "g n = k" if "n \<in> {h k..<h (Suc k)}" for n k
    using the1_equality[OF Ex1 that] by (simp add: g_def)
  have g_h: "g (h n) = n" for n
    by (rule g_eqI) (auto intro: strict_monoD[OF \<open>strict_mono h\<close>])

  have "mono g"
    unfolding incseq_Suc_iff
  proof safe
    fix n :: nat
    have "h (g n) + 1 \<le> Suc n"
      using g[of n] by auto
    also have "Suc n < h (Suc (g (Suc n)))"
      using g[of "Suc n"] by auto
    finally show "g n \<le> g (Suc n)"
      by (metis \<open>strict_mono h\<close> add_lessD1 less_Suc_eq_le strict_mono_less)
  qed

  have "filterlim g at_top at_top"
    unfolding filterlim_at_top
  proof
    fix n :: nat
    show "eventually (\<lambda>m. g m \<ge> n) at_top"
      using eventually_ge_at_top[of "h n"]
    proof eventually_elim
      case (elim m)
      have "n \<le> g (h n)"
        by (simp add: g_h)
      also have "g (h n) \<le> g m"
        by (intro monoD[OF \<open>mono g\<close>] elim)
      finally show ?case .
    qed
  qed

  have vimage: "(f \<circ> g) -` {f n} = {h n..<h (Suc n)}" for n
    using g by (auto intro!: g_eqI)

  show ?thesis
  proof (rule that[of "f \<circ> g"])
    have "incseq (\<lambda>n. (norm \<circ> f) (g n))"
      by (intro monoI monoD[OF f(1)] monoD[OF \<open>incseq g\<close>])
    thus "incseq (norm \<circ> (f \<circ> g))"
      by (simp add: o_def)
  next
    have "range (f \<circ> g) \<subseteq> A"
      using f(3) by auto
    moreover have "A \<subseteq> range (f \<circ> g)"
    proof
      fix z assume "z \<in> A"
      then obtain n where [simp]: "z = f n"
        using f(3) by auto
      have "f (g (h n)) \<in> range (f \<circ> g)"
        unfolding o_def by blast
      thus "z \<in> range (f \<circ> g)"
        by (simp add: g_h)
    qed
    ultimately show "range (f \<circ> g) = A" by blast
  next
    fix z assume "z \<in> A"
    then obtain n where [simp]: "z = f n"
      using f(3) by auto
    have "finite {h n..<h (Suc n)}"
      by auto
    moreover have "card {h n..<h (Suc n)} = c z"
      by (simp add: h_def)
    ultimately show "finite ((f \<circ> g) -` {z}) \<and> card ((f \<circ> g) -` {z}) = c z"
      using vimage[of n] by simp
  next
    show "filterlim (f \<circ> g) at_infinity at_top"
      unfolding o_def by (rule filterlim_compose[OF f(4) \<open>filterlim g at_top at_top\<close>])
  qed
qed

subsection \<open>The factorisation theorem for holomorphic functions\<close>

text \<open>
  If \<open>g\<close> is a holomorphic function on an open connected domain whose zeros do not
  have an accumulation point on the frontier of \<open>A\<close>, then we can write \<open>g\<close> as a product
  of a function \<open>h\<close> holomorphic on \<open>A\<close> and an entire function \<open>f\<close> such that \<open>h\<close> is non-zero
  everywhere in \<open>A\<close> and the zeros of \<open>f\<close> are precisely the zeros of \<open>A\<close> with the same multiplicity.

  In other words, we can get rid of all the zeros of \<open>g\<close> by dividing it with a suitable
  entire function \<open>f\<close>.
\<close>
theorem weierstrass_factorization:
  assumes "g holomorphic_on A" "open A" "connected A" 
  assumes "\<And>z. z \<in> frontier A \<Longrightarrow> \<not>z islimpt {w\<in>A. g w = 0}"
  obtains h f where
    "h holomorphic_on A" "f holomorphic_on UNIV"
    "\<forall>z. f z = 0 \<longleftrightarrow> (\<forall>z\<in>A. g z = 0) \<or> (z \<in> A \<and> g z = 0)"
    "\<forall>z\<in>A. zorder f z = zorder g z"
    "\<forall>z\<in>A. h z \<noteq> 0"
    "\<forall>z\<in>A. g z = h z * f z"
proof (cases "\<forall>z\<in>A. g z = 0")
  case True
  show ?thesis
  proof (rule that[of "\<lambda>_. 1" "\<lambda>_. 0"]; (intro ballI allI impI)?)
    fix z assume z: "z \<in> A"
    have ev: "eventually (\<lambda>w. w \<in> A) (at z)"
      using z assms by (intro eventually_at_in_open') auto
    show "zorder (\<lambda>_::complex. 0 :: complex) z = zorder g z"
      by (intro zorder_cong eventually_mono[OF ev] refl) (use True in auto)
  qed (use assms True in auto)
next
  case not_identically_zero: False
  define Z where "Z = {z\<in>A. g z = 0}"
  have freq_nz: "frequently (\<lambda>z. g z \<noteq> 0) (at z)" if "z \<in> A" for z
  proof -
    have "\<forall>\<^sub>F w in at z. g w \<noteq> 0 \<and> w \<in> A"
      using non_zero_neighbour_alt[OF assms(1,2,3) that(1)] not_identically_zero by auto
    hence  "\<forall>\<^sub>F w in at z. g w \<noteq> 0"
      by eventually_elim auto
    thus ?thesis
      using eventually_frequently by force
  qed

  have zorder_pos_iff: "zorder g z > 0 \<longleftrightarrow> g z = 0" if "z \<in> A" for z
    by (subst zorder_pos_iff[OF assms(1,2) that]) (use freq_nz[of z] that in auto)

  show ?thesis
  proof (cases "finite Z")
    case True
    define f where "f = (\<lambda>z. \<Prod>w\<in>Z. (z - w) powi (zorder g w))"

    have eq_zero_iff: "f z = 0 \<longleftrightarrow> z \<in> A \<and> g z = 0" for z
      using True local.zorder_pos_iff
      unfolding f_def Z_def by fastforce
    have zorder_eq: "zorder f z = zorder g z" if "z \<in> A" for z
    proof (cases "g z = 0")
      case False
      have "g analytic_on {z}"
        using that assms analytic_at by blast
      hence [simp]: "zorder g z = 0"
        using False by (intro zorder_eq_0I) auto
      moreover have "f analytic_on {z}"
        unfolding f_def by (auto intro!: analytic_intros)
      hence "zorder f z = 0"
        using False by (intro zorder_eq_0I) (auto simp: eq_zero_iff)
      ultimately show ?thesis
        by simp
    next
      case zero: True
      have "g analytic_on {z}"
        using that assms(1,2) analytic_at by blast
      hence "zorder g z \<ge> 0"
        using that by (intro zorder_ge_0 freq_nz) auto
      define f' where "f' = (\<lambda>z'. (\<Prod>w\<in>Z-{z}. (z' - w) powi (zorder g w)))"
      have "zorder (\<lambda>z'. (z' - z) powi (zorder g z) * f' z') z = zorder g z"
      proof (rule zorder_eqI)
        show "open (UNIV :: complex set)" "f' holomorphic_on UNIV" "z \<in> UNIV"
          using local.zorder_pos_iff
          by (fastforce intro!: holomorphic_intros simp: f'_def Z_def)+
        show "f' z \<noteq> 0"
          using True unfolding f'_def by (subst prod_zero_iff) auto
      qed (use \<open>zorder g z \<ge> 0\<close> in \<open>auto simp: powr_of_int\<close>)
      also have "(\<lambda>z'. (z' - z) powi (zorder g z) * f' z') = f"
      proof
        fix z' :: complex
        have "Z = insert z (Z - {z})"
          using that zero by (auto simp: Z_def)
        also have "(\<Prod>w\<in>\<dots>. (z' - w) powi (zorder g w)) = (z' - z) powi (zorder g z) * f' z'"
          using True by (subst prod.insert) (auto simp: f'_def)
        finally show "(z' - z) powi (zorder g z) * f' z' = f z'"
          by (simp add: f_def)
      qed
      finally show ?thesis .
    qed

    obtain h :: "complex \<Rightarrow> complex" where h:
       "h holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> h z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> g z = h z * f z"
    proof (rule holomorphic_zorder_factorization[OF assms(1-3)])
      show "f holomorphic_on A"
        using local.zorder_pos_iff
        unfolding f_def Z_def by (fastforce intro: holomorphic_intros)
      show "f z = 0 \<longleftrightarrow> g z = 0" if "z \<in> A" for z
        using that by (subst eq_zero_iff) auto
      show "zorder f z = zorder g z" if "z \<in> A" for z
        by (rule zorder_eq) fact
    qed metis

    show ?thesis
    proof (rule that[of h f]; (intro ballI)?)
      show "h holomorphic_on A"
        by fact
      show "f holomorphic_on UNIV"
        using local.zorder_pos_iff
        unfolding f_def Z_def by (fastforce intro: holomorphic_intros)
    qed (use True not_identically_zero in \<open>auto simp: eq_zero_iff zorder_eq h(2) h(3)[symmetric]\<close>)

  next
    case False
    note infinite_zeroes = not_identically_zero False
    define c where "c = (\<lambda>z. nat (zorder g z))"

    have ev_nz: "eventually (\<lambda>w. g w \<noteq> 0) (at z)" if "z \<in> A" for z
    proof -
      from infinite_zeroes(1) obtain z0 where z0: "z0 \<in> A" "g z0 \<noteq> 0"
        by auto
      have "eventually (\<lambda>w. g w \<noteq> 0 \<and> w \<in> A) (at z)"
        by (rule non_zero_neighbour_alt[where ?\<beta> = z0]) (use assms z0 that in auto)
      thus ?thesis
        by eventually_elim auto
    qed

    have no_limpt_Z: "\<not>z islimpt Z" for z
    proof
      assume "z islimpt Z"
      show False
      proof (cases "z \<in> A")
        case False
        have "z islimpt A"
          by (rule islimpt_subset[OF \<open>z islimpt Z\<close>]) (auto simp: Z_def)
        hence "z \<in> closure A"
          by (simp add: closure_def)
        with \<open>z \<notin> A\<close> have "z \<in> frontier A"
          by (simp add: closure_Un_frontier)
        with assms and \<open>z islimpt Z\<close> show False
          by (auto simp: Z_def)
      next
        case True
        from True have "eventually (\<lambda>w. g w \<noteq> 0) (at z)"
          using ev_nz by blast
        hence "\<not>z islimpt Z"
          by (auto simp: islimpt_iff_eventually Z_def elim!: eventually_mono)
        with \<open>z islimpt Z\<close> show False by blast        
      qed
    qed
    have "closed Z"
      using no_limpt_Z unfolding closed_limpt by blast
   
    obtain a where a:
        "incseq (norm \<circ> a)" "range a = Z - {0}"
        "\<And>z. z \<in> Z - {0} \<Longrightarrow> finite (a -` {z}) \<and> card (a -` {z}) = c z"
        "filterlim a at_infinity at_top"
    proof (rule sequence_of_sparse_set_exists')
      show "infinite (Z - {0})"
        using infinite_zeroes(2) by auto
    next
      show "closed (Z - {0})" 
        unfolding closed_limpt using no_limpt_Z islimpt_subset by blast
    next
      show "finite ((Z - {0}) \<inter> cball 0 R)" if "R \<ge> 0" for R
      proof (rule ccontr)
        assume *: "infinite ((Z - {0}) \<inter> cball 0 R)"
        have "\<exists>z\<in>cball 0 R. z islimpt ((Z - {0}) \<inter> cball 0 R)"
          by (rule Heine_Borel_imp_Bolzano_Weierstrass) (use * in auto)
        then obtain z where "z islimpt ((Z - {0}) \<inter> cball 0 R)"
          by blast
        hence "z islimpt Z"
          using islimpt_subset by blast
        thus False
          using no_limpt_Z by blast
      qed
    next
      show "c z > 0" if "z \<in> Z - {0}" for z
        using zorder_pos_iff[of z] that by (auto simp: c_def Z_def)
    qed metis 

    interpret f: weierstrass_product' a
    proof
      show "a n \<noteq> 0" for n
        using a(2) by auto
      show "finite (a -` {z})" if "z \<in> range a" for z
        using a(3)[of z] a(2) that by simp
    qed fact+

    define m where "m = (if 0 \<in> A then nat (zorder g 0) else  0)"

    have zorder_eq: "zorder (\<lambda>z. z ^ m * f.f z) z = zorder g z" if "z \<in> A" for z
    proof (cases "g z = 0")
      case False
      have "g analytic_on {z}"
        using \<open>z \<in> A\<close> analytic_at assms by blast
      hence "zorder g z = 0"
        by (intro zorder_eq_0I False)
      have "z \<notin> range a"
        using False Z_def a(2) by blast
      hence "zorder (\<lambda>z. z ^ m * f.f z) z = 0"
        using False \<open>zorder g z = 0\<close>
        by (intro zorder_eq_0I analytic_intros) (auto simp: f.zero m_def)
      with \<open>zorder g z = 0\<close> show ?thesis
        by simp
    next
      case True
      define F where "F = fps_expansion f.f z"
      have "frequently (\<lambda>w. g w \<noteq> 0) (at z)"
        using ev_nz[OF that] eventually_frequently by force
      hence "zorder g z \<ge> 0"
        by (intro zorder_ge_0) (use assms that in \<open>auto simp: analytic_at\<close>)
      
      have ev: "eventually (\<lambda>z. z \<in> A) (nhds z)"
        using that assms by (intro eventually_nhds_in_open) auto
      have exp1: "(\<lambda>w. f.f (z + w)) has_fps_expansion F"
        unfolding F_def by (intro analytic_at_imp_has_fps_expansion[OF f.analytic])
      have exp2: "(\<lambda>w. (z + w) ^ m * f.f (z + w)) has_fps_expansion (fps_const z + fps_X) ^ m * F"
        by (intro fps_expansion_intros exp1)
      have [simp]: "F \<noteq> 0"
      proof
        assume "F = 0"
        hence "eventually (\<lambda>z. f.f z = 0) (nhds z)"
          using exp1 by (auto simp: has_fps_expansion_def nhds_to_0' eventually_filtermap)
        hence "eventually (\<lambda>z. g z = 0) (at z)"
          by (auto simp: f.zero a Z_def eventually_at_filter elim!: eventually_mono)
        hence "eventually (\<lambda>z::complex. False) (at z)"
          using ev_nz[OF \<open>z \<in> A\<close>] by eventually_elim auto
        thus False by simp
      qed
      
      have "zorder (\<lambda>w. w ^ m * f.f w) z = int (subdegree ((fps_const z + fps_X) ^ m * F))"
        using has_fps_expansion_zorder[OF exp2] by simp
      also have "\<dots> = int (subdegree F) + (if z = 0 then m else 0)"
        by auto
      also have "int (subdegree F) = zorder f.f z"
        using has_fps_expansion_zorder[OF exp1] by simp
      also have "\<dots> = int (card (a -` {z}))"
        by (rule f.zorder)
      also have "card (a -` {z}) = (if z = 0 then 0 else c z)"
      proof (cases "z = 0")
        case True
        hence "a -` {z} = {}"
          using a(2) by auto
        thus ?thesis using True by simp
      next
        case False
        thus ?thesis
          by (subst a(3)) (use True that in \<open>auto simp: Z_def\<close>)
      qed
      also have "int \<dots> + (if z = 0 then m else 0) = zorder g z"
        using \<open>zorder g z \<ge> 0\<close> that by (auto simp: c_def m_def)
      finally show ?thesis .
    qed 

    have eq_zero_iff: "z ^ m * f.f z = 0 \<longleftrightarrow> g z = 0" if "z \<in> A" for z
      using that by (auto simp add: f.zero a m_def zorder_pos_iff Z_def)

    obtain h :: "complex \<Rightarrow> complex" where h:
       "h holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> h z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> g z = h z * (z ^ m * f.f z)"
    proof (rule holomorphic_zorder_factorization[OF assms(1-3)])
      show "(\<lambda>z. z ^ m * f.f z) holomorphic_on A"
        by (intro holomorphic_intros)
      show "z ^ m * f.f z = 0 \<longleftrightarrow> g z = 0" if "z \<in> A" for z
        by (rule eq_zero_iff) fact+
      show "zorder (\<lambda>z. z ^ m * f.f z) z = zorder g z" if "z \<in> A" for z
        by (rule zorder_eq) fact+
    qed metis

    show ?thesis
    proof (rule that[of h "\<lambda>z. z ^ m * f.f z"]; (intro ballI allI impI)?)
      show "h holomorphic_on A"
        by fact
      show "(\<lambda>z. z ^ m * f.f z) holomorphic_on UNIV"
        by (intro holomorphic_intros)
    next
      fix z :: complex
      show "(z ^ m * f.f z = 0) = ((\<forall>z\<in>A. g z = 0) \<or> z \<in> A \<and> g z = 0)"
        using infinite_zeroes(1) a(2)
        by (auto simp: m_def zorder_eq eq_zero_iff zorder_pos_iff Z_def f.zero)
    qed (use zorder_eq eq_zero_iff h in auto)
  qed
qed

text \<open>
  The following is a simpler version for entire functions.
\<close>
theorem weierstrass_factorization_UNIV:
  assumes "g holomorphic_on UNIV" 
  obtains h f where
    "h holomorphic_on UNIV" "f holomorphic_on UNIV"
    "\<forall>z. f z = 0 \<longleftrightarrow> g z = 0"
    "\<forall>z. zorder f z = zorder g z"
    "\<forall>z. h z \<noteq> 0"
    "\<forall>z. g z = h z * f z"
  using assms by (rule weierstrass_factorization, goal_cases) auto



subsection \<open>The factorisation theorem for meromorphic functions\<close>

text \<open>
  Let \<open>g\<close> be a meromorphic function on a connected open domain \<open>A\<close>. Assume that the poles and
  zeros of \<open>g\<close> have no accumulation point on the border of \<open>A\<close>. Then \<open>g\<close> can be written in the
  form $g(z) = h(z) f_1(z) / f_2(z)$ where $h$ is holomorphic on \<open>A\<close> with no zeroes and $f_1$ and
  $f_2$ are entire.
  
  Moreover, as direct consequences of that, the zeroes of $f_1$ are precisely the zeroes of $g$
  and the zeros of $f_2$ are precisely the poles of $g$ (with the corresponding multiplicity).
\<close>
theorem weierstrass_factorization_meromorphic:
  assumes mero: "g nicely_meromorphic_on A" and A: "open A" "connected A"
  assumes no_limpt: "\<And>z. z \<in> frontier A \<Longrightarrow> \<not>z islimpt {w\<in>A. g w = 0 \<or> is_pole g w}"
  obtains h f1 f2 where
    "h holomorphic_on A" "f1 holomorphic_on UNIV" "f2 holomorphic_on UNIV"
    "\<forall>z\<in>A. f1 z = 0 \<longleftrightarrow> \<not>is_pole g z \<and> g z = 0"
    "\<forall>z\<in>A. f2 z = 0 \<longleftrightarrow> is_pole g z"
    "\<forall>z\<in>A. \<not>is_pole g z \<longrightarrow> zorder f1 z = zorder g z"
    "\<forall>z\<in>A. is_pole g z \<longrightarrow> zorder f2 z = -zorder g z"
    "\<forall>z\<in>A. h z \<noteq> 0"
    "\<forall>z\<in>A. g z = h z * f1 z / f2 z"
proof -
  have mero': "g meromorphic_on A"
    using mero unfolding nicely_meromorphic_on_def by auto
  define pts where "pts = {z\<in>A. is_pole g z}"
  have "{z. is_pole g z} sparse_in A"
    using meromorphic_on_imp_not_pole_cosparse[OF mero']
    by (auto simp: eventually_cosparse)
  hence "pts sparse_in A"
    unfolding pts_def by (rule sparse_in_subset2) auto
  have open_diff_pts: "open (A - pts')" if "pts' \<subseteq> pts" for pts'
  proof (rule open_diff_sparse_pts)
    show "pts' sparse_in A"
      using \<open>pts sparse_in A\<close> by (rule sparse_in_subset2) fact
  qed (use \<open>open A\<close> in auto)
  
  have ev: "eventually (\<lambda>w. w \<in> A - pts) (at z)" if "z \<in> A" for z
  proof (cases "z \<in> pts")
    case False
    thus ?thesis
      using that open_diff_pts[of "pts"] by (intro eventually_at_in_open') auto
  next
    case True
    have "eventually (\<lambda>w. w \<in> (A - (pts - {z})) - {z}) (at z)"
      using that by (intro eventually_at_in_open open_diff_pts) auto
    also have "A - (pts - {z}) - {z} = A - pts"
      using True by auto
    finally show ?thesis .
  qed

  show ?thesis
  proof (cases "\<forall>z\<in>A-pts. g z = 0")
    case True
    have no_poles: "\<not>is_pole g z" if "z \<in> A" for z
    proof -
      have "is_pole g z \<longleftrightarrow> is_pole (\<lambda>_::complex. 0 :: complex) z"
        by (intro is_pole_cong[OF eventually_mono[OF ev]]) (use that True in auto)
      thus ?thesis
        by simp
    qed
    hence [simp]: "pts = {}"
      by (auto simp: pts_def)
    have [simp]: "zorder g z = zorder (\<lambda>_::complex. 0 :: complex) z" if "z \<in> A" for z
      by (intro zorder_cong[OF eventually_mono[OF ev]]) (use True that in auto)
    show ?thesis
      by (rule that[of "\<lambda>_. 1" "\<lambda>_. 0" "\<lambda>_. 1"]) (use True in \<open>auto simp: no_poles\<close>)
  
  next
  
    case False
    have is_pole_iff: "is_pole g z \<longleftrightarrow> z \<in> pts" if "z \<in> A" for z
      using that by (auto simp: pts_def)
  
    obtain h f1 where h_f1:
      "h holomorphic_on A - pts" "f1 holomorphic_on UNIV"
      "\<forall>z. f1 z = 0 \<longleftrightarrow> (\<forall>z\<in>A-pts. g z = 0) \<or> (z \<in> A - pts \<and> g z = 0)"
      "\<forall>z\<in>A-pts. zorder f1 z = zorder g z"
      "\<forall>z\<in>A-pts. h z \<noteq> 0"
      "\<forall>z\<in>A-pts. g z = h z * f1 z"
    proof (rule weierstrass_factorization)
      have "g analytic_on A - pts"
        by (rule nicely_meromorphic_without_singularities)
           (use mero in \<open>auto simp: pts_def dest: nicely_meromorphic_on_subset\<close>)
      thus holo: "g holomorphic_on A - pts"
        by (rule analytic_imp_holomorphic)
      show "open (A - pts)"
        by (rule open_diff_pts) auto
      show "connected (A - pts)"
        by (rule sparse_imp_connected) (use A \<open>pts sparse_in A\<close> in auto)
      show "\<not> z islimpt {w \<in> A - pts. g w = 0}" if "z \<in> frontier (A - pts)" for z
      proof -
        from that have "z \<in> frontier A - pts \<union> pts"
          using \<open>open (A - pts)\<close> \<open>open A\<close> closure_mono[of "A - pts" A]
          by (auto simp: frontier_def interior_open)
        thus ?thesis
        proof
          assume "z \<in> pts"
          hence "is_pole g z"
            by (auto simp: pts_def)
          hence "eventually (\<lambda>z. g z \<noteq> 0) (at z)"
            using non_zero_neighbour_pole by blast
          hence "\<not>z islimpt {w. g w = 0}"
            by (auto simp: islimpt_iff_eventually)
          thus ?thesis
            using islimpt_subset[of z "{w\<in>A-pts. g w = 0}" "{w. g w = 0}"] by blast
        next
          assume z: "z \<in> frontier A - pts"
          show "\<not> z islimpt {w \<in> A - pts. g w = 0}"
          proof
            assume "z islimpt {w \<in> A - pts. g w = 0}"
            hence "z islimpt {w \<in> A. g w = 0 \<or> is_pole g w}"
              by (rule islimpt_subset) (auto simp: pts_def)
            thus False using no_limpt z by blast
          qed
        qed
      qed
    qed
  
    have f1_eq_0_iff: "f1 z = 0 \<longleftrightarrow> (z \<in> A - pts \<and> g z = 0)" for z
      using h_f1(3) False by auto
  
    define h' where "h' = (\<lambda>z. if z \<in> pts then 0 else inverse (h z))"

    have isolated_h: "isolated_singularity_at h z" if "z \<in> pts" for z
    proof -
      have "open (A - (pts - {z}))"
        by (rule open_diff_pts) auto
      moreover have "z \<in> (A - (pts - {z}))"
        using that by (auto simp: pts_def)
      moreover have "h holomorphic_on (A - (pts - {z})) - {z}"
        by (rule holomorphic_on_subset[OF h_f1(1)]) (use that in auto)
      ultimately show "isolated_singularity_at h z"
        using isolated_singularity_at_holomorphic by blast
    qed

    have is_pole_h: "is_pole h z" if "z \<in> A" "is_pole g z" for z
    proof -
      have f1: "f1 analytic_on {z}"
        by (meson analytic_on_holomorphic h_f1(2) open_UNIV top_greatest)
      have "eventually (\<lambda>w. g w \<noteq> 0) (at z)"
        using \<open>is_pole g z\<close> non_zero_neighbour_pole by blast
      with ev[OF that(1)] have ev': "eventually (\<lambda>w. g w * f1 w \<noteq> 0) (at z)"
        by eventually_elim (use h_f1(3) in auto)

      have "is_pole (\<lambda>w. g w / f1 w) z"
      proof (rule is_pole_divide_zorder)
        show "isolated_singularity_at f1 z" "not_essential f1 z"
          using f1 by (simp_all add: isolated_singularity_at_analytic not_essential_analytic)
        show "isolated_singularity_at g z" "not_essential g z"
          using mero' that unfolding meromorphic_on_altdef by blast+
        show freq: "frequently (\<lambda>w. g w * f1 w \<noteq> 0) (at z)"
          using ev' by (rule eventually_frequently[rotated]) auto
        from freq have freq': "frequently (\<lambda>w. f1 w \<noteq> 0) (at z)"
          using frequently_elim1 by fastforce
        have "zorder g z < 0"
          using \<open>is_pole g z\<close> \<open>isolated_singularity_at g z\<close> isolated_pole_imp_neg_zorder by auto
        also have "0 \<le> zorder f1 z"
          by (rule zorder_ge_0[OF f1 freq'])
        finally show "zorder g z < zorder f1 z" .
      qed
      also have "?this \<longleftrightarrow> is_pole h z"
      proof (intro is_pole_cong refl eventually_mono[OF eventually_conj[OF ev[OF that(1)] ev']])
        fix w assume "w \<in> A - pts \<and> g w * f1 w \<noteq> 0"
        thus "g w / f1 w = h w" using h_f1(6)
          by (auto simp: divide_simps)
      qed
      finally show "is_pole h z" .
    qed

    have "h' analytic_on {z}" if "z \<in> A" for z
    proof (cases "z \<in> pts")
      case False
      moreover have "open (A - pts)"
        by (rule open_diff_pts) auto
      ultimately have "(\<lambda>z. inverse (h z)) analytic_on {z}"
        using that h_f1(1,2,5) \<open>open (A - pts)\<close> analytic_at False
        by (intro analytic_intros) (auto simp: f1_eq_0_iff)
      also have "eventually (\<lambda>z. z \<in> A - pts) (nhds z)"
        using that False \<open>open (A - pts)\<close> by (intro eventually_nhds_in_open) auto
      hence "(\<lambda>z. inverse (h z)) analytic_on {z} \<longleftrightarrow> h' analytic_on {z}"
        by (intro analytic_at_cong) (auto elim!: eventually_mono simp: h'_def)
      finally show ?thesis .
    next
      case True
      have "(\<lambda>w. if w = z then 0 else inverse (h w)) holomorphic_on (A - (pts - {z}))"
      proof (rule is_pole_inverse_holomorphic)
        from True have "A - (pts - {z}) - {z} = A - pts"
          by auto
        thus "h holomorphic_on A - (pts - {z}) - {z}"
          using h_f1(1) by simp
      next
        show "open (A - (pts - {z}))"
          by (rule open_diff_pts) auto
      next
        have "is_pole g z"
          using True that by (simp add: is_pole_iff)
        thus "is_pole h z"
          using is_pole_h that by auto
      next
        show "\<forall>w\<in>A-(pts-{z})-{z}. h w \<noteq> 0"
          using h_f1(5) by auto
      qed
      also have "?this \<longleftrightarrow> h' holomorphic_on A - (pts - {z})"
      proof (intro holomorphic_cong refl)
        fix w assume w: "w \<in> A - (pts - {z})"
        show "(if w = z then 0 else inverse (h w)) = h' w"
          using True w by (cases "w = z") (auto simp: h'_def)
      qed
      finally have "h' holomorphic_on A - (pts - {z})" .
      moreover have "z \<in> A - (pts - {z})" "open (A - (pts - {z}))"
        using True that by (auto intro!: open_diff_pts)
      ultimately show "h' analytic_on {z}"
        using analytic_at by blast
    qed
    hence h': "h' analytic_on A"
      using analytic_on_analytic_at by blast
  
    have h'_eq_0_iff: "h' w = 0 \<longleftrightarrow> is_pole g w" if "w \<in> A" for w
      using that h_f1(5) is_pole_iff[of w] by (auto simp: h'_def)
 
    obtain h'' f2 where h''_f2:
       "h'' holomorphic_on A" "f2 holomorphic_on UNIV"
       "\<forall>z. f2 z = 0 \<longleftrightarrow> (\<forall>z\<in>A. h' z = 0) \<or> (z \<in> A \<and> h' z = 0)"
       "\<forall>z\<in>A. h' z = 0 \<longrightarrow> zorder f2 z = zorder h' z"
       "\<forall>z\<in>A. h'' z \<noteq> 0" "\<forall>z\<in>A. h' z = h'' z * f2 z"
    proof (rule weierstrass_factorization[of h' A])
      show "open A" "connected A"
        by fact+
      show "h' holomorphic_on A"
        using h' \<open>open A\<close> by (simp add: analytic_on_open)
      show "\<not>z islimpt {w\<in>A. h' w = 0}" if "z \<in> frontier A" for z
      proof
        assume "z islimpt {w\<in>A. h' w = 0}"
        also have "{w\<in>A. h' w = 0} = pts"
          by (auto simp: h'_eq_0_iff pts_def)
        finally have "z islimpt {w \<in> A. g w = 0 \<or> is_pole g w}"
          by (rule islimpt_subset) (auto simp: pts_def)
        thus False using no_limpt[of z] that
          by blast
      qed
    qed blast
  
    show ?thesis
    proof (rule that[of "\<lambda>w. inverse (h'' w)" f1 f2]; (intro ballI allI impI)?)
      show "(\<lambda>w. inverse (h'' w)) holomorphic_on A"
        using h''_f2(1,2,5) by (intro holomorphic_intros) auto
    next
      show "f1 holomorphic_on UNIV" "f2 holomorphic_on UNIV"
        by fact+
    next
      show "f1 z = 0 \<longleftrightarrow> \<not> is_pole g z \<and> g z = 0" if "z \<in> A" for z
        using that by (subst f1_eq_0_iff) (auto simp: pts_def)
    next
      show "f2 z = 0 \<longleftrightarrow> is_pole g z" if "z \<in> A" for z
      proof -
        have "\<not>(\<forall>z\<in>A. h' z = 0)"
          using False h''_f2(6) h_f1(6) h'_eq_0_iff is_pole_iff by auto
        hence "f2 z = 0 \<longleftrightarrow> h' z = 0"
          using h''_f2(3) that by auto
        also have "\<dots> \<longleftrightarrow> is_pole g z"
          using that by (simp add: is_pole_iff h'_eq_0_iff)
        finally show ?thesis .
      qed
    next
      show "zorder f1 z = zorder g z" if "z \<in> A" "\<not>is_pole g z" for z
        using h_f1(4) that by (auto simp: pts_def)
    next
      show "zorder f2 z = -zorder g z" if "z \<in> A" "is_pole g z" for z
      proof -
        have "zorder f2 z = zorder h' z"
          using h''_f2(4) that h'_eq_0_iff[of z] is_pole_iff[of z] by auto
        also have "\<dots> = zorder (\<lambda>w. inverse (h w)) z"
          using that by (intro zorder_cong eventually_mono[OF ev]) (auto simp: h'_def)
        also have "\<dots> = -zorder h z"
        proof (intro zorder_inverse)
          have "is_pole h z"
            using that is_pole_iff[of z] is_pole_h[of z] by auto
          thus "not_essential h z"
            by force
          show "frequently (\<lambda>w. h w \<noteq> 0) (at z)"
            using non_zero_neighbour_pole[OF \<open>is_pole h z\<close>] eventually_frequently by force
        qed (use that in \<open>auto intro!: isolated_h simp: pts_def\<close>)
        also have "zorder f1 z = 0"
        proof (rule zorder_eq_0I)
          show "f1 analytic_on {z}"
            using that h_f1(2) holomorphic_on_imp_analytic_at by blast
          show "f1 z \<noteq> 0"
            using that h_f1(3) False by (auto simp: pts_def)
        qed
        hence "zorder h z = zorder f1 z + zorder h z"
          by simp
        also have "\<dots> = zorder (\<lambda>w. f1 w * h w) z"
        proof (rule zorder_times [symmetric])
          have "f1 analytic_on {z}"
            using that h_f1(2) holomorphic_on_imp_analytic_at by blast
          thus "isolated_singularity_at f1 z" "not_essential f1 z"
            using isolated_singularity_at_analytic not_essential_analytic by blast+
          show "isolated_singularity_at h z"
            using that by (intro isolated_h) (auto simp: pts_def)
          have "is_pole h z"
            using is_pole_iff[of z] that by (intro is_pole_h) auto
          thus "not_essential h z"
            by force
          have "z \<in> A"
            using that by auto
          have "eventually (\<lambda>w. g w \<noteq> 0) (at z)"
            using non_zero_neighbour_pole[of g z] that by auto
          hence "eventually (\<lambda>w. f1 w * h w \<noteq> 0) (at z)"
            using ev[OF \<open>z \<in> A\<close>]  by eventually_elim (use h_f1(6) in auto)
          thus "frequently (\<lambda>w. f1 w * h w \<noteq> 0) (at z)"
            using eventually_frequently by force
        qed
        also have "\<dots> = zorder g z"
        proof (rule zorder_cong)
          have "eventually (\<lambda>w. w \<in> A - pts) (at z)"
            using ev[of z] that by auto
          thus "eventually (\<lambda>w. f1 w * h w = g w) (at z)"
            by eventually_elim (use h_f1(6) in auto)
        qed auto
        finally show ?thesis .
      qed
    next
      show "inverse (h'' z) \<noteq> 0" if "z \<in> A" for z
        using h''_f2(5) that by auto
    next
      show "g z = inverse (h'' z) * f1 z / f2 z" if z: "z \<in> A" for z
      proof (cases "is_pole g z")
        case False
        have *: "g z = h z * f1 z" "h' z = h'' z * f2 z" "h'' z \<noteq> 0" "h z \<noteq> 0"
          using that h''_f2(5,6) h_f1(5,6) False unfolding pts_def by blast+
        have "g z = h z * f1 z"
          by fact
        also have "\<dots> = f1 z / h' z"
          using * that False by (simp add: h'_def field_simps pts_def)
        also have "h' z = h'' z * f2 z"
          by fact
        also have "f1 z / (h'' z * f2 z) = inverse (h'' z) * f1 z / f2 z"
          by (simp add: divide_inverse_commute)
        finally show ?thesis .
      next
        case True
        have "\<not>g \<midarrow>z\<rightarrow> g z"
          using True at_neq_bot is_pole_def not_tendsto_and_filterlim_at_infinity by blast
        with mero and z and True have "g z = 0"
          by (auto simp: nicely_meromorphic_on_def)
        moreover have "f2 z = 0"
          using True z by (simp add: h''_f2(3) h'_eq_0_iff)
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  Again, we derive an easier version for functions meromorphic on the entire complex plane.
\<close>
theorem weierstrass_factorization_meromorphic_UNIV:
  assumes "g nicely_meromorphic_on UNIV" 
  obtains h f1 f2 where
    "h holomorphic_on UNIV" "f1 holomorphic_on UNIV" "f2 holomorphic_on UNIV"
    "\<forall>z. f1 z = 0 \<longleftrightarrow> \<not>is_pole g z \<and> g z = 0"
    "\<forall>z. f2 z = 0 \<longleftrightarrow> is_pole g z"
    "\<forall>z. \<not>is_pole g z \<longrightarrow> zorder f1 z = zorder g z"
    "\<forall>z. is_pole g z \<longrightarrow> zorder f2 z = -zorder g z"
    "\<forall>z. h z \<noteq> 0"
    "\<forall>z. g z = h z * f1 z / f2 z"
proof (rule weierstrass_factorization_meromorphic)
  show "g nicely_meromorphic_on UNIV"
    by fact
  show "connected (UNIV :: complex set)"
    by (simp add: Convex.connected_UNIV)
  show "\<not> z islimpt {w \<in> UNIV. g w = 0 \<or> is_pole g w}" if "z \<in> frontier UNIV" for z
    using that by simp
  show "open (UNIV :: complex set)"
    by simp
qed auto

end
