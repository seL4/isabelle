section \<open>Conformal Mappings. Consequences of Cauchy's integral theorem.\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2016)\<close>

theory Conformal_Mappings
imports "~~/src/HOL/Multivariate_Analysis/Cauchy_Integral_Thm"

begin

subsection\<open>Cauchy's inequality and more versions of Liouville\<close>

lemma Cauchy_higher_deriv_bound:
    assumes holf: "f holomorphic_on (ball z r)"
        and contf: "continuous_on (cball z r) f"
        and "0 < r" and "0 < n"
        and fin : "\<And>w. w \<in> ball z r \<Longrightarrow> f w \<in> ball y B0"
      shows "norm ((deriv ^^ n) f z) \<le> (fact n) * B0 / r^n"
proof -
  have "0 < B0" using \<open>0 < r\<close> fin [of z]
    by (metis ball_eq_empty ex_in_conv fin not_less)
  have le_B0: "\<And>w. cmod (w - z) \<le> r \<Longrightarrow> cmod (f w - y) \<le> B0"
    apply (rule continuous_on_closure_norm_le [of "ball z r" "\<lambda>w. f w - y"])
    apply (auto simp: \<open>0 < r\<close>  dist_norm norm_minus_commute)
    apply (rule continuous_intros contf)+
    using fin apply (simp add: dist_commute dist_norm less_eq_real_def)
    done
  have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>w. f w) z - (deriv ^^ n) (\<lambda>w. y) z"
    using \<open>0 < n\<close> by simp
  also have "... = (deriv ^^ n) (\<lambda>w. f w - y) z"
    by (rule higher_deriv_diff [OF holf, symmetric]) (auto simp: \<open>0 < r\<close>)
  finally have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>w. f w - y) z" .
  have contf': "continuous_on (cball z r) (\<lambda>u. f u - y)"
    by (rule contf continuous_intros)+
  have holf': "(\<lambda>u. (f u - y)) holomorphic_on (ball z r)"
    by (simp add: holf holomorphic_on_diff)
  def a \<equiv> "(2 * pi)/(fact n)"
  have "0 < a"  by (simp add: a_def)
  have "B0/r^(Suc n)*2 * pi * r = a*((fact n)*B0/r^n)"
    using \<open>0 < r\<close> by (simp add: a_def divide_simps)
  have der_dif: "(deriv ^^ n) (\<lambda>w. f w - y) z = (deriv ^^ n) f z"
    using \<open>0 < r\<close> \<open>0 < n\<close>
    by (auto simp: higher_deriv_diff [OF holf holomorphic_on_const])
  have "norm ((2 * of_real pi * ii)/(fact n) * (deriv ^^ n) (\<lambda>w. f w - y) z)
        \<le> (B0/r^(Suc n)) * (2 * pi * r)"
    apply (rule has_contour_integral_bound_circlepath [of "(\<lambda>u. (f u - y)/(u - z)^(Suc n))" _ z])
    using Cauchy_has_contour_integral_higher_derivative_circlepath [OF contf' holf']
    using \<open>0 < B0\<close> \<open>0 < r\<close>
    apply (auto simp: norm_divide norm_mult norm_power divide_simps le_B0)
    done
  then show ?thesis
    using \<open>0 < r\<close>
    by (auto simp: norm_divide norm_mult norm_power field_simps der_dif le_B0)
qed

proposition Cauchy_inequality:
    assumes holf: "f holomorphic_on (ball \<xi> r)"
        and contf: "continuous_on (cball \<xi> r) f"
        and "0 < r"
        and nof: "\<And>x. norm(\<xi>-x) = r \<Longrightarrow> norm(f x) \<le> B"
      shows "norm ((deriv ^^ n) f \<xi>) \<le> (fact n) * B / r^n"
proof -
  obtain x where "norm (\<xi>-x) = r"
    by (metis abs_of_nonneg add_diff_cancel_left' \<open>0 < r\<close> diff_add_cancel
                 dual_order.strict_implies_order norm_of_real)
  then have "0 \<le> B"
    by (metis nof norm_not_less_zero not_le order_trans)
  have  "((\<lambda>u. f u / (u - \<xi>) ^ Suc n) has_contour_integral (2 * pi) * \<i> / fact n * (deriv ^^ n) f \<xi>)
         (circlepath \<xi> r)"
    apply (rule Cauchy_has_contour_integral_higher_derivative_circlepath [OF contf holf])
    using \<open>0 < r\<close> by simp
  then have "norm ((2 * pi * ii)/(fact n) * (deriv ^^ n) f \<xi>) \<le> (B / r^(Suc n)) * (2 * pi * r)"
    apply (rule has_contour_integral_bound_circlepath)
    using \<open>0 \<le> B\<close> \<open>0 < r\<close>
    apply (simp_all add: norm_divide norm_power nof frac_le norm_minus_commute del: power_Suc)
    done
  then show ?thesis using \<open>0 < r\<close>
    by (simp add: norm_divide norm_mult field_simps)
qed

proposition Liouville_polynomial:
    assumes holf: "f holomorphic_on UNIV"
        and nof: "\<And>z. A \<le> norm z \<Longrightarrow> norm(f z) \<le> B * norm z ^ n"
      shows "f \<xi> = (\<Sum>k\<le>n. (deriv^^k) f 0 / fact k * \<xi> ^ k)"
proof (cases rule: le_less_linear [THEN disjE])
  assume "B \<le> 0"
  then have "\<And>z. A \<le> norm z \<Longrightarrow> norm(f z) = 0"
    by (metis nof less_le_trans zero_less_mult_iff neqE norm_not_less_zero norm_power not_le)
  then have f0: "(f \<longlongrightarrow> 0) at_infinity"
    using Lim_at_infinity by force
  then have [simp]: "f = (\<lambda>w. 0)"
    using Liouville_weak [OF holf, of 0]
    by (simp add: eventually_at_infinity f0) meson
  show ?thesis by simp
next
  assume "0 < B"
  have "((\<lambda>k. (deriv ^^ k) f 0 / (fact k) * (\<xi> - 0)^k) sums f \<xi>)"
    apply (rule holomorphic_power_series [where r = "norm \<xi> + 1"])
    using holf holomorphic_on_subset apply auto
    done
  then have sumsf: "((\<lambda>k. (deriv ^^ k) f 0 / (fact k) * \<xi>^k) sums f \<xi>)" by simp
  have "(deriv ^^ k) f 0 / fact k * \<xi> ^ k = 0" if "k>n" for k
  proof (cases "(deriv ^^ k) f 0 = 0")
    case True then show ?thesis by simp
  next
    case False
      def w \<equiv> "complex_of_real (fact k * B / cmod ((deriv ^^ k) f 0) + (\<bar>A\<bar> + 1))"
      have "1 \<le> abs (fact k * B / cmod ((deriv ^^ k) f 0) + (\<bar>A\<bar> + 1))"
        using \<open>0 < B\<close> by simp
      then have wge1: "1 \<le> norm w"
        by (metis norm_of_real w_def)
      then have "w \<noteq> 0" by auto
      have kB: "0 < fact k * B"
        using \<open>0 < B\<close> by simp
      then have "0 \<le> fact k * B / cmod ((deriv ^^ k) f 0)"
        by simp
      then have wgeA: "A \<le> cmod w"
        by (simp only: w_def norm_of_real)
      have "fact k * B / cmod ((deriv ^^ k) f 0) < abs (fact k * B / cmod ((deriv ^^ k) f 0) + (\<bar>A\<bar> + 1))"
        using \<open>0 < B\<close> by simp
      then have wge: "fact k * B / cmod ((deriv ^^ k) f 0) < norm w"
        by (metis norm_of_real w_def)
      then have "fact k * B / norm w < cmod ((deriv ^^ k) f 0)"
        using False by (simp add: divide_simps mult.commute split: if_split_asm)
      also have "... \<le> fact k * (B * norm w ^ n) / norm w ^ k"
        apply (rule Cauchy_inequality)
           using holf holomorphic_on_subset apply force
          using holf holomorphic_on_imp_continuous_on holomorphic_on_subset apply blast
         using \<open>w \<noteq> 0\<close> apply (simp add:)
         by (metis nof wgeA dist_0_norm dist_norm)
      also have "... = fact k * (B * 1 / cmod w ^ (k-n))"
        apply (simp only: mult_cancel_left times_divide_eq_right [symmetric])
        using \<open>k>n\<close> \<open>w \<noteq> 0\<close> \<open>0 < B\<close> apply (simp add: divide_simps semiring_normalization_rules)
        done
      also have "... = fact k * B / cmod w ^ (k-n)"
        by simp
      finally have "fact k * B / cmod w < fact k * B / cmod w ^ (k - n)" .
      then have "1 / cmod w < 1 / cmod w ^ (k - n)"
        by (metis kB divide_inverse inverse_eq_divide mult_less_cancel_left_pos)
      then have "cmod w ^ (k - n) < cmod w"
        by (metis frac_le le_less_trans norm_ge_zero norm_one not_less order_refl wge1 zero_less_one)
      with self_le_power [OF wge1] have False
        by (meson diff_is_0_eq not_gr0 not_le that)
      then show ?thesis by blast
  qed
  then have "(deriv ^^ (k + Suc n)) f 0 / fact (k + Suc n) * \<xi> ^ (k + Suc n) = 0" for k
    using not_less_eq by blast
  then have "(\<lambda>i. (deriv ^^ (i + Suc n)) f 0 / fact (i + Suc n) * \<xi> ^ (i + Suc n)) sums 0"
    by (rule sums_0)
  with sums_split_initial_segment [OF sumsf, where n = "Suc n"]
  show ?thesis
    using atLeast0AtMost lessThan_Suc_atMost sums_unique2 by fastforce
qed

text\<open>Every bounded entire function is a constant function.\<close>
theorem Liouville_theorem:
    assumes holf: "f holomorphic_on UNIV"
        and bf: "bounded (range f)"
    obtains c where "\<And>z. f z = c"
proof -
  obtain B where "\<And>z. cmod (f z) \<le> B"
    by (meson bf bounded_pos rangeI)
  then show ?thesis
    using Liouville_polynomial [OF holf, of 0 B 0, simplified] that by blast
qed



text\<open>A holomorphic function f has only isolated zeros unless f is 0.\<close>

proposition powser_0_nonzero:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_field,banach}"
  assumes r: "0 < r"
      and sm: "\<And>x. norm (x - \<xi>) < r \<Longrightarrow> (\<lambda>n. a n * (x - \<xi>) ^ n) sums (f x)"
      and [simp]: "f \<xi> = 0"
      and m0: "a m \<noteq> 0" and "m>0"
  obtains s where "0 < s" and "\<And>z. z \<in> cball \<xi> s - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
proof -
  have "r \<le> conv_radius a"
    using sm sums_summable by (auto simp: le_conv_radius_iff [where \<xi>=\<xi>])
  obtain m where am: "a m \<noteq> 0" and az [simp]: "(\<And>n. n<m \<Longrightarrow> a n = 0)"
    apply (rule_tac m = "LEAST n. a n \<noteq> 0" in that)
    using m0
    apply (rule LeastI2)
    apply (fastforce intro:  dest!: not_less_Least)+
    done
  def b \<equiv> "\<lambda>i. a (i+m) / a m"
  def g \<equiv> "\<lambda>x. suminf (\<lambda>i. b i * (x - \<xi>) ^ i)"
  have [simp]: "b 0 = 1"
    by (simp add: am b_def)
  { fix x::'a
    assume "norm (x - \<xi>) < r"
    then have "(\<lambda>n. (a m * (x - \<xi>)^m) * (b n * (x - \<xi>)^n)) sums (f x)"
      using am az sm sums_zero_iff_shift [of m "(\<lambda>n. a n * (x - \<xi>) ^ n)" "f x"]
      by (simp add: b_def monoid_mult_class.power_add algebra_simps)
    then have "x \<noteq> \<xi> \<Longrightarrow> (\<lambda>n. b n * (x - \<xi>)^n) sums (f x / (a m * (x - \<xi>)^m))"
      using am by (simp add: sums_mult_D)
  } note bsums = this
  then have  "norm (x - \<xi>) < r \<Longrightarrow> summable (\<lambda>n. b n * (x - \<xi>)^n)" for x
    using sums_summable by (cases "x=\<xi>") auto
  then have "r \<le> conv_radius b"
    by (simp add: le_conv_radius_iff [where \<xi>=\<xi>])
  then have "r/2 < conv_radius b"
    using not_le order_trans r by fastforce
  then have "continuous_on (cball \<xi> (r/2)) g"
    using powser_continuous_suminf [of "r/2" b \<xi>] by (simp add: g_def)
  then obtain s where "s>0"  "\<And>x. \<lbrakk>norm (x - \<xi>) \<le> s; norm (x - \<xi>) \<le> r/2\<rbrakk> \<Longrightarrow> dist (g x) (g \<xi>) < 1/2"
    apply (rule continuous_onE [where x=\<xi> and e = "1/2"])
    using r apply (auto simp: norm_minus_commute dist_norm)
    done
  moreover have "g \<xi> = 1"
    by (simp add: g_def)
  ultimately have gnz: "\<And>x. \<lbrakk>norm (x - \<xi>) \<le> s; norm (x - \<xi>) \<le> r/2\<rbrakk> \<Longrightarrow> (g x) \<noteq> 0"
    by fastforce
  have "f x \<noteq> 0" if "x \<noteq> \<xi>" "norm (x - \<xi>) \<le> s" "norm (x - \<xi>) \<le> r/2" for x
    using bsums [of x] that gnz [of x]
    apply (auto simp: g_def)
    using r sums_iff by fastforce
  then show ?thesis
    apply (rule_tac s="min s (r/2)" in that)
    using \<open>0 < r\<close> \<open>0 < s\<close> by (auto simp: dist_commute dist_norm)
qed

proposition isolated_zeros:
  assumes holf: "f holomorphic_on S"
      and "open S" "connected S" "\<xi> \<in> S" "f \<xi> = 0" "\<beta> \<in> S" "f \<beta> \<noteq> 0"
  obtains r where "0 < r" "ball \<xi> r \<subseteq> S" "\<And>z. z \<in> ball \<xi> r - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
proof -
  obtain r where "0 < r" and r: "ball \<xi> r \<subseteq> S"
    using \<open>open S\<close> \<open>\<xi> \<in> S\<close> open_contains_ball_eq by blast
  have powf: "((\<lambda>n. (deriv ^^ n) f \<xi> / (fact n) * (z - \<xi>)^n) sums f z)" if "z \<in> ball \<xi> r" for z
    apply (rule holomorphic_power_series [OF _ that])
    apply (rule holomorphic_on_subset [OF holf r])
    done
  obtain m where m: "(deriv ^^ m) f \<xi> / (fact m) \<noteq> 0"
    using holomorphic_fun_eq_0_on_connected [OF holf \<open>open S\<close> \<open>connected S\<close> _ \<open>\<xi> \<in> S\<close> \<open>\<beta> \<in> S\<close>] \<open>f \<beta> \<noteq> 0\<close>
    by auto
  then have "m \<noteq> 0" using assms(5) funpow_0 by fastforce
  obtain s where "0 < s" and s: "\<And>z. z \<in> cball \<xi> s - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
    apply (rule powser_0_nonzero [OF \<open>0 < r\<close> powf \<open>f \<xi> = 0\<close> m])
    using \<open>m \<noteq> 0\<close> by (auto simp: dist_commute dist_norm)
  have "0 < min r s"  by (simp add: \<open>0 < r\<close> \<open>0 < s\<close>)
  then show ?thesis
    apply (rule that)
    using r s by auto
qed


proposition analytic_continuation:
  assumes holf: "f holomorphic_on S"
      and S: "open S" "connected S"
      and "U \<subseteq> S" "\<xi> \<in> S"
      and "\<xi> islimpt U"
      and fU0 [simp]: "\<And>z. z \<in> U \<Longrightarrow> f z = 0"
      and "w \<in> S"
    shows "f w = 0"
proof -
  obtain e where "0 < e" and e: "cball \<xi> e \<subseteq> S"
    using \<open>open S\<close> \<open>\<xi> \<in> S\<close> open_contains_cball_eq by blast
  def T \<equiv> "cball \<xi> e \<inter> U"
  have contf: "continuous_on (closure T) f"
    by (metis T_def closed_cball closure_minimal e holf holomorphic_on_imp_continuous_on
              holomorphic_on_subset inf.cobounded1)
  have fT0 [simp]: "\<And>x. x \<in> T \<Longrightarrow> f x = 0"
    by (simp add: T_def)
  have "\<And>r. \<lbrakk>\<forall>e>0. \<exists>x'\<in>U. x' \<noteq> \<xi> \<and> dist x' \<xi> < e; 0 < r\<rbrakk> \<Longrightarrow> \<exists>x'\<in>cball \<xi> e \<inter> U. x' \<noteq> \<xi> \<and> dist x' \<xi> < r"
    by (metis \<open>0 < e\<close> IntI dist_commute less_eq_real_def mem_cball min_less_iff_conj)
  then have "\<xi> islimpt T" using \<open>\<xi> islimpt U\<close>
    by (auto simp: T_def islimpt_approachable)
  then have "\<xi> \<in> closure T"
    by (simp add: closure_def)
  then have "f \<xi> = 0"
    by (auto simp: continuous_constant_on_closure [OF contf])
  show ?thesis
    apply (rule ccontr)
    apply (rule isolated_zeros [OF holf \<open>open S\<close> \<open>connected S\<close> \<open>\<xi> \<in> S\<close> \<open>f \<xi> = 0\<close> \<open>w \<in> S\<close>], assumption)
    by (metis open_ball \<open>\<xi> islimpt T\<close> centre_in_ball fT0 insertE insert_Diff islimptE)
qed


subsection\<open>Open mapping theorem\<close>

lemma holomorphic_contract_to_zero:
  assumes contf: "continuous_on (cball \<xi> r) f"
      and holf: "f holomorphic_on ball \<xi> r"
      and "0 < r"
      and norm_less: "\<And>z. norm(\<xi> - z) = r \<Longrightarrow> norm(f \<xi>) < norm(f z)"
  obtains z where "z \<in> ball \<xi> r" "f z = 0"
proof -
  { assume fnz: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w \<noteq> 0"
    then have "0 < norm (f \<xi>)"
      by (simp add: \<open>0 < r\<close>)
    have fnz': "\<And>w. w \<in> cball \<xi> r \<Longrightarrow> f w \<noteq> 0"
      by (metis norm_less dist_norm fnz less_eq_real_def mem_ball mem_cball norm_not_less_zero norm_zero)
    have "frontier(cball \<xi> r) \<noteq> {}"
      using \<open>0 < r\<close> by simp
    def g \<equiv> "\<lambda>z. inverse (f z)"
    have contg: "continuous_on (cball \<xi> r) g"
      unfolding g_def using contf continuous_on_inverse fnz' by blast
    have holg: "g holomorphic_on ball \<xi> r"
      unfolding g_def using fnz holf holomorphic_on_inverse by blast
    have "frontier (cball \<xi> r) \<subseteq> cball \<xi> r"
      by (simp add: subset_iff)
    then have contf': "continuous_on (frontier (cball \<xi> r)) f"
          and contg': "continuous_on (frontier (cball \<xi> r)) g"
      by (blast intro: contf contg continuous_on_subset)+
    have froc: "frontier(cball \<xi> r) \<noteq> {}"
      using \<open>0 < r\<close> by simp
    moreover have "continuous_on (frontier (cball \<xi> r)) (norm o f)"
      using contf' continuous_on_compose continuous_on_norm_id by blast
    ultimately obtain w where w: "w \<in> frontier(cball \<xi> r)"
                          and now: "\<And>x. x \<in> frontier(cball \<xi> r) \<Longrightarrow> norm (f w) \<le> norm (f x)"
      apply (rule bexE [OF continuous_attains_inf [OF compact_frontier [OF compact_cball]]])
      apply (simp add:)
      done
    then have fw: "0 < norm (f w)"
      by (simp add: fnz')
    have "continuous_on (frontier (cball \<xi> r)) (norm o g)"
      using contg' continuous_on_compose continuous_on_norm_id by blast
    then obtain v where v: "v \<in> frontier(cball \<xi> r)"
               and nov: "\<And>x. x \<in> frontier(cball \<xi> r) \<Longrightarrow> norm (g v) \<ge> norm (g x)"
      apply (rule bexE [OF continuous_attains_sup [OF compact_frontier [OF compact_cball] froc]])
      apply (simp add:)
      done
    then have fv: "0 < norm (f v)"
      by (simp add: fnz')
    have "norm ((deriv ^^ 0) g \<xi>) \<le> fact 0 * norm (g v) / r ^ 0"
      by (rule Cauchy_inequality [OF holg contg \<open>0 < r\<close>]) (simp add: dist_norm nov)
    then have "cmod (g \<xi>) \<le> norm (g v)"
      by simp
    with w have wr: "norm (\<xi> - w) = r" and nfw: "norm (f w) \<le> norm (f \<xi>)"
      apply (simp_all add: dist_norm)
      by (metis \<open>0 < cmod (f \<xi>)\<close> g_def less_imp_inverse_less norm_inverse not_le now order_trans v)
    with fw have False
      using norm_less by force
  }
  with that show ?thesis by blast
qed


theorem open_mapping_thm:
  assumes holf: "f holomorphic_on S"
      and S: "open S" "connected S"
      and "open U" "U \<subseteq> S"
      and fne: "~ f constant_on S"
    shows "open (f ` U)"
proof -
  have *: "open (f ` U)"
          if "U \<noteq> {}" and U: "open U" "connected U" and "f holomorphic_on U" and fneU: "\<And>x. \<exists>y \<in> U. f y \<noteq> x"
          for U
  proof (clarsimp simp: open_contains_ball)
    fix \<xi> assume \<xi>: "\<xi> \<in> U"
    show "\<exists>e>0. ball (f \<xi>) e \<subseteq> f ` U"
    proof -
      have hol: "(\<lambda>z. f z - f \<xi>) holomorphic_on U"
        by (rule holomorphic_intros that)+
      obtain s where "0 < s" and sbU: "ball \<xi> s \<subseteq> U"
                 and sne: "\<And>z. z \<in> ball \<xi> s - {\<xi>} \<Longrightarrow> (\<lambda>z. f z - f \<xi>) z \<noteq> 0"
        using isolated_zeros [OF hol U \<xi>]  by (metis fneU right_minus_eq)
      obtain r where "0 < r" and r: "cball \<xi> r \<subseteq> ball \<xi> s"
        apply (rule_tac r="s/2" in that)
        using \<open>0 < s\<close> by auto
      have "cball \<xi> r \<subseteq> U"
        using sbU r by blast
      then have frsbU: "frontier (cball \<xi> r) \<subseteq> U"
        using Diff_subset frontier_def order_trans by fastforce
      then have cof: "compact (frontier(cball \<xi> r))"
        by blast
      have frne: "frontier (cball \<xi> r) \<noteq> {}"
        using \<open>0 < r\<close> by auto
      have contfr: "continuous_on (frontier (cball \<xi> r)) (\<lambda>z. norm (f z - f \<xi>))"
        apply (rule continuous_on_compose2 [OF Complex_Analysis_Basics.continuous_on_norm_id])
        using hol frsbU holomorphic_on_imp_continuous_on holomorphic_on_subset by blast+
      obtain w where "norm (\<xi> - w) = r"
                 and w: "(\<And>z. norm (\<xi> - z) = r \<Longrightarrow> norm (f w - f \<xi>) \<le> norm(f z - f \<xi>))"
        apply (rule bexE [OF continuous_attains_inf [OF cof frne contfr]])
        apply (simp add: dist_norm)
        done
      moreover def \<epsilon> \<equiv> "norm (f w - f \<xi>) / 3"
      ultimately have "0 < \<epsilon>"
        using \<open>0 < r\<close> dist_complex_def r sne by auto
      have "ball (f \<xi>) \<epsilon> \<subseteq> f ` U"
      proof
        fix \<gamma>
        assume \<gamma>: "\<gamma> \<in> ball (f \<xi>) \<epsilon>"
        have *: "cmod (\<gamma> - f \<xi>) < cmod (\<gamma> - f z)" if "cmod (\<xi> - z) = r" for z
        proof -
          have lt: "cmod (f w - f \<xi>) / 3 < cmod (\<gamma> - f z)"
            using w [OF that] \<gamma>
            using dist_triangle2 [of "f \<xi>" "\<gamma>"  "f z"] dist_triangle2 [of "f \<xi>" "f z" \<gamma>]
            by (simp add: \<epsilon>_def dist_norm norm_minus_commute)
          show ?thesis
            by (metis \<epsilon>_def dist_commute dist_norm less_trans lt mem_ball \<gamma>)
       qed
       have "continuous_on (cball \<xi> r) (\<lambda>z. \<gamma> - f z)"
          apply (rule continuous_intros)+
          using \<open>cball \<xi> r \<subseteq> U\<close> \<open>f holomorphic_on U\<close>
          apply (blast intro: continuous_on_subset holomorphic_on_imp_continuous_on)
          done
        moreover have "(\<lambda>z. \<gamma> - f z) holomorphic_on ball \<xi> r"
          apply (rule holomorphic_intros)+
          apply (metis \<open>cball \<xi> r \<subseteq> U\<close> \<open>f holomorphic_on U\<close> holomorphic_on_subset interior_cball interior_subset)
          done
        ultimately obtain z where "z \<in> ball \<xi> r" "\<gamma> - f z = 0"
          apply (rule holomorphic_contract_to_zero)
          apply (blast intro!: \<open>0 < r\<close> *)+
          done
        then show "\<gamma> \<in> f ` U"
          using \<open>cball \<xi> r \<subseteq> U\<close> by fastforce
      qed
      then show ?thesis using  \<open>0 < \<epsilon>\<close> by blast
    qed
  qed
  have "open (f ` X)" if "X \<in> components U" for X
  proof -
    have holfU: "f holomorphic_on U"
      using \<open>U \<subseteq> S\<close> holf holomorphic_on_subset by blast
    have "X \<noteq> {}"
      using that by (simp add: in_components_nonempty)
    moreover have "open X"
      using that \<open>open U\<close> open_components by auto
    moreover have "connected X"
      using that in_components_maximal by blast
    moreover have "f holomorphic_on X"
      by (meson that holfU holomorphic_on_subset in_components_maximal)
    moreover have "\<exists>y\<in>X. f y \<noteq> x" for x
    proof (rule ccontr)
      assume not: "\<not> (\<exists>y\<in>X. f y \<noteq> x)"
      have "X \<subseteq> S"
        using \<open>U \<subseteq> S\<close> in_components_subset that by blast
      obtain w where w: "w \<in> X" using \<open>X \<noteq> {}\<close> by blast
      have wis: "w islimpt X"
        using w \<open>open X\<close> interior_eq by auto
      have hol: "(\<lambda>z. f z - x) holomorphic_on S"
        by (simp add: holf holomorphic_on_diff)
      with fne [unfolded constant_on_def] analytic_continuation [OF hol S \<open>X \<subseteq> S\<close> _ wis]
           not \<open>X \<subseteq> S\<close> w
      show False by auto
    qed
    ultimately show ?thesis
      by (rule *)
  qed
  then show ?thesis
    by (subst Union_components [of U]) (auto simp: image_Union)
qed


text\<open>No need for @{term S} to be connected. But the nonconstant condition is stronger.\<close>
corollary open_mapping_thm2:
  assumes holf: "f holomorphic_on S"
      and S: "open S"
      and "open U" "U \<subseteq> S"
      and fnc: "\<And>X. \<lbrakk>open X; X \<subseteq> S; X \<noteq> {}\<rbrakk> \<Longrightarrow> ~ f constant_on X"
    shows "open (f ` U)"
proof -
  have "S = \<Union>(components S)" by (fact Union_components)
  with \<open>U \<subseteq> S\<close> have "U = (\<Union>C \<in> components S. C \<inter> U)" by auto
  then have "f ` U = (\<Union>C \<in> components S. f ` (C \<inter> U))"
    by auto
  moreover
  { fix C assume "C \<in> components S"
    with S \<open>C \<in> components S\<close> open_components in_components_connected
    have C: "open C" "connected C" by auto
    have "C \<subseteq> S"
      by (metis \<open>C \<in> components S\<close> in_components_maximal)
    have nf: "\<not> f constant_on C"
      apply (rule fnc)
      using C \<open>C \<subseteq> S\<close> \<open>C \<in> components S\<close> in_components_nonempty by auto
    have "f holomorphic_on C"
      by (metis holf holomorphic_on_subset \<open>C \<subseteq> S\<close>)
    then have "open (f ` (C \<inter> U))"
      apply (rule open_mapping_thm [OF _ C _ _ nf])
      apply (simp add: C \<open>open U\<close> open_Int, blast)
      done
  } ultimately show ?thesis
    by force
qed

corollary open_mapping_thm3:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
    shows  "open (f ` S)"
apply (rule open_mapping_thm2 [OF holf])
using assms
apply (simp_all add:)
using injective_not_constant subset_inj_on by blast



subsection\<open>Maximum Modulus Principle\<close>

text\<open>If @{term f} is holomorphic, then its norm (modulus) cannot exhibit a true local maximum that is
   properly within the domain of @{term f}.\<close>

proposition maximum_modulus_principle:
  assumes holf: "f holomorphic_on S"
      and S: "open S" "connected S"
      and "open U" "U \<subseteq> S" "\<xi> \<in> U"
      and no: "\<And>z. z \<in> U \<Longrightarrow> norm(f z) \<le> norm(f \<xi>)"
    shows "f constant_on S"
proof (rule ccontr)
  assume "\<not> f constant_on S"
  then have "open (f ` U)"
    using open_mapping_thm assms by blast
  moreover have "~ open (f ` U)"
  proof -
    have "\<exists>t. cmod (f \<xi> - t) < e \<and> t \<notin> f ` U" if "0 < e" for e
      apply (rule_tac x="if 0 < Re(f \<xi>) then f \<xi> + (e/2) else f \<xi> - (e/2)" in exI)
      using that
      apply (simp add: dist_norm)
      apply (fastforce simp: cmod_Re_le_iff dest!: no dest: sym)
      done
    then show ?thesis
      unfolding open_contains_ball by (metis \<open>\<xi> \<in> U\<close> contra_subsetD dist_norm imageI mem_ball)
  qed
  ultimately show False
    by blast
qed


proposition maximum_modulus_frontier:
  assumes holf: "f holomorphic_on (interior S)"
      and contf: "continuous_on (closure S) f"
      and bos: "bounded S"
      and leB: "\<And>z. z \<in> frontier S \<Longrightarrow> norm(f z) \<le> B"
      and "\<xi> \<in> S"
    shows "norm(f \<xi>) \<le> B"
proof -
  have "compact (closure S)" using bos
    by (simp add: bounded_closure compact_eq_bounded_closed)
  moreover have "continuous_on (closure S) (cmod \<circ> f)"
    using contf continuous_on_compose continuous_on_norm_id by blast
  ultimately obtain z where zin: "z \<in> closure S" and z: "\<And>y. y \<in> closure S \<Longrightarrow> (cmod \<circ> f) y \<le> (cmod \<circ> f) z"
    using continuous_attains_sup [of "closure S" "norm o f"] \<open>\<xi> \<in> S\<close> by auto
  then consider "z \<in> frontier S" | "z \<in> interior S" using frontier_def by auto
  then have "norm(f z) \<le> B"
  proof cases
    case 1 then show ?thesis using leB by blast
  next
    case 2
    have zin: "z \<in> connected_component_set (interior S) z"
      by (simp add: 2)
    have "f constant_on (connected_component_set (interior S) z)"
      apply (rule maximum_modulus_principle [OF _ _ _ _ _ zin])
      apply (metis connected_component_subset holf holomorphic_on_subset)
      apply (simp_all add: open_connected_component)
      by (metis closure_subset comp_eq_dest_lhs  interior_subset subsetCE z connected_component_in)
    then obtain c where c: "\<And>w. w \<in> connected_component_set (interior S) z \<Longrightarrow> f w = c"
      by (auto simp: constant_on_def)
    have "f ` closure(connected_component_set (interior S) z) \<subseteq> {c}"
      apply (rule image_closure_subset)
      apply (meson closure_mono connected_component_subset contf continuous_on_subset interior_subset)
      using c
      apply auto
      done
    then have cc: "\<And>w. w \<in> closure(connected_component_set (interior S) z) \<Longrightarrow> f w = c" by blast
    have "frontier(connected_component_set (interior S) z) \<noteq> {}"
      apply (simp add: frontier_eq_empty)
      by (metis "2" bos bounded_interior connected_component_eq_UNIV connected_component_refl not_bounded_UNIV)
    then obtain w where w: "w \<in> frontier(connected_component_set (interior S) z)"
       by auto
    then have "norm (f z) = norm (f w)"  by (simp add: "2" c cc frontier_def)
    also have "... \<le> B"
      apply (rule leB)
      using w
using frontier_interior_subset frontier_of_connected_component_subset by blast
    finally show ?thesis .
  qed
  then show ?thesis
    using z \<open>\<xi> \<in> S\<close> closure_subset by fastforce
qed

corollary maximum_real_frontier:
  assumes holf: "f holomorphic_on (interior S)"
      and contf: "continuous_on (closure S) f"
      and bos: "bounded S"
      and leB: "\<And>z. z \<in> frontier S \<Longrightarrow> Re(f z) \<le> B"
      and "\<xi> \<in> S"
    shows "Re(f \<xi>) \<le> B"
using maximum_modulus_frontier [of "exp o f" S "exp B"]
      Transcendental.continuous_on_exp holomorphic_on_compose holomorphic_on_exp assms
by auto


subsection\<open>Factoring out a zero according to its order\<close>

lemma holomorphic_factor_order_of_zero:
  assumes holf: "f holomorphic_on S"
      and os: "open S"
      and "\<xi> \<in> S" "0 < n"
      and dnz: "(deriv ^^ n) f \<xi> \<noteq> 0"
      and dfz: "\<And>i. \<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f \<xi> = 0"
   obtains g r where "0 < r"
                "g holomorphic_on ball \<xi> r"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>)^n * g w"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
proof -
  obtain r where "r>0" and r: "ball \<xi> r \<subseteq> S" using assms by (blast elim!: openE)
  then have holfb: "f holomorphic_on ball \<xi> r"
    using holf holomorphic_on_subset by blast
  def g \<equiv> "\<lambda>w. suminf (\<lambda>i. (deriv ^^ (i + n)) f \<xi> / (fact(i + n)) * (w - \<xi>)^i)"
  have sumsg: "(\<lambda>i. (deriv ^^ (i + n)) f \<xi> / (fact(i + n)) * (w - \<xi>)^i) sums g w"
   and feq: "f w - f \<xi> = (w - \<xi>)^n * g w"
       if w: "w \<in> ball \<xi> r" for w
  proof -
    def powf \<equiv> "(\<lambda>i. (deriv ^^ i) f \<xi>/(fact i) * (w - \<xi>)^i)"
    have sing: "{..<n} - {i. powf i = 0} = (if f \<xi> = 0 then {} else {0})"
      unfolding powf_def using \<open>0 < n\<close> dfz by (auto simp: dfz; metis funpow_0 not_gr0)
    have "powf sums f w"
      unfolding powf_def by (rule holomorphic_power_series [OF holfb w])
    moreover have "(\<Sum>i<n. powf i) = f \<xi>"
      apply (subst Groups_Big.comm_monoid_add_class.setsum.setdiff_irrelevant [symmetric])
      apply (simp add:)
      apply (simp only: dfz sing)
      apply (simp add: powf_def)
      done
    ultimately have fsums: "(\<lambda>i. powf (i+n)) sums (f w - f \<xi>)"
      using w sums_iff_shift' by metis
    then have *: "summable (\<lambda>i. (w - \<xi>) ^ n * ((deriv ^^ (i + n)) f \<xi> * (w - \<xi>) ^ i / fact (i + n)))"
      unfolding powf_def using sums_summable
      by (auto simp: power_add mult_ac)
    have "summable (\<lambda>i. (deriv ^^ (i + n)) f \<xi> * (w - \<xi>) ^ i / fact (i + n))"
    proof (cases "w=\<xi>")
      case False then show ?thesis
        using summable_mult [OF *, of "1 / (w - \<xi>) ^ n"] by (simp add:)
    next
      case True then show ?thesis
        by (auto simp: Power.semiring_1_class.power_0_left intro!: summable_finite [of "{0}"]
                 split: if_split_asm)
    qed
    then show sumsg: "(\<lambda>i. (deriv ^^ (i + n)) f \<xi> / (fact(i + n)) * (w - \<xi>)^i) sums g w"
      by (simp add: summable_sums_iff g_def)
    show "f w - f \<xi> = (w - \<xi>)^n * g w"
      apply (rule sums_unique2)
      apply (rule fsums [unfolded powf_def])
      using sums_mult [OF sumsg, of "(w - \<xi>) ^ n"]
      by (auto simp: power_add mult_ac)
  qed
  then have holg: "g holomorphic_on ball \<xi> r"
    by (meson sumsg power_series_holomorphic)
  then have contg: "continuous_on (ball \<xi> r) g"
    by (blast intro: holomorphic_on_imp_continuous_on)
  have "g \<xi> \<noteq> 0"
    using dnz unfolding g_def
    by (subst suminf_finite [of "{0}"]) auto
  obtain d where "0 < d" and d: "\<And>w. w \<in> ball \<xi> d \<Longrightarrow> g w \<noteq> 0"
    apply (rule exE [OF continuous_on_avoid [OF contg _ \<open>g \<xi> \<noteq> 0\<close>]])
    using \<open>0 < r\<close>
    apply force
    by (metis \<open>0 < r\<close> less_trans mem_ball not_less_iff_gr_or_eq)
  show ?thesis
    apply (rule that [where g=g and r ="min r d"])
    using \<open>0 < r\<close> \<open>0 < d\<close> holg
    apply (auto simp: feq holomorphic_on_subset subset_ball d)
    done
qed


lemma holomorphic_factor_order_of_zero_strong:
  assumes holf: "f holomorphic_on S" "open S"  "\<xi> \<in> S" "0 < n"
      and "(deriv ^^ n) f \<xi> \<noteq> 0"
      and "\<And>i. \<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f \<xi> = 0"
   obtains g r where "0 < r"
                "g holomorphic_on ball \<xi> r"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = ((w - \<xi>) * g w) ^ n"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
proof -
  obtain g r where "0 < r"
               and holg: "g holomorphic_on ball \<xi> r"
               and feq: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>)^n * g w"
               and gne: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
    by (auto intro: holomorphic_factor_order_of_zero [OF assms])
  have con: "continuous_on (ball \<xi> r) (\<lambda>z. deriv g z / g z)"
    by (rule continuous_intros) (auto simp: gne holg holomorphic_deriv holomorphic_on_imp_continuous_on)
  have cd: "\<And>x. dist \<xi> x < r \<Longrightarrow> (\<lambda>z. deriv g z / g z) field_differentiable at x"
    apply (rule derivative_intros)+
    using holg mem_ball apply (blast intro: holomorphic_deriv holomorphic_on_imp_differentiable_at)
    apply (metis Topology_Euclidean_Space.open_ball at_within_open holg holomorphic_on_def mem_ball)
    using gne mem_ball by blast
  obtain h where h: "\<And>x. x \<in> ball \<xi> r \<Longrightarrow> (h has_field_derivative deriv g x / g x) (at x)"
    apply (rule exE [OF holomorphic_convex_primitive [of "ball \<xi> r" "{}" "\<lambda>z. deriv g z / g z"]])
    apply (auto simp: con cd)
    apply (metis open_ball at_within_open mem_ball)
    done
  then have "continuous_on (ball \<xi> r) h"
    by (metis open_ball holomorphic_on_imp_continuous_on holomorphic_on_open)
  then have con: "continuous_on (ball \<xi> r) (\<lambda>x. exp (h x) / g x)"
    by (auto intro!: continuous_intros simp add: holg holomorphic_on_imp_continuous_on gne)
  have 0: "dist \<xi> x < r \<Longrightarrow> ((\<lambda>x. exp (h x) / g x) has_field_derivative 0) (at x)" for x
    apply (rule h derivative_eq_intros | simp)+
    apply (rule DERIV_deriv_iff_field_differentiable [THEN iffD2])
    using holg apply (auto simp: holomorphic_on_imp_differentiable_at gne h)
    done
  obtain c where c: "\<And>x. x \<in> ball \<xi> r \<Longrightarrow> exp (h x) / g x = c"
    by (rule DERIV_zero_connected_constant [of "ball \<xi> r" "{}" "\<lambda>x. exp(h x) / g x"]) (auto simp: con 0)
  have hol: "(\<lambda>z. exp ((Ln (inverse c) + h z) / of_nat n)) holomorphic_on ball \<xi> r"
    apply (rule holomorphic_on_compose [unfolded o_def, where g = exp])
    apply (rule holomorphic_intros)+
    using h holomorphic_on_open apply blast
    apply (rule holomorphic_intros)+
    using \<open>0 < n\<close> apply (simp add:)
    apply (rule holomorphic_intros)+
    done
  show ?thesis
    apply (rule that [where g="\<lambda>z. exp((Ln(inverse c) + h z)/n)" and r =r])
    using \<open>0 < r\<close> \<open>0 < n\<close>
    apply (auto simp: feq power_mult_distrib exp_divide_power_eq c [symmetric])
    apply (rule hol)
    apply (simp add: Transcendental.exp_add gne)
    done
qed


lemma
  fixes k :: "'a::wellorder"
  assumes a_def: "a == LEAST x. P x" and P: "P k"
  shows def_LeastI: "P a" and def_Least_le: "a \<le> k"
unfolding a_def
by (rule LeastI Least_le; rule P)+

lemma holomorphic_factor_zero_nonconstant:
  assumes holf: "f holomorphic_on S" and S: "open S" "connected S"
      and "\<xi> \<in> S" "f \<xi> = 0"
      and nonconst: "\<And>c. \<exists>z \<in> S. f z \<noteq> c"
   obtains g r n
      where "0 < n"  "0 < r"  "ball \<xi> r \<subseteq> S"
            "g holomorphic_on ball \<xi> r"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w = (w - \<xi>)^n * g w"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
proof (cases "\<forall>n>0. (deriv ^^ n) f \<xi> = 0")
  case True then show ?thesis
    using holomorphic_fun_eq_const_on_connected [OF holf S _ \<open>\<xi> \<in> S\<close>] nonconst by auto
next
  case False
  then obtain n0 where "n0 > 0" and n0: "(deriv ^^ n0) f \<xi> \<noteq> 0" by blast
  obtain r0 where "r0 > 0" "ball \<xi> r0 \<subseteq> S" using S openE \<open>\<xi> \<in> S\<close> by auto
  def n \<equiv> "LEAST n. (deriv ^^ n) f \<xi> \<noteq> 0"
  have n_ne: "(deriv ^^ n) f \<xi> \<noteq> 0"
    by (rule def_LeastI [OF n_def]) (rule n0)
  then have "0 < n" using \<open>f \<xi> = 0\<close>
    using funpow_0 by fastforce
  have n_min: "\<And>k. k < n \<Longrightarrow> (deriv ^^ k) f \<xi> = 0"
    using def_Least_le [OF n_def] not_le by blast
  then obtain g r1
    where  "0 < r1" "g holomorphic_on ball \<xi> r1"
           "\<And>w. w \<in> ball \<xi> r1 \<Longrightarrow> f w = (w - \<xi>) ^ n * g w"
           "\<And>w. w \<in> ball \<xi> r1 \<Longrightarrow> g w \<noteq> 0"
    by (auto intro: holomorphic_factor_order_of_zero [OF holf \<open>open S\<close> \<open>\<xi> \<in> S\<close> \<open>n > 0\<close> n_ne] simp: \<open>f \<xi> = 0\<close>)
  then show ?thesis
    apply (rule_tac g=g and r="min r0 r1" and n=n in that)
    using \<open>0 < n\<close> \<open>0 < r0\<close> \<open>0 < r1\<close> \<open>ball \<xi> r0 \<subseteq> S\<close>
    apply (auto simp: subset_ball intro: holomorphic_on_subset)
    done
qed


lemma holomorphic_lower_bound_difference:
  assumes holf: "f holomorphic_on S" and S: "open S" "connected S"
      and "\<xi> \<in> S" and "\<phi> \<in> S"
      and fne: "f \<phi> \<noteq> f \<xi>"
   obtains k n r
      where "0 < k"  "0 < r"
            "ball \<xi> r \<subseteq> S"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> k * norm(w - \<xi>)^n \<le> norm(f w - f \<xi>)"
proof -
  def n \<equiv> "LEAST n. 0 < n \<and> (deriv ^^ n) f \<xi> \<noteq> 0"
  obtain n0 where "0 < n0" and n0: "(deriv ^^ n0) f \<xi> \<noteq> 0"
    using fne holomorphic_fun_eq_const_on_connected [OF holf S] \<open>\<xi> \<in> S\<close> \<open>\<phi> \<in> S\<close> by blast
  then have "0 < n" and n_ne: "(deriv ^^ n) f \<xi> \<noteq> 0"
    unfolding n_def by (metis (mono_tags, lifting) LeastI)+
  have n_min: "\<And>k. \<lbrakk>0 < k; k < n\<rbrakk> \<Longrightarrow> (deriv ^^ k) f \<xi> = 0"
    unfolding n_def by (blast dest: not_less_Least)
  then obtain g r
    where "0 < r" and holg: "g holomorphic_on ball \<xi> r"
      and fne: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>) ^ n * g w"
      and gnz: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
      by (auto intro: holomorphic_factor_order_of_zero  [OF holf \<open>open S\<close> \<open>\<xi> \<in> S\<close> \<open>n > 0\<close> n_ne])
  obtain e where "e>0" and e: "ball \<xi> e \<subseteq> S" using assms by (blast elim!: openE)
  then have holfb: "f holomorphic_on ball \<xi> e"
    using holf holomorphic_on_subset by blast
  def d \<equiv> "(min e r) / 2"
  have "0 < d" using \<open>0 < r\<close> \<open>0 < e\<close> by (simp add: d_def)
  have "d < r"
    using \<open>0 < r\<close> by (auto simp: d_def)
  then have cbb: "cball \<xi> d \<subseteq> ball \<xi> r"
    by (auto simp: cball_subset_ball_iff)
  then have "g holomorphic_on cball \<xi> d"
    by (rule holomorphic_on_subset [OF holg])
  then have "closed (g ` cball \<xi> d)"
    by (simp add: compact_imp_closed compact_continuous_image holomorphic_on_imp_continuous_on)
  moreover have "g ` cball \<xi> d \<noteq> {}"
    using \<open>0 < d\<close> by auto
  ultimately obtain x where x: "x \<in> g ` cball \<xi> d" and "\<And>y. y \<in> g ` cball \<xi> d \<Longrightarrow> dist 0 x \<le> dist 0 y"
    by (rule distance_attains_inf) blast
  then have leg: "\<And>w. w \<in> cball \<xi> d \<Longrightarrow> norm x \<le> norm (g w)"
    by auto
  have "ball \<xi> d \<subseteq> cball \<xi> d" by auto
  also have "... \<subseteq> ball \<xi> e" using \<open>0 < d\<close> d_def by auto
  also have "... \<subseteq> S" by (rule e)
  finally have dS: "ball \<xi> d \<subseteq> S" .
  moreover have "x \<noteq> 0" using gnz x \<open>d < r\<close> by auto
  ultimately show ?thesis
    apply (rule_tac k="norm x" and n=n and r=d in that)
    using \<open>d < r\<close> leg
    apply (auto simp: \<open>0 < d\<close> fne norm_mult norm_power algebra_simps mult_right_mono)
    done
qed

lemma
  assumes holf: "f holomorphic_on (S - {\<xi>})" and \<xi>: "\<xi> \<in> interior S"
    shows holomorphic_on_extend_lim:
          "(\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S - {\<xi>}. g z = f z)) \<longleftrightarrow>
           ((\<lambda>z. (z - \<xi>) * f z) \<longlongrightarrow> 0) (at \<xi>)"
          (is "?P = ?Q")
     and holomorphic_on_extend_bounded:
          "(\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S - {\<xi>}. g z = f z)) \<longleftrightarrow>
           (\<exists>B. eventually (\<lambda>z. norm(f z) \<le> B) (at \<xi>))"
          (is "?P = ?R")
proof -
  obtain \<delta> where "0 < \<delta>" and \<delta>: "ball \<xi> \<delta> \<subseteq> S"
    using \<xi> mem_interior by blast
  have "?R" if holg: "g holomorphic_on S" and gf: "\<And>z. z \<in> S - {\<xi>} \<Longrightarrow> g z = f z" for g
  proof -
    have *: "\<forall>\<^sub>F z in at \<xi>. dist (g z) (g \<xi>) < 1 \<longrightarrow> cmod (f z) \<le> cmod (g \<xi>) + 1"
      apply (simp add: eventually_at)
      apply (rule_tac x="\<delta>" in exI)
      using \<delta> \<open>0 < \<delta>\<close>
      apply (clarsimp simp:)
      apply (drule_tac c=x in subsetD)
      apply (simp add: dist_commute)
      by (metis DiffI add.commute diff_le_eq dist_norm gf le_less_trans less_eq_real_def norm_triangle_ineq2 singletonD)
    have "continuous_on (interior S) g"
      by (meson continuous_on_subset holg holomorphic_on_imp_continuous_on interior_subset)
    then have "\<And>x. x \<in> interior S \<Longrightarrow> (g \<longlongrightarrow> g x) (at x)"
      using continuous_on_interior continuous_within holg holomorphic_on_imp_continuous_on by blast
    then have "(g \<longlongrightarrow> g \<xi>) (at \<xi>)"
      by (simp add: \<xi>)
    then show ?thesis
      apply (rule_tac x="norm(g \<xi>) + 1" in exI)
      apply (rule eventually_mp [OF * tendstoD [where e=1]], auto)
      done
  qed
  moreover have "?Q" if "\<forall>\<^sub>F z in at \<xi>. cmod (f z) \<le> B" for B
    by (rule lim_null_mult_right_bounded [OF _ that]) (simp add: LIM_zero)
  moreover have "?P" if "(\<lambda>z. (z - \<xi>) * f z) \<midarrow>\<xi>\<rightarrow> 0"
  proof -
    def h \<equiv> "\<lambda>z. (z - \<xi>)^2 * f z"
    have h0: "(h has_field_derivative 0) (at \<xi>)"
      apply (simp add: h_def Derivative.DERIV_within_iff)
      apply (rule Lim_transform_within [OF that, of 1])
      apply (auto simp: divide_simps power2_eq_square)
      done
    have holh: "h holomorphic_on S"
    proof (simp add: holomorphic_on_def, clarify)
      fix z assume "z \<in> S"
      show "h field_differentiable at z within S"
      proof (cases "z = \<xi>")
        case True then show ?thesis
          using field_differentiable_at_within field_differentiable_def h0 by blast
      next
        case False
        then have "f field_differentiable at z within S"
          using holomorphic_onD [OF holf, of z] \<open>z \<in> S\<close>
          unfolding field_differentiable_def DERIV_within_iff
          by (force intro: exI [where x="dist \<xi> z"] elim: Lim_transform_within_set [unfolded eventually_at])
        then show ?thesis
          by (simp add: h_def power2_eq_square derivative_intros)
      qed
    qed
    def g \<equiv> "\<lambda>z. if z = \<xi> then deriv h \<xi> else (h z - h \<xi>) / (z - \<xi>)"
    have holg: "g holomorphic_on S"
      unfolding g_def by (rule pole_lemma [OF holh \<xi>])
    show ?thesis
      apply (rule_tac x="\<lambda>z. if z = \<xi> then deriv g \<xi> else (g z - g \<xi>)/(z - \<xi>)" in exI)
      apply (rule conjI)
      apply (rule pole_lemma [OF holg \<xi>])
      apply (auto simp: g_def power2_eq_square divide_simps)
      using h0 apply (simp add: h0 DERIV_imp_deriv h_def power2_eq_square)
      done
  qed
  ultimately show "?P = ?Q" and "?P = ?R"
    by meson+
qed


proposition pole_at_infinity:
  assumes holf: "f holomorphic_on UNIV" and lim: "((inverse o f) \<longlongrightarrow> l) at_infinity"
  obtains a n where "\<And>z. f z = (\<Sum>i\<le>n. a i * z^i)"
proof (cases "l = 0")
  case False
  with tendsto_inverse [OF lim] show ?thesis
    apply (rule_tac a="(\<lambda>n. inverse l)" and n=0 in that)
    apply (simp add: Liouville_weak [OF holf, of "inverse l"])
    done
next
  case True
  then have [simp]: "l = 0" .
  show ?thesis
  proof (cases "\<exists>r. 0 < r \<and> (\<forall>z \<in> ball 0 r - {0}. f(inverse z) \<noteq> 0)")
    case True
      then obtain r where "0 < r" and r: "\<And>z. z \<in> ball 0 r - {0} \<Longrightarrow> f(inverse z) \<noteq> 0"
             by auto
      have 1: "inverse \<circ> f \<circ> inverse holomorphic_on ball 0 r - {0}"
        by (rule holomorphic_on_compose holomorphic_intros holomorphic_on_subset [OF holf] | force simp: r)+
      have 2: "0 \<in> interior (ball 0 r)"
        using \<open>0 < r\<close> by simp
      have "\<exists>B. 0<B \<and> eventually (\<lambda>z. cmod ((inverse \<circ> f \<circ> inverse) z) \<le> B) (at 0)"
        apply (rule exI [where x=1])
        apply (simp add:)
        using tendstoD [OF lim [unfolded lim_at_infinity_0] zero_less_one]
        apply (rule eventually_mono)
        apply (simp add: dist_norm)
        done
      with holomorphic_on_extend_bounded [OF 1 2]
      obtain g where holg: "g holomorphic_on ball 0 r"
                 and geq: "\<And>z. z \<in> ball 0 r - {0} \<Longrightarrow> g z = (inverse \<circ> f \<circ> inverse) z"
        by meson
      have ifi0: "(inverse \<circ> f \<circ> inverse) \<midarrow>0\<rightarrow> 0"
        using \<open>l = 0\<close> lim lim_at_infinity_0 by blast
      have g2g0: "g \<midarrow>0\<rightarrow> g 0"
        using \<open>0 < r\<close> centre_in_ball continuous_at continuous_on_eq_continuous_at holg
        by (blast intro: holomorphic_on_imp_continuous_on)
      have g2g1: "g \<midarrow>0\<rightarrow> 0"
        apply (rule Lim_transform_within_open [OF ifi0 open_ball [of 0 r]])
        using \<open>0 < r\<close> by (auto simp: geq)
      have [simp]: "g 0 = 0"
        by (rule tendsto_unique [OF _ g2g0 g2g1]) simp
      have "ball 0 r - {0::complex} \<noteq> {}"
        using \<open>0 < r\<close>
        apply (clarsimp simp: ball_def dist_norm)
        apply (drule_tac c="of_real r/2" in subsetD, auto)
        done
      then obtain w::complex where "w \<noteq> 0" and w: "norm w < r" by force
      then have "g w \<noteq> 0" by (simp add: geq r)
      obtain B n e where "0 < B" "0 < e" "e \<le> r"
                     and leg: "\<And>w. norm w < e \<Longrightarrow> B * cmod w ^ n \<le> cmod (g w)"
        apply (rule holomorphic_lower_bound_difference [OF holg open_ball connected_ball, of 0 w])
        using \<open>0 < r\<close> w \<open>g w \<noteq> 0\<close> by (auto simp: ball_subset_ball_iff)
      have "cmod (f z) \<le> cmod z ^ n / B" if "2/e \<le> cmod z" for z
      proof -
        have ize: "inverse z \<in> ball 0 e - {0}" using that \<open>0 < e\<close>
          by (auto simp: norm_divide divide_simps algebra_simps)
        then have [simp]: "z \<noteq> 0" and izr: "inverse z \<in> ball 0 r - {0}" using  \<open>e \<le> r\<close>
          by auto
        then have [simp]: "f z \<noteq> 0"
          using r [of "inverse z"] by simp
        have [simp]: "f z = inverse (g (inverse z))"
          using izr geq [of "inverse z"] by simp
        show ?thesis using ize leg [of "inverse z"]  \<open>0 < B\<close>  \<open>0 < e\<close>
          by (simp add: divide_simps norm_divide algebra_simps)
      qed
      then show ?thesis
        apply (rule_tac a = "\<lambda>k. (deriv ^^ k) f 0 / (fact k)" and n=n in that)
        apply (rule_tac A = "2/e" and B = "1/B" in Liouville_polynomial [OF holf])
        apply (simp add:)
        done
  next
    case False
    then have fi0: "\<And>r. r > 0 \<Longrightarrow> \<exists>z\<in>ball 0 r - {0}. f (inverse z) = 0"
      by simp
    have fz0: "f z = 0" if "0 < r" and lt1: "\<And>x. x \<noteq> 0 \<Longrightarrow> cmod x < r \<Longrightarrow> inverse (cmod (f (inverse x))) < 1"
              for z r
    proof -
      have f0: "(f \<longlongrightarrow> 0) at_infinity"
      proof -
        have DIM_complex[intro]: "2 \<le> DIM(complex)"  --\<open>should not be necessary!\<close>
          by simp
        have "continuous_on (inverse ` (ball 0 r - {0})) f"
          using continuous_on_subset holf holomorphic_on_imp_continuous_on by blast
        then have "connected ((f \<circ> inverse) ` (ball 0 r - {0}))"
          apply (intro connected_continuous_image continuous_intros)
          apply (force intro: connected_punctured_ball)+
          done
        then have "\<lbrakk>w \<noteq> 0; cmod w < r\<rbrakk> \<Longrightarrow> f (inverse w) = 0" for w
          apply (rule disjE [OF connected_closedD [where A = "{0}" and B = "- ball 0 1"]], auto)
          apply (metis (mono_tags, hide_lams) not_less_iff_gr_or_eq one_less_inverse lt1 zero_less_norm_iff)
          using False \<open>0 < r\<close> apply fastforce
          by (metis (no_types, hide_lams) Compl_iff IntI comp_apply empty_iff image_eqI insert_Diff_single insert_iff mem_ball_0 not_less_iff_gr_or_eq one_less_inverse that(2) zero_less_norm_iff)
        then show ?thesis
          apply (simp add: lim_at_infinity_0)
          apply (rule Lim_eventually)
          apply (simp add: eventually_at)
          apply (rule_tac x=r in exI)
          apply (simp add: \<open>0 < r\<close> dist_norm)
          done
      qed
      obtain w where "w \<in> ball 0 r - {0}" and "f (inverse w) = 0"
        using False \<open>0 < r\<close> by blast
      then show ?thesis
        by (auto simp: f0 Liouville_weak [OF holf, of 0])
    qed
    show ?thesis
      apply (rule that [of "\<lambda>n. 0" 0])
      using lim [unfolded lim_at_infinity_0]
      apply (simp add: Lim_at dist_norm norm_inverse)
      apply (drule_tac x=1 in spec)
      using fz0 apply auto
      done
    qed
qed


subsection\<open>Entire proper functions are precisely the non-trivial polynomials\<close>

proposition proper_map_polyfun:
    fixes c :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,heine_borel}"
  assumes "closed S" and "compact K" and c: "c i \<noteq> 0" "1 \<le> i" "i \<le> n"
    shows "compact (S \<inter> {z. (\<Sum>i\<le>n. c i * z^i) \<in> K})"
proof -
  obtain B where "B > 0" and B: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> B"
    by (metis compact_imp_bounded \<open>compact K\<close> bounded_pos)
  have *: "norm x \<le> b"
            if "\<And>x. b \<le> norm x \<Longrightarrow> B + 1 \<le> norm (\<Sum>i\<le>n. c i * x ^ i)"
               "(\<Sum>i\<le>n. c i * x ^ i) \<in> K"  for b x
  proof -
    have "norm (\<Sum>i\<le>n. c i * x ^ i) \<le> B"
      using B that by blast
    moreover have "\<not> B + 1 \<le> B"
      by simp
    ultimately show "norm x \<le> b"
      using that by (metis (no_types) less_eq_real_def not_less order_trans)
  qed
  have "bounded {z. (\<Sum>i\<le>n. c i * z ^ i) \<in> K}"
    using polyfun_extremal [where c=c and B="B+1", OF c]
    by (auto simp: bounded_pos eventually_at_infinity_pos *)
  moreover have "closed {z. (\<Sum>i\<le>n. c i * z ^ i) \<in> K}"
    apply (rule allI continuous_closed_preimage_univ continuous_intros)+
    using \<open>compact K\<close> compact_eq_bounded_closed by blast
  ultimately show ?thesis
    using closed_inter_compact [OF \<open>closed S\<close>] compact_eq_bounded_closed by blast
qed

corollary proper_map_polyfun_univ:
    fixes c :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,heine_borel}"
  assumes "compact K" "c i \<noteq> 0" "1 \<le> i" "i \<le> n"
    shows "compact ({z. (\<Sum>i\<le>n. c i * z^i) \<in> K})"
using proper_map_polyfun [of UNIV K c i n] assms by simp


proposition proper_map_polyfun_eq:
  assumes "f holomorphic_on UNIV"
    shows "(\<forall>k. compact k \<longrightarrow> compact {z. f z \<in> k}) \<longleftrightarrow>
           (\<exists>c n. 0 < n \<and> (c n \<noteq> 0) \<and> f = (\<lambda>z. \<Sum>i\<le>n. c i * z^i))"
          (is "?lhs = ?rhs")
proof
  assume compf [rule_format]: ?lhs
  have 2: "\<exists>k. 0 < k \<and> a k \<noteq> 0 \<and> f = (\<lambda>z. \<Sum>i \<le> k. a i * z ^ i)"
        if "\<And>z. f z = (\<Sum>i\<le>n. a i * z ^ i)" for a n
  proof (cases "\<forall>i\<le>n. 0<i \<longrightarrow> a i = 0")
    case True
    then have [simp]: "\<And>z. f z = a 0"
      by (simp add: that setsum_atMost_shift)
    have False using compf [of "{a 0}"] by simp
    then show ?thesis ..
  next
    case False
    then obtain k where k: "0 < k" "k\<le>n" "a k \<noteq> 0" by force
    def m \<equiv> "GREATEST k. k\<le>n \<and> a k \<noteq> 0"
    have m: "m\<le>n \<and> a m \<noteq> 0"
      unfolding m_def
      apply (rule GreatestI [where b = "Suc n"])
      using k apply auto
      done
    have [simp]: "a i = 0" if "m < i" "i \<le> n" for i
      using Greatest_le [where b = "Suc n" and P = "\<lambda>k. k\<le>n \<and> a k \<noteq> 0"]
      using m_def not_le that by auto
    have "k \<le> m"
      unfolding m_def
      apply (rule Greatest_le [where b = "Suc n"])
      using k apply auto
      done
    with k m show ?thesis
      by (rule_tac x=m in exI) (auto simp: that comm_monoid_add_class.setsum.mono_neutral_right)
  qed
  have "((inverse \<circ> f) \<longlongrightarrow> 0) at_infinity"
  proof (rule Lim_at_infinityI)
    fix e::real assume "0 < e"
    with compf [of "cball 0 (inverse e)"]
    show "\<exists>B. \<forall>x. B \<le> cmod x \<longrightarrow> dist ((inverse \<circ> f) x) 0 \<le> e"
      apply (simp add:)
      apply (clarsimp simp add: compact_eq_bounded_closed bounded_pos norm_inverse)
      apply (rule_tac x="b+1" in exI)
      apply (metis inverse_inverse_eq less_add_same_cancel2 less_imp_inverse_less add.commute not_le not_less_iff_gr_or_eq order_trans zero_less_one)
      done
  qed
  then show ?rhs
    apply (rule pole_at_infinity [OF assms])
    using 2 apply blast
    done
next
  assume ?rhs
  then obtain c n where "0 < n" "c n \<noteq> 0" "f = (\<lambda>z. \<Sum>i\<le>n. c i * z ^ i)" by blast
  then have "compact {z. f z \<in> k}" if "compact k" for k
    by (auto intro: proper_map_polyfun_univ [OF that])
  then show ?lhs by blast
qed


subsection\<open>Relating invertibility and nonvanishing of derivative\<close>

proposition has_complex_derivative_locally_injective:
  assumes holf: "f holomorphic_on S"
      and S: "\<xi> \<in> S" "open S"
      and dnz: "deriv f \<xi> \<noteq> 0"
  obtains r where "r > 0" "ball \<xi> r \<subseteq> S" "inj_on f (ball \<xi> r)"
proof -
  have *: "\<exists>d>0. \<forall>x. dist \<xi> x < d \<longrightarrow> onorm (\<lambda>v. deriv f x * v - deriv f \<xi> * v) < e" if "e > 0" for e
  proof -
    have contdf: "continuous_on S (deriv f)"
      by (simp add: holf holomorphic_deriv holomorphic_on_imp_continuous_on \<open>open S\<close>)
    obtain \<delta> where "\<delta>>0" and \<delta>: "\<And>x. \<lbrakk>x \<in> S; dist x \<xi> \<le> \<delta>\<rbrakk> \<Longrightarrow> cmod (deriv f x - deriv f \<xi>) \<le> e/2"
      using continuous_onE [OF contdf \<open>\<xi> \<in> S\<close>, of "e/2"] \<open>0 < e\<close>
      by (metis dist_complex_def half_gt_zero less_imp_le)
    obtain \<epsilon> where "\<epsilon>>0" "ball \<xi> \<epsilon> \<subseteq> S"
      by (metis openE [OF \<open>open S\<close> \<open>\<xi> \<in> S\<close>])
    with \<open>\<delta>>0\<close> have "\<exists>\<delta>>0. \<forall>x. dist \<xi> x < \<delta> \<longrightarrow> onorm (\<lambda>v. deriv f x * v - deriv f \<xi> * v) \<le> e/2"
      apply (rule_tac x="min \<delta> \<epsilon>" in exI)
      apply (intro conjI allI impI Operator_Norm.onorm_le)
      apply (simp add:)
      apply (simp only: Rings.ring_class.left_diff_distrib [symmetric] norm_mult)
      apply (rule mult_right_mono [OF \<delta>])
      apply (auto simp: dist_commute Rings.ordered_semiring_class.mult_right_mono \<delta>)
      done
    with \<open>e>0\<close> show ?thesis by force
  qed
  have "inj (op * (deriv f \<xi>))"
    using dnz by simp
  then obtain g' where g': "linear g'" "g' \<circ> op * (deriv f \<xi>) = id"
    using linear_injective_left_inverse [of "op * (deriv f \<xi>)"]
    by (auto simp: linear_times)
  show ?thesis
    apply (rule has_derivative_locally_injective [OF S, where f=f and f' = "\<lambda>z h. deriv f z * h" and g' = g'])
    using g' *
    apply (simp_all add: linear_conv_bounded_linear that)
    using DERIV_deriv_iff_field_differentiable has_field_derivative_imp_has_derivative holf
        holomorphic_on_imp_differentiable_at \<open>open S\<close> apply blast
    done
qed


proposition has_complex_derivative_locally_invertible:
  assumes holf: "f holomorphic_on S"
      and S: "\<xi> \<in> S" "open S"
      and dnz: "deriv f \<xi> \<noteq> 0"
  obtains r where "r > 0" "ball \<xi> r \<subseteq> S" "open (f `  (ball \<xi> r))" "inj_on f (ball \<xi> r)"
proof -
  obtain r where "r > 0" "ball \<xi> r \<subseteq> S" "inj_on f (ball \<xi> r)"
    by (blast intro: that has_complex_derivative_locally_injective [OF assms])
  then have \<xi>: "\<xi> \<in> ball \<xi> r" by simp
  then have nc: "~ f constant_on ball \<xi> r"
    using \<open>inj_on f (ball \<xi> r)\<close> injective_not_constant by fastforce
  have holf': "f holomorphic_on ball \<xi> r"
    using \<open>ball \<xi> r \<subseteq> S\<close> holf holomorphic_on_subset by blast
  have "open (f ` ball \<xi> r)"
    apply (rule open_mapping_thm [OF holf'])
    using nc apply auto
    done
  then show ?thesis
    using \<open>0 < r\<close> \<open>ball \<xi> r \<subseteq> S\<close> \<open>inj_on f (ball \<xi> r)\<close> that  by blast
qed


proposition holomorphic_injective_imp_regular:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
      and "\<xi> \<in> S"
    shows "deriv f \<xi> \<noteq> 0"
proof -
  obtain r where "r>0" and r: "ball \<xi> r \<subseteq> S" using assms by (blast elim!: openE)
  have holf': "f holomorphic_on ball \<xi> r"
    using \<open>ball \<xi> r \<subseteq> S\<close> holf holomorphic_on_subset by blast
  show ?thesis
  proof (cases "\<forall>n>0. (deriv ^^ n) f \<xi> = 0")
    case True
    have fcon: "f w = f \<xi>" if "w \<in> ball \<xi> r" for w
      apply (rule holomorphic_fun_eq_const_on_connected [OF holf'])
      using True \<open>0 < r\<close> that by auto
    have False
      using fcon [of "\<xi> + r/2"] \<open>0 < r\<close> r injf unfolding inj_on_def
      by (metis \<open>\<xi> \<in> S\<close> contra_subsetD dist_commute fcon mem_ball perfect_choose_dist)
    then show ?thesis ..
  next
    case False
    then obtain n0 where n0: "n0 > 0 \<and> (deriv ^^ n0) f \<xi> \<noteq> 0" by blast
    def n \<equiv> "LEAST n. n > 0 \<and> (deriv ^^ n) f \<xi> \<noteq> 0"
    have n_ne: "n > 0" "(deriv ^^ n) f \<xi> \<noteq> 0"
      using def_LeastI [OF n_def n0] by auto
    have n_min: "\<And>k. 0 < k \<Longrightarrow> k < n \<Longrightarrow> (deriv ^^ k) f \<xi> = 0"
      using def_Least_le [OF n_def] not_le by auto
    obtain g \<delta> where "0 < \<delta>"
             and holg: "g holomorphic_on ball \<xi> \<delta>"
             and fd: "\<And>w. w \<in> ball \<xi> \<delta> \<Longrightarrow> f w - f \<xi> = ((w - \<xi>) * g w) ^ n"
             and gnz: "\<And>w. w \<in> ball \<xi> \<delta> \<Longrightarrow> g w \<noteq> 0"
      apply (rule holomorphic_factor_order_of_zero_strong [OF holf \<open>open S\<close> \<open>\<xi> \<in> S\<close> n_ne])
      apply (blast intro: n_min)+
      done
    show ?thesis
    proof (cases "n=1")
      case True
      with n_ne show ?thesis by auto
    next
      case False
      have holgw: "(\<lambda>w. (w - \<xi>) * g w) holomorphic_on ball \<xi> (min r \<delta>)"
        apply (rule holomorphic_intros)+
        using holg by (simp add: holomorphic_on_subset subset_ball)
      have gd: "\<And>w. dist \<xi> w < \<delta> \<Longrightarrow> (g has_field_derivative deriv g w) (at w)"
        using holg
        by (simp add: DERIV_deriv_iff_field_differentiable holomorphic_on_def at_within_open_NO_MATCH)
      have *: "\<And>w. w \<in> ball \<xi> (min r \<delta>)
            \<Longrightarrow> ((\<lambda>w. (w - \<xi>) * g w) has_field_derivative ((w - \<xi>) * deriv g w + g w))
                (at w)"
        by (rule gd derivative_eq_intros | simp)+
      have [simp]: "deriv (\<lambda>w. (w - \<xi>) * g w) \<xi> \<noteq> 0"
        using * [of \<xi>] \<open>0 < \<delta>\<close> \<open>0 < r\<close> by (simp add: DERIV_imp_deriv gnz)
      obtain T where "\<xi> \<in> T" "open T" and Tsb: "T \<subseteq> ball \<xi> (min r \<delta>)" and oimT: "open ((\<lambda>w. (w - \<xi>) * g w) ` T)"
        apply (rule has_complex_derivative_locally_invertible [OF holgw, of \<xi>])
        using \<open>0 < r\<close> \<open>0 < \<delta>\<close>
        apply (simp_all add:)
        by (meson Topology_Euclidean_Space.open_ball centre_in_ball)
      def U \<equiv> "(\<lambda>w. (w - \<xi>) * g w) ` T"
      have "open U" by (metis oimT U_def)
      have "0 \<in> U"
        apply (auto simp: U_def)
        apply (rule image_eqI [where x = \<xi>])
        apply (auto simp: \<open>\<xi> \<in> T\<close>)
        done
      then obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>: "cball 0 \<epsilon> \<subseteq> U"
        using \<open>open U\<close> open_contains_cball by blast
      then have "\<epsilon> * exp(2 * of_real pi * ii * (0/n)) \<in> cball 0 \<epsilon>"
                "\<epsilon> * exp(2 * of_real pi * ii * (1/n)) \<in> cball 0 \<epsilon>"
        by (auto simp: norm_mult)
      with \<epsilon> have "\<epsilon> * exp(2 * of_real pi * ii * (0/n)) \<in> U"
                  "\<epsilon> * exp(2 * of_real pi * ii * (1/n)) \<in> U" by blast+
      then obtain y0 y1 where "y0 \<in> T" and y0: "(y0 - \<xi>) * g y0 = \<epsilon> * exp(2 * of_real pi * ii * (0/n))"
                          and "y1 \<in> T" and y1: "(y1 - \<xi>) * g y1 = \<epsilon> * exp(2 * of_real pi * ii * (1/n))"
        by (auto simp: U_def)
      then have "y0 \<in> ball \<xi> \<delta>" "y1 \<in> ball \<xi> \<delta>" using Tsb by auto
      moreover have "y0 \<noteq> y1"
        using y0 y1 \<open>\<epsilon> > 0\<close> complex_root_unity_eq_1 [of n 1] \<open>n > 0\<close> False by auto
      moreover have "T \<subseteq> S"
        by (meson Tsb min.cobounded1 order_trans r subset_ball)
      ultimately have False
        using inj_onD [OF injf, of y0 y1] \<open>y0 \<in> T\<close> \<open>y1 \<in> T\<close>
        using fd [of y0] fd [of y1] complex_root_unity [of n 1]
        apply (simp add: y0 y1 power_mult_distrib)
        apply (force simp: algebra_simps)
        done
      then show ?thesis ..
    qed
  qed
qed


text\<open>Hence a nice clean inverse function theorem\<close>

proposition holomorphic_has_inverse:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
  obtains g where "g holomorphic_on (f ` S)"
                  "\<And>z. z \<in> S \<Longrightarrow> deriv f z * deriv g (f z) = 1"
                  "\<And>z. z \<in> S \<Longrightarrow> g(f z) = z"
proof -
  have ofs: "open (f ` S)"
    by (rule open_mapping_thm3 [OF assms])
  have contf: "continuous_on S f"
    by (simp add: holf holomorphic_on_imp_continuous_on)
  have *: "(the_inv_into S f has_field_derivative inverse (deriv f z)) (at (f z))" if "z \<in> S" for z
  proof -
    have 1: "(f has_field_derivative deriv f z) (at z)"
      using DERIV_deriv_iff_field_differentiable \<open>z \<in> S\<close> \<open>open S\<close> holf holomorphic_on_imp_differentiable_at
      by blast
    have 2: "deriv f z \<noteq> 0"
      using \<open>z \<in> S\<close> \<open>open S\<close> holf holomorphic_injective_imp_regular injf by blast
    show ?thesis
      apply (rule has_complex_derivative_inverse_strong [OF 1 2 \<open>open S\<close> \<open>z \<in> S\<close>])
       apply (simp add: holf holomorphic_on_imp_continuous_on)
      by (simp add: injf the_inv_into_f_f)
  qed
  show ?thesis
    proof
      show "the_inv_into S f holomorphic_on f ` S"
        by (simp add: holomorphic_on_open ofs) (blast intro: *)
    next
      fix z assume "z \<in> S"
      have "deriv f z \<noteq> 0"
        using \<open>z \<in> S\<close> \<open>open S\<close> holf holomorphic_injective_imp_regular injf by blast
      then show "deriv f z * deriv (the_inv_into S f) (f z) = 1"
        using * [OF \<open>z \<in> S\<close>]  by (simp add: DERIV_imp_deriv)
    next
      fix z assume "z \<in> S"
      show "the_inv_into S f (f z) = z"
        by (simp add: \<open>z \<in> S\<close> injf the_inv_into_f_f)
  qed
qed


subsection\<open>The Schwarz Lemma\<close>

lemma Schwarz1:
  assumes holf: "f holomorphic_on S"
      and contf: "continuous_on (closure S) f"
      and S: "open S" "connected S"
      and boS: "bounded S"
      and "S \<noteq> {}"
  obtains w where "w \<in> frontier S"
                  "\<And>z. z \<in> closure S \<Longrightarrow> norm (f z) \<le> norm (f w)"
proof -
  have connf: "continuous_on (closure S) (norm o f)"
    using contf continuous_on_compose continuous_on_norm_id by blast
  have coc: "compact (closure S)"
    by (simp add: \<open>bounded S\<close> bounded_closure compact_eq_bounded_closed)
  then obtain x where x: "x \<in> closure S" and xmax: "\<And>z. z \<in> closure S \<Longrightarrow> norm(f z) \<le> norm(f x)"
    apply (rule bexE [OF continuous_attains_sup [OF _ _ connf]])
    using \<open>S \<noteq> {}\<close> apply auto
    done
  then show ?thesis
  proof (cases "x \<in> frontier S")
    case True
    then show ?thesis using that xmax by blast
  next
    case False
    then have "x \<in> S"
      using \<open>open S\<close> frontier_def interior_eq x by auto
    then have "f constant_on S"
      apply (rule maximum_modulus_principle [OF holf S \<open>open S\<close> order_refl])
      using closure_subset apply (blast intro: xmax)
      done
    then have "f constant_on (closure S)"
      by (rule constant_on_closureI [OF _ contf])
    then obtain c where c: "\<And>x. x \<in> closure S \<Longrightarrow> f x = c"
      by (meson constant_on_def)
    obtain w where "w \<in> frontier S"
      by (metis coc all_not_in_conv assms(6) closure_UNIV frontier_eq_empty not_compact_UNIV)
    then show ?thesis
      by (simp add: c frontier_def that)
  qed
qed

lemma Schwarz2:
 "\<lbrakk>f holomorphic_on ball 0 r;
    0 < s; ball w s \<subseteq> ball 0 r;
    \<And>z. norm (w-z) < s \<Longrightarrow> norm(f z) \<le> norm(f w)\<rbrakk>
    \<Longrightarrow> f constant_on ball 0 r"
by (rule maximum_modulus_principle [where U = "ball w s" and \<xi> = w]) (simp_all add: dist_norm)

lemma Schwarz3:
  assumes holf: "f holomorphic_on (ball 0 r)" and [simp]: "f 0 = 0"
  obtains h where "h holomorphic_on (ball 0 r)" and "\<And>z. norm z < r \<Longrightarrow> f z = z * (h z)" and "deriv f 0 = h 0"
proof -
  def h \<equiv> "\<lambda>z. if z = 0 then deriv f 0 else f z / z"
  have d0: "deriv f 0 = h 0"
    by (simp add: h_def)
  moreover have "h holomorphic_on (ball 0 r)"
    by (rule pole_theorem_open_0 [OF holf, of 0]) (auto simp: h_def)
  moreover have "norm z < r \<Longrightarrow> f z = z * h z" for z
    by (simp add: h_def)
  ultimately show ?thesis
    using that by blast
qed


proposition Schwarz_Lemma:
  assumes holf: "f holomorphic_on (ball 0 1)" and [simp]: "f 0 = 0"
      and no: "\<And>z. norm z < 1 \<Longrightarrow> norm (f z) < 1"
      and \<xi>: "norm \<xi> < 1"
    shows "norm (f \<xi>) \<le> norm \<xi>" and "norm(deriv f 0) \<le> 1"
      and "((\<exists>z. norm z < 1 \<and> z \<noteq> 0 \<and> norm(f z) = norm z) \<or> norm(deriv f 0) = 1)
           \<Longrightarrow> \<exists>\<alpha>. (\<forall>z. norm z < 1 \<longrightarrow> f z = \<alpha> * z) \<and> norm \<alpha> = 1" (is "?P \<Longrightarrow> ?Q")
proof -
  obtain h where holh: "h holomorphic_on (ball 0 1)"
             and fz_eq: "\<And>z. norm z < 1 \<Longrightarrow> f z = z * (h z)" and df0: "deriv f 0 = h 0"
    by (rule Schwarz3 [OF holf]) auto
  have noh_le: "norm (h z) \<le> 1" if z: "norm z < 1" for z
  proof -
    have "norm (h z) < a" if a: "1 < a" for a
    proof -
      have "max (inverse a) (norm z) < 1"
        using z a by (simp_all add: inverse_less_1_iff)
      then obtain r where r: "max (inverse a) (norm z) < r" and "r < 1"
        using Rats_dense_in_real by blast
      then have nzr: "norm z < r" and ira: "inverse r < a"
        using z a less_imp_inverse_less by force+
      then have "0 < r"
        by (meson norm_not_less_zero not_le order.strict_trans2)
      have holh': "h holomorphic_on ball 0 r"
        by (meson holh \<open>r < 1\<close> holomorphic_on_subset less_eq_real_def subset_ball)
      have conth': "continuous_on (cball 0 r) h"
        by (meson \<open>r < 1\<close> dual_order.trans holh holomorphic_on_imp_continuous_on holomorphic_on_subset mem_ball_0 mem_cball_0 not_less subsetI)
      obtain w where w: "norm w = r" and lenw: "\<And>z. norm z < r \<Longrightarrow> norm(h z) \<le> norm(h w)"
        apply (rule Schwarz1 [OF holh']) using conth' \<open>0 < r\<close> by auto
      have "h w = f w / w" using fz_eq \<open>r < 1\<close> nzr w by auto
      then have "cmod (h z) < inverse r"
        by (metis \<open>0 < r\<close> \<open>r < 1\<close> divide_strict_right_mono inverse_eq_divide
                  le_less_trans lenw no norm_divide nzr w)
      then show ?thesis using ira by linarith
    qed
    then show "norm (h z) \<le> 1"
      using not_le by blast
  qed
  show "cmod (f \<xi>) \<le> cmod \<xi>"
  proof (cases "\<xi> = 0")
    case True then show ?thesis by auto
  next
    case False
    then show ?thesis
      by (simp add: noh_le fz_eq \<xi> mult_left_le norm_mult)
  qed
  show no_df0: "norm(deriv f 0) \<le> 1"
    by (simp add: \<open>\<And>z. cmod z < 1 \<Longrightarrow> cmod (h z) \<le> 1\<close> df0)
  show "?Q" if "?P"
  using that
  proof
    assume "\<exists>z. cmod z < 1 \<and> z \<noteq> 0 \<and> cmod (f z) = cmod z"
    then obtain \<gamma> where \<gamma>: "cmod \<gamma> < 1" "\<gamma> \<noteq> 0" "cmod (f \<gamma>) = cmod \<gamma>" by blast
    then have [simp]: "norm (h \<gamma>) = 1"
      by (simp add: fz_eq norm_mult)
    have "ball \<gamma> (1 - cmod \<gamma>) \<subseteq> ball 0 1"
      by (simp add: ball_subset_ball_iff)
    moreover have "\<And>z. cmod (\<gamma> - z) < 1 - cmod \<gamma> \<Longrightarrow> cmod (h z) \<le> cmod (h \<gamma>)"
      apply (simp add: algebra_simps)
      by (metis add_diff_cancel_left' diff_diff_eq2 le_less_trans noh_le norm_triangle_ineq4)
    ultimately obtain c where c: "\<And>z. norm z < 1 \<Longrightarrow> h z = c"
      using Schwarz2 [OF holh, of "1 - norm \<gamma>" \<gamma>, unfolded constant_on_def] \<gamma> by auto
    moreover then have "norm c = 1"
      using \<gamma> by force
    ultimately show ?thesis
      using fz_eq by auto
  next
    assume [simp]: "cmod (deriv f 0) = 1"
    then obtain c where c: "\<And>z. norm z < 1 \<Longrightarrow> h z = c"
      using Schwarz2 [OF holh zero_less_one, of 0, unfolded constant_on_def] df0 noh_le
      by auto
    moreover have "norm c = 1"  using df0 c by auto
    ultimately show ?thesis
      using fz_eq by auto
  qed
qed

subsection\<open>The Schwarz reflection principle\<close>

lemma hol_pal_lem0:
  assumes "d \<bullet> a \<le> k" "k \<le> d \<bullet> b"
  obtains c where
     "c \<in> closed_segment a b" "d \<bullet> c = k"
     "\<And>z. z \<in> closed_segment a c \<Longrightarrow> d \<bullet> z \<le> k"
     "\<And>z. z \<in> closed_segment c b \<Longrightarrow> k \<le> d \<bullet> z"
proof -
  obtain c where cin: "c \<in> closed_segment a b" and keq: "k = d \<bullet> c"
    using connected_ivt_hyperplane [of "closed_segment a b" a b d k]
    by (auto simp: assms)
  have "closed_segment a c \<subseteq> {z. d \<bullet> z \<le> k}"  "closed_segment c b \<subseteq> {z. k \<le> d \<bullet> z}"
    unfolding segment_convex_hull using assms keq
    by (auto simp: convex_halfspace_le convex_halfspace_ge hull_minimal)
  then show ?thesis using cin that by fastforce
qed

lemma hol_pal_lem1:
  assumes "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
          "d \<noteq> 0" and lek: "d \<bullet> a \<le> k" "d \<bullet> b \<le> k" "d \<bullet> c \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof -
  have "interior (convex hull {a, b, c}) \<subseteq> interior(S \<inter> {x. d \<bullet> x \<le> k})"
    apply (rule interior_mono)
    apply (rule hull_minimal)
     apply (simp add: abc lek)
    apply (rule convex_Int [OF \<open>convex S\<close> convex_halfspace_le])
    done
  also have "... \<subseteq> {z \<in> S. d \<bullet> z < k}"
    by (force simp: interior_open [OF \<open>open S\<close>] \<open>d \<noteq> 0\<close>)
  finally have *: "interior (convex hull {a, b, c}) \<subseteq> {z \<in> S. d \<bullet> z < k}" .
  have "continuous_on (convex hull {a,b,c}) f"
    using \<open>convex S\<close> contf abc continuous_on_subset subset_hull
    by fastforce
  moreover have "f holomorphic_on interior (convex hull {a,b,c})"
    by (rule holomorphic_on_subset [OF holf1 *])
  ultimately show ?thesis
    using Cauchy_theorem_triangle_interior has_chain_integral_chain_integral3
      by blast
qed

lemma hol_pal_lem2:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
      and "d \<noteq> 0" and lek: "d \<bullet> a \<le> k" "d \<bullet> b \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "d \<bullet> c \<le> k")
  case True show ?thesis
    by (rule hol_pal_lem1 [OF S abc \<open>d \<noteq> 0\<close> lek True holf1 contf])
next
  case False
  then have "d \<bullet> c > k" by force
  obtain a' where a': "a' \<in> closed_segment b c" and "d \<bullet> a' = k"
     and ba': "\<And>z. z \<in> closed_segment b a' \<Longrightarrow> d \<bullet> z \<le> k"
     and a'c: "\<And>z. z \<in> closed_segment a' c \<Longrightarrow> k \<le> d \<bullet> z"
    apply (rule hol_pal_lem0 [of d b k c, OF \<open>d \<bullet> b \<le> k\<close>])
    using False by auto
  obtain b' where b': "b' \<in> closed_segment a c" and "d \<bullet> b' = k"
     and ab': "\<And>z. z \<in> closed_segment a b' \<Longrightarrow> d \<bullet> z \<le> k"
     and b'c: "\<And>z. z \<in> closed_segment b' c \<Longrightarrow> k \<le> d \<bullet> z"
    apply (rule hol_pal_lem0 [of d a k c, OF \<open>d \<bullet> a \<le> k\<close>])
    using False by auto
  have a'b': "a' \<in> S \<and> b' \<in> S"
    using a' abc b' convex_contains_segment \<open>convex S\<close> by auto
  have "continuous_on (closed_segment c a) f"
    by (meson abc contf continuous_on_subset convex_contains_segment \<open>convex S\<close>)
  then have 1: "contour_integral (linepath c a) f =
                contour_integral (linepath c b') f + contour_integral (linepath b' a) f"
    apply (rule contour_integral_split_linepath)
    using b' by (simp add: closed_segment_commute)
  have "continuous_on (closed_segment b c) f"
    by (meson abc contf continuous_on_subset convex_contains_segment \<open>convex S\<close>)
  then have 2: "contour_integral (linepath b c) f =
                contour_integral (linepath b a') f + contour_integral (linepath a' c) f"
    by (rule contour_integral_split_linepath [OF _ a'])
  have 3: "contour_integral (reversepath (linepath b' a')) f =
                - contour_integral (linepath b' a') f"
    by (rule contour_integral_reversepath [OF valid_path_linepath])
  have fcd_le: "f field_differentiable at x"
               if "x \<in> interior S \<and> x \<in> interior {x. d \<bullet> x \<le> k}" for x
  proof -
    have "f holomorphic_on S \<inter> {c. d \<bullet> c < k}"
      by (metis (no_types) Collect_conj_eq Collect_mem_eq holf1)
    then have "\<exists>C D. x \<in> interior C \<inter> interior D \<and> f holomorphic_on interior C \<inter> interior D"
      using that
      by (metis Collect_mem_eq Int_Collect \<open>d \<noteq> 0\<close> interior_halfspace_le interior_open \<open>open S\<close>)
    then show "f field_differentiable at x"
      by (metis at_within_interior holomorphic_on_def interior_Int interior_interior)
  qed
  have ab_le: "\<And>x. x \<in> closed_segment a b \<Longrightarrow> d \<bullet> x \<le> k"
  proof -
    fix x :: complex
    assume "x \<in> closed_segment a b"
    then have "\<And>C. x \<in> C \<or> b \<notin> C \<or> a \<notin> C \<or> \<not> convex C"
      by (meson contra_subsetD convex_contains_segment)
    then show "d \<bullet> x \<le> k"
      by (metis lek convex_halfspace_le mem_Collect_eq)
  qed
  have "continuous_on (S \<inter> {x. d \<bullet> x \<le> k}) f" using contf
    by (simp add: continuous_on_subset)
  then have "(f has_contour_integral 0)
         (linepath a b +++ linepath b a' +++ linepath a' b' +++ linepath b' a)"
    apply (rule Cauchy_theorem_convex [where k = "{}"])
    apply (simp_all add: path_image_join convex_Int convex_halfspace_le \<open>convex S\<close> fcd_le ab_le
                closed_segment_subset abc a'b' ba')
    by (metis \<open>d \<bullet> a' = k\<close> \<open>d \<bullet> b' = k\<close> convex_contains_segment convex_halfspace_le lek(1) mem_Collect_eq order_refl)
  then have 4: "contour_integral (linepath a b) f +
                contour_integral (linepath b a') f +
                contour_integral (linepath a' b') f +
                contour_integral (linepath b' a) f = 0"
    by (rule has_chain_integral_chain_integral4)
  have fcd_ge: "f field_differentiable at x"
               if "x \<in> interior S \<and> x \<in> interior {x. k \<le> d \<bullet> x}" for x
  proof -
    have f2: "f holomorphic_on S \<inter> {c. k < d \<bullet> c}"
      by (metis (full_types) Collect_conj_eq Collect_mem_eq holf2)
    have f3: "interior S = S"
      by (simp add: interior_open \<open>open S\<close>)
    then have "x \<in> S \<inter> interior {c. k \<le> d \<bullet> c}"
      using that by simp
    then show "f field_differentiable at x"
      using f3 f2 unfolding holomorphic_on_def
      by (metis (no_types) \<open>d \<noteq> 0\<close> at_within_interior interior_Int interior_halfspace_ge interior_interior)
  qed
  have "continuous_on (S \<inter> {x. k \<le> d \<bullet> x}) f" using contf
    by (simp add: continuous_on_subset)
  then have "(f has_contour_integral 0) (linepath a' c +++ linepath c b' +++ linepath b' a')"
    apply (rule Cauchy_theorem_convex [where k = "{}"])
    apply (simp_all add: path_image_join convex_Int convex_halfspace_ge \<open>convex S\<close>
                      fcd_ge closed_segment_subset abc a'b' a'c)
    by (metis \<open>d \<bullet> a' = k\<close> b'c closed_segment_commute convex_contains_segment
              convex_halfspace_ge ends_in_segment(2) mem_Collect_eq order_refl)
  then have 5: "contour_integral (linepath a' c) f + contour_integral (linepath c b') f + contour_integral (linepath b' a') f = 0"
    by (rule has_chain_integral_chain_integral3)
  show ?thesis
    using 1 2 3 4 5 by (metis add.assoc eq_neg_iff_add_eq_0 reversepath_linepath)
qed

lemma hol_pal_lem3:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
      and "d \<noteq> 0" and lek: "d \<bullet> a \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "d \<bullet> b \<le> k")
  case True show ?thesis
    by (rule hol_pal_lem2 [OF S abc \<open>d \<noteq> 0\<close> lek True holf1 holf2 contf])
next
  case False
  show ?thesis
  proof (cases "d \<bullet> c \<le> k")
    case True
    have "contour_integral (linepath c a) f +
          contour_integral (linepath a b) f +
          contour_integral (linepath b c) f = 0"
      by (rule hol_pal_lem2 [OF S \<open>c \<in> S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close> \<open>d \<noteq> 0\<close> \<open>d \<bullet> c \<le> k\<close> lek holf1 holf2 contf])
    then show ?thesis
      by (simp add: algebra_simps)
  next
    case False
    have "contour_integral (linepath b c) f +
          contour_integral (linepath c a) f +
          contour_integral (linepath a b) f = 0"
      apply (rule hol_pal_lem2 [OF S \<open>b \<in> S\<close> \<open>c \<in> S\<close> \<open>a \<in> S\<close>, of "-d" "-k"])
      using \<open>d \<noteq> 0\<close> \<open>\<not> d \<bullet> b \<le> k\<close> False by (simp_all add: holf1 holf2 contf)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
qed

lemma hol_pal_lem4:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S" and "d \<noteq> 0"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "d \<bullet> a \<le> k")
  case True show ?thesis
    by (rule hol_pal_lem3 [OF S abc \<open>d \<noteq> 0\<close> True holf1 holf2 contf])
next
  case False
  show ?thesis
    apply (rule hol_pal_lem3 [OF S abc, of "-d" "-k"])
    using \<open>d \<noteq> 0\<close> False by (simp_all add: holf1 holf2 contf)
qed

proposition holomorphic_on_paste_across_line:
  assumes S: "open S" and "d \<noteq> 0"
      and holf1: "f holomorphic_on (S \<inter> {z. d \<bullet> z < k})"
      and holf2: "f holomorphic_on (S \<inter> {z. k < d \<bullet> z})"
      and contf: "continuous_on S f"
    shows "f holomorphic_on S"
proof -
  have *: "\<exists>t. open t \<and> p \<in> t \<and> continuous_on t f \<and>
               (\<forall>a b c. convex hull {a, b, c} \<subseteq> t \<longrightarrow>
                         contour_integral (linepath a b) f +
                         contour_integral (linepath b c) f +
                         contour_integral (linepath c a) f = 0)"
          if "p \<in> S" for p
  proof -
    obtain e where "e>0" and e: "ball p e \<subseteq> S"
      using \<open>p \<in> S\<close> openE S by blast
    then have "continuous_on (ball p e) f"
      using contf continuous_on_subset by blast
    moreover have "f holomorphic_on {z. dist p z < e \<and> d \<bullet> z < k}"
      apply (rule holomorphic_on_subset [OF holf1])
      using e by auto
    moreover have "f holomorphic_on {z. dist p z < e \<and> k < d \<bullet> z}"
      apply (rule holomorphic_on_subset [OF holf2])
      using e by auto
    ultimately show ?thesis
      apply (rule_tac x="ball p e" in exI)
      using \<open>e > 0\<close> e \<open>d \<noteq> 0\<close>
      apply (simp add:, clarify)
      apply (rule hol_pal_lem4 [of "ball p e" _ _ _ d _ k])
      apply (auto simp: subset_hull)
      done
  qed
  show ?thesis
    by (blast intro: * Morera_local_triangle analytic_imp_holomorphic)
qed

proposition Schwarz_reflection:
  assumes "open S" and cnjs: "cnj ` S \<subseteq> S"
      and  holf: "f holomorphic_on (S \<inter> {z. 0 < Im z})"
      and contf: "continuous_on (S \<inter> {z. 0 \<le> Im z}) f"
      and f: "\<And>z. \<lbrakk>z \<in> S; z \<in> \<real>\<rbrakk> \<Longrightarrow> (f z) \<in> \<real>"
    shows "(\<lambda>z. if 0 \<le> Im z then f z else cnj(f(cnj z))) holomorphic_on S"
proof -
  have 1: "(\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z))) holomorphic_on (S \<inter> {z. 0 < Im z})"
    by (force intro: iffD1 [OF holomorphic_cong [OF refl] holf])
  have cont_cfc: "continuous_on (S \<inter> {z. Im z \<le> 0}) (cnj o f o cnj)"
    apply (intro continuous_intros continuous_on_compose continuous_on_subset [OF contf])
    using cnjs apply auto
    done
  have "cnj \<circ> f \<circ> cnj field_differentiable at x within S \<inter> {z. Im z < 0}"
        if "x \<in> S" "Im x < 0" "f field_differentiable at (cnj x) within S \<inter> {z. 0 < Im z}" for x
    using that
    apply (simp add: field_differentiable_def Derivative.DERIV_within_iff Lim_within dist_norm, clarify)
    apply (rule_tac x="cnj f'" in exI)
    apply (elim all_forward ex_forward conj_forward imp_forward asm_rl, clarify)
    apply (drule_tac x="cnj xa" in bspec)
    using cnjs apply force
    apply (metis complex_cnj_cnj complex_cnj_diff complex_cnj_divide complex_mod_cnj)
    done
  then have hol_cfc: "(cnj o f o cnj) holomorphic_on (S \<inter> {z. Im z < 0})"
    using holf cnjs
    by (force simp: holomorphic_on_def)
  have 2: "(\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z))) holomorphic_on (S \<inter> {z. Im z < 0})"
    apply (rule iffD1 [OF holomorphic_cong [OF refl]])
    using hol_cfc by auto
  have [simp]: "(S \<inter> {z. 0 \<le> Im z}) \<union> (S \<inter> {z. Im z \<le> 0}) = S"
    by force
  have "continuous_on ((S \<inter> {z. 0 \<le> Im z}) \<union> (S \<inter> {z. Im z \<le> 0}))
                       (\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z)))"
    apply (rule continuous_on_cases_local)
    using cont_cfc contf
    apply (simp_all add: closedin_closed_Int closed_halfspace_Im_le closed_halfspace_Im_ge)
    using f Reals_cnj_iff complex_is_Real_iff apply auto
    done
  then have 3: "continuous_on S (\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z)))"
    by force
  show ?thesis
    apply (rule holomorphic_on_paste_across_line [OF \<open>open S\<close>, of "-ii" _ 0])
    using 1 2 3
    apply auto
    done
qed

subsection\<open>Bloch's theorem\<close>

lemma Bloch_lemma_0:
  assumes holf: "f holomorphic_on cball 0 r" and "0 < r"
      and [simp]: "f 0 = 0"
      and le: "\<And>z. norm z < r \<Longrightarrow> norm(deriv f z) \<le> 2 * norm(deriv f 0)"
    shows "ball 0 ((3 - 2 * sqrt 2) * r * norm(deriv f 0)) \<subseteq> f ` ball 0 r"
proof -
  have "sqrt 2 < 3/2"
    by (rule real_less_lsqrt) (auto simp: power2_eq_square)
  then have sq3: "0 < 3 - 2 * sqrt 2" by simp
  show ?thesis
  proof (cases "deriv f 0 = 0")
    case True then show ?thesis by simp
  next
    case False
    def C \<equiv> "2 * norm(deriv f 0)"
    have "0 < C" using False by (simp add: C_def)
    have holf': "f holomorphic_on ball 0 r" using holf
      using ball_subset_cball holomorphic_on_subset by blast
    then have holdf': "deriv f holomorphic_on ball 0 r"
      by (rule holomorphic_deriv [OF _ open_ball])
    have "Le1": "norm(deriv f z - deriv f 0) \<le> norm z / (r - norm z) * C"
                if "norm z < r" for z
    proof -
      have T1: "norm(deriv f z - deriv f 0) \<le> norm z / (R - norm z) * C"
              if R: "norm z < R" "R < r" for R
      proof -
        have "0 < R" using R
          by (metis less_trans norm_zero zero_less_norm_iff)
        have df_le: "\<And>x. norm x < r \<Longrightarrow> norm (deriv f x) \<le> C"
          using le by (simp add: C_def)
        have hol_df: "deriv f holomorphic_on cball 0 R"
          apply (rule holomorphic_on_subset) using R holdf' by auto
        have *: "((\<lambda>w. deriv f w / (w - z)) has_contour_integral 2 * pi * \<i> * deriv f z) (circlepath 0 R)"
                 if "norm z < R" for z
          using \<open>0 < R\<close> that Cauchy_integral_formula_convex_simple [OF convex_cball hol_df, of _ "circlepath 0 R"]
          by (force simp: winding_number_circlepath)
        have **: "((\<lambda>x. deriv f x / (x - z) - deriv f x / x) has_contour_integral
                   of_real (2 * pi) * \<i> * (deriv f z - deriv f 0))
                  (circlepath 0 R)"
           using has_contour_integral_diff [OF * [of z] * [of 0]] \<open>0 < R\<close> that
           by (simp add: algebra_simps)
        have [simp]: "\<And>x. norm x = R \<Longrightarrow> x \<noteq> z"  using that(1) by blast
        have "norm (deriv f x / (x - z) - deriv f x / x)
                     \<le> C * norm z / (R * (R - norm z))"
                  if "norm x = R" for x
        proof -
          have [simp]: "norm (deriv f x * x - deriv f x * (x - z)) =
                        norm (deriv f x) * norm z"
            by (simp add: norm_mult right_diff_distrib')
          show ?thesis
            using  \<open>0 < R\<close> \<open>0 < C\<close> R that
            apply (simp add: norm_mult norm_divide divide_simps)
            using df_le norm_triangle_ineq2 \<open>0 < C\<close> apply (auto intro!: mult_mono)
            done
        qed
        then show ?thesis
          using has_contour_integral_bound_circlepath
                  [OF **, of "C * norm z/(R*(R - norm z))"]
                \<open>0 < R\<close> \<open>0 < C\<close> R
          apply (simp add: norm_mult norm_divide)
          apply (simp add: divide_simps mult.commute)
          done
      qed
      obtain r' where r': "norm z < r'" "r' < r"
        using Rats_dense_in_real [of "norm z" r] \<open>norm z < r\<close> by blast
      then have [simp]: "closure {r'<..<r} = {r'..r}" by simp
      show ?thesis
        apply (rule continuous_ge_on_closure
                 [where f = "\<lambda>r. norm z / (r - norm z) * C" and s = "{r'<..<r}",
                  OF _ _ T1])
        apply (intro continuous_intros)
        using that r'
        apply (auto simp: not_le)
        done
    qed
    have "*": "(norm z - norm z^2/(r - norm z)) * norm(deriv f 0) \<le> norm(f z)"
              if r: "norm z < r" for z
    proof -
      have 1: "\<And>x. x \<in> ball 0 r \<Longrightarrow>
              ((\<lambda>z. f z - deriv f 0 * z) has_field_derivative deriv f x - deriv f 0)
               (at x within ball 0 r)"
        by (rule derivative_eq_intros holomorphic_derivI holf' | simp)+
      have 2: "closed_segment 0 z \<subseteq> ball 0 r"
        by (metis \<open>0 < r\<close> convex_ball convex_contains_segment dist_self mem_ball mem_ball_0 that)
      have 3: "(\<lambda>t. (norm z)\<^sup>2 * t / (r - norm z) * C) integrable_on {0..1}"
        apply (rule integrable_on_cmult_right [where 'b=real, simplified])
        apply (rule integrable_on_cdivide [where 'b=real, simplified])
        apply (rule integrable_on_cmult_left [where 'b=real, simplified])
        apply (rule ident_integrable_on)
        done
      have 4: "norm (deriv f (x *\<^sub>R z) - deriv f 0) * norm z \<le> norm z * norm z * x * C / (r - norm z)"
              if x: "0 \<le> x" "x \<le> 1" for x
      proof -
        have [simp]: "x * norm z < r"
          using r x by (meson le_less_trans mult_le_cancel_right2 norm_not_less_zero)
        have "norm (deriv f (x *\<^sub>R z) - deriv f 0) \<le> norm (x *\<^sub>R z) / (r - norm (x *\<^sub>R z)) * C"
          apply (rule Le1) using r x \<open>0 < r\<close> by simp
        also have "... \<le> norm (x *\<^sub>R z) / (r - norm z) * C"
          using r x \<open>0 < r\<close>
          apply (simp add: divide_simps)
          by (simp add: \<open>0 < C\<close> mult.assoc mult_left_le_one_le ordered_comm_semiring_class.comm_mult_left_mono)
        finally have "norm (deriv f (x *\<^sub>R z) - deriv f 0) * norm z \<le> norm (x *\<^sub>R z)  / (r - norm z) * C * norm z"
          by (rule mult_right_mono) simp
        with x show ?thesis by (simp add: algebra_simps)
      qed
      have le_norm: "abc \<le> norm d - e \<Longrightarrow> norm(f - d) \<le> e \<Longrightarrow> abc \<le> norm f" for abc d e and f::complex
        by (metis add_diff_cancel_left' add_diff_eq diff_left_mono norm_diff_ineq order_trans)
      have "norm (integral {0..1} (\<lambda>x. (deriv f (x *\<^sub>R z) - deriv f 0) * z))
            \<le> integral {0..1} (\<lambda>t. (norm z)\<^sup>2 * t / (r - norm z) * C)"
        apply (rule integral_norm_bound_integral)
        using contour_integral_primitive [OF 1, of "linepath 0 z"] 2
        apply (simp add: has_contour_integral_linepath has_integral_integrable_integral)
        apply (rule 3)
        apply (simp add: norm_mult power2_eq_square 4)
        done
      then have int_le: "norm (f z - deriv f 0 * z) \<le> (norm z)\<^sup>2 * norm(deriv f 0) / ((r - norm z))"
        using contour_integral_primitive [OF 1, of "linepath 0 z"] 2
        apply (simp add: has_contour_integral_linepath has_integral_integrable_integral C_def)
        done
      show ?thesis
        apply (rule le_norm [OF _ int_le])
        using \<open>norm z < r\<close>
        apply (simp add: power2_eq_square divide_simps C_def norm_mult)
        proof -
          have "norm z * (norm (deriv f 0) * (r - norm z - norm z)) \<le> norm z * (norm (deriv f 0) * (r - norm z) - norm (deriv f 0) * norm z)"
            by (simp add: linordered_field_class.sign_simps(38))
          then show "(norm z * (r - norm z) - norm z * norm z) * norm (deriv f 0) \<le> norm (deriv f 0) * norm z * (r - norm z) - norm z * norm z * norm (deriv f 0)"
            by (simp add: linordered_field_class.sign_simps(38) mult.commute mult.left_commute)
        qed
    qed
    have sq201 [simp]: "0 < (1 - sqrt 2 / 2)" "(1 - sqrt 2 / 2)  < 1"
      by (auto simp:  sqrt2_less_2)
    have 1: "continuous_on (closure (ball 0 ((1 - sqrt 2 / 2) * r))) f"
      apply (rule continuous_on_subset [OF holomorphic_on_imp_continuous_on [OF holf]])
      apply (subst closure_ball)
      using \<open>0 < r\<close> mult_pos_pos sq201
      apply (auto simp: cball_subset_cball_iff)
      done
    have 2: "open (f ` interior (ball 0 ((1 - sqrt 2 / 2) * r)))"
      apply (rule open_mapping_thm [OF holf' open_ball connected_ball], force)
      using \<open>0 < r\<close> mult_pos_pos sq201 apply (simp add: ball_subset_ball_iff)
      using False \<open>0 < r\<close> centre_in_ball holf' holomorphic_nonconstant by blast
    have "ball 0 ((3 - 2 * sqrt 2) * r * norm (deriv f 0)) =
          ball (f 0) ((3 - 2 * sqrt 2) * r * norm (deriv f 0))"
      by simp
    also have "...  \<subseteq> f ` ball 0 ((1 - sqrt 2 / 2) * r)"
    proof -
      have 3: "(3 - 2 * sqrt 2) * r * norm (deriv f 0) \<le> norm (f z)"
           if "norm z = (1 - sqrt 2 / 2) * r" for z
        apply (rule order_trans [OF _ *])
        using  \<open>0 < r\<close>
        apply (simp_all add: field_simps  power2_eq_square that)
        apply (simp add: mult.assoc [symmetric])
        done
      show ?thesis
        apply (rule ball_subset_open_map_image [OF 1 2 _ bounded_ball])
        using \<open>0 < r\<close> sq201 3 apply simp_all
        using C_def \<open>0 < C\<close> sq3 apply force
        done
     qed
    also have "...  \<subseteq> f ` ball 0 r"
      apply (rule image_subsetI [OF imageI], simp)
      apply (erule less_le_trans)
      using \<open>0 < r\<close> apply (auto simp: field_simps)
      done
    finally show ?thesis .
  qed
qed

lemma Bloch_lemma: 
  assumes holf: "f holomorphic_on cball a r" and "0 < r"
      and le: "\<And>z. z \<in> ball a r \<Longrightarrow> norm(deriv f z) \<le> 2 * norm(deriv f a)"
    shows "ball (f a) ((3 - 2 * sqrt 2) * r * norm(deriv f a)) \<subseteq> f ` ball a r"
proof -
  have fz: "(\<lambda>z. f (a + z)) = f o (\<lambda>z. (a + z))"
    by (simp add: o_def)
  have hol0: "(\<lambda>z. f (a + z)) holomorphic_on cball 0 r"
    unfolding fz by (intro holomorphic_intros holf holomorphic_on_compose | simp)+
  then have [simp]: "\<And>x. norm x < r \<Longrightarrow> (\<lambda>z. f (a + z)) field_differentiable at x"
    by (metis Topology_Euclidean_Space.open_ball at_within_open ball_subset_cball diff_0 dist_norm holomorphic_on_def holomorphic_on_subset mem_ball norm_minus_cancel)
  have [simp]: "\<And>z. norm z < r \<Longrightarrow> f field_differentiable at (a + z)"
    by (metis holf open_ball add_diff_cancel_left' dist_complex_def holomorphic_on_imp_differentiable_at holomorphic_on_subset interior_cball interior_subset mem_ball norm_minus_commute)
  then have [simp]: "f field_differentiable at a"
    by (metis add.comm_neutral \<open>0 < r\<close> norm_eq_zero)
  have hol1: "(\<lambda>z. f (a + z) - f a) holomorphic_on cball 0 r"
    by (intro holomorphic_intros hol0)
  then have "ball 0 ((3 - 2 * sqrt 2) * r * norm (deriv (\<lambda>z. f (a + z) - f a) 0))
             \<subseteq> (\<lambda>z. f (a + z) - f a) ` ball 0 r"
    apply (rule Bloch_lemma_0)
    apply (simp_all add: \<open>0 < r\<close>)
    apply (simp add: fz complex_derivative_chain)
    apply (simp add: dist_norm le)
    done
  then show ?thesis
    apply clarify
    apply (drule_tac c="x - f a" in subsetD)
     apply (force simp: fz \<open>0 < r\<close> dist_norm complex_derivative_chain field_differentiable_compose)+
    done
qed

proposition Bloch_unit: 
  assumes holf: "f holomorphic_on ball a 1" and [simp]: "deriv f a = 1"
  obtains b r where "1/12 < r" "ball b r \<subseteq> f ` (ball a 1)"
proof -
  def r \<equiv> "249/256::real"
  have "0 < r" "r < 1" by (auto simp: r_def)
  def g \<equiv> "\<lambda>z. deriv f z * of_real(r - norm(z - a))"
  have "deriv f holomorphic_on ball a 1"
    by (rule holomorphic_deriv [OF holf open_ball])
  then have "continuous_on (ball a 1) (deriv f)"
    using holomorphic_on_imp_continuous_on by blast
  then have "continuous_on (cball a r) (deriv f)"
    by (rule continuous_on_subset) (simp add: cball_subset_ball_iff \<open>r < 1\<close>)
  then have "continuous_on (cball a r) g"
    by (simp add: g_def continuous_intros)
  then have 1: "compact (g ` cball a r)"
    by (rule compact_continuous_image [OF _ compact_cball])
  have 2: "g ` cball a r \<noteq> {}"
    using \<open>r > 0\<close> by auto
  obtain p where pr: "p \<in> cball a r" 
             and pge: "\<And>y. y \<in> cball a r \<Longrightarrow> norm (g y) \<le> norm (g p)"
    using distance_attains_sup [OF 1 2, of 0] by force
  def t \<equiv> "(r - norm(p - a)) / 2"
  have "norm (p - a) \<noteq> r"
    using pge [of a] \<open>r > 0\<close> by (auto simp: g_def norm_mult)
  then have "norm (p - a) < r" using pr 
    by (simp add: norm_minus_commute dist_norm)
  then have "0 < t" 
    by (simp add: t_def)
  have cpt: "cball p t \<subseteq> ball a r"
    using \<open>0 < t\<close> by (simp add: cball_subset_ball_iff dist_norm t_def field_simps)
  have gen_le_dfp: "norm (deriv f y) * (r - norm (y - a)) / (r - norm (p - a)) \<le> norm (deriv f p)" 
            if "y \<in> cball a r" for y
  proof -
    have [simp]: "norm (y - a) \<le> r"
      using that by (simp add: dist_norm norm_minus_commute) 
    have "norm (g y) \<le> norm (g p)"
      using pge [OF that] by simp
    then have "norm (deriv f y) * abs (r - norm (y - a)) \<le> norm (deriv f p) * abs (r - norm (p - a))"
      by (simp only: dist_norm g_def norm_mult norm_of_real)
    with that \<open>norm (p - a) < r\<close> show ?thesis
      by (simp add: dist_norm divide_simps)
  qed
  have le_norm_dfp: "r / (r - norm (p - a)) \<le> norm (deriv f p)"
    using gen_le_dfp [of a] \<open>r > 0\<close> by auto
  have 1: "f holomorphic_on cball p t"
    apply (rule holomorphic_on_subset [OF holf])
    using cpt \<open>r < 1\<close> order_subst1 subset_ball by auto
  have 2: "norm (deriv f z) \<le> 2 * norm (deriv f p)" if "z \<in> ball p t" for z
  proof -
    have z: "z \<in> cball a r"
      by (meson ball_subset_cball subsetD cpt that)
    then have "norm(z - a) < r"
      by (metis ball_subset_cball contra_subsetD cpt dist_norm mem_ball norm_minus_commute that)
    have "norm (deriv f z) * (r - norm (z - a)) / (r - norm (p - a)) \<le> norm (deriv f p)" 
      using gen_le_dfp [OF z] by simp
    with \<open>norm (z - a) < r\<close> \<open>norm (p - a) < r\<close> 
    have "norm (deriv f z) \<le> (r - norm (p - a)) / (r - norm (z - a)) * norm (deriv f p)"
       by (simp add: field_simps)
    also have "... \<le> 2 * norm (deriv f p)"
      apply (rule mult_right_mono)
      using that \<open>norm (p - a) < r\<close> \<open>norm(z - a) < r\<close> 
      apply (simp_all add: field_simps t_def dist_norm [symmetric])
      using dist_triangle3 [of z a p] by linarith
    finally show ?thesis .
  qed
  have sqrt2: "sqrt 2 < 2113/1494"
    by (rule real_less_lsqrt) (auto simp: power2_eq_square)
  then have sq3: "0 < 3 - 2 * sqrt 2" by simp
  have "1 / 12 / ((3 - 2 * sqrt 2) / 2) < r"
    using sq3 sqrt2 by (auto simp: field_simps r_def) 
  also have "... \<le> cmod (deriv f p) * (r - cmod (p - a))"
    using \<open>norm (p - a) < r\<close> le_norm_dfp   by (simp add: pos_divide_le_eq)    
  finally have "1 / 12 < cmod (deriv f p) * (r - cmod (p - a)) * ((3 - 2 * sqrt 2) / 2)"  
    using pos_divide_less_eq half_gt_zero_iff sq3 by blast
  then have **: "1 / 12 < (3 - 2 * sqrt 2) * t * norm (deriv f p)"
    using sq3 by (simp add: mult.commute t_def)
  have "ball (f p) ((3 - 2 * sqrt 2) * t * norm (deriv f p)) \<subseteq> f ` ball p t"
    by (rule Bloch_lemma [OF 1 \<open>0 < t\<close> 2])
  also have "... \<subseteq> f ` ball a 1"
    apply (rule image_mono)
    apply (rule order_trans [OF ball_subset_cball])
    apply (rule order_trans [OF cpt])
    using \<open>0 < t\<close> \<open>r < 1\<close> apply (simp add: ball_subset_ball_iff dist_norm)
    done
  finally have "ball (f p) ((3 - 2 * sqrt 2) * t * norm (deriv f p)) \<subseteq> f ` ball a 1" .
  with ** show ?thesis
    by (rule that)
qed


theorem Bloch:
  assumes holf: "f holomorphic_on ball a r" and "0 < r" 
      and r': "r' \<le> r * norm (deriv f a) / 12"
  obtains b where "ball b r' \<subseteq> f ` (ball a r)"
proof (cases "deriv f a = 0")
  case True with r' show ?thesis
    using ball_eq_empty that by fastforce
next
  case False
    def C \<equiv> "deriv f a"
    have "0 < norm C" using False by (simp add: C_def)
    have dfa: "f field_differentiable at a"
      apply (rule holomorphic_on_imp_differentiable_at [OF holf])
      using \<open>0 < r\<close> by auto
    have fo: "(\<lambda>z. f (a + of_real r * z)) = f o (\<lambda>z. (a + of_real r * z))"
      by (simp add: o_def)
    have holf': "f holomorphic_on (\<lambda>z. a + complex_of_real r * z) ` ball 0 1"
      apply (rule holomorphic_on_subset [OF holf])
      using \<open>0 < r\<close> apply (force simp: dist_norm norm_mult)
      done
    have 1: "(\<lambda>z. f (a + r * z) / (C * r)) holomorphic_on ball 0 1"
      apply (rule holomorphic_intros holomorphic_on_compose holf' | simp add: fo)+
      using \<open>0 < r\<close> by (simp add: C_def False)
    have "((\<lambda>z. f (a + of_real r * z) / (C * of_real r)) has_field_derivative
          (deriv f (a + of_real r * z) / C)) (at z)" 
         if "norm z < 1" for z
    proof -
    have *: "((\<lambda>x. f (a + of_real r * x)) has_field_derivative
             (deriv f (a + of_real r * z) * of_real r)) (at z)"
        apply (simp add: fo)
        apply (rule DERIV_chain [OF field_differentiable_derivI])
        apply (rule holomorphic_on_imp_differentiable_at [OF holf], simp)
        using \<open>0 < r\<close> apply (simp add: dist_norm norm_mult that)
        apply (rule derivative_eq_intros | simp)+
        done
      show ?thesis
        apply (rule derivative_eq_intros * | simp)+
        using \<open>0 < r\<close> by (auto simp: C_def False)
    qed
    have 2: "deriv (\<lambda>z. f (a + of_real r * z) / (C * of_real r)) 0 = 1"
      apply (subst deriv_cdivide_right)
      apply (simp add: field_differentiable_def fo)
      apply (rule exI)
      apply (rule DERIV_chain [OF field_differentiable_derivI])
      apply (simp add: dfa)
      apply (rule derivative_eq_intros | simp add: C_def False fo)+
      using \<open>0 < r\<close> 
      apply (simp add: C_def False fo)
      apply (simp add: derivative_intros dfa complex_derivative_chain)
      done
    have sb1: "op * (C * r) ` (\<lambda>z. f (a + of_real r * z) / (C * r)) ` ball 0 1 
               \<subseteq> f ` ball a r"
      using \<open>0 < r\<close> by (auto simp: dist_norm norm_mult C_def False)
    have sb2: "ball (C * r * b) r' \<subseteq> op * (C * r) ` ball b t" 
               if "1 / 12 < t" for b t
    proof -
      have *: "r * cmod (deriv f a) / 12 \<le> r * (t * cmod (deriv f a))"
        using that \<open>0 < r\<close> less_eq_real_def mult.commute mult.right_neutral mult_left_mono norm_ge_zero times_divide_eq_right 
        by auto
      show ?thesis
        apply clarify
        apply (rule_tac x="x / (C * r)" in image_eqI)
        using \<open>0 < r\<close>  
        apply (simp_all add: dist_norm norm_mult norm_divide C_def False field_simps)
        apply (erule less_le_trans)
        apply (rule order_trans [OF r' *])
        done
    qed
    show ?thesis
      apply (rule Bloch_unit [OF 1 2])
      apply (rename_tac t)
      apply (rule_tac b="(C * of_real r) * b" in that)
      apply (drule image_mono [where f = "\<lambda>z. (C * of_real r) * z"])
      using sb1 sb2
      apply force
      done
qed

corollary Bloch_general:
  assumes holf: "f holomorphic_on s" and "a \<in> s" 
      and tle: "\<And>z. z \<in> frontier s \<Longrightarrow> t \<le> dist a z"
      and rle: "r \<le> t * norm(deriv f a) / 12"
  obtains b where "ball b r \<subseteq> f ` s"
proof -
  consider "r \<le> 0" | "0 < t * norm(deriv f a) / 12" using rle by force
  then show ?thesis
  proof cases
    case 1 then show ?thesis
      by (simp add: Topology_Euclidean_Space.ball_empty that)
  next
    case 2
    show ?thesis
    proof (cases "deriv f a = 0")
      case True then show ?thesis
        using rle by (simp add: Topology_Euclidean_Space.ball_empty that)
    next
      case False
      then have "t > 0"
        using 2 by (force simp: zero_less_mult_iff)
      have "~ ball a t \<subseteq> s \<Longrightarrow> ball a t \<inter> frontier s \<noteq> {}"
        apply (rule connected_Int_frontier [of "ball a t" s], simp_all)
        using \<open>0 < t\<close> \<open>a \<in> s\<close> centre_in_ball apply blast
        done
      with tle have *: "ball a t \<subseteq> s" by fastforce
      then have 1: "f holomorphic_on ball a t"
        using holf using holomorphic_on_subset by blast
      show ?thesis
        apply (rule Bloch [OF 1 \<open>t > 0\<close> rle])
        apply (rule_tac b=b in that)
        using * apply force
        done
    qed
  qed
qed

end
