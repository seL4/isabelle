(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr with additions from LCP
    License: BSD
*)

section \<open>Metrics on product spaces\<close>

theory Function_Metric
  imports
    Function_Topology
    Elementary_Metric_Spaces
begin

text \<open>In general, the product topology is not metrizable, unless the index set is countable.
When the index set is countable, essentially any (convergent) combination of the metrics on the
factors will do. We use below the simplest one, based on \<open>L\<^sup>1\<close>, but \<open>L\<^sup>2\<close> would also work,
for instance.

What is not completely trivial is that the distance thus defined induces the same topology
as the product topology. This is what we have to prove to show that we have an instance
of \<^class>\<open>metric_space\<close>.

The proofs below would work verbatim for general countable products of metric spaces. However,
since distances are only implemented in terms of type classes, we only develop the theory
for countable products of the same space.\<close>

instantiation "fun" :: (countable, metric_space) metric_space
begin

definition\<^marker>\<open>tag important\<close> dist_fun_def:
  "dist x y = (\<Sum>n. (1/2)^n * min (dist (x (from_nat n)) (y (from_nat n))) 1)"

definition\<^marker>\<open>tag important\<close> uniformity_fun_def:
  "(uniformity::(('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b)) filter) = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a\<Rightarrow>'b)) y < e})"

text \<open>Except for the first one, the auxiliary lemmas below are only useful when proving the
instance: once it is proved, they become trivial consequences of the general theory of metric
spaces. It would thus be desirable to hide them once the instance is proved, but I do not know how
to do this.\<close>

lemma dist_fun_le_dist_first_terms:
  "dist x y \<le> 2 * Max {dist (x (from_nat n)) (y (from_nat n))|n. n \<le> N} + (1/2)^N"
proof -
  have "(\<Sum>n. (1 / 2) ^ (n+Suc N) * min (dist (x (from_nat (n+Suc N))) (y (from_nat (n+Suc N)))) 1)
          = (\<Sum>n. (1 / 2) ^ (Suc N) * ((1/2) ^ n * min (dist (x (from_nat (n+Suc N))) (y (from_nat (n+Suc N)))) 1))"
    by (rule suminf_cong, simp add: power_add)
  also have "... = (1/2)^(Suc N) * (\<Sum>n. (1 / 2) ^ n * min (dist (x (from_nat (n+Suc N))) (y (from_nat (n+Suc N)))) 1)"
    apply (rule suminf_mult)
    by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
  also have "... \<le> (1/2)^(Suc N) * (\<Sum>n. (1 / 2) ^ n)"
    apply (simp, rule suminf_le, simp)
    by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
  also have "... = (1/2)^(Suc N) * 2"
    using suminf_geometric[of "1/2"] by auto
  also have "... = (1/2)^N"
    by auto
  finally have *: "(\<Sum>n. (1 / 2) ^ (n+Suc N) * min (dist (x (from_nat (n+Suc N))) (y (from_nat (n+Suc N)))) 1) \<le> (1/2)^N"
    by simp

  define M where "M = Max {dist (x (from_nat n)) (y (from_nat n))|n. n \<le> N}"
  have "dist (x (from_nat 0)) (y (from_nat 0)) \<le> M"
    unfolding M_def by (rule Max_ge, auto)
  then have [simp]: "M \<ge> 0" by (meson dual_order.trans zero_le_dist)
  have "dist (x (from_nat n)) (y (from_nat n)) \<le> M" if "n\<le>N" for n
    unfolding M_def apply (rule Max_ge) using that by auto
  then have i: "min (dist (x (from_nat n)) (y (from_nat n))) 1 \<le> M" if "n\<le>N" for n
    using that by force
  have "(\<Sum>n< Suc N. (1 / 2) ^ n * min (dist (x (from_nat n)) (y (from_nat n))) 1) \<le>
      (\<Sum>n< Suc N. M * (1 / 2) ^ n)"
    by (rule sum_mono, simp add: i)
  also have "... = M * (\<Sum>n<Suc N. (1 / 2) ^ n)"
    by (rule sum_distrib_left[symmetric])
  also have "... \<le> M * (\<Sum>n. (1 / 2) ^ n)"
    by (rule mult_left_mono, rule sum_le_suminf, auto simp add: summable_geometric_iff)
  also have "... = M * 2"
    using suminf_geometric[of "1/2"] by auto
  finally have **: "(\<Sum>n< Suc N. (1 / 2) ^ n * min (dist (x (from_nat n)) (y (from_nat n))) 1) \<le> 2 * M"
    by simp

  have "dist x y = (\<Sum>n. (1 / 2) ^ n * min (dist (x (from_nat n)) (y (from_nat n))) 1)"
    unfolding dist_fun_def by simp
  also have "... = (\<Sum>n. (1 / 2) ^ (n+Suc N) * min (dist (x (from_nat (n+Suc N))) (y (from_nat (n+Suc N)))) 1)
                  + (\<Sum>n<Suc N. (1 / 2) ^ n * min (dist (x (from_nat n)) (y (from_nat n))) 1)"
    apply (rule suminf_split_initial_segment)
    by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
  also have "... \<le> 2 * M + (1/2)^N"
    using * ** by auto
  finally show ?thesis unfolding M_def by simp
qed

lemma open_fun_contains_ball_aux:
  assumes "open (U::(('a \<Rightarrow> 'b) set))"
          "x \<in> U"
  shows "\<exists>e>0. {y. dist x y < e} \<subseteq> U"
proof -
  have *: "openin (product_topology (\<lambda>i. euclidean) UNIV) U"
    using open_fun_def assms by auto
  obtain X where H: "Pi\<^sub>E UNIV X \<subseteq> U"
                    "\<And>i. openin euclidean (X i)"
                    "finite {i. X i \<noteq> topspace euclidean}"
                    "x \<in> Pi\<^sub>E UNIV X"
    using product_topology_open_contains_basis[OF * \<open>x \<in> U\<close>] by auto
  define I where "I = {i. X i \<noteq> topspace euclidean}"
  have "finite I" unfolding I_def using H(3) by auto
  {
    fix i
    have "x i \<in> X i" using \<open>x \<in> U\<close> H by auto
    then have "\<exists>e. e>0 \<and> ball (x i) e \<subseteq> X i"
      using \<open>openin euclidean (X i)\<close> open_openin open_contains_ball by blast
    then obtain e where "e>0" "ball (x i) e \<subseteq> X i" by blast
    define f where "f = min e (1/2)"
    have "f>0" "f<1" unfolding f_def using \<open>e>0\<close> by auto
    moreover have "ball (x i) f \<subseteq> X i" unfolding f_def using \<open>ball (x i) e \<subseteq> X i\<close> by auto
    ultimately have "\<exists>f. f > 0 \<and> f < 1 \<and> ball (x i) f \<subseteq> X i" by auto
  } note * = this
  have "\<exists>e. \<forall>i. e i > 0 \<and> e i < 1 \<and> ball (x i) (e i) \<subseteq> X i"
    by (rule choice, auto simp add: *)
  then obtain e where "\<And>i. e i > 0" "\<And>i. e i < 1" "\<And>i. ball (x i) (e i) \<subseteq> X i"
    by blast
  define m where "m = Min {(1/2)^(to_nat i) * e i|i. i \<in> I}"
  have "m > 0" if "I\<noteq>{}"
    unfolding m_def Min_gr_iff using \<open>finite I\<close> \<open>I \<noteq> {}\<close> \<open>\<And>i. e i > 0\<close> by auto
  moreover have "{y. dist x y < m} \<subseteq> U"
  proof (auto)
    fix y assume "dist x y < m"
    have "y i \<in> X i" if "i \<in> I" for i
    proof -
      have *: "summable (\<lambda>n. (1/2)^n * min (dist (x (from_nat n)) (y (from_nat n))) 1)"
        by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
      define n where "n = to_nat i"
      have "(1/2)^n * min (dist (x (from_nat n)) (y (from_nat n))) 1 < m"
        using \<open>dist x y < m\<close> unfolding dist_fun_def using sum_le_suminf[OF *, of "{n}"] by auto
      then have "(1/2)^(to_nat i) * min (dist (x i) (y i)) 1 < m"
        using \<open>n = to_nat i\<close> by auto
      also have "... \<le> (1/2)^(to_nat i) * e i"
        unfolding m_def apply (rule Min_le) using \<open>finite I\<close> \<open>i \<in> I\<close> by auto
      ultimately have "min (dist (x i) (y i)) 1 < e i"
        by (auto simp add: field_split_simps)
      then have "dist (x i) (y i) < e i"
        using \<open>e i < 1\<close> by auto
      then show "y i \<in> X i" using \<open>ball (x i) (e i) \<subseteq> X i\<close> by auto
    qed
    then have "y \<in> Pi\<^sub>E UNIV X" using H(1) unfolding I_def topspace_euclidean by (auto simp add: PiE_iff)
    then show "y \<in> U" using \<open>Pi\<^sub>E UNIV X \<subseteq> U\<close> by auto
  qed
  ultimately have *: "\<exists>m>0. {y. dist x y < m} \<subseteq> U" if "I \<noteq> {}" using that by auto

  have "U = UNIV" if "I = {}"
    using that H(1) unfolding I_def topspace_euclidean by (auto simp add: PiE_iff)
  then have "\<exists>m>0. {y. dist x y < m} \<subseteq> U" if "I = {}" using that zero_less_one by blast
  then show "\<exists>m>0. {y. dist x y < m} \<subseteq> U" using * by blast
qed

lemma ball_fun_contains_open_aux:
  fixes x::"('a \<Rightarrow> 'b)" and e::real
  assumes "e>0"
  shows "\<exists>U. open U \<and> x \<in> U \<and> U \<subseteq> {y. dist x y < e}"
proof -
  have "\<exists>N::nat. 2^N > 8/e"
    by (simp add: real_arch_pow)
  then obtain N::nat where "2^N > 8/e" by auto
  define f where "f = e/4"
  have [simp]: "e>0" "f > 0" unfolding f_def using assms by auto
  define X::"('a \<Rightarrow> 'b set)" where "X = (\<lambda>i. if (\<exists>n\<le>N. i = from_nat n) then {z. dist (x i) z < f} else UNIV)"
  have "{i. X i \<noteq> UNIV} \<subseteq> from_nat`{0..N}"
    unfolding X_def by auto
  then have "finite {i. X i \<noteq> topspace euclidean}"
    unfolding topspace_euclidean using finite_surj by blast
  have "\<And>i. open (X i)"
    unfolding X_def using metric_space_class.open_ball open_UNIV by auto
  then have "\<And>i. openin euclidean (X i)"
    using open_openin by auto
  define U where "U = Pi\<^sub>E UNIV X"
  have "open U"
    unfolding open_fun_def product_topology_def apply (rule topology_generated_by_Basis)
    unfolding U_def using \<open>\<And>i. openin euclidean (X i)\<close> \<open>finite {i. X i \<noteq> topspace euclidean}\<close>
    by auto
  moreover have "x \<in> U"
    unfolding U_def X_def by (auto simp add: PiE_iff)
  moreover have "dist x y < e" if "y \<in> U" for y
  proof -
    have *: "dist (x (from_nat n)) (y (from_nat n)) \<le> f" if "n \<le> N" for n
      using \<open>y \<in> U\<close> unfolding U_def apply (auto simp add: PiE_iff)
      unfolding X_def using that by (metis less_imp_le mem_Collect_eq)
    have **: "Max {dist (x (from_nat n)) (y (from_nat n))|n. n \<le> N} \<le> f"
      apply (rule Max.boundedI) using * by auto

    have "dist x y \<le> 2 * Max {dist (x (from_nat n)) (y (from_nat n))|n. n \<le> N} + (1/2)^N"
      by (rule dist_fun_le_dist_first_terms)
    also have "... \<le> 2 * f + e / 8"
      apply (rule add_mono) using ** \<open>2^N > 8/e\<close> by(auto simp add: field_split_simps)
    also have "... \<le> e/2 + e/8"
      unfolding f_def by auto
    also have "... < e"
      by auto
    finally show "dist x y < e" by simp
  qed
  ultimately show ?thesis by auto
qed

lemma fun_open_ball_aux:
  fixes U::"('a \<Rightarrow> 'b) set"
  shows "open U \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> y \<in> U)"
proof (auto)
  assume "open U"
  fix x assume "x \<in> U"
  then show "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> y \<in> U"
    using open_fun_contains_ball_aux[OF \<open>open U\<close> \<open>x \<in> U\<close>] by auto
next
  assume H: "\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> y \<in> U"
  define K where "K = {V. open V \<and> V \<subseteq> U}"
  {
    fix x assume "x \<in> U"
    then obtain e where e: "e>0" "{y. dist x y < e} \<subseteq> U" using H by blast
    then obtain V where V: "open V" "x \<in> V" "V \<subseteq> {y. dist x y < e}"
      using ball_fun_contains_open_aux[OF \<open>e>0\<close>, of x] by auto
    have "V \<in> K"
      unfolding K_def using e(2) V(1) V(3) by auto
    then have "x \<in> (\<Union>K)" using \<open>x \<in> V\<close> by auto
  }
  then have "(\<Union>K) = U"
    unfolding K_def by auto
  moreover have "open (\<Union>K)"
    unfolding K_def by auto
  ultimately show "open U" by simp
qed

instance proof
  fix x y::"'a \<Rightarrow> 'b" show "(dist x y = 0) = (x = y)"
  proof
    assume "x = y"
    then show "dist x y = 0" unfolding dist_fun_def using \<open>x = y\<close> by auto
  next
    assume "dist x y = 0"
    have *: "summable (\<lambda>n. (1/2)^n * min (dist (x (from_nat n)) (y (from_nat n))) 1)"
      by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
    have "(1/2)^n * min (dist (x (from_nat n)) (y (from_nat n))) 1 = 0" for n
      using \<open>dist x y = 0\<close> unfolding dist_fun_def by (simp add: "*" suminf_eq_zero_iff)
    then have "dist (x (from_nat n)) (y (from_nat n)) = 0" for n
      by (metis div_0 min_def nonzero_mult_div_cancel_left power_eq_0_iff
                zero_eq_1_divide_iff zero_neq_numeral)
    then have "x (from_nat n) = y (from_nat n)" for n
      by auto
    then have "x i = y i" for i
      by (metis from_nat_to_nat)
    then show "x = y"
      by auto
  qed
next
  text\<open>The proof of the triangular inequality is trivial, modulo the fact that we are dealing
        with infinite series, hence we should justify the convergence at each step. In this
        respect, the following simplification rule is extremely handy.\<close>
  have [simp]: "summable (\<lambda>n. (1/2)^n * min (dist (u (from_nat n)) (v (from_nat n))) 1)" for u v::"'a \<Rightarrow> 'b"
    by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
  fix x y z::"'a \<Rightarrow> 'b"
  {
    fix n
    have *: "dist (x (from_nat n)) (y (from_nat n)) \<le>
            dist (x (from_nat n)) (z (from_nat n)) + dist (y (from_nat n)) (z (from_nat n))"
      by (simp add: dist_triangle2)
    have "0 \<le> dist (y (from_nat n)) (z (from_nat n))"
      using zero_le_dist by blast
    moreover
    {
      assume "min (dist (y (from_nat n)) (z (from_nat n))) 1 \<noteq> dist (y (from_nat n)) (z (from_nat n))"
      then have "1 \<le> min (dist (x (from_nat n)) (z (from_nat n))) 1 + min (dist (y (from_nat n)) (z (from_nat n))) 1"
        by (metis (no_types) diff_le_eq diff_self min_def zero_le_dist zero_le_one)
    }
    ultimately have "min (dist (x (from_nat n)) (y (from_nat n))) 1 \<le>
            min (dist (x (from_nat n)) (z (from_nat n))) 1 + min (dist (y (from_nat n)) (z (from_nat n))) 1"
      using * by linarith
  } note ineq = this
  have "dist x y = (\<Sum>n. (1/2)^n * min (dist (x (from_nat n)) (y (from_nat n))) 1)"
    unfolding dist_fun_def by simp
  also have "... \<le> (\<Sum>n. (1/2)^n * min (dist (x (from_nat n)) (z (from_nat n))) 1
                        + (1/2)^n * min (dist (y (from_nat n)) (z (from_nat n))) 1)"
    apply (rule suminf_le)
    using ineq apply (metis (no_types, opaque_lifting) add.right_neutral distrib_left
      le_divide_eq_numeral1(1) mult_2_right mult_left_mono zero_le_one zero_le_power)
    by (auto simp add: summable_add)
  also have "... = (\<Sum>n. (1/2)^n * min (dist (x (from_nat n)) (z (from_nat n))) 1)
                  + (\<Sum>n. (1/2)^n * min (dist (y (from_nat n)) (z (from_nat n))) 1)"
    by (rule suminf_add[symmetric], auto)
  also have "... = dist x z + dist y z"
    unfolding dist_fun_def by simp
  finally show "dist x y \<le> dist x z + dist y z"
    by simp
next
  text\<open>Finally, we show that the topology generated by the distance and the product
        topology coincide. This is essentially contained in Lemma \<open>fun_open_ball_aux\<close>,
        except that the condition to prove is expressed with filters. To deal with this,
        we copy some mumbo jumbo from Lemma \<open>eventually_uniformity_metric\<close> in
        \<^file>\<open>~~/src/HOL/Real_Vector_Spaces.thy\<close>\<close>
  fix U::"('a \<Rightarrow> 'b) set"
  have "eventually P uniformity \<longleftrightarrow> (\<exists>e>0. \<forall>x (y::('a \<Rightarrow> 'b)). dist x y < e \<longrightarrow> P (x, y))" for P
  unfolding uniformity_fun_def apply (subst eventually_INF_base)
    by (auto simp: eventually_principal subset_eq intro: bexI[of _ "min _ _"])
  then show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    unfolding fun_open_ball_aux by simp
qed (simp add: uniformity_fun_def)

end

text \<open>Nice properties of spaces are preserved under countable products. In addition
to first countability, second countability and metrizability, as we have seen above,
completeness is also preserved, and therefore being Polish.\<close>

instance "fun" :: (countable, complete_space) complete_space
proof
  fix u::"nat \<Rightarrow> ('a \<Rightarrow> 'b)" assume "Cauchy u"
  have "Cauchy (\<lambda>n. u n i)" for i
  unfolding cauchy_def proof (intro impI allI)
    fix e assume "e>(0::real)"
    obtain k where "i = from_nat k"
      using from_nat_to_nat[of i] by metis
    have "(1/2)^k * min e 1 > 0" using \<open>e>0\<close> by auto
    then have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (u m) (u n) < (1/2)^k * min e 1"
      using \<open>Cauchy u\<close> unfolding cauchy_def by blast
    then obtain N::nat where C: "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (u m) (u n) < (1/2)^k * min e 1"
      by blast
    have "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (u m i) (u n i) < e"
    proof (auto)
      fix m n::nat assume "m \<ge> N" "n \<ge> N"
      have "(1/2)^k * min (dist (u m i) (u n i)) 1
              = sum (\<lambda>p. (1/2)^p * min (dist (u m (from_nat p)) (u n (from_nat p))) 1) {k}"
        using \<open>i = from_nat k\<close> by auto
      also have "... \<le> (\<Sum>p. (1/2)^p * min (dist (u m (from_nat p)) (u n (from_nat p))) 1)"
        apply (rule sum_le_suminf)
        by (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n"], auto simp add: summable_geometric_iff)
      also have "... = dist (u m) (u n)"
        unfolding dist_fun_def by auto
      also have "... < (1/2)^k * min e 1"
        using C \<open>m \<ge> N\<close> \<open>n \<ge> N\<close> by auto
      finally have "min (dist (u m i) (u n i)) 1 < min e 1"
        by (auto simp add: field_split_simps)
      then show "dist (u m i) (u n i) < e" by auto
    qed
    then show "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (u m i) (u n i) < e"
      by blast
  qed
  then have "\<exists>x. (\<lambda>n. u n i) \<longlonglongrightarrow> x" for i
    using Cauchy_convergent convergent_def by auto
  then have "\<exists>x. \<forall>i. (\<lambda>n. u n i) \<longlonglongrightarrow> x i"
    using choice by force
  then obtain x where *: "\<And>i. (\<lambda>n. u n i) \<longlonglongrightarrow> x i" by blast
  have "u \<longlonglongrightarrow> x"
  proof (rule metric_LIMSEQ_I)
    fix e assume [simp]: "e>(0::real)"
    have i: "\<exists>K. \<forall>n\<ge>K. dist (u n i) (x i) < e/4" for i
      by (rule metric_LIMSEQ_D, auto simp add: *)
    have "\<exists>K. \<forall>i. \<forall>n\<ge>K i. dist (u n i) (x i) < e/4"
      apply (rule choice) using i by auto
    then obtain K where K: "\<And>i n. n \<ge> K i \<Longrightarrow> dist (u n i) (x i) < e/4"
      by blast

    have "\<exists>N::nat. 2^N > 4/e"
      by (simp add: real_arch_pow)
    then obtain N::nat where "2^N > 4/e" by auto
    define L where "L = Max {K (from_nat n)|n. n \<le> N}"
    have "dist (u k) x < e" if "k \<ge> L" for k
    proof -
      have *: "dist (u k (from_nat n)) (x (from_nat n)) \<le> e / 4" if "n \<le> N" for n
      proof -
        have "K (from_nat n) \<le> L"
          unfolding L_def apply (rule Max_ge) using \<open>n \<le> N\<close> by auto
        then have "k \<ge> K (from_nat n)" using \<open>k \<ge> L\<close> by auto
        then show ?thesis using K less_imp_le by auto
      qed
      have **: "Max {dist (u k (from_nat n)) (x (from_nat n)) |n. n \<le> N} \<le> e/4"
        apply (rule Max.boundedI) using * by auto
      have "dist (u k) x \<le> 2 * Max {dist (u k (from_nat n)) (x (from_nat n)) |n. n \<le> N} + (1/2)^N"
        using dist_fun_le_dist_first_terms by auto
      also have "... \<le> 2 * e/4 + e/4"
        apply (rule add_mono)
        using ** \<open>2^N > 4/e\<close> less_imp_le by (auto simp add: field_split_simps)
      also have "... < e" by auto
      finally show ?thesis by simp
    qed
    then show "\<exists>L. \<forall>k\<ge>L. dist (u k) x < e" by blast
  qed
  then show "convergent u" using convergent_def by blast
qed

instance "fun" :: (countable, polish_space) polish_space
  by standard

end