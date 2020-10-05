section \<open>Bernstein-Weierstrass and Stone-Weierstrass\<close>

text\<open>By L C Paulson (2015)\<close>

theory Weierstrass_Theorems
imports Uniform_Limit Path_Connected Derivative
begin

subsection \<open>Bernstein polynomials\<close>

definition\<^marker>\<open>tag important\<close> Bernstein :: "[nat,nat,real] \<Rightarrow> real" where
  "Bernstein n k x \<equiv> of_nat (n choose k) * x^k * (1 - x)^(n - k)"

lemma Bernstein_nonneg: "\<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> 0 \<le> Bernstein n k x"
  by (simp add: Bernstein_def)

lemma Bernstein_pos: "\<lbrakk>0 < x; x < 1; k \<le> n\<rbrakk> \<Longrightarrow> 0 < Bernstein n k x"
  by (simp add: Bernstein_def)

lemma sum_Bernstein [simp]: "(\<Sum>k\<le>n. Bernstein n k x) = 1"
  using binomial_ring [of x "1-x" n]
  by (simp add: Bernstein_def)

lemma binomial_deriv1:
    "(\<Sum>k\<le>n. (of_nat k * of_nat (n choose k)) * a^(k-1) * b^(n-k)) = real_of_nat n * (a+b)^(n-1)"
  apply (rule DERIV_unique [where f = "\<lambda>a. (a+b)^n" and x=a])
  apply (subst binomial_ring)
  apply (rule derivative_eq_intros sum.cong | simp add: atMost_atLeast0)+
  done

lemma binomial_deriv2:
    "(\<Sum>k\<le>n. (of_nat k * of_nat (k-1) * of_nat (n choose k)) * a^(k-2) * b^(n-k)) =
     of_nat n * of_nat (n-1) * (a+b::real)^(n-2)"
  apply (rule DERIV_unique [where f = "\<lambda>a. of_nat n * (a+b::real)^(n-1)" and x=a])
  apply (subst binomial_deriv1 [symmetric])
  apply (rule derivative_eq_intros sum.cong | simp add: Num.numeral_2_eq_2)+
  done

lemma sum_k_Bernstein [simp]: "(\<Sum>k\<le>n. real k * Bernstein n k x) = of_nat n * x"
  apply (subst binomial_deriv1 [of n x "1-x", simplified, symmetric])
  apply (simp add: sum_distrib_right)
  apply (auto simp: Bernstein_def algebra_simps power_eq_if intro!: sum.cong)
  done

lemma sum_kk_Bernstein [simp]: "(\<Sum>k\<le>n. real k * (real k - 1) * Bernstein n k x) = real n * (real n - 1) * x\<^sup>2"
proof -
  have "(\<Sum>k\<le>n. real k * (real k - 1) * Bernstein n k x) =
        (\<Sum>k\<le>n. real k * real (k - Suc 0) * real (n choose k) * x^(k - 2) * (1 - x)^(n - k) * x\<^sup>2)"
  proof (rule sum.cong [OF refl], simp)
    fix k
    assume "k \<le> n"
    then consider "k = 0" | "k = 1" | k' where "k = Suc (Suc k')"
      by (metis One_nat_def not0_implies_Suc)
    then show "k = 0 \<or>
          (real k - 1) * Bernstein n k x =
          real (k - Suc 0) *
          (real (n choose k) * (x^(k - 2) * ((1 - x)^(n - k) * x\<^sup>2)))"
      by cases (auto simp add: Bernstein_def power2_eq_square algebra_simps)
  qed
  also have "... = real_of_nat n * real_of_nat (n - Suc 0) * x\<^sup>2"
    by (subst binomial_deriv2 [of n x "1-x", simplified, symmetric]) (simp add: sum_distrib_right)
  also have "... = n * (n - 1) * x\<^sup>2"
    by auto
  finally show ?thesis
    by auto
qed

subsection \<open>Explicit Bernstein version of the 1D Weierstrass approximation theorem\<close>

theorem Bernstein_Weierstrass:
  fixes f :: "real \<Rightarrow> real"
  assumes contf: "continuous_on {0..1} f" and e: "0 < e"
    shows "\<exists>N. \<forall>n x. N \<le> n \<and> x \<in> {0..1}
                    \<longrightarrow> \<bar>f x - (\<Sum>k\<le>n. f(k/n) * Bernstein n k x)\<bar> < e"
proof -
  have "bounded (f ` {0..1})"
    using compact_continuous_image compact_imp_bounded contf by blast
  then obtain M where M: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> \<bar>f x\<bar> \<le> M"
    by (force simp add: bounded_iff)
  then have "0 \<le> M" by force
  have ucontf: "uniformly_continuous_on {0..1} f"
    using compact_uniformly_continuous contf by blast
  then obtain d where d: "d>0" "\<And>x x'. \<lbrakk> x \<in> {0..1}; x' \<in> {0..1}; \<bar>x' - x\<bar> < d\<rbrakk> \<Longrightarrow> \<bar>f x' - f x\<bar> < e/2"
     apply (rule uniformly_continuous_onE [where e = "e/2"])
     using e by (auto simp: dist_norm)
  { fix n::nat and x::real
    assume n: "Suc (nat\<lceil>4*M/(e*d\<^sup>2)\<rceil>) \<le> n" and x: "0 \<le> x" "x \<le> 1"
    have "0 < n" using n by simp
    have ed0: "- (e * d\<^sup>2) < 0"
      using e \<open>0<d\<close> by simp
    also have "... \<le> M * 4"
      using \<open>0\<le>M\<close> by simp
    finally have [simp]: "real_of_int (nat \<lceil>4 * M / (e * d\<^sup>2)\<rceil>) = real_of_int \<lceil>4 * M / (e * d\<^sup>2)\<rceil>"
      using \<open>0\<le>M\<close> e \<open>0<d\<close>
      by (simp add: field_simps)
    have "4*M/(e*d\<^sup>2) + 1 \<le> real (Suc (nat\<lceil>4*M/(e*d\<^sup>2)\<rceil>))"
      by (simp add: real_nat_ceiling_ge)
    also have "... \<le> real n"
      using n by (simp add: field_simps)
    finally have nbig: "4*M/(e*d\<^sup>2) + 1 \<le> real n" .
    have sum_bern: "(\<Sum>k\<le>n. (x - k/n)\<^sup>2 * Bernstein n k x) = x * (1 - x) / n"
    proof -
      have *: "\<And>a b x::real. (a - b)\<^sup>2 * x = a * (a - 1) * x + (1 - 2 * b) * a * x + b * b * x"
        by (simp add: algebra_simps power2_eq_square)
      have "(\<Sum>k\<le>n. (k - n * x)\<^sup>2 * Bernstein n k x) = n * x * (1 - x)"
        apply (simp add: * sum.distrib)
        apply (simp flip: sum_distrib_left add: mult.assoc)
        apply (simp add: algebra_simps power2_eq_square)
        done
      then have "(\<Sum>k\<le>n. (k - n * x)\<^sup>2 * Bernstein n k x)/n^2 = x * (1 - x) / n"
        by (simp add: power2_eq_square)
      then show ?thesis
        using n by (simp add: sum_divide_distrib field_split_simps power2_commute)
    qed
    { fix k
      assume k: "k \<le> n"
      then have kn: "0 \<le> k / n" "k / n \<le> 1"
        by (auto simp: field_split_simps)
      consider (lessd) "\<bar>x - k / n\<bar> < d" | (ged) "d \<le> \<bar>x - k / n\<bar>"
        by linarith
      then have "\<bar>(f x - f (k/n))\<bar> \<le> e/2 + 2 * M / d\<^sup>2 * (x - k/n)\<^sup>2"
      proof cases
        case lessd
        then have "\<bar>(f x - f (k/n))\<bar> < e/2"
          using d x kn by (simp add: abs_minus_commute)
        also have "... \<le> (e/2 + 2 * M / d\<^sup>2 * (x - k/n)\<^sup>2)"
          using \<open>M\<ge>0\<close> d by simp
        finally show ?thesis by simp
      next
        case ged
        then have dle: "d\<^sup>2 \<le> (x - k/n)\<^sup>2"
          by (metis d(1) less_eq_real_def power2_abs power_mono)
        have \<section>: "1 \<le> (x - real k / real n)\<^sup>2 / d\<^sup>2"
          using dle \<open>d>0\<close> by auto
        have "\<bar>(f x - f (k/n))\<bar> \<le> \<bar>f x\<bar> + \<bar>f (k/n)\<bar>"
          by (rule abs_triangle_ineq4)
        also have "... \<le> M+M"
          by (meson M add_mono_thms_linordered_semiring(1) kn x)
        also have "... \<le> 2 * M * ((x - k/n)\<^sup>2 / d\<^sup>2)"
          using \<section> \<open>M\<ge>0\<close> mult_left_mono by fastforce
        also have "... \<le> e/2 + 2 * M / d\<^sup>2 * (x - k/n)\<^sup>2"
          using e  by simp
        finally show ?thesis .
        qed
    } note * = this
    have "\<bar>f x - (\<Sum>k\<le>n. f(k / n) * Bernstein n k x)\<bar> \<le> \<bar>\<Sum>k\<le>n. (f x - f(k / n)) * Bernstein n k x\<bar>"
      by (simp add: sum_subtractf sum_distrib_left [symmetric] algebra_simps)
    also have "... \<le> (\<Sum>k\<le>n. \<bar>(f x - f(k / n)) * Bernstein n k x\<bar>)"
      by (rule sum_abs)
    also have "... \<le> (\<Sum>k\<le>n. (e/2 + (2 * M / d\<^sup>2) * (x - k / n)\<^sup>2) * Bernstein n k x)"
      using *
      by (force simp add: abs_mult Bernstein_nonneg x mult_right_mono intro: sum_mono)
    also have "... \<le> e/2 + (2 * M) / (d\<^sup>2 * n)"
      unfolding sum.distrib Rings.semiring_class.distrib_right sum_distrib_left [symmetric] mult.assoc sum_bern
      using \<open>d>0\<close> x by (simp add: divide_simps \<open>M\<ge>0\<close> mult_le_one mult_left_le)
    also have "... < e"
      using \<open>d>0\<close> nbig e \<open>n>0\<close> 
      apply (simp add: field_split_simps)
      using ed0 by linarith
    finally have "\<bar>f x - (\<Sum>k\<le>n. f (real k / real n) * Bernstein n k x)\<bar> < e" .
  }
  then show ?thesis
    by auto
qed


subsection \<open>General Stone-Weierstrass theorem\<close>

text\<open>Source:
Bruno Brosowski and Frank Deutsch.
An Elementary Proof of the Stone-Weierstrass Theorem.
Proceedings of the American Mathematical Society
Volume 81, Number 1, January 1981.
DOI: 10.2307/2043993  \<^url>\<open>https://www.jstor.org/stable/2043993\<close>\<close>

locale function_ring_on =
  fixes R :: "('a::t2_space \<Rightarrow> real) set" and S :: "'a set"
  assumes compact: "compact S"
  assumes continuous: "f \<in> R \<Longrightarrow> continuous_on S f"
  assumes add: "f \<in> R \<Longrightarrow> g \<in> R \<Longrightarrow> (\<lambda>x. f x + g x) \<in> R"
  assumes mult: "f \<in> R \<Longrightarrow> g \<in> R \<Longrightarrow> (\<lambda>x. f x * g x) \<in> R"
  assumes const: "(\<lambda>_. c) \<in> R"
  assumes separable: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>f\<in>R. f x \<noteq> f y"

begin
  lemma minus: "f \<in> R \<Longrightarrow> (\<lambda>x. - f x) \<in> R"
    by (frule mult [OF const [of "-1"]]) simp

  lemma diff: "f \<in> R \<Longrightarrow> g \<in> R \<Longrightarrow> (\<lambda>x. f x - g x) \<in> R"
    unfolding diff_conv_add_uminus by (metis add minus)

  lemma power: "f \<in> R \<Longrightarrow> (\<lambda>x. f x^n) \<in> R"
    by (induct n) (auto simp: const mult)

  lemma sum: "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> f i \<in> R\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Sum>i \<in> I. f i x) \<in> R"
    by (induct I rule: finite_induct; simp add: const add)

  lemma prod: "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> f i \<in> R\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Prod>i \<in> I. f i x) \<in> R"
    by (induct I rule: finite_induct; simp add: const mult)

  definition\<^marker>\<open>tag important\<close> normf :: "('a::t2_space \<Rightarrow> real) \<Rightarrow> real"
    where "normf f \<equiv> SUP x\<in>S. \<bar>f x\<bar>"

  lemma normf_upper: 
    assumes "continuous_on S f" "x \<in> S" shows "\<bar>f x\<bar> \<le> normf f"
  proof -
    have "bdd_above ((\<lambda>x. \<bar>f x\<bar>) ` S)"
      by (simp add: assms(1) bounded_imp_bdd_above compact compact_continuous_image compact_imp_bounded continuous_on_rabs)
    then show ?thesis
      using assms cSUP_upper normf_def by fastforce
  qed

  lemma normf_least: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<le> M) \<Longrightarrow> normf f \<le> M"
    by (simp add: normf_def cSUP_least)

end

lemma (in function_ring_on) one:
  assumes U: "open U" and t0: "t0 \<in> S" "t0 \<in> U" and t1: "t1 \<in> S-U"
    shows "\<exists>V. open V \<and> t0 \<in> V \<and> S \<inter> V \<subseteq> U \<and>
               (\<forall>e>0. \<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>t \<in> S \<inter> V. f t < e) \<and> (\<forall>t \<in> S - U. f t > 1 - e))"
proof -
  have "\<exists>pt \<in> R. pt t0 = 0 \<and> pt t > 0 \<and> pt ` S \<subseteq> {0..1}" if t: "t \<in> S - U" for t
  proof -
    have "t \<noteq> t0" using t t0 by auto
    then obtain g where g: "g \<in> R" "g t \<noteq> g t0"
      using separable t0  by (metis Diff_subset subset_eq t)
    define h where [abs_def]: "h x = g x - g t0" for x
    have "h \<in> R"
      unfolding h_def by (fast intro: g const diff)
    then have hsq: "(\<lambda>w. (h w)\<^sup>2) \<in> R"
      by (simp add: power2_eq_square mult)
    have "h t \<noteq> h t0"
      by (simp add: h_def g)
    then have "h t \<noteq> 0"
      by (simp add: h_def)
    then have ht2: "0 < (h t)^2"
      by simp
    also have "... \<le> normf (\<lambda>w. (h w)\<^sup>2)"
      using t normf_upper [where x=t] continuous [OF hsq] by force
    finally have nfp: "0 < normf (\<lambda>w. (h w)\<^sup>2)" .
    define p where [abs_def]: "p x = (1 / normf (\<lambda>w. (h w)\<^sup>2)) * (h x)^2" for x
    have "p \<in> R"
      unfolding p_def by (fast intro: hsq const mult)
    moreover have "p t0 = 0"
      by (simp add: p_def h_def)
    moreover have "p t > 0"
      using nfp ht2 by (simp add: p_def)
    moreover have "\<And>x. x \<in> S \<Longrightarrow> p x \<in> {0..1}"
      using nfp normf_upper [OF continuous [OF hsq] ] by (auto simp: p_def)
    ultimately show "\<exists>pt \<in> R. pt t0 = 0 \<and> pt t > 0 \<and> pt ` S \<subseteq> {0..1}"
      by auto
  qed
  then obtain pf where pf: "\<And>t. t \<in> S-U \<Longrightarrow> pf t \<in> R \<and> pf t t0 = 0 \<and> pf t t > 0"
                   and pf01: "\<And>t. t \<in> S-U \<Longrightarrow> pf t ` S \<subseteq> {0..1}"
    by metis
  have com_sU: "compact (S-U)"
    using compact closed_Int_compact U by (simp add: Diff_eq compact_Int_closed open_closed)
  have "\<And>t. t \<in> S-U \<Longrightarrow> \<exists>A. open A \<and> A \<inter> S = {x\<in>S. 0 < pf t x}"
    apply (rule open_Collect_positive)
    by (metis pf continuous)
  then obtain Uf where Uf: "\<And>t. t \<in> S-U \<Longrightarrow> open (Uf t) \<and> (Uf t) \<inter> S = {x\<in>S. 0 < pf t x}"
    by metis
  then have open_Uf: "\<And>t. t \<in> S-U \<Longrightarrow> open (Uf t)"
    by blast
  have tUft: "\<And>t. t \<in> S-U \<Longrightarrow> t \<in> Uf t"
    using pf Uf by blast
  then have *: "S-U \<subseteq> (\<Union>x \<in> S-U. Uf x)"
    by blast
  obtain subU where subU: "subU \<subseteq> S - U" "finite subU" "S - U \<subseteq> (\<Union>x \<in> subU. Uf x)"
    by (blast intro: that compactE_image [OF com_sU open_Uf *])
  then have [simp]: "subU \<noteq> {}"
    using t1 by auto
  then have cardp: "card subU > 0" using subU
    by (simp add: card_gt_0_iff)
  define p where [abs_def]: "p x = (1 / card subU) * (\<Sum>t \<in> subU. pf t x)" for x
  have pR: "p \<in> R"
    unfolding p_def using subU pf by (fast intro: pf const mult sum)
  have pt0 [simp]: "p t0 = 0"
    using subU pf by (auto simp: p_def intro: sum.neutral)
  have pt_pos: "p t > 0" if t: "t \<in> S-U" for t
  proof -
    obtain i where i: "i \<in> subU" "t \<in> Uf i" using subU t by blast
    show ?thesis
      using subU i t
      apply (clarsimp simp: p_def field_split_simps)
      apply (rule sum_pos2 [OF \<open>finite subU\<close>])
      using Uf t pf01 apply auto
      apply (force elim!: subsetCE)
      done
  qed
  have p01: "p x \<in> {0..1}" if t: "x \<in> S" for x
  proof -
    have "0 \<le> p x"
      using subU cardp t pf01
      by (fastforce simp add: p_def field_split_simps intro: sum_nonneg)
    moreover have "p x \<le> 1"
      using subU cardp t 
      apply (simp add: p_def field_split_simps)
      apply (rule sum_bounded_above [where 'a=real and K=1, simplified])
      using pf01 by force
    ultimately show ?thesis
      by auto
  qed
  have "compact (p ` (S-U))"
    by (meson Diff_subset com_sU compact_continuous_image continuous continuous_on_subset pR)
  then have "open (- (p ` (S-U)))"
    by (simp add: compact_imp_closed open_Compl)
  moreover have "0 \<in> - (p ` (S-U))"
    by (metis (no_types) ComplI image_iff not_less_iff_gr_or_eq pt_pos)
  ultimately obtain delta0 where delta0: "delta0 > 0" "ball 0 delta0 \<subseteq> - (p ` (S-U))"
    by (auto simp: elim!: openE)
  then have pt_delta: "\<And>x. x \<in> S-U \<Longrightarrow> p x \<ge> delta0"
    by (force simp: ball_def dist_norm dest: p01)
  define \<delta> where "\<delta> = delta0/2"
  have "delta0 \<le> 1" using delta0 p01 [of t1] t1
      by (force simp: ball_def dist_norm dest: p01)
  with delta0 have \<delta>01: "0 < \<delta>" "\<delta> < 1"
    by (auto simp: \<delta>_def)
  have pt_\<delta>: "\<And>x. x \<in> S-U \<Longrightarrow> p x \<ge> \<delta>"
    using pt_delta delta0 by (force simp: \<delta>_def)
  have "\<exists>A. open A \<and> A \<inter> S = {x\<in>S. p x < \<delta>/2}"
    by (rule open_Collect_less_Int [OF continuous [OF pR] continuous_on_const])
  then obtain V where V: "open V" "V \<inter> S = {x\<in>S. p x < \<delta>/2}"
    by blast
  define k where "k = nat\<lfloor>1/\<delta>\<rfloor> + 1"
  have "k>0"  by (simp add: k_def)
  have "k-1 \<le> 1/\<delta>"
    using \<delta>01 by (simp add: k_def)
  with \<delta>01 have "k \<le> (1+\<delta>)/\<delta>"
    by (auto simp: algebra_simps add_divide_distrib)
  also have "... < 2/\<delta>"
    using \<delta>01 by (auto simp: field_split_simps)
  finally have k2\<delta>: "k < 2/\<delta>" .
  have "1/\<delta> < k"
    using \<delta>01 unfolding k_def by linarith
  with \<delta>01 k2\<delta> have k\<delta>: "1 < k*\<delta>" "k*\<delta> < 2"
    by (auto simp: field_split_simps)
  define q where [abs_def]: "q n t = (1 - p t^n)^(k^n)" for n t
  have qR: "q n \<in> R" for n
    by (simp add: q_def const diff power pR)
  have q01: "\<And>n t. t \<in> S \<Longrightarrow> q n t \<in> {0..1}"
    using p01 by (simp add: q_def power_le_one algebra_simps)
  have qt0 [simp]: "\<And>n. n>0 \<Longrightarrow> q n t0 = 1"
    using t0 pf by (simp add: q_def power_0_left)
  { fix t and n::nat
    assume t: "t \<in> S \<inter> V"
    with \<open>k>0\<close> V have "k * p t < k * \<delta> / 2"
       by force
    then have "1 - (k * \<delta> / 2)^n \<le> 1 - (k * p t)^n"
      using  \<open>k>0\<close> p01 t by (simp add: power_mono)
    also have "... \<le> q n t"
      using Bernoulli_inequality [of "- ((p t)^n)" "k^n"] 
      apply (simp add: q_def)
      by (metis IntE atLeastAtMost_iff p01 power_le_one power_mult_distrib t)
    finally have "1 - (k * \<delta> / 2)^n \<le> q n t" .
  } note limitV = this
  { fix t and n::nat
    assume t: "t \<in> S - U"
    with \<open>k>0\<close> U have "k * \<delta> \<le> k * p t"
      by (simp add: pt_\<delta>)
    with k\<delta> have kpt: "1 < k * p t"
      by (blast intro: less_le_trans)
    have ptn_pos: "0 < p t^n"
      using pt_pos [OF t] by simp
    have ptn_le: "p t^n \<le> 1"
      by (meson DiffE atLeastAtMost_iff p01 power_le_one t)
    have "q n t = (1/(k^n * (p t)^n)) * (1 - p t^n)^(k^n) * k^n * (p t)^n"
      using pt_pos [OF t] \<open>k>0\<close> by (simp add: q_def)
    also have "... \<le> (1/(k * (p t))^n) * (1 - p t^n)^(k^n) * (1 + k^n * (p t)^n)"
      using pt_pos [OF t] \<open>k>0\<close>
      by (simp add: divide_simps mult_left_mono ptn_le)
    also have "... \<le> (1/(k * (p t))^n) * (1 - p t^n)^(k^n) * (1 + (p t)^n)^(k^n)"
    proof (rule mult_left_mono [OF Bernoulli_inequality])
      show "0 \<le> 1 / (real k * p t)^n * (1 - p t^n)^k^n"
        using ptn_pos ptn_le by (auto simp: power_mult_distrib)
    qed (use ptn_pos in auto)
    also have "... = (1/(k * (p t))^n) * (1 - p t^(2*n))^(k^n)"
      using pt_pos [OF t] \<open>k>0\<close>
      by (simp add: algebra_simps power_mult power2_eq_square flip: power_mult_distrib)
    also have "... \<le> (1/(k * (p t))^n) * 1"
      using pt_pos \<open>k>0\<close> p01 power_le_one t
      by (intro mult_left_mono [OF power_le_one]) auto
    also have "... \<le> (1 / (k*\<delta>))^n"
      using \<open>k>0\<close> \<delta>01  power_mono pt_\<delta> t
      by (fastforce simp: field_simps)
    finally have "q n t \<le> (1 / (real k * \<delta>))^n " .
  } note limitNonU = this
  define NN
    where "NN e = 1 + nat \<lceil>max (ln e / ln (real k * \<delta> / 2)) (- ln e / ln (real k * \<delta>))\<rceil>" for e
  have NN: "of_nat (NN e) > ln e / ln (real k * \<delta> / 2)"  "of_nat (NN e) > - ln e / ln (real k * \<delta>)"
              if "0<e" for e
      unfolding NN_def  by linarith+
    have NN1: "(k * \<delta> / 2)^NN e < e" if "e>0" for e
    proof -
      have "ln ((real k * \<delta> / 2)^NN e) = real (NN e) * ln (real k * \<delta> / 2)"
        by (simp add: \<open>\<delta>>0\<close> \<open>0 < k\<close> ln_realpow)
      also have "... < ln e"
        using NN k\<delta> that by (force simp add: field_simps)
      finally show ?thesis
        by (simp add: \<open>\<delta>>0\<close> \<open>0 < k\<close> that)
    qed
  have NN0: "(1/(k*\<delta>))^(NN e) < e" if "e>0" for e
  proof -
    have "0 < ln (real k) + ln \<delta>"
      using \<delta>01(1) \<open>0 < k\<close> k\<delta>(1) ln_gt_zero ln_mult by fastforce 
    then have "real (NN e) * ln (1 / (real k * \<delta>)) < ln e"
      using k\<delta>(1) NN(2) [of e] that by (simp add: ln_div divide_simps)
    then have "exp (real (NN e) * ln (1 / (real k * \<delta>))) < e"
      by (metis exp_less_mono exp_ln that)
    then show ?thesis
      by (simp add: \<delta>01(1) \<open>0 < k\<close> exp_of_nat_mult)
  qed
  { fix t and e::real
    assume "e>0"
    have "t \<in> S \<inter> V \<Longrightarrow> 1 - q (NN e) t < e" "t \<in> S - U \<Longrightarrow> q (NN e) t < e"
    proof -
      assume t: "t \<in> S \<inter> V"
      show "1 - q (NN e) t < e"
        by (metis add.commute diff_le_eq not_le limitV [OF t] less_le_trans [OF NN1 [OF \<open>e>0\<close>]])
    next
      assume t: "t \<in> S - U"
      show "q (NN e) t < e"
      using  limitNonU [OF t] less_le_trans [OF NN0 [OF \<open>e>0\<close>]] not_le by blast
    qed
  } then have "\<And>e. e > 0 \<Longrightarrow> \<exists>f\<in>R. f ` S \<subseteq> {0..1} \<and> (\<forall>t \<in> S \<inter> V. f t < e) \<and> (\<forall>t \<in> S - U. 1 - e < f t)"
    using q01
    by (rule_tac x="\<lambda>x. 1 - q (NN e) x" in bexI) (auto simp: algebra_simps intro: diff const qR)
  moreover have t0V: "t0 \<in> V"  "S \<inter> V \<subseteq> U"
    using pt_\<delta> t0 U V \<delta>01  by fastforce+
  ultimately show ?thesis using V t0V
    by blast
qed

text\<open>Non-trivial case, with \<^term>\<open>A\<close> and \<^term>\<open>B\<close> both non-empty\<close>
lemma (in function_ring_on) two_special:
  assumes A: "closed A" "A \<subseteq> S" "a \<in> A"
      and B: "closed B" "B \<subseteq> S" "b \<in> B"
      and disj: "A \<inter> B = {}"
      and e: "0 < e" "e < 1"
    shows "\<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>x \<in> A. f x < e) \<and> (\<forall>x \<in> B. f x > 1 - e)"
proof -
  { fix w
    assume "w \<in> A"
    then have "open ( - B)" "b \<in> S" "w \<notin> B" "w \<in> S"
      using assms by auto
    then have "\<exists>V. open V \<and> w \<in> V \<and> S \<inter> V \<subseteq> -B \<and>
               (\<forall>e>0. \<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>x \<in> S \<inter> V. f x < e) \<and> (\<forall>x \<in> S \<inter> B. f x > 1 - e))"
      using one [of "-B" w b] assms \<open>w \<in> A\<close> by simp
  }
  then obtain Vf where Vf:
         "\<And>w. w \<in> A \<Longrightarrow> open (Vf w) \<and> w \<in> Vf w \<and> S \<inter> Vf w \<subseteq> -B \<and>
                         (\<forall>e>0. \<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>x \<in> S \<inter> Vf w. f x < e) \<and> (\<forall>x \<in> S \<inter> B. f x > 1 - e))"
    by metis
  then have open_Vf: "\<And>w. w \<in> A \<Longrightarrow> open (Vf w)"
    by blast
  have tVft: "\<And>w. w \<in> A \<Longrightarrow> w \<in> Vf w"
    using Vf by blast
  then have sum_max_0: "A \<subseteq> (\<Union>x \<in> A. Vf x)"
    by blast
  have com_A: "compact A" using A
    by (metis compact compact_Int_closed inf.absorb_iff2)
  obtain subA where subA: "subA \<subseteq> A" "finite subA" "A \<subseteq> (\<Union>x \<in> subA. Vf x)"
    by (blast intro: that compactE_image [OF com_A open_Vf sum_max_0])
  then have [simp]: "subA \<noteq> {}"
    using \<open>a \<in> A\<close> by auto
  then have cardp: "card subA > 0" using subA
    by (simp add: card_gt_0_iff)
  have "\<And>w. w \<in> A \<Longrightarrow> \<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>x \<in> S \<inter> Vf w. f x < e / card subA) \<and> (\<forall>x \<in> S \<inter> B. f x > 1 - e / card subA)"
    using Vf e cardp by simp
  then obtain ff where ff:
         "\<And>w. w \<in> A \<Longrightarrow> ff w \<in> R \<and> ff w ` S \<subseteq> {0..1} \<and>
                         (\<forall>x \<in> S \<inter> Vf w. ff w x < e / card subA) \<and> (\<forall>x \<in> S \<inter> B. ff w x > 1 - e / card subA)"
    by metis
  define pff where [abs_def]: "pff x = (\<Prod>w \<in> subA. ff w x)" for x
  have pffR: "pff \<in> R"
    unfolding pff_def using subA ff by (auto simp: intro: prod)
  moreover
  have pff01: "pff x \<in> {0..1}" if t: "x \<in> S" for x
  proof -
    have "0 \<le> pff x"
      using subA cardp t ff
      by (fastforce simp: pff_def field_split_simps sum_nonneg intro: prod_nonneg)
    moreover have "pff x \<le> 1"
      using subA cardp t ff 
      by (fastforce simp add: pff_def field_split_simps sum_nonneg intro: prod_mono [where g = "\<lambda>x. 1", simplified])
    ultimately show ?thesis
      by auto
  qed
  moreover
  { fix v x
    assume v: "v \<in> subA" and x: "x \<in> Vf v" "x \<in> S"
    from subA v have "pff x = ff v x * (\<Prod>w \<in> subA - {v}. ff w x)"
      unfolding pff_def  by (metis prod.remove)
    also have "... \<le> ff v x * 1"
    proof -
      have "\<And>i. i \<in> subA - {v} \<Longrightarrow> 0 \<le> ff i x \<and> ff i x \<le> 1"
        by (metis Diff_subset atLeastAtMost_iff ff image_subset_iff subA(1) subsetD x(2))
      moreover have "0 \<le> ff v x"
        using ff subA(1) v x(2) by fastforce
      ultimately show ?thesis
        by (metis mult_left_mono prod_mono [where g = "\<lambda>x. 1", simplified])
    qed
    also have "... < e / card subA"
      using ff subA(1) v x by auto
    also have "... \<le> e"
      using cardp e by (simp add: field_split_simps)
    finally have "pff x < e" .
  }
  then have "\<And>x. x \<in> A \<Longrightarrow> pff x < e"
    using A Vf subA by (metis UN_E contra_subsetD)
  moreover
  { fix x
    assume x: "x \<in> B"
    then have "x \<in> S"
      using B by auto
    have "1 - e \<le> (1 - e / card subA)^card subA"
      using Bernoulli_inequality [of "-e / card subA" "card subA"] e cardp
      by (auto simp: field_simps)
    also have "... = (\<Prod>w \<in> subA. 1 - e / card subA)"
      by (simp add: subA(2))
    also have "... < pff x"
    proof -
      have "\<And>i. i \<in> subA \<Longrightarrow> e / real (card subA) \<le> 1 \<and> 1 - e / real (card subA) < ff i x"
        using e \<open>B \<subseteq> S\<close> ff subA(1) x by (force simp: field_split_simps)
      then show ?thesis
        using prod_mono_strict [where f = "\<lambda>x. 1 - e / card subA"] subA(2) by (force simp add: pff_def)
    qed
    finally have "1 - e < pff x" .
  }
  ultimately show ?thesis by blast
qed

lemma (in function_ring_on) two:
  assumes A: "closed A" "A \<subseteq> S"
      and B: "closed B" "B \<subseteq> S"
      and disj: "A \<inter> B = {}"
      and e: "0 < e" "e < 1"
    shows "\<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>x \<in> A. f x < e) \<and> (\<forall>x \<in> B. f x > 1 - e)"
proof (cases "A \<noteq> {} \<and> B \<noteq> {}")
  case True then show ?thesis
    using assms
    by (force simp flip: ex_in_conv intro!: two_special)
next
  case False 
  then consider "A={}" | "B={}" by force
  then show ?thesis
  proof cases
    case 1
    with e show ?thesis
      by (rule_tac x="\<lambda>x. 1" in bexI) (auto simp: const)
  next
    case 2
    with e show ?thesis
      by (rule_tac x="\<lambda>x. 0" in bexI) (auto simp: const)
  qed
qed

text\<open>The special case where \<^term>\<open>f\<close> is non-negative and \<^term>\<open>e<1/3\<close>\<close>
lemma (in function_ring_on) Stone_Weierstrass_special:
  assumes f: "continuous_on S f" and fpos: "\<And>x. x \<in> S \<Longrightarrow> f x \<ge> 0"
      and e: "0 < e" "e < 1/3"
  shows "\<exists>g \<in> R. \<forall>x\<in>S. \<bar>f x - g x\<bar> < 2*e"
proof -
  define n where "n = 1 + nat \<lceil>normf f / e\<rceil>"
  define A where "A j = {x \<in> S. f x \<le> (j - 1/3)*e}" for j :: nat
  define B where "B j = {x \<in> S. f x \<ge> (j + 1/3)*e}" for j :: nat
  have ngt: "(n-1) * e \<ge> normf f"
    using e pos_divide_le_eq real_nat_ceiling_ge[of "normf f / e"]
    by (fastforce simp add: divide_simps n_def)
  moreover have "n\<ge>1"
    by (simp_all add: n_def)
  ultimately have ge_fx: "(n-1) * e \<ge> f x" if "x \<in> S" for x
    using f normf_upper that by fastforce
  have "closed S"
    by (simp add: compact compact_imp_closed)
  { fix j
    have "closed (A j)" "A j \<subseteq> S"
      using \<open>closed S\<close> continuous_on_closed_Collect_le [OF f continuous_on_const]
      by (simp_all add: A_def Collect_restrict)
    moreover have "closed (B j)" "B j \<subseteq> S"
      using \<open>closed S\<close> continuous_on_closed_Collect_le [OF continuous_on_const f]
      by (simp_all add: B_def Collect_restrict)
    moreover have "(A j) \<inter> (B j) = {}"
      using e by (auto simp: A_def B_def field_simps)
    ultimately have "\<exists>f \<in> R. f ` S \<subseteq> {0..1} \<and> (\<forall>x \<in> A j. f x < e/n) \<and> (\<forall>x \<in> B j. f x > 1 - e/n)"
      using e \<open>1 \<le> n\<close> by (auto intro: two)
  }
  then obtain xf where xfR: "\<And>j. xf j \<in> R" and xf01: "\<And>j. xf j ` S \<subseteq> {0..1}"
                   and xfA: "\<And>x j. x \<in> A j \<Longrightarrow> xf j x < e/n"
                   and xfB: "\<And>x j. x \<in> B j \<Longrightarrow> xf j x > 1 - e/n"
    by metis
  define g where [abs_def]: "g x = e * (\<Sum>i\<le>n. xf i x)" for x
  have gR: "g \<in> R"
    unfolding g_def by (fast intro: mult const sum xfR)
  have gge0: "\<And>x. x \<in> S \<Longrightarrow> g x \<ge> 0"
    using e xf01 by (simp add: g_def zero_le_mult_iff image_subset_iff sum_nonneg)
  have A0: "A 0 = {}"
    using fpos e by (fastforce simp: A_def)
  have An: "A n = S"
    using e ngt \<open>n\<ge>1\<close> f normf_upper by (fastforce simp: A_def field_simps of_nat_diff)
  have Asub: "A j \<subseteq> A i" if "i\<ge>j" for i j
    using e that by (force simp: A_def intro: order_trans)
  { fix t
    assume t: "t \<in> S"
    define j where "j = (LEAST j. t \<in> A j)"
    have jn: "j \<le> n"
      using t An by (simp add: Least_le j_def)
    have Aj: "t \<in> A j"
      using t An by (fastforce simp add: j_def intro: LeastI)
    then have Ai: "t \<in> A i" if "i\<ge>j" for i
      using Asub [OF that] by blast
    then have fj1: "f t \<le> (j - 1/3)*e"
      by (simp add: A_def)
    then have Anj: "t \<notin> A i" if "i<j" for i
      using  Aj \<open>i<j\<close> not_less_Least by (fastforce simp add: j_def)
    have j1: "1 \<le> j"
      using A0 Aj j_def not_less_eq_eq by (fastforce simp add: j_def)
    then have Anj: "t \<notin> A (j-1)"
      using Least_le by (fastforce simp add: j_def)
    then have fj2: "(j - 4/3)*e < f t"
      using j1 t  by (simp add: A_def of_nat_diff)
    have xf_le1: "\<And>i. xf i t \<le> 1"
      using xf01 t by force
    have "g t = e * (\<Sum>i\<le>n. xf i t)"
      by (simp add: g_def flip: distrib_left)
    also have "... = e * (\<Sum>i \<in> {..<j} \<union> {j..n}. xf i t)"
      by (simp add: ivl_disj_un_one(4) jn)
    also have "... = e * (\<Sum>i<j. xf i t) + e * (\<Sum>i=j..n. xf i t)"
      by (simp add: distrib_left ivl_disj_int sum.union_disjoint)
    also have "... \<le> e*j + e * ((Suc n - j)*e/n)"
    proof (intro add_mono mult_left_mono)
      show "(\<Sum>i<j. xf i t) \<le> j"
        by (rule sum_bounded_above [OF xf_le1, where A = "lessThan j", simplified])
      have "xf i t \<le> e/n" if "i\<ge>j" for i
        using xfA [OF Ai] that by (simp add: less_eq_real_def)
      then show "(\<Sum>i = j..n. xf i t) \<le> real (Suc n - j) * e / real n"
        using sum_bounded_above [of "{j..n}" "\<lambda>i. xf i t"]
        by fastforce 
    qed (use e in auto)
    also have "... \<le> j*e + e*(n - j + 1)*e/n "
      using \<open>1 \<le> n\<close> e  by (simp add: field_simps del: of_nat_Suc)
    also have "... \<le> j*e + e*e"
      using \<open>1 \<le> n\<close> e j1 by (simp add: field_simps del: of_nat_Suc)
    also have "... < (j + 1/3)*e"
      using e by (auto simp: field_simps)
    finally have gj1: "g t < (j + 1 / 3) * e" .
    have gj2: "(j - 4/3)*e < g t"
    proof (cases "2 \<le> j")
      case False
      then have "j=1" using j1 by simp
      with t gge0 e show ?thesis by force
    next
      case True
      then have "(j - 4/3)*e < (j-1)*e - e^2"
        using e by (auto simp: of_nat_diff algebra_simps power2_eq_square)
      also have "... < (j-1)*e - ((j - 1)/n) * e^2"
        using e True jn by (simp add: power2_eq_square field_simps)
      also have "... = e * (j-1) * (1 - e/n)"
        by (simp add: power2_eq_square field_simps)
      also have "... \<le> e * (\<Sum>i\<le>j-2. xf i t)"
      proof -
        { fix i
          assume "i+2 \<le> j"
          then obtain d where "i+2+d = j"
            using le_Suc_ex that by blast
          then have "t \<in> B i"
            using Anj e ge_fx [OF t] \<open>1 \<le> n\<close> fpos [OF t] t
            unfolding A_def B_def
            by (auto simp add: field_simps of_nat_diff not_le intro: order_trans [of _ "e * 2 + e * d * 3 + e * i * 3"])
          then have "xf i t > 1 - e/n"
            by (rule xfB)
        } 
        moreover have "real (j - Suc 0) * (1 - e / real n) \<le> real (card {..j - 2}) * (1 - e / real n)"
          using Suc_diff_le True by fastforce
        ultimately show ?thesis
          using e True by (auto intro: order_trans [OF _ sum_bounded_below [OF less_imp_le]])
      qed
      also have "... \<le> g t"
        using jn e xf01 t
        by (auto intro!: Groups_Big.sum_mono2 simp add: g_def zero_le_mult_iff image_subset_iff sum_nonneg)
      finally show ?thesis .
    qed
    have "\<bar>f t - g t\<bar> < 2 * e"
      using fj1 fj2 gj1 gj2 by (simp add: abs_less_iff field_simps)
  }
  then show ?thesis
    by (rule_tac x=g in bexI) (auto intro: gR)
qed

text\<open>The ``unpretentious'' formulation\<close>
proposition (in function_ring_on) Stone_Weierstrass_basic:
  assumes f: "continuous_on S f" and e: "e > 0"
  shows "\<exists>g \<in> R. \<forall>x\<in>S. \<bar>f x - g x\<bar> < e"
proof -
  have "\<exists>g \<in> R. \<forall>x\<in>S. \<bar>(f x + normf f) - g x\<bar> < 2 * min (e/2) (1/4)"
  proof (rule Stone_Weierstrass_special)
    show "continuous_on S (\<lambda>x. f x + normf f)"
      by (force intro: Limits.continuous_on_add [OF f Topological_Spaces.continuous_on_const])
    show "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x + normf f"
      using normf_upper [OF f] by force 
  qed (use e in auto)
  then obtain g where "g \<in> R" "\<forall>x\<in>S. \<bar>g x - (f x + normf f)\<bar> < e"
    by force
  then show ?thesis
    by (rule_tac x="\<lambda>x. g x - normf f" in bexI) (auto simp: algebra_simps intro: diff const)
qed


theorem (in function_ring_on) Stone_Weierstrass:
  assumes f: "continuous_on S f"
  shows "\<exists>F\<in>UNIV \<rightarrow> R. LIM n sequentially. F n :> uniformly_on S f"
proof -
  define h where "h \<equiv> \<lambda>n::nat. SOME g. g \<in> R \<and> (\<forall>x\<in>S. \<bar>f x - g x\<bar> < 1 / (1 + n))"
  show ?thesis
  proof
    { fix e::real
      assume e: "0 < e"
      then obtain N::nat where N: "0 < N" "0 < inverse N" "inverse N < e"
        by (auto simp: real_arch_inverse [of e])
      { fix n :: nat and x :: 'a and g :: "'a \<Rightarrow> real"
        assume n: "N \<le> n"  "\<forall>x\<in>S. \<bar>f x - g x\<bar> < 1 / (1 + real n)"
        assume x: "x \<in> S"
        have "\<not> real (Suc n) < inverse e"
          using \<open>N \<le> n\<close> N using less_imp_inverse_less by force
        then have "1 / (1 + real n) \<le> e"
          using e by (simp add: field_simps)
        then have "\<bar>f x - g x\<bar> < e"
          using n(2) x by auto
      } 
      then have "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. \<bar>f x - h n x\<bar> < e"
        unfolding h_def
        by (force intro: someI2_bex [OF Stone_Weierstrass_basic [OF f]] eventually_sequentiallyI [of N])
    } 
    then show "uniform_limit S h f sequentially"
      unfolding uniform_limit_iff by (auto simp: dist_norm abs_minus_commute)
    show "h \<in> UNIV \<rightarrow> R"
      unfolding h_def by (force intro: someI2_bex [OF Stone_Weierstrass_basic [OF f]])
  qed
qed

text\<open>A HOL Light formulation\<close>
corollary Stone_Weierstrass_HOL:
  fixes R :: "('a::t2_space \<Rightarrow> real) set" and S :: "'a set"
  assumes "compact S"  "\<And>c. P(\<lambda>x. c::real)"
          "\<And>f. P f \<Longrightarrow> continuous_on S f"
          "\<And>f g. P(f) \<and> P(g) \<Longrightarrow> P(\<lambda>x. f x + g x)"  "\<And>f g. P(f) \<and> P(g) \<Longrightarrow> P(\<lambda>x. f x * g x)"
          "\<And>x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y \<Longrightarrow> \<exists>f. P(f) \<and> f x \<noteq> f y"
          "continuous_on S f"
       "0 < e"
    shows "\<exists>g. P(g) \<and> (\<forall>x \<in> S. \<bar>f x - g x\<bar> < e)"
proof -
  interpret PR: function_ring_on "Collect P"
    by unfold_locales (use assms in auto)
  show ?thesis
    using PR.Stone_Weierstrass_basic [OF \<open>continuous_on S f\<close> \<open>0 < e\<close>]
    by blast
qed


subsection \<open>Polynomial functions\<close>

inductive real_polynomial_function :: "('a::real_normed_vector \<Rightarrow> real) \<Rightarrow> bool" where
    linear: "bounded_linear f \<Longrightarrow> real_polynomial_function f"
  | const: "real_polynomial_function (\<lambda>x. c)"
  | add:   "\<lbrakk>real_polynomial_function f; real_polynomial_function g\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. f x + g x)"
  | mult:  "\<lbrakk>real_polynomial_function f; real_polynomial_function g\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. f x * g x)"

declare real_polynomial_function.intros [intro]

definition\<^marker>\<open>tag important\<close> polynomial_function :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
  where
   "polynomial_function p \<equiv> (\<forall>f. bounded_linear f \<longrightarrow> real_polynomial_function (f o p))"

lemma real_polynomial_function_eq: "real_polynomial_function p = polynomial_function p"
unfolding polynomial_function_def
proof
  assume "real_polynomial_function p"
  then show " \<forall>f. bounded_linear f \<longrightarrow> real_polynomial_function (f \<circ> p)"
  proof (induction p rule: real_polynomial_function.induct)
    case (linear h) then show ?case
      by (auto simp: bounded_linear_compose real_polynomial_function.linear)
  next
    case (const h) then show ?case
      by (simp add: real_polynomial_function.const)
  next
    case (add h) then show ?case
      by (force simp add: bounded_linear_def linear_add real_polynomial_function.add)
  next
    case (mult h) then show ?case
      by (force simp add: real_bounded_linear const real_polynomial_function.mult)
  qed
next
  assume [rule_format, OF bounded_linear_ident]: "\<forall>f. bounded_linear f \<longrightarrow> real_polynomial_function (f \<circ> p)"
  then show "real_polynomial_function p"
    by (simp add: o_def)
qed

lemma polynomial_function_const [iff]: "polynomial_function (\<lambda>x. c)"
  by (simp add: polynomial_function_def o_def const)

lemma polynomial_function_bounded_linear:
  "bounded_linear f \<Longrightarrow> polynomial_function f"
  by (simp add: polynomial_function_def o_def bounded_linear_compose real_polynomial_function.linear)

lemma polynomial_function_id [iff]: "polynomial_function(\<lambda>x. x)"
  by (simp add: polynomial_function_bounded_linear)

lemma polynomial_function_add [intro]:
    "\<lbrakk>polynomial_function f; polynomial_function g\<rbrakk> \<Longrightarrow> polynomial_function (\<lambda>x. f x + g x)"
  by (auto simp: polynomial_function_def bounded_linear_def linear_add real_polynomial_function.add o_def)

lemma polynomial_function_mult [intro]:
  assumes f: "polynomial_function f" and g: "polynomial_function g"
  shows "polynomial_function (\<lambda>x. f x *\<^sub>R g x)"
proof -
  have "real_polynomial_function (\<lambda>x. h (g x))" if "bounded_linear h" for h
    using g that unfolding polynomial_function_def o_def bounded_linear_def
    by (auto simp: real_polynomial_function_eq)
  moreover have "real_polynomial_function f"
    by (simp add: f real_polynomial_function_eq)
  ultimately show ?thesis
    unfolding polynomial_function_def bounded_linear_def o_def
    by (auto simp: linear.scaleR)
qed

lemma polynomial_function_cmul [intro]:
  assumes f: "polynomial_function f"
    shows "polynomial_function (\<lambda>x. c *\<^sub>R f x)"
  by (rule polynomial_function_mult [OF polynomial_function_const f])

lemma polynomial_function_minus [intro]:
  assumes f: "polynomial_function f"
    shows "polynomial_function (\<lambda>x. - f x)"
  using polynomial_function_cmul [OF f, of "-1"] by simp

lemma polynomial_function_diff [intro]:
    "\<lbrakk>polynomial_function f; polynomial_function g\<rbrakk> \<Longrightarrow> polynomial_function (\<lambda>x. f x - g x)"
  unfolding add_uminus_conv_diff [symmetric]
  by (metis polynomial_function_add polynomial_function_minus)

lemma polynomial_function_sum [intro]:
    "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> polynomial_function (\<lambda>x. f x i)\<rbrakk> \<Longrightarrow> polynomial_function (\<lambda>x. sum (f x) I)"
by (induct I rule: finite_induct) auto

lemma real_polynomial_function_minus [intro]:
    "real_polynomial_function f \<Longrightarrow> real_polynomial_function (\<lambda>x. - f x)"
  using polynomial_function_minus [of f]
  by (simp add: real_polynomial_function_eq)

lemma real_polynomial_function_diff [intro]:
    "\<lbrakk>real_polynomial_function f; real_polynomial_function g\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. f x - g x)"
  using polynomial_function_diff [of f]
  by (simp add: real_polynomial_function_eq)

lemma real_polynomial_function_sum [intro]:
    "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> real_polynomial_function (\<lambda>x. f x i)\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. sum (f x) I)"
  using polynomial_function_sum [of I f]
  by (simp add: real_polynomial_function_eq)

lemma real_polynomial_function_power [intro]:
    "real_polynomial_function f \<Longrightarrow> real_polynomial_function (\<lambda>x. f x^n)"
  by (induct n) (simp_all add: const mult)

lemma real_polynomial_function_compose [intro]:
  assumes f: "polynomial_function f" and g: "real_polynomial_function g"
    shows "real_polynomial_function (g o f)"
  using g
proof (induction g rule: real_polynomial_function.induct)
  case (linear f)
  then show ?case
    using f polynomial_function_def by blast
next
  case (add f g)
  then show ?case
    using f add by (auto simp: polynomial_function_def)
next
  case (mult f g)
  then show ?case
  using f mult by (auto simp: polynomial_function_def)
qed auto

lemma polynomial_function_compose [intro]:
  assumes f: "polynomial_function f" and g: "polynomial_function g"
    shows "polynomial_function (g o f)"
  using g real_polynomial_function_compose [OF f]
  by (auto simp: polynomial_function_def o_def)

lemma sum_max_0:
  fixes x::real (*in fact "'a::comm_ring_1"*)
  shows "(\<Sum>i\<le>max m n. x^i * (if i \<le> m then a i else 0)) = (\<Sum>i\<le>m. x^i * a i)"
proof -
  have "(\<Sum>i\<le>max m n. x^i * (if i \<le> m then a i else 0)) = (\<Sum>i\<le>max m n. (if i \<le> m then x^i * a i else 0))"
    by (auto simp: algebra_simps intro: sum.cong)
  also have "... = (\<Sum>i\<le>m. (if i \<le> m then x^i * a i else 0))"
    by (rule sum.mono_neutral_right) auto
  also have "... = (\<Sum>i\<le>m. x^i * a i)"
    by (auto simp: algebra_simps intro: sum.cong)
  finally show ?thesis .
qed

lemma real_polynomial_function_imp_sum:
  assumes "real_polynomial_function f"
    shows "\<exists>a n::nat. f = (\<lambda>x. \<Sum>i\<le>n. a i * x^i)"
using assms
proof (induct f)
  case (linear f)
  then obtain c where f: "f = (\<lambda>x. x * c)"
    by (auto simp add: real_bounded_linear)
  have "x * c = (\<Sum>i\<le>1. (if i = 0 then 0 else c) * x^i)" for x
    by (simp add: mult_ac)
  with f show ?case
    by fastforce
next
  case (const c)
  have "c = (\<Sum>i\<le>0. c * x^i)" for x
    by auto
  then show ?case
    by fastforce
  case (add f1 f2)
  then obtain a1 n1 a2 n2 where
    "f1 = (\<lambda>x. \<Sum>i\<le>n1. a1 i * x^i)" "f2 = (\<lambda>x. \<Sum>i\<le>n2. a2 i * x^i)"
    by auto
  then have "f1 x + f2 x = (\<Sum>i\<le>max n1 n2. ((if i \<le> n1 then a1 i else 0) + (if i \<le> n2 then a2 i else 0)) * x^i)" 
      for x
    using sum_max_0 [where m=n1 and n=n2] sum_max_0 [where m=n2 and n=n1]
    by (simp add: sum.distrib algebra_simps max.commute)
  then show ?case
    by force
  case (mult f1 f2)
  then obtain a1 n1 a2 n2 where
    "f1 = (\<lambda>x. \<Sum>i\<le>n1. a1 i * x^i)" "f2 = (\<lambda>x. \<Sum>i\<le>n2. a2 i * x^i)"
    by auto
  then obtain b1 b2 where
    "f1 = (\<lambda>x. \<Sum>i\<le>n1. b1 i * x^i)" "f2 = (\<lambda>x. \<Sum>i\<le>n2. b2 i * x^i)"
    "b1 = (\<lambda>i. if i\<le>n1 then a1 i else 0)" "b2 = (\<lambda>i. if i\<le>n2 then a2 i else 0)"
    by auto
  then have "f1 x * f2 x = (\<Sum>i\<le>n1 + n2. (\<Sum>k\<le>i. b1 k * b2 (i - k)) * x ^ i)" for x
    using polynomial_product [of n1 b1 n2 b2] by (simp add: Set_Interval.atLeast0AtMost)
  then show ?case
    by force
qed

lemma real_polynomial_function_iff_sum:
     "real_polynomial_function f \<longleftrightarrow> (\<exists>a n. f = (\<lambda>x. \<Sum>i\<le>n. a i * x^i))"  (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis real_polynomial_function_imp_sum)
next
  assume ?rhs then show ?lhs
    by (auto simp: linear mult const real_polynomial_function_power real_polynomial_function_sum)
qed

lemma polynomial_function_iff_Basis_inner:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  shows "polynomial_function f \<longleftrightarrow> (\<forall>b\<in>Basis. real_polynomial_function (\<lambda>x. inner (f x) b))"
        (is "?lhs = ?rhs")
unfolding polynomial_function_def
proof (intro iffI allI impI)
  assume "\<forall>h. bounded_linear h \<longrightarrow> real_polynomial_function (h \<circ> f)"
  then show ?rhs
    by (force simp add: bounded_linear_inner_left o_def)
next
  fix h :: "'b \<Rightarrow> real"
  assume rp: "\<forall>b\<in>Basis. real_polynomial_function (\<lambda>x. f x \<bullet> b)" and h: "bounded_linear h"
  have "real_polynomial_function (h \<circ> (\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b))"
    using rp
    by (force simp: real_polynomial_function_eq polynomial_function_mult 
              intro!: real_polynomial_function_compose [OF _  linear [OF h]])
  then show "real_polynomial_function (h \<circ> f)"
    by (simp add: euclidean_representation_sum_fun)
qed

subsection \<open>Stone-Weierstrass theorem for polynomial functions\<close>

text\<open>First, we need to show that they are continuous, differentiable and separable.\<close>

lemma continuous_real_polymonial_function:
  assumes "real_polynomial_function f"
    shows "continuous (at x) f"
using assms
by (induct f) (auto simp: linear_continuous_at)

lemma continuous_polymonial_function:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "polynomial_function f"
    shows "continuous (at x) f"
proof (rule euclidean_isCont)
  show "\<And>b. b \<in> Basis \<Longrightarrow> isCont (\<lambda>x. (f x \<bullet> b) *\<^sub>R b) x"
  using assms continuous_real_polymonial_function
  by (force simp: polynomial_function_iff_Basis_inner intro: isCont_scaleR)
qed

lemma continuous_on_polymonial_function:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "polynomial_function f"
    shows "continuous_on S f"
  using continuous_polymonial_function [OF assms] continuous_at_imp_continuous_on
  by blast

lemma has_real_derivative_polynomial_function:
  assumes "real_polynomial_function p"
    shows "\<exists>p'. real_polynomial_function p' \<and>
                 (\<forall>x. (p has_real_derivative (p' x)) (at x))"
using assms
proof (induct p)
  case (linear p)
  then show ?case
    by (force simp: real_bounded_linear const intro!: derivative_eq_intros)
next
  case (const c)
  show ?case
    by (rule_tac x="\<lambda>x. 0" in exI) auto
  case (add f1 f2)
  then obtain p1 p2 where
    "real_polynomial_function p1" "\<And>x. (f1 has_real_derivative p1 x) (at x)"
    "real_polynomial_function p2" "\<And>x. (f2 has_real_derivative p2 x) (at x)"
    by auto
  then show ?case
    by (rule_tac x="\<lambda>x. p1 x + p2 x" in exI) (auto intro!: derivative_eq_intros)
  case (mult f1 f2)
  then obtain p1 p2 where
    "real_polynomial_function p1" "\<And>x. (f1 has_real_derivative p1 x) (at x)"
    "real_polynomial_function p2" "\<And>x. (f2 has_real_derivative p2 x) (at x)"
    by auto
  then show ?case
    using mult
    by (rule_tac x="\<lambda>x. f1 x * p2 x + f2 x * p1 x" in exI) (auto intro!: derivative_eq_intros)
qed

lemma has_vector_derivative_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "polynomial_function p"
  obtains p' where "polynomial_function p'" "\<And>x. (p has_vector_derivative (p' x)) (at x)"
proof -
  { fix b :: 'a
    assume "b \<in> Basis"
    then
    obtain p' where p': "real_polynomial_function p'" and pd: "\<And>x. ((\<lambda>x. p x \<bullet> b) has_real_derivative p' x) (at x)"
      using assms [unfolded polynomial_function_iff_Basis_inner] has_real_derivative_polynomial_function
      by blast
    have "polynomial_function (\<lambda>x. p' x *\<^sub>R b)"
      using \<open>b \<in> Basis\<close> p' const [where 'a=real and c=0]
      by (simp add: polynomial_function_iff_Basis_inner inner_Basis)
    then have "\<exists>q. polynomial_function q \<and> (\<forall>x. ((\<lambda>u. (p u \<bullet> b) *\<^sub>R b) has_vector_derivative q x) (at x))"
      by (fastforce intro: derivative_eq_intros pd)
  }
  then obtain qf where qf:
      "\<And>b. b \<in> Basis \<Longrightarrow> polynomial_function (qf b)"
      "\<And>b x. b \<in> Basis \<Longrightarrow> ((\<lambda>u. (p u \<bullet> b) *\<^sub>R b) has_vector_derivative qf b x) (at x)"
    by metis
  show ?thesis
  proof
    show "\<And>x. (p has_vector_derivative (\<Sum>b\<in>Basis. qf b x)) (at x)"
      apply (subst euclidean_representation_sum_fun [of p, symmetric])
      by (auto intro: has_vector_derivative_sum qf)
  qed (force intro: qf)
qed

lemma real_polynomial_function_separable:
  fixes x :: "'a::euclidean_space"
  assumes "x \<noteq> y" shows "\<exists>f. real_polynomial_function f \<and> f x \<noteq> f y"
proof -
  have "real_polynomial_function (\<lambda>u. \<Sum>b\<in>Basis. (inner (x-u) b)^2)"
  proof (rule real_polynomial_function_sum)
    show "\<And>i. i \<in> Basis \<Longrightarrow> real_polynomial_function (\<lambda>u. ((x - u) \<bullet> i)\<^sup>2)"
      by (auto simp: algebra_simps real_polynomial_function_diff const linear bounded_linear_inner_left)
  qed auto
  moreover have "(\<Sum>b\<in>Basis. ((x - y) \<bullet> b)\<^sup>2) \<noteq> 0"
    using assms by (force simp add: euclidean_eq_iff [of x y] sum_nonneg_eq_0_iff algebra_simps)
  ultimately show ?thesis
    by auto
qed

lemma Stone_Weierstrass_real_polynomial_function:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "compact S" "continuous_on S f" "0 < e"
  obtains g where "real_polynomial_function g" "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x - g x\<bar> < e"
proof -
  interpret PR: function_ring_on "Collect real_polynomial_function"
  proof unfold_locales
  qed (use assms continuous_on_polymonial_function real_polynomial_function_eq 
       in \<open>auto intro: real_polynomial_function_separable\<close>)
  show ?thesis
    using PR.Stone_Weierstrass_basic [OF \<open>continuous_on S f\<close> \<open>0 < e\<close>] that by blast
qed

theorem Stone_Weierstrass_polynomial_function:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "compact S"
      and f: "continuous_on S f"
      and e: "0 < e"
    shows "\<exists>g. polynomial_function g \<and> (\<forall>x \<in> S. norm(f x - g x) < e)"
proof -
  { fix b :: 'b
    assume "b \<in> Basis"
    have "\<exists>p. real_polynomial_function p \<and> (\<forall>x \<in> S. \<bar>f x \<bullet> b - p x\<bar> < e / DIM('b))"
    proof (rule Stone_Weierstrass_real_polynomial_function [OF S _, of "\<lambda>x. f x \<bullet> b" "e / card Basis"])
      show "continuous_on S (\<lambda>x. f x \<bullet> b)"
        using f by (auto intro: continuous_intros)
    qed (use e in auto)
  }
  then obtain pf where pf:
      "\<And>b. b \<in> Basis \<Longrightarrow> real_polynomial_function (pf b) \<and> (\<forall>x \<in> S. \<bar>f x \<bullet> b - pf b x\<bar> < e / DIM('b))"
    by metis
  let ?g = "\<lambda>x. \<Sum>b\<in>Basis. pf b x *\<^sub>R b"
  { fix x
    assume "x \<in> S"
    have "norm (\<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b - pf b x *\<^sub>R b) \<le> (\<Sum>b\<in>Basis. norm ((f x \<bullet> b) *\<^sub>R b - pf b x *\<^sub>R b))"
      by (rule norm_sum)
    also have "... < of_nat DIM('b) * (e / DIM('b))"
    proof (rule sum_bounded_above_strict)
      show "\<And>i. i \<in> Basis \<Longrightarrow> norm ((f x \<bullet> i) *\<^sub>R i - pf i x *\<^sub>R i) < e / real DIM('b)"
        by (simp add: Real_Vector_Spaces.scaleR_diff_left [symmetric] pf \<open>x \<in> S\<close>)
    qed (rule DIM_positive)
    also have "... = e"
      by (simp add: field_simps)
    finally have "norm (\<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b - pf b x *\<^sub>R b) < e" .
  }
  then have "\<forall>x\<in>S. norm ((\<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) - ?g x) < e"
    by (auto simp flip: sum_subtractf)
  moreover
  have "polynomial_function ?g"
    using pf by (simp add: polynomial_function_sum polynomial_function_mult real_polynomial_function_eq)
  ultimately show ?thesis
    using euclidean_representation_sum_fun [of f] by (metis (no_types, lifting))
qed

proposition Stone_Weierstrass_uniform_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "compact S"
    and f: "continuous_on S f"
  obtains g where "uniform_limit S g f sequentially" "\<And>n. polynomial_function (g n)"
proof -
  have pos: "inverse (Suc n) > 0" for n by auto
  obtain g where g: "\<And>n. polynomial_function (g n)" "\<And>x n. x \<in> S \<Longrightarrow> norm(f x - g n x) < inverse (Suc n)"
    using Stone_Weierstrass_polynomial_function[OF S f pos]
    by metis
  have "uniform_limit S g f sequentially"
  proof (rule uniform_limitI)
    fix e::real assume "0 < e"
    with LIMSEQ_inverse_real_of_nat have "\<forall>\<^sub>F n in sequentially. inverse (Suc n) < e"
      by (rule order_tendstoD)
    moreover have "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. dist (g n x) (f x) < inverse (Suc n)"
      using g by (simp add: dist_norm norm_minus_commute)
    ultimately show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. dist (g n x) (f x) < e"
      by (eventually_elim) auto
  qed
  then show ?thesis using g(1) ..
qed


subsection\<open>Polynomial functions as paths\<close>

text\<open>One application is to pick a smooth approximation to a path,
or just pick a smooth path anyway in an open connected set\<close>

lemma path_polynomial_function:
    fixes g  :: "real \<Rightarrow> 'b::euclidean_space"
    shows "polynomial_function g \<Longrightarrow> path g"
  by (simp add: path_def continuous_on_polymonial_function)

lemma path_approx_polynomial_function:
    fixes g :: "real \<Rightarrow> 'b::euclidean_space"
    assumes "path g" "0 < e"
    obtains p where "polynomial_function p" "pathstart p = pathstart g" "pathfinish p = pathfinish g"
                    "\<And>t. t \<in> {0..1} \<Longrightarrow> norm(p t - g t) < e"
proof -
  obtain q where poq: "polynomial_function q" and noq: "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (g x - q x) < e/4"
    using Stone_Weierstrass_polynomial_function [of "{0..1}" g "e/4"] assms
    by (auto simp: path_def)
  define pf where "pf \<equiv> \<lambda>t. q t + (g 0 - q 0) + t *\<^sub>R (g 1 - q 1 - (g 0 - q 0))"
  show thesis
  proof 
    show "polynomial_function pf"
      by (force simp add: poq pf_def)
    show "norm (pf t - g t) < e"
      if "t \<in> {0..1}" for t
    proof -
      have *: "norm (((q t - g t) + (g 0 - q 0)) + (t *\<^sub>R (g 1 - q 1) + t *\<^sub>R (q 0 - g 0))) < (e/4 + e/4) + (e/4+e/4)"
      proof (intro Real_Vector_Spaces.norm_add_less)
        show "norm (q t - g t) < e / 4"
          by (metis noq norm_minus_commute that)
        show "norm (t *\<^sub>R (g 1 - q 1)) < e / 4"
          using noq that le_less_trans [OF mult_left_le_one_le noq]
          by auto
        show "norm (t *\<^sub>R (q 0 - g 0)) < e / 4"
          using noq that le_less_trans [OF mult_left_le_one_le noq]
          by simp (metis norm_minus_commute order_refl zero_le_one)
      qed (use noq norm_minus_commute that in auto)
      then show ?thesis
        by (auto simp add: algebra_simps pf_def)
    qed
  qed (auto simp add: path_defs pf_def)
qed

proposition connected_open_polynomial_connected:
  fixes S :: "'a::euclidean_space set"
  assumes S: "open S" "connected S"
      and "x \<in> S" "y \<in> S"
    shows "\<exists>g. polynomial_function g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y"
proof -
  have "path_connected S" using assms
    by (simp add: connected_open_path_connected)
  with \<open>x \<in> S\<close> \<open>y \<in> S\<close> obtain p where p: "path p" "path_image p \<subseteq> S" "pathstart p = x" "pathfinish p = y"
    by (force simp: path_connected_def)
  have "\<exists>e. 0 < e \<and> (\<forall>x \<in> path_image p. ball x e \<subseteq> S)"
  proof (cases "S = UNIV")
    case True then show ?thesis
      by (simp add: gt_ex)
  next
    case False
    show ?thesis
    proof (intro exI conjI ballI)
      show "\<And>x. x \<in> path_image p \<Longrightarrow> ball x (setdist (path_image p) (-S)) \<subseteq> S"
        using setdist_le_dist [of _ "path_image p" _ "-S"] by fastforce
      show "0 < setdist (path_image p) (- S)"
        using S p False
        by (fastforce simp add: setdist_gt_0_compact_closed compact_path_image open_closed)
    qed
  qed
  then obtain e where "0 < e"and eb: "\<And>x. x \<in> path_image p \<Longrightarrow> ball x e \<subseteq> S"
    by auto
  obtain pf where "polynomial_function pf" and pf: "pathstart pf = pathstart p" "pathfinish pf = pathfinish p"
                   and pf_e: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm(pf t - p t) < e"
    using path_approx_polynomial_function [OF \<open>path p\<close> \<open>0 < e\<close>] by blast
  show ?thesis 
  proof (intro exI conjI)
    show "polynomial_function pf"
      by fact
    show "pathstart pf = x" "pathfinish pf = y"
      by (simp_all add: p pf)
    show "path_image pf \<subseteq> S"
      unfolding path_image_def
    proof clarsimp
      fix x'::real
      assume "0 \<le> x'" "x' \<le> 1"
      then have "dist (p x') (pf x') < e"
        by (metis atLeastAtMost_iff dist_commute dist_norm pf_e)
      then show "pf x' \<in> S"
        by (metis \<open>0 \<le> x'\<close> \<open>x' \<le> 1\<close> atLeastAtMost_iff eb imageI mem_ball path_image_def subset_iff)
    qed
  qed
qed

lemma differentiable_componentwise_within:
   "f differentiable (at a within S) \<longleftrightarrow>
    (\<forall>i \<in> Basis. (\<lambda>x. f x \<bullet> i) differentiable at a within S)"
proof -
  { assume "\<forall>i\<in>Basis. \<exists>D. ((\<lambda>x. f x \<bullet> i) has_derivative D) (at a within S)"
    then obtain f' where f':
           "\<And>i. i \<in> Basis \<Longrightarrow> ((\<lambda>x. f x \<bullet> i) has_derivative f' i) (at a within S)"
      by metis
    have eq: "(\<lambda>x. (\<Sum>j\<in>Basis. f' j x *\<^sub>R j) \<bullet> i) = f' i" if "i \<in> Basis" for i
      using that by (simp add: inner_add_left inner_add_right)
    have "\<exists>D. \<forall>i\<in>Basis. ((\<lambda>x. f x \<bullet> i) has_derivative (\<lambda>x. D x \<bullet> i)) (at a within S)"
      apply (rule_tac x="\<lambda>x::'a. (\<Sum>j\<in>Basis. f' j x *\<^sub>R j) :: 'b" in exI)
      apply (simp add: eq f')
      done
  }
  then show ?thesis
    apply (simp add: differentiable_def)
    using has_derivative_componentwise_within
    by blast
qed

lemma polynomial_function_inner [intro]:
  fixes i :: "'a::euclidean_space"
  shows "polynomial_function g \<Longrightarrow> polynomial_function (\<lambda>x. g x \<bullet> i)"
  apply (subst euclidean_representation [where x=i, symmetric])
  apply (force simp: inner_sum_right polynomial_function_iff_Basis_inner polynomial_function_sum)
  done

text\<open> Differentiability of real and vector polynomial functions.\<close>

lemma differentiable_at_real_polynomial_function:
   "real_polynomial_function f \<Longrightarrow> f differentiable (at a within S)"
  by (induction f rule: real_polynomial_function.induct)
     (simp_all add: bounded_linear_imp_differentiable)

lemma differentiable_on_real_polynomial_function:
   "real_polynomial_function p \<Longrightarrow> p differentiable_on S"
by (simp add: differentiable_at_imp_differentiable_on differentiable_at_real_polynomial_function)

lemma differentiable_at_polynomial_function:
  fixes f :: "_ \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function f \<Longrightarrow> f differentiable (at a within S)"
  by (metis differentiable_at_real_polynomial_function polynomial_function_iff_Basis_inner differentiable_componentwise_within)

lemma differentiable_on_polynomial_function:
  fixes f :: "_ \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function f \<Longrightarrow> f differentiable_on S"
by (simp add: differentiable_at_polynomial_function differentiable_on_def)

lemma vector_eq_dot_span:
  assumes "x \<in> span B" "y \<in> span B" and i: "\<And>i. i \<in> B \<Longrightarrow> i \<bullet> x = i \<bullet> y"
  shows "x = y"
proof -
  have "\<And>i. i \<in> B \<Longrightarrow> orthogonal (x - y) i"
    by (simp add: i inner_commute inner_diff_right orthogonal_def)
  moreover have "x - y \<in> span B"
    by (simp add: assms span_diff)
  ultimately have "x - y = 0"
    using orthogonal_to_span orthogonal_self by blast
    then show ?thesis by simp
qed

lemma orthonormal_basis_expand:
  assumes B: "pairwise orthogonal B"
      and 1: "\<And>i. i \<in> B \<Longrightarrow> norm i = 1"
      and "x \<in> span B"
      and "finite B"
    shows "(\<Sum>i\<in>B. (x \<bullet> i) *\<^sub>R i) = x"
proof (rule vector_eq_dot_span [OF _ \<open>x \<in> span B\<close>])
  show "(\<Sum>i\<in>B. (x \<bullet> i) *\<^sub>R i) \<in> span B"
    by (simp add: span_clauses span_sum)
  show "i \<bullet> (\<Sum>i\<in>B. (x \<bullet> i) *\<^sub>R i) = i \<bullet> x" if "i \<in> B" for i
  proof -
    have [simp]: "i \<bullet> j = (if j = i then 1 else 0)" if "j \<in> B" for j
      using B 1 that \<open>i \<in> B\<close>
      by (force simp: norm_eq_1 orthogonal_def pairwise_def)
    have "i \<bullet> (\<Sum>i\<in>B. (x \<bullet> i) *\<^sub>R i) = (\<Sum>j\<in>B. x \<bullet> j * (i \<bullet> j))"
      by (simp add: inner_sum_right)
    also have "... = (\<Sum>j\<in>B. if j = i then x \<bullet> i else 0)"
      by (rule sum.cong; simp)
    also have "... = i \<bullet> x"
      by (simp add: \<open>finite B\<close> that inner_commute)
    finally show ?thesis .
  qed
qed


theorem Stone_Weierstrass_polynomial_function_subspace:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact S"
      and contf: "continuous_on S f"
      and "0 < e"
      and "subspace T" "f ` S \<subseteq> T"
    obtains g where "polynomial_function g" "g ` S \<subseteq> T"
                    "\<And>x. x \<in> S \<Longrightarrow> norm(f x - g x) < e"
proof -
  obtain B where "B \<subseteq> T" and orthB: "pairwise orthogonal B"
             and B1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
             and "independent B" and cardB: "card B = dim T"
             and spanB: "span B = T"
    using orthonormal_basis_subspace \<open>subspace T\<close> by metis
  then have "finite B"
    by (simp add: independent_imp_finite)
  then obtain n::nat and b where "B = b ` {i. i < n}" "inj_on b {i. i < n}"
    using finite_imp_nat_seg_image_inj_on by metis
  with cardB have "n = card B" "dim T = n"
    by (auto simp: card_image)
  have fx: "(\<Sum>i\<in>B. (f x \<bullet> i) *\<^sub>R i) = f x" if "x \<in> S" for x
    by (metis (no_types, lifting) B1 \<open>finite B\<close> assms(5) image_subset_iff orthB orthonormal_basis_expand spanB sum.cong that)
  have cont: "continuous_on S (\<lambda>x. \<Sum>i\<in>B. (f x \<bullet> i) *\<^sub>R i)"
    by (intro continuous_intros contf)
  obtain g where "polynomial_function g"
             and g: "\<And>x. x \<in> S \<Longrightarrow> norm ((\<Sum>i\<in>B. (f x \<bullet> i) *\<^sub>R i) - g x) < e / (n+2)"
    using Stone_Weierstrass_polynomial_function [OF \<open>compact S\<close> cont, of "e / real (n + 2)"] \<open>0 < e\<close>
    by auto
  with fx have g: "\<And>x. x \<in> S \<Longrightarrow> norm (f x - g x) < e / (n+2)"
    by auto
  show ?thesis
  proof
    show "polynomial_function (\<lambda>x. \<Sum>i\<in>B. (g x \<bullet> i) *\<^sub>R i)"
      using \<open>polynomial_function g\<close> by (force intro: \<open>finite B\<close>)
    show "(\<lambda>x. \<Sum>i\<in>B. (g x \<bullet> i) *\<^sub>R i) ` S \<subseteq> T"
      using \<open>B \<subseteq> T\<close>
      by (blast intro: subspace_sum subspace_mul \<open>subspace T\<close>)
    show "norm (f x - (\<Sum>i\<in>B. (g x \<bullet> i) *\<^sub>R i)) < e" if "x \<in> S" for x
    proof -
      have orth': "pairwise (\<lambda>i j. orthogonal ((f x \<bullet> i) *\<^sub>R i - (g x \<bullet> i) *\<^sub>R i)
                                              ((f x \<bullet> j) *\<^sub>R j - (g x \<bullet> j) *\<^sub>R j)) B"
        by (auto simp: orthogonal_def inner_diff_right inner_diff_left intro: pairwise_mono [OF orthB])
      then have "(norm (\<Sum>i\<in>B. (f x \<bullet> i) *\<^sub>R i - (g x \<bullet> i) *\<^sub>R i))\<^sup>2 =
                 (\<Sum>i\<in>B. (norm ((f x \<bullet> i) *\<^sub>R i - (g x \<bullet> i) *\<^sub>R i))\<^sup>2)"
        by (simp add:  norm_sum_Pythagorean [OF \<open>finite B\<close> orth'])
      also have "... = (\<Sum>i\<in>B. (norm (((f x - g x) \<bullet> i) *\<^sub>R i))\<^sup>2)"
        by (simp add: algebra_simps)
      also have "... \<le> (\<Sum>i\<in>B. (norm (f x - g x))\<^sup>2)"
      proof -
        have "\<And>i. i \<in> B \<Longrightarrow> ((f x - g x) \<bullet> i)\<^sup>2 \<le> (norm (f x - g x))\<^sup>2"
          by (metis B1 Cauchy_Schwarz_ineq inner_commute mult.left_neutral norm_eq_1 power2_norm_eq_inner)
        then show ?thesis
          by (intro sum_mono) (simp add: sum_mono B1)
      qed
      also have "... = n * norm (f x - g x)^2"
        by (simp add: \<open>n = card B\<close>)
      also have "... \<le> n * (e / (n+2))^2"
      proof (rule mult_left_mono)
        show "(norm (f x - g x))\<^sup>2 \<le> (e / real (n + 2))\<^sup>2"
          by (meson dual_order.order_iff_strict g norm_ge_zero power_mono that)
      qed auto
      also have "... \<le> e^2 / (n+2)"
        using \<open>0 < e\<close> by (simp add: divide_simps power2_eq_square)
      also have "... < e^2"
        using \<open>0 < e\<close> by (simp add: divide_simps)
      finally have "(norm (\<Sum>i\<in>B. (f x \<bullet> i) *\<^sub>R i - (g x \<bullet> i) *\<^sub>R i))\<^sup>2 < e^2" .
      then have "(norm (\<Sum>i\<in>B. (f x \<bullet> i) *\<^sub>R i - (g x \<bullet> i) *\<^sub>R i)) < e"
        by (simp add: \<open>0 < e\<close> norm_lt_square power2_norm_eq_inner)
      then show ?thesis
        using fx that by (simp add: sum_subtractf)
    qed
  qed
qed


hide_fact linear add mult const

end
