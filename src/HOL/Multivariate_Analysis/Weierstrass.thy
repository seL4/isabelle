section \<open>The Bernstein-Weierstrass and Stone-Weierstrass Theorems\<close>

text\<open>By L C Paulson (2015)\<close>

theory Weierstrass
imports Uniform_Limit Path_Connected
begin

subsection \<open>Bernstein polynomials\<close>

definition Bernstein :: "[nat,nat,real] \<Rightarrow> real" where
  "Bernstein n k x \<equiv> of_nat (n choose k) * x ^ k * (1 - x) ^ (n - k)"

lemma Bernstein_nonneg: "\<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> 0 \<le> Bernstein n k x"
  by (simp add: Bernstein_def)

lemma Bernstein_pos: "\<lbrakk>0 < x; x < 1; k \<le> n\<rbrakk> \<Longrightarrow> 0 < Bernstein n k x"
  by (simp add: Bernstein_def)

lemma sum_Bernstein [simp]: "(\<Sum> k = 0..n. Bernstein n k x) = 1"
  using binomial_ring [of x "1-x" n]
  by (simp add: Bernstein_def)

lemma binomial_deriv1:
    "(\<Sum>k=0..n. (of_nat k * of_nat (n choose k)) * a^(k-1) * b^(n-k)) = real_of_nat n * (a+b) ^ (n-1)"
  apply (rule DERIV_unique [where f = "\<lambda>a. (a+b)^n" and x=a])
  apply (subst binomial_ring)
  apply (rule derivative_eq_intros setsum.cong | simp)+
  done

lemma binomial_deriv2:
    "(\<Sum>k=0..n. (of_nat k * of_nat (k-1) * of_nat (n choose k)) * a^(k-2) * b^(n-k)) =
     of_nat n * of_nat (n-1) * (a+b::real) ^ (n-2)"
  apply (rule DERIV_unique [where f = "\<lambda>a. of_nat n * (a+b::real) ^ (n-1)" and x=a])
  apply (subst binomial_deriv1 [symmetric])
  apply (rule derivative_eq_intros setsum.cong | simp add: Num.numeral_2_eq_2)+
  done

lemma sum_k_Bernstein [simp]: "(\<Sum>k = 0..n. real k * Bernstein n k x) = of_nat n * x"
  apply (subst binomial_deriv1 [of n x "1-x", simplified, symmetric])
  apply (simp add: setsum_left_distrib)
  apply (auto simp: Bernstein_def algebra_simps realpow_num_eq_if intro!: setsum.cong)
  done

lemma sum_kk_Bernstein [simp]: "(\<Sum> k = 0..n. real k * (real k - 1) * Bernstein n k x) = real n * (real n - 1) * x\<^sup>2"
proof -
  have "(\<Sum> k = 0..n. real k * (real k - 1) * Bernstein n k x) = real_of_nat n * real_of_nat (n - Suc 0) * x\<^sup>2"
    apply (subst binomial_deriv2 [of n x "1-x", simplified, symmetric])
    apply (simp add: setsum_left_distrib)
    apply (rule setsum.cong [OF refl])
    apply (simp add: Bernstein_def power2_eq_square algebra_simps)
    apply (rename_tac k)
    apply (subgoal_tac "k = 0 \<or> k = 1 \<or> (\<exists>k'. k = Suc (Suc k'))")
    apply (force simp add: field_simps of_nat_Suc power2_eq_square)
    by presburger
  also have "... = n * (n - 1) * x\<^sup>2"
    by auto
  finally show ?thesis
    by auto
qed

subsection \<open>Explicit Bernstein version of the 1D Weierstrass approximation theorem\<close>

lemma Bernstein_Weierstrass:
  fixes f :: "real \<Rightarrow> real"
  assumes contf: "continuous_on {0..1} f" and e: "0 < e"
    shows "\<exists>N. \<forall>n x. N \<le> n \<and> x \<in> {0..1}
                    \<longrightarrow> \<bar>f x - (\<Sum>k = 0..n. f(k/n) * Bernstein n k x)\<bar> < e"
proof -
  have "bounded (f ` {0..1})"
    using compact_continuous_image compact_imp_bounded contf by blast
  then obtain M where M: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> \<bar>f x\<bar> \<le> M"
    by (force simp add: bounded_iff)
  then have Mge0: "0 \<le> M" by force
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
      by (simp add: of_nat_Suc field_simps)
    have "4*M/(e*d\<^sup>2) + 1 \<le> real (Suc (nat\<lceil>4*M/(e*d\<^sup>2)\<rceil>))"
      by (simp add: of_nat_Suc real_nat_ceiling_ge)
    also have "... \<le> real n"
      using n by (simp add: of_nat_Suc field_simps)
    finally have nbig: "4*M/(e*d\<^sup>2) + 1 \<le> real n" .
    have sum_bern: "(\<Sum>k = 0..n. (x - k/n)\<^sup>2 * Bernstein n k x) = x * (1 - x) / n"
    proof -
      have *: "\<And>a b x::real. (a - b)\<^sup>2 * x = a * (a - 1) * x + (1 - 2 * b) * a * x + b * b * x"
        by (simp add: algebra_simps power2_eq_square)
      have "(\<Sum> k = 0..n. (k - n * x)\<^sup>2 * Bernstein n k x) = n * x * (1 - x)"
        apply (simp add: * setsum.distrib)
        apply (simp add: setsum_right_distrib [symmetric] mult.assoc)
        apply (simp add: algebra_simps power2_eq_square)
        done
      then have "(\<Sum> k = 0..n. (k - n * x)\<^sup>2 * Bernstein n k x)/n^2 = x * (1 - x) / n"
        by (simp add: power2_eq_square)
      then show ?thesis
        using n by (simp add: setsum_divide_distrib divide_simps mult.commute power2_commute)
    qed
    { fix k
      assume k: "k \<le> n"
      then have kn: "0 \<le> k / n" "k / n \<le> 1"
        by (auto simp: divide_simps)
      consider (lessd) "\<bar>x - k / n\<bar> < d" | (ged) "d \<le> \<bar>x - k / n\<bar>"
        by linarith
      then have "\<bar>(f x - f (k/n))\<bar> \<le> e/2 + 2 * M / d\<^sup>2 * (x - k/n)\<^sup>2"
      proof cases
        case lessd
        then have "\<bar>(f x - f (k/n))\<bar> < e/2"
          using d x kn by (simp add: abs_minus_commute)
        also have "... \<le> (e/2 + 2 * M / d\<^sup>2 * (x - k/n)\<^sup>2)"
          using Mge0 d by simp
        finally show ?thesis by simp
      next
        case ged
        then have dle: "d\<^sup>2 \<le> (x - k/n)\<^sup>2"
          by (metis d(1) less_eq_real_def power2_abs power_mono)
        have "\<bar>(f x - f (k/n))\<bar> \<le> \<bar>f x\<bar> + \<bar>f (k/n)\<bar>"
          by (rule abs_triangle_ineq4)
        also have "... \<le> M+M"
          by (meson M add_mono_thms_linordered_semiring(1) kn x)
        also have "... \<le> 2 * M * ((x - k/n)\<^sup>2 / d\<^sup>2)"
          apply simp
          apply (rule Rings.ordered_semiring_class.mult_left_mono [of 1 "((x - k/n)\<^sup>2 / d\<^sup>2)", simplified])
          using dle \<open>d>0\<close> \<open>M\<ge>0\<close> by auto
        also have "... \<le> e/2 + 2 * M / d\<^sup>2 * (x - k/n)\<^sup>2"
          using e  by simp
        finally show ?thesis .
        qed
    } note * = this
    have "\<bar>f x - (\<Sum> k = 0..n. f(k / n) * Bernstein n k x)\<bar> \<le> \<bar>\<Sum> k = 0..n. (f x - f(k / n)) * Bernstein n k x\<bar>"
      by (simp add: setsum_subtractf setsum_right_distrib [symmetric] algebra_simps)
    also have "... \<le> (\<Sum> k = 0..n. (e/2 + (2 * M / d\<^sup>2) * (x - k / n)\<^sup>2) * Bernstein n k x)"
      apply (rule order_trans [OF setsum_abs setsum_mono])
      using *
      apply (simp add: abs_mult Bernstein_nonneg x mult_right_mono)
      done
    also have "... \<le> e/2 + (2 * M) / (d\<^sup>2 * n)"
      apply (simp only: setsum.distrib Rings.semiring_class.distrib_right setsum_right_distrib [symmetric] mult.assoc sum_bern)
      using \<open>d>0\<close> x
      apply (simp add: divide_simps Mge0 mult_le_one mult_left_le)
      done
    also have "... < e"
      apply (simp add: field_simps)
      using \<open>d>0\<close> nbig e \<open>n>0\<close>
      apply (simp add: divide_simps algebra_simps)
      using ed0 by linarith
    finally have "\<bar>f x - (\<Sum>k = 0..n. f (real k / real n) * Bernstein n k x)\<bar> < e" .
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
DOI: 10.2307/2043993  http://www.jstor.org/stable/2043993\<close>

locale function_ring_on =
  fixes R :: "('a::t2_space \<Rightarrow> real) set" and s :: "'a set"
  assumes compact: "compact s"
  assumes continuous: "f \<in> R \<Longrightarrow> continuous_on s f"
  assumes add: "f \<in> R \<Longrightarrow> g \<in> R \<Longrightarrow> (\<lambda>x. f x + g x) \<in> R"
  assumes mult: "f \<in> R \<Longrightarrow> g \<in> R \<Longrightarrow> (\<lambda>x. f x * g x) \<in> R"
  assumes const: "(\<lambda>_. c) \<in> R"
  assumes separable: "x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>f\<in>R. f x \<noteq> f y"

begin
  lemma minus: "f \<in> R \<Longrightarrow> (\<lambda>x. - f x) \<in> R"
    by (frule mult [OF const [of "-1"]]) simp

  lemma diff: "f \<in> R \<Longrightarrow> g \<in> R \<Longrightarrow> (\<lambda>x. f x - g x) \<in> R"
    unfolding diff_conv_add_uminus by (metis add minus)

  lemma power: "f \<in> R \<Longrightarrow> (\<lambda>x. f x ^ n) \<in> R"
    by (induct n) (auto simp: const mult)

  lemma setsum: "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> f i \<in> R\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Sum>i \<in> I. f i x) \<in> R"
    by (induct I rule: finite_induct; simp add: const add)

  lemma setprod: "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> f i \<in> R\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Prod>i \<in> I. f i x) \<in> R"
    by (induct I rule: finite_induct; simp add: const mult)

  definition normf :: "('a::t2_space \<Rightarrow> real) \<Rightarrow> real"
    where "normf f \<equiv> SUP x:s. \<bar>f x\<bar>"

  lemma normf_upper: "\<lbrakk>continuous_on s f; x \<in> s\<rbrakk> \<Longrightarrow> \<bar>f x\<bar> \<le> normf f"
    apply (simp add: normf_def)
    apply (rule cSUP_upper, assumption)
    by (simp add: bounded_imp_bdd_above compact compact_continuous_image compact_imp_bounded continuous_on_rabs)

  lemma normf_least: "s \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> s \<Longrightarrow> \<bar>f x\<bar> \<le> M) \<Longrightarrow> normf f \<le> M"
    by (simp add: normf_def cSUP_least)

end

lemma (in function_ring_on) one:
  assumes U: "open U" and t0: "t0 \<in> s" "t0 \<in> U" and t1: "t1 \<in> s-U"
    shows "\<exists>V. open V \<and> t0 \<in> V \<and> s \<inter> V \<subseteq> U \<and>
               (\<forall>e>0. \<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>t \<in> s \<inter> V. f t < e) \<and> (\<forall>t \<in> s - U. f t > 1 - e))"
proof -
  have "\<exists>pt \<in> R. pt t0 = 0 \<and> pt t > 0 \<and> pt ` s \<subseteq> {0..1}" if t: "t \<in> s - U" for t
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
    moreover have "\<And>x. x \<in> s \<Longrightarrow> p x \<in> {0..1}"
      using nfp normf_upper [OF continuous [OF hsq] ] by (auto simp: p_def)
    ultimately show "\<exists>pt \<in> R. pt t0 = 0 \<and> pt t > 0 \<and> pt ` s \<subseteq> {0..1}"
      by auto
  qed
  then obtain pf where pf: "\<And>t. t \<in> s-U \<Longrightarrow> pf t \<in> R \<and> pf t t0 = 0 \<and> pf t t > 0"
                   and pf01: "\<And>t. t \<in> s-U \<Longrightarrow> pf t ` s \<subseteq> {0..1}"
    by metis
  have com_sU: "compact (s-U)"
    using compact closed_Int_compact U by (simp add: Diff_eq compact_Int_closed open_closed)
  have "\<And>t. t \<in> s-U \<Longrightarrow> \<exists>A. open A \<and> A \<inter> s = {x\<in>s. 0 < pf t x}"
    apply (rule open_Collect_positive)
    by (metis pf continuous)
  then obtain Uf where Uf: "\<And>t. t \<in> s-U \<Longrightarrow> open (Uf t) \<and> (Uf t) \<inter> s = {x\<in>s. 0 < pf t x}"
    by metis
  then have open_Uf: "\<And>t. t \<in> s-U \<Longrightarrow> open (Uf t)"
    by blast
  have tUft: "\<And>t. t \<in> s-U \<Longrightarrow> t \<in> Uf t"
    using pf Uf by blast
  then have *: "s-U \<subseteq> (\<Union>x \<in> s-U. Uf x)"
    by blast
  obtain subU where subU: "subU \<subseteq> s - U" "finite subU" "s - U \<subseteq> (\<Union>x \<in> subU. Uf x)"
    by (blast intro: that open_Uf compactE_image [OF com_sU _ *])
  then have [simp]: "subU \<noteq> {}"
    using t1 by auto
  then have cardp: "card subU > 0" using subU
    by (simp add: card_gt_0_iff)
  define p where [abs_def]: "p x = (1 / card subU) * (\<Sum>t \<in> subU. pf t x)" for x
  have pR: "p \<in> R"
    unfolding p_def using subU pf by (fast intro: pf const mult setsum)
  have pt0 [simp]: "p t0 = 0"
    using subU pf by (auto simp: p_def intro: setsum.neutral)
  have pt_pos: "p t > 0" if t: "t \<in> s-U" for t
  proof -
    obtain i where i: "i \<in> subU" "t \<in> Uf i" using subU t by blast
    show ?thesis
      using subU i t
      apply (clarsimp simp: p_def divide_simps)
      apply (rule setsum_pos2 [OF \<open>finite subU\<close>])
      using Uf t pf01 apply auto
      apply (force elim!: subsetCE)
      done
  qed
  have p01: "p x \<in> {0..1}" if t: "x \<in> s" for x
  proof -
    have "0 \<le> p x"
      using subU cardp t
      apply (simp add: p_def divide_simps setsum_nonneg)
      apply (rule setsum_nonneg)
      using pf01 by force
    moreover have "p x \<le> 1"
      using subU cardp t
      apply (simp add: p_def divide_simps setsum_nonneg)
      apply (rule setsum_bounded_above [where 'a=real and K=1, simplified])
      using pf01 by force
    ultimately show ?thesis
      by auto
  qed
  have "compact (p ` (s-U))"
    by (meson Diff_subset com_sU compact_continuous_image continuous continuous_on_subset pR)
  then have "open (- (p ` (s-U)))"
    by (simp add: compact_imp_closed open_Compl)
  moreover have "0 \<in> - (p ` (s-U))"
    by (metis (no_types) ComplI image_iff not_less_iff_gr_or_eq pt_pos)
  ultimately obtain delta0 where delta0: "delta0 > 0" "ball 0 delta0 \<subseteq> - (p ` (s-U))"
    by (auto simp: elim!: openE)
  then have pt_delta: "\<And>x. x \<in> s-U \<Longrightarrow> p x \<ge> delta0"
    by (force simp: ball_def dist_norm dest: p01)
  define \<delta> where "\<delta> = delta0/2"
  have "delta0 \<le> 1" using delta0 p01 [of t1] t1
      by (force simp: ball_def dist_norm dest: p01)
  with delta0 have \<delta>01: "0 < \<delta>" "\<delta> < 1"
    by (auto simp: \<delta>_def)
  have pt_\<delta>: "\<And>x. x \<in> s-U \<Longrightarrow> p x \<ge> \<delta>"
    using pt_delta delta0 by (force simp: \<delta>_def)
  have "\<exists>A. open A \<and> A \<inter> s = {x\<in>s. p x < \<delta>/2}"
    by (rule open_Collect_less_Int [OF continuous [OF pR] continuous_on_const])
  then obtain V where V: "open V" "V \<inter> s = {x\<in>s. p x < \<delta>/2}"
    by blast
  define k where "k = nat\<lfloor>1/\<delta>\<rfloor> + 1"
  have "k>0"  by (simp add: k_def)
  have "k-1 \<le> 1/\<delta>"
    using \<delta>01 by (simp add: k_def)
  with \<delta>01 have "k \<le> (1+\<delta>)/\<delta>"
    by (auto simp: algebra_simps add_divide_distrib)
  also have "... < 2/\<delta>"
    using \<delta>01 by (auto simp: divide_simps)
  finally have k2\<delta>: "k < 2/\<delta>" .
  have "1/\<delta> < k"
    using \<delta>01 unfolding k_def by linarith
  with \<delta>01 k2\<delta> have k\<delta>: "1 < k*\<delta>" "k*\<delta> < 2"
    by (auto simp: divide_simps)
  define q where [abs_def]: "q n t = (1 - p t ^ n) ^ (k^n)" for n t
  have qR: "q n \<in> R" for n
    by (simp add: q_def const diff power pR)
  have q01: "\<And>n t. t \<in> s \<Longrightarrow> q n t \<in> {0..1}"
    using p01 by (simp add: q_def power_le_one algebra_simps)
  have qt0 [simp]: "\<And>n. n>0 \<Longrightarrow> q n t0 = 1"
    using t0 pf by (simp add: q_def power_0_left)
  { fix t and n::nat
    assume t: "t \<in> s \<inter> V"
    with \<open>k>0\<close> V have "k * p t < k * \<delta> / 2"
       by force
    then have "1 - (k * \<delta> / 2)^n \<le> 1 - (k * p t)^n"
      using  \<open>k>0\<close> p01 t by (simp add: power_mono)
    also have "... \<le> q n t"
      using Bernoulli_inequality [of "- ((p t)^n)" "k^n"]
      apply (simp add: q_def)
      by (metis IntE atLeastAtMost_iff p01 power_le_one power_mult_distrib t)
    finally have "1 - (k * \<delta> / 2) ^ n \<le> q n t" .
  } note limitV = this
  { fix t and n::nat
    assume t: "t \<in> s - U"
    with \<open>k>0\<close> U have "k * \<delta> \<le> k * p t"
      by (simp add: pt_\<delta>)
    with k\<delta> have kpt: "1 < k * p t"
      by (blast intro: less_le_trans)
    have ptn_pos: "0 < p t ^ n"
      using pt_pos [OF t] by simp
    have ptn_le: "p t ^ n \<le> 1"
      by (meson DiffE atLeastAtMost_iff p01 power_le_one t)
    have "q n t = (1/(k^n * (p t)^n)) * (1 - p t ^ n) ^ (k^n) * k^n * (p t)^n"
      using pt_pos [OF t] \<open>k>0\<close> by (simp add: q_def)
    also have "... \<le> (1/(k * (p t))^n) * (1 - p t ^ n) ^ (k^n) * (1 + k^n * (p t)^n)"
      using pt_pos [OF t] \<open>k>0\<close>
      apply simp
      apply (simp only: times_divide_eq_right [symmetric])
      apply (rule mult_left_mono [of "1::real", simplified])
      apply (simp_all add: power_mult_distrib)
      apply (rule zero_le_power)
      using ptn_le by linarith
    also have "... \<le> (1/(k * (p t))^n) * (1 - p t ^ n) ^ (k^n) * (1 + (p t)^n) ^ (k^n)"
      apply (rule mult_left_mono [OF Bernoulli_inequality [of "p t ^ n" "k^n"]])
      using \<open>k>0\<close> ptn_pos ptn_le
      apply (auto simp: power_mult_distrib)
      done
    also have "... = (1/(k * (p t))^n) * (1 - p t ^ (2*n)) ^ (k^n)"
      using pt_pos [OF t] \<open>k>0\<close>
      by (simp add: algebra_simps power_mult power2_eq_square power_mult_distrib [symmetric])
    also have "... \<le> (1/(k * (p t))^n) * 1"
      apply (rule mult_left_mono [OF power_le_one])
      using pt_pos \<open>k>0\<close> p01 power_le_one t apply auto
      done
    also have "... \<le> (1 / (k*\<delta>))^n"
      using \<open>k>0\<close> \<delta>01  power_mono pt_\<delta> t
      by (fastforce simp: field_simps)
    finally have "q n t \<le> (1 / (real k * \<delta>)) ^ n " .
  } note limitNonU = this
  define NN
    where "NN e = 1 + nat \<lceil>max (ln e / ln (real k * \<delta> / 2)) (- ln e / ln (real k * \<delta>))\<rceil>" for e
  have NN: "of_nat (NN e) > ln e / ln (real k * \<delta> / 2)"  "of_nat (NN e) > - ln e / ln (real k * \<delta>)"
              if "0<e" for e
      unfolding NN_def  by linarith+
  have NN1: "\<And>e. e>0 \<Longrightarrow> (k * \<delta> / 2)^NN e < e"
    apply (subst Transcendental.ln_less_cancel_iff [symmetric])
      prefer 3 apply (subst ln_realpow)
    using \<open>k>0\<close> \<open>\<delta>>0\<close> NN  k\<delta>
    apply (force simp add: field_simps)+
    done
  have NN0: "\<And>e. e>0 \<Longrightarrow> (1/(k*\<delta>))^NN e < e"
    apply (subst Transcendental.ln_less_cancel_iff [symmetric])
      prefer 3 apply (subst ln_realpow)
    using \<open>k>0\<close> \<open>\<delta>>0\<close> NN k\<delta>
    apply (force simp add: field_simps ln_div)+
    done
  { fix t and e::real
    assume "e>0"
    have "t \<in> s \<inter> V \<Longrightarrow> 1 - q (NN e) t < e" "t \<in> s - U \<Longrightarrow> q (NN e) t < e"
    proof -
      assume t: "t \<in> s \<inter> V"
      show "1 - q (NN e) t < e"
        by (metis add.commute diff_le_eq not_le limitV [OF t] less_le_trans [OF NN1 [OF \<open>e>0\<close>]])
    next
      assume t: "t \<in> s - U"
      show "q (NN e) t < e"
      using  limitNonU [OF t] less_le_trans [OF NN0 [OF \<open>e>0\<close>]] not_le by blast
    qed
  } then have "\<And>e. e > 0 \<Longrightarrow> \<exists>f\<in>R. f ` s \<subseteq> {0..1} \<and> (\<forall>t \<in> s \<inter> V. f t < e) \<and> (\<forall>t \<in> s - U. 1 - e < f t)"
    using q01
    by (rule_tac x="\<lambda>x. 1 - q (NN e) x" in bexI) (auto simp: algebra_simps intro: diff const qR)
  moreover have t0V: "t0 \<in> V"  "s \<inter> V \<subseteq> U"
    using pt_\<delta> t0 U V \<delta>01  by fastforce+
  ultimately show ?thesis using V t0V
    by blast
qed

text\<open>Non-trivial case, with @{term A} and @{term B} both non-empty\<close>
lemma (in function_ring_on) two_special:
  assumes A: "closed A" "A \<subseteq> s" "a \<in> A"
      and B: "closed B" "B \<subseteq> s" "b \<in> B"
      and disj: "A \<inter> B = {}"
      and e: "0 < e" "e < 1"
    shows "\<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>x \<in> A. f x < e) \<and> (\<forall>x \<in> B. f x > 1 - e)"
proof -
  { fix w
    assume "w \<in> A"
    then have "open ( - B)" "b \<in> s" "w \<notin> B" "w \<in> s"
      using assms by auto
    then have "\<exists>V. open V \<and> w \<in> V \<and> s \<inter> V \<subseteq> -B \<and>
               (\<forall>e>0. \<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>x \<in> s \<inter> V. f x < e) \<and> (\<forall>x \<in> s \<inter> B. f x > 1 - e))"
      using one [of "-B" w b] assms \<open>w \<in> A\<close> by simp
  }
  then obtain Vf where Vf:
         "\<And>w. w \<in> A \<Longrightarrow> open (Vf w) \<and> w \<in> Vf w \<and> s \<inter> Vf w \<subseteq> -B \<and>
                         (\<forall>e>0. \<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>x \<in> s \<inter> Vf w. f x < e) \<and> (\<forall>x \<in> s \<inter> B. f x > 1 - e))"
    by metis
  then have open_Vf: "\<And>w. w \<in> A \<Longrightarrow> open (Vf w)"
    by blast
  have tVft: "\<And>w. w \<in> A \<Longrightarrow> w \<in> Vf w"
    using Vf by blast
  then have setsum_max_0: "A \<subseteq> (\<Union>x \<in> A. Vf x)"
    by blast
  have com_A: "compact A" using A
    by (metis compact compact_Int_closed inf.absorb_iff2)
  obtain subA where subA: "subA \<subseteq> A" "finite subA" "A \<subseteq> (\<Union>x \<in> subA. Vf x)"
    by (blast intro: that open_Vf compactE_image [OF com_A _ setsum_max_0])
  then have [simp]: "subA \<noteq> {}"
    using \<open>a \<in> A\<close> by auto
  then have cardp: "card subA > 0" using subA
    by (simp add: card_gt_0_iff)
  have "\<And>w. w \<in> A \<Longrightarrow> \<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>x \<in> s \<inter> Vf w. f x < e / card subA) \<and> (\<forall>x \<in> s \<inter> B. f x > 1 - e / card subA)"
    using Vf e cardp by simp
  then obtain ff where ff:
         "\<And>w. w \<in> A \<Longrightarrow> ff w \<in> R \<and> ff w ` s \<subseteq> {0..1} \<and>
                         (\<forall>x \<in> s \<inter> Vf w. ff w x < e / card subA) \<and> (\<forall>x \<in> s \<inter> B. ff w x > 1 - e / card subA)"
    by metis
  define pff where [abs_def]: "pff x = (\<Prod>w \<in> subA. ff w x)" for x
  have pffR: "pff \<in> R"
    unfolding pff_def using subA ff by (auto simp: intro: setprod)
  moreover
  have pff01: "pff x \<in> {0..1}" if t: "x \<in> s" for x
  proof -
    have "0 \<le> pff x"
      using subA cardp t
      apply (simp add: pff_def divide_simps setsum_nonneg)
      apply (rule Groups_Big.linordered_semidom_class.setprod_nonneg)
      using ff by fastforce
    moreover have "pff x \<le> 1"
      using subA cardp t
      apply (simp add: pff_def divide_simps setsum_nonneg)
      apply (rule setprod_mono [where g = "\<lambda>x. 1", simplified])
      using ff by fastforce
    ultimately show ?thesis
      by auto
  qed
  moreover
  { fix v x
    assume v: "v \<in> subA" and x: "x \<in> Vf v" "x \<in> s"
    from subA v have "pff x = ff v x * (\<Prod>w \<in> subA - {v}. ff w x)"
      unfolding pff_def  by (metis setprod.remove)
    also have "... \<le> ff v x * 1"
      apply (rule Rings.ordered_semiring_class.mult_left_mono)
      apply (rule setprod_mono [where g = "\<lambda>x. 1", simplified])
      using ff [THEN conjunct2, THEN conjunct1] v subA x
      apply auto
      apply (meson atLeastAtMost_iff contra_subsetD imageI)
      apply (meson atLeastAtMost_iff contra_subsetD image_eqI)
      using atLeastAtMost_iff by blast
    also have "... < e / card subA"
      using ff [THEN conjunct2, THEN conjunct2, THEN conjunct1] v subA x
      by auto
    also have "... \<le> e"
      using cardp e by (simp add: divide_simps)
    finally have "pff x < e" .
  }
  then have "\<And>x. x \<in> A \<Longrightarrow> pff x < e"
    using A Vf subA by (metis UN_E contra_subsetD)
  moreover
  { fix x
    assume x: "x \<in> B"
    then have "x \<in> s"
      using B by auto
    have "1 - e \<le> (1 - e / card subA) ^ card subA"
      using Bernoulli_inequality [of "-e / card subA" "card subA"] e cardp
      by (auto simp: field_simps)
    also have "... = (\<Prod>w \<in> subA. 1 - e / card subA)"
      by (simp add: setprod_constant subA(2))
    also have "... < pff x"
      apply (simp add: pff_def)
      apply (rule setprod_mono_strict [where f = "\<lambda>x. 1 - e / card subA", simplified])
      apply (simp_all add: subA(2))
      apply (intro ballI conjI)
      using e apply (force simp: divide_simps)
      using ff [THEN conjunct2, THEN conjunct2, THEN conjunct2] subA B x
      apply blast
      done
    finally have "1 - e < pff x" .
  }
  ultimately
  show ?thesis by blast
qed

lemma (in function_ring_on) two:
  assumes A: "closed A" "A \<subseteq> s"
      and B: "closed B" "B \<subseteq> s"
      and disj: "A \<inter> B = {}"
      and e: "0 < e" "e < 1"
    shows "\<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>x \<in> A. f x < e) \<and> (\<forall>x \<in> B. f x > 1 - e)"
proof (cases "A \<noteq> {} \<and> B \<noteq> {}")
  case True then show ?thesis
    apply (simp add: ex_in_conv [symmetric])
    using assms
    apply safe
    apply (force simp add: intro!: two_special)
    done
next
  case False with e show ?thesis
    apply simp
    apply (erule disjE)
    apply (rule_tac [2] x="\<lambda>x. 0" in bexI)
    apply (rule_tac x="\<lambda>x. 1" in bexI)
    apply (auto simp: const)
    done
qed

text\<open>The special case where @{term f} is non-negative and @{term"e<1/3"}\<close>
lemma (in function_ring_on) Stone_Weierstrass_special:
  assumes f: "continuous_on s f" and fpos: "\<And>x. x \<in> s \<Longrightarrow> f x \<ge> 0"
      and e: "0 < e" "e < 1/3"
  shows "\<exists>g \<in> R. \<forall>x\<in>s. \<bar>f x - g x\<bar> < 2*e"
proof -
  define n where "n = 1 + nat \<lceil>normf f / e\<rceil>"
  define A where "A j = {x \<in> s. f x \<le> (j - 1/3)*e}" for j :: nat
  define B where "B j = {x \<in> s. f x \<ge> (j + 1/3)*e}" for j :: nat
  have ngt: "(n-1) * e \<ge> normf f" "n\<ge>1"
    using e
    apply (simp_all add: n_def field_simps of_nat_Suc)
    by (metis real_nat_ceiling_ge mult.commute not_less pos_less_divide_eq)
  then have ge_fx: "(n-1) * e \<ge> f x" if "x \<in> s" for x
    using f normf_upper that by fastforce
  { fix j
    have A: "closed (A j)" "A j \<subseteq> s"
      apply (simp_all add: A_def Collect_restrict)
      apply (rule continuous_on_closed_Collect_le [OF f continuous_on_const])
      apply (simp add: compact compact_imp_closed)
      done
    have B: "closed (B j)" "B j \<subseteq> s"
      apply (simp_all add: B_def Collect_restrict)
      apply (rule continuous_on_closed_Collect_le [OF continuous_on_const f])
      apply (simp add: compact compact_imp_closed)
      done
    have disj: "(A j) \<inter> (B j) = {}"
      using e by (auto simp: A_def B_def field_simps)
    have "\<exists>f \<in> R. f ` s \<subseteq> {0..1} \<and> (\<forall>x \<in> A j. f x < e/n) \<and> (\<forall>x \<in> B j. f x > 1 - e/n)"
      apply (rule two)
      using e A B disj ngt
      apply simp_all
      done
  }
  then obtain xf where xfR: "\<And>j. xf j \<in> R" and xf01: "\<And>j. xf j ` s \<subseteq> {0..1}"
                   and xfA: "\<And>x j. x \<in> A j \<Longrightarrow> xf j x < e/n"
                   and xfB: "\<And>x j. x \<in> B j \<Longrightarrow> xf j x > 1 - e/n"
    by metis
  define g where [abs_def]: "g x = e * (\<Sum>i\<le>n. xf i x)" for x
  have gR: "g \<in> R"
    unfolding g_def by (fast intro: mult const setsum xfR)
  have gge0: "\<And>x. x \<in> s \<Longrightarrow> g x \<ge> 0"
    using e xf01 by (simp add: g_def zero_le_mult_iff image_subset_iff setsum_nonneg)
  have A0: "A 0 = {}"
    using fpos e by (fastforce simp: A_def)
  have An: "A n = s"
    using e ngt f normf_upper by (fastforce simp: A_def field_simps of_nat_diff)
  have Asub: "A j \<subseteq> A i" if "i\<ge>j" for i j
    using e that apply (clarsimp simp: A_def)
    apply (erule order_trans, simp)
    done
  { fix t
    assume t: "t \<in> s"
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
      using  Aj  \<open>i<j\<close>
      apply (simp add: j_def)
      using not_less_Least by blast
    have j1: "1 \<le> j"
      using A0 Aj j_def not_less_eq_eq by (fastforce simp add: j_def)
    then have Anj: "t \<notin> A (j-1)"
      using Least_le by (fastforce simp add: j_def)
    then have fj2: "(j - 4/3)*e < f t"
      using j1 t  by (simp add: A_def of_nat_diff)
    have ***: "xf i t \<le> e/n" if "i\<ge>j" for i
      using xfA [OF Ai] that by (simp add: less_eq_real_def)
    { fix i
      assume "i+2 \<le> j"
      then obtain d where "i+2+d = j"
        using le_Suc_ex that by blast
      then have "t \<in> B i"
        using Anj e ge_fx [OF t] \<open>1 \<le> n\<close> fpos [OF t] t
        apply (simp add: A_def B_def)
        apply (clarsimp simp add: field_simps of_nat_diff not_le of_nat_Suc)
        apply (rule order_trans [of _ "e * 2 + (e * (real d * 3) + e * (real i * 3))"])
        apply auto
        done
      then have "xf i t > 1 - e/n"
        by (rule xfB)
    } note **** = this
    have xf_le1: "\<And>i. xf i t \<le> 1"
      using xf01 t by force
    have "g t = e * (\<Sum>i<j. xf i t) + e * (\<Sum>i=j..n. xf i t)"
      using j1 jn e
      apply (simp add: g_def distrib_left [symmetric])
      apply (subst setsum.union_disjoint [symmetric])
      apply (auto simp: ivl_disj_un)
      done
    also have "... \<le> e*j + e * ((Suc n - j)*e/n)"
      apply (rule add_mono)
      apply (simp_all only: mult_le_cancel_left_pos e)
      apply (rule setsum_bounded_above [OF xf_le1, where A = "lessThan j", simplified])
      using setsum_bounded_above [of "{j..n}" "\<lambda>i. xf i t", OF ***]
      apply simp
      done
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
        using e
        apply simp
        apply (rule order_trans [OF _ setsum_bounded_below [OF less_imp_le [OF ****]]])
        using True
        apply (simp_all add: of_nat_Suc of_nat_diff)
        done
      also have "... \<le> g t"
        using jn e
        using e xf01 t
        apply (simp add: g_def zero_le_mult_iff image_subset_iff setsum_nonneg)
        apply (rule Groups_Big.setsum_mono2, auto)
        done
      finally show ?thesis .
    qed
    have "\<bar>f t - g t\<bar> < 2 * e"
      using fj1 fj2 gj1 gj2 by (simp add: abs_less_iff field_simps)
  }
  then show ?thesis
    by (rule_tac x=g in bexI) (auto intro: gR)
qed

text\<open>The ``unpretentious'' formulation\<close>
lemma (in function_ring_on) Stone_Weierstrass_basic:
  assumes f: "continuous_on s f" and e: "e > 0"
  shows "\<exists>g \<in> R. \<forall>x\<in>s. \<bar>f x - g x\<bar> < e"
proof -
  have "\<exists>g \<in> R. \<forall>x\<in>s. \<bar>(f x + normf f) - g x\<bar> < 2 * min (e/2) (1/4)"
    apply (rule Stone_Weierstrass_special)
    apply (rule Limits.continuous_on_add [OF f Topological_Spaces.continuous_on_const])
    using normf_upper [OF f] apply force
    apply (simp add: e, linarith)
    done
  then obtain g where "g \<in> R" "\<forall>x\<in>s. \<bar>g x - (f x + normf f)\<bar> < e"
    by force
  then show ?thesis
    apply (rule_tac x="\<lambda>x. g x - normf f" in bexI)
    apply (auto simp: algebra_simps intro: diff const)
    done
qed


theorem (in function_ring_on) Stone_Weierstrass:
  assumes f: "continuous_on s f"
  shows "\<exists>F\<in>UNIV \<rightarrow> R. LIM n sequentially. F n :> uniformly_on s f"
proof -
  { fix e::real
    assume e: "0 < e"
    then obtain N::nat where N: "0 < N" "0 < inverse N" "inverse N < e"
      by (auto simp: real_arch_inverse [of e])
    { fix n :: nat and x :: 'a and g :: "'a \<Rightarrow> real"
      assume n: "N \<le> n"  "\<forall>x\<in>s. \<bar>f x - g x\<bar> < 1 / (1 + real n)"
      assume x: "x \<in> s"
      have "\<not> real (Suc n) < inverse e"
        using \<open>N \<le> n\<close> N using less_imp_inverse_less by force
      then have "1 / (1 + real n) \<le> e"
        using e by (simp add: field_simps of_nat_Suc)
      then have "\<bar>f x - g x\<bar> < e"
        using n(2) x by auto
    } note * = this
    have "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>s. \<bar>f x - (SOME g. g \<in> R \<and> (\<forall>x\<in>s. \<bar>f x - g x\<bar> < 1 / (1 + real n))) x\<bar> < e"
      apply (rule eventually_sequentiallyI [of N])
      apply (auto intro: someI2_bex [OF Stone_Weierstrass_basic [OF f]] *)
      done
  } then
  show ?thesis
    apply (rule_tac x="\<lambda>n::nat. SOME g. g \<in> R \<and> (\<forall>x\<in>s. \<bar>f x - g x\<bar> < 1 / (1 + n))" in bexI)
    prefer 2  apply (force intro: someI2_bex [OF Stone_Weierstrass_basic [OF f]])
    unfolding uniform_limit_iff
    apply (auto simp: dist_norm abs_minus_commute)
    done
qed

text\<open>A HOL Light formulation\<close>
corollary Stone_Weierstrass_HOL:
  fixes R :: "('a::t2_space \<Rightarrow> real) set" and s :: "'a set"
  assumes "compact s"  "\<And>c. P(\<lambda>x. c::real)"
          "\<And>f. P f \<Longrightarrow> continuous_on s f"
          "\<And>f g. P(f) \<and> P(g) \<Longrightarrow> P(\<lambda>x. f x + g x)"  "\<And>f g. P(f) \<and> P(g) \<Longrightarrow> P(\<lambda>x. f x * g x)"
          "\<And>x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) \<Longrightarrow> \<exists>f. P(f) \<and> ~(f x = f y)"
          "continuous_on s f"
       "0 < e"
    shows "\<exists>g. P(g) \<and> (\<forall>x \<in> s. \<bar>f x - g x\<bar> < e)"
proof -
  interpret PR: function_ring_on "Collect P"
    apply unfold_locales
    using assms
    by auto
  show ?thesis
    using PR.Stone_Weierstrass_basic [OF \<open>continuous_on s f\<close> \<open>0 < e\<close>]
    by blast
qed


subsection \<open>Polynomial functions\<close>

inductive real_polynomial_function :: "('a::real_normed_vector \<Rightarrow> real) \<Rightarrow> bool" where
    linear: "bounded_linear f \<Longrightarrow> real_polynomial_function f"
  | const: "real_polynomial_function (\<lambda>x. c)"
  | add:   "\<lbrakk>real_polynomial_function f; real_polynomial_function g\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. f x + g x)"
  | mult:  "\<lbrakk>real_polynomial_function f; real_polynomial_function g\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. f x * g x)"

declare real_polynomial_function.intros [intro]

definition polynomial_function :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
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
  using g
  apply (auto simp: polynomial_function_def bounded_linear_def Real_Vector_Spaces.linear.scaleR  const real_polynomial_function.mult o_def)
  apply (rule mult)
  using f
  apply (auto simp: real_polynomial_function_eq)
  done

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

lemma polynomial_function_setsum [intro]:
    "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> polynomial_function (\<lambda>x. f x i)\<rbrakk> \<Longrightarrow> polynomial_function (\<lambda>x. setsum (f x) I)"
by (induct I rule: finite_induct) auto

lemma real_polynomial_function_minus [intro]:
    "real_polynomial_function f \<Longrightarrow> real_polynomial_function (\<lambda>x. - f x)"
  using polynomial_function_minus [of f]
  by (simp add: real_polynomial_function_eq)

lemma real_polynomial_function_diff [intro]:
    "\<lbrakk>real_polynomial_function f; real_polynomial_function g\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. f x - g x)"
  using polynomial_function_diff [of f]
  by (simp add: real_polynomial_function_eq)

lemma real_polynomial_function_setsum [intro]:
    "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> real_polynomial_function (\<lambda>x. f x i)\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. setsum (f x) I)"
  using polynomial_function_setsum [of I f]
  by (simp add: real_polynomial_function_eq)

lemma real_polynomial_function_power [intro]:
    "real_polynomial_function f \<Longrightarrow> real_polynomial_function (\<lambda>x. f x ^ n)"
  by (induct n) (simp_all add: const mult)

lemma real_polynomial_function_compose [intro]:
  assumes f: "polynomial_function f" and g: "real_polynomial_function g"
    shows "real_polynomial_function (g o f)"
  using g
  apply (induction g rule: real_polynomial_function.induct)
  using f
  apply (simp_all add: polynomial_function_def o_def const add mult)
  done

lemma polynomial_function_compose [intro]:
  assumes f: "polynomial_function f" and g: "polynomial_function g"
    shows "polynomial_function (g o f)"
  using g real_polynomial_function_compose [OF f]
  by (auto simp: polynomial_function_def o_def)

lemma setsum_max_0:
  fixes x::real (*in fact "'a::comm_ring_1"*)
  shows "(\<Sum>i = 0..max m n. x^i * (if i \<le> m then a i else 0)) = (\<Sum>i = 0..m. x^i * a i)"
proof -
  have "(\<Sum>i = 0..max m n. x^i * (if i \<le> m then a i else 0)) = (\<Sum>i = 0..max m n. (if i \<le> m then x^i * a i else 0))"
    by (auto simp: algebra_simps intro: setsum.cong)
  also have "... = (\<Sum>i = 0..m. (if i \<le> m then x^i * a i else 0))"
    by (rule setsum.mono_neutral_right) auto
  also have "... = (\<Sum>i = 0..m. x^i * a i)"
    by (auto simp: algebra_simps intro: setsum.cong)
  finally show ?thesis .
qed

lemma real_polynomial_function_imp_setsum:
  assumes "real_polynomial_function f"
    shows "\<exists>a n::nat. f = (\<lambda>x. \<Sum>i=0..n. a i * x ^ i)"
using assms
proof (induct f)
  case (linear f)
  then show ?case
    apply (clarsimp simp add: real_bounded_linear)
    apply (rule_tac x="\<lambda>i. if i=0 then 0 else c" in exI)
    apply (rule_tac x=1 in exI)
    apply (simp add: mult_ac)
    done
next
  case (const c)
  show ?case
    apply (rule_tac x="\<lambda>i. c" in exI)
    apply (rule_tac x=0 in exI)
    apply (auto simp: mult_ac of_nat_Suc)
    done
  case (add f1 f2)
  then obtain a1 n1 a2 n2 where
    "f1 = (\<lambda>x. \<Sum>i = 0..n1. a1 i * x ^ i)" "f2 = (\<lambda>x. \<Sum>i = 0..n2. a2 i * x ^ i)"
    by auto
  then show ?case
    apply (rule_tac x="\<lambda>i. (if i \<le> n1 then a1 i else 0) + (if i \<le> n2 then a2 i else 0)" in exI)
    apply (rule_tac x="max n1 n2" in exI)
    using setsum_max_0 [where m=n1 and n=n2] setsum_max_0 [where m=n2 and n=n1]
    apply (simp add: setsum.distrib algebra_simps max.commute)
    done
  case (mult f1 f2)
  then obtain a1 n1 a2 n2 where
    "f1 = (\<lambda>x. \<Sum>i = 0..n1. a1 i * x ^ i)" "f2 = (\<lambda>x. \<Sum>i = 0..n2. a2 i * x ^ i)"
    by auto
  then obtain b1 b2 where
    "f1 = (\<lambda>x. \<Sum>i = 0..n1. b1 i * x ^ i)" "f2 = (\<lambda>x. \<Sum>i = 0..n2. b2 i * x ^ i)"
    "b1 = (\<lambda>i. if i\<le>n1 then a1 i else 0)" "b2 = (\<lambda>i. if i\<le>n2 then a2 i else 0)"
    by auto
  then show ?case
    apply (rule_tac x="\<lambda>i. \<Sum>k\<le>i. b1 k * b2 (i - k)" in exI)
    apply (rule_tac x="n1+n2" in exI)
    using polynomial_product [of n1 b1 n2 b2]
    apply (simp add: Set_Interval.atLeast0AtMost)
    done
qed

lemma real_polynomial_function_iff_setsum:
     "real_polynomial_function f \<longleftrightarrow> (\<exists>a n::nat. f = (\<lambda>x. \<Sum>i=0..n. a i * x ^ i))"
  apply (rule iffI)
  apply (erule real_polynomial_function_imp_setsum)
  apply (auto simp: linear mult const real_polynomial_function_power real_polynomial_function_setsum)
  done

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
    apply (rule real_polynomial_function_compose [OF _  linear [OF h]])
    using rp
    apply (auto simp: real_polynomial_function_eq polynomial_function_mult)
    done
  then show "real_polynomial_function (h \<circ> f)"
    by (simp add: euclidean_representation_setsum_fun)
qed

subsection \<open>Stone-Weierstrass theorem for polynomial functions\<close>

text\<open>First, we need to show that they are continous, differentiable and separable.\<close>

lemma continuous_real_polymonial_function:
  assumes "real_polynomial_function f"
    shows "continuous (at x) f"
using assms
by (induct f) (auto simp: linear_continuous_at)

lemma continuous_polymonial_function:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "polynomial_function f"
    shows "continuous (at x) f"
  apply (rule euclidean_isCont)
  using assms apply (simp add: polynomial_function_iff_Basis_inner)
  apply (force dest: continuous_real_polymonial_function intro: isCont_scaleR)
  done

lemma continuous_on_polymonial_function:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "polynomial_function f"
    shows "continuous_on s f"
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
    apply (rule_tac x="\<lambda>x. p1 x + p2 x" in exI)
    apply (auto intro!: derivative_eq_intros)
    done
  case (mult f1 f2)
  then obtain p1 p2 where
    "real_polynomial_function p1" "\<And>x. (f1 has_real_derivative p1 x) (at x)"
    "real_polynomial_function p2" "\<And>x. (f2 has_real_derivative p2 x) (at x)"
    by auto
  then show ?case
    using mult
    apply (rule_tac x="\<lambda>x. f1 x * p2 x + f2 x * p1 x" in exI)
    apply (auto intro!: derivative_eq_intros)
    done
qed

lemma has_vector_derivative_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "polynomial_function p"
    shows "\<exists>p'. polynomial_function p' \<and>
                 (\<forall>x. (p has_vector_derivative (p' x)) (at x))"
proof -
  { fix b :: 'a
    assume "b \<in> Basis"
    then
    obtain p' where p': "real_polynomial_function p'" and pd: "\<And>x. ((\<lambda>x. p x \<bullet> b) has_real_derivative p' x) (at x)"
      using assms [unfolded polynomial_function_iff_Basis_inner, rule_format]  \<open>b \<in> Basis\<close>
      has_real_derivative_polynomial_function
      by blast
    have "\<exists>q. polynomial_function q \<and> (\<forall>x. ((\<lambda>u. (p u \<bullet> b) *\<^sub>R b) has_vector_derivative q x) (at x))"
      apply (rule_tac x="\<lambda>x. p' x *\<^sub>R b" in exI)
      using \<open>b \<in> Basis\<close> p'
      apply (simp add: polynomial_function_iff_Basis_inner inner_Basis)
      apply (auto intro: derivative_eq_intros pd)
      done
  }
  then obtain qf where qf:
      "\<And>b. b \<in> Basis \<Longrightarrow> polynomial_function (qf b)"
      "\<And>b x. b \<in> Basis \<Longrightarrow> ((\<lambda>u. (p u \<bullet> b) *\<^sub>R b) has_vector_derivative qf b x) (at x)"
    by metis
  show ?thesis
    apply (subst euclidean_representation_setsum_fun [of p, symmetric])
    apply (rule_tac x="\<lambda>x. \<Sum>b\<in>Basis. qf b x" in exI)
    apply (auto intro: has_vector_derivative_setsum qf)
    done
qed

lemma real_polynomial_function_separable:
  fixes x :: "'a::euclidean_space"
  assumes "x \<noteq> y" shows "\<exists>f. real_polynomial_function f \<and> f x \<noteq> f y"
proof -
  have "real_polynomial_function (\<lambda>u. \<Sum>b\<in>Basis. (inner (x-u) b)^2)"
    apply (rule real_polynomial_function_setsum)
    apply (auto simp: algebra_simps real_polynomial_function_power real_polynomial_function_diff
                 const linear bounded_linear_inner_left)
    done
  then show ?thesis
    apply (intro exI conjI, assumption)
    using assms
    apply (force simp add: euclidean_eq_iff [of x y] setsum_nonneg_eq_0_iff algebra_simps)
    done
qed

lemma Stone_Weierstrass_real_polynomial_function:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "compact s" "continuous_on s f" "0 < e"
    shows "\<exists>g. real_polynomial_function g \<and> (\<forall>x \<in> s. \<bar>f x - g x\<bar> < e)"
proof -
  interpret PR: function_ring_on "Collect real_polynomial_function"
    apply unfold_locales
    using assms continuous_on_polymonial_function real_polynomial_function_eq
    apply (auto intro: real_polynomial_function_separable)
    done
  show ?thesis
    using PR.Stone_Weierstrass_basic [OF \<open>continuous_on s f\<close> \<open>0 < e\<close>]
    by blast
qed

lemma Stone_Weierstrass_polynomial_function:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes s: "compact s"
      and f: "continuous_on s f"
      and e: "0 < e"
    shows "\<exists>g. polynomial_function g \<and> (\<forall>x \<in> s. norm(f x - g x) < e)"
proof -
  { fix b :: 'b
    assume "b \<in> Basis"
    have "\<exists>p. real_polynomial_function p \<and> (\<forall>x \<in> s. \<bar>f x \<bullet> b - p x\<bar> < e / DIM('b))"
      apply (rule exE [OF Stone_Weierstrass_real_polynomial_function [OF s _, of "\<lambda>x. f x \<bullet> b" "e / card Basis"]])
      using e f
      apply (auto simp: Euclidean_Space.DIM_positive intro: continuous_intros)
      done
  }
  then obtain pf where pf:
      "\<And>b. b \<in> Basis \<Longrightarrow> real_polynomial_function (pf b) \<and> (\<forall>x \<in> s. \<bar>f x \<bullet> b - pf b x\<bar> < e / DIM('b))"
      apply (rule bchoice [rule_format, THEN exE])
      apply assumption
      apply (force simp add: intro: that)
      done
  have "polynomial_function (\<lambda>x. \<Sum>b\<in>Basis. pf b x *\<^sub>R b)"
    using pf
    by (simp add: polynomial_function_setsum polynomial_function_mult real_polynomial_function_eq)
  moreover
  { fix x
    assume "x \<in> s"
    have "norm (\<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b - pf b x *\<^sub>R b) \<le> (\<Sum>b\<in>Basis. norm ((f x \<bullet> b) *\<^sub>R b - pf b x *\<^sub>R b))"
      by (rule norm_setsum)
    also have "... < of_nat DIM('b) * (e / DIM('b))"
      apply (rule setsum_bounded_above_strict)
      apply (simp add: Real_Vector_Spaces.scaleR_diff_left [symmetric] pf \<open>x \<in> s\<close>)
      apply (rule DIM_positive)
      done
    also have "... = e"
      using DIM_positive by (simp add: field_simps)
    finally have "norm (\<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b - pf b x *\<^sub>R b) < e" .
  }
  ultimately
  show ?thesis
    apply (subst euclidean_representation_setsum_fun [of f, symmetric])
    apply (rule_tac x="\<lambda>x. \<Sum>b\<in>Basis. pf b x *\<^sub>R b" in exI)
    apply (auto simp: setsum_subtractf [symmetric])
    done
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
    shows "\<exists>p. polynomial_function p \<and>
                pathstart p = pathstart g \<and>
                pathfinish p = pathfinish g \<and>
                (\<forall>t \<in> {0..1}. norm(p t - g t) < e)"
proof -
  obtain q where poq: "polynomial_function q" and noq: "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (g x - q x) < e/4"
    using Stone_Weierstrass_polynomial_function [of "{0..1}" g "e/4"] assms
    by (auto simp: path_def)
  have pf: "polynomial_function (\<lambda>t. q t + (g 0 - q 0) + t *\<^sub>R (g 1 - q 1 - (g 0 - q 0)))"
    by (force simp add: poq)
  have *: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (((q t - g t) + (g 0 - q 0)) + (t *\<^sub>R (g 1 - q 1) + t *\<^sub>R (q 0 - g 0))) < (e/4 + e/4) + (e/4+e/4)"
    apply (intro Real_Vector_Spaces.norm_add_less)
    using noq
    apply (auto simp: norm_minus_commute intro: le_less_trans [OF mult_left_le_one_le noq] simp del: less_divide_eq_numeral1)
    done
  show ?thesis
    apply (intro exI conjI)
    apply (rule pf)
    using *
    apply (auto simp add: pathstart_def pathfinish_def algebra_simps)
    done
qed

lemma connected_open_polynomial_connected:
  fixes s :: "'a::euclidean_space set"
  assumes s: "open s" "connected s"
      and "x \<in> s" "y \<in> s"
    shows "\<exists>g. polynomial_function g \<and> path_image g \<subseteq> s \<and>
               pathstart g = x \<and> pathfinish g = y"
proof -
  have "path_connected s" using assms
    by (simp add: connected_open_path_connected)
  with \<open>x \<in> s\<close> \<open>y \<in> s\<close> obtain p where p: "path p" "path_image p \<subseteq> s" "pathstart p = x" "pathfinish p = y"
    by (force simp: path_connected_def)
  have "\<exists>e. 0 < e \<and> (\<forall>x \<in> path_image p. ball x e \<subseteq> s)"
  proof (cases "s = UNIV")
    case True then show ?thesis
      by (simp add: gt_ex)
  next
    case False
    then have "- s \<noteq> {}" by blast
    then show ?thesis
      apply (rule_tac x="setdist (path_image p) (-s)" in exI)
      using s p
      apply (simp add: setdist_gt_0_compact_closed compact_path_image open_closed)
      using setdist_le_dist [of _ "path_image p" _ "-s"]
      by fastforce
  qed
  then obtain e where "0 < e"and eb: "\<And>x. x \<in> path_image p \<Longrightarrow> ball x e \<subseteq> s"
    by auto
  show ?thesis
    using path_approx_polynomial_function [OF \<open>path p\<close> \<open>0 < e\<close>]
    apply clarify
    apply (intro exI conjI, assumption)
    using p
    apply (fastforce simp add: dist_norm path_image_def norm_minus_commute intro: eb [THEN subsetD])+
    done
qed

hide_fact linear add mult const

end
