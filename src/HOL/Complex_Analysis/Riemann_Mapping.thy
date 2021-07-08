(*  Title:      HOL/Analysis/Riemann_Mapping.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Moebius functions, Equivalents of Simply Connected Sets, Riemann Mapping Theorem\<close>

theory Riemann_Mapping
imports Great_Picard
begin

subsection\<open>Moebius functions are biholomorphisms of the unit disc\<close>

definition\<^marker>\<open>tag important\<close> Moebius_function :: "[real,complex,complex] \<Rightarrow> complex" where
  "Moebius_function \<equiv> \<lambda>t w z. exp(\<i> * of_real t) * (z - w) / (1 - cnj w * z)"

lemma Moebius_function_simple:
   "Moebius_function 0 w z = (z - w) / (1 - cnj w * z)"
  by (simp add: Moebius_function_def)

lemma Moebius_function_eq_zero:
   "Moebius_function t w w = 0"
  by (simp add: Moebius_function_def)

lemma Moebius_function_of_zero:
   "Moebius_function t w 0 = - exp(\<i> * of_real t) * w"
  by (simp add: Moebius_function_def)

lemma Moebius_function_norm_lt_1:
  assumes w1: "norm w < 1" and z1: "norm z < 1"
  shows "norm (Moebius_function t w z) < 1"
proof -
  have "1 - cnj w * z \<noteq> 0"
    by (metis complex_cnj_cnj complex_mod_sqrt_Re_mult_cnj mult.commute mult_less_cancel_right1 norm_ge_zero norm_mult norm_one order.asym right_minus_eq w1 z1)
  then have VV: "1 - w * cnj z \<noteq> 0"
    by (metis complex_cnj_cnj complex_cnj_mult complex_cnj_one right_minus_eq)
  then have "1 - norm (Moebius_function t w z) ^ 2 =
         ((1 - norm w ^ 2) / (norm (1 - cnj w * z) ^ 2)) * (1 - norm z ^ 2)"
    apply (cases w)
    apply (cases z)
    apply (simp add: Moebius_function_def divide_simps norm_divide norm_mult)
    apply (simp add: complex_norm complex_diff complex_mult one_complex.code complex_cnj)
    apply (auto simp: algebra_simps power2_eq_square)
    done
  then have "1 - (cmod (Moebius_function t w z))\<^sup>2 = (1 - cmod (w * w)) / (cmod (1 - cnj w * z))\<^sup>2 * (1 - cmod (z * z))"
    by (simp add: norm_mult power2_eq_square)
  moreover have "0 < 1 - cmod (z * z)"
    by (metis (no_types) z1 diff_gt_0_iff_gt mult.left_neutral norm_mult_less)
  ultimately have "0 < 1 - norm (Moebius_function t w z) ^ 2"
    using \<open>1 - cnj w * z \<noteq> 0\<close> w1 norm_mult_less by fastforce
  then show ?thesis
    using linorder_not_less by fastforce
qed

lemma Moebius_function_holomorphic:
  assumes "norm w < 1"
  shows "Moebius_function t w holomorphic_on ball 0 1"
proof -
  have *: "1 - z * w \<noteq> 0" if "norm z < 1" for z
  proof -
    have "norm (1::complex) \<noteq> norm (z * w)"
      using assms that norm_mult_less by fastforce
    then show ?thesis by auto
  qed
  show ?thesis
  apply (simp add: Moebius_function_def)
  apply (intro holomorphic_intros)
  using assms *
  by (metis complex_cnj_cnj complex_cnj_mult complex_cnj_one complex_mod_cnj mem_ball_0 mult.commute right_minus_eq)
qed

lemma Moebius_function_compose:
  assumes meq: "-w1 = w2" and "norm w1 < 1" "norm z < 1"
  shows "Moebius_function 0 w1 (Moebius_function 0 w2 z) = z"
proof -
  have "norm w2 < 1"
    using assms by auto
  then have "-w1 = z" if "cnj w2 * z = 1"
    by (metis assms(3) complex_mod_cnj less_irrefl mult.right_neutral norm_mult_less norm_one that)
  moreover have "z=0" if "1 - cnj w2 * z = cnj w1 * (z - w2)"
  proof -
    have "w2 * cnj w2 = 1"
      using that meq by (auto simp: algebra_simps)
    then show "z = 0"
      by (metis (no_types) \<open>cmod w2 < 1\<close> complex_mod_cnj less_irrefl mult.right_neutral norm_mult_less norm_one)
  qed
  moreover have "z - w2 - w1 * (1 - cnj w2 * z) = z * (1 - cnj w2 * z - cnj w1 * (z - w2))"
    using meq by (fastforce simp: algebra_simps)
  ultimately
  show ?thesis
    by (simp add: Moebius_function_def divide_simps norm_divide norm_mult)
qed

lemma ball_biholomorphism_exists:
  assumes "a \<in> ball 0 1"
  obtains f g where "f a = 0"
                "f holomorphic_on ball 0 1" "f ` ball 0 1 \<subseteq> ball 0 1"
                "g holomorphic_on ball 0 1" "g ` ball 0 1 \<subseteq> ball 0 1"
                "\<And>z. z \<in> ball 0 1 \<Longrightarrow> f (g z) = z"
                "\<And>z. z \<in> ball 0 1 \<Longrightarrow> g (f z) = z"
proof
  show "Moebius_function 0 a holomorphic_on ball 0 1"  "Moebius_function 0 (-a) holomorphic_on ball 0 1"
    using Moebius_function_holomorphic assms mem_ball_0 by auto
  show "Moebius_function 0 a a = 0"
    by (simp add: Moebius_function_eq_zero)
  show "Moebius_function 0 a ` ball 0 1 \<subseteq> ball 0 1"
       "Moebius_function 0 (- a) ` ball 0 1 \<subseteq> ball 0 1"
    using Moebius_function_norm_lt_1 assms by auto
  show "Moebius_function 0 a (Moebius_function 0 (- a) z) = z"
       "Moebius_function 0 (- a) (Moebius_function 0 a z) = z" if "z \<in> ball 0 1" for z
    using Moebius_function_compose assms that by auto
qed


subsection\<open>A big chain of equivalents of simple connectedness for an open set\<close>

lemma biholomorphic_to_disc_aux:
  assumes "open S" "connected S" "0 \<in> S" and S01: "S \<subseteq> ball 0 1"
      and prev: "\<And>f. \<lbrakk>f holomorphic_on S; \<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0; inj_on f S\<rbrakk>
               \<Longrightarrow> \<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
  shows "\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
               (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
               (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z)"
proof -
  define F where "F \<equiv> {h. h holomorphic_on S \<and> h ` S \<subseteq> ball 0 1 \<and> h 0 = 0 \<and> inj_on h S}"
  have idF: "id \<in> F"
    using S01 by (auto simp: F_def)
  then have "F \<noteq> {}"
    by blast
  have imF_ne: "((\<lambda>h. norm(deriv h 0)) ` F) \<noteq> {}"
    using idF by auto
  have holF: "\<And>h. h \<in> F \<Longrightarrow> h holomorphic_on S"
    by (auto simp: F_def)
  obtain f where "f \<in> F" and normf: "\<And>h. h \<in> F \<Longrightarrow> norm(deriv h 0) \<le> norm(deriv f 0)"
  proof -
    obtain r where "r > 0" and r: "ball 0 r \<subseteq> S"
      using \<open>open S\<close> \<open>0 \<in> S\<close> openE by auto
    have bdd: "bdd_above ((\<lambda>h. norm(deriv h 0)) ` F)"
    proof (intro bdd_aboveI exI ballI, clarify)
      show "norm (deriv f 0) \<le> 1 / r" if "f \<in> F" for f
      proof -
        have r01: "(*) (complex_of_real r) ` ball 0 1 \<subseteq> S"
          using that \<open>r > 0\<close> by (auto simp: norm_mult r [THEN subsetD])
        then have "f holomorphic_on (*) (complex_of_real r) ` ball 0 1"
          using holomorphic_on_subset [OF holF] by (simp add: that)
        then have holf: "f \<circ> (\<lambda>z. (r * z)) holomorphic_on (ball 0 1)"
          by (intro holomorphic_intros holomorphic_on_compose)
        have f0: "(f \<circ> (*) (complex_of_real r)) 0 = 0"
          using F_def that by auto
        have "f ` S \<subseteq> ball 0 1"
          using F_def that by blast
        with r01 have fr1: "\<And>z. norm z < 1 \<Longrightarrow> norm ((f \<circ> (*)(of_real r))z) < 1"
          by force
        have *: "((\<lambda>w. f (r * w)) has_field_derivative deriv f (r * z) * r) (at z)"
          if "z \<in> ball 0 1" for z::complex
        proof (rule DERIV_chain' [where g=f])
          show "(f has_field_derivative deriv f (of_real r * z)) (at (of_real r * z))"
            apply (rule holomorphic_derivI [OF holF \<open>open S\<close>])
             apply (rule \<open>f \<in> F\<close>)
            by (meson imageI r01 subset_iff that)
        qed simp
        have df0: "((\<lambda>w. f (r * w)) has_field_derivative deriv f 0 * r) (at 0)"
          using * [of 0] by simp
        have deq: "deriv (\<lambda>x. f (complex_of_real r * x)) 0 = deriv f 0 * complex_of_real r"
          using DERIV_imp_deriv df0 by blast
        have "norm (deriv (f \<circ> (*) (complex_of_real r)) 0) \<le> 1"
          by (auto intro: Schwarz_Lemma [OF holf f0 fr1, of 0])
        with \<open>r > 0\<close> show ?thesis
          by (simp add: deq norm_mult divide_simps o_def)
      qed
    qed
    define l where "l \<equiv> SUP h\<in>F. norm (deriv h 0)"
    have eql: "norm (deriv f 0) = l" if le: "l \<le> norm (deriv f 0)" and "f \<in> F" for f
      apply (rule order_antisym [OF _ le])
      using \<open>f \<in> F\<close> bdd cSUP_upper by (fastforce simp: l_def)
    obtain \<F> where \<F>in: "\<And>n. \<F> n \<in> F" and \<F>lim: "(\<lambda>n. norm (deriv (\<F> n) 0)) \<longlonglongrightarrow> l"
    proof -
      have "\<exists>f. f \<in> F \<and> \<bar>norm (deriv f 0) - l\<bar> < 1 / (Suc n)" for n
      proof -
        obtain f where "f \<in> F" and f: "l < norm (deriv f 0) + 1/(Suc n)"
          using cSup_least [OF imF_ne, of "l - 1/(Suc n)"] by (fastforce simp add: l_def)
        then have "\<bar>norm (deriv f 0) - l\<bar> < 1 / (Suc n)"
          by (fastforce simp add: abs_if not_less eql)
        with \<open>f \<in> F\<close> show ?thesis
          by blast
      qed
      then obtain \<F> where fF: "\<And>n. (\<F> n) \<in> F"
        and fless:  "\<And>n. \<bar>norm (deriv (\<F> n) 0) - l\<bar> < 1 / (Suc n)"
        by metis
      have "(\<lambda>n. norm (deriv (\<F> n) 0)) \<longlonglongrightarrow> l"
      proof (rule metric_LIMSEQ_I)
        fix e::real
        assume "e > 0"
        then obtain N::nat where N: "e > 1/(Suc N)"
          using nat_approx_posE by blast
        show "\<exists>N. \<forall>n\<ge>N. dist (norm (deriv (\<F> n) 0)) l < e"
        proof (intro exI allI impI)
          fix n assume "N \<le> n"
          have "dist (norm (deriv (\<F> n) 0)) l < 1 / (Suc n)"
            using fless by (simp add: dist_norm)
          also have "... < e"
            using N \<open>N \<le> n\<close> inverse_of_nat_le le_less_trans by blast
          finally show "dist (norm (deriv (\<F> n) 0)) l < e" .
        qed
      qed
      with fF show ?thesis
        using that by blast
    qed
    have "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>B. \<forall>h\<in>F. \<forall>z\<in>K. norm (h z) \<le> B"
      by (rule_tac x=1 in exI) (force simp: F_def)
    moreover have "range \<F> \<subseteq> F"
      using \<open>\<And>n. \<F> n \<in> F\<close> by blast
    ultimately obtain f and r :: "nat \<Rightarrow> nat"
      where holf: "f holomorphic_on S" and r: "strict_mono r"
        and limf: "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>n. \<F> (r n) x) \<longlonglongrightarrow> f x"
        and ulimf: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K (\<F> \<circ> r) f sequentially"
      using Montel [of S F \<F>, OF \<open>open S\<close> holF] by auto+
    have der: "\<And>n x. x \<in> S \<Longrightarrow> ((\<F> \<circ> r) n has_field_derivative ((\<lambda>n. deriv (\<F> n)) \<circ> r) n x) (at x)"
      using \<open>\<And>n. \<F> n \<in> F\<close> \<open>open S\<close> holF holomorphic_derivI by fastforce
    have ulim: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d>0. cball x d \<subseteq> S \<and> uniform_limit (cball x d) (\<F> \<circ> r) f sequentially"
      by (meson ulimf \<open>open S\<close> compact_cball open_contains_cball)
    obtain f' :: "complex\<Rightarrow>complex" where f': "(f has_field_derivative f' 0) (at 0)"
      and tof'0: "(\<lambda>n. ((\<lambda>n. deriv (\<F> n)) \<circ> r) n 0) \<longlonglongrightarrow> f' 0"
      using has_complex_derivative_uniform_sequence [OF \<open>open S\<close> der ulim] \<open>0 \<in> S\<close> by metis
    then have derf0: "deriv f 0 = f' 0"
      by (simp add: DERIV_imp_deriv)
    have "f field_differentiable (at 0)"
      using field_differentiable_def f' by blast
    have "(\<lambda>x.  (norm (deriv (\<F> (r x)) 0))) \<longlonglongrightarrow> norm (deriv f 0)"
      using isCont_tendsto_compose [OF continuous_norm [OF continuous_ident] tof'0] derf0 by auto
    with LIMSEQ_subseq_LIMSEQ [OF \<F>lim r] have no_df0: "norm(deriv f 0) = l"
      by (force simp: o_def intro: tendsto_unique)
    have nonconstf: "\<not> f constant_on S"
    proof -
      have False if "\<And>x. x \<in> S \<Longrightarrow> f x = c" for c
      proof -
        have "deriv f 0 = 0"
          by (metis that \<open>open S\<close> \<open>0 \<in> S\<close> DERIV_imp_deriv [OF has_field_derivative_transform_within_open [OF DERIV_const]])
        with no_df0 have "l = 0"
          by auto
        with eql [OF _ idF] show False by auto
      qed
      then show ?thesis
        by (meson constant_on_def)
    qed
    show ?thesis
    proof
      show "f \<in> F"
        unfolding F_def
      proof (intro CollectI conjI holf)
        have "norm(f z) \<le> 1" if "z \<in> S" for z
        proof (intro Lim_norm_ubound [OF _ limf] always_eventually allI that)
          fix n
          have "\<F> (r n) \<in> F"
            by (simp add: \<F>in)
          then show "norm (\<F> (r n) z) \<le> 1"
            using that by (auto simp: F_def)
        qed simp
        then have fless1: "norm(f z) < 1" if "z \<in> S" for z
          using maximum_modulus_principle [OF holf \<open>open S\<close> \<open>connected S\<close> \<open>open S\<close>] nonconstf that
          by fastforce
        then show "f ` S \<subseteq> ball 0 1"
          by auto
        have "(\<lambda>n. \<F> (r n) 0) \<longlonglongrightarrow> 0"
          using \<F>in by (auto simp: F_def)
        then show "f 0 = 0"
          using tendsto_unique [OF _ limf ] \<open>0 \<in> S\<close> trivial_limit_sequentially by blast
        show "inj_on f S"
        proof (rule Hurwitz_injective [OF \<open>open S\<close> \<open>connected S\<close> _ holf])
          show "\<And>n. (\<F> \<circ> r) n holomorphic_on S"
            by (simp add: \<F>in holF)
          show "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K(\<F> \<circ> r) f sequentially"
            by (metis ulimf)
          show "\<not> f constant_on S"
            using nonconstf by auto
          show "\<And>n. inj_on ((\<F> \<circ> r) n) S"
            using \<F>in by (auto simp: F_def)
        qed
      qed
      show "\<And>h. h \<in> F \<Longrightarrow> norm (deriv h 0) \<le> norm (deriv f 0)"
        by (metis eql le_cases no_df0)
    qed
  qed
  have holf: "f holomorphic_on S" and injf: "inj_on f S" and f01: "f ` S \<subseteq> ball 0 1"
    using \<open>f \<in> F\<close> by (auto simp: F_def)
  obtain g where holg: "g holomorphic_on (f ` S)"
             and derg: "\<And>z. z \<in> S \<Longrightarrow> deriv f z * deriv g (f z) = 1"
             and gf: "\<And>z. z \<in> S \<Longrightarrow> g(f z) = z"
    using holomorphic_has_inverse [OF holf \<open>open S\<close> injf] by metis
  have "ball 0 1 \<subseteq> f ` S"
  proof
    fix a::complex
    assume a: "a \<in> ball 0 1"
    have False if "\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> a"
    proof -
      obtain h k where "h a = 0"
        and holh: "h holomorphic_on ball 0 1" and h01: "h ` ball 0 1 \<subseteq> ball 0 1"
        and holk: "k holomorphic_on ball 0 1" and k01: "k ` ball 0 1 \<subseteq> ball 0 1"
        and hk: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> h (k z) = z"
        and kh: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> k (h z) = z"
        using ball_biholomorphism_exists [OF a] by blast
      have nf1: "\<And>z. z \<in> S \<Longrightarrow> norm(f z) < 1"
        using \<open>f \<in> F\<close> by (auto simp: F_def)
      have 1: "h \<circ> f holomorphic_on S"
        using F_def \<open>f \<in> F\<close> holh holomorphic_on_compose holomorphic_on_subset by blast
      have 2: "\<And>z. z \<in> S \<Longrightarrow> (h \<circ> f) z \<noteq> 0"
        by (metis \<open>h a = 0\<close> a comp_eq_dest_lhs nf1 kh mem_ball_0 that)
      have 3: "inj_on (h \<circ> f) S"
        by (metis (no_types, lifting) F_def \<open>f \<in> F\<close> comp_inj_on inj_on_inverseI injf kh mem_Collect_eq subset_inj_on)
      obtain \<psi> where hol\<psi>: "\<psi> holomorphic_on ((h \<circ> f) ` S)"
        and \<psi>2: "\<And>z. z \<in> S  \<Longrightarrow> \<psi>(h (f z)) ^ 2 = h(f z)"
      proof (rule exE [OF prev [OF 1 2 3]], safe)
        fix \<theta>
        assume hol\<theta>: "\<theta> holomorphic_on S" and \<theta>2: "(\<forall>z\<in>S. (h \<circ> f) z = (\<theta> z)\<^sup>2)"
        show thesis
        proof
          show "(\<theta> \<circ> g \<circ> k) holomorphic_on (h \<circ> f) ` S"
          proof (intro holomorphic_on_compose)
            show "k holomorphic_on (h \<circ> f) ` S"
              apply (rule holomorphic_on_subset [OF holk])
              using f01 h01 by force
            show "g holomorphic_on k ` (h \<circ> f) ` S"
              apply (rule holomorphic_on_subset [OF holg])
              by (auto simp: kh nf1)
            show "\<theta> holomorphic_on g ` k ` (h \<circ> f) ` S"
              apply (rule holomorphic_on_subset [OF hol\<theta>])
              by (auto simp: gf kh nf1)
          qed
          show "((\<theta> \<circ> g \<circ> k) (h (f z)))\<^sup>2 = h (f z)" if "z \<in> S" for z
          proof -
            have "f z \<in> ball 0 1"
              by (simp add: nf1 that)
            then have "(\<theta> (g (k (h (f z)))))\<^sup>2 = (\<theta> (g (f z)))\<^sup>2"
              by (metis kh)
            also have "... = h (f z)"
              using \<theta>2 gf that by auto
            finally show ?thesis
              by (simp add: o_def)
          qed
        qed
      qed
      have norm\<psi>1: "norm(\<psi> (h (f z))) < 1" if "z \<in> S" for z
      proof -
        have "norm (\<psi> (h (f z)) ^ 2) < 1"
          by (metis (no_types) that DIM_complex \<psi>2 h01 image_subset_iff mem_ball_0 nf1)
        then show ?thesis
          by (metis le_less_trans mult_less_cancel_left2 norm_ge_zero norm_power not_le power2_eq_square)
      qed
      then have \<psi>01: "\<psi> (h (f 0)) \<in> ball 0 1"
        by (simp add: \<open>0 \<in> S\<close>)
      obtain p q where p0: "p (\<psi> (h (f 0))) = 0"
        and holp: "p holomorphic_on ball 0 1" and p01: "p ` ball 0 1 \<subseteq> ball 0 1"
        and holq: "q holomorphic_on ball 0 1" and q01: "q ` ball 0 1 \<subseteq> ball 0 1"
        and pq: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> p (q z) = z"
        and qp: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> q (p z) = z"
        using ball_biholomorphism_exists [OF \<psi>01] by metis
      have "p \<circ> \<psi> \<circ> h \<circ> f \<in> F"
        unfolding F_def
      proof (intro CollectI conjI holf)
        show "p \<circ> \<psi> \<circ> h \<circ> f holomorphic_on S"
        proof (intro holomorphic_on_compose holf)
          show "h holomorphic_on f ` S"
            apply (rule holomorphic_on_subset [OF holh])
            using f01 by force
          show "\<psi> holomorphic_on h ` f ` S"
            apply (rule holomorphic_on_subset [OF hol\<psi>])
            by auto
          show "p holomorphic_on \<psi> ` h ` f ` S"
            apply (rule holomorphic_on_subset [OF holp])
            by (auto simp: norm\<psi>1)
        qed
        show "(p \<circ> \<psi> \<circ> h \<circ> f) ` S \<subseteq> ball 0 1"
          apply clarsimp
          by (meson norm\<psi>1 p01 image_subset_iff mem_ball_0)
        show "(p \<circ> \<psi> \<circ> h \<circ> f) 0 = 0"
          by (simp add: \<open>p (\<psi> (h (f 0))) = 0\<close>)
        show "inj_on (p \<circ> \<psi> \<circ> h \<circ> f) S"
          unfolding inj_on_def o_def
          by (metis \<psi>2 dist_0_norm gf kh mem_ball nf1 norm\<psi>1 qp)
      qed
      then have le_norm_df0: "norm (deriv (p \<circ> \<psi> \<circ> h \<circ> f) 0) \<le> norm (deriv f 0)"
        by (rule normf)
      have 1: "k \<circ> power2 \<circ> q holomorphic_on ball 0 1"
      proof (intro holomorphic_on_compose holq)
        show "power2 holomorphic_on q ` ball 0 1"
          using holomorphic_on_subset holomorphic_on_power
          by (blast intro: holomorphic_on_ident)
        show "k holomorphic_on power2 ` q ` ball 0 1"
          apply (rule holomorphic_on_subset [OF holk])
          using q01 by (auto simp: norm_power abs_square_less_1)
      qed
      have 2: "(k \<circ> power2 \<circ> q) 0 = 0"
        using p0 F_def \<open>f \<in> F\<close> \<psi>01 \<psi>2 \<open>0 \<in> S\<close> kh qp by force
      have 3: "norm ((k \<circ> power2 \<circ> q) z) < 1" if "norm z < 1" for z
      proof -
        have "norm ((power2 \<circ> q) z) < 1"
          using that q01 by (force simp: norm_power abs_square_less_1)
        with k01 show ?thesis
          by fastforce
      qed
      have False if c: "\<forall>z. norm z < 1 \<longrightarrow> (k \<circ> power2 \<circ> q) z = c * z" and "norm c = 1" for c
      proof -
        have "c \<noteq> 0" using that by auto
        have "norm (p(1/2)) < 1" "norm (p(-1/2)) < 1"
          using p01 by force+
        then have "(k \<circ> power2 \<circ> q) (p(1/2)) = c * p(1/2)" "(k \<circ> power2 \<circ> q) (p(-1/2)) = c * p(-1/2)"
          using c by force+
        then have "p (1/2) = p (- (1/2))"
          by (auto simp: \<open>c \<noteq> 0\<close> qp o_def)
        then have "q (p (1/2)) = q (p (- (1/2)))"
          by simp
        then have "1/2 = - (1/2::complex)"
          by (auto simp: qp)
        then show False
          by simp
      qed
      moreover
      have False if "norm (deriv (k \<circ> power2 \<circ> q) 0) \<noteq> 1" "norm (deriv (k \<circ> power2 \<circ> q) 0) \<le> 1"
        and le: "\<And>\<xi>. norm \<xi> < 1 \<Longrightarrow> norm ((k \<circ> power2 \<circ> q) \<xi>) \<le> norm \<xi>"
      proof -
        have "norm (deriv (k \<circ> power2 \<circ> q) 0) < 1"
          using that by simp
        moreover have eq: "deriv f 0 = deriv (k \<circ> (\<lambda>z. z ^ 2) \<circ> q) 0 * deriv (p \<circ> \<psi> \<circ> h \<circ> f) 0"
        proof (intro DERIV_imp_deriv has_field_derivative_transform_within_open [OF DERIV_chain])
          show "(k \<circ> power2 \<circ> q has_field_derivative deriv (k \<circ> power2 \<circ> q) 0) (at ((p \<circ> \<psi> \<circ> h \<circ> f) 0))"
            using "1" holomorphic_derivI p0 by auto
          show "(p \<circ> \<psi> \<circ> h \<circ> f has_field_derivative deriv (p \<circ> \<psi> \<circ> h \<circ> f) 0) (at 0)"
            using \<open>p \<circ> \<psi> \<circ> h \<circ> f \<in> F\<close> \<open>open S\<close> \<open>0 \<in> S\<close> holF holomorphic_derivI by blast
          show "\<And>x. x \<in> S \<Longrightarrow> (k \<circ> power2 \<circ> q \<circ> (p \<circ> \<psi> \<circ> h \<circ> f)) x = f x"
            using \<psi>2 f01 kh norm\<psi>1 qp by auto
        qed (use assms in simp_all)
        ultimately have "cmod (deriv (p \<circ> \<psi> \<circ> h \<circ> f) 0) \<le> 0"
          using le_norm_df0
          by (metis linorder_not_le mult.commute mult_less_cancel_left2 norm_mult)
        moreover have "1 \<le> norm (deriv f 0)"
          using normf [of id] by (simp add: idF)
        ultimately show False
          by (simp add: eq)
      qed
      ultimately show ?thesis
        using Schwarz_Lemma [OF 1 2 3] norm_one by blast
    qed
    then show "a \<in> f ` S"
      by blast
  qed
  then have "f ` S = ball 0 1"
    using F_def \<open>f \<in> F\<close> by blast
  then show ?thesis
    apply (rule_tac x=f in exI)
    apply (rule_tac x=g in exI)
    using holf holg derg gf by safe force+
qed


locale SC_Chain =
  fixes S :: "complex set"
  assumes openS: "open S"
begin

lemma winding_number_zero:
  assumes "simply_connected S"
  shows "connected S \<and>
         (\<forall>\<gamma> z. path \<gamma> \<and> path_image \<gamma> \<subseteq> S \<and>
                   pathfinish \<gamma> = pathstart \<gamma> \<and> z \<notin> S \<longrightarrow> winding_number \<gamma> z = 0)"
  using assms
  by (auto simp: simply_connected_imp_connected simply_connected_imp_winding_number_zero)

lemma contour_integral_zero:
  assumes "valid_path g" "path_image g \<subseteq> S" "pathfinish g = pathstart g" "f holomorphic_on S"
         "\<And>\<gamma> z. \<lbrakk>path \<gamma>; path_image \<gamma> \<subseteq> S; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> S\<rbrakk> \<Longrightarrow> winding_number \<gamma> z = 0"
  shows "(f has_contour_integral 0) g"
  using assms by (meson Cauchy_theorem_global openS valid_path_imp_path)

lemma global_primitive:
  assumes "connected S" and holf: "f holomorphic_on S"
  and prev: "\<And>\<gamma> f. \<lbrakk>valid_path \<gamma>; path_image \<gamma> \<subseteq> S; pathfinish \<gamma> = pathstart \<gamma>; f holomorphic_on S\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) \<gamma>"
  shows "\<exists>h. \<forall>z \<in> S. (h has_field_derivative f z) (at z)"
proof (cases "S = {}")
case True then show ?thesis
    by simp
next
  case False
  then obtain a where "a \<in> S"
    by blast
  show ?thesis
  proof (intro exI ballI)
    fix x assume "x \<in> S"
    then obtain d where "d > 0" and d: "cball x d \<subseteq> S"
      using openS open_contains_cball_eq by blast
    let ?g = "\<lambda>z. (SOME g. polynomial_function g \<and> path_image g \<subseteq> S \<and> pathstart g = a \<and> pathfinish g = z)"
    show "((\<lambda>z. contour_integral (?g z) f) has_field_derivative f x)
          (at x)"
    proof (simp add: has_field_derivative_def has_derivative_at2 bounded_linear_mult_right, rule Lim_transform)
      show "(\<lambda>y. inverse(norm(y - x)) *\<^sub>R (contour_integral(linepath x y) f - f x * (y - x))) \<midarrow>x\<rightarrow> 0"
      proof (clarsimp simp add: Lim_at)
        fix e::real assume "e > 0"
        moreover have "continuous (at x) f"
          using openS \<open>x \<in> S\<close> holf continuous_on_eq_continuous_at holomorphic_on_imp_continuous_on by auto
        ultimately obtain d1 where "d1 > 0"
             and d1: "\<And>x'. dist x' x < d1 \<Longrightarrow> dist (f x') (f x) < e/2"
          unfolding continuous_at_eps_delta
          by (metis less_divide_eq_numeral1(1) mult_zero_left)
        obtain d2 where "d2 > 0" and d2: "ball x d2 \<subseteq> S"
          using openS \<open>x \<in> S\<close> open_contains_ball_eq by blast
        have "inverse (norm (y - x)) * norm (contour_integral (linepath x y) f - f x * (y - x)) < e"
          if "0 < d1" "0 < d2" "y \<noteq> x" "dist y x < d1" "dist y x < d2" for y
        proof -
          have "f contour_integrable_on linepath x y"
          proof (rule contour_integrable_continuous_linepath [OF continuous_on_subset])
            show "continuous_on S f"
              by (simp add: holf holomorphic_on_imp_continuous_on)
            have "closed_segment x y \<subseteq> ball x d2"
              by (meson dist_commute_lessI dist_in_closed_segment le_less_trans mem_ball subsetI that(5))
            with d2 show "closed_segment x y \<subseteq> S"
              by blast
          qed
          then obtain z where z: "(f has_contour_integral z) (linepath x y)"
            by (force simp: contour_integrable_on_def)
          have con: "((\<lambda>w. f x) has_contour_integral f x * (y - x)) (linepath x y)"
            using has_contour_integral_const_linepath [of "f x" y x] by metis
          have "norm (z - f x * (y - x)) \<le> (e/2) * norm (y - x)"
          proof (rule has_contour_integral_bound_linepath)
            show "((\<lambda>w. f w - f x) has_contour_integral z - f x * (y - x)) (linepath x y)"
              by (rule has_contour_integral_diff [OF z con])
            show "\<And>w. w \<in> closed_segment x y \<Longrightarrow> norm (f w - f x) \<le> e/2"
              by (metis d1 dist_norm less_le_trans not_less not_less_iff_gr_or_eq segment_bound1 that(4))
          qed (use \<open>e > 0\<close> in auto)
          with \<open>e > 0\<close> have "inverse (norm (y - x)) * norm (z - f x * (y - x)) \<le> e/2"
            by (simp add: field_split_simps)
          also have "... < e"
            using \<open>e > 0\<close> by simp
          finally show ?thesis
            by (simp add: contour_integral_unique [OF z])
        qed
        with  \<open>d1 > 0\<close> \<open>d2 > 0\<close>
        show "\<exists>d>0. \<forall>z. z \<noteq> x \<and> dist z x < d \<longrightarrow>
                 inverse (norm (z - x)) * norm (contour_integral (linepath x z) f - f x * (z - x)) < e"
          by (rule_tac x="min d1 d2" in exI) auto
      qed
    next
      have *: "(1 / norm (y - x)) *\<^sub>R (contour_integral (?g y) f -
               (contour_integral (?g x) f + f x * (y - x))) =
               (contour_integral (linepath x y) f - f x * (y - x)) /\<^sub>R norm (y - x)"
        if "0 < d" "y \<noteq> x" and yx: "dist y x < d" for y
      proof -
        have "y \<in> S"
          by (metis subsetD d dist_commute less_eq_real_def mem_cball yx)
        have gxy: "polynomial_function (?g x) \<and> path_image (?g x) \<subseteq> S \<and> pathstart (?g x) = a \<and> pathfinish (?g x) = x"
                  "polynomial_function (?g y) \<and> path_image (?g y) \<subseteq> S \<and> pathstart (?g y) = a \<and> pathfinish (?g y) = y"
          using someI_ex [OF connected_open_polynomial_connected [OF openS \<open>connected S\<close> \<open>a \<in> S\<close>]] \<open>x \<in> S\<close> \<open>y \<in> S\<close>
          by meson+
        then have vp: "valid_path (?g x)" "valid_path (?g y)"
          by (simp_all add: valid_path_polynomial_function)
        have f0: "(f has_contour_integral 0) ((?g x) +++ linepath x y +++ reversepath (?g y))"
        proof (rule prev)
          show "valid_path ((?g x) +++ linepath x y +++ reversepath (?g y))"
            using gxy vp by (auto simp: valid_path_join)
          have "closed_segment x y \<subseteq> cball x d"
            using  yx by (auto simp: dist_commute dest!: dist_in_closed_segment)
          then have "closed_segment x y \<subseteq> S"
            using d by blast
          then show "path_image ((?g x) +++ linepath x y +++ reversepath (?g y)) \<subseteq> S"
            using gxy by (auto simp: path_image_join)
        qed (use gxy holf in auto)
        then have fintxy: "f contour_integrable_on linepath x y"
          by (metis (no_types, lifting) contour_integrable_joinD1 contour_integrable_joinD2 gxy(2) has_contour_integral_integrable pathfinish_linepath pathstart_reversepath valid_path_imp_reverse valid_path_join valid_path_linepath vp(2))
        have fintgx: "f contour_integrable_on (?g x)" "f contour_integrable_on (?g y)"
          using openS contour_integrable_holomorphic_simple gxy holf vp by blast+
        show ?thesis
          apply (clarsimp simp add: divide_simps)
          using contour_integral_unique [OF f0]
          apply (simp add: fintxy gxy contour_integrable_reversepath contour_integral_reversepath fintgx vp)
          apply (simp add: algebra_simps)
          done
      qed
      show "(\<lambda>z. (1 / norm (z - x)) *\<^sub>R
                 (contour_integral (?g z) f - (contour_integral (?g x) f + f x * (z - x))) -
                 (contour_integral (linepath x z) f - f x * (z - x)) /\<^sub>R norm (z - x))
            \<midarrow>x\<rightarrow> 0"
        apply (rule tendsto_eventually)
        apply (simp add: eventually_at)
        apply (rule_tac x=d in exI)
        using \<open>d > 0\<close> * by simp
    qed
  qed
qed

lemma holomorphic_log:
  assumes "connected S" and holf: "f holomorphic_on S" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  and prev: "\<And>f. f holomorphic_on S \<Longrightarrow> \<exists>h. \<forall>z \<in> S. (h has_field_derivative f z) (at z)"
  shows "\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = exp(g z))"
proof -
  have "(\<lambda>z. deriv f z / f z) holomorphic_on S"
    by (simp add: openS holf holomorphic_deriv holomorphic_on_divide nz)
  then obtain g where g: "\<And>z. z \<in> S \<Longrightarrow> (g has_field_derivative deriv f z / f z) (at z)"
    using prev [of "\<lambda>z. deriv f z / f z"] by metis
  have hfd: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>z. exp (g z) / f z) has_field_derivative 0) (at x)"
    apply (rule derivative_eq_intros g| simp)+
      apply (subst DERIV_deriv_iff_field_differentiable)
    using openS holf holomorphic_on_imp_differentiable_at nz apply auto
    done
  obtain c where c: "\<And>x. x \<in> S \<Longrightarrow> exp (g x) / f x = c"
  proof (rule DERIV_zero_connected_constant[OF \<open>connected S\<close> openS finite.emptyI])
    show "continuous_on S (\<lambda>z. exp (g z) / f z)"
      by (metis (full_types) openS g continuous_on_divide continuous_on_exp holf holomorphic_on_imp_continuous_on holomorphic_on_open nz)
    then show "\<forall>x\<in>S - {}. ((\<lambda>z. exp (g z) / f z) has_field_derivative 0) (at x)"
      using hfd by (blast intro: DERIV_zero_connected_constant [OF \<open>connected S\<close> openS finite.emptyI, of "\<lambda>z. exp(g z) / f z"])
  qed auto
  show ?thesis
  proof (intro exI ballI conjI)
    show "(\<lambda>z. Ln(inverse c) + g z) holomorphic_on S"
      apply (intro holomorphic_intros)
      using openS g holomorphic_on_open by blast
    fix z :: complex
    assume "z \<in> S"
    then have "exp (g z) / c = f z"
      by (metis c divide_divide_eq_right exp_not_eq_zero nonzero_mult_div_cancel_left)
    moreover have "1 / c \<noteq> 0"
      using \<open>z \<in> S\<close> c nz by fastforce
    ultimately show "f z = exp (Ln (inverse c) + g z)"
      by (simp add: exp_add inverse_eq_divide)
  qed
qed

lemma holomorphic_sqrt:
  assumes holf: "f holomorphic_on S" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  and prev: "\<And>f. \<lbrakk>f holomorphic_on S; \<forall>z \<in> S. f z \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = exp(g z))"
  shows "\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
proof -
  obtain g where holg: "g holomorphic_on S" and g: "\<And>z. z \<in> S \<Longrightarrow> f z = exp (g z)"
    using prev [of f] holf nz by metis
  show ?thesis
  proof (intro exI ballI conjI)
    show "(\<lambda>z. exp(g z/2)) holomorphic_on S"
      by (intro holomorphic_intros) (auto simp: holg)
    show "\<And>z. z \<in> S \<Longrightarrow> f z = (exp (g z/2))\<^sup>2"
      by (metis (no_types) g exp_double nonzero_mult_div_cancel_left times_divide_eq_right zero_neq_numeral)
  qed
qed

lemma biholomorphic_to_disc:
  assumes "connected S" and S: "S \<noteq> {}" "S \<noteq> UNIV"
  and prev: "\<And>f. \<lbrakk>f holomorphic_on S; \<forall>z \<in> S. f z \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
  shows "\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
                   (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
                   (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z)"
proof -
  obtain a b where "a \<in> S" "b \<notin> S"
    using S by blast
  then obtain \<delta> where "\<delta> > 0" and \<delta>: "ball a \<delta> \<subseteq> S"
    using openS openE by blast
  obtain g where holg: "g holomorphic_on S" and eqg: "\<And>z. z \<in> S \<Longrightarrow> z - b = (g z)\<^sup>2"
  proof (rule exE [OF prev [of "\<lambda>z. z - b"]])
    show "(\<lambda>z. z - b) holomorphic_on S"
      by (intro holomorphic_intros)
  qed (use \<open>b \<notin> S\<close> in auto)
  have "\<not> g constant_on S"
  proof -
    have "(a + \<delta>/2) \<in> ball a \<delta>" "a + (\<delta>/2) \<noteq> a"
      using \<open>\<delta> > 0\<close> by (simp_all add: dist_norm)
    then show ?thesis
      unfolding constant_on_def
      using eqg [of a] eqg [of "a + \<delta>/2"] \<open>a \<in> S\<close> \<delta>
      by (metis diff_add_cancel subset_eq)
  qed
  then have "open (g ` ball a \<delta>)"
    using open_mapping_thm [of g S "ball a \<delta>", OF holg openS \<open>connected S\<close>] \<delta> by blast
  then obtain r where "r > 0" and r: "ball (g a) r \<subseteq> (g ` ball a \<delta>)"
    by (metis \<open>0 < \<delta>\<close> centre_in_ball imageI openE)
  have g_not_r: "g z \<notin> ball (-(g a)) r" if "z \<in> S" for z
  proof
    assume "g z \<in> ball (-(g a)) r"
    then have "- g z \<in> ball (g a) r"
      by (metis add.inverse_inverse dist_minus mem_ball)
    with r have "- g z \<in> (g ` ball a \<delta>)"
      by blast
    then obtain w where w: "- g z = g w" "dist a w < \<delta>"
      by auto
    then have "w \<in> ball a \<delta>"
      by simp
    then have "w \<in> S"
      using \<delta> by blast
    then have "w = z"
      by (metis diff_add_cancel eqg power_minus_Bit0 that w(1))
    then have "g z = 0"
      using \<open>- g z = g w\<close> by auto
    with eqg [OF that] have "z = b"
      by auto
    with that \<open>b \<notin> S\<close> show False
      by simp
  qed
  then have nz: "\<And>z. z \<in> S \<Longrightarrow> g z + g a \<noteq> 0"
    by (metis \<open>0 < r\<close> add.commute add_diff_cancel_left' centre_in_ball diff_0)
  let ?f = "\<lambda>z. (r/3) / (g z + g a) - (r/3) / (g a + g a)"
  obtain h where holh: "h holomorphic_on S" and "h a = 0" and h01: "h ` S \<subseteq> ball 0 1" and "inj_on h S"
  proof
    show "?f holomorphic_on S"
      by (intro holomorphic_intros holg nz)
    have 3: "\<lbrakk>norm x \<le> 1/3; norm y \<le> 1/3\<rbrakk> \<Longrightarrow> norm(x - y) < 1" for x y::complex
      using norm_triangle_ineq4 [of x y] by simp
    have "norm ((r/3) / (g z + g a) - (r/3) / (g a + g a)) < 1" if "z \<in> S" for z
      apply (rule 3)
      unfolding norm_divide
      using \<open>r > 0\<close> g_not_r [OF \<open>z \<in> S\<close>] g_not_r [OF \<open>a \<in> S\<close>]
      by (simp_all add: field_split_simps dist_commute dist_norm)
  then show "?f ` S \<subseteq> ball 0 1"
    by auto
    show "inj_on ?f S"
      using \<open>r > 0\<close> eqg apply (clarsimp simp: inj_on_def)
      by (metis diff_add_cancel)
  qed auto
  obtain k where holk: "k holomorphic_on (h ` S)"
             and derk: "\<And>z. z \<in> S \<Longrightarrow> deriv h z * deriv k (h z) = 1"
             and kh: "\<And>z. z \<in> S \<Longrightarrow> k(h z) = z"
    using holomorphic_has_inverse [OF holh openS \<open>inj_on h S\<close>] by metis

  have 1: "open (h ` S)"
    by (simp add: \<open>inj_on h S\<close> holh openS open_mapping_thm3)
  have 2: "connected (h ` S)"
    by (simp add: connected_continuous_image \<open>connected S\<close> holh holomorphic_on_imp_continuous_on)
  have 3: "0 \<in> h ` S"
    using \<open>a \<in> S\<close> \<open>h a = 0\<close> by auto
  have 4: "\<exists>g. g holomorphic_on h ` S \<and> (\<forall>z\<in>h ` S. f z = (g z)\<^sup>2)"
    if holf: "f holomorphic_on h ` S" and nz: "\<And>z. z \<in> h ` S \<Longrightarrow> f z \<noteq> 0" "inj_on f (h ` S)" for f
  proof -
    obtain g where holg: "g holomorphic_on S" and eqg: "\<And>z. z \<in> S \<Longrightarrow> (f \<circ> h) z = (g z)\<^sup>2"
    proof -
      have "f \<circ> h holomorphic_on S"
        by (simp add: holh holomorphic_on_compose holf)
      moreover have "\<forall>z\<in>S. (f \<circ> h) z \<noteq> 0"
        by (simp add: nz)
      ultimately show thesis
        using prev that by blast
    qed
    show ?thesis
    proof (intro exI conjI)
      show "g \<circ> k holomorphic_on h ` S"
      proof -
        have "k ` h ` S \<subseteq> S"
          by (simp add: \<open>\<And>z. z \<in> S \<Longrightarrow> k (h z) = z\<close> image_subset_iff)
        then show ?thesis
          by (meson holg holk holomorphic_on_compose holomorphic_on_subset)
      qed
      show "\<forall>z\<in>h ` S. f z = ((g \<circ> k) z)\<^sup>2"
        using eqg kh by auto
    qed
  qed
  obtain f g where f: "f holomorphic_on h ` S" and g: "g holomorphic_on ball 0 1"
       and gf: "\<forall>z\<in>h ` S. f z \<in> ball 0 1 \<and> g (f z) = z"  and fg:"\<forall>z\<in>ball 0 1. g z \<in> h ` S \<and> f (g z) = z"
    using biholomorphic_to_disc_aux [OF 1 2 3 h01 4] by blast
  show ?thesis
  proof (intro exI conjI)
    show "f \<circ> h holomorphic_on S"
      by (simp add: f holh holomorphic_on_compose)
    show "k \<circ> g holomorphic_on ball 0 1"
      by (metis holomorphic_on_subset image_subset_iff fg holk g holomorphic_on_compose)
  qed (use fg gf kh in auto)
qed

lemma homeomorphic_to_disc:
  assumes S: "S \<noteq> {}"
    and prev: "S = UNIV \<or>
               (\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
                     (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
                     (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z))" (is "_ \<or> ?P")
  shows "S homeomorphic ball (0::complex) 1"
  using prev
proof
  assume "S = UNIV" then show ?thesis
    using homeomorphic_ball01_UNIV homeomorphic_sym by blast
next
  assume ?P
  then show ?thesis
    unfolding homeomorphic_minimal
    using holomorphic_on_imp_continuous_on by blast
qed

lemma homeomorphic_to_disc_imp_simply_connected:
  assumes "S = {} \<or> S homeomorphic ball (0::complex) 1"
  shows "simply_connected S"
  using assms homeomorphic_simply_connected_eq convex_imp_simply_connected by auto

end

proposition
  assumes "open S"
  shows simply_connected_eq_winding_number_zero:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>g z. path g \<and> path_image g \<subseteq> S \<and>
                 pathfinish g = pathstart g \<and> (z \<notin> S)
                 \<longrightarrow> winding_number g z = 0)" (is "?wn0")
    and simply_connected_eq_contour_integral_zero:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>g f. valid_path g \<and> path_image g \<subseteq> S \<and>
                 pathfinish g = pathstart g \<and> f holomorphic_on S
               \<longrightarrow> (f has_contour_integral 0) g)" (is "?ci0")
    and simply_connected_eq_global_primitive:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>f. f holomorphic_on S \<longrightarrow>
                (\<exists>h. \<forall>z. z \<in> S \<longrightarrow> (h has_field_derivative f z) (at z)))" (is "?gp")
    and simply_connected_eq_holomorphic_log:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>f. f holomorphic_on S \<and> (\<forall>z \<in> S. f z \<noteq> 0)
               \<longrightarrow> (\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = exp(g z))))" (is "?log")
    and simply_connected_eq_holomorphic_sqrt:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>f. f holomorphic_on S \<and> (\<forall>z \<in> S. f z \<noteq> 0)
                \<longrightarrow> (\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S.  f z = (g z)\<^sup>2)))" (is "?sqrt")
    and simply_connected_eq_biholomorphic_to_disc:
         "simply_connected S \<longleftrightarrow>
           S = {} \<or> S = UNIV \<or>
           (\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
                 (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
                 (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z))" (is "?bih")
    and simply_connected_eq_homeomorphic_to_disc:
          "simply_connected S \<longleftrightarrow> S = {} \<or> S homeomorphic ball (0::complex) 1" (is "?disc")
proof -
  interpret SC_Chain
    using assms by (simp add: SC_Chain_def)
  have "?wn0 \<and> ?ci0 \<and> ?gp \<and> ?log \<and> ?sqrt \<and> ?bih \<and> ?disc"
proof -
  have *: "\<lbrakk>\<alpha> \<Longrightarrow> \<beta>; \<beta> \<Longrightarrow> \<gamma>; \<gamma> \<Longrightarrow> \<delta>; \<delta> \<Longrightarrow> \<zeta>; \<zeta> \<Longrightarrow> \<eta>; \<eta> \<Longrightarrow> \<theta>; \<theta> \<Longrightarrow> \<xi>; \<xi> \<Longrightarrow> \<alpha>\<rbrakk>
        \<Longrightarrow> (\<alpha> \<longleftrightarrow> \<beta>) \<and> (\<alpha> \<longleftrightarrow> \<gamma>) \<and> (\<alpha> \<longleftrightarrow> \<delta>) \<and> (\<alpha> \<longleftrightarrow> \<zeta>) \<and>
            (\<alpha> \<longleftrightarrow> \<eta>) \<and> (\<alpha> \<longleftrightarrow> \<theta>) \<and> (\<alpha> \<longleftrightarrow> \<xi>)" for \<alpha> \<beta> \<gamma> \<delta> \<zeta> \<eta> \<theta> \<xi>
    by blast
  show ?thesis
    apply (rule *)
    using winding_number_zero apply metis
    using contour_integral_zero apply metis
    using global_primitive apply metis
    using holomorphic_log apply metis
    using holomorphic_sqrt apply simp
    using biholomorphic_to_disc apply blast
    using homeomorphic_to_disc apply blast
    using homeomorphic_to_disc_imp_simply_connected apply blast
    done
qed
  then show ?wn0 ?ci0 ?gp ?log ?sqrt ?bih ?disc
    by safe
qed

corollary contractible_eq_simply_connected_2d:
  fixes S :: "complex set"
  shows "open S \<Longrightarrow> (contractible S \<longleftrightarrow> simply_connected S)"
  apply safe
   apply (simp add: contractible_imp_simply_connected)
  using convex_imp_contractible homeomorphic_contractible_eq simply_connected_eq_homeomorphic_to_disc by auto

subsection\<open>A further chain of equivalences about components of the complement of a simply connected set\<close>

text\<open>(following 1.35 in Burckel'S book)\<close>

context SC_Chain
begin

lemma frontier_properties:
  assumes "simply_connected S"
  shows "if bounded S then connected(frontier S)
         else \<forall>C \<in> components(frontier S). \<not> bounded C"
proof -
  have "S = {} \<or> S homeomorphic ball (0::complex) 1"
    using simply_connected_eq_homeomorphic_to_disc assms openS by blast
  then show ?thesis
  proof
    assume "S = {}"
    then have "bounded S"
      by simp
    with \<open>S = {}\<close> show ?thesis
      by simp
  next
    assume S01: "S homeomorphic ball (0::complex) 1"
    then obtain g f
      where gim: "g ` S = ball 0 1" and fg: "\<And>x. x \<in> S \<Longrightarrow> f(g x) = x"
        and fim: "f ` ball 0 1 = S" and gf: "\<And>y. cmod y < 1 \<Longrightarrow> g(f y) = y"
        and contg: "continuous_on S g" and contf: "continuous_on (ball 0 1) f"
      by (fastforce simp: homeomorphism_def homeomorphic_def)
    define D where "D \<equiv> \<lambda>n. ball (0::complex) (1 - 1/(of_nat n + 2))"
    define A where "A \<equiv> \<lambda>n. {z::complex. 1 - 1/(of_nat n + 2) < norm z \<and> norm z < 1}"
    define X where "X \<equiv> \<lambda>n::nat. closure(f ` A n)"
    have D01: "D n \<subseteq> ball 0 1" for n
      by (simp add: D_def ball_subset_ball_iff)
    have A01: "A n \<subseteq> ball 0 1" for n
      by (auto simp: A_def)
    have cloX: "closed(X n)" for n
      by (simp add: X_def)
    have Xsubclo: "X n \<subseteq> closure S" for n
      unfolding X_def by (metis A01 closure_mono fim image_mono)
    have connX: "connected(X n)" for n
      unfolding X_def
      apply (rule connected_imp_connected_closure)
      apply (rule connected_continuous_image)
      apply (simp add: continuous_on_subset [OF contf A01])
      using connected_annulus [of _ "0::complex"] by (simp add: A_def)
    have nestX: "X n \<subseteq> X m" if "m \<le> n" for m n
    proof -
      have "1 - 1 / (real m + 2) \<le> 1 - 1 / (real n + 2)"
        using that by (auto simp: field_simps)
      then show ?thesis
        by (auto simp: X_def A_def intro!: closure_mono)
    qed
    have "closure S - S \<subseteq> (\<Inter>n. X n)"
    proof
      fix x
      assume "x \<in> closure S - S"
      then have "x \<in> closure S" "x \<notin> S" by auto
      show "x \<in> (\<Inter>n. X n)"
      proof
        fix n
        have "ball 0 1 = closure (D n) \<union> A n"
          by (auto simp: D_def A_def le_less_trans)
        with fim have Seq: "S = f ` (closure (D n)) \<union> f ` (A n)"
          by (simp add: image_Un)
        have "continuous_on (closure (D n)) f"
          by (simp add: D_def cball_subset_ball_iff continuous_on_subset [OF contf])
        moreover have "compact (closure (D n))"
          by (simp add: D_def)
        ultimately have clo_fim: "closed (f ` closure (D n))"
          using compact_continuous_image compact_imp_closed by blast
        have *: "(f ` cball 0 (1 - 1 / (real n + 2))) \<subseteq> S"
          by (force simp: D_def Seq)
        show "x \<in> X n"
          using \<open>x \<in> closure S\<close> unfolding X_def Seq
          using \<open>x \<notin> S\<close> * D_def clo_fim by auto
      qed
    qed
    moreover have "(\<Inter>n. X n) \<subseteq> closure S - S"
    proof -
      have "(\<Inter>n. X n) \<subseteq> closure S"
      proof -
        have "(\<Inter>n. X n) \<subseteq> X 0"
          by blast
        also have "... \<subseteq> closure S"
          apply (simp add: X_def fim [symmetric])
          apply (rule closure_mono)
          by (auto simp: A_def)
        finally show "(\<Inter>n. X n) \<subseteq> closure S" .
      qed
      moreover have "(\<Inter>n. X n) \<inter> S \<subseteq> {}"
      proof (clarify, clarsimp simp: X_def fim [symmetric])
        fix x assume x [rule_format]: "\<forall>n. f x \<in> closure (f ` A n)" and "cmod x < 1"
        then obtain n where n: "1 / (1 - norm x) < of_nat n"
          using reals_Archimedean2 by blast
        with \<open>cmod x < 1\<close> gr0I have XX: "1 / of_nat n < 1 - norm x" and "n > 0"
          by (fastforce simp: field_split_simps algebra_simps)+
        have "f x \<in> f ` (D n)"
          using n \<open>cmod x < 1\<close> by (auto simp: field_split_simps algebra_simps D_def)
        moreover have " f ` D n \<inter> closure (f ` A n) = {}"
        proof -
          have op_fDn: "open(f ` (D n))"
          proof (rule invariance_of_domain)
            show "continuous_on (D n) f"
              by (rule continuous_on_subset [OF contf D01])
            show "open (D n)"
              by (simp add: D_def)
            show "inj_on f (D n)"
              unfolding inj_on_def using D01 by (metis gf mem_ball_0 subsetCE)
          qed
          have injf: "inj_on f (ball 0 1)"
            by (metis mem_ball_0 inj_on_def gf)
          have "D n \<union> A n \<subseteq> ball 0 1"
            using D01 A01 by simp
          moreover have "D n \<inter> A n = {}"
            by (auto simp: D_def A_def)
          ultimately have "f ` D n \<inter> f ` A n = {}"
            by (metis A01 D01 image_is_empty inj_on_image_Int injf)
          then show ?thesis
            by (simp add: open_Int_closure_eq_empty [OF op_fDn])
        qed
        ultimately show False
          using x [of n] by blast
      qed
      ultimately
      show "(\<Inter>n. X n) \<subseteq> closure S - S"
        using closure_subset disjoint_iff_not_equal by blast
    qed
    ultimately have "closure S - S = (\<Inter>n. X n)" by blast
    then have frontierS: "frontier S = (\<Inter>n. X n)"
      by (simp add: frontier_def openS interior_open)
    show ?thesis
    proof (cases "bounded S")
      case True
      have bouX: "bounded (X n)" for n
        apply (simp add: X_def)
        apply (rule bounded_closure)
        by (metis A01 fim image_mono bounded_subset [OF True])
      have compaX: "compact (X n)" for n
        apply (simp add: compact_eq_bounded_closed bouX)
        apply (auto simp: X_def)
        done
      have "connected (\<Inter>n. X n)"
        by (metis nestX compaX connX connected_nest)
      then show ?thesis
        by (simp add: True \<open>frontier S = (\<Inter>n. X n)\<close>)
    next
      case False
      have unboundedX: "\<not> bounded(X n)" for n
      proof
        assume bXn: "bounded(X n)"
        have "continuous_on (cball 0 (1 - 1 / (2 + real n))) f"
          by (simp add: cball_subset_ball_iff continuous_on_subset [OF contf])
        then have "bounded (f ` cball 0 (1 - 1 / (2 + real n)))"
          by (simp add: compact_imp_bounded [OF compact_continuous_image])
        moreover have "bounded (f ` A n)"
          by (auto simp: X_def closure_subset image_subset_iff bounded_subset [OF bXn])
        ultimately have "bounded (f ` (cball 0 (1 - 1/(2 + real n)) \<union> A n))"
          by (simp add: image_Un)
        then have "bounded (f ` ball 0 1)"
          apply (rule bounded_subset)
          apply (auto simp: A_def algebra_simps)
          done
        then show False
          using False by (simp add: fim [symmetric])
      qed
      have clo_INTX: "closed(\<Inter>(range X))"
        by (metis cloX closed_INT)
      then have lcX: "locally compact (\<Inter>(range X))"
        by (metis closed_imp_locally_compact)
      have False if C: "C \<in> components (frontier S)" and boC: "bounded C" for C
      proof -
        have "closed C"
          by (metis C closed_components frontier_closed)
        then have "compact C"
          by (metis boC compact_eq_bounded_closed)
        have Cco: "C \<in> components (\<Inter>(range X))"
          by (metis frontierS C)
        obtain K where "C \<subseteq> K" "compact K"
                   and Ksub: "K \<subseteq> \<Inter>(range X)" and clo: "closed(\<Inter>(range X) - K)"
        proof (cases "{k. C \<subseteq> k \<and> compact k \<and> openin (top_of_set (\<Inter>(range X))) k} = {}")
          case True
          then show ?thesis
            using Sura_Bura [OF lcX Cco \<open>compact C\<close>] boC
            by (simp add: True)
        next
          case False
          then obtain L where "compact L" "C \<subseteq> L" and K: "openin (top_of_set (\<Inter>x. X x)) L"
            by blast
          show ?thesis
          proof
            show "L \<subseteq> \<Inter>(range X)"
              by (metis K openin_imp_subset)
            show "closed (\<Inter>(range X) - L)"
              by (metis closedin_diff closedin_self closedin_closed_trans [OF _ clo_INTX] K)
          qed (use \<open>compact L\<close> \<open>C \<subseteq> L\<close> in auto)
        qed
        obtain U V where "open U" and "compact (closure U)" and "open V" "K \<subseteq> U"
                     and V: "\<Inter>(range X) - K \<subseteq> V" and "U \<inter> V = {}"
          using separation_normal_compact [OF \<open>compact K\<close> clo] by blast
        then have "U \<inter> (\<Inter> (range X) - K) = {}"
          by blast
        have "(closure U - U) \<inter> (\<Inter>n. X n \<inter> closure U) \<noteq> {}"
        proof (rule compact_imp_fip)
          show "compact (closure U - U)"
            by (metis \<open>compact (closure U)\<close> \<open>open U\<close> compact_diff)
          show "\<And>T. T \<in> range (\<lambda>n. X n \<inter> closure U) \<Longrightarrow> closed T"
            by clarify (metis cloX closed_Int closed_closure)
          show "(closure U - U) \<inter> \<Inter>\<F> \<noteq> {}"
            if "finite \<F>" and \<F>: "\<F> \<subseteq> range (\<lambda>n. X n \<inter> closure U)" for \<F>
          proof
            assume empty: "(closure U - U) \<inter> \<Inter>\<F> = {}"
            obtain J where "finite J" and J: "\<F> = (\<lambda>n. X n \<inter> closure U) ` J"
              using finite_subset_image [OF \<open>finite \<F>\<close> \<F>] by auto
            show False
            proof (cases "J = {}")
              case True
              with J empty have "closed U"
                by (simp add: closure_subset_eq)
              have "C \<noteq> {}"
                using C in_components_nonempty by blast
              then have "U \<noteq> {}"
                using \<open>K \<subseteq> U\<close> \<open>C \<subseteq> K\<close> by blast
              moreover have "U \<noteq> UNIV"
                using \<open>compact (closure U)\<close> by auto
              ultimately show False
                using \<open>open U\<close> \<open>closed U\<close> clopen by blast
            next
              case False
              define j where "j \<equiv> Max J"
              have "j \<in> J"
                by (simp add: False \<open>finite J\<close> j_def)
              have jmax: "\<And>m. m \<in> J \<Longrightarrow> m \<le> j"
                by (simp add: j_def \<open>finite J\<close>)
              have "\<Inter> ((\<lambda>n. X n \<inter> closure U) ` J) = X j \<inter> closure U"
                using False jmax nestX \<open>j \<in> J\<close> by auto
              then have "X j \<inter> closure U = X j \<inter> U"
                apply safe
                using DiffI J empty apply auto[1]
                using closure_subset by blast
              then have "openin (top_of_set (X j)) (X j \<inter> closure U)"
                by (simp add: openin_open_Int \<open>open U\<close>)
              moreover have "closedin (top_of_set (X j)) (X j \<inter> closure U)"
                by (simp add: closedin_closed_Int)
              moreover have "X j \<inter> closure U \<noteq> X j"
                by (metis unboundedX \<open>compact (closure U)\<close> bounded_subset compact_eq_bounded_closed inf.order_iff)
              moreover have "X j \<inter> closure U \<noteq> {}"
              proof -
                have "C \<noteq> {}"
                  using C in_components_nonempty by blast
                moreover have "C \<subseteq> X j \<inter> closure U"
                  using \<open>C \<subseteq> K\<close> \<open>K \<subseteq> U\<close> Ksub closure_subset by blast
                ultimately show ?thesis by blast
              qed
              ultimately show False
                using connX [of j] by (force simp: connected_clopen)
            qed
          qed
        qed
        moreover have "(\<Inter>n. X n \<inter> closure U) = (\<Inter>n. X n) \<inter> closure U"
          by blast
        moreover have "x \<in> U" if "\<And>n. x \<in> X n" "x \<in> closure U" for x
        proof -
          have "x \<notin> V"
            using \<open>U \<inter> V = {}\<close> \<open>open V\<close> closure_iff_nhds_not_empty that(2) by blast
          then show ?thesis
            by (metis (no_types) Diff_iff INT_I V \<open>K \<subseteq> U\<close> contra_subsetD that(1))
        qed
        ultimately show False
          by (auto simp: open_Int_closure_eq_empty [OF \<open>open V\<close>, of U])
      qed
      then show ?thesis
        by (auto simp: False)
    qed
  qed
qed


lemma unbounded_complement_components:
  assumes C: "C \<in> components (- S)" and S: "connected S"
    and prev: "if bounded S then connected(frontier S)
               else \<forall>C \<in> components(frontier S). \<not> bounded C"
  shows "\<not> bounded C"
proof (cases "bounded S")
  case True
  with prev have "S \<noteq> UNIV" and confr: "connected(frontier S)"
    by auto
  obtain w where C_ccsw: "C = connected_component_set (- S) w" and "w \<notin> S"
    using C by (auto simp: components_def)
  show ?thesis
  proof (cases "S = {}")
    case True with C show ?thesis by auto
  next
    case False
    show ?thesis
    proof
      assume "bounded C"
      then have "outside C \<noteq> {}"
        using outside_bounded_nonempty by metis
      then obtain z where z: "\<not> bounded (connected_component_set (- C) z)" and "z \<notin> C"
        by (auto simp: outside_def)
      have clo_ccs: "closed (connected_component_set (- S) x)" for x
        by (simp add: closed_Compl closed_connected_component openS)
      have "connected_component_set (- S) w = connected_component_set (- S) z"
      proof (rule joinable_connected_component_eq [OF confr])
        show "frontier S \<subseteq> - S"
          using openS by (auto simp: frontier_def interior_open)
        have False if "connected_component_set (- S) w \<inter> frontier (- S) = {}"
        proof -
          have "C \<inter> frontier S = {}"
            using that by (simp add: C_ccsw)
          then show False
            by (metis C_ccsw ComplI Compl_eq_Compl_iff Diff_subset False \<open>w \<notin> S\<close> clo_ccs closure_closed compl_bot_eq connected_component_eq_UNIV connected_component_eq_empty empty_subsetI frontier_complement frontier_def frontier_not_empty frontier_of_connected_component_subset le_inf_iff subset_antisym)
        qed
        then show "connected_component_set (- S) w \<inter> frontier S \<noteq> {}"
          by auto
        have *: "\<lbrakk>frontier C \<subseteq> C; frontier C \<subseteq> F; frontier C \<noteq> {}\<rbrakk> \<Longrightarrow> C \<inter> F \<noteq> {}" for C F::"complex set"
          by blast
        have "connected_component_set (- S) z \<inter> frontier (- S) \<noteq> {}"
        proof (rule *)
          show "frontier (connected_component_set (- S) z) \<subseteq> connected_component_set (- S) z"
            by (auto simp: closed_Compl closed_connected_component frontier_def openS)
          show "frontier (connected_component_set (- S) z) \<subseteq> frontier (- S)"
            using frontier_of_connected_component_subset by fastforce
          have "\<not> bounded (-S)"
            by (simp add: True cobounded_imp_unbounded)
          then have "connected_component_set (- S) z \<noteq> {}"
            apply (simp only: connected_component_eq_empty)
            using confr openS \<open>bounded C\<close> \<open>w \<notin> S\<close>
            apply (simp add: frontier_def interior_open C_ccsw)
            by (metis ComplI Compl_eq_Diff_UNIV connected_UNIV closed_closure closure_subset connected_component_eq_self
                      connected_diff_open_from_closed subset_UNIV)
          then show "frontier (connected_component_set (- S) z) \<noteq> {}"
            apply (simp add: frontier_eq_empty connected_component_eq_UNIV)
            apply (metis False compl_top_eq double_compl)
            done
        qed
        then show "connected_component_set (- S) z \<inter> frontier S \<noteq> {}"
          by auto
      qed
      then show False
        by (metis C_ccsw Compl_iff \<open>w \<notin> S\<close> \<open>z \<notin> C\<close> connected_component_eq_empty connected_component_idemp)
    qed
  qed
next
  case False
  obtain w where C_ccsw: "C = connected_component_set (- S) w" and "w \<notin> S"
    using C by (auto simp: components_def)
  have "frontier (connected_component_set (- S) w) \<subseteq> connected_component_set (- S) w"
    by (simp add: closed_Compl closed_connected_component frontier_subset_eq openS)
  moreover have "frontier (connected_component_set (- S) w) \<subseteq> frontier S"
    using frontier_complement frontier_of_connected_component_subset by blast
  moreover have "frontier (connected_component_set (- S) w) \<noteq> {}"
    by (metis C C_ccsw False bounded_empty compl_top_eq connected_component_eq_UNIV double_compl frontier_not_empty in_components_nonempty)
  ultimately obtain z where zin: "z \<in> frontier S" and z: "z \<in> connected_component_set (- S) w"
    by blast
  have *: "connected_component_set (frontier S) z \<in> components(frontier S)"
    by (simp add: \<open>z \<in> frontier S\<close> componentsI)
  with prev False have "\<not> bounded (connected_component_set (frontier S) z)"
    by simp
  moreover have "connected_component (- S) w = connected_component (- S) z"
    using connected_component_eq [OF z] by force
  ultimately show ?thesis
    by (metis C_ccsw * zin bounded_subset closed_Compl closure_closed connected_component_maximal
              connected_component_refl connected_connected_component frontier_closures in_components_subset le_inf_iff mem_Collect_eq openS)
qed

lemma empty_inside:
  assumes "connected S" "\<And>C. C \<in> components (- S) \<Longrightarrow> \<not> bounded C"
  shows "inside S = {}"
  using assms by (auto simp: components_def inside_def)

lemma empty_inside_imp_simply_connected:
  "\<lbrakk>connected S; inside S = {}\<rbrakk> \<Longrightarrow> simply_connected S"
  by (metis ComplI inside_Un_outside openS outside_mono simply_connected_eq_winding_number_zero subsetCE sup_bot.left_neutral winding_number_zero_in_outside)

end

proposition
  fixes S :: "complex set"
  assumes "open S"
  shows simply_connected_eq_frontier_properties:
         "simply_connected S \<longleftrightarrow>
          connected S \<and>
             (if bounded S then connected(frontier S)
             else (\<forall>C \<in> components(frontier S). \<not>bounded C))" (is "?fp")
    and simply_connected_eq_unbounded_complement_components:
         "simply_connected S \<longleftrightarrow>
          connected S \<and> (\<forall>C \<in> components(- S). \<not>bounded C)" (is "?ucc")
    and simply_connected_eq_empty_inside:
         "simply_connected S \<longleftrightarrow>
          connected S \<and> inside S = {}" (is "?ei")
proof -
  interpret SC_Chain
    using assms by (simp add: SC_Chain_def)
  have "?fp \<and> ?ucc \<and> ?ei"
proof -
  have *: "\<lbrakk>\<alpha> \<Longrightarrow> \<beta>; \<beta> \<Longrightarrow> \<gamma>; \<gamma> \<Longrightarrow> \<delta>; \<delta> \<Longrightarrow> \<alpha>\<rbrakk>
           \<Longrightarrow> (\<alpha> \<longleftrightarrow> \<beta>) \<and> (\<alpha> \<longleftrightarrow> \<gamma>) \<and> (\<alpha> \<longleftrightarrow> \<delta>)" for \<alpha> \<beta> \<gamma> \<delta>
    by blast
  show ?thesis
    apply (rule *)
    using frontier_properties simply_connected_imp_connected apply blast
apply clarify
    using unbounded_complement_components simply_connected_imp_connected apply blast
    using empty_inside apply blast
    using empty_inside_imp_simply_connected apply blast
    done
qed
  then show ?fp ?ucc ?ei
    by safe
qed

lemma simply_connected_iff_simple:
  fixes S :: "complex set"
  assumes "open S" "bounded S"
  shows "simply_connected S \<longleftrightarrow> connected S \<and> connected(- S)"
  apply (simp add: simply_connected_eq_unbounded_complement_components assms, safe)
   apply (metis DIM_complex assms(2) cobounded_has_bounded_component double_compl order_refl)
  by (meson assms inside_bounded_complement_connected_empty simply_connected_eq_empty_inside simply_connected_eq_unbounded_complement_components)

subsection\<open>Further equivalences based on continuous logs and sqrts\<close>

context SC_Chain
begin

lemma continuous_log:
  fixes f :: "complex\<Rightarrow>complex"
  assumes S: "simply_connected S"
    and contf: "continuous_on S f" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  shows "\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = exp(g z))"
proof -
  consider "S = {}" | "S homeomorphic ball (0::complex) 1"
    using simply_connected_eq_homeomorphic_to_disc [OF openS] S by metis
  then show ?thesis
  proof cases
    case 1 then show ?thesis
      by simp
  next
    case 2
    then obtain h k :: "complex\<Rightarrow>complex"
      where kh: "\<And>x. x \<in> S \<Longrightarrow> k(h x) = x" and him: "h ` S = ball 0 1"
      and conth: "continuous_on S h"
      and hk: "\<And>y. y \<in> ball 0 1 \<Longrightarrow> h(k y) = y" and kim: "k ` ball 0 1 = S"
      and contk: "continuous_on (ball 0 1) k"
      unfolding homeomorphism_def homeomorphic_def by metis
    obtain g where contg: "continuous_on (ball 0 1) g"
             and expg: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> (f \<circ> k) z = exp (g z)"
    proof (rule continuous_logarithm_on_ball)
      show "continuous_on (ball 0 1) (f \<circ> k)"
        apply (rule continuous_on_compose [OF contk])
        using kim continuous_on_subset [OF contf]
        by blast
      show "\<And>z. z \<in> ball 0 1 \<Longrightarrow> (f \<circ> k) z \<noteq> 0"
        using kim nz by auto
    qed auto
    then show ?thesis
      by (metis comp_apply conth continuous_on_compose him imageI kh)
  qed
qed

lemma continuous_sqrt:
  fixes f :: "complex\<Rightarrow>complex"
  assumes contf: "continuous_on S f" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  and prev: "\<And>f::complex\<Rightarrow>complex.
                \<lbrakk>continuous_on S f; \<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0\<rbrakk>
                  \<Longrightarrow> \<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = exp(g z))"
  shows "\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
proof -
  obtain g where contg: "continuous_on S g" and geq: "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
    using contf nz prev by metis
  show ?thesis
proof (intro exI ballI conjI)
  show "continuous_on S (\<lambda>z. exp(g z/2))"
      by (intro continuous_intros) (auto simp: contg)
    show "\<And>z. z \<in> S \<Longrightarrow> f z = (exp (g z/2))\<^sup>2"
      by (metis (no_types, lifting) divide_inverse exp_double geq mult.left_commute mult.right_neutral right_inverse zero_neq_numeral)
  qed
qed

lemma continuous_sqrt_imp_simply_connected:
  assumes "connected S"
    and prev: "\<And>f::complex\<Rightarrow>complex. \<lbrakk>continuous_on S f; \<forall>z \<in> S. f z \<noteq> 0\<rbrakk>
                \<Longrightarrow> \<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
  shows "simply_connected S"
proof (clarsimp simp add: simply_connected_eq_holomorphic_sqrt [OF openS] \<open>connected S\<close>)
  fix f
  assume "f holomorphic_on S" and nz: "\<forall>z\<in>S. f z \<noteq> 0"
  then obtain g where contg: "continuous_on S g" and geq: "\<And>z. z \<in> S \<Longrightarrow> f z = (g z)\<^sup>2"
    by (metis holomorphic_on_imp_continuous_on prev)
  show "\<exists>g. g holomorphic_on S \<and> (\<forall>z\<in>S. f z = (g z)\<^sup>2)"
  proof (intro exI ballI conjI)
    show "g holomorphic_on S"
    proof (clarsimp simp add: holomorphic_on_open [OF openS])
      fix z
      assume "z \<in> S"
      with nz geq have "g z \<noteq> 0"
        by auto
      obtain \<delta> where "0 < \<delta>" "\<And>w. \<lbrakk>w \<in> S; dist w z < \<delta>\<rbrakk> \<Longrightarrow> dist (g w) (g z) < cmod (g z)"
        using contg [unfolded continuous_on_iff] by (metis \<open>g z \<noteq> 0\<close> \<open>z \<in> S\<close> zero_less_norm_iff)
      then have \<delta>: "\<And>w. \<lbrakk>w \<in> S; w \<in> ball z \<delta>\<rbrakk> \<Longrightarrow> g w + g z \<noteq> 0"
        apply (clarsimp simp: dist_norm)
        by (metis \<open>g z \<noteq> 0\<close> add_diff_cancel_left' diff_0_right norm_eq_zero norm_increases_online norm_minus_commute norm_not_less_zero not_less_iff_gr_or_eq)
      have *: "(\<lambda>x. (f x - f z) / (x - z) / (g x + g z)) \<midarrow>z\<rightarrow> deriv f z / (g z + g z)"
        apply (intro tendsto_intros)
        using SC_Chain.openS SC_Chain_axioms \<open>f holomorphic_on S\<close> \<open>z \<in> S\<close> has_field_derivativeD holomorphic_derivI apply fastforce
        using \<open>z \<in> S\<close> contg continuous_on_eq_continuous_at isCont_def openS apply blast
        by (simp add: \<open>g z \<noteq> 0\<close>)
      then have "(g has_field_derivative deriv f z / (g z + g z)) (at z)"
        unfolding has_field_derivative_iff
      proof (rule Lim_transform_within_open)
        show "open (ball z \<delta> \<inter> S)"
          by (simp add: openS open_Int)
        show "z \<in> ball z \<delta> \<inter> S"
          using \<open>z \<in> S\<close> \<open>0 < \<delta>\<close> by simp
        show "\<And>x. \<lbrakk>x \<in> ball z \<delta> \<inter> S; x \<noteq> z\<rbrakk>
                  \<Longrightarrow> (f x - f z) / (x - z) / (g x + g z) = (g x - g z) / (x - z)"
          using \<delta>
          apply (simp add: geq \<open>z \<in> S\<close> divide_simps)
          apply (auto simp: algebra_simps power2_eq_square)
          done
      qed
      then show "\<exists>f'. (g has_field_derivative f') (at z)" ..
    qed
  qed (use geq in auto)
qed

end

proposition
  fixes S :: "complex set"
  assumes "open S"
  shows simply_connected_eq_continuous_log:
         "simply_connected S \<longleftrightarrow>
          connected S \<and>
          (\<forall>f::complex\<Rightarrow>complex. continuous_on S f \<and> (\<forall>z \<in> S. f z \<noteq> 0)
            \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = exp (g z))))" (is "?log")
    and simply_connected_eq_continuous_sqrt:
         "simply_connected S \<longleftrightarrow>
          connected S \<and>
          (\<forall>f::complex\<Rightarrow>complex. continuous_on S f \<and> (\<forall>z \<in> S. f z \<noteq> 0)
            \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)))" (is "?sqrt")
proof -
  interpret SC_Chain
    using assms by (simp add: SC_Chain_def)
  have "?log \<and> ?sqrt"
proof -
  have *: "\<lbrakk>\<alpha> \<Longrightarrow> \<beta>; \<beta> \<Longrightarrow> \<gamma>; \<gamma> \<Longrightarrow> \<alpha>\<rbrakk>
           \<Longrightarrow> (\<alpha> \<longleftrightarrow> \<beta>) \<and> (\<alpha> \<longleftrightarrow> \<gamma>)" for \<alpha> \<beta> \<gamma>
    by blast
  show ?thesis
    apply (rule *)
    apply (simp add: local.continuous_log winding_number_zero)
    apply (simp add: continuous_sqrt)
    apply (simp add: continuous_sqrt_imp_simply_connected)
    done
qed
  then show ?log ?sqrt
    by safe
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>More Borsukian results\<close>

lemma Borsukian_componentwise_eq:
  fixes S :: "'a::euclidean_space set"
  assumes S: "locally connected S \<or> compact S"
  shows "Borsukian S \<longleftrightarrow> (\<forall>C \<in> components S. Borsukian C)"
proof -
  have *: "ANR(-{0::complex})"
    by (simp add: ANR_delete open_Compl open_imp_ANR)
  show ?thesis
    using cohomotopically_trivial_on_components [OF assms *] by (auto simp: Borsukian_alt)
qed

lemma Borsukian_componentwise:
  fixes S :: "'a::euclidean_space set"
  assumes "locally connected S \<or> compact S" "\<And>C. C \<in> components S \<Longrightarrow> Borsukian C"
  shows "Borsukian S"
  by (metis Borsukian_componentwise_eq assms)

lemma simply_connected_eq_Borsukian:
  fixes S :: "complex set"
  shows "open S \<Longrightarrow> (simply_connected S \<longleftrightarrow> connected S \<and> Borsukian S)"
  by (auto simp: simply_connected_eq_continuous_log Borsukian_continuous_logarithm)

lemma Borsukian_eq_simply_connected:
  fixes S :: "complex set"
  shows "open S \<Longrightarrow> Borsukian S \<longleftrightarrow> (\<forall>C \<in> components S. simply_connected C)"
apply (auto simp: Borsukian_componentwise_eq open_imp_locally_connected)
  using in_components_connected open_components simply_connected_eq_Borsukian apply blast
  using open_components simply_connected_eq_Borsukian by blast

lemma Borsukian_separation_open_closed:
  fixes S :: "complex set"
  assumes S: "open S \<or> closed S" and "bounded S"
  shows "Borsukian S \<longleftrightarrow> connected(- S)"
  using S
proof
  assume "open S"
  show ?thesis
    unfolding Borsukian_eq_simply_connected [OF \<open>open S\<close>]
    by (meson \<open>open S\<close> \<open>bounded S\<close> bounded_subset in_components_connected in_components_subset nonseparation_by_component_eq open_components simply_connected_iff_simple)
next
  assume "closed S"
  with \<open>bounded S\<close> show ?thesis
    by (simp add: Borsukian_separation_compact compact_eq_bounded_closed)
qed


subsection\<open>Finally, the Riemann Mapping Theorem\<close>

theorem Riemann_mapping_theorem:
    "open S \<and> simply_connected S \<longleftrightarrow>
     S = {} \<or> S = UNIV \<or>
     (\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
           (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
           (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z))"
    (is "_ = ?rhs")
proof -
  have "simply_connected S \<longleftrightarrow> ?rhs" if "open S"
    by (simp add: simply_connected_eq_biholomorphic_to_disc that)
  moreover have "open S" if "?rhs"
  proof -
    { fix f g
      assume g: "g holomorphic_on ball 0 1" "\<forall>z\<in>ball 0 1. g z \<in> S \<and> f (g z) = z"
        and "\<forall>z\<in>S. cmod (f z) < 1 \<and> g (f z) = z"
      then have "S = g ` (ball 0 1)"
        by (force simp:)
      then have "open S"
        by (metis open_ball g inj_on_def open_mapping_thm3)
    }
    with that show "open S" by auto
  qed
  ultimately show ?thesis by metis
qed


subsection \<open>Applications to Winding Numbers\<close>

lemma simply_connected_inside_simple_path:
  fixes p :: "real \<Rightarrow> complex"
  shows "simple_path p \<Longrightarrow> simply_connected(inside(path_image p))"
  using Jordan_inside_outside connected_simple_path_image inside_simple_curve_imp_closed simply_connected_eq_frontier_properties
  by fastforce

lemma simply_connected_Int:
  fixes S :: "complex set"
  assumes "open S" "open T" "simply_connected S" "simply_connected T" "connected (S \<inter> T)"
  shows "simply_connected (S \<inter> T)"
  using assms by (force simp: simply_connected_eq_winding_number_zero open_Int)


subsection\<^marker>\<open>tag unimportant\<close> \<open>The winding number defines a continuous logarithm for the path itself\<close>

lemma winding_number_as_continuous_log:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  obtains q where "path q"
                  "pathfinish q - pathstart q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
                  "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = \<zeta> + exp(q t)"
proof -
  let ?q = "\<lambda>t. 2 * of_real pi * \<i> * winding_number(subpath 0 t p) \<zeta> + Ln(pathstart p - \<zeta>)"
  show ?thesis
  proof
    have *: "continuous (at t within {0..1}) (\<lambda>x. winding_number (subpath 0 x p) \<zeta>)"
      if t: "t \<in> {0..1}" for t
    proof -
      let ?B = "ball (p t) (norm(p t - \<zeta>))"
      have "p t \<noteq> \<zeta>"
        using path_image_def that \<zeta> by blast
      then have "simply_connected ?B"
        by (simp add: convex_imp_simply_connected)
      then have "\<And>f::complex\<Rightarrow>complex. continuous_on ?B f \<and> (\<forall>\<zeta> \<in> ?B. f \<zeta> \<noteq> 0)
                  \<longrightarrow> (\<exists>g. continuous_on ?B g \<and> (\<forall>\<zeta> \<in> ?B. f \<zeta> = exp (g \<zeta>)))"
        by (simp add: simply_connected_eq_continuous_log)
      moreover have "continuous_on ?B (\<lambda>w. w - \<zeta>)"
        by (intro continuous_intros)
      moreover have "(\<forall>z \<in> ?B. z - \<zeta> \<noteq> 0)"
        by (auto simp: dist_norm)
      ultimately obtain g where contg: "continuous_on ?B g"
        and geq: "\<And>z. z \<in> ?B \<Longrightarrow> z - \<zeta> = exp (g z)" by blast
      obtain d where "0 < d" and d:
        "\<And>x. \<lbrakk>x \<in> {0..1}; dist x t < d\<rbrakk> \<Longrightarrow> dist (p x) (p t) < cmod (p t - \<zeta>)"
        using \<open>path p\<close> t unfolding path_def continuous_on_iff
        by (metis \<open>p t \<noteq> \<zeta>\<close> right_minus_eq zero_less_norm_iff)
      have "((\<lambda>x. winding_number (\<lambda>w. subpath 0 x p w - \<zeta>) 0 -
                  winding_number (\<lambda>w. subpath 0 t p w - \<zeta>) 0) \<longlongrightarrow> 0)
            (at t within {0..1})"
      proof (rule Lim_transform_within [OF _ \<open>d > 0\<close>])
        have "continuous (at t within {0..1}) (g o p)"
        proof (rule continuous_within_compose)
          show "continuous (at t within {0..1}) p"
            using \<open>path p\<close> continuous_on_eq_continuous_within path_def that by blast
          show "continuous (at (p t) within p ` {0..1}) g"
            by (metis (no_types, lifting) open_ball UNIV_I \<open>p t \<noteq> \<zeta>\<close> centre_in_ball contg continuous_on_eq_continuous_at continuous_within_topological right_minus_eq zero_less_norm_iff)
        qed
        with LIM_zero have "((\<lambda>u. (g (subpath t u p 1) - g (subpath t u p 0))) \<longlongrightarrow> 0) (at t within {0..1})"
          by (auto simp: subpath_def continuous_within o_def)
        then show "((\<lambda>u.  (g (subpath t u p 1) - g (subpath t u p 0)) / (2 * of_real pi * \<i>)) \<longlongrightarrow> 0)
           (at t within {0..1})"
          by (simp add: tendsto_divide_zero)
        show "(g (subpath t u p 1) - g (subpath t u p 0)) / (2 * of_real pi * \<i>) =
              winding_number (\<lambda>w. subpath 0 u p w - \<zeta>) 0 - winding_number (\<lambda>w. subpath 0 t p w - \<zeta>) 0"
          if "u \<in> {0..1}" "0 < dist u t" "dist u t < d" for u
        proof -
          have "closed_segment t u \<subseteq> {0..1}"
            using closed_segment_eq_real_ivl t that by auto
          then have piB: "path_image(subpath t u p) \<subseteq> ?B"
            apply (clarsimp simp add: path_image_subpath_gen)
            by (metis subsetD le_less_trans \<open>dist u t < d\<close> d dist_commute dist_in_closed_segment)
          have *: "path (g \<circ> subpath t u p)"
            apply (rule path_continuous_image)
            using \<open>path p\<close> t that apply auto[1]
            using piB contg continuous_on_subset by blast
          have "(g (subpath t u p 1) - g (subpath t u p 0)) / (2 * of_real pi * \<i>)
              =  winding_number (exp \<circ> g \<circ> subpath t u p) 0"
            using winding_number_compose_exp [OF *]
            by (simp add: pathfinish_def pathstart_def o_assoc)
          also have "... = winding_number (\<lambda>w. subpath t u p w - \<zeta>) 0"
          proof (rule winding_number_cong)
            have "exp(g y) = y - \<zeta>" if "y \<in> (subpath t u p) ` {0..1}" for y
              by (metis that geq path_image_def piB subset_eq)
            then show "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> (exp \<circ> g \<circ> subpath t u p) x = subpath t u p x - \<zeta>"
              by auto
          qed
          also have "... = winding_number (\<lambda>w. subpath 0 u p w - \<zeta>) 0 -
                           winding_number (\<lambda>w. subpath 0 t p w - \<zeta>) 0"
            apply (simp add: winding_number_offset [symmetric])
            using winding_number_subpath_combine [OF \<open>path p\<close> \<zeta>, of 0 t u] \<open>t \<in> {0..1}\<close> \<open>u \<in> {0..1}\<close>
            by (simp add: add.commute eq_diff_eq)
          finally show ?thesis .
        qed
      qed
      then show ?thesis
        by (subst winding_number_offset) (simp add: continuous_within LIM_zero_iff)
    qed
    show "path ?q"
      unfolding path_def
      by (intro continuous_intros) (simp add: continuous_on_eq_continuous_within *)

    have "\<zeta> \<noteq> p 0"
      by (metis \<zeta> pathstart_def pathstart_in_path_image)
    then show "pathfinish ?q - pathstart ?q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
      by (simp add: pathfinish_def pathstart_def)
    show "p t = \<zeta> + exp (?q t)" if "t \<in> {0..1}" for t
    proof -
      have "path (subpath 0 t p)"
        using \<open>path p\<close> that by auto
      moreover
      have "\<zeta> \<notin> path_image (subpath 0 t p)"
        using \<zeta> [unfolded path_image_def] that by (auto simp: path_image_subpath)
      ultimately show ?thesis
        using winding_number_exp_2pi [of "subpath 0 t p" \<zeta>] \<open>\<zeta> \<noteq> p 0\<close>
        by (auto simp: exp_add algebra_simps pathfinish_def pathstart_def subpath_def)
    qed
  qed
qed

subsection \<open>Winding number equality is the same as path/loop homotopy in C - {0}\<close>

lemma winding_number_homotopic_loops_null_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> (\<exists>a. homotopic_loops (-{\<zeta>}) p (\<lambda>t. a))"
    (is "?lhs = ?rhs")
proof
  assume [simp]: ?lhs
  obtain q where "path q"
             and qeq:  "pathfinish q - pathstart q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
             and peq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = \<zeta> + exp(q t)"
    using winding_number_as_continuous_log [OF assms] by blast
  have *: "homotopic_with_canon (\<lambda>r. pathfinish r = pathstart r)
                       {0..1} (-{\<zeta>}) ((\<lambda>w. \<zeta> + exp w) \<circ> q) ((\<lambda>w. \<zeta> + exp w) \<circ> (\<lambda>t. 0))"
  proof (rule homotopic_with_compose_continuous_left)
    show "homotopic_with_canon (\<lambda>f. pathfinish ((\<lambda>w. \<zeta> + exp w) \<circ> f) = pathstart ((\<lambda>w. \<zeta> + exp w) \<circ> f))
              {0..1} UNIV q (\<lambda>t. 0)"
    proof (rule homotopic_with_mono, simp_all add: pathfinish_def pathstart_def)
      have "homotopic_loops UNIV q (\<lambda>t. 0)"
        by (rule homotopic_loops_linear) (use qeq \<open>path q\<close> in \<open>auto simp: path_defs\<close>)
      then have "homotopic_with (\<lambda>r. r 1 = r 0) (top_of_set {0..1}) euclidean q (\<lambda>t. 0)"
        by (simp add: homotopic_loops_def pathfinish_def pathstart_def)
      then show "homotopic_with (\<lambda>h. exp (h 1) = exp (h 0)) (top_of_set {0..1}) euclidean q (\<lambda>t. 0)"
        by (rule homotopic_with_mono) simp
    qed
    show "continuous_on UNIV (\<lambda>w. \<zeta> + exp w)"
      by (rule continuous_intros)+
    show "range (\<lambda>w. \<zeta> + exp w) \<subseteq> -{\<zeta>}"
      by auto
  qed
  then have "homotopic_with_canon (\<lambda>r. pathfinish r = pathstart r) {0..1} (-{\<zeta>}) p (\<lambda>x. \<zeta> + 1)"
    by (rule homotopic_with_eq) (auto simp: o_def peq pathfinish_def pathstart_def)
  then have "homotopic_loops (-{\<zeta>}) p (\<lambda>t. \<zeta> + 1)"
    by (simp add: homotopic_loops_def)
  then show ?rhs ..
next
  assume ?rhs
  then obtain a where "homotopic_loops (-{\<zeta>}) p (\<lambda>t. a)" ..
  then have "winding_number p \<zeta> = winding_number (\<lambda>t. a) \<zeta>" "a \<noteq> \<zeta>"
    using winding_number_homotopic_loops homotopic_loops_imp_subset by (force simp:)+
  moreover have "winding_number (\<lambda>t. a) \<zeta> = 0"
    by (metis winding_number_zero_const \<open>a \<noteq> \<zeta>\<close>)
  ultimately show ?lhs by metis
qed

lemma winding_number_homotopic_paths_null_explicit_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> homotopic_paths (-{\<zeta>}) p (linepath (pathstart p) (pathstart p))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (auto simp: winding_number_homotopic_loops_null_eq [OF assms])
    apply (rule homotopic_loops_imp_homotopic_paths_null)
    apply (simp add: linepath_refl)
    done
next
  assume ?rhs
  then show ?lhs
    by (metis \<zeta> pathstart_in_path_image winding_number_homotopic_paths winding_number_trivial)
qed

lemma winding_number_homotopic_paths_null_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> (\<exists>a. homotopic_paths (-{\<zeta>}) p (\<lambda>t. a))"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: winding_number_homotopic_paths_null_explicit_eq [OF assms] linepath_refl)
next
  assume ?rhs
  then show ?lhs
    by (metis \<zeta> homotopic_paths_imp_pathfinish pathfinish_def pathfinish_in_path_image winding_number_homotopic_paths winding_number_zero_const)
qed

proposition winding_number_homotopic_paths_eq:
  assumes "path p" and \<zeta>p: "\<zeta> \<notin> path_image p"
      and "path q" and \<zeta>q: "\<zeta> \<notin> path_image q"
      and qp: "pathstart q = pathstart p" "pathfinish q = pathfinish p"
    shows "winding_number p \<zeta> = winding_number q \<zeta> \<longleftrightarrow> homotopic_paths (-{\<zeta>}) p q"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "winding_number (p +++ reversepath q) \<zeta> = 0"
    using assms by (simp add: winding_number_join winding_number_reversepath)
  moreover
  have "path (p +++ reversepath q)" "\<zeta> \<notin> path_image (p +++ reversepath q)"
    using assms by (auto simp: not_in_path_image_join)
  ultimately obtain a where "homotopic_paths (- {\<zeta>}) (p +++ reversepath q) (linepath a a)"
    using winding_number_homotopic_paths_null_explicit_eq by blast
  then show ?rhs
    using homotopic_paths_imp_pathstart assms
    by (fastforce simp add: dest: homotopic_paths_imp_homotopic_loops homotopic_paths_loop_parts)
next
  assume ?rhs
  then show ?lhs
    by (simp add: winding_number_homotopic_paths)
qed

lemma winding_number_homotopic_loops_eq:
  assumes "path p" and \<zeta>p: "\<zeta> \<notin> path_image p"
      and "path q" and \<zeta>q: "\<zeta> \<notin> path_image q"
      and loops: "pathfinish p = pathstart p" "pathfinish q = pathstart q"
    shows "winding_number p \<zeta> = winding_number q \<zeta> \<longleftrightarrow> homotopic_loops (-{\<zeta>}) p q"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have "pathstart p \<noteq> \<zeta>" "pathstart q \<noteq> \<zeta>"
    using \<zeta>p \<zeta>q by blast+
  moreover have "path_connected (-{\<zeta>})"
    by (simp add: path_connected_punctured_universe)
  ultimately obtain r where "path r" and rim: "path_image r \<subseteq> -{\<zeta>}"
                        and pas: "pathstart r = pathstart p" and paf: "pathfinish r = pathstart q"
    by (auto simp: path_connected_def)
  then have "pathstart r \<noteq> \<zeta>" by blast
  have "homotopic_loops (- {\<zeta>}) p (r +++ q +++ reversepath r)"
  proof (rule homotopic_paths_imp_homotopic_loops)
    show "homotopic_paths (- {\<zeta>}) p (r +++ q +++ reversepath r)"
      by (metis (mono_tags, opaque_lifting) \<open>path r\<close> L \<zeta>p \<zeta>q \<open>path p\<close> \<open>path q\<close> homotopic_loops_conjugate loops not_in_path_image_join paf pas path_image_reversepath path_imp_reversepath path_join_eq pathfinish_join pathfinish_reversepath  pathstart_join pathstart_reversepath rim subset_Compl_singleton winding_number_homotopic_loops winding_number_homotopic_paths_eq)
  qed (use loops pas in auto)
  moreover have "homotopic_loops (- {\<zeta>}) (r +++ q +++ reversepath r) q"
    using rim \<zeta>q by (auto simp: homotopic_loops_conjugate paf \<open>path q\<close> \<open>path r\<close> loops)
  ultimately show ?rhs
    using homotopic_loops_trans by metis
next
  assume ?rhs
  then show ?lhs
    by (simp add: winding_number_homotopic_loops)
qed

end
