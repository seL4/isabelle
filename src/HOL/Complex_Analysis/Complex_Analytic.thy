section \<open>Complex Analyticity and the Complexification of Real-Analytic Functions\<close>

text \<open>
  Connections with complex analysis: a Cauchy--Riemann criterion for holomorphy;
  holomorphic functions are \<open>C\<^sup>\<infinity>\<close>; and a real function is real-analytic at a point iff
  it extends holomorphically to a complex ball around that point.
\<close>

theory Complex_Analytic
  imports "HOL-Analysis.Real_Analytic" Cauchy_Integral_Formula
begin

subsection \<open>A CR-linear self-map of the plane is multiplication by a scalar\<close>

definition CR_linear :: "(complex \<Rightarrow> complex) \<Rightarrow> bool" where
  "CR_linear L \<longleftrightarrow> bounded_linear L \<and> (\<forall>v. L (\<i> * v) = \<i> * L v)"

lemma CR_linear_is_mult:
  assumes "CR_linear L"
  shows "\<exists>a. \<forall>v. L v = a * v"
proof -
  from assms have bl: "bounded_linear L" and cr: "\<And>v. L (\<i> * v) = \<i> * L v"
    by (auto simp: CR_linear_def)
  interpret bounded_linear L by (rule bl)
  have Lof: "L (complex_of_real r) = complex_of_real r * L 1" for r
  proof -
    have "L (complex_of_real r) = L (r *\<^sub>R 1)"
      by (simp add: scaleR_conv_of_real)
    also have "\<dots> = r *\<^sub>R L 1"
      by (rule scaleR)
    also have "\<dots> = complex_of_real r * L 1"
      by (simp add: scaleR_conv_of_real)
    finally show ?thesis .
  qed
  have "L v = L 1 * v" for v
  proof -
    have decomp: "v = complex_of_real (Re v) + \<i> * complex_of_real (Im v)"
      by (simp add: complex_eq_iff)
    have "L v = L (complex_of_real (Re v) + \<i> * complex_of_real (Im v))"
      using decomp by simp
    also have "\<dots> = L (complex_of_real (Re v)) + L (\<i> * complex_of_real (Im v))"
      by (rule add)
    also have "\<dots> = L (complex_of_real (Re v)) + \<i> * L (complex_of_real (Im v))"
      using cr by simp
    also have "\<dots> = complex_of_real (Re v) * L 1 + \<i> * (complex_of_real (Im v) * L 1)"
      by (simp add: Lof)
    also have "\<dots> = L 1 * (complex_of_real (Re v) + \<i> * complex_of_real (Im v))"
      by (simp add: algebra_simps)
    also have "\<dots> = L 1 * v"
      using decomp by simp
    finally show ?thesis .
  qed
  thus ?thesis by blast
qed


subsection \<open>Several-variable Cauchy--Riemann criterion\<close>

theorem CauchyRiemann_imp_holomorphic:
  fixes f :: "complex \<Rightarrow> complex"
  assumes Sopen: "open S"
    and diff: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative (L x)) (at x)"
    and CR:   "\<And>x. x \<in> S \<Longrightarrow> CR_linear (L x)"
  shows "f holomorphic_on S"
proof -
  have "f field_differentiable (at x)" if xS: "x \<in> S" for x
  proof -
    from CR[OF xS] obtain a where a: "\<And>v. L x v = a * v"
      using CR_linear_is_mult by blast
    from diff[OF xS] have "(f has_derivative (L x)) (at x)" .
    moreover have "L x = (*) a"
      using a by auto
    ultimately have "(f has_derivative (*) a) (at x)" by simp
    hence "(f has_field_derivative a) (at x)"
      by (simp add: has_field_derivative_def mult.commute)
    thus ?thesis
      using field_differentiable_def by blast
  qed
  thus ?thesis
    using Sopen by (simp add: holomorphic_on_open field_differentiable_def)
qed

text \<open>A constant multiple of a holomorphic function is \<open>C\<^sup>k\<close> at each point, for every \<open>k\<close>.\<close>

lemma holomorphic_const_mult_Ck_at:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "f holomorphic_on U" and "open U" and "x \<in> U"
  shows "Ck_at k (\<lambda>y. c * f y) x"
  using assms
proof (induction k arbitrary: f x c)
  case 0
  have "continuous (at x) (\<lambda>y. c * f y)"
  proof -
    have "continuous_on U f"
      using 0 holomorphic_on_imp_continuous_on by blast
    hence "continuous (at x) f"
      using 0 by (simp add: continuous_on_eq_continuous_at)
    thus ?thesis by (intro continuous_intros)
  qed
  thus ?case by simp
next
  case (Suc k)
  note holf = Suc.prems(1) and openU = Suc.prems(2) and xU = Suc.prems(3)

  \<comment> \<open>The scaled map is holomorphic, hence differentiable on \<open>U\<close>.\<close>
  have holcf: "(\<lambda>y. c * f y) holomorphic_on U"
    using holf by (intro holomorphic_intros)

  \<comment> \<open>(i) Neighbourhood: \<open>Ck_at k\<close> holds throughout \<open>U\<close> by the induction hypothesis.\<close>
  have nbhd: "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k (\<lambda>y. c * f y) y)"
  proof (intro exI[of _ U] conjI ballI)
    fix y assume "y \<in> U"
    show "Ck_at k (\<lambda>z. c * f z) y"
      using Suc.IH[OF holf openU \<open>y \<in> U\<close>] .
  qed (use openU xU in auto)

  \<comment> \<open>(ii) Differentiability at \<open>x\<close>.\<close>
  have diff: "(\<lambda>y. c * f y) differentiable (at x)"
    using holomorphic_imp_differentiable_real[OF holcf openU xU] .

  \<comment> \<open>(iii) The directional derivative map is \<open>C\<^sup>k\<close> at \<open>x\<close>.\<close>
  have derivs: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative (\<lambda>z. c * f z) (at y) v) x"
  proof
    fix v
    \<comment> \<open>On \<open>U\<close> the directional derivative equals \<open>(c * v) * deriv f y\<close>.\<close>
    have eqd: "\<And>y. y \<in> U \<Longrightarrow>
                 frechet_derivative (\<lambda>z. c * f z) (at y) v = (c * v) * deriv f y"
    proof -
      fix y assume yU: "y \<in> U"
      have "frechet_derivative (\<lambda>z. c * f z) (at y) v = deriv (\<lambda>z. c * f z) y * v"
        using frechet_derivative_holomorphic[OF holcf openU yU] by simp
      also have "deriv (\<lambda>z. c * f z) y = c * deriv f y"
        using holf openU yU
        by (simp add: deriv_cmult holomorphic_on_imp_differentiable_at)
      finally show "frechet_derivative (\<lambda>z. c * f z) (at y) v = (c * v) * deriv f y"
        by (simp add: algebra_simps)
    qed
    \<comment> \<open>\<open>deriv f\<close> is holomorphic on \<open>U\<close>, so \<open>(c*v) * deriv f\<close> is \<open>C\<^sup>k\<close> by the IH.\<close>
    have holderiv: "deriv f holomorphic_on U"
      using holf openU by (rule holomorphic_deriv)
    have base: "Ck_at k (\<lambda>y. (c * v) * deriv f y) x"
      using Suc.IH[OF holderiv openU xU] .
    show "Ck_at k (\<lambda>y. frechet_derivative (\<lambda>z. c * f z) (at y) v) x"
      by (rule Ck_at_transfer_open[OF openU xU _ base]) (simp add: eqd)
  qed

  show ?case
    unfolding Ck_at.simps(2)
    using nbhd diff derivs by blast
qed

theorem holomorphic_imp_Cinfinity_on:
  assumes "f holomorphic_on U" and "open U"
  shows "Cinfinity_on f U"
  unfolding Cinfinity_on_def Cinfinity_at_def
proof (intro conjI ballI allI)
  show "open U" by (rule assms(2))
next
  fix x :: complex and k assume xU: "x \<in> U"
  have "Ck_at k (\<lambda>y. 1 * f y) x"
    using holomorphic_const_mult_Ck_at[OF assms(1) assms(2) xU] .
  thus "Ck_at k f x" by simp
qed



subsection \<open>Real analyticity via holomorphic extension\<close>

definition has_holo_extension_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "has_holo_extension_at f c \<longleftrightarrow>
     (\<exists>r>0. \<exists>g. g holomorphic_on ball (complex_of_real c) r
                \<and> (\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow> g (complex_of_real x) = complex_of_real (f x)))"


lemma real_analytic_at_1d_imp_holo_extension:
  fixes f :: "real \<Rightarrow> real"
  assumes "real_analytic_at_1d f c"
  shows "has_holo_extension_at f c"
proof -
  from assms obtain r where r: "0 < r"
    and TS: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow>
              (\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x"
    unfolding real_analytic_at_1d_def by blast
  \<comment> \<open>the complex coefficients (same as the real Taylor coefficients)\<close>
  define b :: "nat \<Rightarrow> complex" where "b = (\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n))"
  \<comment> \<open>the complex sum function on the ball; well-defined by summability\<close>
  define g :: "complex \<Rightarrow> complex" where
    "g = (\<lambda>w. \<Sum>n. b n * (w - complex_of_real c) ^ n)"
  \<comment> \<open>The complex power series is summable at every complex point of the ball.\<close>
  have summ_complex: "summable (\<lambda>n. b n * (w - complex_of_real c) ^ n)"
    if w: "w \<in> ball (complex_of_real c) r" for w
  proof -
    have nw: "norm (w - complex_of_real c) < r"
      using w by (simp add: dist_norm norm_minus_commute)
    \<comment> \<open>pick an intermediate real radius @{term s}\<close>
    define s where "s = (norm (w - complex_of_real c) + r) / 2"
    have s_pos: "0 < s"
    proof -
      have "0 < norm (w - complex_of_real c) + r"
        using r norm_ge_zero[of "w - complex_of_real c"] by linarith
      thus ?thesis by (simp add: s_def)
    qed
    have s_lt_r: "s < r" using nw by (simp add: s_def)
    have nw_lt_s: "norm (w - complex_of_real c) < s"
      using nw by (simp add: s_def)
    \<comment> \<open>real series converges at @{term "c + s"}, since @{term "\<bar>s\<bar> < r"}\<close>
    have "\<bar>(c + s) - c\<bar> < r" using s_pos s_lt_r by simp
    from TS[OF this] have realsum:
      "summable (\<lambda>n. (deriv ^^ n) f c / fact n * ((c + s) - c) ^ n)"
      by (rule sums_summable)
    have realsum': "summable (\<lambda>n. (deriv ^^ n) f c / fact n * s ^ n)"
      using realsum by simp
    \<comment> \<open>cast to complex: @{term "b n * (of_real s)^n"} is summable\<close>
    have cast: "summable (\<lambda>n. b n * (complex_of_real s) ^ n)"
    proof -
      have "(\<lambda>n. of_real ((deriv ^^ n) f c / fact n * s ^ n) :: complex)
              = (\<lambda>n. b n * (complex_of_real s) ^ n)"
        by (simp only: b_def of_real_mult of_real_power)
      moreover have "summable (\<lambda>n. of_real ((deriv ^^ n) f c / fact n * s ^ n) :: complex)"
        using realsum' by (rule summable_of_real)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>\<open>powser_inside\<close> upgrades to summability strictly inside\<close>
    have "norm (w - complex_of_real c) < norm (complex_of_real s)"
      using nw_lt_s s_pos by simp
    from powser_inside[OF cast this]
    show ?thesis .
  qed
  \<comment> \<open>hence at each ball point the series sums to @{term "g w"}\<close>
  have sums_g: "(\<lambda>n. b n * (w - complex_of_real c) ^ n) sums g w"
    if w: "w \<in> ball (complex_of_real c) r" for w
    using summ_complex[OF w] by (simp add: g_def summable_sums)
  \<comment> \<open>holomorphy from \<open>power_series_holomorphic\<close>\<close>
  have holo: "g holomorphic_on ball (complex_of_real c) r"
  proof (rule power_series_holomorphic)
    fix w :: complex assume "w \<in> ball (complex_of_real c) r"
    thus "(\<lambda>n. b n * (w - complex_of_real c) ^ n) sums g w"
      by (rule sums_g)
  qed
  \<comment> \<open>on the real axis, the series sums to @{term "of_real (f x)"}\<close>
  have realaxis: "g (complex_of_real x) = complex_of_real (f x)"
    if x: "\<bar>x - c\<bar> < r" for x
  proof -
    have wball: "complex_of_real x \<in> ball (complex_of_real c) r"
      using x by (simp add: dist_norm norm_minus_commute flip: of_real_diff)
    have "(\<lambda>n. b n * (complex_of_real x - complex_of_real c) ^ n) sums g (complex_of_real x)"
      by (rule sums_g[OF wball])
    moreover have
      "(\<lambda>n. b n * (complex_of_real x - complex_of_real c) ^ n)
         = (\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n * (x - c) ^ n))"
      by (simp only: b_def of_real_mult of_real_power flip: of_real_diff)
    ultimately have
      "(\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n * (x - c) ^ n))
         sums g (complex_of_real x)" by simp
    moreover have
      "(\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n * (x - c) ^ n))
         sums complex_of_real (f x)"
      using TS[OF x] by (rule sums_of_real)
    ultimately show ?thesis by (rule sums_unique2)
  qed
  show ?thesis
    unfolding has_holo_extension_at_def
    using r holo realaxis by blast
qed


text \<open>A real function with a holomorphic extension around \<open>c\<close> is real-analytic
  at \<open>c\<close>.\<close>

lemma holo_extension_imp_real_analytic_at_1d:
  fixes f :: "real \<Rightarrow> real"
  assumes "has_holo_extension_at f c"
  shows "real_analytic_at_1d f c"
proof -
  from assms obtain r g where r: "0 < r"
    and holo: "g holomorphic_on ball (complex_of_real c) r"
    and onaxis: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow> g (complex_of_real x) = complex_of_real (f x)"
    unfolding has_holo_extension_at_def by blast
  \<comment> \<open>the real coefficients are the real parts of the complex Taylor coefficients\<close>
  define A :: "nat \<Rightarrow> complex" where
    "A = (\<lambda>n. (deriv ^^ n) g (complex_of_real c) / fact n)"
  define a :: "nat \<Rightarrow> real" where "a = (\<lambda>n. Re (A n))"
  \<comment> \<open>the real power series with coefficients @{term a} sums to @{term "f x"} on the ball\<close>
  have PS: "(\<lambda>n. a n * (x - c) ^ n) sums f x" if x: "\<bar>x - c\<bar> < r" for x
  proof -
    have wball: "complex_of_real x \<in> ball (complex_of_real c) r"
      using x by (simp add: dist_norm norm_minus_commute flip: of_real_diff)
    \<comment> \<open>complex Taylor series of @{term g} at the real point\<close>
    have cseries: "(\<lambda>n. A n * (complex_of_real x - complex_of_real c) ^ n)
                     sums g (complex_of_real x)"
      unfolding A_def by (rule holomorphic_power_series[OF holo wball])
    have eqf: "g (complex_of_real x) = complex_of_real (f x)" by (rule onaxis[OF x])
    \<comment> \<open>rewrite the complex terms and take real parts\<close>
    have term_eq: "A n * (complex_of_real x - complex_of_real c) ^ n
                     = complex_of_real (a n * (x - c) ^ n)
                       + \<i> * complex_of_real (Im (A n) * (x - c) ^ n)" for n
    proof -
      have pw: "(complex_of_real x - complex_of_real c) ^ n
                  = complex_of_real ((x - c) ^ n)"
        by (simp flip: of_real_diff of_real_power)
      have "A n * (complex_of_real x - complex_of_real c) ^ n
              = A n * complex_of_real ((x - c) ^ n)" by (simp only: pw)
      also have "\<dots> = complex_of_real (Re (A n) * (x - c) ^ n)
                       + \<i> * complex_of_real (Im (A n) * (x - c) ^ n)"
        by (simp add: complex_eq_iff)
      finally show ?thesis by (simp add: a_def)
    qed
    have cseries': "(\<lambda>n. complex_of_real (a n * (x - c) ^ n)
                          + \<i> * complex_of_real (Im (A n) * (x - c) ^ n))
                      sums complex_of_real (f x)"
      using cseries by (simp add: term_eq eqf)
    \<comment> \<open>take real parts\<close>
    have "(\<lambda>n. Re (complex_of_real (a n * (x - c) ^ n)
                   + \<i> * complex_of_real (Im (A n) * (x - c) ^ n)))
            sums Re (complex_of_real (f x))"
      by (rule sums_Re[OF cseries'])
    thus ?thesis by simp
  qed
  show ?thesis by (rule real_powser_imp_real_analytic_at_1d[OF r PS])
qed


theorem real_analytic_at_1d_iff_holo_extension:
  fixes f :: "real \<Rightarrow> real"
  shows "real_analytic_at_1d f c \<longleftrightarrow> has_holo_extension_at f c"
  using real_analytic_at_1d_imp_holo_extension holo_extension_imp_real_analytic_at_1d
  by blast

end
