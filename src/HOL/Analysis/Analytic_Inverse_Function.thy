section \<open>The real-analytic inverse function theorem\<close>

text \<open>
  A real-analytic map between Euclidean spaces whose derivative at a point is bijective has
  a real-analytic local inverse.  The \<open>C\<^sup>1\<close> inverse function theorem of HOL-Analysis
  provides the inverse; the majorant method of \<open>Real_Analytic_Inverse\<close> shows that it is
  real-analytic.
\<close>

theory Analytic_Inverse_Function
  imports Real_Analytic_Inverse Ck_Implicit_Function
begin

subsection \<open>The \<open>C\<^sup>1\<close> inverse function theorem, with derivative data\<close>

text \<open>Local inverse data for a real-analytic map, from @{thm [source] inverse_function_theorem}.\<close>

lemma real_analytic_C1_local_inverse_data:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
proof -
  have Cinf: "Cinfinity_on f U"
    by (rule real_analytic_imp_Cinfinity[OF ana])
  have C1: "Ck_on (Suc 0) f U"
    by (rule Cinfinity_on_imp_Ck_on[OF Cinf])
  have derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative blinfun_apply (Dblinfun f x)) (at x)"
    by (rule Ck1_on_imp_has_derivative_blinfun[OF C1])
  have contf: "continuous_on U (Dblinfun f)"
    by (rule Ck1_on_imp_continuous_Dblinfun[OF C1])

  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  have d0: "(f has_derivative blinfun_apply (Dblinfun f x0)) (at x0)"
    using derf x0 by blast
  have D_eq: "blinfun_apply (Dblinfun f x0) = L"
    by (rule has_derivative_unique[OF d0 Lder])
  have blL: "bounded_linear L"
    by (rule has_derivative_bounded_linear[OF Lder])
  have injL: "inj L"
    using bijL by (simp add: bij_def)
  have bl_invL: "bounded_linear (inv L)"
    by (rule inj_linear_imp_inv_bounded_linear[OF blL injL])
  define invf :: "'a \<Rightarrow>\<^sub>L 'a" where "invf = Blinfun (inv L)"
  have invf_apply: "blinfun_apply invf = inv L"
    unfolding invf_def by (rule bounded_linear_Blinfun_apply[OF bl_invL])
  have invf_id: "invf o\<^sub>L Dblinfun f x0 = id_blinfun"
  proof (rule blinfun_eqI)
    fix h
    show "blinfun_apply (invf o\<^sub>L Dblinfun f x0) h = blinfun_apply id_blinfun h"
      by (simp add: D_eq invf_apply inv_f_f[OF injL])
  qed

  show ?thesis
  proof (rule inverse_function_theorem[OF U derf contf x0 invf_id])
    fix U' V g g'
    assume inv: "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g"
    assume derg: "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative g' y) (at y)"
    assume g'_eq: "\<And>y. y \<in> V \<Longrightarrow> g' y = inv (blinfun_apply (Dblinfun f (g y)))"
    assume bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
    have derg': "\<And>y. y \<in> V \<Longrightarrow>
      (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
      using derg g'_eq by simp
    show thesis
      by (rule that[of U' V g, OF inv(1) inv(3) inv(2) inv(4) inv(5) inv(6) derg' bijg])
  qed
qed


subsection \<open>Derivatives of real-analytic maps\<close>

lemma real_analytic_on_has_derivative_Dblinfun:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ana: "real_analytic_on f U"
    and xU: "x \<in> U"
  shows "(f has_derivative blinfun_apply (Dblinfun f x)) (at x)"
proof -
  from ana xU obtain r c where r0: "0 < r"
    and ser: "\<And>y. dist y x < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum f y) ra_idx"
    unfolding real_analytic_on_def by blast
  define D where "D = (\<lambda>v. infsum
    (\<lambda>\<alpha>. ra_Dmonomial (x - x) \<alpha> v *\<^sub>R c \<alpha>) ra_idx)"
  have xdist: "dist x x < r"
    using r0 by simp
  have derD: "(f has_derivative D) (at x)"
    unfolding D_def
    by (rule ra_power_series_has_derivative[OF r0 ser xdist])
  have diff: "f differentiable (at x)"
    using derD unfolding differentiable_def by blast
  have D_eq: "D = frechet_derivative f (at x)"
    by (rule frechet_derivative_at[OF derD])
  show ?thesis
    using derD diff by (simp add: D_eq blinfun_apply_Dblinfun)
qed


subsection \<open>Upgrading the \<open>C\<^sup>1\<close> local inverse to real-analytic\<close>

lemma real_analytic_C1_inverse_upgrade_normalized:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
    and U'_open: "open U'"
    and zero_U': "0 \<in> U'"
    and U'_sub: "U' \<subseteq> U"
    and V_open: "open V"
    and zero_V: "0 \<in> V"
    and homeo: "homeomorphism U' V f g"
    and derg: "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    and bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
  shows "real_analytic_on g V"
  \<comment> \<open>Near each \<open>y0 \<in> V\<close>, \<open>g\<close> agrees with the analytic right inverse of the
      normalised map.\<close>
proof (rule real_analytic_on_locality[OF V_open])
  fix y0 :: 'a assume y0V: "y0 \<in> V"
  \<comment> \<open>Base point and its derivative data.\<close>
  define x0 where "x0 = g y0"
  have x0U': "x0 \<in> U'"
    using homeomorphism_image2[OF homeo] y0V by (auto simp: x0_def)
  have x0U: "x0 \<in> U" using x0U' U'_sub by blast
  have fx0: "f x0 = y0"
    using homeomorphism_apply2[OF homeo y0V] by (simp add: x0_def)
  define Dap where "Dap = blinfun_apply (Dblinfun f x0)"
  have der: "(f has_derivative Dap) (at x0)"
    unfolding Dap_def by (rule real_analytic_on_has_derivative_Dblinfun[OF ana x0U])
  have bijDap: "bij Dap"
    using bijg[OF y0V] by (simp add: Dap_def x0_def)
  have injDap: "inj Dap" using bijDap by (simp add: bij_def)
  have surjDap: "surj Dap" using bijDap by (simp add: bij_def)
  have blDap: "bounded_linear Dap"
    by (rule has_derivative_bounded_linear[OF der])
  define Dinv where "Dinv = inv Dap"
  have bl_Dinv: "bounded_linear Dinv"
    unfolding Dinv_def by (rule inj_linear_imp_inv_bounded_linear[OF blDap injDap])
  interpret Dinv: bounded_linear Dinv by (rule bl_Dinv)
  have Dinv_D: "Dinv (Dap u) = u" for u
    by (simp add: Dinv_def inv_f_f[OF injDap])
  have D_Dinv: "Dap (Dinv z) = z" for z
    by (simp add: Dinv_def surj_f_inv_f[OF surjDap])
  have Dinv0: "Dinv 0 = 0" by (rule Dinv.zero)
  \<comment> \<open>The normalised map \<open>ftil u = Dinv (f (x0 + u) - y0)\<close>, analytic near \<open>0\<close>.\<close>
  define ftil where "ftil = (\<lambda>u. Dinv (f (x0 + u) - y0))"
  obtain \<delta>0 where \<delta>0: "0 < \<delta>0" and ballU: "ball x0 \<delta>0 \<subseteq> U"
    using U x0U by (metis open_contains_ball)
  define W0 where "W0 = ball (0::'a) \<delta>0"
  have openW0: "open W0" by (simp add: W0_def)
  have zeroW0: "0 \<in> W0" using \<delta>0 by (simp add: W0_def)
  have shift_ana: "real_analytic_on (\<lambda>u. x0 + u) W0"
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF openW0]
        real_analytic_on_bounded_linear[OF openW0 bounded_linear_ident]])
  have shift_img: "(\<lambda>u. x0 + u) ` W0 \<subseteq> U"
  proof
    fix z assume "z \<in> (\<lambda>u. x0 + u) ` W0"
    then obtain u where u: "u \<in> W0" and z: "z = x0 + u" by blast
    have "norm u < \<delta>0" using u by (simp add: W0_def dist_norm)
    hence "dist z x0 < \<delta>0" by (simp add: z dist_norm)
    thus "z \<in> U" using ballU by (auto simp: mem_ball dist_commute)
  qed
  have fshift_ana: "real_analytic_on (\<lambda>u. f (x0 + u)) W0"
    by (rule real_analytic_on_compose[OF shift_ana ana shift_img])
  have fshift_diff: "real_analytic_on (\<lambda>u. f (x0 + u) - y0) W0"
    by (rule real_analytic_on_diff[OF fshift_ana real_analytic_on_const[OF openW0]])
  have Dinv_ana: "real_analytic_on Dinv (UNIV::'a set)"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV bl_Dinv])
  have ftil_ana: "real_analytic_on ftil W0"
    unfolding ftil_def
    by (rule real_analytic_on_compose[OF fshift_diff Dinv_ana subset_UNIV])
  have ftil0: "ftil 0 = 0"
    by (simp add: ftil_def fx0 Dinv0)
  \<comment> \<open>The derivative of \<open>ftil\<close> at \<open>0\<close> is the identity.\<close>
  have sh_der: "((+) x0 has_derivative (\<lambda>x. x)) (at 0)"
    by (rule shift_has_derivative_id)
  have der': "(f has_derivative Dap) (at ((+) x0 0))" using der by simp
  have comp1: "((f \<circ> (+) x0) has_derivative (Dap \<circ> (\<lambda>x. x))) (at 0)"
    by (rule diff_chain_at[OF sh_der der'])
  have step1: "((\<lambda>u. f (x0 + u)) has_derivative Dap) (at 0)"
    using comp1 by (simp add: comp_def)
  have step2: "((\<lambda>u. f (x0 + u) - y0) has_derivative Dap) (at 0)"
  proof -
    have "((\<lambda>u. f (x0 + u) - y0) has_derivative (\<lambda>h. Dap h - 0)) (at 0)"
      by (rule has_derivative_diff[OF step1 has_derivative_const])
    thus ?thesis by simp
  qed
  have step3: "(ftil has_derivative (\<lambda>h. Dinv (Dap h))) (at 0)"
    unfolding ftil_def
    by (rule bounded_linear.has_derivative[OF bl_Dinv step2])
  have ftil_der: "(ftil has_derivative id) (at 0)"
  proof -
    have "(\<lambda>h. Dinv (Dap h)) = id" by (rule ext) (simp add: Dinv_D)
    with step3 show ?thesis by simp
  qed
  \<comment> \<open>Analytic formal right inverse \<open>Hfun\<close> of the normalised map.\<close>
  obtain \<sigma> bphi where \<sigma>0: "0 < \<sigma>"
    and Hana: "real_analytic_on
        (\<lambda>h. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) (ball (0::'a) (\<sigma> / 2))"
    and Hsum: "\<And>h. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)) (ra_idx::('a \<Rightarrow> nat) set)"
    and Hinv: "\<And>h. norm h < \<sigma> \<Longrightarrow>
        ftil (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) = h"
  proof (rule normalized_analytic_formal_right_inverse[OF ftil_ana zeroW0 ftil0 ftil_der])
    fix s :: real and bp :: "('a \<Rightarrow> nat) \<Rightarrow> 'a"
    assume A1: "0 < s"
      and A2: "real_analytic_on
          (\<lambda>h. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bp \<gamma>) (ball (0::'a) (s / 2))"
      and A3: "\<And>h. norm h < s \<Longrightarrow>
          ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bp \<gamma>)
            has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bp \<gamma>)) (ra_idx::('a \<Rightarrow> nat) set)"
      and A4: "\<And>h. norm h < s \<Longrightarrow>
          ftil (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bp \<gamma>) = h"
    show thesis by (rule that[OF A1 A2 A3 A4])
  qed
  define Hfun :: "'a \<Rightarrow> 'a" where
    "Hfun = (\<lambda>h. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)"
  have Hana': "real_analytic_on Hfun (ball (0::'a) (\<sigma> / 2))"
    using Hana by (simp only: Hfun_def)
  have Hsum': "\<And>h. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) has_sum Hfun h) (ra_idx::('a \<Rightarrow> nat) set)"
    using Hsum by (simp only: Hfun_def)
  have Hinv': "\<And>h. norm h < \<sigma> \<Longrightarrow> ftil (Hfun h) = h"
    using Hinv by (simp only: Hfun_def)
  have H0: "Hfun 0 = 0"
  proof -
    have n0: "norm (0::'a) < \<sigma>" using \<sigma>0 by simp
    have "((\<lambda>\<gamma>. ra_monomial (0::'a) \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) has_sum Hfun 0)
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule Hsum'[OF n0])
    hence "ra_inverse_coeffs bphi ra_idx_zero = Hfun 0"
      by (rule ra_series_at_zero_coeff)
    thus ?thesis by (simp add: ra_inverse_coeffs_idx_zero)
  qed
  \<comment> \<open>Affine change of variable \<open>Lfun y = Dinv (y - y0)\<close> and the domain \<open>W2\<close>.\<close>
  define Lfun where "Lfun = (\<lambda>y. Dinv (y - y0))"
  have Lfun_y0: "Lfun y0 = 0" by (simp add: Lfun_def Dinv0)
  have Lfun_ana: "real_analytic_on Lfun (UNIV::'a set)"
    unfolding Lfun_def
    by (rule real_analytic_on_compose[OF
        real_analytic_on_diff[OF
          real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_ident]
          real_analytic_on_const[OF open_UNIV]]
        Dinv_ana subset_UNIV])
  obtain K where K0: "0 < K" and Kbound: "\<And>z. norm (Dinv z) \<le> norm z * K"
    using Dinv.pos_bounded by blast
  define \<epsilon>2 where "\<epsilon>2 = (\<sigma> / 2) / K"
  have \<epsilon>20: "0 < \<epsilon>2" using \<sigma>0 K0 by (simp add: \<epsilon>2_def)
  define W2 where "W2 = ball y0 \<epsilon>2"
  have openW2: "open W2" by (simp add: W2_def)
  have y0W2: "y0 \<in> W2" using \<epsilon>20 by (simp add: W2_def)
  have Lfun_small: "norm (Lfun y) < \<sigma> / 2" if yW2: "y \<in> W2" for y
  proof -
    have dy: "norm (y - y0) < \<epsilon>2"
      using yW2 by (simp add: W2_def dist_norm norm_minus_commute)
    have "norm (Lfun y) = norm (Dinv (y - y0))" by (simp add: Lfun_def)
    also have "\<dots> \<le> norm (y - y0) * K" by (rule Kbound)
    also have "\<dots> < \<epsilon>2 * K" using mult_strict_right_mono[OF dy K0] .
    also have "\<dots> = \<sigma> / 2" using K0 by (simp add: \<epsilon>2_def)
    finally show ?thesis .
  qed
  have Lfun_img: "Lfun ` W2 \<subseteq> ball (0::'a) (\<sigma> / 2)"
  proof
    fix z assume "z \<in> Lfun ` W2"
    then obtain y where y: "y \<in> W2" and z: "z = Lfun y" by blast
    show "z \<in> ball (0::'a) (\<sigma> / 2)"
      using Lfun_small[OF y] by (simp add: z dist_norm)
  qed
  \<comment> \<open>The candidate analytic inverse \<open>Gfun y = x0 + Hfun (Lfun y)\<close>.\<close>
  define Gfun where "Gfun = (\<lambda>y. x0 + Hfun (Lfun y))"
  have Lfun_ana_W2: "real_analytic_on Lfun W2"
    by (rule real_analytic_on_open_subset[OF Lfun_ana openW2 subset_UNIV])
  have HL_ana: "real_analytic_on (\<lambda>y. Hfun (Lfun y)) W2"
    by (rule real_analytic_on_compose[OF Lfun_ana_W2 Hana' Lfun_img])
  have Gfun_ana: "real_analytic_on Gfun W2"
    unfolding Gfun_def
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF openW2] HL_ana])
  have Gfun_y0: "Gfun y0 = x0"
    by (simp add: Gfun_def Lfun_y0 H0)
  \<comment> \<open>\<open>Gfun\<close> is continuous and maps a neighbourhood of \<open>y0\<close> into \<open>U'\<close>.\<close>
  have contG: "continuous (at y0) Gfun"
    by (rule real_analytic_on_imp_continuous_vec[OF Gfun_ana y0W2])
  have GU'_ev: "eventually (\<lambda>y. Gfun y \<in> U') (at y0)"
  proof (rule topological_tendstoD)
    show "(Gfun \<longlongrightarrow> Gfun y0) (at y0)" using contG by (simp add: continuous_at)
    show "open U'" by (rule U'_open)
    show "Gfun y0 \<in> U'" using Gfun_y0 x0U' by simp
  qed
  obtain \<epsilon>4 where \<epsilon>40: "0 < \<epsilon>4"
    and GU'ball: "\<forall>y. y \<noteq> y0 \<and> dist y y0 < \<epsilon>4 \<longrightarrow> Gfun y \<in> U'"
    using GU'_ev by (auto simp: eventually_at)
  have GU': "Gfun y \<in> U'" if "dist y y0 < \<epsilon>4" for y
  proof (cases "y = y0")
    case True thus ?thesis using Gfun_y0 x0U' by simp
  next
    case False thus ?thesis using GU'ball that by blast
  qed
  \<comment> \<open>The final neighbourhood \<open>W3\<close> on which \<open>g\<close> agrees with \<open>Gfun\<close>.\<close>
  obtain \<epsilon>V where \<epsilon>V0: "0 < \<epsilon>V" and ballV: "ball y0 \<epsilon>V \<subseteq> V"
    using V_open y0V by (metis open_contains_ball)
  define \<epsilon> where "\<epsilon> = min \<epsilon>2 (min \<epsilon>V \<epsilon>4)"
  have \<epsilon>0: "0 < \<epsilon>" using \<epsilon>20 \<epsilon>V0 \<epsilon>40 by (simp add: \<epsilon>_def)
  have e_le2: "\<epsilon> \<le> \<epsilon>2" unfolding \<epsilon>_def by (rule min.cobounded1)
  have e_leV: "\<epsilon> \<le> \<epsilon>V" unfolding \<epsilon>_def
    by (meson min.cobounded1 min.cobounded2 order_trans)
  have e_le4: "\<epsilon> \<le> \<epsilon>4" unfolding \<epsilon>_def
    by (meson min.cobounded2 order_trans)
  define W3 where "W3 = ball y0 \<epsilon>"
  have openW3: "open W3" by (simp add: W3_def)
  have y0W3: "y0 \<in> W3" using \<epsilon>0 by (simp add: W3_def)
  have W3_W2: "W3 \<subseteq> W2" unfolding W3_def W2_def by (rule subset_ball[OF e_le2])
  have W3_V: "W3 \<subseteq> V"
  proof -
    have "W3 \<subseteq> ball y0 \<epsilon>V" unfolding W3_def by (rule subset_ball[OF e_leV])
    thus ?thesis using ballV by blast
  qed
  have eqGg: "g y = Gfun y" if yW3: "y \<in> W3" for y
  proof -
    have dyy0: "dist y y0 < \<epsilon>" using yW3 by (simp add: W3_def dist_commute)
    have yW2: "y \<in> W2" using yW3 W3_W2 by blast
    have Lsmall: "norm (Lfun y) < \<sigma>"
    proof -
      have "norm (Lfun y) < \<sigma> / 2" by (rule Lfun_small[OF yW2])
      also have "\<dots> < \<sigma>" using \<sigma>0 by simp
      finally show ?thesis .
    qed
    have fGy: "f (Gfun y) = y"
    proof -
      have "ftil (Hfun (Lfun y)) = Lfun y" by (rule Hinv'[OF Lsmall])
      hence "Dinv (f (x0 + Hfun (Lfun y)) - y0) = Dinv (y - y0)"
        by (simp add: ftil_def Lfun_def)
      hence "Dap (Dinv (f (x0 + Hfun (Lfun y)) - y0)) = Dap (Dinv (y - y0))"
        by simp
      hence "f (x0 + Hfun (Lfun y)) - y0 = y - y0"
        by (simp add: D_Dinv)
      hence "f (x0 + Hfun (Lfun y)) = y" by simp
      thus ?thesis by (simp add: Gfun_def)
    qed
    have GyU': "Gfun y \<in> U'"
    proof (rule GU')
      show "dist y y0 < \<epsilon>4" using dyy0 e_le4 by linarith
    qed
    have "g (f (Gfun y)) = Gfun y"
      by (rule homeomorphism_apply1[OF homeo GyU'])
    thus "g y = Gfun y" using fGy by simp
  qed
  have "real_analytic_on g W3"
    by (rule real_analytic_on_cong_nbhd[OF Gfun_ana openW3 W3_W2 eqGg])
  thus "\<exists>W. open W \<and> y0 \<in> W \<and> W \<subseteq> V \<and> real_analytic_on g W"
    using openW3 y0W3 W3_V by blast
qed

subsection \<open>The real-analytic local inverse theorem\<close>

theorem real_analytic_local_inverse_normalized:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
  obtains U' V g where
    "open U'" "0 \<in> U'" "U' \<subseteq> U" "open V" "0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
proof -
  have reg: "\<exists>L. (f has_derivative L) (at 0) \<and> bij L"
    using der0 by (intro exI[where x=id]) (simp add: bij_id)
  show ?thesis
  proof (rule real_analytic_C1_local_inverse_data[OF ana U zero_U reg])
    fix U' V g
    assume U'_open: "open U'"
      and zero_U': "0 \<in> U'"
      and U'_sub: "U' \<subseteq> U"
      and V_open: "open V"
      and f0_V: "f 0 \<in> V"
      and homeo: "homeomorphism U' V f g"
      and derg: "\<And>y. y \<in> V \<Longrightarrow>
        (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
      and bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
    have zero_V: "0 \<in> V"
      using f0 f0_V by simp
    have g_ana: "real_analytic_on g V"
      by (rule real_analytic_C1_inverse_upgrade_normalized
          [OF ana U zero_U f0 der0 U'_open zero_U' U'_sub V_open zero_V homeo derg bijg])
    show thesis
      by (rule that[OF U'_open zero_U' U'_sub V_open zero_V homeo g_ana])
  qed
qed

theorem real_analytic_local_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
  \<comment> \<open>Reduce to the normalised case by an affine change of variables.\<close>
proof -
  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  have blL: "bounded_linear L"
    using Lder by (rule has_derivative_bounded_linear)
  have linL: "linear L"
    using blL by (rule bounded_linear.linear)
  have injL: "inj L" and surjL: "surj L"
    using bijL by (auto simp: bij_def)
  have blInvL: "bounded_linear (inv L)"
    by (rule inj_linear_imp_inv_bounded_linear[OF blL injL])
  have linInvL: "linear (inv L)"
    using blInvL by (rule bounded_linear.linear)

  let ?U0 = "(+) (- x0) ` U"
  let ?F = "\<lambda>x. inv L (f (x0 + x) - f x0)"
  have U0_open: "open ?U0"
    using U open_translation by blast
  have zero_U0: "0 \<in> ?U0"
    using x0 by force
  have shift_image: "(\<lambda>x. x0 + x) ` ?U0 \<subseteq> U"
    by auto

  have id_ana: "real_analytic_on (\<lambda>x::'a. x) ?U0"
    by (rule real_analytic_on_bounded_linear[OF U0_open bounded_linear_ident])
  have shift_ana: "real_analytic_on (\<lambda>x::'a. x0 + x) ?U0"
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF U0_open] id_ana])
  have fshift_ana: "real_analytic_on (\<lambda>x. f (x0 + x)) ?U0"
    using real_analytic_on_compose[OF shift_ana ana shift_image] by simp
  have fshift0_ana: "real_analytic_on (\<lambda>x. f (x0 + x) - f x0) ?U0"
    by (rule real_analytic_on_diff[OF fshift_ana real_analytic_on_const[OF U0_open]])
  have invL_ana_UNIV: "real_analytic_on (inv L) UNIV"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV blInvL])
  have F_ana: "real_analytic_on ?F ?U0"
    by (rule real_analytic_on_compose[OF fshift0_ana invL_ana_UNIV]) simp

  have F0: "?F 0 = 0"
    using linInvL by (simp add: linear_0)
  have shift_der: "((\<lambda>x::'a. x0 + x) has_derivative id) (at 0)"
    by (auto intro!: derivative_eq_intros)
  have Lder_shift0: "(f has_derivative L) (at ((\<lambda>x::'a. x0 + x) 0))"
    using Lder by simp
  have fshift_der: "((\<lambda>x. f (x0 + x)) has_derivative L) (at 0)"
    using has_derivative_compose[OF shift_der Lder_shift0] by (simp add: comp_def)
  have const_der: "((\<lambda>x::'a. f x0) has_derivative (\<lambda>h. 0)) (at 0)"
    by (rule has_derivative_const)
  have fshift0_der: "((\<lambda>x. f (x0 + x) - f x0) has_derivative L) (at 0)"
    using has_derivative_diff[OF fshift_der const_der] by simp
  have invL_der:
    "((inv L) has_derivative inv L) (at ((\<lambda>x. f (x0 + x) - f x0) 0))"
    by (rule bounded_linear.has_derivative[OF blInvL has_derivative_ident])
  have F_der_raw: "(?F has_derivative (\<lambda>h. inv L (L h))) (at 0)"
    using has_derivative_compose[OF fshift0_der invL_der] by (simp add: comp_def)
  have invL_L: "inv L (L h) = h" for h
    using injL by (simp add: inv_f_f)
  have F_der: "(?F has_derivative id) (at 0)"
    by (rule has_derivative_eq_rhs[OF F_der_raw]) (simp add: fun_eq_iff invL_L)

  obtain U0' V0 h where U0'_open: "open U0'" and zero_U0': "0 \<in> U0'"
    and U0'_sub: "U0' \<subseteq> ?U0" and V0_open: "open V0" and zero_V0: "0 \<in> V0"
    and homeo0: "homeomorphism U0' V0 ?F h"
    and h_ana: "real_analytic_on h V0"
    by (rule real_analytic_local_inverse_normalized[OF F_ana U0_open zero_U0 F0 F_der]) blast

  define U' where "U' = (+) x0 ` U0'"
  define V where "V = (\<lambda>z. f x0 + L z) ` V0"
  define g where "g = (\<lambda>y. x0 + h (inv L (y - f x0)))"
  let ?S = "\<lambda>y. inv L (y - f x0)"

  have U'_open: "open U'"
    unfolding U'_def using U0'_open open_translation by blast
  have x0_U': "x0 \<in> U'"
    unfolding U'_def using zero_U0' by force
  have U'_sub: "U' \<subseteq> U"
  proof
    fix y assume "y \<in> U'"
    then obtain z where z: "z \<in> U0'" and y: "y = x0 + z"
      unfolding U'_def by blast
    obtain u where u: "u \<in> U" and z_eq: "z = - x0 + u"
      using U0'_sub z by blast
    show "y \<in> U"
      using u y z_eq by simp
  qed
  have L_V0_open: "open (L ` V0)"
    using V0_open linL surjL by (rule open_surjective_linear_image)
  have V_eq: "V = (+) (f x0) ` (L ` V0)"
    unfolding V_def by auto
  have V_open: "open V"
    unfolding V_eq using L_V0_open open_translation by blast
  have fx0_V: "f x0 \<in> V"
    unfolding V_def using zero_V0 linL by (force simp: linear_0)

  have S_V_sub: "?S ` V \<subseteq> V0"
  proof
    fix s assume "s \<in> ?S ` V"
    then obtain y z where z: "z \<in> V0" and y: "y = f x0 + L z"
      and s: "s = ?S y"
      unfolding V_def by blast
    have "s = z"
      using s y injL by (simp add: inv_f_f)
    thus "s \<in> V0"
      using z by simp
  qed

  have f_image: "f ` U' \<subseteq> V"
  proof
    fix y assume "y \<in> f ` U'"
    then obtain x z where z: "z \<in> U0'" and x: "x = x0 + z" and y: "y = f x"
      unfolding U'_def by blast
    have Fz: "?F z \<in> V0"
      using homeomorphism_image1[OF homeo0] z by blast
    have L_Fz: "L (?F z) = f (x0 + z) - f x0"
      using surjL by (simp add: surj_f_inv_f)
    have "f x = f x0 + L (?F z)"
      using x L_Fz by simp
    thus "y \<in> V"
      unfolding V_def using y Fz by blast
  qed

  have g_image: "g ` V \<subseteq> U'"
  proof
    fix y assume "y \<in> g ` V"
    then obtain v z where z: "z \<in> V0" and v: "v = f x0 + L z" and y: "y = g v"
      unfolding V_def by blast
    have hz: "h z \<in> U0'"
      using homeomorphism_image2[OF homeo0] z by blast
    have coord: "?S v = z"
      using v injL by (simp add: inv_f_f)
    have "y = x0 + h z"
      using y coord by (simp add: g_def)
    thus "y \<in> U'"
      unfolding U'_def using hz by blast
  qed

  have gf: "g (f x) = x" if x: "x \<in> U'" for x
  proof -
    obtain z where z: "z \<in> U0'" and xeq: "x = x0 + z"
      using x unfolding U'_def by blast
    have "g (f x) = x0 + h (?F z)"
      using xeq by (simp add: g_def)
    also have "\<dots> = x0 + z"
      using homeomorphism_apply1[OF homeo0 z] by simp
    also have "\<dots> = x"
      using xeq by simp
    finally show ?thesis .
  qed

  have fg: "f (g y) = y" if y: "y \<in> V" for y
  proof -
    obtain z where z: "z \<in> V0" and yeq: "y = f x0 + L z"
      using y unfolding V_def by blast
    have coord: "?S y = z"
      using yeq injL by (simp add: inv_f_f)
    have hz: "h z \<in> U0'"
      using homeomorphism_image2[OF homeo0] z by blast
    have F_hz: "?F (h z) = z"
      by (rule homeomorphism_apply2[OF homeo0 z])
    have L_Fhz: "L (?F (h z)) = f (x0 + h z) - f x0"
      using surjL by (simp add: surj_f_inv_f)
    have "f (g y) = f (x0 + h z)"
      using coord by (simp add: g_def)
    also have "\<dots> = f x0 + L z"
      using F_hz L_Fhz by simp
    also have "\<dots> = y"
      using yeq by simp
    finally show ?thesis .
  qed

  have f_cont_U: "continuous_on U f"
    by (rule continuous_at_imp_continuous_on)
       (use ana in \<open>auto intro: real_analytic_on_imp_continuous_vec\<close>)
  have f_cont_U': "continuous_on U' f"
    by (rule continuous_on_subset[OF f_cont_U U'_sub])
  have S_cont: "continuous_on V ?S"
  proof -
    have diff_cont: "continuous_on V (\<lambda>y. y - f x0)"
      by (intro continuous_intros)
    have inv_cont: "continuous_on UNIV (inv L)"
      using bounded_linear.continuous_on[OF blInvL continuous_on_id[of UNIV]]
      by (simp add: o_def)
    show ?thesis
      by (rule continuous_on_compose2[OF inv_cont diff_cont]) simp
  qed
  have h_cont_S: "continuous_on V (\<lambda>y. h (?S y))"
    by (rule continuous_on_compose2[OF homeomorphism_cont2[OF homeo0] S_cont S_V_sub])
  have g_cont_V: "continuous_on V g"
    unfolding g_def by (intro continuous_intros h_cont_S)
  have homeo: "homeomorphism U' V f g"
    by (rule homeomorphismI[OF f_cont_U' g_cont_V f_image g_image gf fg])

  have diff_ana: "real_analytic_on (\<lambda>y::'a. y - f x0) V"
    by (rule real_analytic_on_diff)
       (rule real_analytic_on_bounded_linear[OF V_open bounded_linear_ident],
        rule real_analytic_on_const[OF V_open])
  have S_ana: "real_analytic_on ?S V"
    by (rule real_analytic_on_compose[OF diff_ana invL_ana_UNIV]) simp
  have hS_ana: "real_analytic_on (\<lambda>y. h (?S y)) V"
    by (rule real_analytic_on_compose[OF S_ana h_ana S_V_sub])
  have g_ana: "real_analytic_on g V"
    unfolding g_def
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF V_open] hS_ana])

  show ?thesis
    by (rule that[OF U'_open x0_U' U'_sub V_open fx0_V homeo g_ana])
qed


section \<open>The real-analytic implicit function theorem\<close>

text \<open>
  If \<open>F\<close> is real-analytic near \<open>(x0, y0)\<close>, \<open>F (x0, y0) = 0\<close> and the partial derivative
  of \<open>F\<close> in its second argument at \<open>(x0, y0)\<close> is bijective, then near \<open>x0\<close> there is a
  real-analytic \<open>g\<close> with \<open>g x0 = y0\<close> and \<open>F (x, g x) = 0\<close>.
\<close>

text \<open>
  Proof: apply the real-analytic inverse function theorem to \<open>\<Phi> (x, y) = (x, F (x, y))\<close>
  and read off the solution from the second component of the local inverse.
\<close>

theorem real_analytic_implicit_function:
  fixes F :: "('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
  assumes ana: "real_analytic_on F W"
    and Wopen: "open W"
    and pW: "(x0, y0) \<in> W"
    and F0: "F (x0, y0) = 0"
    and reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at y0) \<and> bij L"
  obtains U g where
      "open U" and "x0 \<in> U" and "g x0 = y0"
      and "real_analytic_on g U"
      and "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
proof -
  let ?Phi = "\<lambda>p::'a \<times> 'b. (fst p, F p)"
  let ?p0 = "(x0, y0)"
  obtain L where Lder: "((\<lambda>y. F (x0, y)) has_derivative L) (at y0)"
    and bijL: "bij L"
    using reg by blast

  have Phi_ana: "real_analytic_on ?Phi W"
    by (rule real_analytic_on_Pair[OF real_analytic_on_fst[OF Wopen] ana])

  have C1_F: "Ck_at (Suc 0) F ?p0"
    using real_analytic_imp_Cinfinity[OF ana] pW
    unfolding Cinfinity_on_def Cinfinity_at_def
    by blast
  hence Fdiff: "F differentiable at ?p0"
    by (simp only: Ck_at.simps(2))
  then obtain A where Fder: "(F has_derivative A) (at ?p0)"
    unfolding differentiable_def by blast

  have slice_der: "((\<lambda>y. F (x0, y)) has_derivative (\<lambda>dy. A (0, dy))) (at y0)"
  proof -
    have pair_der: "((\<lambda>y. (x0, y)) has_derivative (\<lambda>dy. (0, dy))) (at y0)"
    proof -
      have cder: "((\<lambda>y::'b. x0) has_derivative (\<lambda>dy. 0)) (at y0)"
        by (rule has_derivative_const)
      have idder: "((\<lambda>y::'b. y) has_derivative (\<lambda>dy. dy)) (at y0)"
        by (rule has_derivative_ident)
      show ?thesis
        using has_derivative_Pair[OF cder idder] by simp
    qed
    show ?thesis
      using has_derivative_compose[OF pair_der Fder] by simp
  qed
  have L_eq: "L = (\<lambda>dy. A (0, dy))"
    by (rule has_derivative_unique[OF Lder slice_der])

  let ?B = "\<lambda>h::'a \<times> 'b. (fst h, A h)"
  have Phi_der: "(?Phi has_derivative ?B) (at ?p0)"
  proof -
    have fst_der: "((fst :: ('a \<times> 'b) \<Rightarrow> 'a) has_derivative fst) (at ?p0)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
    show ?thesis
      using has_derivative_Pair[OF fst_der Fder] by simp
  qed

  have blA: "bounded_linear A"
    using Fder by (rule has_derivative_bounded_linear)
  interpret A: bounded_linear A by (rule blA)
  have surjL: "surj L" and injL: "inj L"
    using bijL by (auto simp: bij_def)

  let ?C = "\<lambda>q::'a \<times> 'b. (fst q, inv L (snd q - A (fst q, 0)))"
  have B_C: "?B (?C q) = q" for q
  proof -
    let ?w = "snd q - A (fst q, 0)"
    have decomp: "(fst q, inv L ?w) = (fst q, 0) + (0, inv L ?w)"
      by simp
    have Aq: "A (fst q, inv L ?w) = A (fst q, 0) + A (0, inv L ?w)"
      by (subst decomp) (rule A.add)
    have A0_inv: "A (0, inv L ?w) = ?w"
    proof -
      have "A (0, inv L ?w) = L (inv L ?w)"
        using L_eq by simp
      also have "... = ?w"
        using surjL by (rule surj_f_inv_f)
      finally show ?thesis .
    qed
    have Aeq: "A (fst q, inv L ?w) = snd q"
      using Aq A0_inv by simp
    show ?thesis
      using Aeq
      by simp
  qed
  have C_B: "?C (?B h) = h" for h
  proof -
    have Ah: "A h = A (fst h, 0) + A (0, snd h)"
    proof -
      have decomp: "h = (fst h, 0) + (0, snd h)"
        by simp
      show ?thesis
        by (subst decomp) (rule A.add)
    qed
    have "A h - A (fst h, 0) = L (snd h)"
      using Ah L_eq by simp
    thus ?thesis
      using injL by (simp add: inv_f_f)
  qed
  have bijB: "bij ?B"
  proof (rule bijI)
    show "inj ?B"
    proof (rule injI)
      fix x y :: "'a \<times> 'b"
      assume "?B x = ?B y"
      hence H: "?C (?B x) = ?C (?B y)"
        by simp
      have Cx: "?C (?B x) = x"
        by (rule C_B)
      have Cy: "?C (?B y) = y"
        by (rule C_B)
      show "x = y"
        using H Cx Cy by metis
    qed
    show "surj ?B"
      unfolding surj_def
    proof
      fix y :: "'a \<times> 'b"
      have "?B (?C y) = y"
        by (rule B_C)
      hence "y = ?B (?C y)"
        by simp
      show "\<exists>x. y = ?B x"
        using \<open>y = ?B (?C y)\<close> by blast
    qed
  qed

  obtain U' V Psi where U'_open: "open U'" and p0_U': "?p0 \<in> U'"
    and U'_sub: "U' \<subseteq> W" and V_open: "open V"
    and Phi_p0_V: "?Phi ?p0 \<in> V"
    and homeo: "homeomorphism U' V ?Phi Psi"
    and Psi_ana: "real_analytic_on Psi V"
  proof (rule real_analytic_local_inverse[OF Phi_ana Wopen pW])
    show "\<exists>L. (?Phi has_derivative L) (at ?p0) \<and> bij L"
      using Phi_der bijB by blast
  qed blast

  define U where "U = {x. (x, 0::'b) \<in> V}"
  define g where "g = (\<lambda>x. snd (Psi (x, 0::'b)))"

  have U_open: "open U"
  proof -
    have cont_slice: "continuous_on UNIV (\<lambda>x::'a. (x, 0::'b))"
      by (intro continuous_intros)
    have "open (UNIV \<inter> (\<lambda>x::'a. (x, 0::'b)) -` V)"
      by (rule continuous_open_preimage[OF cont_slice open_UNIV V_open])
    thus ?thesis
      by (simp add: U_def vimage_def)
  qed
  have x0_U: "x0 \<in> U"
    using Phi_p0_V F0 by (simp add: U_def)
  have g_x0: "g x0 = y0"
    using homeomorphism_apply1[OF homeo p0_U'] F0
    by (simp add: g_def)

  have slice_ana: "real_analytic_on (\<lambda>x::'a. (x, 0::'b)) U"
    by (rule real_analytic_on_Pair_const[OF U_open])
  have slice_image: "(\<lambda>x::'a. (x, 0::'b)) ` U \<subseteq> V"
    by (auto simp: U_def)
  have Psi_slice_ana: "real_analytic_on (\<lambda>x::'a. Psi (x, 0::'b)) U"
    using real_analytic_on_compose[OF slice_ana Psi_ana slice_image] by simp
  have g_ana: "real_analytic_on g U"
  proof -
    have snd_ana: "real_analytic_on (snd :: ('a \<times> 'b) \<Rightarrow> 'b) UNIV"
      by (rule real_analytic_on_snd) simp
    have "real_analytic_on (\<lambda>x::'a. snd (Psi (x, 0::'b))) U"
      by (rule real_analytic_on_compose[OF Psi_slice_ana snd_ana]) simp
    thus ?thesis
      by (simp add: g_def)
  qed

  have solution: "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
  proof
    fix x assume xU: "x \<in> U"
    have x0V: "(x, 0::'b) \<in> V"
      using xU by (simp add: U_def)
    have Psi_in: "Psi (x, 0::'b) \<in> U'"
      using homeomorphism_image2[OF homeo] x0V by blast
    have Phi_Psi: "?Phi (Psi (x, 0::'b)) = (x, 0::'b)"
      by (rule homeomorphism_apply2[OF homeo x0V])
    have fst_Psi: "fst (Psi (x, 0::'b)) = x"
      using Phi_Psi by simp
    have F_Psi: "F (Psi (x, 0::'b)) = 0"
      using Phi_Psi by simp
    have "(x, g x) = Psi (x, 0::'b)"
      using fst_Psi by (simp add: g_def prod_eq_iff)
    thus "(x, g x) \<in> W \<and> F (x, g x) = 0"
      using Psi_in U'_sub F_Psi by auto
  qed

  show ?thesis
    by (rule that[OF U_open x0_U g_x0 g_ana solution])
qed

end
