(*  Title:     HOL/Probability/Sinc_Integral.thy
    Authors:   Jeremy Avigad (CMU), Luke Serafin (CMU)
    Authors:   Johannes Hölzl, TU München
*)

section \<open>Integral of sinc\<close>

theory Sinc_Integral
  imports Distributions
begin

subsection \<open>Various preparatory integrals\<close>

text \<open> Naming convention
The theorem name consists of the following parts:
  \<^item> Kind of integral: \<open>has_bochner_integral\<close> / \<open>integrable\<close> / \<open>LBINT\<close>
  \<^item> Interval: Interval (0 / infinity / open / closed) (infinity / open / closed)
  \<^item> Name of the occurring constants: power, exp, m (for minus), scale, sin, $\ldots$
\<close>

lemma has_bochner_integral_I0i_power_exp_m':
  "has_bochner_integral lborel (\<lambda>x. x^k * exp (-x) * indicator {0 ..} x::real) (fact k)"
  using nn_intergal_power_times_exp_Ici[of k]
  by (intro has_bochner_integral_nn_integral)
     (auto simp: nn_integral_set_ennreal split: split_indicator)

lemma has_bochner_integral_I0i_power_exp_m:
  "has_bochner_integral lborel (\<lambda>x. x^k * exp (-x) * indicator {0 <..} x::real) (fact k)"
  using AE_lborel_singleton[of 0]
  by (intro has_bochner_integral_cong_AE[THEN iffD1, OF _ _ _ has_bochner_integral_I0i_power_exp_m'])
     (auto split: split_indicator)

lemma integrable_I0i_exp_mscale: "0 < (u::real) \<Longrightarrow> set_integrable lborel {0 <..} (\<lambda>x. exp (-(x * u)))"
  using lborel_integrable_real_affine_iff[of u "\<lambda>x. indicator {0 <..} x *\<^sub>R exp (- x)" 0]
        has_bochner_integral_I0i_power_exp_m[of 0]
  by (simp add: indicator_def zero_less_mult_iff mult_ac integrable.intros set_integrable_def)

lemma LBINT_I0i_exp_mscale: "0 < (u::real) \<Longrightarrow> LBINT x=0..\<infinity>. exp (-(x * u)) = 1 / u"
  using lborel_integral_real_affine[of u "\<lambda>x. indicator {0<..} x *\<^sub>R exp (- x)" 0]
        has_bochner_integral_I0i_power_exp_m[of 0]
  by (auto simp: indicator_def zero_less_mult_iff interval_lebesgue_integral_0_infty set_lebesgue_integral_def field_simps
           dest!: has_bochner_integral_integral_eq)

lemma LBINT_I0c_exp_mscale_sin:
  "LBINT x=0..t. exp (-(u * x)) * sin x =
    (1 / (1 + u^2)) * (1 - exp (-(u * t)) * (u * sin t + cos t))" (is "_ = ?F t")
  unfolding zero_ereal_def
proof (subst interval_integral_FTC_finite)
  show "(?F has_vector_derivative exp (- (u * x)) * sin x) (at x within {min 0 t..max 0 t})" for x
    by (auto intro!: derivative_eq_intros
             simp: has_real_derivative_iff_has_vector_derivative[symmetric] power2_eq_square)
       (simp_all add: field_simps add_nonneg_eq_0_iff)
qed (auto intro: continuous_at_imp_continuous_on)

lemma LBINT_I0i_exp_mscale_sin:
  assumes "0 < x"
  shows "LBINT u=0..\<infinity>. \<bar>exp (-u * x) * sin x\<bar> = \<bar>sin x\<bar> / x"
proof (subst interval_integral_FTC_nonneg)
  let ?F = "\<lambda>u. 1 / x * (1 - exp (- u * x)) * \<bar>sin x\<bar>"
  show "\<And>t. (?F has_real_derivative \<bar>exp (- t * x) * sin x\<bar>) (at t)"
    using \<open>0 < x\<close> by (auto intro!: derivative_eq_intros simp: abs_mult)
  show "((?F \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_right 0)"
    using \<open>0 < x\<close> by (auto simp: zero_ereal_def ereal_tendsto_simps intro!: tendsto_eq_intros)
  have *: "((\<lambda>t. exp (- t * x)) \<longlongrightarrow> 0) at_top"
    using \<open>0 < x\<close>
    by (auto intro!: exp_at_bot[THEN filterlim_compose] filterlim_tendsto_pos_mult_at_top filterlim_ident
             simp: filterlim_uminus_at_bot mult.commute[of _ x])
  show "((?F \<circ> real_of_ereal) \<longlongrightarrow> \<bar>sin x\<bar> / x) (at_left \<infinity>)"
    using \<open>0 < x\<close> unfolding ereal_tendsto_simps
    by (intro filterlim_compose[OF _ *]) (auto intro!: tendsto_eq_intros filterlim_ident)
qed auto

lemma
  shows integrable_inverse_1_plus_square:
      "set_integrable lborel (einterval (-\<infinity>) \<infinity>) (\<lambda>x. inverse (1 + x^2))"
  and LBINT_inverse_1_plus_square:
      "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = pi"
proof -
  have 1: "- (pi / 2) < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> (tan has_real_derivative 1 + (tan x)\<^sup>2) (at x)" for x
    using cos_gt_zero_pi[of x] by (subst tan_sec) (auto intro!: DERIV_tan simp: power_inverse)
  have 2: "- (pi / 2) < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> isCont (\<lambda>x. 1 + (tan x)\<^sup>2) x" for x
    using cos_gt_zero_pi[of x] by auto
  have 3: "\<lbrakk>- (pi / 2) < x; x * 2 < pi\<rbrakk>  \<Longrightarrow> isCont (\<lambda>x. inverse (1 + x\<^sup>2)) (tan x)" for x
    by (rule continuous_intros | simp add: add_nonneg_eq_0_iff)+
  show "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = pi"
    by (subst interval_integral_substitution_nonneg[of "-pi/2" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
       (auto intro: derivative_eq_intros 1 2 3 filterlim_tan_at_right
             simp add: ereal_tendsto_simps filterlim_tan_at_left add_nonneg_eq_0_iff set_integrable_def)
  show "set_integrable lborel (einterval (-\<infinity>) \<infinity>) (\<lambda>x. inverse (1 + x^2))"
    by (subst interval_integral_substitution_nonneg[of "-pi/2" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
       (auto intro: derivative_eq_intros 1 2 3 filterlim_tan_at_right
             simp add: ereal_tendsto_simps filterlim_tan_at_left add_nonneg_eq_0_iff set_integrable_def)
qed

lemma
  shows integrable_I0i_1_div_plus_square:
    "interval_lebesgue_integrable lborel 0 \<infinity> (\<lambda>x. 1 / (1 + x^2))"
  and LBINT_I0i_1_div_plus_square:
    "LBINT x=0..\<infinity>. 1 / (1 + x^2) = pi / 2"
proof -
  have 1: "0 < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> (tan has_real_derivative 1 + (tan x)\<^sup>2) (at x)" for x
    using cos_gt_zero_pi[of x] by (subst tan_sec) (auto intro!: DERIV_tan simp: power_inverse)
  have 2: "0 < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> isCont (\<lambda>x. 1 + (tan x)\<^sup>2) x" for x
    using cos_gt_zero_pi[of x] by auto
  show "LBINT x=0..\<infinity>. 1 / (1 + x^2) = pi / 2"
    by (subst interval_integral_substitution_nonneg[of "0" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
       (auto intro: derivative_eq_intros 1 2 tendsto_eq_intros
             simp add: ereal_tendsto_simps filterlim_tan_at_left zero_ereal_def add_nonneg_eq_0_iff set_integrable_def)
  show "interval_lebesgue_integrable lborel 0 \<infinity> (\<lambda>x. 1 / (1 + x^2))"
    unfolding interval_lebesgue_integrable_def
    by (subst interval_integral_substitution_nonneg[of "0" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
       (auto intro: derivative_eq_intros 1 2 tendsto_eq_intros
             simp add: ereal_tendsto_simps filterlim_tan_at_left zero_ereal_def add_nonneg_eq_0_iff set_integrable_def)
qed

section \<open>The sinc function, and the sine integral (Si)\<close>

abbreviation sinc :: "real \<Rightarrow> real" where
  "sinc \<equiv> (\<lambda>x. if x = 0 then 1 else sin x / x)"

lemma sinc_at_0: "((\<lambda>x. sin x / x::real) \<longlongrightarrow> 1) (at 0)"
  using DERIV_sin [of 0] by (auto simp add: has_field_derivative_def field_has_derivative_at)

lemma isCont_sinc: "isCont sinc x"
proof cases
  assume "x = 0" then show ?thesis
    using LIM_equal [where g = "\<lambda>x. sin x / x" and a=0 and f=sinc and l=1]
    by (auto simp: isCont_def sinc_at_0)
next
  assume "x \<noteq> 0" show ?thesis
    by (rule continuous_transform_within [where \<delta> = "abs x" and f = "\<lambda>x. sin x / x"])
       (auto simp add: dist_real_def \<open>x \<noteq> 0\<close>)
qed

lemma continuous_on_sinc[continuous_intros]:
  "continuous_on S f \<Longrightarrow> continuous_on S (\<lambda>x. sinc (f x))"
  using continuous_on_compose[of S f sinc, OF _ continuous_at_imp_continuous_on]
  by (auto simp: isCont_sinc)

lemma borel_measurable_sinc[measurable]: "sinc \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_at_imp_continuous_on ballI isCont_sinc)

lemma sinc_AE: "AE x in lborel. sin x / x = sinc x"
  by (rule AE_I [where N = "{0}"], auto)

definition Si :: "real \<Rightarrow> real" where "Si t \<equiv> LBINT x=0..t. sin x / x"

lemma sinc_neg [simp]: "sinc (- x) = sinc x"
  by auto

(* TODO: Determine whether this can reasonably be eliminated by redefining Si. *)
lemma Si_alt_def : "Si t = LBINT x=0..t. sinc x"
proof cases
  assume "0 \<le> t" then show ?thesis
    using AE_lborel_singleton[of 0]
    by (auto simp: Si_def intro!: interval_lebesgue_integral_cong_AE)
next
  assume "\<not> 0 \<le> t" then show ?thesis
    unfolding Si_def using AE_lborel_singleton[of 0]
    by (subst (1 2) interval_integral_endpoints_reverse)
       (auto simp: Si_def intro!: interval_lebesgue_integral_cong_AE)
qed

lemma Si_neg:
  assumes "T \<ge> 0" shows "Si (- T) = - Si T"
proof -
  have "LBINT x=ereal 0..T. -1 *\<^sub>R sinc (- x) = LBINT y= ereal (- 0)..ereal (- T). sinc y"
    by (rule interval_integral_substitution_finite [OF assms])
       (auto intro: derivative_intros continuous_at_imp_continuous_on isCont_sinc)
  also have "(LBINT x=ereal 0..T. -1 *\<^sub>R sinc (- x)) = -(LBINT x=ereal 0..T. sinc x)"
    by (subst sinc_neg) (simp_all add: interval_lebesgue_integral_uminus)
  finally have *: "-(LBINT x=ereal 0..T. sinc x) = LBINT y= ereal 0..ereal (- T). sinc y"
    by simp
  show ?thesis
    using assms unfolding Si_alt_def
    by (subst zero_ereal_def)+ (auto simp add: * [symmetric])
qed

lemma integrable_sinc':
  "interval_lebesgue_integrable lborel (ereal 0) (ereal T) (\<lambda>t. sin (t * \<theta>) / t)"
proof -
  have *: "interval_lebesgue_integrable lborel (ereal 0) (ereal T) (\<lambda>t. \<theta> * sinc (t * \<theta>))"
    by (intro interval_lebesgue_integrable_mult_right interval_integrable_isCont continuous_within_compose3 [OF isCont_sinc])
       auto
  have "0 \<notin> einterval (min (ereal 0) (ereal T)) (max (ereal 0) (ereal T))"
    by (smt (verit, best) einterval_iff max_def min_def_raw order_less_le)
  then show ?thesis
    by (intro interval_lebesgue_integrable_cong_AE[THEN iffD1, OF _ _ _ *]) auto
qed

(* TODO: need a better version of FTC2 *)
lemma DERIV_Si: "(Si has_real_derivative sinc x) (at x)"
proof -
  have "(at x within {min 0 (x - 1)..max 0 (x + 1)}) = at x"
    by (intro at_within_interior) auto
  moreover have "min 0 (x - 1) \<le> x" "x \<le> max 0 (x + 1)"
    by auto
  ultimately show ?thesis
    using interval_integral_FTC2[of "min 0 (x - 1)" 0 "max 0 (x + 1)" sinc x]
    by (auto simp: continuous_at_imp_continuous_on isCont_sinc Si_alt_def[abs_def] zero_ereal_def
                   has_real_derivative_iff_has_vector_derivative
             split del: if_split)
qed

lemma isCont_Si: "isCont Si x"
  using DERIV_Si by (rule DERIV_isCont)

lemma borel_measurable_Si[measurable]: "Si \<in> borel_measurable borel"
  by (auto intro: isCont_Si continuous_at_imp_continuous_on borel_measurable_continuous_onI)

lemma Si_at_top_LBINT:
  "((\<lambda>t. (LBINT x=0..\<infinity>. exp (-(x * t)) * (x * sin t + cos t) / (1 + x^2))) \<longlongrightarrow> 0) at_top"
proof -
  let ?F = "\<lambda>x t. exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2) :: real"
  have int: "set_integrable lborel {0<..} (\<lambda>x. exp (- x) * (x + 1) :: real)"
    unfolding distrib_left
    using has_bochner_integral_I0i_power_exp_m[of 0] has_bochner_integral_I0i_power_exp_m[of 1]
    by (intro set_integral_add) (auto dest!: integrable.intros simp: ac_simps set_integrable_def)

  have "((\<lambda>t::real. LBINT x:{0<..}. ?F x t) \<longlongrightarrow> (LBINT x::real:{0<..}. 0)) at_top"
    unfolding set_lebesgue_integral_def
  proof (rule integral_dominated_convergence_at_top[OF _ _ int [unfolded set_integrable_def]], 
         simp_all del: abs_divide split: split_indicator)
    have *: "0 < x \<Longrightarrow> \<bar>x * sin t + cos t\<bar> / (1 + x\<^sup>2) \<le> (x * 1 + 1) / 1" for x t :: real
      by (intro frac_le abs_triangle_ineq[THEN order_trans] add_mono)
         (auto simp add: abs_mult simp del: mult_1_right intro!: mult_mono)
    then have "1 \<le> t \<Longrightarrow> 0 < x \<Longrightarrow> \<bar>?F x t\<bar> \<le> exp (- x) * (x + 1)" for x t :: real
        by (auto simp add: abs_mult times_divide_eq_right[symmetric] simp del: times_divide_eq_right
                 intro!:  mult_mono)
    then show "\<forall>\<^sub>F i in at_top. AE x in lborel. 0 < x \<longrightarrow> \<bar>?F x i\<bar> \<le> exp (- x) * (x + 1)"
      by (auto intro: eventually_mono eventually_ge_at_top[of "1::real"])
    show "AE x in lborel. 0 < x \<longrightarrow> (?F x \<longlongrightarrow> 0) at_top"
    proof (intro always_eventually impI allI)
      fix x :: real assume "0 < x"
      show "((\<lambda>t. exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2)) \<longlongrightarrow> 0) at_top"
      proof (rule Lim_null_comparison)
        show "\<forall>\<^sub>F t in at_top. norm (?F x t) \<le> exp (- (x * t)) * (x + 1)"
          using eventually_ge_at_top[of "1::real"] * \<open>0 < x\<close>
          by (auto simp add: abs_mult times_divide_eq_right[symmetric] simp del: times_divide_eq_right
                   intro!: mult_mono elim: eventually_mono)
        show "((\<lambda>t. exp (- (x * t)) * (x + 1)) \<longlongrightarrow> 0) at_top"
          by (auto simp: filterlim_uminus_at_top [symmetric]
                   intro!: filterlim_tendsto_pos_mult_at_top[OF tendsto_const] \<open>0<x\<close> filterlim_ident
                           tendsto_mult_left_zero filterlim_compose[OF exp_at_bot])
      qed
    qed
  qed
  then show "((\<lambda>t. (LBINT x=0..\<infinity>. exp (-(x * t)) * (x * sin t + cos t) / (1 + x^2))) \<longlongrightarrow> 0) at_top"
    by (simp add: interval_lebesgue_integral_0_infty set_lebesgue_integral_def)
qed

lemma Si_at_top_integrable:
  assumes "t \<ge> 0"
  shows "interval_lebesgue_integrable lborel 0 \<infinity> (\<lambda>x. exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2))"
  using \<open>0 \<le> t\<close> unfolding le_less
proof
  assume "0 = t" then show ?thesis
    using integrable_I0i_1_div_plus_square by simp
next
  assume [arith]: "0 < t"
  have *: "0 \<le> a \<Longrightarrow> 0 < x \<Longrightarrow> a / (1 + x\<^sup>2) \<le> a" for a x :: real
    using zero_le_power2[of x, arith] using divide_left_mono[of 1 "1+x\<^sup>2" a] by auto
  have "set_integrable lborel {0<..} (\<lambda>x. (exp (- x) * x) * (sin t/t) + exp (- x) * cos t)"
    using has_bochner_integral_I0i_power_exp_m[of 0] has_bochner_integral_I0i_power_exp_m[of 1]
    by (intro set_integral_add set_integrable_mult_left)
       (auto dest!: integrable.intros simp: ac_simps set_integrable_def)
  from lborel_integrable_real_affine[OF this [unfolded set_integrable_def], of t 0]
  show ?thesis
    unfolding interval_lebesgue_integral_0_infty set_integrable_def
    by (rule Bochner_Integration.integrable_bound) (auto simp: field_simps * split: split_indicator)
qed

lemma Si_at_top: "(Si \<longlongrightarrow> pi / 2) at_top"
proof -
  have \<dagger>: "\<forall>\<^sub>F t in at_top. pi / 2 - (LBINT u=0..\<infinity>. exp (-(u * t)) * (u * sin t + cos t) / (1 + u^2)) = Si t"
    using eventually_ge_at_top[of 0]
  proof eventually_elim
    fix t :: real assume "t \<ge> 0"
    have "Si t = LBINT x=0..t. sin x * (LBINT u=0..\<infinity>. exp (-(u * x)))"
      unfolding Si_def using \<open>0 \<le> t\<close>
      by (intro interval_integral_discrete_difference[where X="{0}"]) (auto simp: LBINT_I0i_exp_mscale)
    also have "\<dots> = (LBINT x. (LBINT u=ereal 0..\<infinity>. indicator {0 <..< t} x *\<^sub>R sin x * exp (-(u * x))))"
      using \<open>0\<le>t\<close> by (simp add: zero_ereal_def interval_lebesgue_integral_le_eq mult_ac set_lebesgue_integral_def)
    also have "\<dots> = (LBINT x. (LBINT u. indicator ({0<..} \<times> {0 <..< t}) (u, x) *\<^sub>R (sin x * exp (-(u * x)))))"
      apply (subst interval_integral_Ioi)
      unfolding set_lebesgue_integral_def  by(simp_all add: indicator_times ac_simps )
    also have "\<dots> = (LBINT u. (LBINT x. indicator ({0<..} \<times> {0 <..< t}) (u, x) *\<^sub>R (sin x * exp (-(u * x)))))"
    proof (intro lborel_pair.Fubini_integral[symmetric] lborel_pair.Fubini_integrable)
      show "(\<lambda>(x, y). indicator ({0<..} \<times> {0<..<t}) (y, x) *\<^sub>R (sin x * exp (- (y * x))))
          \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)" (is "?f \<in> borel_measurable _")
        by measurable

      have "AE x in lborel. indicator {0..t} x *\<^sub>R abs (sinc x) = (LBINT y. norm (?f (x, y)))"
        using AE_lborel_singleton[of 0] AE_lborel_singleton[of t]
      proof eventually_elim
        fix x :: real assume x: "x \<noteq> 0" "x \<noteq> t"
        have "(LBINT y. \<bar>indicator ({0<..} \<times> {0<..<t}) (y, x) *\<^sub>R (sin x * exp (- (y * x)))\<bar>) =
              (LBINT y. \<bar>sin x\<bar> * exp (- (y * x)) * indicator {0<..} y * indicator {0<..<t} x)"
          by (intro Bochner_Integration.integral_cong) (auto split: split_indicator simp: abs_mult)
        also have "\<dots> = \<bar>sin x\<bar> * indicator {0<..<t} x * (LBINT y=0..\<infinity>.  exp (- (y * x)))"
          by (cases "x > 0")
             (auto simp: field_simps interval_lebesgue_integral_0_infty set_lebesgue_integral_def split: split_indicator)
        also have "\<dots> = \<bar>sin x\<bar> * indicator {0<..<t} x * (1 / x)"
          by (cases "x > 0") (auto simp add: LBINT_I0i_exp_mscale)
        also have "\<dots> = indicator {0..t} x *\<^sub>R \<bar>sinc x\<bar>"
          using x by (simp add: field_simps split: split_indicator)
        finally show "indicator {0..t} x *\<^sub>R abs (sinc x) = (LBINT y. norm (?f (x, y)))"
          by simp
      qed
      moreover have "integrable lborel (\<lambda>x. indicat_real {0..t} x *\<^sub>R \<bar>sinc x\<bar>)"
        by (auto intro!: borel_integrable_compact continuous_intros simp del: real_scaleR_def)
      ultimately show "integrable lborel (\<lambda>x. LBINT y. norm (?f (x, y)))"
        by (rule integrable_cong_AE_imp[rotated 2]) simp

      have "0 < x \<Longrightarrow> set_integrable lborel {0<..} (\<lambda>y. sin x * exp (- (y * x)))" for x :: real
          by (intro set_integrable_mult_right integrable_I0i_exp_mscale)
      then show "AE x in lborel. integrable lborel (\<lambda>y. ?f (x, y))"
        by (intro AE_I2) (auto simp: indicator_times set_integrable_def split: split_indicator)
    qed
    also have "... = (LBINT u=0..\<infinity>. (LBINT x=0..t. exp (-(u * x)) * sin x))"
      using \<open>0\<le>t\<close>
      by (auto simp: interval_lebesgue_integral_def set_lebesgue_integral_def zero_ereal_def ac_simps
               split: split_indicator intro!: Bochner_Integration.integral_cong)
    also have "\<dots> = (LBINT u=0..\<infinity>. 1 / (1 + u\<^sup>2) - 1 / (1 + u\<^sup>2) * (exp (- (u * t)) * (u * sin t + cos t)))"
      by (auto simp: divide_simps LBINT_I0c_exp_mscale_sin intro!: interval_integral_cong)
    also have "... = pi / 2 - (LBINT u=0..\<infinity>. exp (- (u * t)) * (u * sin t + cos t) / (1 + u^2))"
      using Si_at_top_integrable[OF \<open>0\<le>t\<close>] by (simp add: integrable_I0i_1_div_plus_square LBINT_I0i_1_div_plus_square)
    finally show "pi / 2 - (LBINT u=0..\<infinity>. exp (-(u * t)) * (u * sin t + cos t) / (1 + u^2)) = Si t" ..
  qed
  show ?thesis
    by (rule Lim_transform_eventually [OF _ \<dagger>])
       (auto intro!: tendsto_eq_intros Si_at_top_LBINT)
qed

subsection \<open>The final theorems: boundedness and scalability\<close>

lemma bounded_Si: "\<exists>B. \<forall>T. \<bar>Si T\<bar> \<le> B"
proof -
  have *: "0 \<le> y \<Longrightarrow> dist x y < z \<Longrightarrow> abs x \<le> y + z" for x y z :: real
    by (simp add: dist_real_def)

  have "eventually (\<lambda>T. dist (Si T) (pi / 2) < 1) at_top"
    using Si_at_top by (elim tendstoD) simp
  then have "eventually (\<lambda>T. 0 \<le> T \<and> \<bar>Si T\<bar> \<le> pi / 2 + 1) at_top"
    using eventually_ge_at_top[of 0] by eventually_elim (insert *[of "pi/2" "Si _" 1], auto)
  then have "\<exists>T. 0 \<le> T \<and> (\<forall>t \<ge> T. \<bar>Si t\<bar> \<le> pi / 2 + 1)"
    by (auto simp add: eventually_at_top_linorder)
  then obtain T where T: "0 \<le> T" "\<And>t. t \<ge> T \<Longrightarrow> \<bar>Si t\<bar> \<le> pi / 2 + 1"
    by auto
  moreover have "t \<le> - T \<Longrightarrow> \<bar>Si t\<bar> \<le> pi / 2 + 1" for t
    using T(1) T(2)[of "-t"] Si_neg[of "- t"] by simp
  moreover have "\<exists>M. \<forall>t. -T \<le> t \<and> t \<le> T \<longrightarrow> \<bar>Si t\<bar> \<le> M"
    by (rule isCont_bounded) (auto intro!: isCont_Si continuous_intros \<open>0 \<le> T\<close>)
  then obtain M where M: "\<And>t. -T \<le> t \<and> t \<le> T \<Longrightarrow> \<bar>Si t\<bar> \<le> M"
    by auto
  ultimately show ?thesis
    by (intro exI[of _ "max M (pi/2 + 1)"]) (meson le_max_iff_disj linorder_not_le order_le_less)
qed

lemma LBINT_I0c_sin_scale_divide:
  assumes "T \<ge> 0"
  shows "LBINT t=0..T. sin (t * \<theta>) / t = sgn \<theta> * Si (T * \<bar>\<theta>\<bar>)"
proof -
  { assume "0 < \<theta>"
    have "(LBINT t=ereal 0..T. sin (t * \<theta>) / t) = (LBINT t=ereal 0..T. \<theta> *\<^sub>R sinc (t * \<theta>))"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    also have "\<dots> = (LBINT t=ereal (0 * \<theta>)..T * \<theta>. sinc t)"
      apply (rule interval_integral_substitution_finite [OF assms])
      apply (subst mult.commute, rule DERIV_subset)
      by (auto intro!: derivative_intros continuous_at_imp_continuous_on isCont_sinc)
    also have "\<dots> = (LBINT t=ereal (0 * \<theta>)..T * \<theta>. sin t / t)"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    finally have "(LBINT t=ereal 0..T. sin (t * \<theta>) / t) = (LBINT t=ereal 0..T * \<theta>. sin t / t)"
      by simp
    hence "(LBINT x. indicator {0<..<T} x * sin (x * \<theta>) / x) = (LBINT x. indicator {0<..<T * \<theta>} x * sin x / x)"
      using assms \<open>0 < \<theta>\<close> unfolding interval_lebesgue_integral_def einterval_eq zero_ereal_def
        by (auto simp: ac_simps set_lebesgue_integral_def)
  } note aux1 = this
  { assume "0 > \<theta>"
    have [simp]: "integrable lborel (\<lambda>x. sin (x * \<theta>) * indicator {0<..<T} x / x)"
      using integrable_sinc' [of T \<theta>] assms
      by (simp add: interval_lebesgue_integrable_def set_integrable_def ac_simps)
    have "(LBINT t=ereal 0..T. sin (t * -\<theta>) / t) = (LBINT t=ereal 0..T. -\<theta> *\<^sub>R sinc (t * -\<theta>))"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    also have "\<dots> = (LBINT t=ereal (0 * -\<theta>)..T * -\<theta>. sinc t)"
      apply (rule interval_integral_substitution_finite [OF assms])
      apply (subst mult.commute, rule DERIV_subset)
      by (auto intro!: derivative_intros continuous_at_imp_continuous_on isCont_sinc)
    also have "\<dots> = (LBINT t=ereal (0 * -\<theta>)..T * -\<theta>. sin t / t)"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    finally have "(LBINT t=ereal 0..T. sin (t * -\<theta>) / t) = (LBINT t=ereal 0..T * -\<theta>. sin t / t)"
      by simp
    hence "(LBINT x. indicator {0<..<T} x * sin (x * \<theta>) / x) =
       - (LBINT x. indicator {0<..<- (T * \<theta>)} x * sin x / x)"
      using assms \<open>0 > \<theta>\<close> unfolding interval_lebesgue_integral_def einterval_eq zero_ereal_def
        by (auto simp add: field_simps mult_le_0_iff set_lebesgue_integral_def split: if_split_asm)
  } note aux2 = this
  show ?thesis
    using assms unfolding Si_def interval_lebesgue_integral_def set_lebesgue_integral_def sgn_real_def einterval_eq zero_ereal_def
    by (auto simp: aux1 aux2)
qed

end
