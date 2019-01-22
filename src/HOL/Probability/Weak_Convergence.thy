(*  Title:     HOL/Probability/Weak_Convergence.thy
    Authors:   Jeremy Avigad (CMU), Johannes Hölzl (TUM)
*)

section \<open>Weak Convergence of Functions and Distributions\<close>

text \<open>Properties of weak convergence of functions and measures, including the portmanteau theorem.\<close>

theory Weak_Convergence
  imports Distribution_Functions
begin

section \<open>Weak Convergence of Functions\<close>

definition
  weak_conv :: "(nat \<Rightarrow> (real \<Rightarrow> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
where
  "weak_conv F_seq F \<equiv> \<forall>x. isCont F x \<longrightarrow> (\<lambda>n. F_seq n x) \<longlonglongrightarrow> F x"

section \<open>Weak Convergence of Distributions\<close>

definition
  weak_conv_m :: "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
where
  "weak_conv_m M_seq M \<equiv> weak_conv (\<lambda>n. cdf (M_seq n)) (cdf M)"

section \<open>Skorohod's theorem\<close>

locale right_continuous_mono =
  fixes f :: "real \<Rightarrow> real" and a b :: real
  assumes cont: "\<And>x. continuous (at_right x) f"
  assumes mono: "mono f"
  assumes bot: "(f \<longlongrightarrow> a) at_bot"
  assumes top: "(f \<longlongrightarrow> b) at_top"
begin

abbreviation I :: "real \<Rightarrow> real" where
  "I \<omega> \<equiv> Inf {x. \<omega> \<le> f x}"

lemma pseudoinverse: assumes "a < \<omega>" "\<omega> < b" shows "\<omega> \<le> f x \<longleftrightarrow> I \<omega> \<le> x"
proof
  let ?F = "{x. \<omega> \<le> f x}"
  obtain y where "f y < \<omega>"
    by (metis eventually_happens' trivial_limit_at_bot_linorder order_tendstoD(2) bot \<open>a < \<omega>\<close>)
  with mono have bdd: "bdd_below ?F"
    by (auto intro!: bdd_belowI[of _ y] elim: mono_invE[OF _ less_le_trans])

  have ne: "?F \<noteq> {}"
    using order_tendstoD(1)[OF top \<open>\<omega> < b\<close>]
    by (auto dest!: eventually_happens'[OF trivial_limit_at_top_linorder] intro: less_imp_le)

  show "\<omega> \<le> f x \<Longrightarrow> I \<omega> \<le> x"
    by (auto intro!: cInf_lower bdd)

  { assume *: "I \<omega> \<le> x"
    have "\<omega> \<le> (INF s\<in>{x. \<omega> \<le> f x}. f s)"
      by (rule cINF_greatest[OF ne]) auto
    also have "\<dots> = f (I \<omega>)"
      using continuous_at_Inf_mono[OF mono cont ne bdd] ..
    also have "\<dots> \<le> f x"
      using * by (rule monoD[OF \<open>mono f\<close>])
    finally show "\<omega> \<le> f x" . }
qed

lemma pseudoinverse': "\<forall>\<omega>\<in>{a<..<b}. \<forall>x. \<omega> \<le> f x \<longleftrightarrow> I \<omega> \<le> x"
  by (intro ballI allI impI pseudoinverse) auto

lemma mono_I: "mono_on I {a <..< b}"
  unfolding mono_on_def by (metis order.trans order.refl pseudoinverse')

end

locale cdf_distribution = real_distribution
begin

abbreviation "C \<equiv> cdf M"

sublocale right_continuous_mono C 0 1
  by standard
     (auto intro: cdf_nondecreasing cdf_is_right_cont cdf_lim_at_top_prob cdf_lim_at_bot monoI)

lemma measurable_C[measurable]: "C \<in> borel_measurable borel"
  by (intro borel_measurable_mono mono)

lemma measurable_CI[measurable]: "I \<in> borel_measurable (restrict_space borel {0<..<1})"
  by (intro borel_measurable_mono_on_fnc mono_I)

lemma emeasure_distr_I: "emeasure (distr (restrict_space lborel {0<..<1::real}) borel I) UNIV = 1"
  by (simp add: emeasure_distr space_restrict_space emeasure_restrict_space )

lemma distr_I_eq_M: "distr (restrict_space lborel {0<..<1::real}) borel I = M" (is "?I = _")
proof (intro cdf_unique ext)
  let ?\<Omega> = "restrict_space lborel {0<..<1}::real measure"
  interpret \<Omega>: prob_space ?\<Omega>
    by (auto simp add: emeasure_restrict_space space_restrict_space intro!: prob_spaceI)
  show "real_distribution ?I"
    by auto

  fix x
  have "cdf ?I x = measure lborel {\<omega>\<in>{0<..<1}. \<omega> \<le> C x}"
    by (subst cdf_def)
       (auto simp: pseudoinverse[symmetric] measure_distr space_restrict_space measure_restrict_space
             intro!: arg_cong2[where f="measure"])
  also have "\<dots> = measure lborel {0 <..< C x}"
    using cdf_bounded_prob[of x] AE_lborel_singleton[of "C x"]
    by (auto intro!: arg_cong[where f=enn2real] emeasure_eq_AE simp: measure_def)
  also have "\<dots> = C x"
    by (simp add: cdf_nonneg)
  finally show "cdf (distr ?\<Omega> borel I) x = C x" .
qed standard

end

context
  fixes \<mu> :: "nat \<Rightarrow> real measure"
    and M :: "real measure"
  assumes \<mu>: "\<And>n. real_distribution (\<mu> n)"
  assumes M: "real_distribution M"
  assumes \<mu>_to_M: "weak_conv_m \<mu> M"
begin

(* state using obtains? *)
theorem Skorohod:
 "\<exists> (\<Omega> :: real measure) (Y_seq :: nat \<Rightarrow> real \<Rightarrow> real) (Y :: real \<Rightarrow> real).
    prob_space \<Omega> \<and>
    (\<forall>n. Y_seq n \<in> measurable \<Omega> borel) \<and>
    (\<forall>n. distr \<Omega> borel (Y_seq n) = \<mu> n) \<and>
    Y \<in> measurable \<Omega> lborel \<and>
    distr \<Omega> borel Y = M \<and>
    (\<forall>x \<in> space \<Omega>. (\<lambda>n. Y_seq n x) \<longlonglongrightarrow> Y x)"
proof -
  interpret \<mu>: cdf_distribution "\<mu> n" for n
    unfolding cdf_distribution_def by (rule \<mu>)
  interpret M: cdf_distribution M
    unfolding cdf_distribution_def by (rule M)

  have conv: "measure M {x} = 0 \<Longrightarrow> (\<lambda>n. \<mu>.C n x) \<longlonglongrightarrow> M.C x" for x
    using \<mu>_to_M M.isCont_cdf by (auto simp: weak_conv_m_def weak_conv_def)

  let ?\<Omega> = "restrict_space lborel {0<..<1} :: real measure"
  have "prob_space ?\<Omega>"
    by (auto simp: space_restrict_space emeasure_restrict_space intro!: prob_spaceI)
  interpret \<Omega>: prob_space ?\<Omega>
    by fact

  have Y_distr: "distr ?\<Omega> borel M.I = M"
    by (rule M.distr_I_eq_M)

  have Y_cts_cnv: "(\<lambda>n. \<mu>.I n \<omega>) \<longlonglongrightarrow> M.I \<omega>"
    if \<omega>: "\<omega> \<in> {0<..<1}" "isCont M.I \<omega>" for \<omega> :: real
  proof (intro limsup_le_liminf_real)
    show "liminf (\<lambda>n. \<mu>.I n \<omega>) \<ge> M.I \<omega>"
      unfolding le_Liminf_iff
    proof safe
      fix B :: ereal assume B: "B < M.I \<omega>"
      then show "\<forall>\<^sub>F n in sequentially. B < \<mu>.I n \<omega>"
      proof (cases B)
        case (real r)
        with B have r: "r < M.I \<omega>"
          by simp
        then obtain x where x: "r < x" "x < M.I \<omega>" "measure M {x} = 0"
          using open_minus_countable[OF M.countable_support, of "{r<..<M.I \<omega>}"] by auto
        then have Fx_less: "M.C x < \<omega>"
          using M.pseudoinverse' \<omega> not_less by blast

        have "\<forall>\<^sub>F n in sequentially. \<mu>.C n x < \<omega>"
          using order_tendstoD(2)[OF conv[OF x(3)] Fx_less] .
        then have "\<forall>\<^sub>F n in sequentially. x < \<mu>.I n \<omega>"
          by eventually_elim (insert \<omega> \<mu>.pseudoinverse[symmetric], simp add: not_le[symmetric])
        then show ?thesis
          by eventually_elim (insert x(1), simp add: real)
      qed auto
    qed

    have *: "limsup (\<lambda>n. \<mu>.I n \<omega>) \<le> M.I \<omega>'"
      if \<omega>': "0 < \<omega>'" "\<omega>' < 1" "\<omega> < \<omega>'" for \<omega>' :: real
    proof (rule dense_ge_bounded)
      fix B' assume "ereal (M.I \<omega>') < B'" "B' < ereal (M.I \<omega>' + 1)"
      then obtain B where "M.I \<omega>' < B" and [simp]: "B' = ereal B"
        by (cases B') auto
      then obtain y where y: "M.I \<omega>' < y" "y < B" "measure M {y} = 0"
        using open_minus_countable[OF M.countable_support, of "{M.I \<omega>'<..<B}"] by auto
      then have "\<omega>' \<le> M.C (M.I \<omega>')"
        using M.pseudoinverse' \<omega>' by (metis greaterThanLessThan_iff order_refl)
      also have "... \<le> M.C y"
        using M.mono y unfolding mono_def by auto
      finally have Fy_gt: "\<omega> < M.C y"
        using \<omega>'(3) by simp

      have "\<forall>\<^sub>F n in sequentially. \<omega> \<le> \<mu>.C n y"
        using order_tendstoD(1)[OF conv[OF y(3)] Fy_gt] by eventually_elim (rule less_imp_le)
      then have 2: "\<forall>\<^sub>F n in sequentially. \<mu>.I n \<omega> \<le> ereal y"
        by simp (subst \<mu>.pseudoinverse'[rule_format, OF \<omega>(1), symmetric])
      then show "limsup (\<lambda>n. \<mu>.I n \<omega>) \<le> B'"
        using \<open>y < B\<close>
        by (intro Limsup_bounded[rotated]) (auto intro: le_less_trans elim: eventually_mono)
    qed simp

    have **: "(M.I \<longlongrightarrow> ereal (M.I \<omega>)) (at_right \<omega>)"
      using \<omega>(2) by (auto intro: tendsto_within_subset simp: continuous_at)
    show "limsup (\<lambda>n. \<mu>.I n \<omega>) \<le> M.I \<omega>"
      using \<omega>
      by (intro tendsto_lowerbound[OF **])
         (auto intro!: exI[of _ 1] * simp: eventually_at_right[of _ 1])
  qed

  let ?D = "{\<omega>\<in>{0<..<1}. \<not> isCont M.I \<omega>}"
  have D_countable: "countable ?D"
    using mono_on_ctble_discont[OF M.mono_I] by (simp add: at_within_open[of _ "{0 <..< 1}"] cong: conj_cong)
  hence D: "emeasure ?\<Omega> ?D = 0"
    using emeasure_lborel_countable[OF D_countable]
    by (subst emeasure_restrict_space) auto

  define Y' where "Y' \<omega> = (if \<omega> \<in> ?D then 0 else M.I \<omega>)" for \<omega>
  have Y'_AE: "AE \<omega> in ?\<Omega>. Y' \<omega> = M.I \<omega>"
    by (rule AE_I [OF _ D]) (auto simp: space_restrict_space sets_restrict_space_iff Y'_def)

  define Y_seq' where "Y_seq' n \<omega> = (if \<omega> \<in> ?D then 0 else \<mu>.I n \<omega>)" for n \<omega>
  have Y_seq'_AE: "\<And>n. AE \<omega> in ?\<Omega>. Y_seq' n \<omega> = \<mu>.I n \<omega>"
    by (rule AE_I [OF _ D]) (auto simp: space_restrict_space sets_restrict_space_iff Y_seq'_def)

  have Y'_cnv: "\<forall>\<omega>\<in>{0<..<1}. (\<lambda>n. Y_seq' n \<omega>) \<longlonglongrightarrow> Y' \<omega>"
    by (auto simp: Y'_def Y_seq'_def Y_cts_cnv)

  have [simp]: "Y_seq' n \<in> borel_measurable ?\<Omega>" for n
    by (rule measurable_discrete_difference[of "\<mu>.I n" _ _ ?D])
       (insert \<mu>.measurable_CI[of n] D_countable, auto simp: sets_restrict_space Y_seq'_def)
  moreover have "distr ?\<Omega> borel (Y_seq' n) = \<mu> n" for n
    using \<mu>.distr_I_eq_M [of n] Y_seq'_AE [of n]
    by (subst distr_cong_AE[where f = "Y_seq' n" and g = "\<mu>.I n"], auto)
  moreover have [simp]: "Y' \<in> borel_measurable ?\<Omega>"
    by (rule measurable_discrete_difference[of M.I _ _ ?D])
       (insert M.measurable_CI D_countable, auto simp: sets_restrict_space Y'_def)
  moreover have "distr ?\<Omega> borel Y' = M"
    using M.distr_I_eq_M Y'_AE
    by (subst distr_cong_AE[where f = Y' and g = M.I], auto)
  ultimately have "prob_space ?\<Omega> \<and> (\<forall>n. Y_seq' n \<in> borel_measurable ?\<Omega>) \<and>
    (\<forall>n. distr ?\<Omega> borel (Y_seq' n) = \<mu> n) \<and> Y' \<in> measurable ?\<Omega> lborel \<and> distr ?\<Omega> borel Y' = M \<and>
    (\<forall>x\<in>space ?\<Omega>. (\<lambda>n. Y_seq' n x) \<longlonglongrightarrow> Y' x)"
    using Y'_cnv \<open>prob_space ?\<Omega>\<close> by (auto simp: space_restrict_space)
  thus ?thesis by metis
qed

text \<open>
  The Portmanteau theorem, that is, the equivalence of various definitions of weak convergence.
\<close>

theorem weak_conv_imp_bdd_ae_continuous_conv:
  fixes
    f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes
    discont_null: "M ({x. \<not> isCont f x}) = 0" and
    f_bdd: "\<And>x. norm (f x) \<le> B" and
    [measurable]: "f \<in> borel_measurable borel"
  shows
    "(\<lambda> n. integral\<^sup>L (\<mu> n) f) \<longlonglongrightarrow> integral\<^sup>L M f"
proof -
  have "0 \<le> B"
    using norm_ge_zero f_bdd by (rule order_trans)
  note Skorohod
  then obtain Omega Y_seq Y where
    ps_Omega [simp]: "prob_space Omega" and
    Y_seq_measurable [measurable]: "\<And>n. Y_seq n \<in> borel_measurable Omega" and
    distr_Y_seq: "\<And>n. distr Omega borel (Y_seq n) = \<mu> n" and
    Y_measurable [measurable]: "Y \<in> borel_measurable Omega" and
    distr_Y: "distr Omega borel Y = M" and
    YnY: "\<And>x :: real. x \<in> space Omega \<Longrightarrow> (\<lambda>n. Y_seq n x) \<longlonglongrightarrow> Y x"  by force
  interpret prob_space Omega by fact
  have *: "emeasure Omega (Y -` {x. \<not> isCont f x} \<inter> space Omega) = 0"
    by (subst emeasure_distr [symmetric, where N=borel]) (auto simp: distr_Y discont_null)
  have *: "AE x in Omega. (\<lambda>n. f (Y_seq n x)) \<longlonglongrightarrow> f (Y x)"
    by (rule AE_I [OF _ *]) (auto intro: isCont_tendsto_compose YnY)
  show ?thesis
    by (auto intro!: integral_dominated_convergence[where w="\<lambda>x. B"]
             simp: f_bdd * integral_distr distr_Y_seq [symmetric] distr_Y [symmetric])
qed

theorem weak_conv_imp_integral_bdd_continuous_conv:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes
    "\<And>x. isCont f x" and
    "\<And>x. norm (f x) \<le> B"
  shows
    "(\<lambda> n. integral\<^sup>L (\<mu> n) f) \<longlonglongrightarrow> integral\<^sup>L M f"
  using assms
  by (intro weak_conv_imp_bdd_ae_continuous_conv)
     (auto intro!: borel_measurable_continuous_on1 continuous_at_imp_continuous_on)

theorem weak_conv_imp_continuity_set_conv:
  fixes f :: "real \<Rightarrow> real"
  assumes [measurable]: "A \<in> sets borel" and "M (frontier A) = 0"
  shows "(\<lambda>n. measure (\<mu> n) A) \<longlonglongrightarrow> measure M A"
proof -
  interpret M: real_distribution M by fact
  interpret \<mu>: real_distribution "\<mu> n" for n by fact

  have "(\<lambda>n. (\<integral>x. indicator A x \<partial>\<mu> n) :: real) \<longlonglongrightarrow> (\<integral>x. indicator A x \<partial>M)"
    by (intro weak_conv_imp_bdd_ae_continuous_conv[where B=1])
       (auto intro: assms simp: isCont_indicator)
  then show ?thesis
    by simp
qed

end

definition
  cts_step :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
where
  "cts_step a b x \<equiv> if x \<le> a then 1 else if x \<ge> b then 0 else (b - x) / (b - a)"

lemma cts_step_uniformly_continuous:
  assumes [arith]: "a < b"
  shows "uniformly_continuous_on UNIV (cts_step a b)"
  unfolding uniformly_continuous_on_def
proof clarsimp
  fix e :: real assume [arith]: "0 < e"
  let ?d = "min (e * (b - a)) (b - a)"
  have "?d > 0"
    by (auto simp add: field_simps)
  moreover have "dist x' x < ?d \<Longrightarrow> dist (cts_step a b x') (cts_step a b x) < e" for x x'
    by (auto simp: dist_real_def divide_simps cts_step_def)
  ultimately show "\<exists>d > 0. \<forall>x x'. dist x' x < d \<longrightarrow> dist (cts_step a b x') (cts_step a b x) < e"
    by blast
qed

lemma (in real_distribution) integrable_cts_step: "a < b \<Longrightarrow> integrable M (cts_step a b)"
  by (rule integrable_const_bound [of _ 1]) (auto simp: cts_step_def[abs_def])

lemma (in real_distribution) cdf_cts_step:
  assumes [arith]: "x < y"
  shows "cdf M x \<le> integral\<^sup>L M (cts_step x y)" and "integral\<^sup>L M (cts_step x y) \<le> cdf M y"
proof -
  have "cdf M x = integral\<^sup>L M (indicator {..x})"
    by (simp add: cdf_def)
  also have "\<dots> \<le> expectation (cts_step x y)"
    by (intro integral_mono integrable_cts_step)
       (auto simp: cts_step_def less_top[symmetric] split: split_indicator)
  finally show "cdf M x \<le> expectation (cts_step x y)" .
next
  have "expectation (cts_step x y) \<le> integral\<^sup>L M (indicator {..y})"
    by (intro integral_mono integrable_cts_step)
       (auto simp: cts_step_def less_top[symmetric] split: split_indicator)
  also have "\<dots> = cdf M y"
    by (simp add: cdf_def)
  finally show "expectation (cts_step x y) \<le> cdf M y" .
qed

context
  fixes M_seq :: "nat \<Rightarrow> real measure"
    and M :: "real measure"
  assumes distr_M_seq [simp]: "\<And>n. real_distribution (M_seq n)"
  assumes distr_M [simp]: "real_distribution M"
begin

theorem continuity_set_conv_imp_weak_conv:
  fixes f :: "real \<Rightarrow> real"
  assumes *: "\<And>A. A \<in> sets borel \<Longrightarrow> M (frontier A) = 0 \<Longrightarrow> (\<lambda> n. (measure (M_seq n) A)) \<longlonglongrightarrow> measure M A"
  shows "weak_conv_m M_seq M"
proof -
  interpret real_distribution M by simp
  show ?thesis
    by (auto intro!: * simp: frontier_real_atMost isCont_cdf emeasure_eq_measure weak_conv_m_def weak_conv_def cdf_def2)
qed

theorem integral_cts_step_conv_imp_weak_conv:
  assumes integral_conv: "\<And>x y. x < y \<Longrightarrow> (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step x y)) \<longlonglongrightarrow> integral\<^sup>L M (cts_step x y)"
  shows "weak_conv_m M_seq M"
  unfolding weak_conv_m_def weak_conv_def
proof (clarsimp)
  interpret real_distribution M by (rule distr_M)
  fix x assume "isCont (cdf M) x"
  hence left_cont: "continuous (at_left x) (cdf M)"
    unfolding continuous_at_split ..
  { fix y :: real assume [arith]: "x < y"
    have "limsup (\<lambda>n. cdf (M_seq n) x) \<le> limsup (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step x y))"
      by (auto intro!: Limsup_mono always_eventually real_distribution.cdf_cts_step)
    also have "\<dots> = integral\<^sup>L M (cts_step x y)"
      by (intro lim_imp_Limsup) (auto intro: integral_conv)
    also have "\<dots> \<le> cdf M y"
      by (simp add: cdf_cts_step)
    finally have "limsup (\<lambda>n. cdf (M_seq n) x) \<le> cdf M y" .
  } note * = this
  { fix y :: real assume [arith]: "x > y"
    have "cdf M y \<le> ereal (integral\<^sup>L M (cts_step y x))"
      by (simp add: cdf_cts_step)
    also have "\<dots> = liminf (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step y x))"
      by (intro lim_imp_Liminf[symmetric]) (auto intro: integral_conv)
    also have "\<dots> \<le> liminf (\<lambda>n. cdf (M_seq n) x)"
      by (auto intro!: Liminf_mono always_eventually real_distribution.cdf_cts_step)
    finally have "liminf (\<lambda>n. cdf (M_seq n) x) \<ge> cdf M y" .
  } note ** = this

  have "limsup (\<lambda>n. cdf (M_seq n) x) \<le> cdf M x"
  proof (rule tendsto_lowerbound)
    show "\<forall>\<^sub>F i in at_right x. limsup (\<lambda>xa. ereal (cdf (M_seq xa) x)) \<le> ereal (cdf M i)"
      by (subst eventually_at_right[of _ "x + 1"]) (auto simp: * intro: exI [of _ "x+1"])
  qed (insert cdf_is_right_cont, auto simp: continuous_within)
  moreover have "cdf M x \<le> liminf (\<lambda>n. cdf (M_seq n) x)"
  proof (rule tendsto_upperbound)
    show "\<forall>\<^sub>F i in at_left x. ereal (cdf M i) \<le> liminf (\<lambda>xa. ereal (cdf (M_seq xa) x))"
      by (subst eventually_at_left[of "x - 1"]) (auto simp: ** intro: exI [of _ "x-1"])
  qed (insert left_cont, auto simp: continuous_within)
  ultimately show "(\<lambda>n. cdf (M_seq n) x) \<longlonglongrightarrow> cdf M x"
    by (elim limsup_le_liminf_real)
qed

theorem integral_bdd_continuous_conv_imp_weak_conv:
  assumes
    "\<And>f. (\<And>x. isCont f x) \<Longrightarrow> (\<And>x. abs (f x) \<le> 1) \<Longrightarrow> (\<lambda>n. integral\<^sup>L (M_seq n) f::real) \<longlonglongrightarrow> integral\<^sup>L M f"
  shows
    "weak_conv_m M_seq M"
  apply (rule integral_cts_step_conv_imp_weak_conv [OF assms])
  apply (rule continuous_on_interior)
  apply (rule uniformly_continuous_imp_continuous)
  apply (rule cts_step_uniformly_continuous)
  apply (auto simp: cts_step_def)
  done

end

end
