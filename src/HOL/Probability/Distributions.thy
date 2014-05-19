theory Distributions
  imports Probability_Measure
begin

subsection {* Exponential distribution *}

definition exponential_density :: "real \<Rightarrow> real \<Rightarrow> real" where
  "exponential_density l x = (if x < 0 then 0 else l * exp (- x * l))"

lemma borel_measurable_exponential_density[measurable]: "exponential_density l \<in> borel_measurable borel"
  by (auto simp add: exponential_density_def[abs_def])

lemma (in prob_space) exponential_distributed_params:
  assumes D: "distributed M lborel X (exponential_density l)"
  shows "0 < l"
proof (cases l "0 :: real" rule: linorder_cases)
  assume "l < 0"
  have "emeasure lborel {0 <.. 1::real} \<le>
    emeasure lborel {x :: real \<in> space lborel. 0 < x}"
    by (rule emeasure_mono) (auto simp: greaterThan_def[symmetric])
  also have "emeasure lborel {x :: real \<in> space lborel. 0 < x} = 0"
  proof -
    have "AE x in lborel. 0 \<le> exponential_density l x"
      using assms by (auto simp: distributed_real_AE)
    then have "AE x in lborel. x \<le> (0::real)"
      apply eventually_elim 
      using `l < 0`
      apply (auto simp: exponential_density_def zero_le_mult_iff split: split_if_asm)
      done
    then show "emeasure lborel {x :: real \<in> space lborel. 0 < x} = 0"
      by (subst (asm) AE_iff_measurable[OF _ refl]) (auto simp: not_le greaterThan_def[symmetric])
  qed
  finally show "0 < l" by simp
next
  assume "l = 0"
  then have [simp]: "\<And>x. ereal (exponential_density l x) = 0"
    by (simp add: exponential_density_def)
  interpret X: prob_space "distr M lborel X"
    using distributed_measurable[OF D] by (rule prob_space_distr)
  from X.emeasure_space_1
  show "0 < l"
    by (simp add: emeasure_density distributed_distr_eq_density[OF D])
qed assumption

lemma
  assumes [arith]: "0 < l"
  shows emeasure_exponential_density_le0: "0 \<le> a \<Longrightarrow> emeasure (density lborel (exponential_density l)) {.. a} = 1 - exp (- a * l)"
    and prob_space_exponential_density: "prob_space (density lborel (exponential_density l))"
      (is "prob_space ?D")
proof -
  let ?f = "\<lambda>x. l * exp (- x * l)"
  let ?F = "\<lambda>x. - exp (- x * l)"

  have deriv: "\<And>x. DERIV ?F x :> ?f x" "\<And>x. 0 \<le> l * exp (- x * l)"
    by (auto intro!: derivative_eq_intros simp: zero_le_mult_iff)

  have "emeasure ?D (space ?D) = (\<integral>\<^sup>+ x. ereal (?f x) * indicator {0..} x \<partial>lborel)"
    by (auto simp: emeasure_density exponential_density_def
             intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ereal (0 - ?F 0)"
  proof (rule nn_integral_FTC_atLeast)
    have "((\<lambda>x. exp (l * x)) ---> 0) at_bot"
      by (rule filterlim_compose[OF exp_at_bot filterlim_tendsto_pos_mult_at_bot[of _ l]])
         (simp_all add: tendsto_const filterlim_ident)
    then show "((\<lambda>x. - exp (- x * l)) ---> 0) at_top"
      unfolding filterlim_at_top_mirror
      by (simp add: tendsto_minus_cancel_left[symmetric] ac_simps)
  qed (insert deriv, auto)
  also have "\<dots> = 1" by (simp add: one_ereal_def)
  finally have "emeasure ?D (space ?D) = 1" .
  then show "prob_space ?D" by rule

  assume "0 \<le> a"
  have "emeasure ?D {..a} = (\<integral>\<^sup>+x. ereal (?f x) * indicator {0..a} x \<partial>lborel)"
    by (auto simp add: emeasure_density intro!: nn_integral_cong split: split_indicator)
       (auto simp: exponential_density_def)
  also have "(\<integral>\<^sup>+x. ereal (?f x) * indicator {0..a} x \<partial>lborel) = ereal (?F a) - ereal (?F 0)"
    using `0 \<le> a` deriv by (intro nn_integral_FTC_atLeastAtMost) auto
  also have "\<dots> = 1 - exp (- a * l)"
    by simp
  finally show "emeasure ?D {.. a} = 1 - exp (- a * l)" .
qed


lemma (in prob_space) exponential_distributedD_le:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a"
  shows "\<P>(x in M. X x \<le> a) = 1 - exp (- a * l)"
proof -
  have "emeasure M {x \<in> space M. X x \<le> a } = emeasure (distr M lborel X) {.. a}"
    using distributed_measurable[OF D] 
    by (subst emeasure_distr) (auto intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = emeasure (density lborel (exponential_density l)) {.. a}"
    unfolding distributed_distr_eq_density[OF D] ..
  also have "\<dots> = 1 - exp (- a * l)"
    using emeasure_exponential_density_le0[OF exponential_distributed_params[OF D] a] .
  finally show ?thesis
    by (auto simp: measure_def)
qed

lemma (in prob_space) exponential_distributedD_gt:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a"
  shows "\<P>(x in M. a < X x ) = exp (- a * l)"
proof -
  have "exp (- a * l) = 1 - \<P>(x in M. X x \<le> a)"
    unfolding exponential_distributedD_le[OF D a] by simp
  also have "\<dots> = prob (space M - {x \<in> space M. X x \<le> a })"
    using distributed_measurable[OF D]
    by (subst prob_compl) auto
  also have "\<dots> = \<P>(x in M. a < X x )"
    by (auto intro!: arg_cong[where f=prob] simp: not_le)
  finally show ?thesis by simp
qed

lemma (in prob_space) exponential_distributed_memoryless:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a"and t: "0 \<le> t"
  shows "\<P>(x in M. a + t < X x \<bar> a < X x) = \<P>(x in M. t < X x)"
proof -
  have "\<P>(x in M. a + t < X x \<bar> a < X x) = \<P>(x in M. a + t < X x) / \<P>(x in M. a < X x)"
    using `0 \<le> t` by (auto simp: cond_prob_def intro!: arg_cong[where f=prob] arg_cong2[where f="op /"])
  also have "\<dots> = exp (- (a + t) * l) / exp (- a * l)"
    using a t by (simp add: exponential_distributedD_gt[OF D])
  also have "\<dots> = exp (- t * l)"
    using exponential_distributed_params[OF D] by (auto simp: field_simps exp_add[symmetric])
  finally show ?thesis
    using t by (simp add: exponential_distributedD_gt[OF D])
qed

lemma exponential_distributedI:
  assumes X[measurable]: "X \<in> borel_measurable M" and [arith]: "0 < l"
    and X_distr: "\<And>a. 0 \<le> a \<Longrightarrow> emeasure M {x\<in>space M. X x \<le> a} = 1 - exp (- a * l)"
  shows "distributed M lborel X (exponential_density l)"
proof (rule distributedI_borel_atMost)
  fix a :: real

  { assume "a \<le> 0"  
    with X have "emeasure M {x\<in>space M. X x \<le> a} \<le> emeasure M {x\<in>space M. X x \<le> 0}"
      by (intro emeasure_mono) auto
    then have "emeasure M {x\<in>space M. X x \<le> a} = 0"
      using X_distr[of 0] by (simp add: one_ereal_def emeasure_le_0_iff) }
  note eq_0 = this

  have "\<And>x. \<not> 0 \<le> a \<Longrightarrow> ereal (exponential_density l x) * indicator {..a} x = 0"
    by (simp add: exponential_density_def)
  then show "(\<integral>\<^sup>+ x. exponential_density l x * indicator {..a} x \<partial>lborel) = ereal (if 0 \<le> a then 1 - exp (- a * l) else 0)"
    using emeasure_exponential_density_le0[of l a]
    by (auto simp: emeasure_density times_ereal.simps[symmetric] ereal_indicator
             simp del: times_ereal.simps ereal_zero_times)
  show "emeasure M {x\<in>space M. X x \<le> a} = ereal (if 0 \<le> a then 1 - exp (- a * l) else 0)"
    using X_distr[of a] eq_0 by (auto simp: one_ereal_def)
  show "AE x in lborel. 0 \<le> exponential_density l x "
    by (auto simp: exponential_density_def)
qed simp_all

lemma (in prob_space) exponential_distributed_iff:
  "distributed M lborel X (exponential_density l) \<longleftrightarrow>
    (X \<in> borel_measurable M \<and> 0 < l \<and> (\<forall>a\<ge>0. \<P>(x in M. X x \<le> a) = 1 - exp (- a * l)))"
  using
    distributed_measurable[of M lborel X "exponential_density l"]
    exponential_distributed_params[of X l]
    emeasure_exponential_density_le0[of l]
    exponential_distributedD_le[of X l]
  by (auto intro!: exponential_distributedI simp: one_ereal_def emeasure_eq_measure)

lemma borel_integral_x_exp:
  "has_bochner_integral lborel (\<lambda>x. x * exp (- x) * indicator {0::real ..} x) 1"
proof (rule has_bochner_integral_monotone_convergence)
  let ?f = "\<lambda>i x. x * exp (- x) * indicator {0::real .. i} x"
  have "eventually (\<lambda>b::real. 0 \<le> b) at_top"
    by (rule eventually_ge_at_top)
  then have "eventually (\<lambda>b. 1 - (inverse (exp b) + b / exp b) = integral\<^sup>L lborel (?f b)) at_top"
  proof eventually_elim
   fix b :: real assume [simp]: "0 \<le> b"
    have "(\<integral>x. (exp (-x)) * indicator {0 .. b} x \<partial>lborel) - (integral\<^sup>L lborel (?f b)) = 
      (\<integral>x. (exp (-x) - x * exp (-x)) * indicator {0 .. b} x \<partial>lborel)"
      by (subst integral_diff[symmetric])
         (auto intro!: borel_integrable_atLeastAtMost integral_cong split: split_indicator)
    also have "\<dots> = b * exp (-b) - 0 * exp (- 0)"
    proof (rule integral_FTC_atLeastAtMost)
      fix x assume "0 \<le> x" "x \<le> b"
      show "DERIV (\<lambda>x. x * exp (-x)) x :> exp (-x) - x * exp (-x)"
        by (auto intro!: derivative_eq_intros)
      show "isCont (\<lambda>x. exp (- x) - x * exp (- x)) x "
        by (intro continuous_intros)
    qed fact
    also have "(\<integral>x. (exp (-x)) * indicator {0 .. b} x \<partial>lborel) = - exp (- b) - - exp (- 0)"
      by (rule integral_FTC_atLeastAtMost) (auto intro!: derivative_eq_intros)
    finally show "1 - (inverse (exp b) + b / exp b) = integral\<^sup>L lborel (?f b)"
      by (auto simp: field_simps exp_minus inverse_eq_divide)
  qed
  then have "((\<lambda>i. integral\<^sup>L lborel (?f i)) ---> 1 - (0 + 0)) at_top"
  proof (rule Lim_transform_eventually)
    show "((\<lambda>i. 1 - (inverse (exp i) + i / exp i)) ---> 1 - (0 + 0 :: real)) at_top"
      using tendsto_power_div_exp_0[of 1]
      by (intro tendsto_intros tendsto_inverse_0_at_top exp_at_top) simp
  qed
  then show "(\<lambda>i. integral\<^sup>L lborel (?f i)) ----> 1"
    by (intro filterlim_compose[OF _ filterlim_real_sequentially]) simp
  show "AE x in lborel. mono (\<lambda>n::nat. x * exp (- x) * indicator {0..real n} x)"
    by (auto simp: mono_def mult_le_0_iff zero_le_mult_iff split: split_indicator)
  show "\<And>i::nat. integrable lborel (\<lambda>x. x * exp (- x) * indicator {0..real i} x)"
    by (rule borel_integrable_atLeastAtMost) auto
  show "AE x in lborel. (\<lambda>i. x * exp (- x) * indicator {0..real i} x) ----> x * exp (- x) * indicator {0..} x"
    apply (intro AE_I2 Lim_eventually )
    apply (rule_tac c="natfloor x + 1" in eventually_sequentiallyI)
    apply (auto simp add: not_le dest!: ge_natfloor_plus_one_imp_gt[simplified] split: split_indicator)
    done
qed (auto intro!: borel_measurable_times borel_measurable_exp)

lemma (in prob_space) exponential_distributed_expectation:
  assumes D: "distributed M lborel X (exponential_density l)"
  shows "expectation X = 1 / l"
proof (subst distributed_integral[OF D, of "\<lambda>x. x", symmetric])
  have "0 < l"
   using exponential_distributed_params[OF D] .
  have [simp]: "\<And>x. x * (l * (exp (- (x * l)) * indicator {0..} (x * l))) =
    x * exponential_density l x"
    using `0 < l`
    by (auto split: split_indicator simp: zero_le_mult_iff exponential_density_def)
  from borel_integral_x_exp `0 < l`
  have "has_bochner_integral lborel (\<lambda>x. exponential_density l x * x) (1 / l)"
    by (subst (asm) lborel_has_bochner_integral_real_affine_iff[of l _ _ 0])
       (simp_all add: field_simps)
  then show "(\<integral> x. exponential_density l x * x \<partial>lborel) = 1 / l"
    by (metis has_bochner_integral_integral_eq)
qed simp

subsection {* Uniform distribution *}

lemma uniform_distrI:
  assumes X: "X \<in> measurable M M'"
    and A: "A \<in> sets M'" "emeasure M' A \<noteq> \<infinity>" "emeasure M' A \<noteq> 0"
  assumes distr: "\<And>B. B \<in> sets M' \<Longrightarrow> emeasure M (X -` B \<inter> space M) = emeasure M' (A \<inter> B) / emeasure M' A"
  shows "distr M M' X = uniform_measure M' A"
  unfolding uniform_measure_def
proof (intro measure_eqI)
  let ?f = "\<lambda>x. indicator A x / emeasure M' A"
  fix B assume B: "B \<in> sets (distr M M' X)"
  with X have "emeasure M (X -` B \<inter> space M) = emeasure M' (A \<inter> B) / emeasure M' A"
    by (simp add: distr[of B] measurable_sets)
  also have "\<dots> = (1 / emeasure M' A) * emeasure M' (A \<inter> B)"
     by simp
  also have "\<dots> = (\<integral>\<^sup>+ x. (1 / emeasure M' A) * indicator (A \<inter> B) x \<partial>M')"
    using A B
    by (intro nn_integral_cmult_indicator[symmetric]) (auto intro!: zero_le_divide_ereal)
  also have "\<dots> = (\<integral>\<^sup>+ x. ?f x * indicator B x \<partial>M')"
    by (rule nn_integral_cong) (auto split: split_indicator)
  finally show "emeasure (distr M M' X) B = emeasure (density M' ?f) B"
    using A B X by (auto simp add: emeasure_distr emeasure_density)
qed simp

lemma uniform_distrI_borel:
  fixes A :: "real set"
  assumes X[measurable]: "X \<in> borel_measurable M" and A: "emeasure lborel A = ereal r" "0 < r"
    and [measurable]: "A \<in> sets borel"
  assumes distr: "\<And>a. emeasure M {x\<in>space M. X x \<le> a} = emeasure lborel (A \<inter> {.. a}) / r"
  shows "distributed M lborel X (\<lambda>x. indicator A x / measure lborel A)"
proof (rule distributedI_borel_atMost)
  let ?f = "\<lambda>x. 1 / r * indicator A x"
  fix a
  have "emeasure lborel (A \<inter> {..a}) \<le> emeasure lborel A"
    using A by (intro emeasure_mono) auto
  also have "\<dots> < \<infinity>"
    using A by simp
  finally have fin: "emeasure lborel (A \<inter> {..a}) \<noteq> \<infinity>"
    by simp
  from emeasure_eq_ereal_measure[OF this]
  have fin_eq: "emeasure lborel (A \<inter> {..a}) / r = ereal (measure lborel (A \<inter> {..a}) / r)"
    using A by simp
  then show "emeasure M {x\<in>space M. X x \<le> a} = ereal (measure lborel (A \<inter> {..a}) / r)"
    using distr by simp
 
  have "(\<integral>\<^sup>+ x. ereal (indicator A x / measure lborel A * indicator {..a} x) \<partial>lborel) =
    (\<integral>\<^sup>+ x. ereal (1 / measure lborel A) * indicator (A \<inter> {..a}) x \<partial>lborel)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ereal (1 / measure lborel A) * emeasure lborel (A \<inter> {..a})"
    using `A \<in> sets borel`
    by (intro nn_integral_cmult_indicator) (auto simp: measure_nonneg)
  also have "\<dots> = ereal (measure lborel (A \<inter> {..a}) / r)"
    unfolding emeasure_eq_ereal_measure[OF fin] using A by (simp add: measure_def)
  finally show "(\<integral>\<^sup>+ x. ereal (indicator A x / measure lborel A * indicator {..a} x) \<partial>lborel) =
    ereal (measure lborel (A \<inter> {..a}) / r)" .
qed (auto simp: measure_nonneg)

lemma (in prob_space) uniform_distrI_borel_atLeastAtMost:
  fixes a b :: real
  assumes X: "X \<in> borel_measurable M" and "a < b"
  assumes distr: "\<And>t. a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow> \<P>(x in M. X x \<le> t) = (t - a) / (b - a)"
  shows "distributed M lborel X (\<lambda>x. indicator {a..b} x / measure lborel {a..b})"
proof (rule uniform_distrI_borel)
  fix t
  have "t < a \<or> (a \<le> t \<and> t \<le> b) \<or> b < t"
    by auto
  then show "emeasure M {x\<in>space M. X x \<le> t} = emeasure lborel ({a .. b} \<inter> {..t}) / (b - a)"
  proof (elim disjE conjE)
    assume "t < a" 
    then have "emeasure M {x\<in>space M. X x \<le> t} \<le> emeasure M {x\<in>space M. X x \<le> a}"
      using X by (auto intro!: emeasure_mono measurable_sets)
    also have "\<dots> = 0"
      using distr[of a] `a < b` by (simp add: emeasure_eq_measure)
    finally have "emeasure M {x\<in>space M. X x \<le> t} = 0"
      by (simp add: antisym measure_nonneg emeasure_le_0_iff)
    with `t < a` show ?thesis by simp
  next
    assume bnds: "a \<le> t" "t \<le> b"
    have "{a..b} \<inter> {..t} = {a..t}"
      using bnds by auto
    then show ?thesis using `a \<le> t` `a < b`
      using distr[OF bnds] by (simp add: emeasure_eq_measure)
  next
    assume "b < t" 
    have "1 = emeasure M {x\<in>space M. X x \<le> b}"
      using distr[of b] `a < b` by (simp add: one_ereal_def emeasure_eq_measure)
    also have "\<dots> \<le> emeasure M {x\<in>space M. X x \<le> t}"
      using X `b < t` by (auto intro!: emeasure_mono measurable_sets)
    finally have "emeasure M {x\<in>space M. X x \<le> t} = 1"
       by (simp add: antisym emeasure_eq_measure one_ereal_def)
    with `b < t` `a < b` show ?thesis by (simp add: measure_def one_ereal_def)
  qed
qed (insert X `a < b`, auto)

lemma (in prob_space) uniform_distributed_measure:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  assumes " a \<le> t" "t \<le> b"
  shows "\<P>(x in M. X x \<le> t) = (t - a) / (b - a)"
proof -
  have "emeasure M {x \<in> space M. X x \<le> t} = emeasure (distr M lborel X) {.. t}"
    using distributed_measurable[OF D]
    by (subst emeasure_distr) (auto intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = (\<integral>\<^sup>+x. ereal (1 / (b - a)) * indicator {a .. t} x \<partial>lborel)"
    using distributed_borel_measurable[OF D] `a \<le> t` `t \<le> b`
    unfolding distributed_distr_eq_density[OF D]
    by (subst emeasure_density)
       (auto intro!: nn_integral_cong simp: measure_def split: split_indicator)
  also have "\<dots> = ereal (1 / (b - a)) * (t - a)"
    using `a \<le> t` `t \<le> b`
    by (subst nn_integral_cmult_indicator) auto
  finally show ?thesis
    by (simp add: measure_def)
qed

lemma (in prob_space) uniform_distributed_bounds:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  shows "a < b"
proof (rule ccontr)
  assume "\<not> a < b"
  then have "{a .. b} = {} \<or> {a .. b} = {a .. a}" by simp
  with uniform_distributed_params[OF D] show False 
    by (auto simp: measure_def)
qed

lemma (in prob_space) uniform_distributed_iff:
  fixes a b :: real
  shows "distributed M lborel X (\<lambda>x. indicator {a..b} x / measure lborel {a..b}) \<longleftrightarrow> 
    (X \<in> borel_measurable M \<and> a < b \<and> (\<forall>t\<in>{a .. b}. \<P>(x in M. X x \<le> t)= (t - a) / (b - a)))"
  using
    uniform_distributed_bounds[of X a b]
    uniform_distributed_measure[of X a b]
    distributed_measurable[of M lborel X]
  by (auto intro!: uniform_distrI_borel_atLeastAtMost 
              simp: one_ereal_def emeasure_eq_measure
              simp del: measure_lborel)

lemma (in prob_space) uniform_distributed_expectation:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  shows "expectation X = (a + b) / 2"
proof (subst distributed_integral[OF D, of "\<lambda>x. x", symmetric])
  have "a < b"
    using uniform_distributed_bounds[OF D] .

  have "(\<integral> x. indicator {a .. b} x / measure lborel {a .. b} * x \<partial>lborel) = 
    (\<integral> x. (x / measure lborel {a .. b}) * indicator {a .. b} x \<partial>lborel)"
    by (intro integral_cong) auto
  also have "(\<integral> x. (x / measure lborel {a .. b}) * indicator {a .. b} x \<partial>lborel) = (a + b) / 2"
  proof (subst integral_FTC_atLeastAtMost)
    fix x
    show "DERIV (\<lambda>x. x\<^sup>2 / (2 * measure lborel {a..b})) x :> x / measure lborel {a..b}"
      using uniform_distributed_params[OF D]
      by (auto intro!: derivative_eq_intros)
    show "isCont (\<lambda>x. x / Sigma_Algebra.measure lborel {a..b}) x"
      using uniform_distributed_params[OF D]
      by (auto intro!: isCont_divide)
    have *: "b\<^sup>2 / (2 * measure lborel {a..b}) - a\<^sup>2 / (2 * measure lborel {a..b}) =
      (b*b - a * a) / (2 * (b - a))"
      using `a < b`
      by (auto simp: measure_def power2_eq_square diff_divide_distrib[symmetric])
    show "b\<^sup>2 / (2 * measure lborel {a..b}) - a\<^sup>2 / (2 * measure lborel {a..b}) = (a + b) / 2"
      using `a < b`
      unfolding * square_diff_square_factored by (auto simp: field_simps)
  qed (insert `a < b`, simp)
  finally show "(\<integral> x. indicator {a .. b} x / measure lborel {a .. b} * x \<partial>lborel) = (a + b) / 2" .
qed auto

end
