(*  Title:      HOL/Probability/Distributions.thy
    Author:     Sudeep Kanav, TU München
    Author:     Johannes Hölzl, TU München
    Author:     Jeremy Avigad, CMU *)

section \<open>Properties of Various Distributions\<close>

theory Distributions
  imports Convolution Information
begin

lemma (in prob_space) distributed_affine:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes f: "distributed M lborel X f"
  assumes c: "c \<noteq> 0"
  shows "distributed M lborel (\<lambda>x. t + c * X x) (\<lambda>x. f ((x - t) / c) / \<bar>c\<bar>)"
  unfolding distributed_def
proof safe
  have [measurable]: "f \<in> borel_measurable borel"
    using f by (simp add: distributed_def)
  have [measurable]: "X \<in> borel_measurable M"
    using f by (simp add: distributed_def)

  show "(\<lambda>x. f ((x - t) / c) / \<bar>c\<bar>) \<in> borel_measurable lborel"
    by simp
  show "random_variable lborel (\<lambda>x. t + c * X x)"
    by simp

  have eq: "ennreal \<bar>c\<bar> * (f x / ennreal \<bar>c\<bar>) = f x" for x
    using c
    by (cases "f x")
       (auto simp: divide_ennreal ennreal_mult[symmetric] ennreal_top_divide ennreal_mult_top)

  have "density lborel f = distr M lborel X"
    using f by (simp add: distributed_def)
  with c show "distr M lborel (\<lambda>x. t + c * X x) = density lborel (\<lambda>x. f ((x - t) / c) / ennreal \<bar>c\<bar>)"
    by (subst (2) lborel_real_affine[where c="c" and t="t"])
       (simp_all add: density_density_eq density_distr distr_distr field_simps eq cong: distr_cong)
qed

lemma (in prob_space) distributed_affineI:
  fixes f :: "real \<Rightarrow> ennreal" and c :: real
  assumes f: "distributed M lborel (\<lambda>x. (X x - t) / c) (\<lambda>x. \<bar>c\<bar> * f (x * c + t))"
  assumes c: "c \<noteq> 0"
  shows "distributed M lborel X f"
proof -
  have eq: "f x * ennreal \<bar>c\<bar> / ennreal \<bar>c\<bar> = f x" for x
    using c by (simp add: ennreal_times_divide[symmetric])

  show ?thesis
    using distributed_affine[OF f c, where t=t] c
    by (simp add: field_simps eq)
qed

lemma (in prob_space) distributed_AE2:
  assumes [measurable]: "distributed M N X f" "Measurable.pred N P"
  shows "(AE x in M. P (X x)) \<longleftrightarrow> (AE x in N. 0 < f x \<longrightarrow> P x)"
proof -
  have "(AE x in M. P (X x)) \<longleftrightarrow> (AE x in distr M N X. P x)"
    by (simp add: AE_distr_iff)
  also have "\<dots> \<longleftrightarrow> (AE x in density N f. P x)"
    unfolding distributed_distr_eq_density[OF assms(1)] ..
  also have "\<dots> \<longleftrightarrow>  (AE x in N. 0 < f x \<longrightarrow> P x)"
    by (rule AE_density) simp
  finally show ?thesis .
qed

subsection \<open>Erlang\<close>

lemma nn_intergal_power_times_exp_Icc:
  assumes [arith]: "0 \<le> a"
  shows "(\<integral>\<^sup>+x. ennreal (x^k * exp (-x)) * indicator {0 .. a} x \<partial>lborel) =
    (1 - (\<Sum>n\<le>k. (a^n * exp (-a)) / fact n)) * fact k" (is "?I = _")
proof -
  let ?f = "\<lambda>k x. x^k * exp (-x) / fact k"
  let ?F = "\<lambda>k x. - (\<Sum>n\<le>k. (x^n * exp (-x)) / fact n)"
  have "?I * (inverse (real_of_nat (fact k))) =
      (\<integral>\<^sup>+x. ennreal (x^k * exp (-x)) * indicator {0 .. a} x * (inverse (real_of_nat (fact k))) \<partial>lborel)"
    by (intro nn_integral_multc[symmetric]) auto
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (?f k x) * indicator {0 .. a} x \<partial>lborel)"
    by (intro nn_integral_cong)
       (simp add: field_simps ennreal_mult'[symmetric] indicator_mult_ennreal)
  also have "\<dots> = ennreal (?F k a - ?F k 0)"
  proof (rule nn_integral_FTC_Icc)
    fix x assume "x \<in> {0..a}"
    show "DERIV (?F k) x :> ?f k x"
    proof(induction k)
      case 0 show ?case by (auto intro!: derivative_eq_intros)
    next
      case (Suc k)
      have "DERIV (\<lambda>x. ?F k x - (x^Suc k * exp (-x)) / fact (Suc k)) x :>
        ?f k x - ((real (Suc k) - x) * x ^ k * exp (- x)) / (fact (Suc k))"
        by (intro DERIV_diff Suc)
           (auto intro!: derivative_eq_intros simp del: fact_Suc power_Suc
                 simp add: field_simps power_Suc[symmetric])
      also have "(\<lambda>x. ?F k x - (x^Suc k * exp (-x)) / fact (Suc k)) = ?F (Suc k)"
        by simp
      also have "?f k x - ((real (Suc k) - x) * x ^ k * exp (- x)) / (fact (Suc k)) = ?f (Suc k) x"
        by (auto simp: field_simps simp del: fact_Suc)
           (simp_all add: of_nat_Suc field_simps)
      finally show ?case .
    qed
  qed auto
  also have "\<dots> = ennreal (1 - (\<Sum>n\<le>k. (a^n * exp (-a)) / fact n))"
    by (auto simp: power_0_left if_distrib[where f="\<lambda>x. x / a" for a] sum.If_cases)
  also have "\<dots> = ennreal ((1 - (\<Sum>n\<le>k. (a^n * exp (-a)) / fact n)) * fact k) * ennreal (inverse (fact k))"
    by (subst ennreal_mult''[symmetric]) (auto intro!: arg_cong[where f=ennreal])
  finally show ?thesis
    by (auto simp add: mult_right_ennreal_cancel le_less)
qed

lemma nn_intergal_power_times_exp_Ici:
  shows "(\<integral>\<^sup>+x. ennreal (x^k * exp (-x)) * indicator {0 ..} x \<partial>lborel) = real_of_nat (fact k)"
proof (rule LIMSEQ_unique)
  let ?X = "\<lambda>n. \<integral>\<^sup>+ x. ennreal (x^k * exp (-x)) * indicator {0 .. real n} x \<partial>lborel"
  show "?X \<longlonglongrightarrow> (\<integral>\<^sup>+x. ennreal (x^k * exp (-x)) * indicator {0 ..} x \<partial>lborel)"
    apply (intro nn_integral_LIMSEQ)
    apply (auto simp: incseq_def le_fun_def eventually_sequentially
                split: split_indicator intro!: tendsto_eventually)
    apply (metis nat_ceiling_le_eq)
    done

  have "((\<lambda>x::real. (1 - (\<Sum>n\<le>k. (x ^ n / exp x) / (fact n))) * fact k) \<longlongrightarrow>
        (1 - (\<Sum>n\<le>k. 0 / (fact n))) * fact k) at_top"
    by (intro tendsto_intros tendsto_power_div_exp_0) simp
  then show "?X \<longlonglongrightarrow> real_of_nat (fact k)"
    by (subst nn_intergal_power_times_exp_Icc)
       (auto simp: exp_minus field_simps intro!: filterlim_compose[OF _ filterlim_real_sequentially])
qed

definition erlang_density :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "erlang_density k l x = (if x < 0 then 0 else (l^(Suc k) * x^k * exp (- l * x)) / fact k)"

definition erlang_CDF ::  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "erlang_CDF k l x = (if x < 0 then 0 else 1 - (\<Sum>n\<le>k. ((l * x)^n * exp (- l * x) / fact n)))"

lemma erlang_density_nonneg[simp]: "0 \<le> l \<Longrightarrow> 0 \<le> erlang_density k l x"
  by (simp add: erlang_density_def)

lemma borel_measurable_erlang_density[measurable]: "erlang_density k l \<in> borel_measurable borel"
  by (auto simp add: erlang_density_def[abs_def])

lemma erlang_CDF_transform: "0 < l \<Longrightarrow> erlang_CDF k l a = erlang_CDF k 1 (l * a)"
  by (auto simp add: erlang_CDF_def mult_less_0_iff)

lemma erlang_CDF_nonneg[simp]: assumes "0 < l" shows "0 \<le> erlang_CDF k l x"
 unfolding erlang_CDF_def
proof (clarsimp simp: not_less)
  assume "0 \<le> x"
  have "(\<Sum>n\<le>k. (l * x) ^ n * exp (- (l * x)) / fact n) =
    exp (- (l * x)) * (\<Sum>n\<le>k. (l * x) ^ n / fact n)"
    unfolding sum_distrib_left by (intro sum.cong) (auto simp: field_simps)
  also have "\<dots> = (\<Sum>n\<le>k. (l * x) ^ n / fact n) / exp (l * x)"
    by (simp add: exp_minus field_simps)
  also have "\<dots> \<le> 1"
  proof (subst divide_le_eq_1_pos)
    show "(\<Sum>n\<le>k. (l * x) ^ n / fact n) \<le> exp (l * x)"
      using \<open>0 < l\<close> \<open>0 \<le> x\<close> summable_exp_generic[of "l * x"]
      by (auto simp: exp_def divide_inverse ac_simps intro!: sum_le_suminf)
  qed simp
  finally show "(\<Sum>n\<le>k. (l * x) ^ n * exp (- (l * x)) / fact n) \<le> 1" .
qed

lemma nn_integral_erlang_density:
  assumes [arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x. ennreal (erlang_density k l x) * indicator {.. a} x \<partial>lborel) = erlang_CDF k l a"
proof (cases "0 \<le> a")
  case [arith]: True
  have eq: "\<And>x. indicator {0..a} (x / l) = indicator {0..a*l} x"
    by (simp add: field_simps split: split_indicator)
  have "(\<integral>\<^sup>+x. ennreal (erlang_density k l x) * indicator {.. a} x \<partial>lborel) =
    (\<integral>\<^sup>+x. (l/fact k) * (ennreal ((l*x)^k * exp (- (l*x))) * indicator {0 .. a} x) \<partial>lborel)"
    by (intro nn_integral_cong)
       (auto simp: erlang_density_def power_mult_distrib ennreal_mult[symmetric] split: split_indicator)
  also have "\<dots> = (l/fact k) * (\<integral>\<^sup>+x. ennreal ((l*x)^k * exp (- (l*x))) * indicator {0 .. a} x \<partial>lborel)"
    by (intro nn_integral_cmult) auto
  also have "\<dots> = ennreal (l/fact k) * ((1/l) * (\<integral>\<^sup>+x. ennreal (x^k * exp (- x)) * indicator {0 .. l * a} x \<partial>lborel))"
    by (subst nn_integral_real_affine[where c="1 / l" and t=0]) (auto simp: field_simps eq)
  also have "\<dots> = (1 - (\<Sum>n\<le>k. ((l * a)^n * exp (-(l * a))) / fact n))"
    by (subst nn_intergal_power_times_exp_Icc) (auto simp: ennreal_mult'[symmetric])
  also have "\<dots> = erlang_CDF k l a"
    by (auto simp: erlang_CDF_def)
  finally show ?thesis .
next
  case False
  then have "(\<integral>\<^sup>+ x. ennreal (erlang_density k l x) * indicator {.. a} x \<partial>lborel) = (\<integral>\<^sup>+x. 0 \<partial>(lborel::real measure))"
    by (intro nn_integral_cong) (auto simp: erlang_density_def)
  with False show ?thesis
    by (simp add: erlang_CDF_def)
qed

lemma emeasure_erlang_density:
  "0 < l \<Longrightarrow> emeasure (density lborel (erlang_density k l)) {.. a} = erlang_CDF k l a"
  by (simp add: emeasure_density nn_integral_erlang_density)

lemma nn_integral_erlang_ith_moment:
  fixes k i :: nat and l :: real
  assumes [arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x. ennreal (erlang_density k l x * x ^ i) \<partial>lborel) = fact (k + i) / (fact k * l ^ i)"
proof -
  have eq: "\<And>x. indicator {0..} (x / l) = indicator {0..} x"
    by (simp add: field_simps split: split_indicator)
  have "(\<integral>\<^sup>+ x. ennreal (erlang_density k l x * x^i) \<partial>lborel) =
    (\<integral>\<^sup>+x. (l/(fact k * l^i)) * (ennreal ((l*x)^(k+i) * exp (- (l*x))) * indicator {0 ..} x) \<partial>lborel)"
    by (intro nn_integral_cong)
       (auto simp: erlang_density_def power_mult_distrib power_add ennreal_mult'[symmetric] split: split_indicator)
  also have "\<dots> = (l/(fact k * l^i)) * (\<integral>\<^sup>+x. ennreal ((l*x)^(k+i) * exp (- (l*x))) * indicator {0 ..} x \<partial>lborel)"
    by (intro nn_integral_cmult) auto
  also have "\<dots> = ennreal (l/(fact k * l^i)) * ((1/l) * (\<integral>\<^sup>+x. ennreal (x^(k+i) * exp (- x)) * indicator {0 ..} x \<partial>lborel))"
    by (subst nn_integral_real_affine[where c="1 / l" and t=0]) (auto simp: field_simps eq)
  also have "\<dots> = fact (k + i) / (fact k * l ^ i)"
    by (subst nn_intergal_power_times_exp_Ici) (auto simp: ennreal_mult'[symmetric])
  finally show ?thesis .
qed

lemma prob_space_erlang_density:
  assumes l[arith]: "0 < l"
  shows "prob_space (density lborel (erlang_density k l))" (is "prob_space ?D")
proof
  show "emeasure ?D (space ?D) = 1"
    using nn_integral_erlang_ith_moment[OF l, where k=k and i=0] by (simp add: emeasure_density)
qed

lemma (in prob_space) erlang_distributed_le:
  assumes D: "distributed M lborel X (erlang_density k l)"
  assumes [simp, arith]: "0 < l" "0 \<le> a"
  shows "\<P>(x in M. X x \<le> a) = erlang_CDF k l a"
proof -
  have "emeasure M {x \<in> space M. X x \<le> a } = emeasure (distr M lborel X) {.. a}"
    using distributed_measurable[OF D]
    by (subst emeasure_distr) (auto intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = emeasure (density lborel (erlang_density k l)) {.. a}"
    unfolding distributed_distr_eq_density[OF D] ..
  also have "\<dots> = erlang_CDF k l a"
    by (auto intro!: emeasure_erlang_density)
  finally show ?thesis
    by (auto simp: emeasure_eq_measure measure_nonneg)
qed

lemma (in prob_space) erlang_distributed_gt:
  assumes D[simp]: "distributed M lborel X (erlang_density k l)"
  assumes [arith]: "0 < l" "0 \<le> a"
  shows "\<P>(x in M. a < X x ) = 1 - (erlang_CDF k l a)"
proof -
  have " 1 - (erlang_CDF k l a) = 1 - \<P>(x in M. X x \<le> a)" by (subst erlang_distributed_le) auto
  also have "\<dots> = prob (space M - {x \<in> space M. X x \<le> a })"
    using distributed_measurable[OF D] by (auto simp: prob_compl)
  also have "\<dots> = \<P>(x in M. a < X x )" by (auto intro!: arg_cong[where f=prob] simp: not_le)
  finally show ?thesis by simp
qed

lemma erlang_CDF_at0: "erlang_CDF k l 0 = 0"
  by (induction k) (auto simp: erlang_CDF_def)

lemma erlang_distributedI:
  assumes X[measurable]: "X \<in> borel_measurable M" and [arith]: "0 < l"
    and X_distr: "\<And>a. 0 \<le> a \<Longrightarrow> emeasure M {x\<in>space M. X x \<le> a} = erlang_CDF k l a"
  shows "distributed M lborel X (erlang_density k l)"
proof (rule distributedI_borel_atMost)
  fix a :: real
  { assume "a \<le> 0"
    with X have "emeasure M {x\<in>space M. X x \<le> a} \<le> emeasure M {x\<in>space M. X x \<le> 0}"
      by (intro emeasure_mono) auto
    also have "... = 0"  by (auto intro!: erlang_CDF_at0 simp: X_distr[of 0])
    finally have "emeasure M {x\<in>space M. X x \<le> a} \<le> 0" by simp
    then have "emeasure M {x\<in>space M. X x \<le> a} = 0" by simp
  }
  note eq_0 = this

  show "(\<integral>\<^sup>+ x. erlang_density k l x * indicator {..a} x \<partial>lborel) = ennreal (erlang_CDF k l a)"
    using nn_integral_erlang_density[of l k a]
    by (simp add: ennreal_indicator ennreal_mult)

  show "emeasure M {x\<in>space M. X x \<le> a} = ennreal (erlang_CDF k l a)"
    using X_distr[of a] eq_0 by (auto simp: one_ennreal_def erlang_CDF_def)
qed simp_all

lemma (in prob_space) erlang_distributed_iff:
  assumes [arith]: "0<l"
  shows "distributed M lborel X (erlang_density k l) \<longleftrightarrow>
    (X \<in> borel_measurable M \<and> 0 < l \<and>  (\<forall>a\<ge>0. \<P>(x in M. X x \<le> a) = erlang_CDF k l a ))"
  using
    distributed_measurable[of M lborel X "erlang_density k l"]
    emeasure_erlang_density[of l]
    erlang_distributed_le[of X k l]
  by (auto intro!: erlang_distributedI simp: one_ennreal_def emeasure_eq_measure)

lemma (in prob_space) erlang_distributed_mult_const:
  assumes erlX: "distributed M lborel X (erlang_density k l)"
  assumes a_pos[arith]: "0 < \<alpha>"  "0 < l"
  shows  "distributed M lborel (\<lambda>x. \<alpha> * X x) (erlang_density k (l / \<alpha>))"
proof (subst erlang_distributed_iff, safe)
  have [measurable]: "random_variable borel X"  and  [arith]: "0 < l "
  and  [simp]: "\<And>a. 0 \<le> a \<Longrightarrow> prob {x \<in> space M. X x \<le> a} = erlang_CDF k l a"
    by(insert erlX, auto simp: erlang_distributed_iff)

  show "random_variable borel (\<lambda>x. \<alpha> * X x)" "0 < l / \<alpha>"  "0 < l / \<alpha>"
    by (auto simp:field_simps)

  fix a:: real assume [arith]: "0 \<le> a"
  obtain b:: real  where [simp, arith]: "b = a/ \<alpha>" by blast

  have [arith]: "0 \<le> b" by (auto simp: divide_nonneg_pos)

  have "prob {x \<in> space M. \<alpha> * X x \<le> a}  = prob {x \<in> space M.  X x \<le> b}"
    by (rule arg_cong[where f= prob]) (auto simp:field_simps)

  moreover have "prob {x \<in> space M. X x \<le> b} = erlang_CDF k l b" by auto
  moreover have "erlang_CDF k (l / \<alpha>) a = erlang_CDF k l b" unfolding erlang_CDF_def by auto
  ultimately show "prob {x \<in> space M. \<alpha> * X x \<le> a} = erlang_CDF k (l / \<alpha>) a" by fastforce
qed

lemma (in prob_space) has_bochner_integral_erlang_ith_moment:
  fixes k i :: nat and l :: real
  assumes [arith]: "0 < l" and D: "distributed M lborel X (erlang_density k l)"
  shows "has_bochner_integral M (\<lambda>x. X x ^ i) (fact (k + i) / (fact k * l ^ i))"
proof (rule has_bochner_integral_nn_integral)
  show "AE x in M. 0 \<le> X x ^ i"
    by (subst distributed_AE2[OF D]) (auto simp: erlang_density_def)
  show "(\<integral>\<^sup>+ x. ennreal (X x ^ i) \<partial>M) = ennreal (fact (k + i) / (fact k * l ^ i))"
    using nn_integral_erlang_ith_moment[of l k i]
    by (subst distributed_nn_integral[symmetric, OF D]) (auto simp: ennreal_mult')
qed (insert distributed_measurable[OF D], auto)

lemma (in prob_space) erlang_ith_moment_integrable:
  "0 < l \<Longrightarrow> distributed M lborel X (erlang_density k l) \<Longrightarrow> integrable M (\<lambda>x. X x ^ i)"
  by rule (rule has_bochner_integral_erlang_ith_moment)

lemma (in prob_space) erlang_ith_moment:
  "0 < l \<Longrightarrow> distributed M lborel X (erlang_density k l) \<Longrightarrow>
    expectation (\<lambda>x. X x ^ i) = fact (k + i) / (fact k * l ^ i)"
  by (rule has_bochner_integral_integral_eq) (rule has_bochner_integral_erlang_ith_moment)

lemma (in prob_space) erlang_distributed_variance:
  assumes [arith]: "0 < l" and "distributed M lborel X (erlang_density k l)"
  shows "variance X = (k + 1) / l\<^sup>2"
proof (subst variance_eq)
  show "integrable M X" "integrable M (\<lambda>x. (X x)\<^sup>2)"
    using erlang_ith_moment_integrable[OF assms, of 1] erlang_ith_moment_integrable[OF assms, of 2]
    by auto

  show "expectation (\<lambda>x. (X x)\<^sup>2) - (expectation X)\<^sup>2 = real (k + 1) / l\<^sup>2"
    using erlang_ith_moment[OF assms, of 1] erlang_ith_moment[OF assms, of 2]
    by simp (auto simp: power2_eq_square field_simps of_nat_Suc)
qed

subsection \<open>Exponential distribution\<close>

abbreviation exponential_density :: "real \<Rightarrow> real \<Rightarrow> real" where
  "exponential_density \<equiv> erlang_density 0"

lemma exponential_density_def:
  "exponential_density l x = (if x < 0 then 0 else l * exp (- x * l))"
  by (simp add: fun_eq_iff erlang_density_def)

lemma erlang_CDF_0: "erlang_CDF 0 l a = (if 0 \<le> a then 1 - exp (- l * a) else 0)"
  by (simp add: erlang_CDF_def)

lemma prob_space_exponential_density: "0 < l \<Longrightarrow> prob_space (density lborel (exponential_density l))"
  by (rule prob_space_erlang_density)

lemma (in prob_space) exponential_distributedD_le:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a" and l: "0 < l"
  shows "\<P>(x in M. X x \<le> a) = 1 - exp (- a * l)"
  using erlang_distributed_le[OF D l a] a by (simp add: erlang_CDF_def)

lemma (in prob_space) exponential_distributedD_gt:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a" and l: "0 < l"
  shows "\<P>(x in M. a < X x ) = exp (- a * l)"
  using erlang_distributed_gt[OF D l a] a by (simp add: erlang_CDF_def)

lemma (in prob_space) exponential_distributed_memoryless:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a" and l: "0 < l" and t: "0 \<le> t"
  shows "\<P>(x in M. a + t < X x \<bar> a < X x) = \<P>(x in M. t < X x)"
proof -
  have "\<P>(x in M. a + t < X x \<bar> a < X x) = \<P>(x in M. a + t < X x) / \<P>(x in M. a < X x)"
    using \<open>0 \<le> t\<close> by (auto simp: cond_prob_def intro!: arg_cong[where f=prob] arg_cong2[where f="(/)"])
  also have "\<dots> = exp (- (a + t) * l) / exp (- a * l)"
    using a t by (simp add: exponential_distributedD_gt[OF D _ l])
  also have "\<dots> = exp (- t * l)"
    using l by (auto simp: field_simps exp_add[symmetric])
  finally show ?thesis
    using t by (simp add: exponential_distributedD_gt[OF D _ l])
qed

lemma exponential_distributedI:
  assumes X[measurable]: "X \<in> borel_measurable M" and [arith]: "0 < l"
    and X_distr: "\<And>a. 0 \<le> a \<Longrightarrow> emeasure M {x\<in>space M. X x \<le> a} = 1 - exp (- a * l)"
  shows "distributed M lborel X (exponential_density l)"
proof (rule erlang_distributedI)
  fix a :: real assume "0 \<le> a" then show "emeasure M {x \<in> space M. X x \<le> a} = ennreal (erlang_CDF 0 l a)"
    using X_distr[of a] by (simp add: erlang_CDF_def ennreal_minus ennreal_1[symmetric] del: ennreal_1)
qed fact+

lemma (in prob_space) exponential_distributed_iff:
  assumes "0 < l"
  shows "distributed M lborel X (exponential_density l) \<longleftrightarrow>
    (X \<in> borel_measurable M \<and> (\<forall>a\<ge>0. \<P>(x in M. X x \<le> a) = 1 - exp (- a * l)))"
  using assms erlang_distributed_iff[of l X 0] by (auto simp: erlang_CDF_0)


lemma (in prob_space) exponential_distributed_expectation:
  "0 < l \<Longrightarrow> distributed M lborel X (exponential_density l) \<Longrightarrow> expectation X = 1 / l"
  using erlang_ith_moment[of l X 0 1] by simp

lemma exponential_density_nonneg: "0 < l \<Longrightarrow> 0 \<le> exponential_density l x"
  by (auto simp: exponential_density_def)

lemma (in prob_space) exponential_distributed_min:
  assumes "0 < l" "0 < u"
  assumes expX: "distributed M lborel X (exponential_density l)"
  assumes expY: "distributed M lborel Y (exponential_density u)"
  assumes ind: "indep_var borel X borel Y"
  shows "distributed M lborel (\<lambda>x. min (X x) (Y x)) (exponential_density (l + u))"
proof (subst exponential_distributed_iff, safe)
  have randX: "random_variable borel X"
    using expX \<open>0 < l\<close> by (simp add: exponential_distributed_iff)
  moreover have randY: "random_variable borel Y"
    using expY \<open>0 < u\<close> by (simp add: exponential_distributed_iff)
  ultimately show "random_variable borel (\<lambda>x. min (X x) (Y x))" by auto

  show " 0 < l + u"
    using \<open>0 < l\<close> \<open>0 < u\<close> by auto

  fix a::real assume a[arith]: "0 \<le> a"
  have gt1[simp]: "\<P>(x in M. a < X x ) = exp (- a * l)"
    by (rule exponential_distributedD_gt[OF expX a]) fact
  have gt2[simp]: "\<P>(x in M. a < Y x ) = exp (- a * u)"
    by (rule exponential_distributedD_gt[OF expY a]) fact

  have "\<P>(x in M. a < (min (X x) (Y x)) ) =  \<P>(x in M. a < (X x) \<and> a < (Y x))" by (auto intro!:arg_cong[where f=prob])

  also have " ... =  \<P>(x in M. a < (X x)) *  \<P>(x in M. a< (Y x) )"
    using prob_indep_random_variable[OF ind, of "{a <..}" "{a <..}"] by simp
  also have " ... = exp (- a * (l + u))" by (auto simp:field_simps mult_exp_exp)
  finally have indep_prob: "\<P>(x in M. a < (min (X x) (Y x)) ) = exp (- a * (l + u))" .

  have "{x \<in> space M. (min (X x) (Y x)) \<le>a } = (space M - {x \<in> space M. a<(min (X x) (Y x)) })"
    by auto
  then have "1 - prob {x \<in> space M. a < (min (X x) (Y x))} = prob {x \<in> space M. (min (X x) (Y x)) \<le> a}"
    using randX randY by (auto simp: prob_compl)
  then show "prob {x \<in> space M. (min (X x) (Y x)) \<le> a} = 1 - exp (- a * (l + u))"
    using indep_prob by auto
qed

lemma (in prob_space) exponential_distributed_Min:
  assumes finI: "finite I"
  assumes A: "I \<noteq> {}"
  assumes l: "\<And>i. i \<in> I \<Longrightarrow> 0 < l i"
  assumes expX: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (exponential_density (l i))"
  assumes ind: "indep_vars (\<lambda>i. borel) X I"
  shows "distributed M lborel (\<lambda>x. Min ((\<lambda>i. X i x)`I)) (exponential_density (\<Sum>i\<in>I. l i))"
using assms
proof (induct rule: finite_ne_induct)
  case (singleton i) then show ?case by simp
next
  case (insert i I)
  then have "distributed M lborel (\<lambda>x. min (X i x) (Min ((\<lambda>i. X i x)`I))) (exponential_density (l i + (\<Sum>i\<in>I. l i)))"
      by (intro exponential_distributed_min indep_vars_Min insert)
         (auto intro: indep_vars_subset sum_pos)
  then show ?case
    using insert by simp
qed

lemma (in prob_space) exponential_distributed_variance:
  "0 < l \<Longrightarrow> distributed M lborel X (exponential_density l) \<Longrightarrow> variance X = 1 / l\<^sup>2"
  using erlang_distributed_variance[of l X 0] by simp

lemma nn_integral_zero': "AE x in M. f x = 0 \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>M) = 0"
  by (simp cong: nn_integral_cong_AE)

lemma convolution_erlang_density:
  fixes k\<^sub>1 k\<^sub>2 :: nat
  assumes [simp, arith]: "0 < l"
  shows "(\<lambda>x. \<integral>\<^sup>+y. ennreal (erlang_density k\<^sub>1 l (x - y)) * ennreal (erlang_density k\<^sub>2 l y) \<partial>lborel) =
    (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l)"
      (is "?LHS = ?RHS")
proof
  fix x :: real
  have "x \<le> 0 \<or> 0 < x"
    by arith
  then show "?LHS x = ?RHS x"
  proof
    assume "x \<le> 0" then show ?thesis
      apply (subst nn_integral_zero')
      apply (rule AE_I[where N="{0}"])
      apply (auto simp add: erlang_density_def not_less)
      done
  next
    note zero_le_mult_iff[simp] zero_le_divide_iff[simp]

    have I_eq1: "integral\<^sup>N lborel (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l) = 1"
      using nn_integral_erlang_ith_moment[of l "Suc k\<^sub>1 + Suc k\<^sub>2 - 1" 0] by (simp del: fact_Suc)

    have 1: "(\<integral>\<^sup>+ x. ennreal (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l x * indicator {0<..} x) \<partial>lborel) = 1"
      apply (subst I_eq1[symmetric])
      unfolding erlang_density_def
      by (auto intro!: nn_integral_cong split:split_indicator)

    have "prob_space (density lborel ?LHS)"
      by (intro prob_space_convolution_density)
         (auto intro!: prob_space_erlang_density erlang_density_nonneg)
    then have 2: "integral\<^sup>N lborel ?LHS = 1"
      by (auto dest!: prob_space.emeasure_space_1 simp: emeasure_density)

    let ?I = "(integral\<^sup>N lborel (\<lambda>y. ennreal ((1 - y)^ k\<^sub>1 * y^k\<^sub>2 * indicator {0..1} y)))"
    let ?C = "(fact (Suc (k\<^sub>1 + k\<^sub>2))) / ((fact k\<^sub>1) * (fact k\<^sub>2))"
    let ?s = "Suc k\<^sub>1 + Suc k\<^sub>2 - 1"
    let ?L = "(\<lambda>x. \<integral>\<^sup>+y. ennreal (erlang_density k\<^sub>1 l (x- y) * erlang_density k\<^sub>2 l y * indicator {0..x} y) \<partial>lborel)"

    { fix x :: real assume [arith]: "0 < x"
      have *: "\<And>x y n. (x - y * x::real)^n = x^n * (1 - y)^n"
        unfolding power_mult_distrib[symmetric] by (simp add: field_simps)

      have "?LHS x = ?L x"
        unfolding erlang_density_def
        by (auto intro!: nn_integral_cong simp: ennreal_mult split:split_indicator)
      also have "... = (\<lambda>x. ennreal ?C * ?I * erlang_density ?s l x) x"
        apply (subst nn_integral_real_affine[where c=x and t = 0])
        apply (simp_all add: nn_integral_cmult[symmetric] nn_integral_multc[symmetric] del: fact_Suc)
        apply (intro nn_integral_cong)
        apply (auto simp add: erlang_density_def mult_less_0_iff exp_minus field_simps exp_diff power_add *
                              ennreal_mult[symmetric]
                    simp del: fact_Suc split: split_indicator)
        done
      finally have "(\<integral>\<^sup>+y. ennreal (erlang_density k\<^sub>1 l (x - y) * erlang_density k\<^sub>2 l y) \<partial>lborel) =
        (\<lambda>x. ennreal ?C * ?I * erlang_density ?s l x) x"
        by (simp add: ennreal_mult) }
    note * = this

    assume [arith]: "0 < x"
    have 3: "1 = integral\<^sup>N lborel (\<lambda>xa. ?LHS xa * indicator {0<..} xa)"
      by (subst 2[symmetric])
         (auto intro!: nn_integral_cong_AE AE_I[where N="{0}"]
               simp: erlang_density_def  nn_integral_multc[symmetric] indicator_def split: if_split_asm)
    also have "... = integral\<^sup>N lborel (\<lambda>x. (ennreal (?C) * ?I) * ((erlang_density ?s l x) * indicator {0<..} x))"
      by (auto intro!: nn_integral_cong simp: ennreal_mult[symmetric] * split: split_indicator)
    also have "... = ennreal (?C) * ?I"
      using 1
      by (auto simp: nn_integral_cmult)
    finally have " ennreal (?C) * ?I = 1" by presburger

    then show ?thesis
      using * by (simp add: ennreal_mult)
  qed
qed

lemma (in prob_space) sum_indep_erlang:
  assumes indep: "indep_var borel X borel Y"
  assumes [simp, arith]: "0 < l"
  assumes erlX: "distributed M lborel X (erlang_density k\<^sub>1 l)"
  assumes erlY: "distributed M lborel Y (erlang_density k\<^sub>2 l)"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l)"
  using assms
  apply (subst convolution_erlang_density[symmetric, OF \<open>0<l\<close>])
  apply (intro distributed_convolution)
  apply auto
  done

lemma (in prob_space) erlang_distributed_sum:
  assumes finI : "finite I"
  assumes A: "I \<noteq> {}"
  assumes [simp, arith]: "0 < l"
  assumes expX: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (erlang_density (k i) l)"
  assumes ind: "indep_vars (\<lambda>i. borel) X I"
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (erlang_density ((\<Sum>i\<in>I. Suc (k i)) - 1) l)"
using assms
proof (induct rule: finite_ne_induct)
  case (singleton i) then show ?case by auto
next
  case (insert i I)
    then have "distributed M lborel (\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) (erlang_density (Suc (k i) + Suc ((\<Sum>i\<in>I. Suc (k i)) - 1) - 1) l)"
      by(intro sum_indep_erlang indep_vars_sum) (auto intro!: indep_vars_subset)
    also have "(\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) = (\<lambda>x. \<Sum>i\<in>insert i I. X i x)"
      using insert by auto
    also have "Suc(k i) + Suc ((\<Sum>i\<in>I. Suc (k i)) - 1) - 1 = (\<Sum>i\<in>insert i I. Suc (k i)) - 1"
      using insert by (auto intro!: Suc_pred simp: ac_simps)
    finally show ?case by fast
qed

lemma (in prob_space) exponential_distributed_sum:
  assumes finI: "finite I"
  assumes A: "I \<noteq> {}"
  assumes l: "0 < l"
  assumes expX: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (exponential_density l)"
  assumes ind: "indep_vars (\<lambda>i. borel) X I"
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (erlang_density ((card I) - 1) l)"
  using erlang_distributed_sum[OF assms] by simp

lemma (in information_space) entropy_exponential:
  assumes l[simp, arith]: "0 < l"
  assumes D: "distributed M lborel X (exponential_density l)"
  shows "entropy b lborel X = log b (exp 1 / l)"
proof -
  have [simp]: "integrable lborel (exponential_density l)"
    using distributed_integrable[OF D, of "\<lambda>_. 1"] by simp

  have [simp]: "integral\<^sup>L lborel (exponential_density l) = 1"
    using distributed_integral[OF D, of "\<lambda>_. 1"] by (simp add: prob_space)

  have [simp]: "integrable lborel (\<lambda>x. exponential_density l x * x)"
    using erlang_ith_moment_integrable[OF l D, of 1] distributed_integrable[OF D, of "\<lambda>x. x"] by simp

  have [simp]: "integral\<^sup>L lborel (\<lambda>x. exponential_density l x * x) = 1 / l"
    using erlang_ith_moment[OF l D, of 1] distributed_integral[OF D, of "\<lambda>x. x"] by simp

  have "entropy b lborel X = - (\<integral> x. exponential_density l x * log b (exponential_density l x) \<partial>lborel)"
    using D by (rule entropy_distr) simp
  also have "(\<integral> x. exponential_density l x * log b (exponential_density l x) \<partial>lborel) =
    (\<integral> x. (ln l * exponential_density l x - l * (exponential_density l x * x)) / ln b \<partial>lborel)"
    by (intro Bochner_Integration.integral_cong) (auto simp: log_def ln_mult exponential_density_def field_simps)
  also have "\<dots> = (ln l - 1) / ln b"
    by simp
  finally show ?thesis
    by (simp add: log_def ln_div) (simp add: field_split_simps)
qed

subsection \<open>Uniform distribution\<close>

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
     by (simp add: divide_ennreal_def ac_simps)
  also have "\<dots> = (\<integral>\<^sup>+ x. (1 / emeasure M' A) * indicator (A \<inter> B) x \<partial>M')"
    using A B
    by (intro nn_integral_cmult_indicator[symmetric]) (auto intro!: )
  also have "\<dots> = (\<integral>\<^sup>+ x. ?f x * indicator B x \<partial>M')"
    by (rule nn_integral_cong) (auto split: split_indicator)
  finally show "emeasure (distr M M' X) B = emeasure (density M' ?f) B"
    using A B X by (auto simp add: emeasure_distr emeasure_density)
qed simp

lemma uniform_distrI_borel:
  fixes A :: "real set"
  assumes X[measurable]: "X \<in> borel_measurable M" and A: "emeasure lborel A = ennreal r" "0 < r"
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
  finally have fin: "emeasure lborel (A \<inter> {..a}) \<noteq> top"
    by simp
  from emeasure_eq_ennreal_measure[OF this]
  have fin_eq: "emeasure lborel (A \<inter> {..a}) / r = ennreal (measure lborel (A \<inter> {..a}) / r)"
    using A by (simp add: divide_ennreal measure_nonneg)
  then show "emeasure M {x\<in>space M. X x \<le> a} = ennreal (measure lborel (A \<inter> {..a}) / r)"
    using distr by simp

  have "(\<integral>\<^sup>+ x. ennreal (indicator A x / measure lborel A * indicator {..a} x) \<partial>lborel) =
    (\<integral>\<^sup>+ x. ennreal (1 / measure lborel A) * indicator (A \<inter> {..a}) x \<partial>lborel)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ennreal (1 / measure lborel A) * emeasure lborel (A \<inter> {..a})"
    using \<open>A \<in> sets borel\<close>
    by (intro nn_integral_cmult_indicator) (auto simp: measure_nonneg)
  also have "\<dots> = ennreal (measure lborel (A \<inter> {..a}) / r)"
    unfolding emeasure_eq_ennreal_measure[OF fin] using A
    by (simp add: measure_def ennreal_mult'[symmetric])
  finally show "(\<integral>\<^sup>+ x. ennreal (indicator A x / measure lborel A * indicator {..a} x) \<partial>lborel) =
    ennreal (measure lborel (A \<inter> {..a}) / r)" .
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
      using distr[of a] \<open>a < b\<close> by (simp add: emeasure_eq_measure)
    finally have "emeasure M {x\<in>space M. X x \<le> t} = 0"
      by (simp add: antisym measure_nonneg)
    with \<open>t < a\<close> show ?thesis by simp
  next
    assume bnds: "a \<le> t" "t \<le> b"
    have "{a..b} \<inter> {..t} = {a..t}"
      using bnds by auto
    then show ?thesis using \<open>a \<le> t\<close> \<open>a < b\<close>
      using distr[OF bnds] by (simp add: emeasure_eq_measure divide_ennreal)
  next
    assume "b < t"
    have "1 = emeasure M {x\<in>space M. X x \<le> b}"
      using distr[of b] \<open>a < b\<close> by (simp add: one_ennreal_def emeasure_eq_measure)
    also have "\<dots> \<le> emeasure M {x\<in>space M. X x \<le> t}"
      using X \<open>b < t\<close> by (auto intro!: emeasure_mono measurable_sets)
    finally have "emeasure M {x\<in>space M. X x \<le> t} = 1"
       by (simp add: antisym emeasure_eq_measure)
    with \<open>b < t\<close> \<open>a < b\<close> show ?thesis by (simp add: measure_def divide_ennreal)
  qed
qed (insert X \<open>a < b\<close>, auto)

lemma (in prob_space) uniform_distributed_measure:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  assumes t: "a \<le> t" "t \<le> b"
  shows "\<P>(x in M. X x \<le> t) = (t - a) / (b - a)"
proof -
  have "emeasure M {x \<in> space M. X x \<le> t} = emeasure (distr M lborel X) {.. t}"
    using distributed_measurable[OF D]
    by (subst emeasure_distr) (auto intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (1 / (b - a)) * indicator {a .. t} x \<partial>lborel)"
    using distributed_borel_measurable[OF D] \<open>a \<le> t\<close> \<open>t \<le> b\<close>
    unfolding distributed_distr_eq_density[OF D]
    by (subst emeasure_density)
       (auto intro!: nn_integral_cong simp: measure_def split: split_indicator)
  also have "\<dots> = ennreal (1 / (b - a)) * (t - a)"
    using \<open>a \<le> t\<close> \<open>t \<le> b\<close>
    by (subst nn_integral_cmult_indicator) auto
  finally show ?thesis
    using t by (simp add: emeasure_eq_measure ennreal_mult''[symmetric] measure_nonneg)
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
  by (auto intro!: uniform_distrI_borel_atLeastAtMost simp del: content_real_if)

lemma (in prob_space) uniform_distributed_expectation:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  shows "expectation X = (a + b) / 2"
proof (subst distributed_integral[OF D, of "\<lambda>x. x", symmetric])
  have "a < b"
    using uniform_distributed_bounds[OF D] .

  have "(\<integral> x. indicator {a .. b} x / measure lborel {a .. b} * x \<partial>lborel) =
    (\<integral> x. (x / measure lborel {a .. b}) * indicator {a .. b} x \<partial>lborel)"
    by (intro Bochner_Integration.integral_cong) auto
  also have "(\<integral> x. (x / measure lborel {a .. b}) * indicator {a .. b} x \<partial>lborel) = (a + b) / 2"
  proof (subst integral_FTC_Icc_real)
    fix x
    show "DERIV (\<lambda>x. x\<^sup>2 / (2 * measure lborel {a..b})) x :> x / measure lborel {a..b}"
      using uniform_distributed_params[OF D]
      by (auto intro!: derivative_eq_intros simp del: content_real_if)
    show "isCont (\<lambda>x. x / Sigma_Algebra.measure lborel {a..b}) x"
      using uniform_distributed_params[OF D]
      by (auto intro!: isCont_divide)
    have *: "b\<^sup>2 / (2 * measure lborel {a..b}) - a\<^sup>2 / (2 * measure lborel {a..b}) =
      (b*b - a * a) / (2 * (b - a))"
      using \<open>a < b\<close>
      by (auto simp: measure_def power2_eq_square diff_divide_distrib[symmetric])
    show "b\<^sup>2 / (2 * measure lborel {a..b}) - a\<^sup>2 / (2 * measure lborel {a..b}) = (a + b) / 2"
      using \<open>a < b\<close>
      unfolding * square_diff_square_factored by (auto simp: field_simps)
  qed (insert \<open>a < b\<close>, simp)
  finally show "(\<integral> x. indicator {a .. b} x / measure lborel {a .. b} * x \<partial>lborel) = (a + b) / 2" .
qed (auto simp: measure_nonneg)

lemma (in prob_space) uniform_distributed_variance:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  shows "variance X = (b - a)\<^sup>2 / 12"
proof (subst distributed_variance)
  have [arith]: "a < b" using uniform_distributed_bounds[OF D] .
  let ?\<mu> = "expectation X" let ?D = "\<lambda>x. indicator {a..b} (x + ?\<mu>) / measure lborel {a..b}"
  have "(\<integral>x. x\<^sup>2 * (?D x) \<partial>lborel) = (\<integral>x. x\<^sup>2 * (indicator {a - ?\<mu> .. b - ?\<mu>} x) / measure lborel {a .. b} \<partial>lborel)"
    by (intro Bochner_Integration.integral_cong) (auto split: split_indicator)
  also have "\<dots> = (b - a)\<^sup>2 / 12"
    by (simp add: integral_power uniform_distributed_expectation[OF D])
       (simp add: eval_nat_numeral field_simps )
  finally show "(\<integral>x. x\<^sup>2 * ?D x \<partial>lborel) = (b - a)\<^sup>2 / 12" .
qed (auto intro: D simp del: content_real_if)

subsection \<open>Normal distribution\<close>


definition normal_density :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "normal_density \<mu> \<sigma> x = 1 / sqrt (2 * pi * \<sigma>\<^sup>2) * exp (-(x - \<mu>)\<^sup>2/ (2 * \<sigma>\<^sup>2))"

abbreviation std_normal_density :: "real \<Rightarrow> real" where
  "std_normal_density \<equiv> normal_density 0 1"

lemma std_normal_density_def: "std_normal_density x = (1 / sqrt (2 * pi)) * exp (- x\<^sup>2 / 2)"
  unfolding normal_density_def by simp

lemma normal_density_nonneg[simp]: "0 \<le> normal_density \<mu> \<sigma> x"
  by (auto simp: normal_density_def)

lemma normal_density_pos: "0 < \<sigma> \<Longrightarrow> 0 < normal_density \<mu> \<sigma> x"
  by (auto simp: normal_density_def)

lemma borel_measurable_normal_density[measurable]: "normal_density \<mu> \<sigma> \<in> borel_measurable borel"
  by (auto simp: normal_density_def[abs_def])

lemma gaussian_moment_0:
  "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R exp (- x\<^sup>2)) (sqrt pi / 2)"
proof -
  let ?pI = "\<lambda>f. (\<integral>\<^sup>+s. f (s::real) * indicator {0..} s \<partial>lborel)"
  let ?gauss = "\<lambda>x. exp (- x\<^sup>2)"

  let ?I = "indicator {0<..} :: real \<Rightarrow> real"
  let ?ff= "\<lambda>x s. x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) :: real"

  have *: "?pI ?gauss = (\<integral>\<^sup>+x. ?gauss x * ?I x \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[where N="{0}"]) (auto split: split_indicator)

  have "?pI ?gauss * ?pI ?gauss = (\<integral>\<^sup>+x. \<integral>\<^sup>+s. ?gauss x * ?gauss s * ?I s * ?I x \<partial>lborel \<partial>lborel)"
    by (auto simp: nn_integral_cmult[symmetric] nn_integral_multc[symmetric] * ennreal_mult[symmetric]
             intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+s. ?ff x s * ?I s * ?I x \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_cong, cases)
    fix x :: real assume "x \<noteq> 0"
    then show "(\<integral>\<^sup>+s. ?gauss x * ?gauss s * ?I s * ?I x \<partial>lborel) = (\<integral>\<^sup>+s. ?ff x s * ?I s * ?I x \<partial>lborel)"
      by (subst nn_integral_real_affine[where t="0" and c="x"])
         (auto simp: mult_exp_exp nn_integral_cmult[symmetric] field_simps zero_less_mult_iff ennreal_mult[symmetric]
               intro!: nn_integral_cong split: split_indicator)
  qed simp
  also have "... = \<integral>\<^sup>+s. \<integral>\<^sup>+x. ?ff x s * ?I s * ?I x \<partial>lborel \<partial>lborel"
    by (rule lborel_pair.Fubini'[symmetric]) auto
  also have "... = ?pI (\<lambda>s. ?pI (\<lambda>x. ?ff x s))"
    by (rule nn_integral_cong_AE)
       (auto intro!: nn_integral_cong_AE AE_I[where N="{0}"] split: split_indicator_asm)
  also have "\<dots> = ?pI (\<lambda>s. ennreal (1 / (2 * (1 + s\<^sup>2))))"
  proof (intro nn_integral_cong ennreal_mult_right_cong)
    fix s :: real show "?pI (\<lambda>x. ?ff x s) = ennreal (1 / (2 * (1 + s\<^sup>2)))"
    proof (subst nn_integral_FTC_atLeast)
      have "((\<lambda>a. - (exp (- (a\<^sup>2 * (1 + s\<^sup>2))) / (2 + 2 * s\<^sup>2))) \<longlongrightarrow> (- (0 / (2 + 2 * s\<^sup>2)))) at_top"
        apply (intro tendsto_intros filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top])
        apply (subst mult.commute)
        apply (auto intro!: filterlim_tendsto_pos_mult_at_top
                            filterlim_at_top_mult_at_top[OF filterlim_ident filterlim_ident]
                    simp: add_pos_nonneg  power2_eq_square add_nonneg_eq_0_iff)
        done
      then show "((\<lambda>a. - (exp (- a\<^sup>2 - s\<^sup>2 * a\<^sup>2) / (2 + 2 * s\<^sup>2))) \<longlongrightarrow> 0) at_top"
        by (simp add: field_simps)
    qed (auto intro!: derivative_eq_intros simp: field_simps add_nonneg_eq_0_iff)
  qed
  also have "... = ennreal (pi / 4)"
  proof (subst nn_integral_FTC_atLeast)
    show "((\<lambda>a. arctan a / 2) \<longlongrightarrow> (pi / 2) / 2 ) at_top"
      by (intro tendsto_intros) (simp_all add: tendsto_arctan_at_top)
  qed (auto intro!: derivative_eq_intros simp: add_nonneg_eq_0_iff field_simps power2_eq_square)
  finally have "?pI ?gauss^2 = pi / 4"
    by (simp add: power2_eq_square)
  then have "?pI ?gauss = sqrt (pi / 4)"
    using power_eq_iff_eq_base[of 2 "enn2real (?pI ?gauss)" "sqrt (pi / 4)"]
    by (cases "?pI ?gauss") (auto simp: power2_eq_square ennreal_mult[symmetric] ennreal_top_mult)
  also have "?pI ?gauss = (\<integral>\<^sup>+x. indicator {0..} x *\<^sub>R exp (- x\<^sup>2) \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also have "sqrt (pi / 4) = sqrt pi / 2"
    by (simp add: real_sqrt_divide)
  finally show ?thesis
    by (rule has_bochner_integral_nn_integral[rotated 3])
       auto
qed

lemma gaussian_moment_1:
  "has_bochner_integral lborel (\<lambda>x::real. indicator {0..} x *\<^sub>R (exp (- x\<^sup>2) * x)) (1 / 2)"
proof -
  have "(\<integral>\<^sup>+x. indicator {0..} x *\<^sub>R (exp (- x\<^sup>2) * x) \<partial>lborel) =
    (\<integral>\<^sup>+x. ennreal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel)"
    by (intro nn_integral_cong)
       (auto simp: ac_simps split: split_indicator)
  also have "\<dots> = ennreal (0 - (- exp (- 0\<^sup>2) / 2))"
  proof (rule nn_integral_FTC_atLeast)
    have "((\<lambda>x::real. - exp (- x\<^sup>2) / 2) \<longlongrightarrow> - 0 / 2) at_top"
      by (intro tendsto_divide tendsto_minus filterlim_compose[OF exp_at_bot]
                   filterlim_compose[OF filterlim_uminus_at_bot_at_top]
                   filterlim_pow_at_top filterlim_ident)
         auto
    then show "((\<lambda>a::real. - exp (- a\<^sup>2) / 2) \<longlongrightarrow> 0) at_top"
      by simp
  qed (auto intro!: derivative_eq_intros)
  also have "\<dots> = ennreal (1 / 2)"
    by simp
  finally show ?thesis
    by (rule has_bochner_integral_nn_integral[rotated 3])
        (auto split: split_indicator)
qed

lemma
  fixes k :: nat
  shows gaussian_moment_even_pos:
    "has_bochner_integral lborel (\<lambda>x::real. indicator {0..} x *\<^sub>R (exp (-x\<^sup>2)*x^(2 * k)))
       ((sqrt pi / 2) * (fact (2 * k) / (2 ^ (2 * k) * fact k)))"
       (is "?even")
    and gaussian_moment_odd_pos:
      "has_bochner_integral lborel (\<lambda>x::real. indicator {0..} x *\<^sub>R (exp (-x\<^sup>2)*x^(2 * k + 1))) (fact k / 2)"
      (is "?odd")
proof -
  let ?M = "\<lambda>k x. exp (- x\<^sup>2) * x^k :: real"

  { fix k I assume Mk: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R ?M k x) I"
    have "2 \<noteq> (0::real)"
      by linarith
    let ?f = "\<lambda>b. \<integral>x. indicator {0..} x *\<^sub>R ?M (k + 2) x * indicator {..b} x \<partial>lborel"
    have "((\<lambda>b. (k + 1) / 2 * (\<integral>x. indicator {..b} x *\<^sub>R (indicator {0..} x *\<^sub>R ?M k x) \<partial>lborel) - ?M (k + 1) b / 2) \<longlongrightarrow>
        (k + 1) / 2 * (\<integral>x. indicator {0..} x *\<^sub>R ?M k x \<partial>lborel) - 0 / 2) at_top" (is ?tendsto)
    proof (intro tendsto_intros \<open>2 \<noteq> 0\<close> tendsto_integral_at_top sets_lborel Mk[THEN integrable.intros])
      show "(?M (k + 1) \<longlongrightarrow> 0) at_top"
      proof cases
        assume "even k"
        have "((\<lambda>x. ((x\<^sup>2)^(k div 2 + 1) / exp (x\<^sup>2)) * (1 / x) :: real) \<longlongrightarrow> 0 * 0) at_top"
          by (intro tendsto_intros tendsto_divide_0[OF tendsto_const] filterlim_compose[OF tendsto_power_div_exp_0]
                   filterlim_at_top_imp_at_infinity filterlim_ident filterlim_pow_at_top filterlim_ident)
             auto
        also have "(\<lambda>x. ((x\<^sup>2)^(k div 2 + 1) / exp (x\<^sup>2)) * (1 / x) :: real) = ?M (k + 1)"
          using \<open>even k\<close> by (auto simp: fun_eq_iff exp_minus field_simps power2_eq_square power_mult elim: evenE)
        finally show ?thesis by simp
      next
        assume "odd k"
        have "((\<lambda>x. ((x\<^sup>2)^((k - 1) div 2 + 1) / exp (x\<^sup>2)) :: real) \<longlongrightarrow> 0) at_top"
          by (intro filterlim_compose[OF tendsto_power_div_exp_0] filterlim_at_top_imp_at_infinity
                    filterlim_ident filterlim_pow_at_top)
             auto
        also have "(\<lambda>x. ((x\<^sup>2)^((k - 1) div 2 + 1) / exp (x\<^sup>2)) :: real) = ?M (k + 1)"
          using \<open>odd k\<close> by (auto simp: fun_eq_iff exp_minus field_simps power2_eq_square power_mult elim: oddE)
        finally show ?thesis by simp
      qed
    qed
    also have "?tendsto \<longleftrightarrow> ((?f \<longlongrightarrow> (k + 1) / 2 * (\<integral>x. indicator {0..} x *\<^sub>R ?M k x \<partial>lborel) - 0 / 2) at_top)"
    proof (intro filterlim_cong refl eventually_at_top_linorder[THEN iffD2] exI[of _ 0] allI impI)
      fix b :: real assume b: "0 \<le> b"
      have "Suc k * (\<integral>x. indicator {0..b} x *\<^sub>R ?M k x \<partial>lborel) = (\<integral>x. indicator {0..b} x *\<^sub>R (exp (- x\<^sup>2) * ((Suc k) * x ^ k)) \<partial>lborel)"
        unfolding integral_mult_right_zero[symmetric] by (intro Bochner_Integration.integral_cong) auto
      also have "\<dots> = exp (- b\<^sup>2) * b ^ (Suc k) - exp (- 0\<^sup>2) * 0 ^ (Suc k) -
          (\<integral>x. indicator {0..b} x *\<^sub>R (- 2 * x * exp (- x\<^sup>2) * x ^ (Suc k)) \<partial>lborel)"
        by (rule integral_by_parts')
           (auto intro!: derivative_eq_intros b
                 simp: diff_Suc of_nat_Suc field_simps split: nat.split)
      also have "... = exp (- b\<^sup>2) * b ^ (Suc k) - (\<integral>x. indicator {0..b} x *\<^sub>R (- 2 * (exp (- x\<^sup>2) * x ^ (k + 2))) \<partial>lborel)"
        by (auto simp: intro!: Bochner_Integration.integral_cong)
      also have "... = exp (- b\<^sup>2) * b ^ (Suc k) + 2 * (\<integral>x. indicator {0..b} x *\<^sub>R ?M (k + 2) x \<partial>lborel)"
        unfolding Bochner_Integration.integral_mult_right_zero [symmetric]
        by (simp del: real_scaleR_def)
      finally have "Suc k * (\<integral>x. indicator {0..b} x *\<^sub>R ?M k x \<partial>lborel) =
        exp (- b\<^sup>2) * b ^ (Suc k) + 2 * (\<integral>x. indicator {0..b} x *\<^sub>R ?M (k + 2) x \<partial>lborel)" .
      then show "(k + 1) / 2 * (\<integral>x. indicator {..b} x *\<^sub>R (indicator {0..} x *\<^sub>R ?M k x)\<partial>lborel) - exp (- b\<^sup>2) * b ^ (k + 1) / 2 = ?f b"
        by (simp add: field_simps atLeastAtMost_def indicator_inter_arith)
    qed
    finally have int_M_at_top: "((?f \<longlongrightarrow> (k + 1) / 2 * (\<integral>x. indicator {0..} x *\<^sub>R ?M k x \<partial>lborel)) at_top)"
      by simp

    have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R ?M (k + 2) x) ((k + 1) / 2 * I)"
    proof (rule has_bochner_integral_monotone_convergence_at_top)
      fix y :: real
      have *: "(\<lambda>x. indicator {0..} x *\<^sub>R ?M (k + 2) x * indicator {..y} x::real) =
            (\<lambda>x. indicator {0..y} x *\<^sub>R ?M (k + 2) x)"
        by rule (simp split: split_indicator)
      show "integrable lborel (\<lambda>x. indicator {0..} x *\<^sub>R (?M (k + 2) x) * indicator {..y} x::real)"
        unfolding * by (rule borel_integrable_compact) (auto intro!: continuous_intros)
      show "((?f \<longlongrightarrow> (k + 1) / 2 * I) at_top)"
        using int_M_at_top has_bochner_integral_integral_eq[OF Mk] by simp
    qed (auto split: split_indicator) }
  note step = this

  show ?even
  proof (induct k)
    case (Suc k)
    note step[OF this]
    also have "(real (2 * k + 1) / 2 * (sqrt pi / 2 * ((fact (2 * k)) / ((2::real)^(2*k) * fact k)))) =
      sqrt pi / 2 * ((fact (2 * Suc k)) / ((2::real)^(2 * Suc k) * fact (Suc k)))"
      apply (simp add: field_simps del: fact_Suc)
      apply (simp add: of_nat_mult field_simps)
      done
    finally show ?case
      by simp
  qed (insert gaussian_moment_0, simp)

  show ?odd
  proof (induct k)
    case (Suc k)
    note step[OF this]
    also have "(real (2 * k + 1 + 1) / (2::real) * ((fact k) / 2)) = (fact (Suc k)) / 2"
      by (simp add: field_simps of_nat_Suc field_split_simps del: fact_Suc) (simp add: field_simps)
    finally show ?case
      by simp
  qed (insert gaussian_moment_1, simp)
qed

context
  fixes k :: nat and \<mu> \<sigma> :: real assumes [arith]: "0 < \<sigma>"
begin

lemma normal_moment_even:
  "has_bochner_integral lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>) ^ (2 * k)) (fact (2 * k) / ((2 / \<sigma>\<^sup>2)^k * fact k))"
proof -
  have eq: "\<And>x::real. x\<^sup>2^k = (x^k)\<^sup>2"
    by (simp add: power_mult[symmetric] ac_simps)

  have "has_bochner_integral lborel (\<lambda>x. exp (-x\<^sup>2)*x^(2 * k))
      (sqrt pi * (fact (2 * k) / (2 ^ (2 * k) * fact k)))"
    using has_bochner_integral_even_function[OF gaussian_moment_even_pos[where k=k]] by simp
  then have "has_bochner_integral lborel (\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k)) * ((2*\<sigma>\<^sup>2)^k / sqrt (2 * pi * \<sigma>\<^sup>2)))
      ((sqrt pi * (fact (2 * k) / (2 ^ (2 * k) * fact k))) * ((2*\<sigma>\<^sup>2)^k / sqrt (2 * pi * \<sigma>\<^sup>2)))"
    by (rule has_bochner_integral_mult_left)
  also have "(\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k)) * ((2*\<sigma>\<^sup>2)^k / sqrt (2 * pi * \<sigma>\<^sup>2))) =
    (\<lambda>x. exp (- ((sqrt 2 * \<sigma>) * x)\<^sup>2 / (2*\<sigma>\<^sup>2)) * ((sqrt 2 * \<sigma>) * x) ^ (2 * k) / sqrt (2 * pi * \<sigma>\<^sup>2))"
    by (auto simp: fun_eq_iff field_simps real_sqrt_power[symmetric] real_sqrt_mult
                   real_sqrt_divide power_mult eq)
  also have "((sqrt pi * (fact (2 * k) / (2 ^ (2 * k) * fact k))) * ((2*\<sigma>\<^sup>2)^k / sqrt (2 * pi * \<sigma>\<^sup>2))) =
    (inverse (sqrt 2 * \<sigma>) * ((fact (2 * k))) / ((2/\<sigma>\<^sup>2) ^ k * (fact k)))"
    by (auto simp: fun_eq_iff power_mult field_simps real_sqrt_power[symmetric] real_sqrt_mult
                   power2_eq_square)
  finally show ?thesis
    unfolding normal_density_def
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="sqrt 2 * \<sigma>" and t=\<mu>]) simp_all
qed

lemma normal_moment_abs_odd:
  "has_bochner_integral lborel (\<lambda>x. normal_density \<mu> \<sigma> x * \<bar>x - \<mu>\<bar>^(2 * k + 1)) (2^k * \<sigma>^(2 * k + 1) * fact k * sqrt (2 / pi))"
proof -
  have "has_bochner_integral lborel (\<lambda>x::real. indicator {0..} x *\<^sub>R (exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1))) (fact k / 2)"
    by (rule has_bochner_integral_cong[THEN iffD1, OF _ _ _ gaussian_moment_odd_pos[of k]]) auto
  from has_bochner_integral_even_function[OF this]
  have "has_bochner_integral lborel (\<lambda>x::real. exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1)) (fact k)"
    by simp
  then have "has_bochner_integral lborel (\<lambda>x. (exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1)) * (2^k * \<sigma>^(2 * k + 1) / sqrt (pi * \<sigma>\<^sup>2)))
      (fact k * (2^k * \<sigma>^(2 * k + 1) / sqrt (pi * \<sigma>\<^sup>2)))"
    by (rule has_bochner_integral_mult_left)
  also have "(\<lambda>x. (exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1)) * (2^k * \<sigma>^(2 * k + 1) / sqrt (pi * \<sigma>\<^sup>2))) =
    (\<lambda>x. exp (- (((sqrt 2 * \<sigma>) * x)\<^sup>2 / (2 * \<sigma>\<^sup>2))) * \<bar>sqrt 2 * \<sigma> * x\<bar> ^ (2 * k + 1) / sqrt (2 * pi * \<sigma>\<^sup>2))"
    by (simp add: field_simps abs_mult real_sqrt_power[symmetric] power_mult real_sqrt_mult)
  also have "(fact k * (2^k * \<sigma>^(2 * k + 1) / sqrt (pi * \<sigma>\<^sup>2))) =
    (inverse (sqrt 2) * inverse \<sigma> * (2 ^ k * (\<sigma> * \<sigma> ^ (2 * k)) * (fact k) * sqrt (2 / pi)))"
    by (auto simp: fun_eq_iff power_mult field_simps real_sqrt_power[symmetric] real_sqrt_divide
                   real_sqrt_mult)
  finally show ?thesis
    unfolding normal_density_def
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="sqrt 2 * \<sigma>" and t=\<mu>])
       simp_all
qed

lemma normal_moment_odd:
  "has_bochner_integral lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)^(2 * k + 1)) 0"
proof -
  have "has_bochner_integral lborel (\<lambda>x. exp (- x\<^sup>2) * x^(2 * k + 1)::real) 0"
    using gaussian_moment_odd_pos by (rule has_bochner_integral_odd_function) simp
  then have "has_bochner_integral lborel (\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k + 1)) * (2^k*\<sigma>^(2*k)/sqrt pi))
      (0 * (2^k*\<sigma>^(2*k)/sqrt pi))"
    by (rule has_bochner_integral_mult_left)
  also have "(\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k + 1)) * (2^k*\<sigma>^(2*k)/sqrt pi)) =
    (\<lambda>x. exp (- ((sqrt 2 * \<sigma> * x)\<^sup>2 / (2 * \<sigma>\<^sup>2))) *
          (sqrt 2 * \<sigma> * x * (sqrt 2 * \<sigma> * x) ^ (2 * k)) /
          sqrt (2 * pi * \<sigma>\<^sup>2))"
    unfolding real_sqrt_mult
    by (simp add: field_simps abs_mult real_sqrt_power[symmetric] power_mult fun_eq_iff)
  finally show ?thesis
    unfolding normal_density_def
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="sqrt 2 * \<sigma>" and t=\<mu>]) simp_all
qed

lemma integral_normal_moment_even:
  "integral\<^sup>L lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)^(2 * k)) = fact (2 * k) / ((2 / \<sigma>\<^sup>2)^k * fact k)"
  using normal_moment_even by (rule has_bochner_integral_integral_eq)

lemma integral_normal_moment_abs_odd:
  "integral\<^sup>L lborel (\<lambda>x. normal_density \<mu> \<sigma> x * \<bar>x - \<mu>\<bar>^(2 * k + 1)) = 2 ^ k * \<sigma> ^ (2 * k + 1) * fact k * sqrt (2 / pi)"
  using normal_moment_abs_odd by (rule has_bochner_integral_integral_eq)

lemma integral_normal_moment_odd:
  "integral\<^sup>L lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)^(2 * k + 1)) = 0"
  using normal_moment_odd by (rule has_bochner_integral_integral_eq)

end


context
  fixes \<sigma> :: real
  assumes \<sigma>_pos[arith]: "0 < \<sigma>"
begin

lemma normal_moment_nz_1: "has_bochner_integral lborel (\<lambda>x. normal_density \<mu> \<sigma> x * x) \<mu>"
proof -
  note normal_moment_even[OF \<sigma>_pos, of \<mu> 0]
  note normal_moment_odd[OF \<sigma>_pos, of \<mu> 0] has_bochner_integral_mult_left[of \<mu>, OF this]
  note has_bochner_integral_add[OF this]
  then show ?thesis
    by (simp add: power2_eq_square field_simps)
qed

lemma integral_normal_moment_nz_1:
  "integral\<^sup>L lborel (\<lambda>x. normal_density \<mu> \<sigma> x * x) = \<mu>"
  using normal_moment_nz_1 by (rule has_bochner_integral_integral_eq)

lemma integrable_normal_moment_nz_1: "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * x)"
  using normal_moment_nz_1 by rule

lemma integrable_normal_moment: "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)^k)"
proof cases
  assume "even k" then show ?thesis
    using integrable.intros[OF normal_moment_even] by (auto elim: evenE)
next
  assume "odd k" then show ?thesis
    using integrable.intros[OF normal_moment_odd] by (auto elim: oddE)
qed

lemma integrable_normal_moment_abs: "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * \<bar>x - \<mu>\<bar>^k)"
proof cases
  assume "even k" then show ?thesis
    using integrable.intros[OF normal_moment_even] by (auto simp add: power_even_abs elim: evenE)
next
  assume "odd k" then show ?thesis
    using integrable.intros[OF normal_moment_abs_odd] by (auto elim: oddE)
qed

lemma integrable_normal_density[simp, intro]: "integrable lborel (normal_density \<mu> \<sigma>)"
  using integrable_normal_moment[of \<mu> 0] by simp

lemma integral_normal_density[simp]: "(\<integral>x. normal_density \<mu> \<sigma> x \<partial>lborel) = 1"
  using integral_normal_moment_even[of \<sigma> \<mu> 0] by simp

lemma prob_space_normal_density:
  "prob_space (density lborel (normal_density \<mu> \<sigma>))"
  proof qed (simp add: emeasure_density nn_integral_eq_integral normal_density_nonneg)

end



context
  fixes k :: nat
begin

lemma std_normal_moment_even:
  "has_bochner_integral lborel (\<lambda>x. std_normal_density x * x ^ (2 * k)) (fact (2 * k) / (2^k * fact k))"
  using normal_moment_even[of 1 0 k] by simp

lemma std_normal_moment_abs_odd:
  "has_bochner_integral lborel (\<lambda>x. std_normal_density x * \<bar>x\<bar>^(2 * k + 1)) (sqrt (2/pi) * 2^k * fact k)"
  using normal_moment_abs_odd[of 1 0 k] by (simp add: ac_simps)

lemma std_normal_moment_odd:
  "has_bochner_integral lborel (\<lambda>x. std_normal_density x * x^(2 * k + 1)) 0"
  using normal_moment_odd[of 1 0 k] by simp

lemma integral_std_normal_moment_even:
  "integral\<^sup>L lborel (\<lambda>x. std_normal_density x * x^(2*k)) = fact (2 * k) / (2^k * fact k)"
  using std_normal_moment_even by (rule has_bochner_integral_integral_eq)

lemma integral_std_normal_moment_abs_odd:
  "integral\<^sup>L lborel (\<lambda>x. std_normal_density x * \<bar>x\<bar>^(2 * k + 1)) = sqrt (2 / pi) * 2^k * fact k"
  using std_normal_moment_abs_odd by (rule has_bochner_integral_integral_eq)

lemma integral_std_normal_moment_odd:
  "integral\<^sup>L lborel (\<lambda>x. std_normal_density x * x^(2 * k + 1)) = 0"
  using std_normal_moment_odd by (rule has_bochner_integral_integral_eq)

lemma integrable_std_normal_moment_abs: "integrable lborel (\<lambda>x. std_normal_density x * \<bar>x\<bar>^k)"
  using integrable_normal_moment_abs[of 1 0 k] by simp

lemma integrable_std_normal_moment: "integrable lborel (\<lambda>x. std_normal_density x * x^k)"
  using integrable_normal_moment[of 1 0 k] by simp

end

lemma (in prob_space) normal_density_affine:
  assumes X: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes [simp, arith]: "0 < \<sigma>" "\<alpha> \<noteq> 0"
  shows "distributed M lborel (\<lambda>x. \<beta> + \<alpha> * X x) (normal_density (\<beta> + \<alpha> * \<mu>) (\<bar>\<alpha>\<bar> * \<sigma>))"
proof -
  have eq: "\<And>x. \<bar>\<alpha>\<bar> * normal_density (\<beta> + \<alpha> * \<mu>) (\<bar>\<alpha>\<bar> * \<sigma>) (x * \<alpha> + \<beta>) =
    normal_density \<mu> \<sigma> x"
    by (simp add: normal_density_def real_sqrt_mult field_simps)
       (simp add: power2_eq_square field_simps)
  show ?thesis
    by (rule distributed_affineI[OF _ \<open>\<alpha> \<noteq> 0\<close>, where t=\<beta>])
       (simp_all add: eq X ennreal_mult'[symmetric])
qed

lemma (in prob_space) normal_standard_normal_convert:
  assumes pos_var[simp, arith]: "0 < \<sigma>"
  shows "distributed M lborel X (normal_density  \<mu> \<sigma>) = distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) std_normal_density"
proof auto
  assume "distributed M lborel X (\<lambda>x. ennreal (normal_density \<mu> \<sigma> x))"
  then have "distributed M lborel (\<lambda>x. -\<mu> / \<sigma> + (1/\<sigma>) * X x) (\<lambda>x. ennreal (normal_density (-\<mu> / \<sigma> + (1/\<sigma>)* \<mu>) (\<bar>1/\<sigma>\<bar> * \<sigma>) x))"
    by(rule normal_density_affine) auto

  then show "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ennreal (std_normal_density x))"
    by (simp add: diff_divide_distrib[symmetric] field_simps)
next
  assume *: "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ennreal (std_normal_density x))"
  have "distributed M lborel (\<lambda>x. \<mu> + \<sigma> * ((X x - \<mu>) / \<sigma>)) (\<lambda>x. ennreal (normal_density \<mu> \<bar>\<sigma>\<bar> x))"
    using normal_density_affine[OF *, of \<sigma> \<mu>] by simp
  then show "distributed M lborel X (\<lambda>x. ennreal (normal_density \<mu> \<sigma> x))" by simp
qed

lemma conv_normal_density_zero_mean:
  assumes [simp, arith]: "0 < \<sigma>" "0 < \<tau>"
  shows "(\<lambda>x. \<integral>\<^sup>+y. ennreal (normal_density 0 \<sigma> (x - y) * normal_density 0 \<tau> y) \<partial>lborel) =
    normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"  (is "?LHS = ?RHS")
proof -
  define \<sigma>' \<tau>' where "\<sigma>' = \<sigma>\<^sup>2" and "\<tau>' = \<tau>\<^sup>2"
  then have [simp, arith]: "0 < \<sigma>'" "0 < \<tau>'"
    by simp_all
  let ?\<sigma> = "sqrt ((\<sigma>' * \<tau>') / (\<sigma>' + \<tau>'))"
  have sqrt: "(sqrt (2 * pi * (\<sigma>' + \<tau>')) * sqrt (2 * pi * (\<sigma>' * \<tau>') / (\<sigma>' + \<tau>'))) =
    (sqrt (2 * pi * \<sigma>') * sqrt (2 * pi * \<tau>'))"
    by (subst power_eq_iff_eq_base[symmetric, where n=2])
       (simp_all add: real_sqrt_mult[symmetric] power2_eq_square)
  have "?LHS =
    (\<lambda>x. \<integral>\<^sup>+y. ennreal((normal_density 0 (sqrt (\<sigma>' + \<tau>')) x) * normal_density (\<tau>' * x / (\<sigma>' + \<tau>')) ?\<sigma> y) \<partial>lborel)"
    apply (intro ext nn_integral_cong)
    apply (simp add: normal_density_def \<sigma>'_def[symmetric] \<tau>'_def[symmetric] sqrt mult_exp_exp)
    apply (simp add: divide_simps power2_eq_square)
    apply (simp add: algebra_simps)
    done

  also have "... =
    (\<lambda>x. (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x) * (\<integral>\<^sup>+y. ennreal( normal_density (\<tau>\<^sup>2* x / (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) ?\<sigma> y) \<partial>lborel))"
    by (subst nn_integral_cmult[symmetric])
       (auto simp: \<sigma>'_def \<tau>'_def normal_density_def ennreal_mult'[symmetric])

  also have "... = (\<lambda>x. (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    by (subst nn_integral_eq_integral) (auto simp: normal_density_nonneg)

  finally show ?thesis by fast
qed

lemma conv_std_normal_density:
  "(\<lambda>x. \<integral>\<^sup>+y. ennreal (std_normal_density (x - y) * std_normal_density y) \<partial>lborel) =
  (normal_density 0 (sqrt 2))"
  by (subst conv_normal_density_zero_mean) simp_all

lemma (in prob_space) add_indep_normal:
  assumes indep: "indep_var borel X borel Y"
  assumes pos_var[arith]: "0 < \<sigma>" "0 < \<tau>"
  assumes normalX[simp]: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes normalY[simp]: "distributed M lborel Y (normal_density \<nu> \<tau>)"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (normal_density (\<mu> + \<nu>) (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"
proof -
  have ind[simp]: "indep_var borel (\<lambda>x. - \<mu> + X x) borel (\<lambda>x. - \<nu> + Y x)"
  proof -
    have "indep_var borel ( (\<lambda>x. -\<mu> + x) o X) borel ((\<lambda>x. - \<nu> + x) o Y)"
      by (auto intro!: indep_var_compose assms)
    then show ?thesis by (simp add: o_def)
  qed

  have "distributed M lborel (\<lambda>x. -\<mu> + 1 * X x) (normal_density (- \<mu> + 1 * \<mu>) (\<bar>1\<bar> * \<sigma>))"
    by(rule normal_density_affine[OF normalX pos_var(1), of 1 "-\<mu>"]) simp
  then have 1[simp]: "distributed M lborel (\<lambda>x. - \<mu> +  X x) (normal_density 0 \<sigma>)" by simp

  have "distributed M lborel (\<lambda>x. -\<nu> + 1 * Y x) (normal_density (- \<nu> + 1 * \<nu>) (\<bar>1\<bar> * \<tau>))"
    by(rule normal_density_affine[OF normalY pos_var(2), of 1 "-\<nu>"]) simp
  then have 2[simp]: "distributed M lborel (\<lambda>x. - \<nu> +  Y x) (normal_density 0 \<tau>)" by simp

  have *: "distributed M lborel (\<lambda>x. (- \<mu> + X x) + (- \<nu> + Y x)) (\<lambda>x. ennreal (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    using distributed_convolution[OF ind 1 2] conv_normal_density_zero_mean[OF pos_var]
    by (simp add: ennreal_mult'[symmetric] normal_density_nonneg)

  have "distributed M lborel (\<lambda>x. \<mu> + \<nu> + 1 * (- \<mu> + X x + (- \<nu> + Y x)))
        (\<lambda>x. ennreal (normal_density (\<mu> + \<nu> + 1 * 0) (\<bar>1\<bar> * sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    by (rule normal_density_affine[OF *, of 1 "\<mu> + \<nu>"]) (auto simp: add_pos_pos)

  then show ?thesis by auto
qed

lemma (in prob_space) diff_indep_normal:
  assumes indep[simp]: "indep_var borel X borel Y"
  assumes [simp, arith]: "0 < \<sigma>" "0 < \<tau>"
  assumes normalX[simp]: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes normalY[simp]: "distributed M lborel Y (normal_density \<nu> \<tau>)"
  shows "distributed M lborel (\<lambda>x. X x - Y x) (normal_density (\<mu> - \<nu>) (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"
proof -
  have "distributed M lborel (\<lambda>x. 0 + - 1 * Y x) (\<lambda>x. ennreal (normal_density (0 + - 1 * \<nu>) (\<bar>- 1\<bar> * \<tau>) x))"
    by(rule normal_density_affine, auto)
  then have [simp]:"distributed M lborel (\<lambda>x. - Y x) (\<lambda>x. ennreal (normal_density (- \<nu>) \<tau> x))" by simp

  have "distributed M lborel (\<lambda>x. X x + (- Y x)) (normal_density (\<mu> + - \<nu>) (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"
    apply (rule add_indep_normal)
    apply (rule indep_var_compose[unfolded comp_def, of borel _ borel _ "\<lambda>x. x" _ "\<lambda>x. - x"])
    apply simp_all
    done
  then show ?thesis by simp
qed

lemma (in prob_space) sum_indep_normal:
  assumes "finite I" "I \<noteq> {}" "indep_vars (\<lambda>i. borel) X I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 < \<sigma> i"
  assumes normal: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (normal_density (\<mu> i) (\<sigma> i))"
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (normal_density (\<Sum>i\<in>I. \<mu> i) (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2)))"
  using assms
proof (induct I rule: finite_ne_induct)
  case (singleton i) then show ?case by (simp add : abs_of_pos)
next
  case (insert i I)
    then have 1: "distributed M lborel (\<lambda>x. (X i x) + (\<Sum>i\<in>I. X i x))
                (normal_density (\<mu> i  + sum \<mu> I)  (sqrt ((\<sigma> i)\<^sup>2 + (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2))\<^sup>2)))"
      apply (intro add_indep_normal indep_vars_sum insert real_sqrt_gt_zero)
      apply (auto intro: indep_vars_subset intro!: sum_pos)
      apply fastforce
      done
    have 2: "(\<lambda>x. (X i x)+ (\<Sum>i\<in>I. X i x)) = (\<lambda>x. (\<Sum>j\<in>insert i I. X j x))"
          "\<mu> i + sum \<mu> I = sum \<mu> (insert i I)"
      using insert by auto

    have 3: "(sqrt ((\<sigma> i)\<^sup>2 + (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2))\<^sup>2)) = (sqrt (\<Sum>i\<in>insert i I. (\<sigma> i)\<^sup>2))"
      using insert by (simp add: sum_nonneg)

    show ?case using 1 2 3 by simp
qed

lemma (in prob_space) standard_normal_distributed_expectation:
  assumes D: "distributed M lborel X std_normal_density"
  shows "expectation X = 0"
  using integral_std_normal_moment_odd[of 0]
    distributed_integral[OF D, of "\<lambda>x. x", symmetric]
  by auto

lemma (in prob_space) normal_distributed_expectation:
  assumes \<sigma>[arith]: "0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "expectation X = \<mu>"
  using integral_normal_moment_nz_1[OF \<sigma>, of \<mu>] distributed_integral[OF D, of "\<lambda>x. x", symmetric]
  by (auto simp: field_simps)

lemma (in prob_space) normal_distributed_variance:
  fixes a b :: real
  assumes [simp, arith]: "0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "variance X = \<sigma>\<^sup>2"
  using integral_normal_moment_even[of \<sigma> \<mu> 1]
  by (subst distributed_integral[OF D, symmetric])
     (simp_all add: eval_nat_numeral normal_distributed_expectation[OF assms])

lemma (in prob_space) standard_normal_distributed_variance:
  "distributed M lborel X std_normal_density \<Longrightarrow> variance X = 1"
  using normal_distributed_variance[of 1 X 0] by simp

lemma (in information_space) entropy_normal_density:
  assumes [arith]: "0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "entropy b lborel X = log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2"
proof -
  have "entropy b lborel X = - (\<integral> x. normal_density \<mu> \<sigma> x * log b (normal_density \<mu> \<sigma> x) \<partial>lborel)"
    using D by (rule entropy_distr) simp
  also have "\<dots> = - (\<integral> x. normal_density \<mu> \<sigma> x * (- ln (2 * pi * \<sigma>\<^sup>2) - (x - \<mu>)\<^sup>2 / \<sigma>\<^sup>2) / (2 * ln b) \<partial>lborel)"
    by (intro arg_cong[where f="uminus"] Bochner_Integration.integral_cong)
       (auto simp: normal_density_def field_simps ln_mult log_def ln_div ln_sqrt)
  also have "\<dots> = - (\<integral>x. - (normal_density \<mu> \<sigma> x * (ln (2 * pi * \<sigma>\<^sup>2)) + (normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2) / \<sigma>\<^sup>2) / (2 * ln b) \<partial>lborel)"
    by (intro arg_cong[where f="uminus"] Bochner_Integration.integral_cong) (auto simp: field_split_simps field_simps)
  also have "\<dots> = (\<integral>x. normal_density \<mu> \<sigma> x * (ln (2 * pi * \<sigma>\<^sup>2)) + (normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2) / \<sigma>\<^sup>2 \<partial>lborel) / (2 * ln b)"
    by (simp del: minus_add_distrib)
  also have "\<dots> = (ln (2 * pi * \<sigma>\<^sup>2) + 1) / (2 * ln b)"
    using integral_normal_moment_even[of \<sigma> \<mu> 1] by (simp add: integrable_normal_moment fact_numeral)
  also have "\<dots> = log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2"
    by (simp add: log_def field_simps ln_mult)
  finally show ?thesis .
qed

end
