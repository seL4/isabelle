(*  Title:      HOL/Probability/Distributions.thy
    Author:     Sudeep Kanav, TU München
    Author:     Johannes Hölzl, TU München *)

header {* Properties of Various Distributions *}

theory Distributions
  imports Probability_Measure Convolution
begin

lemma measure_lebesgue_Icc: "measure lebesgue {a .. b} = (if a \<le> b then b - a else 0)"
  by (auto simp: measure_def)

lemma integral_power:
  "a \<le> b \<Longrightarrow> (\<integral>x. x^k * indicator {a..b} x \<partial>lborel) = (b^Suc k - a^Suc k) / Suc k"
proof (subst integral_FTC_atLeastAtMost)
  fix x show "DERIV (\<lambda>x. x^Suc k / Suc k) x :> x^k"
    by (intro derivative_eq_intros) auto
qed (auto simp: field_simps)

lemma has_bochner_integral_nn_integral:
  assumes "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes "(\<integral>\<^sup>+x. f x \<partial>M) = ereal x"
  shows "has_bochner_integral M f x"
  unfolding has_bochner_integral_iff
proof
  show "integrable M f"
    using assms by (rule integrableI_nn_integral_finite)
qed (auto simp: assms integral_eq_nn_integral)

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

subsection {* Erlang *}

lemma nn_intergal_power_times_exp_Icc:
  assumes [arith]: "0 \<le> a"
  shows "(\<integral>\<^sup>+x. ereal (x^k * exp (-x)) * indicator {0 .. a} x \<partial>lborel) =
    (1 - (\<Sum>n\<le>k. (a^n * exp (-a)) / fact n)) * fact k" (is "?I = _")
proof -
  let ?f = "\<lambda>k x. x^k * exp (-x) / fact k"
  let ?F = "\<lambda>k x. - (\<Sum>n\<le>k. (x^n * exp (-x)) / fact n)"

  have "?I * (inverse (fact k)) = 
      (\<integral>\<^sup>+x. ereal (x^k * exp (-x)) * indicator {0 .. a} x * (inverse (fact k)) \<partial>lborel)"
    by (intro nn_integral_multc[symmetric]) auto
  also have "\<dots> = (\<integral>\<^sup>+x. ereal (?f k x) * indicator {0 .. a} x \<partial>lborel)"
    by (intro nn_integral_cong) (simp add: field_simps)
  also have "\<dots> = ereal (?F k a) - (?F k 0)"
  proof (rule nn_integral_FTC_atLeastAtMost)
    fix x assume "x \<in> {0..a}"
    show "DERIV (?F k) x :> ?f k x"
    proof(induction k)
      case 0 show ?case by (auto intro!: derivative_eq_intros)
    next
      case (Suc k)
      have "DERIV (\<lambda>x. ?F k x - (x^Suc k * exp (-x)) / fact (Suc k)) x :>
        ?f k x - ((real (Suc k) - x) * x ^ k * exp (- x)) / real (fact (Suc k))"
        by (intro DERIV_diff Suc)
           (auto intro!: derivative_eq_intros simp del: fact_Suc power_Suc
                 simp add: field_simps power_Suc[symmetric] real_of_nat_def[symmetric])
      also have "(\<lambda>x. ?F k x - (x^Suc k * exp (-x)) / fact (Suc k)) = ?F (Suc k)"
        by simp
      also have "?f k x - ((real (Suc k) - x) * x ^ k * exp (- x)) / real (fact (Suc k)) = ?f (Suc k) x"
        by (auto simp: field_simps simp del: fact_Suc)
           (simp_all add: real_of_nat_Suc field_simps)
      finally show ?case .
    qed
  qed auto
  also have "\<dots> = ereal (1 - (\<Sum>n\<le>k. (a^n * exp (-a)) / fact n))"
    by (auto simp: power_0_left if_distrib[where f="\<lambda>x. x / a" for a] setsum_cases)
  finally show ?thesis
    by (cases "?I") (auto simp: field_simps)
qed

lemma nn_intergal_power_times_exp_Ici:
  shows "(\<integral>\<^sup>+x. ereal (x^k * exp (-x)) * indicator {0 ..} x \<partial>lborel) = fact k"
proof (rule LIMSEQ_unique)
  let ?X = "\<lambda>n. \<integral>\<^sup>+ x. ereal (x^k * exp (-x)) * indicator {0 .. real n} x \<partial>lborel"
  show "?X ----> (\<integral>\<^sup>+x. ereal (x^k * exp (-x)) * indicator {0 ..} x \<partial>lborel)"
    apply (intro nn_integral_LIMSEQ)
    apply (auto simp: incseq_def le_fun_def eventually_sequentially
                split: split_indicator intro!: Lim_eventually)
    apply (metis natceiling_le_eq)
    done

  have "((\<lambda>x. (1 - (\<Sum>n\<le>k. (x ^ n / exp x) / real (fact n))) * fact k) ---> (1 - (\<Sum>n\<le>k. 0 / real (fact n))) * fact k) at_top"
    by (intro tendsto_intros tendsto_power_div_exp_0) simp
  then show "?X ----> fact k"
    by (subst nn_intergal_power_times_exp_Icc)
       (auto simp: exp_minus field_simps intro!: filterlim_compose[OF _ filterlim_real_sequentially])
qed

definition erlang_density :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "erlang_density k l x = (if x < 0 then 0 else (l^(Suc k) * x^k * exp (- l * x)) / fact k)"

definition erlang_CDF ::  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "erlang_CDF k l x = (if x < 0 then 0 else 1 - (\<Sum>n\<le>k. ((l * x)^n * exp (- l * x) / fact n)))"

lemma erlang_density_nonneg: "0 \<le> l \<Longrightarrow> 0 \<le> erlang_density k l x"
  by (simp add: erlang_density_def)

lemma borel_measurable_erlang_density[measurable]: "erlang_density k l \<in> borel_measurable borel"
  by (auto simp add: erlang_density_def[abs_def])

lemma erlang_CDF_transform: "0 < l \<Longrightarrow> erlang_CDF k l a = erlang_CDF k 1 (l * a)"
  by (auto simp add: erlang_CDF_def mult_less_0_iff)

lemma nn_integral_erlang_density:
  assumes [arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x. ereal (erlang_density k l x) * indicator {.. a} x \<partial>lborel) = erlang_CDF k l a"
proof cases
  assume [arith]: "0 \<le> a"
  have eq: "\<And>x. indicator {0..a} (x / l) = indicator {0..a*l} x"
    by (simp add: field_simps split: split_indicator)
  have "(\<integral>\<^sup>+x. ereal (erlang_density k l x) * indicator {.. a} x \<partial>lborel) =
    (\<integral>\<^sup>+x. (l/fact k) * (ereal ((l*x)^k * exp (- (l*x))) * indicator {0 .. a} x) \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: erlang_density_def power_mult_distrib split: split_indicator)
  also have "\<dots> = (l/fact k) * (\<integral>\<^sup>+x. ereal ((l*x)^k * exp (- (l*x))) * indicator {0 .. a} x \<partial>lborel)"
    by (intro nn_integral_cmult) auto
  also have "\<dots> = ereal (l/fact k) * ((1/l) * (\<integral>\<^sup>+x. ereal (x^k * exp (- x)) * indicator {0 .. l * a} x \<partial>lborel))"
    by (subst nn_integral_real_affine[where c="1 / l" and t=0]) (auto simp: field_simps eq)
  also have "\<dots> = (1 - (\<Sum>n\<le>k. ((l * a)^n * exp (-(l * a))) / fact n))"
    by (subst nn_intergal_power_times_exp_Icc) auto
  also have "\<dots> = erlang_CDF k l a"
    by (auto simp: erlang_CDF_def)
  finally show ?thesis .
next
  assume "\<not> 0 \<le> a" 
  moreover then have "(\<integral>\<^sup>+ x. ereal (erlang_density k l x) * indicator {.. a} x \<partial>lborel) = (\<integral>\<^sup>+x. 0 \<partial>(lborel::real measure))"
    by (intro nn_integral_cong) (auto simp: erlang_density_def)
  ultimately show ?thesis
    by (simp add: erlang_CDF_def)
qed

lemma emeasure_erlang_density: 
  "0 < l \<Longrightarrow> emeasure (density lborel (erlang_density k l)) {.. a} = erlang_CDF k l a"
  by (simp add: emeasure_density nn_integral_erlang_density)

lemma nn_integral_erlang_ith_moment: 
  fixes k i :: nat and l :: real
  assumes [arith]: "0 < l" 
  shows "(\<integral>\<^sup>+ x. ereal (erlang_density k l x * x ^ i) \<partial>lborel) = fact (k + i) / (fact k * l ^ i)"
proof -
  have eq: "\<And>x. indicator {0..} (x / l) = indicator {0..} x"
    by (simp add: field_simps split: split_indicator)
  have "(\<integral>\<^sup>+ x. ereal (erlang_density k l x * x^i) \<partial>lborel) =
    (\<integral>\<^sup>+x. (l/(fact k * l^i)) * (ereal ((l*x)^(k+i) * exp (- (l*x))) * indicator {0 ..} x) \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: erlang_density_def power_mult_distrib power_add split: split_indicator)
  also have "\<dots> = (l/(fact k * l^i)) * (\<integral>\<^sup>+x. ereal ((l*x)^(k+i) * exp (- (l*x))) * indicator {0 ..} x \<partial>lborel)"
    by (intro nn_integral_cmult) auto
  also have "\<dots> = ereal (l/(fact k * l^i)) * ((1/l) * (\<integral>\<^sup>+x. ereal (x^(k+i) * exp (- x)) * indicator {0 ..} x \<partial>lborel))"
    by (subst nn_integral_real_affine[where c="1 / l" and t=0]) (auto simp: field_simps eq)
  also have "\<dots> = fact (k + i) / (fact k * l ^ i)"
    by (subst nn_intergal_power_times_exp_Ici) auto
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
    by (auto simp: measure_def)
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
    then have "emeasure M {x\<in>space M. X x \<le> a} = 0" by (simp add:emeasure_le_0_iff)
  }
  note eq_0 = this

  show "(\<integral>\<^sup>+ x. erlang_density k l x * indicator {..a} x \<partial>lborel) = ereal (erlang_CDF k l a)"
    using nn_integral_erlang_density[of l k a]
    by (simp add: times_ereal.simps(1)[symmetric] ereal_indicator del: times_ereal.simps)

  show "emeasure M {x\<in>space M. X x \<le> a} = ereal (erlang_CDF k l a)"
    using X_distr[of a] eq_0 by (auto simp: one_ereal_def erlang_CDF_def)
qed (simp_all add: erlang_density_nonneg)

lemma (in prob_space) erlang_distributed_iff:
  assumes [arith]: "0<l"
  shows "distributed M lborel X (erlang_density k l) \<longleftrightarrow>
    (X \<in> borel_measurable M \<and> 0 < l \<and>  (\<forall>a\<ge>0. \<P>(x in M. X x \<le> a) = erlang_CDF k l a ))"
  using
    distributed_measurable[of M lborel X "erlang_density k l"]
    emeasure_erlang_density[of l]
    erlang_distributed_le[of X k l]
  by (auto intro!: erlang_distributedI simp: one_ereal_def emeasure_eq_measure) 

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
  show "(\<integral>\<^sup>+ x. ereal (X x ^ i) \<partial>M) = ereal (fact (k + i) / (fact k * l ^ i))"
    using nn_integral_erlang_ith_moment[of l k i]
    by (subst distributed_nn_integral[symmetric, OF D]) auto
qed (insert distributed_measurable[OF D], simp)

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
    by simp (auto simp: power2_eq_square field_simps real_of_nat_Suc)
qed

subsection {* Exponential distribution *}

abbreviation exponential_density :: "real \<Rightarrow> real \<Rightarrow> real" where
  "exponential_density \<equiv> erlang_density 0"

lemma exponential_density_def:
  "exponential_density l x = (if x < 0 then 0 else l * exp (- x * l))"
  by (simp add: fun_eq_iff erlang_density_def)

lemma erlang_CDF_0: "erlang_CDF 0 l a = (if 0 \<le> a then 1 - exp (- l * a) else 0)"
  by (simp add: erlang_CDF_def)

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

lemma prob_space_exponential_density: "0 < l \<Longrightarrow> prob_space (density lborel (exponential_density l))"
  by (rule prob_space_erlang_density)

lemma (in prob_space) exponential_distributedD_le:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a"
  shows "\<P>(x in M. X x \<le> a) = 1 - exp (- a * l)"
  using erlang_distributed_le[OF D exponential_distributed_params[OF D] a] a
  by (simp add: erlang_CDF_def)

lemma (in prob_space) exponential_distributedD_gt:
  assumes D: "distributed M lborel X (exponential_density l)" and a: "0 \<le> a"
  shows "\<P>(x in M. a < X x ) = exp (- a * l)"
  using erlang_distributed_gt[OF D exponential_distributed_params[OF D] a] a
  by (simp add: erlang_CDF_def)

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
proof (rule erlang_distributedI)
  fix a :: real assume "0 \<le> a" then show "emeasure M {x \<in> space M. X x \<le> a} = ereal (erlang_CDF 0 l a)"
    using X_distr[of a] by (simp add: erlang_CDF_def one_ereal_def)
qed fact+

lemma (in prob_space) exponential_distributed_iff:
  "distributed M lborel X (exponential_density l) \<longleftrightarrow>
    (X \<in> borel_measurable M \<and> 0 < l \<and> (\<forall>a\<ge>0. \<P>(x in M. X x \<le> a) = 1 - exp (- a * l)))"
  using exponential_distributed_params[of X l] erlang_distributed_iff[of l X 0] by (auto simp: erlang_CDF_0)


lemma (in prob_space) exponential_distributed_expectation:
  "distributed M lborel X (exponential_density l) \<Longrightarrow> expectation X = 1 / l"
  using erlang_ith_moment[OF exponential_distributed_params, of X l X 0 1] by simp

lemma exponential_density_nonneg: "0 < l \<Longrightarrow> 0 \<le> exponential_density l x"
  by (auto simp: exponential_density_def)

lemma (in prob_space) exponential_distributed_min:
  assumes expX: "distributed M lborel X (exponential_density l)"
  assumes expY: "distributed M lborel Y (exponential_density u)"
  assumes ind: "indep_var borel X borel Y"
  shows "distributed M lborel (\<lambda>x. min (X x) (Y x)) (exponential_density (l + u))"
proof (subst exponential_distributed_iff, safe)
  have randX: "random_variable borel X" using expX by (simp add: exponential_distributed_iff)
  moreover have randY: "random_variable borel Y" using expY by (simp add: exponential_distributed_iff)
  ultimately show "random_variable borel (\<lambda>x. min (X x) (Y x))" by auto
  
  have "0 < l" by (rule exponential_distributed_params) fact
  moreover have "0 < u" by (rule exponential_distributed_params) fact
  ultimately  show " 0 < l + u" by force

  fix a::real assume a[arith]: "0 \<le> a"
  have gt1[simp]: "\<P>(x in M. a < X x ) = exp (- a * l)" by (rule exponential_distributedD_gt[OF expX a]) 
  have gt2[simp]: "\<P>(x in M. a < Y x ) = exp (- a * u)" by (rule exponential_distributedD_gt[OF expY a]) 

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
         (auto intro: indep_vars_subset) 
  then show ?case
    using insert by simp
qed

lemma (in prob_space) exponential_distributed_variance:
  "distributed M lborel X (exponential_density l) \<Longrightarrow> variance X = 1 / l\<^sup>2"
  using erlang_distributed_variance[OF exponential_distributed_params, of X l X 0] by simp

lemma nn_integral_zero': "AE x in M. f x = 0 \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>M) = 0"
  by (simp cong: nn_integral_cong_AE)

lemma convolution_erlang_density:
  fixes k\<^sub>1 k\<^sub>2 :: nat
  assumes [simp, arith]: "0 < l"
  shows "(\<lambda>x. \<integral>\<^sup>+y. ereal (erlang_density k\<^sub>1 l (x - y)) * ereal (erlang_density k\<^sub>2 l y) \<partial>lborel) =
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
  
    have 1: "(\<integral>\<^sup>+ x. ereal (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l x * indicator {0<..} x) \<partial>lborel) = 1"
      apply (subst I_eq1[symmetric])
      unfolding erlang_density_def
      by (auto intro!: nn_integral_cong split:split_indicator)
  
    have "prob_space (density lborel ?LHS)"
      unfolding times_ereal.simps[symmetric]
      by (intro prob_space_convolution_density) 
         (auto intro!: prob_space_erlang_density erlang_density_nonneg)
    then have 2: "integral\<^sup>N lborel ?LHS = 1"
      by (auto dest!: prob_space.emeasure_space_1 simp: emeasure_density)
  
    let ?I = "(integral\<^sup>N lborel (\<lambda>y. ereal ((1 - y)^ k\<^sub>1 * y^k\<^sub>2 * indicator {0..1} y)))"
    let ?C = "real (fact (Suc (k\<^sub>1 + k\<^sub>2))) / (real (fact k\<^sub>1) * real (fact k\<^sub>2))"
    let ?s = "Suc k\<^sub>1 + Suc k\<^sub>2 - 1"
    let ?L = "(\<lambda>x. \<integral>\<^sup>+y. ereal (erlang_density k\<^sub>1 l (x- y) * erlang_density k\<^sub>2 l y * indicator {0..x} y) \<partial>lborel)"

    { fix x :: real assume [arith]: "0 < x"
      have *: "\<And>x y n. (x - y * x::real)^n = x^n * (1 - y)^n"
        unfolding power_mult_distrib[symmetric] by (simp add: field_simps)
    
      have "?LHS x = ?L x"
        unfolding erlang_density_def
        by (auto intro!: nn_integral_cong split:split_indicator)
      also have "... = (\<lambda>x. ereal ?C * ?I * erlang_density ?s l x) x"
        apply (subst nn_integral_real_affine[where c=x and t = 0])
        apply (simp_all add: nn_integral_cmult[symmetric] nn_integral_multc[symmetric] erlang_density_nonneg del: fact_Suc)
        apply (intro nn_integral_cong)
        apply (auto simp add: erlang_density_def mult_less_0_iff exp_minus field_simps exp_diff power_add *
                    simp del: fact_Suc split: split_indicator)
        done
      finally have "(\<integral>\<^sup>+y. ereal (erlang_density k\<^sub>1 l (x - y) * erlang_density k\<^sub>2 l y) \<partial>lborel) = 
        (\<lambda>x. ereal ?C * ?I * erlang_density ?s l x) x"
        by simp }
    note * = this

    assume [arith]: "0 < x"
    have 3: "1 = integral\<^sup>N lborel (\<lambda>xa. ?LHS xa * indicator {0<..} xa)"
      by (subst 2[symmetric])
         (auto intro!: nn_integral_cong_AE AE_I[where N="{0}"]
               simp: erlang_density_def  nn_integral_multc[symmetric] indicator_def split: split_if_asm)
    also have "... = integral\<^sup>N lborel (\<lambda>x. (ereal (?C) * ?I) * ((erlang_density ?s l x) * indicator {0<..} x))"
      by (auto intro!: nn_integral_cong simp: * split: split_indicator)
    also have "... = ereal (?C) * ?I"
      using 1
      by (auto simp: nn_integral_nonneg nn_integral_cmult)  
    finally have " ereal (?C) * ?I = 1" by presburger
  
    then show ?thesis
      using * by simp
  qed
qed

lemma (in prob_space) sum_indep_erlang:
  assumes indep: "indep_var borel X borel Y"
  assumes [simp, arith]: "0 < l"
  assumes erlX: "distributed M lborel X (erlang_density k\<^sub>1 l)"
  assumes erlY: "distributed M lborel Y (erlang_density k\<^sub>2 l)"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l)"
  using assms
  apply (subst convolution_erlang_density[symmetric, OF `0<l`])
  apply (intro distributed_convolution)
  apply auto
  done

lemma (in prob_space) erlang_distributed_setsum:
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
      by(intro sum_indep_erlang indep_vars_setsum) (auto intro!: indep_vars_subset)
    also have "(\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) = (\<lambda>x. \<Sum>i\<in>insert i I. X i x)"
      using insert by auto
    also have "Suc(k i) + Suc ((\<Sum>i\<in>I. Suc (k i)) - 1) - 1 = (\<Sum>i\<in>insert i I. Suc (k i)) - 1"
      using insert by (auto intro!: Suc_pred simp: ac_simps)    
    finally show ?case by fast
qed

lemma (in prob_space) exponential_distributed_setsum:
  assumes finI: "finite I"
  assumes A: "I \<noteq> {}"
  assumes expX: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (exponential_density l)"
  assumes ind: "indep_vars (\<lambda>i. borel) X I" 
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (erlang_density ((card I) - 1) l)"
proof -
  obtain i where "i \<in> I" using assms by auto
  note exponential_distributed_params[OF expX[OF this]]
  from erlang_distributed_setsum[OF assms(1,2) this assms(3,4)] show ?thesis by simp
qed

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

lemma (in prob_space) uniform_distributed_variance:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  shows "variance X = (b - a)\<^sup>2 / 12"
proof (subst distributed_variance)
  have [arith]: "a < b" using uniform_distributed_bounds[OF D] .
  let ?\<mu> = "expectation X" let ?D = "\<lambda>x. indicator {a..b} (x + ?\<mu>) / measure lborel {a..b}"
  have "(\<integral>x. x\<^sup>2 * (?D x) \<partial>lborel) = (\<integral>x. x\<^sup>2 * (indicator {a - ?\<mu> .. b - ?\<mu>} x) / measure lborel {a .. b} \<partial>lborel)"
    by (intro integral_cong) (auto split: split_indicator)
  also have "\<dots> = (b - a)\<^sup>2 / 12"
    by (simp add: integral_power measure_lebesgue_Icc uniform_distributed_expectation[OF D])
       (simp add: eval_nat_numeral field_simps )
  finally show "(\<integral>x. x\<^sup>2 * ?D x \<partial>lborel) = (b - a)\<^sup>2 / 12" .
qed fact

end
