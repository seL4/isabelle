(*  Title:      HOL/Probability/Convolution.thy
    Author:     Sudeep Kanav, TU München
    Author:     Johannes Hölzl, TU München *)

section \<open>Convolution Measure\<close>

theory Convolution
  imports Independent_Family
begin

lemma (in finite_measure) sigma_finite_measure: "sigma_finite_measure M"
  ..

definition convolution :: "('a :: ordered_euclidean_space) measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" (infix \<open>\<star>\<close> 50) where
  "convolution M N = distr (M \<Otimes>\<^sub>M N) borel (\<lambda>(x, y). x + y)"

lemma
  shows space_convolution[simp]: "space (convolution M N) = space borel"
    and sets_convolution[simp]: "sets (convolution M N) = sets borel"
    and measurable_convolution1[simp]: "measurable A (convolution M N) = measurable A borel"
    and measurable_convolution2[simp]: "measurable (convolution M N) B = measurable borel B"
  by (simp_all add: convolution_def)

lemma nn_integral_convolution:
  assumes "finite_measure M" "finite_measure N"
  assumes [measurable_cong]: "sets N = sets borel" "sets M = sets borel"
  assumes [measurable]: "f \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x. f x \<partial>convolution M N) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x + y) \<partial>N \<partial>M)"
proof -
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  interpret pair_sigma_finite M N ..
  show ?thesis
    unfolding convolution_def
    by (simp add: nn_integral_distr N.nn_integral_fst[symmetric])
qed

lemma convolution_emeasure:
  assumes "A \<in> sets borel" "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  assumes [simp]: "space M = space N" "space N = space borel"
  shows "emeasure (M \<star> N) A = \<integral>\<^sup>+x. (emeasure N {a. a + x \<in> A}) \<partial>M "
  using assms by (auto intro!: nn_integral_cong simp del: nn_integral_indicator simp: nn_integral_convolution
    nn_integral_indicator [symmetric] ac_simps split:split_indicator)

lemma convolution_emeasure':
  assumes [simp]:"A \<in> sets borel"
  assumes [simp]: "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  shows  "emeasure (M \<star> N) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y.  (indicator  A (x + y)) \<partial>N  \<partial>M"
  by (auto simp del: nn_integral_indicator simp: nn_integral_convolution
    nn_integral_indicator[symmetric] borel_measurable_indicator)

lemma convolution_finite:
  assumes [simp]: "finite_measure M" "finite_measure N"
  assumes [measurable_cong]: "sets N = sets borel" "sets M = sets borel"
  shows "finite_measure (M \<star> N)"
  unfolding convolution_def
  by (intro finite_measure_pair_measure finite_measure.finite_measure_distr) auto

lemma convolution_emeasure_3:
  assumes [simp, measurable]: "A \<in> sets borel"
  assumes [simp]: "finite_measure M" "finite_measure N" "finite_measure L"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel" "sets L = sets borel"
  shows "emeasure (L \<star> (M \<star> N )) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z. indicator A (x + y + z) \<partial>N \<partial>M \<partial>L"
  apply (subst nn_integral_indicator[symmetric], simp)
  apply (subst nn_integral_convolution,
        auto intro!: borel_measurable_indicator borel_measurable_indicator' convolution_finite)+
  by (rule nn_integral_cong)+ (auto simp: semigroup_add_class.add.assoc)

lemma convolution_emeasure_3':
  assumes [simp, measurable]:"A \<in> sets borel"
  assumes [simp]: "finite_measure M" "finite_measure N"  "finite_measure L"
  assumes [measurable_cong, simp]: "sets N = sets borel" "sets M = sets borel" "sets L = sets borel"
  shows "emeasure ((L \<star> M) \<star> N ) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z. indicator A (x + y + z) \<partial>N \<partial>M \<partial>L"
  apply (subst nn_integral_indicator[symmetric], simp)+
  apply (subst nn_integral_convolution)
  apply (simp_all add: convolution_finite)
  apply (subst nn_integral_convolution)
  apply (simp_all add: finite_measure.sigma_finite_measure sigma_finite_measure.borel_measurable_nn_integral)
  done

lemma convolution_commutative:
  assumes [simp]: "finite_measure M" "finite_measure N"
  assumes [measurable_cong, simp]: "sets N = sets borel" "sets M = sets borel"
  shows "(M \<star> N) = (N \<star> M)"
proof (rule measure_eqI)
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  interpret pair_sigma_finite M N ..

  show "sets (M \<star> N) = sets (N \<star> M)" by simp

  fix A assume "A \<in> sets (M \<star> N)"
  then have 1[measurable]:"A \<in> sets borel" by simp
  have "emeasure (M \<star> N) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator A (x + y) \<partial>N \<partial>M" by (auto intro!: convolution_emeasure')
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. (\<lambda>(x,y). indicator A (x + y)) (x, y) \<partial>N \<partial>M" by (auto intro!: nn_integral_cong)
  also have "... = \<integral>\<^sup>+y. \<integral>\<^sup>+x. (\<lambda>(x,y). indicator A (x + y)) (x, y) \<partial>M \<partial>N" by (rule Fubini[symmetric]) simp
  also have "... = emeasure (N \<star> M) A" by (auto intro!: nn_integral_cong simp: add.commute convolution_emeasure')
  finally show "emeasure (M \<star> N) A = emeasure (N \<star> M) A" by simp
qed

lemma convolution_associative:
  assumes [simp]: "finite_measure M" "finite_measure N"  "finite_measure L"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel" "sets L = sets borel"
  shows "(L \<star> (M \<star> N)) = ((L \<star> M) \<star> N)"
  by (auto intro!: measure_eqI simp: convolution_emeasure_3 convolution_emeasure_3')

lemma (in prob_space) sum_indep_random_variable:
  assumes ind: "indep_var borel X borel Y"
  assumes [simp, measurable]: "random_variable borel X"
  assumes [simp, measurable]: "random_variable borel Y"
  shows "distr M borel (\<lambda>x. X x + Y x) = convolution (distr M borel X)  (distr M borel Y)"
  using ind unfolding indep_var_distribution_eq convolution_def
  by (auto simp: distr_distr intro!:arg_cong[where f = "distr M borel"])

lemma (in prob_space) sum_indep_random_variable_lborel:
  assumes ind: "indep_var borel X borel Y"
  assumes [simp, measurable]: "random_variable lborel X"
  assumes [simp, measurable]:"random_variable lborel Y"
  shows "distr M lborel (\<lambda>x. X x + Y x) = convolution (distr M lborel X)  (distr M lborel Y)"
  using ind unfolding indep_var_distribution_eq convolution_def
  by (auto simp: distr_distr o_def intro!: arg_cong[where f = "distr M borel"] cong: distr_cong)

lemma convolution_density:
  fixes f g :: "real \<Rightarrow> ennreal"
  assumes [measurable]: "f \<in> borel_measurable borel" "g \<in> borel_measurable borel"
  assumes [simp]:"finite_measure (density lborel f)" "finite_measure (density lborel g)"
  shows "density lborel f \<star> density lborel g = density lborel (\<lambda>x. \<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel)"
    (is "?l = ?r")
proof (intro measure_eqI)
  fix A assume "A \<in> sets ?l"
  then have [measurable]: "A \<in> sets borel"
    by simp

  have "(\<integral>\<^sup>+x. f x * (\<integral>\<^sup>+y. g y * indicator A (x + y) \<partial>lborel) \<partial>lborel) =
    (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. g y * (f x * indicator A (x + y)) \<partial>lborel) \<partial>lborel)"
  proof (intro nn_integral_cong_AE, eventually_elim)
    fix x
    have "f x * (\<integral>\<^sup>+ y. g y * indicator A (x + y) \<partial>lborel) =
      (\<integral>\<^sup>+ y. f x * (g y * indicator A (x + y)) \<partial>lborel)"
      by (intro nn_integral_cmult[symmetric]) auto
    then show "f x * (\<integral>\<^sup>+ y. g y * indicator A (x + y) \<partial>lborel) =
      (\<integral>\<^sup>+ y. g y * (f x * indicator A (x + y)) \<partial>lborel)"
      by (simp add: ac_simps)
  qed
  also have "\<dots> = (\<integral>\<^sup>+y. (\<integral>\<^sup>+x. g y * (f x * indicator A (x + y)) \<partial>lborel) \<partial>lborel)"
    by (intro lborel_pair.Fubini') simp
  also have "\<dots> = (\<integral>\<^sup>+y. (\<integral>\<^sup>+x. f (x - y) * g y * indicator A x \<partial>lborel) \<partial>lborel)"
  proof (intro nn_integral_cong_AE, eventually_elim)
    fix y
    have "(\<integral>\<^sup>+x. g y * (f x * indicator A (x + y)) \<partial>lborel) =
      g y * (\<integral>\<^sup>+x. f x * indicator A (x + y) \<partial>lborel)"
      by (intro nn_integral_cmult) auto
    also have "\<dots> = g y * (\<integral>\<^sup>+x. f (x - y) * indicator A x \<partial>lborel)"
      by (subst nn_integral_real_affine[where c=1 and t="-y"])
         (auto simp add: one_ennreal_def[symmetric])
    also have "\<dots> = (\<integral>\<^sup>+x. g y * (f (x - y) * indicator A x) \<partial>lborel)"
      by (intro nn_integral_cmult[symmetric]) auto
    finally show "(\<integral>\<^sup>+ x. g y * (f x * indicator A (x + y)) \<partial>lborel) =
      (\<integral>\<^sup>+ x. f (x - y) * g y * indicator A x \<partial>lborel)"
      by (simp add: ac_simps)
  qed
  also have "\<dots> = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x - y) * g y * indicator A x \<partial>lborel) \<partial>lborel)"
    by (intro lborel_pair.Fubini') simp
  finally show "emeasure ?l A = emeasure ?r A"
    by (auto simp: convolution_emeasure' nn_integral_density emeasure_density
      nn_integral_multc)
qed simp

lemma (in prob_space) distributed_finite_measure_density:
  "distributed M N X f \<Longrightarrow> finite_measure (density N f)"
  using finite_measure_distr[of X N] distributed_distr_eq_density[of M N X f] by simp


lemma (in prob_space) distributed_convolution:
  fixes f :: "real \<Rightarrow> _"
  fixes g :: "real \<Rightarrow> _"
  assumes indep: "indep_var borel X borel Y"
  assumes X: "distributed M lborel X f"
  assumes Y: "distributed M lborel Y g"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (\<lambda>x. \<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel)"
  unfolding distributed_def
proof safe
  have fg[measurable]: "f \<in> borel_measurable borel" "g \<in> borel_measurable borel"
    using distributed_borel_measurable[OF X] distributed_borel_measurable[OF Y] by simp_all

  show "(\<lambda>x. \<integral>\<^sup>+ xa. f (x - xa) * g xa \<partial>lborel) \<in> borel_measurable lborel"
    by measurable

  have "distr M borel (\<lambda>x. X x + Y x) = (distr M borel X \<star> distr M borel Y)"
    using distributed_measurable[OF X] distributed_measurable[OF Y]
    by (intro sum_indep_random_variable) (auto simp: indep)
  also have "\<dots> = (density lborel f \<star> density lborel g)"
    using distributed_distr_eq_density[OF X] distributed_distr_eq_density[OF Y]
    by (simp cong: distr_cong)
  also have "\<dots> = density lborel (\<lambda>x. \<integral>\<^sup>+ y. f (x - y) * g y \<partial>lborel)"
  proof (rule convolution_density)
    show "finite_measure (density lborel f)"
      using X by (rule distributed_finite_measure_density)
    show "finite_measure (density lborel g)"
      using Y by (rule distributed_finite_measure_density)
  qed fact+
  finally show "distr M lborel (\<lambda>x. X x + Y x) = density lborel (\<lambda>x. \<integral>\<^sup>+ y. f (x - y) * g y \<partial>lborel)"
    by (simp cong: distr_cong)
  show "random_variable lborel (\<lambda>x. X x + Y x)"
    using distributed_measurable[OF X] distributed_measurable[OF Y] by simp
qed

lemma prob_space_convolution_density:
  fixes f:: "real \<Rightarrow> _"
  fixes g:: "real \<Rightarrow> _"
  assumes [measurable]: "f\<in> borel_measurable borel"
  assumes [measurable]: "g\<in> borel_measurable borel"
  assumes gt_0[simp]: "\<And>x. 0 \<le> f x" "\<And>x. 0 \<le> g x"
  assumes "prob_space (density lborel f)" (is "prob_space ?F")
  assumes "prob_space (density lborel g)" (is "prob_space ?G")
  shows "prob_space (density lborel (\<lambda>x.\<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel))" (is "prob_space ?D")
proof (subst convolution_density[symmetric])
  interpret F: prob_space ?F by fact
  show "finite_measure ?F" by unfold_locales
  interpret G: prob_space ?G by fact
  show "finite_measure ?G" by unfold_locales
  interpret FG: pair_prob_space ?F ?G ..

  show "prob_space (density lborel f \<star> density lborel g)"
    unfolding convolution_def by (rule FG.prob_space_distr) simp
qed simp_all

end
