(*  Title:      HOL/Probability/Probability_Mass_Function.thy
    Author:     Johannes Hölzl, TU München
    Author:     Andreas Lochbihler, ETH Zurich
    Author:     Manuel Eberl, TU München
*)

section \<open> Probability mass function \<close>

theory Probability_Mass_Function
imports
  Giry_Monad
  "HOL-Library.Multiset"
begin

lemma AE_emeasure_singleton:
  assumes x: "emeasure M {x} \<noteq> 0" and ae: "AE x in M. P x" shows "P x"
proof -
  from x have x_M: "{x} \<in> sets M"
    by (auto intro: emeasure_notin_sets)
  from ae obtain N where N: "{x\<in>space M. \<not> P x} \<subseteq> N" "emeasure M N = 0" "N \<in> sets M"
    by (auto elim: AE_E)
  { assume "\<not> P x"
    with x_M[THEN sets.sets_into_space] N have "emeasure M {x} \<le> emeasure M N"
      by (intro emeasure_mono) auto
    with x N have False
      by (auto simp:) }
  then show "P x" by auto
qed

lemma AE_measure_singleton: "measure M {x} \<noteq> 0 \<Longrightarrow> AE x in M. P x \<Longrightarrow> P x"
  by (metis AE_emeasure_singleton measure_def emeasure_empty measure_empty)

lemma (in finite_measure) AE_support_countable:
  assumes [simp]: "sets M = UNIV"
  shows "(AE x in M. measure M {x} \<noteq> 0) \<longleftrightarrow> (\<exists>S. countable S \<and> (AE x in M. x \<in> S))"
proof
  assume "\<exists>S. countable S \<and> (AE x in M. x \<in> S)"
  then obtain S where S[intro]: "countable S" and ae: "AE x in M. x \<in> S"
    by auto
  then have "emeasure M (\<Union>x\<in>{x\<in>S. emeasure M {x} \<noteq> 0}. {x}) =
    (\<integral>\<^sup>+ x. emeasure M {x} * indicator {x\<in>S. emeasure M {x} \<noteq> 0} x \<partial>count_space UNIV)"
    by (subst emeasure_UN_countable)
       (auto simp: disjoint_family_on_def nn_integral_restrict_space[symmetric] restrict_count_space)
  also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} * indicator S x \<partial>count_space UNIV)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = emeasure M (\<Union>x\<in>S. {x})"
    by (subst emeasure_UN_countable)
       (auto simp: disjoint_family_on_def nn_integral_restrict_space[symmetric] restrict_count_space)
  also have "\<dots> = emeasure M (space M)"
    using ae by (intro emeasure_eq_AE) auto
  finally have "emeasure M {x \<in> space M. x\<in>S \<and> emeasure M {x} \<noteq> 0} = emeasure M (space M)"
    by (simp add: emeasure_single_in_space cong: rev_conj_cong)
  with finite_measure_compl[of "{x \<in> space M. x\<in>S \<and> emeasure M {x} \<noteq> 0}"]
  have "AE x in M. x \<in> S \<and> emeasure M {x} \<noteq> 0"
    by (intro AE_I[OF order_refl]) (auto simp: emeasure_eq_measure measure_nonneg set_diff_eq cong: conj_cong)
  then show "AE x in M. measure M {x} \<noteq> 0"
    by (auto simp: emeasure_eq_measure)
qed (auto intro!: exI[of _ "{x. measure M {x} \<noteq> 0}"] countable_support)

subsection \<open> PMF as measure \<close>

typedef 'a pmf = "{M :: 'a measure. prob_space M \<and> sets M = UNIV \<and> (AE x in M. measure M {x} \<noteq> 0)}"
  morphisms measure_pmf Abs_pmf
  by (intro exI[of _ "uniform_measure (count_space UNIV) {undefined}"])
     (auto intro!: prob_space_uniform_measure AE_uniform_measureI)

declare [[coercion measure_pmf]]

lemma prob_space_measure_pmf: "prob_space (measure_pmf p)"
  using pmf.measure_pmf[of p] by auto

interpretation measure_pmf: prob_space "measure_pmf M" for M
  by (rule prob_space_measure_pmf)

interpretation measure_pmf: subprob_space "measure_pmf M" for M
  by (rule prob_space_imp_subprob_space) unfold_locales

lemma subprob_space_measure_pmf: "subprob_space (measure_pmf x)"
  by unfold_locales

locale pmf_as_measure
begin

setup_lifting type_definition_pmf

end

context
begin

interpretation pmf_as_measure .

lemma sets_measure_pmf[simp]: "sets (measure_pmf p) = UNIV"
  by transfer blast

lemma sets_measure_pmf_count_space[measurable_cong]:
  "sets (measure_pmf M) = sets (count_space UNIV)"
  by simp

lemma space_measure_pmf[simp]: "space (measure_pmf p) = UNIV"
  using sets_eq_imp_space_eq[of "measure_pmf p" "count_space UNIV"] by simp

lemma measure_pmf_UNIV [simp]: "measure (measure_pmf p) UNIV = 1"
using measure_pmf.prob_space[of p] by simp

lemma measure_pmf_in_subprob_algebra[measurable (raw)]: "measure_pmf x \<in> space (subprob_algebra (count_space UNIV))"
  by (simp add: space_subprob_algebra subprob_space_measure_pmf)

lemma measurable_pmf_measure1[simp]: "measurable (M :: 'a pmf) N = UNIV \<rightarrow> space N"
  by (auto simp: measurable_def)

lemma measurable_pmf_measure2[simp]: "measurable N (M :: 'a pmf) = measurable N (count_space UNIV)"
  by (intro measurable_cong_sets) simp_all

lemma measurable_pair_restrict_pmf2:
  assumes "countable A"
  assumes [measurable]: "\<And>y. y \<in> A \<Longrightarrow> (\<lambda>x. f (x, y)) \<in> measurable M L"
  shows "f \<in> measurable (M \<Otimes>\<^sub>M restrict_space (measure_pmf N) A) L" (is "f \<in> measurable ?M _")
proof -
  have [measurable_cong]: "sets (restrict_space (count_space UNIV) A) = sets (count_space A)"
    by (simp add: restrict_count_space)

  show ?thesis
    by (intro measurable_compose_countable'[where f="\<lambda>a b. f (fst b, a)" and g=snd and I=A,
                                            unfolded prod.collapse] assms)
        measurable
qed

lemma measurable_pair_restrict_pmf1:
  assumes "countable A"
  assumes [measurable]: "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) \<in> measurable N L"
  shows "f \<in> measurable (restrict_space (measure_pmf M) A \<Otimes>\<^sub>M N) L"
proof -
  have [measurable_cong]: "sets (restrict_space (count_space UNIV) A) = sets (count_space A)"
    by (simp add: restrict_count_space)

  show ?thesis
    by (intro measurable_compose_countable'[where f="\<lambda>a b. f (a, snd b)" and g=fst and I=A,
                                            unfolded prod.collapse] assms)
        measurable
qed

lift_definition pmf :: "'a pmf \<Rightarrow> 'a \<Rightarrow> real" is "\<lambda>M x. measure M {x}" .

lift_definition set_pmf :: "'a pmf \<Rightarrow> 'a set" is "\<lambda>M. {x. measure M {x} \<noteq> 0}" .
declare [[coercion set_pmf]]

lemma AE_measure_pmf: "AE x in (M::'a pmf). x \<in> M"
  by transfer simp

lemma emeasure_pmf_single_eq_zero_iff:
  fixes M :: "'a pmf"
  shows "emeasure M {y} = 0 \<longleftrightarrow> y \<notin> M"
  unfolding set_pmf.rep_eq by (simp add: measure_pmf.emeasure_eq_measure)

lemma AE_measure_pmf_iff: "(AE x in measure_pmf M. P x) \<longleftrightarrow> (\<forall>y\<in>M. P y)"
  using AE_measure_singleton[of M] AE_measure_pmf[of M]
  by (auto simp: set_pmf.rep_eq)

lemma AE_pmfI: "(\<And>y. y \<in> set_pmf M \<Longrightarrow> P y) \<Longrightarrow> almost_everywhere (measure_pmf M) P"
by(simp add: AE_measure_pmf_iff)

lemma countable_set_pmf [simp]: "countable (set_pmf p)"
  by transfer (metis prob_space.finite_measure finite_measure.countable_support)

lemma pmf_positive: "x \<in> set_pmf p \<Longrightarrow> 0 < pmf p x"
  by transfer (simp add: less_le)

lemma pmf_nonneg[simp]: "0 \<le> pmf p x"
  by transfer simp

lemma pmf_not_neg [simp]: "\<not>pmf p x < 0"
  by (simp add: not_less pmf_nonneg)

lemma pmf_pos [simp]: "pmf p x \<noteq> 0 \<Longrightarrow> pmf p x > 0"
  using pmf_nonneg[of p x] by linarith

lemma pmf_le_1: "pmf p x \<le> 1"
  by (simp add: pmf.rep_eq)

lemma set_pmf_not_empty: "set_pmf M \<noteq> {}"
  using AE_measure_pmf[of M] by (intro notI) simp

lemma set_pmf_iff: "x \<in> set_pmf M \<longleftrightarrow> pmf M x \<noteq> 0"
  by transfer simp

lemma pmf_positive_iff: "0 < pmf p x \<longleftrightarrow> x \<in> set_pmf p"
  unfolding less_le by (simp add: set_pmf_iff)

lemma set_pmf_eq: "set_pmf M = {x. pmf M x \<noteq> 0}"
  by (auto simp: set_pmf_iff)

lemma set_pmf_eq': "set_pmf p = {x. pmf p x > 0}"
proof safe
  fix x assume "x \<in> set_pmf p"
  hence "pmf p x \<noteq> 0" by (auto simp: set_pmf_eq)
  with pmf_nonneg[of p x] show "pmf p x > 0" by simp
qed (auto simp: set_pmf_eq)

lemma emeasure_pmf_single:
  fixes M :: "'a pmf"
  shows "emeasure M {x} = pmf M x"
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma measure_pmf_single: "measure (measure_pmf M) {x} = pmf M x"
  using emeasure_pmf_single[of M x] by(simp add: measure_pmf.emeasure_eq_measure pmf_nonneg measure_nonneg)

lemma emeasure_measure_pmf_finite: "finite S \<Longrightarrow> emeasure (measure_pmf M) S = (\<Sum>s\<in>S. pmf M s)"
  by (subst emeasure_eq_sum_singleton) (auto simp: emeasure_pmf_single pmf_nonneg)

lemma measure_measure_pmf_finite: "finite S \<Longrightarrow> measure (measure_pmf M) S = sum (pmf M) S"
  using emeasure_measure_pmf_finite[of S M]
  by (simp add: measure_pmf.emeasure_eq_measure measure_nonneg sum_nonneg pmf_nonneg)

lemma sum_pmf_eq_1:
  assumes "finite A" "set_pmf p \<subseteq> A"
  shows   "(\<Sum>x\<in>A. pmf p x) = 1"
proof -
  have "(\<Sum>x\<in>A. pmf p x) = measure_pmf.prob p A"
    by (simp add: measure_measure_pmf_finite assms)
  also from assms have "\<dots> = 1"
    by (subst measure_pmf.prob_eq_1) (auto simp: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma nn_integral_measure_pmf_support:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes f: "finite A" and nn: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" "\<And>x. x \<in> set_pmf M \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>A. f x * pmf M x)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M)"
    using nn by (intro nn_integral_cong_AE) (auto simp: AE_measure_pmf_iff split: split_indicator)
  also have "\<dots> = (\<Sum>x\<in>A. f x * emeasure M {x})"
    using assms by (intro nn_integral_indicator_finite) auto
  finally show ?thesis
    by (simp add: emeasure_measure_pmf_finite)
qed

lemma nn_integral_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes f: "finite (set_pmf M)" and nn: "\<And>x. x \<in> set_pmf M \<Longrightarrow> 0 \<le> f x"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>set_pmf M. f x * pmf M x)"
  using assms by (intro nn_integral_measure_pmf_support) auto

lemma integrable_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "finite (set_pmf M) \<Longrightarrow> integrable M f"
  by (auto intro!: integrableI_bounded simp: nn_integral_measure_pmf_finite ennreal_mult_less_top)

lemma integral_measure_pmf_real:
  assumes [simp]: "finite A" and "\<And>a. a \<in> set_pmf M \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> A"
  shows "(\<integral>x. f x \<partial>measure_pmf M) = (\<Sum>a\<in>A. f a * pmf M a)"
proof -
  have "(\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x * indicator A x \<partial>measure_pmf M)"
    using assms(2) by (intro integral_cong_AE) (auto split: split_indicator simp: AE_measure_pmf_iff)
  also have "\<dots> = (\<Sum>a\<in>A. f a * pmf M a)"
    by (subst integral_indicator_finite_real)
       (auto simp: measure_def emeasure_measure_pmf_finite pmf_nonneg)
  finally show ?thesis .
qed

lemma integrable_pmf: "integrable (count_space X) (pmf M)"
proof -
  have " (\<integral>\<^sup>+ x. pmf M x \<partial>count_space X) = (\<integral>\<^sup>+ x. pmf M x \<partial>count_space (M \<inter> X))"
    by (auto simp add: nn_integral_count_space_indicator set_pmf_iff intro!: nn_integral_cong split: split_indicator)
  then have "integrable (count_space X) (pmf M) = integrable (count_space (M \<inter> X)) (pmf M)"
    by (simp add: integrable_iff_bounded pmf_nonneg)
  then show ?thesis
    by (simp add: pmf.rep_eq measure_pmf.integrable_measure disjoint_family_on_def)
qed

lemma integral_pmf: "(\<integral>x. pmf M x \<partial>count_space X) = measure M X"
proof -
  have "(\<integral>x. pmf M x \<partial>count_space X) = (\<integral>\<^sup>+x. pmf M x \<partial>count_space X)"
    by (simp add: pmf_nonneg integrable_pmf nn_integral_eq_integral)
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space (X \<inter> M))"
    by (auto intro!: nn_integral_cong_AE split: split_indicator
             simp: pmf.rep_eq measure_pmf.emeasure_eq_measure nn_integral_count_space_indicator
                   AE_count_space set_pmf_iff)
  also have "\<dots> = emeasure M (X \<inter> M)"
    by (rule emeasure_countable_singleton[symmetric]) (auto intro: countable_set_pmf)
  also have "\<dots> = emeasure M X"
    by (auto intro!: emeasure_eq_AE simp: AE_measure_pmf_iff)
  finally show ?thesis
    by (simp add: measure_pmf.emeasure_eq_measure measure_nonneg integral_nonneg pmf_nonneg)
qed

lemma integral_pmf_restrict:
  "(f::'a \<Rightarrow> 'b::{banach, second_countable_topology}) \<in> borel_measurable (count_space UNIV) \<Longrightarrow>
    (\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x \<partial>restrict_space M M)"
  by (auto intro!: integral_cong_AE simp add: integral_restrict_space AE_measure_pmf_iff)

lemma emeasure_pmf: "emeasure (M::'a pmf) M = 1"
proof -
  have "emeasure (M::'a pmf) M = emeasure (M::'a pmf) (space M)"
    by (intro emeasure_eq_AE) (simp_all add: AE_measure_pmf)
  then show ?thesis
    using measure_pmf.emeasure_space_1 by simp
qed

lemma emeasure_pmf_UNIV [simp]: "emeasure (measure_pmf M) UNIV = 1"
using measure_pmf.emeasure_space_1[of M] by simp

lemma in_null_sets_measure_pmfI:
  "A \<inter> set_pmf p = {} \<Longrightarrow> A \<in> null_sets (measure_pmf p)"
using emeasure_eq_0_AE[where ?P="\<lambda>x. x \<in> A" and M="measure_pmf p"]
by(auto simp add: null_sets_def AE_measure_pmf_iff)

lemma measure_subprob: "measure_pmf M \<in> space (subprob_algebra (count_space UNIV))"
  by (simp add: space_subprob_algebra subprob_space_measure_pmf)

subsection \<open> Monad Interpretation \<close>

lemma measurable_measure_pmf[measurable]:
  "(\<lambda>x. measure_pmf (M x)) \<in> measurable (count_space UNIV) (subprob_algebra (count_space UNIV))"
  by (auto simp: space_subprob_algebra intro!: prob_space_imp_subprob_space) unfold_locales

lemma bind_measure_pmf_cong:
  assumes "\<And>x. A x \<in> space (subprob_algebra N)" "\<And>x. B x \<in> space (subprob_algebra N)"
  assumes "\<And>i. i \<in> set_pmf x \<Longrightarrow> A i = B i"
  shows "bind (measure_pmf x) A = bind (measure_pmf x) B"
proof (rule measure_eqI)
  show "sets (measure_pmf x \<bind> A) = sets (measure_pmf x \<bind> B)"
    using assms by (subst (1 2) sets_bind) (auto simp: space_subprob_algebra)
next
  fix X assume "X \<in> sets (measure_pmf x \<bind> A)"
  then have X: "X \<in> sets N"
    using assms by (subst (asm) sets_bind) (auto simp: space_subprob_algebra)
  show "emeasure (measure_pmf x \<bind> A) X = emeasure (measure_pmf x \<bind> B) X"
    using assms
    by (subst (1 2) emeasure_bind[where N=N, OF _ _ X])
       (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
qed

lift_definition bind_pmf :: "'a pmf \<Rightarrow> ('a \<Rightarrow> 'b pmf ) \<Rightarrow> 'b pmf" is bind
proof (clarify, intro conjI)
  fix f :: "'a measure" and g :: "'a \<Rightarrow> 'b measure"
  assume "prob_space f"
  then interpret f: prob_space f .
  assume "sets f = UNIV" and ae_f: "AE x in f. measure f {x} \<noteq> 0"
  then have s_f[simp]: "sets f = sets (count_space UNIV)"
    by simp
  assume g: "\<And>x. prob_space (g x) \<and> sets (g x) = UNIV \<and> (AE y in g x. measure (g x) {y} \<noteq> 0)"
  then have g: "\<And>x. prob_space (g x)" and s_g[simp]: "\<And>x. sets (g x) = sets (count_space UNIV)"
    and ae_g: "\<And>x. AE y in g x. measure (g x) {y} \<noteq> 0"
    by auto

  have [measurable]: "g \<in> measurable f (subprob_algebra (count_space UNIV))"
    by (auto simp: measurable_def space_subprob_algebra prob_space_imp_subprob_space g)

  show "prob_space (f \<bind> g)"
    using g by (intro f.prob_space_bind[where S="count_space UNIV"]) auto
  then interpret fg: prob_space "f \<bind> g" .
  show [simp]: "sets (f \<bind> g) = UNIV"
    using sets_eq_imp_space_eq[OF s_f]
    by (subst sets_bind[where N="count_space UNIV"]) auto
  show "AE x in f \<bind> g. measure (f \<bind> g) {x} \<noteq> 0"
    apply (simp add: fg.prob_eq_0 AE_bind[where B="count_space UNIV"])
    using ae_f
    apply eventually_elim
    using ae_g
    apply eventually_elim
    apply (auto dest: AE_measure_singleton)
    done
qed

adhoc_overloading Monad_Syntax.bind bind_pmf

lemma ennreal_pmf_bind: "pmf (bind_pmf N f) i = (\<integral>\<^sup>+x. pmf (f x) i \<partial>measure_pmf N)"
  unfolding pmf.rep_eq bind_pmf.rep_eq
  by (auto simp: measure_pmf.measure_bind[where N="count_space UNIV"] measure_subprob measure_nonneg
           intro!: nn_integral_eq_integral[symmetric] measure_pmf.integrable_const_bound[where B=1])

lemma pmf_bind: "pmf (bind_pmf N f) i = (\<integral>x. pmf (f x) i \<partial>measure_pmf N)"
  using ennreal_pmf_bind[of N f i]
  by (subst (asm) nn_integral_eq_integral)
     (auto simp: pmf_nonneg pmf_le_1 pmf_nonneg integral_nonneg
           intro!: nn_integral_eq_integral[symmetric] measure_pmf.integrable_const_bound[where B=1])

lemma bind_pmf_const[simp]: "bind_pmf M (\<lambda>x. c) = c"
  by transfer (simp add: bind_const' prob_space_imp_subprob_space)

lemma set_bind_pmf[simp]: "set_pmf (bind_pmf M N) = (\<Union>M\<in>set_pmf M. set_pmf (N M))"
proof -
  have "set_pmf (bind_pmf M N) = {x. ennreal (pmf (bind_pmf M N) x) \<noteq> 0}"
    by (simp add: set_pmf_eq pmf_nonneg)
  also have "\<dots> = (\<Union>M\<in>set_pmf M. set_pmf (N M))"
    unfolding ennreal_pmf_bind
    by (subst nn_integral_0_iff_AE) (auto simp: AE_measure_pmf_iff pmf_nonneg set_pmf_eq)
  finally show ?thesis .
qed

lemma bind_pmf_cong [fundef_cong]:
  assumes "p = q"
  shows "(\<And>x. x \<in> set_pmf q \<Longrightarrow> f x = g x) \<Longrightarrow> bind_pmf p f = bind_pmf q g"
  unfolding \<open>p = q\<close>[symmetric] measure_pmf_inject[symmetric] bind_pmf.rep_eq
  by (auto simp: AE_measure_pmf_iff Pi_iff space_subprob_algebra subprob_space_measure_pmf
                 sets_bind[where N="count_space UNIV"] emeasure_bind[where N="count_space UNIV"]
           intro!: nn_integral_cong_AE measure_eqI)

lemma bind_pmf_cong_simp:
  "p = q \<Longrightarrow> (\<And>x. x \<in> set_pmf q =simp=> f x = g x) \<Longrightarrow> bind_pmf p f = bind_pmf q g"
  by (simp add: simp_implies_def cong: bind_pmf_cong)

lemma measure_pmf_bind: "measure_pmf (bind_pmf M f) = (measure_pmf M \<bind> (\<lambda>x. measure_pmf (f x)))"
  by transfer simp

lemma nn_integral_bind_pmf[simp]: "(\<integral>\<^sup>+x. f x \<partial>bind_pmf M N) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f y \<partial>N x \<partial>M)"
  using measurable_measure_pmf[of N]
  unfolding measure_pmf_bind
  apply (intro nn_integral_bind[where B="count_space UNIV"])
  apply auto
  done

lemma emeasure_bind_pmf[simp]: "emeasure (bind_pmf M N) X = (\<integral>\<^sup>+x. emeasure (N x) X \<partial>M)"
  using measurable_measure_pmf[of N]
  unfolding measure_pmf_bind
  by (subst emeasure_bind[where N="count_space UNIV"]) auto

lift_definition return_pmf :: "'a \<Rightarrow> 'a pmf" is "return (count_space UNIV)"
  by (auto intro!: prob_space_return simp: AE_return measure_return)

lemma bind_return_pmf: "bind_pmf (return_pmf x) f = f x"
  by transfer
     (auto intro!: prob_space_imp_subprob_space bind_return[where N="count_space UNIV"]
           simp: space_subprob_algebra)

lemma set_return_pmf[simp]: "set_pmf (return_pmf x) = {x}"
  by transfer (auto simp add: measure_return split: split_indicator)

lemma bind_return_pmf': "bind_pmf N return_pmf = N"
proof (transfer, clarify)
  fix N :: "'a measure" assume "sets N = UNIV" then show "N \<bind> return (count_space UNIV) = N"
    by (subst return_sets_cong[where N=N]) (simp_all add: bind_return')
qed

lemma bind_assoc_pmf: "bind_pmf (bind_pmf A B) C = bind_pmf A (\<lambda>x. bind_pmf (B x) C)"
  by transfer
     (auto intro!: bind_assoc[where N="count_space UNIV" and R="count_space UNIV"]
           simp: measurable_def space_subprob_algebra prob_space_imp_subprob_space)

definition "map_pmf f M = bind_pmf M (\<lambda>x. return_pmf (f x))"

lemma map_bind_pmf: "map_pmf f (bind_pmf M g) = bind_pmf M (\<lambda>x. map_pmf f (g x))"
  by (simp add: map_pmf_def bind_assoc_pmf)

lemma bind_map_pmf: "bind_pmf (map_pmf f M) g = bind_pmf M (\<lambda>x. g (f x))"
  by (simp add: map_pmf_def bind_assoc_pmf bind_return_pmf)

lemma map_pmf_transfer[transfer_rule]:
  "rel_fun (=) (rel_fun cr_pmf cr_pmf) (\<lambda>f M. distr M (count_space UNIV) f) map_pmf"
proof -
  have "rel_fun (=) (rel_fun pmf_as_measure.cr_pmf pmf_as_measure.cr_pmf)
     (\<lambda>f M. M \<bind> (return (count_space UNIV) o f)) map_pmf"
    unfolding map_pmf_def[abs_def] comp_def by transfer_prover
  then show ?thesis
    by (force simp: rel_fun_def cr_pmf_def bind_return_distr)
qed

lemma map_pmf_rep_eq:
  "measure_pmf (map_pmf f M) = distr (measure_pmf M) (count_space UNIV) f"
  unfolding map_pmf_def bind_pmf.rep_eq comp_def return_pmf.rep_eq
  using bind_return_distr[of M f "count_space UNIV"] by (simp add: comp_def)

lemma map_pmf_id[simp]: "map_pmf id = id"
  by (rule, transfer) (auto simp: emeasure_distr measurable_def intro!: measure_eqI)

lemma map_pmf_ident[simp]: "map_pmf (\<lambda>x. x) = (\<lambda>x. x)"
  using map_pmf_id unfolding id_def .

lemma map_pmf_compose: "map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g"
  by (rule, transfer) (simp add: distr_distr[symmetric, where N="count_space UNIV"] measurable_def)

lemma map_pmf_comp: "map_pmf f (map_pmf g M) = map_pmf (\<lambda>x. f (g x)) M"
  using map_pmf_compose[of f g] by (simp add: comp_def)

lemma map_pmf_cong: "p = q \<Longrightarrow> (\<And>x. x \<in> set_pmf q \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g q"
  unfolding map_pmf_def by (rule bind_pmf_cong) auto

lemma pmf_set_map: "set_pmf \<circ> map_pmf f = (`) f \<circ> set_pmf"
  by (auto simp add: comp_def fun_eq_iff map_pmf_def)

lemma set_map_pmf[simp]: "set_pmf (map_pmf f M) = f`set_pmf M"
  using pmf_set_map[of f] by (auto simp: comp_def fun_eq_iff)

lemma emeasure_map_pmf[simp]: "emeasure (map_pmf f M) X = emeasure M (f -` X)"
  unfolding map_pmf_rep_eq by (subst emeasure_distr) auto

lemma measure_map_pmf[simp]: "measure (map_pmf f M) X = measure M (f -` X)"
using emeasure_map_pmf[of f M X] by(simp add: measure_pmf.emeasure_eq_measure measure_nonneg)

lemma nn_integral_map_pmf[simp]: "(\<integral>\<^sup>+x. f x \<partial>map_pmf g M) = (\<integral>\<^sup>+x. f (g x) \<partial>M)"
  unfolding map_pmf_rep_eq by (intro nn_integral_distr) auto

lemma ennreal_pmf_map: "pmf (map_pmf f p) x = (\<integral>\<^sup>+ y. indicator (f -` {x}) y \<partial>measure_pmf p)"
proof (transfer fixing: f x)
  fix p :: "'b measure"
  presume "prob_space p"
  then interpret prob_space p .
  presume "sets p = UNIV"
  then show "ennreal (measure (distr p (count_space UNIV) f) {x}) = integral\<^sup>N p (indicator (f -` {x}))"
    by(simp add: measure_distr measurable_def emeasure_eq_measure)
qed simp_all

lemma pmf_map: "pmf (map_pmf f p) x = measure p (f -` {x})"
proof (transfer fixing: f x)
  fix p :: "'b measure"
  presume "prob_space p"
  then interpret prob_space p .
  presume "sets p = UNIV"
  then show "measure (distr p (count_space UNIV) f) {x} = measure p (f -` {x})"
    by(simp add: measure_distr measurable_def emeasure_eq_measure)
qed simp_all

lemma nn_integral_pmf: "(\<integral>\<^sup>+ x. pmf p x \<partial>count_space A) = emeasure (measure_pmf p) A"
proof -
  have "(\<integral>\<^sup>+ x. pmf p x \<partial>count_space A) = (\<integral>\<^sup>+ x. pmf p x \<partial>count_space (A \<inter> set_pmf p))"
    by(auto simp add: nn_integral_count_space_indicator indicator_def set_pmf_iff intro: nn_integral_cong)
  also have "\<dots> = emeasure (measure_pmf p) (\<Union>x\<in>A \<inter> set_pmf p. {x})"
    by(subst emeasure_UN_countable)(auto simp add: emeasure_pmf_single disjoint_family_on_def)
  also have "\<dots> = emeasure (measure_pmf p) ((\<Union>x\<in>A \<inter> set_pmf p. {x}) \<union> {x. x \<in> A \<and> x \<notin> set_pmf p})"
    by(rule emeasure_Un_null_set[symmetric])(auto intro: in_null_sets_measure_pmfI)
  also have "\<dots> = emeasure (measure_pmf p) A"
    by(auto intro: arg_cong2[where f=emeasure])
  finally show ?thesis .
qed

lemma integral_map_pmf[simp]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integral\<^sup>L (map_pmf g p) f = integral\<^sup>L p (\<lambda>x. f (g x))"
  by (simp add: integral_distr map_pmf_rep_eq)

lemma integrable_map_pmf_eq [simp]:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integrable (map_pmf f p) g \<longleftrightarrow> integrable (measure_pmf p) (\<lambda>x. g (f x))"              
  by (subst map_pmf_rep_eq, subst integrable_distr_eq) auto

lemma integrable_map_pmf [intro]:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integrable (measure_pmf p) (\<lambda>x. g (f x)) \<Longrightarrow> integrable (map_pmf f p) g"
  by (subst integrable_map_pmf_eq)

lemma pmf_abs_summable [intro]: "pmf p abs_summable_on A"
  by (rule abs_summable_on_subset[OF _ subset_UNIV])
     (auto simp:  abs_summable_on_def integrable_iff_bounded nn_integral_pmf)

lemma measure_pmf_conv_infsetsum: "measure (measure_pmf p) A = infsetsum (pmf p) A"
  unfolding infsetsum_def by (simp add: integral_eq_nn_integral nn_integral_pmf measure_def)

lemma infsetsum_pmf_eq_1:
  assumes "set_pmf p \<subseteq> A"
  shows   "infsetsum (pmf p) A = 1"
proof -
  have "infsetsum (pmf p) A = lebesgue_integral (count_space UNIV) (pmf p)"
    using assms unfolding infsetsum_altdef set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def set_pmf_eq)
  also have "\<dots> = 1"
    by (subst integral_eq_nn_integral) (auto simp: nn_integral_pmf)
  finally show ?thesis .
qed

lemma map_return_pmf [simp]: "map_pmf f (return_pmf x) = return_pmf (f x)"
  by transfer (simp add: distr_return)

lemma map_pmf_const[simp]: "map_pmf (\<lambda>_. c) M = return_pmf c"
  by transfer (auto simp: prob_space.distr_const)

lemma pmf_return [simp]: "pmf (return_pmf x) y = indicator {y} x"
  by transfer (simp add: measure_return)

lemma nn_integral_return_pmf[simp]: "0 \<le> f x \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>return_pmf x) = f x"
  unfolding return_pmf.rep_eq by (intro nn_integral_return) auto

lemma emeasure_return_pmf[simp]: "emeasure (return_pmf x) X = indicator X x"
  unfolding return_pmf.rep_eq by (intro emeasure_return) auto

lemma measure_return_pmf [simp]: "measure_pmf.prob (return_pmf x) A = indicator A x"
proof -
  have "ennreal (measure_pmf.prob (return_pmf x) A) =
          emeasure (measure_pmf (return_pmf x)) A"
    by (simp add: measure_pmf.emeasure_eq_measure)
  also have "\<dots> = ennreal (indicator A x)" by (simp add: ennreal_indicator)
  finally show ?thesis by simp
qed

lemma return_pmf_inj[simp]: "return_pmf x = return_pmf y \<longleftrightarrow> x = y"
  by (metis insertI1 set_return_pmf singletonD)

lemma map_pmf_eq_return_pmf_iff:
  "map_pmf f p = return_pmf x \<longleftrightarrow> (\<forall>y \<in> set_pmf p. f y = x)"
proof
  assume "map_pmf f p = return_pmf x"
  then have "set_pmf (map_pmf f p) = set_pmf (return_pmf x)" by simp
  then show "\<forall>y \<in> set_pmf p. f y = x" by auto
next
  assume "\<forall>y \<in> set_pmf p. f y = x"
  then show "map_pmf f p = return_pmf x"
    unfolding map_pmf_const[symmetric, of _ p] by (intro map_pmf_cong) auto
qed

definition "pair_pmf A B = bind_pmf A (\<lambda>x. bind_pmf B (\<lambda>y. return_pmf (x, y)))"

lemma pmf_pair: "pmf (pair_pmf M N) (a, b) = pmf M a * pmf N b"
  unfolding pair_pmf_def pmf_bind pmf_return
  apply (subst integral_measure_pmf_real[where A="{b}"])
  apply (auto simp: indicator_eq_0_iff)
  apply (subst integral_measure_pmf_real[where A="{a}"])
  apply (auto simp: indicator_eq_0_iff sum_nonneg_eq_0_iff pmf_nonneg)
  done

lemma set_pair_pmf[simp]: "set_pmf (pair_pmf A B) = set_pmf A \<times> set_pmf B"
  unfolding pair_pmf_def set_bind_pmf set_return_pmf by auto

lemma measure_pmf_in_subprob_space[measurable (raw)]:
  "measure_pmf M \<in> space (subprob_algebra (count_space UNIV))"
  by (simp add: space_subprob_algebra) intro_locales

lemma nn_integral_pair_pmf': "(\<integral>\<^sup>+x. f x \<partial>pair_pmf A B) = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. f (a, b) \<partial>B \<partial>A)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>pair_pmf A B) = (\<integral>\<^sup>+x. f x * indicator (A \<times> B) x \<partial>pair_pmf A B)"
    by (auto simp: AE_measure_pmf_iff intro!: nn_integral_cong_AE)
  also have "\<dots> = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. f (a, b) * indicator (A \<times> B) (a, b) \<partial>B \<partial>A)"
    by (simp add: pair_pmf_def)
  also have "\<dots> = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. f (a, b) \<partial>B \<partial>A)"
    by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma bind_pair_pmf:
  assumes M[measurable]: "M \<in> measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) (subprob_algebra N)"
  shows "measure_pmf (pair_pmf A B) \<bind> M = (measure_pmf A \<bind> (\<lambda>x. measure_pmf B \<bind> (\<lambda>y. M (x, y))))"
    (is "?L = ?R")
proof (rule measure_eqI)
  have M'[measurable]: "M \<in> measurable (pair_pmf A B) (subprob_algebra N)"
    using M[THEN measurable_space] by (simp_all add: space_pair_measure)

  note measurable_bind[where N="count_space UNIV", measurable]
  note measure_pmf_in_subprob_space[simp]

  have sets_eq_N: "sets ?L = N"
    by (subst sets_bind[OF sets_kernel[OF M']]) auto
  show "sets ?L = sets ?R"
    using measurable_space[OF M]
    by (simp add: sets_eq_N space_pair_measure space_subprob_algebra)
  fix X assume "X \<in> sets ?L"
  then have X[measurable]: "X \<in> sets N"
    unfolding sets_eq_N .
  then show "emeasure ?L X = emeasure ?R X"
    apply (simp add: emeasure_bind[OF _ M' X])
    apply (simp add: nn_integral_bind[where B="count_space UNIV"] pair_pmf_def measure_pmf_bind[of A]
                     nn_integral_measure_pmf_finite)
    apply (subst emeasure_bind[OF _ _ X])
    apply measurable
    apply (subst emeasure_bind[OF _ _ X])
    apply measurable
    done
qed

lemma map_fst_pair_pmf: "map_pmf fst (pair_pmf A B) = A"
  by (simp add: pair_pmf_def map_pmf_def bind_assoc_pmf bind_return_pmf bind_return_pmf')

lemma map_snd_pair_pmf: "map_pmf snd (pair_pmf A B) = B"
  by (simp add: pair_pmf_def map_pmf_def bind_assoc_pmf bind_return_pmf bind_return_pmf')

lemma nn_integral_pmf':
  "inj_on f A \<Longrightarrow> (\<integral>\<^sup>+x. pmf p (f x) \<partial>count_space A) = emeasure p (f ` A)"
  by (subst nn_integral_bij_count_space[where g=f and B="f`A"])
     (auto simp: bij_betw_def nn_integral_pmf)

lemma pmf_le_0_iff[simp]: "pmf M p \<le> 0 \<longleftrightarrow> pmf M p = 0"
  using pmf_nonneg[of M p] by arith

lemma min_pmf_0[simp]: "min (pmf M p) 0 = 0" "min 0 (pmf M p) = 0"
  using pmf_nonneg[of M p] by arith+

lemma pmf_eq_0_set_pmf: "pmf M p = 0 \<longleftrightarrow> p \<notin> set_pmf M"
  unfolding set_pmf_iff by simp

lemma pmf_map_inj: "inj_on f (set_pmf M) \<Longrightarrow> x \<in> set_pmf M \<Longrightarrow> pmf (map_pmf f M) (f x) = pmf M x"
  by (auto simp: pmf.rep_eq map_pmf_rep_eq measure_distr AE_measure_pmf_iff inj_onD
           intro!: measure_pmf.finite_measure_eq_AE)

lemma pair_return_pmf [simp]: "pair_pmf (return_pmf x) (return_pmf y) = return_pmf (x, y)"
  by (auto simp: pair_pmf_def bind_return_pmf)

lemma pmf_map_inj': "inj f \<Longrightarrow> pmf (map_pmf f M) (f x) = pmf M x"
apply(cases "x \<in> set_pmf M")
 apply(simp add: pmf_map_inj[OF subset_inj_on])
apply(simp add: pmf_eq_0_set_pmf[symmetric])
apply(auto simp add: pmf_eq_0_set_pmf dest: injD)
done

lemma expectation_pair_pmf_fst [simp]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "measure_pmf.expectation (pair_pmf p q) (\<lambda>x. f (fst x)) = measure_pmf.expectation p f"
proof -
  have "measure_pmf.expectation (pair_pmf p q) (\<lambda>x. f (fst x)) = 
          measure_pmf.expectation (map_pmf fst (pair_pmf p q)) f" by simp
  also have "map_pmf fst (pair_pmf p q) = p"
    by (simp add: map_fst_pair_pmf)
  finally show ?thesis .
qed

lemma expectation_pair_pmf_snd [simp]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "measure_pmf.expectation (pair_pmf p q) (\<lambda>x. f (snd x)) = measure_pmf.expectation q f"
proof -
  have "measure_pmf.expectation (pair_pmf p q) (\<lambda>x. f (snd x)) = 
          measure_pmf.expectation (map_pmf snd (pair_pmf p q)) f" by simp
  also have "map_pmf snd (pair_pmf p q) = q"
    by (simp add: map_snd_pair_pmf)
  finally show ?thesis .
qed

lemma pmf_map_outside: "x \<notin> f ` set_pmf M \<Longrightarrow> pmf (map_pmf f M) x = 0"
  unfolding pmf_eq_0_set_pmf by simp

lemma measurable_set_pmf[measurable]: "Measurable.pred (count_space UNIV) (\<lambda>x. x \<in> set_pmf M)"
  by simp


subsection \<open> PMFs as function \<close>

context
  fixes f :: "'a \<Rightarrow> real"
  assumes nonneg: "\<And>x. 0 \<le> f x"
  assumes prob: "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = 1"
begin

lift_definition embed_pmf :: "'a pmf" is "density (count_space UNIV) (ennreal \<circ> f)"
proof (intro conjI)
  have *[simp]: "\<And>x y. ennreal (f y) * indicator {x} y = ennreal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  show "AE x in density (count_space UNIV) (ennreal \<circ> f).
    measure (density (count_space UNIV) (ennreal \<circ> f)) {x} \<noteq> 0"
    by (simp add: AE_density nonneg measure_def emeasure_density max_def)
  show "prob_space (density (count_space UNIV) (ennreal \<circ> f))"
    by standard (simp add: emeasure_density prob)
qed simp

lemma pmf_embed_pmf: "pmf embed_pmf x = f x"
proof transfer
  have *[simp]: "\<And>x y. ennreal (f y) * indicator {x} y = ennreal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  fix x show "measure (density (count_space UNIV) (ennreal \<circ> f)) {x} = f x"
    by transfer (simp add: measure_def emeasure_density nonneg max_def)
qed

lemma set_embed_pmf: "set_pmf embed_pmf = {x. f x \<noteq> 0}"
by(auto simp add: set_pmf_eq pmf_embed_pmf)

end

lemma embed_pmf_transfer:
  "rel_fun (eq_onp (\<lambda>f. (\<forall>x. 0 \<le> f x) \<and> (\<integral>\<^sup>+x. ennreal (f x) \<partial>count_space UNIV) = 1)) pmf_as_measure.cr_pmf (\<lambda>f. density (count_space UNIV) (ennreal \<circ> f)) embed_pmf"
  by (auto simp: rel_fun_def eq_onp_def embed_pmf.transfer)

lemma measure_pmf_eq_density: "measure_pmf p = density (count_space UNIV) (pmf p)"
proof (transfer, elim conjE)
  fix M :: "'a measure" assume [simp]: "sets M = UNIV" and ae: "AE x in M. measure M {x} \<noteq> 0"
  assume "prob_space M" then interpret prob_space M .
  show "M = density (count_space UNIV) (\<lambda>x. ennreal (measure M {x}))"
  proof (rule measure_eqI)
    fix A :: "'a set"
    have "(\<integral>\<^sup>+ x. ennreal (measure M {x}) * indicator A x \<partial>count_space UNIV) =
      (\<integral>\<^sup>+ x. emeasure M {x} * indicator (A \<inter> {x. measure M {x} \<noteq> 0}) x \<partial>count_space UNIV)"
      by (auto intro!: nn_integral_cong simp: emeasure_eq_measure split: split_indicator)
    also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} \<partial>count_space (A \<inter> {x. measure M {x} \<noteq> 0}))"
      by (subst nn_integral_restrict_space[symmetric]) (auto simp: restrict_count_space)
    also have "\<dots> = emeasure M (\<Union>x\<in>(A \<inter> {x. measure M {x} \<noteq> 0}). {x})"
      by (intro emeasure_UN_countable[symmetric] countable_Int2 countable_support)
         (auto simp: disjoint_family_on_def)
    also have "\<dots> = emeasure M A"
      using ae by (intro emeasure_eq_AE) auto
    finally show " emeasure M A = emeasure (density (count_space UNIV) (\<lambda>x. ennreal (measure M {x}))) A"
      using emeasure_space_1 by (simp add: emeasure_density)
  qed simp
qed

lemma td_pmf_embed_pmf:
  "type_definition pmf embed_pmf {f::'a \<Rightarrow> real. (\<forall>x. 0 \<le> f x) \<and> (\<integral>\<^sup>+x. ennreal (f x) \<partial>count_space UNIV) = 1}"
  unfolding type_definition_def
proof safe
  fix p :: "'a pmf"
  have "(\<integral>\<^sup>+ x. 1 \<partial>measure_pmf p) = 1"
    using measure_pmf.emeasure_space_1[of p] by simp
  then show *: "(\<integral>\<^sup>+ x. ennreal (pmf p x) \<partial>count_space UNIV) = 1"
    by (simp add: measure_pmf_eq_density nn_integral_density pmf_nonneg del: nn_integral_const)

  show "embed_pmf (pmf p) = p"
    by (intro measure_pmf_inject[THEN iffD1])
       (simp add: * embed_pmf.rep_eq pmf_nonneg measure_pmf_eq_density[of p] comp_def)
next
  fix f :: "'a \<Rightarrow> real" assume "\<forall>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = 1"
  then show "pmf (embed_pmf f) = f"
    by (auto intro!: pmf_embed_pmf)
qed (rule pmf_nonneg)

end

lemma nn_integral_measure_pmf: "(\<integral>\<^sup>+ x. f x \<partial>measure_pmf p) = \<integral>\<^sup>+ x. ennreal (pmf p x) * f x \<partial>count_space UNIV"
by(simp add: measure_pmf_eq_density nn_integral_density pmf_nonneg)

lemma integral_measure_pmf:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes A: "finite A"
  shows "(\<And>a. a \<in> set_pmf M \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> A) \<Longrightarrow> (LINT x|M. f x) = (\<Sum>a\<in>A. pmf M a *\<^sub>R f a)"
  unfolding measure_pmf_eq_density
  apply (simp add: integral_density)
  apply (subst lebesgue_integral_count_space_finite_support)
  apply (auto intro!: finite_subset[OF _ \<open>finite A\<close>] sum.mono_neutral_left simp: pmf_eq_0_set_pmf)
  done

lemma expectation_return_pmf [simp]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "measure_pmf.expectation (return_pmf x) f = f x"
  by (subst integral_measure_pmf[of "{x}"]) simp_all

lemma pmf_expectation_bind:
  fixes p :: "'a pmf" and f :: "'a \<Rightarrow> 'b pmf"
    and  h :: "'b \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (set_pmf (f x))" "set_pmf p \<subseteq> A"
  shows "measure_pmf.expectation (p \<bind> f) h =
           (\<Sum>a\<in>A. pmf p a *\<^sub>R measure_pmf.expectation (f a) h)"
proof -
  have "measure_pmf.expectation (p \<bind> f) h = (\<Sum>a\<in>(\<Union>x\<in>A. set_pmf (f x)). pmf (p \<bind> f) a *\<^sub>R h a)"
    using assms by (intro integral_measure_pmf) auto
  also have "\<dots> = (\<Sum>x\<in>(\<Union>x\<in>A. set_pmf (f x)). (\<Sum>a\<in>A. (pmf p a * pmf (f a) x) *\<^sub>R h x))"
  proof (intro sum.cong refl, goal_cases)
    case (1 x)
    thus ?case
      by (subst pmf_bind, subst integral_measure_pmf[of A])
         (insert assms, auto simp: scaleR_sum_left)
  qed
  also have "\<dots> = (\<Sum>j\<in>A. pmf p j *\<^sub>R (\<Sum>i\<in>(\<Union>x\<in>A. set_pmf (f x)). pmf (f j) i *\<^sub>R h i))"
    by (subst sum.swap) (simp add: scaleR_sum_right)
  also have "\<dots> = (\<Sum>j\<in>A. pmf p j *\<^sub>R measure_pmf.expectation (f j) h)"
  proof (intro sum.cong refl, goal_cases)
    case (1 x)
    thus ?case
      by (subst integral_measure_pmf[of "(\<Union>x\<in>A. set_pmf (f x))"])
         (insert assms, auto simp: scaleR_sum_left)
  qed
  finally show ?thesis .
qed

lemma continuous_on_LINT_pmf: \<comment> \<open>This is dominated convergence!?\<close>
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f: "\<And>i. i \<in> set_pmf M \<Longrightarrow> continuous_on A (f i)"
    and bnd: "\<And>a i. a \<in> A \<Longrightarrow> i \<in> set_pmf M \<Longrightarrow> norm (f i a) \<le> B"
  shows "continuous_on A (\<lambda>a. LINT i|M. f i a)"
proof cases
  assume "finite M" with f show ?thesis
    using integral_measure_pmf[OF \<open>finite M\<close>]
    by (subst integral_measure_pmf[OF \<open>finite M\<close>])
       (auto intro!: continuous_on_sum continuous_on_scaleR continuous_on_const)
next
  assume "infinite M"
  let ?f = "\<lambda>i x. pmf (map_pmf (to_nat_on M) M) i *\<^sub>R f (from_nat_into M i) x"

  show ?thesis
  proof (rule uniform_limit_theorem)
    show "\<forall>\<^sub>F n in sequentially. continuous_on A (\<lambda>a. \<Sum>i<n. ?f i a)"
      by (intro always_eventually allI continuous_on_sum continuous_on_scaleR continuous_on_const f
                from_nat_into set_pmf_not_empty)
    show "uniform_limit A (\<lambda>n a. \<Sum>i<n. ?f i a) (\<lambda>a. LINT i|M. f i a) sequentially"
    proof (subst uniform_limit_cong[where g="\<lambda>n a. \<Sum>i<n. ?f i a"])
      fix a assume "a \<in> A"
      have 1: "(LINT i|M. f i a) = (LINT i|map_pmf (to_nat_on M) M. f (from_nat_into M i) a)"
        by (auto intro!: integral_cong_AE AE_pmfI)
      have 2: "\<dots> = (LINT i|count_space UNIV. pmf (map_pmf (to_nat_on M) M) i *\<^sub>R f (from_nat_into M i) a)"
        by (simp add: measure_pmf_eq_density integral_density)
      have "(\<lambda>n. ?f n a) sums (LINT i|M. f i a)"
        unfolding 1 2
      proof (intro sums_integral_count_space_nat)
        have A: "integrable M (\<lambda>i. f i a)"
          using \<open>a\<in>A\<close> by (auto intro!: measure_pmf.integrable_const_bound AE_pmfI bnd)
        have "integrable (map_pmf (to_nat_on M) M) (\<lambda>i. f (from_nat_into M i) a)"
          by (auto simp add: map_pmf_rep_eq integrable_distr_eq intro!: AE_pmfI integrable_cong_AE_imp[OF A])
        then show "integrable (count_space UNIV) (\<lambda>n. ?f n a)"
          by (simp add: measure_pmf_eq_density integrable_density)
      qed
      then show "(LINT i|M. f i a) = (\<Sum> n. ?f n a)"
        by (simp add: sums_unique)
    next
      show "uniform_limit A (\<lambda>n a. \<Sum>i<n. ?f i a) (\<lambda>a. (\<Sum> n. ?f n a)) sequentially"
      proof (rule Weierstrass_m_test)
        fix n a assume "a\<in>A"
        then show "norm (?f n a) \<le> pmf (map_pmf (to_nat_on M) M) n * B"
          using bnd by (auto intro!: mult_mono simp: from_nat_into set_pmf_not_empty)
      next
        have "integrable (map_pmf (to_nat_on M) M) (\<lambda>n. B)"
          by auto
        then show "summable (\<lambda>n. pmf (map_pmf (to_nat_on (set_pmf M)) M) n * B)"
          by (fastforce simp add: measure_pmf_eq_density integrable_density integrable_count_space_nat_iff summable_mult2)
      qed
    qed simp
  qed simp
qed

lemma continuous_on_LBINT:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "\<And>b. a \<le> b \<Longrightarrow> set_integrable lborel {a..b} f"
  shows "continuous_on UNIV (\<lambda>b. LBINT x:{a..b}. f x)"
proof (subst set_borel_integral_eq_integral)
  { fix b :: real assume "a \<le> b"
    from f[OF this] have "continuous_on {a..b} (\<lambda>b. integral {a..b} f)"
      by (intro indefinite_integral_continuous_1 set_borel_integral_eq_integral) }
  note * = this

  have "continuous_on (\<Union>b\<in>{a..}. {a <..< b}) (\<lambda>b. integral {a..b} f)"
  proof (intro continuous_on_open_UN)
    show "b \<in> {a..} \<Longrightarrow> continuous_on {a<..<b} (\<lambda>b. integral {a..b} f)" for b
      using *[of b] by (rule continuous_on_subset) auto
  qed simp
  also have "(\<Union>b\<in>{a..}. {a <..< b}) = {a <..}"
    by (auto simp: lt_ex gt_ex less_imp_le) (simp add: Bex_def less_imp_le gt_ex cong: rev_conj_cong)
  finally have "continuous_on {a+1 ..} (\<lambda>b. integral {a..b} f)"
    by (rule continuous_on_subset) auto
  moreover have "continuous_on {a..a+1} (\<lambda>b. integral {a..b} f)"
    by (rule *) simp
  moreover
  have "x \<le> a \<Longrightarrow> {a..x} = (if a = x then {a} else {})" for x
    by auto
  then have "continuous_on {..a} (\<lambda>b. integral {a..b} f)"
    by (subst continuous_on_cong[OF refl, where g="\<lambda>x. 0"]) (auto intro!: continuous_on_const)
  ultimately have "continuous_on ({..a} \<union> {a..a+1} \<union> {a+1 ..}) (\<lambda>b. integral {a..b} f)"
    by (intro continuous_on_closed_Un) auto
  also have "{..a} \<union> {a..a+1} \<union> {a+1 ..} = UNIV"
    by auto
  finally show "continuous_on UNIV (\<lambda>b. integral {a..b} f)"
    by auto
next
  show "set_integrable lborel {a..b} f" for b
    using f by (cases "a \<le> b") auto
qed

locale pmf_as_function
begin

setup_lifting td_pmf_embed_pmf

lemma set_pmf_transfer[transfer_rule]:
  assumes "bi_total A"
  shows "rel_fun (pcr_pmf A) (rel_set A) (\<lambda>f. {x. f x \<noteq> 0}) set_pmf"
  using \<open>bi_total A\<close>
  by (auto simp: pcr_pmf_def cr_pmf_def rel_fun_def rel_set_def bi_total_def Bex_def set_pmf_iff)
     metis+

end

context
begin

interpretation pmf_as_function .

lemma pmf_eqI: "(\<And>i. pmf M i = pmf N i) \<Longrightarrow> M = N"
  by transfer auto

lemma pmf_eq_iff: "M = N \<longleftrightarrow> (\<forall>i. pmf M i = pmf N i)"
  by (auto intro: pmf_eqI)

lemma pmf_neq_exists_less:
  assumes "M \<noteq> N"
  shows   "\<exists>x. pmf M x < pmf N x"
proof (rule ccontr)
  assume "\<not>(\<exists>x. pmf M x < pmf N x)"
  hence ge: "pmf M x \<ge> pmf N x" for x by (auto simp: not_less)
  from assms obtain x where "pmf M x \<noteq> pmf N x" by (auto simp: pmf_eq_iff)
  with ge[of x] have gt: "pmf M x > pmf N x" by simp
  have "1 = measure (measure_pmf M) UNIV" by simp
  also have "\<dots> = measure (measure_pmf N) {x} + measure (measure_pmf N) (UNIV - {x})"
    by (subst measure_pmf.finite_measure_Union [symmetric]) simp_all
  also from gt have "measure (measure_pmf N) {x} < measure (measure_pmf M) {x}"
    by (simp add: measure_pmf_single)
  also have "measure (measure_pmf N) (UNIV - {x}) \<le> measure (measure_pmf M) (UNIV - {x})"
    by (subst (1 2) integral_pmf [symmetric])
       (intro integral_mono integrable_pmf, simp_all add: ge)
  also have "measure (measure_pmf M) {x} + \<dots> = 1"
    by (subst measure_pmf.finite_measure_Union [symmetric]) simp_all
  finally show False by simp_all
qed

lemma bind_commute_pmf: "bind_pmf A (\<lambda>x. bind_pmf B (C x)) = bind_pmf B (\<lambda>y. bind_pmf A (\<lambda>x. C x y))"
  unfolding pmf_eq_iff pmf_bind
proof
  fix i
  interpret B: prob_space "restrict_space B B"
    by (intro prob_space_restrict_space measure_pmf.emeasure_eq_1_AE)
       (auto simp: AE_measure_pmf_iff)
  interpret A: prob_space "restrict_space A A"
    by (intro prob_space_restrict_space measure_pmf.emeasure_eq_1_AE)
       (auto simp: AE_measure_pmf_iff)

  interpret AB: pair_prob_space "restrict_space A A" "restrict_space B B"
    by unfold_locales

  have "(\<integral> x. \<integral> y. pmf (C x y) i \<partial>B \<partial>A) = (\<integral> x. (\<integral> y. pmf (C x y) i \<partial>restrict_space B B) \<partial>A)"
    by (rule Bochner_Integration.integral_cong) (auto intro!: integral_pmf_restrict)
  also have "\<dots> = (\<integral> x. (\<integral> y. pmf (C x y) i \<partial>restrict_space B B) \<partial>restrict_space A A)"
    by (intro integral_pmf_restrict B.borel_measurable_lebesgue_integral measurable_pair_restrict_pmf2
              countable_set_pmf borel_measurable_count_space)
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>restrict_space A A \<partial>restrict_space B B)"
    by (rule AB.Fubini_integral[symmetric])
       (auto intro!: AB.integrable_const_bound[where B=1] measurable_pair_restrict_pmf2
             simp: pmf_nonneg pmf_le_1 measurable_restrict_space1)
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>restrict_space A A \<partial>B)"
    by (intro integral_pmf_restrict[symmetric] A.borel_measurable_lebesgue_integral measurable_pair_restrict_pmf2
              countable_set_pmf borel_measurable_count_space)
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)"
    by (rule Bochner_Integration.integral_cong) (auto intro!: integral_pmf_restrict[symmetric])
  finally show "(\<integral> x. \<integral> y. pmf (C x y) i \<partial>B \<partial>A) = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)" .
qed

lemma pair_map_pmf1: "pair_pmf (map_pmf f A) B = map_pmf (apfst f) (pair_pmf A B)"
proof (safe intro!: pmf_eqI)
  fix a :: "'a" and b :: "'b"
  have [simp]: "\<And>c d. indicator (apfst f -` {(a, b)}) (c, d) = indicator (f -` {a}) c * (indicator {b} d::ennreal)"
    by (auto split: split_indicator)

  have "ennreal (pmf (pair_pmf (map_pmf f A) B) (a, b)) =
         ennreal (pmf (map_pmf (apfst f) (pair_pmf A B)) (a, b))"
    unfolding pmf_pair ennreal_pmf_map
    by (simp add: nn_integral_pair_pmf' max_def emeasure_pmf_single nn_integral_multc pmf_nonneg
                  emeasure_map_pmf[symmetric] ennreal_mult del: emeasure_map_pmf)
  then show "pmf (pair_pmf (map_pmf f A) B) (a, b) = pmf (map_pmf (apfst f) (pair_pmf A B)) (a, b)"
    by (simp add: pmf_nonneg)
qed

lemma pair_map_pmf2: "pair_pmf A (map_pmf f B) = map_pmf (apsnd f) (pair_pmf A B)"
proof (safe intro!: pmf_eqI)
  fix a :: "'a" and b :: "'b"
  have [simp]: "\<And>c d. indicator (apsnd f -` {(a, b)}) (c, d) = indicator {a} c * (indicator (f -` {b}) d::ennreal)"
    by (auto split: split_indicator)

  have "ennreal (pmf (pair_pmf A (map_pmf f B)) (a, b)) =
         ennreal (pmf (map_pmf (apsnd f) (pair_pmf A B)) (a, b))"
    unfolding pmf_pair ennreal_pmf_map
    by (simp add: nn_integral_pair_pmf' max_def emeasure_pmf_single nn_integral_cmult nn_integral_multc pmf_nonneg
                  emeasure_map_pmf[symmetric] ennreal_mult del: emeasure_map_pmf)
  then show "pmf (pair_pmf A (map_pmf f B)) (a, b) = pmf (map_pmf (apsnd f) (pair_pmf A B)) (a, b)"
    by (simp add: pmf_nonneg)
qed

lemma map_pair: "map_pmf (\<lambda>(a, b). (f a, g b)) (pair_pmf A B) = pair_pmf (map_pmf f A) (map_pmf g B)"
  by (simp add: pair_map_pmf2 pair_map_pmf1 map_pmf_comp split_beta')

end

lemma pair_return_pmf1: "pair_pmf (return_pmf x) y = map_pmf (Pair x) y"
by(simp add: pair_pmf_def bind_return_pmf map_pmf_def)

lemma pair_return_pmf2: "pair_pmf x (return_pmf y) = map_pmf (\<lambda>x. (x, y)) x"
by(simp add: pair_pmf_def bind_return_pmf map_pmf_def)

lemma pair_pair_pmf: "pair_pmf (pair_pmf u v) w = map_pmf (\<lambda>(x, (y, z)). ((x, y), z)) (pair_pmf u (pair_pmf v w))"
by(simp add: pair_pmf_def bind_return_pmf map_pmf_def bind_assoc_pmf)

lemma pair_commute_pmf: "pair_pmf x y = map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf y x)"
unfolding pair_pmf_def by(subst bind_commute_pmf)(simp add: map_pmf_def bind_assoc_pmf bind_return_pmf)

lemma set_pmf_subset_singleton: "set_pmf p \<subseteq> {x} \<longleftrightarrow> p = return_pmf x"
proof(intro iffI pmf_eqI)
  fix i
  assume x: "set_pmf p \<subseteq> {x}"
  hence *: "set_pmf p = {x}" using set_pmf_not_empty[of p] by auto
  have "ennreal (pmf p x) = \<integral>\<^sup>+ i. indicator {x} i \<partial>p" by(simp add: emeasure_pmf_single)
  also have "\<dots> = \<integral>\<^sup>+ i. 1 \<partial>p" by(rule nn_integral_cong_AE)(simp add: AE_measure_pmf_iff * )
  also have "\<dots> = 1" by simp
  finally show "pmf p i = pmf (return_pmf x) i" using x
    by(auto split: split_indicator simp add: pmf_eq_0_set_pmf)
qed auto

lemma bind_eq_return_pmf:
  "bind_pmf p f = return_pmf x \<longleftrightarrow> (\<forall>y\<in>set_pmf p. f y = return_pmf x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI strip)
  fix y
  assume y: "y \<in> set_pmf p"
  assume "?lhs"
  hence "set_pmf (bind_pmf p f) = {x}" by simp
  hence "(\<Union>y\<in>set_pmf p. set_pmf (f y)) = {x}" by simp
  hence "set_pmf (f y) \<subseteq> {x}" using y by auto
  thus "f y = return_pmf x" by(simp add: set_pmf_subset_singleton)
next
  assume *: ?rhs
  show ?lhs
  proof(rule pmf_eqI)
    fix i
    have "ennreal (pmf (bind_pmf p f) i) = \<integral>\<^sup>+ y. ennreal (pmf (f y) i) \<partial>p"
      by (simp add: ennreal_pmf_bind)
    also have "\<dots> = \<integral>\<^sup>+ y. ennreal (pmf (return_pmf x) i) \<partial>p"
      by(rule nn_integral_cong_AE)(simp add: AE_measure_pmf_iff * )
    also have "\<dots> = ennreal (pmf (return_pmf x) i)"
      by simp
    finally show "pmf (bind_pmf p f) i = pmf (return_pmf x) i"
      by (simp add: pmf_nonneg)
  qed
qed

lemma pmf_False_conv_True: "pmf p False = 1 - pmf p True"
proof -
  have "pmf p False + pmf p True = measure p {False} + measure p {True}"
    by(simp add: measure_pmf_single)
  also have "\<dots> = measure p ({False} \<union> {True})"
    by(subst measure_pmf.finite_measure_Union) simp_all
  also have "{False} \<union> {True} = space p" by auto
  finally show ?thesis by simp
qed

lemma pmf_True_conv_False: "pmf p True = 1 - pmf p False"
by(simp add: pmf_False_conv_True)

subsection \<open> Conditional Probabilities \<close>

lemma measure_pmf_zero_iff: "measure (measure_pmf p) s = 0 \<longleftrightarrow> set_pmf p \<inter> s = {}"
  by (subst measure_pmf.prob_eq_0) (auto simp: AE_measure_pmf_iff)

context
  fixes p :: "'a pmf" and s :: "'a set"
  assumes not_empty: "set_pmf p \<inter> s \<noteq> {}"
begin

interpretation pmf_as_measure .

lemma emeasure_measure_pmf_not_zero: "emeasure (measure_pmf p) s \<noteq> 0"
proof
  assume "emeasure (measure_pmf p) s = 0"
  then have "AE x in measure_pmf p. x \<notin> s"
    by (rule AE_I[rotated]) auto
  with not_empty show False
    by (auto simp: AE_measure_pmf_iff)
qed

lemma measure_measure_pmf_not_zero: "measure (measure_pmf p) s \<noteq> 0"
  using emeasure_measure_pmf_not_zero by (simp add: measure_pmf.emeasure_eq_measure measure_nonneg)

lift_definition cond_pmf :: "'a pmf" is
  "uniform_measure (measure_pmf p) s"
proof (intro conjI)
  show "prob_space (uniform_measure (measure_pmf p) s)"
    by (intro prob_space_uniform_measure) (auto simp: emeasure_measure_pmf_not_zero)
  show "AE x in uniform_measure (measure_pmf p) s. measure (uniform_measure (measure_pmf p) s) {x} \<noteq> 0"
    by (simp add: emeasure_measure_pmf_not_zero measure_measure_pmf_not_zero AE_uniform_measure
                  AE_measure_pmf_iff set_pmf.rep_eq less_top[symmetric])
qed simp

lemma pmf_cond: "pmf cond_pmf x = (if x \<in> s then pmf p x / measure p s else 0)"
  by transfer (simp add: emeasure_measure_pmf_not_zero pmf.rep_eq)

lemma set_cond_pmf[simp]: "set_pmf cond_pmf = set_pmf p \<inter> s"
  by (auto simp add: set_pmf_iff pmf_cond measure_measure_pmf_not_zero split: if_split_asm)

end

lemma measure_pmf_posI: "x \<in> set_pmf p \<Longrightarrow> x \<in> A \<Longrightarrow> measure_pmf.prob p A > 0"
  using measure_measure_pmf_not_zero[of p A] by (subst zero_less_measure_iff) blast

lemma cond_map_pmf:
  assumes "set_pmf p \<inter> f -` s \<noteq> {}"
  shows "cond_pmf (map_pmf f p) s = map_pmf f (cond_pmf p (f -` s))"
proof -
  have *: "set_pmf (map_pmf f p) \<inter> s \<noteq> {}"
    using assms by auto
  { fix x
    have "ennreal (pmf (map_pmf f (cond_pmf p (f -` s))) x) =
      emeasure p (f -` s \<inter> f -` {x}) / emeasure p (f -` s)"
      unfolding ennreal_pmf_map cond_pmf.rep_eq[OF assms] by (simp add: nn_integral_uniform_measure)
    also have "f -` s \<inter> f -` {x} = (if x \<in> s then f -` {x} else {})"
      by auto
    also have "emeasure p (if x \<in> s then f -` {x} else {}) / emeasure p (f -` s) =
      ennreal (pmf (cond_pmf (map_pmf f p) s) x)"
      using measure_measure_pmf_not_zero[OF *]
      by (simp add: pmf_cond[OF *] ennreal_pmf_map measure_pmf.emeasure_eq_measure
                    divide_ennreal pmf_nonneg measure_nonneg zero_less_measure_iff pmf_map)
    finally have "ennreal (pmf (cond_pmf (map_pmf f p) s) x) = ennreal (pmf (map_pmf f (cond_pmf p (f -` s))) x)"
      by simp }
  then show ?thesis
    by (intro pmf_eqI) (simp add: pmf_nonneg)
qed

lemma bind_cond_pmf_cancel:
  assumes [simp]: "\<And>x. x \<in> set_pmf p \<Longrightarrow> set_pmf q \<inter> {y. R x y} \<noteq> {}"
  assumes [simp]: "\<And>y. y \<in> set_pmf q \<Longrightarrow> set_pmf p \<inter> {x. R x y} \<noteq> {}"
  assumes [simp]: "\<And>x y. x \<in> set_pmf p \<Longrightarrow> y \<in> set_pmf q \<Longrightarrow> R x y \<Longrightarrow> measure q {y. R x y} = measure p {x. R x y}"
  shows "bind_pmf p (\<lambda>x. cond_pmf q {y. R x y}) = q"
proof (rule pmf_eqI)
  fix i
  have "ennreal (pmf (bind_pmf p (\<lambda>x. cond_pmf q {y. R x y})) i) =
    (\<integral>\<^sup>+x. ennreal (pmf q i / measure p {x. R x i}) * ennreal (indicator {x. R x i} x) \<partial>p)"
    by (auto simp add: ennreal_pmf_bind AE_measure_pmf_iff pmf_cond pmf_eq_0_set_pmf pmf_nonneg measure_nonneg
             intro!: nn_integral_cong_AE)
  also have "\<dots> = (pmf q i * measure p {x. R x i}) / measure p {x. R x i}"
    by (simp add: pmf_nonneg measure_nonneg zero_ennreal_def[symmetric] ennreal_indicator
                  nn_integral_cmult measure_pmf.emeasure_eq_measure ennreal_mult[symmetric])
  also have "\<dots> = pmf q i"
    by (cases "pmf q i = 0")
       (simp_all add: pmf_eq_0_set_pmf measure_measure_pmf_not_zero pmf_nonneg)
  finally show "pmf (bind_pmf p (\<lambda>x. cond_pmf q {y. R x y})) i = pmf q i"
    by (simp add: pmf_nonneg)
qed

subsection \<open> Relator \<close>

inductive rel_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf \<Rightarrow> bool"
for R p q
where
  "\<lbrakk> \<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y;
     map_pmf fst pq = p; map_pmf snd pq = q \<rbrakk>
  \<Longrightarrow> rel_pmf R p q"

lemma rel_pmfI:
  assumes R: "rel_set R (set_pmf p) (set_pmf q)"
  assumes eq: "\<And>x y. x \<in> set_pmf p \<Longrightarrow> y \<in> set_pmf q \<Longrightarrow> R x y \<Longrightarrow>
    measure p {x. R x y} = measure q {y. R x y}"
  shows "rel_pmf R p q"
proof
  let ?pq = "bind_pmf p (\<lambda>x. bind_pmf (cond_pmf q {y. R x y}) (\<lambda>y. return_pmf (x, y)))"
  have "\<And>x. x \<in> set_pmf p \<Longrightarrow> set_pmf q \<inter> {y. R x y} \<noteq> {}"
    using R by (auto simp: rel_set_def)
  then show "\<And>x y. (x, y) \<in> set_pmf ?pq \<Longrightarrow> R x y"
    by auto
  show "map_pmf fst ?pq = p"
    by (simp add: map_bind_pmf bind_return_pmf')

  show "map_pmf snd ?pq = q"
    using R eq
    apply (simp add: bind_cond_pmf_cancel map_bind_pmf bind_return_pmf')
    apply (rule bind_cond_pmf_cancel)
    apply (auto simp: rel_set_def)
    done
qed

lemma rel_pmf_imp_rel_set: "rel_pmf R p q \<Longrightarrow> rel_set R (set_pmf p) (set_pmf q)"
  by (force simp add: rel_pmf.simps rel_set_def)

lemma rel_pmfD_measure:
  assumes rel_R: "rel_pmf R p q" and R: "\<And>a b. R a b \<Longrightarrow> R a y \<longleftrightarrow> R x b"
  assumes "x \<in> set_pmf p" "y \<in> set_pmf q"
  shows "measure p {x. R x y} = measure q {y. R x y}"
proof -
  from rel_R obtain pq where pq: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y"
    and eq: "p = map_pmf fst pq" "q = map_pmf snd pq"
    by (auto elim: rel_pmf.cases)
  have "measure p {x. R x y} = measure pq {x. R (fst x) y}"
    by (simp add: eq map_pmf_rep_eq measure_distr)
  also have "\<dots> = measure pq {y. R x (snd y)}"
    by (intro measure_pmf.finite_measure_eq_AE)
       (auto simp: AE_measure_pmf_iff R dest!: pq)
  also have "\<dots> = measure q {y. R x y}"
    by (simp add: eq map_pmf_rep_eq measure_distr)
  finally show "measure p {x. R x y} = measure q {y. R x y}" .
qed

lemma rel_pmf_measureD:
  assumes "rel_pmf R p q"
  shows "measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}" (is "?lhs \<le> ?rhs")
using assms
proof cases
  fix pq
  assume R: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y"
    and p[symmetric]: "map_pmf fst pq = p"
    and q[symmetric]: "map_pmf snd pq = q"
  have "?lhs = measure (measure_pmf pq) (fst -` A)" by(simp add: p)
  also have "\<dots> \<le> measure (measure_pmf pq) {y. \<exists>x\<in>A. R x (snd y)}"
    by(rule measure_pmf.finite_measure_mono_AE)(auto 4 3 simp add: AE_measure_pmf_iff dest: R)
  also have "\<dots> = ?rhs" by(simp add: q)
  finally show ?thesis .
qed

lemma rel_pmf_iff_measure:
  assumes "symp R" "transp R"
  shows "rel_pmf R p q \<longleftrightarrow>
    rel_set R (set_pmf p) (set_pmf q) \<and>
    (\<forall>x\<in>set_pmf p. \<forall>y\<in>set_pmf q. R x y \<longrightarrow> measure p {x. R x y} = measure q {y. R x y})"
  by (safe intro!: rel_pmf_imp_rel_set rel_pmfI)
     (auto intro!: rel_pmfD_measure dest: sympD[OF \<open>symp R\<close>] transpD[OF \<open>transp R\<close>])

lemma quotient_rel_set_disjoint:
  "equivp R \<Longrightarrow> C \<in> UNIV // {(x, y). R x y} \<Longrightarrow> rel_set R A B \<Longrightarrow> A \<inter> C = {} \<longleftrightarrow> B \<inter> C = {}"
  using in_quotient_imp_closed[of UNIV "{(x, y). R x y}" C]
  by (auto 0 0 simp: equivp_equiv rel_set_def set_eq_iff elim: equivpE)
     (blast dest: equivp_symp)+

lemma quotientD: "equiv X R \<Longrightarrow> A \<in> X // R \<Longrightarrow> x \<in> A \<Longrightarrow> A = R `` {x}"
  by (metis Image_singleton_iff equiv_class_eq_iff quotientE)

lemma rel_pmf_iff_equivp:
  assumes "equivp R"
  shows "rel_pmf R p q \<longleftrightarrow> (\<forall>C\<in>UNIV // {(x, y). R x y}. measure p C = measure q C)"
    (is "_ \<longleftrightarrow>   (\<forall>C\<in>_//?R. _)")
proof (subst rel_pmf_iff_measure, safe)
  show "symp R" "transp R"
    using assms by (auto simp: equivp_reflp_symp_transp)
next
  fix C assume C: "C \<in> UNIV // ?R" and R: "rel_set R (set_pmf p) (set_pmf q)"
  assume eq: "\<forall>x\<in>set_pmf p. \<forall>y\<in>set_pmf q. R x y \<longrightarrow> measure p {x. R x y} = measure q {y. R x y}"

  show "measure p C = measure q C"
  proof (cases "p \<inter> C = {}")
    case True
    then have "q \<inter> C = {}"
      using quotient_rel_set_disjoint[OF assms C R] by simp
    with True show ?thesis
      unfolding measure_pmf_zero_iff[symmetric] by simp
  next
    case False
    then have "q \<inter> C \<noteq> {}"
      using quotient_rel_set_disjoint[OF assms C R] by simp
    with False obtain x y where in_set: "x \<in> set_pmf p" "y \<in> set_pmf q" and in_C: "x \<in> C" "y \<in> C"
      by auto
    then have "R x y"
      using in_quotient_imp_in_rel[of UNIV ?R C x y] C assms
      by (simp add: equivp_equiv)
    with in_set eq have "measure p {x. R x y} = measure q {y. R x y}"
      by auto
    moreover have "{y. R x y} = C"
      using assms \<open>x \<in> C\<close> C quotientD[of UNIV ?R C x] by (simp add: equivp_equiv)
    moreover have "{x. R x y} = C"
      using assms \<open>y \<in> C\<close> C quotientD[of UNIV "?R" C y] sympD[of R]
      by (auto simp add: equivp_equiv elim: equivpE)
    ultimately show ?thesis
      by auto
  qed
next
  assume eq: "\<forall>C\<in>UNIV // ?R. measure p C = measure q C"
  show "rel_set R (set_pmf p) (set_pmf q)"
    unfolding rel_set_def
  proof safe
    fix x assume x: "x \<in> set_pmf p"
    have "{y. R x y} \<in> UNIV // ?R"
      by (auto simp: quotient_def)
    with eq have *: "measure q {y. R x y} = measure p {y. R x y}"
      by auto
    have "measure q {y. R x y} \<noteq> 0"
      using x assms unfolding * by (auto simp: measure_pmf_zero_iff set_eq_iff dest: equivp_reflp)
    then show "\<exists>y\<in>set_pmf q. R x y"
      unfolding measure_pmf_zero_iff by auto
  next
    fix y assume y: "y \<in> set_pmf q"
    have "{x. R x y} \<in> UNIV // ?R"
      using assms by (auto simp: quotient_def dest: equivp_symp)
    with eq have *: "measure p {x. R x y} = measure q {x. R x y}"
      by auto
    have "measure p {x. R x y} \<noteq> 0"
      using y assms unfolding * by (auto simp: measure_pmf_zero_iff set_eq_iff dest: equivp_reflp)
    then show "\<exists>x\<in>set_pmf p. R x y"
      unfolding measure_pmf_zero_iff by auto
  qed

  fix x y assume "x \<in> set_pmf p" "y \<in> set_pmf q" "R x y"
  have "{y. R x y} \<in> UNIV // ?R" "{x. R x y} = {y. R x y}"
    using assms \<open>R x y\<close> by (auto simp: quotient_def dest: equivp_symp equivp_transp)
  with eq show "measure p {x. R x y} = measure q {y. R x y}"
    by auto
qed

bnf pmf: "'a pmf" map: map_pmf sets: set_pmf bd : "natLeq" rel: rel_pmf
proof -
  show "map_pmf id = id" by (rule map_pmf_id)
  show "\<And>f g. map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g" by (rule map_pmf_compose)
  show "\<And>f g::'a \<Rightarrow> 'b. \<And>p. (\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g p"
    by (intro map_pmf_cong refl)

  show "\<And>f::'a \<Rightarrow> 'b. set_pmf \<circ> map_pmf f = (`) f \<circ> set_pmf"
    by (rule pmf_set_map)

  show "(card_of (set_pmf p), natLeq) \<in> ordLeq" for p :: "'s pmf"
  proof -
    have "(card_of (set_pmf p), card_of (UNIV :: nat set)) \<in> ordLeq"
      by (rule card_of_ordLeqI[where f="to_nat_on (set_pmf p)"])
         (auto intro: countable_set_pmf)
    also have "(card_of (UNIV :: nat set), natLeq) \<in> ordLeq"
      by (metis Field_natLeq card_of_least natLeq_Well_order)
    finally show ?thesis .
  qed

  show "\<And>R. rel_pmf R = (\<lambda>x y. \<exists>z. set_pmf z \<subseteq> {(x, y). R x y} \<and>
    map_pmf fst z = x \<and> map_pmf snd z = y)"
     by (auto simp add: fun_eq_iff rel_pmf.simps)

  show "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
    for R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  proof -
    { fix p q r
      assume pq: "rel_pmf R p q"
        and qr:"rel_pmf S q r"
      from pq obtain pq where pq: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y"
        and p: "p = map_pmf fst pq" and q: "q = map_pmf snd pq" by cases auto
      from qr obtain qr where qr: "\<And>y z. (y, z) \<in> set_pmf qr \<Longrightarrow> S y z"
        and q': "q = map_pmf fst qr" and r: "r = map_pmf snd qr" by cases auto

      define pr where "pr =
        bind_pmf pq (\<lambda>xy. bind_pmf (cond_pmf qr {yz. fst yz = snd xy})
          (\<lambda>yz. return_pmf (fst xy, snd yz)))"
      have pr_welldefined: "\<And>y. y \<in> q \<Longrightarrow> qr \<inter> {yz. fst yz = y} \<noteq> {}"
        by (force simp: q')

      have "rel_pmf (R OO S) p r"
      proof (rule rel_pmf.intros)
        fix x z assume "(x, z) \<in> pr"
        then have "\<exists>y. (x, y) \<in> pq \<and> (y, z) \<in> qr"
          by (auto simp: q pr_welldefined pr_def split_beta)
        with pq qr show "(R OO S) x z"
          by blast
      next
        have "map_pmf snd pr = map_pmf snd (bind_pmf q (\<lambda>y. cond_pmf qr {yz. fst yz = y}))"
          by (simp add: pr_def q split_beta bind_map_pmf map_pmf_def[symmetric] map_bind_pmf map_pmf_comp)
        then show "map_pmf snd pr = r"
          unfolding r q' bind_map_pmf by (subst (asm) bind_cond_pmf_cancel) (auto simp: eq_commute)
      qed (simp add: pr_def map_bind_pmf split_beta map_pmf_def[symmetric] p map_pmf_comp)
    }
    then show ?thesis
      by(auto simp add: le_fun_def)
  qed
qed (fact natLeq_card_order natLeq_cinfinite)+

lemma map_pmf_idI: "(\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = x) \<Longrightarrow> map_pmf f p = p"
by(simp cong: pmf.map_cong)

lemma rel_pmf_conj[simp]:
  "rel_pmf (\<lambda>x y. P \<and> Q x y) x y \<longleftrightarrow> P \<and> rel_pmf Q x y"
  "rel_pmf (\<lambda>x y. Q x y \<and> P) x y \<longleftrightarrow> P \<and> rel_pmf Q x y"
  using set_pmf_not_empty by (fastforce simp: pmf.in_rel subset_eq)+

lemma rel_pmf_top[simp]: "rel_pmf top = top"
  by (auto simp: pmf.in_rel[abs_def] fun_eq_iff map_fst_pair_pmf map_snd_pair_pmf
           intro: exI[of _ "pair_pmf x y" for x y])

lemma rel_pmf_return_pmf1: "rel_pmf R (return_pmf x) M \<longleftrightarrow> (\<forall>a\<in>M. R x a)"
proof safe
  fix a assume "a \<in> M" "rel_pmf R (return_pmf x) M"
  then obtain pq where *: "\<And>a b. (a, b) \<in> set_pmf pq \<Longrightarrow> R a b"
    and eq: "return_pmf x = map_pmf fst pq" "M = map_pmf snd pq"
    by (force elim: rel_pmf.cases)
  moreover have "set_pmf (return_pmf x) = {x}"
    by simp
  with \<open>a \<in> M\<close> have "(x, a) \<in> pq"
    by (force simp: eq)
  with * show "R x a"
    by auto
qed (auto intro!: rel_pmf.intros[where pq="pair_pmf (return_pmf x) M"]
          simp: map_fst_pair_pmf map_snd_pair_pmf)

lemma rel_pmf_return_pmf2: "rel_pmf R M (return_pmf x) \<longleftrightarrow> (\<forall>a\<in>M. R a x)"
  by (subst pmf.rel_flip[symmetric]) (simp add: rel_pmf_return_pmf1)

lemma rel_return_pmf[simp]: "rel_pmf R (return_pmf x1) (return_pmf x2) = R x1 x2"
  unfolding rel_pmf_return_pmf2 set_return_pmf by simp

lemma rel_pmf_False[simp]: "rel_pmf (\<lambda>x y. False) x y = False"
  unfolding pmf.in_rel fun_eq_iff using set_pmf_not_empty by fastforce

lemma rel_pmf_rel_prod:
  "rel_pmf (rel_prod R S) (pair_pmf A A') (pair_pmf B B') \<longleftrightarrow> rel_pmf R A B \<and> rel_pmf S A' B'"
proof safe
  assume "rel_pmf (rel_prod R S) (pair_pmf A A') (pair_pmf B B')"
  then obtain pq where pq: "\<And>a b c d. ((a, c), (b, d)) \<in> set_pmf pq \<Longrightarrow> R a b \<and> S c d"
    and eq: "map_pmf fst pq = pair_pmf A A'" "map_pmf snd pq = pair_pmf B B'"
    by (force elim: rel_pmf.cases)
  show "rel_pmf R A B"
  proof (rule rel_pmf.intros)
    let ?f = "\<lambda>(a, b). (fst a, fst b)"
    have [simp]: "(\<lambda>x. fst (?f x)) = fst o fst" "(\<lambda>x. snd (?f x)) = fst o snd"
      by auto

    show "map_pmf fst (map_pmf ?f pq) = A"
      by (simp add: map_pmf_comp pmf.map_comp[symmetric] eq map_fst_pair_pmf)
    show "map_pmf snd (map_pmf ?f pq) = B"
      by (simp add: map_pmf_comp pmf.map_comp[symmetric] eq map_fst_pair_pmf)

    fix a b assume "(a, b) \<in> set_pmf (map_pmf ?f pq)"
    then obtain c d where "((a, c), (b, d)) \<in> set_pmf pq"
      by auto
    from pq[OF this] show "R a b" ..
  qed
  show "rel_pmf S A' B'"
  proof (rule rel_pmf.intros)
    let ?f = "\<lambda>(a, b). (snd a, snd b)"
    have [simp]: "(\<lambda>x. fst (?f x)) = snd o fst" "(\<lambda>x. snd (?f x)) = snd o snd"
      by auto

    show "map_pmf fst (map_pmf ?f pq) = A'"
      by (simp add: map_pmf_comp pmf.map_comp[symmetric] eq map_snd_pair_pmf)
    show "map_pmf snd (map_pmf ?f pq) = B'"
      by (simp add: map_pmf_comp pmf.map_comp[symmetric] eq map_snd_pair_pmf)

    fix c d assume "(c, d) \<in> set_pmf (map_pmf ?f pq)"
    then obtain a b where "((a, c), (b, d)) \<in> set_pmf pq"
      by auto
    from pq[OF this] show "S c d" ..
  qed
next
  assume "rel_pmf R A B" "rel_pmf S A' B'"
  then obtain Rpq Spq
    where Rpq: "\<And>a b. (a, b) \<in> set_pmf Rpq \<Longrightarrow> R a b"
        "map_pmf fst Rpq = A" "map_pmf snd Rpq = B"
      and Spq: "\<And>a b. (a, b) \<in> set_pmf Spq \<Longrightarrow> S a b"
        "map_pmf fst Spq = A'" "map_pmf snd Spq = B'"
    by (force elim: rel_pmf.cases)

  let ?f = "(\<lambda>((a, c), (b, d)). ((a, b), (c, d)))"
  let ?pq = "map_pmf ?f (pair_pmf Rpq Spq)"
  have [simp]: "(\<lambda>x. fst (?f x)) = (\<lambda>(a, b). (fst a, fst b))" "(\<lambda>x. snd (?f x)) = (\<lambda>(a, b). (snd a, snd b))"
    by auto

  show "rel_pmf (rel_prod R S) (pair_pmf A A') (pair_pmf B B')"
    by (rule rel_pmf.intros[where pq="?pq"])
       (auto simp: map_snd_pair_pmf map_fst_pair_pmf map_pmf_comp Rpq Spq
                   map_pair)
qed

lemma rel_pmf_reflI:
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> P x x"
  shows "rel_pmf P p p"
  by (rule rel_pmf.intros[where pq="map_pmf (\<lambda>x. (x, x)) p"])
     (auto simp add: pmf.map_comp o_def assms)

lemma rel_pmf_bij_betw:
  assumes f: "bij_betw f (set_pmf p) (set_pmf q)"
  and eq: "\<And>x. x \<in> set_pmf p \<Longrightarrow> pmf p x = pmf q (f x)"
  shows "rel_pmf (\<lambda>x y. f x = y) p q"
proof(rule rel_pmf.intros)
  let ?pq = "map_pmf (\<lambda>x. (x, f x)) p"
  show "map_pmf fst ?pq = p" by(simp add: pmf.map_comp o_def)

  have "map_pmf f p = q"
  proof(rule pmf_eqI)
    fix i
    show "pmf (map_pmf f p) i = pmf q i"
    proof(cases "i \<in> set_pmf q")
      case True
      with f obtain j where "i = f j" "j \<in> set_pmf p"
        by(auto simp add: bij_betw_def image_iff)
      thus ?thesis using f by(simp add: bij_betw_def pmf_map_inj eq)
    next
      case False thus ?thesis
        by(subst pmf_map_outside)(auto simp add: set_pmf_iff eq[symmetric])
    qed
  qed
  then show "map_pmf snd ?pq = q" by(simp add: pmf.map_comp o_def)
qed auto

context
begin

interpretation pmf_as_measure .

definition "join_pmf M = bind_pmf M (\<lambda>x. x)"

lemma bind_eq_join_pmf: "bind_pmf M f = join_pmf (map_pmf f M)"
  unfolding join_pmf_def bind_map_pmf ..

lemma join_eq_bind_pmf: "join_pmf M = bind_pmf M id"
  by (simp add: join_pmf_def id_def)

lemma pmf_join: "pmf (join_pmf N) i = (\<integral>M. pmf M i \<partial>measure_pmf N)"
  unfolding join_pmf_def pmf_bind ..

lemma ennreal_pmf_join: "ennreal (pmf (join_pmf N) i) = (\<integral>\<^sup>+M. pmf M i \<partial>measure_pmf N)"
  unfolding join_pmf_def ennreal_pmf_bind ..

lemma set_pmf_join_pmf[simp]: "set_pmf (join_pmf f) = (\<Union>p\<in>set_pmf f. set_pmf p)"
  by (simp add: join_pmf_def)

lemma join_return_pmf: "join_pmf (return_pmf M) = M"
  by (simp add: integral_return pmf_eq_iff pmf_join return_pmf.rep_eq)

lemma map_join_pmf: "map_pmf f (join_pmf AA) = join_pmf (map_pmf (map_pmf f) AA)"
  by (simp add: join_pmf_def map_pmf_def bind_assoc_pmf bind_return_pmf)

lemma join_map_return_pmf: "join_pmf (map_pmf return_pmf A) = A"
  by (simp add: join_pmf_def map_pmf_def bind_assoc_pmf bind_return_pmf bind_return_pmf')

end

lemma rel_pmf_joinI:
  assumes "rel_pmf (rel_pmf P) p q"
  shows "rel_pmf P (join_pmf p) (join_pmf q)"
proof -
  from assms obtain pq where p: "p = map_pmf fst pq"
    and q: "q = map_pmf snd pq"
    and P: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> rel_pmf P x y"
    by cases auto
  from P obtain PQ
    where PQ: "\<And>x y a b. \<lbrakk> (x, y) \<in> set_pmf pq; (a, b) \<in> set_pmf (PQ x y) \<rbrakk> \<Longrightarrow> P a b"
    and x: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> map_pmf fst (PQ x y) = x"
    and y: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> map_pmf snd (PQ x y) = y"
    by(metis rel_pmf.simps)

  let ?r = "bind_pmf pq (\<lambda>(x, y). PQ x y)"
  have "\<And>a b. (a, b) \<in> set_pmf ?r \<Longrightarrow> P a b" by (auto intro: PQ)
  moreover have "map_pmf fst ?r = join_pmf p" "map_pmf snd ?r = join_pmf q"
    by (simp_all add: p q x y join_pmf_def map_bind_pmf bind_map_pmf split_def cong: bind_pmf_cong)
  ultimately show ?thesis ..
qed

lemma rel_pmf_bindI:
  assumes pq: "rel_pmf R p q"
  and fg: "\<And>x y. R x y \<Longrightarrow> rel_pmf P (f x) (g y)"
  shows "rel_pmf P (bind_pmf p f) (bind_pmf q g)"
  unfolding bind_eq_join_pmf
  by (rule rel_pmf_joinI)
     (auto simp add: pmf.rel_map intro: pmf.rel_mono[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp, OF _ pq] fg)

text \<open>
  Proof that \<^const>\<open>rel_pmf\<close> preserves orders.
  Antisymmetry proof follows Thm. 1 in N. Saheb-Djahromi, Cpo's of measures for nondeterminism,
  Theoretical Computer Science 12(1):19--37, 1980,
  \<^url>\<open>https://doi.org/10.1016/0304-3975(80)90003-1\<close>
\<close>

lemma
  assumes *: "rel_pmf R p q"
  and refl: "reflp R" and trans: "transp R"
  shows measure_Ici: "measure p {y. R x y} \<le> measure q {y. R x y}" (is ?thesis1)
  and measure_Ioi: "measure p {y. R x y \<and> \<not> R y x} \<le> measure q {y. R x y \<and> \<not> R y x}" (is ?thesis2)
proof -
  from * obtain pq
    where pq: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y"
    and p: "p = map_pmf fst pq"
    and q: "q = map_pmf snd pq"
    by cases auto
  show ?thesis1 ?thesis2 unfolding p q map_pmf_rep_eq using refl trans
    by(auto 4 3 simp add: measure_distr reflpD AE_measure_pmf_iff intro!: measure_pmf.finite_measure_mono_AE dest!: pq elim: transpE)
qed

lemma rel_pmf_inf:
  fixes p q :: "'a pmf"
  assumes 1: "rel_pmf R p q"
  assumes 2: "rel_pmf R q p"
  and refl: "reflp R" and trans: "transp R"
  shows "rel_pmf (inf R R\<inverse>\<inverse>) p q"
proof (subst rel_pmf_iff_equivp, safe)
  show "equivp (inf R R\<inverse>\<inverse>)"
    using trans refl by (auto simp: equivp_reflp_symp_transp intro: sympI transpI reflpI dest: transpD reflpD)

  fix C assume "C \<in> UNIV // {(x, y). inf R R\<inverse>\<inverse> x y}"
  then obtain x where C: "C = {y. R x y \<and> R y x}"
    by (auto elim: quotientE)

  let ?R = "\<lambda>x y. R x y \<and> R y x"
  let ?\<mu>R = "\<lambda>y. measure q {x. ?R x y}"
  have "measure p {y. ?R x y} = measure p ({y. R x y} - {y. R x y \<and> \<not> R y x})"
    by(auto intro!: arg_cong[where f="measure p"])
  also have "\<dots> = measure p {y. R x y} - measure p {y. R x y \<and> \<not> R y x}"
    by (rule measure_pmf.finite_measure_Diff) auto
  also have "measure p {y. R x y \<and> \<not> R y x} = measure q {y. R x y \<and> \<not> R y x}"
    using 1 2 refl trans by(auto intro!: Orderings.antisym measure_Ioi)
  also have "measure p {y. R x y} = measure q {y. R x y}"
    using 1 2 refl trans by(auto intro!: Orderings.antisym measure_Ici)
  also have "measure q {y. R x y} - measure q {y. R x y \<and> \<not> R y x} =
    measure q ({y. R x y} - {y. R x y \<and> \<not> R y x})"
    by(rule measure_pmf.finite_measure_Diff[symmetric]) auto
  also have "\<dots> = ?\<mu>R x"
    by(auto intro!: arg_cong[where f="measure q"])
  finally show "measure p C = measure q C"
    by (simp add: C conj_commute)
qed

lemma rel_pmf_antisym:
  fixes p q :: "'a pmf"
  assumes 1: "rel_pmf R p q"
  assumes 2: "rel_pmf R q p"
  and refl: "reflp R" and trans: "transp R" and antisym: "antisymp R"
  shows "p = q"
proof -
  from 1 2 refl trans have "rel_pmf (inf R R\<inverse>\<inverse>) p q" by(rule rel_pmf_inf)
  also have "inf R R\<inverse>\<inverse> = (=)"
    using refl antisym by (auto intro!: ext simp add: reflpD dest: antisympD)
  finally show ?thesis unfolding pmf.rel_eq .
qed

lemma reflp_rel_pmf: "reflp R \<Longrightarrow> reflp (rel_pmf R)"
  by (fact pmf.rel_reflp)

lemma antisymp_rel_pmf:
  "\<lbrakk> reflp R; transp R; antisymp R \<rbrakk>
  \<Longrightarrow> antisymp (rel_pmf R)"
by(rule antisympI)(blast intro: rel_pmf_antisym)

lemma transp_rel_pmf:
  assumes "transp R"
  shows "transp (rel_pmf R)"
  using assms by (fact pmf.rel_transp)


subsection \<open> Distributions \<close>

context
begin

interpretation pmf_as_function .

subsubsection \<open> Bernoulli Distribution \<close>

lift_definition bernoulli_pmf :: "real \<Rightarrow> bool pmf" is
  "\<lambda>p b. ((\<lambda>p. if b then p else 1 - p) \<circ> min 1 \<circ> max 0) p"
  by (auto simp: nn_integral_count_space_finite[where A="{False, True}"] UNIV_bool
           split: split_max split_min)

lemma pmf_bernoulli_True[simp]: "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> pmf (bernoulli_pmf p) True = p"
  by transfer simp

lemma pmf_bernoulli_False[simp]: "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> pmf (bernoulli_pmf p) False = 1 - p"
  by transfer simp

lemma set_pmf_bernoulli[simp]: "0 < p \<Longrightarrow> p < 1 \<Longrightarrow> set_pmf (bernoulli_pmf p) = UNIV"
  by (auto simp add: set_pmf_iff UNIV_bool)

lemma nn_integral_bernoulli_pmf[simp]:
  assumes [simp]: "0 \<le> p" "p \<le> 1" "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^sup>+x. f x \<partial>bernoulli_pmf p) = f True * p + f False * (1 - p)"
  by (subst nn_integral_measure_pmf_support[of UNIV])
     (auto simp: UNIV_bool field_simps)

lemma integral_bernoulli_pmf[simp]:
  assumes [simp]: "0 \<le> p" "p \<le> 1"
  shows "(\<integral>x. f x \<partial>bernoulli_pmf p) = f True * p + f False * (1 - p)"
  by (subst integral_measure_pmf[of UNIV]) (auto simp: UNIV_bool)

lemma pmf_bernoulli_half [simp]: "pmf (bernoulli_pmf (1 / 2)) x = 1 / 2"
by(cases x) simp_all

lemma measure_pmf_bernoulli_half: "measure_pmf (bernoulli_pmf (1 / 2)) = uniform_count_measure UNIV"
  by (rule measure_eqI)
     (simp_all add: nn_integral_pmf[symmetric] emeasure_uniform_count_measure ennreal_divide_numeral[symmetric]
                    nn_integral_count_space_finite sets_uniform_count_measure divide_ennreal_def mult_ac
                    ennreal_of_nat_eq_real_of_nat)

subsubsection \<open> Geometric Distribution \<close>

context
  fixes p :: real assumes p[arith]: "0 < p" "p \<le> 1"
begin

lift_definition geometric_pmf :: "nat pmf" is "\<lambda>n. (1 - p)^n * p"
proof
  have "(\<Sum>i. ennreal (p * (1 - p) ^ i)) = ennreal (p * (1 / (1 - (1 - p))))"
    by (intro suminf_ennreal_eq sums_mult geometric_sums) auto
  then show "(\<integral>\<^sup>+ x. ennreal ((1 - p)^x * p) \<partial>count_space UNIV) = 1"
    by (simp add: nn_integral_count_space_nat field_simps)
qed simp

lemma pmf_geometric[simp]: "pmf geometric_pmf n = (1 - p)^n * p"
  by transfer rule

end

lemma geometric_pmf_1 [simp]: "geometric_pmf 1 = return_pmf 0"
  by (intro pmf_eqI) (auto simp: indicator_def)

lemma set_pmf_geometric: "0 < p \<Longrightarrow> p < 1 \<Longrightarrow> set_pmf (geometric_pmf p) = UNIV"
  by (auto simp: set_pmf_iff)

lemma geometric_sums_times_n:
  fixes c::"'a::{banach,real_normed_field}"
  assumes "norm c < 1"
  shows "(\<lambda>n. c^n * of_nat n) sums (c / (1 - c)\<^sup>2)"
proof -
  have "(\<lambda>n. c * z ^ n) sums (c / (1 - z))" if "norm z < 1" for z
    using geometric_sums sums_mult that by fastforce
  moreover have "((\<lambda>z. c / (1 - z)) has_field_derivative (c / (1 - c)\<^sup>2)) (at c)"
      using assms by (auto intro!: derivative_eq_intros simp add: semiring_normalization_rules)
  ultimately have "(\<lambda>n. diffs (\<lambda>n. c) n * c ^ n) sums (c / (1 - c)\<^sup>2)"
    using assms by (intro termdiffs_sums_strong)
  then have "(\<lambda>n. of_nat (Suc n) * c ^ (Suc n)) sums (c / (1 - c)\<^sup>2)"
    unfolding diffs_def by (simp add: power_eq_if mult.assoc)
  then show ?thesis
    by (subst (asm) sums_Suc_iff) (auto simp add: mult.commute)
qed

lemma geometric_sums_times_norm:
  fixes c::"'a::{banach,real_normed_field}"
  assumes "norm c < 1"
  shows "(\<lambda>n. norm (c^n * of_nat n)) sums (norm c / (1 - norm c)\<^sup>2)"
proof -
  have "norm (c^n * of_nat n) = (norm c) ^ n * of_nat n" for n::nat
    by (simp add: norm_power norm_mult)
  then show ?thesis
    using geometric_sums_times_n[of "norm c"] assms
    by force
qed

lemma integrable_real_geometric_pmf:
  assumes "p \<in> {0<..1}"
  shows   "integrable (geometric_pmf p) real"
proof -
  have "summable (\<lambda>x. p * ((1 - p) ^ x * real x))"
    using geometric_sums_times_norm[of "1 - p"] assms
    by (intro summable_mult) (auto simp: sums_iff)
  hence "summable (\<lambda>x. (1 - p) ^ x * real x)"
    by (rule summable_mult_D) (use assms in auto)
  thus ?thesis
    unfolding measure_pmf_eq_density using assms
    by (subst integrable_density)
       (auto simp: integrable_count_space_nat_iff mult_ac)
qed

lemma expectation_geometric_pmf:
  assumes "p \<in> {0<..1}"
  shows   "measure_pmf.expectation (geometric_pmf p) real = (1 - p) / p"
proof -
  have "(\<lambda>n. p * ((1 - p) ^ n * n)) sums (p * ((1 - p) / p^2))"
    using assms geometric_sums_times_n[of "1-p"] by (intro sums_mult) auto
  moreover have "(\<lambda>n. p * ((1 - p) ^ n * n)) = (\<lambda>n. (1 - p) ^ n * p  * real n)"
    by auto
  ultimately have *: "(\<lambda>n. (1 - p) ^ n * p  * real n) sums ((1 - p) / p)"
    using assms sums_subst by (auto simp add: power2_eq_square)
  have "measure_pmf.expectation (geometric_pmf p) real =
        (\<integral>n. pmf (geometric_pmf p) n * real n \<partial>count_space UNIV)"
    unfolding measure_pmf_eq_density by (subst integral_density) auto
  also have "integrable (count_space UNIV) (\<lambda>n. pmf (geometric_pmf p) n * real n)"
    using * assms unfolding integrable_count_space_nat_iff by (simp add: sums_iff)
  hence "(\<integral>n. pmf (geometric_pmf p) n * real n \<partial>count_space UNIV) = (1 - p) / p"
    using * assms by (subst integral_count_space_nat) (simp_all add: sums_iff)
  finally show ?thesis by auto
qed

lemma geometric_bind_pmf_unfold:
  assumes "p \<in> {0<..1}"
  shows "geometric_pmf p =
     do {b \<leftarrow> bernoulli_pmf p;
         if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)}"
proof -
  have *: "(Suc -` {i}) = (if i = 0 then {} else {i - 1})" for i
    by force
  have "pmf (geometric_pmf p) i =
        pmf (bernoulli_pmf p \<bind>
            (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)))
            i" for i
  proof -
    have "pmf (geometric_pmf p) i =
          (if i = 0 then p else (1 - p) * pmf (geometric_pmf p) (i - 1))"
      using assms by (simp add: power_eq_if)
    also have "\<dots> = (if i = 0  then p else (1 - p) * pmf (map_pmf Suc (geometric_pmf p)) i)"
      by (simp add: pmf_map indicator_def measure_pmf_single *)
    also have "\<dots> = measure_pmf.expectation (bernoulli_pmf p)
          (\<lambda>x. pmf (if x then return_pmf 0 else map_pmf Suc (geometric_pmf p)) i)"
      using assms by (auto simp add: pmf_map *)
    also have "\<dots> = pmf (bernoulli_pmf p \<bind>
                   (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)))
                   i"
      by (auto simp add: pmf_bind)
    finally show ?thesis .
  qed
  then show ?thesis
    using pmf_eqI by blast
qed


subsubsection \<open> Uniform Multiset Distribution \<close>

context
  fixes M :: "'a multiset" assumes M_not_empty: "M \<noteq> {#}"
begin

lift_definition pmf_of_multiset :: "'a pmf" is "\<lambda>x. count M x / size M"
proof
  show "(\<integral>\<^sup>+ x. ennreal (real (count M x) / real (size M)) \<partial>count_space UNIV) = 1"
    using M_not_empty
    by (simp add: zero_less_divide_iff nn_integral_count_space nonempty_has_size
                  sum_divide_distrib[symmetric])
       (auto simp: size_multiset_overloaded_eq intro!: sum.cong)
qed simp

lemma pmf_of_multiset[simp]: "pmf pmf_of_multiset x = count M x / size M"
  by transfer rule

lemma set_pmf_of_multiset[simp]: "set_pmf pmf_of_multiset = set_mset M"
  by (auto simp: set_pmf_iff)

end

subsubsection \<open> Uniform Distribution \<close>

context
  fixes S :: "'a set" assumes S_not_empty: "S \<noteq> {}" and S_finite: "finite S"
begin

lift_definition pmf_of_set :: "'a pmf" is "\<lambda>x. indicator S x / card S"
proof
  show "(\<integral>\<^sup>+ x. ennreal (indicator S x / real (card S)) \<partial>count_space UNIV) = 1"
    using S_not_empty S_finite
    by (subst nn_integral_count_space'[of S])
       (auto simp: ennreal_of_nat_eq_real_of_nat ennreal_mult[symmetric])
qed simp

lemma pmf_of_set[simp]: "pmf pmf_of_set x = indicator S x / card S"
  by transfer rule

lemma set_pmf_of_set[simp]: "set_pmf pmf_of_set = S"
  using S_finite S_not_empty by (auto simp: set_pmf_iff)

lemma emeasure_pmf_of_set_space[simp]: "emeasure pmf_of_set S = 1"
  by (rule measure_pmf.emeasure_eq_1_AE) (auto simp: AE_measure_pmf_iff)

lemma nn_integral_pmf_of_set: "nn_integral (measure_pmf pmf_of_set) f = sum f S / card S"
  by (subst nn_integral_measure_pmf_finite)
     (simp_all add: sum_distrib_right[symmetric] card_gt_0_iff S_not_empty S_finite divide_ennreal_def
                divide_ennreal[symmetric] ennreal_of_nat_eq_real_of_nat[symmetric] ennreal_times_divide)

lemma integral_pmf_of_set: "integral\<^sup>L (measure_pmf pmf_of_set) f = sum f S / card S"
  by (subst integral_measure_pmf[of S]) (auto simp: S_finite sum_divide_distrib)

lemma emeasure_pmf_of_set: "emeasure (measure_pmf pmf_of_set) A = card (S \<inter> A) / card S"
  by (subst nn_integral_indicator[symmetric], simp)
     (simp add: S_finite S_not_empty card_gt_0_iff indicator_def sum.If_cases divide_ennreal
                ennreal_of_nat_eq_real_of_nat nn_integral_pmf_of_set)

lemma measure_pmf_of_set: "measure (measure_pmf pmf_of_set) A = card (S \<inter> A) / card S"
  using emeasure_pmf_of_set[of A]
  by (simp add: measure_nonneg measure_pmf.emeasure_eq_measure)

end

lemma pmf_expectation_bind_pmf_of_set:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'b pmf"
    and  h :: "'b \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "A \<noteq> {}" "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (set_pmf (f x))"
  shows "measure_pmf.expectation (pmf_of_set A \<bind> f) h =
           (\<Sum>a\<in>A. measure_pmf.expectation (f a) h /\<^sub>R real (card A))"
  using assms by (subst pmf_expectation_bind[of A]) (auto simp: field_split_simps)

lemma map_pmf_of_set:
  assumes "finite A" "A \<noteq> {}"
  shows   "map_pmf f (pmf_of_set A) = pmf_of_multiset (image_mset f (mset_set A))"
    (is "?lhs = ?rhs")
proof (intro pmf_eqI)
  fix x
  from assms have "ennreal (pmf ?lhs x) = ennreal (pmf ?rhs x)"
    by (subst ennreal_pmf_map)
       (simp_all add: emeasure_pmf_of_set mset_set_empty_iff count_image_mset Int_commute)
  thus "pmf ?lhs x = pmf ?rhs x" by simp
qed

lemma pmf_bind_pmf_of_set:
  assumes "A \<noteq> {}" "finite A"
  shows   "pmf (bind_pmf (pmf_of_set A) f) x =
             (\<Sum>xa\<in>A. pmf (f xa) x) / real_of_nat (card A)" (is "?lhs = ?rhs")
proof -
  from assms have "card A > 0" by auto
  with assms have "ennreal ?lhs = ennreal ?rhs"
    by (subst ennreal_pmf_bind)
       (simp_all add: nn_integral_pmf_of_set max_def pmf_nonneg divide_ennreal [symmetric]
        sum_nonneg ennreal_of_nat_eq_real_of_nat)
  thus ?thesis by (subst (asm) ennreal_inj) (auto intro!: sum_nonneg divide_nonneg_nonneg)
qed

lemma pmf_of_set_singleton: "pmf_of_set {x} = return_pmf x"
by(rule pmf_eqI)(simp add: indicator_def)

lemma map_pmf_of_set_inj:
  assumes f: "inj_on f A"
  and [simp]: "A \<noteq> {}" "finite A"
  shows "map_pmf f (pmf_of_set A) = pmf_of_set (f ` A)" (is "?lhs = ?rhs")
proof(rule pmf_eqI)
  fix i
  show "pmf ?lhs i = pmf ?rhs i"
  proof(cases "i \<in> f ` A")
    case True
    then obtain i' where "i = f i'" "i' \<in> A" by auto
    thus ?thesis using f by(simp add: card_image pmf_map_inj)
  next
    case False
    hence "pmf ?lhs i = 0" by(simp add: pmf_eq_0_set_pmf set_map_pmf)
    moreover have "pmf ?rhs i = 0" using False by simp
    ultimately show ?thesis by simp
  qed
qed

lemma map_pmf_of_set_bij_betw:
  assumes "bij_betw f A B" "A \<noteq> {}" "finite A"
  shows   "map_pmf f (pmf_of_set A) = pmf_of_set B"
proof -
  have "map_pmf f (pmf_of_set A) = pmf_of_set (f ` A)"
    by (intro map_pmf_of_set_inj assms bij_betw_imp_inj_on[OF assms(1)])
  also from assms have "f ` A = B" by (simp add: bij_betw_def)
  finally show ?thesis .
qed

text \<open>
  Choosing an element uniformly at random from the union of a disjoint family
  of finite non-empty sets with the same size is the same as first choosing a set
  from the family uniformly at random and then choosing an element from the chosen set
  uniformly at random.
\<close>
lemma pmf_of_set_UN:
  assumes "finite (\<Union>(f ` A))" "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> {}"
          "\<And>x. x \<in> A \<Longrightarrow> card (f x) = n" "disjoint_family_on f A"
  shows   "pmf_of_set (\<Union>(f ` A)) = do {x \<leftarrow> pmf_of_set A; pmf_of_set (f x)}"
            (is "?lhs = ?rhs")
proof (intro pmf_eqI)
  fix x
  from assms have [simp]: "finite A"
    using infinite_disjoint_family_imp_infinite_UNION[of A f] by blast
  from assms have "ereal (pmf (pmf_of_set (\<Union>(f ` A))) x) =
    ereal (indicator (\<Union>x\<in>A. f x) x / real (card (\<Union>x\<in>A. f x)))"
    by (subst pmf_of_set) auto
  also from assms have "card (\<Union>x\<in>A. f x) = card A * n"
    by (subst card_UN_disjoint) (auto simp: disjoint_family_on_def)
  also from assms
    have "indicator (\<Union>x\<in>A. f x) x / real \<dots> =
              indicator (\<Union>x\<in>A. f x) x / (n * real (card A))"
      by (simp add: sum_divide_distrib [symmetric] mult_ac)
  also from assms have "indicator (\<Union>x\<in>A. f x) x = (\<Sum>y\<in>A. indicator (f y) x)"
    by (intro indicator_UN_disjoint) simp_all
  also from assms have "ereal ((\<Sum>y\<in>A. indicator (f y) x) / (real n * real (card A))) =
                          ereal (pmf ?rhs x)"
    by (subst pmf_bind_pmf_of_set) (simp_all add: sum_divide_distrib)
  finally show "pmf ?lhs x = pmf ?rhs x" by simp
qed

lemma bernoulli_pmf_half_conv_pmf_of_set: "bernoulli_pmf (1 / 2) = pmf_of_set UNIV"
  by (rule pmf_eqI) simp_all

subsubsection \<open> Poisson Distribution \<close>

context
  fixes rate :: real assumes rate_pos: "0 < rate"
begin

lift_definition poisson_pmf :: "nat pmf" is "\<lambda>k. rate ^ k / fact k * exp (-rate)"
proof  (* by Manuel Eberl *)
  have summable: "summable (\<lambda>x::nat. rate ^ x / fact x)" using summable_exp
    by (simp add: field_simps divide_inverse [symmetric])
  have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x * exp (-rate) \<partial>count_space UNIV) =
          exp (-rate) * (\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV)"
    by (simp add: field_simps nn_integral_cmult[symmetric] ennreal_mult'[symmetric])
  also from rate_pos have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV) = (\<Sum>x. rate ^ x / fact x)"
    by (simp_all add: nn_integral_count_space_nat suminf_ennreal summable ennreal_suminf_neq_top)
  also have "... = exp rate" unfolding exp_def
    by (simp add: field_simps divide_inverse [symmetric])
  also have "ennreal (exp (-rate)) * ennreal (exp rate) = 1"
    by (simp add: mult_exp_exp ennreal_mult[symmetric])
  finally show "(\<integral>\<^sup>+ x. ennreal (rate ^ x / (fact x) * exp (- rate)) \<partial>count_space UNIV) = 1" .
qed (simp add: rate_pos[THEN less_imp_le])

lemma pmf_poisson[simp]: "pmf poisson_pmf k = rate ^ k / fact k * exp (-rate)"
  by transfer rule

lemma set_pmf_poisson[simp]: "set_pmf poisson_pmf = UNIV"
  using rate_pos by (auto simp: set_pmf_iff)

end

subsubsection \<open> Binomial Distribution \<close>

context
  fixes n :: nat and p :: real assumes p_nonneg: "0 \<le> p" and p_le_1: "p \<le> 1"
begin

lift_definition binomial_pmf :: "nat pmf" is "\<lambda>k. (n choose k) * p^k * (1 - p)^(n - k)"
proof
  have "(\<integral>\<^sup>+k. ennreal (real (n choose k) * p ^ k * (1 - p) ^ (n - k)) \<partial>count_space UNIV) =
    ennreal (\<Sum>k\<le>n. real (n choose k) * p ^ k * (1 - p) ^ (n - k))"
    using p_le_1 p_nonneg by (subst nn_integral_count_space') auto
  also have "(\<Sum>k\<le>n. real (n choose k) * p ^ k * (1 - p) ^ (n - k)) = (p + (1 - p)) ^ n"
    by (subst binomial_ring) (simp add: atLeast0AtMost)
  finally show "(\<integral>\<^sup>+ x. ennreal (real (n choose x) * p ^ x * (1 - p) ^ (n - x)) \<partial>count_space UNIV) = 1"
    by simp
qed (insert p_nonneg p_le_1, simp)

lemma pmf_binomial[simp]: "pmf binomial_pmf k = (n choose k) * p^k * (1 - p)^(n - k)"
  by transfer rule

lemma set_pmf_binomial_eq: "set_pmf binomial_pmf = (if p = 0 then {0} else if p = 1 then {n} else {.. n})"
  using p_nonneg p_le_1 unfolding set_eq_iff set_pmf_iff pmf_binomial by (auto simp: set_pmf_iff)

end

end

lemma set_pmf_binomial_0[simp]: "set_pmf (binomial_pmf n 0) = {0}"
  by (simp add: set_pmf_binomial_eq)

lemma set_pmf_binomial_1[simp]: "set_pmf (binomial_pmf n 1) = {n}"
  by (simp add: set_pmf_binomial_eq)

lemma set_pmf_binomial[simp]: "0 < p \<Longrightarrow> p < 1 \<Longrightarrow> set_pmf (binomial_pmf n p) = {..n}"
  by (simp add: set_pmf_binomial_eq)

lemma finite_set_pmf_binomial_pmf [intro]: "p \<in> {0..1} \<Longrightarrow> finite (set_pmf (binomial_pmf n p))"
  by (subst set_pmf_binomial_eq) auto

lemma expectation_binomial_pmf':
  fixes f :: "nat \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes p: "p \<in> {0..1}"
  shows   "measure_pmf.expectation (binomial_pmf n p) f =
             (\<Sum>k\<le>n. (real (n choose k) * p ^ k * (1 - p) ^ (n - k)) *\<^sub>R f k)"
  using p by (subst integral_measure_pmf[where A = "{..n}"])
             (auto simp: set_pmf_binomial_eq split: if_splits)

lemma integrable_binomial_pmf [simp, intro]:
  fixes f :: "nat \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes p: "p \<in> {0..1}"
  shows "integrable (binomial_pmf n p) f"
  by (rule integrable_measure_pmf_finite) (use assms in auto)

context includes lifting_syntax
begin

lemma bind_pmf_parametric [transfer_rule]:
  "(rel_pmf A ===> (A ===> rel_pmf B) ===> rel_pmf B) bind_pmf bind_pmf"
by(blast intro: rel_pmf_bindI dest: rel_funD)

lemma return_pmf_parametric [transfer_rule]: "(A ===> rel_pmf A) return_pmf return_pmf"
by(rule rel_funI) simp

end


primrec replicate_pmf :: "nat \<Rightarrow> 'a pmf \<Rightarrow> 'a list pmf" where
  "replicate_pmf 0 _ = return_pmf []"
| "replicate_pmf (Suc n) p = do {x \<leftarrow> p; xs \<leftarrow> replicate_pmf n p; return_pmf (x#xs)}"

lemma replicate_pmf_1: "replicate_pmf 1 p = map_pmf (\<lambda>x. [x]) p"
  by (simp add: map_pmf_def bind_return_pmf)

lemma set_replicate_pmf:
  "set_pmf (replicate_pmf n p) = {xs\<in>lists (set_pmf p). length xs = n}"
  by (induction n) (auto simp: length_Suc_conv)

lemma replicate_pmf_distrib:
  "replicate_pmf (m + n) p =
     do {xs \<leftarrow> replicate_pmf m p; ys \<leftarrow> replicate_pmf n p; return_pmf (xs @ ys)}"
  by (induction m) (simp_all add: bind_return_pmf bind_return_pmf' bind_assoc_pmf)

lemma power_diff':
  assumes "b \<le> a"
  shows   "x ^ (a - b) = (if x = 0 \<and> a = b then 1 else x ^ a / (x::'a::field) ^ b)"
proof (cases "x = 0")
  case True
  with assms show ?thesis by (cases "a - b") simp_all
qed (insert assms, simp_all add: power_diff)


lemma binomial_pmf_Suc:
  assumes "p \<in> {0..1}"
  shows   "binomial_pmf (Suc n) p =
             do {b \<leftarrow> bernoulli_pmf p;
                 k \<leftarrow> binomial_pmf n p;
                 return_pmf ((if b then 1 else 0) + k)}" (is "_ = ?rhs")
proof (intro pmf_eqI)
  fix k
  have A: "indicator {Suc a} (Suc b) = indicator {a} b" for a b
    by (simp add: indicator_def)
  show "pmf (binomial_pmf (Suc n) p) k = pmf ?rhs k"
    by (cases k; cases "k > n")
       (insert assms, auto simp: pmf_bind measure_pmf_single A field_split_simps algebra_simps
          not_less less_eq_Suc_le [symmetric] power_diff')
qed

lemma binomial_pmf_0: "p \<in> {0..1} \<Longrightarrow> binomial_pmf 0 p = return_pmf 0"
  by (rule pmf_eqI) (simp_all add: indicator_def)

lemma binomial_pmf_altdef:
  assumes "p \<in> {0..1}"
  shows   "binomial_pmf n p = map_pmf (length \<circ> filter id) (replicate_pmf n (bernoulli_pmf p))"
  by (induction n)
     (insert assms, auto simp: binomial_pmf_Suc map_pmf_def bind_return_pmf bind_assoc_pmf
        bind_return_pmf' binomial_pmf_0 intro!: bind_pmf_cong)


subsection \<open>Negative Binomial distribution\<close>

text \<open>
  The negative binomial distribution counts the number of times a weighted coin comes up
  tails before having come up heads \<open>n\<close> times. In other words: how many failures do we see before
  seeing the \<open>n\<close>-th success?

  An alternative view is that the negative binomial distribution is the sum of \<open>n\<close> i.i.d.
  geometric variables (this is the definition that we use).

  Note that there are sometimes different conventions for this distributions in the literature;
  for instance, sometimes the number of \<^emph>\<open>attempts\<close> is counted instead of the number of failures.
  This only shifts the entire distribution by a constant number and is thus not a big difference.
  I think that the convention we use is the most natural one since the support of the distribution
  starts at 0, whereas for the other convention it starts at \<open>n\<close>.
\<close>
primrec neg_binomial_pmf :: "nat \<Rightarrow> real \<Rightarrow> nat pmf" where
  "neg_binomial_pmf 0 p = return_pmf 0"
| "neg_binomial_pmf (Suc n) p =
     map_pmf (\<lambda>(x,y). (x + y)) (pair_pmf (geometric_pmf p) (neg_binomial_pmf n p))"

lemma neg_binomial_pmf_Suc_0 [simp]: "neg_binomial_pmf (Suc 0) p = geometric_pmf p"
  by (auto simp: pair_pmf_def bind_return_pmf map_pmf_def bind_assoc_pmf bind_return_pmf')

lemmas neg_binomial_pmf_Suc [simp del] = neg_binomial_pmf.simps(2)

lemma neg_binomial_prob_1 [simp]: "neg_binomial_pmf n 1 = return_pmf 0"
  by (induction n) (simp_all add: neg_binomial_pmf_Suc)

text \<open>
  We can now show the aforementioned intuition about counting the failures before the
  \<open>n\<close>-th success with the following recurrence:
\<close>
lemma neg_binomial_pmf_unfold:
  assumes p: "p \<in> {0<..1}"
  shows "neg_binomial_pmf (Suc n) p =
           do {b \<leftarrow> bernoulli_pmf p;
               if b then neg_binomial_pmf n p else map_pmf Suc (neg_binomial_pmf (Suc n) p)}"
  (is "_ = ?rhs")
  unfolding neg_binomial_pmf_Suc
  by (subst geometric_bind_pmf_unfold[OF p])
     (auto simp: map_pmf_def pair_pmf_def bind_assoc_pmf bind_return_pmf bind_return_pmf'
           intro!: bind_pmf_cong)

text \<open>
  Next, we show an explicit formula for the probability mass function of the negative
  binomial distribution:
\<close>
lemma pmf_neg_binomial:
  assumes p: "p \<in> {0<..1}"
  shows   "pmf (neg_binomial_pmf n p) k = real ((k + n - 1) choose k) * p ^ n * (1 - p) ^ k"
proof (induction n arbitrary: k)
  case 0
  thus ?case using assms by (auto simp: indicator_def)
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True
    thus ?thesis using assms by auto
  next
    case False
    let ?f = "pmf (neg_binomial_pmf n p)"
    have "pmf (neg_binomial_pmf (Suc n) p) k =
            pmf (geometric_pmf p \<bind> (\<lambda>x. map_pmf ((+) x) (neg_binomial_pmf n p))) k"
      by (auto simp: pair_pmf_def bind_return_pmf map_pmf_def bind_assoc_pmf neg_binomial_pmf_Suc)
    also have "\<dots> = measure_pmf.expectation (geometric_pmf p) 
                      (\<lambda>x. measure_pmf.prob (neg_binomial_pmf n p) ((+) x -` {k}))"
      by (simp add: pmf_bind pmf_map)
    also have "(\<lambda>x. (+) x -` {k}) = (\<lambda>x. if x \<le> k then {k - x} else {})"
      by (auto simp: fun_eq_iff)
    also have "(\<lambda>x. measure_pmf.prob (neg_binomial_pmf n p) (\<dots> x)) =
               (\<lambda>x. if x \<le> k then ?f(k - x) else 0)"
      by (auto simp: fun_eq_iff measure_pmf_single)
    also have "measure_pmf.expectation (geometric_pmf p) \<dots> =
                 (\<Sum>i\<le>k. pmf (neg_binomial_pmf n p) (k - i) * pmf (geometric_pmf p) i)"
      by (subst integral_measure_pmf_real[where A = "{..k}"]) (auto split: if_splits)
    also have "\<dots> = p^(n+1) * (1-p)^k * real (\<Sum>i\<le>k. (k - i + n - 1) choose (k - i))"
      unfolding sum_distrib_left of_nat_sum
    proof (intro sum.cong refl, goal_cases)
      case (1 i)
      have "pmf (neg_binomial_pmf n p) (k - i) * pmf (geometric_pmf p) i =
              real ((k - i + n - 1) choose (k - i)) * p^(n+1) * ((1-p)^(k-i) * (1-p)^i)"
        using assms Suc.IH by (simp add: mult_ac)
      also have "(1-p)^(k-i) * (1-p)^i = (1-p)^k"
        using 1 by (subst power_add [symmetric]) auto
      finally show ?case by simp
    qed
    also have "(\<Sum>i\<le>k. (k - i + n - 1) choose (k - i)) = (\<Sum>i\<le>k. (n - 1 + i) choose i)"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>i. k - i" "\<lambda>i. k - i"]) 
         (use \<open>n \<noteq> 0\<close> in \<open>auto simp: algebra_simps\<close>)
    also have "\<dots> = (n + k) choose k"
      by (subst sum_choose_lower) (use \<open>n \<noteq> 0\<close> in auto)
    finally show ?thesis
      by (simp add: add_ac)
  qed
qed

(* TODO: Move? *)
lemma gbinomial_0_left: "0 gchoose k = (if k = 0 then 1 else 0)"
  by (cases k) auto

text \<open>
  The following alternative formula highlights why it is called `negative binomial distribution':
\<close>
lemma pmf_neg_binomial':
  assumes p: "p \<in> {0<..1}"
  shows   "pmf (neg_binomial_pmf n p) k = (-1) ^ k * ((-real n) gchoose k) * p ^ n * (1 - p) ^ k"
proof (cases "n > 0")
  case n: True
  have "pmf (neg_binomial_pmf n p) k = real ((k + n - 1) choose k) * p ^ n * (1 - p) ^ k"
    by (rule pmf_neg_binomial) fact+
  also have "real ((k + n - 1) choose k) = ((real k + real n - 1) gchoose k)"
    using n by (subst binomial_gbinomial) (auto simp: of_nat_diff)
  also have "\<dots> = (-1) ^ k * ((-real n) gchoose k)"
    by (subst gbinomial_negated_upper) auto
  finally show ?thesis by simp
qed (auto simp: indicator_def gbinomial_0_left)

text \<open>
  The cumulative distribution function of the negative binomial distribution can be
  expressed in terms of that of the `normal' binomial distribution.
\<close>
lemma prob_neg_binomial_pmf_atMost:
  assumes p: "p \<in> {0<..1}"
  shows "measure_pmf.prob (neg_binomial_pmf n p) {..k} =
         measure_pmf.prob (binomial_pmf (n + k) (1 - p)) {..k}"
proof (cases "n = 0")
  case [simp]: True
  have "set_pmf (binomial_pmf (n + k) (1 - p)) \<subseteq> {..n+k}"
    using p by (subst set_pmf_binomial_eq) auto
  hence "measure_pmf.prob (binomial_pmf (n + k) (1 - p)) {..k} = 1"
    by (subst measure_pmf.prob_eq_1) (auto intro!: AE_pmfI)
  thus ?thesis by simp
next
  case False
  hence n: "n > 0" by auto
  have "measure_pmf.prob (binomial_pmf (n + k) (1 - p)) {..k} = (\<Sum>i\<le>k. pmf (binomial_pmf (n + k) (1 - p)) i)"
    by (intro measure_measure_pmf_finite) auto
  also have "\<dots> = (\<Sum>i\<le>k. real ((n + k) choose i) * p ^ (n + k - i) * (1 - p) ^ i)"
    using p by (simp add: mult_ac)
  also have "\<dots> = p ^ n * (\<Sum>i\<le>k. real ((n + k) choose i) * (1 - p) ^ i * p ^ (k - i))"
    unfolding sum_distrib_left by (intro sum.cong) (auto simp: algebra_simps simp flip: power_add)
  also have "(\<Sum>i\<le>k. real ((n + k) choose i) * (1 - p) ^ i * p ^ (k - i)) =
             (\<Sum>i\<le>k. ((n + i - 1) choose i) * (1 - p) ^ i)"
    using gbinomial_partial_sum_poly_xpos[of k "real n" "1 - p" p] n
    by (simp add: binomial_gbinomial add_ac of_nat_diff)
  also have "p ^ n * \<dots> = (\<Sum>i\<le>k. pmf (neg_binomial_pmf n p) i)"
    using p unfolding sum_distrib_left by (simp add: pmf_neg_binomial algebra_simps)
  also have "\<dots> = measure_pmf.prob (neg_binomial_pmf n p) {..k}"
    by (intro measure_measure_pmf_finite [symmetric]) auto
  finally show ?thesis ..
qed

lemma prob_neg_binomial_pmf_lessThan:
  assumes p: "p \<in> {0<..1}"
  shows "measure_pmf.prob (neg_binomial_pmf n p) {..<k} =
         measure_pmf.prob (binomial_pmf (n + k - 1) (1 - p)) {..<k}"
proof (cases "k = 0")
  case False
  hence "{..<k} = {..k-1}"
    by auto
  thus ?thesis
    using prob_neg_binomial_pmf_atMost[OF p, of n "k - 1"] False by simp
qed auto  

text \<open>
  The expected value of the negative binomial distribution is $n(1-p)/p$:
\<close>
lemma nn_integral_neg_binomial_pmf_real:
  assumes p: "p \<in> {0<..1}"
  shows "nn_integral (measure_pmf (neg_binomial_pmf n p)) of_nat = ennreal (n * (1 - p) / p)"
proof (induction n)
  case 0
  thus ?case by auto
next
  case (Suc n)
  have "nn_integral (measure_pmf (neg_binomial_pmf (Suc n) p)) of_nat =
        nn_integral (measure_pmf (geometric_pmf p)) of_nat +
        nn_integral (measure_pmf (neg_binomial_pmf n p)) of_nat"
    by (simp add: neg_binomial_pmf_Suc case_prod_unfold nn_integral_add nn_integral_pair_pmf')
  also have "nn_integral (measure_pmf (geometric_pmf p)) of_nat = ennreal ((1-p) / p)"
    unfolding ennreal_of_nat_eq_real_of_nat
    using expectation_geometric_pmf[OF p] integrable_real_geometric_pmf[OF p]
    by (subst nn_integral_eq_integral) auto
  also have "nn_integral (measure_pmf (neg_binomial_pmf n p)) of_nat = n * (1 - p) / p" using p
    by (subst Suc.IH)
       (auto simp: ennreal_of_nat_eq_real_of_nat ennreal_mult simp flip: divide_ennreal ennreal_minus)
  also have "ennreal ((1 - p) / p) + ennreal (real n * (1 - p) / p) =
             ennreal ((1-p) / p + real n * (1 - p) / p)"
    by (intro ennreal_plus [symmetric] divide_nonneg_pos mult_nonneg_nonneg) (use p in auto)
  also have "(1-p) / p + real n * (1 - p) / p = real (Suc n) * (1 - p) / p"
    using p by (auto simp: field_simps)
  finally show ?case
    by (simp add: ennreal_of_nat_eq_real_of_nat)
qed

lemma integrable_neg_binomial_pmf_real:
  assumes p: "p \<in> {0<..1}"
  shows "integrable (measure_pmf (neg_binomial_pmf n p)) real"
  using nn_integral_neg_binomial_pmf_real[OF p, of n]
  by (subst integrable_iff_bounded) (auto simp flip: ennreal_of_nat_eq_real_of_nat)

lemma expectation_neg_binomial_pmf:
  assumes p: "p \<in> {0<..1}"
  shows "measure_pmf.expectation (neg_binomial_pmf n p) real = n * (1 - p) / p"
proof -
  have "nn_integral (measure_pmf (neg_binomial_pmf n p)) of_nat = ennreal (n * (1 - p) / p)"
    by (intro nn_integral_neg_binomial_pmf_real p)
  also have "of_nat = (\<lambda>x. ennreal (real x))"
    by (simp add: ennreal_of_nat_eq_real_of_nat fun_eq_iff)
  finally show ?thesis
    using p by (subst (asm) nn_integral_eq_integrable) auto
qed


subsection \<open>PMFs from association lists\<close>

definition pmf_of_list ::" ('a \<times> real) list \<Rightarrow> 'a pmf" where
  "pmf_of_list xs = embed_pmf (\<lambda>x. sum_list (map snd (filter (\<lambda>z. fst z = x) xs)))"

definition pmf_of_list_wf where
  "pmf_of_list_wf xs \<longleftrightarrow> (\<forall>x\<in>set (map snd xs) . x \<ge> 0) \<and> sum_list (map snd xs) = 1"

lemma pmf_of_list_wfI:
  "(\<And>x. x \<in> set (map snd xs) \<Longrightarrow> x \<ge> 0) \<Longrightarrow> sum_list (map snd xs) = 1 \<Longrightarrow> pmf_of_list_wf xs"
  unfolding pmf_of_list_wf_def by simp

context
begin

private lemma pmf_of_list_aux:
  assumes "\<And>x. x \<in> set (map snd xs) \<Longrightarrow> x \<ge> 0"
  assumes "sum_list (map snd xs) = 1"
  shows "(\<integral>\<^sup>+ x. ennreal (sum_list (map snd [z\<leftarrow>xs . fst z = x])) \<partial>count_space UNIV) = 1"
proof -
  have "(\<integral>\<^sup>+ x. ennreal (sum_list (map snd (filter (\<lambda>z. fst z = x) xs))) \<partial>count_space UNIV) =
            (\<integral>\<^sup>+ x. ennreal (sum_list (map (\<lambda>(x',p). indicator {x'} x * p) xs)) \<partial>count_space UNIV)"
    apply (intro nn_integral_cong ennreal_cong, subst sum_list_map_filter')
    apply (rule arg_cong[where f = sum_list])
    apply (auto cong: map_cong)
    done
  also have "\<dots> = (\<Sum>(x',p)\<leftarrow>xs. (\<integral>\<^sup>+ x. ennreal (indicator {x'} x * p) \<partial>count_space UNIV))"
    using assms(1)
  proof (induction xs)
    case (Cons x xs)
    from Cons.prems have "snd x \<ge> 0" by simp
    moreover have "b \<ge> 0" if "(a,b) \<in> set xs" for a b
      using Cons.prems[of b] that by force
    ultimately have "(\<integral>\<^sup>+ y. ennreal (\<Sum>(x', p)\<leftarrow>x # xs. indicator {x'} y * p) \<partial>count_space UNIV) =
            (\<integral>\<^sup>+ y. ennreal (indicator {fst x} y * snd x) +
            ennreal (\<Sum>(x', p)\<leftarrow>xs. indicator {x'} y * p) \<partial>count_space UNIV)"
      by (intro nn_integral_cong, subst ennreal_plus [symmetric])
         (auto simp: case_prod_unfold indicator_def intro!: sum_list_nonneg)
    also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (indicator {fst x} y * snd x) \<partial>count_space UNIV) +
                      (\<integral>\<^sup>+ y. ennreal (\<Sum>(x', p)\<leftarrow>xs. indicator {x'} y * p) \<partial>count_space UNIV)"
      by (intro nn_integral_add)
         (force intro!: sum_list_nonneg AE_I2 intro: Cons simp: indicator_def)+
    also have "(\<integral>\<^sup>+ y. ennreal (\<Sum>(x', p)\<leftarrow>xs. indicator {x'} y * p) \<partial>count_space UNIV) =
               (\<Sum>(x', p)\<leftarrow>xs. (\<integral>\<^sup>+ y. ennreal (indicator {x'} y * p) \<partial>count_space UNIV))"
      using Cons(1) by (intro Cons) simp_all
    finally show ?case by (simp add: case_prod_unfold)
  qed simp
  also have "\<dots> = (\<Sum>(x',p)\<leftarrow>xs. ennreal p * (\<integral>\<^sup>+ x. indicator {x'} x \<partial>count_space UNIV))"
    using assms(1)
    by (simp cong: map_cong only: case_prod_unfold, subst nn_integral_cmult [symmetric])
       (auto intro!: assms(1) simp: max_def times_ereal.simps [symmetric] mult_ac ereal_indicator
             simp del: times_ereal.simps)+
  also from assms have "\<dots> = sum_list (map snd xs)" by (simp add: case_prod_unfold sum_list_ennreal)
  also have "\<dots> = 1" using assms(2) by simp
  finally show ?thesis .
qed

lemma pmf_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "pmf (pmf_of_list xs) x = sum_list (map snd (filter (\<lambda>z. fst z = x) xs))"
  using assms pmf_of_list_aux[of xs] unfolding pmf_of_list_def pmf_of_list_wf_def
  by (subst pmf_embed_pmf) (auto intro!: sum_list_nonneg)

end

lemma set_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "set_pmf (pmf_of_list xs) \<subseteq> set (map fst xs)"
proof clarify
  fix x assume A: "x \<in> set_pmf (pmf_of_list xs)"
  show "x \<in> set (map fst xs)"
  proof (rule ccontr)
    assume "x \<notin> set (map fst xs)"
    hence "[z\<leftarrow>xs . fst z = x] = []" by (auto simp: filter_empty_conv)
    with A assms show False by (simp add: pmf_pmf_of_list set_pmf_eq)
  qed
qed

lemma finite_set_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "finite (set_pmf (pmf_of_list xs))"
  using assms by (rule finite_subset[OF set_pmf_of_list]) simp_all

lemma emeasure_Int_set_pmf:
  "emeasure (measure_pmf p) (A \<inter> set_pmf p) = emeasure (measure_pmf p) A"
  by (rule emeasure_eq_AE) (auto simp: AE_measure_pmf_iff)

lemma measure_Int_set_pmf:
  "measure (measure_pmf p) (A \<inter> set_pmf p) = measure (measure_pmf p) A"
  using emeasure_Int_set_pmf[of p A] by (simp add: Sigma_Algebra.measure_def)

lemma measure_prob_cong_0:
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> pmf p x = 0"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> pmf p x = 0"
  shows   "measure (measure_pmf p) A = measure (measure_pmf p) B"
proof -
  have "measure_pmf.prob p A = measure_pmf.prob p (A \<inter> set_pmf p)"
    by (simp add: measure_Int_set_pmf)
  also have "A \<inter> set_pmf p = B \<inter> set_pmf p"
    using assms by (auto simp: set_pmf_eq)
  also have "measure_pmf.prob p \<dots> = measure_pmf.prob p B"
    by (simp add: measure_Int_set_pmf)
  finally show ?thesis .
qed

lemma emeasure_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "emeasure (pmf_of_list xs) A = ennreal (sum_list (map snd (filter (\<lambda>x. fst x \<in> A) xs)))"
proof -
  have "emeasure (pmf_of_list xs) A = nn_integral (measure_pmf (pmf_of_list xs)) (indicator A)"
    by simp
  also from assms
    have "\<dots> = (\<Sum>x\<in>set_pmf (pmf_of_list xs) \<inter> A. ennreal (sum_list (map snd [z\<leftarrow>xs . fst z = x])))"
    by (subst nn_integral_measure_pmf_finite) (simp_all add: finite_set_pmf_of_list pmf_pmf_of_list Int_def)
  also from assms
    have "\<dots> = ennreal (\<Sum>x\<in>set_pmf (pmf_of_list xs) \<inter> A. sum_list (map snd [z\<leftarrow>xs . fst z = x]))"
    by (subst sum_ennreal) (auto simp: pmf_of_list_wf_def intro!: sum_list_nonneg)
  also have "\<dots> = ennreal (\<Sum>x\<in>set_pmf (pmf_of_list xs) \<inter> A.
      indicator A x * pmf (pmf_of_list xs) x)" (is "_ = ennreal ?S")
    using assms by (intro ennreal_cong sum.cong) (auto simp: pmf_pmf_of_list)
  also have "?S = (\<Sum>x\<in>set_pmf (pmf_of_list xs). indicator A x * pmf (pmf_of_list xs) x)"
    using assms by (intro sum.mono_neutral_left set_pmf_of_list finite_set_pmf_of_list) auto
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). indicator A x * pmf (pmf_of_list xs) x)"
    using assms by (intro sum.mono_neutral_left set_pmf_of_list) (auto simp: set_pmf_eq)
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). indicator A x *
                      sum_list (map snd (filter (\<lambda>z. fst z = x) xs)))"
    using assms by (simp add: pmf_pmf_of_list)
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). sum_list (map snd (filter (\<lambda>z. fst z = x \<and> x \<in> A) xs)))"
    by (intro sum.cong) (auto simp: indicator_def)
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). (\<Sum>xa = 0..<length xs.
                     if fst (xs ! xa) = x \<and> x \<in> A then snd (xs ! xa) else 0))"
    by (intro sum.cong refl, subst sum_list_map_filter', subst sum_list_sum_nth) simp
  also have "\<dots> = (\<Sum>xa = 0..<length xs. (\<Sum>x\<in>set (map fst xs).
                     if fst (xs ! xa) = x \<and> x \<in> A then snd (xs ! xa) else 0))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>xa = 0..<length xs. if fst (xs ! xa) \<in> A then
                     (\<Sum>x\<in>set (map fst xs). if x = fst (xs ! xa) then snd (xs ! xa) else 0) else 0)"
    by (auto intro!: sum.cong sum.neutral simp del: sum.delta)
  also have "\<dots> = (\<Sum>xa = 0..<length xs. if fst (xs ! xa) \<in> A then snd (xs ! xa) else 0)"
    by (intro sum.cong refl) (simp_all add: sum.delta)
  also have "\<dots> = sum_list (map snd (filter (\<lambda>x. fst x \<in> A) xs))"
    by (subst sum_list_map_filter', subst sum_list_sum_nth) simp_all
  finally show ?thesis .
qed

lemma measure_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "measure (pmf_of_list xs) A = sum_list (map snd (filter (\<lambda>x. fst x \<in> A) xs))"
  using assms unfolding pmf_of_list_wf_def Sigma_Algebra.measure_def
  by (subst emeasure_pmf_of_list [OF assms], subst enn2real_ennreal) (auto intro!: sum_list_nonneg)

(* TODO Move? *)
lemma sum_list_nonneg_eq_zero_iff:
  fixes xs :: "'a :: linordered_ab_group_add list"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0) \<Longrightarrow> sum_list xs = 0 \<longleftrightarrow> set xs \<subseteq> {0}"
proof (induction xs)
  case (Cons x xs)
  from Cons.prems have "sum_list (x#xs) = 0 \<longleftrightarrow> x = 0 \<and> sum_list xs = 0"
    unfolding sum_list_simps by (subst add_nonneg_eq_0_iff) (auto intro: sum_list_nonneg)
  with Cons.IH Cons.prems show ?case by simp
qed simp_all

lemma sum_list_filter_nonzero:
  "sum_list (filter (\<lambda>x. x \<noteq> 0) xs) = sum_list xs"
  by (induction xs) simp_all
(* END MOVE *)

lemma set_pmf_of_list_eq:
  assumes "pmf_of_list_wf xs" "\<And>x. x \<in> snd ` set xs \<Longrightarrow> x > 0"
  shows   "set_pmf (pmf_of_list xs) = fst ` set xs"
proof
  {
    fix x assume A: "x \<in> fst ` set xs" and B: "x \<notin> set_pmf (pmf_of_list xs)"
    then obtain y where y: "(x, y) \<in> set xs" by auto
    from B have "sum_list (map snd [z\<leftarrow>xs. fst z = x]) = 0"
      by (simp add: pmf_pmf_of_list[OF assms(1)] set_pmf_eq)
    moreover from y have "y \<in> snd ` {xa \<in> set xs. fst xa = x}" by force
    ultimately have "y = 0" using assms(1)
      by (subst (asm) sum_list_nonneg_eq_zero_iff) (auto simp: pmf_of_list_wf_def)
    with assms(2) y have False by force
  }
  thus "fst ` set xs \<subseteq> set_pmf (pmf_of_list xs)" by blast
qed (insert set_pmf_of_list[OF assms(1)], simp_all)

lemma pmf_of_list_remove_zeros:
  assumes "pmf_of_list_wf xs"
  defines "xs' \<equiv> filter (\<lambda>z. snd z \<noteq> 0) xs"
  shows   "pmf_of_list_wf xs'" "pmf_of_list xs' = pmf_of_list xs"
proof -
  have "map snd [z\<leftarrow>xs . snd z \<noteq> 0] = filter (\<lambda>x. x \<noteq> 0) (map snd xs)"
    by (induction xs) simp_all
  with assms(1) show wf: "pmf_of_list_wf xs'"
    by (auto simp: pmf_of_list_wf_def xs'_def sum_list_filter_nonzero)
  have "sum_list (map snd [z\<leftarrow>xs' . fst z = i]) = sum_list (map snd [z\<leftarrow>xs . fst z = i])" for i
    unfolding xs'_def by (induction xs) simp_all
  with assms(1) wf show "pmf_of_list xs' = pmf_of_list xs"
    by (intro pmf_eqI) (simp_all add: pmf_pmf_of_list)
qed

end
