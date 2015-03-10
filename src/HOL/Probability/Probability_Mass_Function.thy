(*  Title:      HOL/Probability/Probability_Mass_Function.thy
    Author:     Johannes Hölzl, TU München
    Author:     Andreas Lochbihler, ETH Zurich
*)

section \<open> Probability mass function \<close>

theory Probability_Mass_Function
imports
  Giry_Monad
  "~~/src/HOL/Library/Multiset"
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
      by (auto simp: emeasure_le_0_iff) }
  then show "P x" by auto
qed

lemma AE_measure_singleton: "measure M {x} \<noteq> 0 \<Longrightarrow> AE x in M. P x \<Longrightarrow> P x"
  by (metis AE_emeasure_singleton measure_def emeasure_empty measure_empty)

lemma ereal_divide': "b \<noteq> 0 \<Longrightarrow> ereal (a / b) = ereal a / ereal b"
  using ereal_divide[of a b] by simp

lemma (in finite_measure) countable_support:
  "countable {x. measure M {x} \<noteq> 0}"
proof cases
  assume "measure M (space M) = 0"
  with bounded_measure measure_le_0_iff have "{x. measure M {x} \<noteq> 0} = {}"
    by auto
  then show ?thesis
    by simp
next
  let ?M = "measure M (space M)" and ?m = "\<lambda>x. measure M {x}"
  assume "?M \<noteq> 0"
  then have *: "{x. ?m x \<noteq> 0} = (\<Union>n. {x. ?M / Suc n < ?m x})"
    using reals_Archimedean[of "?m x / ?M" for x]
    by (auto simp: field_simps not_le[symmetric] measure_nonneg divide_le_0_iff measure_le_0_iff)
  have **: "\<And>n. finite {x. ?M / Suc n < ?m x}"
  proof (rule ccontr)
    fix n assume "infinite {x. ?M / Suc n < ?m x}" (is "infinite ?X")
    then obtain X where "finite X" "card X = Suc (Suc n)" "X \<subseteq> ?X"
      by (metis infinite_arbitrarily_large)
    from this(3) have *: "\<And>x. x \<in> X \<Longrightarrow> ?M / Suc n \<le> ?m x"
      by auto
    { fix x assume "x \<in> X"
      from `?M \<noteq> 0` *[OF this] have "?m x \<noteq> 0" by (auto simp: field_simps measure_le_0_iff)
      then have "{x} \<in> sets M" by (auto dest: measure_notin_sets) }
    note singleton_sets = this
    have "?M < (\<Sum>x\<in>X. ?M / Suc n)"
      using `?M \<noteq> 0`
      by (simp add: `card X = Suc (Suc n)` real_eq_of_nat[symmetric] real_of_nat_Suc field_simps less_le measure_nonneg)
    also have "\<dots> \<le> (\<Sum>x\<in>X. ?m x)"
      by (rule setsum_mono) fact
    also have "\<dots> = measure M (\<Union>x\<in>X. {x})"
      using singleton_sets `finite X`
      by (intro finite_measure_finite_Union[symmetric]) (auto simp: disjoint_family_on_def)
    finally have "?M < measure M (\<Union>x\<in>X. {x})" .
    moreover have "measure M (\<Union>x\<in>X. {x}) \<le> ?M"
      using singleton_sets[THEN sets.sets_into_space] by (intro finite_measure_mono) auto
    ultimately show False by simp
  qed
  show ?thesis
    unfolding * by (intro countable_UN countableI_type countable_finite[OF **])
qed

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
    by (intro AE_I[OF order_refl]) (auto simp: emeasure_eq_measure set_diff_eq cong: conj_cong)
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

interpretation measure_pmf!: prob_space "measure_pmf M" for M
  by (rule prob_space_measure_pmf)

interpretation measure_pmf!: subprob_space "measure_pmf M" for M
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
                                            unfolded pair_collapse] assms)
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
                                            unfolded pair_collapse] assms)
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
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma AE_measure_pmf_iff: "(AE x in measure_pmf M. P x) \<longleftrightarrow> (\<forall>y\<in>M. P y)"
  using AE_measure_singleton[of M] AE_measure_pmf[of M]
  by (auto simp: set_pmf.rep_eq)

lemma countable_set_pmf [simp]: "countable (set_pmf p)"
  by transfer (metis prob_space.finite_measure finite_measure.countable_support)

lemma pmf_positive: "x \<in> set_pmf p \<Longrightarrow> 0 < pmf p x"
  by transfer (simp add: less_le measure_nonneg)

lemma pmf_nonneg: "0 \<le> pmf p x"
  by transfer (simp add: measure_nonneg)

lemma pmf_le_1: "pmf p x \<le> 1"
  by (simp add: pmf.rep_eq)

lemma set_pmf_not_empty: "set_pmf M \<noteq> {}"
  using AE_measure_pmf[of M] by (intro notI) simp

lemma set_pmf_iff: "x \<in> set_pmf M \<longleftrightarrow> pmf M x \<noteq> 0"
  by transfer simp

lemma set_pmf_eq: "set_pmf M = {x. pmf M x \<noteq> 0}"
  by (auto simp: set_pmf_iff)

lemma emeasure_pmf_single:
  fixes M :: "'a pmf"
  shows "emeasure M {x} = pmf M x"
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma emeasure_measure_pmf_finite: "finite S \<Longrightarrow> emeasure (measure_pmf M) S = (\<Sum>s\<in>S. pmf M s)"
  by (subst emeasure_eq_setsum_singleton) (auto simp: emeasure_pmf_single)

lemma measure_measure_pmf_finite: "finite S \<Longrightarrow> measure (measure_pmf M) S = setsum (pmf M) S"
  using emeasure_measure_pmf_finite[of S M] by(simp add: measure_pmf.emeasure_eq_measure)

lemma nn_integral_measure_pmf_support:
  fixes f :: "'a \<Rightarrow> ereal"
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
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite (set_pmf M)" and nn: "\<And>x. x \<in> set_pmf M \<Longrightarrow> 0 \<le> f x"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>set_pmf M. f x * pmf M x)"
  using assms by (intro nn_integral_measure_pmf_support) auto
lemma integrable_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "finite (set_pmf M) \<Longrightarrow> integrable M f"
  by (auto intro!: integrableI_bounded simp: nn_integral_measure_pmf_finite)

lemma integral_measure_pmf:
  assumes [simp]: "finite A" and "\<And>a. a \<in> set_pmf M \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> A"
  shows "(\<integral>x. f x \<partial>measure_pmf M) = (\<Sum>a\<in>A. f a * pmf M a)"
proof -
  have "(\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x * indicator A x \<partial>measure_pmf M)"
    using assms(2) by (intro integral_cong_AE) (auto split: split_indicator simp: AE_measure_pmf_iff)
  also have "\<dots> = (\<Sum>a\<in>A. f a * pmf M a)"
    by (subst integral_indicator_finite_real) (auto simp: measure_def emeasure_measure_pmf_finite)
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
    by (simp add: measure_pmf.emeasure_eq_measure)
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
  show "sets (measure_pmf x \<guillemotright>= A) = sets (measure_pmf x \<guillemotright>= B)"
    using assms by (subst (1 2) sets_bind) (auto simp: space_subprob_algebra)
next
  fix X assume "X \<in> sets (measure_pmf x \<guillemotright>= A)"
  then have X: "X \<in> sets N"
    using assms by (subst (asm) sets_bind) (auto simp: space_subprob_algebra)
  show "emeasure (measure_pmf x \<guillemotright>= A) X = emeasure (measure_pmf x \<guillemotright>= B) X"
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

  show "prob_space (f \<guillemotright>= g)"
    using g by (intro f.prob_space_bind[where S="count_space UNIV"]) auto
  then interpret fg: prob_space "f \<guillemotright>= g" .
  show [simp]: "sets (f \<guillemotright>= g) = UNIV"
    using sets_eq_imp_space_eq[OF s_f]
    by (subst sets_bind[where N="count_space UNIV"]) auto
  show "AE x in f \<guillemotright>= g. measure (f \<guillemotright>= g) {x} \<noteq> 0"
    apply (simp add: fg.prob_eq_0 AE_bind[where B="count_space UNIV"])
    using ae_f
    apply eventually_elim
    using ae_g
    apply eventually_elim
    apply (auto dest: AE_measure_singleton)
    done
qed

lemma ereal_pmf_bind: "pmf (bind_pmf N f) i = (\<integral>\<^sup>+x. pmf (f x) i \<partial>measure_pmf N)"
  unfolding pmf.rep_eq bind_pmf.rep_eq
  by (auto simp: measure_pmf.measure_bind[where N="count_space UNIV"] measure_subprob measure_nonneg
           intro!: nn_integral_eq_integral[symmetric] measure_pmf.integrable_const_bound[where B=1])

lemma pmf_bind: "pmf (bind_pmf N f) i = (\<integral>x. pmf (f x) i \<partial>measure_pmf N)"
  using ereal_pmf_bind[of N f i]
  by (subst (asm) nn_integral_eq_integral)
     (auto simp: pmf_nonneg pmf_le_1
           intro!: nn_integral_eq_integral[symmetric] measure_pmf.integrable_const_bound[where B=1])

lemma bind_pmf_const[simp]: "bind_pmf M (\<lambda>x. c) = c"
  by transfer (simp add: bind_const' prob_space_imp_subprob_space)

lemma set_bind_pmf[simp]: "set_pmf (bind_pmf M N) = (\<Union>M\<in>set_pmf M. set_pmf (N M))"
  unfolding set_pmf_eq ereal_eq_0(1)[symmetric] ereal_pmf_bind
  by (auto simp add: nn_integral_0_iff_AE AE_measure_pmf_iff set_pmf_eq not_le less_le pmf_nonneg)

lemma bind_pmf_cong:
  assumes "p = q"
  shows "(\<And>x. x \<in> set_pmf q \<Longrightarrow> f x = g x) \<Longrightarrow> bind_pmf p f = bind_pmf q g"
  unfolding `p = q`[symmetric] measure_pmf_inject[symmetric] bind_pmf.rep_eq
  by (auto simp: AE_measure_pmf_iff Pi_iff space_subprob_algebra subprob_space_measure_pmf
                 sets_bind[where N="count_space UNIV"] emeasure_bind[where N="count_space UNIV"]
           intro!: nn_integral_cong_AE measure_eqI)

lemma bind_pmf_cong_simp:
  "p = q \<Longrightarrow> (\<And>x. x \<in> set_pmf q =simp=> f x = g x) \<Longrightarrow> bind_pmf p f = bind_pmf q g"
  by (simp add: simp_implies_def cong: bind_pmf_cong)

lemma measure_pmf_bind: "measure_pmf (bind_pmf M f) = (measure_pmf M \<guillemotright>= (\<lambda>x. measure_pmf (f x)))"
  by transfer simp

lemma nn_integral_bind_pmf[simp]: "(\<integral>\<^sup>+x. f x \<partial>bind_pmf M N) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f y \<partial>N x \<partial>M)"
  using measurable_measure_pmf[of N]
  unfolding measure_pmf_bind
  apply (subst (1 3) nn_integral_max_0[symmetric])
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
  fix N :: "'a measure" assume "sets N = UNIV" then show "N \<guillemotright>= return (count_space UNIV) = N"
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
  "rel_fun op = (rel_fun cr_pmf cr_pmf) (\<lambda>f M. distr M (count_space UNIV) f) map_pmf"
proof -
  have "rel_fun op = (rel_fun pmf_as_measure.cr_pmf pmf_as_measure.cr_pmf)
     (\<lambda>f M. M \<guillemotright>= (return (count_space UNIV) o f)) map_pmf"
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

lemma pmf_set_map: "set_pmf \<circ> map_pmf f = op ` f \<circ> set_pmf"
  by (auto simp add: comp_def fun_eq_iff map_pmf_def)

lemma set_map_pmf[simp]: "set_pmf (map_pmf f M) = f`set_pmf M"
  using pmf_set_map[of f] by (auto simp: comp_def fun_eq_iff)

lemma emeasure_map_pmf[simp]: "emeasure (map_pmf f M) X = emeasure M (f -` X)"
  unfolding map_pmf_rep_eq by (subst emeasure_distr) auto

lemma nn_integral_map_pmf[simp]: "(\<integral>\<^sup>+x. f x \<partial>map_pmf g M) = (\<integral>\<^sup>+x. f (g x) \<partial>M)"
  unfolding map_pmf_rep_eq by (intro nn_integral_distr) auto

lemma ereal_pmf_map: "pmf (map_pmf f p) x = (\<integral>\<^sup>+ y. indicator (f -` {x}) y \<partial>measure_pmf p)"
proof (transfer fixing: f x)
  fix p :: "'b measure"
  presume "prob_space p"
  then interpret prob_space p .
  presume "sets p = UNIV"
  then show "ereal (measure (distr p (count_space UNIV) f) {x}) = integral\<^sup>N p (indicator (f -` {x}))"
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

lemma map_return_pmf: "map_pmf f (return_pmf x) = return_pmf (f x)"
  by transfer (simp add: distr_return)

lemma map_pmf_const[simp]: "map_pmf (\<lambda>_. c) M = return_pmf c"
  by transfer (auto simp: prob_space.distr_const)

lemma pmf_return: "pmf (return_pmf x) y = indicator {y} x"
  by transfer (simp add: measure_return)

lemma nn_integral_return_pmf[simp]: "0 \<le> f x \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>return_pmf x) = f x"
  unfolding return_pmf.rep_eq by (intro nn_integral_return) auto

lemma emeasure_return_pmf[simp]: "emeasure (return_pmf x) X = indicator X x"
  unfolding return_pmf.rep_eq by (intro emeasure_return) auto

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
  apply (subst integral_measure_pmf[where A="{b}"])
  apply (auto simp: indicator_eq_0_iff)
  apply (subst integral_measure_pmf[where A="{a}"])
  apply (auto simp: indicator_eq_0_iff setsum_nonneg_eq_0_iff pmf_nonneg)
  done

lemma set_pair_pmf[simp]: "set_pmf (pair_pmf A B) = set_pmf A \<times> set_pmf B"
  unfolding pair_pmf_def set_bind_pmf set_return_pmf by auto

lemma measure_pmf_in_subprob_space[measurable (raw)]:
  "measure_pmf M \<in> space (subprob_algebra (count_space UNIV))"
  by (simp add: space_subprob_algebra) intro_locales

lemma nn_integral_pair_pmf': "(\<integral>\<^sup>+x. f x \<partial>pair_pmf A B) = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. f (a, b) \<partial>B \<partial>A)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>pair_pmf A B) = (\<integral>\<^sup>+x. max 0 (f x) * indicator (A \<times> B) x \<partial>pair_pmf A B)"
    by (subst nn_integral_max_0[symmetric])
       (auto simp: AE_measure_pmf_iff intro!: nn_integral_cong_AE)
  also have "\<dots> = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. max 0 (f (a, b)) * indicator (A \<times> B) (a, b) \<partial>B \<partial>A)"
    by (simp add: pair_pmf_def)
  also have "\<dots> = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. max 0 (f (a, b)) \<partial>B \<partial>A)"
    by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
  finally show ?thesis
    unfolding nn_integral_max_0 .
qed

lemma bind_pair_pmf:
  assumes M[measurable]: "M \<in> measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) (subprob_algebra N)"
  shows "measure_pmf (pair_pmf A B) \<guillemotright>= M = (measure_pmf A \<guillemotright>= (\<lambda>x. measure_pmf B \<guillemotright>= (\<lambda>y. M (x, y))))"
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
                     nn_integral_measure_pmf_finite emeasure_nonneg pmf_return one_ereal_def[symmetric])
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
  using pmf_nonneg[of M p] by simp

lemma min_pmf_0[simp]: "min (pmf M p) 0 = 0" "min 0 (pmf M p) = 0"
  using pmf_nonneg[of M p] by simp_all

lemma pmf_eq_0_set_pmf: "pmf M p = 0 \<longleftrightarrow> p \<notin> set_pmf M"
  unfolding set_pmf_iff by simp

lemma pmf_map_inj: "inj_on f (set_pmf M) \<Longrightarrow> x \<in> set_pmf M \<Longrightarrow> pmf (map_pmf f M) (f x) = pmf M x"
  by (auto simp: pmf.rep_eq map_pmf_rep_eq measure_distr AE_measure_pmf_iff inj_onD
           intro!: measure_pmf.finite_measure_eq_AE)

subsection \<open> PMFs as function \<close>

context
  fixes f :: "'a \<Rightarrow> real"
  assumes nonneg: "\<And>x. 0 \<le> f x"
  assumes prob: "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = 1"
begin

lift_definition embed_pmf :: "'a pmf" is "density (count_space UNIV) (ereal \<circ> f)"
proof (intro conjI)
  have *[simp]: "\<And>x y. ereal (f y) * indicator {x} y = ereal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  show "AE x in density (count_space UNIV) (ereal \<circ> f).
    measure (density (count_space UNIV) (ereal \<circ> f)) {x} \<noteq> 0"
    by (simp add: AE_density nonneg measure_def emeasure_density max_def)
  show "prob_space (density (count_space UNIV) (ereal \<circ> f))"
    by default (simp add: emeasure_density prob)
qed simp

lemma pmf_embed_pmf: "pmf embed_pmf x = f x"
proof transfer
  have *[simp]: "\<And>x y. ereal (f y) * indicator {x} y = ereal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  fix x show "measure (density (count_space UNIV) (ereal \<circ> f)) {x} = f x"
    by transfer (simp add: measure_def emeasure_density nonneg max_def)
qed

end

lemma embed_pmf_transfer:
  "rel_fun (eq_onp (\<lambda>f. (\<forall>x. 0 \<le> f x) \<and> (\<integral>\<^sup>+x. ereal (f x) \<partial>count_space UNIV) = 1)) pmf_as_measure.cr_pmf (\<lambda>f. density (count_space UNIV) (ereal \<circ> f)) embed_pmf"
  by (auto simp: rel_fun_def eq_onp_def embed_pmf.transfer)

lemma measure_pmf_eq_density: "measure_pmf p = density (count_space UNIV) (pmf p)"
proof (transfer, elim conjE)
  fix M :: "'a measure" assume [simp]: "sets M = UNIV" and ae: "AE x in M. measure M {x} \<noteq> 0"
  assume "prob_space M" then interpret prob_space M .
  show "M = density (count_space UNIV) (\<lambda>x. ereal (measure M {x}))"
  proof (rule measure_eqI)
    fix A :: "'a set"
    have "(\<integral>\<^sup>+ x. ereal (measure M {x}) * indicator A x \<partial>count_space UNIV) =
      (\<integral>\<^sup>+ x. emeasure M {x} * indicator (A \<inter> {x. measure M {x} \<noteq> 0}) x \<partial>count_space UNIV)"
      by (auto intro!: nn_integral_cong simp: emeasure_eq_measure split: split_indicator)
    also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} \<partial>count_space (A \<inter> {x. measure M {x} \<noteq> 0}))"
      by (subst nn_integral_restrict_space[symmetric]) (auto simp: restrict_count_space)
    also have "\<dots> = emeasure M (\<Union>x\<in>(A \<inter> {x. measure M {x} \<noteq> 0}). {x})"
      by (intro emeasure_UN_countable[symmetric] countable_Int2 countable_support)
         (auto simp: disjoint_family_on_def)
    also have "\<dots> = emeasure M A"
      using ae by (intro emeasure_eq_AE) auto
    finally show " emeasure M A = emeasure (density (count_space UNIV) (\<lambda>x. ereal (measure M {x}))) A"
      using emeasure_space_1 by (simp add: emeasure_density)
  qed simp
qed

lemma td_pmf_embed_pmf:
  "type_definition pmf embed_pmf {f::'a \<Rightarrow> real. (\<forall>x. 0 \<le> f x) \<and> (\<integral>\<^sup>+x. ereal (f x) \<partial>count_space UNIV) = 1}"
  unfolding type_definition_def
proof safe
  fix p :: "'a pmf"
  have "(\<integral>\<^sup>+ x. 1 \<partial>measure_pmf p) = 1"
    using measure_pmf.emeasure_space_1[of p] by simp
  then show *: "(\<integral>\<^sup>+ x. ereal (pmf p x) \<partial>count_space UNIV) = 1"
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

locale pmf_as_function
begin

setup_lifting td_pmf_embed_pmf

lemma set_pmf_transfer[transfer_rule]:
  assumes "bi_total A"
  shows "rel_fun (pcr_pmf A) (rel_set A) (\<lambda>f. {x. f x \<noteq> 0}) set_pmf"
  using `bi_total A`
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
    by (rule integral_cong) (auto intro!: integral_pmf_restrict)
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
    by (rule integral_cong) (auto intro!: integral_pmf_restrict[symmetric])
  finally show "(\<integral> x. \<integral> y. pmf (C x y) i \<partial>B \<partial>A) = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)" .
qed

lemma pair_map_pmf1: "pair_pmf (map_pmf f A) B = map_pmf (apfst f) (pair_pmf A B)"
proof (safe intro!: pmf_eqI)
  fix a :: "'a" and b :: "'b"
  have [simp]: "\<And>c d. indicator (apfst f -` {(a, b)}) (c, d) = indicator (f -` {a}) c * (indicator {b} d::ereal)"
    by (auto split: split_indicator)

  have "ereal (pmf (pair_pmf (map_pmf f A) B) (a, b)) =
         ereal (pmf (map_pmf (apfst f) (pair_pmf A B)) (a, b))"
    unfolding pmf_pair ereal_pmf_map
    by (simp add: nn_integral_pair_pmf' max_def emeasure_pmf_single nn_integral_multc pmf_nonneg
                  emeasure_map_pmf[symmetric] del: emeasure_map_pmf)
  then show "pmf (pair_pmf (map_pmf f A) B) (a, b) = pmf (map_pmf (apfst f) (pair_pmf A B)) (a, b)"
    by simp
qed

lemma pair_map_pmf2: "pair_pmf A (map_pmf f B) = map_pmf (apsnd f) (pair_pmf A B)"
proof (safe intro!: pmf_eqI)
  fix a :: "'a" and b :: "'b"
  have [simp]: "\<And>c d. indicator (apsnd f -` {(a, b)}) (c, d) = indicator {a} c * (indicator (f -` {b}) d::ereal)"
    by (auto split: split_indicator)

  have "ereal (pmf (pair_pmf A (map_pmf f B)) (a, b)) =
         ereal (pmf (map_pmf (apsnd f) (pair_pmf A B)) (a, b))"
    unfolding pmf_pair ereal_pmf_map
    by (simp add: nn_integral_pair_pmf' max_def emeasure_pmf_single nn_integral_cmult nn_integral_multc pmf_nonneg
                  emeasure_map_pmf[symmetric] del: emeasure_map_pmf)
  then show "pmf (pair_pmf A (map_pmf f B)) (a, b) = pmf (map_pmf (apsnd f) (pair_pmf A B)) (a, b)"
    by simp
qed

lemma map_pair: "map_pmf (\<lambda>(a, b). (f a, g b)) (pair_pmf A B) = pair_pmf (map_pmf f A) (map_pmf g B)"
  by (simp add: pair_map_pmf2 pair_map_pmf1 map_pmf_comp split_beta')

end

subsection \<open> Conditional Probabilities \<close>

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
  using emeasure_measure_pmf_not_zero unfolding measure_pmf.emeasure_eq_measure by simp

lift_definition cond_pmf :: "'a pmf" is
  "uniform_measure (measure_pmf p) s"
proof (intro conjI)
  show "prob_space (uniform_measure (measure_pmf p) s)"
    by (intro prob_space_uniform_measure) (auto simp: emeasure_measure_pmf_not_zero)
  show "AE x in uniform_measure (measure_pmf p) s. measure (uniform_measure (measure_pmf p) s) {x} \<noteq> 0"
    by (simp add: emeasure_measure_pmf_not_zero measure_measure_pmf_not_zero AE_uniform_measure
                  AE_measure_pmf_iff set_pmf.rep_eq)
qed simp

lemma pmf_cond: "pmf cond_pmf x = (if x \<in> s then pmf p x / measure p s else 0)"
  by transfer (simp add: emeasure_measure_pmf_not_zero pmf.rep_eq)

lemma set_cond_pmf[simp]: "set_pmf cond_pmf = set_pmf p \<inter> s"
  by (auto simp add: set_pmf_iff pmf_cond measure_measure_pmf_not_zero split: split_if_asm)

end

lemma cond_map_pmf:
  assumes "set_pmf p \<inter> f -` s \<noteq> {}"
  shows "cond_pmf (map_pmf f p) s = map_pmf f (cond_pmf p (f -` s))"
proof -
  have *: "set_pmf (map_pmf f p) \<inter> s \<noteq> {}"
    using assms by auto
  { fix x
    have "ereal (pmf (map_pmf f (cond_pmf p (f -` s))) x) =
      emeasure p (f -` s \<inter> f -` {x}) / emeasure p (f -` s)"
      unfolding ereal_pmf_map cond_pmf.rep_eq[OF assms] by (simp add: nn_integral_uniform_measure)
    also have "f -` s \<inter> f -` {x} = (if x \<in> s then f -` {x} else {})"
      by auto
    also have "emeasure p (if x \<in> s then f -` {x} else {}) / emeasure p (f -` s) =
      ereal (pmf (cond_pmf (map_pmf f p) s) x)"
      using measure_measure_pmf_not_zero[OF *]
      by (simp add: pmf_cond[OF *] ereal_divide' ereal_pmf_map measure_pmf.emeasure_eq_measure[symmetric]
               del: ereal_divide)
    finally have "ereal (pmf (cond_pmf (map_pmf f p) s) x) = ereal (pmf (map_pmf f (cond_pmf p (f -` s))) x)"
      by simp }
  then show ?thesis
    by (intro pmf_eqI) simp
qed

lemma bind_cond_pmf_cancel:
  assumes in_S: "\<And>x. x \<in> set_pmf p \<Longrightarrow> x \<in> S x" "\<And>x. x \<in> set_pmf q \<Longrightarrow> x \<in> S x"
  assumes S_eq: "\<And>x y. x \<in> S y \<Longrightarrow> S x = S y"
  and same: "\<And>x. measure (measure_pmf p) (S x) = measure (measure_pmf q) (S x)"
  shows "bind_pmf p (\<lambda>x. cond_pmf q (S x)) = q" (is "?lhs = _")
proof (rule pmf_eqI)
  { fix x
    assume "x \<in> set_pmf p"
    hence "set_pmf p \<inter> (S x) \<noteq> {}" using in_S by auto
    hence "measure (measure_pmf p) (S x) \<noteq> 0"
      by(auto simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff)
    with same have "measure (measure_pmf q) (S x) \<noteq> 0" by simp
    hence "set_pmf q \<inter> S x \<noteq> {}"
      by(auto simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff) }
  note [simp] = this

  fix z
  have pmf_q_z: "z \<notin> S z \<Longrightarrow> pmf q z = 0"
    by(erule contrapos_np)(simp add: pmf_eq_0_set_pmf in_S)

  have "ereal (pmf ?lhs z) = \<integral>\<^sup>+ x. ereal (pmf (cond_pmf q (S x)) z) \<partial>measure_pmf p"
    by(simp add: ereal_pmf_bind)
  also have "\<dots> = \<integral>\<^sup>+ x. ereal (pmf q z / measure p (S z)) * indicator (S z) x \<partial>measure_pmf p"
    by(rule nn_integral_cong_AE)(auto simp add: AE_measure_pmf_iff pmf_cond same pmf_q_z in_S dest!: S_eq split: split_indicator)
  also have "\<dots> = pmf q z" using pmf_nonneg[of q z]
    by (subst nn_integral_cmult)(auto simp add: measure_nonneg measure_pmf.emeasure_eq_measure same measure_pmf.prob_eq_0 AE_measure_pmf_iff pmf_eq_0_set_pmf in_S)
  finally show "pmf ?lhs z = pmf q z" by simp
qed

subsection \<open> Relator \<close>

inductive rel_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf \<Rightarrow> bool"
for R p q
where
  "\<lbrakk> \<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y;
     map_pmf fst pq = p; map_pmf snd pq = q \<rbrakk>
  \<Longrightarrow> rel_pmf R p q"

bnf pmf: "'a pmf" map: map_pmf sets: set_pmf bd : "natLeq" rel: rel_pmf
proof -
  show "map_pmf id = id" by (rule map_pmf_id)
  show "\<And>f g. map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g" by (rule map_pmf_compose)
  show "\<And>f g::'a \<Rightarrow> 'b. \<And>p. (\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g p"
    by (intro map_pmf_cong refl)

  show "\<And>f::'a \<Rightarrow> 'b. set_pmf \<circ> map_pmf f = op ` f \<circ> set_pmf"
    by (rule pmf_set_map)

  { fix p :: "'s pmf"
    have "(card_of (set_pmf p), card_of (UNIV :: nat set)) \<in> ordLeq"
      by (rule card_of_ordLeqI[where f="to_nat_on (set_pmf p)"])
         (auto intro: countable_set_pmf)
    also have "(card_of (UNIV :: nat set), natLeq) \<in> ordLeq"
      by (metis Field_natLeq card_of_least natLeq_Well_order)
    finally show "(card_of (set_pmf p), natLeq) \<in> ordLeq" . }

  show "\<And>R. rel_pmf R =
         (BNF_Def.Grp {x. set_pmf x \<subseteq> {(x, y). R x y}} (map_pmf fst))\<inverse>\<inverse> OO
         BNF_Def.Grp {x. set_pmf x \<subseteq> {(x, y). R x y}} (map_pmf snd)"
     by (auto simp add: fun_eq_iff BNF_Def.Grp_def OO_def rel_pmf.simps)

  { fix p :: "'a pmf" and f :: "'a \<Rightarrow> 'b" and g x
    assume p: "\<And>z. z \<in> set_pmf p \<Longrightarrow> f z = g z"
      and x: "x \<in> set_pmf p"
    thus "f x = g x" by simp }

  fix R :: "'a => 'b \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  { fix p q r
    assume pq: "rel_pmf R p q"
      and qr:"rel_pmf S q r"
    from pq obtain pq where pq: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y"
      and p: "p = map_pmf fst pq" and q: "q = map_pmf snd pq" by cases auto
    from qr obtain qr where qr: "\<And>y z. (y, z) \<in> set_pmf qr \<Longrightarrow> S y z"
      and q': "q = map_pmf fst qr" and r: "r = map_pmf snd qr" by cases auto

    def pr \<equiv> "bind_pmf pq (\<lambda>(x, y). bind_pmf (cond_pmf qr {(y', z). y' = y}) (\<lambda>(y', z). return_pmf (x, z)))"
    have pr_welldefined: "\<And>y. y \<in> q \<Longrightarrow> qr \<inter> {(y', z). y' = y} \<noteq> {}"
      by (force simp: q')

    have "rel_pmf (R OO S) p r"
    proof (rule rel_pmf.intros)
      fix x z assume "(x, z) \<in> pr"
      then have "\<exists>y. (x, y) \<in> pq \<and> (y, z) \<in> qr"
        by (auto simp: q pr_welldefined pr_def split_beta)
      with pq qr show "(R OO S) x z"
        by blast
    next
      have "map_pmf snd pr = map_pmf snd (bind_pmf q (\<lambda>y. cond_pmf qr {(y', z). y' = y}))"
        by (simp add: pr_def q split_beta bind_map_pmf map_pmf_def[symmetric] map_bind_pmf map_return_pmf)
      then show "map_pmf snd pr = r"
        unfolding r q' bind_map_pmf by (subst (asm) bind_cond_pmf_cancel) auto
    qed (simp add: pr_def map_bind_pmf split_beta map_return_pmf map_pmf_def[symmetric] p) }
  then show "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
    by(auto simp add: le_fun_def)
qed (fact natLeq_card_order natLeq_cinfinite)+

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
  with `a \<in> M` have "(x, a) \<in> pq"
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

lemma ereal_pmf_join: "ereal (pmf (join_pmf N) i) = (\<integral>\<^sup>+M. pmf M i \<partial>measure_pmf N)"
  unfolding join_pmf_def ereal_pmf_bind ..

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

text {*
  Proof that @{const rel_pmf} preserves orders.
  Antisymmetry proof follows Thm. 1 in N. Saheb-Djahromi, Cpo's of measures for nondeterminism,
  Theoretical Computer Science 12(1):19--37, 1980,
  @{url "http://dx.doi.org/10.1016/0304-3975(80)90003-1"}
*}

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
proof
  let ?E = "\<lambda>x. {y. R x y \<and> R y x}"
  let ?\<mu>E = "\<lambda>x. measure q (?E x)"
  { fix x
    have "measure p (?E x) = measure p ({y. R x y} - {y. R x y \<and> \<not> R y x})"
      by(auto intro!: arg_cong[where f="measure p"])
    also have "\<dots> = measure p {y. R x y} - measure p {y. R x y \<and> \<not> R y x}"
      by (rule measure_pmf.finite_measure_Diff) auto
    also have "measure p {y. R x y \<and> \<not> R y x} = measure q {y. R x y \<and> \<not> R y x}"
      using 1 2 refl trans by(auto intro!: Orderings.antisym measure_Ioi)
    also have "measure p {y. R x y} = measure q {y. R x y}"
      using 1 2 refl trans by(auto intro!: Orderings.antisym measure_Ici)
    also have "measure q {y. R x y} - measure q {y. R x y \<and> ~ R y x} =
      measure q ({y. R x y} - {y. R x y \<and> \<not> R y x})"
      by(rule measure_pmf.finite_measure_Diff[symmetric]) auto
    also have "\<dots> = ?\<mu>E x"
      by(auto intro!: arg_cong[where f="measure q"])
    also note calculation }
  note eq = this

  def pq \<equiv> "bind_pmf p (\<lambda>x. bind_pmf (cond_pmf q (?E x)) (\<lambda>y. return_pmf (x, y)))"

  show "map_pmf fst pq = p"
    by(simp add: pq_def map_bind_pmf map_return_pmf bind_return_pmf')

  show "map_pmf snd pq = q"
    unfolding pq_def map_bind_pmf map_return_pmf bind_return_pmf' snd_conv
    by(subst bind_cond_pmf_cancel)(auto simp add: reflpD[OF \<open>reflp R\<close>] eq  intro: transpD[OF \<open>transp R\<close>])

  fix x y
  assume "(x, y) \<in> set_pmf pq"
  moreover
  { assume "x \<in> set_pmf p"
    hence "measure (measure_pmf p) (?E x) \<noteq> 0"
      by (auto simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff intro: reflpD[OF \<open>reflp R\<close>])
    hence "measure (measure_pmf q) (?E x) \<noteq> 0" using eq by simp
    hence "set_pmf q \<inter> {y. R x y \<and> R y x} \<noteq> {}"
      by (auto simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff) }
  ultimately show "inf R R\<inverse>\<inverse> x y"
    by (auto simp add: pq_def)
qed

lemma rel_pmf_antisym:
  fixes p q :: "'a pmf"
  assumes 1: "rel_pmf R p q"
  assumes 2: "rel_pmf R q p"
  and refl: "reflp R" and trans: "transp R" and antisym: "antisymP R"
  shows "p = q"
proof -
  from 1 2 refl trans have "rel_pmf (inf R R\<inverse>\<inverse>) p q" by(rule rel_pmf_inf)
  also have "inf R R\<inverse>\<inverse> = op ="
    using refl antisym by (auto intro!: ext simp add: reflpD dest: antisymD)
  finally show ?thesis unfolding pmf.rel_eq .
qed

lemma reflp_rel_pmf: "reflp R \<Longrightarrow> reflp (rel_pmf R)"
by(blast intro: reflpI rel_pmf_reflI reflpD)

lemma antisymP_rel_pmf:
  "\<lbrakk> reflp R; transp R; antisymP R \<rbrakk>
  \<Longrightarrow> antisymP (rel_pmf R)"
by(rule antisymI)(blast intro: rel_pmf_antisym)

lemma transp_rel_pmf:
  assumes "transp R"
  shows "transp (rel_pmf R)"
proof (rule transpI)
  fix x y z
  assume "rel_pmf R x y" and "rel_pmf R y z"
  hence "rel_pmf (R OO R) x z" by (simp add: pmf.rel_compp relcompp.relcompI)
  thus "rel_pmf R x z"
    using assms by (metis (no_types) pmf.rel_mono rev_predicate2D transp_relcompp_less_eq)
qed

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

lemma set_pmf_bernoulli: "0 < p \<Longrightarrow> p < 1 \<Longrightarrow> set_pmf (bernoulli_pmf p) = UNIV"
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
by(rule measure_eqI)(simp_all add: nn_integral_pmf[symmetric] emeasure_uniform_count_measure nn_integral_count_space_finite sets_uniform_count_measure)

subsubsection \<open> Geometric Distribution \<close>

lift_definition geometric_pmf :: "nat pmf" is "\<lambda>n. 1 / 2^Suc n"
proof
  note geometric_sums[of "1 / 2"]
  note sums_mult[OF this, of "1 / 2"]
  from sums_suminf_ereal[OF this]
  show "(\<integral>\<^sup>+ x. ereal (1 / 2 ^ Suc x) \<partial>count_space UNIV) = 1"
    by (simp add: nn_integral_count_space_nat field_simps)
qed simp

lemma pmf_geometric[simp]: "pmf geometric_pmf n = 1 / 2^Suc n"
  by transfer rule

lemma set_pmf_geometric[simp]: "set_pmf geometric_pmf = UNIV"
  by (auto simp: set_pmf_iff)

subsubsection \<open> Uniform Multiset Distribution \<close>

context
  fixes M :: "'a multiset" assumes M_not_empty: "M \<noteq> {#}"
begin

lift_definition pmf_of_multiset :: "'a pmf" is "\<lambda>x. count M x / size M"
proof
  show "(\<integral>\<^sup>+ x. ereal (real (count M x) / real (size M)) \<partial>count_space UNIV) = 1"
    using M_not_empty
    by (simp add: zero_less_divide_iff nn_integral_count_space nonempty_has_size
                  setsum_divide_distrib[symmetric])
       (auto simp: size_multiset_overloaded_eq intro!: setsum.cong)
qed simp

lemma pmf_of_multiset[simp]: "pmf pmf_of_multiset x = count M x / size M"
  by transfer rule

lemma set_pmf_of_multiset[simp]: "set_pmf pmf_of_multiset = set_of M"
  by (auto simp: set_pmf_iff)

end

subsubsection \<open> Uniform Distribution \<close>

context
  fixes S :: "'a set" assumes S_not_empty: "S \<noteq> {}" and S_finite: "finite S"
begin

lift_definition pmf_of_set :: "'a pmf" is "\<lambda>x. indicator S x / card S"
proof
  show "(\<integral>\<^sup>+ x. ereal (indicator S x / real (card S)) \<partial>count_space UNIV) = 1"
    using S_not_empty S_finite by (subst nn_integral_count_space'[of S]) auto
qed simp

lemma pmf_of_set[simp]: "pmf pmf_of_set x = indicator S x / card S"
  by transfer rule

lemma set_pmf_of_set[simp]: "set_pmf pmf_of_set = S"
  using S_finite S_not_empty by (auto simp: set_pmf_iff)

lemma emeasure_pmf_of_set[simp]: "emeasure pmf_of_set S = 1"
  by (rule measure_pmf.emeasure_eq_1_AE) (auto simp: AE_measure_pmf_iff)

end

subsubsection \<open> Poisson Distribution \<close>

context
  fixes rate :: real assumes rate_pos: "0 < rate"
begin

lift_definition poisson_pmf :: "nat pmf" is "\<lambda>k. rate ^ k / fact k * exp (-rate)"
proof
  (* Proof by Manuel Eberl *)

  have summable: "summable (\<lambda>x::nat. rate ^ x / fact x)" using summable_exp
    by (simp add: field_simps divide_inverse [symmetric])
  have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x * exp (-rate) \<partial>count_space UNIV) =
          exp (-rate) * (\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV)"
    by (simp add: field_simps nn_integral_cmult[symmetric])
  also from rate_pos have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV) = (\<Sum>x. rate ^ x / fact x)"
    by (simp_all add: nn_integral_count_space_nat suminf_ereal summable suminf_ereal_finite)
  also have "... = exp rate" unfolding exp_def
    by (simp add: field_simps divide_inverse [symmetric] transfer_int_nat_factorial)
  also have "ereal (exp (-rate)) * ereal (exp rate) = 1"
    by (simp add: mult_exp_exp)
  finally show "(\<integral>\<^sup>+ x. ereal (rate ^ x / real (fact x) * exp (- rate)) \<partial>count_space UNIV) = 1" .
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
  have "(\<integral>\<^sup>+k. ereal (real (n choose k) * p ^ k * (1 - p) ^ (n - k)) \<partial>count_space UNIV) =
    ereal (\<Sum>k\<le>n. real (n choose k) * p ^ k * (1 - p) ^ (n - k))"
    using p_le_1 p_nonneg by (subst nn_integral_count_space') auto
  also have "(\<Sum>k\<le>n. real (n choose k) * p ^ k * (1 - p) ^ (n - k)) = (p + (1 - p)) ^ n"
    by (subst binomial_ring) (simp add: atLeast0AtMost real_of_nat_def)
  finally show "(\<integral>\<^sup>+ x. ereal (real (n choose x) * p ^ x * (1 - p) ^ (n - x)) \<partial>count_space UNIV) = 1"
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

end
