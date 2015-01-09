(*  Title:      HOL/Probability/Probability_Mass_Function.thy
    Author:     Johannes Hölzl, TU München 
    Author:     Andreas Lochbihler, ETH Zurich
*)

section \<open> Probability mass function \<close>

theory Probability_Mass_Function
imports
  Giry_Monad
  "~~/src/HOL/Number_Theory/Binomial"
  "~~/src/HOL/Library/Multiset"
begin

lemma bind_return'': "sets M = sets N \<Longrightarrow> M \<guillemotright>= return N = M"
   by (cases "space M = {}")
      (simp_all add: bind_empty space_empty[symmetric] bind_nonempty join_return'
                cong: subprob_algebra_cong)


lemma (in prob_space) distr_const[simp]:
  "c \<in> space N \<Longrightarrow> distr M N (\<lambda>x. c) = return N c"
  by (rule measure_eqI) (auto simp: emeasure_distr emeasure_space_1)

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

subsection {* PMF as measure *}

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

lift_definition pmf :: "'a pmf \<Rightarrow> 'a \<Rightarrow> real" is "\<lambda>M x. measure M {x}" .

lift_definition set_pmf :: "'a pmf \<Rightarrow> 'a set" is "\<lambda>M. {x. measure M {x} \<noteq> 0}" .

lift_definition map_pmf :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf" is
  "\<lambda>f M. distr M (count_space UNIV) f"
proof safe
  fix M and f :: "'a \<Rightarrow> 'b"
  let ?D = "distr M (count_space UNIV) f"
  assume "prob_space M" and [simp]: "sets M = UNIV" and ae: "AE x in M. measure M {x} \<noteq> 0"
  interpret prob_space M by fact
  from ae have "AE x in M. measure M (f -` {f x}) \<noteq> 0"
  proof eventually_elim
    fix x
    have "measure M {x} \<le> measure M (f -` {f x})"
      by (intro finite_measure_mono) auto
    then show "measure M {x} \<noteq> 0 \<Longrightarrow> measure M (f -` {f x}) \<noteq> 0"
      using measure_nonneg[of M "{x}"] by auto
  qed
  then show "AE x in ?D. measure ?D {x} \<noteq> 0"
    by (simp add: AE_distr_iff measure_distr measurable_def)
qed (auto simp: measurable_def prob_space.prob_space_distr)

declare [[coercion set_pmf]]

lemma countable_set_pmf [simp]: "countable (set_pmf p)"
  by transfer (metis prob_space.finite_measure finite_measure.countable_support)

lemma sets_measure_pmf[simp]: "sets (measure_pmf p) = UNIV"
  by transfer metis

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

lemma pmf_positive: "x \<in> set_pmf p \<Longrightarrow> 0 < pmf p x"
  by transfer (simp add: less_le measure_nonneg)

lemma pmf_nonneg: "0 \<le> pmf p x"
  by transfer (simp add: measure_nonneg)

lemma pmf_le_1: "pmf p x \<le> 1"
  by (simp add: pmf.rep_eq)

lemma emeasure_pmf_single:
  fixes M :: "'a pmf"
  shows "emeasure M {x} = pmf M x"
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma AE_measure_pmf: "AE x in (M::'a pmf). x \<in> M"
  by transfer simp

lemma emeasure_pmf_single_eq_zero_iff:
  fixes M :: "'a pmf"
  shows "emeasure M {y} = 0 \<longleftrightarrow> y \<notin> M"
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma AE_measure_pmf_iff: "(AE x in measure_pmf M. P x) \<longleftrightarrow> (\<forall>y\<in>M. P y)"
proof -
  { fix y assume y: "y \<in> M" and P: "AE x in M. P x" "\<not> P y"
    with P have "AE x in M. x \<noteq> y"
      by auto
    with y have False
      by (simp add: emeasure_pmf_single_eq_zero_iff AE_iff_measurable[OF _ refl]) }
  then show ?thesis
    using AE_measure_pmf[of M] by auto
qed

lemma set_pmf_not_empty: "set_pmf M \<noteq> {}"
  using AE_measure_pmf[of M] by (intro notI) simp

lemma set_pmf_iff: "x \<in> set_pmf M \<longleftrightarrow> pmf M x \<noteq> 0"
  by transfer simp

lemma emeasure_measure_pmf_finite: "finite S \<Longrightarrow> emeasure (measure_pmf M) S = (\<Sum>s\<in>S. pmf M s)"
  by (subst emeasure_eq_setsum_singleton) (auto simp: emeasure_pmf_single)

lemma measure_measure_pmf_finite: "finite S \<Longrightarrow> measure (measure_pmf M) S = setsum (pmf M) S"
using emeasure_measure_pmf_finite[of S M]
by(simp add: measure_pmf.emeasure_eq_measure)

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

lemma in_null_sets_measure_pmfI:
  "A \<inter> set_pmf p = {} \<Longrightarrow> A \<in> null_sets (measure_pmf p)"
using emeasure_eq_0_AE[where ?P="\<lambda>x. x \<in> A" and M="measure_pmf p"]
by(auto simp add: null_sets_def AE_measure_pmf_iff)

lemma map_pmf_id[simp]: "map_pmf id = id"
  by (rule, transfer) (auto simp: emeasure_distr measurable_def intro!: measure_eqI)

lemma map_pmf_ident[simp]: "map_pmf (\<lambda>x. x) = (\<lambda>x. x)"
  using map_pmf_id unfolding id_def .

lemma map_pmf_compose: "map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g"
  by (rule, transfer) (simp add: distr_distr[symmetric, where N="count_space UNIV"] measurable_def) 

lemma map_pmf_comp: "map_pmf f (map_pmf g M) = map_pmf (\<lambda>x. f (g x)) M"
  using map_pmf_compose[of f g] by (simp add: comp_def)

lemma map_pmf_cong:
  assumes "p = q"
  shows "(\<And>x. x \<in> set_pmf q \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g q"
  unfolding `p = q`[symmetric] measure_pmf_inject[symmetric] map_pmf.rep_eq
  by (auto simp add: emeasure_distr AE_measure_pmf_iff intro!: emeasure_eq_AE measure_eqI)

lemma emeasure_map_pmf[simp]: "emeasure (map_pmf f M) X = emeasure M (f -` X)"
  unfolding map_pmf.rep_eq by (subst emeasure_distr) auto

lemma nn_integral_map_pmf[simp]: "(\<integral>\<^sup>+x. f x \<partial>map_pmf g M) = (\<integral>\<^sup>+x. f (g x) \<partial>M)"
  unfolding map_pmf.rep_eq by (intro nn_integral_distr) auto

lemma ereal_pmf_map: "pmf (map_pmf f p) x = (\<integral>\<^sup>+ y. indicator (f -` {x}) y \<partial>measure_pmf p)"
proof(transfer fixing: f x)
  fix p :: "'b measure"
  presume "prob_space p"
  then interpret prob_space p .
  presume "sets p = UNIV"
  then show "ereal (measure (distr p (count_space UNIV) f) {x}) = integral\<^sup>N p (indicator (f -` {x}))"
    by(simp add: measure_distr measurable_def emeasure_eq_measure)
qed simp_all

lemma pmf_set_map: 
  fixes f :: "'a \<Rightarrow> 'b"
  shows "set_pmf \<circ> map_pmf f = op ` f \<circ> set_pmf"
proof (rule, transfer, clarsimp simp add: measure_distr measurable_def)
  fix f :: "'a \<Rightarrow> 'b" and M :: "'a measure"
  assume "prob_space M" and ae: "AE x in M. measure M {x} \<noteq> 0" and [simp]: "sets M = UNIV"
  interpret prob_space M by fact
  show "{x. measure M (f -` {x}) \<noteq> 0} = f ` {x. measure M {x} \<noteq> 0}"
  proof safe
    fix x assume "measure M (f -` {x}) \<noteq> 0"
    moreover have "measure M (f -` {x}) = measure M {y. f y = x \<and> measure M {y} \<noteq> 0}"
      using ae by (intro finite_measure_eq_AE) auto
    ultimately have "{y. f y = x \<and> measure M {y} \<noteq> 0} \<noteq> {}"
      by (metis measure_empty)
    then show "x \<in> f ` {x. measure M {x} \<noteq> 0}"
      by auto
  next
    fix x assume "measure M {x} \<noteq> 0"
    then have "0 < measure M {x}"
      using measure_nonneg[of M "{x}"] by auto
    also have "measure M {x} \<le> measure M (f -` {f x})"
      by (intro finite_measure_mono) auto
    finally show "measure M (f -` {f x}) = 0 \<Longrightarrow> False"
      by simp
  qed
qed

lemma set_map_pmf: "set_pmf (map_pmf f M) = f`set_pmf M"
  using pmf_set_map[of f] by (auto simp: comp_def fun_eq_iff)

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

subsection {* PMFs as function *}

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

end

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
    by (simp add: field_simps field_divide_inverse[symmetric])
  have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x * exp (-rate) \<partial>count_space UNIV) =
          exp (-rate) * (\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV)"
    by (simp add: field_simps nn_integral_cmult[symmetric])
  also from rate_pos have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV) = (\<Sum>x. rate ^ x / fact x)"
    by (simp_all add: nn_integral_count_space_nat suminf_ereal summable suminf_ereal_finite)
  also have "... = exp rate" unfolding exp_def
    by (simp add: field_simps field_divide_inverse[symmetric] transfer_int_nat_factorial)
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

subsection \<open> Monad Interpretation \<close>

lemma measurable_measure_pmf[measurable]:
  "(\<lambda>x. measure_pmf (M x)) \<in> measurable (count_space UNIV) (subprob_algebra (count_space UNIV))"
  by (auto simp: space_subprob_algebra intro!: prob_space_imp_subprob_space) unfold_locales

lemma bind_pmf_cong:
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

context
begin

interpretation pmf_as_measure .

lift_definition join_pmf :: "'a pmf pmf \<Rightarrow> 'a pmf" is "\<lambda>M. measure_pmf M \<guillemotright>= measure_pmf"
proof (intro conjI)
  fix M :: "'a pmf pmf"

  interpret bind: prob_space "measure_pmf M \<guillemotright>= measure_pmf"
    apply (intro measure_pmf.prob_space_bind[where S="count_space UNIV"] AE_I2)
    apply (auto intro!: subprob_space_measure_pmf simp: space_subprob_algebra)
    apply unfold_locales
    done
  show "prob_space (measure_pmf M \<guillemotright>= measure_pmf)"
    by intro_locales
  show "sets (measure_pmf M \<guillemotright>= measure_pmf) = UNIV"
    by (subst sets_bind) auto
  have "AE x in measure_pmf M \<guillemotright>= measure_pmf. emeasure (measure_pmf M \<guillemotright>= measure_pmf) {x} \<noteq> 0"
    by (auto simp: AE_bind[where B="count_space UNIV"] measure_pmf_in_subprob_algebra
                   emeasure_bind[where N="count_space UNIV"] AE_measure_pmf_iff nn_integral_0_iff_AE
                   measure_pmf.emeasure_eq_measure measure_le_0_iff set_pmf_iff pmf.rep_eq)
  then show "AE x in measure_pmf M \<guillemotright>= measure_pmf. measure (measure_pmf M \<guillemotright>= measure_pmf) {x} \<noteq> 0"
    unfolding bind.emeasure_eq_measure by simp
qed

lemma pmf_join: "pmf (join_pmf N) i = (\<integral>M. pmf M i \<partial>measure_pmf N)"
proof (transfer fixing: N i)
  have N: "subprob_space (measure_pmf N)"
    by (rule prob_space_imp_subprob_space) intro_locales
  show "measure (measure_pmf N \<guillemotright>= measure_pmf) {i} = integral\<^sup>L (measure_pmf N) (\<lambda>M. measure M {i})"
    using measurable_measure_pmf[of "\<lambda>x. x"]
    by (intro subprob_space.measure_bind[where N="count_space UNIV", OF N]) auto
qed (auto simp: Transfer.Rel_def rel_fun_def cr_pmf_def)

lemma set_pmf_join_pmf: "set_pmf (join_pmf f) = (\<Union>p\<in>set_pmf f. set_pmf p)"
apply(simp add: set_eq_iff set_pmf_iff pmf_join)
apply(subst integral_nonneg_eq_0_iff_AE)
apply(auto simp add: pmf_le_1 pmf_nonneg AE_measure_pmf_iff intro!: measure_pmf.integrable_const_bound[where B=1])
done

lift_definition return_pmf :: "'a \<Rightarrow> 'a pmf" is "return (count_space UNIV)"
  by (auto intro!: prob_space_return simp: AE_return measure_return)

lemma join_return_pmf: "join_pmf (return_pmf M) = M"
  by (simp add: integral_return pmf_eq_iff pmf_join return_pmf.rep_eq)

lemma map_return_pmf: "map_pmf f (return_pmf x) = return_pmf (f x)"
  by transfer (simp add: distr_return)

lemma map_pmf_const[simp]: "map_pmf (\<lambda>_. c) M = return_pmf c"
  by transfer (auto simp: prob_space.distr_const)

lemma set_return_pmf: "set_pmf (return_pmf x) = {x}"
  by transfer (auto simp add: measure_return split: split_indicator)

lemma pmf_return: "pmf (return_pmf x) y = indicator {y} x"
  by transfer (simp add: measure_return)

lemma nn_integral_return_pmf[simp]: "0 \<le> f x \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>return_pmf x) = f x"
  unfolding return_pmf.rep_eq by (intro nn_integral_return) auto

lemma emeasure_return_pmf[simp]: "emeasure (return_pmf x) X = indicator X x"
  unfolding return_pmf.rep_eq by (intro emeasure_return) auto

end

definition "bind_pmf M f = join_pmf (map_pmf f M)"

lemma (in pmf_as_measure) bind_transfer[transfer_rule]:
  "rel_fun pmf_as_measure.cr_pmf (rel_fun (rel_fun op = pmf_as_measure.cr_pmf) pmf_as_measure.cr_pmf) op \<guillemotright>= bind_pmf"
proof (auto simp: pmf_as_measure.cr_pmf_def rel_fun_def bind_pmf_def join_pmf.rep_eq map_pmf.rep_eq)
  fix M f and g :: "'a \<Rightarrow> 'b pmf" assume "\<forall>x. f x = measure_pmf (g x)"
  then have f: "f = (\<lambda>x. measure_pmf (g x))"
    by auto
  show "measure_pmf M \<guillemotright>= f = distr (measure_pmf M) (count_space UNIV) g \<guillemotright>= measure_pmf"
    unfolding f by (subst bind_distr[OF _ measurable_measure_pmf]) auto
qed

lemma pmf_bind: "pmf (bind_pmf N f) i = (\<integral>x. pmf (f x) i \<partial>measure_pmf N)"
  by (auto intro!: integral_distr simp: bind_pmf_def pmf_join map_pmf.rep_eq)

lemma bind_return_pmf: "bind_pmf (return_pmf x) f = f x"
  unfolding bind_pmf_def map_return_pmf join_return_pmf ..

lemma join_eq_bind_pmf: "join_pmf M = bind_pmf M id"
  by (simp add: bind_pmf_def)

lemma bind_pmf_const[simp]: "bind_pmf M (\<lambda>x. c) = c"
  unfolding bind_pmf_def map_pmf_const join_return_pmf ..

lemma set_bind_pmf: "set_pmf (bind_pmf M N) = (\<Union>M\<in>set_pmf M. set_pmf (N M))"
  apply (simp add: set_eq_iff set_pmf_iff pmf_bind)
  apply (subst integral_nonneg_eq_0_iff_AE)
  apply (auto simp: pmf_nonneg pmf_le_1 AE_measure_pmf_iff
              intro!: measure_pmf.integrable_const_bound[where B=1])
  done

lemma measurable_pair_restrict_pmf2:
  assumes "countable A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> (\<lambda>x. f (x, y)) \<in> measurable M L"
  shows "f \<in> measurable (M \<Otimes>\<^sub>M restrict_space (measure_pmf N) A) L"
  apply (subst measurable_cong_sets)
  apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
  apply (simp_all add: restrict_count_space)
  apply (subst split_eta[symmetric])
  unfolding measurable_split_conv
  apply (rule measurable_compose_countable'[OF _ measurable_snd `countable A`])
  apply (rule measurable_compose[OF measurable_fst])
  apply fact
  done

lemma measurable_pair_restrict_pmf1:
  assumes "countable A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) \<in> measurable N L"
  shows "f \<in> measurable (restrict_space (measure_pmf M) A \<Otimes>\<^sub>M N) L"
  apply (subst measurable_cong_sets)
  apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
  apply (simp_all add: restrict_count_space)
  apply (subst split_eta[symmetric])
  unfolding measurable_split_conv
  apply (rule measurable_compose_countable'[OF _ measurable_fst `countable A`])
  apply (rule measurable_compose[OF measurable_snd])
  apply fact
  done
                                
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


context
begin

interpretation pmf_as_measure .

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

lemma bind_return_pmf': "bind_pmf N return_pmf = N"
proof (transfer, clarify)
  fix N :: "'a measure" assume "sets N = UNIV" then show "N \<guillemotright>= return (count_space UNIV) = N"
    by (subst return_sets_cong[where N=N]) (simp_all add: bind_return')
qed

lemma bind_return_pmf'': "bind_pmf N (\<lambda>x. return_pmf (f x)) = map_pmf f N"
proof (transfer, clarify)
  fix N :: "'b measure" and f :: "'b \<Rightarrow> 'a" assume "prob_space N" "sets N = UNIV"
  then show "N \<guillemotright>= (\<lambda>x. return (count_space UNIV) (f x)) = distr N (count_space UNIV) f"
    by (subst bind_return_distr[symmetric])
       (auto simp: prob_space.not_empty measurable_def comp_def)
qed

lemma bind_assoc_pmf: "bind_pmf (bind_pmf A B) C = bind_pmf A (\<lambda>x. bind_pmf (B x) C)"
  by transfer
     (auto intro!: bind_assoc[where N="count_space UNIV" and R="count_space UNIV"]
           simp: measurable_def space_subprob_algebra prob_space_imp_subprob_space)

end

lemma map_join_pmf: "map_pmf f (join_pmf AA) = join_pmf (map_pmf (map_pmf f) AA)"
  unfolding bind_pmf_def[symmetric]
  unfolding bind_return_pmf''[symmetric] join_eq_bind_pmf bind_assoc_pmf
  by (simp add: bind_return_pmf'')

definition "pair_pmf A B = bind_pmf A (\<lambda>x. bind_pmf B (\<lambda>y. return_pmf (x, y)))"

lemma pmf_pair: "pmf (pair_pmf M N) (a, b) = pmf M a * pmf N b"
  unfolding pair_pmf_def pmf_bind pmf_return
  apply (subst integral_measure_pmf[where A="{b}"])
  apply (auto simp: indicator_eq_0_iff)
  apply (subst integral_measure_pmf[where A="{a}"])
  apply (auto simp: indicator_eq_0_iff setsum_nonneg_eq_0_iff pmf_nonneg)
  done

lemma set_pair_pmf: "set_pmf (pair_pmf A B) = set_pmf A \<times> set_pmf B"
  unfolding pair_pmf_def set_bind_pmf set_return_pmf by auto

lemma measure_pmf_in_subprob_space[measurable (raw)]:
  "measure_pmf M \<in> space (subprob_algebra (count_space UNIV))"
  by (simp add: space_subprob_algebra) intro_locales

lemma nn_integral_pair_pmf': "(\<integral>\<^sup>+x. f x \<partial>pair_pmf A B) = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. f (a, b) \<partial>B \<partial>A)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>pair_pmf A B) = (\<integral>\<^sup>+x. max 0 (f x) * indicator (A \<times> B) x \<partial>pair_pmf A B)"
    by (subst nn_integral_max_0[symmetric])
       (auto simp: AE_measure_pmf_iff set_pair_pmf intro!: nn_integral_cong_AE)
  also have "\<dots> = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. max 0 (f (a, b)) * indicator (A \<times> B) (a, b) \<partial>B \<partial>A)"
    by (simp add: pair_pmf_def)
  also have "\<dots> = (\<integral>\<^sup>+a. \<integral>\<^sup>+b. max 0 (f (a, b)) \<partial>B \<partial>A)"
    by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
  finally show ?thesis
    unfolding nn_integral_max_0 .
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
      nn_integral_measure_pmf_finite set_return_pmf emeasure_nonneg pmf_return one_ereal_def[symmetric])
    apply (subst emeasure_bind[OF _ _ X])
    apply measurable
    apply (subst emeasure_bind[OF _ _ X])
    apply measurable
    done
qed

lemma join_map_return_pmf: "join_pmf (map_pmf return_pmf A) = A"
  unfolding bind_pmf_def[symmetric] bind_return_pmf' ..

lemma map_fst_pair_pmf: "map_pmf fst (pair_pmf A B) = A"
  by (simp add: pair_pmf_def bind_return_pmf''[symmetric] bind_assoc_pmf bind_return_pmf bind_return_pmf')

lemma map_snd_pair_pmf: "map_pmf snd (pair_pmf A B) = B"
  by (simp add: pair_pmf_def bind_return_pmf''[symmetric] bind_assoc_pmf bind_return_pmf bind_return_pmf')

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
  by (auto simp: pmf.rep_eq map_pmf.rep_eq measure_distr AE_measure_pmf_iff inj_onD
           intro!: measure_pmf.finite_measure_eq_AE)

inductive rel_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf \<Rightarrow> bool"
for R p q
where
  "\<lbrakk> \<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y; 
     map_pmf fst pq = p; map_pmf snd pq = q \<rbrakk>
  \<Longrightarrow> rel_pmf R p q"

lemma nn_integral_count_space_eq:
  "(\<And>x. x \<in> A - B \<Longrightarrow> f x = 0) \<Longrightarrow> (\<And>x. x \<in> B - A \<Longrightarrow> f x = 0) \<Longrightarrow>
    (\<integral>\<^sup>+x. f x \<partial>count_space A) = (\<integral>\<^sup>+x. f x \<partial>count_space B)"
  by (auto simp: nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)

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

    note pmf_nonneg[intro, simp]
    let ?pq = "\<lambda>y x. pmf pq (x, y)"
    let ?qr = "\<lambda>y z. pmf qr (y, z)"

    have nn_integral_pp2: "\<And>y. (\<integral>\<^sup>+ x. ?pq y x \<partial>count_space UNIV) = pmf q y"
      by (simp add: nn_integral_pmf' inj_on_def q)
         (auto simp add: ereal_pmf_map intro!: arg_cong2[where f=emeasure])
    have nn_integral_rr1: "\<And>y. (\<integral>\<^sup>+ x. ?qr y x \<partial>count_space UNIV) = pmf q y"
      by (simp add: nn_integral_pmf' inj_on_def q')
         (auto simp add: ereal_pmf_map intro!: arg_cong2[where f=emeasure])
    have eq: "\<And>y. (\<integral>\<^sup>+ x. ?pq y x \<partial>count_space UNIV) = (\<integral>\<^sup>+ z. ?qr y z \<partial>count_space UNIV)"
      by(simp add: nn_integral_pp2 nn_integral_rr1)

    def assign \<equiv> "\<lambda>y x z. ?pq y x * ?qr y z / pmf q y"
    have assign_nonneg [simp]: "\<And>y x z. 0 \<le> assign y x z" by(simp add: assign_def)
    have assign_eq_0_outside: "\<And>y x z. \<lbrakk> ?pq y x = 0 \<or> ?qr y z = 0 \<rbrakk> \<Longrightarrow> assign y x z = 0"
      by(auto simp add: assign_def)
    have nn_integral_assign1: "\<And>y z. (\<integral>\<^sup>+ x. assign y x z \<partial>count_space UNIV) = ?qr y z"
    proof -
      fix y z
      have "(\<integral>\<^sup>+ x. assign y x z \<partial>count_space UNIV) = 
            (\<integral>\<^sup>+ x. ?pq y x \<partial>count_space UNIV) * (?qr y z / pmf q y)"
        by(simp add: assign_def nn_integral_multc times_ereal.simps(1)[symmetric] divide_real_def mult.assoc del: times_ereal.simps(1))
      also have "\<dots> = ?qr y z" by(auto simp add: image_iff q' pmf_eq_0_set_pmf set_map_pmf nn_integral_pp2)
      finally show "?thesis y z" .
    qed
    have nn_integral_assign2: "\<And>y x. (\<integral>\<^sup>+ z. assign y x z \<partial>count_space UNIV) = ?pq y x"
    proof -
      fix x y
      have "(\<integral>\<^sup>+ z. assign y x z \<partial>count_space UNIV) = (\<integral>\<^sup>+ z. ?qr y z \<partial>count_space UNIV) * (?pq y x / pmf q y)"
        by(simp add: assign_def divide_real_def mult.commute[where a="?pq y x"] mult.assoc nn_integral_multc times_ereal.simps(1)[symmetric] del: times_ereal.simps(1))
      also have "\<dots> = ?pq y x" by(auto simp add: image_iff pmf_eq_0_set_pmf set_map_pmf q nn_integral_rr1)
      finally show "?thesis y x" .
    qed

    def pqr \<equiv> "embed_pmf (\<lambda>(y, x, z). assign y x z)"
    { fix y x z
      have "assign y x z = pmf pqr (y, x, z)"
        unfolding pqr_def
      proof (subst pmf_embed_pmf)
        have "(\<integral>\<^sup>+ x. ereal ((\<lambda>(y, x, z). assign y x z) x) \<partial>count_space UNIV) =
          (\<integral>\<^sup>+ x. ereal ((\<lambda>(y, x, z). assign y x z) x) \<partial>(count_space ((\<lambda>((x, y), z). (y, x, z)) ` (pq \<times> r))))"
          by (force simp add: pmf_eq_0_set_pmf r set_map_pmf split: split_indicator
                    intro!: nn_integral_count_space_eq assign_eq_0_outside)
        also have "\<dots> = (\<integral>\<^sup>+ x. ereal ((\<lambda>((x, y), z). assign y x z) x) \<partial>(count_space (pq \<times> r)))"
          by (subst nn_integral_bij_count_space[OF inj_on_imp_bij_betw, symmetric])
             (auto simp: inj_on_def intro!: nn_integral_cong)
        also have "\<dots> = (\<integral>\<^sup>+ xy. \<integral>\<^sup>+z. ereal ((\<lambda>((x, y), z). assign y x z) (xy, z)) \<partial>count_space r \<partial>count_space pq)"
          by (subst sigma_finite_measure.nn_integral_fst)
             (auto simp: pair_measure_countable sigma_finite_measure_count_space_countable)
        also have "\<dots> = (\<integral>\<^sup>+ xy. \<integral>\<^sup>+z. ereal ((\<lambda>((x, y), z). assign y x z) (xy, z)) \<partial>count_space UNIV \<partial>count_space pq)"
          by (intro nn_integral_cong nn_integral_count_space_eq)
             (force simp: r set_map_pmf pmf_eq_0_set_pmf intro!: assign_eq_0_outside)+
        also have "\<dots> = (\<integral>\<^sup>+ z. ?pq (snd z) (fst z) \<partial>count_space pq)"
          by (subst nn_integral_assign2[symmetric]) (auto intro!: nn_integral_cong)
        finally show "(\<integral>\<^sup>+ x. ereal ((\<lambda>(y, x, z). assign y x z) x) \<partial>count_space UNIV) = 1"
          by (simp add: nn_integral_pmf emeasure_pmf)
      qed auto }
    note a = this

    def pr \<equiv> "map_pmf (\<lambda>(y, x, z). (x, z)) pqr"

    have "rel_pmf (R OO S) p r"
    proof
      have pq_eq: "pq = map_pmf (\<lambda>(y, x, z). (x, y)) pqr"
      proof (rule pmf_eqI)
        fix i
        show "pmf pq i = pmf (map_pmf (\<lambda>(y, x, z). (x, y)) pqr) i"
          using nn_integral_assign2[of "snd i" "fst i", symmetric]
          by (auto simp add: a nn_integral_pmf' inj_on_def ereal.inject[symmetric] ereal_pmf_map 
                   simp del: ereal.inject intro!: arg_cong2[where f=emeasure])
      qed
      then show "map_pmf fst pr = p"
        unfolding p pr_def by (simp add: map_pmf_comp split_beta)

      have qr_eq: "qr = map_pmf (\<lambda>(y, x, z). (y, z)) pqr"
      proof (rule pmf_eqI)
        fix i show "pmf qr i = pmf (map_pmf (\<lambda>(y, x, z). (y, z)) pqr) i"
          using nn_integral_assign1[of "fst i" "snd i", symmetric]
          by (auto simp add: a nn_integral_pmf' inj_on_def ereal.inject[symmetric] ereal_pmf_map 
                   simp del: ereal.inject intro!: arg_cong2[where f=emeasure])
      qed
      then show "map_pmf snd pr = r"
        unfolding r pr_def by (simp add: map_pmf_comp split_beta)

      fix x z assume "(x, z) \<in> set_pmf pr"
      then have "\<exists>y. (x, y) \<in> set_pmf pq \<and> (y, z) \<in> set_pmf qr"
        unfolding pr_def pq_eq qr_eq by (force simp: set_map_pmf)
      with pq qr show "(R OO S) x z"
        by blast
    qed }
  then show "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
    by(auto simp add: le_fun_def)
qed (fact natLeq_card_order natLeq_cinfinite)+

lemma rel_pmf_return_pmf1: "rel_pmf R (return_pmf x) M \<longleftrightarrow> (\<forall>a\<in>M. R x a)"
proof safe
  fix a assume "a \<in> M" "rel_pmf R (return_pmf x) M"
  then obtain pq where *: "\<And>a b. (a, b) \<in> set_pmf pq \<Longrightarrow> R a b"
    and eq: "return_pmf x = map_pmf fst pq" "M = map_pmf snd pq"
    by (force elim: rel_pmf.cases)
  moreover have "set_pmf (return_pmf x) = {x}"
    by (simp add: set_return_pmf)
  with `a \<in> M` have "(x, a) \<in> pq"
    by (force simp: eq set_map_pmf)
  with * show "R x a"
    by auto
qed (auto intro!: rel_pmf.intros[where pq="pair_pmf (return_pmf x) M"]
          simp: map_fst_pair_pmf map_snd_pair_pmf set_pair_pmf set_return_pmf)

lemma rel_pmf_return_pmf2: "rel_pmf R M (return_pmf x) \<longleftrightarrow> (\<forall>a\<in>M. R a x)"
  by (subst pmf.rel_flip[symmetric]) (simp add: rel_pmf_return_pmf1)

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
      by (auto simp: set_map_pmf)
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
      by (auto simp: set_map_pmf)
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
       (auto simp: map_snd_pair_pmf map_fst_pair_pmf set_pair_pmf set_map_pmf map_pmf_comp Rpq Spq
                   map_pair)
qed

end

