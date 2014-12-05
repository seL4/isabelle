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

end

subsection {* Monad interpretation *}

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

    def A \<equiv> "\<lambda>y. {x. (x, y) \<in> set_pmf pq}"
    then have "\<And>y. A y \<subseteq> set_pmf p" by (auto simp add: p set_map_pmf intro: rev_image_eqI)
    then have [simp]: "\<And>y. countable (A y)" by (rule countable_subset) simp
    have A: "\<And>x y. (x, y) \<in> set_pmf pq \<longleftrightarrow> x \<in> A y"
      by (simp add: A_def)

    let ?P = "\<lambda>y. to_nat_on (A y)"
    def pp \<equiv> "map_pmf (\<lambda>(x, y). (y, ?P y x)) pq"
    let ?pp = "\<lambda>y x. pmf pp (y, x)"
    { fix x y have "x \<in> A y \<Longrightarrow> pmf pp (y, ?P y x) = pmf pq (x, y)"
        unfolding pp_def
        by (intro pmf_map_inj[of "\<lambda>(x, y). (y, ?P y x)" pq "(x, y)", simplified])
           (auto simp: inj_on_def A) }
    note pmf_pp = this

    def B \<equiv> "\<lambda>y. {z. (y, z) \<in> set_pmf qr}"
    then have "\<And>y. B y \<subseteq> set_pmf r" by (auto simp add: r set_map_pmf intro: rev_image_eqI)
    then have [simp]: "\<And>y. countable (B y)" by (rule countable_subset) simp
    have B: "\<And>y z. (y, z) \<in> set_pmf qr \<longleftrightarrow> z \<in> B y"
      by (simp add: B_def)

    let ?R = "\<lambda>y. to_nat_on (B y)"
    def rr \<equiv> "map_pmf (\<lambda>(y, z). (y, ?R y z)) qr"
    let ?rr = "\<lambda>y z. pmf rr (y, z)"
    { fix y z have "z \<in> B y \<Longrightarrow> pmf rr (y, ?R y z) = pmf qr (y, z)"
        unfolding rr_def
        by (intro pmf_map_inj[of "\<lambda>(y, z). (y, ?R y z)" qr "(y, z)", simplified])
           (auto simp: inj_on_def B) }
    note pmf_rr = this

    have eq: "\<And>y. (\<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV) = (\<integral>\<^sup>+ z. ?rr y z \<partial>count_space UNIV)"
    proof -
      fix y
      have "(\<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV) = pmf q y"
        by (simp add: nn_integral_pmf' inj_on_def pp_def q)
           (auto simp add: ereal_pmf_map intro!: arg_cong2[where f=emeasure])
      also have "\<dots> = (\<integral>\<^sup>+ x. ?rr y x \<partial>count_space UNIV)"
        by (simp add: nn_integral_pmf' inj_on_def rr_def q')
           (auto simp add: ereal_pmf_map intro!: arg_cong2[where f=emeasure])
      finally show "?thesis y" .
    qed

    def assign_aux \<equiv> "\<lambda>y remainder start weight z.
       if z < start then 0
       else if z = start then min weight remainder
       else if remainder + setsum (?rr y) {Suc start ..<z} < weight then min (weight - remainder - setsum (?rr y) {Suc start..<z}) (?rr y z) else 0"
    hence assign_aux_alt_def: "\<And>y remainder start weight z. assign_aux y remainder start weight z = 
       (if z < start then 0
        else if z = start then min weight remainder
        else if remainder + setsum (?rr y) {Suc start ..<z} < weight then min (weight - remainder - setsum (?rr y) {Suc start..<z}) (?rr y z) else 0)"
       by simp
    { fix y and remainder :: real and start and weight :: real
      assume weight_nonneg: "0 \<le> weight"
      let ?assign_aux = "assign_aux y remainder start weight"
      { fix z
        have "setsum ?assign_aux {..<z} =
           (if z \<le> start then 0 else if remainder + setsum (?rr y) {Suc start..<z} < weight then remainder + setsum (?rr y) {Suc start..<z} else weight)"
        proof(induction z)
          case (Suc z) show ?case
            by (auto simp add: Suc.IH assign_aux_alt_def[where z=z] not_less)
               (metis add.commute add.left_commute add_increasing pmf_nonneg)
        qed(auto simp add: assign_aux_def) }
      note setsum_start_assign_aux = this
      moreover {
        assume remainder_nonneg: "0 \<le> remainder"
        have [simp]: "\<And>z. 0 \<le> ?assign_aux z"
          by(simp add: assign_aux_def weight_nonneg remainder_nonneg)
        moreover have "\<And>z. \<lbrakk> ?rr y z = 0; remainder \<le> ?rr y start \<rbrakk> \<Longrightarrow> ?assign_aux z = 0"
          using remainder_nonneg weight_nonneg
          by(auto simp add: assign_aux_def min_def)
        moreover have "(\<integral>\<^sup>+ z. ?assign_aux z \<partial>count_space UNIV) = 
          min weight (\<integral>\<^sup>+ z. (if z < start then 0 else if z = start then remainder else ?rr y z) \<partial>count_space UNIV)"
          (is "?lhs = ?rhs" is "_ = min _ (\<integral>\<^sup>+ y. ?f y \<partial>_)")
        proof -
          have "?lhs = (SUP n. \<Sum>z<n. ereal (?assign_aux z))"
            by(simp add: nn_integral_count_space_nat suminf_ereal_eq_SUP)
          also have "\<dots> = (SUP n. min weight (\<Sum>z<n. ?f z))"
          proof(rule arg_cong2[where f=SUPREMUM] ext refl)+
            fix n
            have "(\<Sum>z<n. ereal (?assign_aux z)) = min weight ((if n > start then remainder else 0) + setsum ?f {Suc start..<n})"
              using weight_nonneg remainder_nonneg by(simp add: setsum_start_assign_aux min_def)
            also have "\<dots> = min weight (setsum ?f {start..<n})"
              by(simp add: setsum_head_upt_Suc)
            also have "\<dots> = min weight (setsum ?f {..<n})"
              by(intro arg_cong2[where f=min] setsum.mono_neutral_left) auto
            finally show "(\<Sum>z<n. ereal (?assign_aux z)) = \<dots>" .
          qed
          also have "\<dots> = min weight (SUP n. setsum ?f {..<n})"
            unfolding inf_min[symmetric] by(subst inf_SUP) simp
          also have "\<dots> = ?rhs"
            by(simp add: nn_integral_count_space_nat suminf_ereal_eq_SUP remainder_nonneg)
          finally show ?thesis .
        qed
        moreover note calculation }
      moreover note calculation }
    note setsum_start_assign_aux = this(1)
      and assign_aux_nonneg [simp] = this(2)
      and assign_aux_eq_0_outside = this(3)
      and nn_integral_assign_aux = this(4)
    { fix y and remainder :: real and start target
      have "setsum (?rr y) {Suc start..<target} \<ge> 0" by (simp add: setsum_nonneg)
      moreover assume "0 \<le> remainder"
      ultimately have "assign_aux y remainder start 0 target = 0"
        by(auto simp add: assign_aux_def min_def) }
    note assign_aux_weight_0 [simp] = this

    def find_start \<equiv> "\<lambda>y weight. if \<exists>n. weight \<le> setsum (?rr y)  {..n} then Some (LEAST n. weight \<le> setsum (?rr y) {..n}) else None"
    have find_start_eq_Some_above:
      "\<And>y weight n. find_start y weight = Some n \<Longrightarrow> weight \<le> setsum (?rr y) {..n}"
      by(drule sym)(auto simp add: find_start_def split: split_if_asm intro: LeastI)
    { fix y weight n
      assume find_start: "find_start y weight = Some n"
      and weight: "0 \<le> weight"
      have "setsum (?rr y) {..n} \<le> ?rr y n + weight"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?rr y n + weight < setsum (?rr y) {..n}" by simp
        moreover with weight obtain n' where "n = Suc n'" by(cases n) auto
        ultimately have "weight \<le> setsum (?rr y) {..n'}" by simp
        hence "(LEAST n. weight \<le> setsum (?rr y) {..n}) \<le> n'" by(rule Least_le)
        moreover from find_start have "n = (LEAST n. weight \<le> setsum (?rr y) {..n})"
          by(auto simp add: find_start_def split: split_if_asm)
        ultimately show False using \<open>n = Suc n'\<close> by auto
      qed }
    note find_start_eq_Some_least = this
    have find_start_0 [simp]: "\<And>y. find_start y 0 = Some 0"
      by(auto simp add: find_start_def intro!: exI[where x=0])
    { fix y and weight :: real
      assume "weight < \<integral>\<^sup>+ z. ?rr y z \<partial>count_space UNIV"
      also have "(\<integral>\<^sup>+ z. ?rr y z \<partial>count_space UNIV) = (SUP n. \<Sum>z<n. ereal (?rr y z))"
        by(simp add: nn_integral_count_space_nat suminf_ereal_eq_SUP)
      finally obtain n where "weight < (\<Sum>z<n. ?rr y z)" by(auto simp add: less_SUP_iff)
      hence "weight \<in> dom (find_start y)"
        by(auto simp add: find_start_def)(meson atMost_iff finite_atMost lessThan_iff less_imp_le order_trans pmf_nonneg setsum_mono3 subsetI) }
    note in_dom_find_startI = this
    { fix y and w w' :: real and m
      let ?m' = "LEAST m. w' \<le> setsum (?rr y) {..m}"
      assume "w' \<le> w"
      also  assume "find_start y w = Some m"
      hence "w \<le> setsum (?rr y) {..m}" by(rule find_start_eq_Some_above)
      finally have "find_start y w' = Some ?m'" by(auto simp add: find_start_def)
      moreover from \<open>w' \<le> setsum (?rr y) {..m}\<close> have "?m' \<le> m" by(rule Least_le)
      ultimately have "\<exists>m'. find_start y w' = Some m' \<and> m' \<le> m" by blast }
    note find_start_mono = this[rotated]

    def assign \<equiv> "\<lambda>y x z. let used = setsum (?pp y) {..<x}
      in case find_start y used of None \<Rightarrow> 0
         | Some start \<Rightarrow> assign_aux y (setsum (?rr y) {..start} - used) start (?pp y x) z"
    hence assign_alt_def: "\<And>y x z. assign y x z = 
      (let used = setsum (?pp y) {..<x}
       in case find_start y used of None \<Rightarrow> 0
          | Some start \<Rightarrow> assign_aux y (setsum (?rr y) {..start} - used) start (?pp y x) z)"
      by simp
    have assign_nonneg [simp]: "\<And>y x z. 0 \<le> assign y x z"
      by(simp add: assign_def diff_le_iff find_start_eq_Some_above Let_def split: option.split)
    have assign_eq_0_outside: "\<And>y x z. \<lbrakk> ?pp y x = 0 \<or> ?rr y z = 0 \<rbrakk> \<Longrightarrow> assign y x z = 0"
      by(auto simp add: assign_def assign_aux_eq_0_outside diff_le_iff find_start_eq_Some_above find_start_eq_Some_least setsum_nonneg Let_def split: option.split)

    { fix y x z
      have "(\<Sum>n<Suc x. assign y n z) =
            (case find_start y (setsum (?pp y) {..<x}) of None \<Rightarrow> ?rr y z
             | Some m \<Rightarrow> if z < m then ?rr y z 
                         else min (?rr y z) (max 0 (setsum (?pp y) {..<x} + ?pp y x - setsum (?rr y) {..<z})))"
        (is "?lhs x = ?rhs x")
      proof(induction x)
        case 0 thus ?case 
          by(auto simp add: assign_def assign_aux_def setsum_head_upt_Suc atLeast0LessThan[symmetric] not_less field_simps max_def)
      next
        case (Suc x)
        have "?lhs (Suc x) = ?lhs x + assign y (Suc x) z" by simp
        also have "?lhs x = ?rhs x" by(rule Suc.IH)
        also have "?rhs x + assign y (Suc x) z = ?rhs (Suc x)"
        proof(cases "find_start y (setsum (?pp y) {..<Suc x})")
          case None
          thus ?thesis
            by(auto split: option.split simp add: assign_def min_def max_def diff_le_iff setsum_nonneg not_le field_simps)
              (metis add.commute add_increasing find_start_def lessThan_Suc_atMost less_imp_le option.distinct(1) setsum_lessThan_Suc)+
        next 
          case (Some m)
          have [simp]: "setsum (?rr y) {..m} = ?rr y m + setsum (?rr y) {..<m}"
            by(simp add: ivl_disj_un(2)[symmetric])
          from Some obtain m' where m': "find_start y (setsum (?pp y) {..<x}) = Some m'" "m' \<le> m"
            by(auto dest: find_start_mono[where w'2="setsum (?pp y) {..<x}"])
          moreover {
            assume "z < m"
            then have "setsum (?rr y) {..z} \<le> setsum (?rr y) {..<m}"
              by(auto intro: setsum_mono3)
            also have "\<dots> \<le> setsum (?pp y) {..<Suc x}" using find_start_eq_Some_least[OF Some]
              by(simp add: ivl_disj_un(2)[symmetric] setsum_nonneg)
            finally have "?rr y z \<le> max 0 (setsum (?pp y) {..<x} + ?pp y x - setsum (?rr y) {..<z})"
              by(auto simp add: ivl_disj_un(2)[symmetric] max_def diff_le_iff simp del: pmf_le_0_iff)
          } moreover {
            assume "m \<le> z"
            have "setsum (?pp y) {..<Suc x} \<le> setsum (?rr y) {..m}"
              using Some by(rule find_start_eq_Some_above)
            also have "\<dots> \<le> setsum (?rr y) {..<Suc z}" using \<open>m \<le> z\<close> by(intro setsum_mono3) auto
            finally have "max 0 (setsum (?pp y) {..<x} + ?pp y x - setsum (?rr y) {..<z}) \<le> ?rr y z" by simp
            moreover have "z \<noteq> m \<Longrightarrow> setsum (?rr y) {..m} + setsum (?rr y) {Suc m..<z} = setsum (?rr y) {..<z}"
              using \<open>m \<le> z\<close>
              by(subst ivl_disj_un(8)[where l="Suc m", symmetric])
                (simp_all add: setsum_Un ivl_disj_un(2)[symmetric] setsum.neutral)
            moreover note calculation
          } moreover {
            assume "m < z"
            have "setsum (?pp y) {..<Suc x} \<le> setsum (?rr y) {..m}"
              using Some by(rule find_start_eq_Some_above)
            also have "\<dots> \<le> setsum (?rr y) {..<z}" using \<open>m < z\<close> by(intro setsum_mono3) auto
            finally have "max 0 (setsum (?pp y) {..<Suc x} - setsum (?rr y) {..<z}) = 0" by simp }
          moreover have "setsum (?pp y) {..<Suc x} \<ge> setsum (?rr y) {..<m}"
            using find_start_eq_Some_least[OF Some]
            by(simp add: setsum_nonneg ivl_disj_un(2)[symmetric])
          moreover hence "setsum (?pp y) {..<Suc (Suc x)} \<ge> setsum (?rr y) {..<m}"
            by(fastforce intro: order_trans)
          ultimately show ?thesis using Some
            by(auto simp add: assign_def assign_aux_def Let_def field_simps max_def)
        qed
        finally show ?case .
      qed }
    note setsum_assign = this

    have nn_integral_assign1: "\<And>y z. (\<integral>\<^sup>+ x. assign y x z \<partial>count_space UNIV) = ?rr y z"
    proof -
      fix y z
      have "(\<integral>\<^sup>+ x. assign y x z \<partial>count_space UNIV) = (SUP n. ereal (\<Sum>x<n. assign y x z))"
        by(simp add: nn_integral_count_space_nat suminf_ereal_eq_SUP)
      also have "\<dots> = ?rr y z"
      proof(rule antisym)
        show "(SUP n. ereal (\<Sum>x<n. assign y x z)) \<le> ?rr y z"
        proof(rule SUP_least)
          fix n
          show "ereal (\<Sum>x<n. (assign y x z)) \<le> ?rr y z"
            using setsum_assign[of y z "n - 1"]
            by(cases n)(simp_all split: option.split)
        qed
        show "?rr y z \<le> (SUP n. ereal (\<Sum>x<n. assign y x z))"
        proof(cases "setsum (?rr y) {..z} < \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV")
          case True
          then obtain n where "setsum (?rr y) {..z} < setsum (?pp y) {..<n}"
            by(auto simp add: nn_integral_count_space_nat suminf_ereal_eq_SUP less_SUP_iff)
          moreover have "\<And>k. k < z \<Longrightarrow> setsum (?rr y) {..k} \<le> setsum (?rr y) {..<z}"
            by(auto intro: setsum_mono3)
          ultimately have "?rr y z \<le> (\<Sum>x<Suc n. assign y x z)"
            by(subst setsum_assign)(auto split: option.split dest!: find_start_eq_Some_above simp add: ivl_disj_un(2)[symmetric] add.commute add_increasing le_diff_eq le_max_iff_disj)
          also have "\<dots> \<le> (SUP n. ereal (\<Sum>x<n. assign y x z))" 
            by(rule SUP_upper) simp
          finally show ?thesis by simp
        next
          case False
          have "setsum (?rr y) {..z} = \<integral>\<^sup>+ z. ?rr y z \<partial>count_space {..z}"
            by(simp add: nn_integral_count_space_finite max_def)
          also have "\<dots> \<le> \<integral>\<^sup>+ z. ?rr y z \<partial>count_space UNIV"
            by(auto simp add: nn_integral_count_space_indicator indicator_def intro: nn_integral_mono)
          also have "\<dots> = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV" by(simp add: eq)
          finally have *: "setsum (?rr y) {..z} = \<dots>" using False by simp
          also have "\<dots> = (SUP n. ereal (\<Sum>x<n. ?pp y x))"
            by(simp add: nn_integral_count_space_nat suminf_ereal_eq_SUP)
          also have "\<dots> \<le> (SUP n. ereal (\<Sum>x<n. assign y x z)) + setsum (?rr y) {..<z}"
          proof(rule SUP_least)
            fix n
            have "setsum (?pp y) {..<n} = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space {..<n}"
              by(simp add: nn_integral_count_space_finite max_def)
            also have "\<dots> \<le> \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV"
              by(auto simp add: nn_integral_count_space_indicator indicator_def intro: nn_integral_mono)
            also have "\<dots> = setsum (?rr y) {..z}" using * by simp
            finally obtain k where k: "find_start y (setsum (?pp y) {..<n}) = Some k"
              by(fastforce simp add: find_start_def)
            with \<open>ereal (setsum (?pp y) {..<n}) \<le> setsum (?rr y) {..z}\<close>
            have "k \<le> z" by(auto simp add: find_start_def split: split_if_asm intro: Least_le)
            then have "setsum (?pp y) {..<n} - setsum (?rr y) {..<z} \<le> ereal (\<Sum>x<Suc n. assign y x z)"
              using \<open>ereal (setsum (?pp y) {..<n}) \<le> setsum (?rr y) {..z}\<close>
              apply (subst setsum_assign)
              apply (auto simp add: field_simps max_def k ivl_disj_un(2)[symmetric])
              apply (meson add_increasing le_cases pmf_nonneg)
              done
            also have "\<dots> \<le> (SUP n. ereal (\<Sum>x<n. assign y x z))"
              by(rule SUP_upper) simp
            finally show "ereal (\<Sum>x<n. ?pp y x) \<le> \<dots> + setsum (?rr y) {..<z}" 
              by(simp add: ereal_minus(1)[symmetric] ereal_minus_le del: ereal_minus(1))
          qed
          finally show ?thesis
            by(simp add: ivl_disj_un(2)[symmetric] plus_ereal.simps(1)[symmetric] ereal_add_le_add_iff2 del: plus_ereal.simps(1))
        qed
      qed
      finally show "?thesis y z" .
    qed

    { fix y x
      have "(\<integral>\<^sup>+ z. assign y x z \<partial>count_space UNIV) = ?pp y x"
      proof(cases "setsum (?pp y) {..<x} = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV")
        case False
        let ?used = "setsum (?pp y) {..<x}"
        have "?used = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space {..<x}"
          by(simp add: nn_integral_count_space_finite max_def)
        also have "\<dots> \<le> \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV"
          by(auto simp add: nn_integral_count_space_indicator indicator_def intro!: nn_integral_mono)
        finally have "?used < \<dots>" using False by auto
        also note eq finally have "?used \<in> dom (find_start y)" by(rule in_dom_find_startI)
        then obtain k where k: "find_start y ?used = Some k" by auto
        let ?f = "\<lambda>z. if z < k then 0 else if z = k then setsum (?rr y) {..k} - ?used else ?rr y z"
        let ?g = "\<lambda>x'. if x' < x then 0 else ?pp y x'"
        have "?pp y x = ?g x" by simp
        also have "?g x \<le> \<integral>\<^sup>+ x'. ?g x' \<partial>count_space UNIV" by(rule nn_integral_ge_point) simp
        also {
          have "?used = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space {..<x}"
            by(simp add: nn_integral_count_space_finite max_def)
          also have "\<dots> = \<integral>\<^sup>+ x'. (if x' < x then ?pp y x' else 0) \<partial>count_space UNIV"
            by(simp add: nn_integral_count_space_indicator indicator_def if_distrib zero_ereal_def cong del: if_cong)
          also have "(\<integral>\<^sup>+ x'. ?g x' \<partial>count_space UNIV) + \<dots> = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV"
            by(subst nn_integral_add[symmetric])(auto intro: nn_integral_cong)
          also note calculation }
        ultimately have "ereal (?pp y x) + ?used \<le> \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV"
          by (metis (no_types, lifting) ereal_add_mono order_refl)
        also note eq
        also have "(\<integral>\<^sup>+ z. ?rr y z \<partial>count_space UNIV) = (\<integral>\<^sup>+ z. ?f z \<partial>count_space UNIV) + (\<integral>\<^sup>+ z. (if z < k then ?rr y z else if z = k then ?used - setsum (?rr y) {..<k} else 0) \<partial>count_space UNIV)"
          using k by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong simp add: ivl_disj_un(2)[symmetric] setsum_nonneg dest: find_start_eq_Some_least find_start_eq_Some_above)
        also have "(\<integral>\<^sup>+ z. (if z < k then ?rr y z else if z = k then ?used - setsum (?rr y) {..<k} else 0) \<partial>count_space UNIV) =
          (\<integral>\<^sup>+ z. (if z < k then ?rr y z else if z = k then ?used - setsum (?rr y) {..<k} else 0) \<partial>count_space {..k})"
          by(auto simp add: nn_integral_count_space_indicator indicator_def intro: nn_integral_cong)
        also have "\<dots> = ?used" 
          using k by(auto simp add: nn_integral_count_space_finite max_def ivl_disj_un(2)[symmetric] diff_le_iff setsum_nonneg dest: find_start_eq_Some_least)
        finally have "?pp y x \<le> (\<integral>\<^sup>+ z. ?f z \<partial>count_space UNIV)"
          by(cases "\<integral>\<^sup>+ z. ?f z \<partial>count_space UNIV") simp_all
        then show ?thesis using k
          by(simp add: assign_def nn_integral_assign_aux diff_le_iff find_start_eq_Some_above min_def)
      next
        case True
        have "setsum (?pp y) {..x} = \<integral>\<^sup>+ x. ?pp y x \<partial>count_space {..x}"
          by(simp add: nn_integral_count_space_finite max_def)
        also have "\<dots> \<le> \<integral>\<^sup>+ x. ?pp y x \<partial>count_space UNIV"
          by(auto simp add: nn_integral_count_space_indicator indicator_def intro: nn_integral_mono)
        also have "\<dots> = setsum (?pp y) {..<x}" by(simp add: True)
        finally have "?pp y x = 0" by(simp add: ivl_disj_un(2)[symmetric] eq_iff del: pmf_le_0_iff)
        thus ?thesis
          by(cases "find_start y (setsum (?pp y) {..<x})")(simp_all add: assign_def diff_le_iff find_start_eq_Some_above)
      qed }
    note nn_integral_assign2 = this

    def a \<equiv> "embed_pmf (\<lambda>(y, x, z). assign y x z)"
    { fix y x z
      have "assign y x z = pmf a (y, x, z)"
        unfolding a_def
      proof (subst pmf_embed_pmf)
        have "(\<integral>\<^sup>+ x. ereal ((\<lambda>(y, x, z). assign y x z) x) \<partial>count_space UNIV) =
          (\<integral>\<^sup>+ x. ereal ((\<lambda>(y, x, z). assign y x z) x) \<partial>(count_space ((\<lambda>((y, x), z). (y, x, z)) ` (pp \<times> UNIV))))"
          by (force simp add: nn_integral_count_space_indicator pmf_eq_0_set_pmf split: split_indicator
                    intro!: nn_integral_cong assign_eq_0_outside)
        also have "\<dots> = (\<integral>\<^sup>+ x. ereal ((\<lambda>((y, x), z). assign y x z) x) \<partial>(count_space (pp \<times> UNIV)))"
          by (subst nn_integral_bij_count_space[OF inj_on_imp_bij_betw, symmetric])
             (auto simp: inj_on_def intro!: nn_integral_cong)
        also have "\<dots> = (\<integral>\<^sup>+ y. \<integral>\<^sup>+z. ereal ((\<lambda>((y, x), z). assign y x z) (y, z)) \<partial>count_space UNIV \<partial>count_space pp)"
          by (subst sigma_finite_measure.nn_integral_fst)
             (auto simp: pair_measure_countable sigma_finite_measure_count_space_countable)
        also have "\<dots> = (\<integral>\<^sup>+ z. ?pp (fst z) (snd z) \<partial>count_space pp)"
          by (subst nn_integral_assign2[symmetric]) (auto intro!: nn_integral_cong)
        finally show "(\<integral>\<^sup>+ x. ereal ((\<lambda>(y, x, z). assign y x z) x) \<partial>count_space UNIV) = 1"
          by (simp add: nn_integral_pmf emeasure_pmf)
      qed auto }
    note a = this

    def pr \<equiv> "map_pmf (\<lambda>(y, x, z). (from_nat_into (A y) x, from_nat_into (B y) z)) a"

    have "rel_pmf (R OO S) p r"
    proof
      have pp_eq: "pp = map_pmf (\<lambda>(y, x, z). (y, x)) a"
      proof (rule pmf_eqI)
        fix i
        show "pmf pp i = pmf (map_pmf (\<lambda>(y, x, z). (y, x)) a) i"
          using nn_integral_assign2[of "fst i" "snd i", symmetric]
          by (auto simp add: a nn_integral_pmf' inj_on_def ereal.inject[symmetric] ereal_pmf_map 
                   simp del: ereal.inject intro!: arg_cong2[where f=emeasure])
      qed
      moreover have pq_eq: "pq = map_pmf (\<lambda>(y, x). (from_nat_into (A y) x, y)) pp"
        by (simp add: pp_def map_pmf_comp split_beta A[symmetric] cong: map_pmf_cong)
      ultimately show "map_pmf fst pr = p"
        unfolding p pr_def by (simp add: map_pmf_comp split_beta)

      have rr_eq: "rr = map_pmf (\<lambda>(y, x, z). (y, z)) a"
      proof (rule pmf_eqI)
        fix i show "pmf rr i = pmf (map_pmf (\<lambda>(y, x, z). (y, z)) a) i"
          using nn_integral_assign1[of "fst i" "snd i", symmetric]
          by (auto simp add: a nn_integral_pmf' inj_on_def ereal.inject[symmetric] ereal_pmf_map 
                   simp del: ereal.inject intro!: arg_cong2[where f=emeasure])
      qed
      moreover have qr_eq: "qr = map_pmf (\<lambda>(y, z). (y, from_nat_into (B y) z)) rr"
        by (simp add: rr_def map_pmf_comp split_beta B[symmetric] cong: map_pmf_cong)
      ultimately show "map_pmf snd pr = r"
        unfolding r pr_def by (simp add: map_pmf_comp split_beta)

      fix x z assume "(x, z) \<in> set_pmf pr"
      then have "\<exists>y. (x, y) \<in> set_pmf pq \<and> (y, z) \<in> set_pmf qr"
        by (force simp add: pp_eq pq_eq rr_eq qr_eq set_map_pmf pr_def image_image)
      with pq qr show "(R OO S) x z"
        by blast
    qed }
  then show "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
    by(auto simp add: le_fun_def)
qed (fact natLeq_card_order natLeq_cinfinite)+

end

