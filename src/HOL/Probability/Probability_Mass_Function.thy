(*  Title:      HOL/Probability/Probability_Mass_Function.thy
    Author:     Johannes Hölzl, TU München *)

section \<open> Probability mass function \<close>

theory Probability_Mass_Function
imports
  Giry_Monad
  "~~/src/HOL/Library/Multiset"
begin

lemma (in finite_measure) countable_support: (* replace version in pmf *)
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

lemma countable_set_pmf: "countable (set_pmf p)"
  by transfer (metis prob_space.finite_measure finite_measure.countable_support)

lemma sets_measure_pmf[simp]: "sets (measure_pmf p) = UNIV"
  by transfer metis

lemma sets_measure_pmf_count_space: "sets (measure_pmf M) = sets (count_space UNIV)"
  by simp

lemma space_measure_pmf[simp]: "space (measure_pmf p) = UNIV"
  using sets_eq_imp_space_eq[of "measure_pmf p" "count_space UNIV"] by simp

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
    by (simp add: pmf.rep_eq measure_pmf.integrable_measure countable_set_pmf disjoint_family_on_def)
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

lemma map_pmf_id[simp]: "map_pmf id = id"
  by (rule, transfer) (auto simp: emeasure_distr measurable_def intro!: measure_eqI)

lemma map_pmf_compose: "map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g"
  by (rule, transfer) (simp add: distr_distr[symmetric, where N="count_space UNIV"] measurable_def) 

lemma map_pmf_comp: "map_pmf f (map_pmf g M) = map_pmf (\<lambda>x. f (g x)) M"
  using map_pmf_compose[of f g] by (simp add: comp_def)

lemma map_pmf_cong:
  assumes "p = q"
  shows "(\<And>x. x \<in> set_pmf q \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g q"
  unfolding `p = q`[symmetric] measure_pmf_inject[symmetric] map_pmf.rep_eq
  by (auto simp add: emeasure_distr AE_measure_pmf_iff intro!: emeasure_eq_AE measure_eqI)

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
    by (simp add: AE_density nonneg emeasure_density measure_def nn_integral_cmult_indicator)
  show "prob_space (density (count_space UNIV) (ereal \<circ> f))"
    by default (simp add: emeasure_density prob)
qed simp

lemma pmf_embed_pmf: "pmf embed_pmf x = f x"
proof transfer
  have *[simp]: "\<And>x y. ereal (f y) * indicator {x} y = ereal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  fix x show "measure (density (count_space UNIV) (ereal \<circ> f)) {x} = f x"
    by transfer (simp add: measure_def emeasure_density nn_integral_cmult_indicator nonneg)
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

lemma set_pmf_geometric: "set_pmf geometric_pmf = UNIV"
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
    using assms by (subst (1 2) sets_bind) auto
next
  fix X assume "X \<in> sets (measure_pmf x \<guillemotright>= A)"
  then have X: "X \<in> sets N"
    using assms by (subst (asm) sets_bind) auto
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

  have *: "measure_pmf \<in> measurable (measure_pmf M) (subprob_algebra (count_space UNIV))"
    using measurable_measure_pmf[of "\<lambda>x. x"] by simp
  
  interpret bind: prob_space "measure_pmf M \<guillemotright>= measure_pmf"
    apply (rule measure_pmf.prob_space_bind[OF _ *])
    apply (auto intro!: AE_I2)
    apply unfold_locales
    done
  show "prob_space (measure_pmf M \<guillemotright>= measure_pmf)"
    by intro_locales
  show "sets (measure_pmf M \<guillemotright>= measure_pmf) = UNIV"
    by (subst sets_bind[OF *]) auto
  have "AE x in measure_pmf M \<guillemotright>= measure_pmf. emeasure (measure_pmf M \<guillemotright>= measure_pmf) {x} \<noteq> 0"
    by (auto simp add: AE_bind[OF _ *] AE_measure_pmf_iff emeasure_bind[OF _ *]
        nn_integral_0_iff_AE measure_pmf.emeasure_eq_measure measure_le_0_iff set_pmf_iff pmf.rep_eq)
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

lift_definition return_pmf :: "'a \<Rightarrow> 'a pmf" is "return (count_space UNIV)"
  by (auto intro!: prob_space_return simp: AE_return measure_return)

lemma join_return_pmf: "join_pmf (return_pmf M) = M"
  by (simp add: integral_return pmf_eq_iff pmf_join return_pmf.rep_eq)

lemma map_return_pmf: "map_pmf f (return_pmf x) = return_pmf (f x)"
  by transfer (simp add: distr_return)

lemma set_pmf_return: "set_pmf (return_pmf x) = {x}"
  by transfer (auto simp add: measure_return split: split_indicator)

lemma pmf_return: "pmf (return_pmf x) y = indicator {y} x"
  by transfer (simp add: measure_return)

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
    apply (intro integral_pmf_restrict B.borel_measurable_lebesgue_integral)
    apply (auto simp: measurable_split_conv)
    apply (subst measurable_cong_sets)
    apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
    apply (simp add: restrict_count_space)
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (auto intro: countable_set_pmf)
    done
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>restrict_space A A \<partial>restrict_space B B)"
    apply (rule AB.Fubini_integral[symmetric])
    apply (auto intro!: AB.integrable_const_bound[where B=1] simp: pmf_nonneg pmf_le_1)
    apply (auto simp: measurable_split_conv)
    apply (subst measurable_cong_sets)
    apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
    apply (simp add: restrict_count_space)
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (auto intro: countable_set_pmf)
    done
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>restrict_space A A \<partial>B)"
    apply (intro integral_pmf_restrict[symmetric] A.borel_measurable_lebesgue_integral)
    apply (auto simp: measurable_split_conv)
    apply (subst measurable_cong_sets)
    apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
    apply (simp add: restrict_count_space)
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (auto intro: countable_set_pmf)
    done
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)"
    by (rule integral_cong) (auto intro!: integral_pmf_restrict[symmetric])
  finally show "(\<integral> x. \<integral> y. pmf (C x y) i \<partial>B \<partial>A) = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)" .
qed


context
begin

interpretation pmf_as_measure .

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

lemma measure_pmf_bind: "measure_pmf (bind_pmf M f) = (measure_pmf M \<guillemotright>= (\<lambda>x. measure_pmf (f x)))"
  by transfer simp

end

definition "pair_pmf A B = bind_pmf A (\<lambda>x. bind_pmf B (\<lambda>y. return_pmf (x, y)))"

lemma pmf_pair: "pmf (pair_pmf M N) (a, b) = pmf M a * pmf N b"
  unfolding pair_pmf_def pmf_bind pmf_return
  apply (subst integral_measure_pmf[where A="{b}"])
  apply (auto simp: indicator_eq_0_iff)
  apply (subst integral_measure_pmf[where A="{a}"])
  apply (auto simp: indicator_eq_0_iff setsum_nonneg_eq_0_iff pmf_nonneg)
  done

lemma bind_pair_pmf:
  assumes M[measurable]: "M \<in> measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) (subprob_algebra N)"
  shows "measure_pmf (pair_pmf A B) \<guillemotright>= M = (measure_pmf A \<guillemotright>= (\<lambda>x. measure_pmf B \<guillemotright>= (\<lambda>y. M (x, y))))"
    (is "?L = ?R")
proof (rule measure_eqI)
  have M'[measurable]: "M \<in> measurable (pair_pmf A B) (subprob_algebra N)"
    using M[THEN measurable_space] by (simp_all add: space_pair_measure)

  have sets_eq_N: "sets ?L = N"
    by (simp add: sets_bind[OF M'])
  show "sets ?L = sets ?R"
    unfolding sets_eq_N
    apply (subst sets_bind[where N=N])
    apply (rule measurable_bind)
    apply (rule measurable_compose[OF _ measurable_measure_pmf])
    apply measurable
    apply (auto intro!: sets_pair_measure_cong sets_measure_pmf_count_space)
    done
  fix X assume "X \<in> sets ?L"
  then have X[measurable]: "X \<in> sets N"
    unfolding sets_eq_N .
  then show "emeasure ?L X = emeasure ?R X"
    apply (simp add: emeasure_bind[OF _ M' X])
    unfolding pair_pmf_def measure_pmf_bind[of A]
    apply (subst nn_integral_bind[OF _ emeasure_nonneg])
    apply (rule measurable_compose[OF M' measurable_emeasure_subprob_algebra, OF X])
    apply (subst measurable_cong_sets[OF sets_measure_pmf_count_space refl])
    apply (subst subprob_algebra_cong[OF sets_measure_pmf_count_space])
    apply measurable
    unfolding measure_pmf_bind
    apply (subst nn_integral_bind[OF _ emeasure_nonneg])
    apply (rule measurable_compose[OF M' measurable_emeasure_subprob_algebra, OF X])
    apply (subst measurable_cong_sets[OF sets_measure_pmf_count_space refl])
    apply (subst subprob_algebra_cong[OF sets_measure_pmf_count_space])
    apply measurable
    apply (simp add: nn_integral_measure_pmf_finite set_pmf_return emeasure_nonneg pmf_return one_ereal_def[symmetric])
    apply (subst emeasure_bind[OF _ _ X])
    apply simp
    apply (rule measurable_bind[where N="count_space UNIV"])
    apply (rule measurable_compose[OF _ measurable_measure_pmf])
    apply measurable
    apply (rule sets_pair_measure_cong sets_measure_pmf_count_space refl)+
    apply (subst measurable_cong_sets[OF sets_pair_measure_cong[OF sets_measure_pmf_count_space refl] refl])
    apply simp
    apply (subst emeasure_bind[OF _ _ X])
    apply simp
    apply (rule measurable_compose[OF _ M])
    apply (auto simp: space_pair_measure)
    done
qed

lemma set_pmf_bind: "set_pmf (bind_pmf M N) = (\<Union>M\<in>set_pmf M. set_pmf (N M))"
  apply (simp add: set_eq_iff set_pmf_iff pmf_bind)
  apply (subst integral_nonneg_eq_0_iff_AE)
  apply (auto simp: pmf_nonneg pmf_le_1 AE_measure_pmf_iff
              intro!: measure_pmf.integrable_const_bound[where B=1])
  done

lemma set_pmf_pair_pmf: "set_pmf (pair_pmf A B) = set_pmf A \<times> set_pmf B"
  unfolding pair_pmf_def set_pmf_bind set_pmf_return by auto

(*

definition
  "rel_pmf P d1 d2 \<longleftrightarrow> (\<exists>p3. (\<forall>(x, y) \<in> set_pmf p3. P x y) \<and> map_pmf fst p3 = d1 \<and> map_pmf snd p3 = d2)"

bnf pmf: "'a pmf" map: map_pmf sets: set_pmf bd : "natLeq" rel: pmf_rel
proof -
  show "map_pmf id = id" by (rule map_pmf_id)
  show "\<And>f g. map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g" by (rule map_pmf_compose) 
  show "\<And>f g::'a \<Rightarrow> 'b. \<And>p. (\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g p"
    by (intro map_pmg_cong refl)

  show "\<And>f::'a \<Rightarrow> 'b. set_pmf \<circ> map_pmf f = op ` f \<circ> set_pmf"
    by (rule pmf_set_map)

  { fix p :: "'s pmf"
    have "(card_of (set_pmf p), card_of (UNIV :: nat set)) \<in> ordLeq"
      by (rule card_of_ordLeqI[where f="to_nat_on (set_pmf p)"])
         (auto intro: countable_set_pmf inj_on_to_nat_on)
    also have "(card_of (UNIV :: nat set), natLeq) \<in> ordLeq"
      by (metis Field_natLeq card_of_least natLeq_Well_order)
    finally show "(card_of (set_pmf p), natLeq) \<in> ordLeq" . }

  show "\<And>R. pmf_rel R =
         (BNF_Util.Grp {x. set_pmf x \<subseteq> {(x, y). R x y}} (map_pmf fst))\<inverse>\<inverse> OO
         BNF_Util.Grp {x. set_pmf x \<subseteq> {(x, y). R x y}} (map_pmf snd)"
     by (auto simp add: fun_eq_iff pmf_rel_def BNF_Util.Grp_def OO_def)

  { let ?f = "map_pmf fst" and ?s = "map_pmf snd"
    fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and A assume "\<And>x y. (x, y) \<in> set_pmf A \<Longrightarrow> R x y"
    fix S :: "'b \<Rightarrow> 'c \<Rightarrow> bool" and B assume "\<And>y z. (y, z) \<in> set_pmf B \<Longrightarrow> S y z"
    assume "?f B = ?s A"
    have "\<exists>C. (\<forall>(x, z)\<in>set_pmf C. \<exists>y. R x y \<and> S y z) \<and> ?f C = ?f A \<and> ?s C = ?s B"
      sorry }
oops
  then show "\<And>R::'a \<Rightarrow> 'b \<Rightarrow> bool. \<And>S::'b \<Rightarrow> 'c \<Rightarrow> bool. pmf_rel R OO pmf_rel S \<le> pmf_rel (R OO S)"
      by (auto simp add: subset_eq pmf_rel_def fun_eq_iff OO_def Ball_def)
qed (fact natLeq_card_order natLeq_cinfinite)+

notepad
begin
  fix x y :: "nat \<Rightarrow> real"
  def IJz \<equiv> "rec_nat ((0, 0), \<lambda>_. 0) (\<lambda>n ((I, J), z).
    let a = x I - (\<Sum>j<J. z (I, j)) ; b = y J - (\<Sum>i<I. z (i, J)) in
      ((if a \<le> b then I + 1 else I, if b \<le> a then J + 1 else J), z((I, J) := min a b)))"
  def I == "fst \<circ> fst \<circ> IJz" def J == "snd \<circ> fst \<circ> IJz" def z == "snd \<circ> IJz"
  let ?a = "\<lambda>n. x (I n) - (\<Sum>j<J n. z n (I n, j))" and ?b = "\<lambda>n. y (J n) - (\<Sum>i<I n. z n (i, J n))"
  have IJz_0[simp]: "\<And>p. z 0 p = 0" "I 0 = 0" "J 0 = 0"
    by (simp_all add: I_def J_def z_def IJz_def)
  have z_Suc[simp]: "\<And>n. z (Suc n) = (z n)((I n, J n) := min (?a n) (?b n))"
    by (simp add: z_def I_def J_def IJz_def Let_def split_beta)
  have I_Suc[simp]: "\<And>n. I (Suc n) = (if ?a n \<le> ?b n then I n + 1 else I n)"
    by (simp add: z_def I_def J_def IJz_def Let_def split_beta)
  have J_Suc[simp]: "\<And>n. J (Suc n) = (if ?b n \<le> ?a n then J n + 1 else J n)"
    by (simp add: z_def I_def J_def IJz_def Let_def split_beta)
  
  { fix N have "\<And>p. z N p \<noteq> 0 \<Longrightarrow> \<exists>n<N. p = (I n, J n)"
      by (induct N) (auto simp add: less_Suc_eq split: split_if_asm) }
  
  { fix i n assume "i < I n"
    then have "(\<Sum>j. z n (i, j)) = x i" 
    oops
*)

end

