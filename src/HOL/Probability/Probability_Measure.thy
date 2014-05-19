(*  Title:      HOL/Probability/Probability_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Probability measure*}

theory Probability_Measure
  imports Lebesgue_Measure Radon_Nikodym
begin

locale prob_space = finite_measure +
  assumes emeasure_space_1: "emeasure M (space M) = 1"

lemma prob_spaceI[Pure.intro!]:
  assumes *: "emeasure M (space M) = 1"
  shows "prob_space M"
proof -
  interpret finite_measure M
  proof
    show "emeasure M (space M) \<noteq> \<infinity>" using * by simp 
  qed
  show "prob_space M" by default fact
qed

abbreviation (in prob_space) "events \<equiv> sets M"
abbreviation (in prob_space) "prob \<equiv> measure M"
abbreviation (in prob_space) "random_variable M' X \<equiv> X \<in> measurable M M'"
abbreviation (in prob_space) "expectation \<equiv> integral\<^sup>L M"

lemma (in prob_space) prob_space_distr:
  assumes f: "f \<in> measurable M M'" shows "prob_space (distr M M' f)"
proof (rule prob_spaceI)
  have "f -` space M' \<inter> space M = space M" using f by (auto dest: measurable_space)
  with f show "emeasure (distr M M' f) (space (distr M M' f)) = 1"
    by (auto simp: emeasure_distr emeasure_space_1)
qed

lemma (in prob_space) prob_space: "prob (space M) = 1"
  using emeasure_space_1 unfolding measure_def by (simp add: one_ereal_def)

lemma (in prob_space) prob_le_1[simp, intro]: "prob A \<le> 1"
  using bounded_measure[of A] by (simp add: prob_space)

lemma (in prob_space) not_empty: "space M \<noteq> {}"
  using prob_space by auto

lemma (in prob_space) measure_le_1: "emeasure M X \<le> 1"
  using emeasure_space[of M X] by (simp add: emeasure_space_1)

lemma (in prob_space) AE_I_eq_1:
  assumes "emeasure M {x\<in>space M. P x} = 1" "{x\<in>space M. P x} \<in> sets M"
  shows "AE x in M. P x"
proof (rule AE_I)
  show "emeasure M (space M - {x \<in> space M. P x}) = 0"
    using assms emeasure_space_1 by (simp add: emeasure_compl)
qed (insert assms, auto)

lemma (in prob_space) prob_compl:
  assumes A: "A \<in> events"
  shows "prob (space M - A) = 1 - prob A"
  using finite_measure_compl[OF A] by (simp add: prob_space)

lemma (in prob_space) AE_in_set_eq_1:
  assumes "A \<in> events" shows "(AE x in M. x \<in> A) \<longleftrightarrow> prob A = 1"
proof
  assume ae: "AE x in M. x \<in> A"
  have "{x \<in> space M. x \<in> A} = A" "{x \<in> space M. x \<notin> A} = space M - A"
    using `A \<in> events`[THEN sets.sets_into_space] by auto
  with AE_E2[OF ae] `A \<in> events` have "1 - emeasure M A = 0"
    by (simp add: emeasure_compl emeasure_space_1)
  then show "prob A = 1"
    using `A \<in> events` by (simp add: emeasure_eq_measure one_ereal_def)
next
  assume prob: "prob A = 1"
  show "AE x in M. x \<in> A"
  proof (rule AE_I)
    show "{x \<in> space M. x \<notin> A} \<subseteq> space M - A" by auto
    show "emeasure M (space M - A) = 0"
      using `A \<in> events` prob
      by (simp add: prob_compl emeasure_space_1 emeasure_eq_measure one_ereal_def)
    show "space M - A \<in> events"
      using `A \<in> events` by auto
  qed
qed

lemma (in prob_space) AE_False: "(AE x in M. False) \<longleftrightarrow> False"
proof
  assume "AE x in M. False"
  then have "AE x in M. x \<in> {}" by simp
  then show False
    by (subst (asm) AE_in_set_eq_1) auto
qed simp

lemma (in prob_space) AE_prob_1:
  assumes "prob A = 1" shows "AE x in M. x \<in> A"
proof -
  from `prob A = 1` have "A \<in> events"
    by (metis measure_notin_sets zero_neq_one)
  with AE_in_set_eq_1 assms show ?thesis by simp
qed

lemma (in prob_space) AE_const[simp]: "(AE x in M. P) \<longleftrightarrow> P"
  by (cases P) (auto simp: AE_False)

lemma (in prob_space) AE_contr:
  assumes ae: "AE \<omega> in M. P \<omega>" "AE \<omega> in M. \<not> P \<omega>"
  shows False
proof -
  from ae have "AE \<omega> in M. False" by eventually_elim auto
  then show False by auto
qed

lemma (in prob_space) expectation_less:
  fixes X :: "_ \<Rightarrow> real"
  assumes [simp]: "integrable M X"
  assumes gt: "AE x in M. X x < b"
  shows "expectation X < b"
proof -
  have "expectation X < expectation (\<lambda>x. b)"
    using gt emeasure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) expectation_greater:
  fixes X :: "_ \<Rightarrow> real"
  assumes [simp]: "integrable M X"
  assumes gt: "AE x in M. a < X x"
  shows "a < expectation X"
proof -
  have "expectation (\<lambda>x. a) < expectation X"
    using gt emeasure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) jensens_inequality:
  fixes q :: "real \<Rightarrow> real"
  assumes X: "integrable M X" "AE x in M. X x \<in> I"
  assumes I: "I = {a <..< b} \<or> I = {a <..} \<or> I = {..< b} \<or> I = UNIV"
  assumes q: "integrable M (\<lambda>x. q (X x))" "convex_on I q"
  shows "q (expectation X) \<le> expectation (\<lambda>x. q (X x))"
proof -
  let ?F = "\<lambda>x. Inf ((\<lambda>t. (q x - q t) / (x - t)) ` ({x<..} \<inter> I))"
  from X(2) AE_False have "I \<noteq> {}" by auto

  from I have "open I" by auto

  note I
  moreover
  { assume "I \<subseteq> {a <..}"
    with X have "a < expectation X"
      by (intro expectation_greater) auto }
  moreover
  { assume "I \<subseteq> {..< b}"
    with X have "expectation X < b"
      by (intro expectation_less) auto }
  ultimately have "expectation X \<in> I"
    by (elim disjE)  (auto simp: subset_eq)
  moreover
  { fix y assume y: "y \<in> I"
    with q(2) `open I` have "Sup ((\<lambda>x. q x + ?F x * (y - x)) ` I) = q y"
      by (auto intro!: cSup_eq_maximum convex_le_Inf_differential image_eqI [OF _ y] simp: interior_open simp del: Sup_image_eq Inf_image_eq) }
  ultimately have "q (expectation X) = Sup ((\<lambda>x. q x + ?F x * (expectation X - x)) ` I)"
    by simp
  also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
  proof (rule cSup_least)
    show "(\<lambda>x. q x + ?F x * (expectation X - x)) ` I \<noteq> {}"
      using `I \<noteq> {}` by auto
  next
    fix k assume "k \<in> (\<lambda>x. q x + ?F x * (expectation X - x)) ` I"
    then guess x .. note x = this
    have "q x + ?F x * (expectation X  - x) = expectation (\<lambda>w. q x + ?F x * (X w - x))"
      using prob_space by (simp add: X)
    also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
      using `x \<in> I` `open I` X(2)
      apply (intro integral_mono_AE integrable_add integrable_mult_right integrable_diff
                integrable_const X q)
      apply (elim eventually_elim1)
      apply (intro convex_le_Inf_differential)
      apply (auto simp: interior_open q)
      done
    finally show "k \<le> expectation (\<lambda>w. q (X w))" using x by auto
  qed
  finally show "q (expectation X) \<le> expectation (\<lambda>x. q (X x))" .
qed

subsection  {* Introduce binder for probability *}

syntax
  "_prob" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("('\<P>'(_ in _. _'))")

translations
  "\<P>(x in M. P)" => "CONST measure M {x \<in> CONST space M. P}"

definition
  "cond_prob M P Q = \<P>(\<omega> in M. P \<omega> \<and> Q \<omega>) / \<P>(\<omega> in M. Q \<omega>)"

syntax
  "_conditional_prob" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("('\<P>'(_ in _. _ \<bar>/ _'))")

translations
  "\<P>(x in M. P \<bar> Q)" => "CONST cond_prob M (\<lambda>x. P) (\<lambda>x. Q)"

lemma (in prob_space) AE_E_prob:
  assumes ae: "AE x in M. P x"
  obtains S where "S \<subseteq> {x \<in> space M. P x}" "S \<in> events" "prob S = 1"
proof -
  from ae[THEN AE_E] guess N .
  then show thesis
    by (intro that[of "space M - N"])
       (auto simp: prob_compl prob_space emeasure_eq_measure)
qed

lemma (in prob_space) prob_neg: "{x\<in>space M. P x} \<in> events \<Longrightarrow> \<P>(x in M. \<not> P x) = 1 - \<P>(x in M. P x)"
  by (auto intro!: arg_cong[where f=prob] simp add: prob_compl[symmetric])

lemma (in prob_space) prob_eq_AE:
  "(AE x in M. P x \<longleftrightarrow> Q x) \<Longrightarrow> {x\<in>space M. P x} \<in> events \<Longrightarrow> {x\<in>space M. Q x} \<in> events \<Longrightarrow> \<P>(x in M. P x) = \<P>(x in M. Q x)"
  by (rule finite_measure_eq_AE) auto

lemma (in prob_space) prob_eq_0_AE:
  assumes not: "AE x in M. \<not> P x" shows "\<P>(x in M. P x) = 0"
proof cases
  assume "{x\<in>space M. P x} \<in> events"
  with not have "\<P>(x in M. P x) = \<P>(x in M. False)"
    by (intro prob_eq_AE) auto
  then show ?thesis by simp
qed (simp add: measure_notin_sets)

lemma (in prob_space) prob_Collect_eq_0:
  "{x \<in> space M. P x} \<in> sets M \<Longrightarrow> \<P>(x in M. P x) = 0 \<longleftrightarrow> (AE x in M. \<not> P x)"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. \<not> P x"] by (simp add: emeasure_eq_measure)

lemma (in prob_space) prob_Collect_eq_1:
  "{x \<in> space M. P x} \<in> sets M \<Longrightarrow> \<P>(x in M. P x) = 1 \<longleftrightarrow> (AE x in M. P x)"
  using AE_in_set_eq_1[of "{x\<in>space M. P x}"] by simp

lemma (in prob_space) prob_eq_0:
  "A \<in> sets M \<Longrightarrow> prob A = 0 \<longleftrightarrow> (AE x in M. x \<notin> A)"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. x \<notin> A"]
  by (auto simp add: emeasure_eq_measure Int_def[symmetric])

lemma (in prob_space) prob_eq_1:
  "A \<in> sets M \<Longrightarrow> prob A = 1 \<longleftrightarrow> (AE x in M. x \<in> A)"
  using AE_in_set_eq_1[of A] by simp

lemma (in prob_space) prob_sums:
  assumes P: "\<And>n. {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x in M. (\<forall>n. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n. P n x))"
  shows "(\<lambda>n. \<P>(x in M. P n x)) sums \<P>(x in M. Q x)"
proof -
  from ae[THEN AE_E_prob] guess S . note S = this
  then have disj: "disjoint_family (\<lambda>n. {x\<in>space M. P n x} \<inter> S)"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x in M. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. AE x in M. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<P>(x in M. Q x) = prob (\<Union>n. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  from ae_S have **:
    "\<And>n. \<P>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    unfolding * ** using S P disj
    by (intro finite_measure_UNION) auto
qed

lemma (in prob_space) prob_EX_countable:
  assumes sets: "\<And>i. i \<in> I \<Longrightarrow> {x\<in>space M. P i x} \<in> sets M" and I: "countable I" 
  assumes disj: "AE x in M. \<forall>i\<in>I. \<forall>j\<in>I. P i x \<longrightarrow> P j x \<longrightarrow> i = j"
  shows "\<P>(x in M. \<exists>i\<in>I. P i x) = (\<integral>\<^sup>+i. \<P>(x in M. P i x) \<partial>count_space I)"
proof -
  let ?N= "\<lambda>x. \<exists>!i\<in>I. P i x"
  have "ereal (\<P>(x in M. \<exists>i\<in>I. P i x)) = \<P>(x in M. (\<exists>i\<in>I. P i x \<and> ?N x))"
    unfolding ereal.inject
  proof (rule prob_eq_AE)
    show "AE x in M. (\<exists>i\<in>I. P i x) = (\<exists>i\<in>I. P i x \<and> ?N x)"
      using disj by eventually_elim blast
  qed (auto intro!: sets.sets_Collect_countable_Ex' sets.sets_Collect_conj sets.sets_Collect_countable_Ex1' I sets)+
  also have "\<P>(x in M. (\<exists>i\<in>I. P i x \<and> ?N x)) = emeasure M (\<Union>i\<in>I. {x\<in>space M. P i x \<and> ?N x})"
    unfolding emeasure_eq_measure by (auto intro!: arg_cong[where f=prob])
  also have "\<dots> = (\<integral>\<^sup>+i. emeasure M {x\<in>space M. P i x \<and> ?N x} \<partial>count_space I)"
    by (rule emeasure_UN_countable)
       (auto intro!: sets.sets_Collect_countable_Ex' sets.sets_Collect_conj sets.sets_Collect_countable_Ex1' I sets
             simp: disjoint_family_on_def)
  also have "\<dots> = (\<integral>\<^sup>+i. \<P>(x in M. P i x) \<partial>count_space I)"
    unfolding emeasure_eq_measure using disj
    by (intro positive_integral_cong ereal.inject[THEN iffD2] prob_eq_AE)
       (auto intro!: sets.sets_Collect_countable_Ex' sets.sets_Collect_conj sets.sets_Collect_countable_Ex1' I sets)+
  finally show ?thesis .
qed

lemma (in prob_space) cond_prob_eq_AE:
  assumes P: "AE x in M. Q x \<longrightarrow> P x \<longleftrightarrow> P' x" "{x\<in>space M. P x} \<in> events" "{x\<in>space M. P' x} \<in> events"
  assumes Q: "AE x in M. Q x \<longleftrightarrow> Q' x" "{x\<in>space M. Q x} \<in> events" "{x\<in>space M. Q' x} \<in> events"
  shows "cond_prob M P Q = cond_prob M P' Q'"
  using P Q
  by (auto simp: cond_prob_def intro!: arg_cong2[where f="op /"] prob_eq_AE sets.sets_Collect_conj)


lemma (in prob_space) joint_distribution_Times_le_fst:
  "random_variable MX X \<Longrightarrow> random_variable MY Y \<Longrightarrow> A \<in> sets MX \<Longrightarrow> B \<in> sets MY
    \<Longrightarrow> emeasure (distr M (MX \<Otimes>\<^sub>M MY) (\<lambda>x. (X x, Y x))) (A \<times> B) \<le> emeasure (distr M MX X) A"
  by (auto simp: emeasure_distr measurable_pair_iff comp_def intro!: emeasure_mono measurable_sets)

lemma (in prob_space) joint_distribution_Times_le_snd:
  "random_variable MX X \<Longrightarrow> random_variable MY Y \<Longrightarrow> A \<in> sets MX \<Longrightarrow> B \<in> sets MY
    \<Longrightarrow> emeasure (distr M (MX \<Otimes>\<^sub>M MY) (\<lambda>x. (X x, Y x))) (A \<times> B) \<le> emeasure (distr M MY Y) B"
  by (auto simp: emeasure_distr measurable_pair_iff comp_def intro!: emeasure_mono measurable_sets)

locale pair_prob_space = pair_sigma_finite M1 M2 + M1: prob_space M1 + M2: prob_space M2 for M1 M2

sublocale pair_prob_space \<subseteq> P: prob_space "M1 \<Otimes>\<^sub>M M2"
proof
  show "emeasure (M1 \<Otimes>\<^sub>M M2) (space (M1 \<Otimes>\<^sub>M M2)) = 1"
    by (simp add: M2.emeasure_pair_measure_Times M1.emeasure_space_1 M2.emeasure_space_1 space_pair_measure)
qed

locale product_prob_space = product_sigma_finite M for M :: "'i \<Rightarrow> 'a measure" +
  fixes I :: "'i set"
  assumes prob_space: "\<And>i. prob_space (M i)"

sublocale product_prob_space \<subseteq> M: prob_space "M i" for i
  by (rule prob_space)

locale finite_product_prob_space = finite_product_sigma_finite M I + product_prob_space M I for M I

sublocale finite_product_prob_space \<subseteq> prob_space "\<Pi>\<^sub>M i\<in>I. M i"
proof
  show "emeasure (\<Pi>\<^sub>M i\<in>I. M i) (space (\<Pi>\<^sub>M i\<in>I. M i)) = 1"
    by (simp add: measure_times M.emeasure_space_1 setprod_1 space_PiM)
qed

lemma (in finite_product_prob_space) prob_times:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> sets (M i)"
  shows "prob (\<Pi>\<^sub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.prob i (X i))"
proof -
  have "ereal (measure (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>E i\<in>I. X i)) = emeasure (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>E i\<in>I. X i)"
    using X by (simp add: emeasure_eq_measure)
  also have "\<dots> = (\<Prod>i\<in>I. emeasure (M i) (X i))"
    using measure_times X by simp
  also have "\<dots> = ereal (\<Prod>i\<in>I. measure (M i) (X i))"
    using X by (simp add: M.emeasure_eq_measure setprod_ereal)
  finally show ?thesis by simp
qed

section {* Distributions *}

definition "distributed M N X f \<longleftrightarrow> distr M N X = density N f \<and> 
  f \<in> borel_measurable N \<and> (AE x in N. 0 \<le> f x) \<and> X \<in> measurable M N"

lemma
  assumes "distributed M N X f"
  shows distributed_distr_eq_density: "distr M N X = density N f"
    and distributed_measurable: "X \<in> measurable M N"
    and distributed_borel_measurable: "f \<in> borel_measurable N"
    and distributed_AE: "(AE x in N. 0 \<le> f x)"
  using assms by (simp_all add: distributed_def)

lemma
  assumes D: "distributed M N X f"
  shows distributed_measurable'[measurable_dest]:
      "g \<in> measurable L M \<Longrightarrow> (\<lambda>x. X (g x)) \<in> measurable L N"
    and distributed_borel_measurable'[measurable_dest]:
      "h \<in> measurable L N \<Longrightarrow> (\<lambda>x. f (h x)) \<in> borel_measurable L"
  using distributed_measurable[OF D] distributed_borel_measurable[OF D]
  by simp_all

lemma
  shows distributed_real_measurable: "distributed M N X (\<lambda>x. ereal (f x)) \<Longrightarrow> f \<in> borel_measurable N"
    and distributed_real_AE: "distributed M N X (\<lambda>x. ereal (f x)) \<Longrightarrow> (AE x in N. 0 \<le> f x)"
  by (simp_all add: distributed_def borel_measurable_ereal_iff)

lemma
  assumes D: "distributed M N X (\<lambda>x. ereal (f x))"
  shows distributed_real_measurable'[measurable_dest]:
      "h \<in> measurable L N \<Longrightarrow> (\<lambda>x. f (h x)) \<in> borel_measurable L"
  using distributed_real_measurable[OF D]
  by simp_all

lemma
  assumes D: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) f"
  shows joint_distributed_measurable1[measurable_dest]:
      "h1 \<in> measurable N M \<Longrightarrow> (\<lambda>x. X (h1 x)) \<in> measurable N S"
    and joint_distributed_measurable2[measurable_dest]:
      "h2 \<in> measurable N M \<Longrightarrow> (\<lambda>x. Y (h2 x)) \<in> measurable N T"
  using measurable_compose[OF distributed_measurable[OF D] measurable_fst]
  using measurable_compose[OF distributed_measurable[OF D] measurable_snd]
  by auto

lemma distributed_count_space:
  assumes X: "distributed M (count_space A) X P" and a: "a \<in> A" and A: "finite A"
  shows "P a = emeasure M (X -` {a} \<inter> space M)"
proof -
  have "emeasure M (X -` {a} \<inter> space M) = emeasure (distr M (count_space A) X) {a}"
    using X a A by (simp add: emeasure_distr)
  also have "\<dots> = emeasure (density (count_space A) P) {a}"
    using X by (simp add: distributed_distr_eq_density)
  also have "\<dots> = (\<integral>\<^sup>+x. P a * indicator {a} x \<partial>count_space A)"
    using X a by (auto simp add: emeasure_density distributed_def indicator_def intro!: positive_integral_cong)
  also have "\<dots> = P a"
    using X a by (subst positive_integral_cmult_indicator) (auto simp: distributed_def one_ereal_def[symmetric] AE_count_space)
  finally show ?thesis ..
qed

lemma distributed_cong_density:
  "(AE x in N. f x = g x) \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> f \<in> borel_measurable N \<Longrightarrow>
    distributed M N X f \<longleftrightarrow> distributed M N X g"
  by (auto simp: distributed_def intro!: density_cong)

lemma subdensity:
  assumes T: "T \<in> measurable P Q"
  assumes f: "distributed M P X f"
  assumes g: "distributed M Q Y g"
  assumes Y: "Y = T \<circ> X"
  shows "AE x in P. g (T x) = 0 \<longrightarrow> f x = 0"
proof -
  have "{x\<in>space Q. g x = 0} \<in> null_sets (distr M Q (T \<circ> X))"
    using g Y by (auto simp: null_sets_density_iff distributed_def)
  also have "distr M Q (T \<circ> X) = distr (distr M P X) Q T"
    using T f[THEN distributed_measurable] by (rule distr_distr[symmetric])
  finally have "T -` {x\<in>space Q. g x = 0} \<inter> space P \<in> null_sets (distr M P X)"
    using T by (subst (asm) null_sets_distr_iff) auto
  also have "T -` {x\<in>space Q. g x = 0} \<inter> space P = {x\<in>space P. g (T x) = 0}"
    using T by (auto dest: measurable_space)
  finally show ?thesis
    using f g by (auto simp add: null_sets_density_iff distributed_def)
qed

lemma subdensity_real:
  fixes g :: "'a \<Rightarrow> real" and f :: "'b \<Rightarrow> real"
  assumes T: "T \<in> measurable P Q"
  assumes f: "distributed M P X f"
  assumes g: "distributed M Q Y g"
  assumes Y: "Y = T \<circ> X"
  shows "AE x in P. g (T x) = 0 \<longrightarrow> f x = 0"
  using subdensity[OF T, of M X "\<lambda>x. ereal (f x)" Y "\<lambda>x. ereal (g x)"] assms by auto

lemma distributed_emeasure:
  "distributed M N X f \<Longrightarrow> A \<in> sets N \<Longrightarrow> emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>N)"
  by (auto simp: distributed_AE
                 distributed_distr_eq_density[symmetric] emeasure_density[symmetric] emeasure_distr)

lemma distributed_positive_integral:
  "distributed M N X f \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> (\<integral>\<^sup>+x. f x * g x \<partial>N) = (\<integral>\<^sup>+x. g (X x) \<partial>M)"
  by (auto simp: distributed_AE
                 distributed_distr_eq_density[symmetric] positive_integral_density[symmetric] positive_integral_distr)

lemma distributed_integral:
  "distributed M N X f \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> (\<integral>x. f x * g x \<partial>N) = (\<integral>x. g (X x) \<partial>M)"
  by (auto simp: distributed_real_AE
                 distributed_distr_eq_density[symmetric] integral_real_density[symmetric] integral_distr)
  
lemma distributed_transform_integral:
  assumes Px: "distributed M N X Px"
  assumes "distributed M P Y Py"
  assumes Y: "Y = T \<circ> X" and T: "T \<in> measurable N P" and f: "f \<in> borel_measurable P"
  shows "(\<integral>x. Py x * f x \<partial>P) = (\<integral>x. Px x * f (T x) \<partial>N)"
proof -
  have "(\<integral>x. Py x * f x \<partial>P) = (\<integral>x. f (Y x) \<partial>M)"
    by (rule distributed_integral) fact+
  also have "\<dots> = (\<integral>x. f (T (X x)) \<partial>M)"
    using Y by simp
  also have "\<dots> = (\<integral>x. Px x * f (T x) \<partial>N)"
    using measurable_comp[OF T f] Px by (intro distributed_integral[symmetric]) (auto simp: comp_def)
  finally show ?thesis .
qed

lemma (in prob_space) distributed_unique:
  assumes Px: "distributed M S X Px"
  assumes Py: "distributed M S X Py"
  shows "AE x in S. Px x = Py x"
proof -
  interpret X: prob_space "distr M S X"
    using Px by (intro prob_space_distr) simp
  have "sigma_finite_measure (distr M S X)" ..
  with sigma_finite_density_unique[of Px S Py ] Px Py
  show ?thesis
    by (auto simp: distributed_def)
qed

lemma (in prob_space) distributed_jointI:
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes X[measurable]: "X \<in> measurable M S" and Y[measurable]: "Y \<in> measurable M T"
  assumes [measurable]: "f \<in> borel_measurable (S \<Otimes>\<^sub>M T)" and f: "AE x in S \<Otimes>\<^sub>M T. 0 \<le> f x"
  assumes eq: "\<And>A B. A \<in> sets S \<Longrightarrow> B \<in> sets T \<Longrightarrow> 
    emeasure M {x \<in> space M. X x \<in> A \<and> Y x \<in> B} = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x, y) * indicator B y \<partial>T) * indicator A x \<partial>S)"
  shows "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) f"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T by default

  from ST.sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('b \<times> 'c) set" .. note F = this
  let ?E = "{a \<times> b |a b. a \<in> sets S \<and> b \<in> sets T}"
  let ?P = "S \<Otimes>\<^sub>M T"
  show "distr M ?P (\<lambda>x. (X x, Y x)) = density ?P f" (is "?L = ?R")
  proof (rule measure_eqI_generator_eq[OF Int_stable_pair_measure_generator[of S T]])
    show "?E \<subseteq> Pow (space ?P)"
      using sets.space_closed[of S] sets.space_closed[of T] by (auto simp: space_pair_measure)
    show "sets ?L = sigma_sets (space ?P) ?E"
      by (simp add: sets_pair_measure space_pair_measure)
    then show "sets ?R = sigma_sets (space ?P) ?E"
      by simp
  next
    interpret L: prob_space ?L
      by (rule prob_space_distr) (auto intro!: measurable_Pair)
    show "range F \<subseteq> ?E" "(\<Union>i. F i) = space ?P" "\<And>i. emeasure ?L (F i) \<noteq> \<infinity>"
      using F by (auto simp: space_pair_measure)
  next
    fix E assume "E \<in> ?E"
    then obtain A B where E[simp]: "E = A \<times> B"
      and A[measurable]: "A \<in> sets S" and B[measurable]: "B \<in> sets T" by auto
    have "emeasure ?L E = emeasure M {x \<in> space M. X x \<in> A \<and> Y x \<in> B}"
      by (auto intro!: arg_cong[where f="emeasure M"] simp add: emeasure_distr measurable_Pair)
    also have "\<dots> = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. (f (x, y) * indicator B y) * indicator A x \<partial>T) \<partial>S)"
      using f by (auto simp add: eq positive_integral_multc intro!: positive_integral_cong)
    also have "\<dots> = emeasure ?R E"
      by (auto simp add: emeasure_density T.positive_integral_fst[symmetric]
               intro!: positive_integral_cong split: split_indicator)
    finally show "emeasure ?L E = emeasure ?R E" .
  qed
qed (auto simp: f)

lemma (in prob_space) distributed_swap:
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "distributed M (T \<Otimes>\<^sub>M S) (\<lambda>x. (Y x, X x)) (\<lambda>(x, y). Pxy (y, x))"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T by default
  interpret TS: pair_sigma_finite T S by default

  note Pxy[measurable]
  show ?thesis 
    apply (subst TS.distr_pair_swap)
    unfolding distributed_def
  proof safe
    let ?D = "distr (S \<Otimes>\<^sub>M T) (T \<Otimes>\<^sub>M S) (\<lambda>(x, y). (y, x))"
    show 1: "(\<lambda>(x, y). Pxy (y, x)) \<in> borel_measurable ?D"
      by auto
    with Pxy
    show "AE x in distr (S \<Otimes>\<^sub>M T) (T \<Otimes>\<^sub>M S) (\<lambda>(x, y). (y, x)). 0 \<le> (case x of (x, y) \<Rightarrow> Pxy (y, x))"
      by (subst AE_distr_iff)
         (auto dest!: distributed_AE
               simp: measurable_split_conv split_beta
               intro!: measurable_Pair)
    show 2: "random_variable (distr (S \<Otimes>\<^sub>M T) (T \<Otimes>\<^sub>M S) (\<lambda>(x, y). (y, x))) (\<lambda>x. (Y x, X x))"
      using Pxy by auto
    { fix A assume A: "A \<in> sets (T \<Otimes>\<^sub>M S)"
      let ?B = "(\<lambda>(x, y). (y, x)) -` A \<inter> space (S \<Otimes>\<^sub>M T)"
      from sets.sets_into_space[OF A]
      have "emeasure M ((\<lambda>x. (Y x, X x)) -` A \<inter> space M) =
        emeasure M ((\<lambda>x. (X x, Y x)) -` ?B \<inter> space M)"
        by (auto intro!: arg_cong2[where f=emeasure] simp: space_pair_measure)
      also have "\<dots> = (\<integral>\<^sup>+ x. Pxy x * indicator ?B x \<partial>(S \<Otimes>\<^sub>M T))"
        using Pxy A by (intro distributed_emeasure) auto
      finally have "emeasure M ((\<lambda>x. (Y x, X x)) -` A \<inter> space M) =
        (\<integral>\<^sup>+ x. Pxy x * indicator A (snd x, fst x) \<partial>(S \<Otimes>\<^sub>M T))"
        by (auto intro!: positive_integral_cong split: split_indicator) }
    note * = this
    show "distr M ?D (\<lambda>x. (Y x, X x)) = density ?D (\<lambda>(x, y). Pxy (y, x))"
      apply (intro measure_eqI)
      apply (simp_all add: emeasure_distr[OF 2] emeasure_density[OF 1])
      apply (subst positive_integral_distr)
      apply (auto intro!: * simp: comp_def split_beta)
      done
  qed
qed

lemma (in prob_space) distr_marginal1:
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  defines "Px \<equiv> \<lambda>x. (\<integral>\<^sup>+z. Pxy (x, z) \<partial>T)"
  shows "distributed M S X Px"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T by default

  note Pxy[measurable]
  show X: "X \<in> measurable M S" by simp

  show borel: "Px \<in> borel_measurable S"
    by (auto intro!: T.positive_integral_fst simp: Px_def)

  interpret Pxy: prob_space "distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
    by (intro prob_space_distr) simp
  have "(\<integral>\<^sup>+ x. max 0 (- Pxy x) \<partial>(S \<Otimes>\<^sub>M T)) = (\<integral>\<^sup>+ x. 0 \<partial>(S \<Otimes>\<^sub>M T))"
    using Pxy
    by (intro positive_integral_cong_AE) (auto simp: max_def dest: distributed_AE)

  show "distr M S X = density S Px"
  proof (rule measure_eqI)
    fix A assume A: "A \<in> sets (distr M S X)"
    with X measurable_space[of Y M T]
    have "emeasure (distr M S X) A = emeasure (distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))) (A \<times> space T)"
      by (auto simp add: emeasure_distr intro!: arg_cong[where f="emeasure M"])
    also have "\<dots> = emeasure (density (S \<Otimes>\<^sub>M T) Pxy) (A \<times> space T)"
      using Pxy by (simp add: distributed_def)
    also have "\<dots> = \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. Pxy (x, y) * indicator (A \<times> space T) (x, y) \<partial>T \<partial>S"
      using A borel Pxy
      by (simp add: emeasure_density T.positive_integral_fst[symmetric])
    also have "\<dots> = \<integral>\<^sup>+ x. Px x * indicator A x \<partial>S"
      apply (rule positive_integral_cong_AE)
      using Pxy[THEN distributed_AE, THEN ST.AE_pair] AE_space
    proof eventually_elim
      fix x assume "x \<in> space S" "AE y in T. 0 \<le> Pxy (x, y)"
      moreover have eq: "\<And>y. y \<in> space T \<Longrightarrow> indicator (A \<times> space T) (x, y) = indicator A x"
        by (auto simp: indicator_def)
      ultimately have "(\<integral>\<^sup>+ y. Pxy (x, y) * indicator (A \<times> space T) (x, y) \<partial>T) = (\<integral>\<^sup>+ y. Pxy (x, y) \<partial>T) * indicator A x"
        by (simp add: eq positive_integral_multc cong: positive_integral_cong)
      also have "(\<integral>\<^sup>+ y. Pxy (x, y) \<partial>T) = Px x"
        by (simp add: Px_def ereal_real positive_integral_positive)
      finally show "(\<integral>\<^sup>+ y. Pxy (x, y) * indicator (A \<times> space T) (x, y) \<partial>T) = Px x * indicator A x" .
    qed
    finally show "emeasure (distr M S X) A = emeasure (density S Px) A"
      using A borel Pxy by (simp add: emeasure_density)
  qed simp
  
  show "AE x in S. 0 \<le> Px x"
    by (simp add: Px_def positive_integral_positive real_of_ereal_pos)
qed

lemma (in prob_space) distr_marginal2:
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "distributed M T Y (\<lambda>y. (\<integral>\<^sup>+x. Pxy (x, y) \<partial>S))"
  using distr_marginal1[OF T S distributed_swap[OF S T]] Pxy by simp

lemma (in prob_space) distributed_marginal_eq_joint1:
  assumes T: "sigma_finite_measure T"
  assumes S: "sigma_finite_measure S"
  assumes Px: "distributed M S X Px"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "AE x in S. Px x = (\<integral>\<^sup>+y. Pxy (x, y) \<partial>T)"
  using Px distr_marginal1[OF S T Pxy] by (rule distributed_unique)

lemma (in prob_space) distributed_marginal_eq_joint2:
  assumes T: "sigma_finite_measure T"
  assumes S: "sigma_finite_measure S"
  assumes Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "AE y in T. Py y = (\<integral>\<^sup>+x. Pxy (x, y) \<partial>S)"
  using Py distr_marginal2[OF S T Pxy] by (rule distributed_unique)

lemma (in prob_space) distributed_joint_indep':
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes X[measurable]: "distributed M S X Px" and Y[measurable]: "distributed M T Y Py"
  assumes indep: "distr M S X \<Otimes>\<^sub>M distr M T Y = distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
  shows "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) (\<lambda>(x, y). Px x * Py y)"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T by default

  interpret X: prob_space "density S Px"
    unfolding distributed_distr_eq_density[OF X, symmetric]
    by (rule prob_space_distr) simp
  have sf_X: "sigma_finite_measure (density S Px)" ..

  interpret Y: prob_space "density T Py"
    unfolding distributed_distr_eq_density[OF Y, symmetric]
    by (rule prob_space_distr) simp
  have sf_Y: "sigma_finite_measure (density T Py)" ..

  show "distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) = density (S \<Otimes>\<^sub>M T) (\<lambda>(x, y). Px x * Py y)"
    unfolding indep[symmetric] distributed_distr_eq_density[OF X] distributed_distr_eq_density[OF Y]
    using distributed_borel_measurable[OF X] distributed_AE[OF X]
    using distributed_borel_measurable[OF Y] distributed_AE[OF Y]
    by (rule pair_measure_density[OF _ _ _ _ T sf_Y])

  show "random_variable (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))" by auto

  show Pxy: "(\<lambda>(x, y). Px x * Py y) \<in> borel_measurable (S \<Otimes>\<^sub>M T)" by auto

  show "AE x in S \<Otimes>\<^sub>M T. 0 \<le> (case x of (x, y) \<Rightarrow> Px x * Py y)"
    apply (intro ST.AE_pair_measure borel_measurable_le Pxy borel_measurable_const)
    using distributed_AE[OF X]
    apply eventually_elim
    using distributed_AE[OF Y]
    apply eventually_elim
    apply auto
    done
qed

definition
  "simple_distributed M X f \<longleftrightarrow> distributed M (count_space (X`space M)) X (\<lambda>x. ereal (f x)) \<and>
    finite (X`space M)"

lemma simple_distributed:
  "simple_distributed M X Px \<Longrightarrow> distributed M (count_space (X`space M)) X Px"
  unfolding simple_distributed_def by auto

lemma simple_distributed_finite[dest]: "simple_distributed M X P \<Longrightarrow> finite (X`space M)"
  by (simp add: simple_distributed_def)

lemma (in prob_space) distributed_simple_function_superset:
  assumes X: "simple_function M X" "\<And>x. x \<in> X ` space M \<Longrightarrow> P x = measure M (X -` {x} \<inter> space M)"
  assumes A: "X`space M \<subseteq> A" "finite A"
  defines "S \<equiv> count_space A" and "P' \<equiv> (\<lambda>x. if x \<in> X`space M then P x else 0)"
  shows "distributed M S X P'"
  unfolding distributed_def
proof safe
  show "(\<lambda>x. ereal (P' x)) \<in> borel_measurable S" unfolding S_def by simp
  show "AE x in S. 0 \<le> ereal (P' x)"
    using X by (auto simp: S_def P'_def simple_distributed_def intro!: measure_nonneg)
  show "distr M S X = density S P'"
  proof (rule measure_eqI_finite)
    show "sets (distr M S X) = Pow A" "sets (density S P') = Pow A"
      using A unfolding S_def by auto
    show "finite A" by fact
    fix a assume a: "a \<in> A"
    then have "a \<notin> X`space M \<Longrightarrow> X -` {a} \<inter> space M = {}" by auto
    with A a X have "emeasure (distr M S X) {a} = P' a"
      by (subst emeasure_distr)
         (auto simp add: S_def P'_def simple_functionD emeasure_eq_measure measurable_count_space_eq2
               intro!: arg_cong[where f=prob])
    also have "\<dots> = (\<integral>\<^sup>+x. ereal (P' a) * indicator {a} x \<partial>S)"
      using A X a
      by (subst positive_integral_cmult_indicator)
         (auto simp: S_def P'_def simple_distributed_def simple_functionD measure_nonneg)
    also have "\<dots> = (\<integral>\<^sup>+x. ereal (P' x) * indicator {a} x \<partial>S)"
      by (auto simp: indicator_def intro!: positive_integral_cong)
    also have "\<dots> = emeasure (density S P') {a}"
      using a A by (intro emeasure_density[symmetric]) (auto simp: S_def)
    finally show "emeasure (distr M S X) {a} = emeasure (density S P') {a}" .
  qed
  show "random_variable S X"
    using X(1) A by (auto simp: measurable_def simple_functionD S_def)
qed

lemma (in prob_space) simple_distributedI:
  assumes X: "simple_function M X" "\<And>x. x \<in> X ` space M \<Longrightarrow> P x = measure M (X -` {x} \<inter> space M)"
  shows "simple_distributed M X P"
  unfolding simple_distributed_def
proof
  have "distributed M (count_space (X ` space M)) X (\<lambda>x. ereal (if x \<in> X`space M then P x else 0))"
    (is "?A")
    using simple_functionD[OF X(1)] by (intro distributed_simple_function_superset[OF X]) auto
  also have "?A \<longleftrightarrow> distributed M (count_space (X ` space M)) X (\<lambda>x. ereal (P x))"
    by (rule distributed_cong_density) auto
  finally show "\<dots>" .
qed (rule simple_functionD[OF X(1)])

lemma simple_distributed_joint_finite:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x)) Px"
  shows "finite (X ` space M)" "finite (Y ` space M)"
proof -
  have "finite ((\<lambda>x. (X x, Y x)) ` space M)"
    using X by (auto simp: simple_distributed_def simple_functionD)
  then have "finite (fst ` (\<lambda>x. (X x, Y x)) ` space M)" "finite (snd ` (\<lambda>x. (X x, Y x)) ` space M)"
    by auto
  then show fin: "finite (X ` space M)" "finite (Y ` space M)"
    by (auto simp: image_image)
qed

lemma simple_distributed_joint2_finite:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x, Z x)) Px"
  shows "finite (X ` space M)" "finite (Y ` space M)" "finite (Z ` space M)"
proof -
  have "finite ((\<lambda>x. (X x, Y x, Z x)) ` space M)"
    using X by (auto simp: simple_distributed_def simple_functionD)
  then have "finite (fst ` (\<lambda>x. (X x, Y x, Z x)) ` space M)"
    "finite ((fst \<circ> snd) ` (\<lambda>x. (X x, Y x, Z x)) ` space M)"
    "finite ((snd \<circ> snd) ` (\<lambda>x. (X x, Y x, Z x)) ` space M)"
    by auto
  then show fin: "finite (X ` space M)" "finite (Y ` space M)" "finite (Z ` space M)"
    by (auto simp: image_image)
qed

lemma simple_distributed_simple_function:
  "simple_distributed M X Px \<Longrightarrow> simple_function M X"
  unfolding simple_distributed_def distributed_def
  by (auto simp: simple_function_def measurable_count_space_eq2)

lemma simple_distributed_measure:
  "simple_distributed M X P \<Longrightarrow> a \<in> X`space M \<Longrightarrow> P a = measure M (X -` {a} \<inter> space M)"
  using distributed_count_space[of M "X`space M" X P a, symmetric]
  by (auto simp: simple_distributed_def measure_def)

lemma simple_distributed_nonneg: "simple_distributed M X f \<Longrightarrow> x \<in> space M \<Longrightarrow> 0 \<le> f (X x)"
  by (auto simp: simple_distributed_measure measure_nonneg)

lemma (in prob_space) simple_distributed_joint:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x)) Px"
  defines "S \<equiv> count_space (X`space M) \<Otimes>\<^sub>M count_space (Y`space M)"
  defines "P \<equiv> (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x))`space M then Px x else 0)"
  shows "distributed M S (\<lambda>x. (X x, Y x)) P"
proof -
  from simple_distributed_joint_finite[OF X, simp]
  have S_eq: "S = count_space (X`space M \<times> Y`space M)"
    by (simp add: S_def pair_measure_count_space)
  show ?thesis
    unfolding S_eq P_def
  proof (rule distributed_simple_function_superset)
    show "simple_function M (\<lambda>x. (X x, Y x))"
      using X by (rule simple_distributed_simple_function)
    fix x assume "x \<in> (\<lambda>x. (X x, Y x)) ` space M"
    from simple_distributed_measure[OF X this]
    show "Px x = prob ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M)" .
  qed auto
qed

lemma (in prob_space) simple_distributed_joint2:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x, Z x)) Px"
  defines "S \<equiv> count_space (X`space M) \<Otimes>\<^sub>M count_space (Y`space M) \<Otimes>\<^sub>M count_space (Z`space M)"
  defines "P \<equiv> (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x, Z x))`space M then Px x else 0)"
  shows "distributed M S (\<lambda>x. (X x, Y x, Z x)) P"
proof -
  from simple_distributed_joint2_finite[OF X, simp]
  have S_eq: "S = count_space (X`space M \<times> Y`space M \<times> Z`space M)"
    by (simp add: S_def pair_measure_count_space)
  show ?thesis
    unfolding S_eq P_def
  proof (rule distributed_simple_function_superset)
    show "simple_function M (\<lambda>x. (X x, Y x, Z x))"
      using X by (rule simple_distributed_simple_function)
    fix x assume "x \<in> (\<lambda>x. (X x, Y x, Z x)) ` space M"
    from simple_distributed_measure[OF X this]
    show "Px x = prob ((\<lambda>x. (X x, Y x, Z x)) -` {x} \<inter> space M)" .
  qed auto
qed

lemma (in prob_space) simple_distributed_setsum_space:
  assumes X: "simple_distributed M X f"
  shows "setsum f (X`space M) = 1"
proof -
  from X have "setsum f (X`space M) = prob (\<Union>i\<in>X`space M. X -` {i} \<inter> space M)"
    by (subst finite_measure_finite_Union)
       (auto simp add: disjoint_family_on_def simple_distributed_measure simple_distributed_simple_function simple_functionD
             intro!: setsum_cong arg_cong[where f="prob"])
  also have "\<dots> = prob (space M)"
    by (auto intro!: arg_cong[where f=prob])
  finally show ?thesis
    using emeasure_space_1 by (simp add: emeasure_eq_measure one_ereal_def)
qed

lemma (in prob_space) distributed_marginal_eq_joint_simple:
  assumes Px: "simple_function M X"
  assumes Py: "simple_distributed M Y Py"
  assumes Pxy: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
  assumes y: "y \<in> Y`space M"
  shows "Py y = (\<Sum>x\<in>X`space M. if (x, y) \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy (x, y) else 0)"
proof -
  note Px = simple_distributedI[OF Px refl]
  have *: "\<And>f A. setsum (\<lambda>x. max 0 (ereal (f x))) A = ereal (setsum (\<lambda>x. max 0 (f x)) A)"
    by (simp add: setsum_ereal[symmetric] zero_ereal_def)
  from distributed_marginal_eq_joint2[OF
    sigma_finite_measure_count_space_finite
    sigma_finite_measure_count_space_finite
    simple_distributed[OF Py] simple_distributed_joint[OF Pxy],
    OF Py[THEN simple_distributed_finite] Px[THEN simple_distributed_finite]]
    y
    Px[THEN simple_distributed_finite]
    Py[THEN simple_distributed_finite]
    Pxy[THEN simple_distributed, THEN distributed_real_AE]
  show ?thesis
    unfolding AE_count_space
    apply (auto simp add: positive_integral_count_space_finite * intro!: setsum_cong split: split_max)
    done
qed

lemma distributedI_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes gen: "sets M1 = sigma_sets (space M1) E" and "Int_stable E"
    and A: "range A \<subseteq> E" "(\<Union>i::nat. A i) = space M1" "\<And>i. emeasure (distr M M1 X) (A i) \<noteq> \<infinity>"
    and X: "X \<in> measurable M M1"
    and f: "f \<in> borel_measurable M1" "AE x in M1. 0 \<le> f x"
    and eq: "\<And>A. A \<in> E \<Longrightarrow> emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+ x. f x * indicator A x \<partial>M1)"
  shows "distributed M M1 X f"
  unfolding distributed_def
proof (intro conjI)
  show "distr M M1 X = density M1 f"
  proof (rule measure_eqI_generator_eq[where A=A])
    { fix A assume A: "A \<in> E"
      then have "A \<in> sigma_sets (space M1) E" by auto
      then have "A \<in> sets M1"
        using gen by simp
      with f A eq[of A] X show "emeasure (distr M M1 X) A = emeasure (density M1 f) A"
        by (simp add: emeasure_distr emeasure_density borel_measurable_ereal
                      times_ereal.simps[symmetric] ereal_indicator
                 del: times_ereal.simps) }
    note eq_E = this
    show "Int_stable E" by fact
    { fix e assume "e \<in> E"
      then have "e \<in> sigma_sets (space M1) E" by auto
      then have "e \<in> sets M1" unfolding gen .
      then have "e \<subseteq> space M1" by (rule sets.sets_into_space) }
    then show "E \<subseteq> Pow (space M1)" by auto
    show "sets (distr M M1 X) = sigma_sets (space M1) E"
      "sets (density M1 (\<lambda>x. ereal (f x))) = sigma_sets (space M1) E"
      unfolding gen[symmetric] by auto
  qed fact+
qed (insert X f, auto)

lemma distributedI_borel_atMost:
  fixes f :: "real \<Rightarrow> real"
  assumes [measurable]: "X \<in> borel_measurable M"
    and [measurable]: "f \<in> borel_measurable borel" and f[simp]: "AE x in lborel. 0 \<le> f x"
    and g_eq: "\<And>a. (\<integral>\<^sup>+x. f x * indicator {..a} x \<partial>lborel)  = ereal (g a)"
    and M_eq: "\<And>a. emeasure M {x\<in>space M. X x \<le> a} = ereal (g a)"
  shows "distributed M lborel X f"
proof (rule distributedI_real)
  show "sets lborel = sigma_sets (space lborel) (range atMost)"
    by (simp add: borel_eq_atMost)
  show "Int_stable (range atMost :: real set set)"
    by (auto simp: Int_stable_def)
  have vimage_eq: "\<And>a. (X -` {..a} \<inter> space M) = {x\<in>space M. X x \<le> a}" by auto
  def A \<equiv> "\<lambda>i::nat. {.. real i}"
  then show "range A \<subseteq> range atMost" "(\<Union>i. A i) = space lborel"
    "\<And>i. emeasure (distr M lborel X) (A i) \<noteq> \<infinity>"
    by (auto simp: real_arch_simple emeasure_distr vimage_eq M_eq)

  fix A :: "real set" assume "A \<in> range atMost"
  then obtain a where A: "A = {..a}" by auto
  show "emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>lborel)"
    unfolding vimage_eq A M_eq g_eq ..
qed auto

lemma (in prob_space) uniform_distributed_params:
  assumes X: "distributed M MX X (\<lambda>x. indicator A x / measure MX A)"
  shows "A \<in> sets MX" "measure MX A \<noteq> 0"
proof -
  interpret X: prob_space "distr M MX X"
    using distributed_measurable[OF X] by (rule prob_space_distr)

  show "measure MX A \<noteq> 0"
  proof
    assume "measure MX A = 0"
    with X.emeasure_space_1 X.prob_space distributed_distr_eq_density[OF X]
    show False
      by (simp add: emeasure_density zero_ereal_def[symmetric])
  qed
  with measure_notin_sets[of A MX] show "A \<in> sets MX"
    by blast
qed

lemma prob_space_uniform_measure:
  assumes A: "emeasure M A \<noteq> 0" "emeasure M A \<noteq> \<infinity>"
  shows "prob_space (uniform_measure M A)"
proof
  show "emeasure (uniform_measure M A) (space (uniform_measure M A)) = 1"
    using emeasure_uniform_measure[OF emeasure_neq_0_sets[OF A(1)], of "space M"]
    using sets.sets_into_space[OF emeasure_neq_0_sets[OF A(1)]] A
    by (simp add: Int_absorb2 emeasure_nonneg)
qed

lemma prob_space_uniform_count_measure: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> prob_space (uniform_count_measure A)"
  by default (auto simp: emeasure_uniform_count_measure space_uniform_count_measure one_ereal_def)

end
