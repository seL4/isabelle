(*  Title:      HOL/Probability/Probability_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Probability measure*}

theory Probability_Measure
  imports Lebesgue_Measure Radon_Nikodym
begin

lemma funset_eq_UN_fun_upd_I:
  assumes *: "\<And>f. f \<in> F (insert a A) \<Longrightarrow> f(a := d) \<in> F A"
  and **: "\<And>f. f \<in> F (insert a A) \<Longrightarrow> f a \<in> G (f(a:=d))"
  and ***: "\<And>f x. \<lbrakk> f \<in> F A ; x \<in> G f \<rbrakk> \<Longrightarrow> f(a:=x) \<in> F (insert a A)"
  shows "F (insert a A) = (\<Union>f\<in>F A. fun_upd f a ` (G f))"
proof safe
  fix f assume f: "f \<in> F (insert a A)"
  show "f \<in> (\<Union>f\<in>F A. fun_upd f a ` G f)"
  proof (rule UN_I[of "f(a := d)"])
    show "f(a := d) \<in> F A" using *[OF f] .
    show "f \<in> fun_upd (f(a:=d)) a ` G (f(a:=d))"
    proof (rule image_eqI[of _ _ "f a"])
      show "f a \<in> G (f(a := d))" using **[OF f] .
    qed simp
  qed
next
  fix f x assume "f \<in> F A" "x \<in> G f"
  from ***[OF this] show "f(a := x) \<in> F (insert a A)" .
qed

lemma extensional_funcset_insert_eq[simp]:
  assumes "a \<notin> A"
  shows "extensional (insert a A) \<inter> (insert a A \<rightarrow> B) = (\<Union>f \<in> extensional A \<inter> (A \<rightarrow> B). (\<lambda>b. f(a := b)) ` B)"
  apply (rule funset_eq_UN_fun_upd_I)
  using assms
  by (auto intro!: inj_onI dest: inj_onD split: split_if_asm simp: extensional_def)

lemma finite_extensional_funcset[simp, intro]:
  assumes "finite A" "finite B"
  shows "finite (extensional A \<inter> (A \<rightarrow> B))"
  using assms by induct auto

lemma finite_PiE[simp, intro]:
  assumes fin: "finite A" "\<And>i. i \<in> A \<Longrightarrow> finite (B i)"
  shows "finite (Pi\<^isub>E A B)"
proof -
  have *: "(Pi\<^isub>E A B) \<subseteq> extensional A \<inter> (A \<rightarrow> (\<Union>i\<in>A. B i))" by auto
  show ?thesis
    using fin by (intro finite_subset[OF *] finite_extensional_funcset) auto
qed


lemma countably_additiveI[case_names countably]:
  assumes "\<And>A. \<lbrakk> range A \<subseteq> M ; disjoint_family A ; (\<Union>i. A i) \<in> M\<rbrakk> \<Longrightarrow> (\<Sum>n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
  shows "countably_additive M \<mu>"
  using assms unfolding countably_additive_def by auto

lemma convex_le_Inf_differential:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex_on I f"
  assumes "x \<in> interior I" "y \<in> I"
  shows "f y \<ge> f x + Inf ((\<lambda>t. (f x - f t) / (x - t)) ` ({x<..} \<inter> I)) * (y - x)"
    (is "_ \<ge> _ + Inf (?F x) * (y - x)")
proof -
  show ?thesis
  proof (cases rule: linorder_cases)
    assume "x < y"
    moreover
    have "open (interior I)" by auto
    from openE[OF this `x \<in> interior I`] guess e . note e = this
    moreover def t \<equiv> "min (x + e / 2) ((x + y) / 2)"
    ultimately have "x < t" "t < y" "t \<in> ball x e"
      by (auto simp: dist_real_def field_simps split: split_min)
    with `x \<in> interior I` e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

    have "open (interior I)" by auto
    from openE[OF this `x \<in> interior I`] guess e .
    moreover def K \<equiv> "x - e / 2"
    with `0 < e` have "K \<in> ball x e" "K < x" by (auto simp: dist_real_def)
    ultimately have "K \<in> I" "K < x" "x \<in> I"
      using interior_subset[of I] `x \<in> interior I` by auto

    have "Inf (?F x) \<le> (f x - f y) / (x - y)"
    proof (rule Inf_lower2)
      show "(f x - f t) / (x - t) \<in> ?F x"
        using `t \<in> I` `x < t` by auto
      show "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
        using `convex_on I f` `x \<in> I` `y \<in> I` `x < t` `t < y` by (rule convex_on_diff)
    next
      fix y assume "y \<in> ?F x"
      with order_trans[OF convex_on_diff[OF `convex_on I f` `K \<in> I` _ `K < x` _]]
      show "(f K - f x) / (K - x) \<le> y" by auto
    qed
    then show ?thesis
      using `x < y` by (simp add: field_simps)
  next
    assume "y < x"
    moreover
    have "open (interior I)" by auto
    from openE[OF this `x \<in> interior I`] guess e . note e = this
    moreover def t \<equiv> "x + e / 2"
    ultimately have "x < t" "t \<in> ball x e"
      by (auto simp: dist_real_def field_simps)
    with `x \<in> interior I` e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

    have "(f x - f y) / (x - y) \<le> Inf (?F x)"
    proof (rule Inf_greatest)
      have "(f x - f y) / (x - y) = (f y - f x) / (y - x)"
        using `y < x` by (auto simp: field_simps)
      also
      fix z  assume "z \<in> ?F x"
      with order_trans[OF convex_on_diff[OF `convex_on I f` `y \<in> I` _ `y < x`]]
      have "(f y - f x) / (y - x) \<le> z" by auto
      finally show "(f x - f y) / (x - y) \<le> z" .
    next
      have "open (interior I)" by auto
      from openE[OF this `x \<in> interior I`] guess e . note e = this
      then have "x + e / 2 \<in> ball x e" by (auto simp: dist_real_def)
      with e interior_subset[of I] have "x + e / 2 \<in> {x<..} \<inter> I" by auto
      then show "?F x \<noteq> {}" by blast
    qed
    then show ?thesis
      using `y < x` by (simp add: field_simps)
  qed simp
qed

lemma distr_id[simp]: "distr N N (\<lambda>x. x) = N"
  by (rule measure_eqI) (auto simp: emeasure_distr)

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
abbreviation (in prob_space) "expectation \<equiv> integral\<^isup>L M"

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
    using `A \<in> events`[THEN sets_into_space] by auto
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

lemma (in prob_space) prob_space_increasing: "increasing M prob"
  by (auto intro!: finite_measure_mono simp: increasing_def)

lemma (in prob_space) prob_zero_union:
  assumes "s \<in> events" "t \<in> events" "prob t = 0"
  shows "prob (s \<union> t) = prob s"
using assms
proof -
  have "prob (s \<union> t) \<le> prob s"
    using finite_measure_subadditive[of s t] assms by auto
  moreover have "prob (s \<union> t) \<ge> prob s"
    using assms by (blast intro: finite_measure_mono)
  ultimately show ?thesis by simp
qed

lemma (in prob_space) prob_eq_compl:
  assumes "s \<in> events" "t \<in> events"
  assumes "prob (space M - s) = prob (space M - t)"
  shows "prob s = prob t"
  using assms prob_compl by auto

lemma (in prob_space) prob_one_inter:
  assumes events:"s \<in> events" "t \<in> events"
  assumes "prob t = 1"
  shows "prob (s \<inter> t) = prob s"
proof -
  have "prob ((space M - s) \<union> (space M - t)) = prob (space M - s)"
    using events assms  prob_compl[of "t"] by (auto intro!: prob_zero_union)
  also have "(space M - s) \<union> (space M - t) = space M - (s \<inter> t)"
    by blast
  finally show "prob (s \<inter> t) = prob s"
    using events by (auto intro!: prob_eq_compl[of "s \<inter> t" s])
qed

lemma (in prob_space) prob_eq_bigunion_image:
  assumes "range f \<subseteq> events" "range g \<subseteq> events"
  assumes "disjoint_family f" "disjoint_family g"
  assumes "\<And> n :: nat. prob (f n) = prob (g n)"
  shows "(prob (\<Union> i. f i) = prob (\<Union> i. g i))"
using assms
proof -
  have a: "(\<lambda> i. prob (f i)) sums (prob (\<Union> i. f i))"
    by (rule finite_measure_UNION[OF assms(1,3)])
  have b: "(\<lambda> i. prob (g i)) sums (prob (\<Union> i. g i))"
    by (rule finite_measure_UNION[OF assms(2,4)])
  show ?thesis using sums_unique[OF b] sums_unique[OF a] assms by simp
qed

lemma (in prob_space) prob_countably_zero:
  assumes "range c \<subseteq> events"
  assumes "\<And> i. prob (c i) = 0"
  shows "prob (\<Union> i :: nat. c i) = 0"
proof (rule antisym)
  show "prob (\<Union> i :: nat. c i) \<le> 0"
    using finite_measure_subadditive_countably[OF assms(1)] by (simp add: assms(2))
qed (simp add: measure_nonneg)

lemma (in prob_space) prob_equiprobable_finite_unions:
  assumes "s \<in> events"
  assumes s_finite: "finite s" "\<And>x. x \<in> s \<Longrightarrow> {x} \<in> events"
  assumes "\<And> x y. \<lbrakk>x \<in> s; y \<in> s\<rbrakk> \<Longrightarrow> (prob {x} = prob {y})"
  shows "prob s = real (card s) * prob {SOME x. x \<in> s}"
proof (cases "s = {}")
  case False hence "\<exists> x. x \<in> s" by blast
  from someI_ex[OF this] assms
  have prob_some: "\<And> x. x \<in> s \<Longrightarrow> prob {x} = prob {SOME y. y \<in> s}" by blast
  have "prob s = (\<Sum> x \<in> s. prob {x})"
    using finite_measure_eq_setsum_singleton[OF s_finite] by simp
  also have "\<dots> = (\<Sum> x \<in> s. prob {SOME y. y \<in> s})" using prob_some by auto
  also have "\<dots> = real (card s) * prob {(SOME x. x \<in> s)}"
    using setsum_constant assms by (simp add: real_eq_of_nat)
  finally show ?thesis by simp
qed simp

lemma (in prob_space) prob_real_sum_image_fn:
  assumes "e \<in> events"
  assumes "\<And> x. x \<in> s \<Longrightarrow> e \<inter> f x \<in> events"
  assumes "finite s"
  assumes disjoint: "\<And> x y. \<lbrakk>x \<in> s ; y \<in> s ; x \<noteq> y\<rbrakk> \<Longrightarrow> f x \<inter> f y = {}"
  assumes upper: "space M \<subseteq> (\<Union> i \<in> s. f i)"
  shows "prob e = (\<Sum> x \<in> s. prob (e \<inter> f x))"
proof -
  have e: "e = (\<Union> i \<in> s. e \<inter> f i)"
    using `e \<in> events` sets_into_space upper by blast
  hence "prob e = prob (\<Union> i \<in> s. e \<inter> f i)" by simp
  also have "\<dots> = (\<Sum> x \<in> s. prob (e \<inter> f x))"
  proof (rule finite_measure_finite_Union)
    show "finite s" by fact
    show "(\<lambda>i. e \<inter> f i)`s \<subseteq> events" using assms(2) by auto
    show "disjoint_family_on (\<lambda>i. e \<inter> f i) s"
      using disjoint by (auto simp: disjoint_family_on_def)
  qed
  finally show ?thesis .
qed

lemma (in prob_space) expectation_less:
  assumes [simp]: "integrable M X"
  assumes gt: "\<forall>x\<in>space M. X x < b"
  shows "expectation X < b"
proof -
  have "expectation X < expectation (\<lambda>x. b)"
    using gt emeasure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) expectation_greater:
  assumes [simp]: "integrable M X"
  assumes gt: "\<forall>x\<in>space M. a < X x"
  shows "a < expectation X"
proof -
  have "expectation (\<lambda>x. a) < expectation X"
    using gt emeasure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) jensens_inequality:
  fixes a b :: real
  assumes X: "integrable M X" "X ` space M \<subseteq> I"
  assumes I: "I = {a <..< b} \<or> I = {a <..} \<or> I = {..< b} \<or> I = UNIV"
  assumes q: "integrable M (\<lambda>x. q (X x))" "convex_on I q"
  shows "q (expectation X) \<le> expectation (\<lambda>x. q (X x))"
proof -
  let ?F = "\<lambda>x. Inf ((\<lambda>t. (q x - q t) / (x - t)) ` ({x<..} \<inter> I))"
  from not_empty X(2) have "I \<noteq> {}" by auto

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
      by (auto intro!: Sup_eq_maximum convex_le_Inf_differential image_eqI[OF _ y] simp: interior_open) }
  ultimately have "q (expectation X) = Sup ((\<lambda>x. q x + ?F x * (expectation X - x)) ` I)"
    by simp
  also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
  proof (rule Sup_least)
    show "(\<lambda>x. q x + ?F x * (expectation X - x)) ` I \<noteq> {}"
      using `I \<noteq> {}` by auto
  next
    fix k assume "k \<in> (\<lambda>x. q x + ?F x * (expectation X - x)) ` I"
    then guess x .. note x = this
    have "q x + ?F x * (expectation X  - x) = expectation (\<lambda>w. q x + ?F x * (X w - x))"
      using prob_space by (simp add: X)
    also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
      using `x \<in> I` `open I` X(2)
      by (intro integral_mono integral_add integral_cmult integral_diff
                lebesgue_integral_const X q convex_le_Inf_differential)
         (auto simp: interior_open)
    finally show "k \<le> expectation (\<lambda>w. q (X w))" using x by auto
  qed
  finally show "q (expectation X) \<le> expectation (\<lambda>x. q (X x))" .
qed

lemma (in prob_space) prob_x_eq_1_imp_prob_y_eq_0:
  assumes "{x} \<in> events"
  assumes "prob {x} = 1"
  assumes "{y} \<in> events"
  assumes "y \<noteq> x"
  shows "prob {y} = 0"
  using prob_one_inter[of "{y}" "{x}"] assms by auto

lemma (in prob_space) joint_distribution_Times_le_fst:
  "random_variable MX X \<Longrightarrow> random_variable MY Y \<Longrightarrow> A \<in> sets MX \<Longrightarrow> B \<in> sets MY
    \<Longrightarrow> emeasure (distr M (MX \<Otimes>\<^isub>M MY) (\<lambda>x. (X x, Y x))) (A \<times> B) \<le> emeasure (distr M MX X) A"
  by (auto simp: emeasure_distr measurable_pair_iff comp_def intro!: emeasure_mono measurable_sets)

lemma (in prob_space) joint_distribution_Times_le_snd:
  "random_variable MX X \<Longrightarrow> random_variable MY Y \<Longrightarrow> A \<in> sets MX \<Longrightarrow> B \<in> sets MY
    \<Longrightarrow> emeasure (distr M (MX \<Otimes>\<^isub>M MY) (\<lambda>x. (X x, Y x))) (A \<times> B) \<le> emeasure (distr M MY Y) B"
  by (auto simp: emeasure_distr measurable_pair_iff comp_def intro!: emeasure_mono measurable_sets)

locale pair_prob_space = pair_sigma_finite M1 M2 + M1: prob_space M1 + M2: prob_space M2 for M1 M2

sublocale pair_prob_space \<subseteq> P: prob_space "M1 \<Otimes>\<^isub>M M2"
proof
  show "emeasure (M1 \<Otimes>\<^isub>M M2) (space (M1 \<Otimes>\<^isub>M M2)) = 1"
    by (simp add: M2.emeasure_pair_measure_Times M1.emeasure_space_1 M2.emeasure_space_1 space_pair_measure)
qed

locale product_prob_space = product_sigma_finite M for M :: "'i \<Rightarrow> 'a measure" +
  fixes I :: "'i set"
  assumes prob_space: "\<And>i. prob_space (M i)"

sublocale product_prob_space \<subseteq> M: prob_space "M i" for i
  by (rule prob_space)

locale finite_product_prob_space = finite_product_sigma_finite M I + product_prob_space M I for M I

sublocale finite_product_prob_space \<subseteq> prob_space "\<Pi>\<^isub>M i\<in>I. M i"
proof
  show "emeasure (\<Pi>\<^isub>M i\<in>I. M i) (space (\<Pi>\<^isub>M i\<in>I. M i)) = 1"
    by (simp add: measure_times M.emeasure_space_1 setprod_1 space_PiM)
qed

lemma (in finite_product_prob_space) prob_times:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> sets (M i)"
  shows "prob (\<Pi>\<^isub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.prob i (X i))"
proof -
  have "ereal (measure (\<Pi>\<^isub>M i\<in>I. M i) (\<Pi>\<^isub>E i\<in>I. X i)) = emeasure (\<Pi>\<^isub>M i\<in>I. M i) (\<Pi>\<^isub>E i\<in>I. X i)"
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
  shows distributed_distr_eq_density: "distributed M N X f \<Longrightarrow> distr M N X = density N f"
    and distributed_measurable: "distributed M N X f \<Longrightarrow> X \<in> measurable M N"
    and distributed_borel_measurable: "distributed M N X f \<Longrightarrow> f \<in> borel_measurable N"
    and distributed_AE: "distributed M N X f \<Longrightarrow> (AE x in N. 0 \<le> f x)"
  by (simp_all add: distributed_def)

lemma
  shows distributed_real_measurable: "distributed M N X (\<lambda>x. ereal (f x)) \<Longrightarrow> f \<in> borel_measurable N"
    and distributed_real_AE: "distributed M N X (\<lambda>x. ereal (f x)) \<Longrightarrow> (AE x in N. 0 \<le> f x)"
  by (simp_all add: distributed_def borel_measurable_ereal_iff)

lemma distributed_count_space:
  assumes X: "distributed M (count_space A) X P" and a: "a \<in> A" and A: "finite A"
  shows "P a = emeasure M (X -` {a} \<inter> space M)"
proof -
  have "emeasure M (X -` {a} \<inter> space M) = emeasure (distr M (count_space A) X) {a}"
    using X a A by (simp add: distributed_measurable emeasure_distr)
  also have "\<dots> = emeasure (density (count_space A) P) {a}"
    using X by (simp add: distributed_distr_eq_density)
  also have "\<dots> = (\<integral>\<^isup>+x. P a * indicator {a} x \<partial>count_space A)"
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

lemma distributed_integral:
  "distributed M N X f \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> (\<integral>x. f x * g x \<partial>N) = (\<integral>x. g (X x) \<partial>M)"
  by (auto simp: distributed_real_measurable distributed_real_AE distributed_measurable
                 distributed_distr_eq_density[symmetric] integral_density[symmetric] integral_distr)
  
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

lemma distributed_marginal_eq_joint:
  assumes T: "sigma_finite_measure T"
  assumes S: "sigma_finite_measure S"
  assumes Px: "distributed M S X Px"
  assumes Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "AE y in T. Py y = (\<integral>\<^isup>+x. Pxy (x, y) \<partial>S)"
proof (rule sigma_finite_measure.density_unique[OF T])
  interpret ST: pair_sigma_finite S T using S T unfolding pair_sigma_finite_def by simp
  show "Py \<in> borel_measurable T" "AE y in T. 0 \<le> Py y"
    "(\<lambda>x. \<integral>\<^isup>+ xa. Pxy (xa, x) \<partial>S) \<in> borel_measurable T" "AE y in T. 0 \<le> \<integral>\<^isup>+ x. Pxy (x, y) \<partial>S"
    using Pxy[THEN distributed_borel_measurable]
    by (auto intro!: Py[THEN distributed_borel_measurable] Py[THEN distributed_AE]
                     ST.positive_integral_snd_measurable' positive_integral_positive)

  show "density T Py = density T (\<lambda>x. \<integral>\<^isup>+ xa. Pxy (xa, x) \<partial>S)"
  proof (rule measure_eqI)
    fix A assume A: "A \<in> sets (density T Py)"
    have *: "\<And>x y. x \<in> space S \<Longrightarrow> indicator (space S \<times> A) (x, y) = indicator A y"
      by (auto simp: indicator_def)
    have "emeasure (density T Py) A = emeasure (distr M T Y) A"
      unfolding Py[THEN distributed_distr_eq_density] ..
    also have "\<dots> = emeasure (distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))) (space S \<times> A)"
      using A Px Py Pxy
      by (subst (1 2) emeasure_distr)
         (auto dest: measurable_space distributed_measurable intro!: arg_cong[where f="emeasure M"])
    also have "\<dots> = emeasure (density (S \<Otimes>\<^isub>M T) Pxy) (space S \<times> A)"
      unfolding Pxy[THEN distributed_distr_eq_density] ..
    also have "\<dots> = (\<integral>\<^isup>+ x. Pxy x * indicator (space S \<times> A) x \<partial>(S \<Otimes>\<^isub>M T))"
      using A Pxy by (simp add: emeasure_density distributed_borel_measurable)
    also have "\<dots> = (\<integral>\<^isup>+y. \<integral>\<^isup>+x. Pxy (x, y) * indicator (space S \<times> A) (x, y) \<partial>S \<partial>T)"
      using A Pxy
      by (subst ST.positive_integral_snd_measurable) (simp_all add: emeasure_density distributed_borel_measurable)
    also have "\<dots> = (\<integral>\<^isup>+y. (\<integral>\<^isup>+x. Pxy (x, y) \<partial>S) * indicator A y \<partial>T)"
      using measurable_comp[OF measurable_Pair1[OF measurable_identity] distributed_borel_measurable[OF Pxy]]
      using distributed_borel_measurable[OF Pxy] distributed_AE[OF Pxy, THEN ST.AE_pair]
      by (subst (asm) ST.AE_commute) (auto intro!: positive_integral_cong_AE positive_integral_multc cong: positive_integral_cong simp: * comp_def)
    also have "\<dots> = emeasure (density T (\<lambda>x. \<integral>\<^isup>+ xa. Pxy (xa, x) \<partial>S)) A"
      using A by (intro emeasure_density[symmetric])  (auto intro!: ST.positive_integral_snd_measurable' Pxy[THEN distributed_borel_measurable])
    finally show "emeasure (density T Py) A = emeasure (density T (\<lambda>x. \<integral>\<^isup>+ xa. Pxy (xa, x) \<partial>S)) A" .
  qed simp
qed

lemma (in prob_space) distr_marginal1:
  fixes Pxy :: "('b \<times> 'c) \<Rightarrow> real"
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  defines "Px \<equiv> \<lambda>x. real (\<integral>\<^isup>+z. Pxy (x, z) \<partial>T)"
  shows "distributed M S X Px"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T by default

  have XY: "(\<lambda>x. (X x, Y x)) \<in> measurable M (S \<Otimes>\<^isub>M T)"
    using Pxy by (rule distributed_measurable)
  then show X: "X \<in> measurable M S"
    unfolding measurable_pair_iff by (simp add: comp_def)
  from XY have Y: "Y \<in> measurable M T"
    unfolding measurable_pair_iff by (simp add: comp_def)

  from Pxy show borel: "(\<lambda>x. ereal (Px x)) \<in> borel_measurable S"
    by (auto intro!: ST.positive_integral_fst_measurable borel_measurable_real_of_ereal dest!: distributed_real_measurable simp: Px_def)

  interpret Pxy: prob_space "distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
    using XY by (rule prob_space_distr)
  have "(\<integral>\<^isup>+ x. max 0 (ereal (- Pxy x)) \<partial>(S \<Otimes>\<^isub>M T)) = (\<integral>\<^isup>+ x. 0 \<partial>(S \<Otimes>\<^isub>M T))"
    using Pxy
    by (intro positive_integral_cong_AE) (auto simp: max_def dest: distributed_real_measurable distributed_real_AE)
  then have Pxy_integrable: "integrable (S \<Otimes>\<^isub>M T) Pxy"
    using Pxy Pxy.emeasure_space_1
    by (simp add: integrable_def emeasure_density positive_integral_max_0 distributed_def borel_measurable_ereal_iff cong: positive_integral_cong)
    
  show "distr M S X = density S Px"
  proof (rule measure_eqI)
    fix A assume A: "A \<in> sets (distr M S X)"
    with X Y XY have "emeasure (distr M S X) A = emeasure (distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))) (A \<times> space T)"
      by (auto simp add: emeasure_distr
               intro!: arg_cong[where f="emeasure M"] dest: measurable_space)
    also have "\<dots> = emeasure (density (S \<Otimes>\<^isub>M T) Pxy) (A \<times> space T)"
      using Pxy by (simp add: distributed_def)
    also have "\<dots> = \<integral>\<^isup>+ x. \<integral>\<^isup>+ y. ereal (Pxy (x, y)) * indicator (A \<times> space T) (x, y) \<partial>T \<partial>S"
      using A borel Pxy
      by (simp add: emeasure_density ST.positive_integral_fst_measurable(2)[symmetric] distributed_def)
    also have "\<dots> = \<integral>\<^isup>+ x. ereal (Px x) * indicator A x \<partial>S"
      apply (rule positive_integral_cong_AE)
      using Pxy[THEN distributed_real_AE, THEN ST.AE_pair] ST.integrable_fst_measurable(1)[OF Pxy_integrable] AE_space
    proof eventually_elim
      fix x assume "x \<in> space S" "AE y in T. 0 \<le> Pxy (x, y)" and i: "integrable T (\<lambda>y. Pxy (x, y))"
      moreover have eq: "\<And>y. y \<in> space T \<Longrightarrow> indicator (A \<times> space T) (x, y) = indicator A x"
        by (auto simp: indicator_def)
      ultimately have "(\<integral>\<^isup>+ y. ereal (Pxy (x, y)) * indicator (A \<times> space T) (x, y) \<partial>T) =
          (\<integral>\<^isup>+ y. ereal (Pxy (x, y)) \<partial>T) * indicator A x"
        using Pxy[THEN distributed_real_measurable] by (simp add: eq positive_integral_multc measurable_Pair2 cong: positive_integral_cong)
      also have "(\<integral>\<^isup>+ y. ereal (Pxy (x, y)) \<partial>T) = Px x"
        using i by (simp add: Px_def ereal_real integrable_def positive_integral_positive)
      finally show "(\<integral>\<^isup>+ y. ereal (Pxy (x, y)) * indicator (A \<times> space T) (x, y) \<partial>T) = ereal (Px x) * indicator A x" .
    qed
    finally show "emeasure (distr M S X) A = emeasure (density S Px) A"
      using A borel Pxy by (simp add: emeasure_density)
  qed simp
  
  show "AE x in S. 0 \<le> ereal (Px x)"
    by (simp add: Px_def positive_integral_positive real_of_ereal_pos)
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
         (auto simp add: S_def P'_def simple_functionD emeasure_eq_measure
               intro!: arg_cong[where f=prob])
    also have "\<dots> = (\<integral>\<^isup>+x. ereal (P' a) * indicator {a} x \<partial>S)"
      using A X a
      by (subst positive_integral_cmult_indicator)
         (auto simp: S_def P'_def simple_distributed_def simple_functionD measure_nonneg)
    also have "\<dots> = (\<integral>\<^isup>+x. ereal (P' x) * indicator {a} x \<partial>S)"
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
  by (auto simp: simple_function_def)

lemma simple_distributed_measure:
  "simple_distributed M X P \<Longrightarrow> a \<in> X`space M \<Longrightarrow> P a = measure M (X -` {a} \<inter> space M)"
  using distributed_count_space[of M "X`space M" X P a, symmetric]
  by (auto simp: simple_distributed_def measure_def)

lemma simple_distributed_nonneg: "simple_distributed M X f \<Longrightarrow> x \<in> space M \<Longrightarrow> 0 \<le> f (X x)"
  by (auto simp: simple_distributed_measure measure_nonneg)

lemma (in prob_space) simple_distributed_joint:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x)) Px"
  defines "S \<equiv> count_space (X`space M) \<Otimes>\<^isub>M count_space (Y`space M)"
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
  defines "S \<equiv> count_space (X`space M) \<Otimes>\<^isub>M count_space (Y`space M) \<Otimes>\<^isub>M count_space (Z`space M)"
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
  from distributed_marginal_eq_joint[OF sigma_finite_measure_count_space_finite sigma_finite_measure_count_space_finite
    simple_distributed[OF Px] simple_distributed[OF Py] simple_distributed_joint[OF Pxy],
    OF Py[THEN simple_distributed_finite] Px[THEN simple_distributed_finite]]
    y Px[THEN simple_distributed_finite] Py[THEN simple_distributed_finite]
    Pxy[THEN simple_distributed, THEN distributed_real_AE]
  show ?thesis
    unfolding AE_count_space
    apply (elim ballE[where x=y])
    apply (auto simp add: positive_integral_count_space_finite * intro!: setsum_cong split: split_max)
    done
qed


lemma prob_space_uniform_measure:
  assumes A: "emeasure M A \<noteq> 0" "emeasure M A \<noteq> \<infinity>"
  shows "prob_space (uniform_measure M A)"
proof
  show "emeasure (uniform_measure M A) (space (uniform_measure M A)) = 1"
    using emeasure_uniform_measure[OF emeasure_neq_0_sets[OF A(1)], of "space M"]
    using sets_into_space[OF emeasure_neq_0_sets[OF A(1)]] A
    by (simp add: Int_absorb2 emeasure_nonneg)
qed

lemma prob_space_uniform_count_measure: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> prob_space (uniform_count_measure A)"
  by default (auto simp: emeasure_uniform_count_measure space_uniform_count_measure one_ereal_def)

end
