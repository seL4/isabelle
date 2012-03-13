(*  Title:      HOL/Probability/Binary_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Binary product measures*}

theory Binary_Product_Measure
imports Lebesgue_Integration
begin

lemma times_eq_iff: "A \<times> B = C \<times> D \<longleftrightarrow> A = C \<and> B = D \<or> ((A = {} \<or> B = {}) \<and> (C = {} \<or> D = {}))"
  by auto

lemma times_Int_times: "A \<times> B \<inter> C \<times> D = (A \<inter> C) \<times> (B \<inter> D)"
  by auto

lemma Pair_vimage_times[simp]: "\<And>A B x. Pair x -` (A \<times> B) = (if x \<in> A then B else {})"
  by auto

lemma rev_Pair_vimage_times[simp]: "\<And>A B y. (\<lambda>x. (x, y)) -` (A \<times> B) = (if y \<in> B then A else {})"
  by auto

lemma case_prod_distrib: "f (case x of (x, y) \<Rightarrow> g x y) = (case x of (x, y) \<Rightarrow> f (g x y))"
  by (cases x) simp

lemma split_beta': "(\<lambda>(x,y). f x y) = (\<lambda>x. f (fst x) (snd x))"
  by (auto simp: fun_eq_iff)

section "Binary products"

definition
  "pair_measure_generator A B =
    \<lparr> space = space A \<times> space B,
      sets = {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B},
      measure = \<lambda>X. \<integral>\<^isup>+x. (\<integral>\<^isup>+y. indicator X (x,y) \<partial>B) \<partial>A \<rparr>"

definition pair_measure (infixr "\<Otimes>\<^isub>M" 80) where
  "A \<Otimes>\<^isub>M B = sigma (pair_measure_generator A B)"

locale pair_sigma_algebra = M1: sigma_algebra M1 + M2: sigma_algebra M2
  for M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"

abbreviation (in pair_sigma_algebra)
  "E \<equiv> pair_measure_generator M1 M2"

abbreviation (in pair_sigma_algebra)
  "P \<equiv> M1 \<Otimes>\<^isub>M M2"

lemma sigma_algebra_pair_measure:
  "sets M1 \<subseteq> Pow (space M1) \<Longrightarrow> sets M2 \<subseteq> Pow (space M2) \<Longrightarrow> sigma_algebra (pair_measure M1 M2)"
  by (force simp: pair_measure_def pair_measure_generator_def intro!: sigma_algebra_sigma)

sublocale pair_sigma_algebra \<subseteq> sigma_algebra P
  using M1.space_closed M2.space_closed
  by (rule sigma_algebra_pair_measure)

lemma pair_measure_generatorI[intro, simp]:
  "x \<in> sets A \<Longrightarrow> y \<in> sets B \<Longrightarrow> x \<times> y \<in> sets (pair_measure_generator A B)"
  by (auto simp add: pair_measure_generator_def)

lemma pair_measureI[intro, simp]:
  "x \<in> sets A \<Longrightarrow> y \<in> sets B \<Longrightarrow> x \<times> y \<in> sets (A \<Otimes>\<^isub>M B)"
  by (auto simp add: pair_measure_def)

lemma space_pair_measure:
  "space (A \<Otimes>\<^isub>M B) = space A \<times> space B"
  by (simp add: pair_measure_def pair_measure_generator_def)

lemma sets_pair_measure_generator:
  "sets (pair_measure_generator N M) = (\<lambda>(x, y). x \<times> y) ` (sets N \<times> sets M)"
  unfolding pair_measure_generator_def by auto

lemma pair_measure_generator_sets_into_space:
  assumes "sets M \<subseteq> Pow (space M)" "sets N \<subseteq> Pow (space N)"
  shows "sets (pair_measure_generator M N) \<subseteq> Pow (space (pair_measure_generator M N))"
  using assms by (auto simp: pair_measure_generator_def)

lemma pair_measure_generator_Int_snd:
  assumes "sets S1 \<subseteq> Pow (space S1)"
  shows "sets (pair_measure_generator S1 (algebra.restricted_space S2 A)) =
         sets (algebra.restricted_space (pair_measure_generator S1 S2) (space S1 \<times> A))"
  (is "?L = ?R")
  apply (auto simp: pair_measure_generator_def image_iff)
  using assms
  apply (rule_tac x="a \<times> xa" in exI)
  apply force
  using assms
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="b \<inter> A" in exI)
  apply auto
  done

lemma (in pair_sigma_algebra)
  shows measurable_fst[intro!, simp]:
    "fst \<in> measurable P M1" (is ?fst)
  and measurable_snd[intro!, simp]:
    "snd \<in> measurable P M2" (is ?snd)
proof -
  { fix X assume "X \<in> sets M1"
    then have "\<exists>X1\<in>sets M1. \<exists>X2\<in>sets M2. fst -` X \<inter> space M1 \<times> space M2 = X1 \<times> X2"
      apply - apply (rule bexI[of _ X]) apply (rule bexI[of _ "space M2"])
      using M1.sets_into_space by force+ }
  moreover
  { fix X assume "X \<in> sets M2"
    then have "\<exists>X1\<in>sets M1. \<exists>X2\<in>sets M2. snd -` X \<inter> space M1 \<times> space M2 = X1 \<times> X2"
      apply - apply (rule bexI[of _ "space M1"]) apply (rule bexI[of _ X])
      using M2.sets_into_space by force+ }
  ultimately have "?fst \<and> ?snd"
    by (fastforce simp: measurable_def sets_sigma space_pair_measure
                 intro!: sigma_sets.Basic)
  then show ?fst ?snd by auto
qed

lemma (in pair_sigma_algebra) measurable_pair_iff:
  assumes "sigma_algebra M"
  shows "f \<in> measurable M P \<longleftrightarrow>
    (fst \<circ> f) \<in> measurable M M1 \<and> (snd \<circ> f) \<in> measurable M M2"
proof -
  interpret M: sigma_algebra M by fact
  from assms show ?thesis
  proof (safe intro!: measurable_comp[where b=P])
    assume f: "(fst \<circ> f) \<in> measurable M M1" and s: "(snd \<circ> f) \<in> measurable M M2"
    show "f \<in> measurable M P" unfolding pair_measure_def
    proof (rule M.measurable_sigma)
      show "sets (pair_measure_generator M1 M2) \<subseteq> Pow (space E)"
        unfolding pair_measure_generator_def using M1.sets_into_space M2.sets_into_space by auto
      show "f \<in> space M \<rightarrow> space E"
        using f s by (auto simp: mem_Times_iff measurable_def comp_def space_sigma pair_measure_generator_def)
      fix A assume "A \<in> sets E"
      then obtain B C where "B \<in> sets M1" "C \<in> sets M2" "A = B \<times> C"
        unfolding pair_measure_generator_def by auto
      moreover have "(fst \<circ> f) -` B \<inter> space M \<in> sets M"
        using f `B \<in> sets M1` unfolding measurable_def by auto
      moreover have "(snd \<circ> f) -` C \<inter> space M \<in> sets M"
        using s `C \<in> sets M2` unfolding measurable_def by auto
      moreover have "f -` A \<inter> space M = ((fst \<circ> f) -` B \<inter> space M) \<inter> ((snd \<circ> f) -` C \<inter> space M)"
        unfolding `A = B \<times> C` by (auto simp: vimage_Times)
      ultimately show "f -` A \<inter> space M \<in> sets M" by auto
    qed
  qed
qed

lemma (in pair_sigma_algebra) measurable_pair:
  assumes "sigma_algebra M"
  assumes "(fst \<circ> f) \<in> measurable M M1" "(snd \<circ> f) \<in> measurable M M2"
  shows "f \<in> measurable M P"
  unfolding measurable_pair_iff[OF assms(1)] using assms(2,3) by simp

lemma pair_measure_generatorE:
  assumes "X \<in> sets (pair_measure_generator M1 M2)"
  obtains A B where "X = A \<times> B" "A \<in> sets M1" "B \<in> sets M2"
  using assms unfolding pair_measure_generator_def by auto

lemma (in pair_sigma_algebra) pair_measure_generator_swap:
  "(\<lambda>X. (\<lambda>(x,y). (y,x)) -` X \<inter> space M2 \<times> space M1) ` sets E = sets (pair_measure_generator M2 M1)"
proof (safe elim!: pair_measure_generatorE)
  fix A B assume "A \<in> sets M1" "B \<in> sets M2"
  moreover then have "(\<lambda>(x, y). (y, x)) -` (A \<times> B) \<inter> space M2 \<times> space M1 = B \<times> A"
    using M1.sets_into_space M2.sets_into_space by auto
  ultimately show "(\<lambda>(x, y). (y, x)) -` (A \<times> B) \<inter> space M2 \<times> space M1 \<in> sets (pair_measure_generator M2 M1)"
    by (auto intro: pair_measure_generatorI)
next
  fix A B assume "A \<in> sets M1" "B \<in> sets M2"
  then show "B \<times> A \<in> (\<lambda>X. (\<lambda>(x, y). (y, x)) -` X \<inter> space M2 \<times> space M1) ` sets E"
    using M1.sets_into_space M2.sets_into_space
    by (auto intro!: image_eqI[where x="A \<times> B"] pair_measure_generatorI)
qed

lemma (in pair_sigma_algebra) sets_pair_sigma_algebra_swap:
  assumes Q: "Q \<in> sets P"
  shows "(\<lambda>(x,y). (y, x)) -` Q \<in> sets (M2 \<Otimes>\<^isub>M M1)" (is "_ \<in> sets ?Q")
proof -
  let ?f = "\<lambda>Q. (\<lambda>(x,y). (y, x)) -` Q \<inter> space M2 \<times> space M1"
  have *: "(\<lambda>(x,y). (y, x)) -` Q = ?f Q"
    using sets_into_space[OF Q] by (auto simp: space_pair_measure)
  have "sets (M2 \<Otimes>\<^isub>M M1) = sets (sigma (pair_measure_generator M2 M1))"
    unfolding pair_measure_def ..
  also have "\<dots> = sigma_sets (space M2 \<times> space M1) (?f ` sets E)"
    unfolding sigma_def pair_measure_generator_swap[symmetric]
    by (simp add: pair_measure_generator_def)
  also have "\<dots> = ?f ` sigma_sets (space M1 \<times> space M2) (sets E)"
    using M1.sets_into_space M2.sets_into_space
    by (intro sigma_sets_vimage) (auto simp: pair_measure_generator_def)
  also have "\<dots> = ?f ` sets P"
    unfolding pair_measure_def pair_measure_generator_def sigma_def by simp
  finally show ?thesis
    using Q by (subst *) auto
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_swap_measurable:
  shows "(\<lambda>(x,y). (y, x)) \<in> measurable P (M2 \<Otimes>\<^isub>M M1)"
    (is "?f \<in> measurable ?P ?Q")
  unfolding measurable_def
proof (intro CollectI conjI Pi_I ballI)
  fix x assume "x \<in> space ?P" then show "(case x of (x, y) \<Rightarrow> (y, x)) \<in> space ?Q"
    unfolding pair_measure_generator_def pair_measure_def by auto
next
  fix A assume "A \<in> sets (M2 \<Otimes>\<^isub>M M1)"
  interpret Q: pair_sigma_algebra M2 M1 by default
  from Q.sets_pair_sigma_algebra_swap[OF `A \<in> sets (M2 \<Otimes>\<^isub>M M1)`]
  show "?f -` A \<inter> space ?P \<in> sets ?P" by simp
qed

lemma (in pair_sigma_algebra) measurable_cut_fst[simp,intro]:
  assumes "Q \<in> sets P" shows "Pair x -` Q \<in> sets M2"
proof -
  let ?Q' = "{Q. Q \<subseteq> space P \<and> Pair x -` Q \<in> sets M2}"
  let ?Q = "\<lparr> space = space P, sets = ?Q' \<rparr>"
  interpret Q: sigma_algebra ?Q
    proof qed (auto simp: vimage_UN vimage_Diff space_pair_measure)
  have "sets E \<subseteq> sets ?Q"
    using M1.sets_into_space M2.sets_into_space
    by (auto simp: pair_measure_generator_def space_pair_measure)
  then have "sets P \<subseteq> sets ?Q"
    apply (subst pair_measure_def, intro Q.sets_sigma_subset)
    by (simp add: pair_measure_def)
  with assms show ?thesis by auto
qed

lemma (in pair_sigma_algebra) measurable_cut_snd:
  assumes Q: "Q \<in> sets P" shows "(\<lambda>x. (x, y)) -` Q \<in> sets M1" (is "?cut Q \<in> sets M1")
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  from Q.measurable_cut_fst[OF sets_pair_sigma_algebra_swap[OF Q], of y]
  show ?thesis by (simp add: vimage_compose[symmetric] comp_def)
qed

lemma (in pair_sigma_algebra) measurable_pair_image_snd:
  assumes m: "f \<in> measurable P M" and "x \<in> space M1"
  shows "(\<lambda>y. f (x, y)) \<in> measurable M2 M"
  unfolding measurable_def
proof (intro CollectI conjI Pi_I ballI)
  fix y assume "y \<in> space M2" with `f \<in> measurable P M` `x \<in> space M1`
  show "f (x, y) \<in> space M"
    unfolding measurable_def pair_measure_generator_def pair_measure_def by auto
next
  fix A assume "A \<in> sets M"
  then have "Pair x -` (f -` A \<inter> space P) \<in> sets M2" (is "?C \<in> _")
    using `f \<in> measurable P M`
    by (intro measurable_cut_fst) (auto simp: measurable_def)
  also have "?C = (\<lambda>y. f (x, y)) -` A \<inter> space M2"
    using `x \<in> space M1` by (auto simp: pair_measure_generator_def pair_measure_def)
  finally show "(\<lambda>y. f (x, y)) -` A \<inter> space M2 \<in> sets M2" .
qed

lemma (in pair_sigma_algebra) measurable_pair_image_fst:
  assumes m: "f \<in> measurable P M" and "y \<in> space M2"
  shows "(\<lambda>x. f (x, y)) \<in> measurable M1 M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  from Q.measurable_pair_image_snd[OF measurable_comp `y \<in> space M2`,
                                      OF Q.pair_sigma_algebra_swap_measurable m]
  show ?thesis by simp
qed

lemma (in pair_sigma_algebra) Int_stable_pair_measure_generator: "Int_stable E"
  unfolding Int_stable_def
proof (intro ballI)
  fix A B assume "A \<in> sets E" "B \<in> sets E"
  then obtain A1 A2 B1 B2 where "A = A1 \<times> A2" "B = B1 \<times> B2"
    "A1 \<in> sets M1" "A2 \<in> sets M2" "B1 \<in> sets M1" "B2 \<in> sets M2"
    unfolding pair_measure_generator_def by auto
  then show "A \<inter> B \<in> sets E"
    by (auto simp add: times_Int_times pair_measure_generator_def)
qed

lemma finite_measure_cut_measurable:
  fixes M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"
  assumes "sigma_finite_measure M1" "finite_measure M2"
  assumes "Q \<in> sets (M1 \<Otimes>\<^isub>M M2)"
  shows "(\<lambda>x. measure M2 (Pair x -` Q)) \<in> borel_measurable M1"
    (is "?s Q \<in> _")
proof -
  interpret M1: sigma_finite_measure M1 by fact
  interpret M2: finite_measure M2 by fact
  interpret pair_sigma_algebra M1 M2 by default
  have [intro]: "sigma_algebra M1" by fact
  have [intro]: "sigma_algebra M2" by fact
  let ?D = "\<lparr> space = space P, sets = {A\<in>sets P. ?s A \<in> borel_measurable M1}  \<rparr>"
  note space_pair_measure[simp]
  interpret dynkin_system ?D
  proof (intro dynkin_systemI)
    fix A assume "A \<in> sets ?D" then show "A \<subseteq> space ?D"
      using sets_into_space by simp
  next
    from top show "space ?D \<in> sets ?D"
      by (auto simp add: if_distrib intro!: M1.measurable_If)
  next
    fix A assume "A \<in> sets ?D"
    with sets_into_space have "\<And>x. measure M2 (Pair x -` (space M1 \<times> space M2 - A)) =
        (if x \<in> space M1 then measure M2 (space M2) - ?s A x else 0)"
      by (auto intro!: M2.measure_compl simp: vimage_Diff)
    with `A \<in> sets ?D` top show "space ?D - A \<in> sets ?D"
      by (auto intro!: Diff M1.measurable_If M1.borel_measurable_ereal_diff)
  next
    fix F :: "nat \<Rightarrow> ('a\<times>'b) set" assume "disjoint_family F" "range F \<subseteq> sets ?D"
    moreover then have "\<And>x. measure M2 (\<Union>i. Pair x -` F i) = (\<Sum>i. ?s (F i) x)"
      by (intro M2.measure_countably_additive[symmetric])
         (auto simp: disjoint_family_on_def)
    ultimately show "(\<Union>i. F i) \<in> sets ?D"
      by (auto simp: vimage_UN intro!: M1.borel_measurable_psuminf)
  qed
  have "sets P = sets ?D" apply (subst pair_measure_def)
  proof (intro dynkin_lemma)
    show "Int_stable E" by (rule Int_stable_pair_measure_generator)
    from M1.sets_into_space have "\<And>A. A \<in> sets M1 \<Longrightarrow> {x \<in> space M1. x \<in> A} = A"
      by auto
    then show "sets E \<subseteq> sets ?D"
      by (auto simp: pair_measure_generator_def sets_sigma if_distrib
               intro: sigma_sets.Basic intro!: M1.measurable_If)
  qed (auto simp: pair_measure_def)
  with `Q \<in> sets P` have "Q \<in> sets ?D" by simp
  then show "?s Q \<in> borel_measurable M1" by simp
qed

subsection {* Binary products of $\sigma$-finite measure spaces *}

locale pair_sigma_finite = pair_sigma_algebra M1 M2 + M1: sigma_finite_measure M1 + M2: sigma_finite_measure M2
  for M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"

lemma (in pair_sigma_finite) measure_cut_measurable_fst:
  assumes "Q \<in> sets P" shows "(\<lambda>x. measure M2 (Pair x -` Q)) \<in> borel_measurable M1" (is "?s Q \<in> _")
proof -
  have [intro]: "sigma_algebra M1" and [intro]: "sigma_algebra M2" by default+
  have M1: "sigma_finite_measure M1" by default
  from M2.disjoint_sigma_finite guess F .. note F = this
  then have F_sets: "\<And>i. F i \<in> sets M2" by auto
  let ?C = "\<lambda>x i. F i \<inter> Pair x -` Q"
  { fix i
    let ?R = "M2.restricted_space (F i)"
    have [simp]: "space M1 \<times> F i \<inter> space M1 \<times> space M2 = space M1 \<times> F i"
      using F M2.sets_into_space by auto
    let ?R2 = "M2.restricted_space (F i)"
    have "(\<lambda>x. measure ?R2 (Pair x -` (space M1 \<times> space ?R2 \<inter> Q))) \<in> borel_measurable M1"
    proof (intro finite_measure_cut_measurable[OF M1])
      show "finite_measure ?R2"
        using F by (intro M2.restricted_to_finite_measure) auto
      have "(space M1 \<times> space ?R2) \<inter> Q \<in> (op \<inter> (space M1 \<times> F i)) ` sets P"
        using `Q \<in> sets P` by (auto simp: image_iff)
      also have "\<dots> = sigma_sets (space M1 \<times> F i) ((op \<inter> (space M1 \<times> F i)) ` sets E)"
        unfolding pair_measure_def pair_measure_generator_def sigma_def
        using `F i \<in> sets M2` M2.sets_into_space
        by (auto intro!: sigma_sets_Int sigma_sets.Basic)
      also have "\<dots> \<subseteq> sets (M1 \<Otimes>\<^isub>M ?R2)"
        using M1.sets_into_space
        apply (auto simp: times_Int_times pair_measure_def pair_measure_generator_def sigma_def
                    intro!: sigma_sets_subseteq)
        apply (rule_tac x="a" in exI)
        apply (rule_tac x="b \<inter> F i" in exI)
        by auto
      finally show "(space M1 \<times> space ?R2) \<inter> Q \<in> sets (M1 \<Otimes>\<^isub>M ?R2)" .
    qed
    moreover have "\<And>x. Pair x -` (space M1 \<times> F i \<inter> Q) = ?C x i"
      using `Q \<in> sets P` sets_into_space by (auto simp: space_pair_measure)
    ultimately have "(\<lambda>x. measure M2 (?C x i)) \<in> borel_measurable M1"
      by simp }
  moreover
  { fix x
    have "(\<Sum>i. measure M2 (?C x i)) = measure M2 (\<Union>i. ?C x i)"
    proof (intro M2.measure_countably_additive)
      show "range (?C x) \<subseteq> sets M2"
        using F `Q \<in> sets P` by (auto intro!: M2.Int)
      have "disjoint_family F" using F by auto
      show "disjoint_family (?C x)"
        by (rule disjoint_family_on_bisimulation[OF `disjoint_family F`]) auto
    qed
    also have "(\<Union>i. ?C x i) = Pair x -` Q"
      using F sets_into_space `Q \<in> sets P`
      by (auto simp: space_pair_measure)
    finally have "measure M2 (Pair x -` Q) = (\<Sum>i. measure M2 (?C x i))"
      by simp }
  ultimately show ?thesis using `Q \<in> sets P` F_sets
    by (auto intro!: M1.borel_measurable_psuminf M2.Int)
qed

lemma (in pair_sigma_finite) measure_cut_measurable_snd:
  assumes "Q \<in> sets P" shows "(\<lambda>y. M1.\<mu> ((\<lambda>x. (x, y)) -` Q)) \<in> borel_measurable M2"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  note sets_pair_sigma_algebra_swap[OF assms]
  from Q.measure_cut_measurable_fst[OF this]
  show ?thesis by (simp add: vimage_compose[symmetric] comp_def)
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_measurable:
  assumes "f \<in> measurable P M" shows "(\<lambda>(x,y). f (y, x)) \<in> measurable (M2 \<Otimes>\<^isub>M M1) M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  have *: "(\<lambda>(x,y). f (y, x)) = f \<circ> (\<lambda>(x,y). (y, x))" by (simp add: fun_eq_iff)
  show ?thesis
    using Q.pair_sigma_algebra_swap_measurable assms
    unfolding * by (rule measurable_comp)
qed

lemma (in pair_sigma_finite) pair_measure_alt:
  assumes "A \<in> sets P"
  shows "measure (M1 \<Otimes>\<^isub>M M2) A = (\<integral>\<^isup>+ x. measure M2 (Pair x -` A) \<partial>M1)"
  apply (simp add: pair_measure_def pair_measure_generator_def)
proof (rule M1.positive_integral_cong)
  fix x assume "x \<in> space M1"
  have *: "\<And>y. indicator A (x, y) = (indicator (Pair x -` A) y :: ereal)"
    unfolding indicator_def by auto
  show "(\<integral>\<^isup>+ y. indicator A (x, y) \<partial>M2) = measure M2 (Pair x -` A)"
    unfolding *
    apply (subst M2.positive_integral_indicator)
    apply (rule measurable_cut_fst[OF assms])
    by simp
qed

lemma (in pair_sigma_finite) pair_measure_times:
  assumes A: "A \<in> sets M1" and "B \<in> sets M2"
  shows "measure (M1 \<Otimes>\<^isub>M M2) (A \<times> B) = M1.\<mu> A * measure M2 B"
proof -
  have "measure (M1 \<Otimes>\<^isub>M M2) (A \<times> B) = (\<integral>\<^isup>+ x. measure M2 B * indicator A x \<partial>M1)"
    using assms by (auto intro!: M1.positive_integral_cong simp: pair_measure_alt)
  with assms show ?thesis
    by (simp add: M1.positive_integral_cmult_indicator ac_simps)
qed

lemma (in measure_space) measure_not_negative[simp,intro]:
  assumes A: "A \<in> sets M" shows "\<mu> A \<noteq> - \<infinity>"
  using positive_measure[OF A] by auto

lemma (in pair_sigma_finite) sigma_finite_up_in_pair_measure_generator:
  "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> sets E \<and> incseq F \<and> (\<Union>i. F i) = space E \<and>
    (\<forall>i. measure (M1 \<Otimes>\<^isub>M M2) (F i) \<noteq> \<infinity>)"
proof -
  obtain F1 :: "nat \<Rightarrow> 'a set" and F2 :: "nat \<Rightarrow> 'b set" where
    F1: "range F1 \<subseteq> sets M1" "incseq F1" "(\<Union>i. F1 i) = space M1" "\<And>i. M1.\<mu> (F1 i) \<noteq> \<infinity>" and
    F2: "range F2 \<subseteq> sets M2" "incseq F2" "(\<Union>i. F2 i) = space M2" "\<And>i. M2.\<mu> (F2 i) \<noteq> \<infinity>"
    using M1.sigma_finite_up M2.sigma_finite_up by auto
  then have space: "space M1 = (\<Union>i. F1 i)" "space M2 = (\<Union>i. F2 i)" by auto
  let ?F = "\<lambda>i. F1 i \<times> F2 i"
  show ?thesis unfolding space_pair_measure
  proof (intro exI[of _ ?F] conjI allI)
    show "range ?F \<subseteq> sets E" using F1 F2
      by (fastforce intro!: pair_measure_generatorI)
  next
    have "space M1 \<times> space M2 \<subseteq> (\<Union>i. ?F i)"
    proof (intro subsetI)
      fix x assume "x \<in> space M1 \<times> space M2"
      then obtain i j where "fst x \<in> F1 i" "snd x \<in> F2 j"
        by (auto simp: space)
      then have "fst x \<in> F1 (max i j)" "snd x \<in> F2 (max j i)"
        using `incseq F1` `incseq F2` unfolding incseq_def
        by (force split: split_max)+
      then have "(fst x, snd x) \<in> F1 (max i j) \<times> F2 (max i j)"
        by (intro SigmaI) (auto simp add: min_max.sup_commute)
      then show "x \<in> (\<Union>i. ?F i)" by auto
    qed
    then show "(\<Union>i. ?F i) = space E"
      using space by (auto simp: space pair_measure_generator_def)
  next
    fix i show "incseq (\<lambda>i. F1 i \<times> F2 i)"
      using `incseq F1` `incseq F2` unfolding incseq_Suc_iff by auto
  next
    fix i
    from F1 F2 have "F1 i \<in> sets M1" "F2 i \<in> sets M2" by auto
    with F1 F2 M1.positive_measure[OF this(1)] M2.positive_measure[OF this(2)]
    show "measure P (F1 i \<times> F2 i) \<noteq> \<infinity>"
      by (simp add: pair_measure_times)
  qed
qed

sublocale pair_sigma_finite \<subseteq> sigma_finite_measure P
proof
  show "positive P (measure P)"
    unfolding pair_measure_def pair_measure_generator_def sigma_def positive_def
    by (auto intro: M1.positive_integral_positive M2.positive_integral_positive)

  show "countably_additive P (measure P)"
    unfolding countably_additive_def
  proof (intro allI impI)
    fix F :: "nat \<Rightarrow> ('a \<times> 'b) set"
    assume F: "range F \<subseteq> sets P" "disjoint_family F"
    from F have *: "\<And>i. F i \<in> sets P" "(\<Union>i. F i) \<in> sets P" by auto
    moreover from F have "\<And>i. (\<lambda>x. measure M2 (Pair x -` F i)) \<in> borel_measurable M1"
      by (intro measure_cut_measurable_fst) auto
    moreover have "\<And>x. disjoint_family (\<lambda>i. Pair x -` F i)"
      by (intro disjoint_family_on_bisimulation[OF F(2)]) auto
    moreover have "\<And>x. x \<in> space M1 \<Longrightarrow> range (\<lambda>i. Pair x -` F i) \<subseteq> sets M2"
      using F by auto
    ultimately show "(\<Sum>n. measure P (F n)) = measure P (\<Union>i. F i)"
      by (simp add: pair_measure_alt vimage_UN M1.positive_integral_suminf[symmetric]
                    M2.measure_countably_additive
               cong: M1.positive_integral_cong)
  qed

  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  show "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> sets P \<and> (\<Union>i. F i) = space P \<and> (\<forall>i. measure P (F i) \<noteq> \<infinity>)"
  proof (rule exI[of _ F], intro conjI)
    show "range F \<subseteq> sets P" using F by (auto simp: pair_measure_def)
    show "(\<Union>i. F i) = space P"
      using F by (auto simp: pair_measure_def pair_measure_generator_def)
    show "\<forall>i. measure P (F i) \<noteq> \<infinity>" using F by auto
  qed
qed

lemma (in pair_sigma_algebra) sets_swap:
  assumes "A \<in> sets P"
  shows "(\<lambda>(x, y). (y, x)) -` A \<inter> space (M2 \<Otimes>\<^isub>M M1) \<in> sets (M2 \<Otimes>\<^isub>M M1)"
    (is "_ -` A \<inter> space ?Q \<in> sets ?Q")
proof -
  have *: "(\<lambda>(x, y). (y, x)) -` A \<inter> space ?Q = (\<lambda>(x, y). (y, x)) -` A"
    using `A \<in> sets P` sets_into_space by (auto simp: space_pair_measure)
  show ?thesis
    unfolding * using assms by (rule sets_pair_sigma_algebra_swap)
qed

lemma (in pair_sigma_finite) pair_measure_alt2:
  assumes A: "A \<in> sets P"
  shows "\<mu> A = (\<integral>\<^isup>+y. M1.\<mu> ((\<lambda>x. (x, y)) -` A) \<partial>M2)"
    (is "_ = ?\<nu> A")
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  have [simp]: "\<And>m. \<lparr> space = space E, sets = sets (sigma E), measure = m \<rparr> = P\<lparr> measure := m \<rparr>"
    unfolding pair_measure_def by simp

  have "\<mu> A = Q.\<mu> ((\<lambda>(y, x). (x, y)) -` A \<inter> space Q.P)"
  proof (rule measure_unique_Int_stable_vimage[OF Int_stable_pair_measure_generator])
    show "measure_space P" "measure_space Q.P" by default
    show "(\<lambda>(y, x). (x, y)) \<in> measurable Q.P P" by (rule Q.pair_sigma_algebra_swap_measurable)
    show "sets (sigma E) = sets P" "space E = space P" "A \<in> sets (sigma E)"
      using assms unfolding pair_measure_def by auto
    show "range F \<subseteq> sets E" "incseq F" "(\<Union>i. F i) = space E" "\<And>i. \<mu> (F i) \<noteq> \<infinity>"
      using F `A \<in> sets P` by (auto simp: pair_measure_def)
    fix X assume "X \<in> sets E"
    then obtain A B where X[simp]: "X = A \<times> B" and AB: "A \<in> sets M1" "B \<in> sets M2"
      unfolding pair_measure_def pair_measure_generator_def by auto
    then have "(\<lambda>(y, x). (x, y)) -` X \<inter> space Q.P = B \<times> A"
      using M1.sets_into_space M2.sets_into_space by (auto simp: space_pair_measure)
    then show "\<mu> X = Q.\<mu> ((\<lambda>(y, x). (x, y)) -` X \<inter> space Q.P)"
      using AB by (simp add: pair_measure_times Q.pair_measure_times ac_simps)
  qed
  then show ?thesis
    using sets_into_space[OF A] Q.pair_measure_alt[OF sets_swap[OF A]]
    by (auto simp add: Q.pair_measure_alt space_pair_measure
             intro!: M2.positive_integral_cong arg_cong[where f="M1.\<mu>"])
qed

lemma pair_sigma_algebra_sigma:
  assumes 1: "incseq S1" "(\<Union>i. S1 i) = space E1" "range S1 \<subseteq> sets E1" and E1: "sets E1 \<subseteq> Pow (space E1)"
  assumes 2: "decseq S2" "(\<Union>i. S2 i) = space E2" "range S2 \<subseteq> sets E2" and E2: "sets E2 \<subseteq> Pow (space E2)"
  shows "sets (sigma (pair_measure_generator (sigma E1) (sigma E2))) = sets (sigma (pair_measure_generator E1 E2))"
    (is "sets ?S = sets ?E")
proof -
  interpret M1: sigma_algebra "sigma E1" using E1 by (rule sigma_algebra_sigma)
  interpret M2: sigma_algebra "sigma E2" using E2 by (rule sigma_algebra_sigma)
  have P: "sets (pair_measure_generator E1 E2) \<subseteq> Pow (space E1 \<times> space E2)"
    using E1 E2 by (auto simp add: pair_measure_generator_def)
  interpret E: sigma_algebra ?E unfolding pair_measure_generator_def
    using E1 E2 by (intro sigma_algebra_sigma) auto
  { fix A assume "A \<in> sets E1"
    then have "fst -` A \<inter> space ?E = A \<times> (\<Union>i. S2 i)"
      using E1 2 unfolding pair_measure_generator_def by auto
    also have "\<dots> = (\<Union>i. A \<times> S2 i)" by auto
    also have "\<dots> \<in> sets ?E" unfolding pair_measure_generator_def sets_sigma
      using 2 `A \<in> sets E1`
      by (intro sigma_sets.Union)
         (force simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "fst -` A \<inter> space ?E \<in> sets ?E" . }
  moreover
  { fix B assume "B \<in> sets E2"
    then have "snd -` B \<inter> space ?E = (\<Union>i. S1 i) \<times> B"
      using E2 1 unfolding pair_measure_generator_def by auto
    also have "\<dots> = (\<Union>i. S1 i \<times> B)" by auto
    also have "\<dots> \<in> sets ?E"
      using 1 `B \<in> sets E2` unfolding pair_measure_generator_def sets_sigma
      by (intro sigma_sets.Union)
         (force simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "snd -` B \<inter> space ?E \<in> sets ?E" . }
  ultimately have proj:
    "fst \<in> measurable ?E (sigma E1) \<and> snd \<in> measurable ?E (sigma E2)"
    using E1 E2 by (subst (1 2) E.measurable_iff_sigma)
                   (auto simp: pair_measure_generator_def sets_sigma)
  { fix A B assume A: "A \<in> sets (sigma E1)" and B: "B \<in> sets (sigma E2)"
    with proj have "fst -` A \<inter> space ?E \<in> sets ?E" "snd -` B \<inter> space ?E \<in> sets ?E"
      unfolding measurable_def by simp_all
    moreover have "A \<times> B = (fst -` A \<inter> space ?E) \<inter> (snd -` B \<inter> space ?E)"
      using A B M1.sets_into_space M2.sets_into_space
      by (auto simp: pair_measure_generator_def)
    ultimately have "A \<times> B \<in> sets ?E" by auto }
  then have "sigma_sets (space ?E) (sets (pair_measure_generator (sigma E1) (sigma E2))) \<subseteq> sets ?E"
    by (intro E.sigma_sets_subset) (auto simp add: pair_measure_generator_def sets_sigma)
  then have subset: "sets ?S \<subseteq> sets ?E"
    by (simp add: sets_sigma pair_measure_generator_def)
  show "sets ?S = sets ?E"
  proof (intro set_eqI iffI)
    fix A assume "A \<in> sets ?E" then show "A \<in> sets ?S"
      unfolding sets_sigma
    proof induct
      case (Basic A) then show ?case
        by (auto simp: pair_measure_generator_def sets_sigma intro: sigma_sets.Basic)
    qed (auto intro: sigma_sets.intros simp: pair_measure_generator_def)
  next
    fix A assume "A \<in> sets ?S" then show "A \<in> sets ?E" using subset by auto
  qed
qed

section "Fubinis theorem"

lemma (in pair_sigma_finite) simple_function_cut:
  assumes f: "simple_function P f" "\<And>x. 0 \<le> f x"
  shows "(\<lambda>x. \<integral>\<^isup>+y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
    and "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f"
proof -
  have f_borel: "f \<in> borel_measurable P"
    using f(1) by (rule borel_measurable_simple_function)
  let ?F = "\<lambda>z. f -` {z} \<inter> space P"
  let ?F' = "\<lambda>x z. Pair x -` ?F z"
  { fix x assume "x \<in> space M1"
    have [simp]: "\<And>z y. indicator (?F z) (x, y) = indicator (?F' x z) y"
      by (auto simp: indicator_def)
    have "\<And>y. y \<in> space M2 \<Longrightarrow> (x, y) \<in> space P" using `x \<in> space M1`
      by (simp add: space_pair_measure)
    moreover have "\<And>x z. ?F' x z \<in> sets M2" using f_borel
      by (intro borel_measurable_vimage measurable_cut_fst)
    ultimately have "simple_function M2 (\<lambda> y. f (x, y))"
      apply (rule_tac M2.simple_function_cong[THEN iffD2, OF _])
      apply (rule simple_function_indicator_representation[OF f(1)])
      using `x \<in> space M1` by (auto simp del: space_sigma) }
  note M2_sf = this
  { fix x assume x: "x \<in> space M1"
    then have "(\<integral>\<^isup>+y. f (x, y) \<partial>M2) = (\<Sum>z\<in>f ` space P. z * M2.\<mu> (?F' x z))"
      unfolding M2.positive_integral_eq_simple_integral[OF M2_sf[OF x] f(2)]
      unfolding simple_integral_def
    proof (safe intro!: setsum_mono_zero_cong_left)
      from f(1) show "finite (f ` space P)" by (rule simple_functionD)
    next
      fix y assume "y \<in> space M2" then show "f (x, y) \<in> f ` space P"
        using `x \<in> space M1` by (auto simp: space_pair_measure)
    next
      fix x' y assume "(x', y) \<in> space P"
        "f (x', y) \<notin> (\<lambda>y. f (x, y)) ` space M2"
      then have *: "?F' x (f (x', y)) = {}"
        by (force simp: space_pair_measure)
      show  "f (x', y) * M2.\<mu> (?F' x (f (x', y))) = 0"
        unfolding * by simp
    qed (simp add: vimage_compose[symmetric] comp_def
                   space_pair_measure) }
  note eq = this
  moreover have "\<And>z. ?F z \<in> sets P"
    by (auto intro!: f_borel borel_measurable_vimage simp del: space_sigma)
  moreover then have "\<And>z. (\<lambda>x. M2.\<mu> (?F' x z)) \<in> borel_measurable M1"
    by (auto intro!: measure_cut_measurable_fst simp del: vimage_Int)
  moreover have *: "\<And>i x. 0 \<le> M2.\<mu> (Pair x -` (f -` {i} \<inter> space P))"
    using f(1)[THEN simple_functionD(2)] f(2) by (intro M2.positive_measure measurable_cut_fst)
  moreover { fix i assume "i \<in> f`space P"
    with * have "\<And>x. 0 \<le> i * M2.\<mu> (Pair x -` (f -` {i} \<inter> space P))"
      using f(2) by auto }
  ultimately
  show "(\<lambda>x. \<integral>\<^isup>+y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
    and "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f" using f(2)
    by (auto simp del: vimage_Int cong: measurable_cong
             intro!: M1.borel_measurable_ereal_setsum setsum_cong
             simp add: M1.positive_integral_setsum simple_integral_def
                       M1.positive_integral_cmult
                       M1.positive_integral_cong[OF eq]
                       positive_integral_eq_simple_integral[OF f]
                       pair_measure_alt[symmetric])
qed

lemma (in pair_sigma_finite) positive_integral_fst_measurable:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<lambda>x. \<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
      (is "?C f \<in> borel_measurable M1")
    and "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f"
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f] guess F . note F = this
  then have F_borel: "\<And>i. F i \<in> borel_measurable P"
    by (auto intro: borel_measurable_simple_function)
  note sf = simple_function_cut[OF F(1,5)]
  then have "(\<lambda>x. SUP i. ?C (F i) x) \<in> borel_measurable M1"
    using F(1) by auto
  moreover
  { fix x assume "x \<in> space M1"
    from F measurable_pair_image_snd[OF F_borel`x \<in> space M1`]
    have "(\<integral>\<^isup>+y. (SUP i. F i (x, y)) \<partial>M2) = (SUP i. ?C (F i) x)"
      by (intro M2.positive_integral_monotone_convergence_SUP)
         (auto simp: incseq_Suc_iff le_fun_def)
    then have "(SUP i. ?C (F i) x) = ?C f x"
      unfolding F(4) positive_integral_max_0 by simp }
  note SUPR_C = this
  ultimately show "?C f \<in> borel_measurable M1"
    by (simp cong: measurable_cong)
  have "(\<integral>\<^isup>+x. (SUP i. F i x) \<partial>P) = (SUP i. integral\<^isup>P P (F i))"
    using F_borel F
    by (intro positive_integral_monotone_convergence_SUP) auto
  also have "(SUP i. integral\<^isup>P P (F i)) = (SUP i. \<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. F i (x, y) \<partial>M2) \<partial>M1)"
    unfolding sf(2) by simp
  also have "\<dots> = \<integral>\<^isup>+ x. (SUP i. \<integral>\<^isup>+ y. F i (x, y) \<partial>M2) \<partial>M1" using F sf(1)
    by (intro M1.positive_integral_monotone_convergence_SUP[symmetric])
       (auto intro!: M2.positive_integral_mono M2.positive_integral_positive
                simp: incseq_Suc_iff le_fun_def)
  also have "\<dots> = \<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. (SUP i. F i (x, y)) \<partial>M2) \<partial>M1"
    using F_borel F(2,5)
    by (auto intro!: M1.positive_integral_cong M2.positive_integral_monotone_convergence_SUP[symmetric]
             simp: incseq_Suc_iff le_fun_def measurable_pair_image_snd)
  finally show "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f"
    using F by (simp add: positive_integral_max_0)
qed

lemma (in pair_sigma_finite) measure_preserving_swap:
  "(\<lambda>(x,y). (y, x)) \<in> measure_preserving (M1 \<Otimes>\<^isub>M M2) (M2 \<Otimes>\<^isub>M M1)"
proof
  interpret Q: pair_sigma_finite M2 M1 by default
  show *: "(\<lambda>(x,y). (y, x)) \<in> measurable (M1 \<Otimes>\<^isub>M M2) (M2 \<Otimes>\<^isub>M M1)"
    using pair_sigma_algebra_swap_measurable .
  fix X assume "X \<in> sets (M2 \<Otimes>\<^isub>M M1)"
  from measurable_sets[OF * this] this Q.sets_into_space[OF this]
  show "measure (M1 \<Otimes>\<^isub>M M2) ((\<lambda>(x, y). (y, x)) -` X \<inter> space P) = measure (M2 \<Otimes>\<^isub>M M1) X"
    by (auto intro!: M1.positive_integral_cong arg_cong[where f="M2.\<mu>"]
      simp: pair_measure_alt Q.pair_measure_alt2 space_pair_measure)
qed

lemma (in pair_sigma_finite) positive_integral_product_swap:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<integral>\<^isup>+x. f (case x of (x,y)\<Rightarrow>(y,x)) \<partial>(M2 \<Otimes>\<^isub>M M1)) = integral\<^isup>P P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have "sigma_algebra P" by default
  with f show ?thesis
    by (subst Q.positive_integral_vimage[OF _ Q.measure_preserving_swap]) auto
qed

lemma (in pair_sigma_finite) positive_integral_snd_measurable:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<integral>\<^isup>+ y. (\<integral>\<^isup>+ x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^isup>P P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  note pair_sigma_algebra_measurable[OF f]
  from Q.positive_integral_fst_measurable[OF this]
  have "(\<integral>\<^isup>+ y. (\<integral>\<^isup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^isup>+ (x, y). f (y, x) \<partial>Q.P)"
    by simp
  also have "(\<integral>\<^isup>+ (x, y). f (y, x) \<partial>Q.P) = integral\<^isup>P P f"
    unfolding positive_integral_product_swap[OF f, symmetric]
    by (auto intro!: Q.positive_integral_cong)
  finally show ?thesis .
qed

lemma (in pair_sigma_finite) Fubini:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<integral>\<^isup>+ y. (\<integral>\<^isup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1)"
  unfolding positive_integral_snd_measurable[OF assms]
  unfolding positive_integral_fst_measurable[OF assms] ..

lemma (in pair_sigma_finite) AE_pair:
  assumes "AE x in P. Q x"
  shows "AE x in M1. (AE y in M2. Q (x, y))"
proof -
  obtain N where N: "N \<in> sets P" "\<mu> N = 0" "{x\<in>space P. \<not> Q x} \<subseteq> N"
    using assms unfolding almost_everywhere_def by auto
  show ?thesis
  proof (rule M1.AE_I)
    from N measure_cut_measurable_fst[OF `N \<in> sets P`]
    show "M1.\<mu> {x\<in>space M1. M2.\<mu> (Pair x -` N) \<noteq> 0} = 0"
      by (auto simp: pair_measure_alt M1.positive_integral_0_iff)
    show "{x \<in> space M1. M2.\<mu> (Pair x -` N) \<noteq> 0} \<in> sets M1"
      by (intro M1.borel_measurable_ereal_neq_const measure_cut_measurable_fst N)
    { fix x assume "x \<in> space M1" "M2.\<mu> (Pair x -` N) = 0"
      have "M2.almost_everywhere (\<lambda>y. Q (x, y))"
      proof (rule M2.AE_I)
        show "M2.\<mu> (Pair x -` N) = 0" by fact
        show "Pair x -` N \<in> sets M2" by (intro measurable_cut_fst N)
        show "{y \<in> space M2. \<not> Q (x, y)} \<subseteq> Pair x -` N"
          using N `x \<in> space M1` unfolding space_sigma space_pair_measure by auto
      qed }
    then show "{x \<in> space M1. \<not> M2.almost_everywhere (\<lambda>y. Q (x, y))} \<subseteq> {x \<in> space M1. M2.\<mu> (Pair x -` N) \<noteq> 0}"
      by auto
  qed
qed

lemma (in pair_sigma_algebra) measurable_product_swap:
  "f \<in> measurable (M2 \<Otimes>\<^isub>M M1) M \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) \<in> measurable P M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  show ?thesis
    using pair_sigma_algebra_measurable[of "\<lambda>(x,y). f (y, x)"]
    by (auto intro!: pair_sigma_algebra_measurable Q.pair_sigma_algebra_measurable iffI)
qed

lemma (in pair_sigma_finite) integrable_product_swap:
  assumes "integrable P f"
  shows "integrable (M2 \<Otimes>\<^isub>M M1) (\<lambda>(x,y). f (y,x))"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding *
    using assms unfolding integrable_def
    apply (subst (1 2) positive_integral_product_swap)
    using `integrable P f` unfolding integrable_def
    by (auto simp: *[symmetric] Q.measurable_product_swap[symmetric])
qed

lemma (in pair_sigma_finite) integrable_product_swap_iff:
  "integrable (M2 \<Otimes>\<^isub>M M1) (\<lambda>(x,y). f (y,x)) \<longleftrightarrow> integrable P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  from Q.integrable_product_swap[of "\<lambda>(x,y). f (y,x)"] integrable_product_swap[of f]
  show ?thesis by auto
qed

lemma (in pair_sigma_finite) integral_product_swap:
  assumes "integrable P f"
  shows "(\<integral>(x,y). f (y,x) \<partial>(M2 \<Otimes>\<^isub>M M1)) = integral\<^isup>L P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis
    unfolding lebesgue_integral_def *
    apply (subst (1 2) positive_integral_product_swap)
    using `integrable P f` unfolding integrable_def
    by (auto simp: *[symmetric] Q.measurable_product_swap[symmetric])
qed

lemma (in pair_sigma_finite) integrable_fst_measurable:
  assumes f: "integrable P f"
  shows "M1.almost_everywhere (\<lambda>x. integrable M2 (\<lambda> y. f (x, y)))" (is "?AE")
    and "(\<integral>x. (\<integral>y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>L P f" (is "?INT")
proof -
  let ?pf = "\<lambda>x. ereal (f x)" and ?nf = "\<lambda>x. ereal (- f x)"
  have
    borel: "?nf \<in> borel_measurable P""?pf \<in> borel_measurable P" and
    int: "integral\<^isup>P P ?nf \<noteq> \<infinity>" "integral\<^isup>P P ?pf \<noteq> \<infinity>"
    using assms by auto
  have "(\<integral>\<^isup>+x. (\<integral>\<^isup>+y. ereal (f (x, y)) \<partial>M2) \<partial>M1) \<noteq> \<infinity>"
     "(\<integral>\<^isup>+x. (\<integral>\<^isup>+y. ereal (- f (x, y)) \<partial>M2) \<partial>M1) \<noteq> \<infinity>"
    using borel[THEN positive_integral_fst_measurable(1)] int
    unfolding borel[THEN positive_integral_fst_measurable(2)] by simp_all
  with borel[THEN positive_integral_fst_measurable(1)]
  have AE_pos: "AE x in M1. (\<integral>\<^isup>+y. ereal (f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    "AE x in M1. (\<integral>\<^isup>+y. ereal (- f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    by (auto intro!: M1.positive_integral_PInf_AE )
  then have AE: "AE x in M1. \<bar>\<integral>\<^isup>+y. ereal (f (x, y)) \<partial>M2\<bar> \<noteq> \<infinity>"
    "AE x in M1. \<bar>\<integral>\<^isup>+y. ereal (- f (x, y)) \<partial>M2\<bar> \<noteq> \<infinity>"
    by (auto simp: M2.positive_integral_positive)
  from AE_pos show ?AE using assms
    by (simp add: measurable_pair_image_snd integrable_def)
  { fix f have "(\<integral>\<^isup>+ x. - \<integral>\<^isup>+ y. ereal (f x y) \<partial>M2 \<partial>M1) = (\<integral>\<^isup>+x. 0 \<partial>M1)"
      using M2.positive_integral_positive
      by (intro M1.positive_integral_cong_pos) (auto simp: ereal_uminus_le_reorder)
    then have "(\<integral>\<^isup>+ x. - \<integral>\<^isup>+ y. ereal (f x y) \<partial>M2 \<partial>M1) = 0" by simp }
  note this[simp]
  { fix f assume borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable P"
      and int: "integral\<^isup>P P (\<lambda>x. ereal (f x)) \<noteq> \<infinity>"
      and AE: "M1.almost_everywhere (\<lambda>x. (\<integral>\<^isup>+y. ereal (f (x, y)) \<partial>M2) \<noteq> \<infinity>)"
    have "integrable M1 (\<lambda>x. real (\<integral>\<^isup>+y. ereal (f (x, y)) \<partial>M2))" (is "integrable M1 ?f")
    proof (intro integrable_def[THEN iffD2] conjI)
      show "?f \<in> borel_measurable M1"
        using borel by (auto intro!: M1.borel_measurable_real_of_ereal positive_integral_fst_measurable)
      have "(\<integral>\<^isup>+x. ereal (?f x) \<partial>M1) = (\<integral>\<^isup>+x. (\<integral>\<^isup>+y. ereal (f (x, y))  \<partial>M2) \<partial>M1)"
        using AE M2.positive_integral_positive
        by (auto intro!: M1.positive_integral_cong_AE simp: ereal_real)
      then show "(\<integral>\<^isup>+x. ereal (?f x) \<partial>M1) \<noteq> \<infinity>"
        using positive_integral_fst_measurable[OF borel] int by simp
      have "(\<integral>\<^isup>+x. ereal (- ?f x) \<partial>M1) = (\<integral>\<^isup>+x. 0 \<partial>M1)"
        by (intro M1.positive_integral_cong_pos)
           (simp add: M2.positive_integral_positive real_of_ereal_pos)
      then show "(\<integral>\<^isup>+x. ereal (- ?f x) \<partial>M1) \<noteq> \<infinity>" by simp
    qed }
  with this[OF borel(1) int(1) AE_pos(2)] this[OF borel(2) int(2) AE_pos(1)]
  show ?INT
    unfolding lebesgue_integral_def[of P] lebesgue_integral_def[of M2]
      borel[THEN positive_integral_fst_measurable(2), symmetric]
    using AE[THEN M1.integral_real]
    by simp
qed

lemma (in pair_sigma_finite) integrable_snd_measurable:
  assumes f: "integrable P f"
  shows "M2.almost_everywhere (\<lambda>y. integrable M1 (\<lambda>x. f (x, y)))" (is "?AE")
    and "(\<integral>y. (\<integral>x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^isup>L P f" (is "?INT")
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have Q_int: "integrable Q.P (\<lambda>(x, y). f (y, x))"
    using f unfolding integrable_product_swap_iff .
  show ?INT
    using Q.integrable_fst_measurable(2)[OF Q_int]
    using integral_product_swap[OF f] by simp
  show ?AE
    using Q.integrable_fst_measurable(1)[OF Q_int]
    by simp
qed

lemma (in pair_sigma_finite) Fubini_integral:
  assumes f: "integrable P f"
  shows "(\<integral>y. (\<integral>x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>x. (\<integral>y. f (x, y) \<partial>M2) \<partial>M1)"
  unfolding integrable_snd_measurable[OF assms]
  unfolding integrable_fst_measurable[OF assms] ..

section "Products on finite spaces"

lemma sigma_sets_pair_measure_generator_finite:
  assumes "finite A" and "finite B"
  shows "sigma_sets (A \<times> B) { a \<times> b | a b. a \<in> Pow A \<and> b \<in> Pow B} = Pow (A \<times> B)"
  (is "sigma_sets ?prod ?sets = _")
proof safe
  have fin: "finite (A \<times> B)" using assms by (rule finite_cartesian_product)
  fix x assume subset: "x \<subseteq> A \<times> B"
  hence "finite x" using fin by (rule finite_subset)
  from this subset show "x \<in> sigma_sets ?prod ?sets"
  proof (induct x)
    case empty show ?case by (rule sigma_sets.Empty)
  next
    case (insert a x)
    hence "{a} \<in> sigma_sets ?prod ?sets"
      by (auto simp: pair_measure_generator_def intro!: sigma_sets.Basic)
    moreover have "x \<in> sigma_sets ?prod ?sets" using insert by auto
    ultimately show ?case unfolding insert_is_Un[of a x] by (rule sigma_sets_Un)
  qed
next
  fix x a b
  assume "x \<in> sigma_sets ?prod ?sets" and "(a, b) \<in> x"
  from sigma_sets_into_sp[OF _ this(1)] this(2)
  show "a \<in> A" and "b \<in> B" by auto
qed

locale pair_finite_sigma_algebra = pair_sigma_algebra M1 M2 + M1: finite_sigma_algebra M1 + M2: finite_sigma_algebra M2 for M1 M2

lemma (in pair_finite_sigma_algebra) finite_pair_sigma_algebra:
  shows "P = \<lparr> space = space M1 \<times> space M2, sets = Pow (space M1 \<times> space M2), \<dots> = algebra.more P \<rparr>"
proof -
  show ?thesis
    using sigma_sets_pair_measure_generator_finite[OF M1.finite_space M2.finite_space]
    by (intro algebra.equality) (simp_all add: pair_measure_def pair_measure_generator_def sigma_def)
qed

sublocale pair_finite_sigma_algebra \<subseteq> finite_sigma_algebra P
proof
  show "finite (space P)"
    using M1.finite_space M2.finite_space
    by (subst finite_pair_sigma_algebra) simp
  show "sets P = Pow (space P)"
    by (subst (1 2) finite_pair_sigma_algebra) simp
qed

locale pair_finite_space = pair_sigma_finite M1 M2 + pair_finite_sigma_algebra M1 M2 +
  M1: finite_measure_space M1 + M2: finite_measure_space M2 for M1 M2

lemma (in pair_finite_space) pair_measure_Pair[simp]:
  assumes "a \<in> space M1" "b \<in> space M2"
  shows "\<mu> {(a, b)} = M1.\<mu> {a} * M2.\<mu> {b}"
proof -
  have "\<mu> ({a}\<times>{b}) = M1.\<mu> {a} * M2.\<mu> {b}"
    using M1.sets_eq_Pow M2.sets_eq_Pow assms
    by (subst pair_measure_times) auto
  then show ?thesis by simp
qed

lemma (in pair_finite_space) pair_measure_singleton[simp]:
  assumes "x \<in> space M1 \<times> space M2"
  shows "\<mu> {x} = M1.\<mu> {fst x} * M2.\<mu> {snd x}"
  using pair_measure_Pair assms by (cases x) auto

sublocale pair_finite_space \<subseteq> finite_measure_space P
proof unfold_locales
  show "measure P (space P) \<noteq> \<infinity>"
    by (subst (2) finite_pair_sigma_algebra)
       (simp add: pair_measure_times)
qed

end