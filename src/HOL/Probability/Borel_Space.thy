(*  Title:      HOL/Probability/Borel_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Borel spaces*}

theory Borel_Space
  imports Sigma_Algebra "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

section "Generic Borel spaces"

definition borel :: "'a::topological_space measure" where
  "borel = sigma UNIV {S. open S}"

abbreviation "borel_measurable M \<equiv> measurable M borel"

lemma in_borel_measurable:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sigma_sets UNIV {S. open S}. f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma in_borel_measurable_borel:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sets borel.
      f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma space_borel[simp]: "space borel = UNIV"
  unfolding borel_def by auto

lemma borel_open[simp]:
  assumes "open A" shows "A \<in> sets borel"
proof -
  have "A \<in> {S. open S}" unfolding mem_Collect_eq using assms .
  thus ?thesis unfolding borel_def by auto
qed

lemma borel_closed[simp]:
  assumes "closed A" shows "A \<in> sets borel"
proof -
  have "space borel - (- A) \<in> sets borel"
    using assms unfolding closed_def by (blast intro: borel_open)
  thus ?thesis by simp
qed

lemma borel_comp[intro,simp]: "A \<in> sets borel \<Longrightarrow> - A \<in> sets borel"
  unfolding Compl_eq_Diff_UNIV by (intro Diff) auto

lemma borel_measurable_vimage:
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes borel: "f \<in> borel_measurable M"
  shows "f -` {x} \<inter> space M \<in> sets M"
proof (cases "x \<in> f ` space M")
  case True then obtain y where "x = f y" by auto
  from closed_singleton[of "f y"]
  have "{f y} \<in> sets borel" by (rule borel_closed)
  with assms show ?thesis
    unfolding in_borel_measurable_borel `x = f y` by auto
next
  case False hence "f -` {x} \<inter> space M = {}" by auto
  thus ?thesis by auto
qed

lemma borel_measurableI:
  fixes f :: "'a \<Rightarrow> 'x\<Colon>topological_space"
  assumes "\<And>S. open S \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable M"
  unfolding borel_def
proof (rule measurable_measure_of, simp_all)
  fix S :: "'x set" assume "open S" thus "f -` S \<inter> space M \<in> sets M"
    using assms[of S] by simp
qed

lemma borel_singleton[simp, intro]:
  fixes x :: "'a::t1_space"
  shows "A \<in> sets borel \<Longrightarrow> insert x A \<in> sets borel"
  proof (rule insert_in_sets)
    show "{x} \<in> sets borel"
      using closed_singleton[of x] by (rule borel_closed)
  qed simp

lemma borel_measurable_const[simp, intro]:
  "(\<lambda>x. c) \<in> borel_measurable M"
  by auto

lemma borel_measurable_indicator[simp, intro!]:
  assumes A: "A \<in> sets M"
  shows "indicator A \<in> borel_measurable M"
  unfolding indicator_def [abs_def] using A
  by (auto intro!: measurable_If_set)

lemma borel_measurable_indicator_iff:
  "(indicator A :: 'a \<Rightarrow> 'x::{t1_space, zero_neq_one}) \<in> borel_measurable M \<longleftrightarrow> A \<inter> space M \<in> sets M"
    (is "?I \<in> borel_measurable M \<longleftrightarrow> _")
proof
  assume "?I \<in> borel_measurable M"
  then have "?I -` {1} \<inter> space M \<in> sets M"
    unfolding measurable_def by auto
  also have "?I -` {1} \<inter> space M = A \<inter> space M"
    unfolding indicator_def [abs_def] by auto
  finally show "A \<inter> space M \<in> sets M" .
next
  assume "A \<inter> space M \<in> sets M"
  moreover have "?I \<in> borel_measurable M \<longleftrightarrow>
    (indicator (A \<inter> space M) :: 'a \<Rightarrow> 'x) \<in> borel_measurable M"
    by (intro measurable_cong) (auto simp: indicator_def)
  ultimately show "?I \<in> borel_measurable M" by auto
qed

lemma borel_measurable_subalgebra:
  assumes "sets N \<subseteq> sets M" "space N = space M" "f \<in> borel_measurable N"
  shows "f \<in> borel_measurable M"
  using assms unfolding measurable_def by auto

section "Borel spaces on euclidean spaces"

lemma lessThan_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{..< a} \<in> sets borel"
  by (blast intro: borel_open)

lemma greaterThan_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{a <..} \<in> sets borel"
  by (blast intro: borel_open)

lemma greaterThanLessThan_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a<..<b} \<in> sets borel"
  by (blast intro: borel_open)

lemma atMost_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{..a} \<in> sets borel"
  by (blast intro: borel_closed)

lemma atLeast_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{a..} \<in> sets borel"
  by (blast intro: borel_closed)

lemma atLeastAtMost_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a..b} \<in> sets borel"
  by (blast intro: borel_closed)

lemma greaterThanAtMost_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a<..b} \<in> sets borel"
  unfolding greaterThanAtMost_def by blast

lemma atLeastLessThan_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a..<b} \<in> sets borel"
  unfolding atLeastLessThan_def by blast

lemma hafspace_less_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. a < x $$ i} \<in> sets borel"
  by (auto intro!: borel_open open_halfspace_component_gt)

lemma hafspace_greater_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. x $$ i < a} \<in> sets borel"
  by (auto intro!: borel_open open_halfspace_component_lt)

lemma hafspace_less_eq_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. a \<le> x $$ i} \<in> sets borel"
  by (auto intro!: borel_closed closed_halfspace_component_ge)

lemma hafspace_greater_eq_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. x $$ i \<le> a} \<in> sets borel"
  by (auto intro!: borel_closed closed_halfspace_component_le)

lemma borel_measurable_less[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w < g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w < g w} =
        (\<Union>r. (f -` {..< of_rat r} \<inter> space M) \<inter> (g -` {of_rat r <..} \<inter> space M))"
    using Rats_dense_in_real by (auto simp add: Rats_def)
  then show ?thesis using f g
    by simp (blast intro: measurable_sets)
qed

lemma borel_measurable_le[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w \<le> g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w \<le> g w} = space M - {w \<in> space M. g w < f w}"
    by auto
  thus ?thesis using f g
    by simp blast
qed

lemma borel_measurable_eq[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w = g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w = g w} =
        {w \<in> space M. f w \<le> g w} \<inter> {w \<in> space M. g w \<le> f w}"
    by auto
  thus ?thesis using f g by auto
qed

lemma borel_measurable_neq[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w \<noteq> g w} = space M - {w \<in> space M. f w = g w}"
    by auto
  thus ?thesis using f g by auto
qed

subsection "Borel space equals sigma algebras over intervals"

lemma rational_boxes:
  fixes x :: "'a\<Colon>ordered_euclidean_space"
  assumes "0 < e"
  shows "\<exists>a b. (\<forall>i. a $$ i \<in> \<rat>) \<and> (\<forall>i. b $$ i \<in> \<rat>) \<and> x \<in> {a <..< b} \<and> {a <..< b} \<subseteq> ball x e"
proof -
  def e' \<equiv> "e / (2 * sqrt (real (DIM ('a))))"
  then have e: "0 < e'" using assms by (auto intro!: divide_pos_pos)
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x $$ i \<and> x $$ i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i from Rats_dense_in_real[of "x $$ i - e'" "x $$ i"] e
    show "?th i" by auto
  qed
  from choice[OF this] guess a .. note a = this
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x $$ i < y \<and> y - x $$ i < e'" (is "\<forall>i. ?th i")
  proof
    fix i from Rats_dense_in_real[of "x $$ i" "x $$ i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] guess b .. note b = this
  { fix y :: 'a assume *: "Chi a < y" "y < Chi b"
    have "dist x y = sqrt (\<Sum>i<DIM('a). (dist (x $$ i) (y $$ i))\<twosuperior>)"
      unfolding setL2_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>i<DIM('a). e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule setsum_strict_mono)
      fix i assume i: "i \<in> {..<DIM('a)}"
      have "a i < y$$i \<and> y$$i < b i" using * i eucl_less[where 'a='a] by auto
      moreover have "a i < x$$i" "x$$i - a i < e'" using a by auto
      moreover have "x$$i < b i" "b i - x$$i < e'" using b by auto
      ultimately have "\<bar>x$$i - y$$i\<bar> < 2 * e'" by auto
      then have "dist (x $$ i) (y $$ i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x $$ i) (y $$ i))\<twosuperior> < (e/sqrt (real (DIM('a))))\<twosuperior>"
        by (rule power_strict_mono) auto
      then show "(dist (x $$ i) (y $$ i))\<twosuperior> < e\<twosuperior> / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e" using `0 < e` by (simp add: real_eq_of_nat DIM_positive)
    finally have "dist x y < e" . }
  with a b show ?thesis
    apply (rule_tac exI[of _ "Chi a"])
    apply (rule_tac exI[of _ "Chi b"])
    using eucl_less[where 'a='a] by auto
qed

lemma ex_rat_list:
  fixes x :: "'a\<Colon>ordered_euclidean_space"
  assumes "\<And> i. x $$ i \<in> \<rat>"
  shows "\<exists> r. length r = DIM('a) \<and> (\<forall> i < DIM('a). of_rat (r ! i) = x $$ i)"
proof -
  have "\<forall>i. \<exists>r. x $$ i = of_rat r" using assms unfolding Rats_def by blast
  from choice[OF this] guess r ..
  then show ?thesis by (auto intro!: exI[of _ "map r [0 ..< DIM('a)]"])
qed

lemma open_UNION:
  fixes M :: "'a\<Colon>ordered_euclidean_space set"
  assumes "open M"
  shows "M = UNION {(a, b) | a b. {Chi (of_rat \<circ> op ! a) <..< Chi (of_rat \<circ> op ! b)} \<subseteq> M}
                   (\<lambda> (a, b). {Chi (of_rat \<circ> op ! a) <..< Chi (of_rat \<circ> op ! b)})"
    (is "M = UNION ?idx ?box")
proof safe
  fix x assume "x \<in> M"
  obtain e where e: "e > 0" "ball x e \<subseteq> M"
    using openE[OF assms `x \<in> M`] by auto
  then obtain a b where ab: "x \<in> {a <..< b}" "\<And>i. a $$ i \<in> \<rat>" "\<And>i. b $$ i \<in> \<rat>" "{a <..< b} \<subseteq> ball x e"
    using rational_boxes[OF e(1)] by blast
  then obtain p q where pq: "length p = DIM ('a)"
                            "length q = DIM ('a)"
                            "\<forall> i < DIM ('a). of_rat (p ! i) = a $$ i \<and> of_rat (q ! i) = b $$ i"
    using ex_rat_list[OF ab(2)] ex_rat_list[OF ab(3)] by blast
  hence p: "Chi (of_rat \<circ> op ! p) = a"
    using euclidean_eq[of "Chi (of_rat \<circ> op ! p)" a]
    unfolding o_def by auto
  from pq have q: "Chi (of_rat \<circ> op ! q) = b"
    using euclidean_eq[of "Chi (of_rat \<circ> op ! q)" b]
    unfolding o_def by auto
  have "x \<in> ?box (p, q)"
    using p q ab by auto
  thus "x \<in> UNION ?idx ?box" using ab e p q exI[of _ p] exI[of _ q] by auto
qed auto

lemma borel_sigma_sets_subset:
  "A \<subseteq> sets borel \<Longrightarrow> sigma_sets UNIV A \<subseteq> sets borel"
  using sigma_sets_subset[of A borel] by simp

lemma borel_eq_sigmaI1:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV (range F))"
  assumes F: "\<And>i. F i \<in> sets borel"
  shows "borel = sigma UNIV (range F)"
  unfolding borel_def
proof (intro sigma_eqI antisym)
  have borel_rev_eq: "sigma_sets UNIV {S::'a set. open S} = sets borel"
    unfolding borel_def by simp
  also have "\<dots> = sigma_sets UNIV X"
    unfolding borel_eq by simp
  also have "\<dots> \<subseteq> sigma_sets UNIV (range F)"
    using X by (intro sigma_algebra.sigma_sets_subset[OF sigma_algebra_sigma_sets]) auto
  finally show "sigma_sets UNIV {S. open S} \<subseteq> sigma_sets UNIV (range F)" .
  show "sigma_sets UNIV (range F) \<subseteq> sigma_sets UNIV {S. open S}"
    unfolding borel_rev_eq using F by (intro borel_sigma_sets_subset) auto
qed auto

lemma borel_eq_sigmaI2:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range (\<lambda>(i, j). G i j))"
  assumes X: "\<And>i j. G i j \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X="range (\<lambda>(i, j). G i j)" and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI3:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X=X and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI4:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range (\<lambda>(i, j). G i j))"
  assumes X: "\<And>i j. G i j \<in> sets (sigma UNIV (range F))"
  assumes F: "\<And>i. F i \<in> sets borel"
  shows "borel = sigma UNIV (range F)"
  using assms by (intro borel_eq_sigmaI1[where X="range (\<lambda>(i, j). G i j)" and F=F]) auto

lemma borel_eq_sigmaI5:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and G :: "'l \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range G)"
  assumes X: "\<And>i. G i \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X="range G" and F="(\<lambda>(i, j). F i j)"]) auto

lemma halfspace_gt_in_halfspace:
  "{x\<Colon>'a. a < x $$ i} \<in> sigma_sets UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a}))"
  (is "?set \<in> ?SIGMA")
proof -
  interpret sigma_algebra UNIV ?SIGMA
    by (intro sigma_algebra_sigma_sets) simp_all
  have *: "?set = (\<Union>n. UNIV - {x\<Colon>'a. x $$ i < a + 1 / real (Suc n)})"
  proof (safe, simp_all add: not_less)
    fix x assume "a < x $$ i"
    with reals_Archimedean[of "x $$ i - a"]
    obtain n where "a + 1 / real (Suc n) < x $$ i"
      by (auto simp: inverse_eq_divide field_simps)
    then show "\<exists>n. a + 1 / real (Suc n) \<le> x $$ i"
      by (blast intro: less_imp_le)
  next
    fix x n
    have "a < a + 1 / real (Suc n)" by auto
    also assume "\<dots> \<le> x"
    finally show "a < x" .
  qed
  show "?set \<in> ?SIGMA" unfolding *
    by (auto intro!: Diff)
qed

lemma borel_eq_halfspace_less:
  "borel = sigma UNIV (range (\<lambda>(a, i). {x::'a::ordered_euclidean_space. x $$ i < a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI3[OF borel_def])
  fix S :: "'a set" assume "S \<in> {S. open S}"
  then have "open S" by simp
  from open_UNION[OF this]
  obtain I where *: "S =
    (\<Union>(a, b)\<in>I.
        (\<Inter> i<DIM('a). {x. (Chi (real_of_rat \<circ> op ! a)::'a) $$ i < x $$ i}) \<inter>
        (\<Inter> i<DIM('a). {x. x $$ i < (Chi (real_of_rat \<circ> op ! b)::'a) $$ i}))"
    unfolding greaterThanLessThan_def
    unfolding eucl_greaterThan_eq_halfspaces[where 'a='a]
    unfolding eucl_lessThan_eq_halfspaces[where 'a='a]
    by blast
  show "S \<in> ?SIGMA"
    unfolding *
    by (safe intro!: countable_UN Int countable_INT) (auto intro!: halfspace_gt_in_halfspace)
qed auto

lemma borel_eq_halfspace_le:
  "borel = sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. x $$ i \<le> a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a i
  have *: "{x::'a. x$$i < a} = (\<Union>n. {x. x$$i \<le> a - 1/real (Suc n)})"
  proof (safe, simp_all)
    fix x::'a assume *: "x$$i < a"
    with reals_Archimedean[of "a - x$$i"]
    obtain n where "x $$ i < a - 1 / (real (Suc n))"
      by (auto simp: field_simps inverse_eq_divide)
    then show "\<exists>n. x $$ i \<le> a - 1 / (real (Suc n))"
      by (blast intro: less_imp_le)
  next
    fix x::'a and n
    assume "x$$i \<le> a - 1 / real (Suc n)"
    also have "\<dots> < a" by auto
    finally show "x$$i < a" .
  qed
  show "{x. x$$i < a} \<in> ?SIGMA" unfolding *
    by (safe intro!: countable_UN) auto
qed auto

lemma borel_eq_halfspace_ge:
  "borel = sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. a \<le> x $$ i}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a i have *: "{x::'a. x$$i < a} = space ?SIGMA - {x::'a. a \<le> x$$i}" by auto
  show "{x. x$$i < a} \<in> ?SIGMA" unfolding *
      by (safe intro!: compl_sets) auto
qed auto

lemma borel_eq_halfspace_greater:
  "borel = sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. a < x $$ i}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_le])
  fix a i have *: "{x::'a. x$$i \<le> a} = space ?SIGMA - {x::'a. a < x$$i}" by auto
  show "{x. x$$i \<le> a} \<in> ?SIGMA" unfolding *
    by (safe intro!: compl_sets) auto
qed auto

lemma borel_eq_atMost:
  "borel = sigma UNIV (range (\<lambda>a. {..a\<Colon>'a\<Colon>ordered_euclidean_space}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a i show "{x. x$$i \<le> a} \<in> ?SIGMA"
  proof cases
    assume "i < DIM('a)"
    then have *: "{x::'a. x$$i \<le> a} = (\<Union>k::nat. {.. (\<chi>\<chi> n. if n = i then a else real k)})"
    proof (safe, simp_all add: eucl_le[where 'a='a] split: split_if_asm)
      fix x
      from real_arch_simple[of "Max ((\<lambda>i. x$$i)`{..<DIM('a)})"] guess k::nat ..
      then have "\<And>i. i < DIM('a) \<Longrightarrow> x$$i \<le> real k"
        by (subst (asm) Max_le_iff) auto
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> x $$ ia \<le> real k"
        by (auto intro!: exI[of _ k])
    qed
    show "{x. x$$i \<le> a} \<in> ?SIGMA" unfolding *
      by (safe intro!: countable_UN) auto
  qed (auto intro: sigma_sets_top sigma_sets.Empty)
qed auto

lemma borel_eq_greaterThan:
  "borel = sigma UNIV (range (\<lambda>a\<Colon>'a\<Colon>ordered_euclidean_space. {a<..}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a i show "{x. x$$i \<le> a} \<in> ?SIGMA"
  proof cases
    assume "i < DIM('a)"
    have "{x::'a. x$$i \<le> a} = UNIV - {x::'a. a < x$$i}" by auto
    also have *: "{x::'a. a < x$$i} = (\<Union>k::nat. {(\<chi>\<chi> n. if n = i then a else -real k) <..})" using `i <DIM('a)`
    proof (safe, simp_all add: eucl_less[where 'a='a] split: split_if_asm)
      fix x
      from reals_Archimedean2[of "Max ((\<lambda>i. -x$$i)`{..<DIM('a)})"]
      guess k::nat .. note k = this
      { fix i assume "i < DIM('a)"
        then have "-x$$i < real k"
          using k by (subst (asm) Max_less_iff) auto
        then have "- real k < x$$i" by simp }
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> -real k < x $$ ia"
        by (auto intro!: exI[of _ k])
    qed
    finally show "{x. x$$i \<le> a} \<in> ?SIGMA"
      apply (simp only:)
      apply (safe intro!: countable_UN Diff)
      apply (auto intro: sigma_sets_top)
      done
  qed (auto intro: sigma_sets_top sigma_sets.Empty)
qed auto

lemma borel_eq_lessThan:
  "borel = sigma UNIV (range (\<lambda>a\<Colon>'a\<Colon>ordered_euclidean_space. {..<a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_ge])
  fix a i show "{x. a \<le> x$$i} \<in> ?SIGMA"
  proof cases
    fix a i assume "i < DIM('a)"
    have "{x::'a. a \<le> x$$i} = UNIV - {x::'a. x$$i < a}" by auto
    also have *: "{x::'a. x$$i < a} = (\<Union>k::nat. {..< (\<chi>\<chi> n. if n = i then a else real k)})" using `i <DIM('a)`
    proof (safe, simp_all add: eucl_less[where 'a='a] split: split_if_asm)
      fix x
      from reals_Archimedean2[of "Max ((\<lambda>i. x$$i)`{..<DIM('a)})"]
      guess k::nat .. note k = this
      { fix i assume "i < DIM('a)"
        then have "x$$i < real k"
          using k by (subst (asm) Max_less_iff) auto
        then have "x$$i < real k" by simp }
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> x $$ ia < real k"
        by (auto intro!: exI[of _ k])
    qed
    finally show "{x. a \<le> x$$i} \<in> ?SIGMA"
      apply (simp only:)
      apply (safe intro!: countable_UN Diff)
      apply (auto intro: sigma_sets_top)
      done
  qed (auto intro: sigma_sets_top sigma_sets.Empty)
qed auto

lemma borel_eq_atLeastAtMost:
  "borel = sigma UNIV (range (\<lambda>(a,b). {a..b} \<Colon>'a\<Colon>ordered_euclidean_space set))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix a::'a
  have *: "{..a} = (\<Union>n::nat. {- real n *\<^sub>R One .. a})"
  proof (safe, simp_all add: eucl_le[where 'a='a])
    fix x
    from real_arch_simple[of "Max ((\<lambda>i. - x$$i)`{..<DIM('a)})"]
    guess k::nat .. note k = this
    { fix i assume "i < DIM('a)"
      with k have "- x$$i \<le> real k"
        by (subst (asm) Max_le_iff) (auto simp: field_simps)
      then have "- real k \<le> x$$i" by simp }
    then show "\<exists>n::nat. \<forall>i<DIM('a). - real n \<le> x $$ i"
      by (auto intro!: exI[of _ k])
  qed
  show "{..a} \<in> ?SIGMA" unfolding *
    by (safe intro!: countable_UN)
       (auto intro!: sigma_sets_top)
qed auto

lemma borel_eq_greaterThanLessThan:
  "borel = sigma UNIV (range (\<lambda> (a, b). {a <..< b} :: 'a \<Colon> ordered_euclidean_space set))"
    (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI1[OF borel_def])
  fix M :: "'a set" assume "M \<in> {S. open S}"
  then have "open M" by simp
  show "M \<in> ?SIGMA"
    apply (subst open_UNION[OF `open M`])
    apply (safe intro!: countable_UN)
    apply auto
    done
qed auto

lemma borel_eq_atLeastLessThan:
  "borel = sigma UNIV (range (\<lambda>(a, b). {a ..< b :: real}))" (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_lessThan])
  have move_uminus: "\<And>x y::real. -x \<le> y \<longleftrightarrow> -y \<le> x" by auto
  fix x :: real
  have "{..<x} = (\<Union>i::nat. {-real i ..< x})"
    by (auto simp: move_uminus real_arch_simple)
  then show "{..< x} \<in> ?SIGMA"
    by (auto intro: sigma_sets.intros)
qed auto

lemma borel_measurable_halfspacesI:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  assumes F: "borel = sigma UNIV (range F)"
  and S_eq: "\<And>a i. S a i = f -` F (a,i) \<inter> space M" 
  and S: "\<And>a i. \<not> i < DIM('c) \<Longrightarrow> S a i \<in> sets M"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a::real. S a i \<in> sets M)"
proof safe
  fix a :: real and i assume i: "i < DIM('c)" and f: "f \<in> borel_measurable M"
  then show "S a i \<in> sets M" unfolding assms
    by (auto intro!: measurable_sets sigma_sets.Basic simp: assms(1))
next
  assume a: "\<forall>i<DIM('c). \<forall>a. S a i \<in> sets M"
  { fix a i have "S a i \<in> sets M"
    proof cases
      assume "i < DIM('c)"
      with a show ?thesis unfolding assms(2) by simp
    next
      assume "\<not> i < DIM('c)"
      from S[OF this] show ?thesis .
    qed }
  then show "f \<in> borel_measurable M"
    by (auto intro!: measurable_measure_of simp: S_eq F)
qed

lemma borel_measurable_iff_halfspace_le:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. f w $$ i \<le> a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_le]) auto

lemma borel_measurable_iff_halfspace_less:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. f w $$ i < a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_less]) auto

lemma borel_measurable_iff_halfspace_ge:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. a \<le> f w $$ i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_ge]) auto

lemma borel_measurable_iff_halfspace_greater:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. a < f w $$ i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_greater]) auto

lemma borel_measurable_iff_le:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M)"
  using borel_measurable_iff_halfspace_le[where 'c=real] by simp

lemma borel_measurable_iff_less:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w < a} \<in> sets M)"
  using borel_measurable_iff_halfspace_less[where 'c=real] by simp

lemma borel_measurable_iff_ge:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a \<le> f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_ge[where 'c=real] by simp

lemma borel_measurable_iff_greater:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a < f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_greater[where 'c=real] by simp

lemma borel_measurable_euclidean_component':
  "(\<lambda>x::'a::euclidean_space. x $$ i) \<in> borel_measurable borel"
proof (rule borel_measurableI)
  fix S::"real set" assume "open S"
  from open_vimage_euclidean_component[OF this]
  show "(\<lambda>x. x $$ i) -` S \<inter> space borel \<in> sets borel"
    by (auto intro: borel_open)
qed

lemma borel_measurable_euclidean_component:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. f x $$ i) \<in> borel_measurable M"
  using measurable_comp[OF f borel_measurable_euclidean_component'] by (simp add: comp_def)

lemma borel_measurable_euclidean_space:
  fixes f :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). (\<lambda>x. f x $$ i) \<in> borel_measurable M)"
proof safe
  fix i assume "f \<in> borel_measurable M"
  then show "(\<lambda>x. f x $$ i) \<in> borel_measurable M"
    by (auto intro: borel_measurable_euclidean_component)
next
  assume f: "\<forall>i<DIM('c). (\<lambda>x. f x $$ i) \<in> borel_measurable M"
  then show "f \<in> borel_measurable M"
    unfolding borel_measurable_iff_halfspace_le by auto
qed

subsection "Borel measurable operators"

lemma borel_measurable_continuous_on1:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "continuous_on UNIV f"
  shows "f \<in> borel_measurable borel"
  apply(rule borel_measurableI)
  using continuous_open_preimage[OF assms] unfolding vimage_def by auto

lemma borel_measurable_continuous_on:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "continuous_on UNIV f" and g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f (g x)) \<in> borel_measurable M"
  using measurable_comp[OF g borel_measurable_continuous_on1[OF f]] by (simp add: comp_def)

lemma borel_measurable_continuous_on_open':
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t1_space"
  assumes cont: "continuous_on A f" "open A"
  shows "(\<lambda>x. if x \<in> A then f x else c) \<in> borel_measurable borel" (is "?f \<in> _")
proof (rule borel_measurableI)
  fix S :: "'b set" assume "open S"
  then have "open {x\<in>A. f x \<in> S}"
    by (intro continuous_open_preimage[OF cont]) auto
  then have *: "{x\<in>A. f x \<in> S} \<in> sets borel" by auto
  have "?f -` S \<inter> space borel = 
    {x\<in>A. f x \<in> S} \<union> (if c \<in> S then space borel - A else {})"
    by (auto split: split_if_asm)
  also have "\<dots> \<in> sets borel"
    using * `open A` by (auto simp del: space_borel intro!: Un)
  finally show "?f -` S \<inter> space borel \<in> sets borel" .
qed

lemma borel_measurable_continuous_on_open:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t1_space"
  assumes cont: "continuous_on A f" "open A"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. if g x \<in> A then f (g x) else c) \<in> borel_measurable M"
  using measurable_comp[OF g borel_measurable_continuous_on_open'[OF cont], of c]
  by (simp add: comp_def)

lemma borel_measurable_uminus[simp, intro]:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. - g x) \<in> borel_measurable M"
  by (rule borel_measurable_continuous_on[OF _ g]) (auto intro: continuous_on_minus continuous_on_id)

lemma euclidean_component_prod:
  fixes x :: "'a :: euclidean_space \<times> 'b :: euclidean_space"
  shows "x $$ i = (if i < DIM('a) then fst x $$ i else snd x $$ (i - DIM('a)))"
  unfolding euclidean_component_def basis_prod_def inner_prod_def by auto

lemma borel_measurable_Pair[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b::ordered_euclidean_space" and g :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. (f x, g x)) \<in> borel_measurable M"
proof (intro borel_measurable_iff_halfspace_le[THEN iffD2] allI impI)
  fix i and a :: real assume i: "i < DIM('b \<times> 'c)"
  have [simp]: "\<And>P A B C. {w. (P \<longrightarrow> A w \<and> B w) \<and> (\<not> P \<longrightarrow> A w \<and> C w)} = 
    {w. A w \<and> (P \<longrightarrow> B w) \<and> (\<not> P \<longrightarrow> C w)}" by auto
  from i f g show "{w \<in> space M. (f w, g w) $$ i \<le> a} \<in> sets M"
    by (auto simp: euclidean_component_prod intro!: sets_Collect borel_measurable_euclidean_component)
qed

lemma continuous_on_fst: "continuous_on UNIV fst"
proof -
  have [simp]: "range fst = UNIV" by (auto simp: image_iff)
  show ?thesis
    using closed_vimage_fst
    by (auto simp: continuous_on_closed closed_closedin vimage_def)
qed

lemma continuous_on_snd: "continuous_on UNIV snd"
proof -
  have [simp]: "range snd = UNIV" by (auto simp: image_iff)
  show ?thesis
    using closed_vimage_snd
    by (auto simp: continuous_on_closed closed_closedin vimage_def)
qed

lemma borel_measurable_continuous_Pair:
  fixes f :: "'a \<Rightarrow> 'b::ordered_euclidean_space" and g :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  assumes [simp]: "f \<in> borel_measurable M"
  assumes [simp]: "g \<in> borel_measurable M"
  assumes H: "continuous_on UNIV (\<lambda>x. H (fst x) (snd x))"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  have eq: "(\<lambda>x. H (f x) (g x)) = (\<lambda>x. (\<lambda>x. H (fst x) (snd x)) (f x, g x))" by auto
  show ?thesis
    unfolding eq by (rule borel_measurable_continuous_on[OF H]) auto
qed

lemma borel_measurable_add[simp, intro]:
  fixes f g :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
  using f g
  by (rule borel_measurable_continuous_Pair)
     (auto intro: continuous_on_fst continuous_on_snd continuous_on_add)

lemma borel_measurable_setsum[simp, intro]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_diff[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
  unfolding diff_minus using assms by fast

lemma borel_measurable_times[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
  using f g
  by (rule borel_measurable_continuous_Pair)
     (auto intro: continuous_on_fst continuous_on_snd continuous_on_mult)

lemma continuous_on_dist:
  fixes f :: "'a :: t2_space \<Rightarrow> 'b :: metric_space"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_on_eq_continuous_within by (auto simp: continuous_dist)

lemma borel_measurable_dist[simp, intro]:
  fixes g f :: "'a \<Rightarrow> 'b::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. dist (f x) (g x)) \<in> borel_measurable M"
  using f g
  by (rule borel_measurable_continuous_Pair)
     (intro continuous_on_dist continuous_on_fst continuous_on_snd)
  
lemma affine_borel_measurable_vector:
  fixes f :: "'a \<Rightarrow> 'x::real_normed_vector"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. a + b *\<^sub>R f x) \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S :: "'x set" assume "open S"
  show "(\<lambda>x. a + b *\<^sub>R f x) -` S \<inter> space M \<in> sets M"
  proof cases
    assume "b \<noteq> 0"
    with `open S` have "open ((\<lambda>x. (- a + x) /\<^sub>R b) ` S)" (is "open ?S")
      by (auto intro!: open_affinity simp: scaleR_add_right)
    hence "?S \<in> sets borel" by auto
    moreover
    from `b \<noteq> 0` have "(\<lambda>x. a + b *\<^sub>R f x) -` S = f -` ?S"
      apply auto by (rule_tac x="a + b *\<^sub>R f x" in image_eqI, simp_all)
    ultimately show ?thesis using assms unfolding in_borel_measurable_borel
      by auto
  qed simp
qed

lemma affine_borel_measurable:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. a + (g x) * b) \<in> borel_measurable M"
  using affine_borel_measurable_vector[OF assms] by (simp add: mult_commute)

lemma borel_measurable_setprod[simp, intro]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_inverse[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. inverse (f x)) \<in> borel_measurable M"
proof -
  have *: "\<And>x::real. inverse x = (if x \<in> UNIV - {0} then inverse x else 0)" by auto
  show ?thesis
    apply (subst *)
    apply (rule borel_measurable_continuous_on_open)
    apply (auto intro!: f continuous_on_inverse continuous_on_id)
    done
qed

lemma borel_measurable_divide[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  and "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x / g x) \<in> borel_measurable M"
  unfolding field_divide_inverse
  by (rule borel_measurable_inverse borel_measurable_times assms)+

lemma borel_measurable_max[intro, simp]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  unfolding max_def by (auto intro!: assms measurable_If)

lemma borel_measurable_min[intro, simp]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
  unfolding min_def by (auto intro!: assms measurable_If)

lemma borel_measurable_abs[simp, intro]:
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. \<bar>f x :: real\<bar>) \<in> borel_measurable M"
proof -
  have *: "\<And>x. \<bar>f x\<bar> = max 0 (f x) + max 0 (- f x)" by (simp add: max_def)
  show ?thesis unfolding * using assms by auto
qed

lemma borel_measurable_nth[simp, intro]:
  "(\<lambda>x::real^'n. x $ i) \<in> borel_measurable borel"
  using borel_measurable_euclidean_component'
  unfolding nth_conv_component by auto

lemma convex_measurable:
  fixes a b :: real
  assumes X: "X \<in> borel_measurable M" "X ` space M \<subseteq> { a <..< b}"
  assumes q: "convex_on { a <..< b} q"
  shows "(\<lambda>x. q (X x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. if X x \<in> {a <..< b} then q (X x) else 0) \<in> borel_measurable M" (is "?qX")
  proof (rule borel_measurable_continuous_on_open[OF _ _ X(1)])
    show "open {a<..<b}" by auto
    from this q show "continuous_on {a<..<b} q"
      by (rule convex_on_continuous)
  qed
  moreover have "?qX \<longleftrightarrow> (\<lambda>x. q (X x)) \<in> borel_measurable M"
    using X by (intro measurable_cong) auto
  ultimately show ?thesis by simp
qed

lemma borel_measurable_ln[simp,intro]:
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. ln (f x)) \<in> borel_measurable M"
proof -
  { fix x :: real assume x: "x \<le> 0"
    { fix x::real assume "x \<le> 0" then have "\<And>u. exp u = x \<longleftrightarrow> False" by auto }
    from this[of x] x this[of 0] have "ln 0 = ln x"
      by (auto simp: ln_def) }
  note ln_imp = this
  have "(\<lambda>x. if f x \<in> {0<..} then ln (f x) else ln 0) \<in> borel_measurable M"
  proof (rule borel_measurable_continuous_on_open[OF _ _ f])
    show "continuous_on {0<..} ln"
      by (auto intro!: continuous_at_imp_continuous_on DERIV_ln DERIV_isCont
               simp: continuous_isCont[symmetric])
    show "open ({0<..}::real set)" by auto
  qed
  also have "(\<lambda>x. if x \<in> {0<..} then ln x else ln 0) = ln"
    by (simp add: fun_eq_iff not_less ln_imp)
  finally show ?thesis .
qed

lemma borel_measurable_log[simp,intro]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. log b (f x)) \<in> borel_measurable M"
  unfolding log_def by auto

lemma borel_measurable_real_floor:
  "(\<lambda>x::real. real \<lfloor>x\<rfloor>) \<in> borel_measurable borel"
  unfolding borel_measurable_iff_ge
proof (intro allI)
  fix a :: real
  { fix x have "a \<le> real \<lfloor>x\<rfloor> \<longleftrightarrow> real \<lceil>a\<rceil> \<le> x"
      using le_floor_eq[of "\<lceil>a\<rceil>" x] ceiling_le_iff[of a "\<lfloor>x\<rfloor>"]
      unfolding real_eq_of_int by simp }
  then have "{w::real \<in> space borel. a \<le> real \<lfloor>w\<rfloor>} = {real \<lceil>a\<rceil>..}" by auto
  then show "{w::real \<in> space borel. a \<le> real \<lfloor>w\<rfloor>} \<in> sets borel" by auto
qed

lemma borel_measurable_real_natfloor[intro, simp]:
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. real (natfloor (f x))) \<in> borel_measurable M"
proof -
  have "\<And>x. real (natfloor (f x)) = max 0 (real \<lfloor>f x\<rfloor>)"
    by (auto simp: max_def natfloor_def)
  with borel_measurable_max[OF measurable_comp[OF assms borel_measurable_real_floor] borel_measurable_const]
  show ?thesis by (simp add: comp_def)
qed

subsection "Borel space on the extended reals"

lemma borel_measurable_ereal[simp, intro]:
  assumes f: "f \<in> borel_measurable M" shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  using continuous_on_ereal f by (rule borel_measurable_continuous_on)

lemma borel_measurable_real_of_ereal[simp, intro]:
  fixes f :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. real (f x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. if f x \<in> UNIV - { \<infinity>, - \<infinity> } then real (f x) else 0) \<in> borel_measurable M"
    using continuous_on_real
    by (rule borel_measurable_continuous_on_open[OF _ _ f]) auto
  also have "(\<lambda>x. if f x \<in> UNIV - { \<infinity>, - \<infinity> } then real (f x) else 0) = (\<lambda>x. real (f x))"
    by auto
  finally show ?thesis .
qed

lemma borel_measurable_ereal_cases:
  fixes f :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real (f x)))) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>x. if x \<in> f -` {\<infinity>} then H \<infinity> else if x \<in> f -` {-\<infinity>} then H (-\<infinity>) else H (ereal (real (f x)))"
  { fix x have "H (f x) = ?F x" by (cases "f x") auto }
  moreover 
  have "?F \<in> borel_measurable M"
    by (intro measurable_If_set f measurable_sets[OF f] H) auto
  ultimately
  show ?thesis by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f[simp]: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_abs[intro, simp]: "(\<lambda>x. \<bar>f x\<bar>) \<in> borel_measurable M"
    and borel_measurable_ereal_inverse[simp, intro]: "(\<lambda>x. inverse (f x) :: ereal) \<in> borel_measurable M"
    and borel_measurable_uminus_ereal[intro]: "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M"
  by (auto simp del: abs_real_of_ereal simp: borel_measurable_ereal_cases[OF f] measurable_If)

lemma borel_measurable_uminus_eq_ereal[simp]:
  "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M" (is "?l = ?r")
proof
  assume ?l from borel_measurable_uminus_ereal[OF this] show ?r by simp
qed auto

lemma sets_Collect_If_set:
  assumes "A \<inter> space M \<in> sets M" "{x \<in> space M. P x} \<in> sets M" "{x \<in> space M. Q x} \<in> sets M"
  shows "{x \<in> space M. if x \<in> A then P x else Q x} \<in> sets M"
proof -
  have *: "{x \<in> space M. if x \<in> A then P x else Q x} = 
    {x \<in> space M. if x \<in> A \<inter> space M then P x else Q x}" by auto
  show ?thesis unfolding * unfolding if_bool_eq_conj using assms
    by (auto intro!: sets_Collect simp: Int_def conj_commute)
qed

lemma set_Collect_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "{x \<in> space M. H (ereal (real (f x))) (ereal (real (g x)))} \<in> sets M"
    "{x \<in> space M. H (-\<infinity>) (ereal (real (g x)))} \<in> sets M"
    "{x \<in> space M. H (\<infinity>) (ereal (real (g x)))} \<in> sets M"
    "{x \<in> space M. H (ereal (real (f x))) (-\<infinity>)} \<in> sets M"
    "{x \<in> space M. H (ereal (real (f x))) (\<infinity>)} \<in> sets M"
  shows "{x \<in> space M. H (f x) (g x)} \<in> sets M"
proof -
  let ?G = "\<lambda>y x. if x \<in> g -` {\<infinity>} then H y \<infinity> else if x \<in> g -` {-\<infinity>} then H y (-\<infinity>) else H y (ereal (real (g x)))"
  let ?F = "\<lambda>x. if x \<in> f -` {\<infinity>} then ?G \<infinity> x else if x \<in> f -` {-\<infinity>} then ?G (-\<infinity>) x else ?G (ereal (real (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  moreover 
  have "{x \<in> space M. ?F x} \<in> sets M"
    by (intro sets_Collect H measurable_sets[OF f] measurable_sets[OF g] sets_Collect_If_set) auto
  ultimately
  show ?thesis by simp
qed

lemma
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows borel_measurable_ereal_le[intro,simp]: "{x \<in> space M. f x \<le> g x} \<in> sets M"
    and borel_measurable_ereal_less[intro,simp]: "{x \<in> space M. f x < g x} \<in> sets M"
    and borel_measurable_ereal_eq[intro,simp]: "{w \<in> space M. f w = g w} \<in> sets M"
    and borel_measurable_ereal_neq[intro,simp]: "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
  using f g by (auto simp: f g set_Collect_ereal2[OF f g] intro!: sets_Collect_neg)

lemma borel_measurable_ereal_iff:
  shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M"
proof
  assume "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  from borel_measurable_real_of_ereal[OF this]
  show "f \<in> borel_measurable M" by auto
qed auto

lemma borel_measurable_ereal_iff_real:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "f \<in> borel_measurable M \<longleftrightarrow>
    ((\<lambda>x. real (f x)) \<in> borel_measurable M \<and> f -` {\<infinity>} \<inter> space M \<in> sets M \<and> f -` {-\<infinity>} \<inter> space M \<in> sets M)"
proof safe
  assume *: "(\<lambda>x. real (f x)) \<in> borel_measurable M" "f -` {\<infinity>} \<inter> space M \<in> sets M" "f -` {-\<infinity>} \<inter> space M \<in> sets M"
  have "f -` {\<infinity>} \<inter> space M = {x\<in>space M. f x = \<infinity>}" "f -` {-\<infinity>} \<inter> space M = {x\<in>space M. f x = -\<infinity>}" by auto
  with * have **: "{x\<in>space M. f x = \<infinity>} \<in> sets M" "{x\<in>space M. f x = -\<infinity>} \<in> sets M" by simp_all
  let ?f = "\<lambda>x. if f x = \<infinity> then \<infinity> else if f x = -\<infinity> then -\<infinity> else ereal (real (f x))"
  have "?f \<in> borel_measurable M" using * ** by (intro measurable_If) auto
  also have "?f = f" by (auto simp: fun_eq_iff ereal_real)
  finally show "f \<in> borel_measurable M" .
qed (auto intro: measurable_sets borel_measurable_real_of_ereal)

lemma borel_measurable_eq_atMost_ereal:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..a} \<inter> space M \<in> sets M)"
proof (intro iffI allI)
  assume pos[rule_format]: "\<forall>a. f -` {..a} \<inter> space M \<in> sets M"
  show "f \<in> borel_measurable M"
    unfolding borel_measurable_ereal_iff_real borel_measurable_iff_le
  proof (intro conjI allI)
    fix a :: real
    { fix x :: ereal assume *: "\<forall>i::nat. real i < x"
      have "x = \<infinity>"
      proof (rule ereal_top)
        fix B from reals_Archimedean2[of B] guess n ..
        then have "ereal B < real n" by auto
        with * show "B \<le> x" by (metis less_trans less_imp_le)
      qed }
    then have "f -` {\<infinity>} \<inter> space M = space M - (\<Union>i::nat. f -` {.. real i} \<inter> space M)"
      by (auto simp: not_le)
    then show "f -` {\<infinity>} \<inter> space M \<in> sets M" using pos by (auto simp del: UN_simps intro!: Diff)
    moreover
    have "{-\<infinity>::ereal} = {..-\<infinity>}" by auto
    then show "f -` {-\<infinity>} \<inter> space M \<in> sets M" using pos by auto
    moreover have "{x\<in>space M. f x \<le> ereal a} \<in> sets M"
      using pos[of "ereal a"] by (simp add: vimage_def Int_def conj_commute)
    moreover have "{w \<in> space M. real (f w) \<le> a} =
      (if a < 0 then {w \<in> space M. f w \<le> ereal a} - f -` {-\<infinity>} \<inter> space M
      else {w \<in> space M. f w \<le> ereal a} \<union> (f -` {\<infinity>} \<inter> space M) \<union> (f -` {-\<infinity>} \<inter> space M))" (is "?l = ?r")
      proof (intro set_eqI) fix x show "x \<in> ?l \<longleftrightarrow> x \<in> ?r" by (cases "f x") auto qed
    ultimately show "{w \<in> space M. real (f w) \<le> a} \<in> sets M" by auto
  qed
qed (simp add: measurable_sets)

lemma borel_measurable_eq_atLeast_ereal:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a..} \<inter> space M \<in> sets M)"
proof
  assume pos: "\<forall>a. f -` {a..} \<inter> space M \<in> sets M"
  moreover have "\<And>a. (\<lambda>x. - f x) -` {..a} = f -` {-a ..}"
    by (auto simp: ereal_uminus_le_reorder)
  ultimately have "(\<lambda>x. - f x) \<in> borel_measurable M"
    unfolding borel_measurable_eq_atMost_ereal by auto
  then show "f \<in> borel_measurable M" by simp
qed (simp add: measurable_sets)

lemma greater_eq_le_measurable:
  fixes f :: "'a \<Rightarrow> 'c::linorder"
  shows "f -` {..< a} \<inter> space M \<in> sets M \<longleftrightarrow> f -` {a ..} \<inter> space M \<in> sets M"
proof
  assume "f -` {a ..} \<inter> space M \<in> sets M"
  moreover have "f -` {..< a} \<inter> space M = space M - f -` {a ..} \<inter> space M" by auto
  ultimately show "f -` {..< a} \<inter> space M \<in> sets M" by auto
next
  assume "f -` {..< a} \<inter> space M \<in> sets M"
  moreover have "f -` {a ..} \<inter> space M = space M - f -` {..< a} \<inter> space M" by auto
  ultimately show "f -` {a ..} \<inter> space M \<in> sets M" by auto
qed

lemma borel_measurable_ereal_iff_less:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..< a} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_eq_atLeast_ereal greater_eq_le_measurable ..

lemma less_eq_ge_measurable:
  fixes f :: "'a \<Rightarrow> 'c::linorder"
  shows "f -` {a <..} \<inter> space M \<in> sets M \<longleftrightarrow> f -` {..a} \<inter> space M \<in> sets M"
proof
  assume "f -` {a <..} \<inter> space M \<in> sets M"
  moreover have "f -` {..a} \<inter> space M = space M - f -` {a <..} \<inter> space M" by auto
  ultimately show "f -` {..a} \<inter> space M \<in> sets M" by auto
next
  assume "f -` {..a} \<inter> space M \<in> sets M"
  moreover have "f -` {a <..} \<inter> space M = space M - f -` {..a} \<inter> space M" by auto
  ultimately show "f -` {a <..} \<inter> space M \<in> sets M" by auto
qed

lemma borel_measurable_ereal_iff_ge:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a <..} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_eq_atMost_ereal less_eq_ge_measurable ..

lemma borel_measurable_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real (f x))) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (-\<infinity>) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (\<infinity>) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real (f x))) (-\<infinity>)) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real (f x))) (\<infinity>)) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?G = "\<lambda>y x. if x \<in> g -` {\<infinity>} then H y \<infinity> else if x \<in> g -` {-\<infinity>} then H y (-\<infinity>) else H y (ereal (real (g x)))"
  let ?F = "\<lambda>x. if x \<in> f -` {\<infinity>} then ?G \<infinity> x else if x \<in> f -` {-\<infinity>} then ?G (-\<infinity>) x else ?G (ereal (real (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  moreover 
  have "?F \<in> borel_measurable M"
    by (intro measurable_If_set measurable_sets[OF f] measurable_sets[OF g] H) auto
  ultimately
  show ?thesis by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_eq_const: "{x\<in>space M. f x = c} \<in> sets M"
    and borel_measurable_ereal_neq_const: "{x\<in>space M. f x \<noteq> c} \<in> sets M"
  using f by auto

lemma split_sets:
  "{x\<in>space M. P x \<or> Q x} = {x\<in>space M. P x} \<union> {x\<in>space M. Q x}"
  "{x\<in>space M. P x \<and> Q x} = {x\<in>space M. P x} \<inter> {x\<in>space M. Q x}"
  by auto

lemma
  fixes f :: "'a \<Rightarrow> ereal"
  assumes [simp]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows borel_measurable_ereal_add[intro, simp]: "(\<lambda>x. f x + g x) \<in> borel_measurable M"
    and borel_measurable_ereal_times[intro, simp]: "(\<lambda>x. f x * g x) \<in> borel_measurable M"
    and borel_measurable_ereal_min[simp, intro]: "(\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
    and borel_measurable_ereal_max[simp, intro]: "(\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  by (auto simp add: borel_measurable_ereal2 measurable_If min_def max_def)

lemma
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows borel_measurable_ereal_diff[simp, intro]: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    and borel_measurable_ereal_divide[simp, intro]: "(\<lambda>x. f x / g x) \<in> borel_measurable M"
  unfolding minus_ereal_def divide_ereal_def using assms by auto

lemma borel_measurable_ereal_setsum[simp, intro]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms
    by induct auto
qed simp

lemma borel_measurable_ereal_setprod[simp, intro]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_SUP[simp, intro]:
  fixes f :: "'d\<Colon>countable \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. SUP i : A. f i x) \<in> borel_measurable M" (is "?sup \<in> borel_measurable M")
  unfolding borel_measurable_ereal_iff_ge
proof
  fix a
  have "?sup -` {a<..} \<inter> space M = (\<Union>i\<in>A. {x\<in>space M. a < f i x})"
    by (auto simp: less_SUP_iff)
  then show "?sup -` {a<..} \<inter> space M \<in> sets M"
    using assms by auto
qed

lemma borel_measurable_INF[simp, intro]:
  fixes f :: "'d :: countable \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. INF i : A. f i x) \<in> borel_measurable M" (is "?inf \<in> borel_measurable M")
  unfolding borel_measurable_ereal_iff_less
proof
  fix a
  have "?inf -` {..<a} \<inter> space M = (\<Union>i\<in>A. {x\<in>space M. f i x < a})"
    by (auto simp: INF_less_iff)
  then show "?inf -` {..<a} \<inter> space M \<in> sets M"
    using assms by auto
qed

lemma
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows borel_measurable_liminf[simp, intro]: "(\<lambda>x. liminf (\<lambda>i. f i x)) \<in> borel_measurable M"
    and borel_measurable_limsup[simp, intro]: "(\<lambda>x. limsup (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding liminf_SUPR_INFI limsup_INFI_SUPR using assms by auto

lemma borel_measurable_ereal_LIMSEQ:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> u' x = liminf (\<lambda>n. u n x)"
    using u' by (simp add: lim_imp_Liminf[symmetric])
  then show ?thesis by (simp add: u cong: measurable_cong)
qed

lemma borel_measurable_psuminf[simp, intro]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. f i \<in> borel_measurable M" and pos: "\<And>i x. x \<in> space M \<Longrightarrow> 0 \<le> f i x"
  shows "(\<lambda>x. (\<Sum>i. f i x)) \<in> borel_measurable M"
  apply (subst measurable_cong)
  apply (subst suminf_ereal_eq_SUPR)
  apply (rule pos)
  using assms by auto

section "LIMSEQ is borel measurable"

lemma borel_measurable_LIMSEQ:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> liminf (\<lambda>n. ereal (u n x)) = ereal (u' x)"
    using u' by (simp add: lim_imp_Liminf)
  moreover from u have "(\<lambda>x. liminf (\<lambda>n. ereal (u n x))) \<in> borel_measurable M"
    by auto
  ultimately show ?thesis by (simp cong: measurable_cong add: borel_measurable_ereal_iff)
qed

lemma sets_Collect_Cauchy: 
  fixes f :: "nat \<Rightarrow> 'a => real"
  assumes f: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. Cauchy (\<lambda>i. f i x)} \<in> sets M"
  unfolding Cauchy_iff2 using f by (auto intro!: sets_Collect)

lemma borel_measurable_lim:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes f: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  have *: "\<And>x. lim (\<lambda>i. f i x) =
    (if Cauchy (\<lambda>i. f i x) then lim (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0) else (THE x. False))"
    by (auto simp: lim_def convergent_eq_cauchy[symmetric])
  { fix x have "convergent (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)"
      by (cases "Cauchy (\<lambda>i. f i x)")
         (auto simp add: convergent_eq_cauchy[symmetric] convergent_def) }
  note convergent = this
  show ?thesis
    unfolding *
    apply (intro measurable_If sets_Collect_Cauchy f borel_measurable_const)
    apply (rule borel_measurable_LIMSEQ)
    apply (rule convergent_LIMSEQ_iff[THEN iffD1, OF convergent])
    apply (intro measurable_If sets_Collect_Cauchy f borel_measurable_const)
    done
qed

lemma borel_measurable_suminf:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes f: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. suminf (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric]
  by (simp add: f borel_measurable_lim)

end 
