(* Author: Armin Heller, Johannes Hoelzl, TU Muenchen *)

header {*Borel spaces*}

theory Borel
  imports Sigma_Algebra Positive_Infinite_Real Multivariate_Analysis
begin

section "Generic Borel spaces"

definition "borel_space = sigma (UNIV::'a::topological_space set) open"
abbreviation "borel_measurable M \<equiv> measurable M borel_space"

interpretation borel_space: sigma_algebra borel_space
  using sigma_algebra_sigma by (auto simp: borel_space_def)

lemma in_borel_measurable:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sets (sigma UNIV open).
      f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_space_def)

lemma in_borel_measurable_borel_space:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sets borel_space.
      f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_space_def)

lemma space_borel_space[simp]: "space borel_space = UNIV"
  unfolding borel_space_def by auto

lemma borel_space_open[simp]:
  assumes "open A" shows "A \<in> sets borel_space"
proof -
  have "A \<in> open" unfolding mem_def using assms .
  thus ?thesis unfolding borel_space_def sigma_def by (auto intro!: sigma_sets.Basic)
qed

lemma borel_space_closed[simp]:
  assumes "closed A" shows "A \<in> sets borel_space"
proof -
  have "space borel_space - (- A) \<in> sets borel_space"
    using assms unfolding closed_def by (blast intro: borel_space_open)
  thus ?thesis by simp
qed

lemma (in sigma_algebra) borel_measurable_vimage:
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes borel: "f \<in> borel_measurable M"
  shows "f -` {x} \<inter> space M \<in> sets M"
proof (cases "x \<in> f ` space M")
  case True then obtain y where "x = f y" by auto
  from closed_sing[of "f y"]
  have "{f y} \<in> sets borel_space" by (rule borel_space_closed)
  with assms show ?thesis
    unfolding in_borel_measurable_borel_space `x = f y` by auto
next
  case False hence "f -` {x} \<inter> space M = {}" by auto
  thus ?thesis by auto
qed

lemma (in sigma_algebra) borel_measurableI:
  fixes f :: "'a \<Rightarrow> 'x\<Colon>topological_space"
  assumes "\<And>S. open S \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable M"
  unfolding borel_space_def
proof (rule measurable_sigma)
  fix S :: "'x set" assume "S \<in> open" thus "f -` S \<inter> space M \<in> sets M"
    using assms[of S] by (simp add: mem_def)
qed simp_all

lemma borel_space_singleton[simp, intro]:
  fixes x :: "'a::t1_space"
  shows "A \<in> sets borel_space \<Longrightarrow> insert x A \<in> sets borel_space"
  proof (rule borel_space.insert_in_sets)
    show "{x} \<in> sets borel_space"
      using closed_sing[of x] by (rule borel_space_closed)
  qed simp

lemma (in sigma_algebra) borel_measurable_const[simp, intro]:
  "(\<lambda>x. c) \<in> borel_measurable M"
  by (auto intro!: measurable_const)

lemma (in sigma_algebra) borel_measurable_indicator:
  assumes A: "A \<in> sets M"
  shows "indicator A \<in> borel_measurable M"
  unfolding indicator_def_raw using A
  by (auto intro!: measurable_If_set borel_measurable_const)

lemma borel_measurable_translate:
  assumes "A \<in> sets borel_space" and trans: "\<And>B. open B \<Longrightarrow> f -` B \<in> sets borel_space"
  shows "f -` A \<in> sets borel_space"
proof -
  have "A \<in> sigma_sets UNIV open" using assms
    by (simp add: borel_space_def sigma_def)
  thus ?thesis
  proof (induct rule: sigma_sets.induct)
    case (Basic a) thus ?case using trans[of a] by (simp add: mem_def)
  next
    case (Compl a)
    moreover have "UNIV \<in> sets borel_space"
      by (metis borel_space.top borel_space_def_raw mem_def space_sigma)
    ultimately show ?case
      by (auto simp: vimage_Diff borel_space.Diff)
  qed (auto simp add: vimage_UN)
qed

section "Borel spaces on euclidean spaces"

lemma lessThan_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{..< a} \<in> sets borel_space"
  by (blast intro: borel_space_open)

lemma greaterThan_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{a <..} \<in> sets borel_space"
  by (blast intro: borel_space_open)

lemma greaterThanLessThan_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a<..<b} \<in> sets borel_space"
  by (blast intro: borel_space_open)

lemma atMost_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{..a} \<in> sets borel_space"
  by (blast intro: borel_space_closed)

lemma atLeast_borel[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "{a..} \<in> sets borel_space"
  by (blast intro: borel_space_closed)

lemma atLeastAtMost_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a..b} \<in> sets borel_space"
  by (blast intro: borel_space_closed)

lemma greaterThanAtMost_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a<..b} \<in> sets borel_space"
  unfolding greaterThanAtMost_def by blast

lemma atLeastLessThan_borel[simp, intro]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{a..<b} \<in> sets borel_space"
  unfolding atLeastLessThan_def by blast

lemma hafspace_less_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. a < x $$ i} \<in> sets borel_space"
  by (auto intro!: borel_space_open open_halfspace_component_gt)

lemma hafspace_greater_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. x $$ i < a} \<in> sets borel_space"
  by (auto intro!: borel_space_open open_halfspace_component_lt)

lemma hafspace_less_eq_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. a \<le> x $$ i} \<in> sets borel_space"
  by (auto intro!: borel_space_closed closed_halfspace_component_ge)

lemma hafspace_greater_eq_borel[simp, intro]:
  fixes a :: real
  shows "{x::'a::euclidean_space. x $$ i \<le> a} \<in> sets borel_space"
  by (auto intro!: borel_space_closed closed_halfspace_component_le)

lemma (in sigma_algebra) borel_measurable_less[simp, intro]:
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

lemma (in sigma_algebra) borel_measurable_le[simp, intro]:
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

lemma (in sigma_algebra) borel_measurable_eq[simp, intro]:
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

lemma (in sigma_algebra) borel_measurable_neq[simp, intro]:
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

lemma halfspace_span_open:
  "sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a})))
    \<subseteq> sets borel_space"
  by (auto intro!: borel_space.sigma_sets_subset[simplified] borel_space_open
                   open_halfspace_component_lt simp: sets_sigma)

lemma halfspace_lt_in_halfspace:
  "{x\<Colon>'a. x $$ i < a} \<in> sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a})))"
  unfolding sets_sigma by (rule sigma_sets.Basic) auto

lemma halfspace_gt_in_halfspace:
  "{x\<Colon>'a. a < x $$ i} \<in> sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a})))"
    (is "?set \<in> sets ?SIGMA")
proof -
  interpret sigma_algebra ?SIGMA by (rule sigma_algebra_sigma) simp
  have *: "?set = (\<Union>n. space ?SIGMA - {x\<Colon>'a. x $$ i < a + 1 / real (Suc n)})"
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
  show "?set \<in> sets ?SIGMA" unfolding *
    by (safe intro!: countable_UN Diff halfspace_lt_in_halfspace)
qed

lemma (in sigma_algebra) sets_sigma_subset:
  assumes "A = space M"
  assumes "B \<subseteq> sets M"
  shows "sets (sigma A B) \<subseteq> sets M"
  by (unfold assms sets_sigma, rule sigma_sets_subset, rule assms)

lemma open_span_halfspace:
  "sets borel_space \<subseteq> sets (sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. x $$ i < a})))"
    (is "_ \<subseteq> sets ?SIGMA")
proof (unfold borel_space_def, rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) simp
  then interpret sigma_algebra ?SIGMA .
  fix S :: "'a set" assume "S \<in> open" then have "open S" unfolding mem_def .
  from open_UNION[OF this]
  obtain I where *: "S =
    (\<Union>(a, b)\<in>I.
        (\<Inter> i<DIM('a). {x. (Chi (real_of_rat \<circ> op ! a)::'a) $$ i < x $$ i}) \<inter>
        (\<Inter> i<DIM('a). {x. x $$ i < (Chi (real_of_rat \<circ> op ! b)::'a) $$ i}))"
    unfolding greaterThanLessThan_def
    unfolding eucl_greaterThan_eq_halfspaces[where 'a='a]
    unfolding eucl_lessThan_eq_halfspaces[where 'a='a]
    by blast
  show "S \<in> sets ?SIGMA"
    unfolding *
    by (auto intro!: countable_UN Int countable_INT halfspace_lt_in_halfspace halfspace_gt_in_halfspace)
qed auto

lemma halfspace_span_halfspace_le:
  "sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a}))) \<subseteq>
   sets (sigma UNIV (range (\<lambda> (a, i). {x. x $$ i \<le> a})))"
  (is "_ \<subseteq> sets ?SIGMA")
proof (rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
  then interpret sigma_algebra ?SIGMA .
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
  show "{x. x$$i < a} \<in> sets ?SIGMA" unfolding *
    by (safe intro!: countable_UN)
       (auto simp: sets_sigma intro!: sigma_sets.Basic)
qed auto

lemma halfspace_span_halfspace_ge:
  "sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a}))) \<subseteq> 
   sets (sigma UNIV (range (\<lambda> (a, i). {x. a \<le> x $$ i})))"
  (is "_ \<subseteq> sets ?SIGMA")
proof (rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
  then interpret sigma_algebra ?SIGMA .
  fix a i have *: "{x::'a. x$$i < a} = space ?SIGMA - {x::'a. a \<le> x$$i}" by auto
  show "{x. x$$i < a} \<in> sets ?SIGMA" unfolding *
    by (safe intro!: Diff)
       (auto simp: sets_sigma intro!: sigma_sets.Basic)
qed auto

lemma halfspace_le_span_halfspace_gt:
  "sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i \<le> a}))) \<subseteq> 
   sets (sigma UNIV (range (\<lambda> (a, i). {x. a < x $$ i})))"
  (is "_ \<subseteq> sets ?SIGMA")
proof (rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
  then interpret sigma_algebra ?SIGMA .
  fix a i have *: "{x::'a. x$$i \<le> a} = space ?SIGMA - {x::'a. a < x$$i}" by auto
  show "{x. x$$i \<le> a} \<in> sets ?SIGMA" unfolding *
    by (safe intro!: Diff)
       (auto simp: sets_sigma intro!: sigma_sets.Basic)
qed auto

lemma halfspace_le_span_atMost:
  "sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i \<le> a}))) \<subseteq>
   sets (sigma UNIV (range (\<lambda>a. {..a\<Colon>'a\<Colon>ordered_euclidean_space})))"
  (is "_ \<subseteq> sets ?SIGMA")
proof (rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
  then interpret sigma_algebra ?SIGMA .
  fix a i
  show "{x. x$$i \<le> a} \<in> sets ?SIGMA"
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
    show "{x. x$$i \<le> a} \<in> sets ?SIGMA" unfolding *
      by (safe intro!: countable_UN)
         (auto simp: sets_sigma intro!: sigma_sets.Basic)
  next
    assume "\<not> i < DIM('a)"
    then show "{x. x$$i \<le> a} \<in> sets ?SIGMA"
      using top by auto
  qed
qed auto

lemma halfspace_le_span_greaterThan:
  "sets (sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i \<le> a}))) \<subseteq>
   sets (sigma UNIV (range (\<lambda>a. {a<..})))"
  (is "_ \<subseteq> sets ?SIGMA")
proof (rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
  then interpret sigma_algebra ?SIGMA .
  fix a i
  show "{x. x$$i \<le> a} \<in> sets ?SIGMA"
  proof cases
    assume "i < DIM('a)"
    have "{x::'a. x$$i \<le> a} = space ?SIGMA - {x::'a. a < x$$i}" by auto
    also have *: "{x::'a. a < x$$i} = (\<Union>k::nat. {(\<chi>\<chi> n. if n = i then a else -real k) <..})" using `i <DIM('a)`
    proof (safe, simp_all add: eucl_less[where 'a='a] split: split_if_asm)
      fix x
      from real_arch_lt[of "Max ((\<lambda>i. -x$$i)`{..<DIM('a)})"]
      guess k::nat .. note k = this
      { fix i assume "i < DIM('a)"
        then have "-x$$i < real k"
          using k by (subst (asm) Max_less_iff) auto
        then have "- real k < x$$i" by simp }
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> -real k < x $$ ia"
        by (auto intro!: exI[of _ k])
    qed
    finally show "{x. x$$i \<le> a} \<in> sets ?SIGMA"
      apply (simp only:)
      apply (safe intro!: countable_UN Diff)
      by (auto simp: sets_sigma intro!: sigma_sets.Basic)
  next
    assume "\<not> i < DIM('a)"
    then show "{x. x$$i \<le> a} \<in> sets ?SIGMA"
      using top by auto
  qed
qed auto

lemma atMost_span_atLeastAtMost:
  "sets (sigma UNIV (range (\<lambda>a. {..a\<Colon>'a\<Colon>ordered_euclidean_space}))) \<subseteq>
   sets (sigma UNIV (range (\<lambda>(a,b). {a..b})))"
  (is "_ \<subseteq> sets ?SIGMA")
proof (rule sigma_algebra.sets_sigma_subset, safe)
  show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
  then interpret sigma_algebra ?SIGMA .
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
  show "{..a} \<in> sets ?SIGMA" unfolding *
    by (safe intro!: countable_UN)
       (auto simp: sets_sigma intro!: sigma_sets.Basic)
qed auto

lemma borel_space_eq_greaterThanLessThan:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a, b). {a <..< (b :: 'a \<Colon> ordered_euclidean_space)})))"
    (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
  show "sets borel_space \<subseteq> sets ?SIGMA"
    unfolding borel_space_def
  proof (rule sigma_algebra.sets_sigma_subset, safe)
    show "sigma_algebra ?SIGMA" by (rule sigma_algebra_sigma) auto
    then interpret sigma_algebra ?SIGMA .
    fix M :: "'a set" assume "M \<in> open"
    then have "open M" by (simp add: mem_def)
    show "M \<in> sets ?SIGMA"
      apply (subst open_UNION[OF `open M`])
      apply (safe intro!: countable_UN)
      by (auto simp add: sigma_def intro!: sigma_sets.Basic)
  qed auto
qed

lemma borel_space_eq_atMost:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> a. {.. a::'a\<Colon>ordered_euclidean_space})))"
    (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using halfspace_le_span_atMost halfspace_span_halfspace_le open_span_halfspace
    by auto
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma borel_space_eq_atLeastAtMost:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a :: 'a\<Colon>ordered_euclidean_space, b). {a .. b})))"
   (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using atMost_span_atLeastAtMost halfspace_le_span_atMost
      halfspace_span_halfspace_le open_span_halfspace
    by auto
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma borel_space_eq_greaterThan:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a :: 'a\<Colon>ordered_euclidean_space). {a <..})))"
   (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using halfspace_le_span_greaterThan
      halfspace_span_halfspace_le open_span_halfspace
    by auto
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma borel_space_eq_halfspace_le:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. x$$i \<le> a})))"
   (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using open_span_halfspace halfspace_span_halfspace_le by auto
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma borel_space_eq_halfspace_less:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. x$$i < a})))"
   (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using open_span_halfspace .
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma borel_space_eq_halfspace_gt:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. a < x$$i})))"
   (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using halfspace_le_span_halfspace_gt open_span_halfspace halfspace_span_halfspace_le by auto
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma borel_space_eq_halfspace_ge:
  "sets borel_space = sets (sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. a \<le> x$$i})))"
   (is "_ = sets ?SIGMA")
proof (rule antisym)
  show "sets borel_space \<subseteq> sets ?SIGMA"
    using halfspace_span_halfspace_ge open_span_halfspace by auto
  show "sets ?SIGMA \<subseteq> sets borel_space"
    by (rule borel_space.sets_sigma_subset) auto
qed

lemma (in sigma_algebra) borel_measurable_halfspacesI:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  assumes "sets borel_space = sets (sigma UNIV (range F))"
  and "\<And>a i. S a i = f -` F (a,i) \<inter> space M"
  and "\<And>a i. \<not> i < DIM('c) \<Longrightarrow> S a i \<in> sets M"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a::real. S a i \<in> sets M)"
proof safe
  fix a :: real and i assume i: "i < DIM('c)" and f: "f \<in> borel_measurable M"
  then show "S a i \<in> sets M" unfolding assms
    by (auto intro!: measurable_sets sigma_sets.Basic simp: assms(1) sigma_def)
next
  assume a: "\<forall>i<DIM('c). \<forall>a. S a i \<in> sets M"
  { fix a i have "S a i \<in> sets M"
    proof cases
      assume "i < DIM('c)"
      with a show ?thesis unfolding assms(2) by simp
    next
      assume "\<not> i < DIM('c)"
      from assms(3)[OF this] show ?thesis .
    qed }
  then have "f \<in> measurable M (sigma UNIV (range F))"
    by (auto intro!: measurable_sigma simp: assms(2))
  then show "f \<in> borel_measurable M" unfolding measurable_def
    unfolding assms(1) by simp
qed

lemma (in sigma_algebra) borel_measurable_iff_halfspace_le:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. f w $$ i \<le> a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_space_eq_halfspace_le]) auto

lemma (in sigma_algebra) borel_measurable_iff_halfspace_less:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. f w $$ i < a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_space_eq_halfspace_less]) auto

lemma (in sigma_algebra) borel_measurable_iff_halfspace_ge:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. a \<le> f w $$ i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_space_eq_halfspace_ge]) auto

lemma (in sigma_algebra) borel_measurable_iff_halfspace_greater:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. a < f w $$ i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_space_eq_halfspace_gt]) auto

lemma (in sigma_algebra) borel_measurable_iff_le:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M)"
  using borel_measurable_iff_halfspace_le[where 'c=real] by simp

lemma (in sigma_algebra) borel_measurable_iff_less:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w < a} \<in> sets M)"
  using borel_measurable_iff_halfspace_less[where 'c=real] by simp

lemma (in sigma_algebra) borel_measurable_iff_ge:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a \<le> f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_ge[where 'c=real] by simp

lemma (in sigma_algebra) borel_measurable_iff_greater:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a < f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_greater[where 'c=real] by simp

subsection "Borel measurable operators"

lemma (in sigma_algebra) affine_borel_measurable_vector:
  fixes f :: "'a \<Rightarrow> 'x::real_normed_vector"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. a + b *\<^sub>R f x) \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S :: "'x set" assume "open S"
  show "(\<lambda>x. a + b *\<^sub>R f x) -` S \<inter> space M \<in> sets M"
  proof cases
    assume "b \<noteq> 0"
    with `open S` have "((\<lambda>x. (- a + x) /\<^sub>R b) ` S) \<in> open" (is "?S \<in> open")
      by (auto intro!: open_affinity simp: scaleR.add_right mem_def)
    hence "?S \<in> sets borel_space"
      unfolding borel_space_def by (auto simp: sigma_def intro!: sigma_sets.Basic)
    moreover
    from `b \<noteq> 0` have "(\<lambda>x. a + b *\<^sub>R f x) -` S = f -` ?S"
      apply auto by (rule_tac x="a + b *\<^sub>R f x" in image_eqI, simp_all)
    ultimately show ?thesis using assms unfolding in_borel_measurable_borel_space
      by auto
  qed simp
qed

lemma (in sigma_algebra) affine_borel_measurable:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. a + (g x) * b) \<in> borel_measurable M"
  using affine_borel_measurable_vector[OF assms] by (simp add: mult_commute)

lemma (in sigma_algebra) borel_measurable_add[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
proof -
  have 1: "\<And>a. {w\<in>space M. a \<le> f w + g w} = {w \<in> space M. a + g w * -1 \<le> f w}"
    by auto
  have "\<And>a. (\<lambda>w. a + (g w) * -1) \<in> borel_measurable M"
    by (rule affine_borel_measurable [OF g])
  then have "\<And>a. {w \<in> space M. (\<lambda>w. a + (g w) * -1)(w) \<le> f w} \<in> sets M" using f
    by auto
  then have "\<And>a. {w \<in> space M. a \<le> f w + g w} \<in> sets M"
    by (simp add: 1)
  then show ?thesis
    by (simp add: borel_measurable_iff_ge)
qed

lemma (in sigma_algebra) borel_measurable_square:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. (f x)^2) \<in> borel_measurable M"
proof -
  {
    fix a
    have "{w \<in> space M. (f w)\<twosuperior> \<le> a} \<in> sets M"
    proof (cases rule: linorder_cases [of a 0])
      case less
      hence "{w \<in> space M. (f w)\<twosuperior> \<le> a} = {}"
        by auto (metis less order_le_less_trans power2_less_0)
      also have "... \<in> sets M"
        by (rule empty_sets)
      finally show ?thesis .
    next
      case equal
      hence "{w \<in> space M. (f w)\<twosuperior> \<le> a} =
             {w \<in> space M. f w \<le> 0} \<inter> {w \<in> space M. 0 \<le> f w}"
        by auto
      also have "... \<in> sets M"
        apply (insert f)
        apply (rule Int)
        apply (simp add: borel_measurable_iff_le)
        apply (simp add: borel_measurable_iff_ge)
        done
      finally show ?thesis .
    next
      case greater
      have "\<forall>x. (f x ^ 2 \<le> sqrt a ^ 2) = (- sqrt a  \<le> f x & f x \<le> sqrt a)"
        by (metis abs_le_interval_iff abs_of_pos greater real_sqrt_abs
                  real_sqrt_le_iff real_sqrt_power)
      hence "{w \<in> space M. (f w)\<twosuperior> \<le> a} =
             {w \<in> space M. -(sqrt a) \<le> f w} \<inter> {w \<in> space M. f w \<le> sqrt a}"
        using greater by auto
      also have "... \<in> sets M"
        apply (insert f)
        apply (rule Int)
        apply (simp add: borel_measurable_iff_ge)
        apply (simp add: borel_measurable_iff_le)
        done
      finally show ?thesis .
    qed
  }
  thus ?thesis by (auto simp add: borel_measurable_iff_le)
qed

lemma times_eq_sum_squares:
   fixes x::real
   shows"x*y = ((x+y)^2)/4 - ((x-y)^ 2)/4"
by (simp add: power2_eq_square ring_distribs diff_divide_distrib [symmetric])

lemma (in sigma_algebra) borel_measurable_uminus[simp, intro]:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. - g x) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. - g x) = (\<lambda>x. 0 + (g x) * -1)"
    by simp
  also have "... \<in> borel_measurable M"
    by (fast intro: affine_borel_measurable g)
  finally show ?thesis .
qed

lemma (in sigma_algebra) borel_measurable_times[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
proof -
  have 1: "(\<lambda>x. 0 + (f x + g x)\<twosuperior> * inverse 4) \<in> borel_measurable M"
    using assms by (fast intro: affine_borel_measurable borel_measurable_square)
  have "(\<lambda>x. -((f x + -g x) ^ 2 * inverse 4)) =
        (\<lambda>x. 0 + ((f x + -g x) ^ 2 * inverse -4))"
    by (simp add: minus_divide_right)
  also have "... \<in> borel_measurable M"
    using f g by (fast intro: affine_borel_measurable borel_measurable_square f g)
  finally have 2: "(\<lambda>x. -((f x + -g x) ^ 2 * inverse 4)) \<in> borel_measurable M" .
  show ?thesis
    apply (simp add: times_eq_sum_squares diff_minus)
    using 1 2 by simp
qed

lemma (in sigma_algebra) borel_measurable_diff[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
  unfolding diff_minus using assms by fast

lemma (in sigma_algebra) borel_measurable_setsum[simp, intro]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma (in sigma_algebra) borel_measurable_inverse[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. inverse (f x)) \<in> borel_measurable M"
  unfolding borel_measurable_iff_ge unfolding inverse_eq_divide
proof safe
  fix a :: real
  have *: "{w \<in> space M. a \<le> 1 / f w} =
      ({w \<in> space M. 0 < f w} \<inter> {w \<in> space M. a * f w \<le> 1}) \<union>
      ({w \<in> space M. f w < 0} \<inter> {w \<in> space M. 1 \<le> a * f w}) \<union>
      ({w \<in> space M. f w = 0} \<inter> {w \<in> space M. a \<le> 0})" by (auto simp: le_divide_eq)
  show "{w \<in> space M. a \<le> 1 / f w} \<in> sets M" using assms unfolding *
    by (auto intro!: Int Un)
qed

lemma (in sigma_algebra) borel_measurable_divide[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  and "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x / g x) \<in> borel_measurable M"
  unfolding field_divide_inverse
  by (rule borel_measurable_inverse borel_measurable_times assms)+

lemma (in sigma_algebra) borel_measurable_max[intro, simp]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  unfolding borel_measurable_iff_le
proof safe
  fix a
  have "{x \<in> space M. max (g x) (f x) \<le> a} =
    {x \<in> space M. g x \<le> a} \<inter> {x \<in> space M. f x \<le> a}" by auto
  thus "{x \<in> space M. max (g x) (f x) \<le> a} \<in> sets M"
    using assms unfolding borel_measurable_iff_le
    by (auto intro!: Int)
qed

lemma (in sigma_algebra) borel_measurable_min[intro, simp]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
  unfolding borel_measurable_iff_ge
proof safe
  fix a
  have "{x \<in> space M. a \<le> min (g x) (f x)} =
    {x \<in> space M. a \<le> g x} \<inter> {x \<in> space M. a \<le> f x}" by auto
  thus "{x \<in> space M. a \<le> min (g x) (f x)} \<in> sets M"
    using assms unfolding borel_measurable_iff_ge
    by (auto intro!: Int)
qed

lemma (in sigma_algebra) borel_measurable_abs[simp, intro]:
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. \<bar>f x :: real\<bar>) \<in> borel_measurable M"
proof -
  have *: "\<And>x. \<bar>f x\<bar> = max 0 (f x) + max 0 (- f x)" by (simp add: max_def)
  show ?thesis unfolding * using assms by auto
qed

section "Borel space over the real line with infinity"

lemma borel_space_Real_measurable:
  "A \<in> sets borel_space \<Longrightarrow> Real -` A \<in> sets borel_space"
proof (rule borel_measurable_translate)
  fix B :: "pinfreal set" assume "open B"
  then obtain T x where T: "open T" "Real ` (T \<inter> {0..}) = B - {\<omega>}" and
    x: "\<omega> \<in> B \<Longrightarrow> 0 \<le> x" "\<omega> \<in> B \<Longrightarrow> {Real x <..} \<subseteq> B"
    unfolding open_pinfreal_def by blast

  have "Real -` B = Real -` (B - {\<omega>})" by auto
  also have "\<dots> = Real -` (Real ` (T \<inter> {0..}))" using T by simp
  also have "\<dots> = (if 0 \<in> T then T \<union> {.. 0} else T \<inter> {0..})"
    apply (auto simp add: Real_eq_Real image_iff)
    apply (rule_tac x="max 0 x" in bexI)
    by (auto simp: max_def)
  finally show "Real -` B \<in> sets borel_space"
    using `open T` by auto
qed simp

lemma borel_space_real_measurable:
  "A \<in> sets borel_space \<Longrightarrow> (real -` A :: pinfreal set) \<in> sets borel_space"
proof (rule borel_measurable_translate)
  fix B :: "real set" assume "open B"
  { fix x have "0 < real x \<longleftrightarrow> (\<exists>r>0. x = Real r)" by (cases x) auto }
  note Ex_less_real = this
  have *: "real -` B = (if 0 \<in> B then real -` (B \<inter> {0 <..}) \<union> {0, \<omega>} else real -` (B \<inter> {0 <..}))"
    by (force simp: Ex_less_real)

  have "open (real -` (B \<inter> {0 <..}) :: pinfreal set)"
    unfolding open_pinfreal_def using `open B`
    by (auto intro!: open_Int exI[of _ "B \<inter> {0 <..}"] simp: image_iff Ex_less_real)
  then show "(real -` B :: pinfreal set) \<in> sets borel_space" unfolding * by auto
qed simp

lemma (in sigma_algebra) borel_measurable_Real[intro, simp]:
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. Real (f x)) \<in> borel_measurable M"
  unfolding in_borel_measurable_borel_space
proof safe
  fix S :: "pinfreal set" assume "S \<in> sets borel_space"
  from borel_space_Real_measurable[OF this]
  have "(Real \<circ> f) -` S \<inter> space M \<in> sets M"
    using assms
    unfolding vimage_compose in_borel_measurable_borel_space
    by auto
  thus "(\<lambda>x. Real (f x)) -` S \<inter> space M \<in> sets M" by (simp add: comp_def)
qed

lemma (in sigma_algebra) borel_measurable_real[intro, simp]:
  fixes f :: "'a \<Rightarrow> pinfreal"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. real (f x)) \<in> borel_measurable M"
  unfolding in_borel_measurable_borel_space
proof safe
  fix S :: "real set" assume "S \<in> sets borel_space"
  from borel_space_real_measurable[OF this]
  have "(real \<circ> f) -` S \<inter> space M \<in> sets M"
    using assms
    unfolding vimage_compose in_borel_measurable_borel_space
    by auto
  thus "(\<lambda>x. real (f x)) -` S \<inter> space M \<in> sets M" by (simp add: comp_def)
qed

lemma (in sigma_algebra) borel_measurable_Real_eq:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
  shows "(\<lambda>x. Real (f x)) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M"
proof
  have [simp]: "(\<lambda>x. Real (f x)) -` {\<omega>} \<inter> space M = {}"
    by auto
  assume "(\<lambda>x. Real (f x)) \<in> borel_measurable M"
  hence "(\<lambda>x. real (Real (f x))) \<in> borel_measurable M"
    by (rule borel_measurable_real)
  moreover have "\<And>x. x \<in> space M \<Longrightarrow> real (Real (f x)) = f x"
    using assms by auto
  ultimately show "f \<in> borel_measurable M"
    by (simp cong: measurable_cong)
qed auto

lemma (in sigma_algebra) borel_measurable_pinfreal_eq_real:
  "f \<in> borel_measurable M \<longleftrightarrow>
    ((\<lambda>x. real (f x)) \<in> borel_measurable M \<and> f -` {\<omega>} \<inter> space M \<in> sets M)"
proof safe
  assume "f \<in> borel_measurable M"
  then show "(\<lambda>x. real (f x)) \<in> borel_measurable M" "f -` {\<omega>} \<inter> space M \<in> sets M"
    by (auto intro: borel_measurable_vimage borel_measurable_real)
next
  assume *: "(\<lambda>x. real (f x)) \<in> borel_measurable M" "f -` {\<omega>} \<inter> space M \<in> sets M"
  have "f -` {\<omega>} \<inter> space M = {x\<in>space M. f x = \<omega>}" by auto
  with * have **: "{x\<in>space M. f x = \<omega>} \<in> sets M" by simp
  have f: "f = (\<lambda>x. if f x = \<omega> then \<omega> else Real (real (f x)))"
    by (simp add: expand_fun_eq Real_real)
  show "f \<in> borel_measurable M"
    apply (subst f)
    apply (rule measurable_If)
    using * ** by auto
qed

lemma (in sigma_algebra) less_eq_ge_measurable:
  fixes f :: "'a \<Rightarrow> 'c::linorder"
  shows "{x\<in>space M. a < f x} \<in> sets M \<longleftrightarrow> {x\<in>space M. f x \<le> a} \<in> sets M"
proof
  assume "{x\<in>space M. f x \<le> a} \<in> sets M"
  moreover have "{x\<in>space M. a < f x} = space M - {x\<in>space M. f x \<le> a}" by auto
  ultimately show "{x\<in>space M. a < f x} \<in> sets M" by auto
next
  assume "{x\<in>space M. a < f x} \<in> sets M"
  moreover have "{x\<in>space M. f x \<le> a} = space M - {x\<in>space M. a < f x}" by auto
  ultimately show "{x\<in>space M. f x \<le> a} \<in> sets M" by auto
qed

lemma (in sigma_algebra) greater_eq_le_measurable:
  fixes f :: "'a \<Rightarrow> 'c::linorder"
  shows "{x\<in>space M. f x < a} \<in> sets M \<longleftrightarrow> {x\<in>space M. a \<le> f x} \<in> sets M"
proof
  assume "{x\<in>space M. a \<le> f x} \<in> sets M"
  moreover have "{x\<in>space M. f x < a} = space M - {x\<in>space M. a \<le> f x}" by auto
  ultimately show "{x\<in>space M. f x < a} \<in> sets M" by auto
next
  assume "{x\<in>space M. f x < a} \<in> sets M"
  moreover have "{x\<in>space M. a \<le> f x} = space M - {x\<in>space M. f x < a}" by auto
  ultimately show "{x\<in>space M. a \<le> f x} \<in> sets M" by auto
qed

lemma (in sigma_algebra) less_eq_le_pinfreal_measurable:
  fixes f :: "'a \<Rightarrow> pinfreal"
  shows "(\<forall>a. {x\<in>space M. a < f x} \<in> sets M) \<longleftrightarrow> (\<forall>a. {x\<in>space M. a \<le> f x} \<in> sets M)"
proof
  assume a: "\<forall>a. {x\<in>space M. a \<le> f x} \<in> sets M"
  show "\<forall>a. {x \<in> space M. a < f x} \<in> sets M"
  proof
    fix a show "{x \<in> space M. a < f x} \<in> sets M"
    proof (cases a)
      case (preal r)
      have "{x\<in>space M. a < f x} = (\<Union>i. {x\<in>space M. a + inverse (of_nat (Suc i)) \<le> f x})"
      proof safe
        fix x assume "a < f x" and [simp]: "x \<in> space M"
        with ex_pinfreal_inverse_of_nat_Suc_less[of "f x - a"]
        obtain n where "a + inverse (of_nat (Suc n)) < f x"
          by (cases "f x", auto simp: pinfreal_minus_order)
        then have "a + inverse (of_nat (Suc n)) \<le> f x" by simp
        then show "x \<in> (\<Union>i. {x \<in> space M. a + inverse (of_nat (Suc i)) \<le> f x})"
          by auto
      next
        fix i x assume [simp]: "x \<in> space M"
        have "a < a + inverse (of_nat (Suc i))" using preal by auto
        also assume "a + inverse (of_nat (Suc i)) \<le> f x"
        finally show "a < f x" .
      qed
      with a show ?thesis by auto
    qed simp
  qed
next
  assume a': "\<forall>a. {x \<in> space M. a < f x} \<in> sets M"
  then have a: "\<forall>a. {x \<in> space M. f x \<le> a} \<in> sets M" unfolding less_eq_ge_measurable .
  show "\<forall>a. {x \<in> space M. a \<le> f x} \<in> sets M" unfolding greater_eq_le_measurable[symmetric]
  proof
    fix a show "{x \<in> space M. f x < a} \<in> sets M"
    proof (cases a)
      case (preal r)
      show ?thesis
      proof cases
        assume "a = 0" then show ?thesis by simp
      next
        assume "a \<noteq> 0"
        have "{x\<in>space M. f x < a} = (\<Union>i. {x\<in>space M. f x \<le> a - inverse (of_nat (Suc i))})"
        proof safe
          fix x assume "f x < a" and [simp]: "x \<in> space M"
          with ex_pinfreal_inverse_of_nat_Suc_less[of "a - f x"]
          obtain n where "inverse (of_nat (Suc n)) < a - f x"
            using preal by (cases "f x") auto
          then have "f x \<le> a - inverse (of_nat (Suc n)) "
            using preal by (cases "f x") (auto split: split_if_asm)
          then show "x \<in> (\<Union>i. {x \<in> space M. f x \<le> a - inverse (of_nat (Suc i))})"
            by auto
        next
          fix i x assume [simp]: "x \<in> space M"
          assume "f x \<le> a - inverse (of_nat (Suc i))"
          also have "\<dots> < a" using `a \<noteq> 0` preal by auto
          finally show "f x < a" .
        qed
        with a show ?thesis by auto
      qed
    next
      case infinite
      have "f -` {\<omega>} \<inter> space M = (\<Inter>n. {x\<in>space M. of_nat n < f x})"
      proof (safe, simp_all, safe)
        fix x assume *: "\<forall>n::nat. Real (real n) < f x"
        show "f x = \<omega>"    proof (rule ccontr)
          assume "f x \<noteq> \<omega>"
          with real_arch_lt[of "real (f x)"] obtain n where "f x < of_nat n"
            by (auto simp: pinfreal_noteq_omega_Ex)
          with *[THEN spec, of n] show False by auto
        qed
      qed
      with a' have \<omega>: "f -` {\<omega>} \<inter> space M \<in> sets M" by auto
      moreover have "{x \<in> space M. f x < a} = space M - f -` {\<omega>} \<inter> space M"
        using infinite by auto
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_iff_greater:
  "(f::'a \<Rightarrow> pinfreal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. {x\<in>space M. a < f x} \<in> sets M)"
proof safe
  fix a assume f: "f \<in> borel_measurable M"
  have "{x\<in>space M. a < f x} = f -` {a <..} \<inter> space M" by auto
  with f show "{x\<in>space M. a < f x} \<in> sets M"
    by (auto intro!: measurable_sets)
next
  assume *: "\<forall>a. {x\<in>space M. a < f x} \<in> sets M"
  hence **: "\<forall>a. {x\<in>space M. f x < a} \<in> sets M"
    unfolding less_eq_le_pinfreal_measurable
    unfolding greater_eq_le_measurable .

  show "f \<in> borel_measurable M" unfolding borel_measurable_pinfreal_eq_real borel_measurable_iff_greater
  proof safe
    have "f -` {\<omega>} \<inter> space M = space M - {x\<in>space M. f x < \<omega>}" by auto
    then show \<omega>: "f -` {\<omega>} \<inter> space M \<in> sets M" using ** by auto

    fix a
    have "{w \<in> space M. a < real (f w)} =
      (if 0 \<le> a then {w\<in>space M. Real a < f w} - (f -` {\<omega>} \<inter> space M) else space M)"
    proof (split split_if, safe del: notI)
      fix x assume "0 \<le> a"
      { assume "a < real (f x)" then show "Real a < f x" "x \<notin> f -` {\<omega>} \<inter> space M"
          using `0 \<le> a` by (cases "f x", auto) }
      { assume "Real a < f x" "x \<notin> f -` {\<omega>}" then show "a < real (f x)"
          using `0 \<le> a` by (cases "f x", auto) }
    next
      fix x assume "\<not> 0 \<le> a" then show "a < real (f x)" by (cases "f x") auto
    qed
    then show "{w \<in> space M. a < real (f w)} \<in> sets M"
      using \<omega> * by (auto intro!: Diff)
  qed
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_iff_less:
  "(f::'a \<Rightarrow> pinfreal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. {x\<in>space M. f x < a} \<in> sets M)"
  using borel_measurable_pinfreal_iff_greater unfolding less_eq_le_pinfreal_measurable greater_eq_le_measurable .

lemma (in sigma_algebra) borel_measurable_pinfreal_iff_le:
  "(f::'a \<Rightarrow> pinfreal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. {x\<in>space M. f x \<le> a} \<in> sets M)"
  using borel_measurable_pinfreal_iff_greater unfolding less_eq_ge_measurable .

lemma (in sigma_algebra) borel_measurable_pinfreal_iff_ge:
  "(f::'a \<Rightarrow> pinfreal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. {x\<in>space M. a \<le> f x} \<in> sets M)"
  using borel_measurable_pinfreal_iff_greater unfolding less_eq_le_pinfreal_measurable .

lemma (in sigma_algebra) borel_measurable_pinfreal_eq_const:
  fixes f :: "'a \<Rightarrow> pinfreal" assumes "f \<in> borel_measurable M"
  shows "{x\<in>space M. f x = c} \<in> sets M"
proof -
  have "{x\<in>space M. f x = c} = (f -` {c} \<inter> space M)" by auto
  then show ?thesis using assms by (auto intro!: measurable_sets)
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_neq_const:
  fixes f :: "'a \<Rightarrow> pinfreal"
  assumes "f \<in> borel_measurable M"
  shows "{x\<in>space M. f x \<noteq> c} \<in> sets M"
proof -
  have "{x\<in>space M. f x \<noteq> c} = space M - (f -` {c} \<inter> space M)" by auto
  then show ?thesis using assms by (auto intro!: measurable_sets)
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_less[intro,simp]:
  fixes f g :: "'a \<Rightarrow> pinfreal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x < g x} \<in> sets M"
proof -
  have "(\<lambda>x. real (f x)) \<in> borel_measurable M"
    "(\<lambda>x. real (g x)) \<in> borel_measurable M"
    using assms by (auto intro!: borel_measurable_real)
  from borel_measurable_less[OF this]
  have "{x \<in> space M. real (f x) < real (g x)} \<in> sets M" .
  moreover have "{x \<in> space M. f x \<noteq> \<omega>} \<in> sets M" using f by (rule borel_measurable_pinfreal_neq_const)
  moreover have "{x \<in> space M. g x = \<omega>} \<in> sets M" using g by (rule borel_measurable_pinfreal_eq_const)
  moreover have "{x \<in> space M. g x \<noteq> \<omega>} \<in> sets M" using g by (rule borel_measurable_pinfreal_neq_const)
  moreover have "{x \<in> space M. f x < g x} = ({x \<in> space M. g x = \<omega>} \<inter> {x \<in> space M. f x \<noteq> \<omega>}) \<union>
    ({x \<in> space M. g x \<noteq> \<omega>} \<inter> {x \<in> space M. f x \<noteq> \<omega>} \<inter> {x \<in> space M. real (f x) < real (g x)})"
    by (auto simp: real_of_pinfreal_strict_mono_iff)
  ultimately show ?thesis by auto
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_le[intro,simp]:
  fixes f :: "'a \<Rightarrow> pinfreal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x \<le> g x} \<in> sets M"
proof -
  have "{x \<in> space M. f x \<le> g x} = space M - {x \<in> space M. g x < f x}" by auto
  then show ?thesis using g f by auto
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_eq[intro,simp]:
  fixes f :: "'a \<Rightarrow> pinfreal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w = g w} \<in> sets M"
proof -
  have "{x \<in> space M. f x = g x} = {x \<in> space M. g x \<le> f x} \<inter> {x \<in> space M. f x \<le> g x}" by auto
  then show ?thesis using g f by auto
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_neq[intro,simp]:
  fixes f :: "'a \<Rightarrow> pinfreal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w \<noteq> g w} = space M - {w \<in> space M. f w = g w}" by auto
  thus ?thesis using f g by auto
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_add[intro, simp]:
  fixes f :: "'a \<Rightarrow> pinfreal"
  assumes measure: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
proof -
  have *: "(\<lambda>x. f x + g x) =
     (\<lambda>x. if f x = \<omega> then \<omega> else if g x = \<omega> then \<omega> else Real (real (f x) + real (g x)))"
     by (auto simp: expand_fun_eq pinfreal_noteq_omega_Ex)
  show ?thesis using assms unfolding *
    by (auto intro!: measurable_If)
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_times[intro, simp]:
  fixes f :: "'a \<Rightarrow> pinfreal" assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
proof -
  have *: "(\<lambda>x. f x * g x) =
     (\<lambda>x. if f x = 0 then 0 else if g x = 0 then 0 else if f x = \<omega> then \<omega> else if g x = \<omega> then \<omega> else
      Real (real (f x) * real (g x)))"
     by (auto simp: expand_fun_eq pinfreal_noteq_omega_Ex)
  show ?thesis using assms unfolding *
    by (auto intro!: measurable_If)
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_setsum[simp, intro]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> pinfreal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms
    by induct auto
qed (simp add: borel_measurable_const)

lemma (in sigma_algebra) borel_measurable_pinfreal_min[intro, simp]:
  fixes f g :: "'a \<Rightarrow> pinfreal"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
  using assms unfolding min_def by (auto intro!: measurable_If)

lemma (in sigma_algebra) borel_measurable_pinfreal_max[intro]:
  fixes f g :: "'a \<Rightarrow> pinfreal"
  assumes "f \<in> borel_measurable M"
  and "g \<in> borel_measurable M"
  shows "(\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  using assms unfolding max_def by (auto intro!: measurable_If)

lemma (in sigma_algebra) borel_measurable_SUP[simp, intro]:
  fixes f :: "'d\<Colon>countable \<Rightarrow> 'a \<Rightarrow> pinfreal"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(SUP i : A. f i) \<in> borel_measurable M" (is "?sup \<in> borel_measurable M")
  unfolding borel_measurable_pinfreal_iff_greater
proof safe
  fix a
  have "{x\<in>space M. a < ?sup x} = (\<Union>i\<in>A. {x\<in>space M. a < f i x})"
    by (auto simp: less_Sup_iff SUPR_def[where 'a=pinfreal] SUPR_fun_expand[where 'b=pinfreal])
  then show "{x\<in>space M. a < ?sup x} \<in> sets M"
    using assms by auto
qed

lemma (in sigma_algebra) borel_measurable_INF[simp, intro]:
  fixes f :: "'d :: countable \<Rightarrow> 'a \<Rightarrow> pinfreal"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(INF i : A. f i) \<in> borel_measurable M" (is "?inf \<in> borel_measurable M")
  unfolding borel_measurable_pinfreal_iff_less
proof safe
  fix a
  have "{x\<in>space M. ?inf x < a} = (\<Union>i\<in>A. {x\<in>space M. f i x < a})"
    by (auto simp: Inf_less_iff INFI_def[where 'a=pinfreal] INFI_fun_expand)
  then show "{x\<in>space M. ?inf x < a} \<in> sets M"
    using assms by auto
qed

lemma (in sigma_algebra) borel_measurable_pinfreal_diff:
  fixes f g :: "'a \<Rightarrow> pinfreal"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
  unfolding borel_measurable_pinfreal_iff_greater
proof safe
  fix a
  have "{x \<in> space M. a < f x - g x} = {x \<in> space M. g x + a < f x}"
    by (simp add: pinfreal_less_minus_iff)
  then show "{x \<in> space M. a < f x - g x} \<in> sets M"
    using assms by auto
qed

end
