theory Probability_Space
imports Lebesgue_Integration Radon_Nikodym
begin

lemma (in measure_space) measure_inter_full_set:
  assumes "S \<in> sets M" "T \<in> sets M" and not_\<omega>: "\<mu> (T - S) \<noteq> \<omega>"
  assumes T: "\<mu> T = \<mu> (space M)"
  shows "\<mu> (S \<inter> T) = \<mu> S"
proof (rule antisym)
  show " \<mu> (S \<inter> T) \<le> \<mu> S"
    using assms by (auto intro!: measure_mono)

  show "\<mu> S \<le> \<mu> (S \<inter> T)"
  proof (rule ccontr)
    assume contr: "\<not> ?thesis"
    have "\<mu> (space M) = \<mu> ((T - S) \<union> (S \<inter> T))"
      unfolding T[symmetric] by (auto intro!: arg_cong[where f="\<mu>"])
    also have "\<dots> \<le> \<mu> (T - S) + \<mu> (S \<inter> T)"
      using assms by (auto intro!: measure_subadditive)
    also have "\<dots> < \<mu> (T - S) + \<mu> S"
      by (rule pinfreal_less_add[OF not_\<omega>]) (insert contr, auto)
    also have "\<dots> = \<mu> (T \<union> S)"
      using assms by (subst measure_additive) auto
    also have "\<dots> \<le> \<mu> (space M)"
      using assms sets_into_space by (auto intro!: measure_mono)
    finally show False ..
  qed
qed

lemma (in finite_measure) finite_measure_inter_full_set:
  assumes "S \<in> sets M" "T \<in> sets M"
  assumes T: "\<mu> T = \<mu> (space M)"
  shows "\<mu> (S \<inter> T) = \<mu> S"
  using measure_inter_full_set[OF assms(1,2) finite_measure assms(3)] assms
  by auto

locale prob_space = measure_space +
  assumes measure_space_1: "\<mu> (space M) = 1"

sublocale prob_space < finite_measure
proof
  from measure_space_1 show "\<mu> (space M) \<noteq> \<omega>" by simp
qed

context prob_space
begin

abbreviation "events \<equiv> sets M"
abbreviation "prob \<equiv> \<lambda>A. real (\<mu> A)"
abbreviation "prob_preserving \<equiv> measure_preserving"
abbreviation "random_variable \<equiv> \<lambda> s X. X \<in> measurable M s"
abbreviation "expectation \<equiv> integral"

definition
  "indep A B \<longleftrightarrow> A \<in> events \<and> B \<in> events \<and> prob (A \<inter> B) = prob A * prob B"

definition
  "indep_families F G \<longleftrightarrow> (\<forall> A \<in> F. \<forall> B \<in> G. indep A B)"

definition
  "distribution X = (\<lambda>s. \<mu> ((X -` s) \<inter> (space M)))"

abbreviation
  "joint_distribution X Y \<equiv> distribution (\<lambda>x. (X x, Y x))"

lemma prob_space: "prob (space M) = 1"
  unfolding measure_space_1 by simp

lemma measure_le_1[simp, intro]:
  assumes "A \<in> events" shows "\<mu> A \<le> 1"
proof -
  have "\<mu> A \<le> \<mu> (space M)"
    using assms sets_into_space by(auto intro!: measure_mono)
  also note measure_space_1
  finally show ?thesis .
qed

lemma measure_finite[simp, intro]:
  assumes "A \<in> events" shows "\<mu> A \<noteq> \<omega>"
  using measure_le_1[OF assms] by auto

lemma prob_compl:
  assumes "A \<in> events"
  shows "prob (space M - A) = 1 - prob A"
  using `A \<in> events`[THEN sets_into_space] `A \<in> events` measure_space_1
  by (subst real_finite_measure_Diff) auto

lemma indep_space:
  assumes "s \<in> events"
  shows "indep (space M) s"
  using assms prob_space by (simp add: indep_def)

lemma prob_space_increasing: "increasing M prob"
  by (auto intro!: real_measure_mono simp: increasing_def)

lemma prob_zero_union:
  assumes "s \<in> events" "t \<in> events" "prob t = 0"
  shows "prob (s \<union> t) = prob s"
using assms
proof -
  have "prob (s \<union> t) \<le> prob s"
    using real_finite_measure_subadditive[of s t] assms by auto
  moreover have "prob (s \<union> t) \<ge> prob s"
    using assms by (blast intro: real_measure_mono)
  ultimately show ?thesis by simp
qed

lemma prob_eq_compl:
  assumes "s \<in> events" "t \<in> events"
  assumes "prob (space M - s) = prob (space M - t)"
  shows "prob s = prob t"
  using assms prob_compl by auto

lemma prob_one_inter:
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

lemma prob_eq_bigunion_image:
  assumes "range f \<subseteq> events" "range g \<subseteq> events"
  assumes "disjoint_family f" "disjoint_family g"
  assumes "\<And> n :: nat. prob (f n) = prob (g n)"
  shows "(prob (\<Union> i. f i) = prob (\<Union> i. g i))"
using assms
proof -
  have a: "(\<lambda> i. prob (f i)) sums (prob (\<Union> i. f i))"
    by (rule real_finite_measure_UNION[OF assms(1,3)])
  have b: "(\<lambda> i. prob (g i)) sums (prob (\<Union> i. g i))"
    by (rule real_finite_measure_UNION[OF assms(2,4)])
  show ?thesis using sums_unique[OF b] sums_unique[OF a] assms by simp
qed

lemma prob_countably_zero:
  assumes "range c \<subseteq> events"
  assumes "\<And> i. prob (c i) = 0"
  shows "prob (\<Union> i :: nat. c i) = 0"
proof (rule antisym)
  show "prob (\<Union> i :: nat. c i) \<le> 0"
    using real_finite_measurable_countably_subadditive[OF assms(1)]
    by (simp add: assms(2) suminf_zero summable_zero)
  show "0 \<le> prob (\<Union> i :: nat. c i)" by (rule real_pinfreal_nonneg)
qed

lemma indep_sym:
   "indep a b \<Longrightarrow> indep b a"
unfolding indep_def using Int_commute[of a b] by auto

lemma indep_refl:
  assumes "a \<in> events"
  shows "indep a a = (prob a = 0) \<or> (prob a = 1)"
using assms unfolding indep_def by auto

lemma prob_equiprobable_finite_unions:
  assumes "s \<in> events"
  assumes s_finite: "finite s" "\<And>x. x \<in> s \<Longrightarrow> {x} \<in> events"
  assumes "\<And> x y. \<lbrakk>x \<in> s; y \<in> s\<rbrakk> \<Longrightarrow> (prob {x} = prob {y})"
  shows "prob s = real (card s) * prob {SOME x. x \<in> s}"
proof (cases "s = {}")
  case False hence "\<exists> x. x \<in> s" by blast
  from someI_ex[OF this] assms
  have prob_some: "\<And> x. x \<in> s \<Longrightarrow> prob {x} = prob {SOME y. y \<in> s}" by blast
  have "prob s = (\<Sum> x \<in> s. prob {x})"
    using real_finite_measure_finite_singelton[OF s_finite] by simp
  also have "\<dots> = (\<Sum> x \<in> s. prob {SOME y. y \<in> s})" using prob_some by auto
  also have "\<dots> = real (card s) * prob {(SOME x. x \<in> s)}"
    using setsum_constant assms by (simp add: real_eq_of_nat)
  finally show ?thesis by simp
qed simp

lemma prob_real_sum_image_fn:
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
  proof (rule real_finite_measure_finite_Union)
    show "finite s" by fact
    show "\<And>i. i \<in> s \<Longrightarrow> e \<inter> f i \<in> events" by fact
    show "disjoint_family_on (\<lambda>i. e \<inter> f i) s"
      using disjoint by (auto simp: disjoint_family_on_def)
  qed
  finally show ?thesis .
qed

lemma distribution_prob_space:
  assumes S: "sigma_algebra S" "random_variable S X"
  shows "prob_space S (distribution X)"
proof -
  interpret S: measure_space S "distribution X"
    using measure_space_vimage[OF S(2,1)] unfolding distribution_def .
  show ?thesis
  proof
    have "X -` space S \<inter> space M = space M"
      using `random_variable S X` by (auto simp: measurable_def)
    then show "distribution X (space S) = 1"
      using measure_space_1 by (simp add: distribution_def)
  qed
qed

lemma distribution_lebesgue_thm1:
  assumes "random_variable s X"
  assumes "A \<in> sets s"
  shows "real (distribution X A) = expectation (indicator (X -` A \<inter> space M))"
unfolding distribution_def
using assms unfolding measurable_def
using integral_indicator by auto

lemma distribution_lebesgue_thm2:
  assumes "sigma_algebra S" "random_variable S X" and "A \<in> sets S"
  shows "distribution X A =
    measure_space.positive_integral S (distribution X) (indicator A)"
  (is "_ = measure_space.positive_integral _ ?D _")
proof -
  interpret S: prob_space S "distribution X" using assms(1,2) by (rule distribution_prob_space)

  show ?thesis
    using S.positive_integral_indicator(1)
    using assms unfolding distribution_def by auto
qed

lemma finite_expectation1:
  assumes "finite (X`space M)" and rv: "random_variable borel_space X"
  shows "expectation X = (\<Sum> r \<in> X ` space M. r * prob (X -` {r} \<inter> space M))"
proof (rule integral_on_finite(2)[OF assms(2,1)])
  fix x have "X -` {x} \<inter> space M \<in> sets M"
    using rv unfolding measurable_def by auto
  thus "\<mu> (X -` {x} \<inter> space M) \<noteq> \<omega>" using finite_measure by simp
qed

lemma finite_expectation:
  assumes "finite (space M)" "random_variable borel_space X"
  shows "expectation X = (\<Sum> r \<in> X ` (space M). r * real (distribution X {r}))"
  using assms unfolding distribution_def using finite_expectation1 by auto

lemma prob_x_eq_1_imp_prob_y_eq_0:
  assumes "{x} \<in> events"
  assumes "prob {x} = 1"
  assumes "{y} \<in> events"
  assumes "y \<noteq> x"
  shows "prob {y} = 0"
  using prob_one_inter[of "{y}" "{x}"] assms by auto

lemma distribution_empty[simp]: "distribution X {} = 0"
  unfolding distribution_def by simp

lemma distribution_space[simp]: "distribution X (X ` space M) = 1"
proof -
  have "X -` X ` space M \<inter> space M = space M" by auto
  thus ?thesis unfolding distribution_def by (simp add: measure_space_1)
qed

lemma distribution_one:
  assumes "random_variable M X" and "A \<in> events"
  shows "distribution X A \<le> 1"
proof -
  have "distribution X A \<le> \<mu> (space M)" unfolding distribution_def
    using assms[unfolded measurable_def] by (auto intro!: measure_mono)
  thus ?thesis by (simp add: measure_space_1)
qed

lemma distribution_finite:
  assumes "random_variable M X" and "A \<in> events"
  shows "distribution X A \<noteq> \<omega>"
  using distribution_one[OF assms] by auto

lemma distribution_x_eq_1_imp_distribution_y_eq_0:
  assumes X: "random_variable \<lparr>space = X ` (space M), sets = Pow (X ` (space M))\<rparr> X"
    (is "random_variable ?S X")
  assumes "distribution X {x} = 1"
  assumes "y \<noteq> x"
  shows "distribution X {y} = 0"
proof -
  have "sigma_algebra ?S" by (rule sigma_algebra_Pow)
  from distribution_prob_space[OF this X]
  interpret S: prob_space ?S "distribution X" by simp

  have x: "{x} \<in> sets ?S"
  proof (rule ccontr)
    assume "{x} \<notin> sets ?S"
    hence "X -` {x} \<inter> space M = {}" by auto
    thus "False" using assms unfolding distribution_def by auto
  qed

  have [simp]: "{y} \<inter> {x} = {}" "{x} - {y} = {x}" using `y \<noteq> x` by auto

  show ?thesis
  proof cases
    assume "{y} \<in> sets ?S"
    with `{x} \<in> sets ?S` assms show "distribution X {y} = 0"
      using S.measure_inter_full_set[of "{y}" "{x}"]
      by simp
  next
    assume "{y} \<notin> sets ?S"
    hence "X -` {y} \<inter> space M = {}" by auto
    thus "distribution X {y} = 0" unfolding distribution_def by auto
  qed
qed

end

locale finite_prob_space = prob_space + finite_measure_space

lemma finite_prob_space_eq:
  "finite_prob_space M \<mu> \<longleftrightarrow> finite_measure_space M \<mu> \<and> \<mu> (space M) = 1"
  unfolding finite_prob_space_def finite_measure_space_def prob_space_def prob_space_axioms_def
  by auto

lemma (in prob_space) not_empty: "space M \<noteq> {}"
  using prob_space empty_measure by auto

lemma (in finite_prob_space) sum_over_space_eq_1: "(\<Sum>x\<in>space M. \<mu> {x}) = 1"
  using measure_space_1 sum_over_space by simp

lemma (in finite_prob_space) positive_distribution: "0 \<le> distribution X x"
  unfolding distribution_def by simp

lemma (in finite_prob_space) joint_distribution_restriction_fst:
  "joint_distribution X Y A \<le> distribution X (fst ` A)"
  unfolding distribution_def
proof (safe intro!: measure_mono)
  fix x assume "x \<in> space M" and *: "(X x, Y x) \<in> A"
  show "x \<in> X -` fst ` A"
    by (auto intro!: image_eqI[OF _ *])
qed (simp_all add: sets_eq_Pow)

lemma (in finite_prob_space) joint_distribution_restriction_snd:
  "joint_distribution X Y A \<le> distribution Y (snd ` A)"
  unfolding distribution_def
proof (safe intro!: measure_mono)
  fix x assume "x \<in> space M" and *: "(X x, Y x) \<in> A"
  show "x \<in> Y -` snd ` A"
    by (auto intro!: image_eqI[OF _ *])
qed (simp_all add: sets_eq_Pow)

lemma (in finite_prob_space) distribution_order:
  shows "0 \<le> distribution X x'"
  and "(distribution X x' \<noteq> 0) \<longleftrightarrow> (0 < distribution X x')"
  and "r \<le> joint_distribution X Y {(x, y)} \<Longrightarrow> r \<le> distribution X {x}"
  and "r \<le> joint_distribution X Y {(x, y)} \<Longrightarrow> r \<le> distribution Y {y}"
  and "r < joint_distribution X Y {(x, y)} \<Longrightarrow> r < distribution X {x}"
  and "r < joint_distribution X Y {(x, y)} \<Longrightarrow> r < distribution Y {y}"
  and "distribution X {x} = 0 \<Longrightarrow> joint_distribution X Y {(x, y)} = 0"
  and "distribution Y {y} = 0 \<Longrightarrow> joint_distribution X Y {(x, y)} = 0"
  using positive_distribution[of X x']
    positive_distribution[of "\<lambda>x. (X x, Y x)" "{(x, y)}"]
    joint_distribution_restriction_fst[of X Y "{(x, y)}"]
    joint_distribution_restriction_snd[of X Y "{(x, y)}"]
  by auto

lemma (in finite_prob_space) finite_product_measure_space:
  assumes "finite s1" "finite s2"
  shows "finite_measure_space \<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2)\<rparr> (joint_distribution X Y)"
    (is "finite_measure_space ?M ?D")
proof (rule finite_Pow_additivity_sufficient)
  show "positive ?D"
    unfolding positive_def using assms sets_eq_Pow
    by (simp add: distribution_def)

  show "additive ?M ?D" unfolding additive_def
  proof safe
    fix x y
    have A: "((\<lambda>x. (X x, Y x)) -` x) \<inter> space M \<in> sets M" using assms sets_eq_Pow by auto
    have B: "((\<lambda>x. (X x, Y x)) -` y) \<inter> space M \<in> sets M" using assms sets_eq_Pow by auto
    assume "x \<inter> y = {}"
    hence "(\<lambda>x. (X x, Y x)) -` x \<inter> space M \<inter> ((\<lambda>x. (X x, Y x)) -` y \<inter> space M) = {}"
      by auto
    from additive[unfolded additive_def, rule_format, OF A B] this
      finite_measure[OF A] finite_measure[OF B]
    show "?D (x \<union> y) = ?D x + ?D y"
      apply (simp add: distribution_def)
      apply (subst Int_Un_distrib2)
      by (auto simp: real_of_pinfreal_add)
  qed

  show "finite (space ?M)"
    using assms by auto

  show "sets ?M = Pow (space ?M)"
    by simp

  { fix x assume "x \<in> space ?M" thus "?D {x} \<noteq> \<omega>"
    unfolding distribution_def by (auto intro!: finite_measure simp: sets_eq_Pow) }
qed

lemma (in finite_prob_space) finite_product_measure_space_of_images:
  shows "finite_measure_space \<lparr> space = X ` space M \<times> Y ` space M,
                                sets = Pow (X ` space M \<times> Y ` space M) \<rparr>
                              (joint_distribution X Y)"
  using finite_space by (auto intro!: finite_product_measure_space)

lemma (in finite_prob_space) finite_measure_space:
  shows "finite_measure_space \<lparr>space = X ` space M, sets = Pow (X ` space M)\<rparr> (distribution X)"
    (is "finite_measure_space ?S _")
proof (rule finite_Pow_additivity_sufficient, simp_all)
  show "finite (X ` space M)" using finite_space by simp

  show "positive (distribution X)"
    unfolding distribution_def positive_def using sets_eq_Pow by auto

  show "additive ?S (distribution X)" unfolding additive_def distribution_def
  proof (simp, safe)
    fix x y
    have x: "(X -` x) \<inter> space M \<in> sets M"
      and y: "(X -` y) \<inter> space M \<in> sets M" using sets_eq_Pow by auto
    assume "x \<inter> y = {}"
    hence "X -` x \<inter> space M \<inter> (X -` y \<inter> space M) = {}" by auto
    from additive[unfolded additive_def, rule_format, OF x y] this
      finite_measure[OF x] finite_measure[OF y]
    have "\<mu> (((X -` x) \<union> (X -` y)) \<inter> space M) =
      \<mu> ((X -` x) \<inter> space M) + \<mu> ((X -` y) \<inter> space M)"
      by (subst Int_Un_distrib2) auto
    thus "\<mu> ((X -` x \<union> X -` y) \<inter> space M) = \<mu> (X -` x \<inter> space M) + \<mu> (X -` y \<inter> space M)"
      by auto
  qed

  { fix x assume "x \<in> X ` space M" thus "distribution X {x} \<noteq> \<omega>"
    unfolding distribution_def by (auto intro!: finite_measure simp: sets_eq_Pow) }
qed

lemma (in finite_prob_space) finite_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M, sets = Pow (X ` space M)\<rparr> (distribution X)"
  by (simp add: finite_prob_space_eq finite_measure_space)

lemma (in finite_prob_space) finite_product_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M \<times> Y ` space M, sets = Pow (X ` space M \<times> Y ` space M)\<rparr>
                     (joint_distribution X Y)"
  (is "finite_prob_space ?S _")
proof (simp add: finite_prob_space_eq finite_product_measure_space_of_images)
  have "X -` X ` space M \<inter> Y -` Y ` space M \<inter> space M = space M" by auto
  thus "joint_distribution X Y (X ` space M \<times> Y ` space M) = 1"
    by (simp add: distribution_def prob_space vimage_Times comp_def measure_space_1)
qed

lemma (in prob_space) prob_space_subalgebra:
  assumes "N \<subseteq> sets M" "sigma_algebra (M\<lparr> sets := N \<rparr>)"
  shows "prob_space (M\<lparr> sets := N \<rparr>) \<mu>" sorry

lemma (in measure_space) measure_space_subalgebra:
  assumes "N \<subseteq> sets M" "sigma_algebra (M\<lparr> sets := N \<rparr>)"
  shows "measure_space (M\<lparr> sets := N \<rparr>) \<mu>" sorry

lemma pinfreal_0_less_mult_iff[simp]:
  fixes x y :: pinfreal shows "0 < x * y \<longleftrightarrow> 0 < x \<and> 0 < y"
  by (cases x, cases y) (auto simp: zero_less_mult_iff)

lemma (in sigma_algebra) simple_function_subalgebra:
  assumes "sigma_algebra.simple_function (M\<lparr>sets:=N\<rparr>) f"
  and N_subalgebra: "N \<subseteq> sets M" "sigma_algebra (M\<lparr>sets:=N\<rparr>)"
  shows "simple_function f"
  using assms
  unfolding simple_function_def
  unfolding sigma_algebra.simple_function_def[OF N_subalgebra(2)]
  by auto

lemma (in measure_space) simple_integral_subalgebra[simp]:
  assumes "measure_space (M\<lparr>sets := N\<rparr>) \<mu>"
  shows "measure_space.simple_integral (M\<lparr>sets := N\<rparr>) \<mu> = simple_integral"
  unfolding simple_integral_def_raw
  unfolding measure_space.simple_integral_def_raw[OF assms] by simp

lemma (in sigma_algebra) borel_measurable_subalgebra:
  assumes "N \<subseteq> sets M" "f \<in> borel_measurable (M\<lparr>sets:=N\<rparr>)"
  shows "f \<in> borel_measurable M"
  using assms unfolding measurable_def by auto

lemma (in measure_space) positive_integral_subalgebra[simp]:
  assumes borel: "f \<in> borel_measurable (M\<lparr>sets := N\<rparr>)"
  and N_subalgebra: "N \<subseteq> sets M" "sigma_algebra (M\<lparr>sets := N\<rparr>)"
  shows "measure_space.positive_integral (M\<lparr>sets := N\<rparr>) \<mu> f = positive_integral f"
proof -
  note msN = measure_space_subalgebra[OF N_subalgebra]
  then interpret N: measure_space "M\<lparr>sets:=N\<rparr>" \<mu> .

  from N.borel_measurable_implies_simple_function_sequence[OF borel]
  obtain fs where Nsf: "\<And>i. N.simple_function (fs i)" and "fs \<up> f" by blast
  then have sf: "\<And>i. simple_function (fs i)"
    using simple_function_subalgebra[OF _ N_subalgebra] by blast

  from positive_integral_isoton_simple[OF `fs \<up> f` sf] N.positive_integral_isoton_simple[OF `fs \<up> f` Nsf]
  show ?thesis unfolding simple_integral_subalgebra[OF msN] isoton_def by simp
qed

section "Conditional Expectation and Probability"

lemma (in prob_space) conditional_expectation_exists:
  fixes X :: "'a \<Rightarrow> pinfreal"
  assumes borel: "X \<in> borel_measurable M"
  and N_subalgebra: "N \<subseteq> sets M" "sigma_algebra (M\<lparr> sets := N \<rparr>)"
  shows "\<exists>Y\<in>borel_measurable (M\<lparr> sets := N \<rparr>). \<forall>C\<in>N.
      positive_integral (\<lambda>x. Y x * indicator C x) = positive_integral (\<lambda>x. X x * indicator C x)"
proof -
  interpret P: prob_space "M\<lparr> sets := N \<rparr>" \<mu>
    using prob_space_subalgebra[OF N_subalgebra] .

  let "?f A" = "\<lambda>x. X x * indicator A x"
  let "?Q A" = "positive_integral (?f A)"

  from measure_space_density[OF borel]
  have Q: "measure_space (M\<lparr> sets := N \<rparr>) ?Q"
    by (rule measure_space.measure_space_subalgebra[OF _ N_subalgebra])
  then interpret Q: measure_space "M\<lparr> sets := N \<rparr>" ?Q .

  have "P.absolutely_continuous ?Q"
    unfolding P.absolutely_continuous_def
  proof (safe, simp)
    fix A assume "A \<in> N" "\<mu> A = 0"
    moreover then have f_borel: "?f A \<in> borel_measurable M"
      using borel N_subalgebra by (auto intro: borel_measurable_indicator)
    moreover have "{x\<in>space M. ?f A x \<noteq> 0} = (?f A -` {0<..} \<inter> space M) \<inter> A"
      by (auto simp: indicator_def)
    moreover have "\<mu> \<dots> \<le> \<mu> A"
      using `A \<in> N` N_subalgebra f_borel
      by (auto intro!: measure_mono Int[of _ A] measurable_sets)
    ultimately show "?Q A = 0"
      by (simp add: positive_integral_0_iff)
  qed
  from P.Radon_Nikodym[OF Q this]
  obtain Y where Y: "Y \<in> borel_measurable (M\<lparr>sets := N\<rparr>)"
    "\<And>A. A \<in> sets (M\<lparr>sets:=N\<rparr>) \<Longrightarrow> ?Q A = P.positive_integral (\<lambda>x. Y x * indicator A x)"
    by blast
  with N_subalgebra show ?thesis
    by (auto intro!: bexI[OF _ Y(1)])
qed

definition (in prob_space)
  "conditional_expectation N X = (SOME Y. Y\<in>borel_measurable (M\<lparr>sets:=N\<rparr>)
    \<and> (\<forall>C\<in>N. positive_integral (\<lambda>x. Y x * indicator C x) = positive_integral (\<lambda>x. X x * indicator C x)))"

abbreviation (in prob_space)
  "conditional_probabiltiy N A \<equiv> conditional_expectation N (indicator A)"

lemma (in prob_space)
  fixes X :: "'a \<Rightarrow> pinfreal"
  assumes borel: "X \<in> borel_measurable M"
  and N_subalgebra: "N \<subseteq> sets M" "sigma_algebra (M\<lparr> sets := N \<rparr>)"
  shows borel_measurable_conditional_expectation:
    "conditional_expectation N X \<in> borel_measurable (M\<lparr> sets := N \<rparr>)"
  and conditional_expectation: "\<And>C. C \<in> N \<Longrightarrow>
      positive_integral (\<lambda>x. conditional_expectation N X x * indicator C x) =
      positive_integral (\<lambda>x. X x * indicator C x)"
   (is "\<And>C. C \<in> N \<Longrightarrow> ?eq C")
proof -
  note CE = conditional_expectation_exists[OF assms, unfolded Bex_def]
  then show "conditional_expectation N X \<in> borel_measurable (M\<lparr> sets := N \<rparr>)"
    unfolding conditional_expectation_def by (rule someI2_ex) blast

  from CE show "\<And>C. C\<in>N \<Longrightarrow> ?eq C"
    unfolding conditional_expectation_def by (rule someI2_ex) blast
qed

end
