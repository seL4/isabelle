(*  Title:      HOL/Probability/Probability_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Probability measure*}

theory Probability_Measure
imports Lebesgue_Integration Radon_Nikodym Finite_Product_Measure
begin

lemma real_of_extreal_inverse[simp]:
  fixes X :: extreal
  shows "real (inverse X) = 1 / real X"
  by (cases X) (auto simp: inverse_eq_divide)

lemma real_of_extreal_le_0[simp]: "real (X :: extreal) \<le> 0 \<longleftrightarrow> (X \<le> 0 \<or> X = \<infinity>)"
  by (cases X) auto

lemma abs_real_of_extreal[simp]: "\<bar>real (X :: extreal)\<bar> = real \<bar>X\<bar>"
  by (cases X) auto

lemma zero_less_real_of_extreal: "0 < real X \<longleftrightarrow> (0 < X \<and> X \<noteq> \<infinity>)"
  by (cases X) auto

lemma real_of_extreal_le_1: fixes X :: extreal shows "X \<le> 1 \<Longrightarrow> real X \<le> 1"
  by (cases X) (auto simp: one_extreal_def)

locale prob_space = measure_space +
  assumes measure_space_1: "measure M (space M) = 1"

sublocale prob_space < finite_measure
proof
  from measure_space_1 show "\<mu> (space M) \<noteq> \<infinity>" by simp
qed

abbreviation (in prob_space) "events \<equiv> sets M"
abbreviation (in prob_space) "prob \<equiv> \<mu>'"
abbreviation (in prob_space) "random_variable M' X \<equiv> sigma_algebra M' \<and> X \<in> measurable M M'"
abbreviation (in prob_space) "expectation \<equiv> integral\<^isup>L M"

definition (in prob_space)
  "indep A B \<longleftrightarrow> A \<in> events \<and> B \<in> events \<and> prob (A \<inter> B) = prob A * prob B"

definition (in prob_space)
  "indep_families F G \<longleftrightarrow> (\<forall> A \<in> F. \<forall> B \<in> G. indep A B)"

definition (in prob_space)
  "distribution X A = \<mu>' (X -` A \<inter> space M)"

abbreviation (in prob_space)
  "joint_distribution X Y \<equiv> distribution (\<lambda>x. (X x, Y x))"

declare (in finite_measure) positive_measure'[intro, simp]

lemma (in prob_space) distribution_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> X x = Y x"
  shows "distribution X = distribution Y"
  unfolding distribution_def fun_eq_iff
  using assms by (auto intro!: arg_cong[where f="\<mu>'"])

lemma (in prob_space) joint_distribution_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "joint_distribution X Y = joint_distribution X' Y'"
  unfolding distribution_def fun_eq_iff
  using assms by (auto intro!: arg_cong[where f="\<mu>'"])

lemma (in prob_space) distribution_id[simp]:
  "N \<in> events \<Longrightarrow> distribution (\<lambda>x. x) N = prob N"
  by (auto simp: distribution_def intro!: arg_cong[where f=prob])

lemma (in prob_space) prob_space: "prob (space M) = 1"
  using measure_space_1 unfolding \<mu>'_def by (simp add: one_extreal_def)

lemma (in prob_space) prob_le_1[simp, intro]: "prob A \<le> 1"
  using bounded_measure[of A] by (simp add: prob_space)

lemma (in prob_space) distribution_positive[simp, intro]:
  "0 \<le> distribution X A" unfolding distribution_def by auto

lemma (in prob_space) joint_distribution_remove[simp]:
    "joint_distribution X X {(x, x)} = distribution X {x}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

lemma (in prob_space) distribution_1:
  "distribution X A \<le> 1"
  unfolding distribution_def by simp

lemma (in prob_space) prob_compl:
  assumes A: "A \<in> events"
  shows "prob (space M - A) = 1 - prob A"
  using finite_measure_compl[OF A] by (simp add: prob_space)

lemma (in prob_space) indep_space: "s \<in> events \<Longrightarrow> indep (space M) s"
  by (simp add: indep_def prob_space)

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
    using finite_measure_countably_subadditive[OF assms(1)]
    by (simp add: assms(2) suminf_zero summable_zero)
qed simp

lemma (in prob_space) indep_sym:
   "indep a b \<Longrightarrow> indep b a"
unfolding indep_def using Int_commute[of a b] by auto

lemma (in prob_space) indep_refl:
  assumes "a \<in> events"
  shows "indep a a = (prob a = 0) \<or> (prob a = 1)"
using assms unfolding indep_def by auto

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
    using finite_measure_finite_singleton[OF s_finite] by simp
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
    show "\<And>i. i \<in> s \<Longrightarrow> e \<inter> f i \<in> events" by fact
    show "disjoint_family_on (\<lambda>i. e \<inter> f i) s"
      using disjoint by (auto simp: disjoint_family_on_def)
  qed
  finally show ?thesis .
qed

lemma (in prob_space) prob_space_vimage:
  assumes S: "sigma_algebra S"
  assumes T: "T \<in> measure_preserving M S"
  shows "prob_space S"
proof -
  interpret S: measure_space S
    using S and T by (rule measure_space_vimage)
  show ?thesis
  proof
    from T[THEN measure_preservingD2]
    have "T -` space S \<inter> space M = space M"
      by (auto simp: measurable_def)
    with T[THEN measure_preservingD, of "space S", symmetric]
    show  "measure S (space S) = 1"
      using measure_space_1 by simp
  qed
qed

lemma (in prob_space) distribution_prob_space:
  assumes X: "random_variable S X"
  shows "prob_space (S\<lparr>measure := extreal \<circ> distribution X\<rparr>)" (is "prob_space ?S")
proof (rule prob_space_vimage)
  show "X \<in> measure_preserving M ?S"
    using X
    unfolding measure_preserving_def distribution_def_raw
    by (auto simp: finite_measure_eq measurable_sets)
  show "sigma_algebra ?S" using X by simp
qed

lemma (in prob_space) AE_distribution:
  assumes X: "random_variable MX X" and "AE x in MX\<lparr>measure := extreal \<circ> distribution X\<rparr>. Q x"
  shows "AE x. Q (X x)"
proof -
  interpret X: prob_space "MX\<lparr>measure := extreal \<circ> distribution X\<rparr>" using X by (rule distribution_prob_space)
  obtain N where N: "N \<in> sets MX" "distribution X N = 0" "{x\<in>space MX. \<not> Q x} \<subseteq> N"
    using assms unfolding X.almost_everywhere_def by auto
  from X[unfolded measurable_def] N show "AE x. Q (X x)"
    by (intro AE_I'[where N="X -` N \<inter> space M"])
       (auto simp: finite_measure_eq distribution_def measurable_sets)
qed

lemma (in prob_space) distribution_eq_integral:
  "random_variable S X \<Longrightarrow> A \<in> sets S \<Longrightarrow> distribution X A = expectation (indicator (X -` A \<inter> space M))"
  using finite_measure_eq[of "X -` A \<inter> space M"]
  by (auto simp: measurable_sets distribution_def)

lemma (in prob_space) distribution_eq_translated_integral:
  assumes "random_variable S X" "A \<in> sets S"
  shows "distribution X A = integral\<^isup>P (S\<lparr>measure := extreal \<circ> distribution X\<rparr>) (indicator A)"
proof -
  interpret S: prob_space "S\<lparr>measure := extreal \<circ> distribution X\<rparr>"
    using assms(1) by (rule distribution_prob_space)
  show ?thesis
    using S.positive_integral_indicator(1)[of A] assms by simp
qed

lemma (in prob_space) finite_expectation1:
  assumes f: "finite (X`space M)" and rv: "random_variable borel X"
  shows "expectation X = (\<Sum>r \<in> X ` space M. r * prob (X -` {r} \<inter> space M))" (is "_ = ?r")
proof (subst integral_on_finite)
  show "X \<in> borel_measurable M" "finite (X`space M)" using assms by auto
  show "(\<Sum> r \<in> X ` space M. r * real (\<mu> (X -` {r} \<inter> space M))) = ?r"
    "\<And>x. \<mu> (X -` {x} \<inter> space M) \<noteq> \<infinity>"
    using finite_measure_eq[OF borel_measurable_vimage, of X] rv by auto
qed

lemma (in prob_space) finite_expectation:
  assumes "finite (X`space M)" "random_variable borel X"
  shows "expectation X = (\<Sum> r \<in> X ` (space M). r * distribution X {r})"
  using assms unfolding distribution_def using finite_expectation1 by auto

lemma (in prob_space) prob_x_eq_1_imp_prob_y_eq_0:
  assumes "{x} \<in> events"
  assumes "prob {x} = 1"
  assumes "{y} \<in> events"
  assumes "y \<noteq> x"
  shows "prob {y} = 0"
  using prob_one_inter[of "{y}" "{x}"] assms by auto

lemma (in prob_space) distribution_empty[simp]: "distribution X {} = 0"
  unfolding distribution_def by simp

lemma (in prob_space) distribution_space[simp]: "distribution X (X ` space M) = 1"
proof -
  have "X -` X ` space M \<inter> space M = space M" by auto
  thus ?thesis unfolding distribution_def by (simp add: prob_space)
qed

lemma (in prob_space) distribution_one:
  assumes "random_variable M' X" and "A \<in> sets M'"
  shows "distribution X A \<le> 1"
proof -
  have "distribution X A \<le> \<mu>' (space M)" unfolding distribution_def
    using assms[unfolded measurable_def] by (auto intro!: finite_measure_mono)
  thus ?thesis by (simp add: prob_space)
qed

lemma (in prob_space) distribution_x_eq_1_imp_distribution_y_eq_0:
  assumes X: "random_variable \<lparr>space = X ` (space M), sets = Pow (X ` (space M))\<rparr> X"
    (is "random_variable ?S X")
  assumes "distribution X {x} = 1"
  assumes "y \<noteq> x"
  shows "distribution X {y} = 0"
proof cases
  { fix x have "X -` {x} \<inter> space M \<in> sets M"
    proof cases
      assume "x \<in> X`space M" with X show ?thesis
        by (auto simp: measurable_def image_iff)
    next
      assume "x \<notin> X`space M" then have "X -` {x} \<inter> space M = {}" by auto
      then show ?thesis by auto
    qed } note single = this
  have "X -` {x} \<inter> space M - X -` {y} \<inter> space M = X -` {x} \<inter> space M"
    "X -` {y} \<inter> space M \<inter> (X -` {x} \<inter> space M) = {}"
    using `y \<noteq> x` by auto
  with finite_measure_inter_full_set[OF single single, of x y] assms(2)
  show ?thesis by (auto simp: distribution_def prob_space)
next
  assume "{y} \<notin> sets ?S"
  then have "X -` {y} \<inter> space M = {}" by auto
  thus "distribution X {y} = 0" unfolding distribution_def by auto
qed

lemma (in prob_space) joint_distribution_Times_le_fst:
  assumes X: "random_variable MX X" and Y: "random_variable MY Y"
    and A: "A \<in> sets MX" and B: "B \<in> sets MY"
  shows "joint_distribution X Y (A \<times> B) \<le> distribution X A"
  unfolding distribution_def
proof (intro finite_measure_mono)
  show "(\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M \<subseteq> X -` A \<inter> space M" by force
  show "X -` A \<inter> space M \<in> events"
    using X A unfolding measurable_def by simp
  have *: "(\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M =
    (X -` A \<inter> space M) \<inter> (Y -` B \<inter> space M)" by auto
qed

lemma (in prob_space) joint_distribution_commute:
  "joint_distribution X Y x = joint_distribution Y X ((\<lambda>(x,y). (y,x))`x)"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

lemma (in prob_space) joint_distribution_Times_le_snd:
  assumes X: "random_variable MX X" and Y: "random_variable MY Y"
    and A: "A \<in> sets MX" and B: "B \<in> sets MY"
  shows "joint_distribution X Y (A \<times> B) \<le> distribution Y B"
  using assms
  by (subst joint_distribution_commute)
     (simp add: swap_product joint_distribution_Times_le_fst)

lemma (in prob_space) random_variable_pairI:
  assumes "random_variable MX X"
  assumes "random_variable MY Y"
  shows "random_variable (MX \<Otimes>\<^isub>M MY) (\<lambda>x. (X x, Y x))"
proof
  interpret MX: sigma_algebra MX using assms by simp
  interpret MY: sigma_algebra MY using assms by simp
  interpret P: pair_sigma_algebra MX MY by default
  show "sigma_algebra (MX \<Otimes>\<^isub>M MY)" by default
  have sa: "sigma_algebra M" by default
  show "(\<lambda>x. (X x, Y x)) \<in> measurable M (MX \<Otimes>\<^isub>M MY)"
    unfolding P.measurable_pair_iff[OF sa] using assms by (simp add: comp_def)
qed

lemma (in prob_space) joint_distribution_commute_singleton:
  "joint_distribution X Y {(x, y)} = joint_distribution Y X {(y, x)}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

lemma (in prob_space) joint_distribution_assoc_singleton:
  "joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)} =
   joint_distribution (\<lambda>x. (X x, Y x)) Z {((x, y), z)}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

locale pair_prob_space = M1: prob_space M1 + M2: prob_space M2 for M1 M2

sublocale pair_prob_space \<subseteq> pair_sigma_finite M1 M2 by default

sublocale pair_prob_space \<subseteq> P: prob_space P
by default (simp add: pair_measure_times M1.measure_space_1 M2.measure_space_1 space_pair_measure)

lemma countably_additiveI[case_names countably]:
  assumes "\<And>A. \<lbrakk> range A \<subseteq> sets M ; disjoint_family A ; (\<Union>i. A i) \<in> sets M\<rbrakk> \<Longrightarrow>
    (\<Sum>n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
  shows "countably_additive M \<mu>"
  using assms unfolding countably_additive_def by auto

lemma (in prob_space) joint_distribution_prob_space:
  assumes "random_variable MX X" "random_variable MY Y"
  shows "prob_space ((MX \<Otimes>\<^isub>M MY) \<lparr> measure := extreal \<circ> joint_distribution X Y\<rparr>)"
  using random_variable_pairI[OF assms] by (rule distribution_prob_space)

section "Probability spaces on finite sets"

locale finite_prob_space = prob_space + finite_measure_space

abbreviation (in prob_space) "finite_random_variable M' X \<equiv> finite_sigma_algebra M' \<and> X \<in> measurable M M'"

lemma (in prob_space) finite_random_variableD:
  assumes "finite_random_variable M' X" shows "random_variable M' X"
proof -
  interpret M': finite_sigma_algebra M' using assms by simp
  then show "random_variable M' X" using assms by simp default
qed

lemma (in prob_space) distribution_finite_prob_space:
  assumes "finite_random_variable MX X"
  shows "finite_prob_space (MX\<lparr>measure := extreal \<circ> distribution X\<rparr>)"
proof -
  interpret X: prob_space "MX\<lparr>measure := extreal \<circ> distribution X\<rparr>"
    using assms[THEN finite_random_variableD] by (rule distribution_prob_space)
  interpret MX: finite_sigma_algebra MX
    using assms by auto
  show ?thesis by default (simp_all add: MX.finite_space)
qed

lemma (in prob_space) simple_function_imp_finite_random_variable[simp, intro]:
  assumes "simple_function M X"
  shows "finite_random_variable \<lparr> space = X`space M, sets = Pow (X`space M), \<dots> = x \<rparr> X"
    (is "finite_random_variable ?X _")
proof (intro conjI)
  have [simp]: "finite (X ` space M)" using assms unfolding simple_function_def by simp
  interpret X: sigma_algebra ?X by (rule sigma_algebra_Pow)
  show "finite_sigma_algebra ?X"
    by default auto
  show "X \<in> measurable M ?X"
  proof (unfold measurable_def, clarsimp)
    fix A assume A: "A \<subseteq> X`space M"
    then have "finite A" by (rule finite_subset) simp
    then have "X -` (\<Union>a\<in>A. {a}) \<inter> space M \<in> events"
      unfolding vimage_UN UN_extend_simps
      apply (rule finite_UN)
      using A assms unfolding simple_function_def by auto
    then show "X -` A \<inter> space M \<in> events" by simp
  qed
qed

lemma (in prob_space) simple_function_imp_random_variable[simp, intro]:
  assumes "simple_function M X"
  shows "random_variable \<lparr> space = X`space M, sets = Pow (X`space M), \<dots> = ext \<rparr> X"
  using simple_function_imp_finite_random_variable[OF assms, of ext]
  by (auto dest!: finite_random_variableD)

lemma (in prob_space) sum_over_space_real_distribution:
  "simple_function M X \<Longrightarrow> (\<Sum>x\<in>X`space M. distribution X {x}) = 1"
  unfolding distribution_def prob_space[symmetric]
  by (subst finite_measure_finite_Union[symmetric])
     (auto simp add: disjoint_family_on_def simple_function_def
           intro!: arg_cong[where f=prob])

lemma (in prob_space) finite_random_variable_pairI:
  assumes "finite_random_variable MX X"
  assumes "finite_random_variable MY Y"
  shows "finite_random_variable (MX \<Otimes>\<^isub>M MY) (\<lambda>x. (X x, Y x))"
proof
  interpret MX: finite_sigma_algebra MX using assms by simp
  interpret MY: finite_sigma_algebra MY using assms by simp
  interpret P: pair_finite_sigma_algebra MX MY by default
  show "finite_sigma_algebra (MX \<Otimes>\<^isub>M MY)" by default
  have sa: "sigma_algebra M" by default
  show "(\<lambda>x. (X x, Y x)) \<in> measurable M (MX \<Otimes>\<^isub>M MY)"
    unfolding P.measurable_pair_iff[OF sa] using assms by (simp add: comp_def)
qed

lemma (in prob_space) finite_random_variable_imp_sets:
  "finite_random_variable MX X \<Longrightarrow> x \<in> space MX \<Longrightarrow> {x} \<in> sets MX"
  unfolding finite_sigma_algebra_def finite_sigma_algebra_axioms_def by simp

lemma (in prob_space) finite_random_variable_measurable:
  assumes X: "finite_random_variable MX X" shows "X -` A \<inter> space M \<in> events"
proof -
  interpret X: finite_sigma_algebra MX using X by simp
  from X have vimage: "\<And>A. A \<subseteq> space MX \<Longrightarrow> X -` A \<inter> space M \<in> events" and
    "X \<in> space M \<rightarrow> space MX"
    by (auto simp: measurable_def)
  then have *: "X -` A \<inter> space M = X -` (A \<inter> space MX) \<inter> space M"
    by auto
  show "X -` A \<inter> space M \<in> events"
    unfolding * by (intro vimage) auto
qed

lemma (in prob_space) joint_distribution_finite_Times_le_fst:
  assumes X: "finite_random_variable MX X" and Y: "finite_random_variable MY Y"
  shows "joint_distribution X Y (A \<times> B) \<le> distribution X A"
  unfolding distribution_def
proof (intro finite_measure_mono)
  show "(\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M \<subseteq> X -` A \<inter> space M" by force
  show "X -` A \<inter> space M \<in> events"
    using finite_random_variable_measurable[OF X] .
  have *: "(\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M =
    (X -` A \<inter> space M) \<inter> (Y -` B \<inter> space M)" by auto
qed

lemma (in prob_space) joint_distribution_finite_Times_le_snd:
  assumes X: "finite_random_variable MX X" and Y: "finite_random_variable MY Y"
  shows "joint_distribution X Y (A \<times> B) \<le> distribution Y B"
  using assms
  by (subst joint_distribution_commute)
     (simp add: swap_product joint_distribution_finite_Times_le_fst)

lemma (in prob_space) finite_distribution_order:
  fixes MX :: "('c, 'd) measure_space_scheme" and MY :: "('e, 'f) measure_space_scheme"
  assumes "finite_random_variable MX X" "finite_random_variable MY Y"
  shows "r \<le> joint_distribution X Y {(x, y)} \<Longrightarrow> r \<le> distribution X {x}"
    and "r \<le> joint_distribution X Y {(x, y)} \<Longrightarrow> r \<le> distribution Y {y}"
    and "r < joint_distribution X Y {(x, y)} \<Longrightarrow> r < distribution X {x}"
    and "r < joint_distribution X Y {(x, y)} \<Longrightarrow> r < distribution Y {y}"
    and "distribution X {x} = 0 \<Longrightarrow> joint_distribution X Y {(x, y)} = 0"
    and "distribution Y {y} = 0 \<Longrightarrow> joint_distribution X Y {(x, y)} = 0"
  using joint_distribution_finite_Times_le_snd[OF assms, of "{x}" "{y}"]
  using joint_distribution_finite_Times_le_fst[OF assms, of "{x}" "{y}"]
  by (auto intro: antisym)

lemma (in prob_space) setsum_joint_distribution:
  assumes X: "finite_random_variable MX X"
  assumes Y: "random_variable MY Y" "B \<in> sets MY"
  shows "(\<Sum>a\<in>space MX. joint_distribution X Y ({a} \<times> B)) = distribution Y B"
  unfolding distribution_def
proof (subst finite_measure_finite_Union[symmetric])
  interpret MX: finite_sigma_algebra MX using X by auto
  show "finite (space MX)" using MX.finite_space .
  let "?d i" = "(\<lambda>x. (X x, Y x)) -` ({i} \<times> B) \<inter> space M"
  { fix i assume "i \<in> space MX"
    moreover have "?d i = (X -` {i} \<inter> space M) \<inter> (Y -` B \<inter> space M)" by auto
    ultimately show "?d i \<in> events"
      using measurable_sets[of X M MX] measurable_sets[of Y M MY B] X Y
      using MX.sets_eq_Pow by auto }
  show "disjoint_family_on ?d (space MX)" by (auto simp: disjoint_family_on_def)
  show "\<mu>' (\<Union>i\<in>space MX. ?d i) = \<mu>' (Y -` B \<inter> space M)"
    using X[unfolded measurable_def] by (auto intro!: arg_cong[where f=\<mu>'])
qed

lemma (in prob_space) setsum_joint_distribution_singleton:
  assumes X: "finite_random_variable MX X"
  assumes Y: "finite_random_variable MY Y" "b \<in> space MY"
  shows "(\<Sum>a\<in>space MX. joint_distribution X Y {(a, b)}) = distribution Y {b}"
  using setsum_joint_distribution[OF X
    finite_random_variableD[OF Y(1)]
    finite_random_variable_imp_sets[OF Y]] by simp

locale pair_finite_prob_space = M1: finite_prob_space M1 + M2: finite_prob_space M2 for M1 M2

sublocale pair_finite_prob_space \<subseteq> pair_prob_space M1 M2 by default
sublocale pair_finite_prob_space \<subseteq> pair_finite_space M1 M2  by default
sublocale pair_finite_prob_space \<subseteq> finite_prob_space P by default

locale product_finite_prob_space =
  fixes M :: "'i \<Rightarrow> ('a,'b) measure_space_scheme"
    and I :: "'i set"
  assumes finite_space: "\<And>i. finite_prob_space (M i)" and finite_index: "finite I"

sublocale product_finite_prob_space \<subseteq> M!: finite_prob_space "M i" using finite_space .
sublocale product_finite_prob_space \<subseteq> finite_product_sigma_finite M I by default (rule finite_index)
sublocale product_finite_prob_space \<subseteq> prob_space "Pi\<^isub>M I M"
proof
  show "\<mu> (space P) = 1"
    using measure_times[OF M.top] M.measure_space_1
    by (simp add: setprod_1 space_product_algebra)
qed

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
  using assms by induct (auto simp: extensional_funcset_insert_eq)

lemma finite_PiE[simp, intro]:
  assumes fin: "finite A" "\<And>i. i \<in> A \<Longrightarrow> finite (B i)"
  shows "finite (Pi\<^isub>E A B)"
proof -
  have *: "(Pi\<^isub>E A B) \<subseteq> extensional A \<inter> (A \<rightarrow> (\<Union>i\<in>A. B i))" by auto
  show ?thesis
    using fin by (intro finite_subset[OF *] finite_extensional_funcset) auto
qed

sublocale product_finite_prob_space \<subseteq> finite_prob_space "Pi\<^isub>M I M"
proof
  show "finite (space P)"
    using finite_index M.finite_space by auto

  { fix x assume "x \<in> space P"
    then have x: "{x} = (\<Pi>\<^isub>E i\<in>I. {x i})"
    proof safe
      fix y assume *: "y \<in> (\<Pi> i\<in>I. {x i})" "y \<in> extensional I"
      show "y = x"
      proof
        fix i show "y i = x i"
          using * `x \<in> space P` by (cases "i \<in> I") (auto simp: extensional_def)
      qed
    qed auto
    with `x \<in> space P` have "{x} \<in> sets P"
      by (auto intro!: in_P) }
  note x_in_P = this

  have "Pow (space P) \<subseteq> sets P"
  proof
    fix X assume "X \<in> Pow (space P)"
    moreover then have "finite X"
      using `finite (space P)` by (blast intro: finite_subset)
    ultimately have "(\<Union>x\<in>X. {x}) \<in> sets P"
      by (intro finite_UN x_in_P) auto
    then show "X \<in> sets P" by simp
  qed
  with space_closed show [simp]: "sets P = Pow (space P)" ..


  { fix x assume "x \<in> space P"
    from this top have "\<mu> {x} \<le> \<mu> (space P)" by (intro measure_mono) auto
    then show "\<mu> {x} \<noteq> \<infinity>"
      using measure_space_1 by auto }
qed

lemma (in product_finite_prob_space) measure_finite_times:
  "(\<And>i. i \<in> I \<Longrightarrow> X i \<subseteq> space (M i)) \<Longrightarrow> \<mu> (\<Pi>\<^isub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.\<mu> i (X i))"
  by (rule measure_times) simp

lemma (in product_finite_prob_space) prob_times:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<subseteq> space (M i)"
  shows "prob (\<Pi>\<^isub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.prob i (X i))"
proof -
  have "extreal (\<mu>' (\<Pi>\<^isub>E i\<in>I. X i)) = \<mu> (\<Pi>\<^isub>E i\<in>I. X i)"
    using X by (intro finite_measure_eq[symmetric] in_P) auto
  also have "\<dots> = (\<Prod>i\<in>I. M.\<mu> i (X i))"
    using measure_finite_times X by simp
  also have "\<dots> = extreal (\<Prod>i\<in>I. M.\<mu>' i (X i))"
    using X by (simp add: M.finite_measure_eq setprod_extreal)
  finally show ?thesis by simp
qed

lemma (in prob_space) joint_distribution_finite_prob_space:
  assumes X: "finite_random_variable MX X"
  assumes Y: "finite_random_variable MY Y"
  shows "finite_prob_space ((MX \<Otimes>\<^isub>M MY)\<lparr> measure := extreal \<circ> joint_distribution X Y\<rparr>)"
  by (intro distribution_finite_prob_space finite_random_variable_pairI X Y)

lemma finite_prob_space_eq:
  "finite_prob_space M \<longleftrightarrow> finite_measure_space M \<and> measure M (space M) = 1"
  unfolding finite_prob_space_def finite_measure_space_def prob_space_def prob_space_axioms_def
  by auto

lemma (in prob_space) not_empty: "space M \<noteq> {}"
  using prob_space empty_measure' by auto

lemma (in finite_prob_space) sum_over_space_eq_1: "(\<Sum>x\<in>space M. \<mu> {x}) = 1"
  using measure_space_1 sum_over_space by simp

lemma (in finite_prob_space) joint_distribution_restriction_fst:
  "joint_distribution X Y A \<le> distribution X (fst ` A)"
  unfolding distribution_def
proof (safe intro!: finite_measure_mono)
  fix x assume "x \<in> space M" and *: "(X x, Y x) \<in> A"
  show "x \<in> X -` fst ` A"
    by (auto intro!: image_eqI[OF _ *])
qed (simp_all add: sets_eq_Pow)

lemma (in finite_prob_space) joint_distribution_restriction_snd:
  "joint_distribution X Y A \<le> distribution Y (snd ` A)"
  unfolding distribution_def
proof (safe intro!: finite_measure_mono)
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
  using
    joint_distribution_restriction_fst[of X Y "{(x, y)}"]
    joint_distribution_restriction_snd[of X Y "{(x, y)}"]
  by (auto intro: antisym)

lemma (in finite_prob_space) distribution_mono:
  assumes "\<And>t. \<lbrakk> t \<in> space M ; X t \<in> x \<rbrakk> \<Longrightarrow> Y t \<in> y"
  shows "distribution X x \<le> distribution Y y"
  unfolding distribution_def
  using assms by (auto simp: sets_eq_Pow intro!: finite_measure_mono)

lemma (in finite_prob_space) distribution_mono_gt_0:
  assumes gt_0: "0 < distribution X x"
  assumes *: "\<And>t. \<lbrakk> t \<in> space M ; X t \<in> x \<rbrakk> \<Longrightarrow> Y t \<in> y"
  shows "0 < distribution Y y"
  by (rule less_le_trans[OF gt_0 distribution_mono]) (rule *)

lemma (in finite_prob_space) sum_over_space_distrib:
  "(\<Sum>x\<in>X`space M. distribution X {x}) = 1"
  unfolding distribution_def prob_space[symmetric] using finite_space
  by (subst finite_measure_finite_Union[symmetric])
     (auto simp add: disjoint_family_on_def sets_eq_Pow
           intro!: arg_cong[where f=\<mu>'])

lemma (in finite_prob_space) finite_sum_over_space_eq_1:
  "(\<Sum>x\<in>space M. prob {x}) = 1"
  using prob_space finite_space
  by (subst (asm) finite_measure_finite_singleton) auto

lemma (in prob_space) distribution_remove_const:
  shows "joint_distribution X (\<lambda>x. ()) {(x, ())} = distribution X {x}"
  and "joint_distribution (\<lambda>x. ()) X {((), x)} = distribution X {x}"
  and "joint_distribution X (\<lambda>x. (Y x, ())) {(x, y, ())} = joint_distribution X Y {(x, y)}"
  and "joint_distribution X (\<lambda>x. ((), Y x)) {(x, (), y)} = joint_distribution X Y {(x, y)}"
  and "distribution (\<lambda>x. ()) {()} = 1"
  by (auto intro!: arg_cong[where f=\<mu>'] simp: distribution_def prob_space[symmetric])

lemma (in finite_prob_space) setsum_distribution_gen:
  assumes "Z -` {c} \<inter> space M = (\<Union>x \<in> X`space M. Y -` {f x}) \<inter> space M"
  and "inj_on f (X`space M)"
  shows "(\<Sum>x \<in> X`space M. distribution Y {f x}) = distribution Z {c}"
  unfolding distribution_def assms
  using finite_space assms
  by (subst finite_measure_finite_Union[symmetric])
     (auto simp add: disjoint_family_on_def sets_eq_Pow inj_on_def
      intro!: arg_cong[where f=prob])

lemma (in finite_prob_space) setsum_distribution:
  "(\<Sum>x \<in> X`space M. joint_distribution X Y {(x, y)}) = distribution Y {y}"
  "(\<Sum>y \<in> Y`space M. joint_distribution X Y {(x, y)}) = distribution X {x}"
  "(\<Sum>x \<in> X`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution Y Z {(y, z)}"
  "(\<Sum>y \<in> Y`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution X Z {(x, z)}"
  "(\<Sum>z \<in> Z`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution X Y {(x, y)}"
  by (auto intro!: inj_onI setsum_distribution_gen)

lemma (in finite_prob_space) uniform_prob:
  assumes "x \<in> space M"
  assumes "\<And> x y. \<lbrakk>x \<in> space M ; y \<in> space M\<rbrakk> \<Longrightarrow> prob {x} = prob {y}"
  shows "prob {x} = 1 / card (space M)"
proof -
  have prob_x: "\<And> y. y \<in> space M \<Longrightarrow> prob {y} = prob {x}"
    using assms(2)[OF _ `x \<in> space M`] by blast
  have "1 = prob (space M)"
    using prob_space by auto
  also have "\<dots> = (\<Sum> x \<in> space M. prob {x})"
    using finite_measure_finite_Union[of "space M" "\<lambda> x. {x}", simplified]
      sets_eq_Pow inj_singleton[unfolded inj_on_def, rule_format]
      finite_space unfolding disjoint_family_on_def  prob_space[symmetric]
    by (auto simp add:setsum_restrict_set)
  also have "\<dots> = (\<Sum> y \<in> space M. prob {x})"
    using prob_x by auto
  also have "\<dots> = real_of_nat (card (space M)) * prob {x}" by simp
  finally have one: "1 = real (card (space M)) * prob {x}"
    using real_eq_of_nat by auto
  hence two: "real (card (space M)) \<noteq> 0" by fastsimp 
  from one have three: "prob {x} \<noteq> 0" by fastsimp
  thus ?thesis using one two three divide_cancel_right
    by (auto simp:field_simps)
qed

lemma (in prob_space) prob_space_subalgebra:
  assumes "sigma_algebra N" "sets N \<subseteq> sets M" "space N = space M"
    and "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A"
  shows "prob_space N"
proof -
  interpret N: measure_space N
    by (rule measure_space_subalgebra[OF assms])
  show ?thesis
  proof qed (insert assms(4)[OF N.top], simp add: assms measure_space_1)
qed

lemma (in prob_space) prob_space_of_restricted_space:
  assumes "\<mu> A \<noteq> 0" "A \<in> sets M"
  shows "prob_space (restricted_space A \<lparr>measure := \<lambda>S. \<mu> S / \<mu> A\<rparr>)"
    (is "prob_space ?P")
proof -
  interpret A: measure_space "restricted_space A"
    using `A \<in> sets M` by (rule restricted_measure_space)
  interpret A': sigma_algebra ?P
    by (rule A.sigma_algebra_cong) auto
  show "prob_space ?P"
  proof
    show "measure ?P (space ?P) = 1"
      using real_measure[OF `A \<in> events`] `\<mu> A \<noteq> 0` by auto
    show "positive ?P (measure ?P)"
    proof (simp add: positive_def, safe)
      show "0 / \<mu> A = 0" using `\<mu> A \<noteq> 0` by (cases "\<mu> A") (auto simp: zero_extreal_def)
      fix B assume "B \<in> events"
      with real_measure[of "A \<inter> B"] real_measure[OF `A \<in> events`] `A \<in> sets M`
      show "0 \<le> \<mu> (A \<inter> B) / \<mu> A" by (auto simp: Int)
    qed
    show "countably_additive ?P (measure ?P)"
    proof (simp add: countably_additive_def, safe)
      fix B and F :: "nat \<Rightarrow> 'a set"
      assume F: "range F \<subseteq> op \<inter> A ` events" "disjoint_family F"
      { fix i
        from F have "F i \<in> op \<inter> A ` events" by auto
        with `A \<in> events` have "F i \<in> events" by auto }
      moreover then have "range F \<subseteq> events" by auto
      moreover have "\<And>S. \<mu> S / \<mu> A = inverse (\<mu> A) * \<mu> S"
        by (simp add: mult_commute divide_extreal_def)
      moreover have "0 \<le> inverse (\<mu> A)"
        using real_measure[OF `A \<in> events`] by auto
      ultimately show "(\<Sum>i. \<mu> (F i) / \<mu> A) = \<mu> (\<Union>i. F i) / \<mu> A"
        using measure_countably_additive[of F] F
        by (auto simp: suminf_cmult_extreal)
    qed
  qed
qed

lemma finite_prob_spaceI:
  assumes "finite (space M)" "sets M = Pow(space M)"
    and "measure M (space M) = 1" "measure M {} = 0" "\<And>A. A \<subseteq> space M \<Longrightarrow> 0 \<le> measure M A"
    and "\<And>A B. A\<subseteq>space M \<Longrightarrow> B\<subseteq>space M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> measure M (A \<union> B) = measure M A + measure M B"
  shows "finite_prob_space M"
  unfolding finite_prob_space_eq
proof
  show "finite_measure_space M" using assms
    by (auto intro!: finite_measure_spaceI)
  show "measure M (space M) = 1" by fact
qed

lemma (in finite_prob_space) finite_measure_space:
  fixes X :: "'a \<Rightarrow> 'x"
  shows "finite_measure_space \<lparr>space = X ` space M, sets = Pow (X ` space M), measure = extreal \<circ> distribution X\<rparr>"
    (is "finite_measure_space ?S")
proof (rule finite_measure_spaceI, simp_all)
  show "finite (X ` space M)" using finite_space by simp
next
  fix A B :: "'x set" assume "A \<inter> B = {}"
  then show "distribution X (A \<union> B) = distribution X A + distribution X B"
    unfolding distribution_def
    by (subst finite_measure_Union[symmetric])
       (auto intro!: arg_cong[where f=\<mu>'] simp: sets_eq_Pow)
qed

lemma (in finite_prob_space) finite_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M, sets = Pow (X ` space M), measure = extreal \<circ> distribution X \<rparr>"
  by (simp add: finite_prob_space_eq finite_measure_space measure_space_1 one_extreal_def)

lemma (in finite_prob_space) finite_product_measure_space:
  fixes X :: "'a \<Rightarrow> 'x" and Y :: "'a \<Rightarrow> 'y"
  assumes "finite s1" "finite s2"
  shows "finite_measure_space \<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2), measure = extreal \<circ> joint_distribution X Y\<rparr>"
    (is "finite_measure_space ?M")
proof (rule finite_measure_spaceI, simp_all)
  show "finite (s1 \<times> s2)"
    using assms by auto
next
  fix A B :: "('x*'y) set" assume "A \<inter> B = {}"
  then show "joint_distribution X Y (A \<union> B) = joint_distribution X Y A + joint_distribution X Y B"
    unfolding distribution_def
    by (subst finite_measure_Union[symmetric])
       (auto intro!: arg_cong[where f=\<mu>'] simp: sets_eq_Pow)
qed

lemma (in finite_prob_space) finite_product_measure_space_of_images:
  shows "finite_measure_space \<lparr> space = X ` space M \<times> Y ` space M,
                                sets = Pow (X ` space M \<times> Y ` space M),
                                measure = extreal \<circ> joint_distribution X Y \<rparr>"
  using finite_space by (auto intro!: finite_product_measure_space)

lemma (in finite_prob_space) finite_product_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M \<times> Y ` space M, sets = Pow (X ` space M \<times> Y ` space M),
                       measure = extreal \<circ> joint_distribution X Y \<rparr>"
  (is "finite_prob_space ?S")
proof (simp add: finite_prob_space_eq finite_product_measure_space_of_images one_extreal_def)
  have "X -` X ` space M \<inter> Y -` Y ` space M \<inter> space M = space M" by auto
  thus "joint_distribution X Y (X ` space M \<times> Y ` space M) = 1"
    by (simp add: distribution_def prob_space vimage_Times comp_def measure_space_1)
qed

section "Conditional Expectation and Probability"

lemma (in prob_space) conditional_expectation_exists:
  fixes X :: "'a \<Rightarrow> extreal" and N :: "('a, 'b) measure_space_scheme"
  assumes borel: "X \<in> borel_measurable M" "AE x. 0 \<le> X x"
  and N: "sigma_algebra N" "sets N \<subseteq> sets M" "space N = space M" "\<And>A. measure N A = \<mu> A"
  shows "\<exists>Y\<in>borel_measurable N. (\<forall>x. 0 \<le> Y x) \<and> (\<forall>C\<in>sets N.
      (\<integral>\<^isup>+x. Y x * indicator C x \<partial>M) = (\<integral>\<^isup>+x. X x * indicator C x \<partial>M))"
proof -
  note N(4)[simp]
  interpret P: prob_space N
    using prob_space_subalgebra[OF N] .

  let "?f A" = "\<lambda>x. X x * indicator A x"
  let "?Q A" = "integral\<^isup>P M (?f A)"

  from measure_space_density[OF borel]
  have Q: "measure_space (N\<lparr> measure := ?Q \<rparr>)"
    apply (rule measure_space.measure_space_subalgebra[of "M\<lparr> measure := ?Q \<rparr>"])
    using N by (auto intro!: P.sigma_algebra_cong)
  then interpret Q: measure_space "N\<lparr> measure := ?Q \<rparr>" .

  have "P.absolutely_continuous ?Q"
    unfolding P.absolutely_continuous_def
  proof safe
    fix A assume "A \<in> sets N" "P.\<mu> A = 0"
    then have f_borel: "?f A \<in> borel_measurable M" "AE x. x \<notin> A"
      using borel N by (auto intro!: borel_measurable_indicator AE_not_in)
    then show "?Q A = 0"
      by (auto simp add: positive_integral_0_iff_AE)
  qed
  from P.Radon_Nikodym[OF Q this]
  obtain Y where Y: "Y \<in> borel_measurable N" "\<And>x. 0 \<le> Y x"
    "\<And>A. A \<in> sets N \<Longrightarrow> ?Q A =(\<integral>\<^isup>+x. Y x * indicator A x \<partial>N)"
    by blast
  with N(2) show ?thesis
    by (auto intro!: bexI[OF _ Y(1)] simp: positive_integral_subalgebra[OF _ _ N(2,3,4,1)])
qed

definition (in prob_space)
  "conditional_expectation N X = (SOME Y. Y\<in>borel_measurable N \<and> (\<forall>x. 0 \<le> Y x)
    \<and> (\<forall>C\<in>sets N. (\<integral>\<^isup>+x. Y x * indicator C x\<partial>M) = (\<integral>\<^isup>+x. X x * indicator C x\<partial>M)))"

abbreviation (in prob_space)
  "conditional_prob N A \<equiv> conditional_expectation N (indicator A)"

lemma (in prob_space)
  fixes X :: "'a \<Rightarrow> extreal" and N :: "('a, 'b) measure_space_scheme"
  assumes borel: "X \<in> borel_measurable M" "AE x. 0 \<le> X x"
  and N: "sigma_algebra N" "sets N \<subseteq> sets M" "space N = space M" "\<And>A. measure N A = \<mu> A"
  shows borel_measurable_conditional_expectation:
    "conditional_expectation N X \<in> borel_measurable N"
  and conditional_expectation: "\<And>C. C \<in> sets N \<Longrightarrow>
      (\<integral>\<^isup>+x. conditional_expectation N X x * indicator C x \<partial>M) =
      (\<integral>\<^isup>+x. X x * indicator C x \<partial>M)"
   (is "\<And>C. C \<in> sets N \<Longrightarrow> ?eq C")
proof -
  note CE = conditional_expectation_exists[OF assms, unfolded Bex_def]
  then show "conditional_expectation N X \<in> borel_measurable N"
    unfolding conditional_expectation_def by (rule someI2_ex) blast

  from CE show "\<And>C. C \<in> sets N \<Longrightarrow> ?eq C"
    unfolding conditional_expectation_def by (rule someI2_ex) blast
qed

lemma (in sigma_algebra) factorize_measurable_function_pos:
  fixes Z :: "'a \<Rightarrow> extreal" and Y :: "'a \<Rightarrow> 'c"
  assumes "sigma_algebra M'" and "Y \<in> measurable M M'" "Z \<in> borel_measurable M"
  assumes Z: "Z \<in> borel_measurable (sigma_algebra.vimage_algebra M' (space M) Y)"
  shows "\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. max 0 (Z x) = g (Y x)"
proof -
  interpret M': sigma_algebra M' by fact
  have Y: "Y \<in> space M \<rightarrow> space M'" using assms unfolding measurable_def by auto
  from M'.sigma_algebra_vimage[OF this]
  interpret va: sigma_algebra "M'.vimage_algebra (space M) Y" .

  from va.borel_measurable_implies_simple_function_sequence'[OF Z] guess f . note f = this

  have "\<forall>i. \<exists>g. simple_function M' g \<and> (\<forall>x\<in>space M. f i x = g (Y x))"
  proof
    fix i
    from f(1)[of i] have "finite (f i`space M)" and B_ex:
      "\<forall>z\<in>(f i)`space M. \<exists>B. B \<in> sets M' \<and> (f i) -` {z} \<inter> space M = Y -` B \<inter> space M"
      unfolding simple_function_def by auto
    from B_ex[THEN bchoice] guess B .. note B = this

    let ?g = "\<lambda>x. \<Sum>z\<in>f i`space M. z * indicator (B z) x"

    show "\<exists>g. simple_function M' g \<and> (\<forall>x\<in>space M. f i x = g (Y x))"
    proof (intro exI[of _ ?g] conjI ballI)
      show "simple_function M' ?g" using B by auto

      fix x assume "x \<in> space M"
      then have "\<And>z. z \<in> f i`space M \<Longrightarrow> indicator (B z) (Y x) = (indicator (f i -` {z} \<inter> space M) x::extreal)"
        unfolding indicator_def using B by auto
      then show "f i x = ?g (Y x)" using `x \<in> space M` f(1)[of i]
        by (subst va.simple_function_indicator_representation) auto
    qed
  qed
  from choice[OF this] guess g .. note g = this

  show ?thesis
  proof (intro ballI bexI)
    show "(\<lambda>x. SUP i. g i x) \<in> borel_measurable M'"
      using g by (auto intro: M'.borel_measurable_simple_function)
    fix x assume "x \<in> space M"
    have "max 0 (Z x) = (SUP i. f i x)" using f by simp
    also have "\<dots> = (SUP i. g i (Y x))"
      using g `x \<in> space M` by simp
    finally show "max 0 (Z x) = (SUP i. g i (Y x))" .
  qed
qed

lemma extreal_0_le_iff_le_0[simp]:
  fixes a :: extreal shows "0 \<le> -a \<longleftrightarrow> a \<le> 0"
  by (cases rule: extreal2_cases[of a]) auto

lemma (in sigma_algebra) factorize_measurable_function:
  fixes Z :: "'a \<Rightarrow> extreal" and Y :: "'a \<Rightarrow> 'c"
  assumes "sigma_algebra M'" and "Y \<in> measurable M M'" "Z \<in> borel_measurable M"
  shows "Z \<in> borel_measurable (sigma_algebra.vimage_algebra M' (space M) Y)
    \<longleftrightarrow> (\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. Z x = g (Y x))"
proof safe
  interpret M': sigma_algebra M' by fact
  have Y: "Y \<in> space M \<rightarrow> space M'" using assms unfolding measurable_def by auto
  from M'.sigma_algebra_vimage[OF this]
  interpret va: sigma_algebra "M'.vimage_algebra (space M) Y" .

  { fix g :: "'c \<Rightarrow> extreal" assume "g \<in> borel_measurable M'"
    with M'.measurable_vimage_algebra[OF Y]
    have "g \<circ> Y \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
      by (rule measurable_comp)
    moreover assume "\<forall>x\<in>space M. Z x = g (Y x)"
    then have "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y) \<longleftrightarrow>
       g \<circ> Y \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
       by (auto intro!: measurable_cong)
    ultimately show "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
      by simp }

  assume Z: "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
  with assms have "(\<lambda>x. - Z x) \<in> borel_measurable M"
    "(\<lambda>x. - Z x) \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
    by auto
  from factorize_measurable_function_pos[OF assms(1,2) this] guess n .. note n = this
  from factorize_measurable_function_pos[OF assms Z] guess p .. note p = this
  let "?g x" = "p x - n x"
  show "\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. Z x = g (Y x)"
  proof (intro bexI ballI)
    show "?g \<in> borel_measurable M'" using p n by auto
    fix x assume "x \<in> space M"
    then have "p (Y x) = max 0 (Z x)" "n (Y x) = max 0 (- Z x)"
      using p n by auto
    then show "Z x = ?g (Y x)"
      by (auto split: split_max)
  qed
qed

subsection "Bernoulli space"

definition "bernoulli_space p = \<lparr> space = UNIV, sets = UNIV,
  measure = extreal \<circ> setsum (\<lambda>b. if b then min 1 (max 0 p) else 1 - min 1 (max 0 p)) \<rparr>"

interpretation bernoulli: finite_prob_space "bernoulli_space p" for p
  by (rule finite_prob_spaceI)
     (auto simp: bernoulli_space_def UNIV_bool one_extreal_def setsum_Un_disjoint intro!: setsum_nonneg)

lemma bernoulli_measure:
  "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> bernoulli.prob p B = (\<Sum>b\<in>B. if b then p else 1 - p)"
  unfolding bernoulli.\<mu>'_def unfolding bernoulli_space_def by (auto intro!: setsum_cong)

lemma bernoulli_measure_True: "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> bernoulli.prob p {True} = p"
  and bernoulli_measure_False: "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> bernoulli.prob p {False} = 1 - p"
  unfolding bernoulli_measure by simp_all

end
