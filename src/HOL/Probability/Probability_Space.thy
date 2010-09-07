theory Probability_Space
imports Lebesgue_Integration Radon_Nikodym
begin

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

lemma (in prob_space) distribution_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> X x = Y x"
  shows "distribution X = distribution Y"
  unfolding distribution_def ext_iff
  using assms by (auto intro!: arg_cong[where f="\<mu>"])

lemma (in prob_space) joint_distribution_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "joint_distribution X Y = joint_distribution X' Y'"
  unfolding distribution_def ext_iff
  using assms by (auto intro!: arg_cong[where f="\<mu>"])

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

lemma (in finite_prob_space) distribution_mono:
  assumes "\<And>t. \<lbrakk> t \<in> space M ; X t \<in> x \<rbrakk> \<Longrightarrow> Y t \<in> y"
  shows "distribution X x \<le> distribution Y y"
  unfolding distribution_def
  using assms by (auto simp: sets_eq_Pow intro!: measure_mono)

lemma (in finite_prob_space) distribution_mono_gt_0:
  assumes gt_0: "0 < distribution X x"
  assumes *: "\<And>t. \<lbrakk> t \<in> space M ; X t \<in> x \<rbrakk> \<Longrightarrow> Y t \<in> y"
  shows "0 < distribution Y y"
  by (rule less_le_trans[OF gt_0 distribution_mono]) (rule *)

lemma (in finite_prob_space) sum_over_space_distrib:
  "(\<Sum>x\<in>X`space M. distribution X {x}) = 1"
  unfolding distribution_def measure_space_1[symmetric] using finite_space
  by (subst measure_finitely_additive'')
     (auto simp add: disjoint_family_on_def sets_eq_Pow intro!: arg_cong[where f=\<mu>])

lemma (in finite_prob_space) sum_over_space_real_distribution:
  "(\<Sum>x\<in>X`space M. real (distribution X {x})) = 1"
  unfolding distribution_def prob_space[symmetric] using finite_space
  by (subst real_finite_measure_finite_Union[symmetric])
     (auto simp add: disjoint_family_on_def sets_eq_Pow intro!: arg_cong[where f=prob])

lemma (in finite_prob_space) finite_sum_over_space_eq_1:
  "(\<Sum>x\<in>space M. real (\<mu> {x})) = 1"
  using sum_over_space_eq_1 finite_measure by (simp add: real_of_pinfreal_setsum sets_eq_Pow)

lemma (in finite_prob_space) distribution_finite:
  "distribution X A \<noteq> \<omega>"
  using finite_measure[of "X -` A \<inter> space M"]
  unfolding distribution_def sets_eq_Pow by auto

lemma (in finite_prob_space) real_distribution_gt_0[simp]:
  "0 < real (distribution Y y) \<longleftrightarrow>  0 < distribution Y y"
  using assms by (auto intro!: real_pinfreal_pos distribution_finite)

lemma (in finite_prob_space) real_distribution_mult_pos_pos:
  assumes "0 < distribution Y y"
  and "0 < distribution X x"
  shows "0 < real (distribution Y y * distribution X x)"
  unfolding real_of_pinfreal_mult[symmetric]
  using assms by (auto intro!: mult_pos_pos)

lemma (in finite_prob_space) real_distribution_divide_pos_pos:
  assumes "0 < distribution Y y"
  and "0 < distribution X x"
  shows "0 < real (distribution Y y / distribution X x)"
  unfolding divide_pinfreal_def real_of_pinfreal_mult[symmetric]
  using assms distribution_finite[of X x] by (cases "distribution X x") (auto intro!: mult_pos_pos)

lemma (in finite_prob_space) real_distribution_mult_inverse_pos_pos:
  assumes "0 < distribution Y y"
  and "0 < distribution X x"
  shows "0 < real (distribution Y y * inverse (distribution X x))"
  unfolding divide_pinfreal_def real_of_pinfreal_mult[symmetric]
  using assms distribution_finite[of X x] by (cases "distribution X x") (auto intro!: mult_pos_pos)

lemma (in prob_space) distribution_remove_const:
  shows "joint_distribution X (\<lambda>x. ()) {(x, ())} = distribution X {x}"
  and "joint_distribution (\<lambda>x. ()) X {((), x)} = distribution X {x}"
  and "joint_distribution X (\<lambda>x. (Y x, ())) {(x, y, ())} = joint_distribution X Y {(x, y)}"
  and "joint_distribution X (\<lambda>x. ((), Y x)) {(x, (), y)} = joint_distribution X Y {(x, y)}"
  and "distribution (\<lambda>x. ()) {()} = 1"
  unfolding measure_space_1[symmetric]
  by (auto intro!: arg_cong[where f="\<mu>"] simp: distribution_def)

lemma (in finite_prob_space) setsum_distribution_gen:
  assumes "Z -` {c} \<inter> space M = (\<Union>x \<in> X`space M. Y -` {f x}) \<inter> space M"
  and "inj_on f (X`space M)"
  shows "(\<Sum>x \<in> X`space M. distribution Y {f x}) = distribution Z {c}"
  unfolding distribution_def assms
  using finite_space assms
  by (subst measure_finitely_additive'')
     (auto simp add: disjoint_family_on_def sets_eq_Pow inj_on_def
      intro!: arg_cong[where f=prob])

lemma (in finite_prob_space) setsum_distribution:
  "(\<Sum>x \<in> X`space M. joint_distribution X Y {(x, y)}) = distribution Y {y}"
  "(\<Sum>y \<in> Y`space M. joint_distribution X Y {(x, y)}) = distribution X {x}"
  "(\<Sum>x \<in> X`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution Y Z {(y, z)}"
  "(\<Sum>y \<in> Y`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution X Z {(x, z)}"
  "(\<Sum>z \<in> Z`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution X Y {(x, y)}"
  by (auto intro!: inj_onI setsum_distribution_gen)

lemma (in finite_prob_space) setsum_real_distribution_gen:
  assumes "Z -` {c} \<inter> space M = (\<Union>x \<in> X`space M. Y -` {f x}) \<inter> space M"
  and "inj_on f (X`space M)"
  shows "(\<Sum>x \<in> X`space M. real (distribution Y {f x})) = real (distribution Z {c})"
  unfolding distribution_def assms
  using finite_space assms
  by (subst real_finite_measure_finite_Union[symmetric])
     (auto simp add: disjoint_family_on_def sets_eq_Pow inj_on_def
        intro!: arg_cong[where f=prob])

lemma (in finite_prob_space) setsum_real_distribution:
  "(\<Sum>x \<in> X`space M. real (joint_distribution X Y {(x, y)})) = real (distribution Y {y})"
  "(\<Sum>y \<in> Y`space M. real (joint_distribution X Y {(x, y)})) = real (distribution X {x})"
  "(\<Sum>x \<in> X`space M. real (joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)})) = real (joint_distribution Y Z {(y, z)})"
  "(\<Sum>y \<in> Y`space M. real (joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)})) = real (joint_distribution X Z {(x, z)})"
  "(\<Sum>z \<in> Z`space M. real (joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)})) = real (joint_distribution X Y {(x, y)})"
  by (auto intro!: inj_onI setsum_real_distribution_gen)

lemma (in finite_prob_space) real_distribution_order:
  shows "r \<le> real (joint_distribution X Y {(x, y)}) \<Longrightarrow> r \<le> real (distribution X {x})"
  and "r \<le> real (joint_distribution X Y {(x, y)}) \<Longrightarrow> r \<le> real (distribution Y {y})"
  and "r < real (joint_distribution X Y {(x, y)}) \<Longrightarrow> r < real (distribution X {x})"
  and "r < real (joint_distribution X Y {(x, y)}) \<Longrightarrow> r < real (distribution Y {y})"
  and "distribution X {x} = 0 \<Longrightarrow> real (joint_distribution X Y {(x, y)}) = 0"
  and "distribution Y {y} = 0 \<Longrightarrow> real (joint_distribution X Y {(x, y)}) = 0"
  using real_of_pinfreal_mono[OF distribution_finite joint_distribution_restriction_fst, of X Y "{(x, y)}"]
  using real_of_pinfreal_mono[OF distribution_finite joint_distribution_restriction_snd, of X Y "{(x, y)}"]
  using real_pinfreal_nonneg[of "joint_distribution X Y {(x, y)}"]
  by auto

lemma (in prob_space) joint_distribution_remove[simp]:
    "joint_distribution X X {(x, x)} = distribution X {x}"
  unfolding distribution_def by (auto intro!: arg_cong[where f="\<mu>"])

lemma (in finite_prob_space) distribution_1:
  "distribution X A \<le> 1"
  unfolding distribution_def measure_space_1[symmetric]
  by (auto intro!: measure_mono simp: sets_eq_Pow)

lemma (in finite_prob_space) real_distribution_1:
  "real (distribution X A) \<le> 1"
  unfolding real_pinfreal_1[symmetric]
  by (rule real_of_pinfreal_mono[OF _ distribution_1]) simp

lemma (in finite_prob_space) uniform_prob:
  assumes "x \<in> space M"
  assumes "\<And> x y. \<lbrakk>x \<in> space M ; y \<in> space M\<rbrakk> \<Longrightarrow> prob {x} = prob {y}"
  shows "prob {x} = 1 / real (card (space M))"
proof -
  have prob_x: "\<And> y. y \<in> space M \<Longrightarrow> prob {y} = prob {x}"
    using assms(2)[OF _ `x \<in> space M`] by blast
  have "1 = prob (space M)"
    using prob_space by auto
  also have "\<dots> = (\<Sum> x \<in> space M. prob {x})"
    using real_finite_measure_finite_Union[of "space M" "\<lambda> x. {x}", simplified]
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
  assumes "N \<subseteq> sets M" "sigma_algebra (M\<lparr> sets := N \<rparr>)"
  shows "prob_space (M\<lparr> sets := N \<rparr>) \<mu>"
proof -
  interpret N: measure_space "M\<lparr> sets := N \<rparr>" \<mu>
    using measure_space_subalgebra[OF assms] .
  show ?thesis
    proof qed (simp add: measure_space_1)
qed

lemma (in prob_space) prob_space_of_restricted_space:
  assumes "\<mu> A \<noteq> 0" "\<mu> A \<noteq> \<omega>" "A \<in> sets M"
  shows "prob_space (restricted_space A) (\<lambda>S. \<mu> S / \<mu> A)"
  unfolding prob_space_def prob_space_axioms_def
proof
  show "\<mu> (space (restricted_space A)) / \<mu> A = 1"
    using `\<mu> A \<noteq> 0` `\<mu> A \<noteq> \<omega>` by (auto simp: pinfreal_noteq_omega_Ex)
  have *: "\<And>S. \<mu> S / \<mu> A = inverse (\<mu> A) * \<mu> S" by (simp add: mult_commute)
  interpret A: measure_space "restricted_space A" \<mu>
    using `A \<in> sets M` by (rule restricted_measure_space)
  show "measure_space (restricted_space A) (\<lambda>S. \<mu> S / \<mu> A)"
  proof
    show "\<mu> {} / \<mu> A = 0" by auto
    show "countably_additive (restricted_space A) (\<lambda>S. \<mu> S / \<mu> A)"
        unfolding countably_additive_def psuminf_cmult_right *
        using A.measure_countably_additive by auto
  qed
qed

lemma finite_prob_spaceI:
  assumes "finite (space M)" "sets M = Pow(space M)" "\<mu> (space M) = 1" "\<mu> {} = 0"
    and "\<And>A B. A\<subseteq>space M \<Longrightarrow> B\<subseteq>space M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> \<mu> (A \<union> B) = \<mu> A + \<mu> B"
  shows "finite_prob_space M \<mu>"
  unfolding finite_prob_space_eq
proof
  show "finite_measure_space M \<mu>" using assms
     by (auto intro!: finite_measure_spaceI)
  show "\<mu> (space M) = 1" by fact
qed

lemma (in finite_prob_space) finite_measure_space:
  fixes X :: "'a \<Rightarrow> 'x"
  shows "finite_measure_space \<lparr>space = X ` space M, sets = Pow (X ` space M)\<rparr> (distribution X)"
    (is "finite_measure_space ?S _")
proof (rule finite_measure_spaceI, simp_all)
  show "finite (X ` space M)" using finite_space by simp
next
  fix A B :: "'x set" assume "A \<inter> B = {}"
  then show "distribution X (A \<union> B) = distribution X A + distribution X B"
    unfolding distribution_def
    by (subst measure_additive)
       (auto intro!: arg_cong[where f=\<mu>] simp: sets_eq_Pow)
qed

lemma (in finite_prob_space) finite_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M, sets = Pow (X ` space M)\<rparr> (distribution X)"
  by (simp add: finite_prob_space_eq finite_measure_space)

lemma (in prob_space) joint_distribution_commute:
  "joint_distribution X Y x = joint_distribution Y X ((\<lambda>(x,y). (y,x))`x)"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>])

lemma (in finite_prob_space) real_distribution_order':
  shows "real (distribution X {x}) = 0 \<Longrightarrow> real (joint_distribution X Y {(x, y)}) = 0"
  and "real (distribution Y {y}) = 0 \<Longrightarrow> real (joint_distribution X Y {(x, y)}) = 0"
  using real_of_pinfreal_mono[OF distribution_finite joint_distribution_restriction_fst, of X Y "{(x, y)}"]
  using real_of_pinfreal_mono[OF distribution_finite joint_distribution_restriction_snd, of X Y "{(x, y)}"]
  using real_pinfreal_nonneg[of "joint_distribution X Y {(x, y)}"]
  by auto

lemma (in finite_prob_space) finite_product_measure_space:
  fixes X :: "'a \<Rightarrow> 'x" and Y :: "'a \<Rightarrow> 'y"
  assumes "finite s1" "finite s2"
  shows "finite_measure_space \<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2)\<rparr> (joint_distribution X Y)"
    (is "finite_measure_space ?M ?D")
proof (rule finite_measure_spaceI, simp_all)
  show "finite (s1 \<times> s2)"
    using assms by auto
  show "joint_distribution X Y (s1\<times>s2) \<noteq> \<omega>"
    using distribution_finite .
next
  fix A B :: "('x*'y) set" assume "A \<inter> B = {}"
  then show "joint_distribution X Y (A \<union> B) = joint_distribution X Y A + joint_distribution X Y B"
    unfolding distribution_def
    by (subst measure_additive)
       (auto intro!: arg_cong[where f=\<mu>] simp: sets_eq_Pow)
qed

lemma (in finite_prob_space) finite_product_measure_space_of_images:
  shows "finite_measure_space \<lparr> space = X ` space M \<times> Y ` space M,
                                sets = Pow (X ` space M \<times> Y ` space M) \<rparr>
                              (joint_distribution X Y)"
  using finite_space by (auto intro!: finite_product_measure_space)

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
  "conditional_prob N A \<equiv> conditional_expectation N (indicator A)"

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

lemma (in sigma_algebra) factorize_measurable_function:
  fixes Z :: "'a \<Rightarrow> pinfreal" and Y :: "'a \<Rightarrow> 'c"
  assumes "sigma_algebra M'" and "Y \<in> measurable M M'" "Z \<in> borel_measurable M"
  shows "Z \<in> borel_measurable (sigma_algebra.vimage_algebra M' (space M) Y)
    \<longleftrightarrow> (\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. Z x = g (Y x))"
proof safe
  interpret M': sigma_algebra M' by fact
  have Y: "Y \<in> space M \<rightarrow> space M'" using assms unfolding measurable_def by auto
  from M'.sigma_algebra_vimage[OF this]
  interpret va: sigma_algebra "M'.vimage_algebra (space M) Y" .

  { fix g :: "'c \<Rightarrow> pinfreal" assume "g \<in> borel_measurable M'"
    with M'.measurable_vimage_algebra[OF Y]
    have "g \<circ> Y \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
      by (rule measurable_comp)
    moreover assume "\<forall>x\<in>space M. Z x = g (Y x)"
    then have "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y) \<longleftrightarrow>
       g \<circ> Y \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
       by (auto intro!: measurable_cong)
    ultimately show "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
      by simp }

  assume "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
  from va.borel_measurable_implies_simple_function_sequence[OF this]
  obtain f where f: "\<And>i. va.simple_function (f i)" and "f \<up> Z" by blast

  have "\<forall>i. \<exists>g. M'.simple_function g \<and> (\<forall>x\<in>space M. f i x = g (Y x))"
  proof
    fix i
    from f[of i] have "finite (f i`space M)" and B_ex:
      "\<forall>z\<in>(f i)`space M. \<exists>B. B \<in> sets M' \<and> (f i) -` {z} \<inter> space M = Y -` B \<inter> space M"
      unfolding va.simple_function_def by auto
    from B_ex[THEN bchoice] guess B .. note B = this

    let ?g = "\<lambda>x. \<Sum>z\<in>f i`space M. z * indicator (B z) x"

    show "\<exists>g. M'.simple_function g \<and> (\<forall>x\<in>space M. f i x = g (Y x))"
    proof (intro exI[of _ ?g] conjI ballI)
      show "M'.simple_function ?g" using B by auto

      fix x assume "x \<in> space M"
      then have "\<And>z. z \<in> f i`space M \<Longrightarrow> indicator (B z) (Y x) = (indicator (f i -` {z} \<inter> space M) x::pinfreal)"
        unfolding indicator_def using B by auto
      then show "f i x = ?g (Y x)" using `x \<in> space M` f[of i]
        by (subst va.simple_function_indicator_representation) auto
    qed
  qed
  from choice[OF this] guess g .. note g = this

  show "\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. Z x = g (Y x)"
  proof (intro ballI bexI)
    show "(SUP i. g i) \<in> borel_measurable M'"
      using g by (auto intro: M'.borel_measurable_simple_function)
    fix x assume "x \<in> space M"
    have "Z x = (SUP i. f i) x" using `f \<up> Z` unfolding isoton_def by simp
    also have "\<dots> = (SUP i. g i) (Y x)" unfolding SUPR_fun_expand
      using g `x \<in> space M` by simp
    finally show "Z x = (SUP i. g i) (Y x)" .
  qed
qed

end
