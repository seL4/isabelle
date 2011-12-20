(*  Title:      HOL/Probability/Probability_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Probability measure*}

theory Probability_Measure
imports Lebesgue_Measure
begin

locale prob_space = finite_measure +
  assumes measure_space_1: "measure M (space M) = 1"

lemma prob_spaceI[Pure.intro!]:
  assumes "measure_space M"
  assumes *: "measure M (space M) = 1"
  shows "prob_space M"
proof -
  interpret finite_measure M
  proof
    show "measure_space M" by fact
    show "measure M (space M) \<noteq> \<infinity>" using * by simp 
  qed
  show "prob_space M" by default fact
qed

abbreviation (in prob_space) "events \<equiv> sets M"
abbreviation (in prob_space) "prob \<equiv> \<mu>'"
abbreviation (in prob_space) "random_variable M' X \<equiv> sigma_algebra M' \<and> X \<in> measurable M M'"
abbreviation (in prob_space) "expectation \<equiv> integral\<^isup>L M"

definition (in prob_space)
  "distribution X A = \<mu>' (X -` A \<inter> space M)"

abbreviation (in prob_space)
  "joint_distribution X Y \<equiv> distribution (\<lambda>x. (X x, Y x))"

lemma (in prob_space) prob_space_cong:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "space N = space M" "sets N = sets M"
  shows "prob_space N"
proof
  show "measure_space N" by (intro measure_space_cong assms)
  show "measure N (space N) = 1"
    using measure_space_1 assms by simp
qed

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
  using measure_space_1 unfolding \<mu>'_def by (simp add: one_ereal_def)

lemma (in prob_space) prob_le_1[simp, intro]: "prob A \<le> 1"
  using bounded_measure[of A] by (simp add: prob_space)

lemma (in prob_space) distribution_positive[simp, intro]:
  "0 \<le> distribution X A" unfolding distribution_def by auto

lemma (in prob_space) not_zero_less_distribution[simp]:
  "(\<not> 0 < distribution X A) \<longleftrightarrow> distribution X A = 0"
  using distribution_positive[of X A] by arith

lemma (in prob_space) joint_distribution_remove[simp]:
    "joint_distribution X X {(x, x)} = distribution X {x}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

lemma (in prob_space) distribution_unit[simp]: "distribution (\<lambda>x. ()) {()} = 1"
  unfolding distribution_def using prob_space by auto

lemma (in prob_space) joint_distribution_unit[simp]: "distribution (\<lambda>x. (X x, ())) {(a, ())} = distribution X {a}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

lemma (in prob_space) not_empty: "space M \<noteq> {}"
  using prob_space empty_measure' by auto

lemma (in prob_space) measure_le_1: "X \<in> sets M \<Longrightarrow> \<mu> X \<le> 1"
  unfolding measure_space_1[symmetric]
  using sets_into_space
  by (intro measure_mono) auto

lemma (in prob_space) AE_I_eq_1:
  assumes "\<mu> {x\<in>space M. P x} = 1" "{x\<in>space M. P x} \<in> sets M"
  shows "AE x. P x"
proof (rule AE_I)
  show "\<mu> (space M - {x \<in> space M. P x}) = 0"
    using assms measure_space_1 by (simp add: measure_compl)
qed (insert assms, auto)

lemma (in prob_space) distribution_1:
  "distribution X A \<le> 1"
  unfolding distribution_def by simp

lemma (in prob_space) prob_compl:
  assumes A: "A \<in> events"
  shows "prob (space M - A) = 1 - prob A"
  using finite_measure_compl[OF A] by (simp add: prob_space)

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
proof
  interpret S: measure_space S
    using S and T by (rule measure_space_vimage)
  show "measure_space S" ..
  
  from T[THEN measure_preservingD2]
  have "T -` space S \<inter> space M = space M"
    by (auto simp: measurable_def)
  with T[THEN measure_preservingD, of "space S", symmetric]
  show  "measure S (space S) = 1"
    using measure_space_1 by simp
qed

lemma prob_space_unique_Int_stable:
  fixes E :: "('a, 'b) algebra_scheme" and A :: "nat \<Rightarrow> 'a set"
  assumes E: "Int_stable E" "space E \<in> sets E"
  and M: "prob_space M" "space M = space E" "sets M = sets (sigma E)"
  and N: "prob_space N" "space N = space E" "sets N = sets (sigma E)"
  and eq: "\<And>X. X \<in> sets E \<Longrightarrow> finite_measure.\<mu>' M X = finite_measure.\<mu>' N X"
  assumes "X \<in> sets (sigma E)"
  shows "finite_measure.\<mu>' M X = finite_measure.\<mu>' N X"
proof -
  interpret M!: prob_space M by fact
  interpret N!: prob_space N by fact
  have "measure M X = measure N X"
  proof (rule measure_unique_Int_stable[OF `Int_stable E`])
    show "range (\<lambda>i. space M) \<subseteq> sets E" "incseq (\<lambda>i. space M)" "(\<Union>i. space M) = space E"
      using E M N by auto
    show "\<And>i. M.\<mu> (space M) \<noteq> \<infinity>"
      using M.measure_space_1 by simp
    show "measure_space \<lparr>space = space E, sets = sets (sigma E), measure_space.measure = M.\<mu>\<rparr>"
      using E M N by (auto intro!: M.measure_space_cong)
    show "measure_space \<lparr>space = space E, sets = sets (sigma E), measure_space.measure = N.\<mu>\<rparr>"
      using E M N by (auto intro!: N.measure_space_cong)
    { fix X assume "X \<in> sets E"
      then have "X \<in> sets (sigma E)"
        by (auto simp: sets_sigma sigma_sets.Basic)
      with eq[OF `X \<in> sets E`] M N show "M.\<mu> X = N.\<mu> X"
        by (simp add: M.finite_measure_eq N.finite_measure_eq) }
  qed fact
  with `X \<in> sets (sigma E)` M N show ?thesis
    by (simp add: M.finite_measure_eq N.finite_measure_eq)
qed

lemma (in prob_space) distribution_prob_space:
  assumes X: "random_variable S X"
  shows "prob_space (S\<lparr>measure := ereal \<circ> distribution X\<rparr>)" (is "prob_space ?S")
proof (rule prob_space_vimage)
  show "X \<in> measure_preserving M ?S"
    using X
    unfolding measure_preserving_def distribution_def_raw
    by (auto simp: finite_measure_eq measurable_sets)
  show "sigma_algebra ?S" using X by simp
qed

lemma (in prob_space) AE_distribution:
  assumes X: "random_variable MX X" and "AE x in MX\<lparr>measure := ereal \<circ> distribution X\<rparr>. Q x"
  shows "AE x. Q (X x)"
proof -
  interpret X: prob_space "MX\<lparr>measure := ereal \<circ> distribution X\<rparr>" using X by (rule distribution_prob_space)
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

lemma (in prob_space) expectation_less:
  assumes [simp]: "integrable M X"
  assumes gt: "\<forall>x\<in>space M. X x < b"
  shows "expectation X < b"
proof -
  have "expectation X < expectation (\<lambda>x. b)"
    using gt measure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) expectation_greater:
  assumes [simp]: "integrable M X"
  assumes gt: "\<forall>x\<in>space M. a < X x"
  shows "a < expectation X"
proof -
  have "expectation (\<lambda>x. a) < expectation X"
    using gt measure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

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
      by (auto simp: mem_ball dist_real_def field_simps split: split_min)
    with `x \<in> interior I` e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

    have "open (interior I)" by auto
    from openE[OF this `x \<in> interior I`] guess e .
    moreover def K \<equiv> "x - e / 2"
    with `0 < e` have "K \<in> ball x e" "K < x" by (auto simp: mem_ball dist_real_def)
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
      by (auto simp: mem_ball dist_real_def field_simps)
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
      then have "x + e / 2 \<in> ball x e" by (auto simp: mem_ball dist_real_def)
      with e interior_subset[of I] have "x + e / 2 \<in> {x<..} \<inter> I" by auto
      then show "?F x \<noteq> {}" by blast
    qed
    then show ?thesis
      using `y < x` by (simp add: field_simps)
  qed simp
qed

lemma (in prob_space) jensens_inequality:
  fixes a b :: real
  assumes X: "integrable M X" "X ` space M \<subseteq> I"
  assumes I: "I = {a <..< b} \<or> I = {a <..} \<or> I = {..< b} \<or> I = UNIV"
  assumes q: "integrable M (\<lambda>x. q (X x))" "convex_on I q"
  shows "q (expectation X) \<le> expectation (\<lambda>x. q (X x))"
proof -
  let "?F x" = "Inf ((\<lambda>t. (q x - q t) / (x - t)) ` ({x<..} \<inter> I))"
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
      using prob_space
      by (simp add: integral_add integral_cmult integral_diff lebesgue_integral_const X)
    also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
      using `x \<in> I` `open I` X(2)
      by (intro integral_mono integral_add integral_cmult integral_diff
                lebesgue_integral_const X q convex_le_Inf_differential)
         (auto simp: interior_open)
    finally show "k \<le> expectation (\<lambda>w. q (X w))" using x by auto
  qed
  finally show "q (expectation X) \<le> expectation (\<lambda>x. q (X x))" .
qed

lemma (in prob_space) distribution_eq_translated_integral:
  assumes "random_variable S X" "A \<in> sets S"
  shows "distribution X A = integral\<^isup>P (S\<lparr>measure := ereal \<circ> distribution X\<rparr>) (indicator A)"
proof -
  interpret S: prob_space "S\<lparr>measure := ereal \<circ> distribution X\<rparr>"
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

locale pair_prob_space = pair_sigma_finite M1 M2 + M1: prob_space M1 + M2: prob_space M2 for M1 M2

sublocale pair_prob_space \<subseteq> P: prob_space P
proof
  show "measure_space P" ..
  show "measure P (space P) = 1"
    by (simp add: pair_measure_times M1.measure_space_1 M2.measure_space_1 space_pair_measure)
qed

lemma countably_additiveI[case_names countably]:
  assumes "\<And>A. \<lbrakk> range A \<subseteq> sets M ; disjoint_family A ; (\<Union>i. A i) \<in> sets M\<rbrakk> \<Longrightarrow>
    (\<Sum>n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
  shows "countably_additive M \<mu>"
  using assms unfolding countably_additive_def by auto

lemma (in prob_space) joint_distribution_prob_space:
  assumes "random_variable MX X" "random_variable MY Y"
  shows "prob_space ((MX \<Otimes>\<^isub>M MY) \<lparr> measure := ereal \<circ> joint_distribution X Y\<rparr>)"
  using random_variable_pairI[OF assms] by (rule distribution_prob_space)

locale product_prob_space = product_sigma_finite M for M :: "'i \<Rightarrow> ('a, 'b) measure_space_scheme" +
  fixes I :: "'i set"
  assumes prob_space: "\<And>i. prob_space (M i)"

sublocale product_prob_space \<subseteq> M: prob_space "M i" for i
  by (rule prob_space)

locale finite_product_prob_space = finite_product_sigma_finite M I + product_prob_space M I for M I

sublocale finite_product_prob_space \<subseteq> prob_space "\<Pi>\<^isub>M i\<in>I. M i"
proof
  show "measure_space P" ..
  show "measure P (space P) = 1"
    by (simp add: measure_times M.measure_space_1 setprod_1)
qed

lemma (in finite_product_prob_space) prob_times:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> sets (M i)"
  shows "prob (\<Pi>\<^isub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.prob i (X i))"
proof -
  have "ereal (\<mu>' (\<Pi>\<^isub>E i\<in>I. X i)) = \<mu> (\<Pi>\<^isub>E i\<in>I. X i)"
    using X by (intro finite_measure_eq[symmetric] in_P) auto
  also have "\<dots> = (\<Prod>i\<in>I. M.\<mu> i (X i))"
    using measure_times X by simp
  also have "\<dots> = ereal (\<Prod>i\<in>I. M.\<mu>' i (X i))"
    using X by (simp add: M.finite_measure_eq setprod_ereal)
  finally show ?thesis by simp
qed

lemma (in prob_space) random_variable_restrict:
  assumes I: "finite I"
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> random_variable (N i) (X i)"
  shows "random_variable (Pi\<^isub>M I N) (\<lambda>x. \<lambda>i\<in>I. X i x)"
proof
  { fix i assume "i \<in> I"
    with X interpret N: sigma_algebra "N i" by simp
    have "sets (N i) \<subseteq> Pow (space (N i))" by (rule N.space_closed) }
  note N_closed = this
  then show "sigma_algebra (Pi\<^isub>M I N)"
    by (simp add: product_algebra_def)
       (intro sigma_algebra_sigma product_algebra_generator_sets_into_space)
  show "(\<lambda>x. \<lambda>i\<in>I. X i x) \<in> measurable M (Pi\<^isub>M I N)"
    using X by (intro measurable_restrict[OF I N_closed]) auto
qed

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
  shows "finite_prob_space (MX\<lparr>measure := ereal \<circ> distribution X\<rparr>)"
proof -
  interpret X: prob_space "MX\<lparr>measure := ereal \<circ> distribution X\<rparr>"
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
  show "finite_sigma_algebra (MX \<Otimes>\<^isub>M MY)" ..
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

lemma (in prob_space) setsum_distribution:
  assumes X: "finite_random_variable MX X" shows "(\<Sum>a\<in>space MX. distribution X {a}) = 1"
  using setsum_joint_distribution[OF assms, of "\<lparr> space = UNIV, sets = Pow UNIV \<rparr>" "\<lambda>x. ()" "{()}"]
  using sigma_algebra_Pow[of "UNIV::unit set" "()"] by simp

locale pair_finite_prob_space = pair_prob_space M1 M2 + pair_finite_space M1 M2 + M1: finite_prob_space M1 + M2: finite_prob_space M2 for M1 M2

sublocale pair_finite_prob_space \<subseteq> finite_prob_space P by default

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

locale finite_product_finite_prob_space = finite_product_prob_space M I for M I +
  assumes finite_space: "\<And>i. finite_prob_space (M i)"

sublocale finite_product_finite_prob_space \<subseteq> M!: finite_prob_space "M i" using finite_space .

lemma (in finite_product_finite_prob_space) singleton_eq_product:
  assumes x: "x \<in> space P" shows "{x} = (\<Pi>\<^isub>E i\<in>I. {x i})"
proof (safe intro!: ext[of _ x])
  fix y i assume *: "y \<in> (\<Pi> i\<in>I. {x i})" "y \<in> extensional I"
  with x show "y i = x i"
    by (cases "i \<in> I") (auto simp: extensional_def)
qed (insert x, auto)

sublocale finite_product_finite_prob_space \<subseteq> finite_prob_space "Pi\<^isub>M I M"
proof
  show "finite (space P)"
    using finite_index M.finite_space by auto

  { fix x assume "x \<in> space P"
    with this[THEN singleton_eq_product]
    have "{x} \<in> sets P"
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
qed

lemma (in finite_product_finite_prob_space) measure_finite_times:
  "(\<And>i. i \<in> I \<Longrightarrow> X i \<subseteq> space (M i)) \<Longrightarrow> \<mu> (\<Pi>\<^isub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.\<mu> i (X i))"
  by (rule measure_times) simp

lemma (in finite_product_finite_prob_space) measure_singleton_times:
  assumes x: "x \<in> space P" shows "\<mu> {x} = (\<Prod>i\<in>I. M.\<mu> i {x i})"
  unfolding singleton_eq_product[OF x] using x
  by (intro measure_finite_times) auto

lemma (in finite_product_finite_prob_space) prob_finite_times:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<subseteq> space (M i)"
  shows "prob (\<Pi>\<^isub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.prob i (X i))"
proof -
  have "ereal (\<mu>' (\<Pi>\<^isub>E i\<in>I. X i)) = \<mu> (\<Pi>\<^isub>E i\<in>I. X i)"
    using X by (intro finite_measure_eq[symmetric] in_P) auto
  also have "\<dots> = (\<Prod>i\<in>I. M.\<mu> i (X i))"
    using measure_finite_times X by simp
  also have "\<dots> = ereal (\<Prod>i\<in>I. M.\<mu>' i (X i))"
    using X by (simp add: M.finite_measure_eq setprod_ereal)
  finally show ?thesis by simp
qed

lemma (in finite_product_finite_prob_space) prob_singleton_times:
  assumes x: "x \<in> space P"
  shows "prob {x} = (\<Prod>i\<in>I. M.prob i {x i})"
  unfolding singleton_eq_product[OF x] using x
  by (intro prob_finite_times) auto

lemma (in finite_product_finite_prob_space) prob_finite_product:
  "A \<subseteq> space P \<Longrightarrow> prob A = (\<Sum>x\<in>A. \<Prod>i\<in>I. M.prob i {x i})"
  by (auto simp add: finite_measure_singleton prob_singleton_times
           simp del: space_product_algebra
           intro!: setsum_cong prob_singleton_times)

lemma (in prob_space) joint_distribution_finite_prob_space:
  assumes X: "finite_random_variable MX X"
  assumes Y: "finite_random_variable MY Y"
  shows "finite_prob_space ((MX \<Otimes>\<^isub>M MY)\<lparr> measure := ereal \<circ> joint_distribution X Y\<rparr>)"
  by (intro distribution_finite_prob_space finite_random_variable_pairI X Y)

lemma finite_prob_space_eq:
  "finite_prob_space M \<longleftrightarrow> finite_measure_space M \<and> measure M (space M) = 1"
  unfolding finite_prob_space_def finite_measure_space_def prob_space_def prob_space_axioms_def
  by auto

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

lemma (in finite_prob_space) setsum_distribution_cut:
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
  hence two: "real (card (space M)) \<noteq> 0" by fastforce
  from one have three: "prob {x} \<noteq> 0" by fastforce
  thus ?thesis using one two three divide_cancel_right
    by (auto simp:field_simps)
qed

lemma (in prob_space) prob_space_subalgebra:
  assumes "sigma_algebra N" "sets N \<subseteq> sets M" "space N = space M"
    and "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A"
  shows "prob_space N"
proof
  interpret N: measure_space N
    by (rule measure_space_subalgebra[OF assms])
  show "measure_space N" ..
  show "measure N (space N) = 1"
    using assms(4)[OF N.top] by (simp add: assms measure_space_1)
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
    show "measure_space ?P"
    proof
      show "positive ?P (measure ?P)"
      proof (simp add: positive_def, safe)
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
          by (simp add: mult_commute divide_ereal_def)
        moreover have "0 \<le> inverse (\<mu> A)"
          using real_measure[OF `A \<in> events`] by auto
        ultimately show "(\<Sum>i. \<mu> (F i) / \<mu> A) = \<mu> (\<Union>i. F i) / \<mu> A"
          using measure_countably_additive[of F] F
          by (auto simp: suminf_cmult_ereal)
      qed
    qed
    show "measure ?P (space ?P) = 1"
      using real_measure[OF `A \<in> events`] `\<mu> A \<noteq> 0` by auto
  qed
qed

lemma finite_prob_spaceI:
  assumes "finite (space M)" "sets M = Pow(space M)"
    and 1: "measure M (space M) = 1" and "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> measure M {x}"
    and add: "\<And>A B. A \<subseteq> space M \<Longrightarrow> measure M A = (\<Sum>x\<in>A. measure M {x})"
  shows "finite_prob_space M"
proof -
  interpret finite_measure_space M
  proof
    show "measure M (space M) \<noteq> \<infinity>" using 1 by simp
  qed fact+
  show ?thesis by default fact
qed

lemma (in finite_prob_space) distribution_eq_setsum:
  "distribution X A = (\<Sum>x\<in>A \<inter> X ` space M. distribution X {x})"
proof -
  have *: "X -` A \<inter> space M = (\<Union>x\<in>A \<inter> X ` space M. X -` {x} \<inter> space M)"
    by auto
  then show "distribution X A = (\<Sum>x\<in>A \<inter> X ` space M. distribution X {x})"
    using finite_space unfolding distribution_def *
    by (intro finite_measure_finite_Union)
       (auto simp: disjoint_family_on_def)
qed

lemma (in finite_prob_space) distribution_eq_setsum_finite:
  assumes "finite A"
  shows "distribution X A = (\<Sum>x\<in>A. distribution X {x})"
proof -
  note distribution_eq_setsum[of X A]
  also have "(\<Sum>x\<in>A \<inter> X ` space M. distribution X {x}) = (\<Sum>x\<in>A. distribution X {x})"
  proof (intro setsum_mono_zero_cong_left ballI)
    fix i assume "i\<in>A - A \<inter> X ` space M"
    then have "X -` {i} \<inter> space M = {}" by auto
    then show "distribution X {i} = 0"
      by (simp add: distribution_def)
  next
    show "finite A" by fact
  qed simp_all
  finally show ?thesis .
qed

lemma (in finite_prob_space) finite_measure_space:
  fixes X :: "'a \<Rightarrow> 'x"
  shows "finite_measure_space \<lparr>space = X ` space M, sets = Pow (X ` space M), measure = ereal \<circ> distribution X\<rparr>"
    (is "finite_measure_space ?S")
proof (rule finite_measure_spaceI, simp_all)
  show "finite (X ` space M)" using finite_space by simp
next
  fix A assume "A \<subseteq> X ` space M"
  then show "distribution X A = (\<Sum>x\<in>A. distribution X {x})"
    by (subst distribution_eq_setsum) (simp add: Int_absorb2)
qed

lemma (in finite_prob_space) finite_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M, sets = Pow (X ` space M), measure = ereal \<circ> distribution X \<rparr>"
  by (simp add: finite_prob_space_eq finite_measure_space measure_space_1 one_ereal_def)

lemma (in finite_prob_space) finite_product_measure_space:
  fixes X :: "'a \<Rightarrow> 'x" and Y :: "'a \<Rightarrow> 'y"
  assumes "finite s1" "finite s2"
  shows "finite_measure_space \<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2), measure = ereal \<circ> joint_distribution X Y\<rparr>"
    (is "finite_measure_space ?M")
proof (rule finite_measure_spaceI, simp_all)
  show "finite (s1 \<times> s2)"
    using assms by auto
next
  fix A assume "A \<subseteq> (s1 \<times> s2)"
  with assms show "joint_distribution X Y A = (\<Sum>x\<in>A. joint_distribution X Y {x})"
    by (intro distribution_eq_setsum_finite) (auto dest: finite_subset)
qed

lemma (in finite_prob_space) finite_product_measure_space_of_images:
  shows "finite_measure_space \<lparr> space = X ` space M \<times> Y ` space M,
                                sets = Pow (X ` space M \<times> Y ` space M),
                                measure = ereal \<circ> joint_distribution X Y \<rparr>"
  using finite_space by (auto intro!: finite_product_measure_space)

lemma (in finite_prob_space) finite_product_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M \<times> Y ` space M, sets = Pow (X ` space M \<times> Y ` space M),
                       measure = ereal \<circ> joint_distribution X Y \<rparr>"
  (is "finite_prob_space ?S")
proof (simp add: finite_prob_space_eq finite_product_measure_space_of_images one_ereal_def)
  have "X -` X ` space M \<inter> Y -` Y ` space M \<inter> space M = space M" by auto
  thus "joint_distribution X Y (X ` space M \<times> Y ` space M) = 1"
    by (simp add: distribution_def prob_space vimage_Times comp_def measure_space_1)
qed

subsection "Borel Measure on {0 ..< 1}"

definition pborel :: "real measure_space" where
  "pborel = lborel.restricted_space {0 ..< 1}"

lemma space_pborel[simp]:
  "space pborel = {0 ..< 1}"
  unfolding pborel_def by auto

lemma sets_pborel:
  "A \<in> sets pborel \<longleftrightarrow> A \<in> sets borel \<and> A \<subseteq> { 0 ..< 1}"
  unfolding pborel_def by auto

lemma in_pborel[intro, simp]:
  "A \<subseteq> {0 ..< 1} \<Longrightarrow> A \<in> sets borel \<Longrightarrow> A \<in> sets pborel"
  unfolding pborel_def by auto

interpretation pborel: measure_space pborel
  using lborel.restricted_measure_space[of "{0 ..< 1}"]
  by (simp add: pborel_def)

interpretation pborel: prob_space pborel
proof
  show "measure pborel (space pborel) = 1"
    by (simp add: one_ereal_def pborel_def)
qed default

lemma pborel_prob: "pborel.prob A = (if A \<in> sets borel \<and> A \<subseteq> {0 ..< 1} then real (lborel.\<mu> A) else 0)"
  unfolding pborel.\<mu>'_def by (auto simp: pborel_def)

lemma pborel_singelton[simp]: "pborel.prob {a} = 0"
  by (auto simp: pborel_prob)

lemma
  shows pborel_atLeastAtMost[simp]: "pborel.\<mu>' {a .. b} = (if 0 \<le> a \<and> a \<le> b \<and> b < 1 then b - a else 0)"
    and pborel_atLeastLessThan[simp]: "pborel.\<mu>' {a ..< b} = (if 0 \<le> a \<and> a \<le> b \<and> b \<le> 1 then b - a else 0)"
    and pborel_greaterThanAtMost[simp]: "pborel.\<mu>' {a <.. b} = (if 0 \<le> a \<and> a \<le> b \<and> b < 1 then b - a else 0)"
    and pborel_greaterThanLessThan[simp]: "pborel.\<mu>' {a <..< b} = (if 0 \<le> a \<and> a \<le> b \<and> b \<le> 1 then b - a else 0)"
  unfolding pborel_prob
  by (auto simp: atLeastAtMost_subseteq_atLeastLessThan_iff
    greaterThanAtMost_subseteq_atLeastLessThan_iff greaterThanLessThan_subseteq_atLeastLessThan_iff)

lemma pborel_lebesgue_measure:
  "A \<in> sets pborel \<Longrightarrow> pborel.prob A = real (measure lebesgue A)"
  by (simp add: sets_pborel pborel_prob)

lemma pborel_alt:
  "pborel = sigma \<lparr>
    space = {0..<1},
    sets = range (\<lambda>(x,y). {x..<y} \<inter> {0..<1}),
    measure = measure lborel \<rparr>" (is "_ = ?R")
proof -
  have *: "{0..<1::real} \<in> sets borel" by auto
  have **: "op \<inter> {0..<1::real} ` range (\<lambda>(x, y). {x..<y}) = range (\<lambda>(x,y). {x..<y} \<inter> {0..<1})"
    unfolding image_image by (intro arg_cong[where f=range]) auto
  have "pborel = algebra.restricted_space (sigma \<lparr>space=UNIV, sets=range (\<lambda>(a, b). {a ..< b :: real}),
    measure = measure pborel\<rparr>) {0 ..< 1}"
    by (simp add: sigma_def lebesgue_def pborel_def borel_eq_atLeastLessThan lborel_def)
  also have "\<dots> = ?R"
    by (subst restricted_sigma)
       (simp_all add: sets_sigma sigma_sets.Basic ** pborel_def image_eqI[of _ _ "(0,1)"])
  finally show ?thesis .
qed

subsection "Bernoulli space"

definition "bernoulli_space p = \<lparr> space = UNIV, sets = UNIV,
  measure = ereal \<circ> setsum (\<lambda>b. if b then min 1 (max 0 p) else 1 - min 1 (max 0 p)) \<rparr>"

interpretation bernoulli: finite_prob_space "bernoulli_space p" for p
  by (rule finite_prob_spaceI)
     (auto simp: bernoulli_space_def UNIV_bool one_ereal_def setsum_Un_disjoint intro!: setsum_nonneg)

lemma bernoulli_measure:
  "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> bernoulli.prob p B = (\<Sum>b\<in>B. if b then p else 1 - p)"
  unfolding bernoulli.\<mu>'_def unfolding bernoulli_space_def by (auto intro!: setsum_cong)

lemma bernoulli_measure_True: "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> bernoulli.prob p {True} = p"
  and bernoulli_measure_False: "0 \<le> p \<Longrightarrow> p \<le> 1 \<Longrightarrow> bernoulli.prob p {False} = 1 - p"
  unfolding bernoulli_measure by simp_all

end
