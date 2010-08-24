theory Product_Measure
imports Lebesgue_Integration
begin

definition prod_sets where
  "prod_sets A B = {z. \<exists>x \<in> A. \<exists>y \<in> B. z = x \<times> y}"

definition
  "prod_measure M \<mu> N \<nu> = (\<lambda>A. measure_space.positive_integral M \<mu> (\<lambda>s0. \<nu> ((\<lambda>s1. (s0, s1)) -` A)))"

definition
  "prod_measure_space M1 M2 = sigma (space M1 \<times> space M2) (prod_sets (sets M1) (sets M2))"

lemma prod_setsI: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> (x \<times> y) \<in> prod_sets A B"
  by (auto simp add: prod_sets_def)

lemma sigma_prod_sets_finite:
  assumes "finite A" and "finite B"
  shows "sigma_sets (A \<times> B) (prod_sets (Pow A) (Pow B)) = Pow (A \<times> B)"
proof safe
  have fin: "finite (A \<times> B)" using assms by (rule finite_cartesian_product)

  fix x assume subset: "x \<subseteq> A \<times> B"
  hence "finite x" using fin by (rule finite_subset)
  from this subset show "x \<in> sigma_sets (A\<times>B) (prod_sets (Pow A) (Pow B))"
    (is "x \<in> sigma_sets ?prod ?sets")
  proof (induct x)
    case empty show ?case by (rule sigma_sets.Empty)
  next
    case (insert a x)
    hence "{a} \<in> sigma_sets ?prod ?sets" by (auto simp: prod_sets_def intro!: sigma_sets.Basic)
    moreover have "x \<in> sigma_sets ?prod ?sets" using insert by auto
    ultimately show ?case unfolding insert_is_Un[of a x] by (rule sigma_sets_Un)
  qed
next
  fix x a b
  assume "x \<in> sigma_sets (A\<times>B) (prod_sets (Pow A) (Pow B))" and "(a, b) \<in> x"
  from sigma_sets_into_sp[OF _ this(1)] this(2)
  show "a \<in> A" and "b \<in> B"
    by (auto simp: prod_sets_def)
qed

lemma (in sigma_algebra) measurable_prod_sigma:
  assumes sa1: "sigma_algebra a1" and sa2: "sigma_algebra a2"
  assumes 1: "(fst o f) \<in> measurable M a1" and 2: "(snd o f) \<in> measurable M a2"
  shows "f \<in> measurable M (sigma ((space a1) \<times> (space a2))
                          (prod_sets (sets a1) (sets a2)))"
proof -
  from 1 have fn1: "fst \<circ> f \<in> space M \<rightarrow> space a1"
     and q1: "\<forall>y\<in>sets a1. (fst \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def)
  from 2 have fn2: "snd \<circ> f \<in> space M \<rightarrow> space a2"
     and q2: "\<forall>y\<in>sets a2. (snd \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def)
  show ?thesis
    proof (rule measurable_sigma)
      show "prod_sets (sets a1) (sets a2) \<subseteq> Pow (space a1 \<times> space a2)" using sa1 sa2
        by (auto simp add: prod_sets_def sigma_algebra_iff dest: algebra.space_closed)
    next
      show "f \<in> space M \<rightarrow> space a1 \<times> space a2"
        by (rule prod_final [OF fn1 fn2])
    next
      fix z
      assume z: "z \<in> prod_sets (sets a1) (sets a2)"
      thus "f -` z \<inter> space M \<in> sets M"
        proof (auto simp add: prod_sets_def vimage_Times)
          fix x y
          assume x: "x \<in> sets a1" and y: "y \<in> sets a2"
          have "(fst \<circ> f) -` x \<inter> (snd \<circ> f) -` y \<inter> space M =
                ((fst \<circ> f) -` x \<inter> space M) \<inter> ((snd \<circ> f) -` y \<inter> space M)"
            by blast
          also have "...  \<in> sets M" using x y q1 q2
            by blast
          finally show "(fst \<circ> f) -` x \<inter> (snd \<circ> f) -` y \<inter> space M \<in> sets M" .
        qed
    qed
qed

lemma (in sigma_finite_measure) prod_measure_times:
  assumes "sigma_finite_measure N \<nu>"
  and "A1 \<in> sets M" "A2 \<in> sets N"
  shows "prod_measure M \<mu> N \<nu> (A1 \<times> A2) = \<mu> A1 * \<nu> A2"
  oops

lemma (in sigma_finite_measure) sigma_finite_prod_measure_space:
  assumes "sigma_finite_measure N \<nu>"
  shows "sigma_finite_measure (prod_measure_space M N) (prod_measure M \<mu> N \<nu>)"
  oops

lemma (in finite_measure_space) simple_function_finite:
  "simple_function f"
  unfolding simple_function_def sets_eq_Pow using finite_space by auto

lemma (in finite_measure_space) borel_measurable_finite[intro, simp]: "f \<in> borel_measurable M"
  unfolding measurable_def sets_eq_Pow by auto

lemma (in finite_measure_space) positive_integral_finite_eq_setsum:
  "positive_integral f = (\<Sum>x \<in> space M. f x * \<mu> {x})"
proof -
  have *: "positive_integral f = positive_integral (\<lambda>x. \<Sum>y\<in>space M. f y * indicator {y} x)"
    by (auto intro!: positive_integral_cong simp add: indicator_def if_distrib setsum_cases[OF finite_space])
  show ?thesis unfolding * using borel_measurable_finite[of f]
    by (simp add: positive_integral_setsum positive_integral_cmult_indicator sets_eq_Pow)
qed

lemma (in finite_measure_space) finite_prod_measure_times:
  assumes "finite_measure_space N \<nu>"
  and "A1 \<in> sets M" "A2 \<in> sets N"
  shows "prod_measure M \<mu> N \<nu> (A1 \<times> A2) = \<mu> A1 * \<nu> A2"
proof -
  interpret N: finite_measure_space N \<nu> by fact
  have *: "\<And>x. \<nu> (Pair x -` (A1 \<times> A2)) * \<mu> {x} = (if x \<in> A1 then \<nu> A2 * \<mu> {x} else 0)"
    by (auto simp: vimage_Times comp_def)
  have "finite A1"
    using `A1 \<in> sets M` finite_space by (auto simp: sets_eq_Pow intro: finite_subset)
  then have "\<mu> A1 = (\<Sum>x\<in>A1. \<mu> {x})" using `A1 \<in> sets M`
    by (auto intro!: measure_finite_singleton simp: sets_eq_Pow)
  then show ?thesis using `A1 \<in> sets M`
    unfolding prod_measure_def positive_integral_finite_eq_setsum *
    by (auto simp add: sets_eq_Pow setsum_right_distrib[symmetric] mult_commute setsum_cases[OF finite_space])
qed

lemma (in finite_measure_space) finite_prod_measure_space:
  assumes "finite_measure_space N \<nu>"
  shows "prod_measure_space M N = \<lparr> space = space M \<times> space N, sets = Pow (space M \<times> space N) \<rparr>"
proof -
  interpret N: finite_measure_space N \<nu> by fact
  show ?thesis using finite_space N.finite_space
    by (simp add: sigma_def prod_measure_space_def sigma_prod_sets_finite sets_eq_Pow N.sets_eq_Pow)
qed

lemma (in finite_measure_space) finite_measure_space_finite_prod_measure:
  assumes "finite_measure_space N \<nu>"
  shows "finite_measure_space (prod_measure_space M N) (prod_measure M \<mu> N \<nu>)"
  unfolding finite_prod_measure_space[OF assms]
proof (rule finite_measure_spaceI)
  interpret N: finite_measure_space N \<nu> by fact

  let ?P = "\<lparr>space = space M \<times> space N, sets = Pow (space M \<times> space N)\<rparr>"
  show "measure_space ?P (prod_measure M \<mu> N \<nu>)"
  proof (rule sigma_algebra.finite_additivity_sufficient)
    show "sigma_algebra ?P" by (rule sigma_algebra_Pow)
    show "finite (space ?P)" using finite_space N.finite_space by auto
    from finite_prod_measure_times[OF assms, of "{}" "{}"]
    show "positive (prod_measure M \<mu> N \<nu>)"
      unfolding positive_def by simp

    show "additive ?P (prod_measure M \<mu> N \<nu>)"
      unfolding additive_def
      apply (auto simp add: sets_eq_Pow prod_measure_def positive_integral_add[symmetric]
                  intro!: positive_integral_cong)
      apply (subst N.measure_additive[symmetric])
      by (auto simp: N.sets_eq_Pow sets_eq_Pow)
  qed
  show "finite (space ?P)" using finite_space N.finite_space by auto
  show "sets ?P = Pow (space ?P)" by simp

  fix x assume "x \<in> space ?P"
  with finite_prod_measure_times[OF assms, of "{fst x}" "{snd x}"]
    finite_measure[of "{fst x}"] N.finite_measure[of "{snd x}"]
  show "prod_measure M \<mu> N \<nu> {x} \<noteq> \<omega>"
    by (auto simp add: sets_eq_Pow N.sets_eq_Pow elim!: SigmaE)
qed

lemma (in finite_measure_space) finite_measure_space_finite_prod_measure_alterantive:
  assumes N: "finite_measure_space N \<nu>"
  shows "finite_measure_space \<lparr> space = space M \<times> space N, sets = Pow (space M \<times> space N) \<rparr> (prod_measure M \<mu> N \<nu>)"
    (is "finite_measure_space ?M ?m")
  unfolding finite_prod_measure_space[OF N, symmetric]
  using finite_measure_space_finite_prod_measure[OF N] .

end