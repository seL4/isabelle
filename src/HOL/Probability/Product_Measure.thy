theory Product_Measure
imports "~~/src/HOL/Probability/Lebesgue"
begin

definition
  "prod_measure M M' = (\<lambda>a. measure_space.integral M (\<lambda>s0. measure M' ((\<lambda>s1. (s0, s1)) -` a)))"

definition
  "prod_measure_space M M' \<equiv>
    \<lparr> space = space M \<times> space M',
      sets = sets (sigma (space M \<times> space M') (prod_sets (sets M) (sets M'))),
      measure = prod_measure M M' \<rparr>"

lemma prod_measure_times:
  assumes "measure_space M" and "measure_space M'" and a: "a \<in> sets M"
  shows "prod_measure M M' (a \<times> a') = measure M a * measure M' a'"
proof -
  interpret M: measure_space M by fact
  interpret M': measure_space M' by fact

  { fix \<omega>
    have "(\<lambda>\<omega>'. (\<omega>, \<omega>')) -` (a \<times> a') = (if \<omega> \<in> a then a' else {})"
      by auto
    hence "measure M' ((\<lambda>\<omega>'. (\<omega>, \<omega>')) -` (a \<times> a')) =
      measure M' a' * indicator_fn a \<omega>"
      unfolding indicator_fn_def by auto }
  note vimage_eq_indicator = this

  show ?thesis
    unfolding prod_measure_def vimage_eq_indicator
      M.integral_cmul_indicator(1)[OF `a \<in> sets M`]
    by simp
qed



lemma measure_space_finite_prod_measure:
  fixes M :: "('a, 'b) measure_space_scheme"
    and M' :: "('c, 'd) measure_space_scheme"
  assumes "measure_space M" and "measure_space M'"
  and finM: "finite (space M)" "Pow (space M) = sets M"
  and finM': "finite (space M')" "Pow (space M') = sets M'"
  shows "measure_space (prod_measure_space M M')"
proof (rule finite_additivity_sufficient)
  interpret M: measure_space M by fact
  interpret M': measure_space M' by fact

  have measure: "measure_space.measure (prod_measure_space M M') = prod_measure M M'"
    unfolding prod_measure_space_def by simp

  have prod_sets: "prod_sets (sets M) (sets M') \<subseteq> Pow (space M \<times> space M')"
    using M.sets_into_space M'.sets_into_space unfolding prod_sets_def by auto
  show sigma: "sigma_algebra (prod_measure_space M M')" unfolding prod_measure_space_def
    by (rule sigma_algebra_sigma_sets[where a="prod_sets (sets M) (sets M')"])
       (simp_all add: sigma_def prod_sets)

  then interpret sa: sigma_algebra "prod_measure_space M M'" .

  { fix x y assume "y \<in> sets (prod_measure_space M M')" and "x \<in> space M"
    hence "y \<subseteq> space M \<times> space M'"
      using sa.sets_into_space unfolding prod_measure_space_def by simp
    hence "Pair x -` y \<in> sets M'"
      using `x \<in> space M` unfolding finM'(2)[symmetric] by auto }
  note Pair_in_sets = this

  show "additive (prod_measure_space M M') (measure (prod_measure_space M M'))"
    unfolding measure additive_def
  proof safe
    fix x y assume x: "x \<in> sets (prod_measure_space M M')" and y: "y \<in> sets (prod_measure_space M M')"
      and disj_x_y: "x \<inter> y = {}"
    { fix z have "Pair z -` x \<inter> Pair z -` y = {}" using disj_x_y by auto }
    note Pair_disj = this

    from M'.measure_additive[OF Pair_in_sets[OF x] Pair_in_sets[OF y] Pair_disj, symmetric]
    show "prod_measure M M' (x \<union> y) = prod_measure M M' x + prod_measure M M' y"
      unfolding prod_measure_def
      apply (subst (1 2 3) M.integral_finite_singleton[OF finM])
      by (simp_all add: setsum_addf[symmetric] field_simps)
  qed

  show "finite (space (prod_measure_space M M'))"
    unfolding prod_measure_space_def using finM finM' by simp

  have singletonM: "\<And>x. x \<in> space M \<Longrightarrow> {x} \<in> sets M"
    unfolding finM(2)[symmetric] by simp

  show "positive (prod_measure_space M M') (measure (prod_measure_space M M'))"
    unfolding positive_def
  proof (safe, simp add: M.integral_zero prod_measure_space_def prod_measure_def)
    fix Q assume "Q \<in> sets (prod_measure_space M M')"
    from Pair_in_sets[OF this]
    show "0 \<le> measure (prod_measure_space M M') Q"
      unfolding prod_measure_space_def prod_measure_def
      apply (subst M.integral_finite_singleton[OF finM])
      using M.positive M'.positive singletonM
      by (auto intro!: setsum_nonneg mult_nonneg_nonneg)
  qed
qed

lemma measure_space_finite_prod_measure_alterantive:
  assumes "measure_space M" and "measure_space M'"
  and finM: "finite (space M)" "Pow (space M) = sets M"
  and finM': "finite (space M')" "Pow (space M') = sets M'"
  shows "measure_space \<lparr> space = space M \<times> space M',
                         sets = Pow (space M \<times> space M'),
		         measure = prod_measure M M' \<rparr>"
  (is "measure_space ?space")
proof (rule finite_additivity_sufficient)
  interpret M: measure_space M by fact
  interpret M': measure_space M' by fact

  show "sigma_algebra ?space"
    using sigma_algebra.sigma_algebra_extend[where M="\<lparr> space = space M \<times> space M', sets = Pow (space M \<times> space M') \<rparr>"]
    by (auto intro!: sigma_algebra_Pow)
  then interpret sa: sigma_algebra ?space .

  have measure: "measure_space.measure (prod_measure_space M M') = prod_measure M M'"
    unfolding prod_measure_space_def by simp

  { fix x y assume "y \<in> sets ?space" and "x \<in> space M"
    hence "y \<subseteq> space M \<times> space M'"
      using sa.sets_into_space by simp
    hence "Pair x -` y \<in> sets M'"
      using `x \<in> space M` unfolding finM'(2)[symmetric] by auto }
  note Pair_in_sets = this

  show "additive ?space (measure ?space)"
    unfolding measure additive_def
  proof safe
    fix x y assume x: "x \<in> sets ?space" and y: "y \<in> sets ?space"
      and disj_x_y: "x \<inter> y = {}"
    { fix z have "Pair z -` x \<inter> Pair z -` y = {}" using disj_x_y by auto }
    note Pair_disj = this

    from M'.measure_additive[OF Pair_in_sets[OF x] Pair_in_sets[OF y] Pair_disj, symmetric]
    show "measure ?space (x \<union> y) = measure ?space x + measure ?space y"
      apply (simp add: prod_measure_def)
      apply (subst (1 2 3) M.integral_finite_singleton[OF finM])
      by (simp_all add: setsum_addf[symmetric] field_simps)
  qed

  show "finite (space ?space)" using finM finM' by simp

  have singletonM: "\<And>x. x \<in> space M \<Longrightarrow> {x} \<in> sets M"
    unfolding finM(2)[symmetric] by simp

  show "positive ?space (measure ?space)"
    unfolding positive_def
  proof (safe, simp add: M.integral_zero prod_measure_def)
    fix Q assume "Q \<in> sets ?space"
    from Pair_in_sets[OF this]
    show "0 \<le> measure ?space Q"
      unfolding prod_measure_space_def prod_measure_def
      apply (subst M.integral_finite_singleton[OF finM])
      using M.positive M'.positive singletonM
      by (auto intro!: setsum_nonneg mult_nonneg_nonneg)
  qed
qed

end