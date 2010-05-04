theory Product_Measure
imports Lebesgue
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

lemma finite_prod_measure_space:
  assumes "finite_measure_space M" and "finite_measure_space M'"
  shows "prod_measure_space M M' =
      \<lparr> space = space M \<times> space M',
        sets = Pow (space M \<times> space M'),
        measure = prod_measure M M' \<rparr>"
proof -
  interpret M: finite_measure_space M by fact
  interpret M': finite_measure_space M' by fact
  show ?thesis using M.finite_space M'.finite_space
    by (simp add: sigma_prod_sets_finite M.sets_eq_Pow M'.sets_eq_Pow
      prod_measure_space_def)
qed

lemma finite_measure_space_finite_prod_measure:
  assumes "finite_measure_space M" and "finite_measure_space M'"
  shows "finite_measure_space (prod_measure_space M M')"
proof (rule finite_Pow_additivity_sufficient)
  interpret M: finite_measure_space M by fact
  interpret M': finite_measure_space M' by fact

  from M.finite_space M'.finite_space
  show "finite (space (prod_measure_space M M'))" and
    "sets (prod_measure_space M M') = Pow (space (prod_measure_space M M'))"
    by (simp_all add: finite_prod_measure_space[OF assms])

  show "additive (prod_measure_space M M') (measure (prod_measure_space M M'))"
    unfolding additive_def finite_prod_measure_space[OF assms]
  proof (simp, safe)
    fix x y assume subs: "x \<subseteq> space M \<times> space M'" "y \<subseteq> space M \<times> space M'"
      and disj_x_y: "x \<inter> y = {}"
    have "\<And>z. measure M' (Pair z -` x \<union> Pair z -` y) =
        measure M' (Pair z -` x) + measure M' (Pair z -` y)"
      using disj_x_y subs by (subst M'.measure_additive) (auto simp: M'.sets_eq_Pow)
    thus "prod_measure M M' (x \<union> y) = prod_measure M M' x + prod_measure M M' y"
      unfolding prod_measure_def M.integral_finite_singleton
      by (simp_all add: setsum_addf[symmetric] field_simps)
  qed

  show "positive (prod_measure_space M M') (measure (prod_measure_space M M'))"
    unfolding positive_def
    by (auto intro!: setsum_nonneg mult_nonneg_nonneg M'.positive M.positive
      simp add: M.integral_zero finite_prod_measure_space[OF assms]
        prod_measure_def M.integral_finite_singleton
        M.sets_eq_Pow M'.sets_eq_Pow)
qed

lemma finite_measure_space_finite_prod_measure_alterantive:
  assumes M: "finite_measure_space M" and M': "finite_measure_space M'"
  shows "finite_measure_space \<lparr> space = space M \<times> space M', sets = Pow (space M \<times> space M'), measure = prod_measure M M' \<rparr>"
    (is "finite_measure_space ?M")
proof -
  interpret M: finite_measure_space M by fact
  interpret M': finite_measure_space M' by fact

  show ?thesis
    using finite_measure_space_finite_prod_measure[OF assms]
    unfolding prod_measure_space_def M.sets_eq_Pow M'.sets_eq_Pow
    using M.finite_space M'.finite_space
    by (simp add: sigma_prod_sets_finite)
qed

end