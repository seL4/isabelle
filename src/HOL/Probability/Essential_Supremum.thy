(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Essential_Supremum
imports "../Analysis/Analysis"
begin

section {*The essential supremum*}

text {*In this paragraph, we define the essential supremum and give its basic properties. The
essential supremum of a function is its maximum value if one is allowed to throw away a set
of measure $0$. It is convenient to define it to be infinity for non-measurable functions, as
it allows for neater statements in general. This is a prerequisiste to define the space $L^\infty$.*}

definition esssup::"'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> ereal"
  where "esssup M f = (if f \<in> borel_measurable M then Inf {z. emeasure M {x \<in> space M. f x > z} = 0} else \<infinity>)"

lemma esssup_zero_measure:
  "emeasure M {x \<in> space M. f x > esssup M f} = 0"
proof (cases "esssup M f = \<infinity>")
  case True
  then show ?thesis by auto
next
  case False
  then have [measurable]: "f \<in> borel_measurable M" unfolding esssup_def by meson
  have "esssup M f < \<infinity>" using False by auto
  have *: "{x \<in> space M. f x > z} \<in> null_sets M" if "z > esssup M f" for z
  proof -
    have "\<exists>w. w < z \<and> emeasure M {x \<in> space M. f x > w} = 0"
      using `z > esssup M f` unfolding esssup_def apply auto
      by (metis (mono_tags, lifting) Inf_less_iff mem_Collect_eq)
    then obtain w where "w < z" "emeasure M {x \<in> space M. f x > w} = 0" by auto
    then have a: "{x \<in> space M. f x > w} \<in> null_sets M" by auto
    have b: "{x \<in> space M. f x > z} \<subseteq> {x \<in> space M. f x > w}" using `w < z` by auto
    show ?thesis using null_sets_subset[OF a _ b] by simp
  qed
  obtain u::"nat \<Rightarrow> ereal" where u: "\<And>n. u n > esssup M f" "u \<longlonglongrightarrow> esssup M f"
    using approx_from_above_dense_linorder[OF `esssup M f < \<infinity>`] by auto
  have "{x \<in> space M. f x > esssup M f} = (\<Union>n. {x \<in> space M. f x > u n})"
    using u apply auto
    apply (metis (mono_tags, lifting) order_tendsto_iff eventually_mono LIMSEQ_unique)
    using less_imp_le less_le_trans by blast
  also have "... \<in> null_sets M"
    using *[OF u(1)] by auto
  finally show ?thesis by auto
qed

lemma esssup_AE:
  "AE x in M. f x \<le> esssup M f"
proof (cases "f \<in> borel_measurable M")
  case True
  show ?thesis
    apply (rule AE_I[OF _ esssup_zero_measure[of _ f]]) using True by auto
next
  case False
  then have "esssup M f = \<infinity>" unfolding esssup_def by auto
  then show ?thesis by auto
qed

lemma esssup_pos_measure:
  assumes "f \<in> borel_measurable M" "z < esssup M f"
  shows "emeasure M {x \<in> space M. f x > z} > 0"
using assms Inf_less_iff mem_Collect_eq not_gr_zero unfolding esssup_def by force

lemma esssup_non_measurable:
  assumes "f \<notin> borel_measurable M"
  shows "esssup M f = \<infinity>"
using assms unfolding esssup_def by auto

lemma esssup_I [intro]:
  assumes "f \<in> borel_measurable M" "AE x in M. f x \<le> c"
  shows "esssup M f \<le> c"
proof -
  have "emeasure M {x \<in> space M. \<not> f x \<le> c} = 0"
    apply (rule AE_E2[OF assms(2)]) using assms(1) by simp
  then have *: "emeasure M {x \<in> space M. f x > c} = 0"
    by (metis (mono_tags, lifting) Collect_cong not_less)
  show ?thesis unfolding esssup_def using assms apply simp by (rule Inf_lower, simp add: *)
qed

lemma esssup_AE_mono:
  assumes "f \<in> borel_measurable M" "AE x in M. f x \<le> g x"
  shows "esssup M f \<le> esssup M g"
proof (cases "g \<in> borel_measurable M")
  case False
  then show ?thesis unfolding esssup_def by auto
next
  case True
  have "AE x in M. f x \<le> esssup M g"
    using assms(2) esssup_AE[of g M] by auto
  then show ?thesis using esssup_I assms(1) by auto
qed

lemma esssup_mono:
  assumes "f \<in> borel_measurable M" "\<And>x. f x \<le> g x"
  shows "esssup M f \<le> esssup M g"
apply (rule esssup_AE_mono) using assms by auto

lemma esssup_AE_cong:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
      and "AE x in M. f x = g x"
  shows "esssup M f = esssup M g"
proof -
  have "esssup M f \<le> esssup M g"
    using esssup_AE_mono[OF assms(1), of g] assms(3) by (simp add: eq_iff)
  moreover have "esssup M g \<le> esssup M f"
    using esssup_AE_mono[OF assms(2), of f] assms(3) by (simp add: eq_iff)
  ultimately show ?thesis by simp
qed

lemma esssup_const:
  assumes "emeasure M (space M) \<noteq> 0"
  shows "esssup M (\<lambda>x. c) = c"
proof -
  have "emeasure M {x \<in> space M. (\<lambda>x. c) x > z} = (if c > z then emeasure M (space M) else 0)" for z
    by auto
  then have "{z. emeasure M {x \<in> space M. (\<lambda>x. c) x > z} = 0} = {c..}" using assms by auto
  then have "esssup M (\<lambda>x. c) = Inf {c..}" unfolding esssup_def by auto
  then show ?thesis by auto
qed

lemma esssup_cmult:
  assumes "c > (0::real)"
  shows "esssup M (\<lambda>x. c * f x) = c * esssup M f"
proof (cases "f \<in> borel_measurable M")
  case True
  then have a [measurable]: "f \<in> borel_measurable M" by simp
  then have b [measurable]: "(\<lambda>x. c * f x) \<in> borel_measurable M" by simp
  have a: "{x \<in> space M. c * z < c * f x} = {x \<in> space M. z < f x}" for z::ereal
    by (meson assms ereal_less(2) ereal_mult_left_mono ereal_mult_strict_left_mono less_ereal.simps(4) less_imp_le not_less)
  have *: "{z::ereal. emeasure M {x \<in> space M. ereal c * f x > z} = 0} = {c * z| z::ereal. emeasure M {x \<in> space M. f x > z} = 0}"
  proof (auto)
    fix y assume *: "emeasure M {x \<in> space M. y < c * f x} = 0"
    define z where "z = y / c"
    have **: "y = c * z" unfolding z_def using assms by (simp add: ereal_mult_divide)
    then have "y = c * z \<and> emeasure M {x \<in> space M. z < f x} = 0"
      using * unfolding ** unfolding a by auto
    then show "\<exists>z. y = ereal c * z \<and> emeasure M {x \<in> space M. z < f x} = 0"
      by auto
  next
    fix z assume *: "emeasure M {x \<in> space M. z < f x} = 0"
    then show "emeasure M {x \<in> space M. c * z < c * f x} = 0"
        using a by auto
  qed
  have "esssup M (\<lambda>x. c * f x) = Inf {z::ereal. emeasure M {x \<in> space M. c * f x > z} = 0}"
    unfolding esssup_def using b by auto
  also have "... = Inf {c * z| z::ereal. emeasure M {x \<in> space M. f x > z} = 0}"
    using * by auto
  also have "... = ereal c * Inf {z. emeasure M {x \<in> space M. f x > z} = 0}"
    apply (rule ereal_Inf_cmult) using assms by auto
  also have "... = c * esssup M f"
    unfolding esssup_def by auto
  finally show ?thesis by simp
next
  case False
  have "esssup M f = \<infinity>" using False unfolding esssup_def by auto
  then have *: "c * esssup M f = \<infinity>" using assms by (simp add: ennreal_mult_eq_top_iff)
  have "(\<lambda>x. c * f x) \<notin> borel_measurable M"
  proof (rule ccontr)
    assume "\<not> (\<lambda>x. c * f x) \<notin> borel_measurable M"
    then have [measurable]: "(\<lambda>x. c * f x) \<in> borel_measurable M" by simp
    then have "(\<lambda>x. (1/c) * (c * f x)) \<in> borel_measurable M" by measurable
    moreover have "(1/c) * (c * f x) = f x" for x
      by (metis "*" PInfty_neq_ereal(1) divide_inverse divide_self_if ereal_zero_mult mult.assoc mult.commute mult.left_neutral one_ereal_def times_ereal.simps(1) zero_ereal_def)
    ultimately show False using False by auto
  qed
  then have "esssup M (\<lambda>x. c * f x) = \<infinity>" unfolding esssup_def by simp
  then show ?thesis using * by auto
qed

lemma esssup_add:
  "esssup M (\<lambda>x. f x + g x) \<le> esssup M f + esssup M g"
proof (cases "f \<in> borel_measurable M \<and> g \<in> borel_measurable M")
  case True
  then have [measurable]: "(\<lambda>x. f x + g x) \<in> borel_measurable M" by auto
  have "f x + g x \<le> esssup M f + esssup M g" if "f x \<le> esssup M f" "g x \<le> esssup M g" for x
    using that ereal_add_mono by auto
  then have "AE x in M. f x + g x \<le> esssup M f + esssup M g"
    using esssup_AE[of f M] esssup_AE[of g M] by auto
  then show ?thesis using esssup_I by auto
next
  case False
  then have "esssup M f + esssup M g = \<infinity>" unfolding esssup_def by auto
  then show ?thesis by auto
qed

lemma esssup_zero_space:
  assumes "emeasure M (space M) = 0"
          "f \<in> borel_measurable M"
  shows "esssup M f = - \<infinity>"
proof -
  have "emeasure M {x \<in> space M. f x > - \<infinity>} = 0"
    using assms(1) emeasure_mono emeasure_eq_0 by fastforce
  then show ?thesis unfolding esssup_def using assms(2) Inf_eq_MInfty by auto
qed

end

