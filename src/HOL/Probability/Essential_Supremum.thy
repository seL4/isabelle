(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    Author:  Johannes Hölzl (TUM) -- ported to Limsup
    License: BSD
*)

theory Essential_Supremum
imports "HOL-Analysis.Analysis"
begin

lemma ae_filter_eq_bot_iff: "ae_filter M = bot \<longleftrightarrow> emeasure M (space M) = 0"
  by (simp add: AE_iff_measurable trivial_limit_def)

section \<open>The essential supremum\<close>

text \<open>In this paragraph, we define the essential supremum and give its basic properties. The
essential supremum of a function is its maximum value if one is allowed to throw away a set
of measure $0$. It is convenient to define it to be infinity for non-measurable functions, as
it allows for neater statements in general. This is a prerequisiste to define the space $L^\infty$.\<close>

definition esssup::"'a measure \<Rightarrow> ('a \<Rightarrow> 'b::{second_countable_topology, dense_linorder, linorder_topology, complete_linorder}) \<Rightarrow> 'b"
  where "esssup M f = (if f \<in> borel_measurable M then Limsup (ae_filter M) f else top)"

lemma esssup_non_measurable: "f \<notin> M \<rightarrow>\<^sub>M borel \<Longrightarrow> esssup M f = top"
  by (simp add: esssup_def)

lemma esssup_eq_AE:
  assumes f: "f \<in> M \<rightarrow>\<^sub>M borel" shows "esssup M f = Inf {z. AE x in M. f x \<le> z}"
  unfolding esssup_def if_P[OF f] Limsup_def
proof (intro antisym INF_greatest Inf_greatest; clarsimp)
  fix y assume "AE x in M. f x \<le> y"
  then have "(\<lambda>x. f x \<le> y) \<in> {P. AE x in M. P x}"
    by simp
  then show "(INF P\<in>{P. AE x in M. P x}. SUP x\<in>Collect P. f x) \<le> y"
    by (rule INF_lower2) (auto intro: SUP_least)
next
  fix P assume P: "AE x in M. P x"
  show "Inf {z. AE x in M. f x \<le> z} \<le> (SUP x\<in>Collect P. f x)"
  proof (rule Inf_lower; clarsimp)
    show "AE x in M. f x \<le> (SUP x\<in>Collect P. f x)"
      using P by (auto elim: eventually_mono simp: SUP_upper)
  qed
qed

lemma esssup_eq: "f \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> esssup M f = Inf {z. emeasure M {x \<in> space M. f x > z} = 0}"
  by (auto simp add: esssup_eq_AE not_less[symmetric] AE_iff_measurable[OF _ refl] intro!: arg_cong[where f=Inf])

lemma esssup_zero_measure:
  "emeasure M {x \<in> space M. f x > esssup M f} = 0"
proof (cases "esssup M f = top")
  case True
  then show ?thesis by auto
next
  case False
  then have f[measurable]: "f \<in> M \<rightarrow>\<^sub>M borel" unfolding esssup_def by meson
  have "esssup M f < top" using False by (auto simp: less_top)
  have *: "{x \<in> space M. f x > z} \<in> null_sets M" if "z > esssup M f" for z
  proof -
    have "\<exists>w. w < z \<and> emeasure M {x \<in> space M. f x > w} = 0"
      using \<open>z > esssup M f\<close> f by (auto simp: esssup_eq Inf_less_iff)
    then obtain w where "w < z" "emeasure M {x \<in> space M. f x > w} = 0" by auto
    then have a: "{x \<in> space M. f x > w} \<in> null_sets M" by auto
    have b: "{x \<in> space M. f x > z} \<subseteq> {x \<in> space M. f x > w}" using \<open>w < z\<close> by auto
    show ?thesis using null_sets_subset[OF a _ b] by simp
  qed
  obtain u::"nat \<Rightarrow> 'b" where u: "\<And>n. u n > esssup M f" "u \<longlonglongrightarrow> esssup M f"
    using approx_from_above_dense_linorder[OF \<open>esssup M f < top\<close>] by auto
  have "{x \<in> space M. f x > esssup M f} = (\<Union>n. {x \<in> space M. f x > u n})"
    using u apply auto
    apply (metis (mono_tags, lifting) order_tendsto_iff eventually_mono LIMSEQ_unique)
    using less_imp_le less_le_trans by blast
  also have "... \<in> null_sets M"
    using *[OF u(1)] by auto
  finally show ?thesis by auto
qed

lemma esssup_AE: "AE x in M. f x \<le> esssup M f"
proof (cases "f \<in> M \<rightarrow>\<^sub>M borel")
  case True then show ?thesis
    by (intro AE_I[OF _ esssup_zero_measure[of _ f]]) auto
qed (simp add: esssup_non_measurable)

lemma esssup_pos_measure:
  "f \<in> borel_measurable M \<Longrightarrow> z < esssup M f \<Longrightarrow> emeasure M {x \<in> space M. f x > z} > 0"
  using Inf_less_iff mem_Collect_eq not_gr_zero by (force simp: esssup_eq)

lemma esssup_I [intro]: "f \<in> borel_measurable M \<Longrightarrow> AE x in M. f x \<le> c \<Longrightarrow> esssup M f \<le> c"
  unfolding esssup_def by (simp add: Limsup_bounded)

lemma esssup_AE_mono: "f \<in> borel_measurable M \<Longrightarrow> AE x in M. f x \<le> g x \<Longrightarrow> esssup M f \<le> esssup M g"
  by (auto simp: esssup_def Limsup_mono)

lemma esssup_mono: "f \<in> borel_measurable M \<Longrightarrow> (\<And>x. f x \<le> g x) \<Longrightarrow> esssup M f \<le> esssup M g"
  by (rule esssup_AE_mono) auto

lemma esssup_AE_cong:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> AE x in M. f x = g x \<Longrightarrow> esssup M f = esssup M g"
  by (auto simp: esssup_def intro!: Limsup_eq)

lemma esssup_const: "emeasure M (space M) \<noteq> 0 \<Longrightarrow> esssup M (\<lambda>x. c) = c"
  by (simp add: esssup_def Limsup_const ae_filter_eq_bot_iff)

lemma esssup_cmult: assumes "c > (0::real)" shows "esssup M (\<lambda>x. c * f x::ereal) = c * esssup M f"
proof -
  have "(\<lambda>x. ereal c * f x) \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> f \<in> M \<rightarrow>\<^sub>M borel"
  proof (subst measurable_cong)
    fix \<omega> show "f \<omega> = ereal (1/c) * (ereal c * f \<omega>)"
      using \<open>0 < c\<close> by (cases "f \<omega>") auto
  qed auto
  then have "(\<lambda>x. ereal c * f x) \<in> M \<rightarrow>\<^sub>M borel \<longleftrightarrow> f \<in> M \<rightarrow>\<^sub>M borel"
    by(safe intro!: borel_measurable_ereal_times borel_measurable_const)
  with \<open>0<c\<close> show ?thesis
    by (cases "ae_filter M = bot")
       (auto simp: esssup_def bot_ereal_def top_ereal_def Limsup_ereal_mult_left)
qed

lemma esssup_add:
  "esssup M (\<lambda>x. f x + g x::ereal) \<le> esssup M f + esssup M g"
proof (cases "f \<in> borel_measurable M \<and> g \<in> borel_measurable M")
  case True
  then have [measurable]: "(\<lambda>x. f x + g x) \<in> borel_measurable M" by auto
  have "f x + g x \<le> esssup M f + esssup M g" if "f x \<le> esssup M f" "g x \<le> esssup M g" for x
    using that add_mono by auto
  then have "AE x in M. f x + g x \<le> esssup M f + esssup M g"
    using esssup_AE[of f M] esssup_AE[of g M] by auto
  then show ?thesis using esssup_I by auto
next
  case False
  then have "esssup M f + esssup M g = \<infinity>" unfolding esssup_def top_ereal_def by auto
  then show ?thesis by auto
qed

lemma esssup_zero_space:
  "emeasure M (space M) = 0 \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow> esssup M f = (- \<infinity>::ereal)"
  by (simp add: esssup_def ae_filter_eq_bot_iff[symmetric] bot_ereal_def)

end

