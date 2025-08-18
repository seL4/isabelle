(*  Title:      HOL/Analysis/Set_Integral.thy
    Author:     Jeremy Avigad (CMU), Johannes Hölzl (TUM), Luke Serafin (CMU)
    Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    Author:     Ata Keskin, TU Muenchen

Notation and useful facts for working with integrals over a set.

TODO: keep all these? Need unicode translations as well.
*)

chapter \<open>Integrals over a Set\<close>

theory Set_Integral
  imports Radon_Nikodym
begin

section \<open>Notation\<close>

definition\<^marker>\<open>tag important\<close> "set_borel_measurable M A f \<equiv> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"

definition\<^marker>\<open>tag important\<close>  "set_integrable M A f \<equiv> integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"

definition\<^marker>\<open>tag important\<close>  "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. indicator A x *\<^sub>R f x)"

syntax
  "_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  (\<open>(\<open>indent=4 notation=\<open>binder LINT\<close>\<close>LINT (_):(_)/|(_)./ _)\<close> [0,0,0,10] 10)
syntax_consts
  "_ascii_set_lebesgue_integral" == set_lebesgue_integral
translations
  "LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"


section \<open>Basic properties\<close>

lemma set_integrable_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "set_integrable M \<Omega> f = integrable (restrict_space M \<Omega>) f"
  by (meson assms integrable_restrict_space set_integrable_def)

lemma set_integrable_cong:
  assumes "M = M'" "A = A'" "\<And>x. x \<in> A \<Longrightarrow> f x = f' x"
  shows   "set_integrable M A f = set_integrable M' A' f'"
proof -
  have "(\<lambda>x. indicator A x *\<^sub>R f x) = (\<lambda>x. indicator A' x *\<^sub>R f' x)"
    using assms by (auto simp: indicator_def of_bool_def)
  thus ?thesis by (simp add: set_integrable_def assms)
qed

lemma set_borel_measurable_sets:
  fixes f :: "_ \<Rightarrow> _::real_normed_vector"
  assumes "set_borel_measurable M X f" "B \<in> sets borel" "X \<in> sets M"
  shows "f -` B \<inter> X \<in> sets M"
proof -
  have "f \<in> borel_measurable (restrict_space M X)"
    using assms unfolding set_borel_measurable_def by (subst borel_measurable_restrict_space_iff) auto
  then have "f -` B \<inter> space (restrict_space M X) \<in> sets (restrict_space M X)"
    by (rule measurable_sets) fact
  with \<open>X \<in> sets M\<close> show ?thesis
    by (subst (asm) sets_restrict_space_iff) (auto simp: space_restrict_space)
qed

lemma set_integrable_bound:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and g :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_borel_measurable M A g"
  assumes "AE x in M. x \<in> A \<longrightarrow> norm (g x) \<le> norm (f x)"
  shows   "set_integrable M A g"
  unfolding set_integrable_def
proof (rule Bochner_Integration.integrable_bound)
  from assms(1) show "integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"
    by (simp add: set_integrable_def)
  from assms(2) show "(\<lambda>x. indicat_real A x *\<^sub>R g x) \<in> borel_measurable M"
    by (simp add: set_borel_measurable_def)
  from assms(3) show "AE x in M. norm (indicat_real A x *\<^sub>R g x) \<le> norm (indicat_real A x *\<^sub>R f x)"
    by eventually_elim (simp add: indicator_def)
qed

lemma set_lebesgue_integral_zero [simp]: "set_lebesgue_integral M A (\<lambda>x. 0) = 0"
  by (auto simp: set_lebesgue_integral_def)

lemma set_lebesgue_integral_cong:
  assumes "A \<in> sets M" and "\<forall>x. x \<in> A \<longrightarrow> f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
  unfolding set_lebesgue_integral_def
  using assms
  by (metis indicator_simps(2) real_vector.scale_zero_left)

lemma set_lebesgue_integral_cong_AE:
  assumes [measurable]: "A \<in> sets M" "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "AE x \<in> A in M. f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
proof-
  have "AE x in M. indicator A x *\<^sub>R f x = indicator A x *\<^sub>R g x"
    using assms by auto
  thus ?thesis
  unfolding set_lebesgue_integral_def by (intro integral_cong_AE) auto
qed

lemma set_integrable_cong_AE:
    "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    AE x \<in> A in M. f x = g x \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A f = set_integrable M A g"
  unfolding set_integrable_def
  by (rule integrable_cong_AE) auto

lemma set_integrable_subset:
  fixes M A B and f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"
  shows "set_integrable M B f"
proof -
  have "set_integrable M B (\<lambda>x. indicator A x *\<^sub>R f x)"
    using assms integrable_mult_indicator set_integrable_def by blast
  with \<open>B \<subseteq> A\<close> show ?thesis
    unfolding set_integrable_def
    by (simp add: indicator_inter_arith[symmetric] Int_absorb2)
qed

lemma set_integrable_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f: "set_integrable M S f" and T: "T \<in> sets (restrict_space M S)"
  shows "set_integrable M T f"
proof -
  obtain T' where T_eq: "T = S \<inter> T'" and "T' \<in> sets M" 
    using T by (auto simp: sets_restrict_space)
  have \<open>integrable M (\<lambda>x. indicator T' x *\<^sub>R (indicator S x *\<^sub>R f x))\<close>
    using \<open>T' \<in> sets M\<close> f integrable_mult_indicator set_integrable_def by blast
  then show ?thesis
    unfolding set_integrable_def
    unfolding T_eq indicator_inter_arith by (simp add: ac_simps)
qed

(* TODO: integral_cmul_indicator should be named set_integral_const *)
(* TODO: borel_integrable_atLeastAtMost should be named something like set_integrable_Icc_isCont *)

lemma set_integral_scaleR_left: 
  assumes "A \<in> sets M" "c \<noteq> 0 \<Longrightarrow> integrable M f"
  shows "(LINT t:A|M. f t *\<^sub>R c) = (LINT t:A|M. f t) *\<^sub>R c"
  unfolding set_lebesgue_integral_def 
  using integrable_mult_indicator[OF assms]
  by (subst integral_scaleR_left[symmetric], auto)

lemma set_integral_scaleR_right [simp]: "(LINT t:A|M. a *\<^sub>R f t) = a *\<^sub>R (LINT t:A|M. f t)"
  unfolding set_lebesgue_integral_def
  by (subst integral_scaleR_right[symmetric]) (auto intro!: Bochner_Integration.integral_cong)

lemma set_integral_mult_right [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(LINT t:A|M. a * f t) = a * (LINT t:A|M. f t)"
  unfolding set_lebesgue_integral_def
  by (subst integral_mult_right_zero[symmetric]) auto

lemma set_integral_mult_left [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(LINT t:A|M. f t * a) = (LINT t:A|M. f t) * a"
  unfolding set_lebesgue_integral_def
  by (subst integral_mult_left_zero[symmetric]) auto

lemma set_integral_divide_zero [simp]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  shows "(LINT t:A|M. f t / a) = (LINT t:A|M. f t) / a"
  unfolding set_lebesgue_integral_def
  by (subst integral_divide_zero[symmetric], intro Bochner_Integration.integral_cong)
     (auto split: split_indicator)

lemma set_integrable_scaleR_right [simp, intro]:
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a *\<^sub>R f t)"
  unfolding set_integrable_def
  unfolding scaleR_left_commute by (rule integrable_scaleR_right)

lemma set_integrable_scaleR_left [simp, intro]:
  fixes a :: "_ :: {banach, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t *\<^sub>R a)"
  unfolding set_integrable_def
  using integrable_scaleR_left[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_right [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a * f t)"
  unfolding set_integrable_def
  using integrable_mult_right[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_right_iff [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  assumes "a \<noteq> 0"
  shows "set_integrable M A (\<lambda>t. a * f t) \<longleftrightarrow> set_integrable M A f"
proof
  assume "set_integrable M A (\<lambda>t. a * f t)"
  then have "set_integrable M A (\<lambda>t. 1/a * (a * f t))"
    using set_integrable_mult_right by blast
  then show "set_integrable M A f"
    using assms by auto
qed auto

lemma set_integrable_mult_left [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t * a)"
  unfolding set_integrable_def
  using integrable_mult_left[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_left_iff [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  assumes "a \<noteq> 0"
  shows "set_integrable M A (\<lambda>t. f t * a) \<longleftrightarrow> set_integrable M A f"
  using assms by (subst set_integrable_mult_right_iff [symmetric]) (auto simp: mult.commute)

lemma set_integrable_divide [simp, intro]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  assumes "a \<noteq> 0 \<Longrightarrow> set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. f t / a)"
proof -
  have "integrable M (\<lambda>x. indicator A x *\<^sub>R f x / a)"
    using assms unfolding set_integrable_def by (rule integrable_divide_zero)
  also have "(\<lambda>x. indicator A x *\<^sub>R f x / a) = (\<lambda>x. indicator A x *\<^sub>R (f x / a))"
    by (auto split: split_indicator)
  finally show ?thesis 
    unfolding set_integrable_def .
qed

lemma set_integrable_mult_divide_iff [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  assumes "a \<noteq> 0"
  shows "set_integrable M A (\<lambda>t. f t / a) \<longleftrightarrow> set_integrable M A f"
  by (simp add: divide_inverse assms)

lemma set_integral_add [simp, intro]:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x + g x)"
    and "(LINT x:A|M. f x + g x) = (LINT x:A|M. f x) + (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def by (simp_all add: scaleR_add_right)

lemma set_integral_diff [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x - g x)" and "(LINT x:A|M. f x - g x) = (LINT x:A|M. f x) - (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def by (simp_all add: scaleR_diff_right)

lemma set_integral_uminus: "set_integrable M A f \<Longrightarrow> (LINT x:A|M. - f x) = - (LINT x:A|M. f x)"
  unfolding set_integrable_def set_lebesgue_integral_def
  by (subst integral_minus[symmetric]) simp_all

lemma set_integral_complex_of_real:
  "(LINT x:A|M. complex_of_real (f x)) = of_real (LINT x:A|M. f x)"
  unfolding set_lebesgue_integral_def
  by (subst integral_complex_of_real[symmetric])
     (auto intro!: Bochner_Integration.integral_cong split: split_indicator)

lemma set_integral_mono:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def
  by (auto intro: integral_mono split: split_indicator)

lemma set_integral_mono_AE:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "AE x \<in> A in M. f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def
  by (auto intro: integral_mono_AE split: split_indicator)

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar> :: real)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"]unfolding set_integrable_def by (simp add: abs_mult ac_simps)

lemma set_integrable_abs_iff:
  fixes f :: "_ \<Rightarrow> real"
  shows "set_borel_measurable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
  unfolding set_integrable_def set_borel_measurable_def
  by (subst (2) integrable_abs_iff[symmetric]) (simp_all add: abs_mult ac_simps)

lemma set_integrable_abs_iff':
  fixes f :: "_ \<Rightarrow> real"
  shows "f \<in> borel_measurable M \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
  by (simp add: set_borel_measurable_def set_integrable_abs_iff)

lemma set_integrable_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_integrable M A f \<longleftrightarrow> set_integrable M B f"
  unfolding set_integrable_def
proof (rule integrable_discrete_difference[where X=X])
  show "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> X \<Longrightarrow> indicator A x *\<^sub>R f x = indicator B x *\<^sub>R f x"
    using diff by (auto split: split_indicator)
qed fact+

lemma set_integral_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_lebesgue_integral M A f = set_lebesgue_integral M B f"
  unfolding set_lebesgue_integral_def
proof (rule integral_discrete_difference[where X=X])
  show "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> X \<Longrightarrow> indicator A x *\<^sub>R f x = indicator B x *\<^sub>R f x"
    using diff by (auto split: split_indicator)
qed fact+

lemma set_integrable_Un:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes f_A: "set_integrable M A f" and f_B:  "set_integrable M B f"
    and [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "set_integrable M (A \<union> B) f"
proof -
  have "set_integrable M (A - B) f"
    using f_A by (rule set_integrable_subset) auto
  with f_B have "integrable M (\<lambda>x. indicator (A - B) x *\<^sub>R f x + indicator B x *\<^sub>R f x)"
    unfolding set_integrable_def using integrable_add by blast
  then show ?thesis
    unfolding set_integrable_def
    by (rule integrable_cong[THEN iffD1, rotated 2]) (auto split: split_indicator)
qed

lemma set_integrable_empty [simp]: "set_integrable M {} f"
  by (auto simp: set_integrable_def)

lemma set_integrable_UN:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
    "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
  using assms
  by (induct I) (auto simp: set_integrable_Un sets.finite_UN)

lemma set_integral_Un:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
shows "(LINT x:A\<union>B|M. f x) = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  using assms
  unfolding set_integrable_def set_lebesgue_integral_def
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric] scaleR_add_left)

lemma set_integral_cong_set:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_borel_measurable M A f" "set_borel_measurable M B f"
    and ae: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "(LINT x:B|M. f x) = (LINT x:A|M. f x)"
  unfolding set_lebesgue_integral_def
proof (rule integral_cong_AE)
  show "AE x in M. indicator B x *\<^sub>R f x = indicator A x *\<^sub>R f x"
    using ae by (auto simp: subset_eq split: split_indicator)
qed (use assms in \<open>auto simp: set_borel_measurable_def\<close>)

proposition set_borel_measurable_subset:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "set_borel_measurable M A f" "B \<in> sets M" and "B \<subseteq> A"
  shows "set_borel_measurable M B f"
proof-
  have "set_borel_measurable M B (\<lambda>x. indicator A x *\<^sub>R f x)"
    using assms unfolding set_borel_measurable_def
    using borel_measurable_indicator borel_measurable_scaleR by blast 
  moreover have "(\<lambda>x. indicator B x *\<^sub>R indicator A x *\<^sub>R f x) = (\<lambda>x. indicator B x *\<^sub>R f x)"
    using \<open>B \<subseteq> A\<close> by (auto simp: fun_eq_iff split: split_indicator)
  ultimately show ?thesis 
    unfolding set_borel_measurable_def by simp
qed

lemma set_integral_Un_AE:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes ae: "AE x in M. \<not> (x \<in> A \<and> x \<in> B)" and [measurable]: "A \<in> sets M" "B \<in> sets M"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "(LINT x:A\<union>B|M. f x) = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
proof -
  have f: "set_integrable M (A \<union> B) f"
    by (intro set_integrable_Un assms)
  then have f': "set_borel_measurable M (A \<union> B) f"
    using integrable_iff_bounded set_borel_measurable_def set_integrable_def by blast
  have "(LINT x:A\<union>B|M. f x) = (LINT x:(A - A \<inter> B) \<union> (B - A \<inter> B)|M. f x)"
  proof (rule set_integral_cong_set)
    show "AE x in M. (x \<in> A - A \<inter> B \<union> (B - A \<inter> B)) = (x \<in> A \<union> B)"
      using ae by auto
    show "set_borel_measurable M (A - A \<inter> B \<union> (B - A \<inter> B)) f"
      using f' by (rule set_borel_measurable_subset) auto
  qed fact
  also have "\<dots> = (LINT x:(A - A \<inter> B)|M. f x) + (LINT x:(B - A \<inter> B)|M. f x)"
    by (auto intro!: set_integral_Un set_integrable_subset[OF f])
  also have "\<dots> = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
    using ae
    by (intro arg_cong2[where f="(+)"] set_integral_cong_set)
       (auto intro!: set_borel_measurable_subset[OF f'])
  finally show ?thesis .
qed

lemma set_integral_finite_Union:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using assms
proof induction
  case (insert x F)
  then have "A x \<inter> \<Union>(A ` F) = {}"
    by (meson disjoint_family_on_insert)
  with insert show ?case
    by (simp add: set_integral_Un set_integrable_Un set_integrable_UN disjoint_family_on_insert)
qed (simp add: set_lebesgue_integral_def)

(* TODO: find a better name? *)
lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) \<longlonglongrightarrow> l"
shows "set_integrable M (\<Union>i. A i) f"
  unfolding set_integrable_def
  apply (rule integrable_monotone_convergence[where f = "\<lambda>i::nat. \<lambda>x. indicator (A i) x *\<^sub>R f x" and x = l])
      apply (rule intgbl [unfolded set_integrable_def])
     prefer 3 apply (rule lim [unfolded set_lebesgue_integral_def])
    apply (rule AE_I2)
  using \<open>mono A\<close> apply (auto simp: mono_def nneg split: split_indicator) []
proof (rule AE_I2)
  { fix x assume "x \<in> space M"
    show "(\<lambda>i. indicator (A i) x *\<^sub>R f x) \<longlonglongrightarrow> indicator (\<Union>i. A i) x *\<^sub>R f x"
    proof cases
      assume "\<exists>i. x \<in> A i"
      then obtain i where "x \<in> A i" ..
      then have "\<forall>\<^sub>F i in sequentially. x \<in> A i"
        using \<open>x \<in> A i\<close> \<open>mono A\<close> by (auto simp: eventually_sequentially mono_def)
      with eventually_mono have "\<forall>\<^sub>F i in sequentially. indicat_real (A i) x *\<^sub>R f x = indicat_real (\<Union> (range A)) x *\<^sub>R f x"
        by fastforce
      then show ?thesis
        by (intro tendsto_eventually)
    qed auto }
  then show "(\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R f x) \<in> borel_measurable M"
    apply (rule borel_measurable_LIMSEQ_real)
     apply assumption
    using intgbl set_integrable_def by blast
qed

text \<open>Proof from Royden, \emph{Real Analysis}, p. 91.\<close>
lemma lebesgue_integral_countable_add:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
    and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(LINT x:(\<Union>i. A i)|M. f x) = (\<Sum>i. (LINT x:(A i)|M. f x))"
    unfolding set_lebesgue_integral_def
proof (subst integral_suminf[symmetric])
  show int_A: "integrable M (\<lambda>x. indicat_real (A i) x *\<^sub>R f x)" for i
    using intgbl unfolding set_integrable_def [symmetric]
    by (rule set_integrable_subset) auto
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. indicator (A i) x *\<^sub>R f x) sums (indicator (\<Union>i. A i) x *\<^sub>R f x)"
      by (intro sums_scaleR_left indicator_sums) fact }
  note sums = this

  have norm_f: "\<And>i. set_integrable M (A i) (\<lambda>x. norm (f x))"
    using int_A[THEN integrable_norm] unfolding set_integrable_def by auto

  show "AE x in M. summable (\<lambda>i. norm (indicator (A i) x *\<^sub>R f x))"
    using disj by (intro AE_I2) (auto intro!: summable_mult2 sums_summable[OF indicator_sums])

  show "summable (\<lambda>i. LINT x|M. norm (indicator (A i) x *\<^sub>R f x))"
  proof (rule summableI_nonneg_bounded)
    fix n
    show "0 \<le> LINT x|M. norm (indicator (A n) x *\<^sub>R f x)"
      using norm_f by (auto intro!: integral_nonneg_AE)

    have "(\<Sum>i<n. LINT x|M. norm (indicator (A i) x *\<^sub>R f x)) = (\<Sum>i<n. LINT x:A i|M. norm (f x))"
      by (simp add: abs_mult set_lebesgue_integral_def)
    also have "\<dots> = set_lebesgue_integral M (\<Union>i<n. A i) (\<lambda>x. norm (f x))"
      using norm_f
      by (subst set_integral_finite_Union) (auto simp: disjoint_family_on_def disj)
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. norm (f x))"
      using intgbl[unfolded set_integrable_def, THEN integrable_norm] norm_f
      unfolding set_lebesgue_integral_def set_integrable_def
      apply (intro integral_mono set_integrable_UN[of "{..<n}", unfolded set_integrable_def])
          apply (auto split: split_indicator)
      done
    finally show "(\<Sum>i<n. LINT x|M. norm (indicator (A i) x *\<^sub>R f x)) \<le>
      set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. norm (f x))"
      by simp
  qed
  show "LINT x|M. indicator (\<Union>(A ` UNIV)) x *\<^sub>R f x = LINT x|M. (\<Sum>i. indicator (A i) x *\<^sub>R f x)"
    by (metis (no_types, lifting) integral_cong sums sums_unique)
qed

lemma set_integral_cont_up:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
shows "(\<lambda>i. LINT x:(A i)|M. f x) \<longlonglongrightarrow> (LINT x:(\<Union>i. A i)|M. f x)"
  unfolding set_lebesgue_integral_def
proof (intro integral_dominated_convergence[where w="\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R norm (f x)"])
  have int_A: "\<And>i. set_integrable M (A i) f"
    using intgbl by (rule set_integrable_subset) auto
  show "\<And>i. (\<lambda>x. indicator (A i) x *\<^sub>R f x) \<in> borel_measurable M"
    using int_A integrable_iff_bounded set_integrable_def by blast
  show "(\<lambda>x. indicator (\<Union>(A ` UNIV)) x *\<^sub>R f x) \<in> borel_measurable M"
    using integrable_iff_bounded intgbl set_integrable_def by blast
  show "integrable M (\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R norm (f x))"
    using int_A intgbl integrable_norm unfolding set_integrable_def 
    by fastforce
  { fix x i assume "x \<in> A i"
    with A have "(\<lambda>xa. indicator (A xa) x::real) \<longlonglongrightarrow> 1 \<longleftrightarrow> (\<lambda>xa. 1::real) \<longlonglongrightarrow> 1"
      by (intro filterlim_cong refl)
         (fastforce simp: eventually_sequentially incseq_def subset_eq intro!: exI[of _ i]) }
  then show "AE x in M. (\<lambda>i. indicator (A i) x *\<^sub>R f x) \<longlonglongrightarrow> indicator (\<Union>i. A i) x *\<^sub>R f x"
    by (intro AE_I2 tendsto_intros) (auto split: split_indicator)
qed (auto split: split_indicator)

(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) \<longlonglongrightarrow> (LINT x:(\<Inter>i. A i)|M. f x)"
  unfolding set_lebesgue_integral_def
proof (rule integral_dominated_convergence)
  have int_A: "\<And>i. set_integrable M (A i) f"
    using int0 by (rule set_integrable_subset) (insert A, auto simp: decseq_def)
  have "integrable M (\<lambda>c. norm (indicat_real (A 0) c *\<^sub>R f c))"
    by (metis (no_types) int0 integrable_norm set_integrable_def)
  then show "integrable M (\<lambda>x. indicator (A 0) x *\<^sub>R norm (f x))"
    by force
  have "set_integrable M (\<Inter>i. A i) f"
    using int0 by (rule set_integrable_subset) (insert A, auto simp: decseq_def)
  with int_A show "(\<lambda>x. indicat_real (\<Inter>(A ` UNIV)) x *\<^sub>R f x) \<in> borel_measurable M"
                  "\<And>i. (\<lambda>x. indicat_real (A i) x *\<^sub>R f x) \<in> borel_measurable M"
    by (auto simp: set_integrable_def)
  show "\<And>i. AE x in M. norm (indicator (A i) x *\<^sub>R f x) \<le> indicator (A 0) x *\<^sub>R norm (f x)"
    using A by (auto split: split_indicator simp: decseq_def)
  { fix x i assume "x \<in> space M" "x \<notin> A i"
    with A have "(\<lambda>i. indicator (A i) x::real) \<longlonglongrightarrow> 0 \<longleftrightarrow> (\<lambda>i. 0::real) \<longlonglongrightarrow> 0"
      by (intro filterlim_cong refl)
         (auto split: split_indicator simp: eventually_sequentially decseq_def intro!: exI[of _ i]) }
  then show "AE x in M. (\<lambda>i. indicator (A i) x *\<^sub>R f x) \<longlonglongrightarrow> indicator (\<Inter>i. A i) x *\<^sub>R f x"
    by (intro AE_I2 tendsto_intros) (auto split: split_indicator)
qed

lemma set_integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and [simp]: "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * measure M {a}"
proof-
  have "set_lebesgue_integral M {a} f = set_lebesgue_integral M {a} (%x. f a)"
    by (intro set_lebesgue_integral_cong) simp_all
  then show ?thesis using assms
    unfolding set_lebesgue_integral_def by simp
qed


section \<open>Complex integrals\<close>

abbreviation complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_integrable M f \<equiv> integrable M f"

abbreviation complex_lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" (\<open>integral\<^sup>C\<close>) where
  "integral\<^sup>C M f == integral\<^sup>L M f"

syntax
  "_complex_lebesgue_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> 'a measure \<Rightarrow> complex"
 (\<open>(\<open>open_block notation=\<open>binder integral\<close>\<close>\<integral>\<^sup>C _. _ \<partial>_)\<close> [0,0] 110)
syntax_consts
  "_complex_lebesgue_integral" == complex_lebesgue_integral
translations
  "\<integral>\<^sup>Cx. f \<partial>M" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

syntax
  "_ascii_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  (\<open>(\<open>indent=3 notation=\<open>binder CLINT\<close>\<close>CLINT _|_. _)\<close> [0,0,10] 10)
syntax_consts
  "_ascii_complex_lebesgue_integral" == complex_lebesgue_integral
translations
  "CLINT x|M. f" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

lemma complex_integrable_cnj [simp]:
  "complex_integrable M (\<lambda>x. cnj (f x)) \<longleftrightarrow> complex_integrable M f"
proof
  assume "complex_integrable M (\<lambda>x. cnj (f x))"
  then have "complex_integrable M (\<lambda>x. cnj (cnj (f x)))"
    by (rule integrable_cnj)
  then show "complex_integrable M f"
    by simp
qed simp

lemma complex_of_real_integrable_eq:
  "complex_integrable M (\<lambda>x. complex_of_real (f x)) \<longleftrightarrow> integrable M f"
proof
  assume "complex_integrable M (\<lambda>x. complex_of_real (f x))"
  then have "integrable M (\<lambda>x. Re (complex_of_real (f x)))"
    by (rule integrable_Re)
  then show "integrable M f"
    by simp
qed simp


abbreviation complex_set_integrable :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_set_integrable M A f \<equiv> set_integrable M A f"

abbreviation complex_set_lebesgue_integral :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_set_lebesgue_integral M A f \<equiv> set_lebesgue_integral M A f"

syntax
  "_ascii_complex_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  (\<open>(\<open>indent=4 notation=\<open>binder CLINT\<close>\<close>CLINT _:_|_. _)\<close> [0,0,0,10] 10)
syntax_consts
  "_ascii_complex_set_lebesgue_integral" == complex_set_lebesgue_integral
translations
  "CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

lemma set_measurable_continuous_on:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "A \<in> sets borel \<Longrightarrow> continuous_on A f \<Longrightarrow> set_borel_measurable borel A f"
  by (meson borel_measurable_continuous_on_indicator
      set_borel_measurable_def)

section \<open>NN Set Integrals\<close>

text\<open>This notation is from Sébastien Gouëzel: His use is not directly in line with the
notations in this file, they are more in line with sum, and more readable he thinks.\<close>

abbreviation "set_nn_integral M A f \<equiv> nn_integral M (\<lambda>x. f x * indicator A x)"

syntax
  "_set_nn_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
    (\<open>(\<open>notation=\<open>binder integral\<close>\<close>\<integral>\<^sup>+((_)\<in>(_)./ _)/\<partial>_)\<close> [0,0,0,110] 10)
  "_set_lebesgue_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
    (\<open>(\<open>notation=\<open>binder integral\<close>\<close>\<integral>((_)\<in>(_)./ _)/\<partial>_)\<close> [0,0,0,110] 10)
syntax_consts
  "_set_nn_integral" == set_nn_integral and
  "_set_lebesgue_integral" == set_lebesgue_integral
translations
  "\<integral>\<^sup>+x \<in> A. f \<partial>M" == "CONST set_nn_integral M A (\<lambda>x. f)"
  "\<integral>x \<in> A. f \<partial>M" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

lemma set_nn_integral_cong:
  assumes "M = M'" "A = B" "\<And>x. x \<in> space M \<inter> A \<Longrightarrow> f x = g x"
  shows   "set_nn_integral M A f = set_nn_integral M' B g"
  by (metis (mono_tags, lifting) IntI assms indicator_simps(2) mult_eq_0_iff nn_integral_cong)

lemma nn_integral_disjoint_pair:
  assumes [measurable]: "f \<in> borel_measurable M"
          "B \<in> sets M" "C \<in> sets M"
          "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
proof -
  have mes: "\<And>D. D \<in> sets M \<Longrightarrow> (\<lambda>x. f x * indicator D x) \<in> borel_measurable M" by simp
  have pos: "\<And>D. AE x in M. f x * indicator D x \<ge> 0" using assms(2) by auto
  have "\<And>x. f x * indicator (B \<union> C) x = f x * indicator B x + f x * indicator C x" using assms(4)
    by (auto split: split_indicator)
  then have "(\<integral>\<^sup>+x. f x * indicator (B \<union> C) x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator B x + f x * indicator C x \<partial>M)"
    by simp
  also have "\<dots> = (\<integral>\<^sup>+x. f x * indicator B x \<partial>M) + (\<integral>\<^sup>+x. f x * indicator C x \<partial>M)"
    by (rule nn_integral_add) (auto simp add: assms mes pos)
  finally show ?thesis by simp
qed

lemma nn_integral_disjoint_pair_countspace:
  assumes "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+x \<in> B. f x \<partial>count_space UNIV) + (\<integral>\<^sup>+x \<in> C. f x \<partial>count_space UNIV)"
by (rule nn_integral_disjoint_pair) (simp_all add: assms)

lemma nn_integral_null_delta:
  assumes "A \<in> sets M" "B \<in> sets M"
          "(A - B) \<union> (B - A) \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M)"
proof (rule nn_integral_cong_AE)
  have *: "AE a in M. a \<notin> (A - B) \<union> (B - A)"
    using assms(3) AE_not_in by blast
  then show \<open>AE x in M. f x * indicator A x = f x * indicator B x\<close>
    by auto
qed

proposition nn_integral_disjoint_family:
  assumes [measurable]: "f \<in> borel_measurable M" "\<And>(n::nat). B n \<in> sets M"
      and "disjoint_family B"
  shows "(\<integral>\<^sup>+x \<in> (\<Union>n. B n). f x \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+x \<in> B n. f x \<partial>M))"
proof -
  have "(\<integral>\<^sup>+ x. (\<Sum>n. f x * indicator (B n) x) \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+ x. f x * indicator (B n) x \<partial>M))"
    by (rule nn_integral_suminf) simp
  moreover have "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (\<Union>n. B n) x" for x
  proof (cases)
    assume "x \<in> (\<Union>n. B n)"
    then obtain n where "x \<in> B n" by blast
    have a: "finite {n}" by simp
    have "\<And>i. i \<noteq> n \<Longrightarrow> x \<notin> B i" using \<open>x \<in> B n\<close> assms(3) disjoint_family_on_def
      by (metis IntI UNIV_I empty_iff)
    then have "\<And>i. i \<notin> {n} \<Longrightarrow> indicator (B i) x = (0::ennreal)" using indicator_def by simp
    then have b: "\<And>i. i \<notin> {n} \<Longrightarrow> f x * indicator (B i) x = (0::ennreal)" by simp

    define h where "h = (\<lambda>i. f x * indicator (B i) x)"
    then have "\<And>i. i \<notin> {n} \<Longrightarrow> h i = 0" using b by simp
    then have "(\<Sum>i. h i) = (\<Sum>i\<in>{n}. h i)"
      by (metis sums_unique[OF sums_finite[OF a]])
    then have "(\<Sum>i. h i) = h n" by simp
    then have "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (B n) x" using h_def by simp
    then have "(\<Sum>n. f x * indicator (B n) x) = f x" using \<open>x \<in> B n\<close> indicator_def by simp
    then show ?thesis using \<open>x \<in> (\<Union>n. B n)\<close> by auto
  next
    assume "x \<notin> (\<Union>n. B n)"
    then have "\<And>n. f x * indicator (B n) x = 0" by simp
    have "(\<Sum>n. f x * indicator (B n) x) = 0"
      by (simp add: \<open>\<And>n. f x * indicator (B n) x = 0\<close>)
    then show ?thesis using \<open>x \<notin> (\<Union>n. B n)\<close> by auto
  qed
  ultimately show ?thesis by simp
qed

lemma nn_set_integral_add:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
  shows "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x \<in> A. f x \<partial>M) + (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x. (f x * indicator A x + g x * indicator A x) \<partial>M)"
    by (auto simp add: indicator_def intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) + (\<integral>\<^sup>+x. g x * indicator A x \<partial>M)"
    apply (rule nn_integral_add) using assms(1) assms(2) by auto
  finally show ?thesis by simp
qed

lemma nn_set_integral_cong:
  assumes "AE x in M. f x = g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
apply (rule nn_integral_cong_AE) using assms(1) by auto

lemma nn_set_integral_set_mono:
  "A \<subseteq> B \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+ x \<in> B. f x \<partial>M)"
by (auto intro!: nn_integral_mono split: split_indicator)

lemma nn_set_integral_mono:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
      and "AE x\<in>A in M. f x \<le> g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
by (auto intro!: nn_integral_mono_AE split: split_indicator simp: assms)

lemma nn_set_integral_space [simp]:
  shows "(\<integral>\<^sup>+ x \<in> space M. f x \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
by (metis (mono_tags, lifting) indicator_simps(1) mult.right_neutral nn_integral_cong)

lemma nn_integral_count_compose_inj:
  assumes "inj_on g A"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+x. f (g x) \<partial>count_space A)"
    by (auto simp add: nn_integral_count_space_indicator[symmetric])
  also have "\<dots> = (\<integral>\<^sup>+y. f y \<partial>count_space (g`A))"
    by (simp add: assms nn_integral_bij_count_space inj_on_imp_bij_betw)
  also have "\<dots> = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (auto simp add: nn_integral_count_space_indicator[symmetric])
  finally show ?thesis by simp
qed

lemma nn_integral_count_compose_bij:
  assumes "bij_betw g A B"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> B. f y \<partial>count_space UNIV)"
proof -
  have "inj_on g A" using assms bij_betw_def by auto
  then have "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (rule nn_integral_count_compose_inj)
  then show ?thesis using assms by (simp add: bij_betw_def)
qed

lemma set_integral_null_delta:
  fixes f::"_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "integrable M f" "A \<in> sets M" "B \<in> sets M"
    and null: "(A - B) \<union> (B - A) \<in> null_sets M"
  shows "(\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> B. f x \<partial>M)"
proof (rule set_integral_cong_set)
  have *: "AE a in M. a \<notin> (A - B) \<union> (B - A)"
    using null AE_not_in by blast
  then show "AE x in M. (x \<in> B) = (x \<in> A)"
    by auto
qed (simp_all add: set_borel_measurable_def)

lemma set_integral_space:
  assumes "integrable M f"
  shows "(\<integral>x \<in> space M. f x \<partial>M) = (\<integral>x. f x \<partial>M)"
  by (metis (no_types, lifting) indicator_simps(1) integral_cong scaleR_one set_lebesgue_integral_def)

lemma null_if_pos_func_has_zero_nn_int:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes [measurable]: "f \<in> borel_measurable M" "A \<in> sets M"
    and "AE x\<in>A in M. f x > 0" "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = 0"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. f x * indicator A x = 0"
    by (subst nn_integral_0_iff_AE[symmetric], auto simp add: assms(4))
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed

lemma null_if_pos_func_has_zero_int:
  assumes [measurable]: "integrable M f" "A \<in> sets M"
      and "AE x\<in>A in M. f x > 0" "(\<integral>x\<in>A. f x \<partial>M) = (0::real)"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. indicator A x * f x = 0"
    apply (subst integral_nonneg_eq_0_iff_AE[symmetric])
    using assms integrable_mult_indicator[OF \<open>A \<in> sets M\<close> assms(1)]
    by (auto simp: set_lebesgue_integral_def)
  then have "AE x\<in>A in M. f x = 0" by auto
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed

text\<open>The next lemma is a variant of \<open>density_unique\<close>. Note that it uses the notation
for nonnegative set integrals introduced earlier.\<close>

lemma (in sigma_finite_measure) density_unique2:
  assumes [measurable]: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+ x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
proof (rule density_unique)
  show "density M f = density M f'"
    by (intro measure_eqI) (auto simp: emeasure_density intro!: density_eq)
qed (auto simp add: assms)


text \<open>The next lemma implies the same statement for Banach-space valued functions
using Hahn-Banach theorem and linear forms. Since they are not yet easily available, I
only formulate it for real-valued functions.\<close>

lemma density_unique_real:
  fixes f f'::"_ \<Rightarrow> real"
  assumes M[measurable]: "integrable M f" "integrable M f'"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
proof -
  define A where "A = {x \<in> space M. f x < f' x}"
  then have [measurable]: "A \<in> sets M" by simp
  have "(\<integral>x \<in> A. (f' x - f x) \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M) - (\<integral>x \<in> A. f x \<partial>M)"
    using \<open>A \<in> sets M\<close> M integrable_mult_indicator set_integrable_def by blast
  then have "(\<integral>x \<in> A. (f' x - f x) \<partial>M) = 0" using assms(3) by simp
  then have "A \<in> null_sets M"
    using A_def null_if_pos_func_has_zero_int[where ?f = "\<lambda>x. f' x - f x" and ?A = A] assms by auto
  then have "AE x in M. x \<notin> A" by (simp add: AE_not_in)
  then have *: "AE x in M. f' x \<le> f x" unfolding A_def by auto

  define B where "B = {x \<in> space M. f' x < f x}"
  then have [measurable]: "B \<in> sets M" by simp
  have "(\<integral>x \<in> B. (f x - f' x) \<partial>M) = (\<integral>x \<in> B. f x \<partial>M) - (\<integral>x \<in> B. f' x \<partial>M)"
    using \<open>B \<in> sets M\<close> M integrable_mult_indicator set_integrable_def by blast
  then have "(\<integral>x \<in> B. (f x - f' x) \<partial>M) = 0" using assms(3) by simp
  then have "B \<in> null_sets M"
    using B_def null_if_pos_func_has_zero_int[where ?f = "\<lambda>x. f x - f' x" and ?A = B] assms by auto
  then have "AE x in M. x \<notin> B" by (simp add: AE_not_in)
  then have "AE x in M. f' x \<ge> f x" unfolding B_def by auto
  then show ?thesis using * by auto
qed

section \<open>Scheffé's lemma\<close>

text \<open>The next lemma shows that \<open>L\<^sup>1\<close> convergence of a sequence of functions follows from almost
everywhere convergence and the weaker condition of the convergence of the integrated norms (or even
just the nontrivial inequality about them). Useful in a lot of contexts! This statement (or its
variations) are known as Scheffe lemma.

The formalization is more painful as one should jump back and forth between reals and ereals and justify
all the time positivity or integrability (thankfully, measurability is handled more or less automatically).\<close>

proposition Scheffe_lemma1:
  assumes "\<And>n. integrable M (F n)" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "limsup (\<lambda>n. \<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  have [measurable]: "\<And>n. F n \<in> borel_measurable M" "f \<in> borel_measurable M"
    using assms(1) assms(2) by simp_all
  define G where "G = (\<lambda>n x. norm(f x) + norm(F n x) - norm(F n x - f x))"
  have [measurable]: "\<And>n. G n \<in> borel_measurable M" unfolding G_def by simp
  have G_pos[simp]: "\<And>n x. G n x \<ge> 0"
    unfolding G_def by (metis ge_iff_diff_ge_0 norm_minus_commute norm_triangle_ineq4)
  have finint: "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    using has_bochner_integral_implies_finite_norm[OF has_bochner_integral_integrable[OF \<open>integrable M f\<close>]]
    by simp
  then have fin2: "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    by (auto simp: ennreal_mult_eq_top_iff)

  {
    fix x assume *: "(\<lambda>n. F n x) \<longlonglongrightarrow> f x"
    then have "(\<lambda>n. norm(F n x)) \<longlonglongrightarrow> norm(f x)" using tendsto_norm by blast
    moreover have "(\<lambda>n. norm(F n x - f x)) \<longlonglongrightarrow> 0" using * Lim_null tendsto_norm_zero_iff by fastforce
    ultimately have a: "(\<lambda>n. norm(F n x) - norm(F n x - f x)) \<longlonglongrightarrow> norm(f x)" using tendsto_diff by fastforce
    have "(\<lambda>n. norm(f x) + (norm(F n x) - norm(F n x - f x))) \<longlonglongrightarrow> norm(f x) + norm(f x)"
      by (rule tendsto_add) (auto simp add: a)
    moreover have "\<And>n. G n x = norm(f x) + (norm(F n x) - norm(F n x - f x))" unfolding G_def by simp
    ultimately have "(\<lambda>n. G n x) \<longlonglongrightarrow> 2 * norm(f x)" by simp
    then have "(\<lambda>n. ennreal(G n x)) \<longlonglongrightarrow> ennreal(2 * norm(f x))" by simp
    then have "liminf (\<lambda>n. ennreal(G n x)) = ennreal(2 * norm(f x))"
      using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  }
  then have "AE x in M. liminf (\<lambda>n. ennreal(G n x)) = ennreal(2 * norm(f x))" using assms(3) by auto
  then have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = (\<integral>\<^sup>+ x. 2 * ennreal(norm(f x)) \<partial>M)"
    by (simp add: nn_integral_cong_AE ennreal_mult)
  also have "\<dots> = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by (rule nn_integral_cmult) auto
  finally have int_liminf: "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
    by simp

  have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M)" for n
    by (rule nn_integral_add) (auto simp add: assms)
  then have "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) =
      limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by simp
  also have "\<dots> = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by (rule Limsup_const_add, auto simp add: finint)
  also have "\<dots> \<le> (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using assms(4) by (simp add: add_left_mono)
  also have "\<dots> = 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    unfolding one_add_one[symmetric] distrib_right by simp
  ultimately have a: "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) \<le>
    2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)" by simp

  have le: "ennreal (norm (F n x - f x)) \<le> ennreal (norm (f x)) + ennreal (norm (F n x))" for n x
    by (simp add: norm_minus_commute norm_triangle_ineq4 ennreal_minus flip: ennreal_plus)
  then have le2: "(\<integral>\<^sup>+ x. ennreal (norm (F n x - f x)) \<partial>M) \<le> (\<integral>\<^sup>+ x. ennreal (norm (f x)) + ennreal (norm (F n x)) \<partial>M)" for n
    by (rule nn_integral_mono)

  have "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M)"
    by (simp add: int_liminf)
  also have "\<dots> \<le> liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M))"
    by (rule nn_integral_liminf) auto
  also have "liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M)) =
    liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
  proof (intro arg_cong[where f=liminf] ext)
    fix n
    have "\<And>x. ennreal(G n x) = ennreal(norm(f x)) + ennreal(norm(F n x)) - ennreal(norm(F n x - f x))"
      unfolding G_def by (simp add: ennreal_minus flip: ennreal_plus)
    moreover have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) - ennreal(norm(F n x - f x)) \<partial>M)
            = (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)"
    proof (rule nn_integral_diff)
      from le show "AE x in M. ennreal (norm (F n x - f x)) \<le> ennreal (norm (f x)) + ennreal (norm (F n x))"
        by simp
      from le2 have "(\<integral>\<^sup>+x. ennreal (norm (F n x - f x)) \<partial>M) < \<infinity>" using assms(1) assms(2)
        by (metis has_bochner_integral_implies_finite_norm integrable.simps Bochner_Integration.integrable_diff)
      then show "(\<integral>\<^sup>+x. ennreal (norm (F n x - f x)) \<partial>M) \<noteq> \<infinity>" by simp
    qed (auto simp add: assms)
    ultimately show "(\<integral>\<^sup>+x. G n x \<partial>M) = (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)"
      by simp
  qed
  finally have "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) \<le>
    liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) +
    limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    by (intro add_mono) auto
  also have "\<dots> \<le> (limsup (\<lambda>n. \<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - limsup (\<lambda>n. \<integral>\<^sup>+x. norm (F n x - f x) \<partial>M)) +
    limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    by (intro add_mono liminf_minus_ennreal le2) auto
  also have "\<dots> = limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M))"
    by (intro diff_add_cancel_ennreal Limsup_mono always_eventually allI le2)
  also have "\<dots> \<le> 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    by fact
  finally have "limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) = 0"
    using fin2 by simp
  then show ?thesis
    by (rule tendsto_0_if_Limsup_eq_0_ennreal)
qed

proposition Scheffe_lemma2:
  fixes F::"nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<And> n::nat. F n \<in> borel_measurable M" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "\<And>n. (\<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof (rule Scheffe_lemma1)
  fix n::nat
  have "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) < \<infinity>" using assms(2) by (metis has_bochner_integral_implies_finite_norm integrable.cases)
  then have "(\<integral>\<^sup>+ x. norm(F n x) \<partial>M) < \<infinity>" using assms(4)[of n] by auto
  then show "integrable M (F n)" by (subst integrable_iff_bounded, simp add: assms(1)[of n])
qed (auto simp add: assms Limsup_bounded)

lemma tendsto_set_lebesgue_integral_at_right:
  fixes a b :: real and f :: "real \<Rightarrow> 'a :: {banach,second_countable_topology}"
  assumes "a < b" and sets: "\<And>a'. a' \<in> {a<..b} \<Longrightarrow> {a'..b} \<in> sets M"
      and "set_integrable M {a<..b} f"
  shows   "((\<lambda>a'. set_lebesgue_integral M {a'..b} f) \<longlongrightarrow>
             set_lebesgue_integral M {a<..b} f) (at_right a)"
proof (rule tendsto_at_right_sequentially[OF assms(1)], goal_cases)
  case (1 S)
  have eq: "(\<Union>n. {S n..b}) = {a<..b}"
  proof safe
    fix x n assume "x \<in> {S n..b}"
    with 1(1,2)[of n] show "x \<in> {a<..b}" by auto
  next
    fix x assume "x \<in> {a<..b}"
    with order_tendstoD[OF \<open>S \<longlonglongrightarrow> a\<close>, of x] show "x \<in> (\<Union>n. {S n..b})"
      by (force simp: eventually_at_top_linorder dest: less_imp_le)
  qed
  have "(\<lambda>n. set_lebesgue_integral M {S n..b} f) \<longlonglongrightarrow> set_lebesgue_integral M (\<Union>n. {S n..b}) f"
    by (rule set_integral_cont_up) (insert assms 1, auto simp: eq incseq_def decseq_def less_imp_le)
  with eq show ?case by simp
qed

section \<open>Convergence of integrals over an interval\<close>

text \<open>
  The next lemmas relate convergence of integrals over an interval to
  improper integrals.
\<close>
lemma tendsto_set_lebesgue_integral_at_left:
  fixes a b :: real and f :: "real \<Rightarrow> 'a :: {banach,second_countable_topology}"
  assumes "a < b" and sets: "\<And>b'. b' \<in> {a..<b} \<Longrightarrow> {a..b'} \<in> sets M"
      and "set_integrable M {a..<b} f"
  shows   "((\<lambda>b'. set_lebesgue_integral M {a..b'} f) \<longlongrightarrow>
             set_lebesgue_integral M {a..<b} f) (at_left b)"
proof (rule tendsto_at_left_sequentially[OF assms(1)], goal_cases)
  case (1 S)
  have eq: "(\<Union>n. {a..S n}) = {a..<b}"
  proof safe
    fix x n assume "x \<in> {a..S n}"
    with 1(1,2)[of n] show "x \<in> {a..<b}" by auto
  next
    fix x assume "x \<in> {a..<b}"
    with order_tendstoD[OF \<open>S \<longlonglongrightarrow> b\<close>, of x] show "x \<in> (\<Union>n. {a..S n})"
      by (force simp: eventually_at_top_linorder dest: less_imp_le)
  qed
  have "(\<lambda>n. set_lebesgue_integral M {a..S n} f) \<longlonglongrightarrow> set_lebesgue_integral M (\<Union>n. {a..S n}) f"
    by (rule set_integral_cont_up) (insert assms 1, auto simp: eq incseq_def decseq_def less_imp_le)
  with eq show ?case by simp
qed

proposition tendsto_set_lebesgue_integral_at_top:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes sets: "\<And>b. b \<ge> a \<Longrightarrow> {a..b} \<in> sets M"
      and int: "set_integrable M {a..} f"
  shows "((\<lambda>b. set_lebesgue_integral M {a..b} f) \<longlongrightarrow> set_lebesgue_integral M {a..} f) at_top"
proof (rule tendsto_at_topI_sequentially)
  fix X :: "nat \<Rightarrow> real" assume "filterlim X at_top sequentially"
  show "(\<lambda>n. set_lebesgue_integral M {a..X n} f) \<longlonglongrightarrow> set_lebesgue_integral M {a..} f"
    unfolding set_lebesgue_integral_def
  proof (rule integral_dominated_convergence)
    show "integrable M (\<lambda>x. indicat_real {a..} x *\<^sub>R norm (f x))"
      using integrable_norm[OF int[unfolded set_integrable_def]] by simp
    show "AE x in M. (\<lambda>n. indicator {a..X n} x *\<^sub>R f x) \<longlonglongrightarrow> indicat_real {a..} x *\<^sub>R f x"
    proof
      fix x
      from \<open>filterlim X at_top sequentially\<close>
      have "eventually (\<lambda>n. x \<le> X n) sequentially"
        unfolding filterlim_at_top_ge[where c=x] by auto
      then show "(\<lambda>n. indicator {a..X n} x *\<^sub>R f x) \<longlonglongrightarrow> indicat_real {a..} x *\<^sub>R f x"
        by (intro tendsto_eventually) (auto split: split_indicator elim!: eventually_mono)
    qed
    fix n show "AE x in M. norm (indicator {a..X n} x *\<^sub>R f x) \<le> 
                             indicator {a..} x *\<^sub>R norm (f x)"
      by (auto split: split_indicator)
  next
    from int show "(\<lambda>x. indicat_real {a..} x *\<^sub>R f x) \<in> borel_measurable M"
      by (simp add: set_integrable_def)
  next
    fix n :: nat
    from sets have "{a..X n} \<in> sets M" by (cases "X n \<ge> a") auto
    with int have "set_integrable M {a..X n} f"
      by (rule set_integrable_subset) auto
    thus "(\<lambda>x. indicat_real {a..X n} x *\<^sub>R f x) \<in> borel_measurable M"
      by (simp add: set_integrable_def)
  qed
qed

proposition tendsto_set_lebesgue_integral_at_bot:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes sets: "\<And>a. a \<le> b \<Longrightarrow> {a..b} \<in> sets M"
      and int: "set_integrable M {..b} f"
    shows "((\<lambda>a. set_lebesgue_integral M {a..b} f) \<longlongrightarrow> set_lebesgue_integral M {..b} f) at_bot"
proof (rule tendsto_at_botI_sequentially)
  fix X :: "nat \<Rightarrow> real" assume "filterlim X at_bot sequentially"
  show "(\<lambda>n. set_lebesgue_integral M {X n..b} f) \<longlonglongrightarrow> set_lebesgue_integral M {..b} f"
    unfolding set_lebesgue_integral_def
  proof (rule integral_dominated_convergence)
    show "integrable M (\<lambda>x. indicat_real {..b} x *\<^sub>R norm (f x))"
      using integrable_norm[OF int[unfolded set_integrable_def]] by simp
    show "AE x in M. (\<lambda>n. indicator {X n..b} x *\<^sub>R f x) \<longlonglongrightarrow> indicat_real {..b} x *\<^sub>R f x"
    proof
      fix x
      from \<open>filterlim X at_bot sequentially\<close>
      have "eventually (\<lambda>n. x \<ge> X n) sequentially"
        unfolding filterlim_at_bot_le[where c=x] by auto
      then show "(\<lambda>n. indicator {X n..b} x *\<^sub>R f x) \<longlonglongrightarrow> indicat_real {..b} x *\<^sub>R f x"
        by (intro tendsto_eventually) (auto split: split_indicator elim!: eventually_mono)
    qed
    fix n show "AE x in M. norm (indicator {X n..b} x *\<^sub>R f x) \<le> 
                             indicator {..b} x *\<^sub>R norm (f x)"
      by (auto split: split_indicator)
  next
    from int show "(\<lambda>x. indicat_real {..b} x *\<^sub>R f x) \<in> borel_measurable M"
      by (simp add: set_integrable_def)
  next
    fix n :: nat
    from sets have "{X n..b} \<in> sets M" by (cases "X n \<le> b") auto
    with int have "set_integrable M {X n..b} f"
      by (rule set_integrable_subset) auto
    thus "(\<lambda>x. indicat_real {X n..b} x *\<^sub>R f x) \<in> borel_measurable M"
      by (simp add: set_integrable_def)
  qed
qed



theorem integral_Markov_inequality':
  fixes u :: "'a \<Rightarrow> real"
  assumes [measurable]: "set_integrable M A u" and "A \<in> sets M"
  assumes "AE x in M. x \<in> A \<longrightarrow> u x \<ge> 0" and "0 < (c::real)"
  shows "emeasure M {x\<in>A. u x \<ge> c} \<le> (1/c::real) * (\<integral>x\<in>A. u x \<partial>M)"
proof -
  have "(\<lambda>x. u x * indicator A x) \<in> borel_measurable M" 
    using assms by (auto simp: set_integrable_def mult_ac)
  hence "(\<lambda>x. ennreal (u x * indicator A x)) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. ennreal (u x * indicator A x)) = (\<lambda>x. ennreal (u x) * indicator A x)"
    by (intro ext) (auto simp: indicator_def)
  finally have meas: "\<dots> \<in> borel_measurable M" .
  from assms(3) have AE: "AE x in M. 0 \<le> u x * indicator A x"
    by eventually_elim (auto simp: indicator_def)
  have nonneg: "set_lebesgue_integral M A u \<ge> 0"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_nonneg_AE eventually_mono[OF AE]) (auto simp: mult_ac)

  have A: "A \<subseteq> space M"
    using \<open>A \<in> sets M\<close> by (simp add: sets.sets_into_space)
  have "{x \<in> A. u x \<ge> c} = {x \<in> A. ennreal(1/c) * u x \<ge> 1}"
    using \<open>c>0\<close> A by (auto simp: ennreal_mult'[symmetric])
  then have "emeasure M {x \<in> A. u x \<ge> c} = emeasure M ({x \<in> A. ennreal(1/c) * u x \<ge> 1})"
    by simp
  also have "\<dots> \<le> ennreal(1/c) * (\<integral>\<^sup>+ x. ennreal(u x) * indicator A x \<partial>M)"
    by (intro nn_integral_Markov_inequality meas assms)
  also have "(\<integral>\<^sup>+ x. ennreal(u x) * indicator A x \<partial>M) = ennreal (set_lebesgue_integral M A u)"
    unfolding set_lebesgue_integral_def nn_integral_set_ennreal using assms AE
    by (subst nn_integral_eq_integral) (simp_all add: mult_ac set_integrable_def)
  finally show ?thesis
    using \<open>c > 0\<close> nonneg by (subst ennreal_mult) auto
qed

theorem integral_Markov_inequality'_measure:
  assumes [measurable]: "set_integrable M A u" and "A \<in> sets M" 
     and "AE x in M. x \<in> A \<longrightarrow> 0 \<le> u x" "0 < (c::real)"
  shows "measure M {x\<in>A. u x \<ge> c} \<le> (\<integral>x\<in>A. u x \<partial>M) / c"
proof -
  have nonneg: "set_lebesgue_integral M A u \<ge> 0"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_nonneg_AE eventually_mono[OF assms(3)])
       (auto simp: mult_ac)
  have le: "emeasure M {x\<in>A. u x \<ge> c} \<le> ennreal ((1/c) * (\<integral>x\<in>A. u x \<partial>M))"
    by (rule integral_Markov_inequality') (use assms in auto)
  also have "\<dots> < top"
    by auto
  finally have "ennreal (measure M {x\<in>A. u x \<ge> c}) = emeasure M {x\<in>A. u x \<ge> c}"
    by (intro emeasure_eq_ennreal_measure [symmetric]) auto
  also note le
  finally show ?thesis using nonneg
    by (subst (asm) ennreal_le_iff)
       (auto intro!: divide_nonneg_pos Bochner_Integration.integral_nonneg_AE assms)
qed

theorem%important (in finite_measure) Chernoff_ineq_ge:
  assumes s: "s > 0"
  assumes integrable: "set_integrable M A (\<lambda>x. exp (s * f x))" and "A \<in> sets M"
  shows   "measure M {x\<in>A. f x \<ge> a} \<le> exp (-s * a) * (\<integral>x\<in>A. exp (s * f x) \<partial>M)"
proof -
  have "{x\<in>A. f x \<ge> a} = {x\<in>A. exp (s * f x) \<ge> exp (s * a)}"
    using s by auto
  also have "measure M \<dots> \<le> set_lebesgue_integral M A (\<lambda>x. exp (s * f x)) / exp (s * a)"
    by (intro integral_Markov_inequality'_measure assms) auto
  finally show ?thesis 
    by (simp add: exp_minus field_simps)
qed

theorem%important (in finite_measure) Chernoff_ineq_le:
  assumes s: "s > 0"
  assumes integrable: "set_integrable M A (\<lambda>x. exp (-s * f x))" and "A \<in> sets M"
  shows   "measure M {x\<in>A. f x \<le> a} \<le> exp (s * a) * (\<integral>x\<in>A. exp (-s * f x) \<partial>M)"
proof -
  have "{x\<in>A. f x \<le> a} = {x\<in>A. exp (-s * f x) \<ge> exp (-s * a)}"
    using s by auto
  also have "measure M \<dots> \<le> set_lebesgue_integral M A (\<lambda>x. exp (-s * f x)) / exp (-s * a)"
    by (intro integral_Markov_inequality'_measure assms) auto
  finally show ?thesis 
    by (simp add: exp_minus field_simps)
qed


section \<open>Integrable Simple Functions\<close>

text \<open>This section is from the Martingales AFP entry, by Ata Keskin, TU München\<close>

text \<open>We restate some basic results concerning Bochner-integrable functions.\<close>
  
lemma integrable_implies_simple_function_sequence:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  obtains s where "\<And>i. simple_function M (s i)"
      and "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
proof-
  have f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>" using assms unfolding integrable_iff_bounded by auto
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" using borel_measurable_implies_sequence_metric[OF f(1)] unfolding norm_conv_dist by metis
  {
    fix i
    have "(\<integral>\<^sup>+x. norm (s i x) \<partial>M) \<le> (\<integral>\<^sup>+x. ennreal (2 * norm (f x)) \<partial>M)" using s by (intro nn_integral_mono, auto)
    also have "\<dots> < \<infinity>" using f by (simp add: nn_integral_cmult ennreal_mult_less_top ennreal_mult)
    finally have sbi: "Bochner_Integration.simple_bochner_integrable M (s i)" using s by (intro simple_bochner_integrableI_bounded) auto
    hence "emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" by (auto intro: integrableI_simple_bochner_integrable simple_bochner_integrable.cases)
  }
  thus ?thesis using that s by blast
qed

text \<open>Simple functions can be represented by sums of indicator functions.\<close>

lemma simple_function_indicator_representation_banach:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "simple_function M f" "x \<in> space M"
  shows "f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"
  (is "?l = ?r")
proof -
  have "?r = (\<Sum>y \<in> f ` space M. (if y = f x then indicator (f -` {y} \<inter> space M) x *\<^sub>R y else 0))" 
    by (auto intro!: sum.cong)
  also have "\<dots> =  indicator (f -` {f x} \<inter> space M) x *\<^sub>R f x" using assms by (auto dest: simple_functionD)
  also have "\<dots> = f x" using assms by (auto simp: indicator_def)
  finally show ?thesis by auto
qed

lemma simple_function_indicator_representation_AE:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "simple_function M f"
  shows "AE x in M. f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"  
  by (metis (mono_tags, lifting) AE_I2 simple_function_indicator_representation_banach assms)

lemmas simple_function_scaleR[intro] = simple_function_compose2[where h="(*\<^sub>R)"]
lemmas integrable_simple_function = simple_bochner_integrable.intros[THEN has_bochner_integral_simple_bochner_integrable, THEN integrable.intros] 

text \<open>Induction rule for simple integrable functions.\<close>

lemma\<^marker>\<open>tag important\<close> integrable_simple_function_induct[consumes 2, case_names cong indicator add, induct set: simple_function]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> 
                    \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> 
                    \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes indicator: "\<And>A y. A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>z. z \<in> space M \<Longrightarrow> norm (f z + g z) = norm (f z) + norm (g z)) \<Longrightarrow>
                      P f \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  shows "P f"
proof-
  let ?f = "\<lambda>x. (\<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
  have f_ae_eq: "f x = ?f x" if "x \<in> space M" for x using simple_function_indicator_representation_banach[OF f(1) that] .
  moreover have "emeasure M {y \<in> space M. ?f y \<noteq> 0} \<noteq> \<infinity>" by (metis (no_types, lifting) Collect_cong calculation f(2))
  moreover have "P (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "simple_function M (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "emeasure M {y \<in> space M. (\<Sum>x\<in>S. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<noteq> \<infinity>"
                if "S \<subseteq> f ` space M" for S using simple_functionD(1)[OF assms(1), THEN rev_finite_subset, OF that] that 
  proof (induction rule: finite_induct)
    case empty
    {
      case 1
      then show ?case using indicator[of "{}"] by force
    next
      case 2
      then show ?case by force 
    next
      case 3
      then show ?case by force 
    }
  next
    case (insert x F)
    have "(f -` {x} \<inter> space M) \<subseteq> {y \<in> space M. f y \<noteq> 0}" if "x \<noteq> 0" using that by blast
    moreover have "{y \<in> space M. f y \<noteq> 0} = space M - (f -` {0} \<inter> space M)" by blast
    moreover have "space M - (f -` {0} \<inter> space M) \<in> sets M" using simple_functionD(2)[OF f(1)] by blast
    ultimately have fin_0: "emeasure M (f -` {x} \<inter> space M) < \<infinity>" if "x \<noteq> 0" using that by (metis emeasure_mono f(2) infinity_ennreal_def top.not_eq_extremum top_unique)
    hence fin_1: "emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0} \<noteq> \<infinity>" if "x \<noteq> 0" by (metis (mono_tags, lifting) emeasure_mono f(1) indicator_simps(2) linorder_not_less mem_Collect_eq scaleR_eq_0_iff simple_functionD(2) subsetI that)

    have *: "(\<Sum>y\<in>insert x F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) = (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) xa *\<^sub>R x" for xa by (metis (no_types, lifting) Diff_empty Diff_insert0 add.commute insert.hyps(1) insert.hyps(2) sum.insert_remove)
    have **: "{y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<subseteq> {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}" unfolding * by fastforce    
    {
      case 1
      hence x: "x \<in> f ` space M" and F: "F \<subseteq> f ` space M" by auto
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert(3)[OF F] by simp
      next
        case False
        have norm_argument: "norm ((\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x) = norm (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + norm (indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x)" if z: "z \<in> space M" for z
        proof (cases "f z = x")
          case True
          have "indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y = 0" if "y \<in> F" for y
            using True insert(2) z that 1 unfolding indicator_def by force
          hence "(\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) = 0" by (meson sum.neutral)
          then show ?thesis by force
        next
          case False
          then show ?thesis by force
        qed
        show ?thesis 
          using False simple_functionD(2)[OF f(1)] insert(3,5)[OF F] simple_function_scaleR fin_0 fin_1 
          by (subst *, subst add, subst simple_function_sum) (blast intro: norm_argument indicator)+
      qed 
    next
      case 2
      hence x: "x \<in> f ` space M" and F: "F \<subseteq> f ` space M" by auto
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert(4)[OF F] by simp
      next
        case False
        then show ?thesis unfolding * using insert(4)[OF F] simple_functionD(2)[OF f(1)] by fast
      qed
    next
      case 3
      hence x: "x \<in> f ` space M" and F: "F \<subseteq> f ` space M" by auto
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert(5)[OF F] by simp
      next
        case False
        have "emeasure M {y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<le> emeasure M ({y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0})"
          using ** simple_functionD(2)[OF insert(4)[OF F]] simple_functionD(2)[OF f(1)] by (intro emeasure_mono, force+)
        also have "\<dots> \<le> emeasure M {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} + emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}"
          using simple_functionD(2)[OF insert(4)[OF F]] simple_functionD(2)[OF f(1)] by (intro emeasure_subadditive, force+)
        also have "\<dots> < \<infinity>" using insert(5)[OF F] fin_1[OF False] by (simp add: less_top)
        finally show ?thesis by simp
      qed
    }
  qed
  moreover have "simple_function M (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" using calculation by blast
  moreover have "P (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" using calculation by blast
  ultimately show ?thesis by (intro cong[OF _ _ f(1,2)], blast, presburger+) 
qed

text \<open>Induction rule for non-negative simple integrable functions\<close>
lemma\<^marker>\<open>tag important\<close> integrable_simple_function_induct_nn[consumes 3, case_names cong indicator add, induct set: simple_function]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes f: "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<longrightarrow> f x \<ge> 0"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes indicator: "\<And>A y. y \<ge> 0 \<Longrightarrow> A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>f g. (\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0) \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>z. z \<in> space M \<Longrightarrow> norm (f z + g z) = norm (f z) + norm (g z)) \<Longrightarrow>
                      P f \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  shows "P f"
proof-
  let ?f = "\<lambda>x. (\<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
  have f_ae_eq: "f x = ?f x" if "x \<in> space M" for x using simple_function_indicator_representation_banach[OF f(1) that] .
  moreover have "emeasure M {y \<in> space M. ?f y \<noteq> 0} \<noteq> \<infinity>" by (metis (no_types, lifting) Collect_cong calculation f(2))
  moreover have "P (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "simple_function M (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "emeasure M {y \<in> space M. (\<Sum>x\<in>S. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<noteq> \<infinity>"
                "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> (\<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                if "S \<subseteq> f ` space M" for S using simple_functionD(1)[OF assms(1), THEN rev_finite_subset, OF that] that 
  proof (induction rule: finite_subset_induct')
    case empty
    {
      case 1
      then show ?case using indicator[of 0 "{}"] by force
    next
      case 2
      then show ?case by force 
    next
      case 3
      then show ?case by force 
    next
      case 4
      then show ?case by force 
    }
  next
    case (insert x F)
    have "(f -` {x} \<inter> space M) \<subseteq> {y \<in> space M. f y \<noteq> 0}" if "x \<noteq> 0" 
      using that by blast
    moreover have "{y \<in> space M. f y \<noteq> 0} = space M - (f -` {0} \<inter> space M)"
      by blast
    moreover have "space M - (f -` {0} \<inter> space M) \<in> sets M" 
      using simple_functionD(2)[OF f(1)] by blast
    ultimately have fin_0: "emeasure M (f -` {x} \<inter> space M) < \<infinity>" if "x \<noteq> 0" 
      using that by (metis emeasure_mono f(2) infinity_ennreal_def top.not_eq_extremum top_unique)
    hence fin_1: "emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0} \<noteq> \<infinity>" if "x \<noteq> 0" 
      by (metis (mono_tags, lifting) emeasure_mono f(1) indicator_simps(2) linorder_not_less mem_Collect_eq scaleR_eq_0_iff simple_functionD(2) subsetI that)

    have nonneg_x: "x \<ge> 0" using insert f by blast
    have *: "(\<Sum>y\<in>insert x F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) = (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) xa *\<^sub>R x" for xa by (metis (no_types, lifting) add.commute insert.hyps(1) insert.hyps(4) sum.insert)
    have **: "{y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<subseteq> {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}" unfolding * by fastforce    
    {
      case 1
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert by simp
      next
        case False
        have norm_argument: "norm ((\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x) 
              = norm (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + norm (indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x)" 
          if z: "z \<in> space M" for z
        proof (cases "f z = x")
          case True
          have "indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y = 0" if "y \<in> F" for y 
            using True insert z that 1 unfolding indicator_def by force
          hence "(\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) = 0" 
            by (meson sum.neutral)
          thus ?thesis by force
        qed (force)
        show ?thesis using False fin_0 fin_1 f norm_argument 
          by (subst *, subst add, presburger add: insert, intro insert, intro insert, fastforce simp add: indicator_def intro!: insert(2) f(3), auto intro!: indicator insert nonneg_x)
      qed 
    next
      case 2
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert by simp
      next
        case False
        then show ?thesis unfolding * using insert simple_functionD(2)[OF f(1)] by fast
      qed
    next
      case 3
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert by simp
      next
        case False
        have "emeasure M {y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} 
           \<le> emeasure M ({y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0})"
          using ** simple_functionD(2)[OF insert(6)] simple_functionD(2)[OF f(1)] insert.IH(2) by (intro emeasure_mono, blast, simp) 
        also have "\<dots> \<le> emeasure M {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} + emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}"
          using simple_functionD(2)[OF insert(6)] simple_functionD(2)[OF f(1)] by (intro emeasure_subadditive, force+)
        also have "\<dots> < \<infinity>" using insert(7) fin_1[OF False] by (simp add: less_top)
        finally show ?thesis by simp
      qed
    next
      case (4 \<xi>)
      thus ?case using insert nonneg_x f(3) by (auto simp add: scaleR_nonneg_nonneg intro: sum_nonneg)
    }
  qed
  moreover have "simple_function M (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" 
    using calculation by blast
  moreover have "P (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" 
    using calculation by blast
  moreover have "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x" using f(3) by simp
  ultimately show ?thesis
    by (smt (verit) Collect_cong f(1) local.cong) 
qed

lemma finite_nn_integral_imp_ae_finite:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>"
  shows "AE x in M. f x < \<infinity>"
proof (rule ccontr, goal_cases)
  case 1
  let ?A = "space M \<inter> {x. f x = \<infinity>}"
  have *: "emeasure M ?A > 0" using 1 assms(1) 
    by (metis (mono_tags, lifting) assms(2) eventually_mono infinity_ennreal_def nn_integral_noteq_infinite top.not_eq_extremum)
  have "(\<integral>\<^sup>+x. f x * indicator ?A x \<partial>M) = (\<integral>\<^sup>+x. \<infinity> * indicator ?A x \<partial>M)" 
    by (metis (mono_tags, lifting) indicator_inter_arith indicator_simps(2) mem_Collect_eq mult_eq_0_iff)
  also have "\<dots> = \<infinity> * emeasure M ?A" 
    using assms(1) by (intro nn_integral_cmult_indicator, simp)
  also have "\<dots> = \<infinity>" 
    using * by fastforce
  finally have "(\<integral>\<^sup>+x. f x * indicator ?A x \<partial>M) = \<infinity>" .
  moreover have "(\<integral>\<^sup>+x. f x * indicator ?A x \<partial>M) \<le> (\<integral>\<^sup>+x. f x \<partial>M)" 
    by (intro nn_integral_mono, simp add: indicator_def)
  ultimately show ?case using assms(2) by simp
qed

text \<open>Convergence in L1-Norm implies existence of a subsequence which convergences almost everywhere. 
      This lemma is easier to use than the existing one in \<^theory>\<open>HOL-Analysis.Bochner_Integration\<close>\<close>

lemma cauchy_L1_AE_cauchy_subseq:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "\<And>n. integrable M (s n)"
      and "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. LINT x|M. norm (s i x - s j x) < e"
  obtains r where "strict_mono r" "AE x in M. Cauchy (\<lambda>i. s (r i) x)"
proof-
  have "\<exists>r. \<forall>n. (\<forall>i\<ge>r n. \<forall>j\<ge> r n. LINT x|M. norm (s i x - s j x) < (1 / 2) ^ n) \<and> (r (Suc n) > r n)"
  proof (intro dependent_nat_choice, goal_cases)
    case 1
    then show ?case using assms(2) by presburger
  next
    case (2 x n)
    obtain N where *: "LINT x|M. norm (s i x - s j x) < (1 / 2) ^ Suc n" if "i \<ge> N" "j \<ge> N" for i j 
      using assms(2)[of "(1 / 2) ^ Suc n"] by auto
    {
      fix i j assume "i \<ge> max N (Suc x)" "j \<ge> max N (Suc x)"
      hence "integral\<^sup>L M (\<lambda>x. norm (s i x - s j x)) < (1 / 2) ^ Suc n" using * by fastforce
    }
    then show ?case by fastforce
  qed
  then obtain r where strict_mono: "strict_mono r" and "\<forall>i\<ge>r n. \<forall>j\<ge> r n. LINT x|M. norm (s i x - s j x) < (1 / 2) ^ n" for n 
    using strict_mono_Suc_iff by blast
  hence r_is: "LINT x|M. norm (s (r (Suc n)) x - s (r n) x) < (1 / 2) ^ n" for n by (simp add: strict_mono_leD)

  define g where "g = (\<lambda>n x. (\<Sum>i\<le>n. ennreal (norm (s (r (Suc i)) x - s (r i) x))))"
  define g' where "g' = (\<lambda>x. \<Sum>i. ennreal (norm (s (r (Suc i)) x - s (r i) x)))"

  have integrable_g: "(\<integral>\<^sup>+ x. g n x \<partial>M) < 2" for n
  proof -
    have "(\<integral>\<^sup>+ x. g n x \<partial>M) = (\<integral>\<^sup>+ x. (\<Sum>i\<le>n. ennreal (norm (s (r (Suc i)) x - s (r i) x))) \<partial>M)"
      using g_def by simp
    also have "\<dots> = (\<Sum>i\<le>n. (\<integral>\<^sup>+ x. ennreal (norm (s (r (Suc i)) x - s (r i) x)) \<partial>M))" 
      by (intro nn_integral_sum, simp)
    also have "\<dots> = (\<Sum>i\<le>n. LINT x|M. norm (s (r (Suc i)) x - s (r i) x))" 
      unfolding dist_norm using assms(1) by (subst nn_integral_eq_integral[OF integrable_norm], auto)
    also have "\<dots> < ennreal (\<Sum>i\<le>n. (1 / 2) ^ i)" 
      by (intro ennreal_lessI[OF sum_pos sum_strict_mono[OF finite_atMost _ r_is]], auto)
    also have "\<dots> \<le> ennreal 2" 
      unfolding sum_gp0[of "1 / 2" n] by (intro ennreal_leI, auto)
    finally show "(\<integral>\<^sup>+ x. g n x \<partial>M) < 2" by simp
  qed

  have integrable_g': "(\<integral>\<^sup>+ x. g' x \<partial>M) \<le> 2"
  proof -
    have "incseq (\<lambda>n. g n x)" for x by (intro incseq_SucI, auto simp add: g_def ennreal_leI)
    hence "convergent (\<lambda>n. g n x)" for x
      unfolding convergent_def using LIMSEQ_incseq_SUP by fast
    hence "(\<lambda>n. g n x) \<longlonglongrightarrow> g' x" for x 
      unfolding g_def g'_def by (intro summable_iff_convergent'[THEN iffD2, THEN summable_LIMSEQ'], blast)
    hence "(\<integral>\<^sup>+ x. g' x \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. g n x) \<partial>M)" by (metis lim_imp_Liminf trivial_limit_sequentially)
    also have "\<dots> \<le> liminf (\<lambda>n. \<integral>\<^sup>+ x. g n x \<partial>M)" by (intro nn_integral_liminf, simp add: g_def)
    also have "\<dots> \<le> liminf (\<lambda>n. 2)" using integrable_g by (intro Liminf_mono) (simp add: order_le_less)
    also have "\<dots> = 2" 
      using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
    finally show ?thesis .
  qed
  hence "AE x in M. g' x < \<infinity>" 
    by (intro finite_nn_integral_imp_ae_finite) (auto simp add: order_le_less_trans g'_def)
  moreover have "summable (\<lambda>i. norm (s (r (Suc i)) x - s (r i) x))" if "g' x \<noteq> \<infinity>" for x 
    using that unfolding g'_def by (intro summable_suminf_not_top) fastforce+ 
  ultimately have ae_summable: "AE x in M. summable (\<lambda>i. s (r (Suc i)) x - s (r i) x)" 
    using summable_norm_cancel unfolding dist_norm by force

  {
    fix x assume "summable (\<lambda>i. s (r (Suc i)) x - s (r i) x)"
    hence "(\<lambda>n. \<Sum>i<n. s (r (Suc i)) x - s (r i) x) \<longlonglongrightarrow> (\<Sum>i. s (r (Suc i)) x - s (r i) x)" 
      using summable_LIMSEQ by blast
    moreover have "(\<lambda>n. (\<Sum>i<n. s (r (Suc i)) x - s (r i) x)) = (\<lambda>n. s (r n) x - s (r 0) x)" 
      using sum_lessThan_telescope by fastforce
    ultimately have "(\<lambda>n. s (r n) x - s (r 0) x) \<longlonglongrightarrow> (\<Sum>i. s (r (Suc i)) x - s (r i) x)" by argo
    hence "(\<lambda>n. s (r n) x - s (r 0) x + s (r 0) x) \<longlonglongrightarrow> (\<Sum>i. s (r (Suc i)) x - s (r i) x) + s (r 0) x" 
      by (intro isCont_tendsto_compose[of _ "\<lambda>z. z + s (r 0) x"], auto)
    hence "Cauchy (\<lambda>n. s (r n) x)" by (simp add: LIMSEQ_imp_Cauchy)
  }
  hence "AE x in M. Cauchy (\<lambda>i. s (r i) x)" using ae_summable by fast
  thus ?thesis by (rule that[OF strict_mono(1)])
qed

subsection \<open>Totally Ordered Banach Spaces\<close>

lemma integrable_max[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology}"
  assumes fg[measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. max (f x) (g x))"
proof (rule Bochner_Integration.integrable_bound)
  {
    fix x y :: 'b                                             
    have "norm (max x y) \<le> max (norm x) (norm y)" by linarith
    also have "\<dots> \<le> norm x + norm y" by simp
    finally have "norm (max x y) \<le> norm (norm x + norm y)" by simp
  }
  thus "AE x in M. norm (max (f x) (g x)) \<le> norm (norm (f x) + norm (g x))" by simp
qed (auto intro: Bochner_Integration.integrable_add[OF integrable_norm[OF fg(1)] integrable_norm[OF fg(2)]])

lemma integrable_min[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology}"
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. min (f x) (g x))"
proof -
  have "norm (min (f x) (g x)) \<le> norm (f x) \<or> norm (min (f x) (g x)) \<le> norm (g x)" for x by linarith
  thus ?thesis 
    by (intro integrable_bound[OF integrable_max[OF integrable_norm(1,1), OF assms]], auto)
qed

text \<open>Restatement of \<open>integral_nonneg_AE\<close> for functions taking values in a Banach space.\<close>
lemma integral_nonneg_AE_banach:                        
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes [measurable]: "f \<in> borel_measurable M" and nonneg: "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^sup>L M f"
proof cases
  assume integrable: "integrable M f"
  hence max: "(\<lambda>x. max 0 (f x)) \<in> borel_measurable M" "\<And>x. 0 \<le> max 0 (f x)" "integrable M (\<lambda>x. max 0 (f x))" by auto
  hence "0 \<le> integral\<^sup>L M (\<lambda>x. max 0 (f x))"
  proof -
  obtain s where *: "\<And>i. simple_function M (s i)" 
                    "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" 
                    "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" 
                    "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" 
    using integrable_implies_simple_function_sequence[OF integrable] by blast
  have simple: "\<And>i. simple_function M (\<lambda>x. max 0 (s i x))" 
    using * by fast
    have "\<And>i. {y \<in> space M. max 0 (s i y) \<noteq> 0} \<subseteq> {y \<in> space M. s i y \<noteq> 0}" 
      unfolding max_def by force
    moreover have "\<And>i. {y \<in> space M. s i y \<noteq> 0} \<in> sets M" 
      using * by measurable
    ultimately have "\<And>i. emeasure M {y \<in> space M. max 0 (s i y) \<noteq> 0} \<le> emeasure M {y \<in> space M. s i y \<noteq> 0}" 
      by (rule emeasure_mono) 
    hence **:"\<And>i. emeasure M {y \<in> space M. max 0 (s i y) \<noteq> 0} \<noteq> \<infinity>" 
      using *(2) by (auto intro: order.strict_trans1 simp add:  top.not_eq_extremum)
    have "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. max 0 (s i x)) \<longlonglongrightarrow> max 0 (f x)"
      using *(3) tendsto_max by blast
    moreover have "\<And>x i. x \<in> space M \<Longrightarrow> norm (max 0 (s i x)) \<le> norm (2 *\<^sub>R f x)" 
      using *(4) unfolding max_def by auto
    ultimately have tendsto: "(\<lambda>i. integral\<^sup>L M (\<lambda>x. max 0 (s i x))) \<longlonglongrightarrow> integral\<^sup>L M (\<lambda>x. max 0 (f x))" 
      using borel_measurable_simple_function simple integrable by (intro integral_dominated_convergence[OF max(1) _ integrable_norm[OF integrable_scaleR_right], of _ 2 f], blast+)
    {
      fix h :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}" 
      assume "simple_function M h" "emeasure M {y \<in> space M. h y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<longrightarrow> h x \<ge> 0"
      hence *: "integral\<^sup>L M h \<ge> 0"
      proof (induct rule: integrable_simple_function_induct_nn)
        case (cong f g)                   
        then show ?case using Bochner_Integration.integral_cong by force
      next
        case (indicator A y)
        hence "A \<noteq> {} \<Longrightarrow> y \<ge> 0" using sets.sets_into_space by fastforce
        then show ?case using indicator by (cases "A = {}", auto simp add: scaleR_nonneg_nonneg)
      next
        case (add f g)
        then show ?case by (simp add: integrable_simple_function)
      qed
    }
    thus ?thesis using LIMSEQ_le_const[OF tendsto, of 0] ** simple by fastforce
  qed
  also have "\<dots> = integral\<^sup>L M f" using nonneg by (auto intro: integral_cong_AE)
  finally show ?thesis .
qed (simp add: not_integrable_integral_eq)

lemma integral_mono_AE_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  using integral_nonneg_AE_banach[of "\<lambda>x. g x - f x"] assms Bochner_Integration.integral_diff[OF assms(1,2)] by force

lemma integral_mono_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  using integral_mono_AE_banach assms by blast

subsection \<open>Auxiliary Lemmas for Set Integrals\<close>

lemma nn_set_integral_eq_set_integral:
  assumes [measurable]:"integrable M f"
      and "AE x \<in> A in M. 0 \<le> f x" "A \<in> sets M"
    shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = (\<integral> x \<in> A. f x \<partial>M)"
proof-
  have "(\<integral>\<^sup>+x. indicator A x *\<^sub>R f x \<partial>M) = (\<integral> x \<in> A. f x \<partial>M)"
    unfolding set_lebesgue_integral_def 
    using assms(2) by (intro nn_integral_eq_integral[of _ "\<lambda>x. indicat_real A x *\<^sub>R f x"], blast intro: assms integrable_mult_indicator, fastforce)
  moreover have "(\<integral>\<^sup>+x. indicator A x *\<^sub>R f x \<partial>M) = (\<integral>\<^sup>+x\<in>A. f x \<partial>M)"  
    by (metis ennreal_0 indicator_simps(1) indicator_simps(2) mult.commute mult_1 mult_zero_left real_scaleR_def)
  ultimately show ?thesis by argo
qed

lemma set_integral_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "set_lebesgue_integral (restrict_space M \<Omega>) A f = set_lebesgue_integral M A (\<lambda>x. indicator \<Omega> x *\<^sub>R f x)"
  unfolding set_lebesgue_integral_def 
  by (subst integral_restrict_space, auto intro!: integrable_mult_indicator assms simp: mult.commute)

lemma set_integral_const:
  fixes c :: "'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M" "emeasure M A \<noteq> \<infinity>"
  shows "set_lebesgue_integral M A (\<lambda>_. c) = measure M A *\<^sub>R c"
  unfolding set_lebesgue_integral_def 
  using assms by (metis has_bochner_integral_indicator has_bochner_integral_integral_eq infinity_ennreal_def less_top)

lemma set_integral_mono_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def
  by (auto intro: integral_mono_banach split: split_indicator)

lemma set_integral_mono_AE_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "set_integrable M A f" "set_integrable M A g" "AE x\<in>A in M. f x \<le> g x"
  shows "set_lebesgue_integral M A f \<le> set_lebesgue_integral M A g" using assms unfolding set_lebesgue_integral_def by (auto simp add: set_integrable_def intro!: integral_mono_AE_banach[of M "\<lambda>x. indicator A x *\<^sub>R f x" "\<lambda>x. indicator A x *\<^sub>R g x"], simp add: indicator_def)

subsection \<open>Integrability and Measurability of the Diameter\<close>

context
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}" and M
  assumes bounded: "\<And>x. x \<in> space M \<Longrightarrow> bounded (range (\<lambda>i. s i x))"
begin

lemma borel_measurable_diameter: 
  assumes [measurable]: "\<And>i. (s i) \<in> borel_measurable M"
  shows "(\<lambda>x. diameter {s i x |i. n \<le> i}) \<in> borel_measurable M"
proof -
  have "{s i x |i. N \<le> i} \<noteq> {}" for x N by blast
  hence diameter_SUP: "diameter {s i x |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x))" for x N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  
  have "case_prod dist ` ({s i x |i. n \<le> i} \<times> {s i x |i. n \<le> i}) = ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..}))" for x by fast
  hence *: "(\<lambda>x. diameter {s i x |i. n \<le> i}) =  (\<lambda>x. Sup ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..})))" using diameter_SUP by (simp add: case_prod_beta')
  
  have "bounded ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..}))" if "x \<in> space M" for x by (rule bounded_imp_dist_bounded[OF bounded, OF that])
  hence bdd: "bdd_above ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..}))" if "x \<in> space M" for x using that bounded_imp_bdd_above by presburger
  have "fst p \<in> borel_measurable M" "snd p \<in> borel_measurable M" if "p \<in> s ` {n..} \<times> s ` {n..}" for p using that by fastforce+
  hence "(\<lambda>x. fst p x - snd p x) \<in> borel_measurable M" if "p \<in> s ` {n..} \<times> s ` {n..}" for p using that borel_measurable_diff by simp
  hence "(\<lambda>x. case p of (f, g) \<Rightarrow> dist (f x) (g x)) \<in> borel_measurable M" if "p \<in> s ` {n..} \<times> s ` {n..}" for p unfolding dist_norm using that by measurable
  moreover have "countable (s ` {n..} \<times> s ` {n..})" by (intro countable_SIGMA countable_image, auto)
  ultimately show ?thesis unfolding * by (auto intro!: borel_measurable_cSUP bdd)
qed

lemma integrable_bound_diameter:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f" 
      and [measurable]: "\<And>i. (s i) \<in> borel_measurable M"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> f x"
    shows "integrable M (\<lambda>x. diameter {s i x |i. n \<le> i})"
proof -
  have "{s i x |i. N \<le> i} \<noteq> {}" for x N by blast
  hence diameter_SUP: "diameter {s i x |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x))" for x N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  {
    fix x assume x: "x \<in> space M"
    let ?S = "(\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..})"
    have "case_prod dist ` ({s i x |i. n \<le> i} \<times> {s i x |i. n \<le> i}) = (\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..})" by fast
    hence *: "diameter {s i x |i. n \<le> i} =  Sup ?S" using diameter_SUP by (simp add: case_prod_beta')
    
    have "bounded ?S" by (rule bounded_imp_dist_bounded[OF bounded[OF x]])
    hence Sup_S_nonneg:"0 \<le> Sup ?S" by (auto intro!: cSup_upper2 x bounded_imp_bdd_above)

    have "dist (s i x) (s j x) \<le>  2 * f x" for i j by (intro dist_triangle2[THEN order_trans, of _ 0]) (metis norm_conv_dist assms(3) x add_mono mult_2)
    hence "\<forall>c \<in> ?S. c \<le> 2 * f x" by force
    hence "Sup ?S \<le> 2 * f x" by (intro cSup_least, auto)
    hence "norm (Sup ?S) \<le> 2 * norm (f x)" using Sup_S_nonneg by auto
    also have "\<dots> = norm (2 *\<^sub>R f x)" by simp
    finally have "norm (diameter {s i x |i. n \<le> i}) \<le> norm (2 *\<^sub>R f x)" unfolding * .
  }
  hence "AE x in M. norm (diameter {s i x |i. n \<le> i}) \<le> norm (2 *\<^sub>R f x)" by blast
  thus  "integrable M (\<lambda>x. diameter {s i x |i. n \<le> i})" using borel_measurable_diameter by (intro Bochner_Integration.integrable_bound[OF assms(1)[THEN integrable_scaleR_right[of 2]]], measurable)
qed
end    

subsection \<open>Averaging Theorem\<close>

text \<open>We aim to lift results from the real case to arbitrary Banach spaces. 
      Our fundamental tool in this regard will be the averaging theorem. The proof of this theorem is due to Serge Lang (Real and Functional Analysis) \<^cite>\<open>"Lang_1993"\<close>. 
      The theorem allows us to make statements about a function's value almost everywhere, depending on the value its integral takes on various sets of the measure space.\<close>

text \<open>Before we introduce and prove the averaging theorem, we will first show the following lemma which is crucial for our proof. 
      While not stated exactly in this manner, our proof makes use of the characterization of second-countable topological spaces given in the book General Topology by Ryszard Engelking (Theorem 4.1.15) \<^cite>\<open>"engelking_1989"\<close>.
    (Engelking's book \emph{General Topology})\<close>

lemma balls_countable_basis:
  obtains D :: "'a :: {metric_space, second_countable_topology} set" 
  where "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))"
    and "countable D"
    and "D \<noteq> {}"    
proof -
  obtain D :: "'a set" where dense_subset: "countable D" "D \<noteq> {}" "\<lbrakk>open U; U \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>y \<in> D. y \<in> U" for U using countable_dense_exists by blast
  have "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))"
  proof (intro topological_basis_iff[THEN iffD2], fast, clarify)
    fix U and x :: 'a assume asm: "open U" "x \<in> U"
    obtain e where e: "e > 0" "ball x e \<subseteq> U" using asm openE by blast
    obtain y where y: "y \<in> D" "y \<in> ball x (e / 3)" using dense_subset(3)[OF open_ball, of x "e / 3"] centre_in_ball[THEN iffD2, OF divide_pos_pos[OF e(1), of 3]] by force
    obtain r where r: "r \<in> \<rat> \<inter> {e/3<..<e/2}" unfolding Rats_def using of_rat_dense[OF divide_strict_left_mono[OF _ e(1)], of 2 3] by auto

    have *: "x \<in> ball y r" using r y by (simp add: dist_commute)
    hence "ball y r \<subseteq> U" using r by (intro order_trans[OF _ e(2)], simp, metric)
    moreover have "ball y r \<in> (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))" using y(1) r by force
    ultimately show "\<exists>B'\<in>(case_prod ball ` (D \<times> (\<rat> \<inter> {0<..}))). x \<in> B' \<and> B' \<subseteq> U" using * by meson
  qed
  thus ?thesis using that dense_subset by blast
qed

context sigma_finite_measure
begin         

text \<open>To show statements concerning \<open>\<sigma>\<close>-finite measure spaces, one usually shows the statement for finite measure spaces and uses a limiting argument to show it for the \<open>\<sigma>\<close>-finite case.
      The following induction scheme formalizes this.\<close>
lemma sigma_finite_measure_induct[case_names finite_measure, consumes 0]:
  assumes "\<And>(N :: 'a measure) \<Omega>. finite_measure N 
                              \<Longrightarrow> N = restrict_space M \<Omega>
                              \<Longrightarrow> \<Omega> \<in> sets M 
                              \<Longrightarrow> emeasure N \<Omega> \<noteq> \<infinity> 
                              \<Longrightarrow> emeasure N \<Omega> \<noteq> 0 
                              \<Longrightarrow> almost_everywhere N Q"
      and [measurable]: "Measurable.pred M Q"
  shows "almost_everywhere M Q"
proof -
  have *: "almost_everywhere N Q" if "finite_measure N" "N = restrict_space M \<Omega>" "\<Omega> \<in> sets M" "emeasure N \<Omega> \<noteq> \<infinity>" for N \<Omega> using that by (cases "emeasure N \<Omega> = 0", auto intro: emeasure_0_AE assms(1))

  obtain A :: "nat \<Rightarrow> 'a set" where A: "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" and emeasure_finite: "emeasure M (A i) \<noteq> \<infinity>" for i using sigma_finite by metis
  note A(1)[measurable]
  have space_restr: "space (restrict_space M (A i)) = A i" for i unfolding space_restrict_space by simp
  {
    fix i    
    have *: "{x \<in> A i \<inter> space M. Q x} = {x \<in> space M. Q x} \<inter> (A i)" by fast
    have "Measurable.pred (restrict_space M (A i)) Q" using A by (intro measurableI, auto simp add: space_restr intro!: sets_restrict_space_iff[THEN iffD2], measurable, auto)
  }
  note this[measurable]
  {
    fix i
    have "finite_measure (restrict_space M (A i))" using emeasure_finite by (intro finite_measureI, subst space_restr, subst emeasure_restrict_space, auto)
    hence "emeasure (restrict_space M (A i)) {x \<in> A i. \<not>Q x} = 0" using emeasure_finite by (intro AE_iff_measurable[THEN iffD1, OF _ _ *], measurable, subst space_restr[symmetric], intro sets.top, auto simp add: emeasure_restrict_space)
    hence "emeasure M {x \<in> A i. \<not> Q x} = 0" by (subst emeasure_restrict_space[symmetric], auto)
  }
  hence "emeasure M (\<Union>i. {x \<in> A i. \<not> Q x}) = 0" by (intro emeasure_UN_eq_0, auto)
  moreover have "(\<Union>i. {x \<in> A i. \<not> Q x}) = {x \<in> space M. \<not> Q x}" using A by auto
  ultimately show ?thesis by (intro AE_iff_measurable[THEN iffD2], auto)
qed

text \<open>Real Functional Analysis - Lang\<close>
text \<open>The Averaging Theorem allows us to make statements concerning how a function behaves almost everywhere, depending on its behaviour on average.\<close>
lemma averaging_theorem:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes [measurable]: "integrable M f" 
      and closed: "closed S"
      and "\<And>A. A \<in> sets M \<Longrightarrow> measure M A > 0 \<Longrightarrow> (1 / measure M A) *\<^sub>R set_lebesgue_integral M A f \<in> S"
    shows "AE x in M. f x \<in> S"
proof (induct rule: sigma_finite_measure_induct)
  case (finite_measure N \<Omega>)

  interpret finite_measure N by (rule finite_measure)
  
  have integrable[measurable]: "integrable N f" using assms finite_measure by (auto simp: integrable_restrict_space integrable_mult_indicator)
  have average: "(1 / Sigma_Algebra.measure N A) *\<^sub>R set_lebesgue_integral N A f \<in> S" if "A \<in> sets N" "measure N A > 0" for A
  proof -
    have *: "A \<in> sets M" using that by (simp add: sets_restrict_space_iff finite_measure)
    have "A = A \<inter> \<Omega>" by (metis finite_measure(2,3) inf.orderE sets.sets_into_space space_restrict_space that(1))
    hence "set_lebesgue_integral N A f = set_lebesgue_integral M A f" unfolding finite_measure by (subst set_integral_restrict_space, auto simp add: finite_measure set_lebesgue_integral_def indicator_inter_arith[symmetric])
    moreover have "measure N A = measure M A" using that by (auto intro!: measure_restrict_space simp add: finite_measure sets_restrict_space_iff)
    ultimately show ?thesis using that * assms(3) by presburger
  qed

  obtain D :: "'b set" where balls_basis: "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))" and countable_D: "countable D" using balls_countable_basis by blast
  have countable_balls: "countable (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))" using countable_rat countable_D by blast

  obtain B where B_balls: "B \<subseteq> case_prod ball ` (D \<times> (\<rat> \<inter> {0<..}))" "\<Union>B = -S" using topological_basis[THEN iffD1, OF balls_basis] open_Compl[OF assms(2)] by meson
  hence countable_B: "countable B" using countable_balls countable_subset by fast

  define b where "b = from_nat_into (B \<union> {{}})"
  have "B \<union> {{}} \<noteq> {}" by simp
  have range_b: "range b = B \<union> {{}}" using countable_B by (auto simp add: b_def intro!: range_from_nat_into)
  have open_b: "open (b i)" for i unfolding b_def using B_balls open_ball from_nat_into[of "B \<union> {{}}" i] by force
  have Union_range_b: "\<Union>(range b) = -S" using B_balls range_b by simp

  {
    fix v r assume ball_in_Compl: "ball v r \<subseteq> -S"
    define A where "A = f -` ball v r \<inter> space N"
    have dist_less: "dist (f x) v < r" if "x \<in> A" for x using that unfolding A_def vimage_def by (simp add: dist_commute)
    hence AE_less: "AE x \<in> A in N. norm (f x - v) < r" by (auto simp add: dist_norm)
    have *: "A \<in> sets N" unfolding A_def by simp
    have "emeasure N A = 0" 
    proof -
      {
        assume asm: "emeasure N A > 0"
        hence measure_pos: "measure N A > 0" unfolding emeasure_eq_measure by simp
        hence "(1 / measure N A) *\<^sub>R set_lebesgue_integral N A f - v 
             = (1 / measure N A) *\<^sub>R set_lebesgue_integral N A (\<lambda>x. f x - v)" 
          using integrable integrable_const * 
          by (subst set_integral_diff(2), auto simp add: set_integrable_def set_integral_const[OF *] algebra_simps intro!: integrable_mult_indicator)
        moreover have "norm (\<integral>x\<in>A. (f x - v)\<partial>N) \<le> (\<integral>x\<in>A. norm (f x - v)\<partial>N)" 
          using * by (auto intro!: integral_norm_bound[of N "\<lambda>x. indicator A x *\<^sub>R (f x - v)", THEN order_trans] integrable_mult_indicator integrable simp add: set_lebesgue_integral_def)
        ultimately have "norm ((1 / measure N A) *\<^sub>R set_lebesgue_integral N A f - v) 
                       \<le> set_lebesgue_integral N A (\<lambda>x. norm (f x - v)) / measure N A" using asm by (auto intro: divide_right_mono)
        also have "\<dots> < set_lebesgue_integral N A (\<lambda>x. r) / measure N A" 
          unfolding set_lebesgue_integral_def 
          using asm * integrable integrable_const AE_less measure_pos
          by (intro divide_strict_right_mono integral_less_AE[of _ _ A] integrable_mult_indicator)
            (fastforce simp add: dist_less dist_norm indicator_def)+
        also have "\<dots> = r" using * measure_pos by (simp add: set_integral_const)
        finally have "dist ((1 / measure N A) *\<^sub>R set_lebesgue_integral N A f) v < r" by (subst dist_norm)
        hence "False" using average[OF * measure_pos] by (metis ComplD dist_commute in_mono mem_ball ball_in_Compl)
      }
      thus ?thesis by fastforce
    qed
  }
  note * = this
  {
    fix b' assume "b' \<in> B"
    hence ball_subset_Compl: "b' \<subseteq> -S" and ball_radius_pos: "\<exists>v \<in> D. \<exists>r>0. b' = ball v r" using B_balls by (blast, fast)
  }
  note ** = this
  hence "emeasure N (f -` b i \<inter> space N) = 0" for i by (cases "b i = {}", simp) (metis UnE singletonD  * range_b[THEN eq_refl, THEN range_subsetD])
  hence "emeasure N (\<Union>i. f -` b i \<inter> space N) = 0" using open_b by (intro emeasure_UN_eq_0) fastforce+
  moreover have "(\<Union>i. f -` b i \<inter> space N) = f -` (\<Union>(range b)) \<inter> space N" by blast
  ultimately have "emeasure N (f -` (-S) \<inter> space N) = 0" using Union_range_b by argo
  hence "AE x in N. f x \<notin> -S" using open_Compl[OF assms(2)] by (intro AE_iff_measurable[THEN iffD2], auto)
  thus ?case by force
qed (simp add: pred_sets2[OF borel_closed] assms(2))
  
lemma density_zero:
  fixes f::"'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
      and density_0: "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f = 0"
  shows "AE x in M. f x = 0"
  using averaging_theorem[OF assms(1), of "{0}"] assms(2)
  by (simp add: scaleR_nonneg_nonneg)

text \<open>The following lemma shows that densities are unique in Banach spaces.\<close>
lemma density_unique_banach:
  fixes f f'::"'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f" "integrable M f'"
      and density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f = set_lebesgue_integral M A f'"
  shows "AE x in M. f x = f' x"
proof-
  { 
    fix A assume asm: "A \<in> sets M"
    hence "LINT x|M. indicat_real A x *\<^sub>R (f x - f' x) = 0" using density_eq assms(1,2) by (simp add: set_lebesgue_integral_def algebra_simps Bochner_Integration.integral_diff[OF integrable_mult_indicator(1,1)])
  }
  thus ?thesis using density_zero[OF Bochner_Integration.integrable_diff[OF assms(1,2)]] by (simp add: set_lebesgue_integral_def)
qed

lemma density_nonneg:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" 
      and "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f \<ge> 0"
    shows "AE x in M. f x \<ge> 0"
  using averaging_theorem[OF assms(1), of "{0..}", OF closed_atLeast] assms(2)
  by (simp add: scaleR_nonneg_nonneg)

corollary integral_nonneg_eq_0_iff_AE_banach:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes f[measurable]: "integrable M f" and nonneg: "AE x in M. 0 \<le> f x"
  shows "integral\<^sup>L M f = 0 \<longleftrightarrow> (AE x in M. f x = 0)"
proof 
  assume *: "integral\<^sup>L M f = 0"
  {
    fix A assume asm: "A \<in> sets M"
    have "0 \<le> integral\<^sup>L M (\<lambda>x. indicator A x *\<^sub>R f x)" using nonneg by (subst integral_zero[of M, symmetric], intro integral_mono_AE_banach integrable_mult_indicator asm f integrable_zero, auto simp add: indicator_def)
    moreover have "\<dots> \<le> integral\<^sup>L M f" using nonneg by (intro integral_mono_AE_banach integrable_mult_indicator asm f, auto simp add: indicator_def)
    ultimately have "set_lebesgue_integral M A f = 0" unfolding set_lebesgue_integral_def using * by force
  }
  thus "AE x in M. f x = 0" by (intro density_zero f, blast)
qed (auto simp add: integral_eq_zero_AE)

corollary integral_eq_mono_AE_eq_AE:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "integral\<^sup>L M f = integral\<^sup>L M g" "AE x in M. f x \<le> g x" 
  shows "AE x in M. f x = g x"
proof -
  define h where "h = (\<lambda>x. g x - f x)"
  have "AE x in M. h x = 0" unfolding h_def using assms by (subst integral_nonneg_eq_0_iff_AE_banach[symmetric]) auto
  then show ?thesis unfolding h_def by auto
qed

end

end
