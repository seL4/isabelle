(*  Title:      HOL/Analysis/Set_Integral.thy
    Author:     Jeremy Avigad (CMU), Johannes Hölzl (TUM), Luke Serafin (CMU)
    Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr

Notation and useful facts for working with integrals over a set.

TODO: keep all these? Need unicode translations as well.
*)

theory Set_Integral
  imports Radon_Nikodym
begin

(*
    Notation
*)

definition\<^marker>\<open>tag important\<close> "set_borel_measurable M A f \<equiv> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"

definition\<^marker>\<open>tag important\<close>  "set_integrable M A f \<equiv> integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"

definition\<^marker>\<open>tag important\<close>  "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. indicator A x *\<^sub>R f x)"

syntax
  "_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  ("(4LINT (_):(_)/|(_)./ _)" [0,60,110,61] 60)

translations
  "LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

(*
    Notation for integration wrt lebesgue measure on the reals:

      LBINT x. f
      LBINT x : A. f

    TODO: keep all these? Need unicode.
*)

syntax
  "_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
  ("(2LBINT _./ _)" [0,60] 60)

syntax
  "_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
  ("(3LBINT _:_./ _)" [0,60,61] 60)

(*
    Basic properties
*)

(*
lemma indicator_abs_eq: "\<And>A x. \<bar>indicator A x\<bar> = ((indicator A x) :: real)"
  by (auto simp add: indicator_def)
*)

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
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
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

lemma set_integral_scaleR_right [simp]: "LINT t:A|M. a *\<^sub>R f t = a *\<^sub>R (LINT t:A|M. f t)"
  unfolding set_lebesgue_integral_def
  by (subst integral_scaleR_right[symmetric]) (auto intro!: Bochner_Integration.integral_cong)

lemma set_integral_mult_right [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
  unfolding set_lebesgue_integral_def
  by (subst integral_mult_right_zero[symmetric]) auto

lemma set_integral_mult_left [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "LINT t:A|M. f t * a = (LINT t:A|M. f t) * a"
  unfolding set_lebesgue_integral_def
  by (subst integral_mult_left_zero[symmetric]) auto

lemma set_integral_divide_zero [simp]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  shows "LINT t:A|M. f t / a = (LINT t:A|M. f t) / a"
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
    and "LINT x:A|M. f x + g x = (LINT x:A|M. f x) + (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def by (simp_all add: scaleR_add_right)

lemma set_integral_diff [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x - g x)" and "LINT x:A|M. f x - g x =
    (LINT x:A|M. f x) - (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def by (simp_all add: scaleR_diff_right)

lemma set_integral_uminus: "set_integrable M A f \<Longrightarrow> LINT x:A|M. - f x = - (LINT x:A|M. f x)"
  unfolding set_integrable_def set_lebesgue_integral_def
  by (subst integral_minus[symmetric]) simp_all

lemma set_integral_complex_of_real:
  "LINT x:A|M. complex_of_real (f x) = of_real (LINT x:A|M. f x)"
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
shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  using assms
  unfolding set_integrable_def set_lebesgue_integral_def
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric] scaleR_add_left)

lemma set_integral_cong_set:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_borel_measurable M A f" "set_borel_measurable M B f"
    and ae: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "LINT x:B|M. f x = LINT x:A|M. f x"
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
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
proof -
  have f: "set_integrable M (A \<union> B) f"
    by (intro set_integrable_Un assms)
  then have f': "set_borel_measurable M (A \<union> B) f"
    using integrable_iff_bounded set_borel_measurable_def set_integrable_def by blast
  have "LINT x:A\<union>B|M. f x = LINT x:(A - A \<inter> B) \<union> (B - A \<inter> B)|M. f x"
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
      then guess i ..
      then have *: "eventually (\<lambda>i. x \<in> A i) sequentially"
        using \<open>x \<in> A i\<close> \<open>mono A\<close> by (auto simp: eventually_sequentially mono_def)
      show ?thesis
        apply (intro tendsto_eventually)
        using *
        apply eventually_elim
        apply (auto split: split_indicator)
        done
    qed auto }
  then show "(\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R f x) \<in> borel_measurable M"
    apply (rule borel_measurable_LIMSEQ_real)
    apply assumption
    using intgbl set_integrable_def by blast
qed

(* Proof from Royden Real Analysis, p. 91. *)
lemma lebesgue_integral_countable_add:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
    and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"
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
    apply (rule Bochner_Integration.integral_cong[OF refl])
    apply (subst suminf_scaleR_left[OF sums_summable[OF indicator_sums, OF disj], symmetric])
    using sums_unique[OF indicator_sums[OF disj]]
    apply auto
    done
qed

lemma set_integral_cont_up:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
shows "(\<lambda>i. LINT x:(A i)|M. f x) \<longlonglongrightarrow> LINT x:(\<Union>i. A i)|M. f x"
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
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) \<longlonglongrightarrow> LINT x:(\<Inter>i. A i)|M. f x"
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


abbreviation complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_integrable M f \<equiv> integrable M f"

abbreviation complex_lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" ("integral\<^sup>C") where
  "integral\<^sup>C M f == integral\<^sup>L M f"

syntax
  "_complex_lebesgue_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> 'a measure \<Rightarrow> complex"
 ("\<integral>\<^sup>C _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>Cx. f \<partial>M" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

syntax
  "_ascii_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  ("(3CLINT _|_. _)" [0,110,60] 60)

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
("(4CLINT _:_|_. _)" [0,60,110,61] 60)

translations
"CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

lemma set_measurable_continuous_on_ivl:
  assumes "continuous_on {a..b} (f :: real \<Rightarrow> real)"
  shows "set_borel_measurable borel {a..b} f"
  unfolding set_borel_measurable_def
  by (rule borel_measurable_continuous_on_indicator[OF _ assms]) simp


text\<open>This notation is from Sébastien Gouëzel: His use is not directly in line with the
notations in this file, they are more in line with sum, and more readable he thinks.\<close>

abbreviation "set_nn_integral M A f \<equiv> nn_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_set_nn_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>\<^sup>+((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

"_set_lebesgue_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

translations
"\<integral>\<^sup>+x \<in> A. f \<partial>M" == "CONST set_nn_integral M A (\<lambda>x. f)"
"\<integral>x \<in> A. f \<partial>M" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

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
  also have "... = (\<integral>\<^sup>+x. f x * indicator B x \<partial>M) + (\<integral>\<^sup>+x. f x * indicator C x \<partial>M)"
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
  also have "... = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) + (\<integral>\<^sup>+x. g x * indicator A x \<partial>M)"
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
  also have "... = (\<integral>\<^sup>+y. f y \<partial>count_space (g`A))"
    by (simp add: assms nn_integral_bij_count_space inj_on_imp_bij_betw)
  also have "... = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
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
  also have "... = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by (rule nn_integral_cmult) auto
  finally have int_liminf: "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
    by simp

  have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M)" for n
    by (rule nn_integral_add) (auto simp add: assms)
  then have "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) =
      limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by simp
  also have "... = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by (rule Limsup_const_add, auto simp add: finint)
  also have "... \<le> (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using assms(4) by (simp add: add_left_mono)
  also have "... = 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
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
  also have "... \<le> ennreal(1/c) * (\<integral>\<^sup>+ x. ennreal(u x) * indicator A x \<partial>M)"
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

end
