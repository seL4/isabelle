(*  Title:      HOL/Probability/Set_Integral.thy
    Author:     Jeremy Avigad, Johannes Hölzl, Luke Serafin

Notation and useful facts for working with integrals over a set.

TODO: keep all these? Need unicode translations as well.
*)

theory Set_Integral
  imports Bochner_Integration Lebesgue_Measure
begin

(* 
    Notation
*)

syntax
"_ascii_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(3LINT _|_. _)" [0,110,60] 60)

translations
"LINT x|M. f" == "CONST lebesgue_integral M (\<lambda>x. f)"

abbreviation "set_borel_measurable M A f \<equiv> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"

abbreviation "set_integrable M A f \<equiv> integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"

abbreviation "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. indicator A x *\<^sub>R f x)"

syntax
"_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4LINT _:_|_. _)" [0,60,110,61] 60)

translations
"LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

abbreviation
  "set_almost_everywhere A M P \<equiv> AE x in M. x \<in> A \<longrightarrow> P x"

syntax
  "_set_almost_everywhere" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool"
("AE _\<in>_ in _. _" [0,0,0,10] 10)

translations
  "AE x\<in>A in M. P" == "CONST set_almost_everywhere A M (\<lambda>x. P)"

(*
    Notation for integration wrt lebesgue measure on the reals:

      LBINT x. f
      LBINT x : A. f

    TODO: keep all these? Need unicode.
*)

syntax
"_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
("(2LBINT _. _)" [0,60] 60)

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

syntax
"_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
("(3LBINT _:_. _)" [0,60,61] 60)

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

(* 
    Basic properties 
*)

(*
lemma indicator_abs_eq: "\<And>A x. abs (indicator A x) = ((indicator A x) :: real)"
  by (auto simp add: indicator_def)
*)

lemma set_lebesgue_integral_cong:
  assumes "A \<in> sets M" and "\<forall>x. x \<in> A \<longrightarrow> f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
  using assms by (auto intro!: integral_cong split: split_indicator simp add: sets.sets_into_space)

lemma set_lebesgue_integral_cong_AE:
  assumes [measurable]: "A \<in> sets M" "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "AE x \<in> A in M. f x = g x"
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
proof-
  have "AE x in M. indicator A x *\<^sub>R f x = indicator A x *\<^sub>R g x"
    using assms by auto
  thus ?thesis by (intro integral_cong_AE) auto
qed

lemma set_integrable_cong_AE:
    "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    AE x \<in> A in M. f x = g x \<Longrightarrow> A \<in> sets M \<Longrightarrow> 
    set_integrable M A f = set_integrable M A g"
  by (rule integrable_cong_AE) auto

lemma set_integrable_subset: 
  fixes M A B and f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"  
  shows "set_integrable M B f"
proof -
  have "set_integrable M B (\<lambda>x. indicator A x *\<^sub>R f x)"
    by (rule integrable_mult_indicator) fact+
  with `B \<subseteq> A` show ?thesis
    by (simp add: indicator_inter_arith[symmetric] Int_absorb2)
qed

(* TODO: integral_cmul_indicator should be named set_integral_const *)
(* TODO: borel_integrable_atLeastAtMost should be named something like set_integrable_Icc_isCont *)

lemma set_integral_scaleR_right [simp]: "LINT t:A|M. a *\<^sub>R f t = a *\<^sub>R (LINT t:A|M. f t)"
  by (subst integral_scaleR_right[symmetric]) (auto intro!: integral_cong)

lemma set_integral_mult_right [simp]: 
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
  by (subst integral_mult_right_zero[symmetric]) (auto intro!: integral_cong)

lemma set_integral_mult_left [simp]: 
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "LINT t:A|M. f t * a = (LINT t:A|M. f t) * a"
  by (subst integral_mult_left_zero[symmetric]) (auto intro!: integral_cong)

lemma set_integral_divide_zero [simp]: 
  fixes a :: "'a::{real_normed_field, field_inverse_zero, second_countable_topology}"
  shows "LINT t:A|M. f t / a = (LINT t:A|M. f t) / a"
  by (subst integral_divide_zero[symmetric], intro integral_cong)
     (auto split: split_indicator)

lemma set_integrable_scaleR_right [simp, intro]:
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a *\<^sub>R f t)"
  unfolding scaleR_left_commute by (rule integrable_scaleR_right)

lemma set_integrable_scaleR_left [simp, intro]:
  fixes a :: "_ :: {banach, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t *\<^sub>R a)"
  using integrable_scaleR_left[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_right [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a * f t)"
  using integrable_mult_right[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_left [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t * a)"
  using integrable_mult_left[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_divide [simp, intro]:
  fixes a :: "'a::{real_normed_field, field_inverse_zero, second_countable_topology}"
  assumes "a \<noteq> 0 \<Longrightarrow> set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. f t / a)"
proof -
  have "integrable M (\<lambda>x. indicator A x *\<^sub>R f x / a)"
    using assms by (rule integrable_divide_zero)
  also have "(\<lambda>x. indicator A x *\<^sub>R f x / a) = (\<lambda>x. indicator A x *\<^sub>R (f x / a))"
    by (auto split: split_indicator)
  finally show ?thesis .
qed

lemma set_integral_add [simp, intro]:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x + g x)"
    and "LINT x:A|M. f x + g x = (LINT x:A|M. f x) + (LINT x:A|M. g x)"
  using assms by (simp_all add: scaleR_add_right)

lemma set_integral_diff [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x - g x)" and "LINT x:A|M. f x - g x =
    (LINT x:A|M. f x) - (LINT x:A|M. g x)"
  using assms by (simp_all add: scaleR_diff_right)

lemma set_integral_reflect:
  fixes S and f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "(LBINT x : S. f x) = (LBINT x : {x. - x \<in> S}. f (- x))"
  using assms
  by (subst lborel_integral_real_affine[where c="-1" and t=0])
     (auto intro!: integral_cong split: split_indicator)

(* question: why do we have this for negation, but multiplication by a constant
   requires an integrability assumption? *)
lemma set_integral_uminus: "set_integrable M A f \<Longrightarrow> LINT x:A|M. - f x = - (LINT x:A|M. f x)"
  by (subst integral_minus[symmetric]) simp_all

lemma set_integral_complex_of_real:
  "LINT x:A|M. complex_of_real (f x) = of_real (LINT x:A|M. f x)"
  by (subst integral_complex_of_real[symmetric])
     (auto intro!: integral_cong split: split_indicator)

lemma set_integral_mono:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
using assms by (auto intro: integral_mono split: split_indicator)

lemma set_integral_mono_AE: 
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "AE x \<in> A in M. f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
using assms by (auto intro: integral_mono_AE split: split_indicator)

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar> :: real)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"] by (simp add: abs_mult ac_simps)

lemma set_integrable_abs_iff:
  fixes f :: "_ \<Rightarrow> real"
  shows "set_borel_measurable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f" 
  by (subst (2) integrable_abs_iff[symmetric]) (simp_all add: abs_mult ac_simps)

lemma set_integrable_abs_iff':
  fixes f :: "_ \<Rightarrow> real"
  shows "f \<in> borel_measurable M \<Longrightarrow> A \<in> sets M \<Longrightarrow> 
    set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
by (intro set_integrable_abs_iff) auto

lemma set_integrable_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_integrable M A f \<longleftrightarrow> set_integrable M B f"
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
  from integrable_add[OF this f_B] show ?thesis
    by (rule integrable_cong[THEN iffD1, rotated 2]) (auto split: split_indicator)
qed

lemma set_integrable_UN:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
    "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
using assms by (induct I) (auto intro!: set_integrable_Un)

lemma set_integral_Un:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      scaleR_add_left assms)

lemma set_integral_cong_set:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "set_borel_measurable M A f" "set_borel_measurable M B f"
    and ae: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "LINT x:B|M. f x = LINT x:A|M. f x"
proof (rule integral_cong_AE)
  show "AE x in M. indicator B x *\<^sub>R f x = indicator A x *\<^sub>R f x"
    using ae by (auto simp: subset_eq split: split_indicator)
qed fact+

lemma set_borel_measurable_subset:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "set_borel_measurable M A f" "B \<in> sets M" and "B \<subseteq> A"
  shows "set_borel_measurable M B f"
proof -
  have "set_borel_measurable M B (\<lambda>x. indicator A x *\<^sub>R f x)"
    by measurable
  also have "(\<lambda>x. indicator B x *\<^sub>R indicator A x *\<^sub>R f x) = (\<lambda>x. indicator B x *\<^sub>R f x)"
    using `B \<subseteq> A` by (auto simp: fun_eq_iff split: split_indicator)
  finally show ?thesis .
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
    by (rule borel_measurable_integrable)
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
    by (intro arg_cong2[where f="op+"] set_integral_cong_set)
       (auto intro!: set_borel_measurable_subset[OF f'])
  finally show ?thesis .
qed

lemma set_integral_finite_Union:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using assms
  apply induct
  apply (auto intro!: set_integral_Un set_integrable_Un set_integrable_UN simp: disjoint_family_on_def)
by (subst set_integral_Un, auto intro: set_integrable_UN)

(* TODO: find a better name? *)
lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) ----> l"
  shows "set_integrable M (\<Union>i. A i) f"
  apply (rule integrable_monotone_convergence[where f = "\<lambda>i::nat. \<lambda>x. indicator (A i) x *\<^sub>R f x" and x = l])
  apply (rule intgbl)
  prefer 3 apply (rule lim)
  apply (rule AE_I2)
  using `mono A` apply (auto simp: mono_def nneg split: split_indicator) []
proof (rule AE_I2)
  { fix x assume "x \<in> space M"
    show "(\<lambda>i. indicator (A i) x *\<^sub>R f x) ----> indicator (\<Union>i. A i) x *\<^sub>R f x"
    proof cases
      assume "\<exists>i. x \<in> A i"
      then guess i ..
      then have *: "eventually (\<lambda>i. x \<in> A i) sequentially"
        using `x \<in> A i` `mono A` by (auto simp: eventually_sequentially mono_def)
      show ?thesis
        apply (intro Lim_eventually)
        using *
        apply eventually_elim
        apply (auto split: split_indicator)
        done
    qed auto }
  then show "(\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R f x) \<in> borel_measurable M"
    apply (rule borel_measurable_LIMSEQ)
    apply assumption
    apply (intro borel_measurable_integrable intgbl)
    done
qed

(* Proof from Royden Real Analysis, p. 91. *)
lemma lebesgue_integral_countable_add:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
    and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"
proof (subst integral_suminf[symmetric])
  show int_A: "\<And>i. set_integrable M (A i) f"
    using intgbl by (rule set_integrable_subset) auto
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. indicator (A i) x *\<^sub>R f x) sums (indicator (\<Union>i. A i) x *\<^sub>R f x)"
      by (intro sums_scaleR_left indicator_sums) fact }
  note sums = this

  have norm_f: "\<And>i. set_integrable M (A i) (\<lambda>x. norm (f x))"
    using int_A[THEN integrable_norm] by auto

  show "AE x in M. summable (\<lambda>i. norm (indicator (A i) x *\<^sub>R f x))"
    using disj by (intro AE_I2) (auto intro!: summable_mult2 sums_summable[OF indicator_sums])

  show "summable (\<lambda>i. LINT x|M. norm (indicator (A i) x *\<^sub>R f x))"
  proof (rule summableI_nonneg_bounded)
    fix n
    show "0 \<le> LINT x|M. norm (indicator (A n) x *\<^sub>R f x)"
      using norm_f by (auto intro!: integral_nonneg_AE)
    
    have "(\<Sum>i<n. LINT x|M. norm (indicator (A i) x *\<^sub>R f x)) =
      (\<Sum>i<n. set_lebesgue_integral M (A i) (\<lambda>x. norm (f x)))"
      by (simp add: abs_mult)
    also have "\<dots> = set_lebesgue_integral M (\<Union>i<n. A i) (\<lambda>x. norm (f x))"
      using norm_f
      by (subst set_integral_finite_Union) (auto simp: disjoint_family_on_def disj)
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. norm (f x))"
      using intgbl[THEN integrable_norm]
      by (intro integral_mono set_integrable_UN[of "{..<n}"] norm_f)
         (auto split: split_indicator)
    finally show "(\<Sum>i<n. LINT x|M. norm (indicator (A i) x *\<^sub>R f x)) \<le>
      set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. norm (f x))"
      by simp
  qed
  show "set_lebesgue_integral M (UNION UNIV A) f = LINT x|M. (\<Sum>i. indicator (A i) x *\<^sub>R f x)"
    apply (rule integral_cong[OF refl])
    apply (subst suminf_scaleR_left[OF sums_summable[OF indicator_sums, OF disj], symmetric])
    using sums_unique[OF indicator_sums[OF disj]]
    apply auto
    done
qed

lemma set_integral_cont_up:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(\<lambda>i. LINT x:(A i)|M. f x) ----> LINT x:(\<Union>i. A i)|M. f x"
proof (intro integral_dominated_convergence[where w="\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R norm (f x)"])
  have int_A: "\<And>i. set_integrable M (A i) f"
    using intgbl by (rule set_integrable_subset) auto
  then show "\<And>i. set_borel_measurable M (A i) f" "set_borel_measurable M (\<Union>i. A i) f"
    "set_integrable M (\<Union>i. A i) (\<lambda>x. norm (f x))"
    using intgbl integrable_norm[OF intgbl] by auto
  
  { fix x i assume "x \<in> A i"
    with A have "(\<lambda>xa. indicator (A xa) x::real) ----> 1 \<longleftrightarrow> (\<lambda>xa. 1::real) ----> 1"
      by (intro filterlim_cong refl)
         (fastforce simp: eventually_sequentially incseq_def subset_eq intro!: exI[of _ i]) }
  then show "AE x in M. (\<lambda>i. indicator (A i) x *\<^sub>R f x) ----> indicator (\<Union>i. A i) x *\<^sub>R f x"
    by (intro AE_I2 tendsto_intros) (auto split: split_indicator)
qed (auto split: split_indicator)
        
(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) ----> LINT x:(\<Inter>i. A i)|M. f x"
proof (rule integral_dominated_convergence)
  have int_A: "\<And>i. set_integrable M (A i) f"
    using int0 by (rule set_integrable_subset) (insert A, auto simp: decseq_def)
  show "set_integrable M (A 0) (\<lambda>x. norm (f x))"
    using int0[THEN integrable_norm] by simp
  have "set_integrable M (\<Inter>i. A i) f"
    using int0 by (rule set_integrable_subset) (insert A, auto simp: decseq_def)
  with int_A show "set_borel_measurable M (\<Inter>i. A i) f" "\<And>i. set_borel_measurable M (A i) f"
    by auto
  show "\<And>i. AE x in M. norm (indicator (A i) x *\<^sub>R f x) \<le> indicator (A 0) x *\<^sub>R norm (f x)"
    using A by (auto split: split_indicator simp: decseq_def)
  { fix x i assume "x \<in> space M" "x \<notin> A i"
    with A have "(\<lambda>i. indicator (A i) x::real) ----> 0 \<longleftrightarrow> (\<lambda>i. 0::real) ----> 0"
      by (intro filterlim_cong refl)
         (auto split: split_indicator simp: eventually_sequentially decseq_def intro!: exI[of _ i]) }
  then show "AE x in M. (\<lambda>i. indicator (A i) x *\<^sub>R f x) ----> indicator (\<Inter>i. A i) x *\<^sub>R f x"
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
  then show ?thesis using assms by simp
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

(*
lemma cmod_mult: "cmod ((a :: real) * (x :: complex)) = abs a * cmod x"
  apply (simp add: norm_mult)
  by (subst norm_mult, auto)
*)

lemma borel_integrable_atLeastAtMost':
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes f: "continuous_on {a..b} f"
  shows "set_integrable lborel {a..b} f" (is "integrable _ ?f")
  by (intro borel_integrable_compact compact_Icc f)

lemma integral_FTC_atLeastAtMost:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "a \<le> b"
    and F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    and f: "continuous_on {a .. b} f"
  shows "integral\<^sup>L lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x) = F b - F a"
proof -
  let ?f = "\<lambda>x. indicator {a .. b} x *\<^sub>R f x"
  have "(?f has_integral (\<integral>x. ?f x \<partial>lborel)) UNIV"
    using borel_integrable_atLeastAtMost'[OF f] by (rule has_integral_integral_lborel)
  moreover
  have "(f has_integral F b - F a) {a .. b}"
    by (intro fundamental_theorem_of_calculus ballI assms) auto
  then have "(?f has_integral F b - F a) {a .. b}"
    by (subst has_integral_eq_eq[where g=f]) auto
  then have "(?f has_integral F b - F a) UNIV"
    by (intro has_integral_on_superset[where t=UNIV and s="{a..b}"]) auto
  ultimately show "integral\<^sup>L lborel ?f = F b - F a"
    by (rule has_integral_unique)
qed

lemma set_borel_integral_eq_integral:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "set_integrable lborel S f"
  shows "f integrable_on S" "LINT x : S | lborel. f x = integral S f"
proof -
  let ?f = "\<lambda>x. indicator S x *\<^sub>R f x"
  have "(?f has_integral LINT x : S | lborel. f x) UNIV"
    by (rule has_integral_integral_lborel) fact
  hence 1: "(f has_integral (set_lebesgue_integral lborel S f)) S"
    apply (subst has_integral_restrict_univ [symmetric])
    apply (rule has_integral_eq)
    by auto
  thus "f integrable_on S"
    by (auto simp add: integrable_on_def)
  with 1 have "(f has_integral (integral S f)) S"
    by (intro integrable_integral, auto simp add: integrable_on_def)
  thus "LINT x : S | lborel. f x = integral S f"
    by (intro has_integral_unique [OF 1])
qed

lemma set_borel_measurable_continuous:
  fixes f :: "_ \<Rightarrow> _::real_normed_vector"
  assumes "S \<in> sets borel" "continuous_on S f"
  shows "set_borel_measurable borel S f"
proof -
  have "(\<lambda>x. if x \<in> S then f x else 0) \<in> borel_measurable borel"
    by (intro assms borel_measurable_continuous_on_if continuous_on_const)
  also have "(\<lambda>x. if x \<in> S then f x else 0) = (\<lambda>x. indicator S x *\<^sub>R f x)"
    by auto
  finally show ?thesis .
qed

lemma set_measurable_continuous_on_ivl:
  assumes "continuous_on {a..b} (f :: real \<Rightarrow> real)"
  shows "set_borel_measurable borel {a..b} f"
  by (rule set_borel_measurable_continuous[OF _ assms]) simp

end

