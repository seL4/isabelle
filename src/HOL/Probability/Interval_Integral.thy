(*  Title:      HOL/Probability/Interval_Integral.thy
    Author:     Jeremy Avigad, Johannes Hölzl, Luke Serafin

Lebesgue integral over an interval (with endpoints possibly +-\<infinity>)
*)

theory Interval_Integral
  imports Set_Integral
begin

lemma continuous_on_vector_derivative:
  "(\<And>x. x \<in> S \<Longrightarrow> (f has_vector_derivative f' x) (at x within S)) \<Longrightarrow> continuous_on S f"
  by (auto simp: continuous_on_eq_continuous_within intro!: has_vector_derivative_continuous)

lemma has_vector_derivative_weaken:
  fixes x D and f g s t
  assumes f: "(f has_vector_derivative D) (at x within t)"
    and "x \<in> s" "s \<subseteq> t" 
    and "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(g has_vector_derivative D) (at x within s)"
proof -
  have "(f has_vector_derivative D) (at x within s) \<longleftrightarrow> (g has_vector_derivative D) (at x within s)"
    unfolding has_vector_derivative_def has_derivative_iff_norm
    using assms by (intro conj_cong Lim_cong_within refl) auto
  then show ?thesis
    using has_vector_derivative_within_subset[OF f `s \<subseteq> t`] by simp
qed

definition "einterval a b = {x. a < ereal x \<and> ereal x < b}"

lemma einterval_eq[simp]:
  shows einterval_eq_Icc: "einterval (ereal a) (ereal b) = {a <..< b}"
    and einterval_eq_Ici: "einterval (ereal a) \<infinity> = {a <..}"
    and einterval_eq_Iic: "einterval (- \<infinity>) (ereal b) = {..< b}"
    and einterval_eq_UNIV: "einterval (- \<infinity>) \<infinity> = UNIV"
  by (auto simp: einterval_def)

lemma einterval_same: "einterval a a = {}"
  by (auto simp add: einterval_def)

lemma einterval_iff: "x \<in> einterval a b \<longleftrightarrow> a < ereal x \<and> ereal x < b"
  by (simp add: einterval_def)

lemma einterval_nonempty: "a < b \<Longrightarrow> \<exists>c. c \<in> einterval a b"
  by (cases a b rule: ereal2_cases, auto simp: einterval_def intro!: dense gt_ex lt_ex)

lemma open_einterval[simp]: "open (einterval a b)"
  by (cases a b rule: ereal2_cases)
     (auto simp: einterval_def intro!: open_Collect_conj open_Collect_less continuous_intros)

lemma borel_einterval[measurable]: "einterval a b \<in> sets borel"
  unfolding einterval_def by measurable

(* 
    Approximating a (possibly infinite) interval
*)

lemma filterlim_sup1: "(LIM x F. f x :> G1) \<Longrightarrow> (LIM x F. f x :> (sup G1 G2))"
 unfolding filterlim_def by (auto intro: le_supI1)

lemma ereal_incseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "incseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> b"
proof (cases b)
  case PInf
  with `a < b` have "a = -\<infinity> \<or> (\<exists>r. a = ereal r)"
    by (cases a) auto
  moreover have " (\<lambda>x. ereal (real (Suc x))) ----> \<infinity>"
    using nat_ceiling_le_eq by (subst LIMSEQ_Suc_iff) (auto simp: Lim_PInfty)
  moreover have "\<And>r. (\<lambda>x. ereal (r + real (Suc x))) ----> \<infinity>"
    apply (subst LIMSEQ_Suc_iff)
    apply (subst Lim_PInfty)
    apply (metis add.commute diff_le_eq nat_ceiling_le_eq ereal_less_eq(3))
    done
  ultimately show thesis
    by (intro that[of "\<lambda>i. real a + Suc i"])
       (auto simp: incseq_def PInf)
next
  case (real b')
  def d \<equiv> "b' - (if a = -\<infinity> then b' - 1 else real a)"
  with `a < b` have a': "0 < d"
    by (cases a) (auto simp: real)
  moreover
  have "\<And>i r. r < b' \<Longrightarrow> (b' - r) * 1 < (b' - r) * real (Suc (Suc i))"
    by (intro mult_strict_left_mono) auto
  with `a < b` a' have "\<And>i. a < ereal (b' - d / real (Suc (Suc i)))"
    by (cases a) (auto simp: real d_def field_simps)
  moreover have "(\<lambda>i. b' - d / Suc (Suc i)) ----> b'"
    apply (subst filterlim_sequentially_Suc)
    apply (subst filterlim_sequentially_Suc)
    apply (rule tendsto_eq_intros)
    apply (auto intro!: tendsto_divide_0[OF tendsto_const] filterlim_sup1
                simp: at_infinity_eq_at_top_bot filterlim_real_sequentially)
    done
  ultimately show thesis
    by (intro that[of "\<lambda>i. b' - d / Suc (Suc i)"])
       (auto simp add: real incseq_def intro!: divide_left_mono)
qed (insert `a < b`, auto)

lemma ereal_decseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "decseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> a"
proof -
  have "-b < -a" using `a < b` by simp
  from ereal_incseq_approx[OF this] guess X .
  then show thesis
    apply (intro that[of "\<lambda>i. - X i"])
    apply (auto simp add: uminus_ereal.simps[symmetric] decseq_def incseq_def
                simp del: uminus_ereal.simps)
    apply (metis ereal_minus_less_minus ereal_uminus_uminus ereal_Lim_uminus)+
    done
qed

lemma einterval_Icc_approximation:
  fixes a b :: ereal
  assumes "a < b"
  obtains u l :: "nat \<Rightarrow> real" where 
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
proof -
  from dense[OF `a < b`] obtain c where "a < c" "c < b" by safe
  from ereal_incseq_approx[OF `c < b`] guess u . note u = this
  from ereal_decseq_approx[OF `a < c`] guess l . note l = this
  { fix i from less_trans[OF `l i < c` `c < u i`] have "l i < u i" by simp }
  have "einterval a b = (\<Union>i. {l i .. u i})"
  proof (auto simp: einterval_iff)
    fix x assume "a < ereal x" "ereal x < b"
    have "eventually (\<lambda>i. ereal (l i) < ereal x) sequentially"
      using l(4) `a < ereal x` by (rule order_tendstoD)
    moreover 
    have "eventually (\<lambda>i. ereal x < ereal (u i)) sequentially"
      using u(4) `ereal x< b` by (rule order_tendstoD)
    ultimately have "eventually (\<lambda>i. l i < x \<and> x < u i) sequentially"
      by eventually_elim auto
    then show "\<exists>i. l i \<le> x \<and> x \<le> u i"
      by (auto intro: less_imp_le simp: eventually_sequentially)
  next
    fix x i assume "l i \<le> x" "x \<le> u i" 
    with `a < ereal (l i)` `ereal (u i) < b`
    show "a < ereal x" "ereal x < b"
      by (auto simp del: ereal_less_eq(3) simp add: ereal_less_eq(3)[symmetric])
  qed
  show thesis
    by (intro that) fact+
qed

(* TODO: in this definition, it would be more natural if einterval a b included a and b when 
   they are real. *)
definition interval_lebesgue_integral :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> 'a::{banach, second_countable_topology}" where
  "interval_lebesgue_integral M a b f =
    (if a \<le> b then (LINT x:einterval a b|M. f x) else - (LINT x:einterval b a|M. f x))"

syntax
  "_ascii_interval_lebesgue_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _=_.._|_. _)" [0,60,60,61,100] 60)

translations
  "LINT x=a..b|M. f" == "CONST interval_lebesgue_integral M a b (\<lambda>x. f)"

definition interval_lebesgue_integrable :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> 'a::{banach, second_countable_topology}) \<Rightarrow> bool" where
  "interval_lebesgue_integrable M a b f =
    (if a \<le> b then set_integrable M (einterval a b) f else set_integrable M (einterval b a) f)"

syntax
  "_ascii_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

(*
    Basic properties of integration over an interval.
*)

lemma interval_lebesgue_integral_cong:
  "a \<le> b \<Longrightarrow> (\<And>x. x \<in> einterval a b \<Longrightarrow> f x = g x) \<Longrightarrow> einterval a b \<in> sets M \<Longrightarrow>
    interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b g"
  by (auto intro: set_lebesgue_integral_cong simp: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_cong_AE:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    a \<le> b \<Longrightarrow> AE x \<in> einterval a b in M. f x = g x \<Longrightarrow> einterval a b \<in> sets M \<Longrightarrow>
    interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b g"
  by (auto intro: set_lebesgue_integral_cong_AE simp: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_add [intro, simp]: 
  fixes M a b f 
  assumes "interval_lebesgue_integrable M a b f" "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. f x + g x)" and 
    "interval_lebesgue_integral M a b (\<lambda>x. f x + g x) = 
   interval_lebesgue_integral M a b f + interval_lebesgue_integral M a b g"
using assms by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def 
    field_simps)

lemma interval_lebesgue_integral_diff [intro, simp]: 
  fixes M a b f 
  assumes "interval_lebesgue_integrable M a b f"
    "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. f x - g x)" and 
    "interval_lebesgue_integral M a b (\<lambda>x. f x - g x) = 
   interval_lebesgue_integral M a b f - interval_lebesgue_integral M a b g"
using assms by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def 
    field_simps)

lemma interval_lebesgue_integrable_mult_right [intro, simp]:
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> interval_lebesgue_integrable M a b f) \<Longrightarrow>
    interval_lebesgue_integrable M a b (\<lambda>x. c * f x)"
  by (simp add: interval_lebesgue_integrable_def)

lemma interval_lebesgue_integrable_mult_left [intro, simp]:
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> interval_lebesgue_integrable M a b f) \<Longrightarrow>
    interval_lebesgue_integrable M a b (\<lambda>x. f x * c)"
  by (simp add: interval_lebesgue_integrable_def)

lemma interval_lebesgue_integrable_divide [intro, simp]:
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, field_inverse_zero, second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> interval_lebesgue_integrable M a b f) \<Longrightarrow>
    interval_lebesgue_integrable M a b (\<lambda>x. f x / c)"
  by (simp add: interval_lebesgue_integrable_def)

lemma interval_lebesgue_integral_mult_right [simp]:
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, second_countable_topology}"
  shows "interval_lebesgue_integral M a b (\<lambda>x. c * f x) =
    c * interval_lebesgue_integral M a b f"
  by (simp add: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_mult_left [simp]:
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, second_countable_topology}"
  shows "interval_lebesgue_integral M a b (\<lambda>x. f x * c) =
    interval_lebesgue_integral M a b f * c"
  by (simp add: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_divide [simp]:
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, field_inverse_zero, second_countable_topology}"
  shows "interval_lebesgue_integral M a b (\<lambda>x. f x / c) =
    interval_lebesgue_integral M a b f / c"
  by (simp add: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_uminus:
  "interval_lebesgue_integral M a b (\<lambda>x. - f x) = - interval_lebesgue_integral M a b f"
  by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def)

lemma interval_lebesgue_integral_of_real:
  "interval_lebesgue_integral M a b (\<lambda>x. complex_of_real (f x)) =
    of_real (interval_lebesgue_integral M a b f)"
  unfolding interval_lebesgue_integral_def
  by (auto simp add: interval_lebesgue_integral_def set_integral_complex_of_real)

lemma interval_lebesgue_integral_le_eq: 
  fixes a b f
  assumes "a \<le> b"
  shows "interval_lebesgue_integral M a b f = (LINT x : einterval a b | M. f x)"
using assms by (auto simp add: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_gt_eq: 
  fixes a b f
  assumes "a > b"
  shows "interval_lebesgue_integral M a b f = -(LINT x : einterval b a | M. f x)"
using assms by (auto simp add: interval_lebesgue_integral_def less_imp_le einterval_def)

lemma interval_lebesgue_integral_gt_eq':
  fixes a b f
  assumes "a > b"
  shows "interval_lebesgue_integral M a b f = - interval_lebesgue_integral M b a f"
using assms by (auto simp add: interval_lebesgue_integral_def less_imp_le einterval_def)

lemma interval_integral_endpoints_same [simp]: "(LBINT x=a..a. f x) = 0"
  by (simp add: interval_lebesgue_integral_def einterval_same)

lemma interval_integral_endpoints_reverse: "(LBINT x=a..b. f x) = -(LBINT x=b..a. f x)"
  by (cases a b rule: linorder_cases) (auto simp: interval_lebesgue_integral_def einterval_same)

lemma interval_integrable_endpoints_reverse:
  "interval_lebesgue_integrable lborel a b f \<longleftrightarrow>
    interval_lebesgue_integrable lborel b a f"
  by (cases a b rule: linorder_cases) (auto simp: interval_lebesgue_integrable_def einterval_same)

lemma interval_integral_reflect:
  "(LBINT x=a..b. f x) = (LBINT x=-b..-a. f (-x))"
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (auto simp add: interval_lebesgue_integral_def interval_integrable_endpoints_reverse
             split: split_if_asm)
next
  case (le a b) then show ?case
    unfolding interval_lebesgue_integral_def
    by (subst set_integral_reflect)
       (auto simp: interval_lebesgue_integrable_def einterval_iff
                   ereal_uminus_le_reorder ereal_uminus_less_reorder not_less
                   uminus_ereal.simps[symmetric]
             simp del: uminus_ereal.simps
             intro!: integral_cong
             split: split_indicator)
qed

(*
    Basic properties of integration over an interval wrt lebesgue measure.
*)

lemma interval_integral_zero [simp]:
  fixes a b :: ereal
  shows"LBINT x=a..b. 0 = 0" 
using assms unfolding interval_lebesgue_integral_def einterval_eq 
by simp

lemma interval_integral_const [intro, simp]:
  fixes a b c :: real
  shows "interval_lebesgue_integrable lborel a b (\<lambda>x. c)" and "LBINT x=a..b. c = c * (b - a)" 
using assms unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def einterval_eq 
by (auto simp add:  less_imp_le field_simps measure_def)

lemma interval_integral_cong_AE:
  assumes [measurable]: "f \<in> borel_measurable borel" "g \<in> borel_measurable borel"
  assumes "AE x \<in> einterval (min a b) (max a b) in lborel. f x = g x"
  shows "interval_lebesgue_integral lborel a b f = interval_lebesgue_integral lborel a b g"
  using assms
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (simp add: min.commute max.commute interval_integral_endpoints_reverse[of a b])
next
  case (le a b) then show ?case
    by (auto simp: interval_lebesgue_integral_def max_def min_def
             intro!: set_lebesgue_integral_cong_AE)
qed

lemma interval_integral_cong:
  assumes "\<And>x. x \<in> einterval (min a b) (max a b) \<Longrightarrow> f x = g x" 
  shows "interval_lebesgue_integral lborel a b f = interval_lebesgue_integral lborel a b g"
  using assms
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (simp add: min.commute max.commute interval_integral_endpoints_reverse[of a b])
next
  case (le a b) then show ?case
    by (auto simp: interval_lebesgue_integral_def max_def min_def
             intro!: set_lebesgue_integral_cong)
qed

lemma interval_lebesgue_integrable_cong_AE:
    "f \<in> borel_measurable lborel \<Longrightarrow> g \<in> borel_measurable lborel \<Longrightarrow>
    AE x \<in> einterval (min a b) (max a b) in lborel. f x = g x \<Longrightarrow>
    interval_lebesgue_integrable lborel a b f = interval_lebesgue_integrable lborel a b g"
  apply (simp add: interval_lebesgue_integrable_def )
  apply (intro conjI impI set_integrable_cong_AE)
  apply (auto simp: min_def max_def)
  done

lemma interval_integrable_abs_iff:
  fixes f :: "real \<Rightarrow> real"
  shows  "f \<in> borel_measurable lborel \<Longrightarrow>
    interval_lebesgue_integrable lborel a b (\<lambda>x. \<bar>f x\<bar>) = interval_lebesgue_integrable lborel a b f"
  unfolding interval_lebesgue_integrable_def
  by (subst (1 2) set_integrable_abs_iff') simp_all

lemma interval_integral_Icc:
  fixes a b :: real
  shows "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {a..b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{a, b}"]
           simp add: interval_lebesgue_integral_def)

lemma interval_integral_Icc':
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {x. a \<le> ereal x \<and> ereal x \<le> b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{real a, real b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ioc:
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {a<..b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{a, b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

(* TODO: other versions as well? *) (* Yes: I need the Icc' version. *)
lemma interval_integral_Ioc':
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {x. a < ereal x \<and> ereal x \<le> b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{real a, real b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ico:
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {a..<b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{a, b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ioi:
  "\<bar>a\<bar> < \<infinity> \<Longrightarrow> (LBINT x=a..\<infinity>. f x) = (LBINT x : {real a <..}. f x)"
  by (auto simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ioo:
  "a \<le> b \<Longrightarrow> \<bar>a\<bar> < \<infinity> ==> \<bar>b\<bar> < \<infinity> \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {real a <..< real b}. f x)"
  by (auto simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_discrete_difference:
  fixes f :: "real \<Rightarrow> 'b::{banach, second_countable_topology}" and a b :: ereal
  assumes "countable X"
  and eq: "\<And>x. a \<le> b \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow> x \<notin> X \<Longrightarrow> f x = g x"
  and anti_eq: "\<And>x. b \<le> a \<Longrightarrow> b < x \<Longrightarrow> x < a \<Longrightarrow> x \<notin> X \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b g"
  unfolding interval_lebesgue_integral_def
  apply (intro if_cong refl arg_cong[where f="\<lambda>x. - x"] integral_discrete_difference[of X] assms)
  apply (auto simp: eq anti_eq einterval_iff split: split_indicator)
  done

lemma interval_integral_sum: 
  fixes a b c :: ereal
  assumes integrable: "interval_lebesgue_integrable lborel (min a (min b c)) (max a (max b c)) f" 
  shows "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) = (LBINT x=a..c. f x)"
proof -
  let ?I = "\<lambda>a b. LBINT x=a..b. f x"
  { fix a b c :: ereal assume "interval_lebesgue_integrable lborel a c f" "a \<le> b" "b \<le> c"
    then have ord: "a \<le> b" "b \<le> c" "a \<le> c" and f': "set_integrable lborel (einterval a c) f"
      by (auto simp: interval_lebesgue_integrable_def)
    then have f: "set_borel_measurable borel (einterval a c) f"
      by (drule_tac borel_measurable_integrable) simp
    have "(LBINT x:einterval a c. f x) = (LBINT x:einterval a b \<union> einterval b c. f x)"
    proof (rule set_integral_cong_set)
      show "AE x in lborel. (x \<in> einterval a b \<union> einterval b c) = (x \<in> einterval a c)"
        using AE_lborel_singleton[of "real b"] ord
        by (cases a b c rule: ereal3_cases) (auto simp: einterval_iff)
    qed (insert ord, auto intro!: set_borel_measurable_subset[OF f] simp: einterval_iff)
    also have "\<dots> = (LBINT x:einterval a b. f x) + (LBINT x:einterval b c. f x)"
      using ord
      by (intro set_integral_Un_AE) (auto intro!: set_integrable_subset[OF f'] simp: einterval_iff not_less)
    finally have "?I a b + ?I b c = ?I a c"
      using ord by (simp add: interval_lebesgue_integral_def)
  } note 1 = this
  { fix a b c :: ereal assume "interval_lebesgue_integrable lborel a c f" "a \<le> b" "b \<le> c"
    from 1[OF this] have "?I b c + ?I a b = ?I a c"
      by (metis add.commute)
  } note 2 = this
  have 3: "\<And>a b. b \<le> a \<Longrightarrow> (LBINT x=a..b. f x) = - (LBINT x=b..a. f x)"
    by (rule interval_integral_endpoints_reverse)
  show ?thesis
    using integrable
    by (cases a b b c a c rule: linorder_le_cases[case_product linorder_le_cases linorder_cases])
       (simp_all add: min_absorb1 min_absorb2 max_absorb1 max_absorb2 field_simps 1 2 3)
qed

lemma interval_integrable_isCont:
  fixes a b and f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  shows "(\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow> isCont f x) \<Longrightarrow>
    interval_lebesgue_integrable lborel a b f"
proof (induct a b rule: linorder_wlog)
  case (le a b) then show ?case
    by (auto simp: interval_lebesgue_integrable_def
             intro!: set_integrable_subset[OF borel_integrable_compact[of "{a .. b}"]]
                     continuous_at_imp_continuous_on)
qed (auto intro: interval_integrable_endpoints_reverse[THEN iffD1])

lemma interval_integrable_continuous_on:
  fixes a b :: real and f
  assumes "a \<le> b" and "continuous_on {a..b} f"
  shows "interval_lebesgue_integrable lborel a b f"
using assms unfolding interval_lebesgue_integrable_def apply simp
  by (rule set_integrable_subset, rule borel_integrable_atLeastAtMost' [of a b], auto)

lemma interval_integral_eq_integral: 
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> set_integrable lborel {a..b} f \<Longrightarrow> LBINT x=a..b. f x = integral {a..b} f"
  by (subst interval_integral_Icc, simp) (rule set_borel_integral_eq_integral)

lemma interval_integral_eq_integral': 
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> set_integrable lborel (einterval a b) f \<Longrightarrow> LBINT x=a..b. f x = integral (einterval a b) f"
  by (subst interval_lebesgue_integral_le_eq, simp) (rule set_borel_integral_eq_integral)
  
(*
    General limit approximation arguments
*)

lemma interval_integral_Icc_approx_nonneg:
  fixes a b :: ereal
  assumes "a < b"
  fixes u l :: "nat \<Rightarrow> real"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
  fixes f :: "real \<Rightarrow> real"
  assumes f_integrable: "\<And>i. set_integrable lborel {l i..u i} f"
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes f_measurable: "set_borel_measurable lborel (einterval a b) f"
  assumes lbint_lim: "(\<lambda>i. LBINT x=l i.. u i. f x) ----> C"
  shows 
    "set_integrable lborel (einterval a b) f"
    "(LBINT x=a..b. f x) = C"
proof -
  have 1: "\<And>i. set_integrable lborel {l i..u i} f" by (rule f_integrable)
  have 2: "AE x in lborel. mono (\<lambda>n. indicator {l n..u n} x *\<^sub>R f x)"
  proof -
     from f_nonneg have "AE x in lborel. \<forall>i. l i \<le> x \<longrightarrow> x \<le> u i \<longrightarrow> 0 \<le> f x"
      by eventually_elim
         (metis approx(5) approx(6) dual_order.strict_trans1 ereal_less_eq(3) le_less_trans)
    then show ?thesis
      apply eventually_elim
      apply (auto simp: mono_def split: split_indicator)
      apply (metis approx(3) decseqD order_trans)
      apply (metis approx(2) incseqD order_trans)
      done
  qed
  have 3: "AE x in lborel. (\<lambda>i. indicator {l i..u i} x *\<^sub>R f x) ----> indicator (einterval a b) x *\<^sub>R f x"
  proof -
    { fix x i assume "l i \<le> x" "x \<le> u i"
      then have "eventually (\<lambda>i. l i \<le> x \<and> x \<le> u i) sequentially"
        apply (auto simp: eventually_sequentially intro!: exI[of _ i])
        apply (metis approx(3) decseqD order_trans)
        apply (metis approx(2) incseqD order_trans)
        done
      then have "eventually (\<lambda>i. f x * indicator {l i..u i} x = f x) sequentially"
        by eventually_elim auto }
    then show ?thesis
      unfolding approx(1) by (auto intro!: AE_I2 Lim_eventually split: split_indicator)
  qed
  have 4: "(\<lambda>i. \<integral> x. indicator {l i..u i} x *\<^sub>R f x \<partial>lborel) ----> C"
    using lbint_lim by (simp add: interval_integral_Icc approx less_imp_le)
  have 5: "set_borel_measurable lborel (einterval a b) f" by (rule assms)
  have "(LBINT x=a..b. f x) = lebesgue_integral lborel (\<lambda>x. indicator (einterval a b) x *\<^sub>R f x)"
    using assms by (simp add: interval_lebesgue_integral_def less_imp_le)
  also have "... = C" by (rule integral_monotone_convergence [OF 1 2 3 4 5])
  finally show "(LBINT x=a..b. f x) = C" .

  show "set_integrable lborel (einterval a b) f" 
    by (rule integrable_monotone_convergence[OF 1 2 3 4 5])
qed

lemma interval_integral_Icc_approx_integrable:
  fixes u l :: "nat \<Rightarrow> real" and a b :: ereal
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes "a < b"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  shows "(\<lambda>i. LBINT x=l i.. u i. f x) ----> (LBINT x=a..b. f x)"
proof -
  have "(\<lambda>i. LBINT x:{l i.. u i}. f x) ----> (LBINT x:einterval a b. f x)"
  proof (rule integral_dominated_convergence)
    show "integrable lborel (\<lambda>x. norm (indicator (einterval a b) x *\<^sub>R f x))"
      by (rule integrable_norm) fact
    show "set_borel_measurable lborel (einterval a b) f"
      using f_integrable by (rule borel_measurable_integrable)
    then show "\<And>i. set_borel_measurable lborel {l i..u i} f"
      by (rule set_borel_measurable_subset) (auto simp: approx)
    show "\<And>i. AE x in lborel. norm (indicator {l i..u i} x *\<^sub>R f x) \<le> norm (indicator (einterval a b) x *\<^sub>R f x)"
      by (intro AE_I2) (auto simp: approx split: split_indicator)
    show "AE x in lborel. (\<lambda>i. indicator {l i..u i} x *\<^sub>R f x) ----> indicator (einterval a b) x *\<^sub>R f x"
    proof (intro AE_I2 tendsto_intros Lim_eventually)
      fix x
      { fix i assume "l i \<le> x" "x \<le> u i" 
        with `incseq u`[THEN incseqD, of i] `decseq l`[THEN decseqD, of i]
        have "eventually (\<lambda>i. l i \<le> x \<and> x \<le> u i) sequentially"
          by (auto simp: eventually_sequentially decseq_def incseq_def intro: order_trans) }
      then show "eventually (\<lambda>xa. indicator {l xa..u xa} x = (indicator (einterval a b) x::real)) sequentially"
        using approx order_tendstoD(2)[OF `l ----> a`, of x] order_tendstoD(1)[OF `u ----> b`, of x]
        by (auto split: split_indicator)
    qed
  qed
  with `a < b` `\<And>i. l i < u i` show ?thesis
    by (simp add: interval_lebesgue_integral_le_eq[symmetric] interval_integral_Icc less_imp_le)
qed

(*
  A slightly stronger version of integral_FTC_atLeastAtMost and related facts, 
  with continuous_on instead of isCont

  TODO: make the older versions corollaries of these (using continuous_at_imp_continuous_on, etc.)
*)

(*
TODO: many proofs below require inferences like

  a < ereal x \<Longrightarrow> x < y \<Longrightarrow> a < ereal y

where x and y are real. These should be better automated.
*)

(*
    The first Fundamental Theorem of Calculus

    First, for finite intervals, and then two versions for arbitrary intervals.
*)

lemma interval_integral_FTC_finite:
  fixes f F :: "real \<Rightarrow> 'a::euclidean_space" and a b :: real
  assumes f: "continuous_on {min a b..max a b} f"
  assumes F: "\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow> (F has_vector_derivative (f x)) (at x within 
    {min a b..max a b})" 
  shows "(LBINT x=a..b. f x) = F b - F a"
  apply (case_tac "a \<le> b")
  apply (subst interval_integral_Icc, simp)
  apply (rule integral_FTC_atLeastAtMost, assumption)
  apply (metis F max_def min_def)
  using f apply (simp add: min_absorb1 max_absorb2)
  apply (subst interval_integral_endpoints_reverse)
  apply (subst interval_integral_Icc, simp)
  apply (subst integral_FTC_atLeastAtMost, auto)
  apply (metis F max_def min_def)
using f by (simp add: min_absorb2 max_absorb1)

lemma interval_integral_FTC_nonneg:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F x :> f x" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes A: "((F \<circ> real) ---> A) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows
    "set_integrable lborel (einterval a b) f" 
    "(LBINT x=a..b. f x) = B - A"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx apply (intro interval_integral_FTC_finite)
    apply (auto simp add: less_imp_le min_def max_def
      has_field_derivative_iff_has_vector_derivative[symmetric])
    apply (rule continuous_at_imp_continuous_on, auto intro!: f)
    by (rule DERIV_subset [OF F], auto)
  have 1: "\<And>i. set_integrable lborel {l i..u i} f"
  proof -
    fix i show "set_integrable lborel {l i .. u i} f"
      using `a < l i` `u i < b`
      by (intro borel_integrable_compact f continuous_at_imp_continuous_on compact_Icc ballI)
         (auto simp del: ereal_less_eq simp add: ereal_less_eq(3)[symmetric])
  qed
  have 2: "set_borel_measurable lborel (einterval a b) f"
    by (auto simp del: real_scaleR_def intro!: set_borel_measurable_continuous 
             simp: continuous_on_eq_continuous_at einterval_iff f)
  have 3: "(\<lambda>i. LBINT x=l i..u i. f x) ----> B - A"
    apply (subst FTCi)
    apply (intro tendsto_intros)
    using B approx unfolding tendsto_at_iff_sequentially comp_def
    using tendsto_at_iff_sequentially[where 'a=real]
    apply (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
    using A approx unfolding tendsto_at_iff_sequentially comp_def
    by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
  show "(LBINT x=a..b. f x) = B - A"
    by (rule interval_integral_Icc_approx_nonneg [OF `a < b` approx 1 f_nonneg 2 3])
  show "set_integrable lborel (einterval a b) f" 
    by (rule interval_integral_Icc_approx_nonneg [OF `a < b` approx 1 f_nonneg 2 3])
qed

lemma interval_integral_FTC_integrable:
  fixes f F :: "real \<Rightarrow> 'a::euclidean_space" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> (F has_vector_derivative f x) (at x)" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  assumes A: "((F \<circ> real) ---> A) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows "(LBINT x=a..b. f x) = B - A"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx
    by (auto simp add: less_imp_le min_def max_def
             intro!: f continuous_at_imp_continuous_on interval_integral_FTC_finite
             intro: has_vector_derivative_at_within)
  have "(\<lambda>i. LBINT x=l i..u i. f x) ----> B - A"
    apply (subst FTCi)
    apply (intro tendsto_intros)
    using B approx unfolding tendsto_at_iff_sequentially comp_def
    apply (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
    using A approx unfolding tendsto_at_iff_sequentially comp_def
    by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
  moreover have "(\<lambda>i. LBINT x=l i..u i. f x) ----> (LBINT x=a..b. f x)"
    by (rule interval_integral_Icc_approx_integrable [OF `a < b` approx f_integrable])
  ultimately show ?thesis
    by (elim LIMSEQ_unique)
qed

(* 
  The second Fundamental Theorem of Calculus and existence of antiderivatives on an
  einterval.
*)

lemma interval_integral_FTC2:
  fixes a b c :: real and f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> c" "c \<le> b"
  and contf: "continuous_on {a..b} f"
  fixes x :: real
  assumes "a \<le> x" and "x \<le> b"
  shows "((\<lambda>u. LBINT y=c..u. f y) has_vector_derivative (f x)) (at x within {a..b})"
proof -
  let ?F = "(\<lambda>u. LBINT y=a..u. f y)"
  have intf: "set_integrable lborel {a..b} f"
    by (rule borel_integrable_atLeastAtMost', rule contf)
  have "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})"
    apply (intro integral_has_vector_derivative)
    using `a \<le> x` `x \<le> b` by (intro continuous_on_subset [OF contf], auto)
  then have "((\<lambda>u. integral {a..u} f) has_vector_derivative (f x)) (at x within {a..b})"
    by simp
  then have "(?F has_vector_derivative (f x)) (at x within {a..b})"
    by (rule has_vector_derivative_weaken)
       (auto intro!: assms interval_integral_eq_integral[symmetric] set_integrable_subset [OF intf])
  then have "((\<lambda>x. (LBINT y=c..a. f y) + ?F x) has_vector_derivative (f x)) (at x within {a..b})"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis
  proof (rule has_vector_derivative_weaken)
    fix u assume "u \<in> {a .. b}"
    then show "(LBINT y=c..a. f y) + (LBINT y=a..u. f y) = (LBINT y=c..u. f y)"
      using assms
      apply (intro interval_integral_sum)
      apply (auto simp add: interval_lebesgue_integrable_def simp del: real_scaleR_def)
      by (rule set_integrable_subset [OF intf], auto simp add: min_def max_def)
  qed (insert assms, auto)
qed

lemma einterval_antiderivative: 
  fixes a b :: ereal and f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a < b" and contf: "\<And>x :: real. a < x \<Longrightarrow> x < b \<Longrightarrow> isCont f x"
  shows "\<exists>F. \<forall>x :: real. a < x \<longrightarrow> x < b \<longrightarrow> (F has_vector_derivative f x) (at x)"
proof -
  from einterval_nonempty [OF `a < b`] obtain c :: real where [simp]: "a < c" "c < b" 
    by (auto simp add: einterval_def)
  let ?F = "(\<lambda>u. LBINT y=c..u. f y)"
  show ?thesis
  proof (rule exI, clarsimp)
    fix x :: real
    assume [simp]: "a < x" "x < b"
    have 1: "a < min c x" by simp
    from einterval_nonempty [OF 1] obtain d :: real where [simp]: "a < d" "d < c" "d < x" 
      by (auto simp add: einterval_def)
    have 2: "max c x < b" by simp
    from einterval_nonempty [OF 2] obtain e :: real where [simp]: "c < e" "x < e" "e < b" 
      by (auto simp add: einterval_def)
    show "(?F has_vector_derivative f x) (at x)"
      (* TODO: factor out the next three lines to has_field_derivative_within_open *)
      unfolding has_vector_derivative_def
      apply (subst has_derivative_within_open [of _ "{d<..<e}", symmetric], auto)
      apply (subst has_vector_derivative_def [symmetric])
      apply (rule has_vector_derivative_within_subset [of _ _ _ "{d..e}"])
      apply (rule interval_integral_FTC2, auto simp add: less_imp_le)
      apply (rule continuous_at_imp_continuous_on)
      apply (auto intro!: contf)
      apply (rule order_less_le_trans, rule `a < d`, auto)
      apply (rule order_le_less_trans) prefer 2
      by (rule `e < b`, auto)
  qed
qed

(*
    The substitution theorem

    Once again, three versions: first, for finite intervals, and then two versions for
    arbitrary intervals.
*)
  
lemma interval_integral_substitution_finite:
  fixes a b :: real and f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b"
  and derivg: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (g has_real_derivative (g' x)) (at x within {a..b})"
  and contf : "continuous_on (g ` {a..b}) f"
  and contg': "continuous_on {a..b} g'"
  shows "LBINT x=a..b. g' x *\<^sub>R f (g x) = LBINT y=g a..g b. f y"
proof-
  have v_derivg: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (g has_vector_derivative (g' x)) (at x within {a..b})"
    using derivg unfolding has_field_derivative_iff_has_vector_derivative .
  then have contg [simp]: "continuous_on {a..b} g"
    by (rule continuous_on_vector_derivative) auto
  have 1: "\<And>u. min (g a) (g b) \<le> u \<Longrightarrow> u \<le> max (g a) (g b) \<Longrightarrow> 
      \<exists>x\<in>{a..b}. u = g x"
    apply (case_tac "g a \<le> g b")
    apply (auto simp add: min_def max_def less_imp_le)
    apply (frule (1) IVT' [of g], auto simp add: assms)
    by (frule (1) IVT2' [of g], auto simp add: assms)
  from contg `a \<le> b` have "\<exists>c d. g ` {a..b} = {c..d} \<and> c \<le> d"
    by (elim continuous_image_closed_interval)
  then obtain c d where g_im: "g ` {a..b} = {c..d}" and "c \<le> d" by auto
  have "\<exists>F. \<forall>x\<in>{a..b}. (F has_vector_derivative (f (g x))) (at (g x) within (g ` {a..b}))"
    apply (rule exI, auto, subst g_im)
    apply (rule interval_integral_FTC2 [of c c d])
    using `c \<le> d` apply auto
    apply (rule continuous_on_subset [OF contf])
    using g_im by auto
  then guess F ..
  then have derivF: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> 
    (F has_vector_derivative (f (g x))) (at (g x) within (g ` {a..b}))" by auto
  have contf2: "continuous_on {min (g a) (g b)..max (g a) (g b)} f"
    apply (rule continuous_on_subset [OF contf])
    apply (auto simp add: image_def)
    by (erule 1)
  have contfg: "continuous_on {a..b} (\<lambda>x. f (g x))"
    by (blast intro: continuous_on_compose2 contf contg)
  have "LBINT x=a..b. g' x *\<^sub>R f (g x) = F (g b) - F (g a)"
    apply (subst interval_integral_Icc, simp add: assms)
    apply (rule integral_FTC_atLeastAtMost[of a b "\<lambda>x. F (g x)", OF `a \<le> b`])
    apply (rule vector_diff_chain_within[OF v_derivg derivF, unfolded comp_def])
    apply (auto intro!: continuous_on_scaleR contg' contfg)
    done
  moreover have "LBINT y=(g a)..(g b). f y = F (g b) - F (g a)"
    apply (rule interval_integral_FTC_finite)
    apply (rule contf2)
    apply (frule (1) 1, auto)
    apply (rule has_vector_derivative_within_subset [OF derivF])
    apply (auto simp add: image_def)
    by (rule 1, auto)
  ultimately show ?thesis by simp
qed

(* TODO: is it possible to lift the assumption here that g' is nonnegative? *)

lemma interval_integral_substitution_integrable:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and a b u v :: ereal
  assumes "a < b" 
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real) ---> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real) ---> B) (at_left b)"
  and integrable: "set_integrable lborel (einterval a b) (\<lambda>x. g' x *\<^sub>R f (g x))"
  and integrable2: "set_integrable lborel (einterval A B) (\<lambda>x. f x)"
  shows "(LBINT x=A..B. f x) = (LBINT x=a..b. g' x *\<^sub>R f (g x))"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx [simp] = this
  note less_imp_le [simp]
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have [simp]: "\<And>i. l i < b" 
    apply (rule order_less_trans) prefer 2 
    by (rule approx, auto, rule approx)
  have [simp]: "\<And>i. a < u i" 
    by (rule order_less_trans, rule approx, auto, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> l j \<le> l i" by (rule decseqD, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> u i \<le> u j" by (rule incseqD, rule approx)
  have g_nondec [simp]: "\<And>x y. a < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < b \<Longrightarrow> g x \<le> g y"
    apply (erule DERIV_nonneg_imp_nondecreasing, auto)
    apply (rule exI, rule conjI, rule deriv_g)
    apply (erule order_less_le_trans, auto)
    apply (rule order_le_less_trans, subst ereal_less_eq(3), assumption, auto)
    apply (rule g'_nonneg)
    apply (rule less_imp_le, erule order_less_le_trans, auto)
    by (rule less_imp_le, rule le_less_trans, subst ereal_less_eq(3), assumption, auto)
  have "A \<le> B" and un: "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
  proof - 
    have A2: "(\<lambda>i. g (l i)) ----> A"
      using A apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<ge> A"
      by (intro decseq_le, auto simp add: decseq_def)
    have B2: "(\<lambda>i. g (u i)) ----> B"
      using B apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<le> B"
      by (intro incseq_le, auto simp add: incseq_def)
    show "A \<le> B"
      apply (rule order_trans [OF A3 [of 0]])
      apply (rule order_trans [OF _ B3 [of 0]])
      by auto
    { fix x :: real
      assume "A < x" and "x < B"   
      then have "eventually (\<lambda>i. ereal (g (l i)) < x \<and> x < ereal (g (u i))) sequentially"
        apply (intro eventually_conj order_tendstoD)
        by (rule A2, assumption, rule B2, assumption)
      hence "\<exists>i. g (l i) < x \<and> x < g (u i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
      apply (auto simp add: einterval_def)
      apply (erule (1) AB)
      apply (rule order_le_less_trans, rule A3, simp)
      apply (rule order_less_le_trans) prefer 2
      by (rule B3, simp) 
  qed
  (* finally, the main argument *)
  {
     fix i
     have "(LBINT x=l i.. u i. g' x *\<^sub>R f (g x)) = (LBINT y=g (l i)..g (u i). f y)"
        apply (rule interval_integral_substitution_finite, auto)
        apply (rule DERIV_subset)
        unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
        apply (rule deriv_g)
        apply (auto intro!: continuous_at_imp_continuous_on contf contg')
        done
  } note eq1 = this
  have "(\<lambda>i. LBINT x=l i..u i. g' x *\<^sub>R f (g x)) ----> (LBINT x=a..b. g' x *\<^sub>R f (g x))"
    apply (rule interval_integral_Icc_approx_integrable [OF `a < b` approx])
    by (rule assms)
  hence 2: "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x=a..b. g' x *\<^sub>R f (g x))"
    by (simp add: eq1)
  have incseq: "incseq (\<lambda>i. {g (l i)<..<g (u i)})"
    apply (auto simp add: incseq_def)
    apply (rule order_le_less_trans)
    prefer 2 apply (assumption, auto)
    by (erule order_less_le_trans, rule g_nondec, auto)
  have "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x = A..B. f x)"
    apply (subst interval_lebesgue_integral_le_eq, auto simp del: real_scaleR_def)
    apply (subst interval_lebesgue_integral_le_eq, rule `A \<le> B`)
    apply (subst un, rule set_integral_cont_up, auto simp del: real_scaleR_def)
    apply (rule incseq)
    apply (subst un [symmetric])
    by (rule integrable2)
  thus ?thesis by (intro LIMSEQ_unique [OF _ 2])
qed

(* TODO: the last two proofs are only slightly different. Factor out common part?
   An alternative: make the second one the main one, and then have another lemma
   that says that if f is nonnegative and all the other hypotheses hold, then it is integrable. *)

lemma interval_integral_substitution_nonneg:
  fixes f g g':: "real \<Rightarrow> real" and a b u v :: ereal
  assumes "a < b" 
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and f_nonneg: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> 0 \<le> f (g x)" (* TODO: make this AE? *)
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real) ---> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real) ---> B) (at_left b)"
  and integrable_fg: "set_integrable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)"
  shows 
    "set_integrable lborel (einterval A B) f"
    "(LBINT x=A..B. f x) = (LBINT x=a..b. (f (g x) * g' x))"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx [simp] = this
  note less_imp_le [simp]
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have [simp]: "\<And>i. l i < b" 
    apply (rule order_less_trans) prefer 2 
    by (rule approx, auto, rule approx)
  have [simp]: "\<And>i. a < u i" 
    by (rule order_less_trans, rule approx, auto, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> l j \<le> l i" by (rule decseqD, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> u i \<le> u j" by (rule incseqD, rule approx)
  have g_nondec [simp]: "\<And>x y. a < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < b \<Longrightarrow> g x \<le> g y"
    apply (erule DERIV_nonneg_imp_nondecreasing, auto)
    apply (rule exI, rule conjI, rule deriv_g)
    apply (erule order_less_le_trans, auto)
    apply (rule order_le_less_trans, subst ereal_less_eq(3), assumption, auto)
    apply (rule g'_nonneg)
    apply (rule less_imp_le, erule order_less_le_trans, auto)
    by (rule less_imp_le, rule le_less_trans, subst ereal_less_eq(3), assumption, auto)
  have "A \<le> B" and un: "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
  proof - 
    have A2: "(\<lambda>i. g (l i)) ----> A"
      using A apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<ge> A"
      by (intro decseq_le, auto simp add: decseq_def)
    have B2: "(\<lambda>i. g (u i)) ----> B"
      using B apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<le> B"
      by (intro incseq_le, auto simp add: incseq_def)
    show "A \<le> B"
      apply (rule order_trans [OF A3 [of 0]])
      apply (rule order_trans [OF _ B3 [of 0]])
      by auto
    { fix x :: real
      assume "A < x" and "x < B"   
      then have "eventually (\<lambda>i. ereal (g (l i)) < x \<and> x < ereal (g (u i))) sequentially"
        apply (intro eventually_conj order_tendstoD)
        by (rule A2, assumption, rule B2, assumption)
      hence "\<exists>i. g (l i) < x \<and> x < g (u i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
      apply (auto simp add: einterval_def)
      apply (erule (1) AB)
      apply (rule order_le_less_trans, rule A3, simp)
      apply (rule order_less_le_trans) prefer 2
      by (rule B3, simp) 
  qed
  (* finally, the main argument *)
  {
     fix i
     have "(LBINT x=l i.. u i. g' x *\<^sub>R f (g x)) = (LBINT y=g (l i)..g (u i). f y)"
        apply (rule interval_integral_substitution_finite, auto)
        apply (rule DERIV_subset, rule deriv_g, auto)
        apply (rule continuous_at_imp_continuous_on, auto, rule contf, auto)
        by (rule continuous_at_imp_continuous_on, auto, rule contg', auto)
     then have "(LBINT x=l i.. u i. (f (g x) * g' x)) = (LBINT y=g (l i)..g (u i). f y)"
       by (simp add: ac_simps)
  } note eq1 = this
  have "(\<lambda>i. LBINT x=l i..u i. f (g x) * g' x)
      ----> (LBINT x=a..b. f (g x) * g' x)"
    apply (rule interval_integral_Icc_approx_integrable [OF `a < b` approx])
    by (rule assms)
  hence 2: "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x=a..b. f (g x) * g' x)"
    by (simp add: eq1)
  have incseq: "incseq (\<lambda>i. {g (l i)<..<g (u i)})"
    apply (auto simp add: incseq_def)
    apply (rule order_le_less_trans)
    prefer 2 apply assumption
    apply (rule g_nondec, auto)
    by (erule order_less_le_trans, rule g_nondec, auto)
  have img: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> \<exists>c \<ge> l i. c \<le> u i \<and> x = g c"
    apply (frule (1) IVT' [of g], auto)   
    apply (rule continuous_at_imp_continuous_on, auto)
    by (rule DERIV_isCont, rule deriv_g, auto)
  have nonneg_f2: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> 0 \<le> f x"
    by (frule (1) img, auto, rule f_nonneg, auto)
  have contf_2: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> isCont f x"
    by (frule (1) img, auto, rule contf, auto)
  have integrable: "set_integrable lborel (\<Union>i. {g (l i)<..<g (u i)}) f"
    apply (rule pos_integrable_to_top, auto simp del: real_scaleR_def)
    apply (rule incseq)
    apply (rule nonneg_f2, erule less_imp_le, erule less_imp_le)
    apply (rule set_integrable_subset)
    apply (rule borel_integrable_atLeastAtMost')
    apply (rule continuous_at_imp_continuous_on)
    apply (clarsimp, erule (1) contf_2, auto)
    apply (erule less_imp_le)+
    using 2 unfolding interval_lebesgue_integral_def
    by auto
  thus "set_integrable lborel (einterval A B) f"
    by (simp add: un)

  have "(LBINT x=A..B. f x) = (LBINT x=a..b. g' x *\<^sub>R f (g x))"
  proof (rule interval_integral_substitution_integrable)
    show "set_integrable lborel (einterval a b) (\<lambda>x. g' x *\<^sub>R f (g x))"
      using integrable_fg by (simp add: ac_simps)
  qed fact+
  then show "(LBINT x=A..B. f x) = (LBINT x=a..b. (f (g x) * g' x))"
    by (simp add: ac_simps)
qed


syntax
"_complex_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> complex"
("(2CLBINT _. _)" [0,60] 60)

translations
"CLBINT x. f" == "CONST complex_lebesgue_integral CONST lborel (\<lambda>x. f)"

syntax
"_complex_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> complex"
("(3CLBINT _:_. _)" [0,60,61] 60)

translations
"CLBINT x:A. f" == "CONST complex_set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

abbreviation complex_interval_lebesgue_integral :: 
    "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_interval_lebesgue_integral M a b f \<equiv> interval_lebesgue_integral M a b f"

abbreviation complex_interval_lebesgue_integrable :: 
  "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_interval_lebesgue_integrable M a b f \<equiv> interval_lebesgue_integrable M a b f"

syntax
  "_ascii_complex_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> real \<Rightarrow> complex"
  ("(4CLBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "CLBINT x=a..b. f" == "CONST complex_interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

lemma interval_integral_norm:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "interval_lebesgue_integrable lborel a b f \<Longrightarrow> a \<le> b \<Longrightarrow>
    norm (LBINT t=a..b. f t) \<le> LBINT t=a..b. norm (f t)"
  using integral_norm_bound[of lborel "\<lambda>x. indicator (einterval a b) x *\<^sub>R f x"]
  by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def)

lemma interval_integral_norm2:
  "interval_lebesgue_integrable lborel a b f \<Longrightarrow> 
    norm (LBINT t=a..b. f t) \<le> abs (LBINT t=a..b. norm (f t))"
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (simp add: interval_integral_endpoints_reverse[of a b] interval_integrable_endpoints_reverse[of a b])
next
  case (le a b) 
  then have "\<bar>LBINT t=a..b. norm (f t)\<bar> = LBINT t=a..b. norm (f t)"  
    using integrable_norm[of lborel "\<lambda>x. indicator (einterval a b) x *\<^sub>R f x"]
    by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def
             intro!: integral_nonneg_AE abs_of_nonneg)
  then show ?case
    using le by (simp add: interval_integral_norm)
qed

(* TODO: should we have a library of facts like these? *)
lemma integral_cos: "t \<noteq> 0 \<Longrightarrow> LBINT x=a..b. cos (t * x) = sin (t * b) / t - sin (t * a) / t"
  apply (intro interval_integral_FTC_finite continuous_intros)
  by (auto intro!: derivative_eq_intros simp: has_field_derivative_iff_has_vector_derivative[symmetric])


end
