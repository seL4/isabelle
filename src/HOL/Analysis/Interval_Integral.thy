(*  Title:      HOL/Analysis/Interval_Integral.thy
    Author:     Jeremy Avigad (CMU), Johannes Hölzl (TUM), Luke Serafin (CMU)

Lebesgue integral over an interval (with endpoints possibly +-\<infinity>)
*)

theory Interval_Integral (*FIX ME rename? Lebesgue  *)
  imports Equivalence_Lebesgue_Henstock_Integration
begin

definition "einterval a b = {x. a < ereal x \<and> ereal x < b}"

lemma einterval_eq[simp]:
  shows einterval_eq_Icc: "einterval (ereal a) (ereal b) = {a <..< b}"
    and einterval_eq_Ici: "einterval (ereal a) \<infinity> = {a <..}"
    and einterval_eq_Iic: "einterval (- \<infinity>) (ereal b) = {..< b}"
    and einterval_eq_UNIV: "einterval (- \<infinity>) \<infinity> = UNIV"
  by (auto simp: einterval_def)

lemma einterval_same: "einterval a a = {}"
  by (auto simp: einterval_def)

lemma einterval_iff: "x \<in> einterval a b \<longleftrightarrow> a < ereal x \<and> ereal x < b"
  by (simp add: einterval_def)

lemma einterval_nonempty: "a < b \<Longrightarrow> \<exists>c. c \<in> einterval a b"
  by (cases a b rule: ereal2_cases, auto simp: einterval_def intro!: dense gt_ex lt_ex)

lemma open_einterval[simp]: "open (einterval a b)"
  by (cases a b rule: ereal2_cases)
     (auto simp: einterval_def intro!: open_Collect_conj open_Collect_less continuous_intros)

lemma borel_einterval[measurable]: "einterval a b \<in> sets borel"
  unfolding einterval_def by measurable

subsection \<open>Approximating a (possibly infinite) interval\<close>

lemma filterlim_sup1: "(LIM x F. f x :> G1) \<Longrightarrow> (LIM x F. f x :> (sup G1 G2))"
 unfolding filterlim_def by (auto intro: le_supI1)

lemma ereal_incseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where "incseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X \<longlonglongrightarrow> b"
proof (cases b)
  case PInf
  with \<open>a < b\<close> have "a = -\<infinity> \<or> (\<exists>r. a = ereal r)"
    by (cases a) auto
  moreover have "(\<lambda>x. ereal (real (Suc x))) \<longlonglongrightarrow> \<infinity>"
    by (simp add: Lim_PInfty filterlim_sequentially_Suc) (metis le_SucI of_nat_Suc of_nat_mono order_trans real_arch_simple)
  moreover have "\<And>r. (\<lambda>x. ereal (r + real (Suc x))) \<longlonglongrightarrow> \<infinity>"
    by (simp add: filterlim_sequentially_Suc Lim_PInfty) (metis add.commute diff_le_eq nat_ceiling_le_eq)
  ultimately show thesis
    by (intro that[of "\<lambda>i. real_of_ereal a + Suc i"])
       (auto simp: incseq_def PInf)
next
  case (real b')
  define d where "d = b' - (if a = -\<infinity> then b' - 1 else real_of_ereal a)"
  with \<open>a < b\<close> have a': "0 < d"
    by (cases a) (auto simp: real)
  moreover
  have "\<And>i r. r < b' \<Longrightarrow> (b' - r) * 1 < (b' - r) * real (Suc (Suc i))"
    by (intro mult_strict_left_mono) auto
  with \<open>a < b\<close> a' have "\<And>i. a < ereal (b' - d / real (Suc (Suc i)))"
    by (cases a) (auto simp: real d_def field_simps)
  moreover
  have "(\<lambda>i. b' - d / real i) \<longlonglongrightarrow> b'"
    by (force intro: tendsto_eq_intros tendsto_divide_0[OF tendsto_const] filterlim_sup1
              simp: at_infinity_eq_at_top_bot filterlim_real_sequentially)
  then have "(\<lambda>i. b' - d / Suc (Suc i)) \<longlonglongrightarrow> b'"
    by (blast intro: dest: filterlim_sequentially_Suc [THEN iffD2])
  ultimately show thesis
    by (intro that[of "\<lambda>i. b' - d / Suc (Suc i)"])
       (auto simp: real incseq_def intro!: divide_left_mono)
qed (insert \<open>a < b\<close>, auto)

lemma ereal_decseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where
    "decseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X \<longlonglongrightarrow> a"
proof -
  have "-b < -a" using \<open>a < b\<close> by simp
  from ereal_incseq_approx[OF this] guess X .
  then show thesis
    apply (intro that[of "\<lambda>i. - X i"])
    apply (auto simp: decseq_def incseq_def simp flip: uminus_ereal.simps)
    apply (metis ereal_minus_less_minus ereal_uminus_uminus ereal_Lim_uminus)+
    done
qed

proposition einterval_Icc_approximation:
  fixes a b :: ereal
  assumes "a < b"
  obtains u l :: "nat \<Rightarrow> real" where
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b"
proof -
  from dense[OF \<open>a < b\<close>] obtain c where "a < c" "c < b" by safe
  from ereal_incseq_approx[OF \<open>c < b\<close>] guess u . note u = this
  from ereal_decseq_approx[OF \<open>a < c\<close>] guess l . note l = this
  { fix i from less_trans[OF \<open>l i < c\<close> \<open>c < u i\<close>] have "l i < u i" by simp }
  have "einterval a b = (\<Union>i. {l i .. u i})"
  proof (auto simp: einterval_iff)
    fix x assume "a < ereal x" "ereal x < b"
    have "eventually (\<lambda>i. ereal (l i) < ereal x) sequentially"
      using l(4) \<open>a < ereal x\<close> by (rule order_tendstoD)
    moreover
    have "eventually (\<lambda>i. ereal x < ereal (u i)) sequentially"
      using u(4) \<open>ereal x< b\<close> by (rule order_tendstoD)
    ultimately have "eventually (\<lambda>i. l i < x \<and> x < u i) sequentially"
      by eventually_elim auto
    then show "\<exists>i. l i \<le> x \<and> x \<le> u i"
      by (auto intro: less_imp_le simp: eventually_sequentially)
  next
    fix x i assume "l i \<le> x" "x \<le> u i"
    with \<open>a < ereal (l i)\<close> \<open>ereal (u i) < b\<close>
    show "a < ereal x" "ereal x < b"
      by (auto simp flip: ereal_less_eq(3))
  qed
  show thesis
    by (intro that) fact+
qed

(* TODO: in this definition, it would be more natural if einterval a b included a and b when
   they are real. *)
definition\<^marker>\<open>tag important\<close> interval_lebesgue_integral :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> 'a::{banach, second_countable_topology}" where
  "interval_lebesgue_integral M a b f =
    (if a \<le> b then (LINT x:einterval a b|M. f x) else - (LINT x:einterval b a|M. f x))"

syntax
  "_ascii_interval_lebesgue_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _=_.._|_. _)" [0,60,60,61,100] 60)

translations
  "LINT x=a..b|M. f" == "CONST interval_lebesgue_integral M a b (\<lambda>x. f)"

definition\<^marker>\<open>tag important\<close> interval_lebesgue_integrable :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> 'a::{banach, second_countable_topology}) \<Rightarrow> bool" where
  "interval_lebesgue_integrable M a b f =
    (if a \<le> b then set_integrable M (einterval a b) f else set_integrable M (einterval b a) f)"

syntax
  "_ascii_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

subsection\<open>Basic properties of integration over an interval\<close>

lemma interval_lebesgue_integral_cong:
  "a \<le> b \<Longrightarrow> (\<And>x. x \<in> einterval a b \<Longrightarrow> f x = g x) \<Longrightarrow> einterval a b \<in> sets M \<Longrightarrow>
    interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b g"
  by (auto intro: set_lebesgue_integral_cong simp: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_cong_AE:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    a \<le> b \<Longrightarrow> AE x \<in> einterval a b in M. f x = g x \<Longrightarrow> einterval a b \<in> sets M \<Longrightarrow>
    interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b g"
  by (auto intro: set_lebesgue_integral_cong_AE simp: interval_lebesgue_integral_def)

lemma interval_integrable_mirror:
  shows "interval_lebesgue_integrable lborel a b (\<lambda>x. f (-x)) \<longleftrightarrow>
    interval_lebesgue_integrable lborel (-b) (-a) f"
proof -
  have *: "indicator (einterval a b) (- x) = (indicator (einterval (-b) (-a)) x :: real)"
    for a b :: ereal and x :: real
    by (cases a b rule: ereal2_cases) (auto simp: einterval_def split: split_indicator)
  show ?thesis
    unfolding interval_lebesgue_integrable_def
    using lborel_integrable_real_affine_iff[symmetric, of "-1" "\<lambda>x. indicator (einterval _ _) x *\<^sub>R f x" 0]
    by (simp add: * set_integrable_def)
qed

lemma interval_lebesgue_integral_add [intro, simp]:
  fixes M a b f
  assumes "interval_lebesgue_integrable M a b f" "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. f x + g x)" and
    "interval_lebesgue_integral M a b (\<lambda>x. f x + g x) =
   interval_lebesgue_integral M a b f + interval_lebesgue_integral M a b g"
using assms by (auto simp: interval_lebesgue_integral_def interval_lebesgue_integrable_def
    field_simps)

lemma interval_lebesgue_integral_diff [intro, simp]:
  fixes M a b f
  assumes "interval_lebesgue_integrable M a b f"
    "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. f x - g x)" and
    "interval_lebesgue_integral M a b (\<lambda>x. f x - g x) =
   interval_lebesgue_integral M a b f - interval_lebesgue_integral M a b g"
using assms by (auto simp: interval_lebesgue_integral_def interval_lebesgue_integrable_def
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
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, field, second_countable_topology}"
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
  fixes M a b c and f :: "real \<Rightarrow> 'a::{banach, real_normed_field, field, second_countable_topology}"
  shows "interval_lebesgue_integral M a b (\<lambda>x. f x / c) =
    interval_lebesgue_integral M a b f / c"
  by (simp add: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_uminus:
  "interval_lebesgue_integral M a b (\<lambda>x. - f x) = - interval_lebesgue_integral M a b f"
  by (auto simp: interval_lebesgue_integral_def interval_lebesgue_integrable_def set_lebesgue_integral_def)

lemma interval_lebesgue_integral_of_real:
  "interval_lebesgue_integral M a b (\<lambda>x. complex_of_real (f x)) =
    of_real (interval_lebesgue_integral M a b f)"
  unfolding interval_lebesgue_integral_def
  by (auto simp: interval_lebesgue_integral_def set_integral_complex_of_real)

lemma interval_lebesgue_integral_le_eq:
  fixes a b f
  assumes "a \<le> b"
  shows "interval_lebesgue_integral M a b f = (LINT x : einterval a b | M. f x)"
  using assms by (auto simp: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_gt_eq:
  fixes a b f
  assumes "a > b"
  shows "interval_lebesgue_integral M a b f = -(LINT x : einterval b a | M. f x)"
using assms by (auto simp: interval_lebesgue_integral_def less_imp_le einterval_def)

lemma interval_lebesgue_integral_gt_eq':
  fixes a b f
  assumes "a > b"
  shows "interval_lebesgue_integral M a b f = - interval_lebesgue_integral M b a f"
using assms by (auto simp: interval_lebesgue_integral_def less_imp_le einterval_def)

lemma interval_integral_endpoints_same [simp]: "(LBINT x=a..a. f x) = 0"
  by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def einterval_same)

lemma interval_integral_endpoints_reverse: "(LBINT x=a..b. f x) = -(LBINT x=b..a. f x)"
  by (cases a b rule: linorder_cases) (auto simp: interval_lebesgue_integral_def set_lebesgue_integral_def einterval_same)

lemma interval_integrable_endpoints_reverse:
  "interval_lebesgue_integrable lborel a b f \<longleftrightarrow>
    interval_lebesgue_integrable lborel b a f"
  by (cases a b rule: linorder_cases) (auto simp: interval_lebesgue_integrable_def einterval_same)

lemma interval_integral_reflect:
  "(LBINT x=a..b. f x) = (LBINT x=-b..-a. f (-x))"
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (auto simp: interval_lebesgue_integral_def interval_integrable_endpoints_reverse
             split: if_split_asm)
next
  case (le a b) 
  have "LBINT x:{x. - x \<in> einterval a b}. f (- x) = LBINT x:einterval (- b) (- a). f (- x)"
    unfolding interval_lebesgue_integrable_def set_lebesgue_integral_def
    apply (rule Bochner_Integration.integral_cong [OF refl])
    by (auto simp: einterval_iff ereal_uminus_le_reorder ereal_uminus_less_reorder not_less
             simp flip: uminus_ereal.simps
             split: split_indicator)
  then show ?case
    unfolding interval_lebesgue_integral_def 
    by (subst set_integral_reflect) (simp add: le)
qed

lemma interval_lebesgue_integral_0_infty:
  "interval_lebesgue_integrable M 0 \<infinity> f \<longleftrightarrow> set_integrable M {0<..} f"
  "interval_lebesgue_integral M 0 \<infinity> f = (LINT x:{0<..}|M. f x)"
  unfolding zero_ereal_def
  by (auto simp: interval_lebesgue_integral_le_eq interval_lebesgue_integrable_def)

lemma interval_integral_to_infinity_eq: "(LINT x=ereal a..\<infinity> | M. f x) = (LINT x : {a<..} | M. f x)"
  unfolding interval_lebesgue_integral_def by auto

proposition interval_integrable_to_infinity_eq: "(interval_lebesgue_integrable M a \<infinity> f) =
  (set_integrable M {a<..} f)"
  unfolding interval_lebesgue_integrable_def by auto

subsection\<open>Basic properties of integration over an interval wrt lebesgue measure\<close>

lemma interval_integral_zero [simp]:
  fixes a b :: ereal
  shows "LBINT x=a..b. 0 = 0"
unfolding interval_lebesgue_integral_def set_lebesgue_integral_def einterval_eq
by simp

lemma interval_integral_const [intro, simp]:
  fixes a b c :: real
  shows "interval_lebesgue_integrable lborel a b (\<lambda>x. c)" and "LBINT x=a..b. c = c * (b - a)"
  unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def einterval_eq
  by (auto simp: less_imp_le field_simps measure_def set_integrable_def set_lebesgue_integral_def)

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
  apply (simp add: interval_lebesgue_integrable_def)
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
  by (auto intro!: set_integral_discrete_difference[where X="{real_of_ereal a, real_of_ereal b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ioc:
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {a<..b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{a, b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

(* TODO: other versions as well? *) (* Yes: I need the Icc' version. *)
lemma interval_integral_Ioc':
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {x. a < ereal x \<and> ereal x \<le> b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{real_of_ereal a, real_of_ereal b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ico:
  "a \<le> b \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {a..<b}. f x)"
  by (auto intro!: set_integral_discrete_difference[where X="{a, b}"]
           simp add: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ioi:
  "\<bar>a\<bar> < \<infinity> \<Longrightarrow> (LBINT x=a..\<infinity>. f x) = (LBINT x : {real_of_ereal a <..}. f x)"
  by (auto simp: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_Ioo:
  "a \<le> b \<Longrightarrow> \<bar>a\<bar> < \<infinity> ==> \<bar>b\<bar> < \<infinity> \<Longrightarrow> (LBINT x=a..b. f x) = (LBINT x : {real_of_ereal a <..< real_of_ereal b}. f x)"
  by (auto simp: interval_lebesgue_integral_def einterval_iff)

lemma interval_integral_discrete_difference:
  fixes f :: "real \<Rightarrow> 'b::{banach, second_countable_topology}" and a b :: ereal
  assumes "countable X"
  and eq: "\<And>x. a \<le> b \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow> x \<notin> X \<Longrightarrow> f x = g x"
  and anti_eq: "\<And>x. b \<le> a \<Longrightarrow> b < x \<Longrightarrow> x < a \<Longrightarrow> x \<notin> X \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b g"
  unfolding interval_lebesgue_integral_def set_lebesgue_integral_def
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
      unfolding set_integrable_def set_borel_measurable_def
      by (drule_tac borel_measurable_integrable) simp
    have "(LBINT x:einterval a c. f x) = (LBINT x:einterval a b \<union> einterval b c. f x)"
    proof (rule set_integral_cong_set)
      show "AE x in lborel. (x \<in> einterval a b \<union> einterval b c) = (x \<in> einterval a c)"
        using AE_lborel_singleton[of "real_of_ereal b"] ord
        by (cases a b c rule: ereal3_cases) (auto simp: einterval_iff)
      show "set_borel_measurable lborel (einterval a c) f" "set_borel_measurable lborel (einterval a b \<union> einterval b c) f"
        unfolding set_borel_measurable_def
        using ord by (auto simp: einterval_iff intro!: set_borel_measurable_subset[OF f, unfolded set_borel_measurable_def])
    qed
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
    apply (cases a b b c a c rule: linorder_le_cases[case_product linorder_le_cases linorder_cases])
    apply simp_all (* remove some looping cases *)
    by (simp_all add: min_absorb1 min_absorb2 max_absorb1 max_absorb2 field_simps 1 2 3)
qed

lemma interval_integrable_isCont:
  fixes a b and f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  shows "(\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow> isCont f x) \<Longrightarrow>
    interval_lebesgue_integrable lborel a b f"
proof (induct a b rule: linorder_wlog)
  case (le a b) then show ?case
    unfolding interval_lebesgue_integrable_def set_integrable_def
    by (auto simp: interval_lebesgue_integrable_def
        intro!: set_integrable_subset[unfolded set_integrable_def, OF borel_integrable_compact[of "{a .. b}"]]
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


subsection\<open>General limit approximation arguments\<close>

proposition interval_integral_Icc_approx_nonneg:
  fixes a b :: ereal
  assumes "a < b"
  fixes u l :: "nat \<Rightarrow> real"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b"
  fixes f :: "real \<Rightarrow> real"
  assumes f_integrable: "\<And>i. set_integrable lborel {l i..u i} f"
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes f_measurable: "set_borel_measurable lborel (einterval a b) f"
  assumes lbint_lim: "(\<lambda>i. LBINT x=l i.. u i. f x) \<longlonglongrightarrow> C"
  shows
    "set_integrable lborel (einterval a b) f"
    "(LBINT x=a..b. f x) = C"
proof -
  have 1 [unfolded set_integrable_def]: "\<And>i. set_integrable lborel {l i..u i} f" by (rule f_integrable)
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
  have 3: "AE x in lborel. (\<lambda>i. indicator {l i..u i} x *\<^sub>R f x) \<longlonglongrightarrow> indicator (einterval a b) x *\<^sub>R f x"
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
      unfolding approx(1) by (auto intro!: AE_I2 tendsto_eventually split: split_indicator)
  qed
  have 4: "(\<lambda>i. \<integral> x. indicator {l i..u i} x *\<^sub>R f x \<partial>lborel) \<longlonglongrightarrow> C"
    using lbint_lim by (simp add: interval_integral_Icc [unfolded set_lebesgue_integral_def] approx less_imp_le)
  have 5: "(\<lambda>x. indicat_real (einterval a b) x *\<^sub>R f x) \<in> borel_measurable lborel"
    using f_measurable set_borel_measurable_def by blast
  have "(LBINT x=a..b. f x) = lebesgue_integral lborel (\<lambda>x. indicator (einterval a b) x *\<^sub>R f x)"
    using assms by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def less_imp_le)
  also have "\<dots> = C"
    by (rule integral_monotone_convergence [OF 1 2 3 4 5])
  finally show "(LBINT x=a..b. f x) = C" .
  show "set_integrable lborel (einterval a b) f"
    unfolding set_integrable_def
    by (rule integrable_monotone_convergence[OF 1 2 3 4 5])
qed

proposition interval_integral_Icc_approx_integrable:
  fixes u l :: "nat \<Rightarrow> real" and a b :: ereal
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes "a < b"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b"
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  shows "(\<lambda>i. LBINT x=l i.. u i. f x) \<longlonglongrightarrow> (LBINT x=a..b. f x)"
proof -
  have "(\<lambda>i. LBINT x:{l i.. u i}. f x) \<longlonglongrightarrow> (LBINT x:einterval a b. f x)"
    unfolding set_lebesgue_integral_def
  proof (rule integral_dominated_convergence)
    show "integrable lborel (\<lambda>x. norm (indicator (einterval a b) x *\<^sub>R f x))"
      using f_integrable integrable_norm set_integrable_def by blast
    show "(\<lambda>x. indicat_real (einterval a b) x *\<^sub>R f x) \<in> borel_measurable lborel"
      using f_integrable by (simp add: set_integrable_def)
    then show "\<And>i. (\<lambda>x. indicat_real {l i..u i} x *\<^sub>R f x) \<in> borel_measurable lborel"
      by (rule set_borel_measurable_subset [unfolded set_borel_measurable_def]) (auto simp: approx)
    show "\<And>i. AE x in lborel. norm (indicator {l i..u i} x *\<^sub>R f x) \<le> norm (indicator (einterval a b) x *\<^sub>R f x)"
      by (intro AE_I2) (auto simp: approx split: split_indicator)
    show "AE x in lborel. (\<lambda>i. indicator {l i..u i} x *\<^sub>R f x) \<longlonglongrightarrow> indicator (einterval a b) x *\<^sub>R f x"
    proof (intro AE_I2 tendsto_intros tendsto_eventually)
      fix x
      { fix i assume "l i \<le> x" "x \<le> u i"
        with \<open>incseq u\<close>[THEN incseqD, of i] \<open>decseq l\<close>[THEN decseqD, of i]
        have "eventually (\<lambda>i. l i \<le> x \<and> x \<le> u i) sequentially"
          by (auto simp: eventually_sequentially decseq_def incseq_def intro: order_trans) }
      then show "eventually (\<lambda>xa. indicator {l xa..u xa} x = (indicator (einterval a b) x::real)) sequentially"
        using approx order_tendstoD(2)[OF \<open>l \<longlonglongrightarrow> a\<close>, of x] order_tendstoD(1)[OF \<open>u \<longlonglongrightarrow> b\<close>, of x]
        by (auto split: split_indicator)
    qed
  qed
  with \<open>a < b\<close> \<open>\<And>i. l i < u i\<close> show ?thesis
    by (simp add: interval_lebesgue_integral_le_eq[symmetric] interval_integral_Icc less_imp_le)
qed

subsection\<open>A slightly stronger Fundamental Theorem of Calculus\<close>

text\<open>Three versions: first, for finite intervals, and then two versions for
    arbitrary intervals.\<close>

(*
  TODO: make the older versions corollaries of these (using continuous_at_imp_continuous_on, etc.)
*)

lemma interval_integral_FTC_finite:
  fixes f F :: "real \<Rightarrow> 'a::euclidean_space" and a b :: real
  assumes f: "continuous_on {min a b..max a b} f"
  assumes F: "\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow> (F has_vector_derivative (f x)) (at x within
    {min a b..max a b})"
  shows "(LBINT x=a..b. f x) = F b - F a"
proof (cases "a \<le> b")
  case True
  have "(LBINT x=a..b. f x) = (LBINT x. indicat_real {a..b} x *\<^sub>R f x)"
    by (simp add: True interval_integral_Icc set_lebesgue_integral_def)
  also have "\<dots> = F b - F a"
  proof (rule integral_FTC_atLeastAtMost [OF True])
    show "continuous_on {a..b} f"
      using True f by linarith
    show "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> (F has_vector_derivative f x) (at x within {a..b})"
      by (metis F True max.commute max_absorb1 min_def)
  qed
  finally show ?thesis .
next
  case False
  then have "b \<le> a"
    by simp
  have "- interval_lebesgue_integral lborel (ereal b) (ereal a) f = - (LBINT x. indicat_real {b..a} x *\<^sub>R f x)"
    by (simp add: \<open>b \<le> a\<close> interval_integral_Icc set_lebesgue_integral_def)
  also have "\<dots> = F b - F a"
  proof (subst integral_FTC_atLeastAtMost [OF \<open>b \<le> a\<close>])
    show "continuous_on {b..a} f"
      using False f by linarith
    show "\<And>x. \<lbrakk>b \<le> x; x \<le> a\<rbrakk>
         \<Longrightarrow> (F has_vector_derivative f x) (at x within {b..a})"
      by (metis F False max_def min_def)
  qed auto
  finally show ?thesis
    by (metis interval_integral_endpoints_reverse)
qed


lemma interval_integral_FTC_nonneg:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F x :> f x"
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x"
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes A: "((F \<circ> real_of_ereal) \<longlongrightarrow> A) (at_right a)"
  assumes B: "((F \<circ> real_of_ereal) \<longlongrightarrow> B) (at_left b)"
  shows
    "set_integrable lborel (einterval a b) f"
    "(LBINT x=a..b. f x) = B - A"
proof -
  obtain u l where approx:
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b" 
    by (blast intro: einterval_Icc_approximation[OF \<open>a < b\<close>])
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx apply (intro interval_integral_FTC_finite)
    apply (auto simp: less_imp_le min_def max_def
      has_field_derivative_iff_has_vector_derivative[symmetric])
    apply (rule continuous_at_imp_continuous_on, auto intro!: f)
    by (rule DERIV_subset [OF F], auto)
  have 1: "\<And>i. set_integrable lborel {l i..u i} f"
  proof -
    fix i show "set_integrable lborel {l i .. u i} f"
      using \<open>a < l i\<close> \<open>u i < b\<close> unfolding set_integrable_def
      by (intro borel_integrable_compact f continuous_at_imp_continuous_on compact_Icc ballI)
         (auto simp flip: ereal_less_eq)
  qed
  have 2: "set_borel_measurable lborel (einterval a b) f"
    unfolding set_borel_measurable_def
    by (auto simp del: real_scaleR_def intro!: borel_measurable_continuous_on_indicator
             simp: continuous_on_eq_continuous_at einterval_iff f)
  have 3: "(\<lambda>i. LBINT x=l i..u i. f x) \<longlonglongrightarrow> B - A"
    apply (subst FTCi)
    apply (intro tendsto_intros)
    using B approx unfolding tendsto_at_iff_sequentially comp_def
    using tendsto_at_iff_sequentially[where 'a=real]
    apply (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
    using A approx unfolding tendsto_at_iff_sequentially comp_def
    by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
  show "(LBINT x=a..b. f x) = B - A"
    by (rule interval_integral_Icc_approx_nonneg [OF \<open>a < b\<close> approx 1 f_nonneg 2 3])
  show "set_integrable lborel (einterval a b) f"
    by (rule interval_integral_Icc_approx_nonneg [OF \<open>a < b\<close> approx 1 f_nonneg 2 3])
qed

theorem interval_integral_FTC_integrable:
  fixes f F :: "real \<Rightarrow> 'a::euclidean_space" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> (F has_vector_derivative f x) (at x)"
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x"
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  assumes A: "((F \<circ> real_of_ereal) \<longlongrightarrow> A) (at_right a)"
  assumes B: "((F \<circ> real_of_ereal) \<longlongrightarrow> B) (at_left b)"
  shows "(LBINT x=a..b. f x) = B - A"
proof -
  obtain u l where approx:
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b" 
    by (blast intro: einterval_Icc_approximation[OF \<open>a < b\<close>])
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx
    by (auto simp: less_imp_le min_def max_def
             intro!: f continuous_at_imp_continuous_on interval_integral_FTC_finite
             intro: has_vector_derivative_at_within)
  have "(\<lambda>i. LBINT x=l i..u i. f x) \<longlonglongrightarrow> B - A"
    unfolding FTCi
  proof (intro tendsto_intros)
    show "(\<lambda>x. F (l x)) \<longlonglongrightarrow> A"
      using A approx unfolding tendsto_at_iff_sequentially comp_def
      by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
    show "(\<lambda>x. F (u x)) \<longlonglongrightarrow> B"
      using B approx unfolding tendsto_at_iff_sequentially comp_def
      by (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
  qed
  moreover have "(\<lambda>i. LBINT x=l i..u i. f x) \<longlonglongrightarrow> (LBINT x=a..b. f x)"
    by (rule interval_integral_Icc_approx_integrable [OF \<open>a < b\<close> approx f_integrable])
  ultimately show ?thesis
    by (elim LIMSEQ_unique)
qed

(*
  The second Fundamental Theorem of Calculus and existence of antiderivatives on an
  einterval.
*)

theorem interval_integral_FTC2:
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
    using \<open>a \<le> x\<close> \<open>x \<le> b\<close> 
    by (auto intro: integral_has_vector_derivative continuous_on_subset [OF contf])
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
      apply (auto simp: interval_lebesgue_integrable_def simp del: real_scaleR_def)
      by (rule set_integrable_subset [OF intf], auto simp: min_def max_def)
  qed (insert assms, auto)
qed

proposition einterval_antiderivative:
  fixes a b :: ereal and f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a < b" and contf: "\<And>x :: real. a < x \<Longrightarrow> x < b \<Longrightarrow> isCont f x"
  shows "\<exists>F. \<forall>x :: real. a < x \<longrightarrow> x < b \<longrightarrow> (F has_vector_derivative f x) (at x)"
proof -
  from einterval_nonempty [OF \<open>a < b\<close>] obtain c :: real where [simp]: "a < c" "c < b"
    by (auto simp: einterval_def)
  let ?F = "(\<lambda>u. LBINT y=c..u. f y)"
  show ?thesis
  proof (rule exI, clarsimp)
    fix x :: real
    assume [simp]: "a < x" "x < b"
    have 1: "a < min c x" by simp
    from einterval_nonempty [OF 1] obtain d :: real where [simp]: "a < d" "d < c" "d < x"
      by (auto simp: einterval_def)
    have 2: "max c x < b" by simp
    from einterval_nonempty [OF 2] obtain e :: real where [simp]: "c < e" "x < e" "e < b"
      by (auto simp: einterval_def)
    have "(?F has_vector_derivative f x) (at x within {d<..<e})"
    proof (rule has_vector_derivative_within_subset [of _ _ _ "{d..e}"])
      have "continuous_on {d..e} f"
      proof (intro continuous_at_imp_continuous_on ballI contf; clarsimp)
        show "\<And>x. \<lbrakk>d \<le> x; x \<le> e\<rbrakk> \<Longrightarrow> a < ereal x"
          using \<open>a < ereal d\<close> ereal_less_ereal_Ex by auto
        show "\<And>x. \<lbrakk>d \<le> x; x \<le> e\<rbrakk> \<Longrightarrow> ereal x < b"
          using \<open>ereal e < b\<close> ereal_less_eq(3) le_less_trans by blast
      qed
      then show "(?F has_vector_derivative f x) (at x within {d..e})"
        by (intro interval_integral_FTC2) (use \<open>d < c\<close> \<open>c < e\<close> \<open>d < x\<close> \<open>x < e\<close> in \<open>linarith+\<close>)
    qed auto
    then show "(?F has_vector_derivative f x) (at x)"
      by (force simp: has_vector_derivative_within_open [of _ "{d<..<e}"])
  qed
qed

subsection\<open>The substitution theorem\<close>

text\<open>Once again, three versions: first, for finite intervals, and then two versions for
    arbitrary intervals.\<close>

theorem interval_integral_substitution_finite:
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
  have 1: "\<exists>x\<in>{a..b}. u = g x" if "min (g a) (g b) \<le> u" "u \<le> max (g a) (g b)" for u
    by (cases "g a \<le> g b") (use that assms IVT' [of g a u b]  IVT2' [of g b u a]  in \<open>auto simp: min_def max_def\<close>)
  obtain c d where g_im: "g ` {a..b} = {c..d}" and "c \<le> d"
    by (metis continuous_image_closed_interval contg \<open>a \<le> b\<close>)
  obtain F where derivF:
         "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> (F has_vector_derivative (f (g x))) (at (g x) within (g ` {a..b}))" 
    using continuous_on_subset [OF contf] g_im
      by (metis antiderivative_continuous atLeastAtMost_iff image_subset_iff set_eq_subset)
  have contfg: "continuous_on {a..b} (\<lambda>x. f (g x))"
    by (blast intro: continuous_on_compose2 contf contg)
  have "LBINT x. indicat_real {a..b} x *\<^sub>R g' x *\<^sub>R f (g x) = F (g b) - F (g a)"
    apply (rule integral_FTC_atLeastAtMost
                [OF \<open>a \<le> b\<close> vector_diff_chain_within[OF v_derivg derivF, unfolded comp_def]])
    apply (auto intro!: continuous_on_scaleR contg' contfg)
    done
  then have "LBINT x=a..b. g' x *\<^sub>R f (g x) = F (g b) - F (g a)"
    by (simp add: assms interval_integral_Icc set_lebesgue_integral_def)
  moreover have "LBINT y=(g a)..(g b). f y = F (g b) - F (g a)"
  proof (rule interval_integral_FTC_finite)
    show "continuous_on {min (g a) (g b)..max (g a) (g b)} f"
      by (rule continuous_on_subset [OF contf]) (auto simp: image_def 1)
    show "(F has_vector_derivative f y) (at y within {min (g a) (g b)..max (g a) (g b)})" 
      if y: "min (g a) (g b) \<le> y" "y \<le> max (g a) (g b)" for y
    proof -
      obtain x where "a \<le> x" "x \<le> b" "y = g x"
        using 1 y by force
      then show ?thesis
        by (auto simp: image_def intro!: 1  has_vector_derivative_within_subset [OF derivF])
    qed
  qed
  ultimately show ?thesis by simp
qed

(* TODO: is it possible to lift the assumption here that g' is nonnegative? *)

theorem interval_integral_substitution_integrable:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and a b u v :: ereal
  assumes "a < b"
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real_of_ereal) \<longlongrightarrow> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real_of_ereal) \<longlongrightarrow> B) (at_left b)"
  and integrable: "set_integrable lborel (einterval a b) (\<lambda>x. g' x *\<^sub>R f (g x))"
  and integrable2: "set_integrable lborel (einterval A B) (\<lambda>x. f x)"
  shows "(LBINT x=A..B. f x) = (LBINT x=a..b. g' x *\<^sub>R f (g x))"
proof -
  obtain u l where approx [simp]:
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b" 
    by (blast intro: einterval_Icc_approximation[OF \<open>a < b\<close>])
  note less_imp_le [simp]
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  then have lessb[simp]: "\<And>i. l i < b"
    using approx(4) less_eq_real_def by blast
  have [simp]: "\<And>i. a < u i"
    by (rule order_less_trans, rule approx, auto, rule approx)
  have lle[simp]: "\<And>i j. i \<le> j \<Longrightarrow> l j \<le> l i" by (rule decseqD, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> u i \<le> u j" by (rule incseqD, rule approx)
  have g_nondec [simp]: "g x \<le> g y" if "a < x" "x \<le> y" "y < b" for x y
  proof (rule DERIV_nonneg_imp_nondecreasing [OF \<open>x \<le> y\<close>], intro exI conjI)
    show "\<And>u. x \<le> u \<Longrightarrow> u \<le> y \<Longrightarrow> (g has_real_derivative g' u) (at u)"
      by (meson deriv_g ereal_less_eq(3) le_less_trans less_le_trans that)
    show "\<And>u. x \<le> u \<Longrightarrow> u \<le> y \<Longrightarrow> 0 \<le> g' u"
      by (meson assms(5) dual_order.trans le_ereal_le less_imp_le order_refl that)
  qed
  have "A \<le> B" and un: "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
  proof -
    have A2: "(\<lambda>i. g (l i)) \<longlonglongrightarrow> A"
      using A apply (auto simp: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<ge> A"
      by (intro decseq_ge, auto simp: decseq_def)
    have B2: "(\<lambda>i. g (u i)) \<longlonglongrightarrow> B"
      using B apply (auto simp: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<le> B"
      by (intro incseq_le, auto simp: incseq_def)
    have "ereal (g (l 0)) \<le> ereal (g (u 0))"
      by auto
    then show "A \<le> B"
      by (meson A3 B3 order.trans)
    { fix x :: real
      assume "A < x" and "x < B"
      then have "eventually (\<lambda>i. ereal (g (l i)) < x \<and> x < ereal (g (u i))) sequentially"
        by (fast intro: eventually_conj order_tendstoD A2 B2)
      hence "\<exists>i. g (l i) < x \<and> x < g (u i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
    proof
      show "einterval A B \<subseteq> (\<Union>i. {g(l i)<..<g(u i)})"
        by (auto simp: einterval_def AB)
      show "(\<Union>i. {g(l i)<..<g(u i)}) \<subseteq> einterval A B"
      proof (clarsimp simp add: einterval_def, intro conjI)
        show "\<And>x i. \<lbrakk>g (l i) < x; x < g (u i)\<rbrakk> \<Longrightarrow> A < ereal x"
          using A3 le_ereal_less by blast
        show "\<And>x i. \<lbrakk>g (l i) < x; x < g (u i)\<rbrakk> \<Longrightarrow> ereal x < B"
          using B3 ereal_le_less by blast
      qed
    qed
  qed
  (* finally, the main argument *)
  have eq1: "(LBINT x=l i.. u i. g' x *\<^sub>R f (g x)) = (LBINT y=g (l i)..g (u i). f y)" for i
    apply (rule interval_integral_substitution_finite [OF _ DERIV_subset [OF deriv_g]])
    unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
         apply (auto intro!: continuous_at_imp_continuous_on contf contg')
    done
  have "(\<lambda>i. LBINT x=l i..u i. g' x *\<^sub>R f (g x)) \<longlonglongrightarrow> (LBINT x=a..b. g' x *\<^sub>R f (g x))"
    apply (rule interval_integral_Icc_approx_integrable [OF \<open>a < b\<close> approx])
    by (rule assms)
  hence 2: "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) \<longlonglongrightarrow> (LBINT x=a..b. g' x *\<^sub>R f (g x))"
    by (simp add: eq1)
  have incseq: "incseq (\<lambda>i. {g (l i)<..<g (u i)})"
    apply (auto simp: incseq_def)
    using lessb lle approx(5) g_nondec le_less_trans apply blast
    by (force intro: less_le_trans)
  have "(\<lambda>i. set_lebesgue_integral lborel {g (l i)<..<g (u i)} f)
        \<longlonglongrightarrow> set_lebesgue_integral lborel (einterval A B) f"
    unfolding un  by (rule set_integral_cont_up) (use incseq  integrable2 un in auto)
  then have "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) \<longlonglongrightarrow> (LBINT x = A..B. f x)"
    by (simp add: interval_lebesgue_integral_le_eq \<open>A \<le> B\<close>)
  thus ?thesis by (intro LIMSEQ_unique [OF _ 2])
qed

(* TODO: the last two proofs are only slightly different. Factor out common part?
   An alternative: make the second one the main one, and then have another lemma
   that says that if f is nonnegative and all the other hypotheses hold, then it is integrable. *)

theorem interval_integral_substitution_nonneg:
  fixes f g g':: "real \<Rightarrow> real" and a b u v :: ereal
  assumes "a < b"
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and f_nonneg: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> 0 \<le> f (g x)" (* TODO: make this AE? *)
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real_of_ereal) \<longlongrightarrow> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real_of_ereal) \<longlongrightarrow> B) (at_left b)"
  and integrable_fg: "set_integrable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)"
  shows
    "set_integrable lborel (einterval A B) f"
    "(LBINT x=A..B. f x) = (LBINT x=a..b. (f (g x) * g' x))"
proof -
  from einterval_Icc_approximation[OF \<open>a < b\<close>] guess u l . note approx [simp] = this
  note less_imp_le [simp]
  have aless[simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have lessb[simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have llb[simp]: "\<And>i. l i < b"
    using lessb approx(4) less_eq_real_def by blast
  have alu[simp]: "\<And>i. a < u i"
    by (rule order_less_trans, rule approx, auto, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> l j \<le> l i" by (rule decseqD, rule approx)
  have uleu[simp]: "\<And>i j. i \<le> j \<Longrightarrow> u i \<le> u j" by (rule incseqD, rule approx)
  have g_nondec [simp]: "g x \<le> g y" if "a < x" "x \<le> y" "y < b" for x y
  proof (rule DERIV_nonneg_imp_nondecreasing [OF \<open>x \<le> y\<close>], intro exI conjI)
    show "\<And>u. x \<le> u \<Longrightarrow> u \<le> y \<Longrightarrow> (g has_real_derivative g' u) (at u)"
      by (meson deriv_g ereal_less_eq(3) le_less_trans less_le_trans that)
    show "\<And>u. x \<le> u \<Longrightarrow> u \<le> y \<Longrightarrow> 0 \<le> g' u"
      by (meson g'_nonneg less_ereal.simps(1) less_trans not_less that)
  qed
  have "A \<le> B" and un: "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
  proof -
    have A2: "(\<lambda>i. g (l i)) \<longlonglongrightarrow> A"
      using A apply (auto simp: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<ge> A"
      by (intro decseq_ge, auto simp: decseq_def)
    have B2: "(\<lambda>i. g (u i)) \<longlonglongrightarrow> B"
      using B apply (auto simp: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<le> B"
      by (intro incseq_le, auto simp: incseq_def)
    have "ereal (g (l 0)) \<le> ereal (g (u 0))"
      by auto
    then show "A \<le> B"
      by (meson A3 B3 order.trans)
    { fix x :: real
      assume "A < x" and "x < B"
      then have "eventually (\<lambda>i. ereal (g (l i)) < x \<and> x < ereal (g (u i))) sequentially"
        by (fast intro: eventually_conj order_tendstoD A2 B2)
      hence "\<exists>i. g (l i) < x \<and> x < g (u i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
    proof
      show "einterval A B \<subseteq> (\<Union>i. {g (l i)<..<g (u i)})"
        by (auto simp: einterval_def AB)
      show "(\<Union>i. {g (l i)<..<g (u i)}) \<subseteq> einterval A B"
        apply (clarsimp simp: einterval_def, intro conjI)
        using A3 le_ereal_less apply blast
        using B3 ereal_le_less by blast
    qed
  qed
    (* finally, the main argument *)
  have eq1: "(LBINT x=l i.. u i. (f (g x) * g' x)) = (LBINT y=g (l i)..g (u i). f y)" for i
  proof -
    have "(LBINT x=l i.. u i. g' x *\<^sub>R f (g x)) = (LBINT y=g (l i)..g (u i). f y)"
      apply (rule interval_integral_substitution_finite [OF _ DERIV_subset [OF deriv_g]])
      unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
           apply (auto intro!: continuous_at_imp_continuous_on contf contg')
      done
    then show ?thesis
      by (simp add: ac_simps)
  qed
  have incseq: "incseq (\<lambda>i. {g (l i)<..<g (u i)})"
    apply (clarsimp simp add: incseq_def, intro conjI)
    apply (meson llb antimono_def approx(3) approx(5) g_nondec le_less_trans)
    using alu uleu approx(6) g_nondec less_le_trans by blast
  have img: "\<exists>c \<ge> l i. c \<le> u i \<and> x = g c" if "g (l i) \<le> x" "x \<le> g (u i)" for x i
  proof -
    have "continuous_on {l i..u i} g"
      by (force intro!: DERIV_isCont deriv_g continuous_at_imp_continuous_on)
    with that show ?thesis
      using IVT' [of g] approx(4) dual_order.strict_implies_order by blast
  qed
  have "continuous_on {g (l i)..g (u i)} f" for i
    apply (intro continuous_intros continuous_at_imp_continuous_on)
    using contf img by force
  then have int_f: "\<And>i. set_integrable lborel {g (l i)<..<g (u i)} f"
    by (rule set_integrable_subset [OF borel_integrable_atLeastAtMost']) (auto intro: less_imp_le)
  have integrable: "set_integrable lborel (\<Union>i. {g (l i)<..<g (u i)}) f"
  proof (intro pos_integrable_to_top incseq int_f)
    let ?l = "(LBINT x=a..b. f (g x) * g' x)"
    have "(\<lambda>i. LBINT x=l i..u i. f (g x) * g' x) \<longlonglongrightarrow> ?l"
      by (intro assms interval_integral_Icc_approx_integrable [OF \<open>a < b\<close> approx])
    hence "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) \<longlonglongrightarrow> ?l"
      by (simp add: eq1)
    then show "(\<lambda>i. set_lebesgue_integral lborel {g (l i)<..<g (u i)} f) \<longlonglongrightarrow> ?l"
      unfolding interval_lebesgue_integral_def by auto
    have "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> 0 \<le> f x"
      using aless f_nonneg img lessb by blast
    then show "\<And>x i. x \<in> {g (l i)<..<g (u i)} \<Longrightarrow> 0 \<le> f x"
      using less_eq_real_def by auto
  qed (auto simp: greaterThanLessThan_borel)
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


syntax "_complex_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> complex"
  ("(2CLBINT _. _)" [0,60] 60)

translations "CLBINT x. f" == "CONST complex_lebesgue_integral CONST lborel (\<lambda>x. f)"

syntax "_complex_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> complex"
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

proposition interval_integral_norm:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "interval_lebesgue_integrable lborel a b f \<Longrightarrow> a \<le> b \<Longrightarrow>
    norm (LBINT t=a..b. f t) \<le> LBINT t=a..b. norm (f t)"
  using integral_norm_bound[of lborel "\<lambda>x. indicator (einterval a b) x *\<^sub>R f x"]
  by (auto simp: interval_lebesgue_integral_def interval_lebesgue_integrable_def set_lebesgue_integral_def)

proposition interval_integral_norm2:
  "interval_lebesgue_integrable lborel a b f \<Longrightarrow>
    norm (LBINT t=a..b. f t) \<le> \<bar>LBINT t=a..b. norm (f t)\<bar>"
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (simp add: interval_integral_endpoints_reverse[of a b] interval_integrable_endpoints_reverse[of a b])
next
  case (le a b)
  then have "\<bar>LBINT t=a..b. norm (f t)\<bar> = LBINT t=a..b. norm (f t)"
    using integrable_norm[of lborel "\<lambda>x. indicator (einterval a b) x *\<^sub>R f x"]
    by (auto simp: interval_lebesgue_integral_def interval_lebesgue_integrable_def set_lebesgue_integral_def
             intro!: integral_nonneg_AE abs_of_nonneg)
  then show ?case
    using le by (simp add: interval_integral_norm)
qed

(* TODO: should we have a library of facts like these? *)
lemma integral_cos: "t \<noteq> 0 \<Longrightarrow> LBINT x=a..b. cos (t * x) = sin (t * b) / t - sin (t * a) / t"
  apply (intro interval_integral_FTC_finite continuous_intros)
  by (auto intro!: derivative_eq_intros simp: has_field_derivative_iff_has_vector_derivative[symmetric])

end
