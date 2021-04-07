(*  Title:      HOL/Analysis/Nonnegative_Lebesgue_Integration.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section \<open>Lebesgue Integration for Nonnegative Functions\<close>

theory Nonnegative_Lebesgue_Integration
  imports Measure_Space Borel_Space
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Approximating functions\<close>

lemma AE_upper_bound_inf_ennreal:
  fixes F G::"'a \<Rightarrow> ennreal"
  assumes "\<And>e. (e::real) > 0 \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. \<forall>n::nat. F x \<le> G x + ennreal (1 / Suc n)"
    using assms by (auto simp: AE_all_countable)
  then show ?thesis
  proof (eventually_elim)
    fix x assume x: "\<forall>n::nat. F x \<le> G x + ennreal (1 / Suc n)"
    show "F x \<le> G x"
    proof (rule ennreal_le_epsilon)
      fix e :: real assume "0 < e"
      then obtain n where n: "1 / Suc n < e"
        by (blast elim: nat_approx_posE)
      have "F x \<le> G x + 1 / Suc n"
        using x by simp
      also have "\<dots> \<le> G x + e"
        using n by (intro add_mono ennreal_leI) auto
      finally show "F x \<le> G x + ennreal e" .
    qed
  qed
qed

lemma AE_upper_bound_inf:
  fixes F G::"'a \<Rightarrow> real"
  assumes "\<And>e. e > 0 \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. F x \<le> G x + 1/real (n+1)" for n::nat
    by (rule assms, auto)
  then have "AE x in M. \<forall>n::nat \<in> UNIV. F x \<le> G x + 1/real (n+1)"
    by (rule AE_ball_countable', auto)
  moreover
  {
    fix x assume i: "\<forall>n::nat \<in> UNIV. F x \<le> G x + 1/real (n+1)"
    have "(\<lambda>n. G x + 1/real (n+1)) \<longlonglongrightarrow> G x + 0"
      by (rule tendsto_add, simp, rule LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1])
    then have "F x \<le> G x" using i LIMSEQ_le_const by fastforce
  }
  ultimately show ?thesis by auto
qed

lemma not_AE_zero_ennreal_E:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes "\<not> (AE x in M. f x = 0)" and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>A\<in>sets M. \<exists>e::real>0. emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof -
  { assume "\<not> (\<exists>e::real>0. {x \<in> space M. f x \<ge> e} \<notin> null_sets M)"
    then have "0 < e \<Longrightarrow> AE x in M. f x \<le> e" for e :: real
      by (auto simp: not_le less_imp_le dest!: AE_not_in)
    then have "AE x in M. f x \<le> 0"
      by (intro AE_upper_bound_inf_ennreal[where G="\<lambda>_. 0"]) simp
    then have False
      using assms by auto }
  then obtain e::real where e: "e > 0" "{x \<in> space M. f x \<ge> e} \<notin> null_sets M" by auto
  define A where "A = {x \<in> space M. f x \<ge> e}"
  have 1 [measurable]: "A \<in> sets M" unfolding A_def by auto
  have 2: "emeasure M A > 0"
    using e(2) A_def \<open>A \<in> sets M\<close> by auto
  have 3: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> e" unfolding A_def by auto
  show ?thesis using e(1) 1 2 3 by blast
qed

lemma not_AE_zero_E:
  fixes f::"'a \<Rightarrow> real"
  assumes "AE x in M. f x \<ge> 0"
          "\<not>(AE x in M. f x = 0)"
      and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>A e. A \<in> sets M \<and> e>0 \<and> emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof -
  have "\<exists>e. e > 0 \<and> {x \<in> space M. f x \<ge> e} \<notin> null_sets M"
  proof (rule ccontr)
    assume *: "\<not>(\<exists>e. e > 0 \<and> {x \<in> space M. f x \<ge> e} \<notin> null_sets M)"
    {
      fix e::real assume "e > 0"
      then have "{x \<in> space M. f x \<ge> e} \<in> null_sets M" using * by blast
      then have "AE x in M. x \<notin> {x \<in> space M. f x \<ge> e}" using AE_not_in by blast
      then have "AE x in M. f x \<le> e" by auto
    }
    then have "AE x in M. f x \<le> 0" by (rule AE_upper_bound_inf, auto)
    then have "AE x in M. f x = 0" using assms(1) by auto
    then show False using assms(2) by auto
  qed
  then obtain e where e: "e>0" "{x \<in> space M. f x \<ge> e} \<notin> null_sets M" by auto
  define A where "A = {x \<in> space M. f x \<ge> e}"
  have 1 [measurable]: "A \<in> sets M" unfolding A_def by auto
  have 2: "emeasure M A > 0"
    using e(2) A_def \<open>A \<in> sets M\<close> by auto
  have 3: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> e" unfolding A_def by auto
  show ?thesis
    using e(1) 1 2 3 by blast
qed

subsection "Simple function"

text \<open>

Our simple functions are not restricted to nonnegative real numbers. Instead
they are just functions with a finite range and are measurable when singleton
sets are measurable.

\<close>

definition\<^marker>\<open>tag important\<close> "simple_function M g \<longleftrightarrow>
    finite (g ` space M) \<and>
    (\<forall>x \<in> g ` space M. g -` {x} \<inter> space M \<in> sets M)"

lemma simple_functionD:
  assumes "simple_function M g"
  shows "finite (g ` space M)" and "g -` X \<inter> space M \<in> sets M"
proof -
  show "finite (g ` space M)"
    using assms unfolding simple_function_def by auto
  have "g -` X \<inter> space M = g -` (X \<inter> g`space M) \<inter> space M" by auto
  also have "\<dots> = (\<Union>x\<in>X \<inter> g`space M. g-`{x} \<inter> space M)" by auto
  finally show "g -` X \<inter> space M \<in> sets M" using assms
    by (auto simp del: UN_simps simp: simple_function_def)
qed

lemma measurable_simple_function[measurable_dest]:
  "simple_function M f \<Longrightarrow> f \<in> measurable M (count_space UNIV)"
  unfolding simple_function_def measurable_def
proof safe
  fix A assume "finite (f ` space M)" "\<forall>x\<in>f ` space M. f -` {x} \<inter> space M \<in> sets M"
  then have "(\<Union>x\<in>f ` space M. if x \<in> A then f -` {x} \<inter> space M else {}) \<in> sets M"
    by (intro sets.finite_UN) auto
  also have "(\<Union>x\<in>f ` space M. if x \<in> A then f -` {x} \<inter> space M else {}) = f -` A \<inter> space M"
    by (auto split: if_split_asm)
  finally show "f -` A \<inter> space M \<in> sets M" .
qed simp

lemma borel_measurable_simple_function:
  "simple_function M f \<Longrightarrow> f \<in> borel_measurable M"
  by (auto dest!: measurable_simple_function simp: measurable_def)

lemma simple_function_measurable2[intro]:
  assumes "simple_function M f" "simple_function M g"
  shows "f -` A \<inter> g -` B \<inter> space M \<in> sets M"
proof -
  have "f -` A \<inter> g -` B \<inter> space M = (f -` A \<inter> space M) \<inter> (g -` B \<inter> space M)"
    by auto
  then show ?thesis using assms[THEN simple_functionD(2)] by auto
qed

lemma simple_function_indicator_representation:
  fixes f ::"'a \<Rightarrow> ennreal"
  assumes f: "simple_function M f" and x: "x \<in> space M"
  shows "f x = (\<Sum>y \<in> f ` space M. y * indicator (f -` {y} \<inter> space M) x)"
  (is "?l = ?r")
proof -
  have "?r = (\<Sum>y \<in> f ` space M.
    (if y = f x then y * indicator (f -` {y} \<inter> space M) x else 0))"
    by (auto intro!: sum.cong)
  also have "... =  f x *  indicator (f -` {f x} \<inter> space M) x"
    using assms by (auto dest: simple_functionD)
  also have "... = f x" using x by (auto simp: indicator_def)
  finally show ?thesis by auto
qed

lemma simple_function_notspace:
  "simple_function M (\<lambda>x. h x * indicator (- space M) x::ennreal)" (is "simple_function M ?h")
proof -
  have "?h ` space M \<subseteq> {0}" unfolding indicator_def by auto
  hence [simp, intro]: "finite (?h ` space M)" by (auto intro: finite_subset)
  have "?h -` {0} \<inter> space M = space M" by auto
  thus ?thesis unfolding simple_function_def by (auto simp add: image_constant_conv)
qed

lemma simple_function_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "simple_function M f \<longleftrightarrow> simple_function M g"
proof -
  have "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by auto
  with assms show ?thesis
    by (simp add: simple_function_def cong: image_cong)
qed

lemma simple_function_cong_algebra:
  assumes "sets N = sets M" "space N = space M"
  shows "simple_function M f \<longleftrightarrow> simple_function N f"
  unfolding simple_function_def assms ..

lemma simple_function_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::{t2_space}"
  assumes "f \<in> borel_measurable M" and "finite (f ` space M)"
  shows "simple_function M f"
  using assms unfolding simple_function_def
  by (auto intro: borel_measurable_vimage)

lemma simple_function_iff_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::{t2_space}"
  shows "simple_function M f \<longleftrightarrow> finite (f ` space M) \<and> f \<in> borel_measurable M"
  by (metis borel_measurable_simple_function simple_functionD(1) simple_function_borel_measurable)

lemma simple_function_eq_measurable:
  "simple_function M f \<longleftrightarrow> finite (f`space M) \<and> f \<in> measurable M (count_space UNIV)"
  using measurable_simple_function[of M f] by (fastforce simp: simple_function_def)

lemma simple_function_const[intro, simp]:
  "simple_function M (\<lambda>x. c)"
  by (auto intro: finite_subset simp: simple_function_def)
lemma simple_function_compose[intro, simp]:
  assumes "simple_function M f"
  shows "simple_function M (g \<circ> f)"
  unfolding simple_function_def
proof safe
  show "finite ((g \<circ> f) ` space M)"
    using assms unfolding simple_function_def image_comp [symmetric] by auto
next
  fix x assume "x \<in> space M"
  let ?G = "g -` {g (f x)} \<inter> (f`space M)"
  have *: "(g \<circ> f) -` {(g \<circ> f) x} \<inter> space M =
    (\<Union>x\<in>?G. f -` {x} \<inter> space M)" by auto
  show "(g \<circ> f) -` {(g \<circ> f) x} \<inter> space M \<in> sets M"
    using assms unfolding simple_function_def *
    by (rule_tac sets.finite_UN) auto
qed

lemma simple_function_indicator[intro, simp]:
  assumes "A \<in> sets M"
  shows "simple_function M (indicator A)"
proof -
  have "indicator A ` space M \<subseteq> {0, 1}" (is "?S \<subseteq> _")
    by (auto simp: indicator_def)
  hence "finite ?S" by (rule finite_subset) simp
  moreover have "- A \<inter> space M = space M - A" by auto
  ultimately show ?thesis unfolding simple_function_def
    using assms by (auto simp: indicator_def [abs_def])
qed

lemma simple_function_Pair[intro, simp]:
  assumes "simple_function M f"
  assumes "simple_function M g"
  shows "simple_function M (\<lambda>x. (f x, g x))" (is "simple_function M ?p")
  unfolding simple_function_def
proof safe
  show "finite (?p ` space M)"
    using assms unfolding simple_function_def
    by (rule_tac finite_subset[of _ "f`space M \<times> g`space M"]) auto
next
  fix x assume "x \<in> space M"
  have "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M =
      (f -` {f x} \<inter> space M) \<inter> (g -` {g x} \<inter> space M)"
    by auto
  with \<open>x \<in> space M\<close> show "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M \<in> sets M"
    using assms unfolding simple_function_def by auto
qed

lemma simple_function_compose1:
  assumes "simple_function M f"
  shows "simple_function M (\<lambda>x. g (f x))"
  using simple_function_compose[OF assms, of g]
  by (simp add: comp_def)

lemma simple_function_compose2:
  assumes "simple_function M f" and "simple_function M g"
  shows "simple_function M (\<lambda>x. h (f x) (g x))"
proof -
  have "simple_function M ((\<lambda>(x, y). h x y) \<circ> (\<lambda>x. (f x, g x)))"
    using assms by auto
  thus ?thesis by (simp_all add: comp_def)
qed

lemmas simple_function_add[intro, simp] = simple_function_compose2[where h="(+)"]
  and simple_function_diff[intro, simp] = simple_function_compose2[where h="(-)"]
  and simple_function_uminus[intro, simp] = simple_function_compose[where g="uminus"]
  and simple_function_mult[intro, simp] = simple_function_compose2[where h="(*)"]
  and simple_function_div[intro, simp] = simple_function_compose2[where h="(/)"]
  and simple_function_inverse[intro, simp] = simple_function_compose[where g="inverse"]
  and simple_function_max[intro, simp] = simple_function_compose2[where h=max]

lemma simple_function_sum[intro, simp]:
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "simple_function M (\<lambda>x. \<Sum>i\<in>P. f i x)"
proof cases
  assume "finite P" from this assms show ?thesis by induct auto
qed auto

lemma simple_function_ennreal[intro, simp]:
  fixes f g :: "'a \<Rightarrow> real" assumes sf: "simple_function M f"
  shows "simple_function M (\<lambda>x. ennreal (f x))"
  by (rule simple_function_compose1[OF sf])

lemma simple_function_real_of_nat[intro, simp]:
  fixes f g :: "'a \<Rightarrow> nat" assumes sf: "simple_function M f"
  shows "simple_function M (\<lambda>x. real (f x))"
  by (rule simple_function_compose1[OF sf])

lemma\<^marker>\<open>tag important\<close> borel_measurable_implies_simple_function_sequence:
  fixes u :: "'a \<Rightarrow> ennreal"
  assumes u[measurable]: "u \<in> borel_measurable M"
  shows "\<exists>f. incseq f \<and> (\<forall>i. (\<forall>x. f i x < top) \<and> simple_function M (f i)) \<and> u = (SUP i. f i)"
proof -
  define f where [abs_def]:
    "f i x = real_of_int (floor (enn2real (min i (u x)) * 2^i)) / 2^i" for i x

  have [simp]: "0 \<le> f i x" for i x
    by (auto simp: f_def intro!: divide_nonneg_nonneg mult_nonneg_nonneg enn2real_nonneg)

  have *: "2^n * real_of_int x = real_of_int (2^n * x)" for n x
    by simp

  have "real_of_int \<lfloor>real i * 2 ^ i\<rfloor> = real_of_int \<lfloor>i * 2 ^ i\<rfloor>" for i
    by (intro arg_cong[where f=real_of_int]) simp
  then have [simp]: "real_of_int \<lfloor>real i * 2 ^ i\<rfloor> = i * 2 ^ i" for i
    unfolding floor_of_nat by simp

  have "incseq f"
  proof (intro monoI le_funI)
    fix m n :: nat and x assume "m \<le> n"
    moreover
    { fix d :: nat
      have "\<lfloor>2^d::real\<rfloor> * \<lfloor>2^m * enn2real (min (of_nat m) (u x))\<rfloor> \<le>
        \<lfloor>2^d * (2^m * enn2real (min (of_nat m) (u x)))\<rfloor>"
        by (rule le_mult_floor) (auto)
      also have "\<dots> \<le> \<lfloor>2^d * (2^m * enn2real (min (of_nat d + of_nat m) (u x)))\<rfloor>"
        by (intro floor_mono mult_mono enn2real_mono min.mono)
           (auto simp: min_less_iff_disj of_nat_less_top)
      finally have "f m x \<le> f (m + d) x"
        unfolding f_def
        by (auto simp: field_simps power_add * simp del: of_int_mult) }
    ultimately show "f m x \<le> f n x"
      by (auto simp add: le_iff_add)
  qed
  then have inc_f: "incseq (\<lambda>i. ennreal (f i x))" for x
    by (auto simp: incseq_def le_fun_def)
  then have "incseq (\<lambda>i x. ennreal (f i x))"
    by (auto simp: incseq_def le_fun_def)
  moreover
  have "simple_function M (f i)" for i
  proof (rule simple_function_borel_measurable)
    have "\<lfloor>enn2real (min (of_nat i) (u x)) * 2 ^ i\<rfloor> \<le> \<lfloor>int i * 2 ^ i\<rfloor>" for x
      by (cases "u x" rule: ennreal_cases)
         (auto split: split_min intro!: floor_mono)
    then have "f i ` space M \<subseteq> (\<lambda>n. real_of_int n / 2^i) ` {0 .. of_nat i * 2^i}"
      unfolding floor_of_int by (auto simp: f_def intro!: imageI)
    then show "finite (f i ` space M)"
      by (rule finite_subset) auto
    show "f i \<in> borel_measurable M"
      unfolding f_def enn2real_def by measurable
  qed
  moreover
  { fix x
    have "(SUP i. ennreal (f i x)) = u x"
    proof (cases "u x" rule: ennreal_cases)
      case top then show ?thesis
        by (simp add: f_def inf_min[symmetric] ennreal_of_nat_eq_real_of_nat[symmetric]
                      ennreal_SUP_of_nat_eq_top)
    next
      case (real r)
      obtain n where "r \<le> of_nat n" using real_arch_simple by auto
      then have min_eq_r: "\<forall>\<^sub>F x in sequentially. min (real x) r = r"
        by (auto simp: eventually_sequentially intro!: exI[of _ n] split: split_min)

      have "(\<lambda>i. real_of_int \<lfloor>min (real i) r * 2^i\<rfloor> / 2^i) \<longlonglongrightarrow> r"
      proof (rule tendsto_sandwich)
        show "(\<lambda>n. r - (1/2)^n) \<longlonglongrightarrow> r"
          by (auto intro!: tendsto_eq_intros LIMSEQ_power_zero)
        show "\<forall>\<^sub>F n in sequentially. real_of_int \<lfloor>min (real n) r * 2 ^ n\<rfloor> / 2 ^ n \<le> r"
          using min_eq_r by eventually_elim (auto simp: field_simps)
        have *: "r * (2 ^ n * 2 ^ n) \<le> 2^n + 2^n * real_of_int \<lfloor>r * 2 ^ n\<rfloor>" for n
          using real_of_int_floor_ge_diff_one[of "r * 2^n", THEN mult_left_mono, of "2^n"]
          by (auto simp: field_simps)
        show "\<forall>\<^sub>F n in sequentially. r - (1/2)^n \<le> real_of_int \<lfloor>min (real n) r * 2 ^ n\<rfloor> / 2 ^ n"
          using min_eq_r by eventually_elim (insert *, auto simp: field_simps)
      qed auto
      then have "(\<lambda>i. ennreal (f i x)) \<longlonglongrightarrow> ennreal r"
        by (simp add: real f_def ennreal_of_nat_eq_real_of_nat min_ennreal)
      from LIMSEQ_unique[OF LIMSEQ_SUP[OF inc_f] this]
      show ?thesis
        by (simp add: real)
    qed }
  ultimately show ?thesis
    by (intro exI [of _ "\<lambda>i x. ennreal (f i x)"]) (auto simp add: image_comp)
qed

lemma borel_measurable_implies_simple_function_sequence':
  fixes u :: "'a \<Rightarrow> ennreal"
  assumes u: "u \<in> borel_measurable M"
  obtains f where
    "\<And>i. simple_function M (f i)" "incseq f" "\<And>i x. f i x < top" "\<And>x. (SUP i. f i x) = u x"
  using borel_measurable_implies_simple_function_sequence [OF u]
  by (metis SUP_apply)

lemma\<^marker>\<open>tag important\<close> simple_function_induct
    [consumes 1, case_names cong set mult add, induct set: simple_function]:
  fixes u :: "'a \<Rightarrow> ennreal"
  assumes u: "simple_function M u"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> simple_function M g \<Longrightarrow> (AE x in M. f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult: "\<And>u c. P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. P u \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  shows "P u"
proof (rule cong)
  from AE_space show "AE x in M. (\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x) = u x"
  proof eventually_elim
    fix x assume x: "x \<in> space M"
    from simple_function_indicator_representation[OF u x]
    show "(\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x) = u x" ..
  qed
next
  from u have "finite (u ` space M)"
    unfolding simple_function_def by auto
  then show "P (\<lambda>x. \<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x)"
  proof induct
    case empty show ?case
      using set[of "{}"] by (simp add: indicator_def[abs_def])
  qed (auto intro!: add mult set simple_functionD u)
next
  show "simple_function M (\<lambda>x. (\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x))"
    apply (subst simple_function_cong)
    apply (rule simple_function_indicator_representation[symmetric])
    apply (auto intro: u)
    done
qed fact

lemma simple_function_induct_nn[consumes 1, case_names cong set mult add]:
  fixes u :: "'a \<Rightarrow> ennreal"
  assumes u: "simple_function M u"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> simple_function M g \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult: "\<And>u c. simple_function M u \<Longrightarrow> P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. simple_function M u \<Longrightarrow> P u \<Longrightarrow> simple_function M v \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x = 0 \<or> v x = 0) \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  shows "P u"
proof -
  show ?thesis
  proof (rule cong)
    fix x assume x: "x \<in> space M"
    from simple_function_indicator_representation[OF u x]
    show "(\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x) = u x" ..
  next
    show "simple_function M (\<lambda>x. (\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x))"
      apply (subst simple_function_cong)
      apply (rule simple_function_indicator_representation[symmetric])
      apply (auto intro: u)
      done
  next
    from u have "finite (u ` space M)"
      unfolding simple_function_def by auto
    then show "P (\<lambda>x. \<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x)"
    proof induct
      case empty show ?case
        using set[of "{}"] by (simp add: indicator_def[abs_def])
    next
      case (insert x S)
      { fix z have "(\<Sum>y\<in>S. y * indicator (u -` {y} \<inter> space M) z) = 0 \<or>
          x * indicator (u -` {x} \<inter> space M) z = 0"
          using insert by (subst sum_eq_0_iff) (auto simp: indicator_def) }
      note disj = this
      from insert show ?case
        by (auto intro!: add mult set simple_functionD u simple_function_sum disj)
    qed
  qed fact
qed

lemma\<^marker>\<open>tag important\<close> borel_measurable_induct
    [consumes 1, case_names cong set mult add seq, induct set: borel_measurable]:
  fixes u :: "'a \<Rightarrow> ennreal"
  assumes u: "u \<in> borel_measurable M"
  assumes cong: "\<And>f g. f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P g \<Longrightarrow> P f"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult': "\<And>u c. c < top \<Longrightarrow> u \<in> borel_measurable M \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x < top) \<Longrightarrow> P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. u \<in> borel_measurable M\<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x < top) \<Longrightarrow> P u \<Longrightarrow> v \<in> borel_measurable M \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> v x < top) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x = 0 \<or> v x = 0) \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  assumes seq: "\<And>U. (\<And>i. U i \<in> borel_measurable M) \<Longrightarrow> (\<And>i x. x \<in> space M \<Longrightarrow> U i x < top) \<Longrightarrow> (\<And>i. P (U i)) \<Longrightarrow> incseq U \<Longrightarrow> u = (SUP i. U i) \<Longrightarrow> P (SUP i. U i)"
  shows "P u"
  using u
proof (induct rule: borel_measurable_implies_simple_function_sequence')
  fix U assume U: "\<And>i. simple_function M (U i)" "incseq U" "\<And>i x. U i x < top" and sup: "\<And>x. (SUP i. U i x) = u x"
  have u_eq: "u = (SUP i. U i)"
    using u by (auto simp add: image_comp sup)

  have not_inf: "\<And>x i. x \<in> space M \<Longrightarrow> U i x < top"
    using U by (auto simp: image_iff eq_commute)

  from U have "\<And>i. U i \<in> borel_measurable M"
    by (simp add: borel_measurable_simple_function)

  show "P u"
    unfolding u_eq
  proof (rule seq)
    fix i show "P (U i)"
      using \<open>simple_function M (U i)\<close> not_inf[of _ i]
    proof (induct rule: simple_function_induct_nn)
      case (mult u c)
      show ?case
      proof cases
        assume "c = 0 \<or> space M = {} \<or> (\<forall>x\<in>space M. u x = 0)"
        with mult(1) show ?thesis
          by (intro cong[of "\<lambda>x. c * u x" "indicator {}"] set)
             (auto dest!: borel_measurable_simple_function)
      next
        assume "\<not> (c = 0 \<or> space M = {} \<or> (\<forall>x\<in>space M. u x = 0))"
        then obtain x where "space M \<noteq> {}" and x: "x \<in> space M" "u x \<noteq> 0" "c \<noteq> 0"
          by auto
        with mult(3)[of x] have "c < top"
          by (auto simp: ennreal_mult_less_top)
        then have u_fin: "x' \<in> space M \<Longrightarrow> u x' < top" for x'
          using mult(3)[of x'] \<open>c \<noteq> 0\<close> by (auto simp: ennreal_mult_less_top)
        then have "P u"
          by (rule mult)
        with u_fin \<open>c < top\<close> mult(1) show ?thesis
          by (intro mult') (auto dest!: borel_measurable_simple_function)
      qed
    qed (auto intro: cong intro!: set add dest!: borel_measurable_simple_function)
  qed fact+
qed

lemma simple_function_If_set:
  assumes sf: "simple_function M f" "simple_function M g" and A: "A \<inter> space M \<in> sets M"
  shows "simple_function M (\<lambda>x. if x \<in> A then f x else g x)" (is "simple_function M ?IF")
proof -
  define F where "F x = f -` {x} \<inter> space M" for x
  define G where "G x = g -` {x} \<inter> space M" for x
  show ?thesis unfolding simple_function_def
  proof safe
    have "?IF ` space M \<subseteq> f ` space M \<union> g ` space M" by auto
    from finite_subset[OF this] assms
    show "finite (?IF ` space M)" unfolding simple_function_def by auto
  next
    fix x assume "x \<in> space M"
    then have *: "?IF -` {?IF x} \<inter> space M = (if x \<in> A
      then ((F (f x) \<inter> (A \<inter> space M)) \<union> (G (f x) - (G (f x) \<inter> (A \<inter> space M))))
      else ((F (g x) \<inter> (A \<inter> space M)) \<union> (G (g x) - (G (g x) \<inter> (A \<inter> space M)))))"
      using sets.sets_into_space[OF A] by (auto split: if_split_asm simp: G_def F_def)
    have [intro]: "\<And>x. F x \<in> sets M" "\<And>x. G x \<in> sets M"
      unfolding F_def G_def using sf[THEN simple_functionD(2)] by auto
    show "?IF -` {?IF x} \<inter> space M \<in> sets M" unfolding * using A by auto
  qed
qed

lemma simple_function_If:
  assumes sf: "simple_function M f" "simple_function M g" and P: "{x\<in>space M. P x} \<in> sets M"
  shows "simple_function M (\<lambda>x. if P x then f x else g x)"
proof -
  have "{x\<in>space M. P x} = {x. P x} \<inter> space M" by auto
  with simple_function_If_set[OF sf, of "{x. P x}"] P show ?thesis by simp
qed

lemma simple_function_subalgebra:
  assumes "simple_function N f"
  and N_subalgebra: "sets N \<subseteq> sets M" "space N = space M"
  shows "simple_function M f"
  using assms unfolding simple_function_def by auto

lemma simple_function_comp:
  assumes T: "T \<in> measurable M M'"
    and f: "simple_function M' f"
  shows "simple_function M (\<lambda>x. f (T x))"
proof (intro simple_function_def[THEN iffD2] conjI ballI)
  have "(\<lambda>x. f (T x)) ` space M \<subseteq> f ` space M'"
    using T unfolding measurable_def by auto
  then show "finite ((\<lambda>x. f (T x)) ` space M)"
    using f unfolding simple_function_def by (auto intro: finite_subset)
  fix i assume i: "i \<in> (\<lambda>x. f (T x)) ` space M"
  then have "i \<in> f ` space M'"
    using T unfolding measurable_def by auto
  then have "f -` {i} \<inter> space M' \<in> sets M'"
    using f unfolding simple_function_def by auto
  then have "T -` (f -` {i} \<inter> space M') \<inter> space M \<in> sets M"
    using T unfolding measurable_def by auto
  also have "T -` (f -` {i} \<inter> space M') \<inter> space M = (\<lambda>x. f (T x)) -` {i} \<inter> space M"
    using T unfolding measurable_def by auto
  finally show "(\<lambda>x. f (T x)) -` {i} \<inter> space M \<in> sets M" .
qed

subsection "Simple integral"

definition\<^marker>\<open>tag important\<close> simple_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ennreal" ("integral\<^sup>S") where
  "integral\<^sup>S M f = (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M))"

syntax
  "_simple_integral" :: "pttrn \<Rightarrow> ennreal \<Rightarrow> 'a measure \<Rightarrow> ennreal" ("\<integral>\<^sup>S _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>S x. f \<partial>M" == "CONST simple_integral M (%x. f)"

lemma simple_integral_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "integral\<^sup>S M f = integral\<^sup>S M g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma simple_integral_const[simp]:
  "(\<integral>\<^sup>Sx. c \<partial>M) = c * (emeasure M) (space M)"
proof (cases "space M = {}")
  case True thus ?thesis unfolding simple_integral_def by simp
next
  case False hence "(\<lambda>x. c) ` space M = {c}" by auto
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma simple_function_partition:
  assumes f: "simple_function M f" and g: "simple_function M g"
  assumes sub: "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space M \<Longrightarrow> g x = g y \<Longrightarrow> f x = f y"
  assumes v: "\<And>x. x \<in> space M \<Longrightarrow> f x = v (g x)"
  shows "integral\<^sup>S M f = (\<Sum>y\<in>g ` space M. v y * emeasure M {x\<in>space M. g x = y})"
    (is "_ = ?r")
proof -
  from f g have [simp]: "finite (f`space M)" "finite (g`space M)"
    by (auto simp: simple_function_def)
  from f g have [measurable]: "f \<in> measurable M (count_space UNIV)" "g \<in> measurable M (count_space UNIV)"
    by (auto intro: measurable_simple_function)

  { fix y assume "y \<in> space M"
    then have "f ` space M \<inter> {i. \<exists>x\<in>space M. i = f x \<and> g y = g x} = {v (g y)}"
      by (auto cong: sub simp: v[symmetric]) }
  note eq = this

  have "integral\<^sup>S M f =
    (\<Sum>y\<in>f`space M. y * (\<Sum>z\<in>g`space M.
      if \<exists>x\<in>space M. y = f x \<and> z = g x then emeasure M {x\<in>space M. g x = z} else 0))"
    unfolding simple_integral_def
  proof (safe intro!: sum.cong ennreal_mult_left_cong)
    fix y assume y: "y \<in> space M" "f y \<noteq> 0"
    have [simp]: "g ` space M \<inter> {z. \<exists>x\<in>space M. f y = f x \<and> z = g x} =
        {z. \<exists>x\<in>space M. f y = f x \<and> z = g x}"
      by auto
    have eq:"(\<Union>i\<in>{z. \<exists>x\<in>space M. f y = f x \<and> z = g x}. {x \<in> space M. g x = i}) =
        f -` {f y} \<inter> space M"
      by (auto simp: eq_commute cong: sub rev_conj_cong)
    have "finite (g`space M)" by simp
    then have "finite {z. \<exists>x\<in>space M. f y = f x \<and> z = g x}"
      by (rule rev_finite_subset) auto
    then show "emeasure M (f -` {f y} \<inter> space M) =
      (\<Sum>z\<in>g ` space M. if \<exists>x\<in>space M. f y = f x \<and> z = g x then emeasure M {x \<in> space M. g x = z} else 0)"
      apply (simp add: sum.If_cases)
      apply (subst sum_emeasure)
      apply (auto simp: disjoint_family_on_def eq)
      done
  qed
  also have "\<dots> = (\<Sum>y\<in>f`space M. (\<Sum>z\<in>g`space M.
      if \<exists>x\<in>space M. y = f x \<and> z = g x then y * emeasure M {x\<in>space M. g x = z} else 0))"
    by (auto intro!: sum.cong simp: sum_distrib_left)
  also have "\<dots> = ?r"
    by (subst sum.swap)
       (auto intro!: sum.cong simp: sum.If_cases scaleR_sum_right[symmetric] eq)
  finally show "integral\<^sup>S M f = ?r" .
qed

lemma simple_integral_add[simp]:
  assumes f: "simple_function M f" and "\<And>x. 0 \<le> f x" and g: "simple_function M g" and "\<And>x. 0 \<le> g x"
  shows "(\<integral>\<^sup>Sx. f x + g x \<partial>M) = integral\<^sup>S M f + integral\<^sup>S M g"
proof -
  have "(\<integral>\<^sup>Sx. f x + g x \<partial>M) =
    (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. (fst y + snd y) * emeasure M {x\<in>space M. (f x, g x) = y})"
    by (intro simple_function_partition) (auto intro: f g)
  also have "\<dots> = (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. fst y * emeasure M {x\<in>space M. (f x, g x) = y}) +
    (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. snd y * emeasure M {x\<in>space M. (f x, g x) = y})"
    using assms(2,4) by (auto intro!: sum.cong distrib_right simp: sum.distrib[symmetric])
  also have "(\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. fst y * emeasure M {x\<in>space M. (f x, g x) = y}) = (\<integral>\<^sup>Sx. f x \<partial>M)"
    by (intro simple_function_partition[symmetric]) (auto intro: f g)
  also have "(\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. snd y * emeasure M {x\<in>space M. (f x, g x) = y}) = (\<integral>\<^sup>Sx. g x \<partial>M)"
    by (intro simple_function_partition[symmetric]) (auto intro: f g)
  finally show ?thesis .
qed

lemma simple_integral_sum[simp]:
  assumes "\<And>i x. i \<in> P \<Longrightarrow> 0 \<le> f i x"
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "(\<integral>\<^sup>Sx. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^sup>S M (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
    by induct (auto)
qed auto

lemma simple_integral_mult[simp]:
  assumes f: "simple_function M f"
  shows "(\<integral>\<^sup>Sx. c * f x \<partial>M) = c * integral\<^sup>S M f"
proof -
  have "(\<integral>\<^sup>Sx. c * f x \<partial>M) = (\<Sum>y\<in>f ` space M. (c * y) * emeasure M {x\<in>space M. f x = y})"
    using f by (intro simple_function_partition) auto
  also have "\<dots> = c * integral\<^sup>S M f"
    using f unfolding simple_integral_def
    by (subst sum_distrib_left) (auto simp: mult.assoc Int_def conj_commute)
  finally show ?thesis .
qed

lemma simple_integral_mono_AE:
  assumes f[measurable]: "simple_function M f" and g[measurable]: "simple_function M g"
  and mono: "AE x in M. f x \<le> g x"
  shows "integral\<^sup>S M f \<le> integral\<^sup>S M g"
proof -
  let ?\<mu> = "\<lambda>P. emeasure M {x\<in>space M. P x}"
  have "integral\<^sup>S M f = (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. fst y * ?\<mu> (\<lambda>x. (f x, g x) = y))"
    using f g by (intro simple_function_partition) auto
  also have "\<dots> \<le> (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. snd y * ?\<mu> (\<lambda>x. (f x, g x) = y))"
  proof (clarsimp intro!: sum_mono)
    fix x assume "x \<in> space M"
    let ?M = "?\<mu> (\<lambda>y. f y = f x \<and> g y = g x)"
    show "f x * ?M \<le> g x * ?M"
    proof cases
      assume "?M \<noteq> 0"
      then have "0 < ?M"
        by (simp add: less_le)
      also have "\<dots> \<le> ?\<mu> (\<lambda>y. f x \<le> g x)"
        using mono by (intro emeasure_mono_AE) auto
      finally have "\<not> \<not> f x \<le> g x"
        by (intro notI) auto
      then show ?thesis
        by (intro mult_right_mono) auto
    qed simp
  qed
  also have "\<dots> = integral\<^sup>S M g"
    using f g by (intro simple_function_partition[symmetric]) auto
  finally show ?thesis .
qed

lemma simple_integral_mono:
  assumes "simple_function M f" and "simple_function M g"
  and mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>S M f \<le> integral\<^sup>S M g"
  using assms by (intro simple_integral_mono_AE) auto

lemma simple_integral_cong_AE:
  assumes "simple_function M f" and "simple_function M g"
  and "AE x in M. f x = g x"
  shows "integral\<^sup>S M f = integral\<^sup>S M g"
  using assms by (auto simp: eq_iff intro!: simple_integral_mono_AE)

lemma simple_integral_cong':
  assumes sf: "simple_function M f" "simple_function M g"
  and mea: "(emeasure M) {x\<in>space M. f x \<noteq> g x} = 0"
  shows "integral\<^sup>S M f = integral\<^sup>S M g"
proof (intro simple_integral_cong_AE sf AE_I)
  show "(emeasure M) {x\<in>space M. f x \<noteq> g x} = 0" by fact
  show "{x \<in> space M. f x \<noteq> g x} \<in> sets M"
    using sf[THEN borel_measurable_simple_function] by auto
qed simp

lemma simple_integral_indicator:
  assumes A: "A \<in> sets M"
  assumes f: "simple_function M f"
  shows "(\<integral>\<^sup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M \<inter> A))"
proof -
  have eq: "(\<lambda>x. (f x, indicator A x)) ` space M \<inter> {x. snd x = 1} = (\<lambda>x. (f x, 1::ennreal))`A"
    using A[THEN sets.sets_into_space] by (auto simp: indicator_def image_iff split: if_split_asm)
  have eq2: "\<And>x. f x \<notin> f ` A \<Longrightarrow> f -` {f x} \<inter> space M \<inter> A = {}"
    by (auto simp: image_iff)

  have "(\<integral>\<^sup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>y\<in>(\<lambda>x. (f x, indicator A x))`space M. (fst y * snd y) * emeasure M {x\<in>space M. (f x, indicator A x) = y})"
    using assms by (intro simple_function_partition) auto
  also have "\<dots> = (\<Sum>y\<in>(\<lambda>x. (f x, indicator A x::ennreal))`space M.
    if snd y = 1 then fst y * emeasure M (f -` {fst y} \<inter> space M \<inter> A) else 0)"
    by (auto simp: indicator_def split: if_split_asm intro!: arg_cong2[where f="(*)"] arg_cong2[where f=emeasure] sum.cong)
  also have "\<dots> = (\<Sum>y\<in>(\<lambda>x. (f x, 1::ennreal))`A. fst y * emeasure M (f -` {fst y} \<inter> space M \<inter> A))"
    using assms by (subst sum.If_cases) (auto intro!: simple_functionD(1) simp: eq)
  also have "\<dots> = (\<Sum>y\<in>fst`(\<lambda>x. (f x, 1::ennreal))`A. y * emeasure M (f -` {y} \<inter> space M \<inter> A))"
    by (subst sum.reindex [of fst]) (auto simp: inj_on_def)
  also have "\<dots> = (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M \<inter> A))"
    using A[THEN sets.sets_into_space]
    by (intro sum.mono_neutral_cong_left simple_functionD f) (auto simp: image_comp comp_def eq2)
  finally show ?thesis .
qed

lemma simple_integral_indicator_only[simp]:
  assumes "A \<in> sets M"
  shows "integral\<^sup>S M (indicator A) = emeasure M A"
  using simple_integral_indicator[OF assms, of "\<lambda>x. 1"] sets.sets_into_space[OF assms]
  by (simp_all add: image_constant_conv Int_absorb1 split: if_split_asm)

lemma simple_integral_null_set:
  assumes "simple_function M u" "\<And>x. 0 \<le> u x" and "N \<in> null_sets M"
  shows "(\<integral>\<^sup>Sx. u x * indicator N x \<partial>M) = 0"
proof -
  have "AE x in M. indicator N x = (0 :: ennreal)"
    using \<open>N \<in> null_sets M\<close> by (auto simp: indicator_def intro!: AE_I[of _ _ N])
  then have "(\<integral>\<^sup>Sx. u x * indicator N x \<partial>M) = (\<integral>\<^sup>Sx. 0 \<partial>M)"
    using assms apply (intro simple_integral_cong_AE) by auto
  then show ?thesis by simp
qed

lemma simple_integral_cong_AE_mult_indicator:
  assumes sf: "simple_function M f" and eq: "AE x in M. x \<in> S" and "S \<in> sets M"
  shows "integral\<^sup>S M f = (\<integral>\<^sup>Sx. f x * indicator S x \<partial>M)"
  using assms by (intro simple_integral_cong_AE) auto

lemma simple_integral_cmult_indicator:
  assumes A: "A \<in> sets M"
  shows "(\<integral>\<^sup>Sx. c * indicator A x \<partial>M) = c * emeasure M A"
  using simple_integral_mult[OF simple_function_indicator[OF A]]
  unfolding simple_integral_indicator_only[OF A] by simp

lemma simple_integral_nonneg:
  assumes f: "simple_function M f" and ae: "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^sup>S M f"
proof -
  have "integral\<^sup>S M (\<lambda>x. 0) \<le> integral\<^sup>S M f"
    using simple_integral_mono_AE[OF _ f ae] by auto
  then show ?thesis by simp
qed

subsection \<open>Integral on nonnegative functions\<close>

definition\<^marker>\<open>tag important\<close> nn_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ennreal" ("integral\<^sup>N") where
  "integral\<^sup>N M f = (SUP g \<in> {g. simple_function M g \<and> g \<le> f}. integral\<^sup>S M g)"

syntax
  "_nn_integral" :: "pttrn \<Rightarrow> ennreal \<Rightarrow> 'a measure \<Rightarrow> ennreal" ("\<integral>\<^sup>+((2 _./ _)/ \<partial>_)" [60,61] 110)

translations
  "\<integral>\<^sup>+x. f \<partial>M" == "CONST nn_integral M (\<lambda>x. f)"

lemma nn_integral_def_finite:
  "integral\<^sup>N M f = (SUP g \<in> {g. simple_function M g \<and> g \<le> f \<and> (\<forall>x. g x < top)}. integral\<^sup>S M g)"
    (is "_ = Sup (?A ` ?f)")
  unfolding nn_integral_def
proof (safe intro!: antisym SUP_least)
  fix g assume g[measurable]: "simple_function M g" "g \<le> f"

  show "integral\<^sup>S M g \<le> Sup (?A ` ?f)"
  proof cases
    assume ae: "AE x in M. g x \<noteq> top"
    let ?G = "{x \<in> space M. g x \<noteq> top}"
    have "integral\<^sup>S M g = integral\<^sup>S M (\<lambda>x. g x * indicator ?G x)"
    proof (rule simple_integral_cong_AE)
      show "AE x in M. g x = g x * indicator ?G x"
        using ae AE_space by eventually_elim auto
    qed (insert g, auto)
    also have "\<dots> \<le> Sup (?A ` ?f)"
      using g by (intro SUP_upper) (auto simp: le_fun_def less_top split: split_indicator)
    finally show ?thesis .
  next
    assume nAE: "\<not> (AE x in M. g x \<noteq> top)"
    then have "emeasure M {x\<in>space M. g x = top} \<noteq> 0" (is "emeasure M ?G \<noteq> 0")
      by (subst (asm) AE_iff_measurable[OF _ refl]) auto
    then have "top = (SUP n. (\<integral>\<^sup>Sx. of_nat n * indicator ?G x \<partial>M))"
      by (simp add: ennreal_SUP_of_nat_eq_top ennreal_top_eq_mult_iff SUP_mult_right_ennreal[symmetric])
    also have "\<dots> \<le> Sup (?A ` ?f)"
      using g
      by (safe intro!: SUP_least SUP_upper)
         (auto simp: le_fun_def of_nat_less_top top_unique[symmetric] split: split_indicator
               intro: order_trans[of _ "g x" "f x" for x, OF order_trans[of _ top]])
    finally show ?thesis
      by (simp add: top_unique del: SUP_eq_top_iff Sup_eq_top_iff)
  qed
qed (auto intro: SUP_upper)

lemma nn_integral_mono_AE:
  assumes ae: "AE x in M. u x \<le> v x" shows "integral\<^sup>N M u \<le> integral\<^sup>N M v"
  unfolding nn_integral_def
proof (safe intro!: SUP_mono)
  fix n assume n: "simple_function M n" "n \<le> u"
  from ae[THEN AE_E] guess N . note N = this
  then have ae_N: "AE x in M. x \<notin> N" by (auto intro: AE_not_in)
  let ?n = "\<lambda>x. n x * indicator (space M - N) x"
  have "AE x in M. n x \<le> ?n x" "simple_function M ?n"
    using n N ae_N by auto
  moreover
  { fix x have "?n x \<le> v x"
    proof cases
      assume x: "x \<in> space M - N"
      with N have "u x \<le> v x" by auto
      with n(2)[THEN le_funD, of x] x show ?thesis
        by (auto simp: max_def split: if_split_asm)
    qed simp }
  then have "?n \<le> v" by (auto simp: le_funI)
  moreover have "integral\<^sup>S M n \<le> integral\<^sup>S M ?n"
    using ae_N N n by (auto intro!: simple_integral_mono_AE)
  ultimately show "\<exists>m\<in>{g. simple_function M g \<and> g \<le> v}. integral\<^sup>S M n \<le> integral\<^sup>S M m"
    by force
qed

lemma nn_integral_mono:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x \<le> v x) \<Longrightarrow> integral\<^sup>N M u \<le> integral\<^sup>N M v"
  by (auto intro: nn_integral_mono_AE)

lemma mono_nn_integral: "mono F \<Longrightarrow> mono (\<lambda>x. integral\<^sup>N M (F x))"
  by (auto simp add: mono_def le_fun_def intro!: nn_integral_mono)

lemma nn_integral_cong_AE:
  "AE x in M. u x = v x \<Longrightarrow> integral\<^sup>N M u = integral\<^sup>N M v"
  by (auto simp: eq_iff intro!: nn_integral_mono_AE)

lemma nn_integral_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x = v x) \<Longrightarrow> integral\<^sup>N M u = integral\<^sup>N M v"
  by (auto intro: nn_integral_cong_AE)

lemma nn_integral_cong_simp:
  "(\<And>x. x \<in> space M =simp=> u x = v x) \<Longrightarrow> integral\<^sup>N M u = integral\<^sup>N M v"
  by (auto intro: nn_integral_cong simp: simp_implies_def)

lemma incseq_nn_integral:
  assumes "incseq f" shows "incseq (\<lambda>i. integral\<^sup>N M (f i))"
proof -
  have "\<And>i x. f i x \<le> f (Suc i) x"
    using assms by (auto dest!: incseq_SucD simp: le_fun_def)
  then show ?thesis
    by (auto intro!: incseq_SucI nn_integral_mono)
qed

lemma nn_integral_eq_simple_integral:
  assumes f: "simple_function M f" shows "integral\<^sup>N M f = integral\<^sup>S M f"
proof -
  let ?f = "\<lambda>x. f x * indicator (space M) x"
  have f': "simple_function M ?f" using f by auto
  have "integral\<^sup>N M ?f \<le> integral\<^sup>S M ?f" using f'
    by (force intro!: SUP_least simple_integral_mono simp: le_fun_def nn_integral_def)
  moreover have "integral\<^sup>S M ?f \<le> integral\<^sup>N M ?f"
    unfolding nn_integral_def
    using f' by (auto intro!: SUP_upper)
  ultimately show ?thesis
    by (simp cong: nn_integral_cong simple_integral_cong)
qed

text \<open>Beppo-Levi monotone convergence theorem\<close>
lemma nn_integral_monotone_convergence_SUP:
  assumes f: "incseq f" and [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
proof (rule antisym)
  show "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) \<le> (SUP i. (\<integral>\<^sup>+ x. f i x \<partial>M))"
    unfolding nn_integral_def_finite[of _ "\<lambda>x. SUP i. f i x"]
  proof (safe intro!: SUP_least)
    fix u assume sf_u[simp]: "simple_function M u" and
      u: "u \<le> (\<lambda>x. SUP i. f i x)" and u_range: "\<forall>x. u x < top"
    note sf_u[THEN borel_measurable_simple_function, measurable]
    show "integral\<^sup>S M u \<le> (SUP j. \<integral>\<^sup>+x. f j x \<partial>M)"
    proof (rule ennreal_approx_unit)
      fix a :: ennreal assume "a < 1"
      let ?au = "\<lambda>x. a * u x"

      let ?B = "\<lambda>c i. {x\<in>space M. ?au x = c \<and> c \<le> f i x}"
      have "integral\<^sup>S M ?au = (\<Sum>c\<in>?au`space M. c * (SUP i. emeasure M (?B c i)))"
        unfolding simple_integral_def
      proof (intro sum.cong ennreal_mult_left_cong refl)
        fix c assume "c \<in> ?au ` space M" "c \<noteq> 0"
        { fix x' assume x': "x' \<in> space M" "?au x' = c"
          with \<open>c \<noteq> 0\<close> u_range have "?au x' < 1 * u x'"
            by (intro ennreal_mult_strict_right_mono \<open>a < 1\<close>) (auto simp: less_le)
          also have "\<dots> \<le> (SUP i. f i x')"
            using u by (auto simp: le_fun_def)
          finally have "\<exists>i. ?au x' \<le> f i x'"
            by (auto simp: less_SUP_iff intro: less_imp_le) }
        then have *: "?au -` {c} \<inter> space M = (\<Union>i. ?B c i)"
          by auto
        show "emeasure M (?au -` {c} \<inter> space M) = (SUP i. emeasure M (?B c i))"
          unfolding * using f
          by (intro SUP_emeasure_incseq[symmetric])
             (auto simp: incseq_def le_fun_def intro: order_trans)
      qed
      also have "\<dots> = (SUP i. \<Sum>c\<in>?au`space M. c * emeasure M (?B c i))"
        unfolding SUP_mult_left_ennreal using f
        by (intro ennreal_SUP_sum[symmetric])
           (auto intro!: mult_mono emeasure_mono simp: incseq_def le_fun_def intro: order_trans)
      also have "\<dots> \<le> (SUP i. integral\<^sup>N M (f i))"
      proof (intro SUP_subset_mono order_refl)
        fix i
        have "(\<Sum>c\<in>?au`space M. c * emeasure M (?B c i)) =
          (\<integral>\<^sup>Sx. (a * u x) * indicator {x\<in>space M. a * u x \<le> f i x} x \<partial>M)"
          by (subst simple_integral_indicator)
             (auto intro!: sum.cong ennreal_mult_left_cong arg_cong2[where f=emeasure])
        also have "\<dots> = (\<integral>\<^sup>+x. (a * u x) * indicator {x\<in>space M. a * u x \<le> f i x} x \<partial>M)"
          by (rule nn_integral_eq_simple_integral[symmetric]) simp
        also have "\<dots> \<le> (\<integral>\<^sup>+x. f i x \<partial>M)"
          by (intro nn_integral_mono) (auto split: split_indicator)
        finally show "(\<Sum>c\<in>?au`space M. c * emeasure M (?B c i)) \<le> (\<integral>\<^sup>+x. f i x \<partial>M)" .
      qed
      finally show "a * integral\<^sup>S M u \<le> (SUP i. integral\<^sup>N M (f i))"
        by simp
    qed
  qed
qed (auto intro!: SUP_least SUP_upper nn_integral_mono)

lemma sup_continuous_nn_integral[order_continuous_intros]:
  assumes f: "\<And>y. sup_continuous (f y)"
  assumes [measurable]: "\<And>x. (\<lambda>y. f y x) \<in> borel_measurable M"
  shows "sup_continuous (\<lambda>x. (\<integral>\<^sup>+y. f y x \<partial>M))"
  unfolding sup_continuous_def
proof safe
  fix C :: "nat \<Rightarrow> 'b" assume C: "incseq C"
  with sup_continuous_mono[OF f] show "(\<integral>\<^sup>+ y. f y (Sup (C ` UNIV)) \<partial>M) = (SUP i. \<integral>\<^sup>+ y. f y (C i) \<partial>M)"
    unfolding sup_continuousD[OF f C]
    by (subst nn_integral_monotone_convergence_SUP) (auto simp: mono_def le_fun_def)
qed

theorem nn_integral_monotone_convergence_SUP_AE:
  assumes f: "\<And>i. AE x in M. f i x \<le> f (Suc i) x" "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
proof -
  from f have "AE x in M. \<forall>i. f i x \<le> f (Suc i) x"
    by (simp add: AE_all_countable)
  from this[THEN AE_E] guess N . note N = this
  let ?f = "\<lambda>i x. if x \<in> space M - N then f i x else 0"
  have f_eq: "AE x in M. \<forall>i. ?f i x = f i x" using N by (auto intro!: AE_I[of _ _ N])
  then have "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (\<integral>\<^sup>+ x. (SUP i. ?f i x) \<partial>M)"
    by (auto intro!: nn_integral_cong_AE)
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. ?f i x \<partial>M))"
  proof (rule nn_integral_monotone_convergence_SUP)
    show "incseq ?f" using N(1) by (force intro!: incseq_SucI le_funI)
    { fix i show "(\<lambda>x. if x \<in> space M - N then f i x else 0) \<in> borel_measurable M"
        using f N(3) by (intro measurable_If_set) auto }
  qed
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. f i x \<partial>M))"
    using f_eq by (force intro!: arg_cong[where f = "\<lambda>f. Sup (range f)"] nn_integral_cong_AE ext)
  finally show ?thesis .
qed

lemma nn_integral_monotone_convergence_simple:
  "incseq f \<Longrightarrow> (\<And>i. simple_function M (f i)) \<Longrightarrow> (SUP i. \<integral>\<^sup>S x. f i x \<partial>M) = (\<integral>\<^sup>+x. (SUP i. f i x) \<partial>M)"
  using nn_integral_monotone_convergence_SUP[of f M]
  by (simp add: nn_integral_eq_simple_integral[symmetric] borel_measurable_simple_function)

lemma SUP_simple_integral_sequences:
  assumes f: "incseq f" "\<And>i. simple_function M (f i)"
  and g: "incseq g" "\<And>i. simple_function M (g i)"
  and eq: "AE x in M. (SUP i. f i x) = (SUP i. g i x)"
  shows "(SUP i. integral\<^sup>S M (f i)) = (SUP i. integral\<^sup>S M (g i))"
    (is "Sup (?F ` _) = Sup (?G ` _)")
proof -
  have "(SUP i. integral\<^sup>S M (f i)) = (\<integral>\<^sup>+x. (SUP i. f i x) \<partial>M)"
    using f by (rule nn_integral_monotone_convergence_simple)
  also have "\<dots> = (\<integral>\<^sup>+x. (SUP i. g i x) \<partial>M)"
    unfolding eq[THEN nn_integral_cong_AE] ..
  also have "\<dots> = (SUP i. ?G i)"
    using g by (rule nn_integral_monotone_convergence_simple[symmetric])
  finally show ?thesis by simp
qed

lemma nn_integral_const[simp]: "(\<integral>\<^sup>+ x. c \<partial>M) = c * emeasure M (space M)"
  by (subst nn_integral_eq_simple_integral) auto

lemma nn_integral_linear:
  assumes f: "f \<in> borel_measurable M" and g: "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. a * f x + g x \<partial>M) = a * integral\<^sup>N M f + integral\<^sup>N M g"
    (is "integral\<^sup>N M ?L = _")
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f(1)] guess u .
  note u = nn_integral_monotone_convergence_simple[OF this(2,1)] this
  from borel_measurable_implies_simple_function_sequence'[OF g(1)] guess v .
  note v = nn_integral_monotone_convergence_simple[OF this(2,1)] this
  let ?L' = "\<lambda>i x. a * u i x + v i x"

  have "?L \<in> borel_measurable M" using assms by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] guess l .
  note l = nn_integral_monotone_convergence_simple[OF this(2,1)] this

  have inc: "incseq (\<lambda>i. a * integral\<^sup>S M (u i))" "incseq (\<lambda>i. integral\<^sup>S M (v i))"
    using u v by (auto simp: incseq_Suc_iff le_fun_def intro!: add_mono mult_left_mono simple_integral_mono)

  have l': "(SUP i. integral\<^sup>S M (l i)) = (SUP i. integral\<^sup>S M (?L' i))"
  proof (rule SUP_simple_integral_sequences[OF l(3,2)])
    show "incseq ?L'" "\<And>i. simple_function M (?L' i)"
      using u v unfolding incseq_Suc_iff le_fun_def
      by (auto intro!: add_mono mult_left_mono)
    { fix x
      have "(SUP i. a * u i x + v i x) = a * (SUP i. u i x) + (SUP i. v i x)"
        using u(3) v(3) u(4)[of _ x] v(4)[of _ x] unfolding SUP_mult_left_ennreal
        by (auto intro!: ennreal_SUP_add simp: incseq_Suc_iff le_fun_def add_mono mult_left_mono) }
    then show "AE x in M. (SUP i. l i x) = (SUP i. ?L' i x)"
      unfolding l(5) using u(5) v(5) by (intro AE_I2) auto
  qed
  also have "\<dots> = (SUP i. a * integral\<^sup>S M (u i) + integral\<^sup>S M (v i))"
    using u(2) v(2) by auto
  finally show ?thesis
    unfolding l(5)[symmetric] l(1)[symmetric]
    by (simp add: ennreal_SUP_add[OF inc] v u SUP_mult_left_ennreal[symmetric])
qed

lemma nn_integral_cmult: "f \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+ x. c * f x \<partial>M) = c * integral\<^sup>N M f"
  using nn_integral_linear[of f M "\<lambda>x. 0" c] by simp

lemma nn_integral_multc: "f \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+ x. f x * c \<partial>M) = integral\<^sup>N M f * c"
  unfolding mult.commute[of _ c] nn_integral_cmult by simp

lemma nn_integral_divide: "f \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+ x. f x / c \<partial>M) = (\<integral>\<^sup>+ x. f x \<partial>M) / c"
   unfolding divide_ennreal_def by (rule nn_integral_multc)

lemma nn_integral_indicator[simp]: "A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. indicator A x\<partial>M) = (emeasure M) A"
  by (subst nn_integral_eq_simple_integral) (auto simp: simple_integral_indicator)

lemma nn_integral_cmult_indicator: "A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. c * indicator A x \<partial>M) = c * emeasure M A"
  by (subst nn_integral_eq_simple_integral) (auto)

lemma nn_integral_indicator':
  assumes [measurable]: "A \<inter> space M \<in> sets M"
  shows "(\<integral>\<^sup>+ x. indicator A x \<partial>M) = emeasure M (A \<inter> space M)"
proof -
  have "(\<integral>\<^sup>+ x. indicator A x \<partial>M) = (\<integral>\<^sup>+ x. indicator (A \<inter> space M) x \<partial>M)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also have "\<dots> = emeasure M (A \<inter> space M)"
    by simp
  finally show ?thesis .
qed

lemma nn_integral_indicator_singleton[simp]:
  assumes [measurable]: "{y} \<in> sets M" shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>M) = f y * emeasure M {y}"
proof -
  have "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>M) = (\<integral>\<^sup>+x. f y * indicator {y} x \<partial>M)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  then show ?thesis
    by (simp add: nn_integral_cmult)
qed

lemma nn_integral_set_ennreal:
  "(\<integral>\<^sup>+x. ennreal (f x) * indicator A x \<partial>M) = (\<integral>\<^sup>+x. ennreal (f x * indicator A x) \<partial>M)"
  by (rule nn_integral_cong) (simp split: split_indicator)

lemma nn_integral_indicator_singleton'[simp]:
  assumes [measurable]: "{y} \<in> sets M"
  shows "(\<integral>\<^sup>+x. ennreal (f x * indicator {y} x) \<partial>M) = f y * emeasure M {y}"
  by (subst nn_integral_set_ennreal[symmetric]) (simp)

lemma nn_integral_add:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+ x. f x + g x \<partial>M) = integral\<^sup>N M f + integral\<^sup>N M g"
  using nn_integral_linear[of f M g 1] by simp

lemma nn_integral_sum:
  "(\<And>i. i \<in> P \<Longrightarrow> f i \<in> borel_measurable M) \<Longrightarrow> (\<integral>\<^sup>+ x. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^sup>N M (f i))"
  by (induction P rule: infinite_finite_induct) (auto simp: nn_integral_add)

theorem nn_integral_suminf:
  assumes f: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (\<Sum>i. f i x) \<partial>M) = (\<Sum>i. integral\<^sup>N M (f i))"
proof -
  have all_pos: "AE x in M. \<forall>i. 0 \<le> f i x"
    using assms by (auto simp: AE_all_countable)
  have "(\<Sum>i. integral\<^sup>N M (f i)) = (SUP n. \<Sum>i<n. integral\<^sup>N M (f i))"
    by (rule suminf_eq_SUP)
  also have "\<dots> = (SUP n. \<integral>\<^sup>+x. (\<Sum>i<n. f i x) \<partial>M)"
    unfolding nn_integral_sum[OF f] ..
  also have "\<dots> = \<integral>\<^sup>+x. (SUP n. \<Sum>i<n. f i x) \<partial>M" using f all_pos
    by (intro nn_integral_monotone_convergence_SUP_AE[symmetric])
       (elim AE_mp, auto simp: sum_nonneg simp del: sum.lessThan_Suc intro!: AE_I2 sum_mono2)
  also have "\<dots> = \<integral>\<^sup>+x. (\<Sum>i. f i x) \<partial>M" using all_pos
    by (intro nn_integral_cong_AE) (auto simp: suminf_eq_SUP)
  finally show ?thesis by simp
qed

lemma nn_integral_bound_simple_function:
  assumes bnd: "\<And>x. x \<in> space M \<Longrightarrow> f x < \<infinity>"
  assumes f[measurable]: "simple_function M f"
  assumes supp: "emeasure M {x\<in>space M. f x \<noteq> 0} < \<infinity>"
  shows "nn_integral M f < \<infinity>"
proof cases
  assume "space M = {}"
  then have "nn_integral M f = (\<integral>\<^sup>+x. 0 \<partial>M)"
    by (intro nn_integral_cong) auto
  then show ?thesis by simp
next
  assume "space M \<noteq> {}"
  with simple_functionD(1)[OF f] bnd have bnd: "0 \<le> Max (f`space M) \<and> Max (f`space M) < \<infinity>"
    by (subst Max_less_iff) (auto simp: Max_ge_iff)

  have "nn_integral M f \<le> (\<integral>\<^sup>+x. Max (f`space M) * indicator {x\<in>space M. f x \<noteq> 0} x \<partial>M)"
  proof (rule nn_integral_mono)
    fix x assume "x \<in> space M"
    with f show "f x \<le> Max (f ` space M) * indicator {x \<in> space M. f x \<noteq> 0} x"
      by (auto split: split_indicator intro!: Max_ge simple_functionD)
  qed
  also have "\<dots> < \<infinity>"
    using bnd supp by (subst nn_integral_cmult) (auto simp: ennreal_mult_less_top)
  finally show ?thesis .
qed

theorem nn_integral_Markov_inequality:
  assumes u: "(\<lambda>x. u x * indicator A x) \<in> borel_measurable M" and "A \<in> sets M"
  shows "(emeasure M) ({x\<in>A. 1 \<le> c * u x}) \<le> c * (\<integral>\<^sup>+ x. u x * indicator A x \<partial>M)"
    (is "(emeasure M) ?A \<le> _ * ?PI")
proof -
  define u' where "u' = (\<lambda>x. u x * indicator A x)"
  have [measurable]: "u' \<in> borel_measurable M"
    using u unfolding u'_def .
  have "{x\<in>space M. c * u' x \<ge> 1} \<in> sets M"
    by measurable
  also have "{x\<in>space M. c * u' x \<ge> 1} = ?A"
    using sets.sets_into_space[OF \<open>A \<in> sets M\<close>] by (auto simp: u'_def indicator_def)
  finally have "(emeasure M) ?A = (\<integral>\<^sup>+ x. indicator ?A x \<partial>M)"
    using nn_integral_indicator by simp
  also have "\<dots> \<le> (\<integral>\<^sup>+ x. c * (u x * indicator A x) \<partial>M)"
    using u by (auto intro!: nn_integral_mono_AE simp: indicator_def)
  also have "\<dots> = c * (\<integral>\<^sup>+ x. u x * indicator A x \<partial>M)"
    using assms by (auto intro!: nn_integral_cmult)
  finally show ?thesis .
qed

lemma Chernoff_ineq_nn_integral_ge:
  assumes s: "s > 0" and [measurable]: "A \<in> sets M"
  assumes [measurable]: "(\<lambda>x. f x * indicator A x) \<in> borel_measurable M"
  shows   "emeasure M {x\<in>A. f x \<ge> a} \<le>
           ennreal (exp (-s * a)) * nn_integral M (\<lambda>x. ennreal (exp (s * f x)) * indicator A x)"
proof -
  define f' where "f' = (\<lambda>x. f x * indicator A x)"
  have [measurable]: "f' \<in> borel_measurable M"
    using assms(3) unfolding f'_def by assumption
  have "(\<lambda>x. ennreal (exp (s * f' x)) * indicator A x) \<in> borel_measurable M"
    by simp
  also have "(\<lambda>x. ennreal (exp (s * f' x)) * indicator A x) =
             (\<lambda>x. ennreal (exp (s * f x)) * indicator A x)"
    by (auto simp: f'_def indicator_def fun_eq_iff)
  finally have meas: "\<dots> \<in> borel_measurable M" .

  have "{x\<in>A. f x \<ge> a} = {x\<in>A. ennreal (exp (-s * a)) * ennreal (exp (s * f x)) \<ge> 1}"
    using s by (auto simp: exp_minus field_simps simp flip: ennreal_mult)
  also have "emeasure M \<dots> \<le> ennreal (exp (-s * a)) *
               (\<integral>\<^sup>+x. ennreal (exp (s * f x)) * indicator A x \<partial>M)"
    by (intro order.trans[OF nn_integral_Markov_inequality] meas) auto
  finally show ?thesis .
qed

lemma Chernoff_ineq_nn_integral_le:
  assumes s: "s > 0" and [measurable]: "A \<in> sets M"
  assumes [measurable]: "f \<in> borel_measurable M"
  shows   "emeasure M {x\<in>A. f x \<le> a} \<le>
           ennreal (exp (s * a)) * nn_integral M (\<lambda>x. ennreal (exp (-s * f x)) * indicator A x)"
  using Chernoff_ineq_nn_integral_ge[of s A M "\<lambda>x. -f x" "-a"] assms by simp

lemma nn_integral_noteq_infinite:
  assumes g: "g \<in> borel_measurable M" and "integral\<^sup>N M g \<noteq> \<infinity>"
  shows "AE x in M. g x \<noteq> \<infinity>"
proof (rule ccontr)
  assume c: "\<not> (AE x in M. g x \<noteq> \<infinity>)"
  have "(emeasure M) {x\<in>space M. g x = \<infinity>} \<noteq> 0"
    using c g by (auto simp add: AE_iff_null)
  then have "0 < (emeasure M) {x\<in>space M. g x = \<infinity>}"
    by (auto simp: zero_less_iff_neq_zero)
  then have "\<infinity> = \<infinity> * (emeasure M) {x\<in>space M. g x = \<infinity>}"
    by (auto simp: ennreal_top_eq_mult_iff)
  also have "\<dots> \<le> (\<integral>\<^sup>+x. \<infinity> * indicator {x\<in>space M. g x = \<infinity>} x \<partial>M)"
    using g by (subst nn_integral_cmult_indicator) auto
  also have "\<dots> \<le> integral\<^sup>N M g"
    using assms by (auto intro!: nn_integral_mono_AE simp: indicator_def)
  finally show False
    using \<open>integral\<^sup>N M g \<noteq> \<infinity>\<close> by (auto simp: top_unique)
qed

lemma nn_integral_PInf:
  assumes f: "f \<in> borel_measurable M" and not_Inf: "integral\<^sup>N M f \<noteq> \<infinity>"
  shows "emeasure M (f -` {\<infinity>} \<inter> space M) = 0"
proof -
  have "\<infinity> * emeasure M (f -` {\<infinity>} \<inter> space M) = (\<integral>\<^sup>+ x. \<infinity> * indicator (f -` {\<infinity>} \<inter> space M) x \<partial>M)"
    using f by (subst nn_integral_cmult_indicator) (auto simp: measurable_sets)
  also have "\<dots> \<le> integral\<^sup>N M f"
    by (auto intro!: nn_integral_mono simp: indicator_def)
  finally have "\<infinity> * (emeasure M) (f -` {\<infinity>} \<inter> space M) \<le> integral\<^sup>N M f"
    by simp
  then show ?thesis
    using assms by (auto simp: ennreal_top_mult top_unique split: if_split_asm)
qed

lemma simple_integral_PInf:
  "simple_function M f \<Longrightarrow> integral\<^sup>S M f \<noteq> \<infinity> \<Longrightarrow> emeasure M (f -` {\<infinity>} \<inter> space M) = 0"
  by (rule nn_integral_PInf) (auto simp: nn_integral_eq_simple_integral borel_measurable_simple_function)

lemma nn_integral_PInf_AE:
  assumes "f \<in> borel_measurable M" "integral\<^sup>N M f \<noteq> \<infinity>" shows "AE x in M. f x \<noteq> \<infinity>"
proof (rule AE_I)
  show "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
    by (rule nn_integral_PInf[OF assms])
  show "f -` {\<infinity>} \<inter> space M \<in> sets M"
    using assms by (auto intro: borel_measurable_vimage)
qed auto

lemma nn_integral_diff:
  assumes f: "f \<in> borel_measurable M"
  and g: "g \<in> borel_measurable M"
  and fin: "integral\<^sup>N M g \<noteq> \<infinity>"
  and mono: "AE x in M. g x \<le> f x"
  shows "(\<integral>\<^sup>+ x. f x - g x \<partial>M) = integral\<^sup>N M f - integral\<^sup>N M g"
proof -
  have diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    using assms by auto
  have "AE x in M. f x = f x - g x + g x"
    using diff_add_cancel_ennreal mono nn_integral_noteq_infinite[OF g fin] assms by auto
  then have **: "integral\<^sup>N M f = (\<integral>\<^sup>+x. f x - g x \<partial>M) + integral\<^sup>N M g"
    unfolding nn_integral_add[OF diff g, symmetric]
    by (rule nn_integral_cong_AE)
  show ?thesis unfolding **
    using fin
    by (cases rule: ennreal2_cases[of "\<integral>\<^sup>+ x. f x - g x \<partial>M" "integral\<^sup>N M g"]) auto
qed

lemma nn_integral_mult_bounded_inf:
  assumes f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>" and c: "c \<noteq> \<infinity>" and ae: "AE x in M. g x \<le> c * f x"
  shows "(\<integral>\<^sup>+x. g x \<partial>M) < \<infinity>"
proof -
  have "(\<integral>\<^sup>+x. g x \<partial>M) \<le> (\<integral>\<^sup>+x. c * f x \<partial>M)"
    by (intro nn_integral_mono_AE ae)
  also have "(\<integral>\<^sup>+x. c * f x \<partial>M) < \<infinity>"
    using c f by (subst nn_integral_cmult) (auto simp: ennreal_mult_less_top top_unique not_less)
  finally show ?thesis .
qed

text \<open>Fatou's lemma: convergence theorem on limes inferior\<close>

lemma nn_integral_monotone_convergence_INF_AE':
  assumes f: "\<And>i. AE x in M. f (Suc i) x \<le> f i x" and [measurable]: "\<And>i. f i \<in> borel_measurable M"
    and *: "(\<integral>\<^sup>+ x. f 0 x \<partial>M) < \<infinity>"
  shows "(\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) = (INF i. integral\<^sup>N M (f i))"
proof (rule ennreal_minus_cancel)
  have "integral\<^sup>N M (f 0) - (\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) = (\<integral>\<^sup>+x. f 0 x - (INF i. f i x) \<partial>M)"
  proof (rule nn_integral_diff[symmetric])
    have "(\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) \<le> (\<integral>\<^sup>+ x. f 0 x \<partial>M)"
      by (intro nn_integral_mono INF_lower) simp
    with * show "(\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) \<noteq> \<infinity>"
      by simp
  qed (auto intro: INF_lower)
  also have "\<dots> = (\<integral>\<^sup>+x. (SUP i. f 0 x - f i x) \<partial>M)"
    by (simp add: ennreal_INF_const_minus)
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+x. f 0 x - f i x \<partial>M))"
  proof (intro nn_integral_monotone_convergence_SUP_AE)
    show "AE x in M. f 0 x - f i x \<le> f 0 x - f (Suc i) x" for i
      using f[of i] by eventually_elim (auto simp: ennreal_mono_minus)
  qed simp
  also have "\<dots> = (SUP i. nn_integral M (f 0) - (\<integral>\<^sup>+x. f i x \<partial>M))"
  proof (subst nn_integral_diff[symmetric])
    fix i
    have dec: "AE x in M. \<forall>i. f (Suc i) x \<le> f i x"
      unfolding AE_all_countable using f by auto
    then show "AE x in M. f i x \<le> f 0 x"
      using dec by eventually_elim (auto intro: lift_Suc_antimono_le[of "\<lambda>i. f i x" 0 i for x])
    then have "(\<integral>\<^sup>+ x. f i x \<partial>M) \<le> (\<integral>\<^sup>+ x. f 0 x \<partial>M)"
      by (rule nn_integral_mono_AE)
    with * show "(\<integral>\<^sup>+ x. f i x \<partial>M) \<noteq> \<infinity>"
      by simp
  qed (insert f, auto simp: decseq_def le_fun_def)
  finally show "integral\<^sup>N M (f 0) - (\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) =
    integral\<^sup>N M (f 0) - (INF i. \<integral>\<^sup>+ x. f i x \<partial>M)"
    by (simp add: ennreal_INF_const_minus)
qed (insert *, auto intro!: nn_integral_mono intro: INF_lower)

theorem nn_integral_monotone_convergence_INF_AE:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes f: "\<And>i. AE x in M. f (Suc i) x \<le> f i x"
    and [measurable]: "\<And>i. f i \<in> borel_measurable M"
    and fin: "(\<integral>\<^sup>+ x. f i x \<partial>M) < \<infinity>"
  shows "(\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) = (INF i. integral\<^sup>N M (f i))"
proof -
  { fix f :: "nat \<Rightarrow> ennreal" and j assume "decseq f"
    then have "(INF i. f i) = (INF i. f (i + j))"
      apply (intro INF_eq)
      apply (rule_tac x="i" in bexI)
      apply (auto simp: decseq_def le_fun_def)
      done }
  note INF_shift = this
  have mono: "AE x in M. \<forall>i. f (Suc i) x \<le> f i x"
    using f by (auto simp: AE_all_countable)
  then have "AE x in M. (INF i. f i x) = (INF n. f (n + i) x)"
    by eventually_elim (auto intro!: decseq_SucI INF_shift)
  then have "(\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) = (\<integral>\<^sup>+ x. (INF n. f (n + i) x) \<partial>M)"
    by (rule nn_integral_cong_AE)
  also have "\<dots> = (INF n. (\<integral>\<^sup>+ x. f (n + i) x \<partial>M))"
    by (rule nn_integral_monotone_convergence_INF_AE') (insert assms, auto)
  also have "\<dots> = (INF n. (\<integral>\<^sup>+ x. f n x \<partial>M))"
    by (intro INF_shift[symmetric] decseq_SucI nn_integral_mono_AE f)
  finally show ?thesis .
qed

lemma nn_integral_monotone_convergence_INF_decseq:
  assumes f: "decseq f" and *: "\<And>i. f i \<in> borel_measurable M" "(\<integral>\<^sup>+ x. f i x \<partial>M) < \<infinity>"
  shows "(\<integral>\<^sup>+ x. (INF i. f i x) \<partial>M) = (INF i. integral\<^sup>N M (f i))"
  using nn_integral_monotone_convergence_INF_AE[of f M i, OF _ *] f by (auto simp: decseq_Suc_iff le_fun_def)

theorem nn_integral_liminf:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes u: "\<And>i. u i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M) \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
proof -
  have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M) = (SUP n. \<integral>\<^sup>+ x. (INF i\<in>{n..}. u i x) \<partial>M)"
    unfolding liminf_SUP_INF using u
    by (intro nn_integral_monotone_convergence_SUP_AE)
       (auto intro!: AE_I2 intro: INF_greatest INF_superset_mono)
  also have "\<dots> \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
    by (auto simp: liminf_SUP_INF intro!: SUP_mono INF_greatest nn_integral_mono INF_lower)
  finally show ?thesis .
qed

theorem nn_integral_limsup:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes [measurable]: "\<And>i. u i \<in> borel_measurable M" "w \<in> borel_measurable M"
  assumes bounds: "\<And>i. AE x in M. u i x \<le> w x" and w: "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
  shows "limsup (\<lambda>n. integral\<^sup>N M (u n)) \<le> (\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M)"
proof -
  have bnd: "AE x in M. \<forall>i. u i x \<le> w x"
    using bounds by (auto simp: AE_all_countable)
  then have "(\<integral>\<^sup>+ x. (SUP n. u n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. w x \<partial>M)"
    by (auto intro!: nn_integral_mono_AE elim: eventually_mono intro: SUP_least)
  then have "(\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M) = (INF n. \<integral>\<^sup>+ x. (SUP i\<in>{n..}. u i x) \<partial>M)"
    unfolding limsup_INF_SUP using bnd w
    by (intro nn_integral_monotone_convergence_INF_AE')
       (auto intro!: AE_I2 intro: SUP_least SUP_subset_mono)
  also have "\<dots> \<ge> limsup (\<lambda>n. integral\<^sup>N M (u n))"
    by (auto simp: limsup_INF_SUP intro!: INF_mono SUP_least exI nn_integral_mono SUP_upper)
  finally (xtrans) show ?thesis .
qed

lemma nn_integral_LIMSEQ:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M"
    and u: "\<And>x. (\<lambda>i. f i x) \<longlonglongrightarrow> u x"
  shows "(\<lambda>n. integral\<^sup>N M (f n)) \<longlonglongrightarrow> integral\<^sup>N M u"
proof -
  have "(\<lambda>n. integral\<^sup>N M (f n)) \<longlonglongrightarrow> (SUP n. integral\<^sup>N M (f n))"
    using f by (intro LIMSEQ_SUP[of "\<lambda>n. integral\<^sup>N M (f n)"] incseq_nn_integral)
  also have "(SUP n. integral\<^sup>N M (f n)) = integral\<^sup>N M (\<lambda>x. SUP n. f n x)"
    using f by (intro nn_integral_monotone_convergence_SUP[symmetric])
  also have "integral\<^sup>N M (\<lambda>x. SUP n. f n x) = integral\<^sup>N M (\<lambda>x. u x)"
    using f by (subst LIMSEQ_SUP[THEN LIMSEQ_unique, OF _ u]) (auto simp: incseq_def le_fun_def)
  finally show ?thesis .
qed

theorem nn_integral_dominated_convergence:
  assumes [measurable]:
       "\<And>i. u i \<in> borel_measurable M" "u' \<in> borel_measurable M" "w \<in> borel_measurable M"
    and bound: "\<And>j. AE x in M. u j x \<le> w x"
    and w: "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
    and u': "AE x in M. (\<lambda>i. u i x) \<longlonglongrightarrow> u' x"
  shows "(\<lambda>i. (\<integral>\<^sup>+x. u i x \<partial>M)) \<longlonglongrightarrow> (\<integral>\<^sup>+x. u' x \<partial>M)"
proof -
  have "limsup (\<lambda>n. integral\<^sup>N M (u n)) \<le> (\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M)"
    by (intro nn_integral_limsup[OF _ _ bound w]) auto
  moreover have "(\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M) = (\<integral>\<^sup>+ x. u' x \<partial>M)"
    using u' by (intro nn_integral_cong_AE, eventually_elim) (metis tendsto_iff_Liminf_eq_Limsup sequentially_bot)
  moreover have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M) = (\<integral>\<^sup>+ x. u' x \<partial>M)"
    using u' by (intro nn_integral_cong_AE, eventually_elim) (metis tendsto_iff_Liminf_eq_Limsup sequentially_bot)
  moreover have "(\<integral>\<^sup>+x. liminf (\<lambda>n. u n x) \<partial>M) \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
    by (intro nn_integral_liminf) auto
  moreover have "liminf (\<lambda>n. integral\<^sup>N M (u n)) \<le> limsup (\<lambda>n. integral\<^sup>N M (u n))"
    by (intro Liminf_le_Limsup sequentially_bot)
  ultimately show ?thesis
    by (intro Liminf_eq_Limsup) auto
qed

lemma inf_continuous_nn_integral[order_continuous_intros]:
  assumes f: "\<And>y. inf_continuous (f y)"
  assumes [measurable]: "\<And>x. (\<lambda>y. f y x) \<in> borel_measurable M"
  assumes bnd: "\<And>x. (\<integral>\<^sup>+ y. f y x \<partial>M) \<noteq> \<infinity>"
  shows "inf_continuous (\<lambda>x. (\<integral>\<^sup>+y. f y x \<partial>M))"
  unfolding inf_continuous_def
proof safe
  fix C :: "nat \<Rightarrow> 'b" assume C: "decseq C"
  then show "(\<integral>\<^sup>+ y. f y (Inf (C ` UNIV)) \<partial>M) = (INF i. \<integral>\<^sup>+ y. f y (C i) \<partial>M)"
    using inf_continuous_mono[OF f] bnd
    by (auto simp add: inf_continuousD[OF f C] fun_eq_iff antimono_def mono_def le_fun_def less_top
             intro!: nn_integral_monotone_convergence_INF_decseq)
qed

lemma nn_integral_null_set:
  assumes "N \<in> null_sets M" shows "(\<integral>\<^sup>+ x. u x * indicator N x \<partial>M) = 0"
proof -
  have "(\<integral>\<^sup>+ x. u x * indicator N x \<partial>M) = (\<integral>\<^sup>+ x. 0 \<partial>M)"
  proof (intro nn_integral_cong_AE AE_I)
    show "{x \<in> space M. u x * indicator N x \<noteq> 0} \<subseteq> N"
      by (auto simp: indicator_def)
    show "(emeasure M) N = 0" "N \<in> sets M"
      using assms by auto
  qed
  then show ?thesis by simp
qed

lemma nn_integral_0_iff:
  assumes u [measurable]: "u \<in> borel_measurable M"
  shows "integral\<^sup>N M u = 0 \<longleftrightarrow> emeasure M {x\<in>space M. u x \<noteq> 0} = 0"
    (is "_ \<longleftrightarrow> (emeasure M) ?A = 0")
proof -
  have u_eq: "(\<integral>\<^sup>+ x. u x * indicator ?A x \<partial>M) = integral\<^sup>N M u"
    by (auto intro!: nn_integral_cong simp: indicator_def)
  show ?thesis
  proof
    assume "(emeasure M) ?A = 0"
    with nn_integral_null_set[of ?A M u] u
    show "integral\<^sup>N M u = 0" by (simp add: u_eq null_sets_def)
  next
    assume *: "integral\<^sup>N M u = 0"
    let ?M = "\<lambda>n. {x \<in> space M. 1 \<le> real (n::nat) * u x}"
    have "0 = (SUP n. (emeasure M) (?M n \<inter> ?A))"
    proof -
      { fix n :: nat
        have "emeasure M {x \<in> ?A. 1 \<le> of_nat n * u x} \<le>
                of_nat n * \<integral>\<^sup>+ x. u x * indicator ?A x \<partial>M"
          by (intro nn_integral_Markov_inequality) auto
        also have "{x \<in> ?A. 1 \<le> of_nat n * u x} = (?M n \<inter> ?A)"
          by (auto simp: ennreal_of_nat_eq_real_of_nat u_eq * )
        finally have "emeasure M (?M n \<inter> ?A) \<le> 0"
          by (simp add: ennreal_of_nat_eq_real_of_nat u_eq * )
        moreover have "0 \<le> (emeasure M) (?M n \<inter> ?A)" using u by auto
        ultimately have "(emeasure M) (?M n \<inter> ?A) = 0" by auto }
      thus ?thesis by simp
    qed
    also have "\<dots> = (emeasure M) (\<Union>n. ?M n \<inter> ?A)"
    proof (safe intro!: SUP_emeasure_incseq)
      fix n show "?M n \<inter> ?A \<in> sets M"
        using u by (auto intro!: sets.Int)
    next
      show "incseq (\<lambda>n. {x \<in> space M. 1 \<le> real n * u x} \<inter> {x \<in> space M. u x \<noteq> 0})"
      proof (safe intro!: incseq_SucI)
        fix n :: nat and x
        assume *: "1 \<le> real n * u x"
        also have "real n * u x \<le> real (Suc n) * u x"
          by (auto intro!: mult_right_mono)
        finally show "1 \<le> real (Suc n) * u x" by auto
      qed
    qed
    also have "\<dots> = (emeasure M) {x\<in>space M. 0 < u x}"
    proof (safe intro!: arg_cong[where f="(emeasure M)"])
      fix x assume "0 < u x" and [simp, intro]: "x \<in> space M"
      show "x \<in> (\<Union>n. ?M n \<inter> ?A)"
      proof (cases "u x" rule: ennreal_cases)
        case (real r) with \<open>0 < u x\<close> have "0 < r" by auto
        obtain j :: nat where "1 / r \<le> real j" using real_arch_simple ..
        hence "1 / r * r \<le> real j * r" unfolding mult_le_cancel_right using \<open>0 < r\<close> by auto
        hence "1 \<le> real j * r" using real \<open>0 < r\<close> by auto
        thus ?thesis using \<open>0 < r\<close> real
          by (auto simp: ennreal_of_nat_eq_real_of_nat ennreal_1[symmetric] ennreal_mult[symmetric]
                   simp del: ennreal_1)
      qed (insert \<open>0 < u x\<close>, auto simp: ennreal_mult_top)
    qed (auto simp: zero_less_iff_neq_zero)
    finally show "emeasure M ?A = 0"
      by (simp add: zero_less_iff_neq_zero)
  qed
qed

lemma nn_integral_0_iff_AE:
  assumes u: "u \<in> borel_measurable M"
  shows "integral\<^sup>N M u = 0 \<longleftrightarrow> (AE x in M. u x = 0)"
proof -
  have sets: "{x\<in>space M. u x \<noteq> 0} \<in> sets M"
    using u by auto
  show "integral\<^sup>N M u = 0 \<longleftrightarrow> (AE x in M. u x = 0)"
    using nn_integral_0_iff[of u] AE_iff_null[OF sets] u by auto
qed

lemma AE_iff_nn_integral:
  "{x\<in>space M. P x} \<in> sets M \<Longrightarrow> (AE x in M. P x) \<longleftrightarrow> integral\<^sup>N M (indicator {x. \<not> P x}) = 0"
  by (subst nn_integral_0_iff_AE) (auto simp: indicator_def[abs_def])

lemma nn_integral_less:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes f: "(\<integral>\<^sup>+x. f x \<partial>M) \<noteq> \<infinity>"
  assumes ord: "AE x in M. f x \<le> g x" "\<not> (AE x in M. g x \<le> f x)"
  shows "(\<integral>\<^sup>+x. f x \<partial>M) < (\<integral>\<^sup>+x. g x \<partial>M)"
proof -
  have "0 < (\<integral>\<^sup>+x. g x - f x \<partial>M)"
  proof (intro order_le_neq_trans notI)
    assume "0 = (\<integral>\<^sup>+x. g x - f x \<partial>M)"
    then have "AE x in M. g x - f x = 0"
      using nn_integral_0_iff_AE[of "\<lambda>x. g x - f x" M] by simp
    with ord(1) have "AE x in M. g x \<le> f x"
      by eventually_elim (auto simp: ennreal_minus_eq_0)
    with ord show False
      by simp
  qed simp
  also have "\<dots> = (\<integral>\<^sup>+x. g x \<partial>M) - (\<integral>\<^sup>+x. f x \<partial>M)"
    using f by (subst nn_integral_diff) (auto simp: ord)
  finally show ?thesis
    using f by (auto dest!: ennreal_minus_pos_iff[rotated] simp: less_top)
qed

lemma nn_integral_subalgebra:
  assumes f: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
  shows "integral\<^sup>N N f = integral\<^sup>N M f"
proof -
  have [simp]: "\<And>f :: 'a \<Rightarrow> ennreal. f \<in> borel_measurable N \<Longrightarrow> f \<in> borel_measurable M"
    using N by (auto simp: measurable_def)
  have [simp]: "\<And>P. (AE x in N. P x) \<Longrightarrow> (AE x in M. P x)"
    using N by (auto simp add: eventually_ae_filter null_sets_def subset_eq)
  have [simp]: "\<And>A. A \<in> sets N \<Longrightarrow> A \<in> sets M"
    using N by auto
  from f show ?thesis
    apply induct
    apply (simp_all add: nn_integral_add nn_integral_cmult nn_integral_monotone_convergence_SUP N image_comp)
    apply (auto intro!: nn_integral_cong cong: nn_integral_cong simp: N(2)[symmetric])
    done
qed

lemma nn_integral_nat_function:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "f \<in> measurable M (count_space UNIV)"
  shows "(\<integral>\<^sup>+x. of_nat (f x) \<partial>M) = (\<Sum>t. emeasure M {x\<in>space M. t < f x})"
proof -
  define F where "F i = {x\<in>space M. i < f x}" for i
  with assms have [measurable]: "\<And>i. F i \<in> sets M"
    by auto

  { fix x assume "x \<in> space M"
    have "(\<lambda>i. if i < f x then 1 else 0) sums (of_nat (f x)::real)"
      using sums_If_finite[of "\<lambda>i. i < f x" "\<lambda>_. 1::real"] by simp
    then have "(\<lambda>i. ennreal (if i < f x then 1 else 0)) sums of_nat(f x)"
      unfolding ennreal_of_nat_eq_real_of_nat
      by (subst sums_ennreal) auto
    moreover have "\<And>i. ennreal (if i < f x then 1 else 0) = indicator (F i) x"
      using \<open>x \<in> space M\<close> by (simp add: one_ennreal_def F_def)
    ultimately have "of_nat (f x) = (\<Sum>i. indicator (F i) x :: ennreal)"
      by (simp add: sums_iff) }
  then have "(\<integral>\<^sup>+x. of_nat (f x) \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>i. indicator (F i) x) \<partial>M)"
    by (simp cong: nn_integral_cong)
  also have "\<dots> = (\<Sum>i. emeasure M (F i))"
    by (simp add: nn_integral_suminf)
  finally show ?thesis
    by (simp add: F_def)
qed

theorem nn_integral_lfp:
  assumes sets[simp]: "\<And>s. sets (M s) = sets N"
  assumes f: "sup_continuous f"
  assumes g: "sup_continuous g"
  assumes meas: "\<And>F. F \<in> borel_measurable N \<Longrightarrow> f F \<in> borel_measurable N"
  assumes step: "\<And>F s. F \<in> borel_measurable N \<Longrightarrow> integral\<^sup>N (M s) (f F) = g (\<lambda>s. integral\<^sup>N (M s) F) s"
  shows "(\<integral>\<^sup>+\<omega>. lfp f \<omega> \<partial>M s) = lfp g s"
proof (subst lfp_transfer_bounded[where \<alpha>="\<lambda>F s. \<integral>\<^sup>+x. F x \<partial>M s" and g=g and f=f and P="\<lambda>f. f \<in> borel_measurable N", symmetric])
  fix C :: "nat \<Rightarrow> 'b \<Rightarrow> ennreal" assume "incseq C" "\<And>i. C i \<in> borel_measurable N"
  then show "(\<lambda>s. \<integral>\<^sup>+x. (SUP i. C i) x \<partial>M s) = (SUP i. (\<lambda>s. \<integral>\<^sup>+x. C i x \<partial>M s))"
    unfolding SUP_apply[abs_def]
    by (subst nn_integral_monotone_convergence_SUP)
       (auto simp: mono_def fun_eq_iff intro!: arg_cong2[where f=emeasure] cong: measurable_cong_sets)
qed (auto simp add: step le_fun_def SUP_apply[abs_def] bot_fun_def bot_ennreal intro!: meas f g)

theorem nn_integral_gfp:
  assumes sets[simp]: "\<And>s. sets (M s) = sets N"
  assumes f: "inf_continuous f" and g: "inf_continuous g"
  assumes meas: "\<And>F. F \<in> borel_measurable N \<Longrightarrow> f F \<in> borel_measurable N"
  assumes bound: "\<And>F s. F \<in> borel_measurable N \<Longrightarrow> (\<integral>\<^sup>+x. f F x \<partial>M s) < \<infinity>"
  assumes non_zero: "\<And>s. emeasure (M s) (space (M s)) \<noteq> 0"
  assumes step: "\<And>F s. F \<in> borel_measurable N \<Longrightarrow> integral\<^sup>N (M s) (f F) = g (\<lambda>s. integral\<^sup>N (M s) F) s"
  shows "(\<integral>\<^sup>+\<omega>. gfp f \<omega> \<partial>M s) = gfp g s"
proof (subst gfp_transfer_bounded[where \<alpha>="\<lambda>F s. \<integral>\<^sup>+x. F x \<partial>M s" and g=g and f=f
    and P="\<lambda>F. F \<in> borel_measurable N \<and> (\<forall>s. (\<integral>\<^sup>+x. F x \<partial>M s) < \<infinity>)", symmetric])
  fix C :: "nat \<Rightarrow> 'b \<Rightarrow> ennreal" assume "decseq C" "\<And>i. C i \<in> borel_measurable N \<and> (\<forall>s. integral\<^sup>N (M s) (C i) < \<infinity>)"
  then show "(\<lambda>s. \<integral>\<^sup>+x. (INF i. C i) x \<partial>M s) = (INF i. (\<lambda>s. \<integral>\<^sup>+x. C i x \<partial>M s))"
    unfolding INF_apply[abs_def]
    by (subst nn_integral_monotone_convergence_INF_decseq)
       (auto simp: mono_def fun_eq_iff intro!: arg_cong2[where f=emeasure] cong: measurable_cong_sets)
next
  show "\<And>x. g x \<le> (\<lambda>s. integral\<^sup>N (M s) (f top))"
    by (subst step)
       (auto simp add: top_fun_def less_le non_zero le_fun_def ennreal_top_mult
             cong del: if_weak_cong intro!: monoD[OF inf_continuous_mono[OF g], THEN le_funD])
next
  fix C assume "\<And>i::nat. C i \<in> borel_measurable N \<and> (\<forall>s. integral\<^sup>N (M s) (C i) < \<infinity>)" "decseq C"
  with bound show "Inf (C ` UNIV) \<in> borel_measurable N \<and> (\<forall>s. integral\<^sup>N (M s) (Inf (C ` UNIV)) < \<infinity>)"
    unfolding INF_apply[abs_def]
    by (subst nn_integral_monotone_convergence_INF_decseq)
       (auto simp: INF_less_iff cong: measurable_cong_sets intro!: borel_measurable_INF)
next
  show "\<And>x. x \<in> borel_measurable N \<and> (\<forall>s. integral\<^sup>N (M s) x < \<infinity>) \<Longrightarrow>
         (\<lambda>s. integral\<^sup>N (M s) (f x)) = g (\<lambda>s. integral\<^sup>N (M s) x)"
    by (subst step) auto
qed (insert bound, auto simp add: le_fun_def INF_apply[abs_def] top_fun_def intro!: meas f g)


text \<open>Cauchy--Schwarz inequality for \<^const>\<open>nn_integral\<close>\<close>

lemma sum_of_squares_ge_ennreal:
  fixes a b :: ennreal
  shows "2 * a * b \<le> a\<^sup>2 + b\<^sup>2"
proof (cases a; cases b)
  fix x y
  assume xy: "x \<ge> 0" "y \<ge> 0" and [simp]: "a = ennreal x" "b = ennreal y"
  have "0 \<le> (x - y)\<^sup>2"
    by simp
  also have "\<dots> = x\<^sup>2 + y\<^sup>2 - 2 * x * y"
    by (simp add: algebra_simps power2_eq_square)
  finally have "2 * x * y \<le> x\<^sup>2 + y\<^sup>2"
    by simp
  hence "ennreal (2 * x * y) \<le> ennreal (x\<^sup>2 + y\<^sup>2)"
    by (intro ennreal_leI)
  thus ?thesis using xy
    by (simp add: ennreal_mult ennreal_power)
qed auto

lemma Cauchy_Schwarz_nn_integral:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. f x * g x \<partial>M)\<^sup>2 \<le> (\<integral>\<^sup>+x. f x ^ 2 \<partial>M) * (\<integral>\<^sup>+x. g x ^ 2 \<partial>M)"
proof (cases "(\<integral>\<^sup>+x. f x * g x \<partial>M) = 0")
  case False
  define F where "F = nn_integral M (\<lambda>x. f x ^ 2)"
  define G where "G = nn_integral M (\<lambda>x. g x ^ 2)"
  from False have "\<not>(AE x in M. f x = 0 \<or> g x = 0)"
    by (auto simp: nn_integral_0_iff_AE)
  hence "\<not>(AE x in M. f x = 0)" and "\<not>(AE x in M. g x = 0)"
    by (auto intro: AE_disjI1 AE_disjI2)
  hence nz: "F \<noteq> 0" "G \<noteq> 0"
    by (auto simp: nn_integral_0_iff_AE F_def G_def)

  show ?thesis
  proof (cases "F = \<infinity> \<or> G = \<infinity>")
    case True
    thus ?thesis using nz
      by (auto simp: F_def G_def)
  next
    case False
    define F' where "F' = ennreal (sqrt (enn2real F))"
    define G' where "G' = ennreal (sqrt (enn2real G))"
    from False have fin: "F < top" "G < top"
      by (simp_all add: top.not_eq_extremum)
    have F'_sqr: "F'\<^sup>2 = F"
      using False by (cases F) (auto simp: F'_def ennreal_power)
    have G'_sqr: "G'\<^sup>2 = G"
      using False by (cases G) (auto simp: G'_def ennreal_power)
    have nz': "F' \<noteq> 0" "G' \<noteq> 0" and fin': "F' \<noteq> \<infinity>" "G' \<noteq> \<infinity>"
      using F'_sqr G'_sqr nz fin by auto
    from fin' have fin'': "F' < top" "G' < top"
      by (auto simp: top.not_eq_extremum)

    have "2 * (F' / F') * (G' / G') * (\<integral>\<^sup>+x. f x * g x \<partial>M) =
          F' * G' * (\<integral>\<^sup>+x. 2 * (f x / F') * (g x / G') \<partial>M)"
      using nz' fin''
      by (simp add: divide_ennreal_def algebra_simps ennreal_inverse_mult flip: nn_integral_cmult)
    also have "F'/ F' = 1"
      using nz' fin'' by simp
    also have "G'/ G' = 1"
      using nz' fin'' by simp
    also have "2 * 1 * 1 = (2 :: ennreal)" by simp
    also have "F' * G' * (\<integral>\<^sup>+ x. 2 * (f x / F') * (g x / G') \<partial>M) \<le>
               F' * G' * (\<integral>\<^sup>+x. (f x / F')\<^sup>2 + (g x / G')\<^sup>2 \<partial>M)"
      by (intro mult_left_mono nn_integral_mono sum_of_squares_ge_ennreal) auto
    also have "\<dots> = F' * G' * (F / F'\<^sup>2 + G / G'\<^sup>2)" using nz
      by (auto simp: nn_integral_add algebra_simps nn_integral_divide F_def G_def)
    also have "F / F'\<^sup>2 = 1"
      using nz F'_sqr fin by simp
    also have "G / G'\<^sup>2 = 1"
      using nz G'_sqr fin by simp
    also have "F' * G' * (1 + 1) = 2 * (F' * G')"
      by (simp add: mult_ac)
    finally have "(\<integral>\<^sup>+x. f x * g x \<partial>M) \<le> F' * G'"
      by (subst (asm) ennreal_mult_le_mult_iff) auto
    hence "(\<integral>\<^sup>+x. f x * g x \<partial>M)\<^sup>2 \<le> (F' * G')\<^sup>2"
      by (intro power_mono_ennreal)
    also have "\<dots> = F * G"
      by (simp add: algebra_simps F'_sqr G'_sqr)
    finally show ?thesis
      by (simp add: F_def G_def)
  qed
qed auto


(* TODO: rename? *)
subsection \<open>Integral under concrete measures\<close>

lemma nn_integral_mono_measure:
  assumes "sets M = sets N" "M \<le> N" shows "nn_integral M f \<le> nn_integral N f"
  unfolding nn_integral_def
proof (intro SUP_subset_mono)
  note \<open>sets M = sets N\<close>[simp]  \<open>sets M = sets N\<close>[THEN sets_eq_imp_space_eq, simp]
  show "{g. simple_function M g \<and> g \<le> f} \<subseteq> {g. simple_function N g \<and> g \<le> f}"
    by (simp add: simple_function_def)
  show "integral\<^sup>S M x \<le> integral\<^sup>S N x" for x
    using le_measureD3[OF \<open>M \<le> N\<close>]
    by (auto simp add: simple_integral_def intro!: sum_mono mult_mono)
qed

lemma nn_integral_empty:
  assumes "space M = {}"
  shows "nn_integral M f = 0"
proof -
  have "(\<integral>\<^sup>+ x. f x \<partial>M) = (\<integral>\<^sup>+ x. 0 \<partial>M)"
    by(rule nn_integral_cong)(simp add: assms)
  thus ?thesis by simp
qed

lemma nn_integral_bot[simp]: "nn_integral bot f = 0"
  by (simp add: nn_integral_empty)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Distributions\<close>

lemma nn_integral_distr:
  assumes T: "T \<in> measurable M M'" and f: "f \<in> borel_measurable (distr M M' T)"
  shows "integral\<^sup>N (distr M M' T) f = (\<integral>\<^sup>+ x. f (T x) \<partial>M)"
  using f
proof induct
  case (cong f g)
  with T show ?case
    apply (subst nn_integral_cong[of _ f g])
    apply simp
    apply (subst nn_integral_cong[of _ "\<lambda>x. f (T x)" "\<lambda>x. g (T x)"])
    apply (simp add: measurable_def Pi_iff)
    apply simp
    done
next
  case (set A)
  then have eq: "\<And>x. x \<in> space M \<Longrightarrow> indicator A (T x) = indicator (T -` A \<inter> space M) x"
    by (auto simp: indicator_def)
  from set T show ?case
    by (subst nn_integral_cong[OF eq])
       (auto simp add: emeasure_distr intro!: nn_integral_indicator[symmetric] measurable_sets)
qed (simp_all add: measurable_compose[OF T] T nn_integral_cmult nn_integral_add
                   nn_integral_monotone_convergence_SUP le_fun_def incseq_def image_comp)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Counting space\<close>

lemma simple_function_count_space[simp]:
  "simple_function (count_space A) f \<longleftrightarrow> finite (f ` A)"
  unfolding simple_function_def by simp

lemma nn_integral_count_space:
  assumes A: "finite {a\<in>A. 0 < f a}"
  shows "integral\<^sup>N (count_space A) f = (\<Sum>a|a\<in>A \<and> 0 < f a. f a)"
proof -
  have *: "(\<integral>\<^sup>+x. max 0 (f x) \<partial>count_space A) =
    (\<integral>\<^sup>+ x. (\<Sum>a|a\<in>A \<and> 0 < f a. f a * indicator {a} x) \<partial>count_space A)"
    by (auto intro!: nn_integral_cong
             simp add: indicator_def of_bool_def if_distrib sum.If_cases[OF A] max_def le_less)
  also have "\<dots> = (\<Sum>a|a\<in>A \<and> 0 < f a. \<integral>\<^sup>+ x. f a * indicator {a} x \<partial>count_space A)"
    by (subst nn_integral_sum) (simp_all add: AE_count_space  less_imp_le)
  also have "\<dots> = (\<Sum>a|a\<in>A \<and> 0 < f a. f a)"
    by (auto intro!: sum.cong simp: one_ennreal_def[symmetric] max_def)
  finally show ?thesis by (simp add: max.absorb2)
qed

lemma nn_integral_count_space_finite:
    "finite A \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space A) = (\<Sum>a\<in>A. f a)"
  by (auto intro!: sum.mono_neutral_left simp: nn_integral_count_space less_le)

lemma nn_integral_count_space':
  assumes "finite A" "\<And>x. x \<in> B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = 0" "A \<subseteq> B"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space B) = (\<Sum>x\<in>A. f x)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>count_space B) = (\<Sum>a | a \<in> B \<and> 0 < f a. f a)"
    using assms(2,3)
    by (intro nn_integral_count_space finite_subset[OF _ \<open>finite A\<close>]) (auto simp: less_le)
  also have "\<dots> = (\<Sum>a\<in>A. f a)"
    using assms by (intro sum.mono_neutral_cong_left) (auto simp: less_le)
  finally show ?thesis .
qed

lemma nn_integral_bij_count_space:
  assumes g: "bij_betw g A B"
  shows "(\<integral>\<^sup>+x. f (g x) \<partial>count_space A) = (\<integral>\<^sup>+x. f x \<partial>count_space B)"
  using g[THEN bij_betw_imp_funcset]
  by (subst distr_bij_count_space[OF g, symmetric])
     (auto intro!: nn_integral_distr[symmetric])

lemma nn_integral_indicator_finite:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes f: "finite A" and [measurable]: "\<And>a. a \<in> A \<Longrightarrow> {a} \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<Sum>x\<in>A. f x * emeasure M {x})"
proof -
  from f have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>a\<in>A. f a * indicator {a} x) \<partial>M)"
    by (intro nn_integral_cong) (auto simp: indicator_def if_distrib[where f="\<lambda>a. x * a" for x] sum.If_cases)
  also have "\<dots> = (\<Sum>a\<in>A. f a * emeasure M {a})"
    by (subst nn_integral_sum) auto
  finally show ?thesis .
qed

lemma nn_integral_count_space_nat:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<integral>\<^sup>+i. f i \<partial>count_space UNIV) = (\<Sum>i. f i)"
proof -
  have "(\<integral>\<^sup>+i. f i \<partial>count_space UNIV) =
    (\<integral>\<^sup>+i. (\<Sum>j. f j * indicator {j} i) \<partial>count_space UNIV)"
  proof (intro nn_integral_cong)
    fix i
    have "f i = (\<Sum>j\<in>{i}. f j * indicator {j} i)"
      by simp
    also have "\<dots> = (\<Sum>j. f j * indicator {j} i)"
      by (rule suminf_finite[symmetric]) auto
    finally show "f i = (\<Sum>j. f j * indicator {j} i)" .
  qed
  also have "\<dots> = (\<Sum>j. (\<integral>\<^sup>+i. f j * indicator {j} i \<partial>count_space UNIV))"
    by (rule nn_integral_suminf) auto
  finally show ?thesis
    by simp
qed

lemma nn_integral_enat_function:
  assumes f: "f \<in> measurable M (count_space UNIV)"
  shows "(\<integral>\<^sup>+ x. ennreal_of_enat (f x) \<partial>M) = (\<Sum>t. emeasure M {x \<in> space M. t < f x})"
proof -
  define F where "F i = {x\<in>space M. i < f x}" for i :: nat
  with assms have [measurable]: "\<And>i. F i \<in> sets M"
    by auto

  { fix x assume "x \<in> space M"
    have "(\<lambda>i::nat. if i < f x then 1 else 0) sums ennreal_of_enat (f x)"
      using sums_If_finite[of "\<lambda>r. r < f x" "\<lambda>_. 1 :: ennreal"]
      by (cases "f x") (simp_all add: sums_def of_nat_tendsto_top_ennreal)
    also have "(\<lambda>i. (if i < f x then 1 else 0)) = (\<lambda>i. indicator (F i) x)"
      using \<open>x \<in> space M\<close> by (simp add: one_ennreal_def F_def fun_eq_iff)
    finally have "ennreal_of_enat (f x) = (\<Sum>i. indicator (F i) x)"
      by (simp add: sums_iff) }
  then have "(\<integral>\<^sup>+x. ennreal_of_enat (f x) \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>i. indicator (F i) x) \<partial>M)"
    by (simp cong: nn_integral_cong)
  also have "\<dots> = (\<Sum>i. emeasure M (F i))"
    by (simp add: nn_integral_suminf)
  finally show ?thesis
    by (simp add: F_def)
qed

lemma nn_integral_count_space_nn_integral:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes "countable I" and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. \<integral>\<^sup>+i. f i x \<partial>count_space I \<partial>M) = (\<integral>\<^sup>+i. \<integral>\<^sup>+x. f i x \<partial>M \<partial>count_space I)"
proof cases
  assume "finite I" then show ?thesis
    by (simp add: nn_integral_count_space_finite nn_integral_sum)
next
  assume "infinite I"
  then have [simp]: "I \<noteq> {}"
    by auto
  note * = bij_betw_from_nat_into[OF \<open>countable I\<close> \<open>infinite I\<close>]
  have **: "\<And>f. (\<And>i. 0 \<le> f i) \<Longrightarrow> (\<integral>\<^sup>+i. f i \<partial>count_space I) = (\<Sum>n. f (from_nat_into I n))"
    by (simp add: nn_integral_bij_count_space[symmetric, OF *] nn_integral_count_space_nat)
  show ?thesis
    by (simp add: ** nn_integral_suminf from_nat_into)
qed

lemma of_bool_Bex_eq_nn_integral:
  assumes unique: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> x = y"
  shows "of_bool (\<exists>y\<in>X. P y) = (\<integral>\<^sup>+y. of_bool (P y) \<partial>count_space X)"
proof cases
  assume "\<exists>y\<in>X. P y"
  then obtain y where "P y" "y \<in> X" by auto
  then show ?thesis
    by (subst nn_integral_count_space'[where A="{y}"]) (auto dest: unique)
qed (auto cong: nn_integral_cong_simp)

lemma emeasure_UN_countable:
  assumes sets[measurable]: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> sets M" and I[simp]: "countable I"
  assumes disj: "disjoint_family_on X I"
  shows "emeasure M (\<Union>(X ` I)) = (\<integral>\<^sup>+i. emeasure M (X i) \<partial>count_space I)"
proof -
  have eq: "\<And>x. indicator (\<Union>(X ` I)) x = \<integral>\<^sup>+ i. indicator (X i) x \<partial>count_space I"
  proof cases
    fix x assume x: "x \<in> \<Union>(X ` I)"
    then obtain j where j: "x \<in> X j" "j \<in> I"
      by auto
    with disj have "\<And>i. i \<in> I \<Longrightarrow> indicator (X i) x = (indicator {j} i::ennreal)"
      by (auto simp: disjoint_family_on_def split: split_indicator)
    with x j show "?thesis x"
      by (simp cong: nn_integral_cong_simp)
  qed (auto simp: nn_integral_0_iff_AE)

  note sets.countable_UN'[unfolded subset_eq, measurable]
  have "emeasure M (\<Union>(X ` I)) = (\<integral>\<^sup>+x. indicator (\<Union>(X ` I)) x \<partial>M)"
    by simp
  also have "\<dots> = (\<integral>\<^sup>+i. \<integral>\<^sup>+x. indicator (X i) x \<partial>M \<partial>count_space I)"
    by (simp add: eq nn_integral_count_space_nn_integral)
  finally show ?thesis
    by (simp cong: nn_integral_cong_simp)
qed

lemma emeasure_countable_singleton:
  assumes sets: "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M" and X: "countable X"
  shows "emeasure M X = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space X)"
proof -
  have "emeasure M (\<Union>i\<in>X. {i}) = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space X)"
    using assms by (intro emeasure_UN_countable) (auto simp: disjoint_family_on_def)
  also have "(\<Union>i\<in>X. {i}) = X" by auto
  finally show ?thesis .
qed

lemma measure_eqI_countable:
  assumes [simp]: "sets M = Pow A" "sets N = Pow A" and A: "countable A"
  assumes eq: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} = emeasure N {a}"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume "X \<in> sets M"
  then have X: "X \<subseteq> A" by auto
  moreover from A X have "countable X" by (auto dest: countable_subset)
  ultimately have
    "emeasure M X = (\<integral>\<^sup>+a. emeasure M {a} \<partial>count_space X)"
    "emeasure N X = (\<integral>\<^sup>+a. emeasure N {a} \<partial>count_space X)"
    by (auto intro!: emeasure_countable_singleton)
  moreover have "(\<integral>\<^sup>+a. emeasure M {a} \<partial>count_space X) = (\<integral>\<^sup>+a. emeasure N {a} \<partial>count_space X)"
    using X by (intro nn_integral_cong eq) auto
  ultimately show "emeasure M X = emeasure N X"
    by simp
qed simp

lemma measure_eqI_countable_AE:
  assumes [simp]: "sets M = UNIV" "sets N = UNIV"
  assumes ae: "AE x in M. x \<in> \<Omega>" "AE x in N. x \<in> \<Omega>" and [simp]: "countable \<Omega>"
  assumes eq: "\<And>x. x \<in> \<Omega> \<Longrightarrow> emeasure M {x} = emeasure N {x}"
  shows "M = N"
proof (rule measure_eqI)
  fix A
  have "emeasure N A = emeasure N {x\<in>\<Omega>. x \<in> A}"
    using ae by (intro emeasure_eq_AE) auto
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure N {x} \<partial>count_space {x\<in>\<Omega>. x \<in> A})"
    by (intro emeasure_countable_singleton) auto
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space {x\<in>\<Omega>. x \<in> A})"
    by (intro nn_integral_cong eq[symmetric]) auto
  also have "\<dots> = emeasure M {x\<in>\<Omega>. x \<in> A}"
    by (intro emeasure_countable_singleton[symmetric]) auto
  also have "\<dots> = emeasure M A"
    using ae by (intro emeasure_eq_AE) auto
  finally show "emeasure M A = emeasure N A" ..
qed simp

lemma nn_integral_monotone_convergence_SUP_nat:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> ennreal"
  assumes chain: "Complete_Partial_Order.chain (\<le>) (f ` Y)"
  and nonempty: "Y \<noteq> {}"
  shows "(\<integral>\<^sup>+ x. (SUP i\<in>Y. f i x) \<partial>count_space UNIV) = (SUP i\<in>Y. (\<integral>\<^sup>+ x. f i x \<partial>count_space UNIV))"
  (is "?lhs = ?rhs" is "integral\<^sup>N ?M _ = _")
proof (rule order_class.order.antisym)
  show "?rhs \<le> ?lhs"
    by (auto intro!: SUP_least SUP_upper nn_integral_mono)
next
  have "\<exists>g. incseq g \<and> range g \<subseteq> (\<lambda>i. f i x) ` Y \<and> (SUP i\<in>Y. f i x) = (SUP i. g i)" for x
    by (rule ennreal_Sup_countable_SUP) (simp add: nonempty)
  then obtain g where incseq: "\<And>x. incseq (g x)"
    and range: "\<And>x. range (g x) \<subseteq> (\<lambda>i. f i x) ` Y"
    and sup: "\<And>x. (SUP i\<in>Y. f i x) = (SUP i. g x i)" by moura
  from incseq have incseq': "incseq (\<lambda>i x. g x i)"
    by(blast intro: incseq_SucI le_funI dest: incseq_SucD)

  have "?lhs = \<integral>\<^sup>+ x. (SUP i. g x i) \<partial>?M" by(simp add: sup)
  also have "\<dots> = (SUP i. \<integral>\<^sup>+ x. g x i \<partial>?M)" using incseq'
    by(rule nn_integral_monotone_convergence_SUP) simp
  also have "\<dots> \<le> (SUP i\<in>Y. \<integral>\<^sup>+ x. f i x \<partial>?M)"
  proof(rule SUP_least)
    fix n
    have "\<And>x. \<exists>i. g x n = f i x \<and> i \<in> Y" using range by blast
    then obtain I where I: "\<And>x. g x n = f (I x) x" "\<And>x. I x \<in> Y" by moura

    have "(\<integral>\<^sup>+ x. g x n \<partial>count_space UNIV) = (\<Sum>x. g x n)"
      by(rule nn_integral_count_space_nat)
    also have "\<dots> = (SUP m. \<Sum>x<m. g x n)"
      by(rule suminf_eq_SUP)
    also have "\<dots> \<le> (SUP i\<in>Y. \<integral>\<^sup>+ x. f i x \<partial>?M)"
    proof(rule SUP_mono)
      fix m
      show "\<exists>m'\<in>Y. (\<Sum>x<m. g x n) \<le> (\<integral>\<^sup>+ x. f m' x \<partial>?M)"
      proof(cases "m > 0")
        case False
        thus ?thesis using nonempty by auto
      next
        case True
        let ?Y = "I ` {..<m}"
        have "f ` ?Y \<subseteq> f ` Y" using I by auto
        with chain have chain': "Complete_Partial_Order.chain (\<le>) (f ` ?Y)" by(rule chain_subset)
        hence "Sup (f ` ?Y) \<in> f ` ?Y"
          by(rule ccpo_class.in_chain_finite)(auto simp add: True lessThan_empty_iff)
        then obtain m' where "m' < m" and m': "(SUP i\<in>?Y. f i) = f (I m')" by auto
        have "I m' \<in> Y" using I by blast
        have "(\<Sum>x<m. g x n) \<le> (\<Sum>x<m. f (I m') x)"
        proof(rule sum_mono)
          fix x
          assume "x \<in> {..<m}"
          hence "x < m" by simp
          have "g x n = f (I x) x" by(simp add: I)
          also have "\<dots> \<le> (SUP i\<in>?Y. f i) x" unfolding Sup_fun_def image_image
            using \<open>x \<in> {..<m}\<close> by (rule Sup_upper [OF imageI])
          also have "\<dots> = f (I m') x" unfolding m' by simp
          finally show "g x n \<le> f (I m') x" .
        qed
        also have "\<dots> \<le> (SUP m. (\<Sum>x<m. f (I m') x))"
          by(rule SUP_upper) simp
        also have "\<dots> = (\<Sum>x. f (I m') x)"
          by(rule suminf_eq_SUP[symmetric])
        also have "\<dots> = (\<integral>\<^sup>+ x. f (I m') x \<partial>?M)"
          by(rule nn_integral_count_space_nat[symmetric])
        finally show ?thesis using \<open>I m' \<in> Y\<close> by blast
      qed
    qed
    finally show "(\<integral>\<^sup>+ x. g x n \<partial>count_space UNIV) \<le> \<dots>" .
  qed
  finally show "?lhs \<le> ?rhs" .
qed

lemma power_series_tendsto_at_left:
  assumes nonneg: "\<And>i. 0 \<le> f i" and summable: "\<And>z. 0 \<le> z \<Longrightarrow> z < 1 \<Longrightarrow> summable (\<lambda>n. f n * z^n)"
  shows "((\<lambda>z. ennreal (\<Sum>n. f n * z^n)) \<longlongrightarrow> (\<Sum>n. ennreal (f n))) (at_left (1::real))"
proof (intro tendsto_at_left_sequentially)
  show "0 < (1::real)" by simp
  fix S :: "nat \<Rightarrow> real" assume S: "\<And>n. S n < 1" "\<And>n. 0 < S n" "S \<longlonglongrightarrow> 1" "incseq S"
  then have S_nonneg: "\<And>i. 0 \<le> S i" by (auto intro: less_imp_le)

  have "(\<lambda>i. (\<integral>\<^sup>+n. f n * S i^n \<partial>count_space UNIV)) \<longlonglongrightarrow> (\<integral>\<^sup>+n. ennreal (f n) \<partial>count_space UNIV)"
  proof (rule nn_integral_LIMSEQ)
    show "incseq (\<lambda>i n. ennreal (f n * S i^n))"
      using S by (auto intro!: mult_mono power_mono nonneg ennreal_leI
                       simp: incseq_def le_fun_def less_imp_le)
    fix n have "(\<lambda>i. ennreal (f n * S i^n)) \<longlonglongrightarrow> ennreal (f n * 1^n)"
      by (intro tendsto_intros tendsto_ennrealI S)
    then show "(\<lambda>i. ennreal (f n * S i^n)) \<longlonglongrightarrow> ennreal (f n)"
      by simp
  qed (auto simp: S_nonneg intro!: mult_nonneg_nonneg nonneg)
  also have "(\<lambda>i. (\<integral>\<^sup>+n. f n * S i^n \<partial>count_space UNIV)) = (\<lambda>i. \<Sum>n. f n * S i^n)"
    by (subst nn_integral_count_space_nat)
       (intro ext suminf_ennreal2 mult_nonneg_nonneg nonneg S_nonneg
              zero_le_power summable S)+
  also have "(\<integral>\<^sup>+n. ennreal (f n) \<partial>count_space UNIV) = (\<Sum>n. ennreal (f n))"
    by (simp add: nn_integral_count_space_nat nonneg)
  finally show "(\<lambda>n. ennreal (\<Sum>na. f na * S n ^ na)) \<longlonglongrightarrow> (\<Sum>n. ennreal (f n))" .
qed

subsubsection \<open>Measures with Restricted Space\<close>

lemma simple_function_restrict_space_ennreal:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "simple_function (restrict_space M \<Omega>) f \<longleftrightarrow> simple_function M (\<lambda>x. f x * indicator \<Omega> x)"
proof -
  { assume "finite (f ` space (restrict_space M \<Omega>))"
    then have "finite (f ` space (restrict_space M \<Omega>) \<union> {0})" by simp
    then have "finite ((\<lambda>x. f x * indicator \<Omega> x) ` space M)"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  moreover
  { assume "finite ((\<lambda>x. f x * indicator \<Omega> x) ` space M)"
    then have "finite (f ` space (restrict_space M \<Omega>))"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  ultimately show ?thesis
    unfolding
      simple_function_iff_borel_measurable borel_measurable_restrict_space_iff_ennreal[OF assms]
    by auto
qed

lemma simple_function_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "simple_function (restrict_space M \<Omega>) f \<longleftrightarrow> simple_function M (\<lambda>x. indicator \<Omega> x *\<^sub>R f x)"
proof -
  { assume "finite (f ` space (restrict_space M \<Omega>))"
    then have "finite (f ` space (restrict_space M \<Omega>) \<union> {0})" by simp
    then have "finite ((\<lambda>x. indicator \<Omega> x *\<^sub>R f x) ` space M)"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  moreover
  { assume "finite ((\<lambda>x. indicator \<Omega> x *\<^sub>R f x) ` space M)"
    then have "finite (f ` space (restrict_space M \<Omega>))"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  ultimately show ?thesis
    unfolding simple_function_iff_borel_measurable
      borel_measurable_restrict_space_iff[OF assms]
    by auto
qed

lemma simple_integral_restrict_space:
  assumes \<Omega>: "\<Omega> \<inter> space M \<in> sets M" "simple_function (restrict_space M \<Omega>) f"
  shows "simple_integral (restrict_space M \<Omega>) f = simple_integral M (\<lambda>x. f x * indicator \<Omega> x)"
  using simple_function_restrict_space_ennreal[THEN iffD1, OF \<Omega>, THEN simple_functionD(1)]
  by (auto simp add: space_restrict_space emeasure_restrict_space[OF \<Omega>(1)] le_infI2 simple_integral_def
           split: split_indicator split_indicator_asm
           intro!: sum.mono_neutral_cong_left ennreal_mult_left_cong arg_cong2[where f=emeasure])

lemma nn_integral_restrict_space:
  assumes \<Omega>[simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "nn_integral (restrict_space M \<Omega>) f = nn_integral M (\<lambda>x. f x * indicator \<Omega> x)"
proof -
  let ?R = "restrict_space M \<Omega>" and ?X = "\<lambda>M f. {s. simple_function M s \<and> s \<le> f \<and> (\<forall>x. s x < top)}"
  have "integral\<^sup>S ?R ` ?X ?R f = integral\<^sup>S M ` ?X M (\<lambda>x. f x * indicator \<Omega> x)"
  proof (safe intro!: image_eqI)
    fix s assume s: "simple_function ?R s" "s \<le> f" "\<forall>x. s x < top"
    from s show "integral\<^sup>S (restrict_space M \<Omega>) s = integral\<^sup>S M (\<lambda>x. s x * indicator \<Omega> x)"
      by (intro simple_integral_restrict_space) auto
    from s show "simple_function M (\<lambda>x. s x * indicator \<Omega> x)"
      by (simp add: simple_function_restrict_space_ennreal)
    from s show "(\<lambda>x. s x * indicator \<Omega> x) \<le> (\<lambda>x. f x * indicator \<Omega> x)"
      "\<And>x. s x * indicator \<Omega> x < top"
      by (auto split: split_indicator simp: le_fun_def image_subset_iff)
  next
    fix s assume s: "simple_function M s" "s \<le> (\<lambda>x. f x * indicator \<Omega> x)" "\<forall>x. s x < top"
    then have "simple_function M (\<lambda>x. s x * indicator (\<Omega> \<inter> space M) x)" (is ?s')
      by (intro simple_function_mult simple_function_indicator) auto
    also have "?s' \<longleftrightarrow> simple_function M (\<lambda>x. s x * indicator \<Omega> x)"
      by (rule simple_function_cong) (auto split: split_indicator)
    finally show sf: "simple_function (restrict_space M \<Omega>) s"
      by (simp add: simple_function_restrict_space_ennreal)

    from s have s_eq: "s = (\<lambda>x. s x * indicator \<Omega> x)"
      by (auto simp add: fun_eq_iff le_fun_def image_subset_iff
                  split: split_indicator split_indicator_asm
                  intro: antisym)

    show "integral\<^sup>S M s = integral\<^sup>S (restrict_space M \<Omega>) s"
      by (subst s_eq) (rule simple_integral_restrict_space[symmetric, OF \<Omega> sf])
    show "\<And>x. s x < top"
      using s by (auto simp: image_subset_iff)
    from s show "s \<le> f"
      by (subst s_eq) (auto simp: image_subset_iff le_fun_def split: split_indicator split_indicator_asm)
  qed
  then show ?thesis
    unfolding nn_integral_def_finite by (simp cong del: SUP_cong_simp)
qed

lemma nn_integral_count_space_indicator:
  assumes "NO_MATCH (UNIV::'a set) (X::'a set)"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space X) = (\<integral>\<^sup>+x. f x * indicator X x \<partial>count_space UNIV)"
  by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)

lemma nn_integral_count_space_eq:
  "(\<And>x. x \<in> A - B \<Longrightarrow> f x = 0) \<Longrightarrow> (\<And>x. x \<in> B - A \<Longrightarrow> f x = 0) \<Longrightarrow>
    (\<integral>\<^sup>+x. f x \<partial>count_space A) = (\<integral>\<^sup>+x. f x \<partial>count_space B)"
  by (auto simp: nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)

lemma nn_integral_ge_point:
  assumes "x \<in> A"
  shows "p x \<le> \<integral>\<^sup>+ x. p x \<partial>count_space A"
proof -
  from assms have "p x \<le> \<integral>\<^sup>+ x. p x \<partial>count_space {x}"
    by(auto simp add: nn_integral_count_space_finite max_def)
  also have "\<dots> = \<integral>\<^sup>+ x'. p x' * indicator {x} x' \<partial>count_space A"
    using assms by(auto simp add: nn_integral_count_space_indicator indicator_def intro!: nn_integral_cong)
  also have "\<dots> \<le> \<integral>\<^sup>+ x. p x \<partial>count_space A"
    by(rule nn_integral_mono)(simp add: indicator_def)
  finally show ?thesis .
qed

subsubsection \<open>Measure spaces with an associated density\<close>

definition\<^marker>\<open>tag important\<close> density :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a measure" where
  "density M f = measure_of (space M) (sets M) (\<lambda>A. \<integral>\<^sup>+ x. f x * indicator A x \<partial>M)"

lemma
  shows sets_density[simp, measurable_cong]: "sets (density M f) = sets M"
    and space_density[simp]: "space (density M f) = space M"
  by (auto simp: density_def)

(* FIXME: add conversion to simplify space, sets and measurable *)
lemma space_density_imp[measurable_dest]:
  "\<And>x M f. x \<in> space (density M f) \<Longrightarrow> x \<in> space M" by auto

lemma
  shows measurable_density_eq1[simp]: "g \<in> measurable (density Mg f) Mg' \<longleftrightarrow> g \<in> measurable Mg Mg'"
    and measurable_density_eq2[simp]: "h \<in> measurable Mh (density Mh' f) \<longleftrightarrow> h \<in> measurable Mh Mh'"
    and simple_function_density_eq[simp]: "simple_function (density Mu f) u \<longleftrightarrow> simple_function Mu u"
  unfolding measurable_def simple_function_def by simp_all

lemma density_cong: "f \<in> borel_measurable M \<Longrightarrow> f' \<in> borel_measurable M \<Longrightarrow>
  (AE x in M. f x = f' x) \<Longrightarrow> density M f = density M f'"
  unfolding density_def by (auto intro!: measure_of_eq nn_integral_cong_AE sets.space_closed)

lemma emeasure_density:
  assumes f[measurable]: "f \<in> borel_measurable M" and A[measurable]: "A \<in> sets M"
  shows "emeasure (density M f) A = (\<integral>\<^sup>+ x. f x * indicator A x \<partial>M)"
    (is "_ = ?\<mu> A")
  unfolding density_def
proof (rule emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)" ..
  show "positive (sets M) ?\<mu>"
    using f by (auto simp: positive_def)
  show "countably_additive (sets M) ?\<mu>"
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets M"
    then have "\<And>i. A i \<in> sets M" by auto
    then have *: "\<And>i. (\<lambda>x. f x * indicator (A i) x) \<in> borel_measurable M"
      by auto
    assume disj: "disjoint_family A"
    then have "(\<Sum>n. ?\<mu> (A n)) = (\<integral>\<^sup>+ x. (\<Sum>n. f x * indicator (A n) x) \<partial>M)"
       using f * by (subst nn_integral_suminf) auto
    also have "(\<integral>\<^sup>+ x. (\<Sum>n. f x * indicator (A n) x) \<partial>M) = (\<integral>\<^sup>+ x. f x * (\<Sum>n. indicator (A n) x) \<partial>M)"
      using f by (auto intro!: ennreal_suminf_cmult nn_integral_cong_AE)
    also have "\<dots> = (\<integral>\<^sup>+ x. f x * indicator (\<Union>n. A n) x \<partial>M)"
      unfolding suminf_indicator[OF disj] ..
    finally show "(\<Sum>i. \<integral>\<^sup>+ x. f x * indicator (A i) x \<partial>M) = \<integral>\<^sup>+ x. f x * indicator (\<Union>i. A i) x \<partial>M" .
  qed
qed fact

lemma null_sets_density_iff:
  assumes f: "f \<in> borel_measurable M"
  shows "A \<in> null_sets (density M f) \<longleftrightarrow> A \<in> sets M \<and> (AE x in M. x \<in> A \<longrightarrow> f x = 0)"
proof -
  { assume "A \<in> sets M"
    have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = 0 \<longleftrightarrow> emeasure M {x \<in> space M. f x * indicator A x \<noteq> 0} = 0"
      using f \<open>A \<in> sets M\<close> by (intro nn_integral_0_iff) auto
    also have "\<dots> \<longleftrightarrow> (AE x in M. f x * indicator A x = 0)"
      using f \<open>A \<in> sets M\<close> by (intro AE_iff_measurable[OF _ refl, symmetric]) auto
    also have "(AE x in M. f x * indicator A x = 0) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)"
      by (auto simp add: indicator_def max_def split: if_split_asm)
    finally have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = 0 \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)" . }
  with f show ?thesis
    by (simp add: null_sets_def emeasure_density cong: conj_cong)
qed

lemma AE_density:
  assumes f: "f \<in> borel_measurable M"
  shows "(AE x in density M f. P x) \<longleftrightarrow> (AE x in M. 0 < f x \<longrightarrow> P x)"
proof
  assume "AE x in density M f. P x"
  with f obtain N where "{x \<in> space M. \<not> P x} \<subseteq> N" "N \<in> sets M" and ae: "AE x in M. x \<in> N \<longrightarrow> f x = 0"
    by (auto simp: eventually_ae_filter null_sets_density_iff)
  then have "AE x in M. x \<notin> N \<longrightarrow> P x" by auto
  with ae show "AE x in M. 0 < f x \<longrightarrow> P x"
    by (rule eventually_elim2) auto
next
  fix N assume ae: "AE x in M. 0 < f x \<longrightarrow> P x"
  then obtain N where "{x \<in> space M. \<not> (0 < f x \<longrightarrow> P x)} \<subseteq> N" "N \<in> null_sets M"
    by (auto simp: eventually_ae_filter)
  then have *: "{x \<in> space (density M f). \<not> P x} \<subseteq> N \<union> {x\<in>space M. f x = 0}"
    "N \<union> {x\<in>space M. f x = 0} \<in> sets M" and ae2: "AE x in M. x \<notin> N"
    using f by (auto simp: subset_eq zero_less_iff_neq_zero intro!: AE_not_in)
  show "AE x in density M f. P x"
    using ae2
    unfolding eventually_ae_filter[of _ "density M f"] Bex_def null_sets_density_iff[OF f]
    by (intro exI[of _ "N \<union> {x\<in>space M. f x = 0}"] conjI *) (auto elim: eventually_elim2)
qed

lemma\<^marker>\<open>tag important\<close> nn_integral_density:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "integral\<^sup>N (density M f) g = (\<integral>\<^sup>+ x. f x * g x \<partial>M)"
using g proof induct
  case (cong u v)
  then show ?case
    apply (subst nn_integral_cong[OF cong(3)])
    apply (simp_all cong: nn_integral_cong)
    done
next
  case (set A) then show ?case
    by (simp add: emeasure_density f)
next
  case (mult u c)
  moreover have "\<And>x. f x * (c * u x) = c * (f x * u x)" by (simp add: field_simps)
  ultimately show ?case
    using f by (simp add: nn_integral_cmult)
next
  case (add u v)
  then have "\<And>x. f x * (v x + u x) = f x * v x + f x * u x"
    by (simp add: distrib_left)
  with add f show ?case
    by (auto simp add: nn_integral_add intro!: nn_integral_add[symmetric])
next
  case (seq U)
  have eq: "AE x in M. f x * (SUP i. U i x) = (SUP i. f x * U i x)"
    by eventually_elim (simp add: SUP_mult_left_ennreal seq)
  from seq f show ?case
    apply (simp add: nn_integral_monotone_convergence_SUP image_comp)
    apply (subst nn_integral_cong_AE[OF eq])
    apply (subst nn_integral_monotone_convergence_SUP_AE)
    apply (auto simp: incseq_def le_fun_def intro!: mult_left_mono)
    done
qed

lemma density_distr:
  assumes [measurable]: "f \<in> borel_measurable N" "X \<in> measurable M N"
  shows "density (distr M N X) f = distr (density M (\<lambda>x. f (X x))) N X"
  by (intro measure_eqI)
     (auto simp add: emeasure_density nn_integral_distr emeasure_distr
           split: split_indicator intro!: nn_integral_cong)

lemma emeasure_restricted:
  assumes S: "S \<in> sets M" and X: "X \<in> sets M"
  shows "emeasure (density M (indicator S)) X = emeasure M (S \<inter> X)"
proof -
  have "emeasure (density M (indicator S)) X = (\<integral>\<^sup>+x. indicator S x * indicator X x \<partial>M)"
    using S X by (simp add: emeasure_density)
  also have "\<dots> = (\<integral>\<^sup>+x. indicator (S \<inter> X) x \<partial>M)"
    by (auto intro!: nn_integral_cong simp: indicator_def)
  also have "\<dots> = emeasure M (S \<inter> X)"
    using S X by (simp add: sets.Int)
  finally show ?thesis .
qed

lemma measure_restricted:
  "S \<in> sets M \<Longrightarrow> X \<in> sets M \<Longrightarrow> measure (density M (indicator S)) X = measure M (S \<inter> X)"
  by (simp add: emeasure_restricted measure_def)

lemma (in finite_measure) finite_measure_restricted:
  "S \<in> sets M \<Longrightarrow> finite_measure (density M (indicator S))"
  by standard (simp add: emeasure_restricted)

lemma emeasure_density_const:
  "A \<in> sets M \<Longrightarrow> emeasure (density M (\<lambda>_. c)) A = c * emeasure M A"
  by (auto simp: nn_integral_cmult_indicator emeasure_density)

lemma measure_density_const:
  "A \<in> sets M \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow> measure (density M (\<lambda>_. c)) A = enn2real c * measure M A"
  by (auto simp: emeasure_density_const measure_def enn2real_mult)

lemma density_density_eq:
   "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
   density (density M f) g = density M (\<lambda>x. f x * g x)"
  by (auto intro!: measure_eqI simp: emeasure_density nn_integral_density ac_simps)

lemma distr_density_distr:
  assumes T: "T \<in> measurable M M'" and T': "T' \<in> measurable M' M"
    and inv: "\<forall>x\<in>space M. T' (T x) = x"
  assumes f: "f \<in> borel_measurable M'"
  shows "distr (density (distr M M' T) f) M T' = density M (f \<circ> T)" (is "?R = ?L")
proof (rule measure_eqI)
  fix A assume A: "A \<in> sets ?R"
  { fix x assume "x \<in> space M"
    with sets.sets_into_space[OF A]
    have "indicator (T' -` A \<inter> space M') (T x) = (indicator A x :: ennreal)"
      using T inv by (auto simp: indicator_def measurable_space) }
  with A T T' f show "emeasure ?R A = emeasure ?L A"
    by (simp add: measurable_comp emeasure_density emeasure_distr
                  nn_integral_distr measurable_sets cong: nn_integral_cong)
qed simp

lemma density_density_divide:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  assumes ac: "AE x in M. f x = 0 \<longrightarrow> g x = 0"
  shows "density (density M f) (\<lambda>x. g x / f x) = density M g"
proof -
  have "density M g = density M (\<lambda>x. ennreal (f x) * ennreal (g x / f x))"
    using f g ac by (auto intro!: density_cong measurable_If simp: ennreal_mult[symmetric])
  then show ?thesis
    using f g by (subst density_density_eq) auto
qed

lemma density_1: "density M (\<lambda>_. 1) = M"
  by (intro measure_eqI) (auto simp: emeasure_density)

lemma emeasure_density_add:
  assumes X: "X \<in> sets M"
  assumes Mf[measurable]: "f \<in> borel_measurable M"
  assumes Mg[measurable]: "g \<in> borel_measurable M"
  shows "emeasure (density M f) X + emeasure (density M g) X =
           emeasure (density M (\<lambda>x. f x + g x)) X"
  using assms
  apply (subst (1 2 3) emeasure_density, simp_all) []
  apply (subst nn_integral_add[symmetric], simp_all) []
  apply (intro nn_integral_cong, simp split: split_indicator)
  done

subsubsection \<open>Point measure\<close>

definition\<^marker>\<open>tag important\<close> point_measure :: "'a set \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a measure" where
  "point_measure A f = density (count_space A) f"

lemma
  shows space_point_measure: "space (point_measure A f) = A"
    and sets_point_measure: "sets (point_measure A f) = Pow A"
  by (auto simp: point_measure_def)

lemma sets_point_measure_count_space[measurable_cong]: "sets (point_measure A f) = sets (count_space A)"
  by (simp add: sets_point_measure)

lemma measurable_point_measure_eq1[simp]:
  "g \<in> measurable (point_measure A f) M \<longleftrightarrow> g \<in> A \<rightarrow> space M"
  unfolding point_measure_def by simp

lemma measurable_point_measure_eq2_finite[simp]:
  "finite A \<Longrightarrow>
   g \<in> measurable M (point_measure A f) \<longleftrightarrow>
    (g \<in> space M \<rightarrow> A \<and> (\<forall>a\<in>A. g -` {a} \<inter> space M \<in> sets M))"
  unfolding point_measure_def by (simp add: measurable_count_space_eq2)

lemma simple_function_point_measure[simp]:
  "simple_function (point_measure A f) g \<longleftrightarrow> finite (g ` A)"
  by (simp add: point_measure_def)

lemma emeasure_point_measure:
  assumes A: "finite {a\<in>X. 0 < f a}" "X \<subseteq> A"
  shows "emeasure (point_measure A f) X = (\<Sum>a|a\<in>X \<and> 0 < f a. f a)"
proof -
  have "{a. (a \<in> X \<longrightarrow> a \<in> A \<and> 0 < f a) \<and> a \<in> X} = {a\<in>X. 0 < f a}"
    using \<open>X \<subseteq> A\<close> by auto
  with A show ?thesis
    by (simp add: emeasure_density nn_integral_count_space point_measure_def indicator_def of_bool_def)
qed

lemma emeasure_point_measure_finite:
  "finite A \<Longrightarrow> X \<subseteq> A \<Longrightarrow> emeasure (point_measure A f) X = (\<Sum>a\<in>X. f a)"
  by (subst emeasure_point_measure) (auto dest: finite_subset intro!: sum.mono_neutral_left simp: less_le)

lemma emeasure_point_measure_finite2:
  "X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> emeasure (point_measure A f) X = (\<Sum>a\<in>X. f a)"
  by (subst emeasure_point_measure)
     (auto dest: finite_subset intro!: sum.mono_neutral_left simp: less_le)

lemma null_sets_point_measure_iff:
  "X \<in> null_sets (point_measure A f) \<longleftrightarrow> X \<subseteq> A \<and> (\<forall>x\<in>X. f x = 0)"
 by (auto simp: AE_count_space null_sets_density_iff point_measure_def)

lemma AE_point_measure:
  "(AE x in point_measure A f. P x) \<longleftrightarrow> (\<forall>x\<in>A. 0 < f x \<longrightarrow> P x)"
  unfolding point_measure_def
  by (subst AE_density) (auto simp: AE_density AE_count_space point_measure_def)

lemma nn_integral_point_measure:
  "finite {a\<in>A. 0 < f a \<and> 0 < g a} \<Longrightarrow>
    integral\<^sup>N (point_measure A f) g = (\<Sum>a|a\<in>A \<and> 0 < f a \<and> 0 < g a. f a * g a)"
  unfolding point_measure_def
  by (subst nn_integral_density)
     (simp_all add: nn_integral_density nn_integral_count_space ennreal_zero_less_mult_iff)

lemma nn_integral_point_measure_finite:
  "finite A \<Longrightarrow> integral\<^sup>N (point_measure A f) g = (\<Sum>a\<in>A. f a * g a)"
  by (subst nn_integral_point_measure) (auto intro!: sum.mono_neutral_left simp: less_le)

subsubsection \<open>Uniform measure\<close>

definition\<^marker>\<open>tag important\<close> "uniform_measure M A = density M (\<lambda>x. indicator A x / emeasure M A)"

lemma
  shows sets_uniform_measure[simp, measurable_cong]: "sets (uniform_measure M A) = sets M"
    and space_uniform_measure[simp]: "space (uniform_measure M A) = space M"
  by (auto simp: uniform_measure_def)

lemma emeasure_uniform_measure[simp]:
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "emeasure (uniform_measure M A) B = emeasure M (A \<inter> B) / emeasure M A"
proof -
  from A B have "emeasure (uniform_measure M A) B = (\<integral>\<^sup>+x. (1 / emeasure M A) * indicator (A \<inter> B) x \<partial>M)"
    by (auto simp add: uniform_measure_def emeasure_density divide_ennreal_def split: split_indicator
             intro!: nn_integral_cong)
  also have "\<dots> = emeasure M (A \<inter> B) / emeasure M A"
    using A B
    by (subst nn_integral_cmult_indicator) (simp_all add: sets.Int divide_ennreal_def mult.commute)
  finally show ?thesis .
qed

lemma measure_uniform_measure[simp]:
  assumes A: "emeasure M A \<noteq> 0" "emeasure M A \<noteq> \<infinity>" and B: "B \<in> sets M"
  shows "measure (uniform_measure M A) B = measure M (A \<inter> B) / measure M A"
  using emeasure_uniform_measure[OF emeasure_neq_0_sets[OF A(1)] B] A
  by (cases "emeasure M A" "emeasure M (A \<inter> B)" rule: ennreal2_cases)
     (simp_all add: measure_def divide_ennreal top_ennreal.rep_eq top_ereal_def ennreal_top_divide)

lemma AE_uniform_measureI:
  "A \<in> sets M \<Longrightarrow> (AE x in M. x \<in> A \<longrightarrow> P x) \<Longrightarrow> (AE x in uniform_measure M A. P x)"
  unfolding uniform_measure_def by (auto simp: AE_density divide_ennreal_def)

lemma emeasure_uniform_measure_1:
  "emeasure M S \<noteq> 0 \<Longrightarrow> emeasure M S \<noteq> \<infinity> \<Longrightarrow> emeasure (uniform_measure M S) S = 1"
  by (subst emeasure_uniform_measure)
     (simp_all add: emeasure_neq_0_sets emeasure_eq_ennreal_measure divide_ennreal
                    zero_less_iff_neq_zero[symmetric])

lemma nn_integral_uniform_measure:
  assumes f[measurable]: "f \<in> borel_measurable M" and S[measurable]: "S \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x \<partial>uniform_measure M S) = (\<integral>\<^sup>+x. f x * indicator S x \<partial>M) / emeasure M S"
proof -
  { assume "emeasure M S = \<infinity>"
    then have ?thesis
      by (simp add: uniform_measure_def nn_integral_density f) }
  moreover
  { assume [simp]: "emeasure M S = 0"
    then have ae: "AE x in M. x \<notin> S"
      using sets.sets_into_space[OF S]
      by (subst AE_iff_measurable[OF _ refl]) (simp_all add: subset_eq cong: rev_conj_cong)
    from ae have "(\<integral>\<^sup>+ x. indicator S x / 0 * f x \<partial>M) = 0"
      by (subst nn_integral_0_iff_AE) auto
    moreover from ae have "(\<integral>\<^sup>+ x. f x * indicator S x \<partial>M) = 0"
      by (subst nn_integral_0_iff_AE) auto
    ultimately have ?thesis
      by (simp add: uniform_measure_def nn_integral_density f) }
  moreover have "emeasure M S \<noteq> 0 \<Longrightarrow> emeasure M S \<noteq> \<infinity> \<Longrightarrow> ?thesis"
    unfolding uniform_measure_def
    by (subst nn_integral_density)
       (auto simp: ennreal_times_divide f nn_integral_divide[symmetric] mult.commute)
  ultimately show ?thesis by blast
qed

lemma AE_uniform_measure:
  assumes "emeasure M A \<noteq> 0" "emeasure M A < \<infinity>"
  shows "(AE x in uniform_measure M A. P x) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> P x)"
proof -
  have "A \<in> sets M"
    using \<open>emeasure M A \<noteq> 0\<close> by (metis emeasure_notin_sets)
  moreover have "\<And>x. 0 < indicator A x / emeasure M A \<longleftrightarrow> x \<in> A"
    using assms
    by (cases "emeasure M A") (auto split: split_indicator simp: ennreal_zero_less_divide)
  ultimately show ?thesis
    unfolding uniform_measure_def by (simp add: AE_density)
qed

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Null measure\<close>

lemma null_measure_eq_density: "null_measure M = density M (\<lambda>_. 0)"
  by (intro measure_eqI) (simp_all add: emeasure_density)

lemma nn_integral_null_measure[simp]: "(\<integral>\<^sup>+x. f x \<partial>null_measure M) = 0"
  by (auto simp add: nn_integral_def simple_integral_def SUP_constant bot_ennreal_def le_fun_def
           intro!: exI[of _ "\<lambda>x. 0"])

lemma density_null_measure[simp]: "density (null_measure M) f = null_measure M"
proof (intro measure_eqI)
  fix A show "emeasure (density (null_measure M) f) A = emeasure (null_measure M) A"
    by (simp add: density_def) (simp only: null_measure_def[symmetric] emeasure_null_measure)
qed simp

subsubsection \<open>Uniform count measure\<close>

definition\<^marker>\<open>tag important\<close> "uniform_count_measure A = point_measure A (\<lambda>x. 1 / card A)"

lemma
  shows space_uniform_count_measure: "space (uniform_count_measure A) = A"
    and sets_uniform_count_measure: "sets (uniform_count_measure A) = Pow A"
    unfolding uniform_count_measure_def by (auto simp: space_point_measure sets_point_measure)

lemma sets_uniform_count_measure_count_space[measurable_cong]:
  "sets (uniform_count_measure A) = sets (count_space A)"
  by (simp add: sets_uniform_count_measure)

lemma emeasure_uniform_count_measure:
  "finite A \<Longrightarrow> X \<subseteq> A \<Longrightarrow> emeasure (uniform_count_measure A) X = card X / card A"
  by (simp add: emeasure_point_measure_finite uniform_count_measure_def divide_inverse ennreal_mult
                ennreal_of_nat_eq_real_of_nat)

lemma measure_uniform_count_measure:
  "finite A \<Longrightarrow> X \<subseteq> A \<Longrightarrow> measure (uniform_count_measure A) X = card X / card A"
  by (simp add: emeasure_point_measure_finite uniform_count_measure_def measure_def enn2real_mult)

lemma space_uniform_count_measure_empty_iff [simp]:
  "space (uniform_count_measure X) = {} \<longleftrightarrow> X = {}"
by(simp add: space_uniform_count_measure)

lemma sets_uniform_count_measure_eq_UNIV [simp]:
  "sets (uniform_count_measure UNIV) = UNIV \<longleftrightarrow> True"
  "UNIV = sets (uniform_count_measure UNIV) \<longleftrightarrow> True"
by(simp_all add: sets_uniform_count_measure)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Scaled measure\<close>

lemma nn_integral_scale_measure:
  assumes f: "f \<in> borel_measurable M"
  shows "nn_integral (scale_measure r M) f = r * nn_integral M f"
  using f
proof induction
  case (cong f g)
  thus ?case
    by(simp add: cong.hyps space_scale_measure cong: nn_integral_cong_simp)
next
  case (mult f c)
  thus ?case
    by(simp add: nn_integral_cmult max_def mult.assoc mult.left_commute)
next
  case (add f g)
  thus ?case
    by(simp add: nn_integral_add distrib_left)
next
  case (seq U)
  thus ?case
    by(simp add: nn_integral_monotone_convergence_SUP SUP_mult_left_ennreal image_comp)
qed simp

end
