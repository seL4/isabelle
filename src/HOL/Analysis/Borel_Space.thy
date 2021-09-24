(*  Title:      HOL/Analysis/Borel_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section \<open>Borel Space\<close>

theory Borel_Space
imports
  Measurable Derivative Ordered_Euclidean_Space Extended_Real_Limits
begin

lemma is_interval_real_ereal_oo: "is_interval (real_of_ereal ` {N<..<M::ereal})"
  by (auto simp: real_atLeastGreaterThan_eq)

lemma sets_Collect_eventually_sequentially[measurable]:
  "(\<And>i. {x\<in>space M. P x i} \<in> sets M) \<Longrightarrow> {x\<in>space M. eventually (P x) sequentially} \<in> sets M"
  unfolding eventually_sequentially by simp

lemma topological_basis_trivial: "topological_basis {A. open A}"
  by (auto simp: topological_basis_def)

proposition open_prod_generated: "open = generate_topology {A \<times> B | A B. open A \<and> open B}"
proof -
  have "{A \<times> B :: ('a \<times> 'b) set | A B. open A \<and> open B} = ((\<lambda>(a, b). a \<times> b) ` ({A. open A} \<times> {A. open A}))"
    by auto
  then show ?thesis
    by (auto intro: topological_basis_prod topological_basis_trivial topological_basis_imp_subbasis)
qed

proposition mono_on_imp_deriv_nonneg:
  assumes mono: "mono_on f A" and deriv: "(f has_real_derivative D) (at x)"
  assumes "x \<in> interior A"
  shows "D \<ge> 0"
proof (rule tendsto_lowerbound)
  let ?A' = "(\<lambda>y. y - x) ` interior A"
  from deriv show "((\<lambda>h. (f (x + h) - f x) / h) \<longlongrightarrow> D) (at 0)"
      by (simp add: field_has_derivative_at has_field_derivative_def)
  from mono have mono': "mono_on f (interior A)" by (rule mono_on_subset) (rule interior_subset)

  show "eventually (\<lambda>h. (f (x + h) - f x) / h \<ge> 0) (at 0)"
  proof (subst eventually_at_topological, intro exI conjI ballI impI)
    have "open (interior A)" by simp
    hence "open ((+) (-x) ` interior A)" by (rule open_translation)
    also have "((+) (-x) ` interior A) = ?A'" by auto
    finally show "open ?A'" .
  next
    from \<open>x \<in> interior A\<close> show "0 \<in> ?A'" by auto
  next
    fix h assume "h \<in> ?A'"
    hence "x + h \<in> interior A" by auto
    with mono' and \<open>x \<in> interior A\<close> show "(f (x + h) - f x) / h \<ge> 0"
      by (cases h rule: linorder_cases[of _ 0])
         (simp_all add: divide_nonpos_neg divide_nonneg_pos mono_onD field_simps)
  qed
qed simp

proposition mono_on_ctble_discont:
  fixes f :: "real \<Rightarrow> real"
  fixes A :: "real set"
  assumes "mono_on f A"
  shows "countable {a\<in>A. \<not> continuous (at a within A) f}"
proof -
  have mono: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
    using \<open>mono_on f A\<close> by (simp add: mono_on_def)
  have "\<forall>a \<in> {a\<in>A. \<not> continuous (at a within A) f}. \<exists>q :: nat \<times> rat.
      (fst q = 0 \<and> of_rat (snd q) < f a \<and> (\<forall>x \<in> A. x < a \<longrightarrow> f x < of_rat (snd q))) \<or>
      (fst q = 1 \<and> of_rat (snd q) > f a \<and> (\<forall>x \<in> A. x > a \<longrightarrow> f x > of_rat (snd q)))"
  proof (clarsimp simp del: One_nat_def)
    fix a assume "a \<in> A" assume "\<not> continuous (at a within A) f"
    thus "\<exists>q1 q2.
            q1 = 0 \<and> real_of_rat q2 < f a \<and> (\<forall>x\<in>A. x < a \<longrightarrow> f x < real_of_rat q2) \<or>
            q1 = 1 \<and> f a < real_of_rat q2 \<and> (\<forall>x\<in>A. a < x \<longrightarrow> real_of_rat q2 < f x)"
    proof (auto simp add: continuous_within order_tendsto_iff eventually_at)
      fix l assume "l < f a"
      then obtain q2 where q2: "l < of_rat q2" "of_rat q2 < f a"
        using of_rat_dense by blast
      assume * [rule_format]: "\<forall>d>0. \<exists>x\<in>A. x \<noteq> a \<and> dist x a < d \<and> \<not> l < f x"
      from q2 have "real_of_rat q2 < f a \<and> (\<forall>x\<in>A. x < a \<longrightarrow> f x < real_of_rat q2)"
      proof auto
        fix x assume "x \<in> A" "x < a"
        with q2 *[of "a - x"] show "f x < real_of_rat q2"
          apply (auto simp add: dist_real_def not_less)
          apply (subgoal_tac "f x \<le> f xa")
          by (auto intro: mono)
      qed
      thus ?thesis by auto
    next
      fix u assume "u > f a"
      then obtain q2 where q2: "f a < of_rat q2" "of_rat q2 < u"
        using of_rat_dense by blast
      assume *[rule_format]: "\<forall>d>0. \<exists>x\<in>A. x \<noteq> a \<and> dist x a < d \<and> \<not> u > f x"
      from q2 have "real_of_rat q2 > f a \<and> (\<forall>x\<in>A. x > a \<longrightarrow> f x > real_of_rat q2)"
      proof auto
        fix x assume "x \<in> A" "x > a"
        with q2 *[of "x - a"] show "f x > real_of_rat q2"
          apply (auto simp add: dist_real_def)
          apply (subgoal_tac "f x \<ge> f xa")
          by (auto intro: mono)
      qed
      thus ?thesis by auto
    qed
  qed
  then obtain g :: "real \<Rightarrow> nat \<times> rat" where "\<forall>a \<in> {a\<in>A. \<not> continuous (at a within A) f}.
      (fst (g a) = 0 \<and> of_rat (snd (g a)) < f a \<and> (\<forall>x \<in> A. x < a \<longrightarrow> f x < of_rat (snd (g a)))) |
      (fst (g a) = 1 \<and> of_rat (snd (g a)) > f a \<and> (\<forall>x \<in> A. x > a \<longrightarrow> f x > of_rat (snd (g a))))"
    by (rule bchoice [THEN exE]) blast
  hence g: "\<And>a x. a \<in> A \<Longrightarrow> \<not> continuous (at a within A) f \<Longrightarrow> x \<in> A \<Longrightarrow>
      (fst (g a) = 0 \<and> of_rat (snd (g a)) < f a \<and> (x < a \<longrightarrow> f x < of_rat (snd (g a)))) |
      (fst (g a) = 1 \<and> of_rat (snd (g a)) > f a \<and> (x > a \<longrightarrow> f x > of_rat (snd (g a))))"
    by auto
  have "inj_on g {a\<in>A. \<not> continuous (at a within A) f}"
  proof (auto simp add: inj_on_def)
    fix w z
    assume 1: "w \<in> A" and 2: "\<not> continuous (at w within A) f" and
           3: "z \<in> A" and 4: "\<not> continuous (at z within A) f" and
           5: "g w = g z"
    from g [OF 1 2 3] g [OF 3 4 1] 5
    show "w = z" by auto
  qed
  thus ?thesis
    by (rule countableI')
qed

lemma mono_on_ctble_discont_open:
  fixes f :: "real \<Rightarrow> real"
  fixes A :: "real set"
  assumes "open A" "mono_on f A"
  shows "countable {a\<in>A. \<not>isCont f a}"
proof -
  have "{a\<in>A. \<not>isCont f a} = {a\<in>A. \<not>(continuous (at a within A) f)}"
    by (auto simp add: continuous_within_open [OF _ \<open>open A\<close>])
  thus ?thesis
    apply (elim ssubst)
    by (rule mono_on_ctble_discont, rule assms)
qed

lemma mono_ctble_discont:
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
  shows "countable {a. \<not> isCont f a}"
  using assms mono_on_ctble_discont [of f UNIV] unfolding mono_on_def mono_def by auto

lemma has_real_derivative_imp_continuous_on:
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  shows "continuous_on A f"
  apply (intro differentiable_imp_continuous_on, unfold differentiable_on_def)
  using assms differentiable_at_withinI real_differentiable_def by blast

lemma continuous_interval_vimage_Int:
  assumes "continuous_on {a::real..b} g" and mono: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
  assumes "a \<le> b" "(c::real) \<le> d" "{c..d} \<subseteq> {g a..g b}"
  obtains c' d' where "{a..b} \<inter> g -` {c..d} = {c'..d'}" "c' \<le> d'" "g c' = c" "g d' = d"
proof-
  let ?A = "{a..b} \<inter> g -` {c..d}"
  from IVT'[of g a c b, OF _ _ \<open>a \<le> b\<close> assms(1)] assms(4,5)
  obtain c'' where c'': "c'' \<in> ?A" "g c'' = c" by auto
  from IVT'[of g a d b, OF _ _ \<open>a \<le> b\<close> assms(1)] assms(4,5)
  obtain d'' where d'': "d'' \<in> ?A" "g d'' = d" by auto
  hence [simp]: "?A \<noteq> {}" by blast

  define c' where "c' = Inf ?A"
  define d' where "d' = Sup ?A"
  have "?A \<subseteq> {c'..d'}" unfolding c'_def d'_def
    by (intro subsetI) (auto intro: cInf_lower cSup_upper)
  moreover from assms have "closed ?A"
    using continuous_on_closed_vimage[of "{a..b}" g] by (subst Int_commute) simp
  hence c'd'_in_set: "c' \<in> ?A" "d' \<in> ?A" unfolding c'_def d'_def
    by ((intro closed_contains_Inf closed_contains_Sup, simp_all)[])+
  hence "{c'..d'} \<subseteq> ?A" using assms
    by (intro subsetI)
       (auto intro!: order_trans[of c "g c'" "g x" for x] order_trans[of "g x" "g d'" d for x]
             intro!: mono)
  moreover have "c' \<le> d'" using c'd'_in_set(2) unfolding c'_def by (intro cInf_lower) auto
  moreover have "g c' \<le> c" "g d' \<ge> d"
    apply (insert c'' d'' c'd'_in_set)
    apply (subst c''(2)[symmetric])
    apply (auto simp: c'_def intro!: mono cInf_lower c'') []
    apply (subst d''(2)[symmetric])
    apply (auto simp: d'_def intro!: mono cSup_upper d'') []
    done
  with c'd'_in_set have "g c' = c" "g d' = d" by auto
  ultimately show ?thesis using that by blast
qed

subsection \<open>Generic Borel spaces\<close>

definition\<^marker>\<open>tag important\<close> (in topological_space) borel :: "'a measure" where
  "borel = sigma UNIV {S. open S}"

abbreviation "borel_measurable M \<equiv> measurable M borel"

lemma in_borel_measurable:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sigma_sets UNIV {S. open S}. f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma in_borel_measurable_borel:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sets borel.
      f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma space_borel[simp]: "space borel = UNIV"
  unfolding borel_def by auto

lemma space_in_borel[measurable]: "UNIV \<in> sets borel"
  unfolding borel_def by auto

lemma sets_borel: "sets borel = sigma_sets UNIV {S. open S}"
  unfolding borel_def by (rule sets_measure_of) simp

lemma measurable_sets_borel:
    "\<lbrakk>f \<in> measurable borel M; A \<in> sets M\<rbrakk> \<Longrightarrow> f -` A \<in> sets borel"
  by (drule (1) measurable_sets) simp

lemma pred_Collect_borel[measurable (raw)]: "Measurable.pred borel P \<Longrightarrow> {x. P x} \<in> sets borel"
  unfolding borel_def pred_def by auto

lemma borel_open[measurable (raw generic)]:
  assumes "open A" shows "A \<in> sets borel"
proof -
  have "A \<in> {S. open S}" unfolding mem_Collect_eq using assms .
  thus ?thesis unfolding borel_def by auto
qed

lemma borel_closed[measurable (raw generic)]:
  assumes "closed A" shows "A \<in> sets borel"
proof -
  have "space borel - (- A) \<in> sets borel"
    using assms unfolding closed_def by (blast intro: borel_open)
  thus ?thesis by simp
qed

lemma borel_singleton[measurable]:
  "A \<in> sets borel \<Longrightarrow> insert x A \<in> sets (borel :: 'a::t1_space measure)"
  unfolding insert_def by (rule sets.Un) auto

lemma sets_borel_eq_count_space: "sets (borel :: 'a::{countable, t2_space} measure) = count_space UNIV"
proof -
  have "(\<Union>a\<in>A. {a}) \<in> sets borel" for A :: "'a set"
    by (intro sets.countable_UN') auto
  then show ?thesis
    by auto
qed

lemma borel_comp[measurable]: "A \<in> sets borel \<Longrightarrow> - A \<in> sets borel"
  unfolding Compl_eq_Diff_UNIV by simp

lemma borel_measurable_vimage:
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes borel[measurable]: "f \<in> borel_measurable M"
  shows "f -` {x} \<inter> space M \<in> sets M"
  by simp

lemma borel_measurableI:
  fixes f :: "'a \<Rightarrow> 'x::topological_space"
  assumes "\<And>S. open S \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable M"
  unfolding borel_def
proof (rule measurable_measure_of, simp_all)
  fix S :: "'x set" assume "open S" thus "f -` S \<inter> space M \<in> sets M"
    using assms[of S] by simp
qed

lemma borel_measurable_const:
  "(\<lambda>x. c) \<in> borel_measurable M"
  by auto

lemma borel_measurable_indicator:
  assumes A: "A \<in> sets M"
  shows "indicator A \<in> borel_measurable M"
  unfolding indicator_def [abs_def] using A
  by (auto intro!: measurable_If_set)

lemma borel_measurable_count_space[measurable (raw)]:
  "f \<in> borel_measurable (count_space S)"
  unfolding measurable_def by auto

lemma borel_measurable_indicator'[measurable (raw)]:
  assumes [measurable]: "{x\<in>space M. f x \<in> A x} \<in> sets M"
  shows "(\<lambda>x. indicator (A x) (f x)) \<in> borel_measurable M"
  unfolding indicator_def[abs_def]
  by (auto intro!: measurable_If)

lemma borel_measurable_indicator_iff:
  "(indicator A :: 'a \<Rightarrow> 'x::{t1_space, zero_neq_one}) \<in> borel_measurable M \<longleftrightarrow> A \<inter> space M \<in> sets M"
    (is "?I \<in> borel_measurable M \<longleftrightarrow> _")
proof
  assume "?I \<in> borel_measurable M"
  then have "?I -` {1} \<inter> space M \<in> sets M"
    unfolding measurable_def by auto
  also have "?I -` {1} \<inter> space M = A \<inter> space M"
    unfolding indicator_def [abs_def] by auto
  finally show "A \<inter> space M \<in> sets M" .
next
  assume "A \<inter> space M \<in> sets M"
  moreover have "?I \<in> borel_measurable M \<longleftrightarrow>
    (indicator (A \<inter> space M) :: 'a \<Rightarrow> 'x) \<in> borel_measurable M"
    by (intro measurable_cong) (auto simp: indicator_def)
  ultimately show "?I \<in> borel_measurable M" by auto
qed

lemma borel_measurable_subalgebra:
  assumes "sets N \<subseteq> sets M" "space N = space M" "f \<in> borel_measurable N"
  shows "f \<in> borel_measurable M"
  using assms unfolding measurable_def by auto

lemma borel_measurable_restrict_space_iff_ereal:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes \<Omega>[measurable, simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable (restrict_space M \<Omega>) \<longleftrightarrow>
    (\<lambda>x. f x * indicator \<Omega> x) \<in> borel_measurable M"
  by (subst measurable_restrict_space_iff)
     (auto simp: indicator_def of_bool_def if_distrib[where f="\<lambda>x. a * x" for a] cong del: if_weak_cong)

lemma borel_measurable_restrict_space_iff_ennreal:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes \<Omega>[measurable, simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable (restrict_space M \<Omega>) \<longleftrightarrow>
    (\<lambda>x. f x * indicator \<Omega> x) \<in> borel_measurable M"
  by (subst measurable_restrict_space_iff)
     (auto simp: indicator_def of_bool_def if_distrib[where f="\<lambda>x. a * x" for a] cong del: if_weak_cong)

lemma borel_measurable_restrict_space_iff:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes \<Omega>[measurable, simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable (restrict_space M \<Omega>) \<longleftrightarrow>
    (\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> borel_measurable M"
  by (subst measurable_restrict_space_iff)
     (auto simp: indicator_def of_bool_def if_distrib[where f="\<lambda>x. x *\<^sub>R a" for a] ac_simps
       cong del: if_weak_cong)

lemma cbox_borel[measurable]: "cbox a b \<in> sets borel"
  by (auto intro: borel_closed)

lemma box_borel[measurable]: "box a b \<in> sets borel"
  by (auto intro: borel_open)

lemma borel_compact: "compact (A::'a::t2_space set) \<Longrightarrow> A \<in> sets borel"
  by (auto intro: borel_closed dest!: compact_imp_closed)

lemma borel_sigma_sets_subset:
  "A \<subseteq> sets borel \<Longrightarrow> sigma_sets UNIV A \<subseteq> sets borel"
  using sets.sigma_sets_subset[of A borel] by simp

lemma borel_eq_sigmaI1:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV (F ` A))"
  assumes F: "\<And>i. i \<in> A \<Longrightarrow> F i \<in> sets borel"
  shows "borel = sigma UNIV (F ` A)"
  unfolding borel_def
proof (intro sigma_eqI antisym)
  have borel_rev_eq: "sigma_sets UNIV {S::'a set. open S} = sets borel"
    unfolding borel_def by simp
  also have "\<dots> = sigma_sets UNIV X"
    unfolding borel_eq by simp
  also have "\<dots> \<subseteq> sigma_sets UNIV (F`A)"
    using X by (intro sigma_algebra.sigma_sets_subset[OF sigma_algebra_sigma_sets]) auto
  finally show "sigma_sets UNIV {S. open S} \<subseteq> sigma_sets UNIV (F`A)" .
  show "sigma_sets UNIV (F`A) \<subseteq> sigma_sets UNIV {S. open S}"
    unfolding borel_rev_eq using F by (intro borel_sigma_sets_subset) auto
qed auto

lemma borel_eq_sigmaI2:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV ((\<lambda>(i, j). G i j)`B)"
  assumes X: "\<And>i j. (i, j) \<in> B \<Longrightarrow> G i j \<in> sets (sigma UNIV ((\<lambda>(i, j). F i j) ` A))"
  assumes F: "\<And>i j. (i, j) \<in> A \<Longrightarrow> F i j \<in> sets borel"
  shows "borel = sigma UNIV ((\<lambda>(i, j). F i j) ` A)"
  using assms
  by (intro borel_eq_sigmaI1[where X="(\<lambda>(i, j). G i j) ` B" and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI3:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV ((\<lambda>(i, j). F i j) ` A))"
  assumes F: "\<And>i j. (i, j) \<in> A \<Longrightarrow> F i j \<in> sets borel"
  shows "borel = sigma UNIV ((\<lambda>(i, j). F i j) ` A)"
  using assms by (intro borel_eq_sigmaI1[where X=X and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI4:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV ((\<lambda>(i, j). G i j)`A)"
  assumes X: "\<And>i j. (i, j) \<in> A \<Longrightarrow> G i j \<in> sets (sigma UNIV (range F))"
  assumes F: "\<And>i. F i \<in> sets borel"
  shows "borel = sigma UNIV (range F)"
  using assms by (intro borel_eq_sigmaI1[where X="(\<lambda>(i, j). G i j) ` A" and F=F]) auto

lemma borel_eq_sigmaI5:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and G :: "'l \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range G)"
  assumes X: "\<And>i. G i \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X="range G" and F="(\<lambda>(i, j). F i j)"]) auto

theorem second_countable_borel_measurable:
  fixes X :: "'a::second_countable_topology set set"
  assumes eq: "open = generate_topology X"
  shows "borel = sigma UNIV X"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI)
  interpret X: sigma_algebra UNIV "sigma_sets UNIV X"
    by (rule sigma_algebra_sigma_sets) simp

  fix S :: "'a set" assume "S \<in> Collect open"
  then have "generate_topology X S"
    by (auto simp: eq)
  then show "S \<in> sigma_sets UNIV X"
  proof induction
    case (UN K)
    then have K: "\<And>k. k \<in> K \<Longrightarrow> open k"
      unfolding eq by auto
    from ex_countable_basis obtain B :: "'a set set" where
      B:  "\<And>b. b \<in> B \<Longrightarrow> open b" "\<And>X. open X \<Longrightarrow> \<exists>b\<subseteq>B. (\<Union>b) = X" and "countable B"
      by (auto simp: topological_basis_def)
    from B(2)[OF K] obtain m where m: "\<And>k. k \<in> K \<Longrightarrow> m k \<subseteq> B" "\<And>k. k \<in> K \<Longrightarrow> \<Union>(m k) = k"
      by metis
    define U where "U = (\<Union>k\<in>K. m k)"
    with m have "countable U"
      by (intro countable_subset[OF _ \<open>countable B\<close>]) auto
    have "\<Union>U = (\<Union>A\<in>U. A)" by simp
    also have "\<dots> = \<Union>K"
      unfolding U_def UN_simps by (simp add: m)
    finally have "\<Union>U = \<Union>K" .

    have "\<forall>b\<in>U. \<exists>k\<in>K. b \<subseteq> k"
      using m by (auto simp: U_def)
    then obtain u where u: "\<And>b. b \<in> U \<Longrightarrow> u b \<in> K" and "\<And>b. b \<in> U \<Longrightarrow> b \<subseteq> u b"
      by metis
    then have "(\<Union>b\<in>U. u b) \<subseteq> \<Union>K" "\<Union>U \<subseteq> (\<Union>b\<in>U. u b)"
      by auto
    then have "\<Union>K = (\<Union>b\<in>U. u b)"
      unfolding \<open>\<Union>U = \<Union>K\<close> by auto
    also have "\<dots> \<in> sigma_sets UNIV X"
      using u UN by (intro X.countable_UN' \<open>countable U\<close>) auto
    finally show "\<Union>K \<in> sigma_sets UNIV X" .
  qed auto
qed (auto simp: eq intro: generate_topology.Basis)

lemma borel_eq_closed: "borel = sigma UNIV (Collect closed)"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI, safe)
  fix x :: "'a set" assume "open x"
  hence "x = UNIV - (UNIV - x)" by auto
  also have "\<dots> \<in> sigma_sets UNIV (Collect closed)"
    by (force intro: sigma_sets.Compl simp: \<open>open x\<close>)
  finally show "x \<in> sigma_sets UNIV (Collect closed)" by simp
next
  fix x :: "'a set" assume "closed x"
  hence "x = UNIV - (UNIV - x)" by auto
  also have "\<dots> \<in> sigma_sets UNIV (Collect open)"
    by (force intro: sigma_sets.Compl simp: \<open>closed x\<close>)
  finally show "x \<in> sigma_sets UNIV (Collect open)" by simp
qed simp_all

proposition borel_eq_countable_basis:
  fixes B::"'a::topological_space set set"
  assumes "countable B"
  assumes "topological_basis B"
  shows "borel = sigma UNIV B"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI, safe)
  interpret countable_basis "open" B using assms by (rule countable_basis_openI)
  fix X::"'a set" assume "open X"
  from open_countable_basisE[OF this] obtain B' where B': "B' \<subseteq> B" "X = \<Union> B'" .
  then show "X \<in> sigma_sets UNIV B"
    by (blast intro: sigma_sets_UNION \<open>countable B\<close> countable_subset)
next
  fix b assume "b \<in> B"
  hence "open b" by (rule topological_basis_open[OF assms(2)])
  thus "b \<in> sigma_sets UNIV (Collect open)" by auto
qed simp_all

lemma borel_measurable_continuous_on_restrict:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "continuous_on A f"
  shows "f \<in> borel_measurable (restrict_space borel A)"
proof (rule borel_measurableI)
  fix S :: "'b set" assume "open S"
  with f obtain T where "f -` S \<inter> A = T \<inter> A" "open T"
    by (metis continuous_on_open_invariant)
  then show "f -` S \<inter> space (restrict_space borel A) \<in> sets (restrict_space borel A)"
    by (force simp add: sets_restrict_space space_restrict_space)
qed

lemma borel_measurable_continuous_onI: "continuous_on UNIV f \<Longrightarrow> f \<in> borel_measurable borel"
  by (drule borel_measurable_continuous_on_restrict) simp

lemma borel_measurable_continuous_on_if:
  "A \<in> sets borel \<Longrightarrow> continuous_on A f \<Longrightarrow> continuous_on (- A) g \<Longrightarrow>
    (\<lambda>x. if x \<in> A then f x else g x) \<in> borel_measurable borel"
  by (auto simp add: measurable_If_restrict_space_iff Collect_neg_eq
           intro!: borel_measurable_continuous_on_restrict)

lemma borel_measurable_continuous_countable_exceptions:
  fixes f :: "'a::t1_space \<Rightarrow> 'b::topological_space"
  assumes X: "countable X"
  assumes "continuous_on (- X) f"
  shows "f \<in> borel_measurable borel"
proof (rule measurable_discrete_difference[OF _ X])
  have "X \<in> sets borel"
    by (rule sets.countable[OF _ X]) auto
  then show "(\<lambda>x. if x \<in> X then undefined else f x) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_on_if assms continuous_intros)
qed auto

lemma borel_measurable_continuous_on:
  assumes f: "continuous_on UNIV f" and g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f (g x)) \<in> borel_measurable M"
  using measurable_comp[OF g borel_measurable_continuous_onI[OF f]] by (simp add: comp_def)

lemma borel_measurable_continuous_on_indicator:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "A \<in> sets borel \<Longrightarrow> continuous_on A f \<Longrightarrow> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable borel"
  by (subst borel_measurable_restrict_space_iff[symmetric])
     (auto intro: borel_measurable_continuous_on_restrict)

lemma borel_measurable_Pair[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::second_countable_topology" and g :: "'a \<Rightarrow> 'c::second_countable_topology"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes g[measurable]: "g \<in> borel_measurable M"
  shows "(\<lambda>x. (f x, g x)) \<in> borel_measurable M"
proof (subst borel_eq_countable_basis)
  let ?B = "SOME B::'b set set. countable B \<and> topological_basis B"
  let ?C = "SOME B::'c set set. countable B \<and> topological_basis B"
  let ?P = "(\<lambda>(b, c). b \<times> c) ` (?B \<times> ?C)"
  show "countable ?P" "topological_basis ?P"
    by (auto intro!: countable_basis topological_basis_prod is_basis)

  show "(\<lambda>x. (f x, g x)) \<in> measurable M (sigma UNIV ?P)"
  proof (rule measurable_measure_of)
    fix S assume "S \<in> ?P"
    then obtain b c where "b \<in> ?B" "c \<in> ?C" and S: "S = b \<times> c" by auto
    then have borel: "open b" "open c"
      by (auto intro: is_basis topological_basis_open)
    have "(\<lambda>x. (f x, g x)) -` S \<inter> space M = (f -` b \<inter> space M) \<inter> (g -` c \<inter> space M)"
      unfolding S by auto
    also have "\<dots> \<in> sets M"
      using borel by simp
    finally show "(\<lambda>x. (f x, g x)) -` S \<inter> space M \<in> sets M" .
  qed auto
qed

lemma borel_measurable_continuous_Pair:
  fixes f :: "'a \<Rightarrow> 'b::second_countable_topology" and g :: "'a \<Rightarrow> 'c::second_countable_topology"
  assumes [measurable]: "f \<in> borel_measurable M"
  assumes [measurable]: "g \<in> borel_measurable M"
  assumes H: "continuous_on UNIV (\<lambda>x. H (fst x) (snd x))"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  have eq: "(\<lambda>x. H (f x) (g x)) = (\<lambda>x. (\<lambda>x. H (fst x) (snd x)) (f x, g x))" by auto
  show ?thesis
    unfolding eq by (rule borel_measurable_continuous_on[OF H]) auto
qed

subsection \<open>Borel spaces on order topologies\<close>

lemma [measurable]:
  fixes a b :: "'a::linorder_topology"
  shows lessThan_borel: "{..< a} \<in> sets borel"
    and greaterThan_borel: "{a <..} \<in> sets borel"
    and greaterThanLessThan_borel: "{a<..<b} \<in> sets borel"
    and atMost_borel: "{..a} \<in> sets borel"
    and atLeast_borel: "{a..} \<in> sets borel"
    and atLeastAtMost_borel: "{a..b} \<in> sets borel"
    and greaterThanAtMost_borel: "{a<..b} \<in> sets borel"
    and atLeastLessThan_borel: "{a..<b} \<in> sets borel"
  unfolding greaterThanAtMost_def atLeastLessThan_def
  by (blast intro: borel_open borel_closed open_lessThan open_greaterThan open_greaterThanLessThan
                   closed_atMost closed_atLeast closed_atLeastAtMost)+

lemma borel_Iio:
  "borel = sigma UNIV (range lessThan :: 'a::{linorder_topology, second_countable_topology} set set)"
  unfolding second_countable_borel_measurable[OF open_generated_order]
proof (intro sigma_eqI sigma_sets_eqI)
  obtain D :: "'a set" where D: "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d\<in>D. d \<in> X"
    by (rule countable_dense_setE) blast

  interpret L: sigma_algebra UNIV "sigma_sets UNIV (range lessThan)"
    by (rule sigma_algebra_sigma_sets) simp

  fix A :: "'a set" assume "A \<in> range lessThan \<union> range greaterThan"
  then obtain y where "A = {y <..} \<or> A = {..< y}"
    by blast
  then show "A \<in> sigma_sets UNIV (range lessThan)"
  proof
    assume A: "A = {y <..}"
    show ?thesis
    proof cases
      assume "\<forall>x>y. \<exists>d. y < d \<and> d < x"
      with D(2)[of "{y <..< x}" for x] have "\<forall>x>y. \<exists>d\<in>D. y < d \<and> d < x"
        by (auto simp: set_eq_iff)
      then have "A = UNIV - (\<Inter>d\<in>{d\<in>D. y < d}. {..< d})"
        by (auto simp: A) (metis less_asym)
      also have "\<dots> \<in> sigma_sets UNIV (range lessThan)"
        using D(1) by (intro L.Diff L.top L.countable_INT'') auto
      finally show ?thesis .
    next
      assume "\<not> (\<forall>x>y. \<exists>d. y < d \<and> d < x)"
      then obtain x where "y < x"  "\<And>d. y < d \<Longrightarrow> \<not> d < x"
        by auto
      then have "A = UNIV - {..< x}"
        unfolding A by (auto simp: not_less[symmetric])
      also have "\<dots> \<in> sigma_sets UNIV (range lessThan)"
        by auto
      finally show ?thesis .
    qed
  qed auto
qed auto

lemma borel_Ioi:
  "borel = sigma UNIV (range greaterThan :: 'a::{linorder_topology, second_countable_topology} set set)"
  unfolding second_countable_borel_measurable[OF open_generated_order]
proof (intro sigma_eqI sigma_sets_eqI)
  obtain D :: "'a set" where D: "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d\<in>D. d \<in> X"
    by (rule countable_dense_setE) blast

  interpret L: sigma_algebra UNIV "sigma_sets UNIV (range greaterThan)"
    by (rule sigma_algebra_sigma_sets) simp

  fix A :: "'a set" assume "A \<in> range lessThan \<union> range greaterThan"
  then obtain y where "A = {y <..} \<or> A = {..< y}"
    by blast
  then show "A \<in> sigma_sets UNIV (range greaterThan)"
  proof
    assume A: "A = {..< y}"
    show ?thesis
    proof cases
      assume "\<forall>x<y. \<exists>d. x < d \<and> d < y"
      with D(2)[of "{x <..< y}" for x] have "\<forall>x<y. \<exists>d\<in>D. x < d \<and> d < y"
        by (auto simp: set_eq_iff)
      then have "A = UNIV - (\<Inter>d\<in>{d\<in>D. d < y}. {d <..})"
        by (auto simp: A) (metis less_asym)
      also have "\<dots> \<in> sigma_sets UNIV (range greaterThan)"
        using D(1) by (intro L.Diff L.top L.countable_INT'') auto
      finally show ?thesis .
    next
      assume "\<not> (\<forall>x<y. \<exists>d. x < d \<and> d < y)"
      then obtain x where "x < y"  "\<And>d. y > d \<Longrightarrow> x \<ge> d"
        by (auto simp: not_less[symmetric])
      then have "A = UNIV - {x <..}"
        unfolding A Compl_eq_Diff_UNIV[symmetric] by auto
      also have "\<dots> \<in> sigma_sets UNIV (range greaterThan)"
        by auto
      finally show ?thesis .
    qed
  qed auto
qed auto

lemma borel_measurableI_less:
  fixes f :: "'a \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  shows "(\<And>y. {x\<in>space M. f x < y} \<in> sets M) \<Longrightarrow> f \<in> borel_measurable M"
  unfolding borel_Iio
  by (rule measurable_measure_of) (auto simp: Int_def conj_commute)

lemma borel_measurableI_greater:
  fixes f :: "'a \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  shows "(\<And>y. {x\<in>space M. y < f x} \<in> sets M) \<Longrightarrow> f \<in> borel_measurable M"
  unfolding borel_Ioi
  by (rule measurable_measure_of) (auto simp: Int_def conj_commute)

lemma borel_measurableI_le:
  fixes f :: "'a \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  shows "(\<And>y. {x\<in>space M. f x \<le> y} \<in> sets M) \<Longrightarrow> f \<in> borel_measurable M"
  by (rule borel_measurableI_greater) (auto simp: not_le[symmetric])

lemma borel_measurableI_ge:
  fixes f :: "'a \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  shows "(\<And>y. {x\<in>space M. y \<le> f x} \<in> sets M) \<Longrightarrow> f \<in> borel_measurable M"
  by (rule borel_measurableI_less) (auto simp: not_le[symmetric])

lemma borel_measurable_less[measurable]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w < g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w < g w} = (\<lambda>x. (f x, g x)) -` {x. fst x < snd x} \<inter> space M"
    by auto
  also have "\<dots> \<in> sets M"
    by (intro measurable_sets[OF borel_measurable_Pair borel_open, OF assms open_Collect_less]
              continuous_intros)
  finally show ?thesis .
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes g[measurable]: "g \<in> borel_measurable M"
  shows borel_measurable_le[measurable]: "{w \<in> space M. f w \<le> g w} \<in> sets M"
    and borel_measurable_eq[measurable]: "{w \<in> space M. f w = g w} \<in> sets M"
    and borel_measurable_neq: "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
  unfolding eq_iff not_less[symmetric]
  by measurable

lemma borel_measurable_SUP[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{complete_linorder, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. SUP i\<in>I. F i x) \<in> borel_measurable M"
  by (rule borel_measurableI_greater) (simp add: less_SUP_iff)

lemma borel_measurable_INF[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{complete_linorder, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. INF i\<in>I. F i x) \<in> borel_measurable M"
  by (rule borel_measurableI_less) (simp add: INF_less_iff)

lemma borel_measurable_cSUP[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  assumes bdd: "\<And>x. x \<in> space M \<Longrightarrow> bdd_above ((\<lambda>i. F i x) ` I)"
  shows "(\<lambda>x. SUP i\<in>I. F i x) \<in> borel_measurable M"
proof cases
  assume "I = {}" then show ?thesis
    unfolding \<open>I = {}\<close> image_empty by simp
next
  assume "I \<noteq> {}"
  show ?thesis
  proof (rule borel_measurableI_le)
    fix y
    have "{x \<in> space M. \<forall>i\<in>I. F i x \<le> y} \<in> sets M"
      by measurable
    also have "{x \<in> space M. \<forall>i\<in>I. F i x \<le> y} = {x \<in> space M. (SUP i\<in>I. F i x) \<le> y}"
      by (simp add: cSUP_le_iff \<open>I \<noteq> {}\<close> bdd cong: conj_cong)
    finally show "{x \<in> space M. (SUP i\<in>I. F i x) \<le>  y} \<in> sets M"  .
  qed
qed

lemma borel_measurable_cINF[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  assumes bdd: "\<And>x. x \<in> space M \<Longrightarrow> bdd_below ((\<lambda>i. F i x) ` I)"
  shows "(\<lambda>x. INF i\<in>I. F i x) \<in> borel_measurable M"
proof cases
  assume "I = {}" then show ?thesis
    unfolding \<open>I = {}\<close> image_empty by simp
next
  assume "I \<noteq> {}"
  show ?thesis
  proof (rule borel_measurableI_ge)
    fix y
    have "{x \<in> space M. \<forall>i\<in>I. y \<le> F i x} \<in> sets M"
      by measurable
    also have "{x \<in> space M. \<forall>i\<in>I. y \<le> F i x} = {x \<in> space M. y \<le> (INF i\<in>I. F i x)}"
      by (simp add: le_cINF_iff \<open>I \<noteq> {}\<close> bdd cong: conj_cong)
    finally show "{x \<in> space M. y \<le> (INF i\<in>I. F i x)} \<in> sets M"  .
  qed
qed

lemma borel_measurable_lfp[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_linorder, linorder_topology, second_countable_topology})"
  assumes "sup_continuous F"
  assumes *: "\<And>f. f \<in> borel_measurable M \<Longrightarrow> F f \<in> borel_measurable M"
  shows "lfp F \<in> borel_measurable M"
proof -
  { fix i have "((F ^^ i) bot) \<in> borel_measurable M"
      by (induct i) (auto intro!: *) }
  then have "(\<lambda>x. SUP i. (F ^^ i) bot x) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. SUP i. (F ^^ i) bot x) = (SUP i. (F ^^ i) bot)"
    by (auto simp add: image_comp)
  also have "(SUP i. (F ^^ i) bot) = lfp F"
    by (rule sup_continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma borel_measurable_gfp[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_linorder, linorder_topology, second_countable_topology})"
  assumes "inf_continuous F"
  assumes *: "\<And>f. f \<in> borel_measurable M \<Longrightarrow> F f \<in> borel_measurable M"
  shows "gfp F \<in> borel_measurable M"
proof -
  { fix i have "((F ^^ i) top) \<in> borel_measurable M"
      by (induct i) (auto intro!: * simp: bot_fun_def) }
  then have "(\<lambda>x. INF i. (F ^^ i) top x) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. INF i. (F ^^ i) top x) = (INF i. (F ^^ i) top)"
    by (auto simp add: image_comp)
  also have "\<dots> = gfp F"
    by (rule inf_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

lemma borel_measurable_max[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. max (g x) (f x) :: 'b::{second_countable_topology, linorder_topology}) \<in> borel_measurable M"
  by (rule borel_measurableI_less) simp

lemma borel_measurable_min[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. min (g x) (f x) :: 'b::{second_countable_topology, linorder_topology}) \<in> borel_measurable M"
  by (rule borel_measurableI_greater) simp

lemma borel_measurable_Min[measurable (raw)]:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M) \<Longrightarrow> (\<lambda>x. Min ((\<lambda>i. f i x)`I) :: 'b::{second_countable_topology, linorder_topology}) \<in> borel_measurable M"
proof (induct I rule: finite_induct)
  case (insert i I) then show ?case
    by (cases "I = {}") auto
qed auto

lemma borel_measurable_Max[measurable (raw)]:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M) \<Longrightarrow> (\<lambda>x. Max ((\<lambda>i. f i x)`I) :: 'b::{second_countable_topology, linorder_topology}) \<in> borel_measurable M"
proof (induct I rule: finite_induct)
  case (insert i I) then show ?case
    by (cases "I = {}") auto
qed auto

lemma borel_measurable_sup[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. sup (g x) (f x) :: 'b::{lattice, second_countable_topology, linorder_topology}) \<in> borel_measurable M"
  unfolding sup_max by measurable

lemma borel_measurable_inf[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. inf (g x) (f x) :: 'b::{lattice, second_countable_topology, linorder_topology}) \<in> borel_measurable M"
  unfolding inf_min by measurable

lemma [measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology}"
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows borel_measurable_liminf: "(\<lambda>x. liminf (\<lambda>i. f i x)) \<in> borel_measurable M"
    and borel_measurable_limsup: "(\<lambda>x. limsup (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding liminf_SUP_INF limsup_INF_SUP using assms by auto

lemma measurable_convergent[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology}"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. convergent (\<lambda>i. f i x))"
  unfolding convergent_ereal by measurable

lemma sets_Collect_convergent[measurable]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. convergent (\<lambda>i. f i x)} \<in> sets M"
  by measurable

lemma borel_measurable_lim[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology}"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  have "\<And>x. lim (\<lambda>i. f i x) = (if convergent (\<lambda>i. f i x) then limsup (\<lambda>i. f i x) else (THE i. False))"
    by (simp add: lim_def convergent_def convergent_limsup_cl)
  then show ?thesis
    by simp
qed

lemma borel_measurable_LIMSEQ_order:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology}"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) \<longlonglongrightarrow> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> u' x = liminf (\<lambda>n. u n x)"
    using u' by (simp add: lim_imp_Liminf[symmetric])
  with u show ?thesis by (simp cong: measurable_cong)
qed

subsection \<open>Borel spaces on topological monoids\<close>

lemma borel_measurable_add[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, topological_monoid_add}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma borel_measurable_sum[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, topological_comm_monoid_add}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_suminf_order[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology, topological_comm_monoid_add}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. suminf (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

subsection \<open>Borel spaces on Euclidean spaces\<close>

lemma borel_measurable_inner[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_inner}"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x \<bullet> g x) \<in> borel_measurable M"
  using assms
  by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

notation
  eucl_less (infix "<e" 50)

lemma box_oc: "{x. a <e x \<and> x \<le> b} = {x. a <e x} \<inter> {..b}"
  and box_co: "{x. a \<le> x \<and> x <e b} = {a..} \<inter> {x. x <e b}"
  by auto

lemma eucl_ivals[measurable]:
  fixes a b :: "'a::ordered_euclidean_space"
  shows "{x. x <e a} \<in> sets borel"
    and "{x. a <e x} \<in> sets borel"
    and "{..a} \<in> sets borel"
    and "{a..} \<in> sets borel"
    and "{a..b} \<in> sets borel"
    and  "{x. a <e x \<and> x \<le> b} \<in> sets borel"
    and "{x. a \<le> x \<and>  x <e b} \<in> sets borel"
  unfolding box_oc box_co
  by (auto intro: borel_open borel_closed)

lemma
  fixes i :: "'a::{second_countable_topology, real_inner}"
  shows hafspace_less_borel: "{x. a < x \<bullet> i} \<in> sets borel"
    and hafspace_greater_borel: "{x. x \<bullet> i < a} \<in> sets borel"
    and hafspace_less_eq_borel: "{x. a \<le> x \<bullet> i} \<in> sets borel"
    and hafspace_greater_eq_borel: "{x. x \<bullet> i \<le> a} \<in> sets borel"
  by simp_all

lemma borel_eq_box:
  "borel = sigma UNIV (range (\<lambda> (a, b). box a b :: 'a :: euclidean_space set))"
    (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI1[OF borel_def])
  fix M :: "'a set" assume "M \<in> {S. open S}"
  then have "open M" by simp
  show "M \<in> ?SIGMA"
    apply (subst open_UNION_box[OF \<open>open M\<close>])
    apply (safe intro!: sets.countable_UN' countable_PiE countable_Collect)
    apply (auto intro: countable_rat)
    done
qed (auto simp: box_def)

lemma halfspace_gt_in_halfspace:
  assumes i: "i \<in> A"
  shows "{x::'a. a < x \<bullet> i} \<in>
    sigma_sets UNIV ((\<lambda> (a, i). {x::'a::euclidean_space. x \<bullet> i < a}) ` (UNIV \<times> A))"
  (is "?set \<in> ?SIGMA")
proof -
  interpret sigma_algebra UNIV ?SIGMA
    by (intro sigma_algebra_sigma_sets) simp_all
  have *: "?set = (\<Union>n. UNIV - {x::'a. x \<bullet> i < a + 1 / real (Suc n)})"
  proof (safe, simp_all add: not_less del: of_nat_Suc)
    fix x :: 'a assume "a < x \<bullet> i"
    with reals_Archimedean[of "x \<bullet> i - a"]
    obtain n where "a + 1 / real (Suc n) < x \<bullet> i"
      by (auto simp: field_simps)
    then show "\<exists>n. a + 1 / real (Suc n) \<le> x \<bullet> i"
      by (blast intro: less_imp_le)
  next
    fix x n
    have "a < a + 1 / real (Suc n)" by auto
    also assume "\<dots> \<le> x"
    finally show "a < x" .
  qed
  show "?set \<in> ?SIGMA" unfolding *
    by (auto intro!: Diff sigma_sets_Inter i)
qed

lemma borel_eq_halfspace_less:
  "borel = sigma UNIV ((\<lambda>(a, i). {x::'a::euclidean_space. x \<bullet> i < a}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_box])
  fix a b :: 'a
  have "box a b = {x\<in>space ?SIGMA. \<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i}"
    by (auto simp: box_def)
  also have "\<dots> \<in> sets ?SIGMA"
    by (intro sets.sets_Collect_conj sets.sets_Collect_finite_All sets.sets_Collect_const)
       (auto intro!: halfspace_gt_in_halfspace countable_PiE countable_rat)
  finally show "box a b \<in> sets ?SIGMA" .
qed auto

lemma borel_eq_halfspace_le:
  "borel = sigma UNIV ((\<lambda> (a, i). {x::'a::euclidean_space. x \<bullet> i \<le> a}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have i: "i \<in> Basis" by auto
  have *: "{x::'a. x\<bullet>i < a} = (\<Union>n. {x. x\<bullet>i \<le> a - 1/real (Suc n)})"
  proof (safe, simp_all del: of_nat_Suc)
    fix x::'a assume *: "x\<bullet>i < a"
    with reals_Archimedean[of "a - x\<bullet>i"]
    obtain n where "x \<bullet> i < a - 1 / (real (Suc n))"
      by (auto simp: field_simps)
    then show "\<exists>n. x \<bullet> i \<le> a - 1 / (real (Suc n))"
      by (blast intro: less_imp_le)
  next
    fix x::'a and n
    assume "x\<bullet>i \<le> a - 1 / real (Suc n)"
    also have "\<dots> < a" by auto
    finally show "x\<bullet>i < a" .
  qed
  show "{x. x\<bullet>i < a} \<in> ?SIGMA" unfolding *
    by (intro sets.countable_UN) (auto intro: i)
qed auto

lemma borel_eq_halfspace_ge:
  "borel = sigma UNIV ((\<lambda> (a, i). {x::'a::euclidean_space. a \<le> x \<bullet> i}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a :: real and i :: 'a assume i: "(a, i) \<in> UNIV \<times> Basis"
  have *: "{x::'a. x\<bullet>i < a} = space ?SIGMA - {x::'a. a \<le> x\<bullet>i}" by auto
  show "{x. x\<bullet>i < a} \<in> ?SIGMA" unfolding *
    using i by (intro sets.compl_sets) auto
qed auto

lemma borel_eq_halfspace_greater:
  "borel = sigma UNIV ((\<lambda> (a, i). {x::'a::euclidean_space. a < x \<bullet> i}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_le])
  fix a :: real and i :: 'a assume "(a, i) \<in> (UNIV \<times> Basis)"
  then have i: "i \<in> Basis" by auto
  have *: "{x::'a. x\<bullet>i \<le> a} = space ?SIGMA - {x::'a. a < x\<bullet>i}" by auto
  show "{x. x\<bullet>i \<le> a} \<in> ?SIGMA" unfolding *
    by (intro sets.compl_sets) (auto intro: i)
qed auto

lemma borel_eq_atMost:
  "borel = sigma UNIV (range (\<lambda>a. {..a::'a::ordered_euclidean_space}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have "i \<in> Basis" by auto
  then have *: "{x::'a. x\<bullet>i \<le> a} = (\<Union>k::nat. {.. (\<Sum>n\<in>Basis. (if n = i then a else real k)*\<^sub>R n)})"
  proof (safe, simp_all add: eucl_le[where 'a='a] split: if_split_asm)
    fix x :: 'a
    obtain k where "Max ((\<bullet>) x ` Basis) \<le> real k"
      using real_arch_simple by blast
    then have "\<And>i. i \<in> Basis \<Longrightarrow> x\<bullet>i \<le> real k"
      by (subst (asm) Max_le_iff) auto
    then show "\<exists>k::nat. \<forall>ia\<in>Basis. ia \<noteq> i \<longrightarrow> x \<bullet> ia \<le> real k"
      by (auto intro!: exI[of _ k])
  qed
  show "{x. x\<bullet>i \<le> a} \<in> ?SIGMA" unfolding *
    by (intro sets.countable_UN) auto
qed auto

lemma borel_eq_greaterThan:
  "borel = sigma UNIV (range (\<lambda>a::'a::ordered_euclidean_space. {x. a <e x}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have i: "i \<in> Basis" by auto
  have "{x::'a. x\<bullet>i \<le> a} = UNIV - {x::'a. a < x\<bullet>i}" by auto
  also have *: "{x::'a. a < x\<bullet>i} =
      (\<Union>k::nat. {x. (\<Sum>n\<in>Basis. (if n = i then a else -real k) *\<^sub>R n) <e x})" using i
  proof (safe, simp_all add: eucl_less_def split: if_split_asm)
    fix x :: 'a
    obtain k where k: "Max ((\<bullet>) (- x) ` Basis) < real k"
      using reals_Archimedean2 by blast
    { fix i :: 'a assume "i \<in> Basis"
      then have "-x\<bullet>i < real k"
        using k by (subst (asm) Max_less_iff) auto
      then have "- real k < x\<bullet>i" by simp }
    then show "\<exists>k::nat. \<forall>ia\<in>Basis. ia \<noteq> i \<longrightarrow> -real k < x \<bullet> ia"
      by (auto intro!: exI[of _ k])
  qed
  finally show "{x. x\<bullet>i \<le> a} \<in> ?SIGMA"
    apply (simp only:)
    apply (intro sets.countable_UN sets.Diff)
    apply (auto intro: sigma_sets_top)
    done
qed auto

lemma borel_eq_lessThan:
  "borel = sigma UNIV (range (\<lambda>a::'a::ordered_euclidean_space. {x. x <e a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_ge])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have i: "i \<in> Basis" by auto
  have "{x::'a. a \<le> x\<bullet>i} = UNIV - {x::'a. x\<bullet>i < a}" by auto
  also have *: "{x::'a. x\<bullet>i < a} = (\<Union>k::nat. {x. x <e (\<Sum>n\<in>Basis. (if n = i then a else real k) *\<^sub>R n)})" using \<open>i\<in> Basis\<close>
  proof (safe, simp_all add: eucl_less_def split: if_split_asm)
    fix x :: 'a
    obtain k where k: "Max ((\<bullet>) x ` Basis) < real k"
      using reals_Archimedean2 by blast
    { fix i :: 'a assume "i \<in> Basis"
      then have "x\<bullet>i < real k"
        using k by (subst (asm) Max_less_iff) auto
      then have "x\<bullet>i < real k" by simp }
    then show "\<exists>k::nat. \<forall>ia\<in>Basis. ia \<noteq> i \<longrightarrow> x \<bullet> ia < real k"
      by (auto intro!: exI[of _ k])
  qed
  finally show "{x. a \<le> x\<bullet>i} \<in> ?SIGMA"
    apply (simp only:)
    apply (intro sets.countable_UN sets.Diff)
    apply (auto intro: sigma_sets_top )
    done
qed auto

lemma borel_eq_atLeastAtMost:
  "borel = sigma UNIV (range (\<lambda>(a,b). {a..b} ::'a::ordered_euclidean_space set))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix a::'a
  have *: "{..a} = (\<Union>n::nat. {- real n *\<^sub>R One .. a})"
  proof (safe, simp_all add: eucl_le[where 'a='a])
    fix x :: 'a
    obtain k where k: "Max ((\<bullet>) (- x) ` Basis) \<le> real k"
      using real_arch_simple by blast
    { fix i :: 'a assume "i \<in> Basis"
      with k have "- x\<bullet>i \<le> real k"
        by (subst (asm) Max_le_iff) (auto simp: field_simps)
      then have "- real k \<le> x\<bullet>i" by simp }
    then show "\<exists>n::nat. \<forall>i\<in>Basis. - real n \<le> x \<bullet> i"
      by (auto intro!: exI[of _ k])
  qed
  show "{..a} \<in> ?SIGMA" unfolding *
    by (intro sets.countable_UN)
       (auto intro!: sigma_sets_top)
qed auto

lemma borel_set_induct[consumes 1, case_names empty interval compl union]:
  assumes "A \<in> sets borel"
  assumes empty: "P {}" and int: "\<And>a b. a \<le> b \<Longrightarrow> P {a..b}" and compl: "\<And>A. A \<in> sets borel \<Longrightarrow> P A \<Longrightarrow> P (-A)" and
          un: "\<And>f. disjoint_family f \<Longrightarrow> (\<And>i. f i \<in> sets borel) \<Longrightarrow>  (\<And>i. P (f i)) \<Longrightarrow> P (\<Union>i::nat. f i)"
  shows "P (A::real set)"
proof -
  let ?G = "range (\<lambda>(a,b). {a..b::real})"
  have "Int_stable ?G" "?G \<subseteq> Pow UNIV" "A \<in> sigma_sets UNIV ?G"
      using assms(1) by (auto simp add: borel_eq_atLeastAtMost Int_stable_def)
  thus ?thesis
  proof (induction rule: sigma_sets_induct_disjoint)
    case (union f)
      from union.hyps(2) have "\<And>i. f i \<in> sets borel" by (auto simp: borel_eq_atLeastAtMost)
      with union show ?case by (auto intro: un)
  next
    case (basic A)
    then obtain a b where "A = {a .. b}" by auto
    then show ?case
      by (cases "a \<le> b") (auto intro: int empty)
  qed (auto intro: empty compl simp: Compl_eq_Diff_UNIV[symmetric] borel_eq_atLeastAtMost)
qed

lemma borel_sigma_sets_Ioc: "borel = sigma UNIV (range (\<lambda>(a, b). {a <.. b::real}))"
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix i :: real
  have "{..i} = (\<Union>j::nat. {-j <.. i})"
    by (auto simp: minus_less_iff reals_Archimedean2)
  also have "\<dots> \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))"
    by (intro sets.countable_nat_UN) auto
  finally show "{..i} \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))" .
qed simp

lemma eucl_lessThan: "{x::real. x <e a} = lessThan a"
  by (simp add: eucl_less_def lessThan_def)

lemma borel_eq_atLeastLessThan:
  "borel = sigma UNIV (range (\<lambda>(a, b). {a ..< b :: real}))" (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_lessThan])
  have move_uminus: "\<And>x y::real. -x \<le> y \<longleftrightarrow> -y \<le> x" by auto
  fix x :: real
  have "{..<x} = (\<Union>i::nat. {-real i ..< x})"
    by (auto simp: move_uminus real_arch_simple)
  then show "{y. y <e x} \<in> ?SIGMA"
    by (auto intro: sigma_sets.intros(2-) simp: eucl_lessThan)
qed auto

lemma borel_measurable_halfspacesI:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  assumes F: "borel = sigma UNIV (F ` (UNIV \<times> Basis))"
  and S_eq: "\<And>a i. S a i = f -` F (a,i) \<inter> space M"
  shows "f \<in> borel_measurable M = (\<forall>i\<in>Basis. \<forall>a::real. S a i \<in> sets M)"
proof safe
  fix a :: real and i :: 'b assume i: "i \<in> Basis" and f: "f \<in> borel_measurable M"
  then show "S a i \<in> sets M" unfolding assms
    by (auto intro!: measurable_sets simp: assms(1))
next
  assume a: "\<forall>i\<in>Basis. \<forall>a. S a i \<in> sets M"
  then show "f \<in> borel_measurable M"
    by (auto intro!: measurable_measure_of simp: S_eq F)
qed

lemma borel_measurable_iff_halfspace_le:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. f w \<bullet> i \<le> a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_le]) auto

lemma borel_measurable_iff_halfspace_less:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. f w \<bullet> i < a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_less]) auto

lemma borel_measurable_iff_halfspace_ge:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. a \<le> f w \<bullet> i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_ge]) auto

lemma borel_measurable_iff_halfspace_greater:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. a < f w \<bullet> i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_greater]) auto

lemma borel_measurable_iff_le:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M)"
  using borel_measurable_iff_halfspace_le[where 'c=real] by simp

lemma borel_measurable_iff_less:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w < a} \<in> sets M)"
  using borel_measurable_iff_halfspace_less[where 'c=real] by simp

lemma borel_measurable_iff_ge:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a \<le> f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_ge[where 'c=real]
  by simp

lemma borel_measurable_iff_greater:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a < f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_greater[where 'c=real] by simp

lemma borel_measurable_euclidean_space:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i\<in>Basis. (\<lambda>x. f x \<bullet> i) \<in> borel_measurable M)"
proof safe
  assume f: "\<forall>i\<in>Basis. (\<lambda>x. f x \<bullet> i) \<in> borel_measurable M"
  then show "f \<in> borel_measurable M"
    by (subst borel_measurable_iff_halfspace_le) auto
qed auto

subsection "Borel measurable operators"

lemma borel_measurable_norm[measurable]: "norm \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_sgn [measurable]: "(sgn::'a::real_normed_vector \<Rightarrow> 'a) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_countable_exceptions[where X="{0}"])
     (auto intro!: continuous_on_sgn continuous_on_id)

lemma borel_measurable_uminus[measurable (raw)]:
  fixes g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. - g x) \<in> borel_measurable M"
  by (rule borel_measurable_continuous_on[OF _ g]) (intro continuous_intros)

lemma borel_measurable_diff[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
  using borel_measurable_add [of f M "- g"] assms by (simp add: fun_Compl_def)

lemma borel_measurable_times[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_algebra}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma borel_measurable_prod[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, real_normed_field}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_dist[measurable (raw)]:
  fixes g f :: "'a \<Rightarrow> 'b::{second_countable_topology, metric_space}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. dist (f x) (g x)) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma borel_measurable_scaleR[measurable (raw)]:
  fixes g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x *\<^sub>R g x) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma borel_measurable_uminus_eq [simp]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  shows "(\<lambda>x. - f x) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M" (is "?l = ?r")
proof
  assume ?l from borel_measurable_uminus[OF this] show ?r by simp
qed auto

lemma affine_borel_measurable_vector:
  fixes f :: "'a \<Rightarrow> 'x::real_normed_vector"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. a + b *\<^sub>R f x) \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S :: "'x set" assume "open S"
  show "(\<lambda>x. a + b *\<^sub>R f x) -` S \<inter> space M \<in> sets M"
  proof cases
    assume "b \<noteq> 0"
    with \<open>open S\<close> have "open ((\<lambda>x. (- a + x) /\<^sub>R b) ` S)" (is "open ?S")
      using open_affinity [of S "inverse b" "- a /\<^sub>R b"]
      by (auto simp: algebra_simps)
    hence "?S \<in> sets borel" by auto
    moreover
    from \<open>b \<noteq> 0\<close> have "(\<lambda>x. a + b *\<^sub>R f x) -` S = f -` ?S"
      apply auto by (rule_tac x="a + b *\<^sub>R f x" in image_eqI, simp_all)
    ultimately show ?thesis using assms unfolding in_borel_measurable_borel
      by auto
  qed simp
qed

lemma borel_measurable_const_scaleR[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. b *\<^sub>R f x ::'a::real_normed_vector) \<in> borel_measurable M"
  using affine_borel_measurable_vector[of f M 0 b] by simp

lemma borel_measurable_const_add[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. a + f x ::'a::real_normed_vector) \<in> borel_measurable M"
  using affine_borel_measurable_vector[of f M a 1] by simp

lemma borel_measurable_inverse[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. inverse (f x)) \<in> borel_measurable M"
  apply (rule measurable_compose[OF f])
  apply (rule borel_measurable_continuous_countable_exceptions[of "{0}"])
  apply (auto intro!: continuous_on_inverse continuous_on_id)
  done

lemma borel_measurable_divide[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    (\<lambda>x. f x / g x::'b::{second_countable_topology, real_normed_div_algebra}) \<in> borel_measurable M"
  by (simp add: divide_inverse)

lemma borel_measurable_abs[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. \<bar>f x :: real\<bar>) \<in> borel_measurable M"
  unfolding abs_real_def by simp

lemma borel_measurable_nth[measurable (raw)]:
  "(\<lambda>x::real^'n. x $ i) \<in> borel_measurable borel"
  by (simp add: cart_eq_inner_axis)

lemma convex_measurable:
  fixes A :: "'a :: euclidean_space set"
  shows "X \<in> borel_measurable M \<Longrightarrow> X ` space M \<subseteq> A \<Longrightarrow> open A \<Longrightarrow> convex_on A q \<Longrightarrow>
    (\<lambda>x. q (X x)) \<in> borel_measurable M"
  by (rule measurable_compose[where f=X and N="restrict_space borel A"])
     (auto intro!: borel_measurable_continuous_on_restrict convex_on_continuous measurable_restrict_space2)

lemma borel_measurable_ln[measurable (raw)]:
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. ln (f x :: real)) \<in> borel_measurable M"
  apply (rule measurable_compose[OF f])
  apply (rule borel_measurable_continuous_countable_exceptions[of "{0}"])
  apply (auto intro!: continuous_on_ln continuous_on_id)
  done

lemma borel_measurable_log[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. log (g x) (f x)) \<in> borel_measurable M"
  unfolding log_def by auto

lemma borel_measurable_exp[measurable]:
  "(exp::'a::{real_normed_field,banach}\<Rightarrow>'a) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_at_imp_continuous_on ballI isCont_exp)

lemma measurable_real_floor[measurable]:
  "(floor :: real \<Rightarrow> int) \<in> measurable borel (count_space UNIV)"
proof -
  have "\<And>a x. \<lfloor>x\<rfloor> = a \<longleftrightarrow> (real_of_int a \<le> x \<and> x < real_of_int (a + 1))"
    by (auto intro: floor_eq2)
  then show ?thesis
    by (auto simp: vimage_def measurable_count_space_eq2_countable)
qed

lemma measurable_real_ceiling[measurable]:
  "(ceiling :: real \<Rightarrow> int) \<in> measurable borel (count_space UNIV)"
  unfolding ceiling_def[abs_def] by simp

lemma borel_measurable_real_floor: "(\<lambda>x::real. real_of_int \<lfloor>x\<rfloor>) \<in> borel_measurable borel"
  by simp

lemma borel_measurable_root [measurable]: "root n \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_sqrt [measurable]: "sqrt \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_power [measurable (raw)]:
  fixes f :: "_ \<Rightarrow> 'b::{power,real_normed_algebra}"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. (f x) ^ n) \<in> borel_measurable M"
  by (intro borel_measurable_continuous_on [OF _ f] continuous_intros)

lemma borel_measurable_Re [measurable]: "Re \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_Im [measurable]: "Im \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_of_real [measurable]: "(of_real :: _ \<Rightarrow> (_::real_normed_algebra)) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_sin [measurable]: "(sin :: _ \<Rightarrow> (_::{real_normed_field,banach})) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_cos [measurable]: "(cos :: _ \<Rightarrow> (_::{real_normed_field,banach})) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma borel_measurable_arctan [measurable]: "arctan \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma\<^marker>\<open>tag important\<close> borel_measurable_complex_iff:
  "f \<in> borel_measurable M \<longleftrightarrow>
    (\<lambda>x. Re (f x)) \<in> borel_measurable M \<and> (\<lambda>x. Im (f x)) \<in> borel_measurable M"
  apply auto
  apply (subst fun_complex_eq)
  apply (intro borel_measurable_add)
  apply auto
  done

lemma powr_real_measurable [measurable]:
  assumes "f \<in> measurable M borel" "g \<in> measurable M borel"
  shows   "(\<lambda>x. f x powr g x :: real) \<in> measurable M borel"
  using assms by (simp_all add: powr_def)

lemma measurable_of_bool[measurable]: "of_bool \<in> count_space UNIV \<rightarrow>\<^sub>M borel"
  by simp

subsection "Borel space on the extended reals"

lemma borel_measurable_ereal[measurable (raw)]:
  assumes f: "f \<in> borel_measurable M" shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  using continuous_on_ereal f by (rule borel_measurable_continuous_on) (rule continuous_on_id)

lemma borel_measurable_real_of_ereal[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. real_of_ereal (f x)) \<in> borel_measurable M"
  apply (rule measurable_compose[OF f])
  apply (rule borel_measurable_continuous_countable_exceptions[of "{\<infinity>, -\<infinity> }"])
  apply (auto intro: continuous_on_real simp: Compl_eq_Diff_UNIV)
  done

lemma borel_measurable_ereal_cases:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real_of_ereal (f x)))) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>x. if f x = \<infinity> then H \<infinity> else if f x = - \<infinity> then H (-\<infinity>) else H (ereal (real_of_ereal (f x)))"
  { fix x have "H (f x) = ?F x" by (cases "f x") auto }
  with f H show ?thesis by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f[measurable]: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_abs[measurable(raw)]: "(\<lambda>x. \<bar>f x\<bar>) \<in> borel_measurable M"
    and borel_measurable_ereal_inverse[measurable(raw)]: "(\<lambda>x. inverse (f x) :: ereal) \<in> borel_measurable M"
    and borel_measurable_uminus_ereal[measurable(raw)]: "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M"
  by (auto simp del: abs_real_of_ereal simp: borel_measurable_ereal_cases[OF f] measurable_If)

lemma borel_measurable_uminus_eq_ereal[simp]:
  "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M" (is "?l = ?r")
proof
  assume ?l from borel_measurable_uminus_ereal[OF this] show ?r by simp
qed auto

lemma set_Collect_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "{x \<in> space M. H (ereal (real_of_ereal (f x))) (ereal (real_of_ereal (g x)))} \<in> sets M"
    "{x \<in> space borel. H (-\<infinity>) (ereal x)} \<in> sets borel"
    "{x \<in> space borel. H (\<infinity>) (ereal x)} \<in> sets borel"
    "{x \<in> space borel. H (ereal x) (-\<infinity>)} \<in> sets borel"
    "{x \<in> space borel. H (ereal x) (\<infinity>)} \<in> sets borel"
  shows "{x \<in> space M. H (f x) (g x)} \<in> sets M"
proof -
  let ?G = "\<lambda>y x. if g x = \<infinity> then H y \<infinity> else if g x = -\<infinity> then H y (-\<infinity>) else H y (ereal (real_of_ereal (g x)))"
  let ?F = "\<lambda>x. if f x = \<infinity> then ?G \<infinity> x else if f x = -\<infinity> then ?G (-\<infinity>) x else ?G (ereal (real_of_ereal (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  note * = this
  from assms show ?thesis
    by (subst *) (simp del: space_borel split del: if_split)
qed

lemma borel_measurable_ereal_iff:
  shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M"
proof
  assume "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  from borel_measurable_real_of_ereal[OF this]
  show "f \<in> borel_measurable M" by auto
qed auto

lemma borel_measurable_erealD[measurable_dest]:
  "(\<lambda>x. ereal (f x)) \<in> borel_measurable M \<Longrightarrow> g \<in> measurable N M \<Longrightarrow> (\<lambda>x. f (g x)) \<in> borel_measurable N"
  unfolding borel_measurable_ereal_iff by simp

theorem borel_measurable_ereal_iff_real:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "f \<in> borel_measurable M \<longleftrightarrow>
    ((\<lambda>x. real_of_ereal (f x)) \<in> borel_measurable M \<and> f -` {\<infinity>} \<inter> space M \<in> sets M \<and> f -` {-\<infinity>} \<inter> space M \<in> sets M)"
proof safe
  assume *: "(\<lambda>x. real_of_ereal (f x)) \<in> borel_measurable M" "f -` {\<infinity>} \<inter> space M \<in> sets M" "f -` {-\<infinity>} \<inter> space M \<in> sets M"
  have "f -` {\<infinity>} \<inter> space M = {x\<in>space M. f x = \<infinity>}" "f -` {-\<infinity>} \<inter> space M = {x\<in>space M. f x = -\<infinity>}" by auto
  with * have **: "{x\<in>space M. f x = \<infinity>} \<in> sets M" "{x\<in>space M. f x = -\<infinity>} \<in> sets M" by simp_all
  let ?f = "\<lambda>x. if f x = \<infinity> then \<infinity> else if f x = -\<infinity> then -\<infinity> else ereal (real_of_ereal (f x))"
  have "?f \<in> borel_measurable M" using * ** by (intro measurable_If) auto
  also have "?f = f" by (auto simp: fun_eq_iff ereal_real)
  finally show "f \<in> borel_measurable M" .
qed simp_all

lemma borel_measurable_ereal_iff_Iio:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..< a} \<inter> space M \<in> sets M)"
  by (auto simp: borel_Iio measurable_iff_measure_of)

lemma borel_measurable_ereal_iff_Ioi:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a <..} \<inter> space M \<in> sets M)"
  by (auto simp: borel_Ioi measurable_iff_measure_of)

lemma vimage_sets_compl_iff:
  "f -` A \<inter> space M \<in> sets M \<longleftrightarrow> f -` (- A) \<inter> space M \<in> sets M"
proof -
  { fix A assume "f -` A \<inter> space M \<in> sets M"
    moreover have "f -` (- A) \<inter> space M = space M - f -` A \<inter> space M" by auto
    ultimately have "f -` (- A) \<inter> space M \<in> sets M" by auto }
  from this[of A] this[of "-A"] show ?thesis
    by (metis double_complement)
qed

lemma borel_measurable_iff_Iic_ereal:
  "(f::'a\<Rightarrow>ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..a} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_ereal_iff_Ioi vimage_sets_compl_iff[where A="{a <..}" for a] by simp

lemma borel_measurable_iff_Ici_ereal:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a..} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_ereal_iff_Iio vimage_sets_compl_iff[where A="{..< a}" for a] by simp

lemma borel_measurable_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real_of_ereal (f x))) (ereal (real_of_ereal (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (-\<infinity>) (ereal (real_of_ereal (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (\<infinity>) (ereal (real_of_ereal (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real_of_ereal (f x))) (-\<infinity>)) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real_of_ereal (f x))) (\<infinity>)) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?G = "\<lambda>y x. if g x = \<infinity> then H y \<infinity> else if g x = - \<infinity> then H y (-\<infinity>) else H y (ereal (real_of_ereal (g x)))"
  let ?F = "\<lambda>x. if f x = \<infinity> then ?G \<infinity> x else if f x = - \<infinity> then ?G (-\<infinity>) x else ?G (ereal (real_of_ereal (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  note * = this
  from assms show ?thesis unfolding * by simp
qed

lemma [measurable(raw)]:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows borel_measurable_ereal_add: "(\<lambda>x. f x + g x) \<in> borel_measurable M"
    and borel_measurable_ereal_times: "(\<lambda>x. f x * g x) \<in> borel_measurable M"
  by (simp_all add: borel_measurable_ereal2)

lemma [measurable(raw)]:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows borel_measurable_ereal_diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    and borel_measurable_ereal_divide: "(\<lambda>x. f x / g x) \<in> borel_measurable M"
  using assms by (simp_all add: minus_ereal_def divide_ereal_def)

lemma borel_measurable_ereal_sum[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
  using assms by (induction S rule: infinite_finite_induct) auto

lemma borel_measurable_ereal_prod[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
  using assms by (induction S rule: infinite_finite_induct) auto

lemma borel_measurable_extreal_suminf[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. (\<Sum>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

subsection "Borel space on the extended non-negative reals"

text \<open> \<^type>\<open>ennreal\<close> is a topological monoid, so no rules for plus are required, also all order
  statements are usually done on type classes. \<close>

lemma measurable_enn2ereal[measurable]: "enn2ereal \<in> borel \<rightarrow>\<^sub>M borel"
  by (intro borel_measurable_continuous_onI continuous_on_enn2ereal)

lemma measurable_e2ennreal[measurable]: "e2ennreal \<in> borel \<rightarrow>\<^sub>M borel"
  by (intro borel_measurable_continuous_onI continuous_on_e2ennreal)

lemma borel_measurable_enn2real[measurable (raw)]:
  "f \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>x. enn2real (f x)) \<in> M \<rightarrow>\<^sub>M borel"
  unfolding enn2real_def[abs_def] by measurable

definition\<^marker>\<open>tag important\<close> [simp]: "is_borel f M \<longleftrightarrow> f \<in> borel_measurable M"

lemma is_borel_transfer[transfer_rule]: "rel_fun (rel_fun (=) pcr_ennreal) (=) is_borel is_borel"
  unfolding is_borel_def[abs_def]
proof (safe intro!: rel_funI ext dest!: rel_fun_eq_pcr_ennreal[THEN iffD1])
  fix f and M :: "'a measure"
  show "f \<in> borel_measurable M" if f: "enn2ereal \<circ> f \<in> borel_measurable M"
    using measurable_compose[OF f measurable_e2ennreal] by simp
qed simp

context
  includes ennreal.lifting
begin

lemma measurable_ennreal[measurable]: "ennreal \<in> borel \<rightarrow>\<^sub>M borel"
  unfolding is_borel_def[symmetric]
  by transfer simp

lemma borel_measurable_ennreal_iff[simp]:
  assumes [simp]: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
  shows "(\<lambda>x. ennreal (f x)) \<in> M \<rightarrow>\<^sub>M borel \<longleftrightarrow> f \<in> M \<rightarrow>\<^sub>M borel"
proof safe
  assume "(\<lambda>x. ennreal (f x)) \<in> M \<rightarrow>\<^sub>M borel"
  then have "(\<lambda>x. enn2real (ennreal (f x))) \<in> M \<rightarrow>\<^sub>M borel"
    by measurable
  then show "f \<in> M \<rightarrow>\<^sub>M borel"
    by (rule measurable_cong[THEN iffD1, rotated]) auto
qed measurable

lemma borel_measurable_times_ennreal[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> ennreal"
  shows "f \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> g \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>x. f x * g x) \<in> M \<rightarrow>\<^sub>M borel"
  unfolding is_borel_def[symmetric] by transfer simp

lemma borel_measurable_inverse_ennreal[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "f \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>x. inverse (f x)) \<in> M \<rightarrow>\<^sub>M borel"
  unfolding is_borel_def[symmetric] by transfer simp

lemma borel_measurable_divide_ennreal[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "f \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> g \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>x. f x / g x) \<in> M \<rightarrow>\<^sub>M borel"
  unfolding divide_ennreal_def by simp

lemma borel_measurable_minus_ennreal[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "f \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> g \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>x. f x - g x) \<in> M \<rightarrow>\<^sub>M borel"
  unfolding is_borel_def[symmetric] by transfer simp

lemma borel_measurable_power_ennreal [measurable (raw)]:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. (f x) ^ n) \<in> borel_measurable M"
  by (induction n) (use f in auto)

lemma borel_measurable_prod_ennreal[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
  using assms by (induction S rule: infinite_finite_induct) auto

end

hide_const (open) is_borel

subsection \<open>LIMSEQ is borel measurable\<close>

lemma borel_measurable_LIMSEQ_real:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) \<longlonglongrightarrow> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> liminf (\<lambda>n. ereal (u n x)) = ereal (u' x)"
    using u' by (simp add: lim_imp_Liminf)
  moreover from u have "(\<lambda>x. liminf (\<lambda>n. ereal (u n x))) \<in> borel_measurable M"
    by auto
  ultimately show ?thesis by (simp cong: measurable_cong add: borel_measurable_ereal_iff)
qed

lemma borel_measurable_LIMSEQ_metric:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  assumes lim: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. f i x) \<longlonglongrightarrow> g x"
  shows "g \<in> borel_measurable M"
  unfolding borel_eq_closed
proof (safe intro!: measurable_measure_of)
  fix A :: "'b set" assume "closed A"

  have [measurable]: "(\<lambda>x. infdist (g x) A) \<in> borel_measurable M"
  proof (rule borel_measurable_LIMSEQ_real)
    show "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. infdist (f i x) A) \<longlonglongrightarrow> infdist (g x) A"
      by (intro tendsto_infdist lim)
    show "\<And>i. (\<lambda>x. infdist (f i x) A) \<in> borel_measurable M"
      by (intro borel_measurable_continuous_on[where f="\<lambda>x. infdist x A"]
        continuous_at_imp_continuous_on ballI continuous_infdist continuous_ident) auto
  qed

  show "g -` A \<inter> space M \<in> sets M"
  proof cases
    assume "A \<noteq> {}"
    then have "\<And>x. infdist x A = 0 \<longleftrightarrow> x \<in> A"
      using \<open>closed A\<close> by (simp add: in_closed_iff_infdist_zero)
    then have "g -` A \<inter> space M = {x\<in>space M. infdist (g x) A = 0}"
      by auto
    also have "\<dots> \<in> sets M"
      by measurable
    finally show ?thesis .
  qed simp
qed auto

lemma sets_Collect_Cauchy[measurable]:
  fixes f :: "nat \<Rightarrow> 'a => 'b::{metric_space, second_countable_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. Cauchy (\<lambda>i. f i x)} \<in> sets M"
  unfolding metric_Cauchy_iff2 using f by auto

lemma borel_measurable_lim_metric[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  define u' where "u' x = lim (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)" for x
  then have *: "\<And>x. lim (\<lambda>i. f i x) = (if Cauchy (\<lambda>i. f i x) then u' x else (THE x. False))"
    by (auto simp: lim_def convergent_eq_Cauchy[symmetric])
  have "u' \<in> borel_measurable M"
  proof (rule borel_measurable_LIMSEQ_metric)
    fix x
    have "convergent (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)"
      by (cases "Cauchy (\<lambda>i. f i x)")
         (auto simp add: convergent_eq_Cauchy[symmetric] convergent_def)
    then show "(\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0) \<longlonglongrightarrow> u' x"
      unfolding u'_def
      by (rule convergent_LIMSEQ_iff[THEN iffD1])
  qed measurable
  then show ?thesis
    unfolding * by measurable
qed

lemma borel_measurable_suminf[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. suminf (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

lemma Collect_closed_imp_pred_borel: "closed {x. P x} \<Longrightarrow> Measurable.pred borel P"
  by (simp add: pred_def)

(* Proof by Jeremy Avigad and Luke Serafin *)
lemma isCont_borel_pred[measurable]:
  fixes f :: "'b::metric_space \<Rightarrow> 'a::metric_space"
  shows "Measurable.pred borel (isCont f)"
proof (subst measurable_cong)
  let ?I = "\<lambda>j. inverse(real (Suc j))"
  show "isCont f x = (\<forall>i. \<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i)" for x
    unfolding continuous_at_eps_delta
  proof safe
    fix i assume "\<forall>e>0. \<exists>d>0. \<forall>y. dist y x < d \<longrightarrow> dist (f y) (f x) < e"
    moreover have "0 < ?I i / 2"
      by simp
    ultimately obtain d where d: "0 < d" "\<And>y. dist x y < d \<Longrightarrow> dist (f y) (f x) < ?I i / 2"
      by (metis dist_commute)
    then obtain j where j: "?I j < d"
      by (metis reals_Archimedean)

    show "\<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i"
    proof (safe intro!: exI[where x=j])
      fix y z assume *: "dist x y < ?I j" "dist x z < ?I j"
      have "dist (f y) (f z) \<le> dist (f y) (f x) + dist (f z) (f x)"
        by (rule dist_triangle2)
      also have "\<dots> < ?I i / 2 + ?I i / 2"
        by (intro add_strict_mono d less_trans[OF _ j] *)
      also have "\<dots> \<le> ?I i"
        by (simp add: field_simps)
      finally show "dist (f y) (f z) \<le> ?I i"
        by simp
    qed
  next
    fix e::real assume "0 < e"
    then obtain n where n: "?I n < e"
      by (metis reals_Archimedean)
    assume "\<forall>i. \<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i"
    from this[THEN spec, of "Suc n"]
    obtain j where j: "\<And>y z. dist x y < ?I j \<Longrightarrow> dist x z < ?I j \<Longrightarrow> dist (f y) (f z) \<le> ?I (Suc n)"
      by auto

    show "\<exists>d>0. \<forall>y. dist y x < d \<longrightarrow> dist (f y) (f x) < e"
    proof (safe intro!: exI[of _ "?I j"])
      fix y assume "dist y x < ?I j"
      then have "dist (f y) (f x) \<le> ?I (Suc n)"
        by (intro j) (auto simp: dist_commute)
      also have "?I (Suc n) < ?I n"
        by simp
      also note n
      finally show "dist (f y) (f x) < e" .
    qed simp
  qed
qed (intro pred_intros_countable closed_Collect_all closed_Collect_le open_Collect_less
           Collect_closed_imp_pred_borel closed_Collect_imp open_Collect_conj continuous_intros)

lemma isCont_borel:
  fixes f :: "'b::metric_space \<Rightarrow> 'a::metric_space"
  shows "{x. isCont f x} \<in> sets borel"
  by simp

lemma is_real_interval:
  assumes S: "is_interval S"
  shows "\<exists>a b::real. S = {} \<or> S = UNIV \<or> S = {..<b} \<or> S = {..b} \<or> S = {a<..} \<or> S = {a..} \<or>
    S = {a<..<b} \<or> S = {a<..b} \<or> S = {a..<b} \<or> S = {a..b}"
  using S unfolding is_interval_1 by (blast intro: interval_cases)

lemma real_interval_borel_measurable:
  assumes "is_interval (S::real set)"
  shows "S \<in> sets borel"
proof -
  from assms is_real_interval have "\<exists>a b::real. S = {} \<or> S = UNIV \<or> S = {..<b} \<or> S = {..b} \<or>
    S = {a<..} \<or> S = {a..} \<or> S = {a<..<b} \<or> S = {a<..b} \<or> S = {a..<b} \<or> S = {a..b}" by auto
  then show ?thesis
    by auto
qed

text \<open>The next lemmas hold in any second countable linorder (including ennreal or ereal for instance),
but in the current state they are restricted to reals.\<close>

lemma borel_measurable_mono_on_fnc:
  fixes f :: "real \<Rightarrow> real" and A :: "real set"
  assumes "mono_on f A"
  shows "f \<in> borel_measurable (restrict_space borel A)"
  apply (rule measurable_restrict_countable[OF mono_on_ctble_discont[OF assms]])
  apply (auto intro!: image_eqI[where x="{x}" for x] simp: sets_restrict_space)
  apply (auto simp add: sets_restrict_restrict_space continuous_on_eq_continuous_within
              cong: measurable_cong_sets
              intro!: borel_measurable_continuous_on_restrict intro: continuous_within_subset)
  done

lemma borel_measurable_piecewise_mono:
  fixes f::"real \<Rightarrow> real" and C::"real set set"
  assumes "countable C" "\<And>c. c \<in> C \<Longrightarrow> c \<in> sets borel" "\<And>c. c \<in> C \<Longrightarrow> mono_on f c" "(\<Union>C) = UNIV"
  shows "f \<in> borel_measurable borel"
  by (rule measurable_piecewise_restrict[of C], auto intro: borel_measurable_mono_on_fnc simp: assms)

lemma borel_measurable_mono:
  fixes f :: "real \<Rightarrow> real"
  shows "mono f \<Longrightarrow> f \<in> borel_measurable borel"
  using borel_measurable_mono_on_fnc[of f UNIV] by (simp add: mono_def mono_on_def)

lemma measurable_bdd_below_real[measurable (raw)]:
  fixes F :: "'a \<Rightarrow> 'i \<Rightarrow> real"
  assumes [simp]: "countable I" and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> M \<rightarrow>\<^sub>M borel"
  shows "Measurable.pred M (\<lambda>x. bdd_below ((\<lambda>i. F i x)`I))"
proof (subst measurable_cong)
  show "bdd_below ((\<lambda>i. F i x)`I) \<longleftrightarrow> (\<exists>q\<in>\<int>. \<forall>i\<in>I. q \<le> F i x)" for x
    by (auto simp: bdd_below_def intro!: bexI[of _ "of_int (floor _)"] intro: order_trans of_int_floor_le)
  show "Measurable.pred M (\<lambda>w. \<exists>q\<in>\<int>. \<forall>i\<in>I. q \<le> F i w)"
    using countable_int by measurable
qed

lemma borel_measurable_cINF_real[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> real"
  assumes [simp]: "countable I"
  assumes F[measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. INF i\<in>I. F i x) \<in> borel_measurable M"
proof (rule measurable_piecewise_restrict)
  let ?\<Omega> = "{x\<in>space M. bdd_below ((\<lambda>i. F i x)`I)}"
  show "countable {?\<Omega>, - ?\<Omega>}" "space M \<subseteq> \<Union>{?\<Omega>, - ?\<Omega>}" "\<And>X. X \<in> {?\<Omega>, - ?\<Omega>} \<Longrightarrow> X \<inter> space M \<in> sets M"
    by auto
  fix X assume "X \<in> {?\<Omega>, - ?\<Omega>}" then show "(\<lambda>x. INF i\<in>I. F i x) \<in> borel_measurable (restrict_space M X)"
  proof safe
    show "(\<lambda>x. INF i\<in>I. F i x) \<in> borel_measurable (restrict_space M ?\<Omega>)"
      by (intro borel_measurable_cINF measurable_restrict_space1 F)
         (auto simp: space_restrict_space)
    show "(\<lambda>x. INF i\<in>I. F i x) \<in> borel_measurable (restrict_space M (-?\<Omega>))"
    proof (subst measurable_cong)
      fix x assume "x \<in> space (restrict_space M (-?\<Omega>))"
      then have "\<not> (\<forall>i\<in>I. - F i x \<le> y)" for y
        by (auto simp: space_restrict_space bdd_above_def bdd_above_uminus[symmetric])
      then show "(INF i\<in>I. F i x) = - (THE x. False)"
        by (auto simp: space_restrict_space Inf_real_def Sup_real_def Least_def simp del: Set.ball_simps(10))
    qed simp
  qed
qed

lemma borel_Ici: "borel = sigma UNIV (range (\<lambda>x::real. {x ..}))"
proof (safe intro!: borel_eq_sigmaI1[OF borel_Iio])
  fix x :: real
  have eq: "{..<x} = space (sigma UNIV (range atLeast)) - {x ..}"
    by auto
  show "{..<x} \<in> sets (sigma UNIV (range atLeast))"
    unfolding eq by (intro sets.compl_sets) auto
qed auto

lemma borel_measurable_pred_less[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  shows "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> Measurable.pred M (\<lambda>w. f w < g w)"
  unfolding Measurable.pred_def by (rule borel_measurable_less)

no_notation
  eucl_less (infix "<e" 50)

lemma borel_measurable_Max2[measurable (raw)]:
  fixes f::"_ \<Rightarrow> _ \<Rightarrow> 'a::{second_countable_topology, dense_linorder, linorder_topology}"
  assumes "finite I"
    and [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. Max{f i x |i. i \<in> I}) \<in> borel_measurable M"
  by (simp add: borel_measurable_Max[OF assms(1), where ?f=f and ?M=M] Setcompr_eq_image)

lemma measurable_compose_n [measurable (raw)]:
  assumes "T \<in> measurable M M"
  shows "(T^^n) \<in> measurable M M"
by (induction n, auto simp add: measurable_compose[OF _ assms])

lemma measurable_real_imp_nat:
  fixes f::"'a \<Rightarrow> nat"
  assumes [measurable]: "(\<lambda>x. real(f x)) \<in> borel_measurable M"
  shows "f \<in> measurable M (count_space UNIV)"
proof -
  let ?g = "(\<lambda>x. real(f x))"
  have "\<And>(n::nat). ?g-`({real n}) \<inter> space M = f-`{n} \<inter> space M" by auto
  moreover have "\<And>(n::nat). ?g-`({real n}) \<inter> space M \<in> sets M" using assms by measurable
  ultimately have "\<And>(n::nat). f-`{n} \<inter> space M \<in> sets M" by simp
  then show ?thesis using measurable_count_space_eq2_countable by blast
qed

lemma measurable_equality_set [measurable]:
  fixes f g::"_\<Rightarrow> 'a::{second_countable_topology, t2_space}"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x = g x} \<in> sets M"

proof -
  define A where "A = {x \<in> space M. f x = g x}"
  define B where "B = {y. \<exists>x::'a. y = (x,x)}"
  have "A = (\<lambda>x. (f x, g x))-`B \<inter> space M" unfolding A_def B_def by auto
  moreover have "(\<lambda>x. (f x, g x)) \<in> borel_measurable M" by simp
  moreover have "B \<in> sets borel" unfolding B_def by (simp add: closed_diagonal)
  ultimately have "A \<in> sets M" by simp
  then show ?thesis unfolding A_def by simp
qed

lemma measurable_inequality_set [measurable]:
  fixes f g::"_ \<Rightarrow> 'a::{second_countable_topology, linorder_topology}"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x \<le> g x} \<in> sets M"
        "{x \<in> space M. f x < g x} \<in> sets M"
        "{x \<in> space M. f x \<ge> g x} \<in> sets M"
        "{x \<in> space M. f x > g x} \<in> sets M"
proof -
  define F where "F = (\<lambda>x. (f x, g x))"
  have * [measurable]: "F \<in> borel_measurable M" unfolding F_def by simp

  have "{x \<in> space M. f x \<le> g x} = F-`{(x, y) | x y. x \<le> y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x \<le> (y::'a)} \<in> sets borel" using closed_subdiagonal borel_closed by blast
  ultimately show "{x \<in> space M. f x \<le> g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x < g x} = F-`{(x, y) | x y. x < y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x < (y::'a)} \<in> sets borel" using open_subdiagonal borel_open by blast
  ultimately show "{x \<in> space M. f x < g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x \<ge> g x} = F-`{(x, y) | x y. x \<ge> y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x \<ge> (y::'a)} \<in> sets borel" using closed_superdiagonal borel_closed by blast
  ultimately show "{x \<in> space M. f x \<ge> g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x > g x} = F-`{(x, y) | x y. x > y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x > (y::'a)} \<in> sets borel" using open_superdiagonal borel_open by blast
  ultimately show "{x \<in> space M. f x > g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)
qed

proposition measurable_limit [measurable]:
  fixes f::"nat \<Rightarrow> 'a \<Rightarrow> 'b::first_countable_topology"
  assumes [measurable]: "\<And>n::nat. f n \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. (\<lambda>n. f n x) \<longlonglongrightarrow> c)"
proof -
  obtain A :: "nat \<Rightarrow> 'b set" where A:
    "\<And>i. open (A i)"
    "\<And>i. c \<in> A i"
    "\<And>S. open S \<Longrightarrow> c \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
  by (rule countable_basis_at_decseq) blast

  have [measurable]: "\<And>N i. (f N)-`(A i) \<inter> space M \<in> sets M" using A(1) by auto
  then have mes: "(\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i) \<inter> space M) \<in> sets M" by blast

  have "(u \<longlonglongrightarrow> c) \<longleftrightarrow> (\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)" for u::"nat \<Rightarrow> 'b"
  proof
    assume "u \<longlonglongrightarrow> c"
    then have "eventually (\<lambda>n. u n \<in> A i) sequentially" for i using A(1)[of i] A(2)[of i]
      by (simp add: topological_tendstoD)
    then show "(\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)" by auto
  next
    assume H: "(\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)"
    show "(u \<longlonglongrightarrow> c)"
    proof (rule topological_tendstoI)
      fix S assume "open S" "c \<in> S"
      with A(3)[OF this] obtain i where "A i \<subseteq> S"
        using eventually_False_sequentially eventually_mono by blast
      moreover have "eventually (\<lambda>n. u n \<in> A i) sequentially" using H by simp
      ultimately show "\<forall>\<^sub>F n in sequentially. u n \<in> S"
        by (simp add: eventually_mono subset_eq)
    qed
  qed
  then have "{x. (\<lambda>n. f n x) \<longlonglongrightarrow> c} = (\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i))"
    by (auto simp add: atLeast_def eventually_at_top_linorder)
  then have "{x \<in> space M. (\<lambda>n. f n x) \<longlonglongrightarrow> c} = (\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i) \<inter> space M)"
    by auto
  then have "{x \<in> space M. (\<lambda>n. f n x) \<longlonglongrightarrow> c} \<in> sets M" using mes by simp
  then show ?thesis by auto
qed

lemma measurable_limit2 [measurable]:
  fixes u::"nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>n. u n \<in> borel_measurable M" "v \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. (\<lambda>n. u n x) \<longlonglongrightarrow> v x)"
proof -
  define w where "w = (\<lambda>n x. u n x - v x)"
  have [measurable]: "w n \<in> borel_measurable M" for n unfolding w_def by auto
  have "((\<lambda>n. u n x) \<longlonglongrightarrow> v x) \<longleftrightarrow> ((\<lambda>n. w n x) \<longlonglongrightarrow> 0)" for x
    unfolding w_def using Lim_null by auto
  then show ?thesis using measurable_limit by auto
qed

lemma measurable_P_restriction [measurable (raw)]:
  assumes [measurable]: "Measurable.pred M P" "A \<in> sets M"
  shows "{x \<in> A. P x} \<in> sets M"
proof -
  have "A \<subseteq> space M" using sets.sets_into_space[OF assms(2)].
  then have "{x \<in> A. P x} = A \<inter> {x \<in> space M. P x}" by blast
  then show ?thesis by auto
qed

lemma measurable_sum_nat [measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> nat"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> measurable M (count_space UNIV)"
proof cases
  assume "finite S"
  then show ?thesis using assms by induct auto
qed simp


lemma measurable_abs_powr [measurable]:
  fixes p::real
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> borel_measurable M"
  by simp

text \<open>The next one is a variation around \<open>measurable_restrict_space\<close>.\<close>

lemma measurable_restrict_space3:
  assumes "f \<in> measurable M N" and
          "f \<in> A \<rightarrow> B"
  shows "f \<in> measurable (restrict_space M A) (restrict_space N B)"
proof -
  have "f \<in> measurable (restrict_space M A) N" using assms(1) measurable_restrict_space1 by auto
  then show ?thesis by (metis Int_iff funcsetI funcset_mem
      measurable_restrict_space2[of f, of "restrict_space M A", of B, of N] assms(2) space_restrict_space)
qed

lemma measurable_restrict_mono:
  assumes f: "f \<in> restrict_space M A \<rightarrow>\<^sub>M N" and "B \<subseteq> A"
  shows "f \<in> restrict_space M B \<rightarrow>\<^sub>M N"
by (rule measurable_compose[OF measurable_restrict_space3 f])
   (insert \<open>B \<subseteq> A\<close>, auto)

text \<open>The next one is a variation around \<open>measurable_piecewise_restrict\<close>.\<close>

lemma measurable_piecewise_restrict2:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
      and "space M = (\<Union>(n::nat). A n)"
          "\<And>n. \<exists>h \<in> measurable M N. (\<forall>x \<in> A n. f x = h x)"
  shows "f \<in> measurable M N"
proof (rule measurableI)
  fix B assume [measurable]: "B \<in> sets N"
  {
    fix n::nat
    obtain h where [measurable]: "h \<in> measurable M N" and "\<forall>x \<in> A n. f x = h x" using assms(3) by blast
    then have *: "f-`B \<inter> A n = h-`B \<inter> A n" by auto
    have "h-`B \<inter> A n = h-`B \<inter> space M \<inter> A n" using assms(2) sets.sets_into_space by auto
    then have "h-`B \<inter> A n \<in> sets M" by simp
    then have "f-`B \<inter> A n \<in> sets M" using * by simp
  }
  then have "(\<Union>n. f-`B \<inter> A n) \<in> sets M" by measurable
  moreover have "f-`B \<inter> space M = (\<Union>n. f-`B \<inter> A n)" using assms(2) by blast
  ultimately show "f-`B \<inter> space M \<in> sets M" by simp
next
  fix x assume "x \<in> space M"
  then obtain n where "x \<in> A n" using assms(2) by blast
  obtain h where [measurable]: "h \<in> measurable M N" and "\<forall>x \<in> A n. f x = h x" using assms(3) by blast
  then have "f x = h x" using \<open>x \<in> A n\<close> by blast
  moreover have "h x \<in> space N" by (metis measurable_space \<open>x \<in> space M\<close> \<open>h \<in> measurable M N\<close>)
  ultimately show "f x \<in> space N" by simp
qed

end
