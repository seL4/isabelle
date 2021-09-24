(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Stopping times\<close>

theory Stopping_Time
  imports "HOL-Analysis.Analysis"
begin

subsection \<open>Stopping Time\<close>

text \<open>This is also called strong stopping time. Then stopping time is T with alternative is
  \<open>T x < t\<close> measurable.\<close>

definition stopping_time :: "('t::linorder \<Rightarrow> 'a measure) \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> bool"
where
  "stopping_time F T = (\<forall>t. Measurable.pred (F t) (\<lambda>x. T x \<le> t))"

lemma stopping_time_cong: "(\<And>t x. x \<in> space (F t) \<Longrightarrow> T x = S x) \<Longrightarrow> stopping_time F T = stopping_time F S"
  unfolding stopping_time_def by (intro arg_cong[where f=All] ext measurable_cong) simp

lemma stopping_timeD: "stopping_time F T \<Longrightarrow> Measurable.pred (F t) (\<lambda>x. T x \<le> t)"
  by (auto simp: stopping_time_def)

lemma stopping_timeD2: "stopping_time F T \<Longrightarrow> Measurable.pred (F t) (\<lambda>x. t < T x)"
  unfolding not_le[symmetric] by (auto intro: stopping_timeD Measurable.pred_intros_logic)

lemma stopping_timeI[intro?]: "(\<And>t. Measurable.pred (F t) (\<lambda>x. T x \<le> t)) \<Longrightarrow> stopping_time F T"
  by (auto simp: stopping_time_def)

lemma measurable_stopping_time:
  fixes T :: "'a \<Rightarrow> 't::{linorder_topology, second_countable_topology}"
  assumes T: "stopping_time F T"
    and M: "\<And>t. sets (F t) \<subseteq> sets M" "\<And>t. space (F t) = space M"
  shows "T \<in> M \<rightarrow>\<^sub>M borel"
proof (rule borel_measurableI_le)
  show "{x \<in> space M. T x \<le> t} \<in> sets M" for t
    using stopping_timeD[OF T] M by (auto simp: Measurable.pred_def)
qed

lemma stopping_time_const: "stopping_time F (\<lambda>x. c)"
  by (auto simp: stopping_time_def)

lemma stopping_time_min:
  "stopping_time F T \<Longrightarrow> stopping_time F S \<Longrightarrow> stopping_time F (\<lambda>x. min (T x) (S x))"
  by (auto simp: stopping_time_def min_le_iff_disj intro!: pred_intros_logic)

lemma stopping_time_max:
  "stopping_time F T \<Longrightarrow> stopping_time F S \<Longrightarrow> stopping_time F (\<lambda>x. max (T x) (S x))"
  by (auto simp: stopping_time_def intro!: pred_intros_logic)

section \<open>Filtration\<close>

locale filtration =
  fixes \<Omega> :: "'a set" and F :: "'t::{linorder_topology, second_countable_topology} \<Rightarrow> 'a measure"
  assumes space_F: "\<And>i. space (F i) = \<Omega>"
  assumes sets_F_mono: "\<And>i j. i \<le> j \<Longrightarrow> sets (F i) \<le> sets (F j)"
begin

subsection \<open>$\sigma$-algebra of a Stopping Time\<close>

definition pre_sigma :: "('a \<Rightarrow> 't) \<Rightarrow> 'a measure"
where
  "pre_sigma T = sigma \<Omega> {A. \<forall>t. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)}"

lemma space_pre_sigma: "space (pre_sigma T) = \<Omega>"
  unfolding pre_sigma_def using sets.space_closed[of "F _"]
  by (intro space_measure_of) (auto simp: space_F)

lemma measure_pre_sigma[simp]: "emeasure (pre_sigma T) = (\<lambda>_. 0)"
  by (simp add: pre_sigma_def emeasure_sigma)

lemma sigma_algebra_pre_sigma:
  assumes T: "stopping_time F T"
  shows "sigma_algebra \<Omega> {A. \<forall>t. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)}"
  unfolding sigma_algebra_iff2
proof (intro sigma_algebra_iff2[THEN iffD2] conjI ballI allI impI CollectI)
  show "{A. \<forall>t. {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)} \<subseteq> Pow \<Omega>"
    using sets.space_closed[of "F _"] by (auto simp: space_F)
next
  fix A t assume "A \<in> {A. \<forall>t. {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)}"
  then have "{\<omega> \<in> space (F t). T \<omega> \<le> t} - {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)"
    using T stopping_timeD[measurable] by auto
  also have "{\<omega> \<in> space (F t). T \<omega> \<le> t} - {\<omega> \<in> A. T \<omega> \<le> t} = {\<omega> \<in> \<Omega> - A. T \<omega> \<le> t}"
    by (auto simp: space_F)
  finally show "{\<omega> \<in> \<Omega> - A. T \<omega> \<le> t} \<in> sets (F t)" .
next
  fix AA :: "nat \<Rightarrow> 'a set" and t assume "range AA \<subseteq> {A. \<forall>t. {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)}"
  then have "(\<Union>i. {\<omega> \<in> AA i. T \<omega> \<le> t}) \<in> sets (F t)" for t
    by auto
  also have "(\<Union>i. {\<omega> \<in> AA i. T \<omega> \<le> t}) = {\<omega> \<in> \<Union>(AA ` UNIV). T \<omega> \<le> t}"
    by auto
  finally show "{\<omega> \<in> \<Union>(AA ` UNIV). T \<omega> \<le> t} \<in> sets (F t)" .
qed auto

lemma sets_pre_sigma: "stopping_time F T \<Longrightarrow> sets (pre_sigma T) = {A. \<forall>t. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)}"
  unfolding pre_sigma_def by (rule sigma_algebra.sets_measure_of_eq[OF sigma_algebra_pre_sigma])

lemma sets_pre_sigmaI: "stopping_time F T \<Longrightarrow> (\<And>t. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)) \<Longrightarrow> A \<in> sets (pre_sigma T)"
  unfolding sets_pre_sigma by auto

lemma pred_pre_sigmaI:
  assumes T: "stopping_time F T"
  shows "(\<And>t. Measurable.pred (F t) (\<lambda>\<omega>. P \<omega> \<and> T \<omega> \<le> t)) \<Longrightarrow> Measurable.pred (pre_sigma T) P"
  unfolding pred_def space_F space_pre_sigma by (intro sets_pre_sigmaI[OF T]) simp

lemma sets_pre_sigmaD: "stopping_time F T \<Longrightarrow> A \<in> sets (pre_sigma T) \<Longrightarrow> {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)"
  unfolding sets_pre_sigma by auto

lemma stopping_time_le_const: "stopping_time F T \<Longrightarrow> s \<le> t \<Longrightarrow> Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> \<le> s)"
  using stopping_timeD[of F T] sets_F_mono[of _ t] by (auto simp: pred_def space_F)

lemma measurable_stopping_time_pre_sigma:
  assumes T: "stopping_time F T" shows "T \<in> pre_sigma T \<rightarrow>\<^sub>M borel"
proof (intro borel_measurableI_le sets_pre_sigmaI[OF T])
  fix t t'
  have "{\<omega>\<in>space (F (min t' t)). T \<omega> \<le> min t' t} \<in> sets (F (min t' t))"
    using T unfolding pred_def[symmetric] by (rule stopping_timeD)
  also have "\<dots> \<subseteq> sets (F t)"
    by (rule sets_F_mono) simp
  finally show "{\<omega> \<in> {x \<in> space (pre_sigma T). T x \<le> t'}. T \<omega> \<le> t} \<in> sets (F t)"
    by (simp add: space_pre_sigma space_F)
qed

lemma mono_pre_sigma:
  assumes T: "stopping_time F T" and S: "stopping_time F S"
    and le: "\<And>\<omega>. \<omega> \<in> \<Omega> \<Longrightarrow> T \<omega> \<le> S \<omega>"
  shows "sets (pre_sigma T) \<subseteq> sets (pre_sigma S)"
  unfolding sets_pre_sigma[OF S] sets_pre_sigma[OF T]
proof safe
  interpret sigma_algebra \<Omega> "{A. \<forall>t. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)}"
    using T by (rule sigma_algebra_pre_sigma)
  fix A t assume A: "\<forall>t. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)"
  then have "A \<subseteq> \<Omega>"
    using sets_into_space by auto
  from A have "{\<omega>\<in>A. T \<omega> \<le> t} \<inter> {\<omega>\<in>space (F t). S \<omega> \<le> t} \<in> sets (F t)"
    using stopping_timeD[OF S] by (auto simp: pred_def)
  also have "{\<omega>\<in>A. T \<omega> \<le> t} \<inter> {\<omega>\<in>space (F t). S \<omega> \<le> t} = {\<omega>\<in>A. S \<omega> \<le> t}"
    using \<open>A \<subseteq> \<Omega>\<close> sets_into_space[of A] le by (auto simp: space_F intro: order_trans)
  finally show "{\<omega>\<in>A. S \<omega> \<le> t} \<in> sets (F t)"
    by auto
qed

lemma stopping_time_less_const:
  assumes T: "stopping_time F T" shows "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> < t)"
proof -
  obtain D :: "'t set"
    where D: "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d\<in>D. d \<in> X"
  using countable_dense_setE by auto
  show ?thesis
  proof cases
    assume *: "\<forall>t'<t. \<exists>t''. t' < t'' \<and> t'' < t"
    { fix t' assume "t' < t"
      with * have "{t' <..< t} \<noteq> {}"
        by fastforce
      with D(2)[OF _ this]
      have "\<exists>d\<in>D. t'< d \<and> d < t"
        by auto }
    note ** = this

    show ?thesis
    proof (rule measurable_cong[THEN iffD2])
      show "T \<omega> < t \<longleftrightarrow> (\<exists>r\<in>{r\<in>D. r < t}. T \<omega> \<le> r)" for \<omega>
        by (auto dest: ** intro: less_imp_le)
      show "Measurable.pred (F t) (\<lambda>w. \<exists>r\<in>{r \<in> D. r < t}. T w \<le> r)"
        by (intro measurable_pred_countable stopping_time_le_const[OF T] countable_Collect D) auto
    qed
  next
    assume "\<not> (\<forall>t'<t. \<exists>t''. t' < t'' \<and> t'' < t)"
    then obtain t' where t': "t' < t" "\<And>t''. t'' < t \<Longrightarrow> t'' \<le> t'"
      by (auto simp: not_less[symmetric])
    show ?thesis
    proof (rule measurable_cong[THEN iffD2])
      show "T \<omega> < t \<longleftrightarrow> T \<omega> \<le> t'" for \<omega>
        using t' by auto
      show "Measurable.pred (F t) (\<lambda>w. T w \<le> t')"
        using \<open>t'<t\<close> by (intro stopping_time_le_const[OF T]) auto
    qed
  qed
qed

lemma stopping_time_eq_const: "stopping_time F T \<Longrightarrow> Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> = t)"
  unfolding eq_iff using stopping_time_less_const[of T t]
  by (intro pred_intros_logic stopping_time_le_const) (auto simp: not_less[symmetric] )

lemma stopping_time_less:
  assumes T: "stopping_time F T" and S: "stopping_time F S"
  shows "Measurable.pred (pre_sigma T) (\<lambda>\<omega>. T \<omega> < S \<omega>)"
proof (rule pred_pre_sigmaI[OF T])
  fix t
  obtain D :: "'t set"
    where [simp]: "countable D" and semidense_D: "\<And>x y. x < y \<Longrightarrow> (\<exists>b\<in>D. x \<le> b \<and> b < y)"
    using countable_separating_set_linorder2 by auto
  show "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> < S \<omega> \<and> T \<omega> \<le> t)"
  proof (rule measurable_cong[THEN iffD2])
    let ?f = "\<lambda>\<omega>. if T \<omega> = t then \<not> S \<omega> \<le> t else \<exists>s\<in>{s\<in>D. s \<le> t}. T \<omega> \<le> s \<and> \<not> (S \<omega> \<le> s)"
    { fix \<omega> assume "T \<omega> \<le> t" "T \<omega> \<noteq> t" "T \<omega> < S \<omega>"
      then have "T \<omega> < min t (S \<omega>)"
        by auto
      then obtain r where "r \<in> D" "T \<omega> \<le> r" "r < min t (S \<omega>)"
        by (metis semidense_D)
      then have "\<exists>s\<in>{s\<in>D. s \<le> t}. T \<omega> \<le> s \<and> s < S \<omega>"
        by auto }
    then show "(T \<omega> < S \<omega> \<and> T \<omega> \<le> t) = ?f \<omega>" for \<omega>
      by (auto simp: not_le)
    show "Measurable.pred (F t) ?f"
      by (intro pred_intros_logic measurable_If measurable_pred_countable countable_Collect
                stopping_time_le_const predE stopping_time_eq_const T S)
         auto
  qed
qed

end

lemma stopping_time_SUP_enat:
  fixes T :: "nat \<Rightarrow> ('a \<Rightarrow> enat)"
  shows "(\<And>i. stopping_time F (T i)) \<Longrightarrow> stopping_time F (SUP i. T i)"
  unfolding stopping_time_def SUP_apply SUP_le_iff by (auto intro!: pred_intros_countable)

lemma less_eSuc_iff: "a < eSuc b \<longleftrightarrow> (a \<le> b \<and> a \<noteq> \<infinity>)"
  by (cases a) auto

lemma stopping_time_Inf_enat:
  fixes F :: "enat \<Rightarrow> 'a measure"
  assumes F: "filtration \<Omega> F"
  assumes P: "\<And>i. Measurable.pred (F i) (P i)"
  shows "stopping_time F (\<lambda>\<omega>. Inf {i. P i \<omega>})"
proof (rule stopping_timeI, cases)
  fix t :: enat assume "t = \<infinity>" then show "Measurable.pred (F t) (\<lambda>\<omega>. Inf {i. P i \<omega>} \<le> t)"
    by auto
next
  fix t :: enat assume "t \<noteq> \<infinity>"
  moreover
  { fix i \<omega> assume "Inf {i. P i \<omega>} \<le> t"
    with \<open>t \<noteq> \<infinity>\<close> have "(\<exists>i\<le>t. P i \<omega>)"
      unfolding Inf_le_iff by (cases t) (auto elim!: allE[of _ "eSuc t"] simp: less_eSuc_iff) }
  ultimately have *: "\<And>\<omega>. Inf {i. P i \<omega>} \<le> t \<longleftrightarrow> (\<exists>i\<in>{..t}. P i \<omega>)"
    by (auto intro!: Inf_lower2)
  show "Measurable.pred (F t) (\<lambda>\<omega>. Inf {i. P i \<omega>} \<le> t)"
    unfolding * using filtration.sets_F_mono[OF F, of _ t] P
    by (intro pred_intros_countable_bounded) (auto simp: pred_def filtration.space_F[OF F])
qed

lemma stopping_time_Inf_nat:
  fixes F :: "nat \<Rightarrow> 'a measure"
  assumes F: "filtration \<Omega> F"
  assumes P: "\<And>i. Measurable.pred (F i) (P i)" and wf: "\<And>i \<omega>. \<omega> \<in> \<Omega> \<Longrightarrow> \<exists>n. P n \<omega>"
  shows "stopping_time F (\<lambda>\<omega>. Inf {i. P i \<omega>})"
  unfolding stopping_time_def
proof (intro allI, subst measurable_cong)
  fix t \<omega> assume "\<omega> \<in> space (F t)"
  then have "\<omega> \<in> \<Omega>"
    using filtration.space_F[OF F] by auto
  from wf[OF this] have "((LEAST n. P n \<omega>) \<le> t) = (\<exists>i\<le>t. P i \<omega>)"
    by (rule LeastI2_wellorder_ex) auto
  then show "(Inf {i. P i \<omega>} \<le> t) = (\<exists>i\<in>{..t}. P i \<omega>)"
    by (simp add: Inf_nat_def Bex_def)
next
  fix t from P show "Measurable.pred (F t) (\<lambda>w. \<exists>i\<in>{..t}. P i w)"
    using filtration.sets_F_mono[OF F, of _ t]
    by (intro pred_intros_countable_bounded) (auto simp: pred_def filtration.space_F[OF F])
qed

end
