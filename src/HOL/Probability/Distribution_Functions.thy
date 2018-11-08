(*  Title:    HOL/Probability/Distribution_Functions.thy
    Authors:  Jeremy Avigad (CMU) and Luke Serafin (CMU)
*)

section \<open>Distribution Functions\<close>

text \<open>
Shows that the cumulative distribution function (cdf) of a distribution (a measure on the reals) is
nondecreasing and right continuous, which tends to 0 and 1 in either direction.

Conversely, every such function is the cdf of a unique distribution. This direction defines the
measure in the obvious way on half-open intervals, and then applies the Caratheodory extension
theorem.
\<close>

(* TODO: the locales "finite_borel_measure" and "real_distribution" are defined here, but maybe they
 should be somewhere else. *)

theory Distribution_Functions
  imports Probability_Measure
begin

lemma UN_Ioc_eq_UNIV: "(\<Union>n. { -real n <.. real n}) = UNIV"
  by auto
     (metis le_less_trans minus_minus neg_less_iff_less not_le real_arch_simple
            of_nat_0_le_iff reals_Archimedean2)

subsection \<open>Properties of cdf's\<close>

definition
  cdf :: "real measure \<Rightarrow> real \<Rightarrow> real"
where
  "cdf M \<equiv> \<lambda>x. measure M {..x}"

lemma cdf_def2: "cdf M x = measure M {..x}"
  by (simp add: cdf_def)

locale finite_borel_measure = finite_measure M for M :: "real measure" +
  assumes M_is_borel: "sets M = sets borel"
begin

lemma sets_M[intro]: "a \<in> sets borel \<Longrightarrow> a \<in> sets M"
  using M_is_borel by auto

lemma cdf_diff_eq:
  assumes "x < y"
  shows "cdf M y - cdf M x = measure M {x<..y}"
proof -
  from assms have *: "{..x} \<union> {x<..y} = {..y}" by auto
  have "measure M {..y} = measure M {..x} + measure M {x<..y}"
    by (subst finite_measure_Union [symmetric], auto simp add: *)
  thus ?thesis
    unfolding cdf_def by auto
qed

lemma cdf_nondecreasing: "x \<le> y \<Longrightarrow> cdf M x \<le> cdf M y"
  unfolding cdf_def by (auto intro!: finite_measure_mono)

lemma borel_UNIV: "space M = UNIV"
 by (metis in_mono sets.sets_into_space space_in_borel top_le M_is_borel)

lemma cdf_nonneg: "cdf M x \<ge> 0"
  unfolding cdf_def by (rule measure_nonneg)

lemma cdf_bounded: "cdf M x \<le> measure M (space M)"
  unfolding cdf_def by (intro bounded_measure)

lemma cdf_lim_infty:
  "((\<lambda>i. cdf M (real i)) \<longlonglongrightarrow> measure M (space M))"
proof -
  have "(\<lambda>i. cdf M (real i)) \<longlonglongrightarrow> measure M (\<Union> i::nat. {..real i})"
    unfolding cdf_def by (rule finite_Lim_measure_incseq) (auto simp: incseq_def)
  also have "(\<Union> i::nat. {..real i}) = space M"
    by (auto simp: borel_UNIV intro: real_arch_simple)
  finally show ?thesis .
qed

lemma cdf_lim_at_top: "(cdf M \<longlongrightarrow> measure M (space M)) at_top"
  by (rule tendsto_at_topI_sequentially_real)
     (simp_all add: mono_def cdf_nondecreasing cdf_lim_infty)

lemma cdf_lim_neg_infty: "((\<lambda>i. cdf M (- real i)) \<longlonglongrightarrow> 0)"
proof -
  have "(\<lambda>i. cdf M (- real i)) \<longlonglongrightarrow> measure M (\<Inter> i::nat. {.. - real i })"
    unfolding cdf_def by (rule finite_Lim_measure_decseq) (auto simp: decseq_def)
  also have "(\<Inter> i::nat. {..- real i}) = {}"
    by auto (metis leD le_minus_iff reals_Archimedean2)
  finally show ?thesis
    by simp
qed

lemma cdf_lim_at_bot: "(cdf M \<longlongrightarrow> 0) at_bot"
proof -
  have *: "((\<lambda>x :: real. - cdf M (- x)) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_at_topI_sequentially_real monoI)
       (auto simp: cdf_nondecreasing cdf_lim_neg_infty tendsto_minus_cancel_left[symmetric])
  from filterlim_compose [OF *, OF filterlim_uminus_at_top_at_bot]
  show ?thesis
    unfolding tendsto_minus_cancel_left[symmetric] by simp
qed

lemma cdf_is_right_cont: "continuous (at_right a) (cdf M)"
  unfolding continuous_within
proof (rule tendsto_at_right_sequentially[where b="a + 1"])
  fix f :: "nat \<Rightarrow> real" and x assume f: "decseq f" "f \<longlonglongrightarrow> a"
  then have "(\<lambda>n. cdf M (f n)) \<longlonglongrightarrow> measure M (\<Inter>i. {.. f i})"
    using \<open>decseq f\<close> unfolding cdf_def
    by (intro finite_Lim_measure_decseq) (auto simp: decseq_def)
  also have "(\<Inter>i. {.. f i}) = {.. a}"
    using decseq_ge[OF f] by (auto intro: order_trans LIMSEQ_le_const[OF f(2)])
  finally show "(\<lambda>n. cdf M (f n)) \<longlonglongrightarrow> cdf M a"
    by (simp add: cdf_def)
qed simp

lemma cdf_at_left: "(cdf M \<longlongrightarrow> measure M {..<a}) (at_left a)"
proof (rule tendsto_at_left_sequentially[of "a - 1"])
  fix f :: "nat \<Rightarrow> real" and x assume f: "incseq f" "f \<longlonglongrightarrow> a" "\<And>x. f x < a" "\<And>x. a - 1 < f x"
  then have "(\<lambda>n. cdf M (f n)) \<longlonglongrightarrow> measure M (\<Union>i. {.. f i})"
    using \<open>incseq f\<close> unfolding cdf_def
    by (intro finite_Lim_measure_incseq) (auto simp: incseq_def)
  also have "(\<Union>i. {.. f i}) = {..<a}"
    by (auto dest!: order_tendstoD(1)[OF f(2)] eventually_happens'[OF sequentially_bot]
             intro: less_imp_le le_less_trans f(3))
  finally show "(\<lambda>n. cdf M (f n)) \<longlonglongrightarrow> measure M {..<a}"
    by (simp add: cdf_def)
qed auto

lemma isCont_cdf: "isCont (cdf M) x \<longleftrightarrow> measure M {x} = 0"
proof -
  have "isCont (cdf M) x \<longleftrightarrow> cdf M x = measure M {..<x}"
    by (auto simp: continuous_at_split cdf_is_right_cont continuous_within[where s="{..< _}"]
                   cdf_at_left tendsto_unique[OF _ cdf_at_left])
  also have "cdf M x = measure M {..<x} \<longleftrightarrow> measure M {x} = 0"
    unfolding cdf_def ivl_disj_un(2)[symmetric]
    by (subst finite_measure_Union) auto
  finally show ?thesis .
qed

lemma countable_atoms: "countable {x. measure M {x} > 0}"
  using countable_support unfolding zero_less_measure_iff .

end

locale real_distribution = prob_space M for M :: "real measure" +
  assumes events_eq_borel [simp, measurable_cong]: "sets M = sets borel"
begin

lemma finite_borel_measure_M: "finite_borel_measure M"
  by standard auto

sublocale finite_borel_measure M
  by (rule finite_borel_measure_M)

lemma space_eq_univ [simp]: "space M = UNIV"
  using events_eq_borel[THEN sets_eq_imp_space_eq] by simp

lemma cdf_bounded_prob: "\<And>x. cdf M x \<le> 1"
  by (subst prob_space [symmetric], rule cdf_bounded)

lemma cdf_lim_infty_prob: "(\<lambda>i. cdf M (real i)) \<longlonglongrightarrow> 1"
  by (subst prob_space [symmetric], rule cdf_lim_infty)

lemma cdf_lim_at_top_prob: "(cdf M \<longlongrightarrow> 1) at_top"
  by (subst prob_space [symmetric], rule cdf_lim_at_top)

lemma measurable_finite_borel [simp]:
  "f \<in> borel_measurable borel \<Longrightarrow> f \<in> borel_measurable M"
  by (rule borel_measurable_subalgebra[where N=borel]) auto

end

lemma (in prob_space) real_distribution_distr [intro, simp]:
  "random_variable borel X \<Longrightarrow> real_distribution (distr M borel X)"
  unfolding real_distribution_def real_distribution_axioms_def by (auto intro!: prob_space_distr)

subsection \<open>Uniqueness\<close>

lemma (in finite_borel_measure) emeasure_Ioc:
  assumes "a \<le> b" shows "emeasure M {a <.. b} = cdf M b - cdf M a"
proof -
  have "{a <.. b} = {..b} - {..a}"
    by auto
  moreover have "{..x} \<in> sets M" for x
    using atMost_borel[of x] M_is_borel by auto
  moreover note \<open>a \<le> b\<close>
  ultimately show ?thesis
    by (simp add: emeasure_eq_measure finite_measure_Diff cdf_def)
qed

lemma cdf_unique':
  fixes M1 M2
  assumes "finite_borel_measure M1" and "finite_borel_measure M2"
  assumes "cdf M1 = cdf M2"
  shows "M1 = M2"
proof (rule measure_eqI_generator_eq[where \<Omega>=UNIV])
  fix X assume "X \<in> range (\<lambda>(a, b). {a<..b::real})"
  then obtain a b where Xeq: "X = {a<..b}" by auto
  then show "emeasure M1 X = emeasure M2 X"
    by (cases "a \<le> b")
       (simp_all add: assms(1,2)[THEN finite_borel_measure.emeasure_Ioc] assms(3))
next
  show "(\<Union>i. {- real (i::nat)<..real i}) = UNIV"
    by (rule UN_Ioc_eq_UNIV)
qed (auto simp: finite_borel_measure.emeasure_Ioc[OF assms(1)]
  assms(1,2)[THEN finite_borel_measure.M_is_borel] borel_sigma_sets_Ioc
  Int_stable_def)

lemma cdf_unique:
  "real_distribution M1 \<Longrightarrow> real_distribution M2 \<Longrightarrow> cdf M1 = cdf M2 \<Longrightarrow> M1 = M2"
  using cdf_unique'[of M1 M2] by (simp add: real_distribution.finite_borel_measure_M)

lemma
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y"
    and right_cont_F : "\<And>a. continuous (at_right a) F"
    and lim_F_at_bot : "(F \<longlongrightarrow> 0) at_bot"
    and lim_F_at_top : "(F \<longlongrightarrow> m) at_top"
    and m: "0 \<le> m"
  shows interval_measure_UNIV: "emeasure (interval_measure F) UNIV = m"
    and finite_borel_measure_interval_measure: "finite_borel_measure (interval_measure F)"
proof -
  let ?F = "interval_measure F"
  { have "ennreal (m - 0) = (SUP i. ennreal (F (real i) - F (- real i)))"
      by (intro LIMSEQ_unique[OF _ LIMSEQ_SUP] tendsto_ennrealI tendsto_intros
                lim_F_at_bot[THEN filterlim_compose] lim_F_at_top[THEN filterlim_compose]
                lim_F_at_bot[THEN filterlim_compose] filterlim_real_sequentially
                filterlim_uminus_at_top[THEN iffD1])
         (auto simp: incseq_def nondecF intro!: diff_mono)
    also have "\<dots> = (SUP i. emeasure ?F {- real i<..real i})"
      by (subst emeasure_interval_measure_Ioc) (simp_all add: nondecF right_cont_F)
    also have "\<dots> = emeasure ?F (\<Union>i::nat. {- real i<..real i})"
      by (rule SUP_emeasure_incseq) (auto simp: incseq_def)
    also have "(\<Union>i. {- real (i::nat)<..real i}) = space ?F"
      by (simp add: UN_Ioc_eq_UNIV)
    finally have "emeasure ?F (space ?F) = m"
      by simp }
  note * = this
  then show "emeasure (interval_measure F) UNIV = m"
    by simp

  interpret finite_measure ?F
  proof
    show "emeasure ?F (space ?F) \<noteq> \<infinity>"
      using * by simp
  qed
  show "finite_borel_measure (interval_measure F)"
    proof qed simp_all
qed

lemma real_distribution_interval_measure:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and
    lim_F_at_bot : "(F \<longlongrightarrow> 0) at_bot" and
    lim_F_at_top : "(F \<longlongrightarrow> 1) at_top"
  shows "real_distribution (interval_measure F)"
proof -
  let ?F = "interval_measure F"
  interpret prob_space ?F
    proof qed (use interval_measure_UNIV[OF assms] in simp)
  show ?thesis
    proof qed simp_all
qed

lemma
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and
    lim_F_at_bot : "(F \<longlongrightarrow> 0) at_bot"
  shows emeasure_interval_measure_Iic: "emeasure (interval_measure F) {.. x} = F x"
    and measure_interval_measure_Iic: "measure (interval_measure F) {.. x} = F x"
  unfolding cdf_def
proof -
  have F_nonneg[simp]: "0 \<le> F y" for y
    using lim_F_at_bot by (rule tendsto_upperbound) (auto simp: eventually_at_bot_linorder nondecF intro!: exI[of _ y])

  have "emeasure (interval_measure F) (\<Union>i::nat. {-real i <.. x}) = F x - ennreal 0"
  proof (intro LIMSEQ_unique[OF Lim_emeasure_incseq])
    have "(\<lambda>i. F x - F (- real i)) \<longlonglongrightarrow> F x - 0"
      by (intro tendsto_intros lim_F_at_bot[THEN filterlim_compose] filterlim_real_sequentially
                filterlim_uminus_at_top[THEN iffD1])
    from tendsto_ennrealI[OF this]
    show "(\<lambda>i. emeasure (interval_measure F) {- real i<..x}) \<longlonglongrightarrow> F x - ennreal 0"
      apply (rule filterlim_cong[THEN iffD1, rotated 3])
        apply simp
       apply simp
      apply (rule eventually_sequentiallyI[where c="nat (ceiling (- x))"])
      apply (simp add: emeasure_interval_measure_Ioc right_cont_F nondecF)
      done
  qed (auto simp: incseq_def)
  also have "(\<Union>i::nat. {-real i <.. x}) = {..x}"
    by auto (metis minus_minus neg_less_iff_less reals_Archimedean2)
  finally show "emeasure (interval_measure F) {..x} = F x"
    by simp
  then show "measure (interval_measure F) {..x} = F x"
    by (simp add: measure_def)
qed

lemma cdf_interval_measure:
  "(\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y) \<Longrightarrow> (\<And>a. continuous (at_right a) F) \<Longrightarrow> (F \<longlongrightarrow> 0) at_bot \<Longrightarrow> cdf (interval_measure F) = F"
  by (simp add: cdf_def fun_eq_iff measure_interval_measure_Iic)

end
