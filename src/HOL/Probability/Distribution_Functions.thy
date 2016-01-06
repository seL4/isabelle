(*
  Title    : Distribution_Functions.thy
  Authors  : Jeremy Avigad and Luke Serafin
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
  imports Probability_Measure "~~/src/HOL/Library/ContNotDenum"
begin

lemma UN_Ioc_eq_UNIV: "(\<Union>n. { -real n <.. real n}) = UNIV"
  by auto
     (metis le_less_trans minus_minus neg_less_iff_less not_le real_arch_simple
            of_nat_0_le_iff reals_Archimedean2)

subsection {* Properties of cdf's *}

definition
  cdf :: "real measure \<Rightarrow> real \<Rightarrow> real"
where
  "cdf M \<equiv> \<lambda>x. measure M {..x}"

lemma cdf_def2: "cdf M x = measure M {..x}"
  by (simp add: cdf_def)

locale finite_borel_measure = finite_measure M for M :: "real measure" +
  assumes M_super_borel: "sets borel \<subseteq> sets M"
begin

lemma sets_M[intro]: "a \<in> sets borel \<Longrightarrow> a \<in> sets M"
  using M_super_borel by auto

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
 by (metis in_mono sets.sets_into_space space_in_borel top_le M_super_borel)
 
lemma cdf_nonneg: "cdf M x \<ge> 0"
  unfolding cdf_def by (rule measure_nonneg)

lemma cdf_bounded: "cdf M x \<le> measure M (space M)"
  unfolding cdf_def using assms by (intro bounded_measure)

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
    using `decseq f` unfolding cdf_def 
    by (intro finite_Lim_measure_decseq) (auto simp: decseq_def)
  also have "(\<Inter>i. {.. f i}) = {.. a}"
    using decseq_le[OF f] by (auto intro: order_trans LIMSEQ_le_const[OF f(2)])
  finally show "(\<lambda>n. cdf M (f n)) \<longlonglongrightarrow> cdf M a"
    by (simp add: cdf_def)
qed simp

lemma cdf_at_left: "(cdf M \<longlongrightarrow> measure M {..<a}) (at_left a)"
proof (rule tendsto_at_left_sequentially[of "a - 1"])
  fix f :: "nat \<Rightarrow> real" and x assume f: "incseq f" "f \<longlonglongrightarrow> a" "\<And>x. f x < a" "\<And>x. a - 1 < f x"
  then have "(\<lambda>n. cdf M (f n)) \<longlonglongrightarrow> measure M (\<Union>i. {.. f i})"
    using `incseq f` unfolding cdf_def 
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
  assumes events_eq_borel [simp, measurable_cong]: "sets M = sets borel" and space_eq_univ [simp]: "space M = UNIV"
begin

sublocale finite_borel_measure M
  by standard auto

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

subsection {* uniqueness *}

lemma (in real_distribution) emeasure_Ioc:
  assumes "a \<le> b" shows "emeasure M {a <.. b} = cdf M b - cdf M a"
proof -
  have "{a <.. b} = {..b} - {..a}"
    by auto
  with `a \<le> b` show ?thesis
    by (simp add: emeasure_eq_measure finite_measure_Diff cdf_def)
qed

lemma cdf_unique:
  fixes M1 M2
  assumes "real_distribution M1" and "real_distribution M2"
  assumes "cdf M1 = cdf M2"
  shows "M1 = M2"
proof (rule measure_eqI_generator_eq[where \<Omega>=UNIV])
  fix X assume "X \<in> range (\<lambda>(a, b). {a<..b::real})"
  then obtain a b where Xeq: "X = {a<..b}" by auto
  then show "emeasure M1 X = emeasure M2 X"
    by (cases "a \<le> b")
       (simp_all add: assms(1,2)[THEN real_distribution.emeasure_Ioc] assms(3))
next
  show "(\<Union>i. {- real (i::nat)<..real i}) = UNIV"
    by (rule UN_Ioc_eq_UNIV)
qed (auto simp: real_distribution.emeasure_Ioc[OF assms(1)]
  assms(1,2)[THEN real_distribution.events_eq_borel] borel_sigma_sets_Ioc
  Int_stable_def)

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
  proof
    have "ereal (1 - 0) = (SUP i::nat. ereal (F (real i) - F (- real i)))"
      by (intro LIMSEQ_unique[OF _ LIMSEQ_SUP] lim_ereal[THEN iffD2] tendsto_intros
         lim_F_at_bot[THEN filterlim_compose] lim_F_at_top[THEN filterlim_compose]
         lim_F_at_bot[THEN filterlim_compose] filterlim_real_sequentially
         filterlim_uminus_at_top[THEN iffD1])
         (auto simp: incseq_def intro!: diff_mono nondecF)
    also have "\<dots> = (SUP i::nat. emeasure ?F {- real i<..real i})"
      by (subst emeasure_interval_measure_Ioc) (simp_all add: nondecF right_cont_F)
    also have "\<dots> = emeasure ?F (\<Union>i::nat. {- real i<..real i})"
      by (rule SUP_emeasure_incseq) (auto simp: incseq_def)
    also have "(\<Union>i. {- real (i::nat)<..real i}) = space ?F"
      by (simp add: UN_Ioc_eq_UNIV)
    finally show "emeasure ?F (space ?F) = 1"
      by (simp add: one_ereal_def)
  qed
  show ?thesis
    proof qed simp_all
qed

lemma cdf_interval_measure:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and 
    lim_F_at_bot : "(F \<longlongrightarrow> 0) at_bot" and
    lim_F_at_top : "(F \<longlongrightarrow> 1) at_top"
  shows "cdf (interval_measure F) = F"
  unfolding cdf_def
proof (intro ext)
  interpret real_distribution "interval_measure F"
    by (rule real_distribution_interval_measure) fact+
  fix x
  have "F x - 0 = measure (interval_measure F) (\<Union>i::nat. {-real i <.. x})"
  proof (intro LIMSEQ_unique[OF _ finite_Lim_measure_incseq])
    have "(\<lambda>i. F x - F (- real i)) \<longlonglongrightarrow> F x - 0"
      by (intro tendsto_intros lim_F_at_bot[THEN filterlim_compose] filterlim_real_sequentially
                filterlim_uminus_at_top[THEN iffD1])
    then show "(\<lambda>i. measure (interval_measure F) {- real i<..x}) \<longlonglongrightarrow> F x - 0"
      apply (rule filterlim_cong[OF refl refl, THEN iffD1, rotated])
      apply (rule eventually_sequentiallyI[where c="nat (ceiling (- x))"])
      apply (simp add: measure_interval_measure_Ioc right_cont_F nondecF)
      done
  qed (auto simp: incseq_def)
  also have "(\<Union>i::nat. {-real i <.. x}) = {..x}"
    by auto (metis minus_minus neg_less_iff_less reals_Archimedean2)
  finally show "measure (interval_measure F) {..x} = F x"
    by simp
qed

end
