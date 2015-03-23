(*  Title:      HOL/Probability/Giry_Monad.thy
    Author:     Johannes Hölzl, TU München
    Author:     Manuel Eberl, TU München

Defines the subprobability spaces, the subprobability functor and the Giry monad on subprobability
spaces.
*)

theory Giry_Monad
  imports Probability_Measure Lebesgue_Integral_Substitution "~~/src/HOL/Library/Monad_Syntax" 
begin

section {* Sub-probability spaces *}

locale subprob_space = finite_measure +
  assumes emeasure_space_le_1: "emeasure M (space M) \<le> 1"
  assumes subprob_not_empty: "space M \<noteq> {}"

lemma subprob_spaceI[Pure.intro!]:
  assumes *: "emeasure M (space M) \<le> 1"
  assumes "space M \<noteq> {}"
  shows "subprob_space M"
proof -
  interpret finite_measure M
  proof
    show "emeasure M (space M) \<noteq> \<infinity>" using * by auto
  qed
  show "subprob_space M" by default fact+
qed

lemma prob_space_imp_subprob_space:
  "prob_space M \<Longrightarrow> subprob_space M"
  by (rule subprob_spaceI) (simp_all add: prob_space.emeasure_space_1 prob_space.not_empty)

lemma subprob_space_imp_sigma_finite: "subprob_space M \<Longrightarrow> sigma_finite_measure M"
  unfolding subprob_space_def finite_measure_def by simp

sublocale prob_space \<subseteq> subprob_space
  by (rule subprob_spaceI) (simp_all add: emeasure_space_1 not_empty)

lemma (in subprob_space) subprob_space_distr:
  assumes f: "f \<in> measurable M M'" and "space M' \<noteq> {}" shows "subprob_space (distr M M' f)"
proof (rule subprob_spaceI)
  have "f -` space M' \<inter> space M = space M" using f by (auto dest: measurable_space)
  with f show "emeasure (distr M M' f) (space (distr M M' f)) \<le> 1"
    by (auto simp: emeasure_distr emeasure_space_le_1)
  show "space (distr M M' f) \<noteq> {}" by (simp add: assms)
qed

lemma (in subprob_space) subprob_emeasure_le_1: "emeasure M X \<le> 1"
  by (rule order.trans[OF emeasure_space emeasure_space_le_1])

lemma (in subprob_space) subprob_measure_le_1: "measure M X \<le> 1"
  using subprob_emeasure_le_1[of X] by (simp add: emeasure_eq_measure)

lemma (in subprob_space) nn_integral_le_const:
  assumes "0 \<le> c" "AE x in M. f x \<le> c"
  shows "(\<integral>\<^sup>+x. f x \<partial>M) \<le> c"
proof -
  have "(\<integral>\<^sup>+ x. f x \<partial>M) \<le> (\<integral>\<^sup>+ x. c \<partial>M)"
    by(rule nn_integral_mono_AE) fact
  also have "\<dots> \<le> c * emeasure M (space M)"
    using \<open>0 \<le> c\<close> by(simp add: nn_integral_const_If)
  also have "\<dots> \<le> c * 1" using emeasure_space_le_1 \<open>0 \<le> c\<close> by(rule ereal_mult_left_mono)
  finally show ?thesis by simp
qed

lemma emeasure_density_distr_interval:
  fixes h :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real" and g' :: "real \<Rightarrow> real"
  assumes [simp]: "a \<le> b"
  assumes Mf[measurable]: "f \<in> borel_measurable borel"
  assumes Mg[measurable]: "g \<in> borel_measurable borel"
  assumes Mg'[measurable]: "g' \<in> borel_measurable borel"
  assumes Mh[measurable]: "h \<in> borel_measurable borel"
  assumes prob: "subprob_space (density lborel f)"
  assumes nonnegf: "\<And>x. f x \<ge> 0"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'"
  assumes mono: "strict_mono_on g {a..b}" and inv: "\<And>x. h x \<in> {a..b} \<Longrightarrow> g (h x) = x"
  assumes range: "{a..b} \<subseteq> range h"
  shows "emeasure (distr (density lborel f) lborel h) {a..b} = 
             emeasure (density lborel (\<lambda>x. f (g x) * g' x)) {a..b}"
proof (cases "a < b")
  assume "a < b"
  from mono have inj: "inj_on g {a..b}" by (rule strict_mono_on_imp_inj_on)
  from mono have mono': "mono_on g {a..b}" by (rule strict_mono_on_imp_mono_on)
  from mono' derivg have "\<And>x. x \<in> {a<..<b} \<Longrightarrow> g' x \<ge> 0"
    by (rule mono_on_imp_deriv_nonneg) (auto simp: interior_atLeastAtMost_real)
  from contg' this have derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
    by (rule continuous_ge_on_Iii) (simp_all add: `a < b`)

  from derivg have contg: "continuous_on {a..b} g" by (rule has_real_derivative_imp_continuous_on)
  have A: "h -` {a..b} = {g a..g b}"
  proof (intro equalityI subsetI)
    fix x assume x: "x \<in> h -` {a..b}"
    hence "g (h x) \<in> {g a..g b}" by (auto intro: mono_onD[OF mono'])
    with inv and x show "x \<in> {g a..g b}" by simp
  next
    fix y assume y: "y \<in> {g a..g b}"
    with IVT'[OF _ _ _ contg, of y] obtain x where "x \<in> {a..b}" "y = g x" by auto
    with range and inv show "y \<in> h -` {a..b}" by auto
  qed

  have prob': "subprob_space (distr (density lborel f) lborel h)"
    by (rule subprob_space.subprob_space_distr[OF prob]) (simp_all add: Mh)
  have B: "emeasure (distr (density lborel f) lborel h) {a..b} = 
            \<integral>\<^sup>+x. f x * indicator (h -` {a..b}) x \<partial>lborel"
    by (subst emeasure_distr) (simp_all add: emeasure_density Mf Mh measurable_sets_borel[OF Mh])
  also note A
  also have "emeasure (distr (density lborel f) lborel h) {a..b} \<le> 1"
    by (rule subprob_space.subprob_emeasure_le_1) (rule prob')
  hence "emeasure (distr (density lborel f) lborel h) {a..b} \<noteq> \<infinity>" by auto
  with assms have "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
                      (\<integral>\<^sup>+x. f (g x) * g' x * indicator {a..b} x \<partial>lborel)"
    by (intro nn_integral_substitution_aux)
       (auto simp: derivg_nonneg A B emeasure_density mult.commute `a < b`)
  also have "... = emeasure (density lborel (\<lambda>x. f (g x) * g' x)) {a..b}" 
    by (simp add: emeasure_density)
  finally show ?thesis .
next
  assume "\<not>a < b"
  with `a \<le> b` have [simp]: "b = a" by (simp add: not_less del: `a \<le> b`)
  from inv and range have "h -` {a} = {g a}" by auto
  thus ?thesis by (simp_all add: emeasure_distr emeasure_density measurable_sets_borel[OF Mh])
qed

locale pair_subprob_space = 
  pair_sigma_finite M1 M2 + M1: subprob_space M1 + M2: subprob_space M2 for M1 M2

sublocale pair_subprob_space \<subseteq> P: subprob_space "M1 \<Otimes>\<^sub>M M2"
proof
  have "\<And>a b. \<lbrakk>a \<ge> 0; b \<ge> 0; a \<le> 1; b \<le> 1\<rbrakk> \<Longrightarrow> a * b \<le> (1::ereal)"
    by (metis monoid_mult_class.mult.left_neutral dual_order.trans ereal_mult_right_mono)
  from this[OF _ _ M1.emeasure_space_le_1 M2.emeasure_space_le_1]
    show "emeasure (M1 \<Otimes>\<^sub>M M2) (space (M1 \<Otimes>\<^sub>M M2)) \<le> 1"
    by (simp add: M2.emeasure_pair_measure_Times space_pair_measure emeasure_nonneg)
  from M1.subprob_not_empty and M2.subprob_not_empty show "space (M1 \<Otimes>\<^sub>M M2) \<noteq> {}"
    by (simp add: space_pair_measure)
qed

lemma subprob_space_null_measure_iff:
    "subprob_space (null_measure M) \<longleftrightarrow> space M \<noteq> {}"
  by (auto intro!: subprob_spaceI dest: subprob_space.subprob_not_empty)

lemma subprob_space_restrict_space:
  assumes M: "subprob_space M"
  and A: "A \<inter> space M \<in> sets M" "A \<inter> space M \<noteq> {}"
  shows "subprob_space (restrict_space M A)"
proof(rule subprob_spaceI)
  have "emeasure (restrict_space M A) (space (restrict_space M A)) = emeasure M (A \<inter> space M)"
    using A by(simp add: emeasure_restrict_space space_restrict_space)
  also have "\<dots> \<le> 1" by(rule subprob_space.subprob_emeasure_le_1)(rule M)
  finally show "emeasure (restrict_space M A) (space (restrict_space M A)) \<le> 1" .
next
  show "space (restrict_space M A) \<noteq> {}"
    using A by(simp add: space_restrict_space)
qed

definition subprob_algebra :: "'a measure \<Rightarrow> 'a measure measure" where
  "subprob_algebra K =
    (\<Squnion>\<^sub>\<sigma> A\<in>sets K. vimage_algebra {M. subprob_space M \<and> sets M = sets K} (\<lambda>M. emeasure M A) borel)"

lemma space_subprob_algebra: "space (subprob_algebra A) = {M. subprob_space M \<and> sets M = sets A}"
  by (auto simp add: subprob_algebra_def space_Sup_sigma)

lemma subprob_algebra_cong: "sets M = sets N \<Longrightarrow> subprob_algebra M = subprob_algebra N"
  by (simp add: subprob_algebra_def)

lemma measurable_emeasure_subprob_algebra[measurable]: 
  "a \<in> sets A \<Longrightarrow> (\<lambda>M. emeasure M a) \<in> borel_measurable (subprob_algebra A)"
  by (auto intro!: measurable_Sup_sigma1 measurable_vimage_algebra1 simp: subprob_algebra_def)

lemma subprob_measurableD:
  assumes N: "N \<in> measurable M (subprob_algebra S)" and x: "x \<in> space M"
  shows "space (N x) = space S"
    and "sets (N x) = sets S"
    and "measurable (N x) K = measurable S K"
    and "measurable K (N x) = measurable K S"
  using measurable_space[OF N x]
  by (auto simp: space_subprob_algebra intro!: measurable_cong_sets dest: sets_eq_imp_space_eq)

ML {*

fun subprob_cong thm ctxt = (
  let
    val thm' = Thm.transfer (Proof_Context.theory_of ctxt) thm
    val free = thm' |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_comb |> fst |>
      dest_comb |> snd |> strip_abs_body |> head_of |> is_Free
  in
    if free then ([], Measurable.add_local_cong (thm' RS @{thm subprob_measurableD(2)}) ctxt)
            else ([], ctxt)
  end
  handle THM _ => ([], ctxt) | TERM _ => ([], ctxt))

*}

setup \<open>
  Context.theory_map (Measurable.add_preprocessor "subprob_cong" subprob_cong)
\<close>

context
  fixes K M N assumes K: "K \<in> measurable M (subprob_algebra N)"
begin

lemma subprob_space_kernel: "a \<in> space M \<Longrightarrow> subprob_space (K a)"
  using measurable_space[OF K] by (simp add: space_subprob_algebra)

lemma sets_kernel: "a \<in> space M \<Longrightarrow> sets (K a) = sets N"
  using measurable_space[OF K] by (simp add: space_subprob_algebra)

lemma measurable_emeasure_kernel[measurable]: 
    "A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M"
  using measurable_compose[OF K measurable_emeasure_subprob_algebra] .

end

lemma measurable_subprob_algebra:
  "(\<And>a. a \<in> space M \<Longrightarrow> subprob_space (K a)) \<Longrightarrow>
  (\<And>a. a \<in> space M \<Longrightarrow> sets (K a) = sets N) \<Longrightarrow>
  (\<And>A. A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M) \<Longrightarrow>
  K \<in> measurable M (subprob_algebra N)"
  by (auto intro!: measurable_Sup_sigma2 measurable_vimage_algebra2 simp: subprob_algebra_def)

lemma measurable_submarkov:
  "K \<in> measurable M (subprob_algebra M) \<longleftrightarrow>
    (\<forall>x\<in>space M. subprob_space (K x) \<and> sets (K x) = sets M) \<and>
    (\<forall>A\<in>sets M. (\<lambda>x. emeasure (K x) A) \<in> measurable M borel)"
proof
  assume "(\<forall>x\<in>space M. subprob_space (K x) \<and> sets (K x) = sets M) \<and>
    (\<forall>A\<in>sets M. (\<lambda>x. emeasure (K x) A) \<in> borel_measurable M)"
  then show "K \<in> measurable M (subprob_algebra M)"
    by (intro measurable_subprob_algebra) auto
next
  assume "K \<in> measurable M (subprob_algebra M)"
  then show "(\<forall>x\<in>space M. subprob_space (K x) \<and> sets (K x) = sets M) \<and>
    (\<forall>A\<in>sets M. (\<lambda>x. emeasure (K x) A) \<in> borel_measurable M)"
    by (auto dest: subprob_space_kernel sets_kernel)
qed

lemma space_subprob_algebra_empty_iff:
  "space (subprob_algebra N) = {} \<longleftrightarrow> space N = {}"
proof
  have "\<And>x. x \<in> space N \<Longrightarrow> density N (\<lambda>_. 0) \<in> space (subprob_algebra N)"
    by (auto simp: space_subprob_algebra emeasure_density intro!: subprob_spaceI)
  then show "space (subprob_algebra N) = {} \<Longrightarrow> space N = {}"
    by auto
next
  assume "space N = {}"
  hence "sets N = {{}}" by (simp add: space_empty_iff)
  moreover have "\<And>M. subprob_space M \<Longrightarrow> sets M \<noteq> {{}}"
    by (simp add: subprob_space.subprob_not_empty space_empty_iff[symmetric])
  ultimately show "space (subprob_algebra N) = {}" by (auto simp: space_subprob_algebra)
qed

lemma nn_integral_measurable_subprob_algebra':
  assumes f: "f \<in> borel_measurable N" "\<And>x. 0 \<le> f x"
  shows "(\<lambda>M. integral\<^sup>N M f) \<in> borel_measurable (subprob_algebra N)" (is "_ \<in> ?B")
  using f
proof induct
  case (cong f g)
  moreover have "(\<lambda>M'. \<integral>\<^sup>+M''. f M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. \<integral>\<^sup>+M''. g M'' \<partial>M') \<in> ?B"
    by (intro measurable_cong nn_integral_cong cong)
       (auto simp: space_subprob_algebra dest!: sets_eq_imp_space_eq)
  ultimately show ?case by simp
next
  case (set B)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. indicator B M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. emeasure M' B) \<in> ?B"
    by (intro measurable_cong nn_integral_indicator) (simp add: space_subprob_algebra)
  ultimately show ?case
    by (simp add: measurable_emeasure_subprob_algebra)
next
  case (mult f c)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. c * f M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. c * \<integral>\<^sup>+M''. f M'' \<partial>M') \<in> ?B"
    by (intro measurable_cong nn_integral_cmult) (auto simp add: space_subprob_algebra)
  ultimately show ?case
    using [[simp_trace_new]]
    by simp
next
  case (add f g)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. f M'' + g M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. (\<integral>\<^sup>+M''. f M'' \<partial>M') + (\<integral>\<^sup>+M''. g M'' \<partial>M')) \<in> ?B"
    by (intro measurable_cong nn_integral_add) (auto simp add: space_subprob_algebra)
  ultimately show ?case
    by (simp add: ac_simps)
next
  case (seq F)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. (SUP i. F i) M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. SUP i. (\<integral>\<^sup>+M''. F i M'' \<partial>M')) \<in> ?B"
    unfolding SUP_apply
    by (intro measurable_cong nn_integral_monotone_convergence_SUP) (auto simp add: space_subprob_algebra)
  ultimately show ?case
    by (simp add: ac_simps)
qed

lemma nn_integral_measurable_subprob_algebra:
  "f \<in> borel_measurable N \<Longrightarrow> (\<lambda>M. integral\<^sup>N M f) \<in> borel_measurable (subprob_algebra N)"
  by (subst nn_integral_max_0[symmetric])
     (auto intro!: nn_integral_measurable_subprob_algebra')

lemma measurable_distr:
  assumes [measurable]: "f \<in> measurable M N"
  shows "(\<lambda>M'. distr M' N f) \<in> measurable (subprob_algebra M) (subprob_algebra N)"
proof (cases "space N = {}")
  assume not_empty: "space N \<noteq> {}"
  show ?thesis
  proof (rule measurable_subprob_algebra)
    fix A assume A: "A \<in> sets N"
    then have "(\<lambda>M'. emeasure (distr M' N f) A) \<in> borel_measurable (subprob_algebra M) \<longleftrightarrow>
      (\<lambda>M'. emeasure M' (f -` A \<inter> space M)) \<in> borel_measurable (subprob_algebra M)"
      by (intro measurable_cong)
         (auto simp: emeasure_distr space_subprob_algebra
               intro!: arg_cong2[where f=emeasure] sets_eq_imp_space_eq arg_cong2[where f="op \<inter>"])
    also have "\<dots>"
      using A by (intro measurable_emeasure_subprob_algebra) simp
    finally show "(\<lambda>M'. emeasure (distr M' N f) A) \<in> borel_measurable (subprob_algebra M)" .
  qed (auto intro!: subprob_space.subprob_space_distr simp: space_subprob_algebra not_empty cong: measurable_cong_sets)
qed (insert assms, auto simp: measurable_empty_iff space_subprob_algebra_empty_iff)

lemma emeasure_space_subprob_algebra[measurable]:
  "(\<lambda>a. emeasure a (space a)) \<in> borel_measurable (subprob_algebra N)"
proof-
  have "(\<lambda>a. emeasure a (space N)) \<in> borel_measurable (subprob_algebra N)" (is "?f \<in> ?M")
    by (rule measurable_emeasure_subprob_algebra) simp
  also have "?f \<in> ?M \<longleftrightarrow> (\<lambda>a. emeasure a (space a)) \<in> ?M"
    by (rule measurable_cong) (auto simp: space_subprob_algebra dest: sets_eq_imp_space_eq)
  finally show ?thesis .
qed

(* TODO: Rename. This name is too general – Manuel *)
lemma measurable_pair_measure:
  assumes f: "f \<in> measurable M (subprob_algebra N)"
  assumes g: "g \<in> measurable M (subprob_algebra L)"
  shows "(\<lambda>x. f x \<Otimes>\<^sub>M g x) \<in> measurable M (subprob_algebra (N \<Otimes>\<^sub>M L))"
proof (rule measurable_subprob_algebra)
  { fix x assume "x \<in> space M"
    with measurable_space[OF f] measurable_space[OF g]
    have fx: "f x \<in> space (subprob_algebra N)" and gx: "g x \<in> space (subprob_algebra L)"
      by auto
    interpret F: subprob_space "f x"
      using fx by (simp add: space_subprob_algebra)
    interpret G: subprob_space "g x"
      using gx by (simp add: space_subprob_algebra)

    interpret pair_subprob_space "f x" "g x" ..
    show "subprob_space (f x \<Otimes>\<^sub>M g x)" by unfold_locales
    show sets_eq: "sets (f x \<Otimes>\<^sub>M g x) = sets (N \<Otimes>\<^sub>M L)"
      using fx gx by (simp add: space_subprob_algebra)

    have 1: "\<And>A B. A \<in> sets N \<Longrightarrow> B \<in> sets L \<Longrightarrow> emeasure (f x \<Otimes>\<^sub>M g x) (A \<times> B) = emeasure (f x) A * emeasure (g x) B"
      using fx gx by (intro G.emeasure_pair_measure_Times) (auto simp: space_subprob_algebra) 
    have "emeasure (f x \<Otimes>\<^sub>M g x) (space (f x \<Otimes>\<^sub>M g x)) = 
              emeasure (f x) (space (f x)) * emeasure (g x) (space (g x))"
      by (subst G.emeasure_pair_measure_Times[symmetric]) (simp_all add: space_pair_measure)
    hence 2: "\<And>A. A \<in> sets (N \<Otimes>\<^sub>M L) \<Longrightarrow> emeasure (f x \<Otimes>\<^sub>M g x) (space N \<times> space L - A) =
                                             ... - emeasure (f x \<Otimes>\<^sub>M g x) A"
      using emeasure_compl[OF _ P.emeasure_finite]
      unfolding sets_eq
      unfolding sets_eq_imp_space_eq[OF sets_eq]
      by (simp add: space_pair_measure G.emeasure_pair_measure_Times)
    note 1 2 sets_eq }
  note Times = this(1) and Compl = this(2) and sets_eq = this(3)

  fix A assume A: "A \<in> sets (N \<Otimes>\<^sub>M L)"
  show "(\<lambda>a. emeasure (f a \<Otimes>\<^sub>M g a) A) \<in> borel_measurable M"
    using Int_stable_pair_measure_generator pair_measure_closed A
    unfolding sets_pair_measure
  proof (induct A rule: sigma_sets_induct_disjoint)
    case (basic A) then show ?case
      by (auto intro!: borel_measurable_ereal_times simp: Times cong: measurable_cong)
         (auto intro!: measurable_emeasure_kernel f g)
  next
    case (compl A)
    then have A: "A \<in> sets (N \<Otimes>\<^sub>M L)"
      by (auto simp: sets_pair_measure)
    have "(\<lambda>x. emeasure (f x) (space (f x)) * emeasure (g x) (space (g x)) - 
                   emeasure (f x \<Otimes>\<^sub>M g x) A) \<in> borel_measurable M" (is "?f \<in> ?M")
      using compl(2) f g by measurable
    thus ?case by (simp add: Compl A cong: measurable_cong)
  next
    case (union A)
    then have "range A \<subseteq> sets (N \<Otimes>\<^sub>M L)" "disjoint_family A"
      by (auto simp: sets_pair_measure)
    then have "(\<lambda>a. emeasure (f a \<Otimes>\<^sub>M g a) (\<Union>i. A i)) \<in> borel_measurable M \<longleftrightarrow>
      (\<lambda>a. \<Sum>i. emeasure (f a \<Otimes>\<^sub>M g a) (A i)) \<in> borel_measurable M"
      by (intro measurable_cong suminf_emeasure[symmetric])
         (auto simp: sets_eq)
    also have "\<dots>"
      using union by auto
    finally show ?case .
  qed simp
qed

lemma restrict_space_measurable:
  assumes X: "X \<noteq> {}" "X \<in> sets K"
  assumes N: "N \<in> measurable M (subprob_algebra K)"
  shows "(\<lambda>x. restrict_space (N x) X) \<in> measurable M (subprob_algebra (restrict_space K X))"
proof (rule measurable_subprob_algebra)
  fix a assume a: "a \<in> space M"
  from N[THEN measurable_space, OF this]
  have "subprob_space (N a)" and [simp]: "sets (N a) = sets K" "space (N a) = space K"
    by (auto simp add: space_subprob_algebra dest: sets_eq_imp_space_eq)
  then interpret subprob_space "N a"
    by simp
  show "subprob_space (restrict_space (N a) X)"
  proof
    show "space (restrict_space (N a) X) \<noteq> {}"
      using X by (auto simp add: space_restrict_space)
    show "emeasure (restrict_space (N a) X) (space (restrict_space (N a) X)) \<le> 1"
      using X by (simp add: emeasure_restrict_space space_restrict_space subprob_emeasure_le_1)
  qed
  show "sets (restrict_space (N a) X) = sets (restrict_space K X)"
    by (intro sets_restrict_space_cong) fact
next
  fix A assume A: "A \<in> sets (restrict_space K X)"
  show "(\<lambda>a. emeasure (restrict_space (N a) X) A) \<in> borel_measurable M"
  proof (subst measurable_cong)
    fix a assume "a \<in> space M"
    from N[THEN measurable_space, OF this]
    have [simp]: "sets (N a) = sets K" "space (N a) = space K"
      by (auto simp add: space_subprob_algebra dest: sets_eq_imp_space_eq)
    show "emeasure (restrict_space (N a) X) A = emeasure (N a) (A \<inter> X)"
      using X A by (subst emeasure_restrict_space) (auto simp add: sets_restrict_space ac_simps)
  next
    show "(\<lambda>w. emeasure (N w) (A \<inter> X)) \<in> borel_measurable M"
      using A X
      by (intro measurable_compose[OF N measurable_emeasure_subprob_algebra])
         (auto simp: sets_restrict_space)
  qed
qed

section {* Properties of return *}

definition return :: "'a measure \<Rightarrow> 'a \<Rightarrow> 'a measure" where
  "return R x = measure_of (space R) (sets R) (\<lambda>A. indicator A x)"

lemma space_return[simp]: "space (return M x) = space M"
  by (simp add: return_def)

lemma sets_return[simp]: "sets (return M x) = sets M"
  by (simp add: return_def)

lemma measurable_return1[simp]: "measurable (return N x) L = measurable N L"
  by (simp cong: measurable_cong_sets) 

lemma measurable_return2[simp]: "measurable L (return N x) = measurable L N"
  by (simp cong: measurable_cong_sets) 

lemma return_sets_cong: "sets M = sets N \<Longrightarrow> return M = return N"
  by (auto dest: sets_eq_imp_space_eq simp: fun_eq_iff return_def)

lemma return_cong: "sets A = sets B \<Longrightarrow> return A x = return B x"
  by (auto simp add: return_def dest: sets_eq_imp_space_eq)

lemma emeasure_return[simp]:
  assumes "A \<in> sets M"
  shows "emeasure (return M x) A = indicator A x"
proof (rule emeasure_measure_of[OF return_def])
  show "sets M \<subseteq> Pow (space M)" by (rule sets.space_closed)
  show "positive (sets (return M x)) (\<lambda>A. indicator A x)" by (simp add: positive_def)
  from assms show "A \<in> sets (return M x)" unfolding return_def by simp
  show "countably_additive (sets (return M x)) (\<lambda>A. indicator A x)"
    by (auto intro: countably_additiveI simp: suminf_indicator)
qed

lemma prob_space_return: "x \<in> space M \<Longrightarrow> prob_space (return M x)"
  by rule simp

lemma subprob_space_return: "x \<in> space M \<Longrightarrow> subprob_space (return M x)"
  by (intro prob_space_return prob_space_imp_subprob_space)

lemma subprob_space_return_ne: 
  assumes "space M \<noteq> {}" shows "subprob_space (return M x)"
proof
  show "emeasure (return M x) (space (return M x)) \<le> 1"
    by (subst emeasure_return) (auto split: split_indicator)
qed (simp, fact)

lemma measure_return: assumes X: "X \<in> sets M" shows "measure (return M x) X = indicator X x"
  unfolding measure_def emeasure_return[OF X, of x] by (simp split: split_indicator)

lemma AE_return:
  assumes [simp]: "x \<in> space M" and [measurable]: "Measurable.pred M P"
  shows "(AE y in return M x. P y) \<longleftrightarrow> P x"
proof -
  have "(AE y in return M x. y \<notin> {x\<in>space M. \<not> P x}) \<longleftrightarrow> P x"
    by (subst AE_iff_null_sets[symmetric]) (simp_all add: null_sets_def split: split_indicator)
  also have "(AE y in return M x. y \<notin> {x\<in>space M. \<not> P x}) \<longleftrightarrow> (AE y in return M x. P y)"
    by (rule AE_cong) auto
  finally show ?thesis .
qed
  
lemma nn_integral_return:
  assumes "g x \<ge> 0" "x \<in> space M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ a. g a \<partial>return M x) = g x"
proof-
  interpret prob_space "return M x" by (rule prob_space_return[OF `x \<in> space M`])
  have "(\<integral>\<^sup>+ a. g a \<partial>return M x) = (\<integral>\<^sup>+ a. g x \<partial>return M x)" using assms
    by (intro nn_integral_cong_AE) (auto simp: AE_return)
  also have "... = g x"
    using nn_integral_const[OF `g x \<ge> 0`, of "return M x"] emeasure_space_1 by simp
  finally show ?thesis .
qed

lemma integral_return:
  fixes g :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes "x \<in> space M" "g \<in> borel_measurable M"
  shows "(\<integral>a. g a \<partial>return M x) = g x"
proof-
  interpret prob_space "return M x" by (rule prob_space_return[OF `x \<in> space M`])
  have "(\<integral>a. g a \<partial>return M x) = (\<integral>a. g x \<partial>return M x)" using assms
    by (intro integral_cong_AE) (auto simp: AE_return)
  then show ?thesis
    using prob_space by simp
qed

lemma return_measurable[measurable]: "return N \<in> measurable N (subprob_algebra N)"
  by (rule measurable_subprob_algebra) (auto simp: subprob_space_return)

lemma distr_return:
  assumes "f \<in> measurable M N" and "x \<in> space M"
  shows "distr (return M x) N f = return N (f x)"
  using assms by (intro measure_eqI) (simp_all add: indicator_def emeasure_distr)

lemma return_restrict_space:
  "\<Omega> \<in> sets M \<Longrightarrow> return (restrict_space M \<Omega>) x = restrict_space (return M x) \<Omega>"
  by (auto intro!: measure_eqI simp: sets_restrict_space emeasure_restrict_space)

lemma measurable_distr2:
  assumes f[measurable]: "split f \<in> measurable (L \<Otimes>\<^sub>M M) N"
  assumes g[measurable]: "g \<in> measurable L (subprob_algebra M)"
  shows "(\<lambda>x. distr (g x) N (f x)) \<in> measurable L (subprob_algebra N)"
proof -
  have "(\<lambda>x. distr (g x) N (f x)) \<in> measurable L (subprob_algebra N)
    \<longleftrightarrow> (\<lambda>x. distr (return L x \<Otimes>\<^sub>M g x) N (split f)) \<in> measurable L (subprob_algebra N)"
  proof (rule measurable_cong)
    fix x assume x: "x \<in> space L"
    have gx: "g x \<in> space (subprob_algebra M)"
      using measurable_space[OF g x] .
    then have [simp]: "sets (g x) = sets M"
      by (simp add: space_subprob_algebra)
    then have [simp]: "space (g x) = space M"
      by (rule sets_eq_imp_space_eq)
    let ?R = "return L x"
    from measurable_compose_Pair1[OF x f] have f_M': "f x \<in> measurable M N"
      by simp
    interpret subprob_space "g x"
      using gx by (simp add: space_subprob_algebra)
    have space_pair_M'[simp]: "\<And>X. space (X \<Otimes>\<^sub>M g x) = space (X \<Otimes>\<^sub>M M)"
      by (simp add: space_pair_measure)
    show "distr (g x) N (f x) = distr (?R \<Otimes>\<^sub>M g x) N (split f)" (is "?l = ?r")
    proof (rule measure_eqI)
      show "sets ?l = sets ?r"
        by simp
    next
      fix A assume "A \<in> sets ?l"
      then have A[measurable]: "A \<in> sets N"
        by simp
      then have "emeasure ?r A = emeasure (?R \<Otimes>\<^sub>M g x) ((\<lambda>(x, y). f x y) -` A \<inter> space (?R \<Otimes>\<^sub>M g x))"
        by (auto simp add: emeasure_distr f_M' cong: measurable_cong_sets)
      also have "\<dots> = (\<integral>\<^sup>+M''. emeasure (g x) (f M'' -` A \<inter> space M) \<partial>?R)"
        apply (subst emeasure_pair_measure_alt)
        apply (rule measurable_sets[OF _ A])
        apply (auto simp add: f_M' cong: measurable_cong_sets)
        apply (intro nn_integral_cong arg_cong[where f="emeasure (g x)"])
        apply (auto simp: space_subprob_algebra space_pair_measure)
        done
      also have "\<dots> = emeasure (g x) (f x -` A \<inter> space M)"
        by (subst nn_integral_return)
           (auto simp: x intro!: measurable_emeasure)
      also have "\<dots> = emeasure ?l A"
        by (simp add: emeasure_distr f_M' cong: measurable_cong_sets)
      finally show "emeasure ?l A = emeasure ?r A" ..
    qed
  qed
  also have "\<dots>"
    apply (intro measurable_compose[OF measurable_pair_measure measurable_distr])
    apply (rule return_measurable)
    apply measurable
    done
  finally show ?thesis .
qed

lemma nn_integral_measurable_subprob_algebra2:
  assumes f[measurable]: "(\<lambda>(x, y). f x y) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  assumes N[measurable]: "L \<in> measurable M (subprob_algebra N)"
  shows "(\<lambda>x. integral\<^sup>N (L x) (f x)) \<in> borel_measurable M"
proof -
  note nn_integral_measurable_subprob_algebra[measurable]
  note measurable_distr2[measurable]
  have "(\<lambda>x. integral\<^sup>N (distr (L x) (M \<Otimes>\<^sub>M N) (\<lambda>y. (x, y))) (\<lambda>(x, y). f x y)) \<in> borel_measurable M"
    by measurable
  then show "(\<lambda>x. integral\<^sup>N (L x) (f x)) \<in> borel_measurable M"
    by (rule measurable_cong[THEN iffD1, rotated])
       (simp add: nn_integral_distr)
qed

lemma emeasure_measurable_subprob_algebra2:
  assumes A[measurable]: "(SIGMA x:space M. A x) \<in> sets (M \<Otimes>\<^sub>M N)"
  assumes L[measurable]: "L \<in> measurable M (subprob_algebra N)"
  shows "(\<lambda>x. emeasure (L x) (A x)) \<in> borel_measurable M"
proof -
  { fix x assume "x \<in> space M"
    then have "Pair x -` Sigma (space M) A = A x"
      by auto
    with sets_Pair1[OF A, of x] have "A x \<in> sets N"
      by auto }
  note ** = this

  have *: "\<And>x. fst x \<in> space M \<Longrightarrow> snd x \<in> A (fst x) \<longleftrightarrow> x \<in> (SIGMA x:space M. A x)"
    by (auto simp: fun_eq_iff)
  have "(\<lambda>(x, y). indicator (A x) y::ereal) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    apply measurable
    apply (subst measurable_cong)
    apply (rule *)
    apply (auto simp: space_pair_measure)
    done
  then have "(\<lambda>x. integral\<^sup>N (L x) (indicator (A x))) \<in> borel_measurable M"
    by (intro nn_integral_measurable_subprob_algebra2[where N=N] ereal_indicator_nonneg L)
  then show "(\<lambda>x. emeasure (L x) (A x)) \<in> borel_measurable M"
    apply (rule measurable_cong[THEN iffD1, rotated])
    apply (rule nn_integral_indicator)
    apply (simp add: subprob_measurableD[OF L] **)
    done
qed

lemma measure_measurable_subprob_algebra2:
  assumes A[measurable]: "(SIGMA x:space M. A x) \<in> sets (M \<Otimes>\<^sub>M N)"
  assumes L[measurable]: "L \<in> measurable M (subprob_algebra N)"
  shows "(\<lambda>x. measure (L x) (A x)) \<in> borel_measurable M"
  unfolding measure_def
  by (intro borel_measurable_real_of_ereal emeasure_measurable_subprob_algebra2[OF assms])

definition "select_sets M = (SOME N. sets M = sets (subprob_algebra N))"

lemma select_sets1:
  "sets M = sets (subprob_algebra N) \<Longrightarrow> sets M = sets (subprob_algebra (select_sets M))"
  unfolding select_sets_def by (rule someI)

lemma sets_select_sets[simp]:
  assumes sets: "sets M = sets (subprob_algebra N)"
  shows "sets (select_sets M) = sets N"
  unfolding select_sets_def
proof (rule someI2)
  show "sets M = sets (subprob_algebra N)"
    by fact
next
  fix L assume "sets M = sets (subprob_algebra L)"
  with sets have eq: "space (subprob_algebra N) = space (subprob_algebra L)"
    by (intro sets_eq_imp_space_eq) simp
  show "sets L = sets N"
  proof cases
    assume "space (subprob_algebra N) = {}"
    with space_subprob_algebra_empty_iff[of N] space_subprob_algebra_empty_iff[of L]
    show ?thesis
      by (simp add: eq space_empty_iff)
  next
    assume "space (subprob_algebra N) \<noteq> {}"
    with eq show ?thesis
      by (fastforce simp add: space_subprob_algebra)
  qed
qed

lemma space_select_sets[simp]:
  "sets M = sets (subprob_algebra N) \<Longrightarrow> space (select_sets M) = space N"
  by (intro sets_eq_imp_space_eq sets_select_sets)

section {* Join *}

definition join :: "'a measure measure \<Rightarrow> 'a measure" where
  "join M = measure_of (space (select_sets M)) (sets (select_sets M)) (\<lambda>B. \<integral>\<^sup>+ M'. emeasure M' B \<partial>M)"

lemma
  shows space_join[simp]: "space (join M) = space (select_sets M)"
    and sets_join[simp]: "sets (join M) = sets (select_sets M)"
  by (simp_all add: join_def)

lemma emeasure_join:
  assumes M[simp, measurable_cong]: "sets M = sets (subprob_algebra N)" and A: "A \<in> sets N"
  shows "emeasure (join M) A = (\<integral>\<^sup>+ M'. emeasure M' A \<partial>M)"
proof (rule emeasure_measure_of[OF join_def])
  show "countably_additive (sets (join M)) (\<lambda>B. \<integral>\<^sup>+ M'. emeasure M' B \<partial>M)"
  proof (rule countably_additiveI)
    fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets (join M)" "disjoint_family A"
    have "(\<Sum>i. \<integral>\<^sup>+ M'. emeasure M' (A i) \<partial>M) = (\<integral>\<^sup>+M'. (\<Sum>i. emeasure M' (A i)) \<partial>M)"
      using A by (subst nn_integral_suminf) (auto simp: measurable_emeasure_subprob_algebra)
    also have "\<dots> = (\<integral>\<^sup>+M'. emeasure M' (\<Union>i. A i) \<partial>M)"
    proof (rule nn_integral_cong)
      fix M' assume "M' \<in> space M"
      then show "(\<Sum>i. emeasure M' (A i)) = emeasure M' (\<Union>i. A i)"
        using A sets_eq_imp_space_eq[OF M] by (simp add: suminf_emeasure space_subprob_algebra)
    qed
    finally show "(\<Sum>i. \<integral>\<^sup>+M'. emeasure M' (A i) \<partial>M) = (\<integral>\<^sup>+M'. emeasure M' (\<Union>i. A i) \<partial>M)" .
  qed
qed (auto simp: A sets.space_closed positive_def nn_integral_nonneg)

lemma measurable_join:
  "join \<in> measurable (subprob_algebra (subprob_algebra N)) (subprob_algebra N)"
proof (cases "space N \<noteq> {}", rule measurable_subprob_algebra)
  fix A assume "A \<in> sets N"
  let ?B = "borel_measurable (subprob_algebra (subprob_algebra N))"
  have "(\<lambda>M'. emeasure (join M') A) \<in> ?B \<longleftrightarrow> (\<lambda>M'. (\<integral>\<^sup>+ M''. emeasure M'' A \<partial>M')) \<in> ?B"
  proof (rule measurable_cong)
    fix M' assume "M' \<in> space (subprob_algebra (subprob_algebra N))"
    then show "emeasure (join M') A = (\<integral>\<^sup>+ M''. emeasure M'' A \<partial>M')"
      by (intro emeasure_join) (auto simp: space_subprob_algebra `A\<in>sets N`)
  qed
  also have "(\<lambda>M'. \<integral>\<^sup>+M''. emeasure M'' A \<partial>M') \<in> ?B"
    using measurable_emeasure_subprob_algebra[OF `A\<in>sets N`]
    by (rule nn_integral_measurable_subprob_algebra)
  finally show "(\<lambda>M'. emeasure (join M') A) \<in> borel_measurable (subprob_algebra (subprob_algebra N))" .
next
  assume [simp]: "space N \<noteq> {}"
  fix M assume M: "M \<in> space (subprob_algebra (subprob_algebra N))"
  then have "(\<integral>\<^sup>+M'. emeasure M' (space N) \<partial>M) \<le> (\<integral>\<^sup>+M'. 1 \<partial>M)"
    apply (intro nn_integral_mono)
    apply (auto simp: space_subprob_algebra 
                 dest!: sets_eq_imp_space_eq subprob_space.emeasure_space_le_1)
    done
  with M show "subprob_space (join M)"
    by (intro subprob_spaceI)
       (auto simp: emeasure_join space_subprob_algebra M assms dest: subprob_space.emeasure_space_le_1)
next
  assume "\<not>(space N \<noteq> {})"
  thus ?thesis by (simp add: measurable_empty_iff space_subprob_algebra_empty_iff)
qed (auto simp: space_subprob_algebra)

lemma nn_integral_join':
  assumes f: "f \<in> borel_measurable N" "\<And>x. 0 \<le> f x"
    and M[measurable_cong]: "sets M = sets (subprob_algebra N)"
  shows "(\<integral>\<^sup>+x. f x \<partial>join M) = (\<integral>\<^sup>+M'. \<integral>\<^sup>+x. f x \<partial>M' \<partial>M)"
  using f
proof induct
  case (cong f g)
  moreover have "integral\<^sup>N (join M) f = integral\<^sup>N (join M) g"
    by (intro nn_integral_cong cong) (simp add: M)
  moreover from M have "(\<integral>\<^sup>+ M'. integral\<^sup>N M' f \<partial>M) = (\<integral>\<^sup>+ M'. integral\<^sup>N M' g \<partial>M)"
    by (intro nn_integral_cong cong)
       (auto simp add: space_subprob_algebra dest!: sets_eq_imp_space_eq)
  ultimately show ?case
    by simp
next
  case (set A)
  moreover with M have "(\<integral>\<^sup>+ M'. integral\<^sup>N M' (indicator A) \<partial>M) = (\<integral>\<^sup>+ M'. emeasure M' A \<partial>M)" 
    by (intro nn_integral_cong nn_integral_indicator)
       (auto simp: space_subprob_algebra dest!: sets_eq_imp_space_eq)
  ultimately show ?case
    using M by (simp add: emeasure_join)
next
  case (mult f c)
  have "(\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. c * f x \<partial>M' \<partial>M) = (\<integral>\<^sup>+ M'. c * \<integral>\<^sup>+ x. f x \<partial>M' \<partial>M)"
    using mult M M[THEN sets_eq_imp_space_eq]
    by (intro nn_integral_cong nn_integral_cmult) (auto simp add: space_subprob_algebra)
  also have "\<dots> = c * (\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. f x \<partial>M' \<partial>M)"
    using nn_integral_measurable_subprob_algebra[OF mult(3)]
    by (intro nn_integral_cmult mult) (simp add: M)
  also have "\<dots> = c * (integral\<^sup>N (join M) f)"
    by (simp add: mult)
  also have "\<dots> = (\<integral>\<^sup>+ x. c * f x \<partial>join M)"
    using mult(2,3) by (intro nn_integral_cmult[symmetric] mult) (simp add: M cong: measurable_cong_sets)
  finally show ?case by simp
next
  case (add f g)
  have "(\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. f x + g x \<partial>M' \<partial>M) = (\<integral>\<^sup>+ M'. (\<integral>\<^sup>+ x. f x \<partial>M') + (\<integral>\<^sup>+ x. g x \<partial>M') \<partial>M)"
    using add M M[THEN sets_eq_imp_space_eq]
    by (intro nn_integral_cong nn_integral_add) (auto simp add: space_subprob_algebra)
  also have "\<dots> = (\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. f x \<partial>M' \<partial>M) + (\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. g x \<partial>M' \<partial>M)"
    using nn_integral_measurable_subprob_algebra[OF add(1)]
    using nn_integral_measurable_subprob_algebra[OF add(5)]
    by (intro nn_integral_add add) (simp_all add: M nn_integral_nonneg)
  also have "\<dots> = (integral\<^sup>N (join M) f) + (integral\<^sup>N (join M) g)"
    by (simp add: add)
  also have "\<dots> = (\<integral>\<^sup>+ x. f x + g x \<partial>join M)"
    using add by (intro nn_integral_add[symmetric] add) (simp_all add: M cong: measurable_cong_sets)
  finally show ?case by (simp add: ac_simps)
next
  case (seq F)
  have "(\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. (SUP i. F i) x \<partial>M' \<partial>M) = (\<integral>\<^sup>+ M'. (SUP i. \<integral>\<^sup>+ x. F i x \<partial>M') \<partial>M)"
    using seq M M[THEN sets_eq_imp_space_eq] unfolding SUP_apply
    by (intro nn_integral_cong nn_integral_monotone_convergence_SUP)
       (auto simp add: space_subprob_algebra)
  also have "\<dots> = (SUP i. \<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. F i x \<partial>M' \<partial>M)"
    using nn_integral_measurable_subprob_algebra[OF seq(1)] seq
    by (intro nn_integral_monotone_convergence_SUP)
       (simp_all add: M nn_integral_nonneg incseq_nn_integral incseq_def le_fun_def nn_integral_mono )
  also have "\<dots> = (SUP i. integral\<^sup>N (join M) (F i))"
    by (simp add: seq)
  also have "\<dots> = (\<integral>\<^sup>+ x. (SUP i. F i x) \<partial>join M)"
    using seq by (intro nn_integral_monotone_convergence_SUP[symmetric] seq)
                 (simp_all add: M cong: measurable_cong_sets)
  finally show ?case by (simp add: ac_simps)
qed

lemma nn_integral_join:
  assumes f[measurable]: "f \<in> borel_measurable N" "sets M = sets (subprob_algebra N)"
  shows "(\<integral>\<^sup>+x. f x \<partial>join M) = (\<integral>\<^sup>+M'. \<integral>\<^sup>+x. f x \<partial>M' \<partial>M)"
  apply (subst (1 3) nn_integral_max_0[symmetric])
  apply (rule nn_integral_join')
  apply (auto simp: f)
  done

lemma join_assoc:
  assumes M[measurable_cong]: "sets M = sets (subprob_algebra (subprob_algebra N))"
  shows "join (distr M (subprob_algebra N) join) = join (join M)"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (join (distr M (subprob_algebra N) join))"
  then have A: "A \<in> sets N" by simp
  show "emeasure (join (distr M (subprob_algebra N) join)) A = emeasure (join (join M)) A"
    using measurable_join[of N]
    by (auto simp: M A nn_integral_distr emeasure_join measurable_emeasure_subprob_algebra emeasure_nonneg
                   sets_eq_imp_space_eq[OF M] space_subprob_algebra nn_integral_join[OF _ M]
             intro!: nn_integral_cong emeasure_join)
qed (simp add: M)

lemma join_return: 
  assumes "sets M = sets N" and "subprob_space M"
  shows "join (return (subprob_algebra N) M) = M"
  by (rule measure_eqI)
     (simp_all add: emeasure_join emeasure_nonneg space_subprob_algebra  
                    measurable_emeasure_subprob_algebra nn_integral_return assms)

lemma join_return':
  assumes "sets N = sets M"
  shows "join (distr M (subprob_algebra N) (return N)) = M"
apply (rule measure_eqI)
apply (simp add: assms)
apply (subgoal_tac "return N \<in> measurable M (subprob_algebra N)")
apply (simp add: emeasure_join nn_integral_distr measurable_emeasure_subprob_algebra assms)
apply (subst measurable_cong_sets, rule assms[symmetric], rule refl, rule return_measurable)
done

lemma join_distr_distr:
  fixes f :: "'a \<Rightarrow> 'b" and M :: "'a measure measure" and N :: "'b measure"
  assumes "sets M = sets (subprob_algebra R)" and "f \<in> measurable R N"
  shows "join (distr M (subprob_algebra N) (\<lambda>M. distr M N f)) = distr (join M) N f" (is "?r = ?l")
proof (rule measure_eqI)
  fix A assume "A \<in> sets ?r"
  hence A_in_N: "A \<in> sets N" by simp

  from assms have "f \<in> measurable (join M) N" 
      by (simp cong: measurable_cong_sets)
  moreover from assms and A_in_N have "f-`A \<inter> space R \<in> sets R" 
      by (intro measurable_sets) simp_all
  ultimately have "emeasure (distr (join M) N f) A = \<integral>\<^sup>+M'. emeasure M' (f-`A \<inter> space R) \<partial>M"
      by (simp_all add: A_in_N emeasure_distr emeasure_join assms)
  
  also have "... = \<integral>\<^sup>+ x. emeasure (distr x N f) A \<partial>M" using A_in_N
  proof (intro nn_integral_cong, subst emeasure_distr)
    fix M' assume "M' \<in> space M"
    from assms have "space M = space (subprob_algebra R)"
        using sets_eq_imp_space_eq by blast
    with `M' \<in> space M` have [simp]: "sets M' = sets R" using space_subprob_algebra by blast
    show "f \<in> measurable M' N" by (simp cong: measurable_cong_sets add: assms)
    have "space M' = space R" by (rule sets_eq_imp_space_eq) simp
    thus "emeasure M' (f -` A \<inter> space R) = emeasure M' (f -` A \<inter> space M')" by simp
  qed

  also have "(\<lambda>M. distr M N f) \<in> measurable M (subprob_algebra N)"
      by (simp cong: measurable_cong_sets add: assms measurable_distr)
  hence "(\<integral>\<^sup>+ x. emeasure (distr x N f) A \<partial>M) = 
             emeasure (join (distr M (subprob_algebra N) (\<lambda>M. distr M N f))) A"
      by (simp_all add: emeasure_join assms A_in_N nn_integral_distr measurable_emeasure_subprob_algebra)
  finally show "emeasure ?r A = emeasure ?l A" ..
qed simp

definition bind :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b measure) \<Rightarrow> 'b measure" where
  "bind M f = (if space M = {} then count_space {} else
    join (distr M (subprob_algebra (f (SOME x. x \<in> space M))) f))"

adhoc_overloading Monad_Syntax.bind bind

lemma bind_empty: 
  "space M = {} \<Longrightarrow> bind M f = count_space {}"
  by (simp add: bind_def)

lemma bind_nonempty:
  "space M \<noteq> {} \<Longrightarrow> bind M f = join (distr M (subprob_algebra (f (SOME x. x \<in> space M))) f)"
  by (simp add: bind_def)

lemma sets_bind_empty: "sets M = {} \<Longrightarrow> sets (bind M f) = {{}}"
  by (auto simp: bind_def)

lemma space_bind_empty: "space M = {} \<Longrightarrow> space (bind M f) = {}"
  by (simp add: bind_def)

lemma sets_bind[simp, measurable_cong]:
  assumes f: "\<And>x. x \<in> space M \<Longrightarrow> sets (f x) = sets N" and M: "space M \<noteq> {}"
  shows "sets (bind M f) = sets N"
  using f [of "SOME x. x \<in> space M"] by (simp add: bind_nonempty M some_in_eq)

lemma space_bind[simp]: 
  assumes "\<And>x. x \<in> space M \<Longrightarrow> sets (f x) = sets N" and "space M \<noteq> {}"
  shows "space (bind M f) = space N"
  using assms by (intro sets_eq_imp_space_eq sets_bind)

lemma bind_cong: 
  assumes "\<forall>x \<in> space M. f x = g x"
  shows "bind M f = bind M g"
proof (cases "space M = {}")
  assume "space M \<noteq> {}"
  hence "(SOME x. x \<in> space M) \<in> space M" by (rule_tac someI_ex) blast
  with assms have "f (SOME x. x \<in> space M) = g (SOME x. x \<in> space M)" by blast
  with `space M \<noteq> {}` and assms show ?thesis by (simp add: bind_nonempty cong: distr_cong)
qed (simp add: bind_empty)

lemma bind_nonempty':
  assumes "f \<in> measurable M (subprob_algebra N)" "x \<in> space M"
  shows "bind M f = join (distr M (subprob_algebra N) f)"
  using assms
  apply (subst bind_nonempty, blast)
  apply (subst subprob_algebra_cong[OF sets_kernel[OF assms(1) someI_ex]], blast)
  apply (simp add: subprob_algebra_cong[OF sets_kernel[OF assms]])
  done

lemma bind_nonempty'':
  assumes "f \<in> measurable M (subprob_algebra N)" "space M \<noteq> {}"
  shows "bind M f = join (distr M (subprob_algebra N) f)"
  using assms by (auto intro: bind_nonempty')

lemma emeasure_bind:
    "\<lbrakk>space M \<noteq> {}; f \<in> measurable M (subprob_algebra N);X \<in> sets N\<rbrakk>
      \<Longrightarrow> emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. emeasure (f x) X \<partial>M"
  by (simp add: bind_nonempty'' emeasure_join nn_integral_distr measurable_emeasure_subprob_algebra)

lemma nn_integral_bind:
  assumes f: "f \<in> borel_measurable B"
  assumes N: "N \<in> measurable M (subprob_algebra B)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(M \<guillemotright>= N)) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f y \<partial>N x \<partial>M)"
proof cases
  assume M: "space M \<noteq> {}" show ?thesis
    unfolding bind_nonempty''[OF N M] nn_integral_join[OF f sets_distr]
    by (rule nn_integral_distr[OF N nn_integral_measurable_subprob_algebra[OF f]])
qed (simp add: bind_empty space_empty[of M] nn_integral_count_space)

lemma AE_bind:
  assumes P[measurable]: "Measurable.pred B P"
  assumes N[measurable]: "N \<in> measurable M (subprob_algebra B)"
  shows "(AE x in M \<guillemotright>= N. P x) \<longleftrightarrow> (AE x in M. AE y in N x. P y)"
proof cases
  assume M: "space M = {}" show ?thesis
    unfolding bind_empty[OF M] unfolding space_empty[OF M] by (simp add: AE_count_space)
next
  assume M: "space M \<noteq> {}"
  note sets_kernel[OF N, simp]
  have *: "(\<integral>\<^sup>+x. indicator {x. \<not> P x} x \<partial>(M \<guillemotright>= N)) = (\<integral>\<^sup>+x. indicator {x\<in>space B. \<not> P x} x \<partial>(M \<guillemotright>= N))"
    by (intro nn_integral_cong) (simp add: space_bind[OF _ M] split: split_indicator)

  have "(AE x in M \<guillemotright>= N. P x) \<longleftrightarrow> (\<integral>\<^sup>+ x. integral\<^sup>N (N x) (indicator {x \<in> space B. \<not> P x}) \<partial>M) = 0"
    by (simp add: AE_iff_nn_integral sets_bind[OF _ M] space_bind[OF _ M] * nn_integral_bind[where B=B]
             del: nn_integral_indicator)
  also have "\<dots> = (AE x in M. AE y in N x. P y)"
    apply (subst nn_integral_0_iff_AE)
    apply (rule measurable_compose[OF N nn_integral_measurable_subprob_algebra])
    apply measurable
    apply (intro eventually_subst AE_I2)
    apply (auto simp add: emeasure_le_0_iff subprob_measurableD(1)[OF N]
                intro!: AE_iff_measurable[symmetric])
    done
  finally show ?thesis .
qed

lemma measurable_bind':
  assumes M1: "f \<in> measurable M (subprob_algebra N)" and
          M2: "split g \<in> measurable (M \<Otimes>\<^sub>M N) (subprob_algebra R)"
  shows "(\<lambda>x. bind (f x) (g x)) \<in> measurable M (subprob_algebra R)"
proof (subst measurable_cong)
  fix x assume x_in_M: "x \<in> space M"
  with assms have "space (f x) \<noteq> {}" 
      by (blast dest: subprob_space_kernel subprob_space.subprob_not_empty)
  moreover from M2 x_in_M have "g x \<in> measurable (f x) (subprob_algebra R)"
      by (subst measurable_cong_sets[OF sets_kernel[OF M1 x_in_M] refl])
         (auto dest: measurable_Pair2)
  ultimately show "bind (f x) (g x) = join (distr (f x) (subprob_algebra R) (g x))" 
      by (simp_all add: bind_nonempty'')
next
  show "(\<lambda>w. join (distr (f w) (subprob_algebra R) (g w))) \<in> measurable M (subprob_algebra R)"
    apply (rule measurable_compose[OF _ measurable_join])
    apply (rule measurable_distr2[OF M2 M1])
    done
qed

lemma measurable_bind[measurable (raw)]:
  assumes M1: "f \<in> measurable M (subprob_algebra N)" and
          M2: "(\<lambda>x. g (fst x) (snd x)) \<in> measurable (M \<Otimes>\<^sub>M N) (subprob_algebra R)"
  shows "(\<lambda>x. bind (f x) (g x)) \<in> measurable M (subprob_algebra R)"
  using assms by (auto intro: measurable_bind' simp: measurable_split_conv)

lemma measurable_bind2:
  assumes "f \<in> measurable M (subprob_algebra N)" and "g \<in> measurable N (subprob_algebra R)"
  shows "(\<lambda>x. bind (f x) g) \<in> measurable M (subprob_algebra R)"
    using assms by (intro measurable_bind' measurable_const) auto

lemma subprob_space_bind:
  assumes "subprob_space M" "f \<in> measurable M (subprob_algebra N)"
  shows "subprob_space (M \<guillemotright>= f)"
proof (rule subprob_space_kernel[of "\<lambda>x. x \<guillemotright>= f"])
  show "(\<lambda>x. x \<guillemotright>= f) \<in> measurable (subprob_algebra M) (subprob_algebra N)"
    by (rule measurable_bind, rule measurable_ident_sets, rule refl, 
        rule measurable_compose[OF measurable_snd assms(2)])
  from assms(1) show "M \<in> space (subprob_algebra M)"
    by (simp add: space_subprob_algebra)
qed

lemma (in prob_space) prob_space_bind: 
  assumes ae: "AE x in M. prob_space (N x)"
    and N[measurable]: "N \<in> measurable M (subprob_algebra S)"
  shows "prob_space (M \<guillemotright>= N)"
proof
  have "emeasure (M \<guillemotright>= N) (space (M \<guillemotright>= N)) = (\<integral>\<^sup>+x. emeasure (N x) (space (N x)) \<partial>M)"
    by (subst emeasure_bind[where N=S])
       (auto simp: not_empty space_bind[OF sets_kernel] subprob_measurableD[OF N] intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+x. 1 \<partial>M)"
    using ae by (intro nn_integral_cong_AE, eventually_elim) (rule prob_space.emeasure_space_1)
  finally show "emeasure (M \<guillemotright>= N) (space (M \<guillemotright>= N)) = 1"
    by (simp add: emeasure_space_1)
qed

lemma (in subprob_space) bind_in_space:
  "A \<in> measurable M (subprob_algebra N) \<Longrightarrow> (M \<guillemotright>= A) \<in> space (subprob_algebra N)"
  by (auto simp add: space_subprob_algebra subprob_not_empty sets_kernel intro!: subprob_space_bind)
     unfold_locales

lemma (in subprob_space) measure_bind:
  assumes f: "f \<in> measurable M (subprob_algebra N)" and X: "X \<in> sets N"
  shows "measure (M \<guillemotright>= f) X = \<integral>x. measure (f x) X \<partial>M"
proof -
  interpret Mf: subprob_space "M \<guillemotright>= f"
    by (rule subprob_space_bind[OF _ f]) unfold_locales

  { fix x assume "x \<in> space M"
    from f[THEN measurable_space, OF this] interpret subprob_space "f x"
      by (simp add: space_subprob_algebra)
    have "emeasure (f x) X = ereal (measure (f x) X)" "measure (f x) X \<le> 1"
      by (auto simp: emeasure_eq_measure subprob_measure_le_1) }
  note this[simp]

  have "emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. emeasure (f x) X \<partial>M"
    using subprob_not_empty f X by (rule emeasure_bind)
  also have "\<dots> = \<integral>\<^sup>+x. ereal (measure (f x) X) \<partial>M"
    by (intro nn_integral_cong) simp
  also have "\<dots> = \<integral>x. measure (f x) X \<partial>M"
    by (intro nn_integral_eq_integral integrable_const_bound[where B=1]
              measure_measurable_subprob_algebra2[OF _ f] pair_measureI X)
       (auto simp: measure_nonneg)
  finally show ?thesis
    by (simp add: Mf.emeasure_eq_measure)
qed

lemma emeasure_bind_const: 
    "space M \<noteq> {} \<Longrightarrow> X \<in> sets N \<Longrightarrow> subprob_space N \<Longrightarrow> 
         emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)"
  by (simp add: bind_nonempty emeasure_join nn_integral_distr 
                space_subprob_algebra measurable_emeasure_subprob_algebra emeasure_nonneg)

lemma emeasure_bind_const':
  assumes "subprob_space M" "subprob_space N"
  shows "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)"
using assms
proof (case_tac "X \<in> sets N")
  fix X assume "X \<in> sets N"
  thus "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)" using assms
      by (subst emeasure_bind_const) 
         (simp_all add: subprob_space.subprob_not_empty subprob_space.emeasure_space_le_1)
next
  fix X assume "X \<notin> sets N"
  with assms show "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)"
      by (simp add: sets_bind[of _ _ N] subprob_space.subprob_not_empty
                    space_subprob_algebra emeasure_notin_sets)
qed

lemma emeasure_bind_const_prob_space:
  assumes "prob_space M" "subprob_space N"
  shows "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X"
  using assms by (simp add: emeasure_bind_const' prob_space_imp_subprob_space 
                            prob_space.emeasure_space_1)

lemma bind_return: 
  assumes "f \<in> measurable M (subprob_algebra N)" and "x \<in> space M"
  shows "bind (return M x) f = f x"
  using sets_kernel[OF assms] assms
  by (simp_all add: distr_return join_return subprob_space_kernel bind_nonempty'
               cong: subprob_algebra_cong)

lemma bind_return':
  shows "bind M (return M) = M"
  by (cases "space M = {}")
     (simp_all add: bind_empty space_empty[symmetric] bind_nonempty join_return' 
               cong: subprob_algebra_cong)

lemma distr_bind:
  assumes N: "N \<in> measurable M (subprob_algebra K)" "space M \<noteq> {}"
  assumes f: "f \<in> measurable K R"
  shows "distr (M \<guillemotright>= N) R f = (M \<guillemotright>= (\<lambda>x. distr (N x) R f))"
  unfolding bind_nonempty''[OF N]
  apply (subst bind_nonempty''[OF measurable_compose[OF N(1) measurable_distr] N(2)])
  apply (rule f)
  apply (simp add: join_distr_distr[OF _ f, symmetric])
  apply (subst distr_distr[OF measurable_distr, OF f N(1)])
  apply (simp add: comp_def)
  done

lemma bind_distr:
  assumes f[measurable]: "f \<in> measurable M X"
  assumes N[measurable]: "N \<in> measurable X (subprob_algebra K)" and "space M \<noteq> {}"
  shows "(distr M X f \<guillemotright>= N) = (M \<guillemotright>= (\<lambda>x. N (f x)))"
proof -
  have "space X \<noteq> {}" "space M \<noteq> {}"
    using `space M \<noteq> {}` f[THEN measurable_space] by auto
  then show ?thesis
    by (simp add: bind_nonempty''[where N=K] distr_distr comp_def)
qed

lemma bind_count_space_singleton:
  assumes "subprob_space (f x)"
  shows "count_space {x} \<guillemotright>= f = f x"
proof-
  have A: "\<And>A. A \<subseteq> {x} \<Longrightarrow> A = {} \<or> A = {x}" by auto
  have "count_space {x} = return (count_space {x}) x"
    by (intro measure_eqI) (auto dest: A)
  also have "... \<guillemotright>= f = f x"
    by (subst bind_return[of _ _ "f x"]) (auto simp: space_subprob_algebra assms)
  finally show ?thesis .
qed

lemma restrict_space_bind:
  assumes N: "N \<in> measurable M (subprob_algebra K)"
  assumes "space M \<noteq> {}"
  assumes X[simp]: "X \<in> sets K" "X \<noteq> {}"
  shows "restrict_space (bind M N) X = bind M (\<lambda>x. restrict_space (N x) X)"
proof (rule measure_eqI)
  note N_sets = sets_bind[OF sets_kernel[OF N] assms(2), simp]
  note N_space = sets_eq_imp_space_eq[OF N_sets, simp]
  show "sets (restrict_space (bind M N) X) = sets (bind M (\<lambda>x. restrict_space (N x) X))"
    by (simp add: sets_restrict_space assms(2) sets_bind[OF sets_kernel[OF restrict_space_measurable[OF assms(4,3,1)]]])
  fix A assume "A \<in> sets (restrict_space (M \<guillemotright>= N) X)"
  with X have "A \<in> sets K" "A \<subseteq> X"
    by (auto simp: sets_restrict_space)
  then show "emeasure (restrict_space (M \<guillemotright>= N) X) A = emeasure (M \<guillemotright>= (\<lambda>x. restrict_space (N x) X)) A"
    using assms
    apply (subst emeasure_restrict_space)
    apply (simp_all add: emeasure_bind[OF assms(2,1)])
    apply (subst emeasure_bind[OF _ restrict_space_measurable[OF _ _ N]])
    apply (auto simp: sets_restrict_space emeasure_restrict_space space_subprob_algebra
                intro!: nn_integral_cong dest!: measurable_space)
    done
qed

lemma bind_const': "\<lbrakk>prob_space M; subprob_space N\<rbrakk> \<Longrightarrow> M \<guillemotright>= (\<lambda>x. N) = N"
  by (intro measure_eqI) 
     (simp_all add: space_subprob_algebra prob_space.not_empty emeasure_bind_const_prob_space)

lemma bind_return_distr: 
    "space M \<noteq> {} \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> bind M (return N \<circ> f) = distr M N f"
  apply (simp add: bind_nonempty)
  apply (subst subprob_algebra_cong)
  apply (rule sets_return)
  apply (subst distr_distr[symmetric])
  apply (auto intro!: return_measurable simp: distr_distr[symmetric] join_return')
  done

lemma bind_assoc:
  fixes f :: "'a \<Rightarrow> 'b measure" and g :: "'b \<Rightarrow> 'c measure"
  assumes M1: "f \<in> measurable M (subprob_algebra N)" and M2: "g \<in> measurable N (subprob_algebra R)"
  shows "bind (bind M f) g = bind M (\<lambda>x. bind (f x) g)"
proof (cases "space M = {}")
  assume [simp]: "space M \<noteq> {}"
  from assms have [simp]: "space N \<noteq> {}" "space R \<noteq> {}"
      by (auto simp: measurable_empty_iff space_subprob_algebra_empty_iff)
  from assms have sets_fx[simp]: "\<And>x. x \<in> space M \<Longrightarrow> sets (f x) = sets N"
      by (simp add: sets_kernel)
  have ex_in: "\<And>A. A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A" by blast
  note sets_some[simp] = sets_kernel[OF M1 someI_ex[OF ex_in[OF `space M \<noteq> {}`]]]
                         sets_kernel[OF M2 someI_ex[OF ex_in[OF `space N \<noteq> {}`]]]
  note space_some[simp] = sets_eq_imp_space_eq[OF this(1)] sets_eq_imp_space_eq[OF this(2)]

  have "bind M (\<lambda>x. bind (f x) g) = 
        join (distr M (subprob_algebra R) (join \<circ> (\<lambda>x. (distr x (subprob_algebra R) g)) \<circ> f))"
    by (simp add: sets_eq_imp_space_eq[OF sets_fx] bind_nonempty o_def
             cong: subprob_algebra_cong distr_cong)
  also have "distr M (subprob_algebra R) (join \<circ> (\<lambda>x. (distr x (subprob_algebra R) g)) \<circ> f) =
             distr (distr (distr M (subprob_algebra N) f)
                          (subprob_algebra (subprob_algebra R))
                          (\<lambda>x. distr x (subprob_algebra R) g)) 
                   (subprob_algebra R) join"
      apply (subst distr_distr, 
             (blast intro: measurable_comp measurable_distr measurable_join M1 M2)+)+
      apply (simp add: o_assoc)
      done
  also have "join ... = bind (bind M f) g"
      by (simp add: join_assoc join_distr_distr M2 bind_nonempty cong: subprob_algebra_cong)
  finally show ?thesis ..
qed (simp add: bind_empty)

lemma double_bind_assoc:
  assumes Mg: "g \<in> measurable N (subprob_algebra N')"
  assumes Mf: "f \<in> measurable M (subprob_algebra M')"
  assumes Mh: "split h \<in> measurable (M \<Otimes>\<^sub>M M') N"
  shows "do {x \<leftarrow> M; y \<leftarrow> f x; g (h x y)} = do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g"
proof-
  have "do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g = 
            do {x \<leftarrow> M; do {y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g}"
    using Mh by (auto intro!: bind_assoc measurable_bind'[OF Mf] Mf Mg
                      measurable_compose[OF _ return_measurable] simp: measurable_split_conv)
  also from Mh have "\<And>x. x \<in> space M \<Longrightarrow> h x \<in> measurable M' N" by measurable
  hence "do {x \<leftarrow> M; do {y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g} = 
            do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y) \<guillemotright>= g}"
    apply (intro ballI bind_cong bind_assoc)
    apply (subst measurable_cong_sets[OF sets_kernel[OF Mf] refl], simp)
    apply (rule measurable_compose[OF _ return_measurable], auto intro: Mg)
    done
  also have "\<And>x. x \<in> space M \<Longrightarrow> space (f x) = space M'"
    by (intro sets_eq_imp_space_eq sets_kernel[OF Mf])
  with measurable_space[OF Mh] 
    have "do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y) \<guillemotright>= g} = do {x \<leftarrow> M; y \<leftarrow> f x; g (h x y)}"
    by (intro ballI bind_cong bind_return[OF Mg]) (auto simp: space_pair_measure)
  finally show ?thesis ..
qed

lemma (in prob_space) M_in_subprob[measurable (raw)]: "M \<in> space (subprob_algebra M)"
  by (simp add: space_subprob_algebra) unfold_locales

lemma (in pair_prob_space) pair_measure_eq_bind:
  "(M1 \<Otimes>\<^sub>M M2) = (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y))))"
proof (rule measure_eqI)
  have ps_M2: "prob_space M2" by unfold_locales
  note return_measurable[measurable]
  show "sets (M1 \<Otimes>\<^sub>M M2) = sets (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y))))"
    by (simp_all add: M1.not_empty M2.not_empty)
  fix A assume [measurable]: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  show "emeasure (M1 \<Otimes>\<^sub>M M2) A = emeasure (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y)))) A"
    by (auto simp: M2.emeasure_pair_measure M1.not_empty M2.not_empty emeasure_bind[where N="M1 \<Otimes>\<^sub>M M2"]
             intro!: nn_integral_cong)
qed

lemma (in pair_prob_space) bind_rotate:
  assumes C[measurable]: "(\<lambda>(x, y). C x y) \<in> measurable (M1 \<Otimes>\<^sub>M M2) (subprob_algebra N)"
  shows "(M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. C x y))) = (M2 \<guillemotright>= (\<lambda>y. M1 \<guillemotright>= (\<lambda>x. C x y)))"
proof - 
  interpret swap: pair_prob_space M2 M1 by unfold_locales
  note measurable_bind[where N="M2", measurable]
  note measurable_bind[where N="M1", measurable]
  have [simp]: "M1 \<in> space (subprob_algebra M1)" "M2 \<in> space (subprob_algebra M2)"
    by (auto simp: space_subprob_algebra) unfold_locales
  have "(M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. C x y))) = 
    (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y)))) \<guillemotright>= (\<lambda>(x, y). C x y)"
    by (auto intro!: bind_cong simp: bind_return[where N=N] space_pair_measure bind_assoc[where N="M1 \<Otimes>\<^sub>M M2" and R=N])
  also have "\<dots> = (distr (M2 \<Otimes>\<^sub>M M1) (M1 \<Otimes>\<^sub>M M2) (\<lambda>(x, y). (y, x))) \<guillemotright>= (\<lambda>(x, y). C x y)"
    unfolding pair_measure_eq_bind[symmetric] distr_pair_swap[symmetric] ..
  also have "\<dots> = (M2 \<guillemotright>= (\<lambda>x. M1 \<guillemotright>= (\<lambda>y. return (M2 \<Otimes>\<^sub>M M1) (x, y)))) \<guillemotright>= (\<lambda>(y, x). C x y)"
    unfolding swap.pair_measure_eq_bind[symmetric]
    by (auto simp add: space_pair_measure M1.not_empty M2.not_empty bind_distr[OF _ C] intro!: bind_cong)
  also have "\<dots> = (M2 \<guillemotright>= (\<lambda>y. M1 \<guillemotright>= (\<lambda>x. C x y)))"
    by (auto intro!: bind_cong simp: bind_return[where N=N] space_pair_measure bind_assoc[where N="M2 \<Otimes>\<^sub>M M1" and R=N])
  finally show ?thesis .
qed

section {* Measures form a $\omega$-chain complete partial order *}

definition SUP_measure :: "(nat \<Rightarrow> 'a measure) \<Rightarrow> 'a measure" where
  "SUP_measure M = measure_of (\<Union>i. space (M i)) (\<Union>i. sets (M i)) (\<lambda>A. SUP i. emeasure (M i) A)"

lemma
  assumes const: "\<And>i j. sets (M i) = sets (M j)"
  shows space_SUP_measure: "space (SUP_measure M) = space (M i)" (is ?sp)
    and sets_SUP_measure: "sets (SUP_measure M) = sets (M i)" (is ?st)
proof -
  have "(\<Union>i. sets (M i)) = sets (M i)"
    using const by auto
  moreover have "(\<Union>i. space (M i)) = space (M i)"
    using const[THEN sets_eq_imp_space_eq] by auto
  moreover have "\<And>i. sets (M i) \<subseteq> Pow (space (M i))"
    by (auto dest: sets.sets_into_space)
  ultimately show ?sp ?st
    by (simp_all add: SUP_measure_def)
qed

lemma emeasure_SUP_measure:
  assumes const: "\<And>i j. sets (M i) = sets (M j)"
    and mono: "mono (\<lambda>i. emeasure (M i))"
  shows "emeasure (SUP_measure M) A = (SUP i. emeasure (M i) A)"
proof cases
  assume "A \<in> sets (SUP_measure M)"
  show ?thesis
  proof (rule emeasure_measure_of[OF SUP_measure_def])
    show "countably_additive (sets (SUP_measure M)) (\<lambda>A. SUP i. emeasure (M i) A)"
    proof (rule countably_additiveI)
      fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets (SUP_measure M)"
      then have "\<And>i j. A i \<in> sets (M j)"
        using sets_SUP_measure[of M, OF const] by simp
      moreover assume "disjoint_family A"
      ultimately show "(\<Sum>i. SUP ia. emeasure (M ia) (A i)) = (SUP i. emeasure (M i) (\<Union>i. A i))"
        using mono by (subst suminf_SUP_eq) (auto simp: mono_def le_fun_def intro!: SUP_cong suminf_emeasure)
    qed
    show "positive (sets (SUP_measure M)) (\<lambda>A. SUP i. emeasure (M i) A)"
      by (auto simp: positive_def intro: SUP_upper2)
    show "(\<Union>i. sets (M i)) \<subseteq> Pow (\<Union>i. space (M i))"
      using sets.sets_into_space by auto
  qed fact
next
  assume "A \<notin> sets (SUP_measure M)"
  with sets_SUP_measure[of M, OF const] show ?thesis
    by (simp add: emeasure_notin_sets)
qed

lemma bind_return'': "sets M = sets N \<Longrightarrow> M \<guillemotright>= return N = M"
   by (cases "space M = {}")
      (simp_all add: bind_empty space_empty[symmetric] bind_nonempty join_return'
                cong: subprob_algebra_cong)

lemma (in prob_space) distr_const[simp]:
  "c \<in> space N \<Longrightarrow> distr M N (\<lambda>x. c) = return N c"
  by (rule measure_eqI) (auto simp: emeasure_distr emeasure_space_1)

lemma return_count_space_eq_density:
    "return (count_space M) x = density (count_space M) (indicator {x})"
  by (rule measure_eqI) 
     (auto simp: indicator_inter_arith_ereal emeasure_density split: split_indicator)

end
