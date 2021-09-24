(*  Title:      HOL/Probability/Probability_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section \<open>Probability measure\<close>

theory Probability_Measure
  imports "HOL-Analysis.Analysis"
begin

locale prob_space = finite_measure +
  assumes emeasure_space_1: "emeasure M (space M) = 1"

lemma prob_spaceI[Pure.intro!]:
  assumes *: "emeasure M (space M) = 1"
  shows "prob_space M"
proof -
  interpret finite_measure M
  proof
    show "emeasure M (space M) \<noteq> \<infinity>" using * by simp
  qed
  show "prob_space M" by standard fact
qed

lemma prob_space_imp_sigma_finite: "prob_space M \<Longrightarrow> sigma_finite_measure M"
  unfolding prob_space_def finite_measure_def by simp

abbreviation (in prob_space) "events \<equiv> sets M"
abbreviation (in prob_space) "prob \<equiv> measure M"
abbreviation (in prob_space) "random_variable M' X \<equiv> X \<in> measurable M M'"
abbreviation (in prob_space) "expectation \<equiv> integral\<^sup>L M"
abbreviation (in prob_space) "variance X \<equiv> integral\<^sup>L M (\<lambda>x. (X x - expectation X)\<^sup>2)"

lemma (in prob_space) finite_measure [simp]: "finite_measure M"
  by unfold_locales

lemma (in prob_space) prob_space_distr:
  assumes f: "f \<in> measurable M M'" shows "prob_space (distr M M' f)"
proof (rule prob_spaceI)
  have "f -` space M' \<inter> space M = space M" using f by (auto dest: measurable_space)
  with f show "emeasure (distr M M' f) (space (distr M M' f)) = 1"
    by (auto simp: emeasure_distr emeasure_space_1)
qed

lemma prob_space_distrD:
  assumes f: "f \<in> measurable M N" and M: "prob_space (distr M N f)" shows "prob_space M"
proof
  interpret M: prob_space "distr M N f" by fact
  have "f -` space N \<inter> space M = space M"
    using f[THEN measurable_space] by auto
  then show "emeasure M (space M) = 1"
    using M.emeasure_space_1 by (simp add: emeasure_distr[OF f])
qed

lemma (in prob_space) prob_space: "prob (space M) = 1"
  using emeasure_space_1 unfolding measure_def by (simp add: one_ennreal.rep_eq)

lemma (in prob_space) prob_le_1[simp, intro]: "prob A \<le> 1"
  using bounded_measure[of A] by (simp add: prob_space)

lemma (in prob_space) not_empty: "space M \<noteq> {}"
  using prob_space by auto

lemma (in prob_space) emeasure_eq_1_AE:
  "S \<in> sets M \<Longrightarrow> AE x in M. x \<in> S \<Longrightarrow> emeasure M S = 1"
  by (subst emeasure_eq_AE[where B="space M"]) (auto simp: emeasure_space_1)

lemma (in prob_space) emeasure_le_1: "emeasure M S \<le> 1"
  unfolding ennreal_1[symmetric] emeasure_eq_measure by (subst ennreal_le_iff) auto

lemma (in prob_space) emeasure_ge_1_iff: "emeasure M A \<ge> 1 \<longleftrightarrow> emeasure M A = 1"
  by (rule iffI, intro antisym emeasure_le_1) simp_all

lemma (in prob_space) AE_iff_emeasure_eq_1:
  assumes [measurable]: "Measurable.pred M P"
  shows "(AE x in M. P x) \<longleftrightarrow> emeasure M {x\<in>space M. P x} = 1"
proof -
  have *: "{x \<in> space M. \<not> P x} = space M - {x\<in>space M. P x}"
    by auto
  show ?thesis
    by (auto simp add: ennreal_minus_eq_0 * emeasure_compl emeasure_space_1 AE_iff_measurable[OF _ refl]
             intro: antisym emeasure_le_1)
qed

lemma (in prob_space) measure_le_1: "emeasure M X \<le> 1"
  using emeasure_space[of M X] by (simp add: emeasure_space_1)

lemma (in prob_space) measure_ge_1_iff: "measure M A \<ge> 1 \<longleftrightarrow> measure M A = 1"
  by (auto intro!: antisym)

lemma (in prob_space) AE_I_eq_1:
  assumes "emeasure M {x\<in>space M. P x} = 1" "{x\<in>space M. P x} \<in> sets M"
  shows "AE x in M. P x"
proof (rule AE_I)
  show "emeasure M (space M - {x \<in> space M. P x}) = 0"
    using assms emeasure_space_1 by (simp add: emeasure_compl)
qed (insert assms, auto)

lemma prob_space_restrict_space:
  "S \<in> sets M \<Longrightarrow> emeasure M S = 1 \<Longrightarrow> prob_space (restrict_space M S)"
  by (intro prob_spaceI)
     (simp add: emeasure_restrict_space space_restrict_space)

lemma (in prob_space) prob_compl:
  assumes A: "A \<in> events"
  shows "prob (space M - A) = 1 - prob A"
  using finite_measure_compl[OF A] by (simp add: prob_space)

lemma (in prob_space) AE_in_set_eq_1:
  assumes A[measurable]: "A \<in> events" shows "(AE x in M. x \<in> A) \<longleftrightarrow> prob A = 1"
proof -
  have *: "{x\<in>space M. x \<in> A} = A"
    using A[THEN sets.sets_into_space] by auto
  show ?thesis
    by (subst AE_iff_emeasure_eq_1) (auto simp: emeasure_eq_measure *)
qed

lemma (in prob_space) AE_False: "(AE x in M. False) \<longleftrightarrow> False"
proof
  assume "AE x in M. False"
  then have "AE x in M. x \<in> {}" by simp
  then show False
    by (subst (asm) AE_in_set_eq_1) auto
qed simp

lemma (in prob_space) AE_prob_1:
  assumes "prob A = 1" shows "AE x in M. x \<in> A"
proof -
  from \<open>prob A = 1\<close> have "A \<in> events"
    by (metis measure_notin_sets zero_neq_one)
  with AE_in_set_eq_1 assms show ?thesis by simp
qed

lemma (in prob_space) AE_const[simp]: "(AE x in M. P) \<longleftrightarrow> P"
  by (cases P) (auto simp: AE_False)

lemma (in prob_space) ae_filter_bot: "ae_filter M \<noteq> bot"
  by (simp add: trivial_limit_def)

lemma (in prob_space) AE_contr:
  assumes ae: "AE \<omega> in M. P \<omega>" "AE \<omega> in M. \<not> P \<omega>"
  shows False
proof -
  from ae have "AE \<omega> in M. False" by eventually_elim auto
  then show False by auto
qed

lemma (in prob_space) integral_ge_const:
  fixes c :: real
  shows "integrable M f \<Longrightarrow> (AE x in M. c \<le> f x) \<Longrightarrow> c \<le> (\<integral>x. f x \<partial>M)"
  using integral_mono_AE[of M "\<lambda>x. c" f] prob_space by simp

lemma (in prob_space) integral_le_const:
  fixes c :: real
  shows "integrable M f \<Longrightarrow> (AE x in M. f x \<le> c) \<Longrightarrow> (\<integral>x. f x \<partial>M) \<le> c"
  using integral_mono_AE[of M f "\<lambda>x. c"] prob_space by simp

lemma (in prob_space) nn_integral_ge_const:
  "(AE x in M. c \<le> f x) \<Longrightarrow> c \<le> (\<integral>\<^sup>+x. f x \<partial>M)"
  using nn_integral_mono_AE[of "\<lambda>x. c" f M] emeasure_space_1
  by (simp split: if_split_asm)

lemma (in prob_space) expectation_less:
  fixes X :: "_ \<Rightarrow> real"
  assumes [simp]: "integrable M X"
  assumes gt: "AE x in M. X x < b"
  shows "expectation X < b"
proof -
  have "expectation X < expectation (\<lambda>x. b)"
    using gt emeasure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) expectation_greater:
  fixes X :: "_ \<Rightarrow> real"
  assumes [simp]: "integrable M X"
  assumes gt: "AE x in M. a < X x"
  shows "a < expectation X"
proof -
  have "expectation (\<lambda>x. a) < expectation X"
    using gt emeasure_space_1
    by (intro integral_less_AE_space) auto
  then show ?thesis using prob_space by simp
qed

lemma (in prob_space) jensens_inequality:
  fixes q :: "real \<Rightarrow> real"
  assumes X: "integrable M X" "AE x in M. X x \<in> I"
  assumes I: "I = {a <..< b} \<or> I = {a <..} \<or> I = {..< b} \<or> I = UNIV"
  assumes q: "integrable M (\<lambda>x. q (X x))" "convex_on I q"
  shows "q (expectation X) \<le> expectation (\<lambda>x. q (X x))"
proof -
  let ?F = "\<lambda>x. Inf ((\<lambda>t. (q x - q t) / (x - t)) ` ({x<..} \<inter> I))"
  from X(2) AE_False have "I \<noteq> {}" by auto

  from I have "open I" by auto

  note I
  moreover
  { assume "I \<subseteq> {a <..}"
    with X have "a < expectation X"
      by (intro expectation_greater) auto }
  moreover
  { assume "I \<subseteq> {..< b}"
    with X have "expectation X < b"
      by (intro expectation_less) auto }
  ultimately have "expectation X \<in> I"
    by (elim disjE)  (auto simp: subset_eq)
  moreover
  { fix y assume y: "y \<in> I"
    with q(2) \<open>open I\<close> have "Sup ((\<lambda>x. q x + ?F x * (y - x)) ` I) = q y"
      by (auto intro!: cSup_eq_maximum convex_le_Inf_differential image_eqI [OF _ y] simp: interior_open) }
  ultimately have "q (expectation X) = Sup ((\<lambda>x. q x + ?F x * (expectation X - x)) ` I)"
    by simp
  also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
  proof (rule cSup_least)
    show "(\<lambda>x. q x + ?F x * (expectation X - x)) ` I \<noteq> {}"
      using \<open>I \<noteq> {}\<close> by auto
  next
    fix k assume "k \<in> (\<lambda>x. q x + ?F x * (expectation X - x)) ` I"
    then obtain x
      where x: "k = q x + (INF t\<in>{x<..} \<inter> I. (q x - q t) / (x - t)) * (expectation X - x)" "x \<in> I" ..
    have "q x + ?F x * (expectation X  - x) = expectation (\<lambda>w. q x + ?F x * (X w - x))"
      using prob_space by (simp add: X)
    also have "\<dots> \<le> expectation (\<lambda>w. q (X w))"
      using \<open>x \<in> I\<close> \<open>open I\<close> X(2)
      apply (intro integral_mono_AE Bochner_Integration.integrable_add Bochner_Integration.integrable_mult_right Bochner_Integration.integrable_diff
                integrable_const X q)
      apply (elim eventually_mono)
      apply (intro convex_le_Inf_differential)
      apply (auto simp: interior_open q)
      done
    finally show "k \<le> expectation (\<lambda>w. q (X w))" using x by auto
  qed
  finally show "q (expectation X) \<le> expectation (\<lambda>x. q (X x))" .
qed

subsection  \<open>Introduce binder for probability\<close>

syntax
  "_prob" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>('\<P>'((/_ in _./ _)'))\<close>)

translations
  "\<P>(x in M. P)" => "CONST measure M {x \<in> CONST space M. P}"

print_translation \<open>
  let
    fun to_pattern (Const (\<^const_syntax>\<open>Pair\<close>, _) $ l $ r) =
      Syntax.const \<^const_syntax>\<open>Pair\<close> :: to_pattern l @ to_pattern r
    | to_pattern (t as (Const (\<^syntax_const>\<open>_bound\<close>, _)) $ _) = [t]

    fun mk_pattern ((t, n) :: xs) = mk_patterns n xs |>> curry list_comb t
    and mk_patterns 0 xs = ([], xs)
    | mk_patterns n xs =
      let
        val (t, xs') = mk_pattern xs
        val (ts, xs'') = mk_patterns (n - 1) xs'
      in
        (t :: ts, xs'')
      end

    fun unnest_tuples
      (Const (\<^syntax_const>\<open>_pattern\<close>, _) $
        t1 $
        (t as (Const (\<^syntax_const>\<open>_pattern\<close>, _) $ _ $ _)))
      = let
        val (_ $ t2 $ t3) = unnest_tuples t
      in
        Syntax.const \<^syntax_const>\<open>_pattern\<close> $
          unnest_tuples t1 $
          (Syntax.const \<^syntax_const>\<open>_patterns\<close> $ t2 $ t3)
      end
    | unnest_tuples pat = pat

    fun tr' [sig_alg, Const (\<^const_syntax>\<open>Collect\<close>, _) $ t] =
      let
        val bound_dummyT = Const (\<^syntax_const>\<open>_bound\<close>, dummyT)

        fun go pattern elem
          (Const (\<^const_syntax>\<open>conj\<close>, _) $
            (Const (\<^const_syntax>\<open>Set.member\<close>, _) $ elem' $ (Const (\<^const_syntax>\<open>space\<close>, _) $ sig_alg')) $
            u)
          = let
              val _ = if sig_alg aconv sig_alg' andalso to_pattern elem' = rev elem then () else raise Match;
              val (pat, rest) = mk_pattern (rev pattern);
              val _ = case rest of [] => () | _ => raise Match
            in
              Syntax.const \<^syntax_const>\<open>_prob\<close> $ unnest_tuples pat $ sig_alg $ u
            end
        | go pattern elem (Abs abs) =
            let
              val (x as (_ $ tx), t) = Syntax_Trans.atomic_abs_tr' abs
            in
              go ((x, 0) :: pattern) (bound_dummyT $ tx :: elem) t
            end
        | go pattern elem (Const (\<^const_syntax>\<open>case_prod\<close>, _) $ t) =
            go
              ((Syntax.const \<^syntax_const>\<open>_pattern\<close>, 2) :: pattern)
              (Syntax.const \<^const_syntax>\<open>Pair\<close> :: elem)
              t
      in
        go [] [] t
      end
  in
    [(\<^const_syntax>\<open>Sigma_Algebra.measure\<close>, K tr')]
  end
\<close>

definition
  "cond_prob M P Q = \<P>(\<omega> in M. P \<omega> \<and> Q \<omega>) / \<P>(\<omega> in M. Q \<omega>)"

syntax
  "_conditional_prob" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>('\<P>'(_ in _. _ \<bar>/ _'))\<close>)

translations
  "\<P>(x in M. P \<bar> Q)" => "CONST cond_prob M (\<lambda>x. P) (\<lambda>x. Q)"

lemma (in prob_space) AE_E_prob:
  assumes ae: "AE x in M. P x"
  obtains S where "S \<subseteq> {x \<in> space M. P x}" "S \<in> events" "prob S = 1"
proof -
  from ae[THEN AE_E] obtain N
    where "{x \<in> space M. \<not> P x} \<subseteq> N" "emeasure M N = 0" "N \<in> events" by auto
  then show thesis
    by (intro that[of "space M - N"])
       (auto simp: prob_compl prob_space emeasure_eq_measure measure_nonneg)
qed

lemma (in prob_space) prob_neg: "{x\<in>space M. P x} \<in> events \<Longrightarrow> \<P>(x in M. \<not> P x) = 1 - \<P>(x in M. P x)"
  by (auto intro!: arg_cong[where f=prob] simp add: prob_compl[symmetric])

lemma (in prob_space) prob_eq_AE:
  "(AE x in M. P x \<longleftrightarrow> Q x) \<Longrightarrow> {x\<in>space M. P x} \<in> events \<Longrightarrow> {x\<in>space M. Q x} \<in> events \<Longrightarrow> \<P>(x in M. P x) = \<P>(x in M. Q x)"
  by (rule finite_measure_eq_AE) auto

lemma (in prob_space) prob_eq_0_AE:
  assumes not: "AE x in M. \<not> P x" shows "\<P>(x in M. P x) = 0"
proof cases
  assume "{x\<in>space M. P x} \<in> events"
  with not have "\<P>(x in M. P x) = \<P>(x in M. False)"
    by (intro prob_eq_AE) auto
  then show ?thesis by simp
qed (simp add: measure_notin_sets)

lemma (in prob_space) prob_Collect_eq_0:
  "{x \<in> space M. P x} \<in> sets M \<Longrightarrow> \<P>(x in M. P x) = 0 \<longleftrightarrow> (AE x in M. \<not> P x)"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. \<not> P x"] by (simp add: emeasure_eq_measure measure_nonneg)

lemma (in prob_space) prob_Collect_eq_1:
  "{x \<in> space M. P x} \<in> sets M \<Longrightarrow> \<P>(x in M. P x) = 1 \<longleftrightarrow> (AE x in M. P x)"
  using AE_in_set_eq_1[of "{x\<in>space M. P x}"] by simp

lemma (in prob_space) prob_eq_0:
  "A \<in> sets M \<Longrightarrow> prob A = 0 \<longleftrightarrow> (AE x in M. x \<notin> A)"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. x \<notin> A"]
  by (auto simp add: emeasure_eq_measure Int_def[symmetric] measure_nonneg)

lemma (in prob_space) prob_eq_1:
  "A \<in> sets M \<Longrightarrow> prob A = 1 \<longleftrightarrow> (AE x in M. x \<in> A)"
  using AE_in_set_eq_1[of A] by simp

lemma (in prob_space) prob_sums:
  assumes P: "\<And>n. {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x in M. (\<forall>n. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n. P n x))"
  shows "(\<lambda>n. \<P>(x in M. P n x)) sums \<P>(x in M. Q x)"
proof -
  from ae[THEN AE_E_prob] obtain S
    where S:
      "S \<subseteq> {x \<in> space M. (\<forall>n. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n. P n x))}"
      "S \<in> events"
      "prob S = 1"
    by auto
  then have disj: "disjoint_family (\<lambda>n. {x\<in>space M. P n x} \<inter> S)"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x in M. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. AE x in M. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<P>(x in M. Q x) = prob (\<Union>n. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  from ae_S have **:
    "\<And>n. \<P>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    unfolding * ** using S P disj
    by (intro finite_measure_UNION) auto
qed

lemma (in prob_space) prob_sum:
  assumes [simp, intro]: "finite I"
  assumes P: "\<And>n. n \<in> I \<Longrightarrow> {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x in M. (\<forall>n\<in>I. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n\<in>I. P n x))"
  shows "\<P>(x in M. Q x) = (\<Sum>n\<in>I. \<P>(x in M. P n x))"
proof -
  from ae[THEN AE_E_prob] obtain S
    where S:
      "S \<subseteq> {x \<in> space M. (\<forall>n\<in>I. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n. n \<in> I \<and> P n x))}"
      "S \<in> events"
      "prob S = 1"
    by auto
  then have disj: "disjoint_family_on (\<lambda>n. {x\<in>space M. P n x} \<inter> S) I"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x in M. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. n \<in> I \<Longrightarrow> AE x in M. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<P>(x in M. Q x) = prob (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) (auto intro!: sets.Int)
  from ae_S have **:
    "\<And>n. n \<in> I \<Longrightarrow> \<P>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    using S P disj
    by (auto simp add: * ** simp del: UN_simps intro!: finite_measure_finite_Union)
qed

lemma (in prob_space) prob_EX_countable:
  assumes sets: "\<And>i. i \<in> I \<Longrightarrow> {x\<in>space M. P i x} \<in> sets M" and I: "countable I"
  assumes disj: "AE x in M. \<forall>i\<in>I. \<forall>j\<in>I. P i x \<longrightarrow> P j x \<longrightarrow> i = j"
  shows "\<P>(x in M. \<exists>i\<in>I. P i x) = (\<integral>\<^sup>+i. \<P>(x in M. P i x) \<partial>count_space I)"
proof -
  let ?N= "\<lambda>x. \<exists>!i\<in>I. P i x"
  have "ennreal (\<P>(x in M. \<exists>i\<in>I. P i x)) = \<P>(x in M. (\<exists>i\<in>I. P i x \<and> ?N x))"
    unfolding ennreal_inj[OF measure_nonneg measure_nonneg]
  proof (rule prob_eq_AE)
    show "AE x in M. (\<exists>i\<in>I. P i x) = (\<exists>i\<in>I. P i x \<and> ?N x)"
      using disj by eventually_elim blast
  qed (auto intro!: sets.sets_Collect_countable_Ex' sets.sets_Collect_conj sets.sets_Collect_countable_Ex1' I sets)+
  also have "\<P>(x in M. (\<exists>i\<in>I. P i x \<and> ?N x)) = emeasure M (\<Union>i\<in>I. {x\<in>space M. P i x \<and> ?N x})"
    unfolding emeasure_eq_measure by (auto intro!: arg_cong[where f=prob] simp: measure_nonneg)
  also have "\<dots> = (\<integral>\<^sup>+i. emeasure M {x\<in>space M. P i x \<and> ?N x} \<partial>count_space I)"
    by (rule emeasure_UN_countable)
       (auto intro!: sets.sets_Collect_countable_Ex' sets.sets_Collect_conj sets.sets_Collect_countable_Ex1' I sets
             simp: disjoint_family_on_def)
  also have "\<dots> = (\<integral>\<^sup>+i. \<P>(x in M. P i x) \<partial>count_space I)"
    unfolding emeasure_eq_measure using disj
    by (intro nn_integral_cong ennreal_inj[THEN iffD2] prob_eq_AE)
       (auto intro!: sets.sets_Collect_countable_Ex' sets.sets_Collect_conj sets.sets_Collect_countable_Ex1' I sets measure_nonneg)+
  finally show ?thesis .
qed

lemma (in prob_space) cond_prob_eq_AE:
  assumes P: "AE x in M. Q x \<longrightarrow> P x \<longleftrightarrow> P' x" "{x\<in>space M. P x} \<in> events" "{x\<in>space M. P' x} \<in> events"
  assumes Q: "AE x in M. Q x \<longleftrightarrow> Q' x" "{x\<in>space M. Q x} \<in> events" "{x\<in>space M. Q' x} \<in> events"
  shows "cond_prob M P Q = cond_prob M P' Q'"
  using P Q
  by (auto simp: cond_prob_def intro!: arg_cong2[where f="(/)"] prob_eq_AE sets.sets_Collect_conj)


lemma (in prob_space) joint_distribution_Times_le_fst:
  "random_variable MX X \<Longrightarrow> random_variable MY Y \<Longrightarrow> A \<in> sets MX \<Longrightarrow> B \<in> sets MY
    \<Longrightarrow> emeasure (distr M (MX \<Otimes>\<^sub>M MY) (\<lambda>x. (X x, Y x))) (A \<times> B) \<le> emeasure (distr M MX X) A"
  by (auto simp: emeasure_distr measurable_pair_iff comp_def intro!: emeasure_mono measurable_sets)

lemma (in prob_space) joint_distribution_Times_le_snd:
  "random_variable MX X \<Longrightarrow> random_variable MY Y \<Longrightarrow> A \<in> sets MX \<Longrightarrow> B \<in> sets MY
    \<Longrightarrow> emeasure (distr M (MX \<Otimes>\<^sub>M MY) (\<lambda>x. (X x, Y x))) (A \<times> B) \<le> emeasure (distr M MY Y) B"
  by (auto simp: emeasure_distr measurable_pair_iff comp_def intro!: emeasure_mono measurable_sets)

lemma (in prob_space) variance_eq:
  fixes X :: "'a \<Rightarrow> real"
  assumes [simp]: "integrable M X"
  assumes [simp]: "integrable M (\<lambda>x. (X x)\<^sup>2)"
  shows "variance X = expectation (\<lambda>x. (X x)\<^sup>2) - (expectation X)\<^sup>2"
  by (simp add: field_simps prob_space power2_diff power2_eq_square[symmetric])

lemma (in prob_space) variance_positive: "0 \<le> variance (X::'a \<Rightarrow> real)"
  by (intro integral_nonneg_AE) (auto intro!: integral_nonneg_AE)

lemma (in prob_space) variance_mean_zero:
  "expectation X = 0 \<Longrightarrow> variance X = expectation (\<lambda>x. (X x)^2)"
  by simp

theorem%important (in prob_space) Chebyshev_inequality:
  assumes [measurable]: "random_variable borel f"
  assumes "integrable M (\<lambda>x. f x ^ 2)"
  defines "\<mu> \<equiv> expectation f"
  assumes "a > 0"
  shows "prob {x\<in>space M. \<bar>f x - \<mu>\<bar> \<ge> a} \<le> variance f / a\<^sup>2"
  unfolding \<mu>_def
proof (rule second_moment_method)
  have integrable: "integrable M f"
    using assms by (blast dest: square_integrable_imp_integrable)
  show "integrable M (\<lambda>x. (f x - expectation f)\<^sup>2)"
    using assms integrable unfolding power2_eq_square ring_distribs
    by (intro Bochner_Integration.integrable_diff) auto
qed (use assms in auto)

locale pair_prob_space = pair_sigma_finite M1 M2 + M1: prob_space M1 + M2: prob_space M2 for M1 M2

sublocale pair_prob_space \<subseteq> P?: prob_space "M1 \<Otimes>\<^sub>M M2"
proof
  show "emeasure (M1 \<Otimes>\<^sub>M M2) (space (M1 \<Otimes>\<^sub>M M2)) = 1"
    by (simp add: M2.emeasure_pair_measure_Times M1.emeasure_space_1 M2.emeasure_space_1 space_pair_measure)
qed

locale product_prob_space = product_sigma_finite M for M :: "'i \<Rightarrow> 'a measure" +
  fixes I :: "'i set"
  assumes prob_space: "\<And>i. prob_space (M i)"

sublocale product_prob_space \<subseteq> M?: prob_space "M i" for i
  by (rule prob_space)

locale finite_product_prob_space = finite_product_sigma_finite M I + product_prob_space M I for M I

sublocale finite_product_prob_space \<subseteq> prob_space "\<Pi>\<^sub>M i\<in>I. M i"
proof
  show "emeasure (\<Pi>\<^sub>M i\<in>I. M i) (space (\<Pi>\<^sub>M i\<in>I. M i)) = 1"
    by (simp add: measure_times M.emeasure_space_1 prod.neutral_const space_PiM)
qed

lemma (in finite_product_prob_space) prob_times:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> sets (M i)"
  shows "prob (\<Pi>\<^sub>E i\<in>I. X i) = (\<Prod>i\<in>I. M.prob i (X i))"
proof -
  have "ennreal (measure (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>E i\<in>I. X i)) = emeasure (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>E i\<in>I. X i)"
    using X by (simp add: emeasure_eq_measure)
  also have "\<dots> = (\<Prod>i\<in>I. emeasure (M i) (X i))"
    using measure_times X by simp
  also have "\<dots> = ennreal (\<Prod>i\<in>I. measure (M i) (X i))"
    using X by (simp add: M.emeasure_eq_measure prod_ennreal measure_nonneg)
  finally show ?thesis by (simp add: measure_nonneg prod_nonneg)
qed

lemma product_prob_spaceI:
  assumes "\<And>i. prob_space (M i)"
  shows   "product_prob_space M"
  unfolding product_prob_space_def product_prob_space_axioms_def product_sigma_finite_def
proof safe
  fix i
  interpret prob_space "M i"
    by (rule assms)
  show "sigma_finite_measure (M i)" "prob_space (M i)"
    by unfold_locales
qed

subsection \<open>Distributions\<close>

definition distributed :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> ennreal) \<Rightarrow> bool"
where
  "distributed M N X f \<longleftrightarrow>
  distr M N X = density N f \<and> f \<in> borel_measurable N \<and> X \<in> measurable M N"

lemma
  assumes "distributed M N X f"
  shows distributed_distr_eq_density: "distr M N X = density N f"
    and distributed_measurable: "X \<in> measurable M N"
    and distributed_borel_measurable: "f \<in> borel_measurable N"
  using assms by (simp_all add: distributed_def)

lemma
  assumes D: "distributed M N X f"
  shows distributed_measurable'[measurable_dest]:
      "g \<in> measurable L M \<Longrightarrow> (\<lambda>x. X (g x)) \<in> measurable L N"
    and distributed_borel_measurable'[measurable_dest]:
      "h \<in> measurable L N \<Longrightarrow> (\<lambda>x. f (h x)) \<in> borel_measurable L"
  using distributed_measurable[OF D] distributed_borel_measurable[OF D]
  by simp_all

lemma distributed_real_measurable:
  "(\<And>x. x \<in> space N \<Longrightarrow> 0 \<le> f x) \<Longrightarrow> distributed M N X (\<lambda>x. ennreal (f x)) \<Longrightarrow> f \<in> borel_measurable N"
  by (simp_all add: distributed_def)

lemma distributed_real_measurable':
  "(\<And>x. x \<in> space N \<Longrightarrow> 0 \<le> f x) \<Longrightarrow> distributed M N X (\<lambda>x. ennreal (f x)) \<Longrightarrow>
    h \<in> measurable L N \<Longrightarrow> (\<lambda>x. f (h x)) \<in> borel_measurable L"
  using distributed_real_measurable[measurable] by simp

lemma joint_distributed_measurable1:
  "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) f \<Longrightarrow> h1 \<in> measurable N M \<Longrightarrow> (\<lambda>x. X (h1 x)) \<in> measurable N S"
  by simp

lemma joint_distributed_measurable2:
  "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) f \<Longrightarrow> h2 \<in> measurable N M \<Longrightarrow> (\<lambda>x. Y (h2 x)) \<in> measurable N T"
  by simp

lemma distributed_count_space:
  assumes X: "distributed M (count_space A) X P" and a: "a \<in> A" and A: "finite A"
  shows "P a = emeasure M (X -` {a} \<inter> space M)"
proof -
  have "emeasure M (X -` {a} \<inter> space M) = emeasure (distr M (count_space A) X) {a}"
    using X a A by (simp add: emeasure_distr)
  also have "\<dots> = emeasure (density (count_space A) P) {a}"
    using X by (simp add: distributed_distr_eq_density)
  also have "\<dots> = (\<integral>\<^sup>+x. P a * indicator {a} x \<partial>count_space A)"
    using X a by (auto simp add: emeasure_density distributed_def indicator_def intro!: nn_integral_cong)
  also have "\<dots> = P a"
    using X a by (subst nn_integral_cmult_indicator) (auto simp: distributed_def one_ennreal_def[symmetric] AE_count_space)
  finally show ?thesis ..
qed

lemma distributed_cong_density:
  "(AE x in N. f x = g x) \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> f \<in> borel_measurable N \<Longrightarrow>
    distributed M N X f \<longleftrightarrow> distributed M N X g"
  by (auto simp: distributed_def intro!: density_cong)

lemma (in prob_space) distributed_imp_emeasure_nonzero:
  assumes X: "distributed M MX X Px"
  shows "emeasure MX {x \<in> space MX. Px x \<noteq> 0} \<noteq> 0"
proof
  note Px = distributed_borel_measurable[OF X]
  interpret X: prob_space "distr M MX X"
    using distributed_measurable[OF X] by (rule prob_space_distr)

  assume "emeasure MX {x \<in> space MX. Px x \<noteq> 0} = 0"
  with Px have "AE x in MX. Px x = 0"
    by (intro AE_I[OF subset_refl]) (auto simp: borel_measurable_ennreal_iff)
  moreover
  from X.emeasure_space_1 have "(\<integral>\<^sup>+x. Px x \<partial>MX) = 1"
    unfolding distributed_distr_eq_density[OF X] using Px
    by (subst (asm) emeasure_density)
       (auto simp: borel_measurable_ennreal_iff intro!: integral_cong cong: nn_integral_cong)
  ultimately show False
    by (simp add: nn_integral_cong_AE)
qed

lemma subdensity:
  assumes T: "T \<in> measurable P Q"
  assumes f: "distributed M P X f"
  assumes g: "distributed M Q Y g"
  assumes Y: "Y = T \<circ> X"
  shows "AE x in P. g (T x) = 0 \<longrightarrow> f x = 0"
proof -
  have "{x\<in>space Q. g x = 0} \<in> null_sets (distr M Q (T \<circ> X))"
    using g Y by (auto simp: null_sets_density_iff distributed_def)
  also have "distr M Q (T \<circ> X) = distr (distr M P X) Q T"
    using T f[THEN distributed_measurable] by (rule distr_distr[symmetric])
  finally have "T -` {x\<in>space Q. g x = 0} \<inter> space P \<in> null_sets (distr M P X)"
    using T by (subst (asm) null_sets_distr_iff) auto
  also have "T -` {x\<in>space Q. g x = 0} \<inter> space P = {x\<in>space P. g (T x) = 0}"
    using T by (auto dest: measurable_space)
  finally show ?thesis
    using f g by (auto simp add: null_sets_density_iff distributed_def)
qed

lemma subdensity_real:
  fixes g :: "'a \<Rightarrow> real" and f :: "'b \<Rightarrow> real"
  assumes T: "T \<in> measurable P Q"
  assumes f: "distributed M P X f"
  assumes g: "distributed M Q Y g"
  assumes Y: "Y = T \<circ> X"
  shows "(AE x in P. 0 \<le> g (T x)) \<Longrightarrow> (AE x in P. 0 \<le> f x) \<Longrightarrow> AE x in P. g (T x) = 0 \<longrightarrow> f x = 0"
  using subdensity[OF T, of M X "\<lambda>x. ennreal (f x)" Y "\<lambda>x. ennreal (g x)"] assms
  by auto

lemma distributed_emeasure:
  "distributed M N X f \<Longrightarrow> A \<in> sets N \<Longrightarrow> emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>N)"
  by (auto simp: distributed_distr_eq_density[symmetric] emeasure_density[symmetric] emeasure_distr)

lemma distributed_nn_integral:
  "distributed M N X f \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> (\<integral>\<^sup>+x. f x * g x \<partial>N) = (\<integral>\<^sup>+x. g (X x) \<partial>M)"
  by (auto simp: distributed_distr_eq_density[symmetric] nn_integral_density[symmetric] nn_integral_distr)

lemma distributed_integral:
  "distributed M N X f \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> (\<And>x. x \<in> space N \<Longrightarrow> 0 \<le> f x) \<Longrightarrow>
    (\<integral>x. f x * g x \<partial>N) = (\<integral>x. g (X x) \<partial>M)"
  supply distributed_real_measurable[measurable]
  by (auto simp: distributed_distr_eq_density[symmetric] integral_real_density[symmetric] integral_distr)

lemma distributed_transform_integral:
  assumes Px: "distributed M N X Px" "\<And>x. x \<in> space N \<Longrightarrow> 0 \<le> Px x"
  assumes "distributed M P Y Py" "\<And>x. x \<in> space P \<Longrightarrow> 0 \<le> Py x"
  assumes Y: "Y = T \<circ> X" and T: "T \<in> measurable N P" and f: "f \<in> borel_measurable P"
  shows "(\<integral>x. Py x * f x \<partial>P) = (\<integral>x. Px x * f (T x) \<partial>N)"
proof -
  have "(\<integral>x. Py x * f x \<partial>P) = (\<integral>x. f (Y x) \<partial>M)"
    by (rule distributed_integral) fact+
  also have "\<dots> = (\<integral>x. f (T (X x)) \<partial>M)"
    using Y by simp
  also have "\<dots> = (\<integral>x. Px x * f (T x) \<partial>N)"
    using measurable_comp[OF T f] Px by (intro distributed_integral[symmetric]) (auto simp: comp_def)
  finally show ?thesis .
qed

lemma (in prob_space) distributed_unique:
  assumes Px: "distributed M S X Px"
  assumes Py: "distributed M S X Py"
  shows "AE x in S. Px x = Py x"
proof -
  interpret X: prob_space "distr M S X"
    using Px by (intro prob_space_distr) simp
  have "sigma_finite_measure (distr M S X)" ..
  with sigma_finite_density_unique[of Px S Py ] Px Py
  show ?thesis
    by (auto simp: distributed_def)
qed

lemma (in prob_space) distributed_jointI:
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes X[measurable]: "X \<in> measurable M S" and Y[measurable]: "Y \<in> measurable M T"
  assumes [measurable]: "f \<in> borel_measurable (S \<Otimes>\<^sub>M T)" and f: "AE x in S \<Otimes>\<^sub>M T. 0 \<le> f x"
  assumes eq: "\<And>A B. A \<in> sets S \<Longrightarrow> B \<in> sets T \<Longrightarrow>
    emeasure M {x \<in> space M. X x \<in> A \<and> Y x \<in> B} = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x, y) * indicator B y \<partial>T) * indicator A x \<partial>S)"
  shows "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) f"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  from ST.sigma_finite_up_in_pair_measure_generator
  obtain F :: "nat \<Rightarrow> ('b \<times> 'c) set"
    where F: "range F \<subseteq> {A \<times> B |A B. A \<in> sets S \<and> B \<in> sets T} \<and> incseq F \<and>
      \<Union> (range F) = space S \<times> space T \<and> (\<forall>i. emeasure (S \<Otimes>\<^sub>M T) (F i) \<noteq> \<infinity>)" ..
  let ?E = "{a \<times> b |a b. a \<in> sets S \<and> b \<in> sets T}"
  let ?P = "S \<Otimes>\<^sub>M T"
  show "distr M ?P (\<lambda>x. (X x, Y x)) = density ?P f" (is "?L = ?R")
  proof (rule measure_eqI_generator_eq[OF Int_stable_pair_measure_generator[of S T]])
    show "?E \<subseteq> Pow (space ?P)"
      using sets.space_closed[of S] sets.space_closed[of T] by (auto simp: space_pair_measure)
    show "sets ?L = sigma_sets (space ?P) ?E"
      by (simp add: sets_pair_measure space_pair_measure)
    then show "sets ?R = sigma_sets (space ?P) ?E"
      by simp
  next
    interpret L: prob_space ?L
      by (rule prob_space_distr) (auto intro!: measurable_Pair)
    show "range F \<subseteq> ?E" "(\<Union>i. F i) = space ?P" "\<And>i. emeasure ?L (F i) \<noteq> \<infinity>"
      using F by (auto simp: space_pair_measure)
  next
    fix E assume "E \<in> ?E"
    then obtain A B where E[simp]: "E = A \<times> B"
      and A[measurable]: "A \<in> sets S" and B[measurable]: "B \<in> sets T" by auto
    have "emeasure ?L E = emeasure M {x \<in> space M. X x \<in> A \<and> Y x \<in> B}"
      by (auto intro!: arg_cong[where f="emeasure M"] simp add: emeasure_distr measurable_Pair)
    also have "\<dots> = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. (f (x, y) * indicator B y) * indicator A x \<partial>T) \<partial>S)"
      using f by (auto simp add: eq nn_integral_multc intro!: nn_integral_cong)
    also have "\<dots> = emeasure ?R E"
      by (auto simp add: emeasure_density T.nn_integral_fst[symmetric]
               intro!: nn_integral_cong split: split_indicator)
    finally show "emeasure ?L E = emeasure ?R E" .
  qed
qed (auto simp: f)

lemma (in prob_space) distributed_swap:
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "distributed M (T \<Otimes>\<^sub>M S) (\<lambda>x. (Y x, X x)) (\<lambda>(x, y). Pxy (y, x))"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  interpret TS: pair_sigma_finite T S ..

  note Pxy[measurable]
  show ?thesis
    apply (subst TS.distr_pair_swap)
    unfolding distributed_def
  proof safe
    let ?D = "distr (S \<Otimes>\<^sub>M T) (T \<Otimes>\<^sub>M S) (\<lambda>(x, y). (y, x))"
    show 1: "(\<lambda>(x, y). Pxy (y, x)) \<in> borel_measurable ?D"
      by auto
    show 2: "random_variable (distr (S \<Otimes>\<^sub>M T) (T \<Otimes>\<^sub>M S) (\<lambda>(x, y). (y, x))) (\<lambda>x. (Y x, X x))"
      using Pxy by auto
    { fix A assume A: "A \<in> sets (T \<Otimes>\<^sub>M S)"
      let ?B = "(\<lambda>(x, y). (y, x)) -` A \<inter> space (S \<Otimes>\<^sub>M T)"
      from sets.sets_into_space[OF A]
      have "emeasure M ((\<lambda>x. (Y x, X x)) -` A \<inter> space M) =
        emeasure M ((\<lambda>x. (X x, Y x)) -` ?B \<inter> space M)"
        by (auto intro!: arg_cong2[where f=emeasure] simp: space_pair_measure)
      also have "\<dots> = (\<integral>\<^sup>+ x. Pxy x * indicator ?B x \<partial>(S \<Otimes>\<^sub>M T))"
        using Pxy A by (intro distributed_emeasure) auto
      finally have "emeasure M ((\<lambda>x. (Y x, X x)) -` A \<inter> space M) =
        (\<integral>\<^sup>+ x. Pxy x * indicator A (snd x, fst x) \<partial>(S \<Otimes>\<^sub>M T))"
        by (auto intro!: nn_integral_cong split: split_indicator) }
    note * = this
    show "distr M ?D (\<lambda>x. (Y x, X x)) = density ?D (\<lambda>(x, y). Pxy (y, x))"
      apply (intro measure_eqI)
      apply (simp_all add: emeasure_distr[OF 2] emeasure_density[OF 1])
      apply (subst nn_integral_distr)
      apply (auto intro!: * simp: comp_def split_beta)
      done
  qed
qed

lemma (in prob_space) distr_marginal1:
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  defines "Px \<equiv> \<lambda>x. (\<integral>\<^sup>+z. Pxy (x, z) \<partial>T)"
  shows "distributed M S X Px"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  note Pxy[measurable]
  show X: "X \<in> measurable M S" by simp

  show borel: "Px \<in> borel_measurable S"
    by (auto intro!: T.nn_integral_fst simp: Px_def)

  interpret Pxy: prob_space "distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
    by (intro prob_space_distr) simp

  show "distr M S X = density S Px"
  proof (rule measure_eqI)
    fix A assume A: "A \<in> sets (distr M S X)"
    with X measurable_space[of Y M T]
    have "emeasure (distr M S X) A = emeasure (distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))) (A \<times> space T)"
      by (auto simp add: emeasure_distr intro!: arg_cong[where f="emeasure M"])
    also have "\<dots> = emeasure (density (S \<Otimes>\<^sub>M T) Pxy) (A \<times> space T)"
      using Pxy by (simp add: distributed_def)
    also have "\<dots> = \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. Pxy (x, y) * indicator (A \<times> space T) (x, y) \<partial>T \<partial>S"
      using A borel Pxy
      by (simp add: emeasure_density T.nn_integral_fst[symmetric])
    also have "\<dots> = \<integral>\<^sup>+ x. Px x * indicator A x \<partial>S"
    proof (rule nn_integral_cong)
      fix x assume "x \<in> space S"
      moreover have eq: "\<And>y. y \<in> space T \<Longrightarrow> indicator (A \<times> space T) (x, y) = indicator A x"
        by (auto simp: indicator_def)
      ultimately have "(\<integral>\<^sup>+ y. Pxy (x, y) * indicator (A \<times> space T) (x, y) \<partial>T) = (\<integral>\<^sup>+ y. Pxy (x, y) \<partial>T) * indicator A x"
        by (simp add: eq nn_integral_multc cong: nn_integral_cong)
      also have "(\<integral>\<^sup>+ y. Pxy (x, y) \<partial>T) = Px x"
        by (simp add: Px_def)
      finally show "(\<integral>\<^sup>+ y. Pxy (x, y) * indicator (A \<times> space T) (x, y) \<partial>T) = Px x * indicator A x" .
    qed
    finally show "emeasure (distr M S X) A = emeasure (density S Px) A"
      using A borel Pxy by (simp add: emeasure_density)
  qed simp
qed

lemma (in prob_space) distr_marginal2:
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "distributed M T Y (\<lambda>y. (\<integral>\<^sup>+x. Pxy (x, y) \<partial>S))"
  using distr_marginal1[OF T S distributed_swap[OF S T]] Pxy by simp

lemma (in prob_space) distributed_marginal_eq_joint1:
  assumes T: "sigma_finite_measure T"
  assumes S: "sigma_finite_measure S"
  assumes Px: "distributed M S X Px"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "AE x in S. Px x = (\<integral>\<^sup>+y. Pxy (x, y) \<partial>T)"
  using Px distr_marginal1[OF S T Pxy] by (rule distributed_unique)

lemma (in prob_space) distributed_marginal_eq_joint2:
  assumes T: "sigma_finite_measure T"
  assumes S: "sigma_finite_measure S"
  assumes Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "AE y in T. Py y = (\<integral>\<^sup>+x. Pxy (x, y) \<partial>S)"
  using Py distr_marginal2[OF S T Pxy] by (rule distributed_unique)

lemma (in prob_space) distributed_joint_indep':
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes X[measurable]: "distributed M S X Px" and Y[measurable]: "distributed M T Y Py"
  assumes indep: "distr M S X \<Otimes>\<^sub>M distr M T Y = distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
  shows "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) (\<lambda>(x, y). Px x * Py y)"
  unfolding distributed_def
proof safe
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  interpret X: prob_space "density S Px"
    unfolding distributed_distr_eq_density[OF X, symmetric]
    by (rule prob_space_distr) simp
  have sf_X: "sigma_finite_measure (density S Px)" ..

  interpret Y: prob_space "density T Py"
    unfolding distributed_distr_eq_density[OF Y, symmetric]
    by (rule prob_space_distr) simp
  have sf_Y: "sigma_finite_measure (density T Py)" ..

  show "distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) = density (S \<Otimes>\<^sub>M T) (\<lambda>(x, y). Px x * Py y)"
    unfolding indep[symmetric] distributed_distr_eq_density[OF X] distributed_distr_eq_density[OF Y]
    using distributed_borel_measurable[OF X]
    using distributed_borel_measurable[OF Y]
    by (rule pair_measure_density[OF _ _ T sf_Y])

  show "random_variable (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))" by auto

  show Pxy: "(\<lambda>(x, y). Px x * Py y) \<in> borel_measurable (S \<Otimes>\<^sub>M T)" by auto
qed

lemma distributed_integrable:
  "distributed M N X f \<Longrightarrow> g \<in> borel_measurable N \<Longrightarrow> (\<And>x. x \<in> space N \<Longrightarrow> 0 \<le> f x) \<Longrightarrow>
    integrable N (\<lambda>x. f x * g x) \<longleftrightarrow> integrable M (\<lambda>x. g (X x))"
  supply distributed_real_measurable[measurable]
  by (auto simp: distributed_distr_eq_density[symmetric] integrable_real_density[symmetric] integrable_distr_eq)

lemma distributed_transform_integrable:
  assumes Px: "distributed M N X Px" "\<And>x. x \<in> space N \<Longrightarrow> 0 \<le> Px x"
  assumes "distributed M P Y Py" "\<And>x. x \<in> space P \<Longrightarrow> 0 \<le> Py x"
  assumes Y: "Y = (\<lambda>x. T (X x))" and T: "T \<in> measurable N P" and f: "f \<in> borel_measurable P"
  shows "integrable P (\<lambda>x. Py x * f x) \<longleftrightarrow> integrable N (\<lambda>x. Px x * f (T x))"
proof -
  have "integrable P (\<lambda>x. Py x * f x) \<longleftrightarrow> integrable M (\<lambda>x. f (Y x))"
    by (rule distributed_integrable) fact+
  also have "\<dots> \<longleftrightarrow> integrable M (\<lambda>x. f (T (X x)))"
    using Y by simp
  also have "\<dots> \<longleftrightarrow> integrable N (\<lambda>x. Px x * f (T x))"
    using measurable_comp[OF T f] Px by (intro distributed_integrable[symmetric]) (auto simp: comp_def)
  finally show ?thesis .
qed

lemma distributed_integrable_var:
  fixes X :: "'a \<Rightarrow> real"
  shows "distributed M lborel X (\<lambda>x. ennreal (f x)) \<Longrightarrow> (\<And>x. 0 \<le> f x) \<Longrightarrow>
    integrable lborel (\<lambda>x. f x * x) \<Longrightarrow> integrable M X"
  using distributed_integrable[of M lborel X f "\<lambda>x. x"] by simp

lemma (in prob_space) distributed_variance:
  fixes f::"real \<Rightarrow> real"
  assumes D: "distributed M lborel X f" and [simp]: "\<And>x. 0 \<le> f x"
  shows "variance X = (\<integral>x. x\<^sup>2 * f (x + expectation X) \<partial>lborel)"
proof (subst distributed_integral[OF D, symmetric])
  show "(\<integral> x. f x * (x - expectation X)\<^sup>2 \<partial>lborel) = (\<integral> x. x\<^sup>2 * f (x + expectation X) \<partial>lborel)"
    by (subst lborel_integral_real_affine[where c=1 and t="expectation X"])  (auto simp: ac_simps)
qed simp_all

lemma (in prob_space) variance_affine:
  fixes f::"real \<Rightarrow> real"
  assumes [arith]: "b \<noteq> 0"
  assumes D[intro]: "distributed M lborel X f"
  assumes [simp]: "prob_space (density lborel f)"
  assumes I[simp]: "integrable M X"
  assumes I2[simp]: "integrable M (\<lambda>x. (X x)\<^sup>2)"
  shows "variance (\<lambda>x. a + b * X x) = b\<^sup>2 * variance X"
  by (subst variance_eq)
     (auto simp: power2_sum power_mult_distrib prob_space variance_eq right_diff_distrib)

definition
  "simple_distributed M X f \<longleftrightarrow>
    (\<forall>x. 0 \<le> f x) \<and>
    distributed M (count_space (X`space M)) X (\<lambda>x. ennreal (f x)) \<and>
    finite (X`space M)"

lemma simple_distributed_nonneg[dest]: "simple_distributed M X f \<Longrightarrow> 0 \<le> f x"
  by (auto simp: simple_distributed_def)

lemma simple_distributed:
  "simple_distributed M X Px \<Longrightarrow> distributed M (count_space (X`space M)) X Px"
  unfolding simple_distributed_def by auto

lemma simple_distributed_finite[dest]: "simple_distributed M X P \<Longrightarrow> finite (X`space M)"
  by (simp add: simple_distributed_def)

lemma (in prob_space) distributed_simple_function_superset:
  assumes X: "simple_function M X" "\<And>x. x \<in> X ` space M \<Longrightarrow> P x = measure M (X -` {x} \<inter> space M)"
  assumes A: "X`space M \<subseteq> A" "finite A"
  defines "S \<equiv> count_space A" and "P' \<equiv> (\<lambda>x. if x \<in> X`space M then P x else 0)"
  shows "distributed M S X P'"
  unfolding distributed_def
proof safe
  show "(\<lambda>x. ennreal (P' x)) \<in> borel_measurable S" unfolding S_def by simp
  show "distr M S X = density S P'"
  proof (rule measure_eqI_finite)
    show "sets (distr M S X) = Pow A" "sets (density S P') = Pow A"
      using A unfolding S_def by auto
    show "finite A" by fact
    fix a assume a: "a \<in> A"
    then have "a \<notin> X`space M \<Longrightarrow> X -` {a} \<inter> space M = {}" by auto
    with A a X have "emeasure (distr M S X) {a} = P' a"
      by (subst emeasure_distr)
         (auto simp add: S_def P'_def simple_functionD emeasure_eq_measure measurable_count_space_eq2
               intro!: arg_cong[where f=prob])
    also have "\<dots> = (\<integral>\<^sup>+x. ennreal (P' a) * indicator {a} x \<partial>S)"
      using A X a
      by (subst nn_integral_cmult_indicator)
         (auto simp: S_def P'_def simple_distributed_def simple_functionD measure_nonneg)
    also have "\<dots> = (\<integral>\<^sup>+x. ennreal (P' x) * indicator {a} x \<partial>S)"
      by (auto simp: indicator_def intro!: nn_integral_cong)
    also have "\<dots> = emeasure (density S P') {a}"
      using a A by (intro emeasure_density[symmetric]) (auto simp: S_def)
    finally show "emeasure (distr M S X) {a} = emeasure (density S P') {a}" .
  qed
  show "random_variable S X"
    using X(1) A by (auto simp: measurable_def simple_functionD S_def)
qed

lemma (in prob_space) simple_distributedI:
  assumes X: "simple_function M X"
    "\<And>x. 0 \<le> P x"
    "\<And>x. x \<in> X ` space M \<Longrightarrow> P x = measure M (X -` {x} \<inter> space M)"
  shows "simple_distributed M X P"
  unfolding simple_distributed_def
proof (safe intro!: X)
  have "distributed M (count_space (X ` space M)) X (\<lambda>x. ennreal (if x \<in> X`space M then P x else 0))"
    (is "?A")
    using simple_functionD[OF X(1)] by (intro distributed_simple_function_superset[OF X(1,3)]) auto
  also have "?A \<longleftrightarrow> distributed M (count_space (X ` space M)) X (\<lambda>x. ennreal (P x))"
    by (rule distributed_cong_density) auto
  finally show "\<dots>" .
qed (rule simple_functionD[OF X(1)])

lemma simple_distributed_joint_finite:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x)) Px"
  shows "finite (X ` space M)" "finite (Y ` space M)"
proof -
  have "finite ((\<lambda>x. (X x, Y x)) ` space M)"
    using X by (auto simp: simple_distributed_def simple_functionD)
  then have "finite (fst ` (\<lambda>x. (X x, Y x)) ` space M)" "finite (snd ` (\<lambda>x. (X x, Y x)) ` space M)"
    by auto
  then show fin: "finite (X ` space M)" "finite (Y ` space M)"
    by (auto simp: image_image)
qed

lemma simple_distributed_joint2_finite:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x, Z x)) Px"
  shows "finite (X ` space M)" "finite (Y ` space M)" "finite (Z ` space M)"
proof -
  have "finite ((\<lambda>x. (X x, Y x, Z x)) ` space M)"
    using X by (auto simp: simple_distributed_def simple_functionD)
  then have "finite (fst ` (\<lambda>x. (X x, Y x, Z x)) ` space M)"
    "finite ((fst \<circ> snd) ` (\<lambda>x. (X x, Y x, Z x)) ` space M)"
    "finite ((snd \<circ> snd) ` (\<lambda>x. (X x, Y x, Z x)) ` space M)"
    by auto
  then show fin: "finite (X ` space M)" "finite (Y ` space M)" "finite (Z ` space M)"
    by (auto simp: image_image)
qed

lemma simple_distributed_simple_function:
  "simple_distributed M X Px \<Longrightarrow> simple_function M X"
  unfolding simple_distributed_def distributed_def
  by (auto simp: simple_function_def measurable_count_space_eq2)

lemma simple_distributed_measure:
  "simple_distributed M X P \<Longrightarrow> a \<in> X`space M \<Longrightarrow> P a = measure M (X -` {a} \<inter> space M)"
  using distributed_count_space[of M "X`space M" X P a, symmetric]
  by (auto simp: simple_distributed_def measure_def)

lemma (in prob_space) simple_distributed_joint:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x)) Px"
  defines "S \<equiv> count_space (X`space M) \<Otimes>\<^sub>M count_space (Y`space M)"
  defines "P \<equiv> (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x))`space M then Px x else 0)"
  shows "distributed M S (\<lambda>x. (X x, Y x)) P"
proof -
  from simple_distributed_joint_finite[OF X, simp]
  have S_eq: "S = count_space (X`space M \<times> Y`space M)"
    by (simp add: S_def pair_measure_count_space)
  show ?thesis
    unfolding S_eq P_def
  proof (rule distributed_simple_function_superset)
    show "simple_function M (\<lambda>x. (X x, Y x))"
      using X by (rule simple_distributed_simple_function)
    fix x assume "x \<in> (\<lambda>x. (X x, Y x)) ` space M"
    from simple_distributed_measure[OF X this]
    show "Px x = prob ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M)" .
  qed auto
qed

lemma (in prob_space) simple_distributed_joint2:
  assumes X: "simple_distributed M (\<lambda>x. (X x, Y x, Z x)) Px"
  defines "S \<equiv> count_space (X`space M) \<Otimes>\<^sub>M count_space (Y`space M) \<Otimes>\<^sub>M count_space (Z`space M)"
  defines "P \<equiv> (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x, Z x))`space M then Px x else 0)"
  shows "distributed M S (\<lambda>x. (X x, Y x, Z x)) P"
proof -
  from simple_distributed_joint2_finite[OF X, simp]
  have S_eq: "S = count_space (X`space M \<times> Y`space M \<times> Z`space M)"
    by (simp add: S_def pair_measure_count_space)
  show ?thesis
    unfolding S_eq P_def
  proof (rule distributed_simple_function_superset)
    show "simple_function M (\<lambda>x. (X x, Y x, Z x))"
      using X by (rule simple_distributed_simple_function)
    fix x assume "x \<in> (\<lambda>x. (X x, Y x, Z x)) ` space M"
    from simple_distributed_measure[OF X this]
    show "Px x = prob ((\<lambda>x. (X x, Y x, Z x)) -` {x} \<inter> space M)" .
  qed auto
qed

lemma (in prob_space) simple_distributed_sum_space:
  assumes X: "simple_distributed M X f"
  shows "sum f (X`space M) = 1"
proof -
  from X have "sum f (X`space M) = prob (\<Union>i\<in>X`space M. X -` {i} \<inter> space M)"
    by (subst finite_measure_finite_Union)
       (auto simp add: disjoint_family_on_def simple_distributed_measure simple_distributed_simple_function simple_functionD
             intro!: sum.cong arg_cong[where f="prob"])
  also have "\<dots> = prob (space M)"
    by (auto intro!: arg_cong[where f=prob])
  finally show ?thesis
    using emeasure_space_1 by (simp add: emeasure_eq_measure)
qed

lemma (in prob_space) distributed_marginal_eq_joint_simple:
  assumes Px: "simple_function M X"
  assumes Py: "simple_distributed M Y Py"
  assumes Pxy: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
  assumes y: "y \<in> Y`space M"
  shows "Py y = (\<Sum>x\<in>X`space M. if (x, y) \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy (x, y) else 0)"
proof -
  note Px = simple_distributedI[OF Px measure_nonneg refl]
  have "AE y in count_space (Y ` space M). ennreal (Py y) =
       \<integral>\<^sup>+ x. ennreal (if (x, y) \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy (x, y) else 0) \<partial>count_space (X ` space M)"
    using sigma_finite_measure_count_space_finite sigma_finite_measure_count_space_finite
      simple_distributed[OF Py] simple_distributed_joint[OF Pxy]
    by (rule distributed_marginal_eq_joint2)
       (auto intro: Py Px simple_distributed_finite)
  then have "ennreal (Py y) =
    (\<Sum>x\<in>X`space M. ennreal (if (x, y) \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy (x, y) else 0))"
    using y Px[THEN simple_distributed_finite]
    by (auto simp: AE_count_space nn_integral_count_space_finite)
  also have "\<dots> = (\<Sum>x\<in>X`space M. if (x, y) \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy (x, y) else 0)"
    using Pxy by (intro sum_ennreal) auto
  finally show ?thesis
    using simple_distributed_nonneg[OF Py] simple_distributed_nonneg[OF Pxy]
    by (subst (asm) ennreal_inj) (auto intro!: sum_nonneg)
qed

lemma distributedI_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes gen: "sets M1 = sigma_sets (space M1) E" and "Int_stable E"
    and A: "range A \<subseteq> E" "(\<Union>i::nat. A i) = space M1" "\<And>i. emeasure (distr M M1 X) (A i) \<noteq> \<infinity>"
    and X: "X \<in> measurable M M1"
    and f: "f \<in> borel_measurable M1" "AE x in M1. 0 \<le> f x"
    and eq: "\<And>A. A \<in> E \<Longrightarrow> emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+ x. f x * indicator A x \<partial>M1)"
  shows "distributed M M1 X f"
  unfolding distributed_def
proof (intro conjI)
  show "distr M M1 X = density M1 f"
  proof (rule measure_eqI_generator_eq[where A=A])
    { fix A assume A: "A \<in> E"
      then have "A \<in> sigma_sets (space M1) E" by auto
      then have "A \<in> sets M1"
        using gen by simp
      with f A eq[of A] X show "emeasure (distr M M1 X) A = emeasure (density M1 f) A"
        by (auto simp add: emeasure_distr emeasure_density ennreal_indicator
                 intro!: nn_integral_cong split: split_indicator) }
    note eq_E = this
    show "Int_stable E" by fact
    { fix e assume "e \<in> E"
      then have "e \<in> sigma_sets (space M1) E" by auto
      then have "e \<in> sets M1" unfolding gen .
      then have "e \<subseteq> space M1" by (rule sets.sets_into_space) }
    then show "E \<subseteq> Pow (space M1)" by auto
    show "sets (distr M M1 X) = sigma_sets (space M1) E"
      "sets (density M1 (\<lambda>x. ennreal (f x))) = sigma_sets (space M1) E"
      unfolding gen[symmetric] by auto
  qed fact+
qed (insert X f, auto)

lemma distributedI_borel_atMost:
  fixes f :: "real \<Rightarrow> real"
  assumes [measurable]: "X \<in> borel_measurable M"
    and [measurable]: "f \<in> borel_measurable borel" and f[simp]: "AE x in lborel. 0 \<le> f x"
    and g_eq: "\<And>a. (\<integral>\<^sup>+x. f x * indicator {..a} x \<partial>lborel)  = ennreal (g a)"
    and M_eq: "\<And>a. emeasure M {x\<in>space M. X x \<le> a} = ennreal (g a)"
  shows "distributed M lborel X f"
proof (rule distributedI_real)
  show "sets (lborel::real measure) = sigma_sets (space lborel) (range atMost)"
    by (simp add: borel_eq_atMost)
  show "Int_stable (range atMost :: real set set)"
    by (auto simp: Int_stable_def)
  have vimage_eq: "\<And>a. (X -` {..a} \<inter> space M) = {x\<in>space M. X x \<le> a}" by auto
  define A where "A i = {.. real i}" for i :: nat
  then show "range A \<subseteq> range atMost" "(\<Union>i. A i) = space lborel"
    "\<And>i. emeasure (distr M lborel X) (A i) \<noteq> \<infinity>"
    by (auto simp: real_arch_simple emeasure_distr vimage_eq M_eq)

  fix A :: "real set" assume "A \<in> range atMost"
  then obtain a where A: "A = {..a}" by auto
  show "emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>lborel)"
    unfolding vimage_eq A M_eq g_eq ..
qed auto

lemma (in prob_space) uniform_distributed_params:
  assumes X: "distributed M MX X (\<lambda>x. indicator A x / measure MX A)"
  shows "A \<in> sets MX" "measure MX A \<noteq> 0"
proof -
  interpret X: prob_space "distr M MX X"
    using distributed_measurable[OF X] by (rule prob_space_distr)

  show "measure MX A \<noteq> 0"
  proof
    assume "measure MX A = 0"
    with X.emeasure_space_1 X.prob_space distributed_distr_eq_density[OF X]
    show False
      by (simp add: emeasure_density zero_ennreal_def[symmetric])
  qed
  with measure_notin_sets[of A MX] show "A \<in> sets MX"
    by blast
qed

lemma prob_space_uniform_measure:
  assumes A: "emeasure M A \<noteq> 0" "emeasure M A \<noteq> \<infinity>"
  shows "prob_space (uniform_measure M A)"
proof
  show "emeasure (uniform_measure M A) (space (uniform_measure M A)) = 1"
    using emeasure_uniform_measure[OF emeasure_neq_0_sets[OF A(1)], of "space M"]
    using sets.sets_into_space[OF emeasure_neq_0_sets[OF A(1)]] A
    by (simp add: Int_absorb2 less_top)
qed

lemma prob_space_uniform_count_measure: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> prob_space (uniform_count_measure A)"
  by standard (auto simp: emeasure_uniform_count_measure space_uniform_count_measure one_ennreal_def)

lemma (in prob_space) measure_uniform_measure_eq_cond_prob:
  assumes [measurable]: "Measurable.pred M P" "Measurable.pred M Q"
  shows "\<P>(x in uniform_measure M {x\<in>space M. Q x}. P x) = \<P>(x in M. P x \<bar> Q x)"
proof cases
  assume Q: "measure M {x\<in>space M. Q x} = 0"
  then have *: "AE x in M. \<not> Q x"
    by (simp add: prob_eq_0)
  then have "density M (\<lambda>x. indicator {x \<in> space M. Q x} x / emeasure M {x \<in> space M. Q x}) = density M (\<lambda>x. 0)"
    by (intro density_cong) auto
  with * show ?thesis
    unfolding uniform_measure_def
    by (simp add: emeasure_density measure_def cond_prob_def emeasure_eq_0_AE)
next
  assume Q: "measure M {x\<in>space M. Q x} \<noteq> 0"
  then show "\<P>(x in uniform_measure M {x \<in> space M. Q x}. P x) = cond_prob M P Q"
    by (subst measure_uniform_measure)
       (auto simp: emeasure_eq_measure cond_prob_def measure_nonneg intro!: arg_cong[where f=prob])
qed

lemma prob_space_point_measure:
  "finite S \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> 0 \<le> p s) \<Longrightarrow> (\<Sum>s\<in>S. p s) = 1 \<Longrightarrow> prob_space (point_measure S p)"
  by (rule prob_spaceI) (simp add: space_point_measure emeasure_point_measure_finite)

lemma (in prob_space) distr_pair_fst: "distr (N \<Otimes>\<^sub>M M) N fst = N"
proof (intro measure_eqI)
  fix A assume A: "A \<in> sets (distr (N \<Otimes>\<^sub>M M) N fst)"
  from A have "emeasure (distr (N \<Otimes>\<^sub>M M) N fst) A = emeasure (N \<Otimes>\<^sub>M M) (A \<times> space M)"
    by (auto simp add: emeasure_distr space_pair_measure dest: sets.sets_into_space intro!: arg_cong2[where f=emeasure])
  with A show "emeasure (distr (N \<Otimes>\<^sub>M M) N fst) A = emeasure N A"
    by (simp add: emeasure_pair_measure_Times emeasure_space_1)
qed simp

lemma (in product_prob_space) distr_reorder:
  assumes "inj_on t J" "t \<in> J \<rightarrow> K" "finite K"
  shows "distr (PiM K M) (Pi\<^sub>M J (\<lambda>x. M (t x))) (\<lambda>\<omega>. \<lambda>n\<in>J. \<omega> (t n)) = PiM J (\<lambda>x. M (t x))"
proof (rule product_sigma_finite.PiM_eqI)
  show "product_sigma_finite (\<lambda>x. M (t x))" ..
  have "t`J \<subseteq> K" using assms by auto
  then show [simp]: "finite J"
    by (rule finite_imageD[OF finite_subset]) fact+
  fix A assume A: "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets (M (t i))"
  moreover have "((\<lambda>\<omega>. \<lambda>n\<in>J. \<omega> (t n)) -` Pi\<^sub>E J A \<inter> space (Pi\<^sub>M K M)) =
    (\<Pi>\<^sub>E i\<in>K. if i \<in> t`J then A (the_inv_into J t i) else space (M i))"
    using A A[THEN sets.sets_into_space] \<open>t \<in> J \<rightarrow> K\<close> \<open>inj_on t J\<close>
    by (subst prod_emb_Pi[symmetric]) (auto simp: space_PiM PiE_iff the_inv_into_f_f prod_emb_def)
  ultimately show "distr (Pi\<^sub>M K M) (Pi\<^sub>M J (\<lambda>x. M (t x))) (\<lambda>\<omega>. \<lambda>n\<in>J. \<omega> (t n)) (Pi\<^sub>E J A) = (\<Prod>i\<in>J. M (t i) (A i))"
    using assms
    apply (subst emeasure_distr)
    apply (auto intro!: sets_PiM_I_finite simp: Pi_iff)
    apply (subst emeasure_PiM)
    apply (auto simp: the_inv_into_f_f \<open>inj_on t J\<close> prod.reindex[OF \<open>inj_on t J\<close>]
      if_distrib[where f="emeasure (M _)"] prod.If_cases emeasure_space_1 Int_absorb1 \<open>t`J \<subseteq> K\<close>)
    done
qed simp

lemma (in product_prob_space) distr_restrict:
  "J \<subseteq> K \<Longrightarrow> finite K \<Longrightarrow> (\<Pi>\<^sub>M i\<in>J. M i) = distr (\<Pi>\<^sub>M i\<in>K. M i) (\<Pi>\<^sub>M i\<in>J. M i) (\<lambda>f. restrict f J)"
  using distr_reorder[of "\<lambda>x. x" J K] by (simp add: Pi_iff subset_eq)

lemma (in product_prob_space) emeasure_prod_emb[simp]:
  assumes L: "J \<subseteq> L" "finite L" and X: "X \<in> sets (Pi\<^sub>M J M)"
  shows "emeasure (Pi\<^sub>M L M) (prod_emb L M J X) = emeasure (Pi\<^sub>M J M) X"
  by (subst distr_restrict[OF L])
     (simp add: prod_emb_def space_PiM emeasure_distr measurable_restrict_subset L X)

lemma emeasure_distr_restrict:
  assumes "I \<subseteq> K" and Q[measurable_cong]: "sets Q = sets (PiM K M)" and A[measurable]: "A \<in> sets (PiM I M)"
  shows "emeasure (distr Q (PiM I M) (\<lambda>\<omega>. restrict \<omega> I)) A = emeasure Q (prod_emb K M I A)"
  using \<open>I\<subseteq>K\<close> sets_eq_imp_space_eq[OF Q]
  by (subst emeasure_distr)
     (auto simp: measurable_cong_sets[OF Q] prod_emb_def space_PiM[symmetric] intro!: measurable_restrict)

lemma (in prob_space) prob_space_completion: "prob_space (completion M)"
  by (rule prob_spaceI) (simp add: emeasure_space_1)

lemma distr_PiM_finite_prob_space:
  assumes fin: "finite I"
  assumes "product_prob_space M"
  assumes "product_prob_space M'"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> f \<in> measurable (M i) (M' i)"
  shows   "distr (PiM I M) (PiM I M') (compose I f) = PiM I (\<lambda>i. distr (M i) (M' i) f)"
proof -
  interpret M: product_prob_space M by fact
  interpret M': product_prob_space M' by fact
  define N where "N = (\<lambda>i. if i \<in> I then distr (M i) (M' i) f else M' i)"
  have [intro]: "prob_space (N i)" for i
    by (auto simp: N_def intro!: M.M.prob_space_distr M'.prob_space)

  interpret N: product_prob_space N
    by (intro product_prob_spaceI) (auto simp: N_def M'.prob_space intro: M.M.prob_space_distr)

  have "distr (PiM I M) (PiM I M') (compose I f) = PiM I N"
  proof (rule N.PiM_eqI)
    have N_events_eq: "sets (Pi\<^sub>M I N) = sets (Pi\<^sub>M I M')"
      unfolding N_def by (intro sets_PiM_cong) auto
    also have "\<dots> = sets (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f))"
      by simp
    finally show "sets (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f)) = sets (Pi\<^sub>M I N)"  ..

    fix A assume A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> N.M.events i"
    have "emeasure (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f)) (Pi\<^sub>E I A) =
          emeasure (Pi\<^sub>M I M) (compose I f -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I M))"
    proof (intro emeasure_distr)
      show "compose I f \<in> Pi\<^sub>M I M \<rightarrow>\<^sub>M Pi\<^sub>M I M'"
        unfolding compose_def by measurable
      show "Pi\<^sub>E I A \<in> sets (Pi\<^sub>M I M')"
        unfolding N_events_eq [symmetric] by (intro sets_PiM_I_finite fin A)
    qed
    also have "compose I f -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I M) = Pi\<^sub>E I (\<lambda>i. f -` A i \<inter> space (M i))"
      using A by (auto simp: space_PiM PiE_def Pi_def extensional_def N_def compose_def)
    also have "emeasure (Pi\<^sub>M I M) (Pi\<^sub>E I (\<lambda>i. f -` A i \<inter> space (M i))) =
          (\<Prod>i\<in>I. emeasure (M i) (f -` A i \<inter> space (M i)))"
      using A by (intro M.emeasure_PiM fin) (auto simp: N_def)
    also have "\<dots> = (\<Prod>i\<in>I. emeasure (distr (M i) (M' i) f) (A i))"
      using A by (intro prod.cong emeasure_distr [symmetric]) (auto simp: N_def)
    also have "\<dots> = (\<Prod>i\<in>I. emeasure (N i) (A i))"
      unfolding N_def by (intro prod.cong) (auto simp: N_def)
    finally show "emeasure (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f)) (Pi\<^sub>E I A) = \<dots>" .
  qed fact+
  also have "PiM I N = PiM I (\<lambda>i. distr (M i) (M' i) f)"
    by (intro PiM_cong) (auto simp: N_def)
  finally show ?thesis .
qed

end
