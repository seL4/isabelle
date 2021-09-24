(*  Title:      HOL/Analysis/Radon_Nikodym.thy
    Author:     Johannes Hölzl, TU München
*)

section \<open>Radon-Nikod{\'y}m Derivative\<close>

theory Radon_Nikodym
imports Bochner_Integration
begin

definition\<^marker>\<open>tag important\<close> diff_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure"
where
  "diff_measure M N = measure_of (space M) (sets M) (\<lambda>A. emeasure M A - emeasure N A)"

lemma
  shows space_diff_measure[simp]: "space (diff_measure M N) = space M"
    and sets_diff_measure[simp]: "sets (diff_measure M N) = sets M"
  by (auto simp: diff_measure_def)

lemma emeasure_diff_measure:
  assumes fin: "finite_measure M" "finite_measure N" and sets_eq: "sets M = sets N"
  assumes pos: "\<And>A. A \<in> sets M \<Longrightarrow> emeasure N A \<le> emeasure M A" and A: "A \<in> sets M"
  shows "emeasure (diff_measure M N) A = emeasure M A - emeasure N A" (is "_ = ?\<mu> A")
  unfolding diff_measure_def
proof (rule emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)" ..
  show "positive (sets M) ?\<mu>"
    using pos by (simp add: positive_def)
  show "countably_additive (sets M) ?\<mu>"
  proof (rule countably_additiveI)
    fix A :: "nat \<Rightarrow> _"  assume A: "range A \<subseteq> sets M" and "disjoint_family A"
    then have suminf:
      "(\<Sum>i. emeasure M (A i)) = emeasure M (\<Union>i. A i)"
      "(\<Sum>i. emeasure N (A i)) = emeasure N (\<Union>i. A i)"
      by (simp_all add: suminf_emeasure sets_eq)
    with A have "(\<Sum>i. emeasure M (A i) - emeasure N (A i)) =
      (\<Sum>i. emeasure M (A i)) - (\<Sum>i. emeasure N (A i))"
      using fin pos[of "A _"]
      by (intro ennreal_suminf_minus)
         (auto simp: sets_eq finite_measure.emeasure_eq_measure suminf_emeasure)
    then show "(\<Sum>i. emeasure M (A i) - emeasure N (A i)) =
      emeasure M (\<Union>i. A i) - emeasure N (\<Union>i. A i) "
      by (simp add: suminf)
  qed
qed fact

text \<open>An equivalent characterization of sigma-finite spaces is the existence of integrable
positive functions (or, still equivalently, the existence of a probability measure which is in
the same measure class as the original measure).\<close>

proposition (in sigma_finite_measure) obtain_positive_integrable_function:
  obtains f::"'a \<Rightarrow> real" where
    "f \<in> borel_measurable M"
    "\<And>x. f x > 0"
    "\<And>x. f x \<le> 1"
    "integrable M f"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
    using sigma_finite by auto
  then have [measurable]:"A n \<in> sets M" for n by auto
  define g where "g = (\<lambda>x. (\<Sum>n. (1/2)^(Suc n) * indicator (A n) x / (1+ measure M (A n))))"
  have [measurable]: "g \<in> borel_measurable M" unfolding g_def by auto
  have *: "summable (\<lambda>n. (1/2)^(Suc n) * indicator (A n) x / (1+ measure M (A n)))" for x
    apply (rule summable_comparison_test'[of "\<lambda>n. (1/2)^(Suc n)" 0])
    using power_half_series summable_def by (auto simp add: indicator_def divide_simps)
  have "g x \<le> (\<Sum>n. (1/2)^(Suc n))" for x unfolding g_def
    apply (rule suminf_le) using * power_half_series summable_def by (auto simp add: indicator_def divide_simps)
  then have g_le_1: "g x \<le> 1" for x using power_half_series sums_unique by fastforce

  have g_pos: "g x > 0" if "x \<in> space M" for x
  unfolding g_def proof (subst suminf_pos_iff[OF *[of x]], auto)
    obtain i where "x \<in> A i" using \<open>(\<Union>i. A i) = space M\<close> \<open>x \<in> space M\<close> by auto
    then have "0 < (1 / 2) ^ Suc i * indicator (A i) x / (1 + Sigma_Algebra.measure M (A i))"
      unfolding indicator_def apply (auto simp add: divide_simps) using measure_nonneg[of M "A i"]
      by (auto, meson add_nonneg_nonneg linorder_not_le mult_nonneg_nonneg zero_le_numeral zero_le_one zero_le_power)
    then show "\<exists>i. 0 < (1 / 2) ^ i * indicator (A i) x / (2 + 2 * Sigma_Algebra.measure M (A i))"
      by auto
  qed

  have "integrable M g"
  unfolding g_def proof (rule integrable_suminf)
    fix n
    show "integrable M (\<lambda>x. (1 / 2) ^ Suc n * indicator (A n) x / (1 + Sigma_Algebra.measure M (A n)))"
      using \<open>emeasure M (A n) \<noteq> \<infinity>\<close>
      by (auto intro!: integrable_mult_right integrable_divide_zero integrable_real_indicator simp add: top.not_eq_extremum)
  next
    show "AE x in M. summable (\<lambda>n. norm ((1 / 2) ^ Suc n * indicator (A n) x / (1 + Sigma_Algebra.measure M (A n))))"
      using * by auto
    show "summable (\<lambda>n. (\<integral>x. norm ((1 / 2) ^ Suc n * indicator (A n) x / (1 + Sigma_Algebra.measure M (A n))) \<partial>M))"
      apply (rule summable_comparison_test'[of "\<lambda>n. (1/2)^(Suc n)" 0], auto)
      using power_half_series summable_def apply auto[1]
      apply (auto simp add: field_split_simps) using measure_nonneg[of M] not_less by fastforce
  qed

  define f where "f = (\<lambda>x. if x \<in> space M then g x else 1)"
  have "f x > 0" for x unfolding f_def using g_pos by auto
  moreover have "f x \<le> 1" for x unfolding f_def using g_le_1 by auto
  moreover have [measurable]: "f \<in> borel_measurable M" unfolding f_def by auto
  moreover have "integrable M f"
    apply (subst integrable_cong[of _ _ _ g]) unfolding f_def using \<open>integrable M g\<close> by auto
  ultimately show "(\<And>f. f \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 < f x) \<Longrightarrow> (\<And>x. f x \<le> 1) \<Longrightarrow> integrable M f \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by (meson that)
qed

lemma (in sigma_finite_measure) Ex_finite_integrable_function:
  "\<exists>h\<in>borel_measurable M. integral\<^sup>N M h \<noteq> \<infinity> \<and> (\<forall>x\<in>space M. 0 < h x \<and> h x < \<infinity>)"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range[measurable]: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. emeasure M (A i) \<noteq> \<infinity>" and
    disjoint: "disjoint_family A"
    using sigma_finite_disjoint by blast
  let ?B = "\<lambda>i. 2^Suc i * emeasure M (A i)"
  have [measurable]: "\<And>i. A i \<in> sets M"
    using range by fastforce+
  have "\<forall>i. \<exists>x. 0 < x \<and> x < inverse (?B i)"
  proof
    fix i show "\<exists>x. 0 < x \<and> x < inverse (?B i)"
      using measure[of i]
      by (auto intro!: dense simp: ennreal_inverse_positive ennreal_mult_eq_top_iff power_eq_top_ennreal)
  qed
  from choice[OF this] obtain n where n: "\<And>i. 0 < n i"
    "\<And>i. n i < inverse (2^Suc i * emeasure M (A i))" by auto
  { fix i have "0 \<le> n i" using n(1)[of i] by auto } note pos = this
  let ?h = "\<lambda>x. \<Sum>i. n i * indicator (A i) x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?h] del: notI)
    have "integral\<^sup>N M ?h = (\<Sum>i. n i * emeasure M (A i))" using pos
      by (simp add: nn_integral_suminf nn_integral_cmult_indicator)
    also have "\<dots> \<le> (\<Sum>i. ennreal ((1/2)^Suc i))"
    proof (intro suminf_le allI)
      fix N
      have "n N * emeasure M (A N) \<le> inverse (2^Suc N * emeasure M (A N)) * emeasure M (A N)"
        using n[of N] by (intro mult_right_mono) auto
      also have "\<dots> = (1/2)^Suc N * (inverse (emeasure M (A N)) * emeasure M (A N))"
        using measure[of N]
        by (simp add: ennreal_inverse_power divide_ennreal_def ennreal_inverse_mult
                      power_eq_top_ennreal less_top[symmetric] mult_ac
                 del: power_Suc)
      also have "\<dots> \<le> inverse (ennreal 2) ^ Suc N"
        using measure[of N]
        by (cases "emeasure M (A N)"; cases "emeasure M (A N) = 0")
           (auto simp: inverse_ennreal ennreal_mult[symmetric] divide_ennreal_def simp del: power_Suc)
      also have "\<dots> = ennreal (inverse 2 ^ Suc N)"
        by (subst ennreal_power[symmetric], simp) (simp add: inverse_ennreal)
      finally show "n N * emeasure M (A N) \<le> ennreal ((1/2)^Suc N)"
        by simp
    qed auto
    also have "\<dots> < top"
      unfolding less_top[symmetric]
      by (rule ennreal_suminf_neq_top)
         (auto simp: summable_geometric summable_Suc_iff simp del: power_Suc)
    finally show "integral\<^sup>N M ?h \<noteq> \<infinity>"
      by (auto simp: top_unique)
  next
    { fix x assume "x \<in> space M"
      then obtain i where "x \<in> A i" using space[symmetric] by auto
      with disjoint n have "?h x = n i"
        by (auto intro!: suminf_cmult_indicator intro: less_imp_le)
      then show "0 < ?h x" and "?h x < \<infinity>" using n[of i] by (auto simp: less_top[symmetric]) }
    note pos = this
  qed measurable
qed

subsection "Absolutely continuous"

definition\<^marker>\<open>tag important\<close> absolutely_continuous :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "absolutely_continuous M N \<longleftrightarrow> null_sets M \<subseteq> null_sets N"

lemma absolutely_continuousI_count_space: "absolutely_continuous (count_space A) M"
  unfolding absolutely_continuous_def by (auto simp: null_sets_count_space)

lemma absolutely_continuousI_density:
  "f \<in> borel_measurable M \<Longrightarrow> absolutely_continuous M (density M f)"
  by (force simp add: absolutely_continuous_def null_sets_density_iff dest: AE_not_in)

lemma absolutely_continuousI_point_measure_finite:
  "(\<And>x. \<lbrakk> x \<in> A ; f x \<le> 0 \<rbrakk> \<Longrightarrow> g x \<le> 0) \<Longrightarrow> absolutely_continuous (point_measure A f) (point_measure A g)"
  unfolding absolutely_continuous_def by (force simp: null_sets_point_measure_iff)

lemma absolutely_continuousD:
  "absolutely_continuous M N \<Longrightarrow> A \<in> sets M \<Longrightarrow> emeasure M A = 0 \<Longrightarrow> emeasure N A = 0"
  by (auto simp: absolutely_continuous_def null_sets_def)

lemma absolutely_continuous_AE:
  assumes sets_eq: "sets M' = sets M"
    and "absolutely_continuous M M'" "AE x in M. P x"
   shows "AE x in M'. P x"
proof -
  from \<open>AE x in M. P x\<close> obtain N where N: "N \<in> null_sets M" "{x\<in>space M. \<not> P x} \<subseteq> N"
    unfolding eventually_ae_filter by auto
  show "AE x in M'. P x"
  proof (rule AE_I')
    show "{x\<in>space M'. \<not> P x} \<subseteq> N" using sets_eq_imp_space_eq[OF sets_eq] N(2) by simp
    from \<open>absolutely_continuous M M'\<close> show "N \<in> null_sets M'"
      using N unfolding absolutely_continuous_def sets_eq null_sets_def by auto
  qed
qed

subsection "Existence of the Radon-Nikodym derivative"

proposition
 (in finite_measure) Radon_Nikodym_finite_measure:
  assumes "finite_measure N" and sets_eq[simp]: "sets N = sets M"
  assumes "absolutely_continuous M N"
  shows "\<exists>f \<in> borel_measurable M. density M f = N"
proof -
  interpret N: finite_measure N by fact
  define G where "G = {g \<in> borel_measurable M. \<forall>A\<in>sets M. (\<integral>\<^sup>+x. g x * indicator A x \<partial>M) \<le> N A}"
  have [measurable_dest]: "f \<in> G \<Longrightarrow> f \<in> borel_measurable M"
    and G_D: "\<And>A. f \<in> G \<Longrightarrow> A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) \<le> N A" for f
    by (auto simp: G_def)
  note this[measurable_dest]
  have "(\<lambda>x. 0) \<in> G" unfolding G_def by auto
  hence "G \<noteq> {}" by auto
  { fix f g assume f[measurable]: "f \<in> G" and g[measurable]: "g \<in> G"
    have "(\<lambda>x. max (g x) (f x)) \<in> G" (is "?max \<in> G") unfolding G_def
    proof safe
      let ?A = "{x \<in> space M. f x \<le> g x}"
      have "?A \<in> sets M" using f g unfolding G_def by auto
      fix A assume [measurable]: "A \<in> sets M"
      have union: "((?A \<inter> A) \<union> ((space M - ?A) \<inter> A)) = A"
        using sets.sets_into_space[OF \<open>A \<in> sets M\<close>] by auto
      have "\<And>x. x \<in> space M \<Longrightarrow> max (g x) (f x) * indicator A x =
        g x * indicator (?A \<inter> A) x + f x * indicator ((space M - ?A) \<inter> A) x"
        by (auto simp: indicator_def max_def)
      hence "(\<integral>\<^sup>+x. max (g x) (f x) * indicator A x \<partial>M) =
        (\<integral>\<^sup>+x. g x * indicator (?A \<inter> A) x \<partial>M) +
        (\<integral>\<^sup>+x. f x * indicator ((space M - ?A) \<inter> A) x \<partial>M)"
        by (auto cong: nn_integral_cong intro!: nn_integral_add)
      also have "\<dots> \<le> N (?A \<inter> A) + N ((space M - ?A) \<inter> A)"
        using f g unfolding G_def by (auto intro!: add_mono)
      also have "\<dots> = N A"
        using union by (subst plus_emeasure) auto
      finally show "(\<integral>\<^sup>+x. max (g x) (f x) * indicator A x \<partial>M) \<le> N A" .
    qed auto }
  note max_in_G = this
  { fix f assume  "incseq f" and f: "\<And>i. f i \<in> G"
    then have [measurable]: "\<And>i. f i \<in> borel_measurable M" by (auto simp: G_def)
    have "(\<lambda>x. SUP i. f i x) \<in> G" unfolding G_def
    proof safe
      show "(\<lambda>x. SUP i. f i x) \<in> borel_measurable M" by measurable
    next
      fix A assume "A \<in> sets M"
      have "(\<integral>\<^sup>+x. (SUP i. f i x) * indicator A x \<partial>M) =
        (\<integral>\<^sup>+x. (SUP i. f i x * indicator A x) \<partial>M)"
        by (intro nn_integral_cong) (simp split: split_indicator)
      also have "\<dots> = (SUP i. (\<integral>\<^sup>+x. f i x * indicator A x \<partial>M))"
        using \<open>incseq f\<close> f \<open>A \<in> sets M\<close>
        by (intro nn_integral_monotone_convergence_SUP)
           (auto simp: G_def incseq_Suc_iff le_fun_def split: split_indicator)
      finally show "(\<integral>\<^sup>+x. (SUP i. f i x) * indicator A x \<partial>M) \<le> N A"
        using f \<open>A \<in> sets M\<close> by (auto intro!: SUP_least simp: G_D)
    qed }
  note SUP_in_G = this
  let ?y = "SUP g \<in> G. integral\<^sup>N M g"
  have y_le: "?y \<le> N (space M)" unfolding G_def
  proof (safe intro!: SUP_least)
    fix g assume "\<forall>A\<in>sets M. (\<integral>\<^sup>+x. g x * indicator A x \<partial>M) \<le> N A"
    from this[THEN bspec, OF sets.top] show "integral\<^sup>N M g \<le> N (space M)"
      by (simp cong: nn_integral_cong)
  qed
  from ennreal_SUP_countable_SUP [OF \<open>G \<noteq> {}\<close>, of "integral\<^sup>N M"]
  obtain ys :: "nat \<Rightarrow> ennreal"
    where ys: "range ys \<subseteq> integral\<^sup>N M ` G \<and> Sup (integral\<^sup>N M ` G) = Sup (range ys)"
    by auto
  then have "\<forall>n. \<exists>g. g\<in>G \<and> integral\<^sup>N M g = ys n"
  proof safe
    fix n assume "range ys \<subseteq> integral\<^sup>N M ` G"
    hence "ys n \<in> integral\<^sup>N M ` G" by auto
    thus "\<exists>g. g\<in>G \<and> integral\<^sup>N M g = ys n" by auto
  qed
  from choice[OF this] obtain gs where "\<And>i. gs i \<in> G" "\<And>n. integral\<^sup>N M (gs n) = ys n" by auto
  hence y_eq: "?y = (SUP i. integral\<^sup>N M (gs i))" using ys by auto
  let ?g = "\<lambda>i x. Max ((\<lambda>n. gs n x) ` {..i})"
  define f where [abs_def]: "f x = (SUP i. ?g i x)" for x
  let ?F = "\<lambda>A x. f x * indicator A x"
  have gs_not_empty: "\<And>i x. (\<lambda>n. gs n x) ` {..i} \<noteq> {}" by auto
  { fix i have "?g i \<in> G"
    proof (induct i)
      case 0 thus ?case by simp fact
    next
      case (Suc i)
      with Suc gs_not_empty \<open>gs (Suc i) \<in> G\<close> show ?case
        by (auto simp add: atMost_Suc intro!: max_in_G)
    qed }
  note g_in_G = this
  have "incseq ?g" using gs_not_empty
    by (auto intro!: incseq_SucI le_funI simp add: atMost_Suc)

  from SUP_in_G[OF this g_in_G] have [measurable]: "f \<in> G" unfolding f_def .
  then have [measurable]: "f \<in> borel_measurable M" unfolding G_def by auto

  have "integral\<^sup>N M f = (SUP i. integral\<^sup>N M (?g i))" unfolding f_def
    using g_in_G \<open>incseq ?g\<close> by (auto intro!: nn_integral_monotone_convergence_SUP simp: G_def)
  also have "\<dots> = ?y"
  proof (rule antisym)
    show "(SUP i. integral\<^sup>N M (?g i)) \<le> ?y"
      using g_in_G by (auto intro: SUP_mono)
    show "?y \<le> (SUP i. integral\<^sup>N M (?g i))" unfolding y_eq
      by (auto intro!: SUP_mono nn_integral_mono Max_ge)
  qed
  finally have int_f_eq_y: "integral\<^sup>N M f = ?y" .

  have upper_bound: "\<forall>A\<in>sets M. N A \<le> density M f A"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain A where A[measurable]: "A \<in> sets M" and f_less_N: "density M f A < N A"
      by (auto simp: not_le)
    then have pos_A: "0 < M A"
      using \<open>absolutely_continuous M N\<close>[THEN absolutely_continuousD, OF A]
      by (auto simp: zero_less_iff_neq_zero)

    define b where "b = (N A - density M f A) / M A / 2"
    with f_less_N pos_A have "0 < b" "b \<noteq> top"
      by (auto intro!: diff_gr0_ennreal simp: zero_less_iff_neq_zero diff_eq_0_iff_ennreal ennreal_divide_eq_top_iff)

    let ?f = "\<lambda>x. f x + b"
    have "nn_integral M f \<noteq> top"
      using \<open>f \<in> G\<close>[THEN G_D, of "space M"] by (auto simp: top_unique cong: nn_integral_cong)
    with \<open>b \<noteq> top\<close> interpret Mf: finite_measure "density M ?f"
      by (intro finite_measureI)
         (auto simp: field_simps mult_indicator_subset ennreal_mult_eq_top_iff
                     emeasure_density nn_integral_cmult_indicator nn_integral_add
               cong: nn_integral_cong)

    from unsigned_Hahn_decomposition[of "density M ?f" N A]
    obtain Y where [measurable]: "Y \<in> sets M" and [simp]: "Y \<subseteq> A"
       and Y1: "\<And>C. C \<in> sets M \<Longrightarrow> C \<subseteq> Y \<Longrightarrow> density M ?f C \<le> N C"
       and Y2: "\<And>C. C \<in> sets M \<Longrightarrow> C \<subseteq> A \<Longrightarrow> C \<inter> Y = {} \<Longrightarrow> N C \<le> density M ?f C"
       by auto

    let ?f' = "\<lambda>x. f x + b * indicator Y x"
    have "M Y \<noteq> 0"
    proof
      assume "M Y = 0"
      then have "N Y = 0"
        using \<open>absolutely_continuous M N\<close>[THEN absolutely_continuousD, of Y] by auto
      then have "N A = N (A - Y)"
        by (subst emeasure_Diff) auto
      also have "\<dots> \<le> density M ?f (A - Y)"
        by (rule Y2) auto
      also have "\<dots> \<le> density M ?f A - density M ?f Y"
        by (subst emeasure_Diff) auto
      also have "\<dots> \<le> density M ?f A - 0"
        by (intro ennreal_minus_mono) auto
      also have "density M ?f A = b * M A + density M f A"
        by (simp add: emeasure_density field_simps mult_indicator_subset nn_integral_add nn_integral_cmult_indicator)
      also have "\<dots> < N A"
        using f_less_N pos_A
        by (cases "density M f A"; cases "M A"; cases "N A")
           (auto simp: b_def ennreal_less_iff ennreal_minus divide_ennreal ennreal_numeral[symmetric]
                       ennreal_plus[symmetric] ennreal_mult[symmetric] field_simps
                    simp del: ennreal_numeral ennreal_plus)
      finally show False
        by simp
    qed
    then have "nn_integral M f < nn_integral M ?f'"
      using \<open>0 < b\<close> \<open>nn_integral M f \<noteq> top\<close>
      by (simp add: nn_integral_add nn_integral_cmult_indicator ennreal_zero_less_mult_iff zero_less_iff_neq_zero)
    moreover
    have "?f' \<in> G"
      unfolding G_def
    proof safe
      fix X assume [measurable]: "X \<in> sets M"
      have "(\<integral>\<^sup>+ x. ?f' x * indicator X x \<partial>M) = density M f (X - Y) + density M ?f (X \<inter> Y)"
        by (auto simp add: emeasure_density nn_integral_add[symmetric] split: split_indicator intro!: nn_integral_cong)
      also have "\<dots> \<le> N (X - Y) + N (X \<inter> Y)"
        using G_D[OF \<open>f \<in> G\<close>] by (intro add_mono Y1) (auto simp: emeasure_density)
      also have "\<dots> = N X"
        by (subst plus_emeasure) (auto intro!: arg_cong2[where f=emeasure])
      finally show "(\<integral>\<^sup>+ x. ?f' x * indicator X x \<partial>M) \<le> N X" .
    qed simp
    then have "nn_integral M ?f' \<le> ?y"
      by (rule SUP_upper)
    ultimately show False
      by (simp add: int_f_eq_y)
  qed
  show ?thesis
  proof (intro bexI[of _ f] measure_eqI conjI antisym)
    fix A assume "A \<in> sets (density M f)" then show "emeasure (density M f) A \<le> emeasure N A"
      by (auto simp: emeasure_density intro!: G_D[OF \<open>f \<in> G\<close>])
  next
    fix A assume A: "A \<in> sets (density M f)" then show "emeasure N A \<le> emeasure (density M f) A"
      using upper_bound by auto
  qed auto
qed

lemma (in finite_measure) split_space_into_finite_sets_and_rest:
  assumes ac: "absolutely_continuous M N" and sets_eq[simp]: "sets N = sets M"
  shows "\<exists>B::nat\<Rightarrow>'a set. disjoint_family B \<and> range B \<subseteq> sets M \<and> (\<forall>i. N (B i) \<noteq> \<infinity>) \<and>
    (\<forall>A\<in>sets M. A \<inter> (\<Union>i. B i) = {} \<longrightarrow> (emeasure M A = 0 \<and> N A = 0) \<or> (emeasure M A > 0 \<and> N A = \<infinity>))"
proof -
  let ?Q = "{Q\<in>sets M. N Q \<noteq> \<infinity>}"
  let ?a = "SUP Q\<in>?Q. emeasure M Q"
  have "{} \<in> ?Q" by auto
  then have Q_not_empty: "?Q \<noteq> {}" by blast
  have "?a \<le> emeasure M (space M)" using sets.sets_into_space
    by (auto intro!: SUP_least emeasure_mono)
  then have "?a \<noteq> \<infinity>"
    using finite_emeasure_space
    by (auto simp: less_top[symmetric] top_unique simp del: SUP_eq_top_iff Sup_eq_top_iff)
  from ennreal_SUP_countable_SUP [OF Q_not_empty, of "emeasure M"]
  obtain Q'' where "range Q'' \<subseteq> emeasure M ` ?Q" and a: "?a = (SUP i::nat. Q'' i)"
    by auto
  then have "\<forall>i. \<exists>Q'. Q'' i = emeasure M Q' \<and> Q' \<in> ?Q" by auto
  from choice[OF this] obtain Q' where Q': "\<And>i. Q'' i = emeasure M (Q' i)" "\<And>i. Q' i \<in> ?Q"
    by auto
  then have a_Lim: "?a = (SUP i. emeasure M (Q' i))" using a by simp
  let ?O = "\<lambda>n. \<Union>i\<le>n. Q' i"
  have Union: "(SUP i. emeasure M (?O i)) = emeasure M (\<Union>i. ?O i)"
  proof (rule SUP_emeasure_incseq[of ?O])
    show "range ?O \<subseteq> sets M" using Q' by auto
    show "incseq ?O" by (fastforce intro!: incseq_SucI)
  qed
  have Q'_sets[measurable]: "\<And>i. Q' i \<in> sets M" using Q' by auto
  have O_sets: "\<And>i. ?O i \<in> sets M" using Q' by auto
  then have O_in_G: "\<And>i. ?O i \<in> ?Q"
  proof (safe del: notI)
    fix i have "Q' ` {..i} \<subseteq> sets M" using Q' by auto
    then have "N (?O i) \<le> (\<Sum>i\<le>i. N (Q' i))"
      by (simp add: emeasure_subadditive_finite)
    also have "\<dots> < \<infinity>" using Q' by (simp add: less_top)
    finally show "N (?O i) \<noteq> \<infinity>" by simp
  qed auto
  have O_mono: "\<And>n. ?O n \<subseteq> ?O (Suc n)" by fastforce
  have a_eq: "?a = emeasure M (\<Union>i. ?O i)" unfolding Union[symmetric]
  proof (rule antisym)
    show "?a \<le> (SUP i. emeasure M (?O i))" unfolding a_Lim
      using Q' by (auto intro!: SUP_mono emeasure_mono)
    show "(SUP i. emeasure M (?O i)) \<le> ?a"
    proof (safe intro!: Sup_mono, unfold bex_simps)
      fix i
      have *: "(\<Union>(Q' ` {..i})) = ?O i" by auto
      then show "\<exists>x. (x \<in> sets M \<and> N x \<noteq> \<infinity>) \<and>
        emeasure M (\<Union>(Q' ` {..i})) \<le> emeasure M x"
        using O_in_G[of i] by (auto intro!: exI[of _ "?O i"])
    qed
  qed
  let ?O_0 = "(\<Union>i. ?O i)"
  have "?O_0 \<in> sets M" using Q' by auto
  have "disjointed Q' i \<in> sets M" for i
    using sets.range_disjointed_sets[of Q' M] using Q'_sets by (auto simp: subset_eq)
  note Q_sets = this
  show ?thesis
  proof (intro bexI exI conjI ballI impI allI)
    show "disjoint_family (disjointed Q')"
      by (rule disjoint_family_disjointed)
    show "range (disjointed Q') \<subseteq> sets M"
      using Q'_sets by (intro sets.range_disjointed_sets) auto
    { fix A assume A: "A \<in> sets M" "A \<inter> (\<Union>i. disjointed Q' i) = {}"
      then have A1: "A \<inter> (\<Union>i. Q' i) = {}"
        unfolding UN_disjointed_eq by auto
      show "emeasure M A = 0 \<and> N A = 0 \<or> 0 < emeasure M A \<and> N A = \<infinity>"
      proof (rule disjCI, simp)
        assume *: "emeasure M A = 0 \<or> N A \<noteq> top"
        show "emeasure M A = 0 \<and> N A = 0"
        proof (cases "emeasure M A = 0")
          case True
          with ac A have "N A = 0"
            unfolding absolutely_continuous_def by auto
          with True show ?thesis by simp
        next
          case False
          with * have "N A \<noteq> \<infinity>" by auto
          with A have "emeasure M ?O_0 + emeasure M A = emeasure M (?O_0 \<union> A)"
            using Q' A1 by (auto intro!: plus_emeasure simp: set_eq_iff)
          also have "\<dots> = (SUP i. emeasure M (?O i \<union> A))"
          proof (rule SUP_emeasure_incseq[of "\<lambda>i. ?O i \<union> A", symmetric, simplified])
            show "range (\<lambda>i. ?O i \<union> A) \<subseteq> sets M"
              using \<open>N A \<noteq> \<infinity>\<close> O_sets A by auto
          qed (fastforce intro!: incseq_SucI)
          also have "\<dots> \<le> ?a"
          proof (safe intro!: SUP_least)
            fix i have "?O i \<union> A \<in> ?Q"
            proof (safe del: notI)
              show "?O i \<union> A \<in> sets M" using O_sets A by auto
              from O_in_G[of i] have "N (?O i \<union> A) \<le> N (?O i) + N A"
                using emeasure_subadditive[of "?O i" N A] A O_sets by auto
              with O_in_G[of i] show "N (?O i \<union> A) \<noteq> \<infinity>"
                using \<open>N A \<noteq> \<infinity>\<close> by (auto simp: top_unique)
            qed
            then show "emeasure M (?O i \<union> A) \<le> ?a" by (rule SUP_upper)
          qed
          finally have "emeasure M A = 0"
            unfolding a_eq using measure_nonneg[of M A] by (simp add: emeasure_eq_measure)
          with \<open>emeasure M A \<noteq> 0\<close> show ?thesis by auto
        qed
      qed }
    { fix i
      have "N (disjointed Q' i) \<le> N (Q' i)"
        by (auto intro!: emeasure_mono simp: disjointed_def)
      then show "N (disjointed Q' i) \<noteq> \<infinity>"
        using Q'(2)[of i] by (auto simp: top_unique) }
  qed
qed

proposition (in finite_measure) Radon_Nikodym_finite_measure_infinite:
  assumes "absolutely_continuous M N" and sets_eq: "sets N = sets M"
  shows "\<exists>f\<in>borel_measurable M. density M f = N"
proof -
  from split_space_into_finite_sets_and_rest[OF assms]
  obtain Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<inter> (\<Union>i. Q i) = {} \<Longrightarrow> emeasure M A = 0 \<and> N A = 0 \<or> 0 < emeasure M A \<and> N A = \<infinity>"
    and Q_fin: "\<And>i. N (Q i) \<noteq> \<infinity>" by force
  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  let ?N = "\<lambda>i. density N (indicator (Q i))" and ?M = "\<lambda>i. density M (indicator (Q i))"
  have "\<forall>i. \<exists>f\<in>borel_measurable (?M i). density (?M i) f = ?N i"
  proof (intro allI finite_measure.Radon_Nikodym_finite_measure)
    fix i
    from Q show "finite_measure (?M i)"
      by (auto intro!: finite_measureI cong: nn_integral_cong
               simp add: emeasure_density subset_eq sets_eq)
    from Q have "emeasure (?N i) (space N) = emeasure N (Q i)"
      by (simp add: sets_eq[symmetric] emeasure_density subset_eq cong: nn_integral_cong)
    with Q_fin show "finite_measure (?N i)"
      by (auto intro!: finite_measureI)
    show "sets (?N i) = sets (?M i)" by (simp add: sets_eq)
    have [measurable]: "\<And>A. A \<in> sets M \<Longrightarrow> A \<in> sets N" by (simp add: sets_eq)
    show "absolutely_continuous (?M i) (?N i)"
      using \<open>absolutely_continuous M N\<close> \<open>Q i \<in> sets M\<close>
      by (auto simp: absolutely_continuous_def null_sets_density_iff sets_eq
               intro!: absolutely_continuous_AE[OF sets_eq])
  qed
  from choice[OF this[unfolded Bex_def]]
  obtain f where borel: "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
    and f_density: "\<And>i. density (?M i) (f i) = ?N i"
    by force
  { fix A i assume A: "A \<in> sets M"
    with Q borel have "(\<integral>\<^sup>+x. f i x * indicator (Q i \<inter> A) x \<partial>M) = emeasure (density (?M i) (f i)) A"
      by (auto simp add: emeasure_density nn_integral_density subset_eq
               intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> = emeasure N (Q i \<inter> A)"
      using A Q by (simp add: f_density emeasure_restricted subset_eq sets_eq)
    finally have "emeasure N (Q i \<inter> A) = (\<integral>\<^sup>+x. f i x * indicator (Q i \<inter> A) x \<partial>M)" .. }
  note integral_eq = this
  let ?f = "\<lambda>x. (\<Sum>i. f i x * indicator (Q i) x) + \<infinity> * indicator (space M - (\<Union>i. Q i)) x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?f])
    show "?f \<in> borel_measurable M" using borel Q_sets
      by (auto intro!: measurable_If)
    show "density M ?f = N"
    proof (rule measure_eqI)
      fix A assume "A \<in> sets (density M ?f)"
      then have "A \<in> sets M" by simp
      have Qi: "\<And>i. Q i \<in> sets M" using Q by auto
      have [intro,simp]: "\<And>i. (\<lambda>x. f i x * indicator (Q i \<inter> A) x) \<in> borel_measurable M"
        "\<And>i. AE x in M. 0 \<le> f i x * indicator (Q i \<inter> A) x"
        using borel Qi \<open>A \<in> sets M\<close> by auto
      have "(\<integral>\<^sup>+x. ?f x * indicator A x \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>i. f i x * indicator (Q i \<inter> A) x) + \<infinity> * indicator ((space M - (\<Union>i. Q i)) \<inter> A) x \<partial>M)"
        using borel by (intro nn_integral_cong) (auto simp: indicator_def)
      also have "\<dots> = (\<integral>\<^sup>+x. (\<Sum>i. f i x * indicator (Q i \<inter> A) x) \<partial>M) + \<infinity> * emeasure M ((space M - (\<Union>i. Q i)) \<inter> A)"
        using borel Qi \<open>A \<in> sets M\<close>
        by (subst nn_integral_add)
           (auto simp add: nn_integral_cmult_indicator sets.Int intro!: suminf_0_le)
      also have "\<dots> = (\<Sum>i. N (Q i \<inter> A)) + \<infinity> * emeasure M ((space M - (\<Union>i. Q i)) \<inter> A)"
        by (subst integral_eq[OF \<open>A \<in> sets M\<close>], subst nn_integral_suminf) auto
      finally have "(\<integral>\<^sup>+x. ?f x * indicator A x \<partial>M) = (\<Sum>i. N (Q i \<inter> A)) + \<infinity> * emeasure M ((space M - (\<Union>i. Q i)) \<inter> A)" .
      moreover have "(\<Sum>i. N (Q i \<inter> A)) = N ((\<Union>i. Q i) \<inter> A)"
        using Q Q_sets \<open>A \<in> sets M\<close>
        by (subst suminf_emeasure) (auto simp: disjoint_family_on_def sets_eq)
      moreover
      have "(space M - (\<Union>x. Q x)) \<inter> A \<inter> (\<Union>x. Q x) = {}"
        by auto
      then have "\<infinity> * emeasure M ((space M - (\<Union>i. Q i)) \<inter> A) = N ((space M - (\<Union>i. Q i)) \<inter> A)"
        using in_Q0[of "(space M - (\<Union>i. Q i)) \<inter> A"] \<open>A \<in> sets M\<close> Q by (auto simp: ennreal_top_mult)
      moreover have "(space M - (\<Union>i. Q i)) \<inter> A \<in> sets M" "((\<Union>i. Q i) \<inter> A) \<in> sets M"
        using Q_sets \<open>A \<in> sets M\<close> by auto
      moreover have "((\<Union>i. Q i) \<inter> A) \<union> ((space M - (\<Union>i. Q i)) \<inter> A) = A" "((\<Union>i. Q i) \<inter> A) \<inter> ((space M - (\<Union>i. Q i)) \<inter> A) = {}"
        using \<open>A \<in> sets M\<close> sets.sets_into_space by auto
      ultimately have "N A = (\<integral>\<^sup>+x. ?f x * indicator A x \<partial>M)"
        using plus_emeasure[of "(\<Union>i. Q i) \<inter> A" N "(space M - (\<Union>i. Q i)) \<inter> A"] by (simp add: sets_eq)
      with \<open>A \<in> sets M\<close> borel Q show "emeasure (density M ?f) A = N A"
        by (auto simp: subset_eq emeasure_density)
    qed (simp add: sets_eq)
  qed
qed

theorem (in sigma_finite_measure) Radon_Nikodym:
  assumes ac: "absolutely_continuous M N" assumes sets_eq: "sets N = sets M"
  shows "\<exists>f \<in> borel_measurable M. density M f = N"
proof -
  from Ex_finite_integrable_function
  obtain h where finite: "integral\<^sup>N M h \<noteq> \<infinity>" and
    borel: "h \<in> borel_measurable M" and
    nn: "\<And>x. 0 \<le> h x" and
    pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x" and
    "\<And>x. x \<in> space M \<Longrightarrow> h x < \<infinity>" by auto
  let ?T = "\<lambda>A. (\<integral>\<^sup>+x. h x * indicator A x \<partial>M)"
  let ?MT = "density M h"
  from borel finite nn interpret T: finite_measure ?MT
    by (auto intro!: finite_measureI cong: nn_integral_cong simp: emeasure_density)
  have "absolutely_continuous ?MT N" "sets N = sets ?MT"
  proof (unfold absolutely_continuous_def, safe)
    fix A assume "A \<in> null_sets ?MT"
    with borel have "A \<in> sets M" "AE x in M. x \<in> A \<longrightarrow> h x \<le> 0"
      by (auto simp add: null_sets_density_iff)
    with pos sets.sets_into_space have "AE x in M. x \<notin> A"
      by (elim eventually_mono) (auto simp: not_le[symmetric])
    then have "A \<in> null_sets M"
      using \<open>A \<in> sets M\<close> by (simp add: AE_iff_null_sets)
    with ac show "A \<in> null_sets N"
      by (auto simp: absolutely_continuous_def)
  qed (auto simp add: sets_eq)
  from T.Radon_Nikodym_finite_measure_infinite[OF this]
  obtain f where f_borel: "f \<in> borel_measurable M" "density ?MT f = N" by auto
  with nn borel show ?thesis
    by (auto intro!: bexI[of _ "\<lambda>x. h x * f x"] simp: density_density_eq)
qed

subsection \<open>Uniqueness of densities\<close>

lemma finite_density_unique:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes pos: "AE x in M. 0 \<le> f x" "AE x in M. 0 \<le> g x"
  and fin: "integral\<^sup>N M f \<noteq> \<infinity>"
  shows "density M f = density M g \<longleftrightarrow> (AE x in M. f x = g x)"
proof (intro iffI ballI)
  fix A assume eq: "AE x in M. f x = g x"
  with borel show "density M f = density M g"
    by (auto intro: density_cong)
next
  let ?P = "\<lambda>f A. \<integral>\<^sup>+ x. f x * indicator A x \<partial>M"
  assume "density M f = density M g"
  with borel have eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
    by (simp add: emeasure_density[symmetric])
  from this[THEN bspec, OF sets.top] fin
  have g_fin: "integral\<^sup>N M g \<noteq> \<infinity>" by (simp cong: nn_integral_cong)
  { fix f g assume borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
      and pos: "AE x in M. 0 \<le> f x" "AE x in M. 0 \<le> g x"
      and g_fin: "integral\<^sup>N M g \<noteq> \<infinity>" and eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
    let ?N = "{x\<in>space M. g x < f x}"
    have N: "?N \<in> sets M" using borel by simp
    have "?P g ?N \<le> integral\<^sup>N M g" using pos
      by (intro nn_integral_mono_AE) (auto split: split_indicator)
    then have Pg_fin: "?P g ?N \<noteq> \<infinity>" using g_fin by (auto simp: top_unique)
    have "?P (\<lambda>x. (f x - g x)) ?N = (\<integral>\<^sup>+x. f x * indicator ?N x - g x * indicator ?N x \<partial>M)"
      by (auto intro!: nn_integral_cong simp: indicator_def)
    also have "\<dots> = ?P f ?N - ?P g ?N"
    proof (rule nn_integral_diff)
      show "(\<lambda>x. f x * indicator ?N x) \<in> borel_measurable M" "(\<lambda>x. g x * indicator ?N x) \<in> borel_measurable M"
        using borel N by auto
      show "AE x in M. g x * indicator ?N x \<le> f x * indicator ?N x"
        using pos by (auto split: split_indicator)
    qed fact
    also have "\<dots> = 0"
      unfolding eq[THEN bspec, OF N] using Pg_fin by auto
    finally have "AE x in M. f x \<le> g x"
      using pos borel nn_integral_PInf_AE[OF borel(2) g_fin]
      by (subst (asm) nn_integral_0_iff_AE)
         (auto split: split_indicator simp: not_less ennreal_minus_eq_0) }
  from this[OF borel pos g_fin eq] this[OF borel(2,1) pos(2,1) fin] eq
  show "AE x in M. f x = g x" by auto
qed

lemma (in finite_measure) density_unique_finite_measure:
  assumes borel: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes pos: "AE x in M. 0 \<le> f x" "AE x in M. 0 \<le> f' x"
  assumes f: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^sup>+x. f' x * indicator A x \<partial>M)"
    (is "\<And>A. A \<in> sets M \<Longrightarrow> ?P f A = ?P f' A")
  shows "AE x in M. f x = f' x"
proof -
  let ?D = "\<lambda>f. density M f"
  let ?N = "\<lambda>A. ?P f A" and ?N' = "\<lambda>A. ?P f' A"
  let ?f = "\<lambda>A x. f x * indicator A x" and ?f' = "\<lambda>A x. f' x * indicator A x"

  have ac: "absolutely_continuous M (density M f)" "sets (density M f) = sets M"
    using borel by (auto intro!: absolutely_continuousI_density)
  from split_space_into_finite_sets_and_rest[OF this]
  obtain Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<inter> (\<Union>i. Q i) = {} \<Longrightarrow> emeasure M A = 0 \<and> ?D f A = 0 \<or> 0 < emeasure M A \<and> ?D f A = \<infinity>"
    and Q_fin: "\<And>i. ?D f (Q i) \<noteq> \<infinity>" by force
  with borel pos have in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<inter> (\<Union>i. Q i) = {} \<Longrightarrow> emeasure M A = 0 \<and> ?N A = 0 \<or> 0 < emeasure M A \<and> ?N A = \<infinity>"
    and Q_fin: "\<And>i. ?N (Q i) \<noteq> \<infinity>" by (auto simp: emeasure_density subset_eq)

  from Q have Q_sets[measurable]: "\<And>i. Q i \<in> sets M" by auto
  let ?D = "{x\<in>space M. f x \<noteq> f' x}"
  have "?D \<in> sets M" using borel by auto
  have *: "\<And>i x A. \<And>y::ennreal. y * indicator (Q i) x * indicator A x = y * indicator (Q i \<inter> A) x"
    unfolding indicator_def by auto
  have "\<forall>i. AE x in M. ?f (Q i) x = ?f' (Q i) x" using borel Q_fin Q pos
    by (intro finite_density_unique[THEN iffD1] allI)
       (auto intro!: f measure_eqI simp: emeasure_density * subset_eq)
  moreover have "AE x in M. ?f (space M - (\<Union>i. Q i)) x = ?f' (space M - (\<Union>i. Q i)) x"
  proof (rule AE_I')
    { fix f :: "'a \<Rightarrow> ennreal" assume borel: "f \<in> borel_measurable M"
        and eq: "\<And>A. A \<in> sets M \<Longrightarrow> ?N A = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M)"
      let ?A = "\<lambda>i. (space M - (\<Union>i. Q i)) \<inter> {x \<in> space M. f x < (i::nat)}"
      have "(\<Union>i. ?A i) \<in> null_sets M"
      proof (rule null_sets_UN)
        fix i ::nat have "?A i \<in> sets M"
          using borel by auto
        have "?N (?A i) \<le> (\<integral>\<^sup>+x. (i::ennreal) * indicator (?A i) x \<partial>M)"
          unfolding eq[OF \<open>?A i \<in> sets M\<close>]
          by (auto intro!: nn_integral_mono simp: indicator_def)
        also have "\<dots> = i * emeasure M (?A i)"
          using \<open>?A i \<in> sets M\<close> by (auto intro!: nn_integral_cmult_indicator)
        also have "\<dots> < \<infinity>" using emeasure_real[of "?A i"] by (auto simp: ennreal_mult_less_top of_nat_less_top)
        finally have "?N (?A i) \<noteq> \<infinity>" by simp
        then show "?A i \<in> null_sets M" using in_Q0[OF \<open>?A i \<in> sets M\<close>] \<open>?A i \<in> sets M\<close> by auto
      qed
      also have "(\<Union>i. ?A i) = (space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f x \<noteq> \<infinity>}"
        by (auto simp: ennreal_Ex_less_of_nat less_top[symmetric])
      finally have "(space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f x \<noteq> \<infinity>} \<in> null_sets M" by simp }
    from this[OF borel(1) refl] this[OF borel(2) f]
    have "(space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f x \<noteq> \<infinity>} \<in> null_sets M" "(space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f' x \<noteq> \<infinity>} \<in> null_sets M" by simp_all
    then show "((space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f x \<noteq> \<infinity>}) \<union> ((space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f' x \<noteq> \<infinity>}) \<in> null_sets M" by (rule null_sets.Un)
    show "{x \<in> space M. ?f (space M - (\<Union>i. Q i)) x \<noteq> ?f' (space M - (\<Union>i. Q i)) x} \<subseteq>
      ((space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f x \<noteq> \<infinity>}) \<union> ((space M - (\<Union>i. Q i)) \<inter> {x\<in>space M. f' x \<noteq> \<infinity>})" by (auto simp: indicator_def)
  qed
  moreover have "AE x in M. (?f (space M - (\<Union>i. Q i)) x = ?f' (space M - (\<Union>i. Q i)) x) \<longrightarrow> (\<forall>i. ?f (Q i) x = ?f' (Q i) x) \<longrightarrow>
    ?f (space M) x = ?f' (space M) x"
    by (auto simp: indicator_def)
  ultimately have "AE x in M. ?f (space M) x = ?f' (space M) x"
    unfolding AE_all_countable[symmetric]
    by eventually_elim (auto split: if_split_asm simp: indicator_def)
  then show "AE x in M. f x = f' x" by auto
qed

proposition (in sigma_finite_measure) density_unique:
  assumes f: "f \<in> borel_measurable M"
  assumes f': "f' \<in> borel_measurable M"
  assumes density_eq: "density M f = density M f'"
  shows "AE x in M. f x = f' x"
proof -
  obtain h where h_borel: "h \<in> borel_measurable M"
    and fin: "integral\<^sup>N M h \<noteq> \<infinity>" and pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x \<and> h x < \<infinity>" "\<And>x. 0 \<le> h x"
    using Ex_finite_integrable_function by auto
  then have h_nn: "AE x in M. 0 \<le> h x" by auto
  let ?H = "density M h"
  interpret h: finite_measure ?H
    using fin h_borel pos
    by (intro finite_measureI) (simp cong: nn_integral_cong emeasure_density add: fin)
  let ?fM = "density M f"
  let ?f'M = "density M f'"
  { fix A assume "A \<in> sets M"
    then have "{x \<in> space M. h x * indicator A x \<noteq> 0} = A"
      using pos(1) sets.sets_into_space by (force simp: indicator_def)
    then have "(\<integral>\<^sup>+x. h x * indicator A x \<partial>M) = 0 \<longleftrightarrow> A \<in> null_sets M"
      using h_borel \<open>A \<in> sets M\<close> h_nn by (subst nn_integral_0_iff) auto }
  note h_null_sets = this
  { fix A assume "A \<in> sets M"
    have "(\<integral>\<^sup>+x. f x * (h x * indicator A x) \<partial>M) = (\<integral>\<^sup>+x. h x * indicator A x \<partial>?fM)"
      using \<open>A \<in> sets M\<close> h_borel h_nn f f'
      by (intro nn_integral_density[symmetric]) auto
    also have "\<dots> = (\<integral>\<^sup>+x. h x * indicator A x \<partial>?f'M)"
      by (simp_all add: density_eq)
    also have "\<dots> = (\<integral>\<^sup>+x. f' x * (h x * indicator A x) \<partial>M)"
      using \<open>A \<in> sets M\<close> h_borel h_nn f f'
      by (intro nn_integral_density) auto
    finally have "(\<integral>\<^sup>+x. h x * (f x * indicator A x) \<partial>M) = (\<integral>\<^sup>+x. h x * (f' x * indicator A x) \<partial>M)"
      by (simp add: ac_simps)
    then have "(\<integral>\<^sup>+x. (f x * indicator A x) \<partial>?H) = (\<integral>\<^sup>+x. (f' x * indicator A x) \<partial>?H)"
      using \<open>A \<in> sets M\<close> h_borel h_nn f f'
      by (subst (asm) (1 2) nn_integral_density[symmetric]) auto }
  then have "AE x in ?H. f x = f' x" using h_borel h_nn f f'
    by (intro h.density_unique_finite_measure absolutely_continuous_AE[of M]) auto
  with AE_space[of M] pos show "AE x in M. f x = f' x"
    unfolding AE_density[OF h_borel] by auto
qed

lemma (in sigma_finite_measure) density_unique_iff:
  assumes f: "f \<in> borel_measurable M" and f': "f' \<in> borel_measurable M"
  shows "density M f = density M f' \<longleftrightarrow> (AE x in M. f x = f' x)"
  using density_unique[OF assms] density_cong[OF f f'] by auto

lemma sigma_finite_density_unique:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  and fin: "sigma_finite_measure (density M f)"
  shows "density M f = density M g \<longleftrightarrow> (AE x in M. f x = g x)"
proof
  assume "AE x in M. f x = g x" with borel show "density M f = density M g"
    by (auto intro: density_cong)
next
  assume eq: "density M f = density M g"
  interpret f: sigma_finite_measure "density M f" by fact
  from f.sigma_finite_incseq obtain A where cover: "range A \<subseteq> sets (density M f)"
    "\<Union> (range A) = space (density M f)"
    "\<And>i. emeasure (density M f) (A i) \<noteq> \<infinity>"
    "incseq A"
    by auto
  have "AE x in M. \<forall>i. x \<in> A i \<longrightarrow> f x = g x"
    unfolding AE_all_countable
  proof
    fix i
    have "density (density M f) (indicator (A i)) = density (density M g) (indicator (A i))"
      unfolding eq ..
    moreover have "(\<integral>\<^sup>+x. f x * indicator (A i) x \<partial>M) \<noteq> \<infinity>"
      using cover(1) cover(3)[of i] borel by (auto simp: emeasure_density subset_eq)
    ultimately have "AE x in M. f x * indicator (A i) x = g x * indicator (A i) x"
      using borel cover(1)
      by (intro finite_density_unique[THEN iffD1]) (auto simp: density_density_eq subset_eq)
    then show "AE x in M. x \<in> A i \<longrightarrow> f x = g x"
      by auto
  qed
  with AE_space show "AE x in M. f x = g x"
    apply eventually_elim
    using cover(2)[symmetric]
    apply auto
    done
qed

lemma (in sigma_finite_measure) sigma_finite_iff_density_finite':
  assumes f: "f \<in> borel_measurable M"
  shows "sigma_finite_measure (density M f) \<longleftrightarrow> (AE x in M. f x \<noteq> \<infinity>)"
    (is "sigma_finite_measure ?N \<longleftrightarrow> _")
proof
  assume "sigma_finite_measure ?N"
  then interpret N: sigma_finite_measure ?N .
  from N.Ex_finite_integrable_function obtain h where
    h: "h \<in> borel_measurable M" "integral\<^sup>N ?N h \<noteq> \<infinity>" and
    fin: "\<forall>x\<in>space M. 0 < h x \<and> h x < \<infinity>"
    by auto
  have "AE x in M. f x * h x \<noteq> \<infinity>"
  proof (rule AE_I')
    have "integral\<^sup>N ?N h = (\<integral>\<^sup>+x. f x * h x \<partial>M)"
      using f h by (auto intro!: nn_integral_density)
    then have "(\<integral>\<^sup>+x. f x * h x \<partial>M) \<noteq> \<infinity>"
      using h(2) by simp
    then show "(\<lambda>x. f x * h x) -` {\<infinity>} \<inter> space M \<in> null_sets M"
      using f h(1) by (auto intro!: nn_integral_PInf[unfolded infinity_ennreal_def] borel_measurable_vimage)
  qed auto
  then show "AE x in M. f x \<noteq> \<infinity>"
    using fin by (auto elim!: AE_Ball_mp simp: less_top ennreal_mult_less_top)
next
  assume AE: "AE x in M. f x \<noteq> \<infinity>"
  from sigma_finite obtain Q :: "nat \<Rightarrow> 'a set"
    where Q: "range Q \<subseteq> sets M" "\<Union> (range Q) = space M" "\<And>i. emeasure M (Q i) \<noteq> \<infinity>"
    by auto
  define A where "A i =
    f -` (case i of 0 \<Rightarrow> {\<infinity>} | Suc n \<Rightarrow> {.. ennreal(of_nat (Suc n))}) \<inter> space M" for i
  { fix i j have "A i \<inter> Q j \<in> sets M"
    unfolding A_def using f Q
    apply (rule_tac sets.Int)
    by (cases i) (auto intro: measurable_sets[OF f(1)]) }
  note A_in_sets = this

  show "sigma_finite_measure ?N"
  proof (standard, intro exI conjI ballI)
    show "countable (range (\<lambda>(i, j). A i \<inter> Q j))"
      by auto
    show "range (\<lambda>(i, j). A i \<inter> Q j) \<subseteq> sets (density M f)"
      using A_in_sets by auto
  next
    have "\<Union>(range (\<lambda>(i, j). A i \<inter> Q j)) = (\<Union>i j. A i \<inter> Q j)"
      by auto
    also have "\<dots> = (\<Union>i. A i) \<inter> space M" using Q by auto
    also have "(\<Union>i. A i) = space M"
    proof safe
      fix x assume x: "x \<in> space M"
      show "x \<in> (\<Union>i. A i)"
      proof (cases "f x" rule: ennreal_cases)
        case top with x show ?thesis unfolding A_def by (auto intro: exI[of _ 0])
      next
        case (real r)
        with ennreal_Ex_less_of_nat[of "f x"] obtain n :: nat where "f x < n"
          by auto
        also have "n < (Suc n :: ennreal)"
          by simp
        finally show ?thesis
          using x real by (auto simp: A_def ennreal_of_nat_eq_real_of_nat intro!: exI[of _ "Suc n"])
      qed
    qed (auto simp: A_def)
    finally show "\<Union>(range (\<lambda>(i, j). A i \<inter> Q j)) = space ?N" by simp
  next
    fix X assume "X \<in> range (\<lambda>(i, j). A i \<inter> Q j)"
    then obtain i j where [simp]:"X = A i \<inter> Q j" by auto
    have "(\<integral>\<^sup>+x. f x * indicator (A i \<inter> Q j) x \<partial>M) \<noteq> \<infinity>"
    proof (cases i)
      case 0
      have "AE x in M. f x * indicator (A i \<inter> Q j) x = 0"
        using AE by (auto simp: A_def \<open>i = 0\<close>)
      from nn_integral_cong_AE[OF this] show ?thesis by simp
    next
      case (Suc n)
      then have "(\<integral>\<^sup>+x. f x * indicator (A i \<inter> Q j) x \<partial>M) \<le>
        (\<integral>\<^sup>+x. (Suc n :: ennreal) * indicator (Q j) x \<partial>M)"
        by (auto intro!: nn_integral_mono simp: indicator_def A_def ennreal_of_nat_eq_real_of_nat)
      also have "\<dots> = Suc n * emeasure M (Q j)"
        using Q by (auto intro!: nn_integral_cmult_indicator)
      also have "\<dots> < \<infinity>"
        using Q by (auto simp: ennreal_mult_less_top less_top of_nat_less_top)
      finally show ?thesis by simp
    qed
    then show "emeasure ?N X \<noteq> \<infinity>"
      using A_in_sets Q f by (auto simp: emeasure_density)
  qed
qed

lemma (in sigma_finite_measure) sigma_finite_iff_density_finite:
  "f \<in> borel_measurable M \<Longrightarrow> sigma_finite_measure (density M f) \<longleftrightarrow> (AE x in M. f x \<noteq> \<infinity>)"
  by (subst sigma_finite_iff_density_finite')
     (auto simp: max_def intro!: measurable_If)

subsection \<open>Radon-Nikodym derivative\<close>

definition\<^marker>\<open>tag important\<close> RN_deriv :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a \<Rightarrow> ennreal" where
  "RN_deriv M N =
    (if \<exists>f. f \<in> borel_measurable M \<and> density M f = N
       then SOME f. f \<in> borel_measurable M \<and> density M f = N
       else (\<lambda>_. 0))"

lemma RN_derivI:
  assumes "f \<in> borel_measurable M" "density M f = N"
  shows "density M (RN_deriv M N) = N"
proof -
  have *: "\<exists>f. f \<in> borel_measurable M \<and> density M f = N"
    using assms by auto
  then have "density M (SOME f. f \<in> borel_measurable M \<and> density M f = N) = N"
    by (rule someI2_ex) auto
  with * show ?thesis
    by (auto simp: RN_deriv_def)
qed

lemma borel_measurable_RN_deriv[measurable]: "RN_deriv M N \<in> borel_measurable M"
proof -
  { assume ex: "\<exists>f. f \<in> borel_measurable M \<and> density M f = N"
    have 1: "(SOME f. f \<in> borel_measurable M \<and> density M f = N) \<in> borel_measurable M"
      using ex by (rule someI2_ex) auto }
  from this show ?thesis
    by (auto simp: RN_deriv_def)
qed

lemma density_RN_deriv_density:
  assumes f: "f \<in> borel_measurable M"
  shows "density M (RN_deriv M (density M f)) = density M f"
  by (rule RN_derivI[OF f]) simp

lemma (in sigma_finite_measure) density_RN_deriv:
  "absolutely_continuous M N \<Longrightarrow> sets N = sets M \<Longrightarrow> density M (RN_deriv M N) = N"
  by (metis RN_derivI Radon_Nikodym)

lemma (in sigma_finite_measure) RN_deriv_nn_integral:
  assumes N: "absolutely_continuous M N" "sets N = sets M"
    and f: "f \<in> borel_measurable M"
  shows "integral\<^sup>N N f = (\<integral>\<^sup>+x. RN_deriv M N x * f x \<partial>M)"
proof -
  have "integral\<^sup>N N f = integral\<^sup>N (density M (RN_deriv M N)) f"
    using N by (simp add: density_RN_deriv)
  also have "\<dots> = (\<integral>\<^sup>+x. RN_deriv M N x * f x \<partial>M)"
    using f by (simp add: nn_integral_density)
  finally show ?thesis by simp
qed

lemma (in sigma_finite_measure) RN_deriv_unique:
  assumes f: "f \<in> borel_measurable M"
  and eq: "density M f = N"
  shows "AE x in M. f x = RN_deriv M N x"
  unfolding eq[symmetric]
  by (intro density_unique_iff[THEN iffD1] f borel_measurable_RN_deriv
            density_RN_deriv_density[symmetric])

lemma RN_deriv_unique_sigma_finite:
  assumes f: "f \<in> borel_measurable M"
  and eq: "density M f = N" and fin: "sigma_finite_measure N"
  shows "AE x in M. f x = RN_deriv M N x"
  using fin unfolding eq[symmetric]
  by (intro sigma_finite_density_unique[THEN iffD1] f borel_measurable_RN_deriv
            density_RN_deriv_density[symmetric])

lemma (in sigma_finite_measure) RN_deriv_distr:
  fixes T :: "'a \<Rightarrow> 'b"
  assumes T: "T \<in> measurable M M'" and T': "T' \<in> measurable M' M"
    and inv: "\<forall>x\<in>space M. T' (T x) = x"
  and ac[simp]: "absolutely_continuous (distr M M' T) (distr N M' T)"
  and N: "sets N = sets M"
  shows "AE x in M. RN_deriv (distr M M' T) (distr N M' T) (T x) = RN_deriv M N x"
proof (rule RN_deriv_unique)
  have [simp]: "sets N = sets M" by fact
  note sets_eq_imp_space_eq[OF N, simp]
  have measurable_N[simp]: "\<And>M'. measurable N M' = measurable M M'" by (auto simp: measurable_def)
  { fix A assume "A \<in> sets M"
    with inv T T' sets.sets_into_space[OF this]
    have "T -` T' -` A \<inter> T -` space M' \<inter> space M = A"
      by (auto simp: measurable_def) }
  note eq = this[simp]
  { fix A assume "A \<in> sets M"
    with inv T T' sets.sets_into_space[OF this]
    have "(T' \<circ> T) -` A \<inter> space M = A"
      by (auto simp: measurable_def) }
  note eq2 = this[simp]
  let ?M' = "distr M M' T" and ?N' = "distr N M' T"
  interpret M': sigma_finite_measure ?M'
  proof
    from sigma_finite_countable obtain F
      where F: "countable F \<and> F \<subseteq> sets M \<and> \<Union> F = space M \<and> (\<forall>a\<in>F. emeasure M a \<noteq> \<infinity>)" ..
    show "\<exists>A. countable A \<and> A \<subseteq> sets (distr M M' T) \<and> \<Union>A = space (distr M M' T) \<and> (\<forall>a\<in>A. emeasure (distr M M' T) a \<noteq> \<infinity>)"
    proof (intro exI conjI ballI)
      show *: "(\<lambda>A. T' -` A \<inter> space ?M') ` F \<subseteq> sets ?M'"
        using F T' by (auto simp: measurable_def)
      show "\<Union>((\<lambda>A. T' -` A \<inter> space ?M')`F) = space ?M'"
        using F T'[THEN measurable_space] by (auto simp: set_eq_iff)
    next
      fix X assume "X \<in> (\<lambda>A. T' -` A \<inter> space ?M')`F"
      then obtain A where [simp]: "X = T' -` A \<inter> space ?M'" and "A \<in> F" by auto
      have "X \<in> sets M'" using F T' \<open>A\<in>F\<close> by auto
      moreover
      have Fi: "A \<in> sets M" using F \<open>A\<in>F\<close> by auto
      ultimately show "emeasure ?M' X \<noteq> \<infinity>"
        using F T T' \<open>A\<in>F\<close> by (simp add: emeasure_distr)
    qed (use F in auto)
  qed
  have "(RN_deriv ?M' ?N') \<circ> T \<in> borel_measurable M"
    using T ac by measurable
  then show "(\<lambda>x. RN_deriv ?M' ?N' (T x)) \<in> borel_measurable M"
    by (simp add: comp_def)

  have "N = distr N M (T' \<circ> T)"
    by (subst measure_of_of_measure[of N, symmetric])
       (auto simp add: distr_def sets.sigma_sets_eq intro!: measure_of_eq sets.space_closed)
  also have "\<dots> = distr (distr N M' T) M T'"
    using T T' by (simp add: distr_distr)
  also have "\<dots> = distr (density (distr M M' T) (RN_deriv (distr M M' T) (distr N M' T))) M T'"
    using ac by (simp add: M'.density_RN_deriv)
  also have "\<dots> = density M (RN_deriv (distr M M' T) (distr N M' T) \<circ> T)"
    by (simp add: distr_density_distr[OF T T', OF inv])
  finally show "density M (\<lambda>x. RN_deriv (distr M M' T) (distr N M' T) (T x)) = N"
    by (simp add: comp_def)
qed

lemma (in sigma_finite_measure) RN_deriv_finite:
  assumes N: "sigma_finite_measure N" and ac: "absolutely_continuous M N" "sets N = sets M"
  shows "AE x in M. RN_deriv M N x \<noteq> \<infinity>"
proof -
  interpret N: sigma_finite_measure N by fact
  from N show ?thesis
    using sigma_finite_iff_density_finite[OF borel_measurable_RN_deriv, of N] density_RN_deriv[OF ac]
    by simp
qed

lemma (in sigma_finite_measure)
  assumes N: "sigma_finite_measure N" and ac: "absolutely_continuous M N" "sets N = sets M"
    and f: "f \<in> borel_measurable M"
  shows RN_deriv_integrable: "integrable N f \<longleftrightarrow>
      integrable M (\<lambda>x. enn2real (RN_deriv M N x) * f x)" (is ?integrable)
    and RN_deriv_integral: "integral\<^sup>L N f = (\<integral>x. enn2real (RN_deriv M N x) * f x \<partial>M)" (is ?integral)
proof -
  note ac(2)[simp] and sets_eq_imp_space_eq[OF ac(2), simp]
  interpret N: sigma_finite_measure N by fact

  have eq: "density M (RN_deriv M N) = density M (\<lambda>x. enn2real (RN_deriv M N x))"
  proof (rule density_cong)
    from RN_deriv_finite[OF assms(1,2,3)]
    show "AE x in M. RN_deriv M N x = ennreal (enn2real (RN_deriv M N x))"
      by eventually_elim (auto simp: less_top)
  qed (insert ac, auto)

  show ?integrable
    apply (subst density_RN_deriv[OF ac, symmetric])
    unfolding eq
    apply (intro integrable_real_density f AE_I2 enn2real_nonneg)
    apply (insert ac, auto)
    done

  show ?integral
    apply (subst density_RN_deriv[OF ac, symmetric])
    unfolding eq
    apply (intro integral_real_density f AE_I2 enn2real_nonneg)
    apply (insert ac, auto)
    done
qed

proposition (in sigma_finite_measure) real_RN_deriv:
  assumes "finite_measure N"
  assumes ac: "absolutely_continuous M N" "sets N = sets M"
  obtains D where "D \<in> borel_measurable M"
    and "AE x in M. RN_deriv M N x = ennreal (D x)"
    and "AE x in N. 0 < D x"
    and "\<And>x. 0 \<le> D x"
proof
  interpret N: finite_measure N by fact

  note RN = borel_measurable_RN_deriv density_RN_deriv[OF ac]

  let ?RN = "\<lambda>t. {x \<in> space M. RN_deriv M N x = t}"

  show "(\<lambda>x. enn2real (RN_deriv M N x)) \<in> borel_measurable M"
    using RN by auto

  have "N (?RN \<infinity>) = (\<integral>\<^sup>+ x. RN_deriv M N x * indicator (?RN \<infinity>) x \<partial>M)"
    using RN(1) by (subst RN(2)[symmetric]) (auto simp: emeasure_density)
  also have "\<dots> = (\<integral>\<^sup>+ x. \<infinity> * indicator (?RN \<infinity>) x \<partial>M)"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = \<infinity> * emeasure M (?RN \<infinity>)"
    using RN by (intro nn_integral_cmult_indicator) auto
  finally have eq: "N (?RN \<infinity>) = \<infinity> * emeasure M (?RN \<infinity>)" .
  moreover
  have "emeasure M (?RN \<infinity>) = 0"
  proof (rule ccontr)
    assume "emeasure M {x \<in> space M. RN_deriv M N x = \<infinity>} \<noteq> 0"
    then have "0 < emeasure M {x \<in> space M. RN_deriv M N x = \<infinity>}"
      by (auto simp: zero_less_iff_neq_zero)
    with eq have "N (?RN \<infinity>) = \<infinity>" by (simp add: ennreal_mult_eq_top_iff)
    with N.emeasure_finite[of "?RN \<infinity>"] RN show False by auto
  qed
  ultimately have "AE x in M. RN_deriv M N x < \<infinity>"
    using RN by (intro AE_iff_measurable[THEN iffD2]) (auto simp: less_top[symmetric])
  then show "AE x in M. RN_deriv M N x = ennreal (enn2real (RN_deriv M N x))"
    by auto
  then have eq: "AE x in N. RN_deriv M N x = ennreal (enn2real (RN_deriv M N x))"
    using ac absolutely_continuous_AE by auto


  have "N (?RN 0) = (\<integral>\<^sup>+ x. RN_deriv M N x * indicator (?RN 0) x \<partial>M)"
    by (subst RN(2)[symmetric]) (auto simp: emeasure_density)
  also have "\<dots> = (\<integral>\<^sup>+ x. 0 \<partial>M)"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  finally have "AE x in N. RN_deriv M N x \<noteq> 0"
    using RN by (subst AE_iff_measurable[OF _ refl]) (auto simp: ac cong: sets_eq_imp_space_eq)
  with eq show "AE x in N. 0 < enn2real (RN_deriv M N x)"
    by (auto simp: enn2real_positive_iff less_top[symmetric] zero_less_iff_neq_zero)
qed (rule enn2real_nonneg)

lemma (in sigma_finite_measure) RN_deriv_singleton:
  assumes ac: "absolutely_continuous M N" "sets N = sets M"
  and x: "{x} \<in> sets M"
  shows "N {x} = RN_deriv M N x * emeasure M {x}"
proof -
  from \<open>{x} \<in> sets M\<close>
  have "density M (RN_deriv M N) {x} = (\<integral>\<^sup>+w. RN_deriv M N x * indicator {x} w \<partial>M)"
    by (auto simp: indicator_def emeasure_density intro!: nn_integral_cong)
  with x density_RN_deriv[OF ac] show ?thesis
    by (auto simp: max_def)
qed

end
