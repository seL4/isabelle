(*  Title:      HOL/Probability/Radon_Nikodym.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Radon-Nikod{\'y}m derivative*}

theory Radon_Nikodym
imports Lebesgue_Integration
begin

definition "diff_measure M N =
  measure_of (space M) (sets M) (\<lambda>A. emeasure M A - emeasure N A)"

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
    using pos by (simp add: positive_def ereal_diff_positive)
  show "countably_additive (sets M) ?\<mu>"
  proof (rule countably_additiveI)
    fix A :: "nat \<Rightarrow> _"  assume A: "range A \<subseteq> sets M" and "disjoint_family A"
    then have suminf:
      "(\<Sum>i. emeasure M (A i)) = emeasure M (\<Union>i. A i)"
      "(\<Sum>i. emeasure N (A i)) = emeasure N (\<Union>i. A i)"
      by (simp_all add: suminf_emeasure sets_eq)
    with A have "(\<Sum>i. emeasure M (A i) - emeasure N (A i)) =
      (\<Sum>i. emeasure M (A i)) - (\<Sum>i. emeasure N (A i))"
      using fin
      by (intro suminf_ereal_minus pos emeasure_nonneg)
         (auto simp: sets_eq finite_measure.emeasure_eq_measure suminf_emeasure)
    then show "(\<Sum>i. emeasure M (A i) - emeasure N (A i)) =
      emeasure M (\<Union>i. A i) - emeasure N (\<Union>i. A i) "
      by (simp add: suminf)
  qed
qed fact

lemma (in sigma_finite_measure) Ex_finite_integrable_function:
  shows "\<exists>h\<in>borel_measurable M. integral\<^isup>P M h \<noteq> \<infinity> \<and> (\<forall>x\<in>space M. 0 < h x \<and> h x < \<infinity>) \<and> (\<forall>x. 0 \<le> h x)"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. emeasure M (A i) \<noteq> \<infinity>" and
    disjoint: "disjoint_family A"
    using sigma_finite_disjoint by auto
  let ?B = "\<lambda>i. 2^Suc i * emeasure M (A i)"
  have "\<forall>i. \<exists>x. 0 < x \<and> x < inverse (?B i)"
  proof
    fix i show "\<exists>x. 0 < x \<and> x < inverse (?B i)"
      using measure[of i] emeasure_nonneg[of M "A i"]
      by (auto intro!: ereal_dense simp: ereal_0_gt_inverse ereal_zero_le_0_iff)
  qed
  from choice[OF this] obtain n where n: "\<And>i. 0 < n i"
    "\<And>i. n i < inverse (2^Suc i * emeasure M (A i))" by auto
  { fix i have "0 \<le> n i" using n(1)[of i] by auto } note pos = this
  let ?h = "\<lambda>x. \<Sum>i. n i * indicator (A i) x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?h] del: notI)
    have "\<And>i. A i \<in> sets M"
      using range by fastforce+
    then have "integral\<^isup>P M ?h = (\<Sum>i. n i * emeasure M (A i))" using pos
      by (simp add: positive_integral_suminf positive_integral_cmult_indicator)
    also have "\<dots> \<le> (\<Sum>i. (1 / 2)^Suc i)"
    proof (rule suminf_le_pos)
      fix N
      have "n N * emeasure M (A N) \<le> inverse (2^Suc N * emeasure M (A N)) * emeasure M (A N)"
        using n[of N]
        by (intro ereal_mult_right_mono) auto
      also have "\<dots> \<le> (1 / 2) ^ Suc N"
        using measure[of N] n[of N]
        by (cases rule: ereal2_cases[of "n N" "emeasure M (A N)"])
           (simp_all add: inverse_eq_divide power_divide one_ereal_def ereal_power_divide)
      finally show "n N * emeasure M (A N) \<le> (1 / 2) ^ Suc N" .
      show "0 \<le> n N * emeasure M (A N)" using n[of N] `A N \<in> sets M` by (simp add: emeasure_nonneg)
    qed
    finally show "integral\<^isup>P M ?h \<noteq> \<infinity>" unfolding suminf_half_series_ereal by auto
  next
    { fix x assume "x \<in> space M"
      then obtain i where "x \<in> A i" using space[symmetric] by auto
      with disjoint n have "?h x = n i"
        by (auto intro!: suminf_cmult_indicator intro: less_imp_le)
      then show "0 < ?h x" and "?h x < \<infinity>" using n[of i] by auto }
    note pos = this
    fix x show "0 \<le> ?h x"
    proof cases
      assume "x \<in> space M" then show "0 \<le> ?h x" using pos by (auto intro: less_imp_le)
    next
      assume "x \<notin> space M" then have "\<And>i. x \<notin> A i" using space by auto
      then show "0 \<le> ?h x" by auto
    qed
  next
    show "?h \<in> borel_measurable M" using range n
      by (auto intro!: borel_measurable_psuminf borel_measurable_ereal_times ereal_0_le_mult intro: less_imp_le)
  qed
qed

subsection "Absolutely continuous"

definition absolutely_continuous :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "absolutely_continuous M N \<longleftrightarrow> null_sets M \<subseteq> null_sets N"

lemma absolutely_continuousI_count_space: "absolutely_continuous (count_space A) M"
  unfolding absolutely_continuous_def by (auto simp: null_sets_count_space)

lemma absolutely_continuousI_density:
  "f \<in> borel_measurable M \<Longrightarrow> absolutely_continuous M (density M f)"
  by (force simp add: absolutely_continuous_def null_sets_density_iff dest: AE_not_in)

lemma absolutely_continuousI_point_measure_finite:
  "(\<And>x. \<lbrakk> x \<in> A ; f x \<le> 0 \<rbrakk> \<Longrightarrow> g x \<le> 0) \<Longrightarrow> absolutely_continuous (point_measure A f) (point_measure A g)"
  unfolding absolutely_continuous_def by (force simp: null_sets_point_measure_iff)

lemma absolutely_continuous_AE:
  assumes sets_eq: "sets M' = sets M"
    and "absolutely_continuous M M'" "AE x in M. P x"
   shows "AE x in M'. P x"
proof -
  from `AE x in M. P x` obtain N where N: "N \<in> null_sets M" "{x\<in>space M. \<not> P x} \<subseteq> N"
    unfolding eventually_ae_filter by auto
  show "AE x in M'. P x"
  proof (rule AE_I')
    show "{x\<in>space M'. \<not> P x} \<subseteq> N" using sets_eq_imp_space_eq[OF sets_eq] N(2) by simp
    from `absolutely_continuous M M'` show "N \<in> null_sets M'"
      using N unfolding absolutely_continuous_def sets_eq null_sets_def by auto
  qed
qed

subsection "Existence of the Radon-Nikodym derivative"

lemma (in finite_measure) Radon_Nikodym_aux_epsilon:
  fixes e :: real assumes "0 < e"
  assumes "finite_measure N" and sets_eq: "sets N = sets M"
  shows "\<exists>A\<in>sets M. measure M (space M) - measure N (space M) \<le> measure M A - measure N A \<and>
                    (\<forall>B\<in>sets M. B \<subseteq> A \<longrightarrow> - e < measure M B - measure N B)"
proof -
  interpret M': finite_measure N by fact
  let ?d = "\<lambda>A. measure M A - measure N A"
  let ?A = "\<lambda>A. if (\<forall>B\<in>sets M. B \<subseteq> space M - A \<longrightarrow> -e < ?d B)
    then {}
    else (SOME B. B \<in> sets M \<and> B \<subseteq> space M - A \<and> ?d B \<le> -e)"
  def A \<equiv> "\<lambda>n. ((\<lambda>B. B \<union> ?A B) ^^ n) {}"
  have A_simps[simp]:
    "A 0 = {}"
    "\<And>n. A (Suc n) = (A n \<union> ?A (A n))" unfolding A_def by simp_all
  { fix A assume "A \<in> sets M"
    have "?A A \<in> sets M"
      by (auto intro!: someI2[of _ _ "\<lambda>A. A \<in> sets M"] simp: not_less) }
  note A'_in_sets = this
  { fix n have "A n \<in> sets M"
    proof (induct n)
      case (Suc n) thus "A (Suc n) \<in> sets M"
        using A'_in_sets[of "A n"] by (auto split: split_if_asm)
    qed (simp add: A_def) }
  note A_in_sets = this
  hence "range A \<subseteq> sets M" by auto
  { fix n B
    assume Ex: "\<exists>B. B \<in> sets M \<and> B \<subseteq> space M - A n \<and> ?d B \<le> -e"
    hence False: "\<not> (\<forall>B\<in>sets M. B \<subseteq> space M - A n \<longrightarrow> -e < ?d B)" by (auto simp: not_less)
    have "?d (A (Suc n)) \<le> ?d (A n) - e" unfolding A_simps if_not_P[OF False]
    proof (rule someI2_ex[OF Ex])
      fix B assume "B \<in> sets M \<and> B \<subseteq> space M - A n \<and> ?d B \<le> - e"
      hence "A n \<inter> B = {}" "B \<in> sets M" and dB: "?d B \<le> -e" by auto
      hence "?d (A n \<union> B) = ?d (A n) + ?d B"
        using `A n \<in> sets M` finite_measure_Union M'.finite_measure_Union by (simp add: sets_eq)
      also have "\<dots> \<le> ?d (A n) - e" using dB by simp
      finally show "?d (A n \<union> B) \<le> ?d (A n) - e" .
    qed }
  note dA_epsilon = this
  { fix n have "?d (A (Suc n)) \<le> ?d (A n)"
    proof (cases "\<exists>B. B\<in>sets M \<and> B \<subseteq> space M - A n \<and> ?d B \<le> - e")
      case True from dA_epsilon[OF this] show ?thesis using `0 < e` by simp
    next
      case False
      hence "\<forall>B\<in>sets M. B \<subseteq> space M - A n \<longrightarrow> -e < ?d B" by (auto simp: not_le)
      thus ?thesis by simp
    qed }
  note dA_mono = this
  show ?thesis
  proof (cases "\<exists>n. \<forall>B\<in>sets M. B \<subseteq> space M - A n \<longrightarrow> -e < ?d B")
    case True then obtain n where B: "\<And>B. \<lbrakk> B \<in> sets M; B \<subseteq> space M - A n\<rbrakk> \<Longrightarrow> -e < ?d B" by blast
    show ?thesis
    proof (safe intro!: bexI[of _ "space M - A n"])
      fix B assume "B \<in> sets M" "B \<subseteq> space M - A n"
      from B[OF this] show "-e < ?d B" .
    next
      show "space M - A n \<in> sets M" by (rule compl_sets) fact
    next
      show "?d (space M) \<le> ?d (space M - A n)"
      proof (induct n)
        fix n assume "?d (space M) \<le> ?d (space M - A n)"
        also have "\<dots> \<le> ?d (space M - A (Suc n))"
          using A_in_sets sets_into_space dA_mono[of n] finite_measure_compl M'.finite_measure_compl
          by (simp del: A_simps add: sets_eq sets_eq_imp_space_eq[OF sets_eq])
        finally show "?d (space M) \<le> ?d (space M - A (Suc n))" .
      qed simp
    qed
  next
    case False hence B: "\<And>n. \<exists>B. B\<in>sets M \<and> B \<subseteq> space M - A n \<and> ?d B \<le> - e"
      by (auto simp add: not_less)
    { fix n have "?d (A n) \<le> - real n * e"
      proof (induct n)
        case (Suc n) with dA_epsilon[of n, OF B] show ?case by (simp del: A_simps add: real_of_nat_Suc field_simps)
      next
        case 0 with measure_empty show ?case by (simp add: zero_ereal_def)
      qed } note dA_less = this
    have decseq: "decseq (\<lambda>n. ?d (A n))" unfolding decseq_eq_incseq
    proof (rule incseq_SucI)
      fix n show "- ?d (A n) \<le> - ?d (A (Suc n))" using dA_mono[of n] by auto
    qed
    have A: "incseq A" by (auto intro!: incseq_SucI)
    from finite_Lim_measure_incseq[OF _ A] `range A \<subseteq> sets M`
      M'.finite_Lim_measure_incseq[OF _ A]
    have convergent: "(\<lambda>i. ?d (A i)) ----> ?d (\<Union>i. A i)"
      by (auto intro!: tendsto_diff simp: sets_eq)
    obtain n :: nat where "- ?d (\<Union>i. A i) / e < real n" using reals_Archimedean2 by auto
    moreover from order_trans[OF decseq_le[OF decseq convergent] dA_less]
    have "real n \<le> - ?d (\<Union>i. A i) / e" using `0<e` by (simp add: field_simps)
    ultimately show ?thesis by auto
  qed
qed

lemma (in finite_measure) Radon_Nikodym_aux:
  assumes "finite_measure N" and sets_eq: "sets N = sets M"
  shows "\<exists>A\<in>sets M. measure M (space M) - measure N (space M) \<le>
                    measure M A - measure N A \<and>
                    (\<forall>B\<in>sets M. B \<subseteq> A \<longrightarrow> 0 \<le> measure M B - measure N B)"
proof -
  interpret N: finite_measure N by fact
  let ?d = "\<lambda>A. measure M A - measure N A"
  let ?P = "\<lambda>A B n. A \<in> sets M \<and> A \<subseteq> B \<and> ?d B \<le> ?d A \<and> (\<forall>C\<in>sets M. C \<subseteq> A \<longrightarrow> - 1 / real (Suc n) < ?d C)"
  let ?r = "\<lambda>S. restricted_space S"
  { fix S n assume S: "S \<in> sets M"
    then have "finite_measure (density M (indicator S))" "0 < 1 / real (Suc n)"
         "finite_measure (density N (indicator S))" "sets (density N (indicator S)) = sets (density M (indicator S))"
      by (auto simp: finite_measure_restricted N.finite_measure_restricted sets_eq)
    from finite_measure.Radon_Nikodym_aux_epsilon[OF this] guess X .. note X = this
    with S have "?P (S \<inter> X) S n"
      by (simp add: measure_restricted sets_eq Int) (metis inf_absorb2)
    hence "\<exists>A. ?P A S n" .. }
  note Ex_P = this
  def A \<equiv> "nat_rec (space M) (\<lambda>n A. SOME B. ?P B A n)"
  have A_Suc: "\<And>n. A (Suc n) = (SOME B. ?P B (A n) n)" by (simp add: A_def)
  have A_0[simp]: "A 0 = space M" unfolding A_def by simp
  { fix i have "A i \<in> sets M" unfolding A_def
    proof (induct i)
      case (Suc i)
      from Ex_P[OF this, of i] show ?case unfolding nat_rec_Suc
        by (rule someI2_ex) simp
    qed simp }
  note A_in_sets = this
  { fix n have "?P (A (Suc n)) (A n) n"
      using Ex_P[OF A_in_sets] unfolding A_Suc
      by (rule someI2_ex) simp }
  note P_A = this
  have "range A \<subseteq> sets M" using A_in_sets by auto
  have A_mono: "\<And>i. A (Suc i) \<subseteq> A i" using P_A by simp
  have mono_dA: "mono (\<lambda>i. ?d (A i))" using P_A by (simp add: mono_iff_le_Suc)
  have epsilon: "\<And>C i. \<lbrakk> C \<in> sets M; C \<subseteq> A (Suc i) \<rbrakk> \<Longrightarrow> - 1 / real (Suc i) < ?d C"
      using P_A by auto
  show ?thesis
  proof (safe intro!: bexI[of _ "\<Inter>i. A i"])
    show "(\<Inter>i. A i) \<in> sets M" using A_in_sets by auto
    have A: "decseq A" using A_mono by (auto intro!: decseq_SucI)
    from `range A \<subseteq> sets M`
      finite_Lim_measure_decseq[OF _ A] N.finite_Lim_measure_decseq[OF _ A]
    have "(\<lambda>i. ?d (A i)) ----> ?d (\<Inter>i. A i)" by (auto intro!: tendsto_diff simp: sets_eq)
    thus "?d (space M) \<le> ?d (\<Inter>i. A i)" using mono_dA[THEN monoD, of 0 _]
      by (rule_tac LIMSEQ_le_const) auto
  next
    fix B assume B: "B \<in> sets M" "B \<subseteq> (\<Inter>i. A i)"
    show "0 \<le> ?d B"
    proof (rule ccontr)
      assume "\<not> 0 \<le> ?d B"
      hence "0 < - ?d B" by auto
      from ex_inverse_of_nat_Suc_less[OF this]
      obtain n where *: "?d B < - 1 / real (Suc n)"
        by (auto simp: real_eq_of_nat inverse_eq_divide field_simps)
      have "B \<subseteq> A (Suc n)" using B by (auto simp del: nat_rec_Suc)
      from epsilon[OF B(1) this] *
      show False by auto
    qed
  qed
qed

lemma (in finite_measure) Radon_Nikodym_finite_measure:
  assumes "finite_measure N" and sets_eq: "sets N = sets M"
  assumes "absolutely_continuous M N"
  shows "\<exists>f \<in> borel_measurable M. (\<forall>x. 0 \<le> f x) \<and> density M f = N"
proof -
  interpret N: finite_measure N by fact
  def G \<equiv> "{g \<in> borel_measurable M. (\<forall>x. 0 \<le> g x) \<and> (\<forall>A\<in>sets M. (\<integral>\<^isup>+x. g x * indicator A x \<partial>M) \<le> N A)}"
  have "(\<lambda>x. 0) \<in> G" unfolding G_def by auto
  hence "G \<noteq> {}" by auto
  { fix f g assume f: "f \<in> G" and g: "g \<in> G"
    have "(\<lambda>x. max (g x) (f x)) \<in> G" (is "?max \<in> G") unfolding G_def
    proof safe
      show "?max \<in> borel_measurable M" using f g unfolding G_def by auto
      let ?A = "{x \<in> space M. f x \<le> g x}"
      have "?A \<in> sets M" using f g unfolding G_def by auto
      fix A assume "A \<in> sets M"
      hence sets: "?A \<inter> A \<in> sets M" "(space M - ?A) \<inter> A \<in> sets M" using `?A \<in> sets M` by auto
      hence sets': "?A \<inter> A \<in> sets N" "(space M - ?A) \<inter> A \<in> sets N" by (auto simp: sets_eq)
      have union: "((?A \<inter> A) \<union> ((space M - ?A) \<inter> A)) = A"
        using sets_into_space[OF `A \<in> sets M`] by auto
      have "\<And>x. x \<in> space M \<Longrightarrow> max (g x) (f x) * indicator A x =
        g x * indicator (?A \<inter> A) x + f x * indicator ((space M - ?A) \<inter> A) x"
        by (auto simp: indicator_def max_def)
      hence "(\<integral>\<^isup>+x. max (g x) (f x) * indicator A x \<partial>M) =
        (\<integral>\<^isup>+x. g x * indicator (?A \<inter> A) x \<partial>M) +
        (\<integral>\<^isup>+x. f x * indicator ((space M - ?A) \<inter> A) x \<partial>M)"
        using f g sets unfolding G_def
        by (auto cong: positive_integral_cong intro!: positive_integral_add)
      also have "\<dots> \<le> N (?A \<inter> A) + N ((space M - ?A) \<inter> A)"
        using f g sets unfolding G_def by (auto intro!: add_mono)
      also have "\<dots> = N A"
        using plus_emeasure[OF sets'] union by auto
      finally show "(\<integral>\<^isup>+x. max (g x) (f x) * indicator A x \<partial>M) \<le> N A" .
    next
      fix x show "0 \<le> max (g x) (f x)" using f g by (auto simp: G_def split: split_max)
    qed }
  note max_in_G = this
  { fix f assume  "incseq f" and f: "\<And>i. f i \<in> G"
    have "(\<lambda>x. SUP i. f i x) \<in> G" unfolding G_def
    proof safe
      show "(\<lambda>x. SUP i. f i x) \<in> borel_measurable M"
        using f by (auto simp: G_def)
      { fix x show "0 \<le> (SUP i. f i x)"
          using f by (auto simp: G_def intro: SUP_upper2) }
    next
      fix A assume "A \<in> sets M"
      have "(\<integral>\<^isup>+x. (SUP i. f i x) * indicator A x \<partial>M) =
        (\<integral>\<^isup>+x. (SUP i. f i x * indicator A x) \<partial>M)"
        by (intro positive_integral_cong) (simp split: split_indicator)
      also have "\<dots> = (SUP i. (\<integral>\<^isup>+x. f i x * indicator A x \<partial>M))"
        using `incseq f` f `A \<in> sets M`
        by (intro positive_integral_monotone_convergence_SUP)
           (auto simp: G_def incseq_Suc_iff le_fun_def split: split_indicator)
      finally show "(\<integral>\<^isup>+x. (SUP i. f i x) * indicator A x \<partial>M) \<le> N A"
        using f `A \<in> sets M` by (auto intro!: SUP_least simp: G_def)
    qed }
  note SUP_in_G = this
  let ?y = "SUP g : G. integral\<^isup>P M g"
  have y_le: "?y \<le> N (space M)" unfolding G_def
  proof (safe intro!: SUP_least)
    fix g assume "\<forall>A\<in>sets M. (\<integral>\<^isup>+x. g x * indicator A x \<partial>M) \<le> N A"
    from this[THEN bspec, OF top] show "integral\<^isup>P M g \<le> N (space M)"
      by (simp cong: positive_integral_cong)
  qed
  from SUPR_countable_SUPR[OF `G \<noteq> {}`, of "integral\<^isup>P M"] guess ys .. note ys = this
  then have "\<forall>n. \<exists>g. g\<in>G \<and> integral\<^isup>P M g = ys n"
  proof safe
    fix n assume "range ys \<subseteq> integral\<^isup>P M ` G"
    hence "ys n \<in> integral\<^isup>P M ` G" by auto
    thus "\<exists>g. g\<in>G \<and> integral\<^isup>P M g = ys n" by auto
  qed
  from choice[OF this] obtain gs where "\<And>i. gs i \<in> G" "\<And>n. integral\<^isup>P M (gs n) = ys n" by auto
  hence y_eq: "?y = (SUP i. integral\<^isup>P M (gs i))" using ys by auto
  let ?g = "\<lambda>i x. Max ((\<lambda>n. gs n x) ` {..i})"
  def f \<equiv> "\<lambda>x. SUP i. ?g i x"
  let ?F = "\<lambda>A x. f x * indicator A x"
  have gs_not_empty: "\<And>i x. (\<lambda>n. gs n x) ` {..i} \<noteq> {}" by auto
  { fix i have "?g i \<in> G"
    proof (induct i)
      case 0 thus ?case by simp fact
    next
      case (Suc i)
      with Suc gs_not_empty `gs (Suc i) \<in> G` show ?case
        by (auto simp add: atMost_Suc intro!: max_in_G)
    qed }
  note g_in_G = this
  have "incseq ?g" using gs_not_empty
    by (auto intro!: incseq_SucI le_funI simp add: atMost_Suc)
  from SUP_in_G[OF this g_in_G] have "f \<in> G" unfolding f_def .
  then have [simp, intro]: "f \<in> borel_measurable M" unfolding G_def by auto
  have "integral\<^isup>P M f = (SUP i. integral\<^isup>P M (?g i))" unfolding f_def
    using g_in_G `incseq ?g`
    by (auto intro!: positive_integral_monotone_convergence_SUP simp: G_def)
  also have "\<dots> = ?y"
  proof (rule antisym)
    show "(SUP i. integral\<^isup>P M (?g i)) \<le> ?y"
      using g_in_G by (auto intro: Sup_mono simp: SUP_def)
    show "?y \<le> (SUP i. integral\<^isup>P M (?g i))" unfolding y_eq
      by (auto intro!: SUP_mono positive_integral_mono Max_ge)
  qed
  finally have int_f_eq_y: "integral\<^isup>P M f = ?y" .
  have "\<And>x. 0 \<le> f x"
    unfolding f_def using `\<And>i. gs i \<in> G`
    by (auto intro!: SUP_upper2 Max_ge_iff[THEN iffD2] simp: G_def)
  let ?t = "\<lambda>A. N A - (\<integral>\<^isup>+x. ?F A x \<partial>M)"
  let ?M = "diff_measure N (density M f)"
  have f_le_N: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. ?F A x \<partial>M) \<le> N A"
    using `f \<in> G` unfolding G_def by auto
  have emeasure_M: "\<And>A. A \<in> sets M \<Longrightarrow> emeasure ?M A = ?t A"
  proof (subst emeasure_diff_measure)
    from f_le_N[of "space M"] show "finite_measure N" "finite_measure (density M f)"
      by (auto intro!: finite_measureI simp: emeasure_density cong: positive_integral_cong)
  next
    fix B assume "B \<in> sets N" with f_le_N[of B] show "emeasure (density M f) B \<le> emeasure N B"
      by (auto simp: sets_eq emeasure_density cong: positive_integral_cong)
  qed (auto simp: sets_eq emeasure_density)
  from emeasure_M[of "space M"] N.finite_emeasure_space positive_integral_positive[of M "?F (space M)"]
  interpret M': finite_measure ?M
    by (auto intro!: finite_measureI simp: sets_eq_imp_space_eq[OF sets_eq] N.emeasure_eq_measure ereal_minus_eq_PInfty_iff)

  have ac: "absolutely_continuous M ?M" unfolding absolutely_continuous_def
  proof
    fix A assume A: "A \<in> null_sets M"
    with `absolutely_continuous M N` have "A \<in> null_sets N"
      unfolding absolutely_continuous_def by auto
    moreover with A have "(\<integral>\<^isup>+ x. ?F A x \<partial>M) \<le> N A" using `f \<in> G` by (auto simp: G_def)
    ultimately have "N A - (\<integral>\<^isup>+ x. ?F A x \<partial>M) = 0"
      using positive_integral_positive[of M] by (auto intro!: antisym)
    then show "A \<in> null_sets ?M"
      using A by (simp add: emeasure_M null_sets_def sets_eq)
  qed
  have upper_bound: "\<forall>A\<in>sets M. ?M A \<le> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain A where A: "A \<in> sets M" and pos: "0 < ?M A"
      by (auto simp: not_le)
    note pos
    also have "?M A \<le> ?M (space M)"
      using emeasure_space[of ?M A] by (simp add: sets_eq[THEN sets_eq_imp_space_eq])
    finally have pos_t: "0 < ?M (space M)" by simp
    moreover
    then have "emeasure M (space M) \<noteq> 0"
      using ac unfolding absolutely_continuous_def by (auto simp: null_sets_def)
    then have pos_M: "0 < emeasure M (space M)"
      using emeasure_nonneg[of M "space M"] by (simp add: le_less)
    moreover
    have "(\<integral>\<^isup>+x. f x * indicator (space M) x \<partial>M) \<le> N (space M)"
      using `f \<in> G` unfolding G_def by auto
    hence "(\<integral>\<^isup>+x. f x * indicator (space M) x \<partial>M) \<noteq> \<infinity>"
      using M'.finite_emeasure_space by auto
    moreover
    def b \<equiv> "?M (space M) / emeasure M (space M) / 2"
    ultimately have b: "b \<noteq> 0 \<and> 0 \<le> b \<and> b \<noteq> \<infinity>"
      by (auto simp: ereal_divide_eq)
    then have b: "b \<noteq> 0" "0 \<le> b" "0 < b"  "b \<noteq> \<infinity>" by auto
    let ?Mb = "density M (\<lambda>_. b)"
    have Mb: "finite_measure ?Mb" "sets ?Mb = sets ?M"
        using b by (auto simp: emeasure_density_const sets_eq intro!: finite_measureI)
    from M'.Radon_Nikodym_aux[OF this] guess A0 ..
    then have "A0 \<in> sets M"
      and space_less_A0: "measure ?M (space M) - real b * measure M (space M) \<le> measure ?M A0 - real b * measure M A0"
      and *: "\<And>B. B \<in> sets M \<Longrightarrow> B \<subseteq> A0 \<Longrightarrow> 0 \<le> measure ?M B - real b * measure M B"
      using b by (simp_all add: measure_density_const sets_eq_imp_space_eq[OF sets_eq] sets_eq)
    { fix B assume B: "B \<in> sets M" "B \<subseteq> A0"
      with *[OF this] have "b * emeasure M B \<le> ?M B"
        using b unfolding M'.emeasure_eq_measure emeasure_eq_measure by (cases b) auto }
    note bM_le_t = this
    let ?f0 = "\<lambda>x. f x + b * indicator A0 x"
    { fix A assume A: "A \<in> sets M"
      hence "A \<inter> A0 \<in> sets M" using `A0 \<in> sets M` by auto
      have "(\<integral>\<^isup>+x. ?f0 x  * indicator A x \<partial>M) =
        (\<integral>\<^isup>+x. f x * indicator A x + b * indicator (A \<inter> A0) x \<partial>M)"
        by (auto intro!: positive_integral_cong split: split_indicator)
      hence "(\<integral>\<^isup>+x. ?f0 x * indicator A x \<partial>M) =
          (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) + b * emeasure M (A \<inter> A0)"
        using `A0 \<in> sets M` `A \<inter> A0 \<in> sets M` A b `f \<in> G`
        by (simp add: G_def positive_integral_add positive_integral_cmult_indicator) }
    note f0_eq = this
    { fix A assume A: "A \<in> sets M"
      hence "A \<inter> A0 \<in> sets M" using `A0 \<in> sets M` by auto
      have f_le_v: "(\<integral>\<^isup>+x. ?F A x \<partial>M) \<le> N A" using `f \<in> G` A unfolding G_def by auto
      note f0_eq[OF A]
      also have "(\<integral>\<^isup>+x. ?F A x \<partial>M) + b * emeasure M (A \<inter> A0) \<le> (\<integral>\<^isup>+x. ?F A x \<partial>M) + ?M (A \<inter> A0)"
        using bM_le_t[OF `A \<inter> A0 \<in> sets M`] `A \<in> sets M` `A0 \<in> sets M`
        by (auto intro!: add_left_mono)
      also have "\<dots> \<le> (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) + ?M A"
        using emeasure_mono[of "A \<inter> A0" A ?M] `A \<in> sets M` `A0 \<in> sets M`
        by (auto intro!: add_left_mono simp: sets_eq)
      also have "\<dots> \<le> N A"
        unfolding emeasure_M[OF `A \<in> sets M`]
        using f_le_v N.emeasure_eq_measure[of A] positive_integral_positive[of M "?F A"]
        by (cases "\<integral>\<^isup>+x. ?F A x \<partial>M", cases "N A") auto
      finally have "(\<integral>\<^isup>+x. ?f0 x * indicator A x \<partial>M) \<le> N A" . }
    hence "?f0 \<in> G" using `A0 \<in> sets M` b `f \<in> G` unfolding G_def
      by (auto intro!: ereal_add_nonneg_nonneg)
    have int_f_finite: "integral\<^isup>P M f \<noteq> \<infinity>"
      by (metis N.emeasure_finite ereal_infty_less_eq2(1) int_f_eq_y y_le)
    have  "0 < ?M (space M) - emeasure ?Mb (space M)"
      using pos_t
      by (simp add: b emeasure_density_const)
         (simp add: M'.emeasure_eq_measure emeasure_eq_measure pos_M b_def)
    also have "\<dots> \<le> ?M A0 - b * emeasure M A0"
      using space_less_A0 `A0 \<in> sets M` b
      by (cases b) (auto simp add: b emeasure_density_const sets_eq M'.emeasure_eq_measure emeasure_eq_measure)
    finally have 1: "b * emeasure M A0 < ?M A0"
      by (metis M'.emeasure_real `A0 \<in> sets M` bM_le_t diff_self ereal_less(1) ereal_minus(1)
                less_eq_ereal_def mult_zero_left not_square_less_zero subset_refl zero_ereal_def)
    with b have "0 < ?M A0"
      by (metis M'.emeasure_real MInfty_neq_PInfty(1) emeasure_real ereal_less_eq(5) ereal_zero_times
               ereal_mult_eq_MInfty ereal_mult_eq_PInfty ereal_zero_less_0_iff less_eq_ereal_def)
    then have "emeasure M A0 \<noteq> 0" using ac `A0 \<in> sets M`
      by (auto simp: absolutely_continuous_def null_sets_def)
    then have "0 < emeasure M A0" using emeasure_nonneg[of M A0] by auto
    hence "0 < b * emeasure M A0" using b by (auto simp: ereal_zero_less_0_iff)
    with int_f_finite have "?y + 0 < integral\<^isup>P M f + b * emeasure M A0" unfolding int_f_eq_y
      using `f \<in> G`
      by (intro ereal_add_strict_mono) (auto intro!: SUP_upper2 positive_integral_positive)
    also have "\<dots> = integral\<^isup>P M ?f0" using f0_eq[OF top] `A0 \<in> sets M` sets_into_space
      by (simp cong: positive_integral_cong)
    finally have "?y < integral\<^isup>P M ?f0" by simp
    moreover from `?f0 \<in> G` have "integral\<^isup>P M ?f0 \<le> ?y" by (auto intro!: SUP_upper)
    ultimately show False by auto
  qed
  let ?f = "\<lambda>x. max 0 (f x)"
  show ?thesis
  proof (intro bexI[of _ ?f] measure_eqI conjI)
    show "sets (density M ?f) = sets N"
      by (simp add: sets_eq)
    fix A assume A: "A\<in>sets (density M ?f)"
    then show "emeasure (density M ?f) A = emeasure N A"
      using `f \<in> G` A upper_bound[THEN bspec, of A] N.emeasure_eq_measure[of A]
      by (cases "integral\<^isup>P M (?F A)")
         (auto intro!: antisym simp add: emeasure_density G_def emeasure_M density_max_0[symmetric])
  qed auto
qed

lemma (in finite_measure) split_space_into_finite_sets_and_rest:
  assumes ac: "absolutely_continuous M N" and sets_eq: "sets N = sets M"
  shows "\<exists>A0\<in>sets M. \<exists>B::nat\<Rightarrow>'a set. disjoint_family B \<and> range B \<subseteq> sets M \<and> A0 = space M - (\<Union>i. B i) \<and>
    (\<forall>A\<in>sets M. A \<subseteq> A0 \<longrightarrow> (emeasure M A = 0 \<and> N A = 0) \<or> (emeasure M A > 0 \<and> N A = \<infinity>)) \<and>
    (\<forall>i. N (B i) \<noteq> \<infinity>)"
proof -
  let ?Q = "{Q\<in>sets M. N Q \<noteq> \<infinity>}"
  let ?a = "SUP Q:?Q. emeasure M Q"
  have "{} \<in> ?Q" by auto
  then have Q_not_empty: "?Q \<noteq> {}" by blast
  have "?a \<le> emeasure M (space M)" using sets_into_space
    by (auto intro!: SUP_least emeasure_mono)
  then have "?a \<noteq> \<infinity>" using finite_emeasure_space
    by auto
  from SUPR_countable_SUPR[OF Q_not_empty, of "emeasure M"]
  obtain Q'' where "range Q'' \<subseteq> emeasure M ` ?Q" and a: "?a = (SUP i::nat. Q'' i)"
    by auto
  then have "\<forall>i. \<exists>Q'. Q'' i = emeasure M Q' \<and> Q' \<in> ?Q" by auto
  from choice[OF this] obtain Q' where Q': "\<And>i. Q'' i = emeasure M (Q' i)" "\<And>i. Q' i \<in> ?Q"
    by auto
  then have a_Lim: "?a = (SUP i::nat. emeasure M (Q' i))" using a by simp
  let ?O = "\<lambda>n. \<Union>i\<le>n. Q' i"
  have Union: "(SUP i. emeasure M (?O i)) = emeasure M (\<Union>i. ?O i)"
  proof (rule SUP_emeasure_incseq[of ?O])
    show "range ?O \<subseteq> sets M" using Q' by auto
    show "incseq ?O" by (fastforce intro!: incseq_SucI)
  qed
  have Q'_sets: "\<And>i. Q' i \<in> sets M" using Q' by auto
  have O_sets: "\<And>i. ?O i \<in> sets M" using Q' by auto
  then have O_in_G: "\<And>i. ?O i \<in> ?Q"
  proof (safe del: notI)
    fix i have "Q' ` {..i} \<subseteq> sets M" using Q' by auto
    then have "N (?O i) \<le> (\<Sum>i\<le>i. N (Q' i))"
      by (simp add: sets_eq emeasure_subadditive_finite)
    also have "\<dots> < \<infinity>" using Q' by (simp add: setsum_Pinfty)
    finally show "N (?O i) \<noteq> \<infinity>" by simp
  qed auto
  have O_mono: "\<And>n. ?O n \<subseteq> ?O (Suc n)" by fastforce
  have a_eq: "?a = emeasure M (\<Union>i. ?O i)" unfolding Union[symmetric]
  proof (rule antisym)
    show "?a \<le> (SUP i. emeasure M (?O i))" unfolding a_Lim
      using Q' by (auto intro!: SUP_mono emeasure_mono)
    show "(SUP i. emeasure M (?O i)) \<le> ?a" unfolding SUP_def
    proof (safe intro!: Sup_mono, unfold bex_simps)
      fix i
      have *: "(\<Union>Q' ` {..i}) = ?O i" by auto
      then show "\<exists>x. (x \<in> sets M \<and> N x \<noteq> \<infinity>) \<and>
        emeasure M (\<Union>Q' ` {..i}) \<le> emeasure M x"
        using O_in_G[of i] by (auto intro!: exI[of _ "?O i"])
    qed
  qed
  let ?O_0 = "(\<Union>i. ?O i)"
  have "?O_0 \<in> sets M" using Q' by auto
  def Q \<equiv> "\<lambda>i. case i of 0 \<Rightarrow> Q' 0 | Suc n \<Rightarrow> ?O (Suc n) - ?O n"
  { fix i have "Q i \<in> sets M" unfolding Q_def using Q'[of 0] by (cases i) (auto intro: O_sets) }
  note Q_sets = this
  show ?thesis
  proof (intro bexI exI conjI ballI impI allI)
    show "disjoint_family Q"
      by (fastforce simp: disjoint_family_on_def Q_def
        split: nat.split_asm)
    show "range Q \<subseteq> sets M"
      using Q_sets by auto
    { fix A assume A: "A \<in> sets M" "A \<subseteq> space M - ?O_0"
      show "emeasure M A = 0 \<and> N A = 0 \<or> 0 < emeasure M A \<and> N A = \<infinity>"
      proof (rule disjCI, simp)
        assume *: "0 < emeasure M A \<longrightarrow> N A \<noteq> \<infinity>"
        show "emeasure M A = 0 \<and> N A = 0"
        proof cases
          assume "emeasure M A = 0" moreover with ac A have "N A = 0"
            unfolding absolutely_continuous_def by auto
          ultimately show ?thesis by simp
        next
          assume "emeasure M A \<noteq> 0" with * have "N A \<noteq> \<infinity>" using emeasure_nonneg[of M A] by auto
          with A have "emeasure M ?O_0 + emeasure M A = emeasure M (?O_0 \<union> A)"
            using Q' by (auto intro!: plus_emeasure countable_UN)
          also have "\<dots> = (SUP i. emeasure M (?O i \<union> A))"
          proof (rule SUP_emeasure_incseq[of "\<lambda>i. ?O i \<union> A", symmetric, simplified])
            show "range (\<lambda>i. ?O i \<union> A) \<subseteq> sets M"
              using `N A \<noteq> \<infinity>` O_sets A by auto
          qed (fastforce intro!: incseq_SucI)
          also have "\<dots> \<le> ?a"
          proof (safe intro!: SUP_least)
            fix i have "?O i \<union> A \<in> ?Q"
            proof (safe del: notI)
              show "?O i \<union> A \<in> sets M" using O_sets A by auto
              from O_in_G[of i] have "N (?O i \<union> A) \<le> N (?O i) + N A"
                using emeasure_subadditive[of "?O i" N A] A O_sets by (auto simp: sets_eq)
              with O_in_G[of i] show "N (?O i \<union> A) \<noteq> \<infinity>"
                using `N A \<noteq> \<infinity>` by auto
            qed
            then show "emeasure M (?O i \<union> A) \<le> ?a" by (rule SUP_upper)
          qed
          finally have "emeasure M A = 0"
            unfolding a_eq using measure_nonneg[of M A] by (simp add: emeasure_eq_measure)
          with `emeasure M A \<noteq> 0` show ?thesis by auto
        qed
      qed }
    { fix i show "N (Q i) \<noteq> \<infinity>"
      proof (cases i)
        case 0 then show ?thesis
          unfolding Q_def using Q'[of 0] by simp
      next
        case (Suc n)
        with `?O n \<in> ?Q` `?O (Suc n) \<in> ?Q`
            emeasure_Diff[OF _ _ _ O_mono, of N n] emeasure_nonneg[of N "(\<Union> x\<le>n. Q' x)"]
        show ?thesis
          by (auto simp: sets_eq ereal_minus_eq_PInfty_iff Q_def)
      qed }
    show "space M - ?O_0 \<in> sets M" using Q'_sets by auto
    { fix j have "(\<Union>i\<le>j. ?O i) = (\<Union>i\<le>j. Q i)"
      proof (induct j)
        case 0 then show ?case by (simp add: Q_def)
      next
        case (Suc j)
        have eq: "\<And>j. (\<Union>i\<le>j. ?O i) = (\<Union>i\<le>j. Q' i)" by fastforce
        have "{..j} \<union> {..Suc j} = {..Suc j}" by auto
        then have "(\<Union>i\<le>Suc j. Q' i) = (\<Union>i\<le>j. Q' i) \<union> Q (Suc j)"
          by (simp add: UN_Un[symmetric] Q_def del: UN_Un)
        then show ?case using Suc by (auto simp add: eq atMost_Suc)
      qed }
    then have "(\<Union>j. (\<Union>i\<le>j. ?O i)) = (\<Union>j. (\<Union>i\<le>j. Q i))" by simp
    then show "space M - ?O_0 = space M - (\<Union>i. Q i)" by fastforce
  qed
qed

lemma (in finite_measure) Radon_Nikodym_finite_measure_infinite:
  assumes "absolutely_continuous M N" and sets_eq: "sets N = sets M"
  shows "\<exists>f\<in>borel_measurable M. (\<forall>x. 0 \<le> f x) \<and> density M f = N"
proof -
  from split_space_into_finite_sets_and_rest[OF assms]
  obtain Q0 and Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and Q0: "Q0 \<in> sets M" "Q0 = space M - (\<Union>i. Q i)"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> emeasure M A = 0 \<and> N A = 0 \<or> 0 < emeasure M A \<and> N A = \<infinity>"
    and Q_fin: "\<And>i. N (Q i) \<noteq> \<infinity>" by force
  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  let ?N = "\<lambda>i. density N (indicator (Q i))" and ?M = "\<lambda>i. density M (indicator (Q i))"
  have "\<forall>i. \<exists>f\<in>borel_measurable (?M i). (\<forall>x. 0 \<le> f x) \<and> density (?M i) f = ?N i"
  proof (intro allI finite_measure.Radon_Nikodym_finite_measure)
    fix i
    from Q show "finite_measure (?M i)"
      by (auto intro!: finite_measureI cong: positive_integral_cong
               simp add: emeasure_density subset_eq sets_eq)
    from Q have "emeasure (?N i) (space N) = emeasure N (Q i)"
      by (simp add: sets_eq[symmetric] emeasure_density subset_eq cong: positive_integral_cong)
    with Q_fin show "finite_measure (?N i)"
      by (auto intro!: finite_measureI)
    show "sets (?N i) = sets (?M i)" by (simp add: sets_eq)
    show "absolutely_continuous (?M i) (?N i)"
      using `absolutely_continuous M N` `Q i \<in> sets M`
      by (auto simp: absolutely_continuous_def null_sets_density_iff sets_eq
               intro!: absolutely_continuous_AE[OF sets_eq])
  qed
  from choice[OF this[unfolded Bex_def]]
  obtain f where borel: "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
    and f_density: "\<And>i. density (?M i) (f i) = ?N i"
    by auto
  { fix A i assume A: "A \<in> sets M"
    with Q borel have "(\<integral>\<^isup>+x. f i x * indicator (Q i \<inter> A) x \<partial>M) = emeasure (density (?M i) (f i)) A"
      by (auto simp add: emeasure_density positive_integral_density subset_eq
               intro!: positive_integral_cong split: split_indicator)
    also have "\<dots> = emeasure N (Q i \<inter> A)"
      using A Q by (simp add: f_density emeasure_restricted subset_eq sets_eq)
    finally have "emeasure N (Q i \<inter> A) = (\<integral>\<^isup>+x. f i x * indicator (Q i \<inter> A) x \<partial>M)" .. }
  note integral_eq = this
  let ?f = "\<lambda>x. (\<Sum>i. f i x * indicator (Q i) x) + \<infinity> * indicator Q0 x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?f])
    show "?f \<in> borel_measurable M" using Q0 borel Q_sets
      by (auto intro!: measurable_If)
    show "\<And>x. 0 \<le> ?f x" using borel by (auto intro!: suminf_0_le simp: indicator_def)
    show "density M ?f = N"
    proof (rule measure_eqI)
      fix A assume "A \<in> sets (density M ?f)"
      then have "A \<in> sets M" by simp
      have Qi: "\<And>i. Q i \<in> sets M" using Q by auto
      have [intro,simp]: "\<And>i. (\<lambda>x. f i x * indicator (Q i \<inter> A) x) \<in> borel_measurable M"
        "\<And>i. AE x in M. 0 \<le> f i x * indicator (Q i \<inter> A) x"
        using borel Qi Q0(1) `A \<in> sets M` by (auto intro!: borel_measurable_ereal_times)
      have "(\<integral>\<^isup>+x. ?f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. (\<Sum>i. f i x * indicator (Q i \<inter> A) x) + \<infinity> * indicator (Q0 \<inter> A) x \<partial>M)"
        using borel by (intro positive_integral_cong) (auto simp: indicator_def)
      also have "\<dots> = (\<integral>\<^isup>+x. (\<Sum>i. f i x * indicator (Q i \<inter> A) x) \<partial>M) + \<infinity> * emeasure M (Q0 \<inter> A)"
        using borel Qi Q0(1) `A \<in> sets M`
        by (subst positive_integral_add) (auto simp del: ereal_infty_mult
            simp add: positive_integral_cmult_indicator Int intro!: suminf_0_le)
      also have "\<dots> = (\<Sum>i. N (Q i \<inter> A)) + \<infinity> * emeasure M (Q0 \<inter> A)"
        by (subst integral_eq[OF `A \<in> sets M`], subst positive_integral_suminf) auto
      finally have "(\<integral>\<^isup>+x. ?f x * indicator A x \<partial>M) = (\<Sum>i. N (Q i \<inter> A)) + \<infinity> * emeasure M (Q0 \<inter> A)" .
      moreover have "(\<Sum>i. N (Q i \<inter> A)) = N ((\<Union>i. Q i) \<inter> A)"
        using Q Q_sets `A \<in> sets M`
        by (subst suminf_emeasure) (auto simp: disjoint_family_on_def sets_eq)
      moreover have "\<infinity> * emeasure M (Q0 \<inter> A) = N (Q0 \<inter> A)"
      proof -
        have "Q0 \<inter> A \<in> sets M" using Q0(1) `A \<in> sets M` by blast
        from in_Q0[OF this] show ?thesis by auto
      qed
      moreover have "Q0 \<inter> A \<in> sets M" "((\<Union>i. Q i) \<inter> A) \<in> sets M"
        using Q_sets `A \<in> sets M` Q0(1) by auto
      moreover have "((\<Union>i. Q i) \<inter> A) \<union> (Q0 \<inter> A) = A" "((\<Union>i. Q i) \<inter> A) \<inter> (Q0 \<inter> A) = {}"
        using `A \<in> sets M` sets_into_space Q0 by auto
      ultimately have "N A = (\<integral>\<^isup>+x. ?f x * indicator A x \<partial>M)"
        using plus_emeasure[of "(\<Union>i. Q i) \<inter> A" N "Q0 \<inter> A"] by (simp add: sets_eq)
      with `A \<in> sets M` borel Q Q0(1) show "emeasure (density M ?f) A = N A"
        by (subst emeasure_density)
           (auto intro!: borel_measurable_ereal_add borel_measurable_psuminf measurable_If
                 simp: subset_eq)
    qed (simp add: sets_eq)
  qed
qed

lemma (in sigma_finite_measure) Radon_Nikodym:
  assumes ac: "absolutely_continuous M N" assumes sets_eq: "sets N = sets M"
  shows "\<exists>f \<in> borel_measurable M. (\<forall>x. 0 \<le> f x) \<and> density M f = N"
proof -
  from Ex_finite_integrable_function
  obtain h where finite: "integral\<^isup>P M h \<noteq> \<infinity>" and
    borel: "h \<in> borel_measurable M" and
    nn: "\<And>x. 0 \<le> h x" and
    pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x" and
    "\<And>x. x \<in> space M \<Longrightarrow> h x < \<infinity>" by auto
  let ?T = "\<lambda>A. (\<integral>\<^isup>+x. h x * indicator A x \<partial>M)"
  let ?MT = "density M h"
  from borel finite nn interpret T: finite_measure ?MT
    by (auto intro!: finite_measureI cong: positive_integral_cong simp: emeasure_density)
  have "absolutely_continuous ?MT N" "sets N = sets ?MT"
  proof (unfold absolutely_continuous_def, safe)
    fix A assume "A \<in> null_sets ?MT"
    with borel have "A \<in> sets M" "AE x in M. x \<in> A \<longrightarrow> h x \<le> 0"
      by (auto simp add: null_sets_density_iff)
    with pos sets_into_space have "AE x in M. x \<notin> A"
      by (elim eventually_elim1) (auto simp: not_le[symmetric])
    then have "A \<in> null_sets M"
      using `A \<in> sets M` by (simp add: AE_iff_null_sets)
    with ac show "A \<in> null_sets N"
      by (auto simp: absolutely_continuous_def)
  qed (auto simp add: sets_eq)
  from T.Radon_Nikodym_finite_measure_infinite[OF this]
  obtain f where f_borel: "f \<in> borel_measurable M" "\<And>x. 0 \<le> f x" "density ?MT f = N" by auto
  with nn borel show ?thesis
    by (auto intro!: bexI[of _ "\<lambda>x. h x * f x"] simp: density_density_eq)
qed

section "Uniqueness of densities"

lemma finite_density_unique:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes pos: "AE x in M. 0 \<le> f x" "AE x in M. 0 \<le> g x"
  and fin: "integral\<^isup>P M f \<noteq> \<infinity>"
  shows "(\<forall>A\<in>sets M. (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. g x * indicator A x \<partial>M))
    \<longleftrightarrow> (AE x in M. f x = g x)"
    (is "(\<forall>A\<in>sets M. ?P f A = ?P g A) \<longleftrightarrow> _")
proof (intro iffI ballI)
  fix A assume eq: "AE x in M. f x = g x"
  then show "?P f A = ?P g A"
    by (auto intro: positive_integral_cong_AE)
next
  assume eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
  from this[THEN bspec, OF top] fin
  have g_fin: "integral\<^isup>P M g \<noteq> \<infinity>" by (simp cong: positive_integral_cong)
  { fix f g assume borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
      and pos: "AE x in M. 0 \<le> f x" "AE x in M. 0 \<le> g x"
      and g_fin: "integral\<^isup>P M g \<noteq> \<infinity>" and eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
    let ?N = "{x\<in>space M. g x < f x}"
    have N: "?N \<in> sets M" using borel by simp
    have "?P g ?N \<le> integral\<^isup>P M g" using pos
      by (intro positive_integral_mono_AE) (auto split: split_indicator)
    then have Pg_fin: "?P g ?N \<noteq> \<infinity>" using g_fin by auto
    have "?P (\<lambda>x. (f x - g x)) ?N = (\<integral>\<^isup>+x. f x * indicator ?N x - g x * indicator ?N x \<partial>M)"
      by (auto intro!: positive_integral_cong simp: indicator_def)
    also have "\<dots> = ?P f ?N - ?P g ?N"
    proof (rule positive_integral_diff)
      show "(\<lambda>x. f x * indicator ?N x) \<in> borel_measurable M" "(\<lambda>x. g x * indicator ?N x) \<in> borel_measurable M"
        using borel N by auto
      show "AE x in M. g x * indicator ?N x \<le> f x * indicator ?N x"
           "AE x in M. 0 \<le> g x * indicator ?N x"
        using pos by (auto split: split_indicator)
    qed fact
    also have "\<dots> = 0"
      unfolding eq[THEN bspec, OF N] using positive_integral_positive[of M] Pg_fin by auto
    finally have "AE x in M. f x \<le> g x"
      using pos borel positive_integral_PInf_AE[OF borel(2) g_fin]
      by (subst (asm) positive_integral_0_iff_AE)
         (auto split: split_indicator simp: not_less ereal_minus_le_iff) }
  from this[OF borel pos g_fin eq] this[OF borel(2,1) pos(2,1) fin] eq
  show "AE x in M. f x = g x" by auto
qed

lemma (in finite_measure) density_unique_finite_measure:
  assumes borel: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes pos: "AE x in M. 0 \<le> f x" "AE x in M. 0 \<le> f' x"
  assumes f: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. f' x * indicator A x \<partial>M)"
    (is "\<And>A. A \<in> sets M \<Longrightarrow> ?P f A = ?P f' A")
  shows "AE x in M. f x = f' x"
proof -
  let ?D = "\<lambda>f. density M f"
  let ?N = "\<lambda>A. ?P f A" and ?N' = "\<lambda>A. ?P f' A"
  let ?f = "\<lambda>A x. f x * indicator A x" and ?f' = "\<lambda>A x. f' x * indicator A x"

  have ac: "absolutely_continuous M (density M f)" "sets (density M f) = sets M"
    using borel by (auto intro!: absolutely_continuousI_density) 
  from split_space_into_finite_sets_and_rest[OF this]
  obtain Q0 and Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and Q0: "Q0 \<in> sets M" "Q0 = space M - (\<Union>i. Q i)"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> emeasure M A = 0 \<and> ?D f A = 0 \<or> 0 < emeasure M A \<and> ?D f A = \<infinity>"
    and Q_fin: "\<And>i. ?D f (Q i) \<noteq> \<infinity>" by force
  with borel pos have in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> emeasure M A = 0 \<and> ?N A = 0 \<or> 0 < emeasure M A \<and> ?N A = \<infinity>"
    and Q_fin: "\<And>i. ?N (Q i) \<noteq> \<infinity>" by (auto simp: emeasure_density subset_eq)

  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  let ?D = "{x\<in>space M. f x \<noteq> f' x}"
  have "?D \<in> sets M" using borel by auto
  have *: "\<And>i x A. \<And>y::ereal. y * indicator (Q i) x * indicator A x = y * indicator (Q i \<inter> A) x"
    unfolding indicator_def by auto
  have "\<forall>i. AE x in M. ?f (Q i) x = ?f' (Q i) x" using borel Q_fin Q pos
    by (intro finite_density_unique[THEN iffD1] allI)
       (auto intro!: borel_measurable_ereal_times f Int simp: *)
  moreover have "AE x in M. ?f Q0 x = ?f' Q0 x"
  proof (rule AE_I')
    { fix f :: "'a \<Rightarrow> ereal" assume borel: "f \<in> borel_measurable M"
        and eq: "\<And>A. A \<in> sets M \<Longrightarrow> ?N A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
      let ?A = "\<lambda>i. Q0 \<inter> {x \<in> space M. f x < (i::nat)}"
      have "(\<Union>i. ?A i) \<in> null_sets M"
      proof (rule null_sets_UN)
        fix i ::nat have "?A i \<in> sets M"
          using borel Q0(1) by auto
        have "?N (?A i) \<le> (\<integral>\<^isup>+x. (i::ereal) * indicator (?A i) x \<partial>M)"
          unfolding eq[OF `?A i \<in> sets M`]
          by (auto intro!: positive_integral_mono simp: indicator_def)
        also have "\<dots> = i * emeasure M (?A i)"
          using `?A i \<in> sets M` by (auto intro!: positive_integral_cmult_indicator)
        also have "\<dots> < \<infinity>" using emeasure_real[of "?A i"] by simp
        finally have "?N (?A i) \<noteq> \<infinity>" by simp
        then show "?A i \<in> null_sets M" using in_Q0[OF `?A i \<in> sets M`] `?A i \<in> sets M` by auto
      qed
      also have "(\<Union>i. ?A i) = Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>}"
        by (auto simp: less_PInf_Ex_of_nat real_eq_of_nat)
      finally have "Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>} \<in> null_sets M" by simp }
    from this[OF borel(1) refl] this[OF borel(2) f]
    have "Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>} \<in> null_sets M" "Q0 \<inter> {x\<in>space M. f' x \<noteq> \<infinity>} \<in> null_sets M" by simp_all
    then show "(Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>}) \<union> (Q0 \<inter> {x\<in>space M. f' x \<noteq> \<infinity>}) \<in> null_sets M" by (rule null_sets.Un)
    show "{x \<in> space M. ?f Q0 x \<noteq> ?f' Q0 x} \<subseteq>
      (Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>}) \<union> (Q0 \<inter> {x\<in>space M. f' x \<noteq> \<infinity>})" by (auto simp: indicator_def)
  qed
  moreover have "AE x in M. (?f Q0 x = ?f' Q0 x) \<longrightarrow> (\<forall>i. ?f (Q i) x = ?f' (Q i) x) \<longrightarrow>
    ?f (space M) x = ?f' (space M) x"
    by (auto simp: indicator_def Q0)
  ultimately have "AE x in M. ?f (space M) x = ?f' (space M) x"
    unfolding AE_all_countable[symmetric]
    by eventually_elim (auto intro!: AE_I2 split: split_if_asm simp: indicator_def)
  then show "AE x in M. f x = f' x" by auto
qed

lemma (in sigma_finite_measure) density_unique:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes f': "f' \<in> borel_measurable M" "AE x in M. 0 \<le> f' x"
  assumes density_eq: "density M f = density M f'"
  shows "AE x in M. f x = f' x"
proof -
  obtain h where h_borel: "h \<in> borel_measurable M"
    and fin: "integral\<^isup>P M h \<noteq> \<infinity>" and pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x \<and> h x < \<infinity>" "\<And>x. 0 \<le> h x"
    using Ex_finite_integrable_function by auto
  then have h_nn: "AE x in M. 0 \<le> h x" by auto
  let ?H = "density M h"
  interpret h: finite_measure ?H
    using fin h_borel pos
    by (intro finite_measureI) (simp cong: positive_integral_cong emeasure_density add: fin)
  let ?fM = "density M f"
  let ?f'M = "density M f'"
  { fix A assume "A \<in> sets M"
    then have "{x \<in> space M. h x * indicator A x \<noteq> 0} = A"
      using pos(1) sets_into_space by (force simp: indicator_def)
    then have "(\<integral>\<^isup>+x. h x * indicator A x \<partial>M) = 0 \<longleftrightarrow> A \<in> null_sets M"
      using h_borel `A \<in> sets M` h_nn by (subst positive_integral_0_iff) auto }
  note h_null_sets = this
  { fix A assume "A \<in> sets M"
    have "(\<integral>\<^isup>+x. f x * (h x * indicator A x) \<partial>M) = (\<integral>\<^isup>+x. h x * indicator A x \<partial>?fM)"
      using `A \<in> sets M` h_borel h_nn f f'
      by (intro positive_integral_density[symmetric]) auto
    also have "\<dots> = (\<integral>\<^isup>+x. h x * indicator A x \<partial>?f'M)"
      by (simp_all add: density_eq)
    also have "\<dots> = (\<integral>\<^isup>+x. f' x * (h x * indicator A x) \<partial>M)"
      using `A \<in> sets M` h_borel h_nn f f'
      by (intro positive_integral_density) auto
    finally have "(\<integral>\<^isup>+x. h x * (f x * indicator A x) \<partial>M) = (\<integral>\<^isup>+x. h x * (f' x * indicator A x) \<partial>M)"
      by (simp add: ac_simps)
    then have "(\<integral>\<^isup>+x. (f x * indicator A x) \<partial>?H) = (\<integral>\<^isup>+x. (f' x * indicator A x) \<partial>?H)"
      using `A \<in> sets M` h_borel h_nn f f'
      by (subst (asm) (1 2) positive_integral_density[symmetric]) auto }
  then have "AE x in ?H. f x = f' x" using h_borel h_nn f f'
    by (intro h.density_unique_finite_measure absolutely_continuous_AE[of M])
       (auto simp add: AE_density)
  then show "AE x in M. f x = f' x"
    unfolding eventually_ae_filter using h_borel pos
    by (auto simp add: h_null_sets null_sets_density_iff not_less[symmetric]
                          AE_iff_null_sets[symmetric])
       blast
qed

lemma (in sigma_finite_measure) density_unique_iff:
  assumes f: "f \<in> borel_measurable M" and "AE x in M. 0 \<le> f x"
  assumes f': "f' \<in> borel_measurable M" and "AE x in M. 0 \<le> f' x"
  shows "density M f = density M f' \<longleftrightarrow> (AE x in M. f x = f' x)"
  using density_unique[OF assms] density_cong[OF f f'] by auto

lemma (in sigma_finite_measure) sigma_finite_iff_density_finite:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  shows "sigma_finite_measure (density M f) \<longleftrightarrow> (AE x in M. f x \<noteq> \<infinity>)"
    (is "sigma_finite_measure ?N \<longleftrightarrow> _")
proof
  assume "sigma_finite_measure ?N"
  then interpret N: sigma_finite_measure ?N .
  from N.Ex_finite_integrable_function obtain h where
    h: "h \<in> borel_measurable M" "integral\<^isup>P ?N h \<noteq> \<infinity>" and
    h_nn: "\<And>x. 0 \<le> h x" and
    fin: "\<forall>x\<in>space M. 0 < h x \<and> h x < \<infinity>" by auto
  have "AE x in M. f x * h x \<noteq> \<infinity>"
  proof (rule AE_I')
    have "integral\<^isup>P ?N h = (\<integral>\<^isup>+x. f x * h x \<partial>M)" using f h h_nn
      by (auto intro!: positive_integral_density)
    then have "(\<integral>\<^isup>+x. f x * h x \<partial>M) \<noteq> \<infinity>"
      using h(2) by simp
    then show "(\<lambda>x. f x * h x) -` {\<infinity>} \<inter> space M \<in> null_sets M"
      using f h(1) by (auto intro!: positive_integral_PInf borel_measurable_vimage)
  qed auto
  then show "AE x in M. f x \<noteq> \<infinity>"
    using fin by (auto elim!: AE_Ball_mp)
next
  assume AE: "AE x in M. f x \<noteq> \<infinity>"
  from sigma_finite guess Q .. note Q = this
  def A \<equiv> "\<lambda>i. f -` (case i of 0 \<Rightarrow> {\<infinity>} | Suc n \<Rightarrow> {.. ereal(of_nat (Suc n))}) \<inter> space M"
  { fix i j have "A i \<inter> Q j \<in> sets M"
    unfolding A_def using f Q
    apply (rule_tac Int)
    by (cases i) (auto intro: measurable_sets[OF f(1)]) }
  note A_in_sets = this
  let ?A = "\<lambda>n. case prod_decode n of (i,j) \<Rightarrow> A i \<inter> Q j"
  show "sigma_finite_measure ?N"
  proof (default, intro exI conjI subsetI allI)
    fix x assume "x \<in> range ?A"
    then obtain n where n: "x = ?A n" by auto
    then show "x \<in> sets ?N" using A_in_sets by (cases "prod_decode n") auto
  next
    have "(\<Union>i. ?A i) = (\<Union>i j. A i \<inter> Q j)"
    proof safe
      fix x i j assume "x \<in> A i" "x \<in> Q j"
      then show "x \<in> (\<Union>i. case prod_decode i of (i, j) \<Rightarrow> A i \<inter> Q j)"
        by (intro UN_I[of "prod_encode (i,j)"]) auto
    qed auto
    also have "\<dots> = (\<Union>i. A i) \<inter> space M" using Q by auto
    also have "(\<Union>i. A i) = space M"
    proof safe
      fix x assume x: "x \<in> space M"
      show "x \<in> (\<Union>i. A i)"
      proof (cases "f x")
        case PInf with x show ?thesis unfolding A_def by (auto intro: exI[of _ 0])
      next
        case (real r)
        with less_PInf_Ex_of_nat[of "f x"] obtain n :: nat where "f x < n" by (auto simp: real_eq_of_nat)
        then show ?thesis using x real unfolding A_def by (auto intro!: exI[of _ "Suc n"] simp: real_eq_of_nat)
      next
        case MInf with x show ?thesis
          unfolding A_def by (auto intro!: exI[of _ "Suc 0"])
      qed
    qed (auto simp: A_def)
    finally show "(\<Union>i. ?A i) = space ?N" by simp
  next
    fix n obtain i j where
      [simp]: "prod_decode n = (i, j)" by (cases "prod_decode n") auto
    have "(\<integral>\<^isup>+x. f x * indicator (A i \<inter> Q j) x \<partial>M) \<noteq> \<infinity>"
    proof (cases i)
      case 0
      have "AE x in M. f x * indicator (A i \<inter> Q j) x = 0"
        using AE by (auto simp: A_def `i = 0`)
      from positive_integral_cong_AE[OF this] show ?thesis by simp
    next
      case (Suc n)
      then have "(\<integral>\<^isup>+x. f x * indicator (A i \<inter> Q j) x \<partial>M) \<le>
        (\<integral>\<^isup>+x. (Suc n :: ereal) * indicator (Q j) x \<partial>M)"
        by (auto intro!: positive_integral_mono simp: indicator_def A_def real_eq_of_nat)
      also have "\<dots> = Suc n * emeasure M (Q j)"
        using Q by (auto intro!: positive_integral_cmult_indicator)
      also have "\<dots> < \<infinity>"
        using Q by (auto simp: real_eq_of_nat[symmetric])
      finally show ?thesis by simp
    qed
    then show "emeasure ?N (?A n) \<noteq> \<infinity>"
      using A_in_sets Q f by (auto simp: emeasure_density)
  qed
qed

section "Radon-Nikodym derivative"

definition
  "RN_deriv M N \<equiv> SOME f. f \<in> borel_measurable M \<and> (\<forall>x. 0 \<le> f x) \<and> density M f = N"

lemma
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  shows borel_measurable_RN_deriv_density: "RN_deriv M (density M f) \<in> borel_measurable M" (is ?borel)
    and density_RN_deriv_density: "density M (RN_deriv M (density M f)) = density M f" (is ?density)
    and RN_deriv_density_nonneg: "0 \<le> RN_deriv M (density M f) x" (is ?pos)
proof -
  let ?f = "\<lambda>x. max 0 (f x)"
  let ?P = "\<lambda>g. g \<in> borel_measurable M \<and> (\<forall>x. 0 \<le> g x) \<and> density M g = density M f"
  from f have "?P ?f" using f by (auto intro!: density_cong simp: split: split_max)
  then have "?P (RN_deriv M (density M f))"
    unfolding RN_deriv_def by (rule someI[where P="?P"])
  then show ?borel ?density ?pos by auto
qed

lemma (in sigma_finite_measure) RN_deriv:
  assumes "absolutely_continuous M N" "sets N = sets M"
  shows borel_measurable_RN_deriv: "RN_deriv M N \<in> borel_measurable M" (is ?borel)
    and density_RN_deriv: "density M (RN_deriv M N) = N" (is ?density)
    and RN_deriv_nonneg: "0 \<le> RN_deriv M N x" (is ?pos)
proof -
  note Ex = Radon_Nikodym[OF assms, unfolded Bex_def]
  from Ex show ?borel unfolding RN_deriv_def by (rule someI2_ex) simp
  from Ex show ?density unfolding RN_deriv_def by (rule someI2_ex) simp
  from Ex show ?pos unfolding RN_deriv_def by (rule someI2_ex) simp
qed

lemma (in sigma_finite_measure) RN_deriv_positive_integral:
  assumes N: "absolutely_continuous M N" "sets N = sets M"
    and f: "f \<in> borel_measurable M"
  shows "integral\<^isup>P N f = (\<integral>\<^isup>+x. RN_deriv M N x * f x \<partial>M)"
proof -
  have "integral\<^isup>P N f = integral\<^isup>P (density M (RN_deriv M N)) f"
    using N by (simp add: density_RN_deriv)
  also have "\<dots> = (\<integral>\<^isup>+x. RN_deriv M N x * f x \<partial>M)"
    using RN_deriv(1,3)[OF N] f by (simp add: positive_integral_density)
  finally show ?thesis by simp
qed

lemma null_setsD_AE: "N \<in> null_sets M \<Longrightarrow> AE x in M. x \<notin> N"
  using AE_iff_null_sets[of N M] by auto

lemma (in sigma_finite_measure) RN_deriv_unique:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  and eq: "density M f = N"
  shows "AE x in M. f x = RN_deriv M N x"
proof (rule density_unique)
  have ac: "absolutely_continuous M N"
    using f(1) unfolding eq[symmetric] by (rule absolutely_continuousI_density)
  have eq2: "sets N = sets M"
    unfolding eq[symmetric] by simp
  show "RN_deriv M N \<in> borel_measurable M" "AE x in M. 0 \<le> RN_deriv M N x"
    "density M f = density M (RN_deriv M N)"
    using RN_deriv[OF ac eq2] eq by auto
qed fact+

lemma (in sigma_finite_measure) RN_deriv_distr:
  fixes T :: "'a \<Rightarrow> 'b"
  assumes T: "T \<in> measurable M M'" and T': "T' \<in> measurable M' M"
    and inv: "\<forall>x\<in>space M. T' (T x) = x"
  and ac: "absolutely_continuous (distr M M' T) (distr N M' T)"
  and N: "sets N = sets M"
  shows "AE x in M. RN_deriv (distr M M' T) (distr N M' T) (T x) = RN_deriv M N x"
proof (rule RN_deriv_unique)
  have [simp]: "sets N = sets M" by fact
  note sets_eq_imp_space_eq[OF N, simp]
  have measurable_N[simp]: "\<And>M'. measurable N M' = measurable M M'" by (auto simp: measurable_def)
  { fix A assume "A \<in> sets M"
    with inv T T' sets_into_space[OF this]
    have "T -` T' -` A \<inter> T -` space M' \<inter> space M = A"
      by (auto simp: measurable_def) }
  note eq = this[simp]
  { fix A assume "A \<in> sets M"
    with inv T T' sets_into_space[OF this]
    have "(T' \<circ> T) -` A \<inter> space M = A"
      by (auto simp: measurable_def) }
  note eq2 = this[simp]
  let ?M' = "distr M M' T" and ?N' = "distr N M' T"
  interpret M': sigma_finite_measure ?M'
  proof
    from sigma_finite guess F .. note F = this
    show "\<exists>A::nat \<Rightarrow> 'b set. range A \<subseteq> sets ?M' \<and> (\<Union>i. A i) = space ?M' \<and> (\<forall>i. emeasure ?M' (A i) \<noteq> \<infinity>)"
    proof (intro exI conjI allI)
      show *: "range (\<lambda>i. T' -` F i \<inter> space ?M') \<subseteq> sets ?M'"
        using F T' by (auto simp: measurable_def)
      show "(\<Union>i. T' -` F i \<inter> space ?M') = space ?M'"
        using F T' by (force simp: measurable_def)
      fix i
      have "T' -` F i \<inter> space M' \<in> sets M'" using * by auto
      moreover
      have Fi: "F i \<in> sets M" using F by auto
      ultimately show "emeasure ?M' (T' -` F i \<inter> space ?M') \<noteq> \<infinity>"
        using F T T' by (simp add: emeasure_distr)
    qed
  qed
  have "(RN_deriv ?M' ?N') \<circ> T \<in> borel_measurable M"
    using T ac by (intro measurable_comp[where b="?M'"] M'.borel_measurable_RN_deriv) simp_all
  then show "(\<lambda>x. RN_deriv ?M' ?N' (T x)) \<in> borel_measurable M"
    by (simp add: comp_def)
  show "AE x in M. 0 \<le> RN_deriv ?M' ?N' (T x)" using M'.RN_deriv_nonneg[OF ac] by auto

  have "N = distr N M (T' \<circ> T)"
    by (subst measure_of_of_measure[of N, symmetric])
       (auto simp add: distr_def sigma_sets_eq intro!: measure_of_eq space_closed)
  also have "\<dots> = distr (distr N M' T) M T'"
    using T T' by (simp add: distr_distr)
  also have "\<dots> = distr (density (distr M M' T) (RN_deriv (distr M M' T) (distr N M' T))) M T'"
    using ac by (simp add: M'.density_RN_deriv)
  also have "\<dots> = density M (RN_deriv (distr M M' T) (distr N M' T) \<circ> T)"
    using M'.borel_measurable_RN_deriv[OF ac] by (simp add: distr_density_distr[OF T T', OF inv])
  finally show "density M (\<lambda>x. RN_deriv (distr M M' T) (distr N M' T) (T x)) = N"
    by (simp add: comp_def)
qed

lemma (in sigma_finite_measure) RN_deriv_finite:
  assumes N: "sigma_finite_measure N" and ac: "absolutely_continuous M N" "sets N = sets M"
  shows "AE x in M. RN_deriv M N x \<noteq> \<infinity>"
proof -
  interpret N: sigma_finite_measure N by fact
  from N show ?thesis
    using sigma_finite_iff_density_finite[OF RN_deriv(1)[OF ac]] RN_deriv(2,3)[OF ac] by simp
qed

lemma (in sigma_finite_measure)
  assumes N: "sigma_finite_measure N" and ac: "absolutely_continuous M N" "sets N = sets M"
    and f: "f \<in> borel_measurable M"
  shows RN_deriv_integrable: "integrable N f \<longleftrightarrow>
      integrable M (\<lambda>x. real (RN_deriv M N x) * f x)" (is ?integrable)
    and RN_deriv_integral: "integral\<^isup>L N f =
      (\<integral>x. real (RN_deriv M N x) * f x \<partial>M)" (is ?integral)
proof -
  note ac(2)[simp] and sets_eq_imp_space_eq[OF ac(2), simp]
  interpret N: sigma_finite_measure N by fact
  have minus_cong: "\<And>A B A' B'::ereal. A = A' \<Longrightarrow> B = B' \<Longrightarrow> real A - real B = real A' - real B'" by simp
  have f': "(\<lambda>x. - f x) \<in> borel_measurable M" using f by auto
  have Nf: "f \<in> borel_measurable N" using f by (simp add: measurable_def)
  { fix f :: "'a \<Rightarrow> real"
    { fix x assume *: "RN_deriv M N x \<noteq> \<infinity>"
      have "ereal (real (RN_deriv M N x)) * ereal (f x) = ereal (real (RN_deriv M N x) * f x)"
        by (simp add: mult_le_0_iff)
      then have "RN_deriv M N x * ereal (f x) = ereal (real (RN_deriv M N x) * f x)"
        using RN_deriv(3)[OF ac] * by (auto simp add: ereal_real split: split_if_asm) }
    then have "(\<integral>\<^isup>+x. ereal (real (RN_deriv M N x) * f x) \<partial>M) = (\<integral>\<^isup>+x. RN_deriv M N x * ereal (f x) \<partial>M)"
              "(\<integral>\<^isup>+x. ereal (- (real (RN_deriv M N x) * f x)) \<partial>M) = (\<integral>\<^isup>+x. RN_deriv M N x * ereal (- f x) \<partial>M)"
      using RN_deriv_finite[OF N ac] unfolding ereal_mult_minus_right uminus_ereal.simps(1)[symmetric]
      by (auto intro!: positive_integral_cong_AE) }
  note * = this
  show ?integral ?integrable
    unfolding lebesgue_integral_def integrable_def *
    using Nf f RN_deriv(1)[OF ac]
    by (auto simp: RN_deriv_positive_integral[OF ac])
qed

lemma (in sigma_finite_measure) real_RN_deriv:
  assumes "finite_measure N"
  assumes ac: "absolutely_continuous M N" "sets N = sets M"
  obtains D where "D \<in> borel_measurable M"
    and "AE x in M. RN_deriv M N x = ereal (D x)"
    and "AE x in N. 0 < D x"
    and "\<And>x. 0 \<le> D x"
proof
  interpret N: finite_measure N by fact
  
  note RN = RN_deriv[OF ac]

  let ?RN = "\<lambda>t. {x \<in> space M. RN_deriv M N x = t}"

  show "(\<lambda>x. real (RN_deriv M N x)) \<in> borel_measurable M"
    using RN by auto

  have "N (?RN \<infinity>) = (\<integral>\<^isup>+ x. RN_deriv M N x * indicator (?RN \<infinity>) x \<partial>M)"
    using RN(1,3) by (subst RN(2)[symmetric]) (auto simp: emeasure_density)
  also have "\<dots> = (\<integral>\<^isup>+ x. \<infinity> * indicator (?RN \<infinity>) x \<partial>M)"
    by (intro positive_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = \<infinity> * emeasure M (?RN \<infinity>)"
    using RN by (intro positive_integral_cmult_indicator) auto
  finally have eq: "N (?RN \<infinity>) = \<infinity> * emeasure M (?RN \<infinity>)" .
  moreover
  have "emeasure M (?RN \<infinity>) = 0"
  proof (rule ccontr)
    assume "emeasure M {x \<in> space M. RN_deriv M N x = \<infinity>} \<noteq> 0"
    moreover from RN have "0 \<le> emeasure M {x \<in> space M. RN_deriv M N x = \<infinity>}" by auto
    ultimately have "0 < emeasure M {x \<in> space M. RN_deriv M N x = \<infinity>}" by auto
    with eq have "N (?RN \<infinity>) = \<infinity>" by simp
    with N.emeasure_finite[of "?RN \<infinity>"] RN show False by auto
  qed
  ultimately have "AE x in M. RN_deriv M N x < \<infinity>"
    using RN by (intro AE_iff_measurable[THEN iffD2]) auto
  then show "AE x in M. RN_deriv M N x = ereal (real (RN_deriv M N x))"
    using RN(3) by (auto simp: ereal_real)
  then have eq: "AE x in N. RN_deriv M N x = ereal (real (RN_deriv M N x))"
    using ac absolutely_continuous_AE by auto

  show "\<And>x. 0 \<le> real (RN_deriv M N x)"
    using RN by (auto intro: real_of_ereal_pos)

  have "N (?RN 0) = (\<integral>\<^isup>+ x. RN_deriv M N x * indicator (?RN 0) x \<partial>M)"
    using RN(1,3) by (subst RN(2)[symmetric]) (auto simp: emeasure_density)
  also have "\<dots> = (\<integral>\<^isup>+ x. 0 \<partial>M)"
    by (intro positive_integral_cong) (auto simp: indicator_def)
  finally have "AE x in N. RN_deriv M N x \<noteq> 0"
    using RN by (subst AE_iff_measurable[OF _ refl]) (auto simp: ac cong: sets_eq_imp_space_eq)
  with RN(3) eq show "AE x in N. 0 < real (RN_deriv M N x)"
    by (auto simp: zero_less_real_of_ereal le_less)
qed

lemma (in sigma_finite_measure) RN_deriv_singleton:
  assumes ac: "absolutely_continuous M N" "sets N = sets M"
  and x: "{x} \<in> sets M"
  shows "N {x} = RN_deriv M N x * emeasure M {x}"
proof -
  note deriv = RN_deriv[OF ac]
  from deriv(1,3) `{x} \<in> sets M`
  have "density M (RN_deriv M N) {x} = (\<integral>\<^isup>+w. RN_deriv M N x * indicator {x} w \<partial>M)"
    by (auto simp: indicator_def emeasure_density intro!: positive_integral_cong)
  with x deriv show ?thesis
    by (auto simp: positive_integral_cmult_indicator)
qed

end
