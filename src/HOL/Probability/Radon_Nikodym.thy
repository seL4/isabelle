(*  Title:      HOL/Probability/Radon_Nikodym.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Radon-Nikod{\'y}m derivative*}

theory Radon_Nikodym
imports Lebesgue_Integration
begin

lemma (in sigma_finite_measure) Ex_finite_integrable_function:
  shows "\<exists>h\<in>borel_measurable M. integral\<^isup>P M h \<noteq> \<infinity> \<and> (\<forall>x\<in>space M. 0 < h x \<and> h x < \<infinity>) \<and> (\<forall>x. 0 \<le> h x)"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. \<mu> (A i) \<noteq> \<infinity>" and
    disjoint: "disjoint_family A"
    using disjoint_sigma_finite by auto
  let "?B i" = "2^Suc i * \<mu> (A i)"
  have "\<forall>i. \<exists>x. 0 < x \<and> x < inverse (?B i)"
  proof
    fix i have Ai: "A i \<in> sets M" using range by auto
    from measure positive_measure[OF this]
    show "\<exists>x. 0 < x \<and> x < inverse (?B i)"
      by (auto intro!: ereal_dense simp: ereal_0_gt_inverse)
  qed
  from choice[OF this] obtain n where n: "\<And>i. 0 < n i"
    "\<And>i. n i < inverse (2^Suc i * \<mu> (A i))" by auto
  { fix i have "0 \<le> n i" using n(1)[of i] by auto } note pos = this
  let "?h x" = "\<Sum>i. n i * indicator (A i) x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?h] del: notI)
    have "\<And>i. A i \<in> sets M"
      using range by fastforce+
    then have "integral\<^isup>P M ?h = (\<Sum>i. n i * \<mu> (A i))" using pos
      by (simp add: positive_integral_suminf positive_integral_cmult_indicator)
    also have "\<dots> \<le> (\<Sum>i. (1 / 2)^Suc i)"
    proof (rule suminf_le_pos)
      fix N
      have "n N * \<mu> (A N) \<le> inverse (2^Suc N * \<mu> (A N)) * \<mu> (A N)"
        using positive_measure[OF `A N \<in> sets M`] n[of N]
        by (intro ereal_mult_right_mono) auto
      also have "\<dots> \<le> (1 / 2) ^ Suc N"
        using measure[of N] n[of N]
        by (cases rule: ereal2_cases[of "n N" "\<mu> (A N)"])
           (simp_all add: inverse_eq_divide power_divide one_ereal_def ereal_power_divide)
      finally show "n N * \<mu> (A N) \<le> (1 / 2) ^ Suc N" .
      show "0 \<le> n N * \<mu> (A N)" using n[of N] `A N \<in> sets M` by simp
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

definition (in measure_space)
  "absolutely_continuous \<nu> = (\<forall>N\<in>null_sets. \<nu> N = (0 :: ereal))"

lemma (in measure_space) absolutely_continuous_AE:
  assumes "measure_space M'" and [simp]: "sets M' = sets M" "space M' = space M"
    and "absolutely_continuous (measure M')" "AE x. P x"
   shows "AE x in M'. P x"
proof -
  interpret \<nu>: measure_space M' by fact
  from `AE x. P x` obtain N where N: "N \<in> null_sets" and "{x\<in>space M. \<not> P x} \<subseteq> N"
    unfolding almost_everywhere_def by auto
  show "AE x in M'. P x"
  proof (rule \<nu>.AE_I')
    show "{x\<in>space M'. \<not> P x} \<subseteq> N" by simp fact
    from `absolutely_continuous (measure M')` show "N \<in> \<nu>.null_sets"
      using N unfolding absolutely_continuous_def by auto
  qed
qed

lemma (in finite_measure_space) absolutely_continuousI:
  assumes "finite_measure_space (M\<lparr> measure := \<nu>\<rparr>)" (is "finite_measure_space ?\<nu>")
  assumes v: "\<And>x. \<lbrakk> x \<in> space M ; \<mu> {x} = 0 \<rbrakk> \<Longrightarrow> \<nu> {x} = 0"
  shows "absolutely_continuous \<nu>"
proof (unfold absolutely_continuous_def sets_eq_Pow, safe)
  fix N assume "\<mu> N = 0" "N \<subseteq> space M"
  interpret v: finite_measure_space ?\<nu> by fact
  have "\<nu> N = measure ?\<nu> (\<Union>x\<in>N. {x})" by simp
  also have "\<dots> = (\<Sum>x\<in>N. measure ?\<nu> {x})"
  proof (rule v.measure_setsum[symmetric])
    show "finite N" using `N \<subseteq> space M` finite_space by (auto intro: finite_subset)
    show "disjoint_family_on (\<lambda>i. {i}) N" unfolding disjoint_family_on_def by auto
    fix x assume "x \<in> N" thus "{x} \<in> sets ?\<nu>" using `N \<subseteq> space M` sets_eq_Pow by auto
  qed
  also have "\<dots> = 0"
  proof (safe intro!: setsum_0')
    fix x assume "x \<in> N"
    hence "\<mu> {x} \<le> \<mu> N" "0 \<le> \<mu> {x}"
      using sets_eq_Pow `N \<subseteq> space M` positive_measure[of "{x}"]
      by (auto intro!: measure_mono)
    then have "\<mu> {x} = 0" using `\<mu> N = 0` by simp
    thus "measure ?\<nu> {x} = 0" using v[of x] `x \<in> N` `N \<subseteq> space M` by auto
  qed
  finally show "\<nu> N = 0" by simp
qed

lemma (in measure_space) density_is_absolutely_continuous:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
  shows "absolutely_continuous \<nu>"
  using assms unfolding absolutely_continuous_def
  by (simp add: positive_integral_null_set)

subsection "Existence of the Radon-Nikodym derivative"

lemma (in finite_measure) Radon_Nikodym_aux_epsilon:
  fixes e :: real assumes "0 < e"
  assumes "finite_measure (M\<lparr>measure := \<nu>\<rparr>)"
  shows "\<exists>A\<in>sets M. \<mu>' (space M) - finite_measure.\<mu>' (M\<lparr>measure := \<nu>\<rparr>) (space M) \<le>
                    \<mu>' A - finite_measure.\<mu>' (M\<lparr>measure := \<nu>\<rparr>) A \<and>
                    (\<forall>B\<in>sets M. B \<subseteq> A \<longrightarrow> - e < \<mu>' B - finite_measure.\<mu>' (M\<lparr>measure := \<nu>\<rparr>) B)"
proof -
  interpret M': finite_measure "M\<lparr>measure := \<nu>\<rparr>" by fact
  let "?d A" = "\<mu>' A - M'.\<mu>' A"
  let "?A A" = "if (\<forall>B\<in>sets M. B \<subseteq> space M - A \<longrightarrow> -e < ?d B)
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
        using `A n \<in> sets M` finite_measure_Union M'.finite_measure_Union by simp
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
          using A_in_sets sets_into_space dA_mono[of n]
          by (simp del: A_simps add: finite_measure_Diff M'.finite_measure_Diff)
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
        case 0 with M'.empty_measure show ?case by (simp add: zero_ereal_def)
      qed } note dA_less = this
    have decseq: "decseq (\<lambda>n. ?d (A n))" unfolding decseq_eq_incseq
    proof (rule incseq_SucI)
      fix n show "- ?d (A n) \<le> - ?d (A (Suc n))" using dA_mono[of n] by auto
    qed
    have A: "incseq A" by (auto intro!: incseq_SucI)
    from finite_continuity_from_below[OF _ A] `range A \<subseteq> sets M`
      M'.finite_continuity_from_below[OF _ A]
    have convergent: "(\<lambda>i. ?d (A i)) ----> ?d (\<Union>i. A i)"
      by (auto intro!: tendsto_diff)
    obtain n :: nat where "- ?d (\<Union>i. A i) / e < real n" using reals_Archimedean2 by auto
    moreover from order_trans[OF decseq_le[OF decseq convergent] dA_less]
    have "real n \<le> - ?d (\<Union>i. A i) / e" using `0<e` by (simp add: field_simps)
    ultimately show ?thesis by auto
  qed
qed

lemma (in finite_measure) restricted_measure_subset:
  assumes S: "S \<in> sets M" and X: "X \<subseteq> S"
  shows "finite_measure.\<mu>' (restricted_space S) X = \<mu>' X"
proof cases
  note r = restricted_finite_measure[OF S]
  { assume "X \<in> sets M" with S X show ?thesis
      unfolding finite_measure.\<mu>'_def[OF r] \<mu>'_def by auto }
  { assume "X \<notin> sets M"
    moreover then have "S \<inter> X \<notin> sets M"
      using X by (simp add: Int_absorb1)
    ultimately show ?thesis
      unfolding finite_measure.\<mu>'_def[OF r] \<mu>'_def using S by auto }
qed

lemma (in finite_measure) restricted_measure:
  assumes X: "S \<in> sets M" "X \<in> sets (restricted_space S)"
  shows "finite_measure.\<mu>' (restricted_space S) X = \<mu>' X"
proof -
  from X have "S \<in> sets M" "X \<subseteq> S" by auto
  from restricted_measure_subset[OF this] show ?thesis .
qed

lemma (in finite_measure) Radon_Nikodym_aux:
  assumes "finite_measure (M\<lparr>measure := \<nu>\<rparr>)" (is "finite_measure ?M'")
  shows "\<exists>A\<in>sets M. \<mu>' (space M) - finite_measure.\<mu>' (M\<lparr>measure := \<nu>\<rparr>) (space M) \<le>
                    \<mu>' A - finite_measure.\<mu>' (M\<lparr>measure := \<nu>\<rparr>) A \<and>
                    (\<forall>B\<in>sets M. B \<subseteq> A \<longrightarrow> 0 \<le> \<mu>' B - finite_measure.\<mu>' (M\<lparr>measure := \<nu>\<rparr>) B)"
proof -
  interpret M': finite_measure ?M' where
    "space ?M' = space M" and "sets ?M' = sets M" and "measure ?M' = \<nu>" by fact auto
  let "?d A" = "\<mu>' A - M'.\<mu>' A"
  let "?P A B n" = "A \<in> sets M \<and> A \<subseteq> B \<and> ?d B \<le> ?d A \<and> (\<forall>C\<in>sets M. C \<subseteq> A \<longrightarrow> - 1 / real (Suc n) < ?d C)"
  let "?r S" = "restricted_space S"
  { fix S n assume S: "S \<in> sets M"
    note r = M'.restricted_finite_measure[of S] restricted_finite_measure[OF S] S
    then have "finite_measure (?r S)" "0 < 1 / real (Suc n)"
      "finite_measure (?r S\<lparr>measure := \<nu>\<rparr>)" by auto
    from finite_measure.Radon_Nikodym_aux_epsilon[OF this] guess X .. note X = this
    have "?P X S n"
    proof (intro conjI ballI impI)
      show "X \<in> sets M" "X \<subseteq> S" using X(1) `S \<in> sets M` by auto
      have "S \<in> op \<inter> S ` sets M" using `S \<in> sets M` by auto
      then show "?d S \<le> ?d X"
        using S X restricted_measure[OF S] M'.restricted_measure[OF S] by simp
      fix C assume "C \<in> sets M" "C \<subseteq> X"
      then have "C \<in> sets (restricted_space S)" "C \<subseteq> X"
        using `S \<in> sets M` `X \<subseteq> S` by auto
      with X(2) show "- 1 / real (Suc n) < ?d C"
        using S X restricted_measure[OF S] M'.restricted_measure[OF S] by auto
    qed
    hence "\<exists>A. ?P A S n" by auto }
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
    from
      finite_continuity_from_above[OF `range A \<subseteq> sets M` A]
      M'.finite_continuity_from_above[OF `range A \<subseteq> sets M` A]
    have "(\<lambda>i. ?d (A i)) ----> ?d (\<Inter>i. A i)" by (intro tendsto_diff)
    thus "?d (space M) \<le> ?d (\<Inter>i. A i)" using mono_dA[THEN monoD, of 0 _]
      by (rule_tac LIMSEQ_le_const) (auto intro!: exI)
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
  assumes "finite_measure (M\<lparr> measure := \<nu>\<rparr>)" (is "finite_measure ?M'")
  assumes "absolutely_continuous \<nu>"
  shows "\<exists>f \<in> borel_measurable M. \<forall>A\<in>sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
proof -
  interpret M': finite_measure ?M'
    where "space ?M' = space M" and "sets ?M' = sets M" and "measure ?M' = \<nu>"
    using assms(1) by auto
  def G \<equiv> "{g \<in> borel_measurable M. (\<forall>x. 0 \<le> g x) \<and> (\<forall>A\<in>sets M. (\<integral>\<^isup>+x. g x * indicator A x \<partial>M) \<le> \<nu> A)}"
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
      have union: "((?A \<inter> A) \<union> ((space M - ?A) \<inter> A)) = A"
        using sets_into_space[OF `A \<in> sets M`] by auto
      have "\<And>x. x \<in> space M \<Longrightarrow> max (g x) (f x) * indicator A x =
        g x * indicator (?A \<inter> A) x + f x * indicator ((space M - ?A) \<inter> A) x"
        by (auto simp: indicator_def max_def)
      hence "(\<integral>\<^isup>+x. max (g x) (f x) * indicator A x \<partial>M) =
        (\<integral>\<^isup>+x. g x * indicator (?A \<inter> A) x \<partial>M) +
        (\<integral>\<^isup>+x. f x * indicator ((space M - ?A) \<inter> A) x \<partial>M)"
        using f g sets unfolding G_def
        by (auto cong: positive_integral_cong intro!: positive_integral_add borel_measurable_indicator)
      also have "\<dots> \<le> \<nu> (?A \<inter> A) + \<nu> ((space M - ?A) \<inter> A)"
        using f g sets unfolding G_def by (auto intro!: add_mono)
      also have "\<dots> = \<nu> A"
        using M'.measure_additive[OF sets] union by auto
      finally show "(\<integral>\<^isup>+x. max (g x) (f x) * indicator A x \<partial>M) \<le> \<nu> A" .
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
      finally show "(\<integral>\<^isup>+x. (SUP i. f i x) * indicator A x \<partial>M) \<le> \<nu> A"
        using f `A \<in> sets M` by (auto intro!: SUP_least simp: G_def)
    qed }
  note SUP_in_G = this
  let ?y = "SUP g : G. integral\<^isup>P M g"
  have "?y \<le> \<nu> (space M)" unfolding G_def
  proof (safe intro!: SUP_least)
    fix g assume "\<forall>A\<in>sets M. (\<integral>\<^isup>+x. g x * indicator A x \<partial>M) \<le> \<nu> A"
    from this[THEN bspec, OF top] show "integral\<^isup>P M g \<le> \<nu> (space M)"
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
  let "?g i x" = "Max ((\<lambda>n. gs n x) ` {..i})"
  def f \<equiv> "\<lambda>x. SUP i. ?g i x"
  let "?F A x" = "f x * indicator A x"
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
      using g_in_G
      by (auto intro!: exI Sup_mono simp: SUP_def)
    show "?y \<le> (SUP i. integral\<^isup>P M (?g i))" unfolding y_eq
      by (auto intro!: SUP_mono positive_integral_mono Max_ge)
  qed
  finally have int_f_eq_y: "integral\<^isup>P M f = ?y" .
  have "\<And>x. 0 \<le> f x"
    unfolding f_def using `\<And>i. gs i \<in> G`
    by (auto intro!: SUP_upper2 Max_ge_iff[THEN iffD2] simp: G_def)
  let "?t A" = "\<nu> A - (\<integral>\<^isup>+x. ?F A x \<partial>M)"
  let ?M = "M\<lparr> measure := ?t\<rparr>"
  interpret M: sigma_algebra ?M
    by (intro sigma_algebra_cong) auto
  have f_le_\<nu>: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. ?F A x \<partial>M) \<le> \<nu> A"
    using `f \<in> G` unfolding G_def by auto
  have fmM: "finite_measure ?M"
  proof (default, simp_all add: countably_additive_def positive_def, safe del: notI)
    fix A :: "nat \<Rightarrow> 'a set"  assume A: "range A \<subseteq> sets M" "disjoint_family A"
    have "(\<Sum>n. (\<integral>\<^isup>+x. ?F (A n) x \<partial>M)) = (\<integral>\<^isup>+x. (\<Sum>n. ?F (A n) x) \<partial>M)"
      using `range A \<subseteq> sets M` `\<And>x. 0 \<le> f x`
      by (intro positive_integral_suminf[symmetric]) auto
    also have "\<dots> = (\<integral>\<^isup>+x. ?F (\<Union>n. A n) x \<partial>M)"
      using `\<And>x. 0 \<le> f x`
      by (intro positive_integral_cong) (simp add: suminf_cmult_ereal suminf_indicator[OF `disjoint_family A`])
    finally have "(\<Sum>n. (\<integral>\<^isup>+x. ?F (A n) x \<partial>M)) = (\<integral>\<^isup>+x. ?F (\<Union>n. A n) x \<partial>M)" .
    moreover have "(\<Sum>n. \<nu> (A n)) = \<nu> (\<Union>n. A n)"
      using M'.measure_countably_additive A by (simp add: comp_def)
    moreover have v_fin: "\<nu> (\<Union>i. A i) \<noteq> \<infinity>" using M'.finite_measure A by (simp add: countable_UN)
    moreover {
      have "(\<integral>\<^isup>+x. ?F (\<Union>i. A i) x \<partial>M) \<le> \<nu> (\<Union>i. A i)"
        using A `f \<in> G` unfolding G_def by (auto simp: countable_UN)
      also have "\<nu> (\<Union>i. A i) < \<infinity>" using v_fin by simp
      finally have "(\<integral>\<^isup>+x. ?F (\<Union>i. A i) x \<partial>M) \<noteq> \<infinity>" by simp }
    moreover have "\<And>i. (\<integral>\<^isup>+x. ?F (A i) x \<partial>M) \<le> \<nu> (A i)"
      using A by (intro f_le_\<nu>) auto
    ultimately
    show "(\<Sum>n. ?t (A n)) = ?t (\<Union>i. A i)"
      by (subst suminf_ereal_minus) (simp_all add: positive_integral_positive)
  next
    fix A assume A: "A \<in> sets M" show "0 \<le> \<nu> A - \<integral>\<^isup>+ x. ?F A x \<partial>M"
      using f_le_\<nu>[OF A] `f \<in> G` M'.finite_measure[OF A] by (auto simp: G_def ereal_le_minus_iff)
  next
    show "\<nu> (space M) - (\<integral>\<^isup>+ x. ?F (space M) x \<partial>M) \<noteq> \<infinity>" (is "?a - ?b \<noteq> _")
      using positive_integral_positive[of "?F (space M)"]
      by (cases rule: ereal2_cases[of ?a ?b]) auto
  qed
  then interpret M: finite_measure ?M
    where "space ?M = space M" and "sets ?M = sets M" and "measure ?M = ?t"
    by (simp_all add: fmM)
  have ac: "absolutely_continuous ?t" unfolding absolutely_continuous_def
  proof
    fix N assume N: "N \<in> null_sets"
    with `absolutely_continuous \<nu>` have "\<nu> N = 0" unfolding absolutely_continuous_def by auto
    moreover with N have "(\<integral>\<^isup>+ x. ?F N x \<partial>M) \<le> \<nu> N" using `f \<in> G` by (auto simp: G_def)
    ultimately show "\<nu> N - (\<integral>\<^isup>+ x. ?F N x \<partial>M) = 0"
      using positive_integral_positive by (auto intro!: antisym)
  qed
  have upper_bound: "\<forall>A\<in>sets M. ?t A \<le> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain A where A: "A \<in> sets M" and pos: "0 < ?t A"
      by (auto simp: not_le)
    note pos
    also have "?t A \<le> ?t (space M)"
      using M.measure_mono[of A "space M"] A sets_into_space by simp
    finally have pos_t: "0 < ?t (space M)" by simp
    moreover
    then have "\<mu> (space M) \<noteq> 0"
      using ac unfolding absolutely_continuous_def by auto
    then have pos_M: "0 < \<mu> (space M)"
      using positive_measure[OF top] by (simp add: le_less)
    moreover
    have "(\<integral>\<^isup>+x. f x * indicator (space M) x \<partial>M) \<le> \<nu> (space M)"
      using `f \<in> G` unfolding G_def by auto
    hence "(\<integral>\<^isup>+x. f x * indicator (space M) x \<partial>M) \<noteq> \<infinity>"
      using M'.finite_measure_of_space by auto
    moreover
    def b \<equiv> "?t (space M) / \<mu> (space M) / 2"
    ultimately have b: "b \<noteq> 0 \<and> 0 \<le> b \<and> b \<noteq> \<infinity>"
      using M'.finite_measure_of_space positive_integral_positive[of "?F (space M)"]
      by (cases rule: ereal3_cases[of "integral\<^isup>P M (?F (space M))" "\<nu> (space M)" "\<mu> (space M)"])
         (simp_all add: field_simps)
    then have b: "b \<noteq> 0" "0 \<le> b" "0 < b"  "b \<noteq> \<infinity>" by auto
    let ?Mb = "?M\<lparr>measure := \<lambda>A. b * \<mu> A\<rparr>"
    interpret b: sigma_algebra ?Mb by (intro sigma_algebra_cong) auto
    have Mb: "finite_measure ?Mb"
    proof
      show "positive ?Mb (measure ?Mb)"
        using `0 \<le> b` by (auto simp: positive_def)
      show "countably_additive ?Mb (measure ?Mb)"
        using `0 \<le> b` measure_countably_additive
        by (auto simp: countably_additive_def suminf_cmult_ereal subset_eq)
      show "measure ?Mb (space ?Mb) \<noteq> \<infinity>"
        using b by auto
    qed
    from M.Radon_Nikodym_aux[OF this]
    obtain A0 where "A0 \<in> sets M" and
      space_less_A0: "real (?t (space M)) - real (b * \<mu> (space M)) \<le> real (?t A0) - real (b * \<mu> A0)" and
      *: "\<And>B. \<lbrakk> B \<in> sets M ; B \<subseteq> A0 \<rbrakk> \<Longrightarrow> 0 \<le> real (?t B) - real (b * \<mu> B)"
      unfolding M.\<mu>'_def finite_measure.\<mu>'_def[OF Mb] by auto
    { fix B assume B: "B \<in> sets M" "B \<subseteq> A0"
      with *[OF this] have "b * \<mu> B \<le> ?t B"
        using M'.finite_measure b finite_measure M.positive_measure[OF B(1)]
        by (cases rule: ereal2_cases[of "?t B" "b * \<mu> B"]) auto }
    note bM_le_t = this
    let "?f0 x" = "f x + b * indicator A0 x"
    { fix A assume A: "A \<in> sets M"
      hence "A \<inter> A0 \<in> sets M" using `A0 \<in> sets M` by auto
      have "(\<integral>\<^isup>+x. ?f0 x  * indicator A x \<partial>M) =
        (\<integral>\<^isup>+x. f x * indicator A x + b * indicator (A \<inter> A0) x \<partial>M)"
        by (auto intro!: positive_integral_cong split: split_indicator)
      hence "(\<integral>\<^isup>+x. ?f0 x * indicator A x \<partial>M) =
          (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) + b * \<mu> (A \<inter> A0)"
        using `A0 \<in> sets M` `A \<inter> A0 \<in> sets M` A b `f \<in> G`
        by (simp add: G_def positive_integral_add positive_integral_cmult_indicator) }
    note f0_eq = this
    { fix A assume A: "A \<in> sets M"
      hence "A \<inter> A0 \<in> sets M" using `A0 \<in> sets M` by auto
      have f_le_v: "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) \<le> \<nu> A"
        using `f \<in> G` A unfolding G_def by auto
      note f0_eq[OF A]
      also have "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) + b * \<mu> (A \<inter> A0) \<le>
          (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) + ?t (A \<inter> A0)"
        using bM_le_t[OF `A \<inter> A0 \<in> sets M`] `A \<in> sets M` `A0 \<in> sets M`
        by (auto intro!: add_left_mono)
      also have "\<dots> \<le> (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) + ?t A"
        using M.measure_mono[simplified, OF _ `A \<inter> A0 \<in> sets M` `A \<in> sets M`]
        by (auto intro!: add_left_mono)
      also have "\<dots> \<le> \<nu> A"
        using f_le_v M'.finite_measure[simplified, OF `A \<in> sets M`] positive_integral_positive[of "?F A"]
        by (cases "\<integral>\<^isup>+x. ?F A x \<partial>M", cases "\<nu> A") auto
      finally have "(\<integral>\<^isup>+x. ?f0 x * indicator A x \<partial>M) \<le> \<nu> A" . }
    hence "?f0 \<in> G" using `A0 \<in> sets M` b `f \<in> G` unfolding G_def
      by (auto intro!: borel_measurable_indicator borel_measurable_ereal_add
                       borel_measurable_ereal_times ereal_add_nonneg_nonneg)
    have real: "?t (space M) \<noteq> \<infinity>" "?t A0 \<noteq> \<infinity>"
      "b * \<mu> (space M) \<noteq> \<infinity>" "b * \<mu> A0 \<noteq> \<infinity>"
      using `A0 \<in> sets M` b
        finite_measure[of A0] M.finite_measure[of A0]
        finite_measure_of_space M.finite_measure_of_space
      by auto
    have int_f_finite: "integral\<^isup>P M f \<noteq> \<infinity>"
      using M'.finite_measure_of_space pos_t unfolding ereal_less_minus_iff
      by (auto cong: positive_integral_cong)
    have  "0 < ?t (space M) - b * \<mu> (space M)" unfolding b_def
      using finite_measure_of_space M'.finite_measure_of_space pos_t pos_M
      using positive_integral_positive[of "?F (space M)"]
      by (cases rule: ereal3_cases[of "\<mu> (space M)" "\<nu> (space M)" "integral\<^isup>P M (?F (space M))"])
         (auto simp: field_simps mult_less_cancel_left)
    also have "\<dots> \<le> ?t A0 - b * \<mu> A0"
      using space_less_A0 b
      using
        `A0 \<in> sets M`[THEN M.real_measure]
        top[THEN M.real_measure]
      apply safe
      apply simp
      using
        `A0 \<in> sets M`[THEN real_measure]
        `A0 \<in> sets M`[THEN M'.real_measure]
        top[THEN real_measure]
        top[THEN M'.real_measure]
      by (cases b) auto
    finally have 1: "b * \<mu> A0 < ?t A0"
      using
        `A0 \<in> sets M`[THEN M.real_measure]
      apply safe
      apply simp
      using
        `A0 \<in> sets M`[THEN real_measure]
        `A0 \<in> sets M`[THEN M'.real_measure]
      by (cases b) auto
    have "0 < ?t A0"
      using b `A0 \<in> sets M` by (auto intro!: le_less_trans[OF _ 1])
    then have "\<mu> A0 \<noteq> 0" using ac unfolding absolutely_continuous_def
      using `A0 \<in> sets M` by auto
    then have "0 < \<mu> A0" using positive_measure[OF `A0 \<in> sets M`] by auto
    hence "0 < b * \<mu> A0" using b by (auto simp: ereal_zero_less_0_iff)
    with int_f_finite have "?y + 0 < integral\<^isup>P M f + b * \<mu> A0" unfolding int_f_eq_y
      using `f \<in> G`
      by (intro ereal_add_strict_mono) (auto intro!: SUP_upper2 positive_integral_positive)
    also have "\<dots> = integral\<^isup>P M ?f0" using f0_eq[OF top] `A0 \<in> sets M` sets_into_space
      by (simp cong: positive_integral_cong)
    finally have "?y < integral\<^isup>P M ?f0" by simp
    moreover from `?f0 \<in> G` have "integral\<^isup>P M ?f0 \<le> ?y" by (auto intro!: SUP_upper)
    ultimately show False by auto
  qed
  show ?thesis
  proof (safe intro!: bexI[of _ f])
    fix A assume A: "A\<in>sets M"
    show "\<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
    proof (rule antisym)
      show "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) \<le> \<nu> A"
        using `f \<in> G` `A \<in> sets M` unfolding G_def by auto
      show "\<nu> A \<le> (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
        using upper_bound[THEN bspec, OF `A \<in> sets M`]
        using M'.real_measure[OF A]
        by (cases "integral\<^isup>P M (?F A)") auto
    qed
  qed simp
qed

lemma (in finite_measure) split_space_into_finite_sets_and_rest:
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)" (is "measure_space ?N")
  assumes ac: "absolutely_continuous \<nu>"
  shows "\<exists>A0\<in>sets M. \<exists>B::nat\<Rightarrow>'a set. disjoint_family B \<and> range B \<subseteq> sets M \<and> A0 = space M - (\<Union>i. B i) \<and>
    (\<forall>A\<in>sets M. A \<subseteq> A0 \<longrightarrow> (\<mu> A = 0 \<and> \<nu> A = 0) \<or> (\<mu> A > 0 \<and> \<nu> A = \<infinity>)) \<and>
    (\<forall>i. \<nu> (B i) \<noteq> \<infinity>)"
proof -
  interpret v: measure_space ?N
    where "space ?N = space M" and "sets ?N = sets M" and "measure ?N = \<nu>"
    by fact auto
  let ?Q = "{Q\<in>sets M. \<nu> Q \<noteq> \<infinity>}"
  let ?a = "SUP Q:?Q. \<mu> Q"
  have "{} \<in> ?Q" using v.empty_measure by auto
  then have Q_not_empty: "?Q \<noteq> {}" by blast
  have "?a \<le> \<mu> (space M)" using sets_into_space
    by (auto intro!: SUP_least measure_mono top)
  then have "?a \<noteq> \<infinity>" using finite_measure_of_space
    by auto
  from SUPR_countable_SUPR[OF Q_not_empty, of \<mu>]
  obtain Q'' where "range Q'' \<subseteq> \<mu> ` ?Q" and a: "?a = (SUP i::nat. Q'' i)"
    by auto
  then have "\<forall>i. \<exists>Q'. Q'' i = \<mu> Q' \<and> Q' \<in> ?Q" by auto
  from choice[OF this] obtain Q' where Q': "\<And>i. Q'' i = \<mu> (Q' i)" "\<And>i. Q' i \<in> ?Q"
    by auto
  then have a_Lim: "?a = (SUP i::nat. \<mu> (Q' i))" using a by simp
  let "?O n" = "\<Union>i\<le>n. Q' i"
  have Union: "(SUP i. \<mu> (?O i)) = \<mu> (\<Union>i. ?O i)"
  proof (rule continuity_from_below[of ?O])
    show "range ?O \<subseteq> sets M" using Q' by (auto intro!: finite_UN)
    show "incseq ?O" by (fastforce intro!: incseq_SucI)
  qed
  have Q'_sets: "\<And>i. Q' i \<in> sets M" using Q' by auto
  have O_sets: "\<And>i. ?O i \<in> sets M"
     using Q' by (auto intro!: finite_UN Un)
  then have O_in_G: "\<And>i. ?O i \<in> ?Q"
  proof (safe del: notI)
    fix i have "Q' ` {..i} \<subseteq> sets M"
      using Q' by (auto intro: finite_UN)
    with v.measure_finitely_subadditive[of "{.. i}" Q']
    have "\<nu> (?O i) \<le> (\<Sum>i\<le>i. \<nu> (Q' i))" by auto
    also have "\<dots> < \<infinity>" using Q' by (simp add: setsum_Pinfty)
    finally show "\<nu> (?O i) \<noteq> \<infinity>" by simp
  qed auto
  have O_mono: "\<And>n. ?O n \<subseteq> ?O (Suc n)" by fastforce
  have a_eq: "?a = \<mu> (\<Union>i. ?O i)" unfolding Union[symmetric]
  proof (rule antisym)
    show "?a \<le> (SUP i. \<mu> (?O i))" unfolding a_Lim
      using Q' by (auto intro!: SUP_mono measure_mono finite_UN)
    show "(SUP i. \<mu> (?O i)) \<le> ?a" unfolding SUP_def
    proof (safe intro!: Sup_mono, unfold bex_simps)
      fix i
      have *: "(\<Union>Q' ` {..i}) = ?O i" by auto
      then show "\<exists>x. (x \<in> sets M \<and> \<nu> x \<noteq> \<infinity>) \<and>
        \<mu> (\<Union>Q' ` {..i}) \<le> \<mu> x"
        using O_in_G[of i] by (auto intro!: exI[of _ "?O i"])
    qed
  qed
  let "?O_0" = "(\<Union>i. ?O i)"
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
      show "\<mu> A = 0 \<and> \<nu> A = 0 \<or> 0 < \<mu> A \<and> \<nu> A = \<infinity>"
      proof (rule disjCI, simp)
        assume *: "0 < \<mu> A \<longrightarrow> \<nu> A \<noteq> \<infinity>"
        show "\<mu> A = 0 \<and> \<nu> A = 0"
        proof cases
          assume "\<mu> A = 0" moreover with ac A have "\<nu> A = 0"
            unfolding absolutely_continuous_def by auto
          ultimately show ?thesis by simp
        next
          assume "\<mu> A \<noteq> 0" with * have "\<nu> A \<noteq> \<infinity>" using positive_measure[OF A(1)] by auto
          with A have "\<mu> ?O_0 + \<mu> A = \<mu> (?O_0 \<union> A)"
            using Q' by (auto intro!: measure_additive countable_UN)
          also have "\<dots> = (SUP i. \<mu> (?O i \<union> A))"
          proof (rule continuity_from_below[of "\<lambda>i. ?O i \<union> A", symmetric, simplified])
            show "range (\<lambda>i. ?O i \<union> A) \<subseteq> sets M"
              using `\<nu> A \<noteq> \<infinity>` O_sets A by auto
          qed (fastforce intro!: incseq_SucI)
          also have "\<dots> \<le> ?a"
          proof (safe intro!: SUP_least)
            fix i have "?O i \<union> A \<in> ?Q"
            proof (safe del: notI)
              show "?O i \<union> A \<in> sets M" using O_sets A by auto
              from O_in_G[of i]
              moreover have "\<nu> (?O i \<union> A) \<le> \<nu> (?O i) + \<nu> A"
                using v.measure_subadditive[of "?O i" A] A O_sets by auto
              ultimately show "\<nu> (?O i \<union> A) \<noteq> \<infinity>"
                using `\<nu> A \<noteq> \<infinity>` by auto
            qed
            then show "\<mu> (?O i \<union> A) \<le> ?a" by (rule SUP_upper)
          qed
          finally have "\<mu> A = 0"
            unfolding a_eq using real_measure[OF `?O_0 \<in> sets M`] real_measure[OF A(1)] by auto
          with `\<mu> A \<noteq> 0` show ?thesis by auto
        qed
      qed }
    { fix i show "\<nu> (Q i) \<noteq> \<infinity>"
      proof (cases i)
        case 0 then show ?thesis
          unfolding Q_def using Q'[of 0] by simp
      next
        case (Suc n)
        then show ?thesis unfolding Q_def
          using `?O n \<in> ?Q` `?O (Suc n) \<in> ?Q`
          using v.measure_mono[OF O_mono, of n] v.positive_measure[of "?O n"] v.positive_measure[of "?O (Suc n)"]
          using v.measure_Diff[of "?O n" "?O (Suc n)", OF _ _ _ O_mono]
          by (cases rule: ereal2_cases[of "\<nu> (\<Union> x\<le>Suc n. Q' x)" "\<nu> (\<Union> i\<le>n. Q' i)"]) auto
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
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)" (is "measure_space ?N")
  assumes "absolutely_continuous \<nu>"
  shows "\<exists>f \<in> borel_measurable M. (\<forall>x. 0 \<le> f x) \<and> (\<forall>A\<in>sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M))"
proof -
  interpret v: measure_space ?N
    where "space ?N = space M" and "sets ?N = sets M" and "measure ?N = \<nu>"
    by fact auto
  from split_space_into_finite_sets_and_rest[OF assms]
  obtain Q0 and Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and Q0: "Q0 \<in> sets M" "Q0 = space M - (\<Union>i. Q i)"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> \<mu> A = 0 \<and> \<nu> A = 0 \<or> 0 < \<mu> A \<and> \<nu> A = \<infinity>"
    and Q_fin: "\<And>i. \<nu> (Q i) \<noteq> \<infinity>" by force
  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  have "\<forall>i. \<exists>f. f\<in>borel_measurable M \<and> (\<forall>x. 0 \<le> f x) \<and> (\<forall>A\<in>sets M.
    \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. f x * indicator (Q i \<inter> A) x \<partial>M))"
  proof
    fix i
    have indicator_eq: "\<And>f x A. (f x :: ereal) * indicator (Q i \<inter> A) x * indicator (Q i) x
      = (f x * indicator (Q i) x) * indicator A x"
      unfolding indicator_def by auto
    have fm: "finite_measure (restricted_space (Q i))"
      (is "finite_measure ?R") by (rule restricted_finite_measure[OF Q_sets[of i]])
    then interpret R: finite_measure ?R .
    have fmv: "finite_measure (restricted_space (Q i) \<lparr> measure := \<nu>\<rparr>)" (is "finite_measure ?Q")
      unfolding finite_measure_def finite_measure_axioms_def
    proof
      show "measure_space ?Q"
        using v.restricted_measure_space Q_sets[of i] by auto
      show "measure ?Q (space ?Q) \<noteq> \<infinity>" using Q_fin by simp
    qed
    have "R.absolutely_continuous \<nu>"
      using `absolutely_continuous \<nu>` `Q i \<in> sets M`
      by (auto simp: R.absolutely_continuous_def absolutely_continuous_def)
    from R.Radon_Nikodym_finite_measure[OF fmv this]
    obtain f where f: "(\<lambda>x. f x * indicator (Q i) x) \<in> borel_measurable M"
      and f_int: "\<And>A. A\<in>sets M \<Longrightarrow> \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. (f x * indicator (Q i) x) * indicator A x \<partial>M)"
      unfolding Bex_def borel_measurable_restricted[OF `Q i \<in> sets M`]
        positive_integral_restricted[OF `Q i \<in> sets M`] by (auto simp: indicator_eq)
    then show "\<exists>f. f\<in>borel_measurable M \<and> (\<forall>x. 0 \<le> f x) \<and> (\<forall>A\<in>sets M.
      \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. f x * indicator (Q i \<inter> A) x \<partial>M))"
      by (auto intro!: exI[of _ "\<lambda>x. max 0 (f x * indicator (Q i) x)"] positive_integral_cong_pos
        split: split_indicator split_if_asm simp: max_def)
  qed
  from choice[OF this] obtain f where borel: "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
    and f: "\<And>A i. A \<in> sets M \<Longrightarrow>
      \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. f i x * indicator (Q i \<inter> A) x \<partial>M)"
    by auto
  let "?f x" = "(\<Sum>i. f i x * indicator (Q i) x) + \<infinity> * indicator Q0 x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?f])
    show "?f \<in> borel_measurable M" using Q0 borel Q_sets
      by (auto intro!: measurable_If)
    show "\<And>x. 0 \<le> ?f x" using borel by (auto intro!: suminf_0_le simp: indicator_def)
    fix A assume "A \<in> sets M"
    have Qi: "\<And>i. Q i \<in> sets M" using Q by auto
    have [intro,simp]: "\<And>i. (\<lambda>x. f i x * indicator (Q i \<inter> A) x) \<in> borel_measurable M"
      "\<And>i. AE x. 0 \<le> f i x * indicator (Q i \<inter> A) x"
      using borel Qi Q0(1) `A \<in> sets M` by (auto intro!: borel_measurable_ereal_times)
    have "(\<integral>\<^isup>+x. ?f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. (\<Sum>i. f i x * indicator (Q i \<inter> A) x) + \<infinity> * indicator (Q0 \<inter> A) x \<partial>M)"
      using borel by (intro positive_integral_cong) (auto simp: indicator_def)
    also have "\<dots> = (\<integral>\<^isup>+x. (\<Sum>i. f i x * indicator (Q i \<inter> A) x) \<partial>M) + \<infinity> * \<mu> (Q0 \<inter> A)"
      using borel Qi Q0(1) `A \<in> sets M`
      by (subst positive_integral_add) (auto simp del: ereal_infty_mult
          simp add: positive_integral_cmult_indicator Int intro!: suminf_0_le)
    also have "\<dots> = (\<Sum>i. \<nu> (Q i \<inter> A)) + \<infinity> * \<mu> (Q0 \<inter> A)"
      by (subst f[OF `A \<in> sets M`], subst positive_integral_suminf) auto
    finally have "(\<integral>\<^isup>+x. ?f x * indicator A x \<partial>M) = (\<Sum>i. \<nu> (Q i \<inter> A)) + \<infinity> * \<mu> (Q0 \<inter> A)" .
    moreover have "(\<Sum>i. \<nu> (Q i \<inter> A)) = \<nu> ((\<Union>i. Q i) \<inter> A)"
      using Q Q_sets `A \<in> sets M`
      by (intro v.measure_countably_additive[of "\<lambda>i. Q i \<inter> A", unfolded comp_def, simplified])
         (auto simp: disjoint_family_on_def)
    moreover have "\<infinity> * \<mu> (Q0 \<inter> A) = \<nu> (Q0 \<inter> A)"
    proof -
      have "Q0 \<inter> A \<in> sets M" using Q0(1) `A \<in> sets M` by blast
      from in_Q0[OF this] show ?thesis by auto
    qed
    moreover have "Q0 \<inter> A \<in> sets M" "((\<Union>i. Q i) \<inter> A) \<in> sets M"
      using Q_sets `A \<in> sets M` Q0(1) by (auto intro!: countable_UN)
    moreover have "((\<Union>i. Q i) \<inter> A) \<union> (Q0 \<inter> A) = A" "((\<Union>i. Q i) \<inter> A) \<inter> (Q0 \<inter> A) = {}"
      using `A \<in> sets M` sets_into_space Q0 by auto
    ultimately show "\<nu> A = (\<integral>\<^isup>+x. ?f x * indicator A x \<partial>M)"
      using v.measure_additive[simplified, of "(\<Union>i. Q i) \<inter> A" "Q0 \<inter> A"]
      by simp
  qed
qed

lemma (in sigma_finite_measure) Radon_Nikodym:
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)" (is "measure_space ?N")
  assumes ac: "absolutely_continuous \<nu>"
  shows "\<exists>f \<in> borel_measurable M. (\<forall>x. 0 \<le> f x) \<and> (\<forall>A\<in>sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M))"
proof -
  from Ex_finite_integrable_function
  obtain h where finite: "integral\<^isup>P M h \<noteq> \<infinity>" and
    borel: "h \<in> borel_measurable M" and
    nn: "\<And>x. 0 \<le> h x" and
    pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x" and
    "\<And>x. x \<in> space M \<Longrightarrow> h x < \<infinity>" by auto
  let "?T A" = "(\<integral>\<^isup>+x. h x * indicator A x \<partial>M)"
  let ?MT = "M\<lparr> measure := ?T \<rparr>"
  interpret T: finite_measure ?MT
    where "space ?MT = space M" and "sets ?MT = sets M" and "measure ?MT = ?T"
    unfolding finite_measure_def finite_measure_axioms_def using borel finite nn
    by (auto intro!: measure_space_density cong: positive_integral_cong)
  have "T.absolutely_continuous \<nu>"
  proof (unfold T.absolutely_continuous_def, safe)
    fix N assume "N \<in> sets M" "(\<integral>\<^isup>+x. h x * indicator N x \<partial>M) = 0"
    with borel ac pos have "AE x. x \<notin> N"
      by (subst (asm) positive_integral_0_iff_AE) (auto split: split_indicator simp: not_le)
    then have "N \<in> null_sets" using `N \<in> sets M` sets_into_space
      by (subst (asm) AE_iff_measurable[OF `N \<in> sets M`]) auto
    then show "\<nu> N = 0" using ac by (auto simp: absolutely_continuous_def)
  qed
  from T.Radon_Nikodym_finite_measure_infinite[simplified, OF assms(1) this]
  obtain f where f_borel: "f \<in> borel_measurable M" "\<And>x. 0 \<le> f x" and
    fT: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+ x. f x * indicator A x \<partial>?MT)"
    by (auto simp: measurable_def)
  show ?thesis
  proof (safe intro!: bexI[of _ "\<lambda>x. h x * f x"])
    show "(\<lambda>x. h x * f x) \<in> borel_measurable M"
      using borel f_borel by (auto intro: borel_measurable_ereal_times)
    show "\<And>x. 0 \<le> h x * f x" using nn f_borel by auto
    fix A assume "A \<in> sets M"
    then show "\<nu> A = (\<integral>\<^isup>+x. h x * f x * indicator A x \<partial>M)"
      unfolding fT[OF `A \<in> sets M`] mult_assoc using nn borel f_borel
      by (intro positive_integral_translated_density) auto
  qed
qed

section "Uniqueness of densities"

lemma (in measure_space) finite_density_unique:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes pos: "AE x. 0 \<le> f x" "AE x. 0 \<le> g x"
  and fin: "integral\<^isup>P M f \<noteq> \<infinity>"
  shows "(\<forall>A\<in>sets M. (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. g x * indicator A x \<partial>M))
    \<longleftrightarrow> (AE x. f x = g x)"
    (is "(\<forall>A\<in>sets M. ?P f A = ?P g A) \<longleftrightarrow> _")
proof (intro iffI ballI)
  fix A assume eq: "AE x. f x = g x"
  then show "?P f A = ?P g A"
    by (auto intro: positive_integral_cong_AE)
next
  assume eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
  from this[THEN bspec, OF top] fin
  have g_fin: "integral\<^isup>P M g \<noteq> \<infinity>" by (simp cong: positive_integral_cong)
  { fix f g assume borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
      and pos: "AE x. 0 \<le> f x" "AE x. 0 \<le> g x"
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
      show "AE x. g x * indicator ?N x \<le> f x * indicator ?N x"
           "AE x. 0 \<le> g x * indicator ?N x"
        using pos by (auto split: split_indicator)
    qed fact
    also have "\<dots> = 0"
      unfolding eq[THEN bspec, OF N] using positive_integral_positive Pg_fin by auto
    finally have "AE x. f x \<le> g x"
      using pos borel positive_integral_PInf_AE[OF borel(2) g_fin]
      by (subst (asm) positive_integral_0_iff_AE)
         (auto split: split_indicator simp: not_less ereal_minus_le_iff) }
  from this[OF borel pos g_fin eq] this[OF borel(2,1) pos(2,1) fin] eq
  show "AE x. f x = g x" by auto
qed

lemma (in finite_measure) density_unique_finite_measure:
  assumes borel: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes pos: "AE x. 0 \<le> f x" "AE x. 0 \<le> f' x"
  assumes f: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. f' x * indicator A x \<partial>M)"
    (is "\<And>A. A \<in> sets M \<Longrightarrow> ?P f A = ?P f' A")
  shows "AE x. f x = f' x"
proof -
  let "?\<nu> A" = "?P f A" and "?\<nu>' A" = "?P f' A"
  let "?f A x" = "f x * indicator A x" and "?f' A x" = "f' x * indicator A x"
  interpret M: measure_space "M\<lparr> measure := ?\<nu>\<rparr>"
    using borel(1) pos(1) by (rule measure_space_density) simp
  have ac: "absolutely_continuous ?\<nu>"
    using f by (rule density_is_absolutely_continuous)
  from split_space_into_finite_sets_and_rest[OF `measure_space (M\<lparr> measure := ?\<nu>\<rparr>)` ac]
  obtain Q0 and Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and Q0: "Q0 \<in> sets M" "Q0 = space M - (\<Union>i. Q i)"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> \<mu> A = 0 \<and> ?\<nu> A = 0 \<or> 0 < \<mu> A \<and> ?\<nu> A = \<infinity>"
    and Q_fin: "\<And>i. ?\<nu> (Q i) \<noteq> \<infinity>" by force
  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  let ?N = "{x\<in>space M. f x \<noteq> f' x}"
  have "?N \<in> sets M" using borel by auto
  have *: "\<And>i x A. \<And>y::ereal. y * indicator (Q i) x * indicator A x = y * indicator (Q i \<inter> A) x"
    unfolding indicator_def by auto
  have "\<forall>i. AE x. ?f (Q i) x = ?f' (Q i) x" using borel Q_fin Q pos
    by (intro finite_density_unique[THEN iffD1] allI)
       (auto intro!: borel_measurable_ereal_times f Int simp: *)
  moreover have "AE x. ?f Q0 x = ?f' Q0 x"
  proof (rule AE_I')
    { fix f :: "'a \<Rightarrow> ereal" assume borel: "f \<in> borel_measurable M"
        and eq: "\<And>A. A \<in> sets M \<Longrightarrow> ?\<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
      let "?A i" = "Q0 \<inter> {x \<in> space M. f x < (i::nat)}"
      have "(\<Union>i. ?A i) \<in> null_sets"
      proof (rule null_sets_UN)
        fix i ::nat have "?A i \<in> sets M"
          using borel Q0(1) by auto
        have "?\<nu> (?A i) \<le> (\<integral>\<^isup>+x. (i::ereal) * indicator (?A i) x \<partial>M)"
          unfolding eq[OF `?A i \<in> sets M`]
          by (auto intro!: positive_integral_mono simp: indicator_def)
        also have "\<dots> = i * \<mu> (?A i)"
          using `?A i \<in> sets M` by (auto intro!: positive_integral_cmult_indicator)
        also have "\<dots> < \<infinity>"
          using `?A i \<in> sets M`[THEN finite_measure] by auto
        finally have "?\<nu> (?A i) \<noteq> \<infinity>" by simp
        then show "?A i \<in> null_sets" using in_Q0[OF `?A i \<in> sets M`] `?A i \<in> sets M` by auto
      qed
      also have "(\<Union>i. ?A i) = Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>}"
        by (auto simp: less_PInf_Ex_of_nat real_eq_of_nat)
      finally have "Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>} \<in> null_sets" by simp }
    from this[OF borel(1) refl] this[OF borel(2) f]
    have "Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>} \<in> null_sets" "Q0 \<inter> {x\<in>space M. f' x \<noteq> \<infinity>} \<in> null_sets" by simp_all
    then show "(Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>}) \<union> (Q0 \<inter> {x\<in>space M. f' x \<noteq> \<infinity>}) \<in> null_sets" by (rule nullsets.Un)
    show "{x \<in> space M. ?f Q0 x \<noteq> ?f' Q0 x} \<subseteq>
      (Q0 \<inter> {x\<in>space M. f x \<noteq> \<infinity>}) \<union> (Q0 \<inter> {x\<in>space M. f' x \<noteq> \<infinity>})" by (auto simp: indicator_def)
  qed
  moreover have "\<And>x. (?f Q0 x = ?f' Q0 x) \<longrightarrow> (\<forall>i. ?f (Q i) x = ?f' (Q i) x) \<longrightarrow>
    ?f (space M) x = ?f' (space M) x"
    by (auto simp: indicator_def Q0)
  ultimately have "AE x. ?f (space M) x = ?f' (space M) x"
    by (auto simp: AE_all_countable[symmetric])
  then show "AE x. f x = f' x" by auto
qed

lemma (in sigma_finite_measure) density_unique:
  assumes f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x"
  assumes f': "f' \<in> borel_measurable M" "AE x. 0 \<le> f' x"
  assumes eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. f' x * indicator A x \<partial>M)"
    (is "\<And>A. A \<in> sets M \<Longrightarrow> ?P f A = ?P f' A")
  shows "AE x. f x = f' x"
proof -
  obtain h where h_borel: "h \<in> borel_measurable M"
    and fin: "integral\<^isup>P M h \<noteq> \<infinity>" and pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x \<and> h x < \<infinity>" "\<And>x. 0 \<le> h x"
    using Ex_finite_integrable_function by auto
  then have h_nn: "AE x. 0 \<le> h x" by auto
  let ?H = "M\<lparr> measure := \<lambda>A. (\<integral>\<^isup>+x. h x * indicator A x \<partial>M) \<rparr>"
  have H: "measure_space ?H"
    using h_borel h_nn by (rule measure_space_density) simp
  then interpret h: measure_space ?H .
  interpret h: finite_measure "M\<lparr> measure := \<lambda>A. (\<integral>\<^isup>+x. h x * indicator A x \<partial>M) \<rparr>"
    by default (simp cong: positive_integral_cong add: fin)
  let ?fM = "M\<lparr>measure := \<lambda>A. (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)\<rparr>"
  interpret f: measure_space ?fM
    using f by (rule measure_space_density) simp
  let ?f'M = "M\<lparr>measure := \<lambda>A. (\<integral>\<^isup>+x. f' x * indicator A x \<partial>M)\<rparr>"
  interpret f': measure_space ?f'M
    using f' by (rule measure_space_density) simp
  { fix A assume "A \<in> sets M"
    then have "{x \<in> space M. h x * indicator A x \<noteq> 0} = A"
      using pos(1) sets_into_space by (force simp: indicator_def)
    then have "(\<integral>\<^isup>+x. h x * indicator A x \<partial>M) = 0 \<longleftrightarrow> A \<in> null_sets"
      using h_borel `A \<in> sets M` h_nn by (subst positive_integral_0_iff) auto }
  note h_null_sets = this
  { fix A assume "A \<in> sets M"
    have "(\<integral>\<^isup>+x. f x * (h x * indicator A x) \<partial>M) = (\<integral>\<^isup>+x. h x * indicator A x \<partial>?fM)"
      using `A \<in> sets M` h_borel h_nn f f'
      by (intro positive_integral_translated_density[symmetric]) auto
    also have "\<dots> = (\<integral>\<^isup>+x. h x * indicator A x \<partial>?f'M)"
      by (rule f'.positive_integral_cong_measure) (simp_all add: eq)
    also have "\<dots> = (\<integral>\<^isup>+x. f' x * (h x * indicator A x) \<partial>M)"
      using `A \<in> sets M` h_borel h_nn f f'
      by (intro positive_integral_translated_density) auto
    finally have "(\<integral>\<^isup>+x. h x * (f x * indicator A x) \<partial>M) = (\<integral>\<^isup>+x. h x * (f' x * indicator A x) \<partial>M)"
      by (simp add: ac_simps)
    then have "(\<integral>\<^isup>+x. (f x * indicator A x) \<partial>?H) = (\<integral>\<^isup>+x. (f' x * indicator A x) \<partial>?H)"
      using `A \<in> sets M` h_borel h_nn f f'
      by (subst (asm) (1 2) positive_integral_translated_density[symmetric]) auto }
  then have "AE x in ?H. f x = f' x" using h_borel h_nn f f'
    by (intro h.density_unique_finite_measure absolutely_continuous_AE[OF H] density_is_absolutely_continuous)
       simp_all
  then show "AE x. f x = f' x"
    unfolding h.almost_everywhere_def almost_everywhere_def
    by (auto simp add: h_null_sets)
qed

lemma (in sigma_finite_measure) sigma_finite_iff_density_finite:
  assumes \<nu>: "measure_space (M\<lparr>measure := \<nu>\<rparr>)" (is "measure_space ?N")
    and f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x"
    and eq: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
  shows "sigma_finite_measure (M\<lparr>measure := \<nu>\<rparr>) \<longleftrightarrow> (AE x. f x \<noteq> \<infinity>)"
proof
  assume "sigma_finite_measure ?N"
  then interpret \<nu>: sigma_finite_measure ?N
    where "borel_measurable ?N = borel_measurable M" and "measure ?N = \<nu>"
    and "sets ?N = sets M" and "space ?N = space M" by (auto simp: measurable_def)
  from \<nu>.Ex_finite_integrable_function obtain h where
    h: "h \<in> borel_measurable M" "integral\<^isup>P ?N h \<noteq> \<infinity>" and
    h_nn: "\<And>x. 0 \<le> h x" and
    fin: "\<forall>x\<in>space M. 0 < h x \<and> h x < \<infinity>" by auto
  have "AE x. f x * h x \<noteq> \<infinity>"
  proof (rule AE_I')
    have "integral\<^isup>P ?N h = (\<integral>\<^isup>+x. f x * h x \<partial>M)" using f h h_nn
      by (subst \<nu>.positive_integral_cong_measure[symmetric,
          of "M\<lparr> measure := \<lambda> A. \<integral>\<^isup>+x. f x * indicator A x \<partial>M \<rparr>"])
         (auto intro!: positive_integral_translated_density simp: eq)
    then have "(\<integral>\<^isup>+x. f x * h x \<partial>M) \<noteq> \<infinity>"
      using h(2) by simp
    then show "(\<lambda>x. f x * h x) -` {\<infinity>} \<inter> space M \<in> null_sets"
      using f h(1) by (auto intro!: positive_integral_PInf borel_measurable_vimage)
  qed auto
  then show "AE x. f x \<noteq> \<infinity>"
    using fin by (auto elim!: AE_Ball_mp)
next
  assume AE: "AE x. f x \<noteq> \<infinity>"
  from sigma_finite guess Q .. note Q = this
  interpret \<nu>: measure_space ?N
    where "borel_measurable ?N = borel_measurable M" and "measure ?N = \<nu>"
    and "sets ?N = sets M" and "space ?N = space M" using \<nu> by (auto simp: measurable_def)
  def A \<equiv> "\<lambda>i. f -` (case i of 0 \<Rightarrow> {\<infinity>} | Suc n \<Rightarrow> {.. ereal(of_nat (Suc n))}) \<inter> space M"
  { fix i j have "A i \<inter> Q j \<in> sets M"
    unfolding A_def using f Q
    apply (rule_tac Int)
    by (cases i) (auto intro: measurable_sets[OF f(1)]) }
  note A_in_sets = this
  let "?A n" = "case prod_decode n of (i,j) \<Rightarrow> A i \<inter> Q j"
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
      have "AE x. f x * indicator (A i \<inter> Q j) x = 0"
        using AE by (auto simp: A_def `i = 0`)
      from positive_integral_cong_AE[OF this] show ?thesis by simp
    next
      case (Suc n)
      then have "(\<integral>\<^isup>+x. f x * indicator (A i \<inter> Q j) x \<partial>M) \<le>
        (\<integral>\<^isup>+x. (Suc n :: ereal) * indicator (Q j) x \<partial>M)"
        by (auto intro!: positive_integral_mono simp: indicator_def A_def real_eq_of_nat)
      also have "\<dots> = Suc n * \<mu> (Q j)"
        using Q by (auto intro!: positive_integral_cmult_indicator)
      also have "\<dots> < \<infinity>"
        using Q by (auto simp: real_eq_of_nat[symmetric])
      finally show ?thesis by simp
    qed
    then show "measure ?N (?A n) \<noteq> \<infinity>"
      using A_in_sets Q eq by auto
  qed
qed

section "Radon-Nikodym derivative"

definition
  "RN_deriv M \<nu> \<equiv> SOME f. f \<in> borel_measurable M \<and> (\<forall>x. 0 \<le> f x) \<and>
    (\<forall>A \<in> sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M))"

lemma (in sigma_finite_measure) RN_deriv_cong:
  assumes cong: "\<And>A. A \<in> sets M \<Longrightarrow> measure M' A = \<mu> A" "sets M' = sets M" "space M' = space M"
    and \<nu>: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu>' A = \<nu> A"
  shows "RN_deriv M' \<nu>' x = RN_deriv M \<nu> x"
proof -
  interpret \<mu>': sigma_finite_measure M'
    using cong by (rule sigma_finite_measure_cong)
  show ?thesis
    unfolding RN_deriv_def
    by (simp add: cong \<nu> positive_integral_cong_measure[OF cong] measurable_def)
qed

lemma (in sigma_finite_measure) RN_deriv:
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)"
  assumes "absolutely_continuous \<nu>"
  shows "RN_deriv M \<nu> \<in> borel_measurable M" (is ?borel)
  and "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * indicator A x \<partial>M)"
    (is "\<And>A. _ \<Longrightarrow> ?int A")
  and "0 \<le> RN_deriv M \<nu> x"
proof -
  note Ex = Radon_Nikodym[OF assms, unfolded Bex_def]
  then show ?borel unfolding RN_deriv_def by (rule someI2_ex) auto
  from Ex show "0 \<le> RN_deriv M \<nu> x" unfolding RN_deriv_def
    by (rule someI2_ex) simp
  fix A assume "A \<in> sets M"
  from Ex show "?int A" unfolding RN_deriv_def
    by (rule someI2_ex) (simp add: `A \<in> sets M`)
qed

lemma (in sigma_finite_measure) RN_deriv_positive_integral:
  assumes \<nu>: "measure_space (M\<lparr>measure := \<nu>\<rparr>)" "absolutely_continuous \<nu>"
    and f: "f \<in> borel_measurable M"
  shows "integral\<^isup>P (M\<lparr>measure := \<nu>\<rparr>) f = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * f x \<partial>M)"
proof -
  interpret \<nu>: measure_space "M\<lparr>measure := \<nu>\<rparr>" by fact
  note RN = RN_deriv[OF \<nu>]
  have "integral\<^isup>P (M\<lparr>measure := \<nu>\<rparr>) f = (\<integral>\<^isup>+x. max 0 (f x) \<partial>M\<lparr>measure := \<nu>\<rparr>)"
    unfolding positive_integral_max_0 ..
  also have "(\<integral>\<^isup>+x. max 0 (f x) \<partial>M\<lparr>measure := \<nu>\<rparr>) =
    (\<integral>\<^isup>+x. max 0 (f x) \<partial>M\<lparr>measure := \<lambda>A. (\<integral>\<^isup>+x. RN_deriv M \<nu> x * indicator A x \<partial>M)\<rparr>)"
    by (intro \<nu>.positive_integral_cong_measure[symmetric]) (simp_all add: RN(2))
  also have "\<dots> = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * max 0 (f x) \<partial>M)"
    by (intro positive_integral_translated_density) (auto simp add: RN f)
  also have "\<dots> = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * f x \<partial>M)"
    using RN_deriv(3)[OF \<nu>]
    by (auto intro!: positive_integral_cong_pos split: split_if_asm
             simp: max_def ereal_mult_le_0_iff)
  finally show ?thesis .
qed

lemma (in sigma_finite_measure) RN_deriv_unique:
  assumes \<nu>: "measure_space (M\<lparr>measure := \<nu>\<rparr>)" "absolutely_continuous \<nu>"
  and f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x"
  and eq: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x \<partial>M)"
  shows "AE x. f x = RN_deriv M \<nu> x"
proof (rule density_unique[OF f RN_deriv(1)[OF \<nu>]])
  show "AE x. 0 \<le> RN_deriv M \<nu> x" using RN_deriv[OF \<nu>] by auto
  fix A assume A: "A \<in> sets M"
  show "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * indicator A x \<partial>M)"
    unfolding eq[OF A, symmetric] RN_deriv(2)[OF \<nu> A, symmetric] ..
qed

lemma (in sigma_finite_measure) RN_deriv_vimage:
  assumes T: "T \<in> measure_preserving M M'"
    and T': "T' \<in> measure_preserving (M'\<lparr> measure := \<nu>' \<rparr>) (M\<lparr> measure := \<nu> \<rparr>)"
    and inv: "\<And>x. x \<in> space M \<Longrightarrow> T' (T x) = x"
  and \<nu>': "measure_space (M'\<lparr>measure := \<nu>'\<rparr>)" "measure_space.absolutely_continuous M' \<nu>'"
  shows "AE x. RN_deriv M' \<nu>' (T x) = RN_deriv M \<nu> x"
proof (rule RN_deriv_unique)
  interpret \<nu>': measure_space "M'\<lparr>measure := \<nu>'\<rparr>" by fact
  show "measure_space (M\<lparr> measure := \<nu>\<rparr>)"
    by (rule \<nu>'.measure_space_vimage[OF _ T'], simp) default
  interpret M': measure_space M'
  proof (rule measure_space_vimage)
    have "sigma_algebra (M'\<lparr> measure := \<nu>'\<rparr>)" by default
    then show "sigma_algebra M'" by simp
  qed fact
  show "absolutely_continuous \<nu>" unfolding absolutely_continuous_def
  proof safe
    fix N assume N: "N \<in> sets M" and N_0: "\<mu> N = 0"
    then have N': "T' -` N \<inter> space M' \<in> sets M'"
      using T' by (auto simp: measurable_def measure_preserving_def)
    have "T -` (T' -` N \<inter> space M') \<inter> space M = N"
      using inv T N sets_into_space[OF N] by (auto simp: measurable_def measure_preserving_def)
    then have "measure M' (T' -` N \<inter> space M') = 0"
      using measure_preservingD[OF T N'] N_0 by auto
    with \<nu>'(2) N' show "\<nu> N = 0" using measure_preservingD[OF T', of N] N
      unfolding M'.absolutely_continuous_def measurable_def by auto
  qed
  interpret M': sigma_finite_measure M'
  proof
    from sigma_finite guess F .. note F = this
    show "\<exists>A::nat \<Rightarrow> 'c set. range A \<subseteq> sets M' \<and> (\<Union>i. A i) = space M' \<and> (\<forall>i. M'.\<mu> (A i) \<noteq> \<infinity>)"
    proof (intro exI conjI allI)
      show *: "range (\<lambda>i. T' -` F i \<inter> space M') \<subseteq> sets M'"
        using F T' by (auto simp: measurable_def measure_preserving_def)
      show "(\<Union>i. T' -` F i \<inter> space M') = space M'"
        using F T' by (force simp: measurable_def measure_preserving_def)
      fix i
      have "T' -` F i \<inter> space M' \<in> sets M'" using * by auto
      note measure_preservingD[OF T this, symmetric]
      moreover
      have Fi: "F i \<in> sets M" using F by auto
      then have "T -` (T' -` F i \<inter> space M') \<inter> space M = F i"
        using T inv sets_into_space[OF Fi]
        by (auto simp: measurable_def measure_preserving_def)
      ultimately show "measure M' (T' -` F i \<inter> space M') \<noteq> \<infinity>"
        using F by simp
    qed
  qed
  have "(RN_deriv M' \<nu>') \<circ> T \<in> borel_measurable M"
    by (intro measurable_comp[where b=M'] M'.RN_deriv(1) measure_preservingD2[OF T]) fact+
  then show "(\<lambda>x. RN_deriv M' \<nu>' (T x)) \<in> borel_measurable M"
    by (simp add: comp_def)
  show "AE x. 0 \<le> RN_deriv M' \<nu>' (T x)" using M'.RN_deriv(3)[OF \<nu>'] by auto
  fix A let ?A = "T' -` A \<inter> space M'"
  assume A: "A \<in> sets M"
  then have A': "?A \<in> sets M'" using T' unfolding measurable_def measure_preserving_def
    by auto
  from A have "\<nu> A = \<nu>' ?A" using T'[THEN measure_preservingD] by simp
  also have "\<dots> = \<integral>\<^isup>+ x. RN_deriv M' \<nu>' x * indicator ?A x \<partial>M'"
    using A' by (rule M'.RN_deriv(2)[OF \<nu>'])
  also have "\<dots> = \<integral>\<^isup>+ x. RN_deriv M' \<nu>' (T x) * indicator ?A (T x) \<partial>M"
  proof (rule positive_integral_vimage)
    show "sigma_algebra M'" by default
    show "(\<lambda>x. RN_deriv M' \<nu>' x * indicator (T' -` A \<inter> space M') x) \<in> borel_measurable M'"
      by (auto intro!: A' M'.RN_deriv(1)[OF \<nu>'])
  qed fact
  also have "\<dots> = \<integral>\<^isup>+ x. RN_deriv M' \<nu>' (T x) * indicator A x \<partial>M"
    using T inv by (auto intro!: positive_integral_cong simp: measure_preserving_def measurable_def indicator_def)
  finally show "\<nu> A = \<integral>\<^isup>+ x. RN_deriv M' \<nu>' (T x) * indicator A x \<partial>M" .
qed

lemma (in sigma_finite_measure) RN_deriv_finite:
  assumes sfm: "sigma_finite_measure (M\<lparr>measure := \<nu>\<rparr>)" and ac: "absolutely_continuous \<nu>"
  shows "AE x. RN_deriv M \<nu> x \<noteq> \<infinity>"
proof -
  interpret \<nu>: sigma_finite_measure "M\<lparr>measure := \<nu>\<rparr>" by fact
  have \<nu>: "measure_space (M\<lparr>measure := \<nu>\<rparr>)" by default
  from sfm show ?thesis
    using sigma_finite_iff_density_finite[OF \<nu> RN_deriv(1)[OF \<nu> ac]] RN_deriv(2,3)[OF \<nu> ac] by simp
qed

lemma (in sigma_finite_measure)
  assumes \<nu>: "sigma_finite_measure (M\<lparr>measure := \<nu>\<rparr>)" "absolutely_continuous \<nu>"
    and f: "f \<in> borel_measurable M"
  shows RN_deriv_integrable: "integrable (M\<lparr>measure := \<nu>\<rparr>) f \<longleftrightarrow>
      integrable M (\<lambda>x. real (RN_deriv M \<nu> x) * f x)" (is ?integrable)
    and RN_deriv_integral: "integral\<^isup>L (M\<lparr>measure := \<nu>\<rparr>) f =
      (\<integral>x. real (RN_deriv M \<nu> x) * f x \<partial>M)" (is ?integral)
proof -
  interpret \<nu>: sigma_finite_measure "M\<lparr>measure := \<nu>\<rparr>" by fact
  have ms: "measure_space (M\<lparr>measure := \<nu>\<rparr>)" by default
  have minus_cong: "\<And>A B A' B'::ereal. A = A' \<Longrightarrow> B = B' \<Longrightarrow> real A - real B = real A' - real B'" by simp
  have f': "(\<lambda>x. - f x) \<in> borel_measurable M" using f by auto
  have Nf: "f \<in> borel_measurable (M\<lparr>measure := \<nu>\<rparr>)" using f by simp
  { fix f :: "'a \<Rightarrow> real"
    { fix x assume *: "RN_deriv M \<nu> x \<noteq> \<infinity>"
      have "ereal (real (RN_deriv M \<nu> x)) * ereal (f x) = ereal (real (RN_deriv M \<nu> x) * f x)"
        by (simp add: mult_le_0_iff)
      then have "RN_deriv M \<nu> x * ereal (f x) = ereal (real (RN_deriv M \<nu> x) * f x)"
        using RN_deriv(3)[OF ms \<nu>(2)] * by (auto simp add: ereal_real split: split_if_asm) }
    then have "(\<integral>\<^isup>+x. ereal (real (RN_deriv M \<nu> x) * f x) \<partial>M) = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * ereal (f x) \<partial>M)"
              "(\<integral>\<^isup>+x. ereal (- (real (RN_deriv M \<nu> x) * f x)) \<partial>M) = (\<integral>\<^isup>+x. RN_deriv M \<nu> x * ereal (- f x) \<partial>M)"
      using RN_deriv_finite[OF \<nu>] unfolding ereal_mult_minus_right uminus_ereal.simps(1)[symmetric]
      by (auto intro!: positive_integral_cong_AE) }
  note * = this
  show ?integral ?integrable
    unfolding lebesgue_integral_def integrable_def *
    using f RN_deriv(1)[OF ms \<nu>(2)]
    by (auto simp: RN_deriv_positive_integral[OF ms \<nu>(2)])
qed

lemma (in sigma_finite_measure) real_RN_deriv:
  assumes "finite_measure (M\<lparr>measure := \<nu>\<rparr>)" (is "finite_measure ?\<nu>")
  assumes ac: "absolutely_continuous \<nu>"
  obtains D where "D \<in> borel_measurable M"
    and "AE x. RN_deriv M \<nu> x = ereal (D x)"
    and "AE x in M\<lparr>measure := \<nu>\<rparr>. 0 < D x"
    and "\<And>x. 0 \<le> D x"
proof
  interpret \<nu>: finite_measure ?\<nu> by fact
  have ms: "measure_space ?\<nu>" by default
  note RN = RN_deriv[OF ms ac]

  let ?RN = "\<lambda>t. {x \<in> space M. RN_deriv M \<nu> x = t}"

  show "(\<lambda>x. real (RN_deriv M \<nu> x)) \<in> borel_measurable M"
    using RN by auto

  have "\<nu> (?RN \<infinity>) = (\<integral>\<^isup>+ x. RN_deriv M \<nu> x * indicator (?RN \<infinity>) x \<partial>M)"
    using RN by auto
  also have "\<dots> = (\<integral>\<^isup>+ x. \<infinity> * indicator (?RN \<infinity>) x \<partial>M)"
    by (intro positive_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = \<infinity> * \<mu> (?RN \<infinity>)"
    using RN by (intro positive_integral_cmult_indicator) auto
  finally have eq: "\<nu> (?RN \<infinity>) = \<infinity> * \<mu> (?RN \<infinity>)" .
  moreover
  have "\<mu> (?RN \<infinity>) = 0"
  proof (rule ccontr)
    assume "\<mu> {x \<in> space M. RN_deriv M \<nu> x = \<infinity>} \<noteq> 0"
    moreover from RN have "0 \<le> \<mu> {x \<in> space M. RN_deriv M \<nu> x = \<infinity>}" by auto
    ultimately have "0 < \<mu> {x \<in> space M. RN_deriv M \<nu> x = \<infinity>}" by auto
    with eq have "\<nu> (?RN \<infinity>) = \<infinity>" by simp
    with \<nu>.finite_measure[of "?RN \<infinity>"] RN show False by auto
  qed
  ultimately have "AE x. RN_deriv M \<nu> x < \<infinity>"
    using RN by (intro AE_iff_measurable[THEN iffD2]) auto
  then show "AE x. RN_deriv M \<nu> x = ereal (real (RN_deriv M \<nu> x))"
    using RN(3) by (auto simp: ereal_real)
  then have eq: "AE x in (M\<lparr>measure := \<nu>\<rparr>) . RN_deriv M \<nu> x = ereal (real (RN_deriv M \<nu> x))"
    using ac absolutely_continuous_AE[OF ms] by auto

  show "\<And>x. 0 \<le> real (RN_deriv M \<nu> x)"
    using RN by (auto intro: real_of_ereal_pos)

  have "\<nu> (?RN 0) = (\<integral>\<^isup>+ x. RN_deriv M \<nu> x * indicator (?RN 0) x \<partial>M)"
    using RN by auto
  also have "\<dots> = (\<integral>\<^isup>+ x. 0 \<partial>M)"
    by (intro positive_integral_cong) (auto simp: indicator_def)
  finally have "AE x in (M\<lparr>measure := \<nu>\<rparr>). RN_deriv M \<nu> x \<noteq> 0"
    using RN by (intro \<nu>.AE_iff_measurable[THEN iffD2]) auto
  with RN(3) eq show "AE x in (M\<lparr>measure := \<nu>\<rparr>). 0 < real (RN_deriv M \<nu> x)"
    by (auto simp: zero_less_real_of_ereal le_less)
qed

lemma (in sigma_finite_measure) RN_deriv_singleton:
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)"
  and ac: "absolutely_continuous \<nu>"
  and "{x} \<in> sets M"
  shows "\<nu> {x} = RN_deriv M \<nu> x * \<mu> {x}"
proof -
  note deriv = RN_deriv[OF assms(1, 2)]
  from deriv(2)[OF `{x} \<in> sets M`]
  have "\<nu> {x} = (\<integral>\<^isup>+w. RN_deriv M \<nu> x * indicator {x} w \<partial>M)"
    by (auto simp: indicator_def intro!: positive_integral_cong)
  thus ?thesis using positive_integral_cmult_indicator[OF _ `{x} \<in> sets M`] deriv(3)
    by auto
qed

theorem (in finite_measure_space) RN_deriv_finite_measure:
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)"
  and ac: "absolutely_continuous \<nu>"
  and "x \<in> space M"
  shows "\<nu> {x} = RN_deriv M \<nu> x * \<mu> {x}"
proof -
  have "{x} \<in> sets M" using sets_eq_Pow `x \<in> space M` by auto
  from RN_deriv_singleton[OF assms(1,2) this] show ?thesis .
qed

end
