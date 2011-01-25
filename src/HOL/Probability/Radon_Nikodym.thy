theory Radon_Nikodym
imports Lebesgue_Integration
begin

lemma less_\<omega>_Ex_of_nat: "x < \<omega> \<longleftrightarrow> (\<exists>n. x < of_nat n)"
proof safe
  assume "x < \<omega>"
  then obtain r where "0 \<le> r" "x = Real r" by (cases x) auto
  moreover obtain n where "r < of_nat n" using ex_less_of_nat by auto
  ultimately show "\<exists>n. x < of_nat n" by (auto simp: real_eq_of_nat)
qed auto

lemma (in sigma_finite_measure) Ex_finite_integrable_function:
  shows "\<exists>h\<in>borel_measurable M. positive_integral h \<noteq> \<omega> \<and> (\<forall>x\<in>space M. 0 < h x \<and> h x < \<omega>)"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. \<mu> (A i) \<noteq> \<omega>" and
    disjoint: "disjoint_family A"
    using disjoint_sigma_finite by auto
  let "?B i" = "2^Suc i * \<mu> (A i)"
  have "\<forall>i. \<exists>x. 0 < x \<and> x < inverse (?B i)"
  proof
    fix i show "\<exists>x. 0 < x \<and> x < inverse (?B i)"
    proof cases
      assume "\<mu> (A i) = 0"
      then show ?thesis by (auto intro!: exI[of _ 1])
    next
      assume not_0: "\<mu> (A i) \<noteq> 0"
      then have "?B i \<noteq> \<omega>" using measure[of i] by auto
      then have "inverse (?B i) \<noteq> 0" unfolding pextreal_inverse_eq_0 by simp
      then show ?thesis using measure[of i] not_0
        by (auto intro!: exI[of _ "inverse (?B i) / 2"]
                 simp: pextreal_noteq_omega_Ex zero_le_mult_iff zero_less_mult_iff mult_le_0_iff power_le_zero_eq)
    qed
  qed
  from choice[OF this] obtain n where n: "\<And>i. 0 < n i"
    "\<And>i. n i < inverse (2^Suc i * \<mu> (A i))" by auto
  let "?h x" = "\<Sum>\<^isub>\<infinity> i. n i * indicator (A i) x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?h] del: notI)
    have "\<And>i. A i \<in> sets M"
      using range by fastsimp+
    then have "positive_integral ?h = (\<Sum>\<^isub>\<infinity> i. n i * \<mu> (A i))"
      by (simp add: positive_integral_psuminf positive_integral_cmult_indicator)
    also have "\<dots> \<le> (\<Sum>\<^isub>\<infinity> i. Real ((1 / 2)^Suc i))"
    proof (rule psuminf_le)
      fix N show "n N * \<mu> (A N) \<le> Real ((1 / 2) ^ Suc N)"
        using measure[of N] n[of N]
        by (cases "n N")
           (auto simp: pextreal_noteq_omega_Ex field_simps zero_le_mult_iff
                       mult_le_0_iff mult_less_0_iff power_less_zero_eq
                       power_le_zero_eq inverse_eq_divide less_divide_eq
                       power_divide split: split_if_asm)
    qed
    also have "\<dots> = Real 1"
      by (rule suminf_imp_psuminf, rule power_half_series, auto)
    finally show "positive_integral ?h \<noteq> \<omega>" by auto
  next
    fix x assume "x \<in> space M"
    then obtain i where "x \<in> A i" using space[symmetric] by auto
    from psuminf_cmult_indicator[OF disjoint, OF this]
    have "?h x = n i" by simp
    then show "0 < ?h x" and "?h x < \<omega>" using n[of i] by auto
  next
    show "?h \<in> borel_measurable M" using range
      by (auto intro!: borel_measurable_psuminf borel_measurable_pextreal_times)
  qed
qed

subsection "Absolutely continuous"

definition (in measure_space)
  "absolutely_continuous \<nu> = (\<forall>N\<in>null_sets. \<nu> N = (0 :: pextreal))"

lemma (in sigma_finite_measure) absolutely_continuous_AE:
  assumes "measure_space M \<nu>" "absolutely_continuous \<nu>" "AE x. P x"
  shows "measure_space.almost_everywhere M \<nu> P"
proof -
  interpret \<nu>: measure_space M \<nu> by fact
  from `AE x. P x` obtain N where N: "N \<in> null_sets" and "{x\<in>space M. \<not> P x} \<subseteq> N"
    unfolding almost_everywhere_def by auto
  show "\<nu>.almost_everywhere P"
  proof (rule \<nu>.AE_I')
    show "{x\<in>space M. \<not> P x} \<subseteq> N" by fact
    from `absolutely_continuous \<nu>` show "N \<in> \<nu>.null_sets"
      using N unfolding absolutely_continuous_def by auto
  qed
qed

lemma (in finite_measure_space) absolutely_continuousI:
  assumes "finite_measure_space M \<nu>"
  assumes v: "\<And>x. \<lbrakk> x \<in> space M ; \<mu> {x} = 0 \<rbrakk> \<Longrightarrow> \<nu> {x} = 0"
  shows "absolutely_continuous \<nu>"
proof (unfold absolutely_continuous_def sets_eq_Pow, safe)
  fix N assume "\<mu> N = 0" "N \<subseteq> space M"
  interpret v: finite_measure_space M \<nu> by fact
  have "\<nu> N = \<nu> (\<Union>x\<in>N. {x})" by simp
  also have "\<dots> = (\<Sum>x\<in>N. \<nu> {x})"
  proof (rule v.measure_finitely_additive''[symmetric])
    show "finite N" using `N \<subseteq> space M` finite_space by (auto intro: finite_subset)
    show "disjoint_family_on (\<lambda>i. {i}) N" unfolding disjoint_family_on_def by auto
    fix x assume "x \<in> N" thus "{x} \<in> sets M" using `N \<subseteq> space M` sets_eq_Pow by auto
  qed
  also have "\<dots> = 0"
  proof (safe intro!: setsum_0')
    fix x assume "x \<in> N"
    hence "\<mu> {x} \<le> \<mu> N" using sets_eq_Pow `N \<subseteq> space M` by (auto intro!: measure_mono)
    hence "\<mu> {x} = 0" using `\<mu> N = 0` by simp
    thus "\<nu> {x} = 0" using v[of x] `x \<in> N` `N \<subseteq> space M` by auto
  qed
  finally show "\<nu> N = 0" .
qed

lemma (in measure_space) density_is_absolutely_continuous:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
  shows "absolutely_continuous \<nu>"
  using assms unfolding absolutely_continuous_def
  by (simp add: positive_integral_null_set)

subsection "Existence of the Radon-Nikodym derivative"

lemma (in finite_measure) Radon_Nikodym_aux_epsilon:
  fixes e :: real assumes "0 < e"
  assumes "finite_measure M s"
  shows "\<exists>A\<in>sets M. real (\<mu> (space M)) - real (s (space M)) \<le>
                    real (\<mu> A) - real (s A) \<and>
                    (\<forall>B\<in>sets M. B \<subseteq> A \<longrightarrow> - e < real (\<mu> B) - real (s B))"
proof -
  let "?d A" = "real (\<mu> A) - real (s A)"
  interpret M': finite_measure M s by fact
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
        using `A n \<in> sets M` real_finite_measure_Union M'.real_finite_measure_Union by simp
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
            real_finite_measure_Diff[of "space M"]
            real_finite_measure_Diff[of "space M"]
            M'.real_finite_measure_Diff[of "space M"]
            M'.real_finite_measure_Diff[of "space M"]
          by (simp del: A_simps)
        finally show "?d (space M) \<le> ?d (space M - A (Suc n))" .
      qed simp
    qed
  next
    case False hence B: "\<And>n. \<exists>B. B\<in>sets M \<and> B \<subseteq> space M - A n \<and> ?d B \<le> - e"
      by (auto simp add: not_less)
    { fix n have "?d (A n) \<le> - real n * e"
      proof (induct n)
        case (Suc n) with dA_epsilon[of n, OF B] show ?case by (simp del: A_simps add: real_of_nat_Suc field_simps)
      qed simp } note dA_less = this
    have decseq: "decseq (\<lambda>n. ?d (A n))" unfolding decseq_eq_incseq
    proof (rule incseq_SucI)
      fix n show "- ?d (A n) \<le> - ?d (A (Suc n))" using dA_mono[of n] by auto
    qed
    from real_finite_continuity_from_below[of A] `range A \<subseteq> sets M`
      M'.real_finite_continuity_from_below[of A]
    have convergent: "(\<lambda>i. ?d (A i)) ----> ?d (\<Union>i. A i)"
      by (auto intro!: LIMSEQ_diff)
    obtain n :: nat where "- ?d (\<Union>i. A i) / e < real n" using reals_Archimedean2 by auto
    moreover from order_trans[OF decseq_le[OF decseq convergent] dA_less]
    have "real n \<le> - ?d (\<Union>i. A i) / e" using `0<e` by (simp add: field_simps)
    ultimately show ?thesis by auto
  qed
qed

lemma (in finite_measure) Radon_Nikodym_aux:
  assumes "finite_measure M s"
  shows "\<exists>A\<in>sets M. real (\<mu> (space M)) - real (s (space M)) \<le>
                    real (\<mu> A) - real (s A) \<and>
                    (\<forall>B\<in>sets M. B \<subseteq> A \<longrightarrow> 0 \<le> real (\<mu> B) - real (s B))"
proof -
  let "?d A" = "real (\<mu> A) - real (s A)"
  let "?P A B n" = "A \<in> sets M \<and> A \<subseteq> B \<and> ?d B \<le> ?d A \<and> (\<forall>C\<in>sets M. C \<subseteq> A \<longrightarrow> - 1 / real (Suc n) < ?d C)"
  interpret M': finite_measure M s by fact
  let "?r S" = "restricted_space S"
  { fix S n
    assume S: "S \<in> sets M"
    hence **: "\<And>X. X \<in> op \<inter> S ` sets M \<longleftrightarrow> X \<in> sets M \<and> X \<subseteq> S" by auto
    from M'.restricted_finite_measure[of S] restricted_finite_measure[of S] S
    have "finite_measure (?r S) \<mu>" "0 < 1 / real (Suc n)"
      "finite_measure (?r S) s" by auto
    from finite_measure.Radon_Nikodym_aux_epsilon[OF this] guess X ..
    hence "?P X S n"
    proof (simp add: **, safe)
      fix C assume C: "C \<in> sets M" "C \<subseteq> X" "X \<subseteq> S" and
        *: "\<forall>B\<in>sets M. S \<inter> B \<subseteq> X \<longrightarrow> - (1 / real (Suc n)) < ?d (S \<inter> B)"
      hence "C \<subseteq> S" "C \<subseteq> X" "S \<inter> C = C" by auto
      with *[THEN bspec, OF `C \<in> sets M`]
      show "- (1 / real (Suc n)) < ?d C" by auto
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
    from `range A \<subseteq> sets M` A_mono
      real_finite_continuity_from_above[of A]
      M'.real_finite_continuity_from_above[of A]
    have "(\<lambda>i. ?d (A i)) ----> ?d (\<Inter>i. A i)" by (auto intro!: LIMSEQ_diff)
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
  assumes "finite_measure M \<nu>"
  assumes "absolutely_continuous \<nu>"
  shows "\<exists>f \<in> borel_measurable M. \<forall>A\<in>sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
proof -
  interpret M': finite_measure M \<nu> using assms(1) .
  def G \<equiv> "{g \<in> borel_measurable M. \<forall>A\<in>sets M. (\<integral>\<^isup>+x. g x * indicator A x) \<le> \<nu> A}"
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
      hence "(\<integral>\<^isup>+x. max (g x) (f x) * indicator A x) =
        (\<integral>\<^isup>+x. g x * indicator (?A \<inter> A) x) +
        (\<integral>\<^isup>+x. f x * indicator ((space M - ?A) \<inter> A) x)"
        using f g sets unfolding G_def
        by (auto cong: positive_integral_cong intro!: positive_integral_add borel_measurable_indicator)
      also have "\<dots> \<le> \<nu> (?A \<inter> A) + \<nu> ((space M - ?A) \<inter> A)"
        using f g sets unfolding G_def by (auto intro!: add_mono)
      also have "\<dots> = \<nu> A"
        using M'.measure_additive[OF sets] union by auto
      finally show "(\<integral>\<^isup>+x. max (g x) (f x) * indicator A x) \<le> \<nu> A" .
    qed }
  note max_in_G = this
  { fix f g assume  "f \<up> g" and f: "\<And>i. f i \<in> G"
    have "g \<in> G" unfolding G_def
    proof safe
      from `f \<up> g` have [simp]: "g = (\<lambda>x. SUP i. f i x)"
        unfolding isoton_def fun_eq_iff SUPR_apply by simp
      have f_borel: "\<And>i. f i \<in> borel_measurable M" using f unfolding G_def by simp
      thus "g \<in> borel_measurable M" by auto
      fix A assume "A \<in> sets M"
      hence "\<And>i. (\<lambda>x. f i x * indicator A x) \<in> borel_measurable M"
        using f_borel by (auto intro!: borel_measurable_indicator)
      from positive_integral_isoton[OF isoton_indicator[OF `f \<up> g`] this]
      have SUP: "(\<integral>\<^isup>+x. g x * indicator A x) =
          (SUP i. (\<integral>\<^isup>+x. f i x * indicator A x))"
        unfolding isoton_def by simp
      show "(\<integral>\<^isup>+x. g x * indicator A x) \<le> \<nu> A" unfolding SUP
        using f `A \<in> sets M` unfolding G_def by (auto intro!: SUP_leI)
    qed }
  note SUP_in_G = this
  let ?y = "SUP g : G. positive_integral g"
  have "?y \<le> \<nu> (space M)" unfolding G_def
  proof (safe intro!: SUP_leI)
    fix g assume "\<forall>A\<in>sets M. (\<integral>\<^isup>+x. g x * indicator A x) \<le> \<nu> A"
    from this[THEN bspec, OF top] show "positive_integral g \<le> \<nu> (space M)"
      by (simp cong: positive_integral_cong)
  qed
  hence "?y \<noteq> \<omega>" using M'.finite_measure_of_space by auto
  from SUPR_countable_SUPR[OF this `G \<noteq> {}`] guess ys .. note ys = this
  hence "\<forall>n. \<exists>g. g\<in>G \<and> positive_integral g = ys n"
  proof safe
    fix n assume "range ys \<subseteq> positive_integral ` G"
    hence "ys n \<in> positive_integral ` G" by auto
    thus "\<exists>g. g\<in>G \<and> positive_integral g = ys n" by auto
  qed
  from choice[OF this] obtain gs where "\<And>i. gs i \<in> G" "\<And>n. positive_integral (gs n) = ys n" by auto
  hence y_eq: "?y = (SUP i. positive_integral (gs i))" using ys by auto
  let "?g i x" = "Max ((\<lambda>n. gs n x) ` {..i})"
  def f \<equiv> "SUP i. ?g i"
  have gs_not_empty: "\<And>i. (\<lambda>n. gs n x) ` {..i} \<noteq> {}" by auto
  { fix i have "?g i \<in> G"
    proof (induct i)
      case 0 thus ?case by simp fact
    next
      case (Suc i)
      with Suc gs_not_empty `gs (Suc i) \<in> G` show ?case
        by (auto simp add: atMost_Suc intro!: max_in_G)
    qed }
  note g_in_G = this
  have "\<And>x. \<forall>i. ?g i x \<le> ?g (Suc i) x"
    using gs_not_empty by (simp add: atMost_Suc)
  hence isoton_g: "?g \<up> f" by (simp add: isoton_def le_fun_def f_def)
  from SUP_in_G[OF this g_in_G] have "f \<in> G" .
  hence [simp, intro]: "f \<in> borel_measurable M" unfolding G_def by auto
  have "(\<lambda>i. positive_integral (?g i)) \<up> positive_integral f"
    using isoton_g g_in_G by (auto intro!: positive_integral_isoton simp: G_def f_def)
  hence "positive_integral f = (SUP i. positive_integral (?g i))"
    unfolding isoton_def by simp
  also have "\<dots> = ?y"
  proof (rule antisym)
    show "(SUP i. positive_integral (?g i)) \<le> ?y"
      using g_in_G by (auto intro!: exI Sup_mono simp: SUPR_def)
    show "?y \<le> (SUP i. positive_integral (?g i))" unfolding y_eq
      by (auto intro!: SUP_mono positive_integral_mono Max_ge)
  qed
  finally have int_f_eq_y: "positive_integral f = ?y" .
  let "?t A" = "\<nu> A - (\<integral>\<^isup>+x. f x * indicator A x)"
  have "finite_measure M ?t"
  proof
    show "?t {} = 0" by simp
    show "?t (space M) \<noteq> \<omega>" using M'.finite_measure by simp
    show "countably_additive M ?t" unfolding countably_additive_def
    proof safe
      fix A :: "nat \<Rightarrow> 'a set"  assume A: "range A \<subseteq> sets M" "disjoint_family A"
      have "(\<Sum>\<^isub>\<infinity> n. (\<integral>\<^isup>+x. f x * indicator (A n) x))
        = (\<integral>\<^isup>+x. (\<Sum>\<^isub>\<infinity>n. f x * indicator (A n) x))"
        using `range A \<subseteq> sets M`
        by (rule_tac positive_integral_psuminf[symmetric]) (auto intro!: borel_measurable_indicator)
      also have "\<dots> = (\<integral>\<^isup>+x. f x * indicator (\<Union>n. A n) x)"
        apply (rule positive_integral_cong)
        apply (subst psuminf_cmult_right)
        unfolding psuminf_indicator[OF `disjoint_family A`] ..
      finally have "(\<Sum>\<^isub>\<infinity> n. (\<integral>\<^isup>+x. f x * indicator (A n) x))
        = (\<integral>\<^isup>+x. f x * indicator (\<Union>n. A n) x)" .
      moreover have "(\<Sum>\<^isub>\<infinity>n. \<nu> (A n)) = \<nu> (\<Union>n. A n)"
        using M'.measure_countably_additive A by (simp add: comp_def)
      moreover have "\<And>i. (\<integral>\<^isup>+x. f x * indicator (A i) x) \<le> \<nu> (A i)"
          using A `f \<in> G` unfolding G_def by auto
      moreover have v_fin: "\<nu> (\<Union>i. A i) \<noteq> \<omega>" using M'.finite_measure A by (simp add: countable_UN)
      moreover {
        have "(\<integral>\<^isup>+x. f x * indicator (\<Union>i. A i) x) \<le> \<nu> (\<Union>i. A i)"
          using A `f \<in> G` unfolding G_def by (auto simp: countable_UN)
        also have "\<nu> (\<Union>i. A i) < \<omega>" using v_fin by (simp add: pextreal_less_\<omega>)
        finally have "(\<integral>\<^isup>+x. f x * indicator (\<Union>i. A i) x) \<noteq> \<omega>"
          by (simp add: pextreal_less_\<omega>) }
      ultimately
      show "(\<Sum>\<^isub>\<infinity> n. ?t (A n)) = ?t (\<Union>i. A i)"
        apply (subst psuminf_minus) by simp_all
    qed
  qed
  then interpret M: finite_measure M ?t .
  have ac: "absolutely_continuous ?t" using `absolutely_continuous \<nu>` unfolding absolutely_continuous_def by auto
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
    hence pos_M: "0 < \<mu> (space M)"
      using ac top unfolding absolutely_continuous_def by auto
    moreover
    have "(\<integral>\<^isup>+x. f x * indicator (space M) x) \<le> \<nu> (space M)"
      using `f \<in> G` unfolding G_def by auto
    hence "(\<integral>\<^isup>+x. f x * indicator (space M) x) \<noteq> \<omega>"
      using M'.finite_measure_of_space by auto
    moreover
    def b \<equiv> "?t (space M) / \<mu> (space M) / 2"
    ultimately have b: "b \<noteq> 0" "b \<noteq> \<omega>"
      using M'.finite_measure_of_space
      by (auto simp: pextreal_inverse_eq_0 finite_measure_of_space)
    have "finite_measure M (\<lambda>A. b * \<mu> A)" (is "finite_measure M ?b")
    proof
      show "?b {} = 0" by simp
      show "?b (space M) \<noteq> \<omega>" using finite_measure_of_space b by auto
      show "countably_additive M ?b"
        unfolding countably_additive_def psuminf_cmult_right
        using measure_countably_additive by auto
    qed
    from M.Radon_Nikodym_aux[OF this]
    obtain A0 where "A0 \<in> sets M" and
      space_less_A0: "real (?t (space M)) - real (b * \<mu> (space M)) \<le> real (?t A0) - real (b * \<mu> A0)" and
      *: "\<And>B. \<lbrakk> B \<in> sets M ; B \<subseteq> A0 \<rbrakk> \<Longrightarrow> 0 \<le> real (?t B) - real (b * \<mu> B)" by auto
    { fix B assume "B \<in> sets M" "B \<subseteq> A0"
      with *[OF this] have "b * \<mu> B \<le> ?t B"
        using M'.finite_measure b finite_measure
        by (cases "b * \<mu> B", cases "?t B") (auto simp: field_simps) }
    note bM_le_t = this
    let "?f0 x" = "f x + b * indicator A0 x"
    { fix A assume A: "A \<in> sets M"
      hence "A \<inter> A0 \<in> sets M" using `A0 \<in> sets M` by auto
      have "(\<integral>\<^isup>+x. ?f0 x  * indicator A x) =
        (\<integral>\<^isup>+x. f x * indicator A x + b * indicator (A \<inter> A0) x)"
        by (auto intro!: positive_integral_cong simp: field_simps indicator_inter_arith)
      hence "(\<integral>\<^isup>+x. ?f0 x * indicator A x) =
          (\<integral>\<^isup>+x. f x * indicator A x) + b * \<mu> (A \<inter> A0)"
        using `A0 \<in> sets M` `A \<inter> A0 \<in> sets M` A
        by (simp add: borel_measurable_indicator positive_integral_add positive_integral_cmult_indicator) }
    note f0_eq = this
    { fix A assume A: "A \<in> sets M"
      hence "A \<inter> A0 \<in> sets M" using `A0 \<in> sets M` by auto
      have f_le_v: "(\<integral>\<^isup>+x. f x * indicator A x) \<le> \<nu> A"
        using `f \<in> G` A unfolding G_def by auto
      note f0_eq[OF A]
      also have "(\<integral>\<^isup>+x. f x * indicator A x) + b * \<mu> (A \<inter> A0) \<le>
          (\<integral>\<^isup>+x. f x * indicator A x) + ?t (A \<inter> A0)"
        using bM_le_t[OF `A \<inter> A0 \<in> sets M`] `A \<in> sets M` `A0 \<in> sets M`
        by (auto intro!: add_left_mono)
      also have "\<dots> \<le> (\<integral>\<^isup>+x. f x * indicator A x) + ?t A"
        using M.measure_mono[simplified, OF _ `A \<inter> A0 \<in> sets M` `A \<in> sets M`]
        by (auto intro!: add_left_mono)
      also have "\<dots> \<le> \<nu> A"
        using f_le_v M'.finite_measure[simplified, OF `A \<in> sets M`]
        by (cases "(\<integral>\<^isup>+x. f x * indicator A x)", cases "\<nu> A", auto)
      finally have "(\<integral>\<^isup>+x. ?f0 x * indicator A x) \<le> \<nu> A" . }
    hence "?f0 \<in> G" using `A0 \<in> sets M` unfolding G_def
      by (auto intro!: borel_measurable_indicator borel_measurable_pextreal_add borel_measurable_pextreal_times)
    have real: "?t (space M) \<noteq> \<omega>" "?t A0 \<noteq> \<omega>"
      "b * \<mu> (space M) \<noteq> \<omega>" "b * \<mu> A0 \<noteq> \<omega>"
      using `A0 \<in> sets M` b
        finite_measure[of A0] M.finite_measure[of A0]
        finite_measure_of_space M.finite_measure_of_space
      by auto
    have int_f_finite: "positive_integral f \<noteq> \<omega>"
      using M'.finite_measure_of_space pos_t unfolding pextreal_zero_less_diff_iff
      by (auto cong: positive_integral_cong)
    have "?t (space M) > b * \<mu> (space M)" unfolding b_def
      apply (simp add: field_simps)
      apply (subst mult_assoc[symmetric])
      apply (subst pextreal_mult_inverse)
      using finite_measure_of_space M'.finite_measure_of_space pos_t pos_M
      using pextreal_mult_strict_right_mono[of "Real (1/2)" 1 "?t (space M)"]
      by simp_all
    hence  "0 < ?t (space M) - b * \<mu> (space M)"
      by (simp add: pextreal_zero_less_diff_iff)
    also have "\<dots> \<le> ?t A0 - b * \<mu> A0"
      using space_less_A0 pos_M pos_t b real[unfolded pextreal_noteq_omega_Ex] by auto
    finally have "b * \<mu> A0 < ?t A0" unfolding pextreal_zero_less_diff_iff .
    hence "0 < ?t A0" by auto
    hence "0 < \<mu> A0" using ac unfolding absolutely_continuous_def
      using `A0 \<in> sets M` by auto
    hence "0 < b * \<mu> A0" using b by auto
    from int_f_finite this
    have "?y + 0 < positive_integral f + b * \<mu> A0" unfolding int_f_eq_y
      by (rule pextreal_less_add)
    also have "\<dots> = positive_integral ?f0" using f0_eq[OF top] `A0 \<in> sets M` sets_into_space
      by (simp cong: positive_integral_cong)
    finally have "?y < positive_integral ?f0" by simp
    moreover from `?f0 \<in> G` have "positive_integral ?f0 \<le> ?y" by (auto intro!: le_SUPI)
    ultimately show False by auto
  qed
  show ?thesis
  proof (safe intro!: bexI[of _ f])
    fix A assume "A\<in>sets M"
    show "\<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
    proof (rule antisym)
      show "(\<integral>\<^isup>+x. f x * indicator A x) \<le> \<nu> A"
        using `f \<in> G` `A \<in> sets M` unfolding G_def by auto
      show "\<nu> A \<le> (\<integral>\<^isup>+x. f x * indicator A x)"
        using upper_bound[THEN bspec, OF `A \<in> sets M`]
         by (simp add: pextreal_zero_le_diff)
    qed
  qed simp
qed

lemma (in finite_measure) split_space_into_finite_sets_and_rest:
  assumes "measure_space M \<nu>"
  assumes ac: "absolutely_continuous \<nu>"
  shows "\<exists>\<Omega>0\<in>sets M. \<exists>\<Omega>::nat\<Rightarrow>'a set. disjoint_family \<Omega> \<and> range \<Omega> \<subseteq> sets M \<and> \<Omega>0 = space M - (\<Union>i. \<Omega> i) \<and>
    (\<forall>A\<in>sets M. A \<subseteq> \<Omega>0 \<longrightarrow> (\<mu> A = 0 \<and> \<nu> A = 0) \<or> (\<mu> A > 0 \<and> \<nu> A = \<omega>)) \<and>
    (\<forall>i. \<nu> (\<Omega> i) \<noteq> \<omega>)"
proof -
  interpret v: measure_space M \<nu> by fact
  let ?Q = "{Q\<in>sets M. \<nu> Q \<noteq> \<omega>}"
  let ?a = "SUP Q:?Q. \<mu> Q"
  have "{} \<in> ?Q" using v.empty_measure by auto
  then have Q_not_empty: "?Q \<noteq> {}" by blast
  have "?a \<le> \<mu> (space M)" using sets_into_space
    by (auto intro!: SUP_leI measure_mono top)
  then have "?a \<noteq> \<omega>" using finite_measure_of_space
    by auto
  from SUPR_countable_SUPR[OF this Q_not_empty]
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
    show "\<And>i. ?O i \<subseteq> ?O (Suc i)" by fastsimp
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
    also have "\<dots> < \<omega>" unfolding setsum_\<omega> pextreal_less_\<omega> using Q' by auto
    finally show "\<nu> (?O i) \<noteq> \<omega>" unfolding pextreal_less_\<omega> by auto
  qed auto
  have O_mono: "\<And>n. ?O n \<subseteq> ?O (Suc n)" by fastsimp
  have a_eq: "?a = \<mu> (\<Union>i. ?O i)" unfolding Union[symmetric]
  proof (rule antisym)
    show "?a \<le> (SUP i. \<mu> (?O i))" unfolding a_Lim
      using Q' by (auto intro!: SUP_mono measure_mono finite_UN)
    show "(SUP i. \<mu> (?O i)) \<le> ?a" unfolding SUPR_def
    proof (safe intro!: Sup_mono, unfold bex_simps)
      fix i
      have *: "(\<Union>Q' ` {..i}) = ?O i" by auto
      then show "\<exists>x. (x \<in> sets M \<and> \<nu> x \<noteq> \<omega>) \<and>
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
      by (fastsimp simp: disjoint_family_on_def Q_def
        split: nat.split_asm)
    show "range Q \<subseteq> sets M"
      using Q_sets by auto
    { fix A assume A: "A \<in> sets M" "A \<subseteq> space M - ?O_0"
      show "\<mu> A = 0 \<and> \<nu> A = 0 \<or> 0 < \<mu> A \<and> \<nu> A = \<omega>"
      proof (rule disjCI, simp)
        assume *: "0 < \<mu> A \<longrightarrow> \<nu> A \<noteq> \<omega>"
        show "\<mu> A = 0 \<and> \<nu> A = 0"
        proof cases
          assume "\<mu> A = 0" moreover with ac A have "\<nu> A = 0"
            unfolding absolutely_continuous_def by auto
          ultimately show ?thesis by simp
        next
          assume "\<mu> A \<noteq> 0" with * have "\<nu> A \<noteq> \<omega>" by auto
          with A have "\<mu> ?O_0 + \<mu> A = \<mu> (?O_0 \<union> A)"
            using Q' by (auto intro!: measure_additive countable_UN)
          also have "\<dots> = (SUP i. \<mu> (?O i \<union> A))"
          proof (rule continuity_from_below[of "\<lambda>i. ?O i \<union> A", symmetric, simplified])
            show "range (\<lambda>i. ?O i \<union> A) \<subseteq> sets M"
              using `\<nu> A \<noteq> \<omega>` O_sets A by auto
          qed fastsimp
          also have "\<dots> \<le> ?a"
          proof (safe intro!: SUPR_bound)
            fix i have "?O i \<union> A \<in> ?Q"
            proof (safe del: notI)
              show "?O i \<union> A \<in> sets M" using O_sets A by auto
              from O_in_G[of i]
              moreover have "\<nu> (?O i \<union> A) \<le> \<nu> (?O i) + \<nu> A"
                using v.measure_subadditive[of "?O i" A] A O_sets by auto
              ultimately show "\<nu> (?O i \<union> A) \<noteq> \<omega>"
                using `\<nu> A \<noteq> \<omega>` by auto
            qed
            then show "\<mu> (?O i \<union> A) \<le> ?a" by (rule le_SUPI)
          qed
          finally have "\<mu> A = 0" unfolding a_eq using finite_measure[OF `?O_0 \<in> sets M`]
            by (cases "\<mu> A") (auto simp: pextreal_noteq_omega_Ex)
          with `\<mu> A \<noteq> 0` show ?thesis by auto
        qed
      qed }
    { fix i show "\<nu> (Q i) \<noteq> \<omega>"
      proof (cases i)
        case 0 then show ?thesis
          unfolding Q_def using Q'[of 0] by simp
      next
        case (Suc n)
        then show ?thesis unfolding Q_def
          using `?O n \<in> ?Q` `?O (Suc n) \<in> ?Q` O_mono
          using v.measure_Diff[of "?O n" "?O (Suc n)"] by auto
      qed }
    show "space M - ?O_0 \<in> sets M" using Q'_sets by auto
    { fix j have "(\<Union>i\<le>j. ?O i) = (\<Union>i\<le>j. Q i)"
      proof (induct j)
        case 0 then show ?case by (simp add: Q_def)
      next
        case (Suc j)
        have eq: "\<And>j. (\<Union>i\<le>j. ?O i) = (\<Union>i\<le>j. Q' i)" by fastsimp
        have "{..j} \<union> {..Suc j} = {..Suc j}" by auto
        then have "(\<Union>i\<le>Suc j. Q' i) = (\<Union>i\<le>j. Q' i) \<union> Q (Suc j)"
          by (simp add: UN_Un[symmetric] Q_def del: UN_Un)
        then show ?case using Suc by (auto simp add: eq atMost_Suc)
      qed }
    then have "(\<Union>j. (\<Union>i\<le>j. ?O i)) = (\<Union>j. (\<Union>i\<le>j. Q i))" by simp
    then show "space M - ?O_0 = space M - (\<Union>i. Q i)" by fastsimp
  qed
qed

lemma (in finite_measure) Radon_Nikodym_finite_measure_infinite:
  assumes "measure_space M \<nu>"
  assumes "absolutely_continuous \<nu>"
  shows "\<exists>f \<in> borel_measurable M. \<forall>A\<in>sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
proof -
  interpret v: measure_space M \<nu> by fact
  from split_space_into_finite_sets_and_rest[OF assms]
  obtain Q0 and Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and Q0: "Q0 \<in> sets M" "Q0 = space M - (\<Union>i. Q i)"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> \<mu> A = 0 \<and> \<nu> A = 0 \<or> 0 < \<mu> A \<and> \<nu> A = \<omega>"
    and Q_fin: "\<And>i. \<nu> (Q i) \<noteq> \<omega>" by force
  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  have "\<forall>i. \<exists>f. f\<in>borel_measurable M \<and> (\<forall>A\<in>sets M.
    \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. f x * indicator (Q i \<inter> A) x))"
  proof
    fix i
    have indicator_eq: "\<And>f x A. (f x :: pextreal) * indicator (Q i \<inter> A) x * indicator (Q i) x
      = (f x * indicator (Q i) x) * indicator A x"
      unfolding indicator_def by auto
    have fm: "finite_measure (restricted_space (Q i)) \<mu>"
      (is "finite_measure ?R \<mu>") by (rule restricted_finite_measure[OF Q_sets[of i]])
    then interpret R: finite_measure ?R .
    have fmv: "finite_measure ?R \<nu>"
      unfolding finite_measure_def finite_measure_axioms_def
    proof
      show "measure_space ?R \<nu>"
        using v.restricted_measure_space Q_sets[of i] by auto
      show "\<nu>  (space ?R) \<noteq> \<omega>"
        using Q_fin by simp
    qed
    have "R.absolutely_continuous \<nu>"
      using `absolutely_continuous \<nu>` `Q i \<in> sets M`
      by (auto simp: R.absolutely_continuous_def absolutely_continuous_def)
    from finite_measure.Radon_Nikodym_finite_measure[OF fm fmv this]
    obtain f where f: "(\<lambda>x. f x * indicator (Q i) x) \<in> borel_measurable M"
      and f_int: "\<And>A. A\<in>sets M \<Longrightarrow> \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. (f x * indicator (Q i) x) * indicator A x)"
      unfolding Bex_def borel_measurable_restricted[OF `Q i \<in> sets M`]
        positive_integral_restricted[OF `Q i \<in> sets M`] by (auto simp: indicator_eq)
    then show "\<exists>f. f\<in>borel_measurable M \<and> (\<forall>A\<in>sets M.
      \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. f x * indicator (Q i \<inter> A) x))"
      by (fastsimp intro!: exI[of _ "\<lambda>x. f x * indicator (Q i) x"] positive_integral_cong
          simp: indicator_def)
  qed
  from choice[OF this] obtain f where borel: "\<And>i. f i \<in> borel_measurable M"
    and f: "\<And>A i. A \<in> sets M \<Longrightarrow>
      \<nu> (Q i \<inter> A) = (\<integral>\<^isup>+x. f i x * indicator (Q i \<inter> A) x)"
    by auto
  let "?f x" =
    "(\<Sum>\<^isub>\<infinity> i. f i x * indicator (Q i) x) + \<omega> * indicator Q0 x"
  show ?thesis
  proof (safe intro!: bexI[of _ ?f])
    show "?f \<in> borel_measurable M"
      by (safe intro!: borel_measurable_psuminf borel_measurable_pextreal_times
        borel_measurable_pextreal_add borel_measurable_indicator
        borel_measurable_const borel Q_sets Q0 Diff countable_UN)
    fix A assume "A \<in> sets M"
    have *:
      "\<And>x i. indicator A x * (f i x * indicator (Q i) x) =
        f i x * indicator (Q i \<inter> A) x"
      "\<And>x i. (indicator A x * indicator Q0 x :: pextreal) =
        indicator (Q0 \<inter> A) x" by (auto simp: indicator_def)
    have "(\<integral>\<^isup>+x. ?f x * indicator A x) =
      (\<Sum>\<^isub>\<infinity> i. \<nu> (Q i \<inter> A)) + \<omega> * \<mu> (Q0 \<inter> A)"
      unfolding f[OF `A \<in> sets M`]
      apply (simp del: pextreal_times(2) add: field_simps *)
      apply (subst positive_integral_add)
      apply (fastsimp intro: Q0 `A \<in> sets M`)
      apply (fastsimp intro: Q_sets `A \<in> sets M` borel_measurable_psuminf borel)
      apply (subst positive_integral_cmult_indicator)
      apply (fastsimp intro: Q0 `A \<in> sets M`)
      unfolding psuminf_cmult_right[symmetric]
      apply (subst positive_integral_psuminf)
      apply (fastsimp intro: `A \<in> sets M` Q_sets borel)
      apply (simp add: *)
      done
    moreover have "(\<Sum>\<^isub>\<infinity>i. \<nu> (Q i \<inter> A)) = \<nu> ((\<Union>i. Q i) \<inter> A)"
      using Q Q_sets `A \<in> sets M`
      by (intro v.measure_countably_additive[of "\<lambda>i. Q i \<inter> A", unfolded comp_def, simplified])
         (auto simp: disjoint_family_on_def)
    moreover have "\<omega> * \<mu> (Q0 \<inter> A) = \<nu> (Q0 \<inter> A)"
    proof -
      have "Q0 \<inter> A \<in> sets M" using Q0(1) `A \<in> sets M` by blast
      from in_Q0[OF this] show ?thesis by auto
    qed
    moreover have "Q0 \<inter> A \<in> sets M" "((\<Union>i. Q i) \<inter> A) \<in> sets M"
      using Q_sets `A \<in> sets M` Q0(1) by (auto intro!: countable_UN)
    moreover have "((\<Union>i. Q i) \<inter> A) \<union> (Q0 \<inter> A) = A" "((\<Union>i. Q i) \<inter> A) \<inter> (Q0 \<inter> A) = {}"
      using `A \<in> sets M` sets_into_space Q0 by auto
    ultimately show "\<nu> A = (\<integral>\<^isup>+x. ?f x * indicator A x)"
      using v.measure_additive[simplified, of "(\<Union>i. Q i) \<inter> A" "Q0 \<inter> A"]
      by simp
  qed
qed

lemma (in sigma_finite_measure) Radon_Nikodym:
  assumes "measure_space M \<nu>"
  assumes "absolutely_continuous \<nu>"
  shows "\<exists>f \<in> borel_measurable M. \<forall>A\<in>sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
proof -
  from Ex_finite_integrable_function
  obtain h where finite: "positive_integral h \<noteq> \<omega>" and
    borel: "h \<in> borel_measurable M" and
    pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x" and
    "\<And>x. x \<in> space M \<Longrightarrow> h x < \<omega>" by auto
  let "?T A" = "(\<integral>\<^isup>+x. h x * indicator A x)"
  from measure_space_density[OF borel] finite
  interpret T: finite_measure M ?T
    unfolding finite_measure_def finite_measure_axioms_def
    by (simp cong: positive_integral_cong)
  have "\<And>N. N \<in> sets M \<Longrightarrow> {x \<in> space M. h x \<noteq> 0 \<and> indicator N x \<noteq> (0::pextreal)} = N"
    using sets_into_space pos by (force simp: indicator_def)
  then have "T.absolutely_continuous \<nu>" using assms(2) borel
    unfolding T.absolutely_continuous_def absolutely_continuous_def
    by (fastsimp simp: borel_measurable_indicator positive_integral_0_iff)
  from T.Radon_Nikodym_finite_measure_infinite[simplified, OF assms(1) this]
  obtain f where f_borel: "f \<in> borel_measurable M" and
    fT: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = T.positive_integral (\<lambda>x. f x * indicator A x)" by auto
  show ?thesis
  proof (safe intro!: bexI[of _ "\<lambda>x. h x * f x"])
    show "(\<lambda>x. h x * f x) \<in> borel_measurable M"
      using borel f_borel by (auto intro: borel_measurable_pextreal_times)
    fix A assume "A \<in> sets M"
    then have "(\<lambda>x. f x * indicator A x) \<in> borel_measurable M"
      using f_borel by (auto intro: borel_measurable_pextreal_times borel_measurable_indicator)
    from positive_integral_translated_density[OF borel this]
    show "\<nu> A = (\<integral>\<^isup>+x. h x * f x * indicator A x)"
      unfolding fT[OF `A \<in> sets M`] by (simp add: field_simps)
  qed
qed

section "Uniqueness of densities"

lemma (in measure_space) finite_density_unique:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  and fin: "positive_integral f < \<omega>"
  shows "(\<forall>A\<in>sets M. (\<integral>\<^isup>+x. f x * indicator A x) = (\<integral>\<^isup>+x. g x * indicator A x))
    \<longleftrightarrow> (AE x. f x = g x)"
    (is "(\<forall>A\<in>sets M. ?P f A = ?P g A) \<longleftrightarrow> _")
proof (intro iffI ballI)
  fix A assume eq: "AE x. f x = g x"
  show "?P f A = ?P g A"
    by (rule positive_integral_cong_AE[OF AE_mp[OF eq]]) simp
next
  assume eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
  from this[THEN bspec, OF top] fin
  have g_fin: "positive_integral g < \<omega>" by (simp cong: positive_integral_cong)
  { fix f g assume borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
      and g_fin: "positive_integral g < \<omega>" and eq: "\<forall>A\<in>sets M. ?P f A = ?P g A"
    let ?N = "{x\<in>space M. g x < f x}"
    have N: "?N \<in> sets M" using borel by simp
    have "?P (\<lambda>x. (f x - g x)) ?N = (\<integral>\<^isup>+x. f x * indicator ?N x - g x * indicator ?N x)"
      by (auto intro!: positive_integral_cong simp: indicator_def)
    also have "\<dots> = ?P f ?N - ?P g ?N"
    proof (rule positive_integral_diff)
      show "(\<lambda>x. f x * indicator ?N x) \<in> borel_measurable M" "(\<lambda>x. g x * indicator ?N x) \<in> borel_measurable M"
        using borel N by auto
      have "?P g ?N \<le> positive_integral g"
        by (auto intro!: positive_integral_mono simp: indicator_def)
      then show "?P g ?N \<noteq> \<omega>" using g_fin by auto
      fix x assume "x \<in> space M"
      show "g x * indicator ?N x \<le> f x * indicator ?N x"
        by (auto simp: indicator_def)
    qed
    also have "\<dots> = 0"
      using eq[THEN bspec, OF N] by simp
    finally have "\<mu> {x\<in>space M. (f x - g x) * indicator ?N x \<noteq> 0} = 0"
      using borel N by (subst (asm) positive_integral_0_iff) auto
    moreover have "{x\<in>space M. (f x - g x) * indicator ?N x \<noteq> 0} = ?N"
      by (auto simp: pextreal_zero_le_diff)
    ultimately have "?N \<in> null_sets" using N by simp }
  from this[OF borel g_fin eq] this[OF borel(2,1) fin]
  have "{x\<in>space M. g x < f x} \<union> {x\<in>space M. f x < g x} \<in> null_sets"
    using eq by (intro null_sets_Un) auto
  also have "{x\<in>space M. g x < f x} \<union> {x\<in>space M. f x < g x} = {x\<in>space M. f x \<noteq> g x}"
    by auto
  finally show "AE x. f x = g x"
    unfolding almost_everywhere_def by auto
qed

lemma (in finite_measure) density_unique_finite_measure:
  assumes borel: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes f: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. f x * indicator A x) = (\<integral>\<^isup>+x. f' x * indicator A x)"
    (is "\<And>A. A \<in> sets M \<Longrightarrow> ?P f A = ?P f' A")
  shows "AE x. f x = f' x"
proof -
  let "?\<nu> A" = "?P f A" and "?\<nu>' A" = "?P f' A"
  let "?f A x" = "f x * indicator A x" and "?f' A x" = "f' x * indicator A x"
  interpret M: measure_space M ?\<nu>
    using borel(1) by (rule measure_space_density)
  have ac: "absolutely_continuous ?\<nu>"
    using f by (rule density_is_absolutely_continuous)
  from split_space_into_finite_sets_and_rest[OF `measure_space M ?\<nu>` ac]
  obtain Q0 and Q :: "nat \<Rightarrow> 'a set"
    where Q: "disjoint_family Q" "range Q \<subseteq> sets M"
    and Q0: "Q0 \<in> sets M" "Q0 = space M - (\<Union>i. Q i)"
    and in_Q0: "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> Q0 \<Longrightarrow> \<mu> A = 0 \<and> ?\<nu> A = 0 \<or> 0 < \<mu> A \<and> ?\<nu> A = \<omega>"
    and Q_fin: "\<And>i. ?\<nu> (Q i) \<noteq> \<omega>" by force
  from Q have Q_sets: "\<And>i. Q i \<in> sets M" by auto
  let ?N = "{x\<in>space M. f x \<noteq> f' x}"
  have "?N \<in> sets M" using borel by auto
  have *: "\<And>i x A. \<And>y::pextreal. y * indicator (Q i) x * indicator A x = y * indicator (Q i \<inter> A) x"
    unfolding indicator_def by auto
  have 1: "\<forall>i. AE x. ?f (Q i) x = ?f' (Q i) x"
    using borel Q_fin Q
    by (intro finite_density_unique[THEN iffD1] allI)
       (auto intro!: borel_measurable_pextreal_times f Int simp: *)
  have 2: "AE x. ?f Q0 x = ?f' Q0 x"
  proof (rule AE_I')
    { fix f :: "'a \<Rightarrow> pextreal" assume borel: "f \<in> borel_measurable M"
        and eq: "\<And>A. A \<in> sets M \<Longrightarrow> ?\<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
      let "?A i" = "Q0 \<inter> {x \<in> space M. f x < of_nat i}"
      have "(\<Union>i. ?A i) \<in> null_sets"
      proof (rule null_sets_UN)
        fix i have "?A i \<in> sets M"
          using borel Q0(1) by auto
        have "?\<nu> (?A i) \<le> (\<integral>\<^isup>+x. of_nat i * indicator (?A i) x)"
          unfolding eq[OF `?A i \<in> sets M`]
          by (auto intro!: positive_integral_mono simp: indicator_def)
        also have "\<dots> = of_nat i * \<mu> (?A i)"
          using `?A i \<in> sets M` by (auto intro!: positive_integral_cmult_indicator)
        also have "\<dots> < \<omega>"
          using `?A i \<in> sets M`[THEN finite_measure] by auto
        finally have "?\<nu> (?A i) \<noteq> \<omega>" by simp
        then show "?A i \<in> null_sets" using in_Q0[OF `?A i \<in> sets M`] `?A i \<in> sets M` by auto
      qed
      also have "(\<Union>i. ?A i) = Q0 \<inter> {x\<in>space M. f x < \<omega>}"
        by (auto simp: less_\<omega>_Ex_of_nat)
      finally have "Q0 \<inter> {x\<in>space M. f x \<noteq> \<omega>} \<in> null_sets" by (simp add: pextreal_less_\<omega>) }
    from this[OF borel(1) refl] this[OF borel(2) f]
    have "Q0 \<inter> {x\<in>space M. f x \<noteq> \<omega>} \<in> null_sets" "Q0 \<inter> {x\<in>space M. f' x \<noteq> \<omega>} \<in> null_sets" by simp_all
    then show "(Q0 \<inter> {x\<in>space M. f x \<noteq> \<omega>}) \<union> (Q0 \<inter> {x\<in>space M. f' x \<noteq> \<omega>}) \<in> null_sets" by (rule null_sets_Un)
    show "{x \<in> space M. ?f Q0 x \<noteq> ?f' Q0 x} \<subseteq>
      (Q0 \<inter> {x\<in>space M. f x \<noteq> \<omega>}) \<union> (Q0 \<inter> {x\<in>space M. f' x \<noteq> \<omega>})" by (auto simp: indicator_def)
  qed
  have **: "\<And>x. (?f Q0 x = ?f' Q0 x) \<longrightarrow> (\<forall>i. ?f (Q i) x = ?f' (Q i) x) \<longrightarrow>
    ?f (space M) x = ?f' (space M) x"
    by (auto simp: indicator_def Q0)
  have 3: "AE x. ?f (space M) x = ?f' (space M) x"
    by (rule AE_mp[OF 1[unfolded all_AE_countable] AE_mp[OF 2]]) (simp add: **)
  then show "AE x. f x = f' x"
    by (rule AE_mp) (auto intro!: AE_cong simp: indicator_def)
qed

lemma (in sigma_finite_measure) density_unique:
  assumes borel: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes f: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+x. f x * indicator A x) = (\<integral>\<^isup>+x. f' x * indicator A x)"
    (is "\<And>A. A \<in> sets M \<Longrightarrow> ?P f A = ?P f' A")
  shows "AE x. f x = f' x"
proof -
  obtain h where h_borel: "h \<in> borel_measurable M"
    and fin: "positive_integral h \<noteq> \<omega>" and pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x \<and> h x < \<omega>"
    using Ex_finite_integrable_function by auto
  interpret h: measure_space M "\<lambda>A. (\<integral>\<^isup>+x. h x * indicator A x)"
    using h_borel by (rule measure_space_density)
  interpret h: finite_measure M "\<lambda>A. (\<integral>\<^isup>+x. h x * indicator A x)"
    by default (simp cong: positive_integral_cong add: fin)
  interpret f: measure_space M "\<lambda>A. (\<integral>\<^isup>+x. f x * indicator A x)"
    using borel(1) by (rule measure_space_density)
  interpret f': measure_space M "\<lambda>A. (\<integral>\<^isup>+x. f' x * indicator A x)"
    using borel(2) by (rule measure_space_density)
  { fix A assume "A \<in> sets M"
    then have " {x \<in> space M. h x \<noteq> 0 \<and> indicator A x \<noteq> (0::pextreal)} = A"
      using pos sets_into_space by (force simp: indicator_def)
    then have "(\<integral>\<^isup>+x. h x * indicator A x) = 0 \<longleftrightarrow> A \<in> null_sets"
      using h_borel `A \<in> sets M` by (simp add: positive_integral_0_iff) }
  note h_null_sets = this
  { fix A assume "A \<in> sets M"
    have "(\<integral>\<^isup>+x. h x * (f x * indicator A x)) =
      f.positive_integral (\<lambda>x. h x * indicator A x)"
      using `A \<in> sets M` h_borel borel
      by (simp add: positive_integral_translated_density ac_simps cong: positive_integral_cong)
    also have "\<dots> = f'.positive_integral (\<lambda>x. h x * indicator A x)"
      by (rule f'.positive_integral_cong_measure) (rule f)
    also have "\<dots> = (\<integral>\<^isup>+x. h x * (f' x * indicator A x))"
      using `A \<in> sets M` h_borel borel
      by (simp add: positive_integral_translated_density ac_simps cong: positive_integral_cong)
    finally have "(\<integral>\<^isup>+x. h x * (f x * indicator A x)) = (\<integral>\<^isup>+x. h x * (f' x * indicator A x))" . }
  then have "h.almost_everywhere (\<lambda>x. f x = f' x)"
    using h_borel borel
    by (intro h.density_unique_finite_measure[OF borel])
       (simp add: positive_integral_translated_density)
  then show "AE x. f x = f' x"
    unfolding h.almost_everywhere_def almost_everywhere_def
    by (auto simp add: h_null_sets)
qed

lemma (in sigma_finite_measure) sigma_finite_iff_density_finite:
  assumes \<nu>: "measure_space M \<nu>" and f: "f \<in> borel_measurable M"
    and eq: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
  shows "sigma_finite_measure M \<nu> \<longleftrightarrow> (AE x. f x \<noteq> \<omega>)"
proof
  assume "sigma_finite_measure M \<nu>"
  then interpret \<nu>: sigma_finite_measure M \<nu> .
  from \<nu>.Ex_finite_integrable_function obtain h where
    h: "h \<in> borel_measurable M" "\<nu>.positive_integral h \<noteq> \<omega>"
    and fin: "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x \<and> h x < \<omega>" by auto
  have "AE x. f x * h x \<noteq> \<omega>"
  proof (rule AE_I')
    have "\<nu>.positive_integral h = (\<integral>\<^isup>+x. f x * h x)"
      by (simp add: \<nu>.positive_integral_cong_measure[symmetric, OF eq[symmetric]])
         (intro positive_integral_translated_density f h)
    then have "(\<integral>\<^isup>+x. f x * h x) \<noteq> \<omega>"
      using h(2) by simp
    then show "(\<lambda>x. f x * h x) -` {\<omega>} \<inter> space M \<in> null_sets"
      using f h(1) by (auto intro!: positive_integral_omega borel_measurable_vimage)
  qed auto
  then show "AE x. f x \<noteq> \<omega>"
  proof (rule AE_mp, intro AE_cong)
    fix x assume "x \<in> space M" from this[THEN fin]
    show "f x * h x \<noteq> \<omega> \<longrightarrow> f x \<noteq> \<omega>" by auto
  qed
next
  assume AE: "AE x. f x \<noteq> \<omega>"
  from sigma_finite guess Q .. note Q = this
  interpret \<nu>: measure_space M \<nu> by fact
  def A \<equiv> "\<lambda>i. f -` (case i of 0 \<Rightarrow> {\<omega>} | Suc n \<Rightarrow> {.. of_nat (Suc n)}) \<inter> space M"
  { fix i j have "A i \<inter> Q j \<in> sets M"
    unfolding A_def using f Q
    apply (rule_tac Int)
    by (cases i) (auto intro: measurable_sets[OF f]) }
  note A_in_sets = this
  let "?A n" = "case prod_decode n of (i,j) \<Rightarrow> A i \<inter> Q j"
  show "sigma_finite_measure M \<nu>"
  proof (default, intro exI conjI subsetI allI)
    fix x assume "x \<in> range ?A"
    then obtain n where n: "x = ?A n" by auto
    then show "x \<in> sets M" using A_in_sets by (cases "prod_decode n") auto
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
        case infinite then show ?thesis using x unfolding A_def by (auto intro: exI[of _ 0])
      next
        case (preal r)
        with less_\<omega>_Ex_of_nat[of "f x"] obtain n where "f x < of_nat n" by auto
        then show ?thesis using x preal unfolding A_def by (auto intro!: exI[of _ "Suc n"])
      qed
    qed (auto simp: A_def)
    finally show "(\<Union>i. ?A i) = space M" by simp
  next
    fix n obtain i j where
      [simp]: "prod_decode n = (i, j)" by (cases "prod_decode n") auto
    have "(\<integral>\<^isup>+x. f x * indicator (A i \<inter> Q j) x) \<noteq> \<omega>"
    proof (cases i)
      case 0
      have "AE x. f x * indicator (A i \<inter> Q j) x = 0"
        using AE by (rule AE_mp) (auto intro!: AE_cong simp: A_def `i = 0`)
      then have "(\<integral>\<^isup>+x. f x * indicator (A i \<inter> Q j) x) = 0"
        using A_in_sets f
        apply (subst positive_integral_0_iff)
        apply fast
        apply (subst (asm) AE_iff_null_set)
        apply (intro borel_measurable_pextreal_neq_const)
        apply fast
        by simp
      then show ?thesis by simp
    next
      case (Suc n)
      then have "(\<integral>\<^isup>+x. f x * indicator (A i \<inter> Q j) x) \<le>
        (\<integral>\<^isup>+x. of_nat (Suc n) * indicator (Q j) x)"
        by (auto intro!: positive_integral_mono simp: indicator_def A_def)
      also have "\<dots> = of_nat (Suc n) * \<mu> (Q j)"
        using Q by (auto intro!: positive_integral_cmult_indicator)
      also have "\<dots> < \<omega>"
        using Q by auto
      finally show ?thesis by simp
    qed
    then show "\<nu> (?A n) \<noteq> \<omega>"
      using A_in_sets Q eq by auto
  qed
qed

section "Radon-Nikodym derivative"

definition (in sigma_finite_measure)
  "RN_deriv \<nu> \<equiv> SOME f. f \<in> borel_measurable M \<and>
    (\<forall>A \<in> sets M. \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x))"

lemma (in sigma_finite_measure) RN_deriv_cong:
  assumes cong: "\<And>A. A \<in> sets M \<Longrightarrow> \<mu>' A = \<mu> A" "\<And>A. A \<in> sets M \<Longrightarrow> \<nu>' A = \<nu> A"
  shows "sigma_finite_measure.RN_deriv M \<mu>' \<nu>' x = RN_deriv \<nu> x"
proof -
  interpret \<mu>': sigma_finite_measure M \<mu>'
    using cong(1) by (rule sigma_finite_measure_cong)
  show ?thesis
    unfolding RN_deriv_def \<mu>'.RN_deriv_def
    by (simp add: cong positive_integral_cong_measure[OF cong(1)])
qed

lemma (in sigma_finite_measure) RN_deriv:
  assumes "measure_space M \<nu>"
  assumes "absolutely_continuous \<nu>"
  shows "RN_deriv \<nu> \<in> borel_measurable M" (is ?borel)
  and "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. RN_deriv \<nu> x * indicator A x)"
    (is "\<And>A. _ \<Longrightarrow> ?int A")
proof -
  note Ex = Radon_Nikodym[OF assms, unfolded Bex_def]
  thus ?borel unfolding RN_deriv_def by (rule someI2_ex) auto
  fix A assume "A \<in> sets M"
  from Ex show "?int A" unfolding RN_deriv_def
    by (rule someI2_ex) (simp add: `A \<in> sets M`)
qed

lemma (in sigma_finite_measure) RN_deriv_positive_integral:
  assumes \<nu>: "measure_space M \<nu>" "absolutely_continuous \<nu>"
    and f: "f \<in> borel_measurable M"
  shows "measure_space.positive_integral M \<nu> f = (\<integral>\<^isup>+x. RN_deriv \<nu> x * f x)"
proof -
  interpret \<nu>: measure_space M \<nu> by fact
  have "\<nu>.positive_integral f =
    measure_space.positive_integral M (\<lambda>A. (\<integral>\<^isup>+x. RN_deriv \<nu> x * indicator A x)) f"
    by (intro \<nu>.positive_integral_cong_measure[symmetric] RN_deriv(2)[OF \<nu>, symmetric])
  also have "\<dots> = (\<integral>\<^isup>+x. RN_deriv \<nu> x * f x)"
    by (intro positive_integral_translated_density RN_deriv[OF \<nu>] f)
  finally show ?thesis .
qed

lemma (in sigma_finite_measure) RN_deriv_unique:
  assumes \<nu>: "measure_space M \<nu>" "absolutely_continuous \<nu>"
  and f: "f \<in> borel_measurable M"
  and eq: "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = (\<integral>\<^isup>+x. f x * indicator A x)"
  shows "AE x. f x = RN_deriv \<nu> x"
proof (rule density_unique[OF f RN_deriv(1)[OF \<nu>]])
  fix A assume A: "A \<in> sets M"
  show "(\<integral>\<^isup>+x. f x * indicator A x) = (\<integral>\<^isup>+x. RN_deriv \<nu> x * indicator A x)"
    unfolding eq[OF A, symmetric] RN_deriv(2)[OF \<nu> A, symmetric] ..
qed


lemma (in sigma_finite_measure) RN_deriv_finite:
  assumes sfm: "sigma_finite_measure M \<nu>" and ac: "absolutely_continuous \<nu>"
  shows "AE x. RN_deriv \<nu> x \<noteq> \<omega>"
proof -
  interpret \<nu>: sigma_finite_measure M \<nu> by fact
  have \<nu>: "measure_space M \<nu>" by default
  from sfm show ?thesis
    using sigma_finite_iff_density_finite[OF \<nu> RN_deriv[OF \<nu> ac]] by simp
qed

lemma (in sigma_finite_measure)
  assumes \<nu>: "sigma_finite_measure M \<nu>" "absolutely_continuous \<nu>"
    and f: "f \<in> borel_measurable M"
  shows RN_deriv_integral: "measure_space.integral M \<nu> f = (\<integral>x. real (RN_deriv \<nu> x) * f x)" (is ?integral)
    and RN_deriv_integrable: "measure_space.integrable M \<nu> f \<longleftrightarrow> integrable (\<lambda>x. real (RN_deriv \<nu> x) * f x)" (is ?integrable)
proof -
  interpret \<nu>: sigma_finite_measure M \<nu> by fact
  have ms: "measure_space M \<nu>" by default
  have minus_cong: "\<And>A B A' B'::pextreal. A = A' \<Longrightarrow> B = B' \<Longrightarrow> real A - real B = real A' - real B'" by simp
  have f': "(\<lambda>x. - f x) \<in> borel_measurable M" using f by auto
  { fix f :: "'a \<Rightarrow> real" assume "f \<in> borel_measurable M"
    { fix x assume *: "RN_deriv \<nu> x \<noteq> \<omega>"
      have "Real (real (RN_deriv \<nu> x)) * Real (f x) = Real (real (RN_deriv \<nu> x) * f x)"
        by (simp add: mult_le_0_iff)
      then have "RN_deriv \<nu> x * Real (f x) = Real (real (RN_deriv \<nu> x) * f x)"
        using * by (simp add: Real_real) }
    note * = this
    have "(\<integral>\<^isup>+x. RN_deriv \<nu> x * Real (f x)) = (\<integral>\<^isup>+x. Real (real (RN_deriv \<nu> x) * f x))"
      apply (rule positive_integral_cong_AE)
      apply (rule AE_mp[OF RN_deriv_finite[OF \<nu>]])
      by (auto intro!: AE_cong simp: *) }
  with this[OF f] this[OF f'] f f'
  show ?integral ?integrable
    unfolding \<nu>.integral_def integral_def \<nu>.integrable_def integrable_def
    by (auto intro!: RN_deriv(1)[OF ms \<nu>(2)] minus_cong simp: RN_deriv_positive_integral[OF ms \<nu>(2)])
qed

lemma (in sigma_finite_measure) RN_deriv_singleton:
  assumes "measure_space M \<nu>"
  and ac: "absolutely_continuous \<nu>"
  and "{x} \<in> sets M"
  shows "\<nu> {x} = RN_deriv \<nu> x * \<mu> {x}"
proof -
  note deriv = RN_deriv[OF assms(1, 2)]
  from deriv(2)[OF `{x} \<in> sets M`]
  have "\<nu> {x} = (\<integral>\<^isup>+w. RN_deriv \<nu> x * indicator {x} w)"
    by (auto simp: indicator_def intro!: positive_integral_cong)
  thus ?thesis using positive_integral_cmult_indicator[OF `{x} \<in> sets M`]
    by auto
qed

theorem (in finite_measure_space) RN_deriv_finite_measure:
  assumes "measure_space M \<nu>"
  and ac: "absolutely_continuous \<nu>"
  and "x \<in> space M"
  shows "\<nu> {x} = RN_deriv \<nu> x * \<mu> {x}"
proof -
  have "{x} \<in> sets M" using sets_eq_Pow `x \<in> space M` by auto
  from RN_deriv_singleton[OF assms(1,2) this] show ?thesis .
qed

end
