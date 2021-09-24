(*  Title:      HOL/Probability/Information.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section \<open>Information theory\<close>

theory Information
imports
  Independent_Family
begin

lemma log_le: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log a x \<le> log a y"
  by (subst log_le_cancel_iff) auto

lemma log_less: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> x < y \<Longrightarrow> log a x < log a y"
  by (subst log_less_cancel_iff) auto

lemma sum_cartesian_product':
  "(\<Sum>x\<in>A \<times> B. f x) = (\<Sum>x\<in>A. sum (\<lambda>y. f (x, y)) B)"
  unfolding sum.cartesian_product by simp

lemma split_pairs:
  "((A, B) = X) \<longleftrightarrow> (fst X = A \<and> snd X = B)" and
  "(X = (A, B)) \<longleftrightarrow> (fst X = A \<and> snd X = B)" by auto

subsection "Information theory"

locale information_space = prob_space +
  fixes b :: real assumes b_gt_1: "1 < b"

context information_space
begin

text \<open>Introduce some simplification rules for logarithm of base \<^term>\<open>b\<close>.\<close>

lemma log_neg_const:
  assumes "x \<le> 0"
  shows "log b x = log b 0"
proof -
  { fix u :: real
    have "x \<le> 0" by fact
    also have "0 < exp u"
      using exp_gt_zero .
    finally have "exp u \<noteq> x"
      by auto }
  then show "log b x = log b 0"
    by (simp add: log_def ln_real_def)
qed

lemma log_mult_eq:
  "log b (A * B) = (if 0 < A * B then log b \<bar>A\<bar> + log b \<bar>B\<bar> else log b 0)"
  using log_mult[of b "\<bar>A\<bar>" "\<bar>B\<bar>"] b_gt_1 log_neg_const[of "A * B"]
  by (auto simp: zero_less_mult_iff mult_le_0_iff)

lemma log_inverse_eq:
  "log b (inverse B) = (if 0 < B then - log b B else log b 0)"
  using log_inverse[of b B] log_neg_const[of "inverse B"] b_gt_1 by simp

lemma log_divide_eq:
  "log b (A / B) = (if 0 < A * B then log b \<bar>A\<bar> - log b \<bar>B\<bar> else log b 0)"
  unfolding divide_inverse log_mult_eq log_inverse_eq abs_inverse
  by (auto simp: zero_less_mult_iff mult_le_0_iff)

lemmas log_simps = log_mult_eq log_inverse_eq log_divide_eq

end

subsection "Kullback$-$Leibler divergence"

text \<open>The Kullback$-$Leibler divergence is also known as relative entropy or
Kullback$-$Leibler distance.\<close>

definition
  "entropy_density b M N = log b \<circ> enn2real \<circ> RN_deriv M N"

definition
  "KL_divergence b M N = integral\<^sup>L N (entropy_density b M N)"

lemma measurable_entropy_density[measurable]: "entropy_density b M N \<in> borel_measurable M"
  unfolding entropy_density_def by auto

lemma (in sigma_finite_measure) KL_density:
  fixes f :: "'a \<Rightarrow> real"
  assumes "1 < b"
  assumes f[measurable]: "f \<in> borel_measurable M" and nn: "AE x in M. 0 \<le> f x"
  shows "KL_divergence b M (density M f) = (\<integral>x. f x * log b (f x) \<partial>M)"
  unfolding KL_divergence_def
proof (subst integral_real_density)
  show [measurable]: "entropy_density b M (density M (\<lambda>x. ennreal (f x))) \<in> borel_measurable M"
    using f
    by (auto simp: comp_def entropy_density_def)
  have "density M (RN_deriv M (density M f)) = density M f"
    using f nn by (intro density_RN_deriv_density) auto
  then have eq: "AE x in M. RN_deriv M (density M f) x = f x"
    using f nn by (intro density_unique) auto
  show "(\<integral>x. f x * entropy_density b M (density M (\<lambda>x. ennreal (f x))) x \<partial>M) = (\<integral>x. f x * log b (f x) \<partial>M)"
    apply (intro integral_cong_AE)
    apply measurable
    using eq nn
    apply eventually_elim
    apply (auto simp: entropy_density_def)
    done
qed fact+

lemma (in sigma_finite_measure) KL_density_density:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "1 < b"
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  assumes ac: "AE x in M. f x = 0 \<longrightarrow> g x = 0"
  shows "KL_divergence b (density M f) (density M g) = (\<integral>x. g x * log b (g x / f x) \<partial>M)"
proof -
  interpret Mf: sigma_finite_measure "density M f"
    using f by (subst sigma_finite_iff_density_finite) auto
  have "KL_divergence b (density M f) (density M g) =
    KL_divergence b (density M f) (density (density M f) (\<lambda>x. g x / f x))"
    using f g ac by (subst density_density_divide) simp_all
  also have "\<dots> = (\<integral>x. (g x / f x) * log b (g x / f x) \<partial>density M f)"
    using f g \<open>1 < b\<close> by (intro Mf.KL_density) (auto simp: AE_density)
  also have "\<dots> = (\<integral>x. g x * log b (g x / f x) \<partial>M)"
    using ac f g \<open>1 < b\<close> by (subst integral_density) (auto intro!: integral_cong_AE)
  finally show ?thesis .
qed

lemma (in information_space) KL_gt_0:
  fixes D :: "'a \<Rightarrow> real"
  assumes "prob_space (density M D)"
  assumes D: "D \<in> borel_measurable M" "AE x in M. 0 \<le> D x"
  assumes int: "integrable M (\<lambda>x. D x * log b (D x))"
  assumes A: "density M D \<noteq> M"
  shows "0 < KL_divergence b M (density M D)"
proof -
  interpret N: prob_space "density M D" by fact

  obtain A where "A \<in> sets M" "emeasure (density M D) A \<noteq> emeasure M A"
    using measure_eqI[of "density M D" M] \<open>density M D \<noteq> M\<close> by auto

  let ?D_set = "{x\<in>space M. D x \<noteq> 0}"
  have [simp, intro]: "?D_set \<in> sets M"
    using D by auto

  have D_neg: "(\<integral>\<^sup>+ x. ennreal (- D x) \<partial>M) = 0"
    using D by (subst nn_integral_0_iff_AE) (auto simp: ennreal_neg)

  have "(\<integral>\<^sup>+ x. ennreal (D x) \<partial>M) = emeasure (density M D) (space M)"
    using D by (simp add: emeasure_density cong: nn_integral_cong)
  then have D_pos: "(\<integral>\<^sup>+ x. ennreal (D x) \<partial>M) = 1"
    using N.emeasure_space_1 by simp

  have "integrable M D"
    using D D_pos D_neg unfolding real_integrable_def real_lebesgue_integral_def by simp_all
  then have "integral\<^sup>L M D = 1"
    using D D_pos D_neg by (simp add: real_lebesgue_integral_def)

  have "0 \<le> 1 - measure M ?D_set"
    using prob_le_1 by (auto simp: field_simps)
  also have "\<dots> = (\<integral> x. D x - indicator ?D_set x \<partial>M)"
    using \<open>integrable M D\<close> \<open>integral\<^sup>L M D = 1\<close>
    by (simp add: emeasure_eq_measure)
  also have "\<dots> < (\<integral> x. D x * (ln b * log b (D x)) \<partial>M)"
  proof (rule integral_less_AE)
    show "integrable M (\<lambda>x. D x - indicator ?D_set x)"
      using \<open>integrable M D\<close> by (auto simp: less_top[symmetric])
  next
    from integrable_mult_left(1)[OF int, of "ln b"]
    show "integrable M (\<lambda>x. D x * (ln b * log b (D x)))"
      by (simp add: ac_simps)
  next
    show "emeasure M {x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} \<noteq> 0"
    proof
      assume eq_0: "emeasure M {x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} = 0"
      then have disj: "AE x in M. D x = 1 \<or> D x = 0"
        using D(1) by (auto intro!: AE_I[OF subset_refl] sets.sets_Collect)

      have "emeasure M {x\<in>space M. D x = 1} = (\<integral>\<^sup>+ x. indicator {x\<in>space M. D x = 1} x \<partial>M)"
        using D(1) by auto
      also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (D x) \<partial>M)"
        using disj by (auto intro!: nn_integral_cong_AE simp: indicator_def one_ennreal_def)
      finally have "AE x in M. D x = 1"
        using D D_pos by (intro AE_I_eq_1) auto
      then have "(\<integral>\<^sup>+x. indicator A x\<partial>M) = (\<integral>\<^sup>+x. ennreal (D x) * indicator A x\<partial>M)"
        by (intro nn_integral_cong_AE) (auto simp: one_ennreal_def[symmetric])
      also have "\<dots> = density M D A"
        using \<open>A \<in> sets M\<close> D by (simp add: emeasure_density)
      finally show False using \<open>A \<in> sets M\<close> \<open>emeasure (density M D) A \<noteq> emeasure M A\<close> by simp
    qed
    show "{x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} \<in> sets M"
      using D(1) by (auto intro: sets.sets_Collect_conj)

    show "AE t in M. t \<in> {x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} \<longrightarrow>
      D t - indicator ?D_set t \<noteq> D t * (ln b * log b (D t))"
      using D(2)
    proof (eventually_elim, safe)
      fix t assume Dt: "t \<in> space M" "D t \<noteq> 1" "D t \<noteq> 0" "0 \<le> D t"
        and eq: "D t - indicator ?D_set t = D t * (ln b * log b (D t))"

      have "D t - 1 = D t - indicator ?D_set t"
        using Dt by simp
      also note eq
      also have "D t * (ln b * log b (D t)) = - D t * ln (1 / D t)"
        using b_gt_1 \<open>D t \<noteq> 0\<close> \<open>0 \<le> D t\<close>
        by (simp add: log_def ln_div less_le)
      finally have "ln (1 / D t) = 1 / D t - 1"
        using \<open>D t \<noteq> 0\<close> by (auto simp: field_simps)
      from ln_eq_minus_one[OF _ this] \<open>D t \<noteq> 0\<close> \<open>0 \<le> D t\<close> \<open>D t \<noteq> 1\<close>
      show False by auto
    qed

    show "AE t in M. D t - indicator ?D_set t \<le> D t * (ln b * log b (D t))"
      using D(2) AE_space
    proof eventually_elim
      fix t assume "t \<in> space M" "0 \<le> D t"
      show "D t - indicator ?D_set t \<le> D t * (ln b * log b (D t))"
      proof cases
        assume asm: "D t \<noteq> 0"
        then have "0 < D t" using \<open>0 \<le> D t\<close> by auto
        then have "0 < 1 / D t" by auto
        have "D t - indicator ?D_set t \<le> - D t * (1 / D t - 1)"
          using asm \<open>t \<in> space M\<close> by (simp add: field_simps)
        also have "- D t * (1 / D t - 1) \<le> - D t * ln (1 / D t)"
          using ln_le_minus_one \<open>0 < 1 / D t\<close> by (intro mult_left_mono_neg) auto
        also have "\<dots> = D t * (ln b * log b (D t))"
          using \<open>0 < D t\<close> b_gt_1
          by (simp_all add: log_def ln_div)
        finally show ?thesis by simp
      qed simp
    qed
  qed
  also have "\<dots> = (\<integral> x. ln b * (D x * log b (D x)) \<partial>M)"
    by (simp add: ac_simps)
  also have "\<dots> = ln b * (\<integral> x. D x * log b (D x) \<partial>M)"
    using int by simp
  finally show ?thesis
    using b_gt_1 D by (subst KL_density) (auto simp: zero_less_mult_iff)
qed

lemma (in sigma_finite_measure) KL_same_eq_0: "KL_divergence b M M = 0"
proof -
  have "AE x in M. 1 = RN_deriv M M x"
  proof (rule RN_deriv_unique)
    show "density M (\<lambda>x. 1) = M"
      apply (auto intro!: measure_eqI emeasure_density)
      apply (subst emeasure_density)
      apply auto
      done
  qed auto
  then have "AE x in M. log b (enn2real (RN_deriv M M x)) = 0"
    by (elim AE_mp) simp
  from integral_cong_AE[OF _ _ this]
  have "integral\<^sup>L M (entropy_density b M M) = 0"
    by (simp add: entropy_density_def comp_def)
  then show "KL_divergence b M M = 0"
    unfolding KL_divergence_def
    by auto
qed

lemma (in information_space) KL_eq_0_iff_eq:
  fixes D :: "'a \<Rightarrow> real"
  assumes "prob_space (density M D)"
  assumes D: "D \<in> borel_measurable M" "AE x in M. 0 \<le> D x"
  assumes int: "integrable M (\<lambda>x. D x * log b (D x))"
  shows "KL_divergence b M (density M D) = 0 \<longleftrightarrow> density M D = M"
  using KL_same_eq_0[of b] KL_gt_0[OF assms]
  by (auto simp: less_le)

lemma (in information_space) KL_eq_0_iff_eq_ac:
  fixes D :: "'a \<Rightarrow> real"
  assumes "prob_space N"
  assumes ac: "absolutely_continuous M N" "sets N = sets M"
  assumes int: "integrable N (entropy_density b M N)"
  shows "KL_divergence b M N = 0 \<longleftrightarrow> N = M"
proof -
  interpret N: prob_space N by fact
  have "finite_measure N" by unfold_locales
  from real_RN_deriv[OF this ac] obtain D
    where D:
      "random_variable borel D"
      "AE x in M. RN_deriv M N x = ennreal (D x)"
      "AE x in N. 0 < D x"
      "\<And>x. 0 \<le> D x"
    by this auto

  have "N = density M (RN_deriv M N)"
    using ac by (rule density_RN_deriv[symmetric])
  also have "\<dots> = density M D"
    using D by (auto intro!: density_cong)
  finally have N: "N = density M D" .

  from absolutely_continuous_AE[OF ac(2,1) D(2)] D b_gt_1 ac measurable_entropy_density
  have "integrable N (\<lambda>x. log b (D x))"
    by (intro integrable_cong_AE[THEN iffD2, OF _ _ _ int])
       (auto simp: N entropy_density_def)
  with D b_gt_1 have "integrable M (\<lambda>x. D x * log b (D x))"
    by (subst integrable_real_density[symmetric]) (auto simp: N[symmetric] comp_def)
  with \<open>prob_space N\<close> D show ?thesis
    unfolding N
    by (intro KL_eq_0_iff_eq) auto
qed

lemma (in information_space) KL_nonneg:
  assumes "prob_space (density M D)"
  assumes D: "D \<in> borel_measurable M" "AE x in M. 0 \<le> D x"
  assumes int: "integrable M (\<lambda>x. D x * log b (D x))"
  shows "0 \<le> KL_divergence b M (density M D)"
  using KL_gt_0[OF assms] by (cases "density M D = M") (auto simp: KL_same_eq_0)

lemma (in sigma_finite_measure) KL_density_density_nonneg:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "1 < b"
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x" "prob_space (density M f)"
  assumes g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x" "prob_space (density M g)"
  assumes ac: "AE x in M. f x = 0 \<longrightarrow> g x = 0"
  assumes int: "integrable M (\<lambda>x. g x * log b (g x / f x))"
  shows "0 \<le> KL_divergence b (density M f) (density M g)"
proof -
  interpret Mf: prob_space "density M f" by fact
  interpret Mf: information_space "density M f" b by standard fact
  have eq: "density (density M f) (\<lambda>x. g x / f x) = density M g" (is "?DD = _")
    using f g ac by (subst density_density_divide) simp_all

  have "0 \<le> KL_divergence b (density M f) (density (density M f) (\<lambda>x. g x / f x))"
  proof (rule Mf.KL_nonneg)
    show "prob_space ?DD" unfolding eq by fact
    from f g show "(\<lambda>x. g x / f x) \<in> borel_measurable (density M f)"
      by auto
    show "AE x in density M f. 0 \<le> g x / f x"
      using f g by (auto simp: AE_density)
    show "integrable (density M f) (\<lambda>x. g x / f x * log b (g x / f x))"
      using \<open>1 < b\<close> f g ac
      by (subst integrable_density)
         (auto intro!: integrable_cong_AE[THEN iffD2, OF _ _ _ int] measurable_If)
  qed
  also have "\<dots> = KL_divergence b (density M f) (density M g)"
    using f g ac by (subst density_density_divide) simp_all
  finally show ?thesis .
qed

subsection \<open>Finite Entropy\<close>

definition (in information_space) finite_entropy :: "'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> bool"
where
  "finite_entropy S X f \<longleftrightarrow>
    distributed M S X f \<and>
    integrable S (\<lambda>x. f x * log b (f x)) \<and>
    (\<forall>x\<in>space S. 0 \<le> f x)"

lemma (in information_space) finite_entropy_simple_function:
  assumes X: "simple_function M X"
  shows "finite_entropy (count_space (X`space M)) X (\<lambda>a. measure M {x \<in> space M. X x = a})"
  unfolding finite_entropy_def
proof safe
  have [simp]: "finite (X ` space M)"
    using X by (auto simp: simple_function_def)
  then show "integrable (count_space (X ` space M))
     (\<lambda>x. prob {xa \<in> space M. X xa = x} * log b (prob {xa \<in> space M. X xa = x}))"
    by (rule integrable_count_space)
  have d: "distributed M (count_space (X ` space M)) X (\<lambda>x. ennreal (if x \<in> X`space M then prob {xa \<in> space M. X xa = x} else 0))"
    by (rule distributed_simple_function_superset[OF X]) (auto intro!: arg_cong[where f=prob])
  show "distributed M (count_space (X ` space M)) X (\<lambda>x. ennreal (prob {xa \<in> space M. X xa = x}))"
    by (rule distributed_cong_density[THEN iffD1, OF _ _ _ d]) auto
qed (rule measure_nonneg)

lemma ac_fst:
  assumes "sigma_finite_measure T"
  shows "absolutely_continuous S (distr (S \<Otimes>\<^sub>M T) S fst)"
proof -
  interpret sigma_finite_measure T by fact
  { fix A assume A: "A \<in> sets S" "emeasure S A = 0"
    then have "fst -` A \<inter> space (S \<Otimes>\<^sub>M T) = A \<times> space T"
      by (auto simp: space_pair_measure dest!: sets.sets_into_space)
    with A have "emeasure (S \<Otimes>\<^sub>M T) (fst -` A \<inter> space (S \<Otimes>\<^sub>M T)) = 0"
      by (simp add: emeasure_pair_measure_Times) }
  then show ?thesis
    unfolding absolutely_continuous_def
    apply (auto simp: null_sets_distr_iff)
    apply (auto simp: null_sets_def intro!: measurable_sets)
    done
qed

lemma ac_snd:
  assumes "sigma_finite_measure T"
  shows "absolutely_continuous T (distr (S \<Otimes>\<^sub>M T) T snd)"
proof -
  interpret sigma_finite_measure T by fact
  { fix A assume A: "A \<in> sets T" "emeasure T A = 0"
    then have "snd -` A \<inter> space (S \<Otimes>\<^sub>M T) = space S \<times> A"
      by (auto simp: space_pair_measure dest!: sets.sets_into_space)
    with A have "emeasure (S \<Otimes>\<^sub>M T) (snd -` A \<inter> space (S \<Otimes>\<^sub>M T)) = 0"
      by (simp add: emeasure_pair_measure_Times) }
  then show ?thesis
    unfolding absolutely_continuous_def
    apply (auto simp: null_sets_distr_iff)
    apply (auto simp: null_sets_def intro!: measurable_sets)
    done
qed

lemma (in information_space) finite_entropy_integrable:
  "finite_entropy S X Px \<Longrightarrow> integrable S (\<lambda>x. Px x * log b (Px x))"
  unfolding finite_entropy_def by auto

lemma (in information_space) finite_entropy_distributed:
  "finite_entropy S X Px \<Longrightarrow> distributed M S X Px"
  unfolding finite_entropy_def by auto

lemma (in information_space) finite_entropy_nn:
  "finite_entropy S X Px \<Longrightarrow> x \<in> space S \<Longrightarrow> 0 \<le> Px x"
  by (auto simp: finite_entropy_def)

lemma (in information_space) finite_entropy_measurable:
  "finite_entropy S X Px \<Longrightarrow> Px \<in> S \<rightarrow>\<^sub>M borel"
  using distributed_real_measurable[of S Px M X]
    finite_entropy_nn[of S X Px] finite_entropy_distributed[of S X Px] by auto

lemma (in information_space) subdensity_finite_entropy:
  fixes g :: "'b \<Rightarrow> real" and f :: "'c \<Rightarrow> real"
  assumes T: "T \<in> measurable P Q"
  assumes f: "finite_entropy P X f"
  assumes g: "finite_entropy Q Y g"
  assumes Y: "Y = T \<circ> X"
  shows "AE x in P. g (T x) = 0 \<longrightarrow> f x = 0"
  using subdensity[OF T, of M X "\<lambda>x. ennreal (f x)" Y "\<lambda>x. ennreal (g x)"]
    finite_entropy_distributed[OF f] finite_entropy_distributed[OF g]
    finite_entropy_nn[OF f] finite_entropy_nn[OF g]
    assms
  by auto

lemma (in information_space) finite_entropy_integrable_transform:
  "finite_entropy S X Px \<Longrightarrow> distributed M T Y Py \<Longrightarrow> (\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x) \<Longrightarrow>
    X = (\<lambda>x. f (Y x)) \<Longrightarrow> f \<in> measurable T S \<Longrightarrow> integrable T (\<lambda>x. Py x * log b (Px (f x)))"
  using distributed_transform_integrable[of M T Y Py S X Px f "\<lambda>x. log b (Px x)"]
  using distributed_real_measurable[of S Px M X]
  by (auto simp: finite_entropy_def)

subsection \<open>Mutual Information\<close>

definition (in prob_space)
  "mutual_information b S T X Y =
    KL_divergence b (distr M S X \<Otimes>\<^sub>M distr M T Y) (distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)))"

lemma (in information_space) mutual_information_indep_vars:
  fixes S T X Y
  defines "P \<equiv> distr M S X \<Otimes>\<^sub>M distr M T Y"
  defines "Q \<equiv> distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
  shows "indep_var S X T Y \<longleftrightarrow>
    (random_variable S X \<and> random_variable T Y \<and>
      absolutely_continuous P Q \<and> integrable Q (entropy_density b P Q) \<and>
      mutual_information b S T X Y = 0)"
  unfolding indep_var_distribution_eq
proof safe
  assume rv[measurable]: "random_variable S X" "random_variable T Y"

  interpret X: prob_space "distr M S X"
    by (rule prob_space_distr) fact
  interpret Y: prob_space "distr M T Y"
    by (rule prob_space_distr) fact
  interpret XY: pair_prob_space "distr M S X" "distr M T Y" by standard
  interpret P: information_space P b unfolding P_def by standard (rule b_gt_1)

  interpret Q: prob_space Q unfolding Q_def
    by (rule prob_space_distr) simp

  { assume "distr M S X \<Otimes>\<^sub>M distr M T Y = distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
    then have [simp]: "Q = P"  unfolding Q_def P_def by simp

    show ac: "absolutely_continuous P Q" by (simp add: absolutely_continuous_def)
    then have ed: "entropy_density b P Q \<in> borel_measurable P"
      by simp

    have "AE x in P. 1 = RN_deriv P Q x"
    proof (rule P.RN_deriv_unique)
      show "density P (\<lambda>x. 1) = Q"
        unfolding \<open>Q = P\<close> by (intro measure_eqI) (auto simp: emeasure_density)
    qed auto
    then have ae_0: "AE x in P. entropy_density b P Q x = 0"
      by eventually_elim (auto simp: entropy_density_def)
    then have "integrable P (entropy_density b P Q) \<longleftrightarrow> integrable Q (\<lambda>x. 0::real)"
      using ed unfolding \<open>Q = P\<close> by (intro integrable_cong_AE) auto
    then show "integrable Q (entropy_density b P Q)" by simp

    from ae_0 have "mutual_information b S T X Y = (\<integral>x. 0 \<partial>P)"
      unfolding mutual_information_def KL_divergence_def P_def[symmetric] Q_def[symmetric] \<open>Q = P\<close>
      by (intro integral_cong_AE) auto
    then show "mutual_information b S T X Y = 0"
      by simp }

  { assume ac: "absolutely_continuous P Q"
    assume int: "integrable Q (entropy_density b P Q)"
    assume I_eq_0: "mutual_information b S T X Y = 0"

    have eq: "Q = P"
    proof (rule P.KL_eq_0_iff_eq_ac[THEN iffD1])
      show "prob_space Q" by unfold_locales
      show "absolutely_continuous P Q" by fact
      show "integrable Q (entropy_density b P Q)" by fact
      show "sets Q = sets P" by (simp add: P_def Q_def sets_pair_measure)
      show "KL_divergence b P Q = 0"
        using I_eq_0 unfolding mutual_information_def by (simp add: P_def Q_def)
    qed
    then show "distr M S X \<Otimes>\<^sub>M distr M T Y = distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
      unfolding P_def Q_def .. }
qed

abbreviation (in information_space)
  mutual_information_Pow ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> mutual_information b (count_space (X`space M)) (count_space (Y`space M)) X Y"

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Fx: "finite_entropy S X Px" and Fy: "finite_entropy T Y Py"
  assumes Fxy: "finite_entropy (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  defines "f \<equiv> \<lambda>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x)))"
  shows mutual_information_distr': "mutual_information b S T X Y = integral\<^sup>L (S \<Otimes>\<^sub>M T) f" (is "?M = ?R")
    and mutual_information_nonneg': "0 \<le> mutual_information b S T X Y"
proof -
  have Px: "distributed M S X Px" and Px_nn: "\<And>x. x \<in> space S \<Longrightarrow> 0 \<le> Px x"
    using Fx by (auto simp: finite_entropy_def)
  have Py: "distributed M T Y Py" and Py_nn: "\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x"
    using Fy by (auto simp: finite_entropy_def)
  have Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    and Pxy_nn: "\<And>x. x \<in> space (S \<Otimes>\<^sub>M T) \<Longrightarrow> 0 \<le> Pxy x"
      "\<And>x y. x \<in> space S \<Longrightarrow> y \<in> space T \<Longrightarrow> 0 \<le> Pxy (x, y)"
    using Fxy by (auto simp: finite_entropy_def space_pair_measure)

  have [measurable]: "Px \<in> S \<rightarrow>\<^sub>M borel"
    using Px Px_nn by (intro distributed_real_measurable)
  have [measurable]: "Py \<in> T \<rightarrow>\<^sub>M borel"
    using Py Py_nn by (intro distributed_real_measurable)
  have measurable_Pxy[measurable]: "Pxy \<in> (S \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M borel"
    using Pxy Pxy_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)

  have X[measurable]: "random_variable S X"
    using Px by auto
  have Y[measurable]: "random_variable T Y"
    using Py by auto
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  interpret X: prob_space "distr M S X" using X by (rule prob_space_distr)
  interpret Y: prob_space "distr M T Y" using Y by (rule prob_space_distr)
  interpret XY: pair_prob_space "distr M S X" "distr M T Y" ..
  let ?P = "S \<Otimes>\<^sub>M T"
  let ?D = "distr M ?P (\<lambda>x. (X x, Y x))"

  { fix A assume "A \<in> sets S"
    with X[THEN measurable_space] Y[THEN measurable_space]
    have "emeasure (distr M S X) A = emeasure ?D (A \<times> space T)"
      by (auto simp: emeasure_distr intro!: arg_cong[where f="emeasure M"]) }
  note marginal_eq1 = this
  { fix A assume "A \<in> sets T"
    with X[THEN measurable_space] Y[THEN measurable_space]
    have "emeasure (distr M T Y) A = emeasure ?D (space S \<times> A)"
      by (auto simp: emeasure_distr intro!: arg_cong[where f="emeasure M"]) }
  note marginal_eq2 = this

  have distr_eq: "distr M S X \<Otimes>\<^sub>M distr M T Y = density ?P (\<lambda>x. ennreal (Px (fst x) * Py (snd x)))"
    unfolding Px(1)[THEN distributed_distr_eq_density] Py(1)[THEN distributed_distr_eq_density]
  proof (subst pair_measure_density)
    show "(\<lambda>x. ennreal (Px x)) \<in> borel_measurable S" "(\<lambda>y. ennreal (Py y)) \<in> borel_measurable T"
      using Px Py by (auto simp: distributed_def)
    show "sigma_finite_measure (density T Py)" unfolding Py(1)[THEN distributed_distr_eq_density, symmetric] ..
    show "density (S \<Otimes>\<^sub>M T) (\<lambda>(x, y). ennreal (Px x) * ennreal (Py y)) =
      density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Px (fst x) * Py (snd x)))"
      using Px_nn Py_nn by (auto intro!: density_cong simp: distributed_def ennreal_mult space_pair_measure)
  qed fact

  have M: "?M = KL_divergence b (density ?P (\<lambda>x. ennreal (Px (fst x) * Py (snd x)))) (density ?P (\<lambda>x. ennreal (Pxy x)))"
    unfolding mutual_information_def distr_eq Pxy(1)[THEN distributed_distr_eq_density] ..

  from Px Py have f: "(\<lambda>x. Px (fst x) * Py (snd x)) \<in> borel_measurable ?P"
    by (intro borel_measurable_times) (auto intro: distributed_real_measurable measurable_fst'' measurable_snd'')
  have PxPy_nonneg: "AE x in ?P. 0 \<le> Px (fst x) * Py (snd x)"
    using Px_nn Py_nn by (auto simp: space_pair_measure)

  have A: "(AE x in ?P. Px (fst x) = 0 \<longrightarrow> Pxy x = 0)"
    by (rule subdensity_real[OF measurable_fst Pxy Px]) (insert Px_nn Pxy_nn, auto simp: space_pair_measure)
  moreover
  have B: "(AE x in ?P. Py (snd x) = 0 \<longrightarrow> Pxy x = 0)"
    by (rule subdensity_real[OF measurable_snd Pxy Py]) (insert Py_nn Pxy_nn, auto simp: space_pair_measure)
  ultimately have ac: "AE x in ?P. Px (fst x) * Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by eventually_elim auto

  show "?M = ?R"
    unfolding M f_def using Pxy_nn Px_nn Py_nn
    by (intro ST.KL_density_density b_gt_1 f PxPy_nonneg ac) (auto simp: space_pair_measure)

  have X: "X = fst \<circ> (\<lambda>x. (X x, Y x))" and Y: "Y = snd \<circ> (\<lambda>x. (X x, Y x))"
    by auto

  have "integrable (S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Pxy x) - Pxy x * log b (Px (fst x)) - Pxy x * log b (Py (snd x)))"
    using finite_entropy_integrable[OF Fxy]
    using finite_entropy_integrable_transform[OF Fx Pxy, of fst]
    using finite_entropy_integrable_transform[OF Fy Pxy, of snd]
    by (simp add: Pxy_nn)
  moreover have "f \<in> borel_measurable (S \<Otimes>\<^sub>M T)"
    unfolding f_def using Px Py Pxy
    by (auto intro: distributed_real_measurable measurable_fst'' measurable_snd''
      intro!: borel_measurable_times borel_measurable_log borel_measurable_divide)
  ultimately have int: "integrable (S \<Otimes>\<^sub>M T) f"
    apply (rule integrable_cong_AE_imp)
    using A B AE_space
    by eventually_elim
       (auto simp: f_def log_divide_eq log_mult_eq field_simps space_pair_measure Px_nn Py_nn Pxy_nn
                  less_le)

  show "0 \<le> ?M" unfolding M
  proof (intro ST.KL_density_density_nonneg)
    show "prob_space (density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Pxy x))) "
      unfolding distributed_distr_eq_density[OF Pxy, symmetric]
      using distributed_measurable[OF Pxy] by (rule prob_space_distr)
    show "prob_space (density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Px (fst x) * Py (snd x))))"
      unfolding distr_eq[symmetric] by unfold_locales
    show "integrable (S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))))"
      using int unfolding f_def .
  qed (insert ac, auto simp: b_gt_1 Px_nn Py_nn Pxy_nn space_pair_measure)
qed

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Px: "distributed M S X Px" and Px_nn: "\<And>x. x \<in> space S \<Longrightarrow> 0 \<le> Px x"
    and Py: "distributed M T Y Py" and Py_nn: "\<And>y. y \<in> space T \<Longrightarrow> 0 \<le> Py y"
    and Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    and Pxy_nn: "\<And>x y. x \<in> space S \<Longrightarrow> y \<in> space T \<Longrightarrow> 0 \<le> Pxy (x, y)"
  defines "f \<equiv> \<lambda>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x)))"
  shows mutual_information_distr: "mutual_information b S T X Y = integral\<^sup>L (S \<Otimes>\<^sub>M T) f" (is "?M = ?R")
    and mutual_information_nonneg: "integrable (S \<Otimes>\<^sub>M T) f \<Longrightarrow> 0 \<le> mutual_information b S T X Y"
proof -
  have X[measurable]: "random_variable S X"
    using Px by (auto simp: distributed_def)
  have Y[measurable]: "random_variable T Y"
    using Py by (auto simp: distributed_def)
  have [measurable]: "Px \<in> S \<rightarrow>\<^sub>M borel"
    using Px Px_nn by (intro distributed_real_measurable)
  have [measurable]: "Py \<in> T \<rightarrow>\<^sub>M borel"
    using Py Py_nn by (intro distributed_real_measurable)
  have measurable_Pxy[measurable]: "Pxy \<in> (S \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M borel"
    using Pxy Pxy_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)

  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  interpret X: prob_space "distr M S X" using X by (rule prob_space_distr)
  interpret Y: prob_space "distr M T Y" using Y by (rule prob_space_distr)
  interpret XY: pair_prob_space "distr M S X" "distr M T Y" ..
  let ?P = "S \<Otimes>\<^sub>M T"
  let ?D = "distr M ?P (\<lambda>x. (X x, Y x))"

  { fix A assume "A \<in> sets S"
    with X[THEN measurable_space] Y[THEN measurable_space]
    have "emeasure (distr M S X) A = emeasure ?D (A \<times> space T)"
      by (auto simp: emeasure_distr intro!: arg_cong[where f="emeasure M"]) }
  note marginal_eq1 = this
  { fix A assume "A \<in> sets T"
    with X[THEN measurable_space] Y[THEN measurable_space]
    have "emeasure (distr M T Y) A = emeasure ?D (space S \<times> A)"
      by (auto simp: emeasure_distr intro!: arg_cong[where f="emeasure M"]) }
  note marginal_eq2 = this

  have distr_eq: "distr M S X \<Otimes>\<^sub>M distr M T Y = density ?P (\<lambda>x. ennreal (Px (fst x) * Py (snd x)))"
    unfolding Px(1)[THEN distributed_distr_eq_density] Py(1)[THEN distributed_distr_eq_density]
  proof (subst pair_measure_density)
    show "(\<lambda>x. ennreal (Px x)) \<in> borel_measurable S" "(\<lambda>y. ennreal (Py y)) \<in> borel_measurable T"
      using Px Py by (auto simp: distributed_def)
    show "sigma_finite_measure (density T Py)" unfolding Py(1)[THEN distributed_distr_eq_density, symmetric] ..
    show "density (S \<Otimes>\<^sub>M T) (\<lambda>(x, y). ennreal (Px x) * ennreal (Py y)) =
      density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Px (fst x) * Py (snd x)))"
      using Px_nn Py_nn by (auto intro!: density_cong simp: distributed_def ennreal_mult space_pair_measure)
  qed fact

  have M: "?M = KL_divergence b (density ?P (\<lambda>x. ennreal (Px (fst x) * Py (snd x)))) (density ?P (\<lambda>x. ennreal (Pxy x)))"
    unfolding mutual_information_def distr_eq Pxy(1)[THEN distributed_distr_eq_density] ..

  from Px Py have f: "(\<lambda>x. Px (fst x) * Py (snd x)) \<in> borel_measurable ?P"
    by (intro borel_measurable_times) (auto intro: distributed_real_measurable measurable_fst'' measurable_snd'')
  have PxPy_nonneg: "AE x in ?P. 0 \<le> Px (fst x) * Py (snd x)"
    using Px_nn Py_nn by (auto simp: space_pair_measure)

  have "(AE x in ?P. Px (fst x) = 0 \<longrightarrow> Pxy x = 0)"
    by (rule subdensity_real[OF measurable_fst Pxy Px]) (insert Px_nn Pxy_nn, auto simp: space_pair_measure)
  moreover
  have "(AE x in ?P. Py (snd x) = 0 \<longrightarrow> Pxy x = 0)"
    by (rule subdensity_real[OF measurable_snd Pxy Py]) (insert Py_nn Pxy_nn, auto simp: space_pair_measure)
  ultimately have ac: "AE x in ?P. Px (fst x) * Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by eventually_elim auto

  show "?M = ?R"
    unfolding M f_def
    using b_gt_1 f PxPy_nonneg ac Pxy_nn
    by (intro ST.KL_density_density) (auto simp: space_pair_measure)

  assume int: "integrable (S \<Otimes>\<^sub>M T) f"
  show "0 \<le> ?M" unfolding M
  proof (intro ST.KL_density_density_nonneg)
    show "prob_space (density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Pxy x))) "
      unfolding distributed_distr_eq_density[OF Pxy, symmetric]
      using distributed_measurable[OF Pxy] by (rule prob_space_distr)
    show "prob_space (density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Px (fst x) * Py (snd x))))"
      unfolding distr_eq[symmetric] by unfold_locales
    show "integrable (S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))))"
      using int unfolding f_def .
  qed (insert ac, auto simp: b_gt_1 Px_nn Py_nn Pxy_nn space_pair_measure)
qed

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Px[measurable]: "distributed M S X Px" and Px_nn: "\<And>x. x \<in> space S \<Longrightarrow> 0 \<le> Px x"
    and Py[measurable]: "distributed M T Y Py" and Py_nn:  "\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x"
    and Pxy[measurable]: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    and Pxy_nn: "\<And>x. x \<in> space (S \<Otimes>\<^sub>M T) \<Longrightarrow> 0 \<le> Pxy x"
  assumes ae: "AE x in S. AE y in T. Pxy (x, y) = Px x * Py y"
  shows mutual_information_eq_0: "mutual_information b S T X Y = 0"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  note
    distributed_real_measurable[OF Px_nn Px, measurable]
    distributed_real_measurable[OF Py_nn Py, measurable]
    distributed_real_measurable[OF Pxy_nn Pxy, measurable]

  have "AE x in S \<Otimes>\<^sub>M T. Px (fst x) = 0 \<longrightarrow> Pxy x = 0"
    by (rule subdensity_real[OF measurable_fst Pxy Px]) (auto simp: Px_nn Pxy_nn space_pair_measure)
  moreover
  have "AE x in S \<Otimes>\<^sub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (rule subdensity_real[OF measurable_snd Pxy Py]) (auto simp: Py_nn Pxy_nn space_pair_measure)
  moreover
  have "AE x in S \<Otimes>\<^sub>M T. Pxy x = Px (fst x) * Py (snd x)"
    by (intro ST.AE_pair_measure) (auto simp: ae intro!: measurable_snd'' measurable_fst'')
  ultimately have "AE x in S \<Otimes>\<^sub>M T. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))) = 0"
    by eventually_elim simp
  then have "(\<integral>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))) \<partial>(S \<Otimes>\<^sub>M T)) = (\<integral>x. 0 \<partial>(S \<Otimes>\<^sub>M T))"
    by (intro integral_cong_AE) auto
  then show ?thesis
    by (subst mutual_information_distr[OF assms(1-8)]) (auto simp add: space_pair_measure)
qed

lemma (in information_space) mutual_information_simple_distributed:
  assumes X: "simple_distributed M X Px" and Y: "simple_distributed M Y Py"
  assumes XY: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
  shows "\<I>(X ; Y) = (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x))`space M. Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y)))"
proof (subst mutual_information_distr[OF _ _ simple_distributed[OF X] _ simple_distributed[OF Y] _ simple_distributed_joint[OF XY]])
  note fin = simple_distributed_joint_finite[OF XY, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  let ?Pxy = "\<lambda>x. (if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x else 0)"
  let ?f = "\<lambda>x. ?Pxy x * log b (?Pxy x / (Px (fst x) * Py (snd x)))"
  have "\<And>x. ?f x = (if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))) else 0)"
    by auto
  with fin show "(\<integral> x. ?f x \<partial>(count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M))) =
    (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y)))"
    by (auto simp add: pair_measure_count_space lebesgue_integral_count_space_finite sum.If_cases split_beta'
             intro!: sum.cong)
qed (insert X Y XY, auto simp: simple_distributed_def)

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes Px: "simple_distributed M X Px" and Py: "simple_distributed M Y Py"
  assumes Pxy: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
  assumes ae: "\<forall>x\<in>space M. Pxy (X x, Y x) = Px (X x) * Py (Y x)"
  shows mutual_information_eq_0_simple: "\<I>(X ; Y) = 0"
proof (subst mutual_information_simple_distributed[OF Px Py Pxy])
  have "(\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y))) =
    (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. 0)"
    by (intro sum.cong) (auto simp: ae)
  then show "(\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M.
    Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y))) = 0" by simp
qed

subsection \<open>Entropy\<close>

definition (in prob_space) entropy :: "real \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "entropy b S X = - KL_divergence b S (distr M S X)"

abbreviation (in information_space)
  entropy_Pow ("\<H>'(_')") where
  "\<H>(X) \<equiv> entropy b (count_space (X`space M)) X"

lemma (in prob_space) distributed_RN_deriv:
  assumes X: "distributed M S X Px"
  shows "AE x in S. RN_deriv S (density S Px) x = Px x"
proof -
  note D = distributed_measurable[OF X] distributed_borel_measurable[OF X]
  interpret X: prob_space "distr M S X"
    using D(1) by (rule prob_space_distr)

  have sf: "sigma_finite_measure (distr M S X)" by standard
  show ?thesis
    using D
    apply (subst eq_commute)
    apply (intro RN_deriv_unique_sigma_finite)
    apply (auto simp: distributed_distr_eq_density[symmetric, OF X] sf)
    done
qed

lemma (in information_space)
  fixes X :: "'a \<Rightarrow> 'b"
  assumes X[measurable]: "distributed M MX X f" and nn: "\<And>x. x \<in> space MX \<Longrightarrow> 0 \<le> f x"
  shows entropy_distr: "entropy b MX X = - (\<integral>x. f x * log b (f x) \<partial>MX)" (is ?eq)
proof -
  note D = distributed_measurable[OF X] distributed_borel_measurable[OF X]
  note ae = distributed_RN_deriv[OF X]
  note distributed_real_measurable[OF nn X, measurable]

  have ae_eq: "AE x in distr M MX X. log b (enn2real (RN_deriv MX (distr M MX X) x)) =
    log b (f x)"
    unfolding distributed_distr_eq_density[OF X]
    apply (subst AE_density)
    using D apply simp
    using ae apply eventually_elim
    apply auto
    done

  have int_eq: "(\<integral> x. f x * log b (f x) \<partial>MX) = (\<integral> x. log b (f x) \<partial>distr M MX X)"
    unfolding distributed_distr_eq_density[OF X]
    using D
    by (subst integral_density) (auto simp: nn)

  show ?eq
    unfolding entropy_def KL_divergence_def entropy_density_def comp_def int_eq neg_equal_iff_equal
    using ae_eq by (intro integral_cong_AE) (auto simp: nn)
qed

lemma (in information_space) entropy_le:
  fixes Px :: "'b \<Rightarrow> real" and MX :: "'b measure"
  assumes X[measurable]: "distributed M MX X Px" and Px_nn[simp]: "\<And>x. x \<in> space MX \<Longrightarrow> 0 \<le> Px x"
  and fin: "emeasure MX {x \<in> space MX. Px x \<noteq> 0} \<noteq> top"
  and int: "integrable MX (\<lambda>x. - Px x * log b (Px x))"
  shows "entropy b MX X \<le> log b (measure MX {x \<in> space MX. Px x \<noteq> 0})"
proof -
  note Px = distributed_borel_measurable[OF X]
  interpret X: prob_space "distr M MX X"
    using distributed_measurable[OF X] by (rule prob_space_distr)

  have " - log b (measure MX {x \<in> space MX. Px x \<noteq> 0}) =
    - log b (\<integral> x. indicator {x \<in> space MX. Px x \<noteq> 0} x \<partial>MX)"
    using Px Px_nn fin by (auto simp: measure_def)
  also have "- log b (\<integral> x. indicator {x \<in> space MX. Px x \<noteq> 0} x \<partial>MX) = - log b (\<integral> x. 1 / Px x \<partial>distr M MX X)"
  proof -
    have "integral\<^sup>L MX (indicator {x \<in> space MX. Px x \<noteq> 0}) = LINT x|MX. Px x *\<^sub>R (1 / Px x)"
      by (rule Bochner_Integration.integral_cong) auto
    also have "... = LINT x|density MX (\<lambda>x. ennreal (Px x)). 1 / Px x"
      by (rule integral_density [symmetric]) (use Px Px_nn in auto)
    finally show ?thesis
      unfolding distributed_distr_eq_density[OF X] by simp
  qed
  also have "\<dots> \<le> (\<integral> x. - log b (1 / Px x) \<partial>distr M MX X)"
  proof (rule X.jensens_inequality[of "\<lambda>x. 1 / Px x" "{0<..}" 0 1 "\<lambda>x. - log b x"])
    show "AE x in distr M MX X. 1 / Px x \<in> {0<..}"
      unfolding distributed_distr_eq_density[OF X]
      using Px by (auto simp: AE_density)
    have [simp]: "\<And>x. x \<in> space MX \<Longrightarrow> ennreal (if Px x = 0 then 0 else 1) = indicator {x \<in> space MX. Px x \<noteq> 0} x"
      by (auto simp: one_ennreal_def)
    have "(\<integral>\<^sup>+ x. ennreal (- (if Px x = 0 then 0 else 1)) \<partial>MX) = (\<integral>\<^sup>+ x. 0 \<partial>MX)"
      by (intro nn_integral_cong) (auto simp: ennreal_neg)
    then show "integrable (distr M MX X) (\<lambda>x. 1 / Px x)"
      unfolding distributed_distr_eq_density[OF X] using Px
      by (auto simp: nn_integral_density real_integrable_def fin ennreal_neg ennreal_mult[symmetric]
              cong: nn_integral_cong)
    have "integrable MX (\<lambda>x. Px x * log b (1 / Px x)) =
      integrable MX (\<lambda>x. - Px x * log b (Px x))"
      using Px
      by (intro integrable_cong_AE) (auto simp: log_divide_eq less_le)
    then show "integrable (distr M MX X) (\<lambda>x. - log b (1 / Px x))"
      unfolding distributed_distr_eq_density[OF X]
      using Px int
      by (subst integrable_real_density) auto
  qed (auto simp: minus_log_convex[OF b_gt_1])
  also have "\<dots> = (\<integral> x. log b (Px x) \<partial>distr M MX X)"
    unfolding distributed_distr_eq_density[OF X] using Px
    by (intro integral_cong_AE) (auto simp: AE_density log_divide_eq)
  also have "\<dots> = - entropy b MX X"
    unfolding distributed_distr_eq_density[OF X] using Px
    by (subst entropy_distr[OF X]) (auto simp: integral_density)
  finally show ?thesis
    by simp
qed

lemma (in information_space) entropy_le_space:
  fixes Px :: "'b \<Rightarrow> real" and MX :: "'b measure"
  assumes X: "distributed M MX X Px" and Px_nn[simp]: "\<And>x. x \<in> space MX \<Longrightarrow> 0 \<le> Px x"
  and fin: "finite_measure MX"
  and int: "integrable MX (\<lambda>x. - Px x * log b (Px x))"
  shows "entropy b MX X \<le> log b (measure MX (space MX))"
proof -
  note Px = distributed_borel_measurable[OF X]
  interpret finite_measure MX by fact
  have "entropy b MX X \<le> log b (measure MX {x \<in> space MX. Px x \<noteq> 0})"
    using int X by (intro entropy_le) auto
  also have "\<dots> \<le> log b (measure MX (space MX))"
    using Px distributed_imp_emeasure_nonzero[OF X]
    by (intro log_le)
       (auto intro!: finite_measure_mono b_gt_1 less_le[THEN iffD2]
             simp: emeasure_eq_measure cong: conj_cong)
  finally show ?thesis .
qed

lemma (in information_space) entropy_uniform:
  assumes X: "distributed M MX X (\<lambda>x. indicator A x / measure MX A)" (is "distributed _ _ _ ?f")
  shows "entropy b MX X = log b (measure MX A)"
proof (subst entropy_distr[OF X])
  have [simp]: "emeasure MX A \<noteq> \<infinity>"
    using uniform_distributed_params[OF X] by (auto simp add: measure_def)
  have eq: "(\<integral> x. indicator A x / measure MX A * log b (indicator A x / measure MX A) \<partial>MX) =
    (\<integral> x. (- log b (measure MX A) / measure MX A) * indicator A x \<partial>MX)"
    using uniform_distributed_params[OF X]
    by (intro Bochner_Integration.integral_cong) (auto split: split_indicator simp: log_divide_eq zero_less_measure_iff)
  show "- (\<integral> x. indicator A x / measure MX A * log b (indicator A x / measure MX A) \<partial>MX) =
    log b (measure MX A)"
    unfolding eq using uniform_distributed_params[OF X]
    by (subst Bochner_Integration.integral_mult_right) (auto simp: measure_def less_top[symmetric] intro!: integrable_real_indicator)
qed simp

lemma (in information_space) entropy_simple_distributed:
  "simple_distributed M X f \<Longrightarrow> \<H>(X) = - (\<Sum>x\<in>X`space M. f x * log b (f x))"
  by (subst entropy_distr[OF simple_distributed])
     (auto simp add: lebesgue_integral_count_space_finite)

lemma (in information_space) entropy_le_card_not_0:
  assumes X: "simple_distributed M X f"
  shows "\<H>(X) \<le> log b (card (X ` space M \<inter> {x. f x \<noteq> 0}))"
proof -
  let ?X = "count_space (X`space M)"
  have "\<H>(X) \<le> log b (measure ?X {x \<in> space ?X. f x \<noteq> 0})"
    by (rule entropy_le[OF simple_distributed[OF X]])
       (insert X, auto simp: simple_distributed_finite[OF X] subset_eq integrable_count_space emeasure_count_space)
  also have "measure ?X {x \<in> space ?X. f x \<noteq> 0} = card (X ` space M \<inter> {x. f x \<noteq> 0})"
    by (simp_all add: simple_distributed_finite[OF X] subset_eq emeasure_count_space measure_def Int_def)
  finally show ?thesis .
qed

lemma (in information_space) entropy_le_card:
  assumes X: "simple_distributed M X f"
  shows "\<H>(X) \<le> log b (real (card (X ` space M)))"
proof -
  let ?X = "count_space (X`space M)"
  have "\<H>(X) \<le> log b (measure ?X (space ?X))"
    by (rule entropy_le_space[OF simple_distributed[OF X]])
       (insert X, auto simp: simple_distributed_finite[OF X] subset_eq integrable_count_space emeasure_count_space finite_measure_count_space)
  also have "measure ?X (space ?X) = card (X ` space M)"
    by (simp_all add: simple_distributed_finite[OF X] subset_eq emeasure_count_space measure_def)
  finally show ?thesis .
qed

subsection \<open>Conditional Mutual Information\<close>

definition (in prob_space)
  "conditional_mutual_information b MX MY MZ X Y Z \<equiv>
    mutual_information b MX (MY \<Otimes>\<^sub>M MZ) X (\<lambda>x. (Y x, Z x)) -
    mutual_information b MX MZ X Z"

abbreviation (in information_space)
  conditional_mutual_information_Pow ("\<I>'( _ ; _ | _ ')") where
  "\<I>(X ; Y | Z) \<equiv> conditional_mutual_information b
    (count_space (X ` space M)) (count_space (Y ` space M)) (count_space (Z ` space M)) X Y Z"

lemma (in information_space)
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T" and P: "sigma_finite_measure P"
  assumes Px[measurable]: "distributed M S X Px"
    and Px_nn[simp]: "\<And>x. x \<in> space S \<Longrightarrow> 0 \<le> Px x"
  assumes Pz[measurable]: "distributed M P Z Pz"
    and Pz_nn[simp]: "\<And>z. z \<in> space P \<Longrightarrow> 0 \<le> Pz z"
  assumes Pyz[measurable]: "distributed M (T \<Otimes>\<^sub>M P) (\<lambda>x. (Y x, Z x)) Pyz"
    and Pyz_nn[simp]: "\<And>y z. y \<in> space T \<Longrightarrow> z \<in> space P \<Longrightarrow> 0 \<le> Pyz (y, z)"
  assumes Pxz[measurable]: "distributed M (S \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Z x)) Pxz"
    and Pxz_nn[simp]: "\<And>x z. x \<in> space S \<Longrightarrow> z \<in> space P \<Longrightarrow> 0 \<le> Pxz (x, z)"
  assumes Pxyz[measurable]: "distributed M (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Y x, Z x)) Pxyz"
    and Pxyz_nn[simp]: "\<And>x y z. x \<in> space S \<Longrightarrow> y \<in> space T \<Longrightarrow> z \<in> space P \<Longrightarrow> 0 \<le> Pxyz (x, y, z)"
  assumes I1: "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Px x * Pyz (y, z))))"
  assumes I2: "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxz (x, z) / (Px x * Pz z)))"
  shows conditional_mutual_information_generic_eq: "conditional_mutual_information b S T P X Y Z
    = (\<integral>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))" (is "?eq")
    and conditional_mutual_information_generic_nonneg: "0 \<le> conditional_mutual_information b S T P X Y Z" (is "?nonneg")
proof -
  have [measurable]: "Px \<in> S \<rightarrow>\<^sub>M borel"
    using Px Px_nn by (intro distributed_real_measurable)
  have [measurable]: "Pz \<in> P \<rightarrow>\<^sub>M borel"
    using Pz Pz_nn by (intro distributed_real_measurable)
  have measurable_Pyz[measurable]: "Pyz \<in> (T \<Otimes>\<^sub>M P) \<rightarrow>\<^sub>M borel"
    using Pyz Pyz_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)
  have measurable_Pxz[measurable]: "Pxz \<in> (S \<Otimes>\<^sub>M P) \<rightarrow>\<^sub>M borel"
    using Pxz Pxz_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)
  have measurable_Pxyz[measurable]: "Pxyz \<in> (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) \<rightarrow>\<^sub>M borel"
    using Pxyz Pxyz_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)

  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret P: sigma_finite_measure P by fact
  interpret TP: pair_sigma_finite T P ..
  interpret SP: pair_sigma_finite S P ..
  interpret ST: pair_sigma_finite S T ..
  interpret SPT: pair_sigma_finite "S \<Otimes>\<^sub>M P" T ..
  interpret STP: pair_sigma_finite S "T \<Otimes>\<^sub>M P" ..
  interpret TPS: pair_sigma_finite "T \<Otimes>\<^sub>M P" S ..
  have TP: "sigma_finite_measure (T \<Otimes>\<^sub>M P)" ..
  have SP: "sigma_finite_measure (S \<Otimes>\<^sub>M P)" ..
  have YZ: "random_variable (T \<Otimes>\<^sub>M P) (\<lambda>x. (Y x, Z x))"
    using Pyz by (simp add: distributed_measurable)

  from Pxz Pxyz have distr_eq: "distr M (S \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Z x)) =
    distr (distr M (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Y x, Z x))) (S \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). (x, z))"
    by (simp add: comp_def distr_distr)

  have "mutual_information b S P X Z =
    (\<integral>x. Pxz x * log b (Pxz x / (Px (fst x) * Pz (snd x))) \<partial>(S \<Otimes>\<^sub>M P))"
    by (rule mutual_information_distr[OF S P Px Px_nn Pz Pz_nn Pxz Pxz_nn])
  also have "\<dots> = (\<integral>(x,y,z). Pxyz (x,y,z) * log b (Pxz (x,z) / (Px x * Pz z)) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))"
    using b_gt_1 Pxz Px Pz
    by (subst distributed_transform_integral[OF Pxyz _ Pxz _, where T="\<lambda>(x, y, z). (x, z)"])
       (auto simp: split_beta' space_pair_measure)
  finally have mi_eq:
    "mutual_information b S P X Z = (\<integral>(x,y,z). Pxyz (x,y,z) * log b (Pxz (x,z) / (Px x * Pz z)) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))" .

  have ae1: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Px (fst x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of fst, OF _ Pxyz Px]) (auto simp: space_pair_measure)
  moreover have ae2: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pz (snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of "\<lambda>x. snd (snd x)", OF _ Pxyz Pz]) (auto simp: space_pair_measure)
  moreover have ae3: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pxz (fst x, snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of "\<lambda>x. (fst x, snd (snd x))", OF _ Pxyz Pxz]) (auto simp: space_pair_measure)
  moreover have ae4: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pyz (snd x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of snd, OF _ Pxyz Pyz]) (auto simp: space_pair_measure)
  ultimately have ae: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P.
    Pxyz x * log b (Pxyz x / (Px (fst x) * Pyz (snd x))) -
    Pxyz x * log b (Pxz (fst x, snd (snd x)) / (Px (fst x) * Pz (snd (snd x)))) =
    Pxyz x * log b (Pxyz x * Pz (snd (snd x)) / (Pxz (fst x, snd (snd x)) * Pyz (snd x))) "
    using AE_space
  proof eventually_elim
    case (elim x)
    show ?case
    proof cases
      assume "Pxyz x \<noteq> 0"
      with elim have "0 < Px (fst x)" "0 < Pz (snd (snd x))" "0 < Pxz (fst x, snd (snd x))"
        "0 < Pyz (snd x)" "0 < Pxyz x"
        by (auto simp: space_pair_measure less_le)
      then show ?thesis
        using b_gt_1 by (simp add: log_simps less_imp_le field_simps)
    qed simp
  qed
  with I1 I2 show ?eq
    unfolding conditional_mutual_information_def
    apply (subst mi_eq)
    apply (subst mutual_information_distr[OF S TP Px Px_nn Pyz _ Pxyz])
    apply (auto simp: space_pair_measure)
    apply (subst Bochner_Integration.integral_diff[symmetric])
    apply (auto intro!: integral_cong_AE simp: split_beta' simp del: Bochner_Integration.integral_diff)
    done

  let ?P = "density (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) Pxyz"
  interpret P: prob_space ?P
    unfolding distributed_distr_eq_density[OF Pxyz, symmetric]
    by (rule prob_space_distr) simp

  let ?Q = "density (T \<Otimes>\<^sub>M P) Pyz"
  interpret Q: prob_space ?Q
    unfolding distributed_distr_eq_density[OF Pyz, symmetric]
    by (rule prob_space_distr) simp

  let ?f = "\<lambda>(x, y, z). Pxz (x, z) * (Pyz (y, z) / Pz z) / Pxyz (x, y, z)"

  from subdensity_real[of snd, OF _ Pyz Pz _ AE_I2 AE_I2]
  have aeX1: "AE x in T \<Otimes>\<^sub>M P. Pz (snd x) = 0 \<longrightarrow> Pyz x = 0"
    by (auto simp: comp_def space_pair_measure)
  have aeX2: "AE x in T \<Otimes>\<^sub>M P. 0 \<le> Pz (snd x)"
    using Pz by (intro TP.AE_pair_measure) (auto simp: comp_def)

  have aeX3: "AE y in T \<Otimes>\<^sub>M P. (\<integral>\<^sup>+ x. ennreal (Pxz (x, snd y)) \<partial>S) = ennreal (Pz (snd y))"
    using Pz distributed_marginal_eq_joint2[OF P S Pz Pxz]
    by (intro TP.AE_pair_measure) auto

  have "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<le> (\<integral>\<^sup>+ (x, y, z). Pxz (x, z) * (Pyz (y, z) / Pz z) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))"
    by (subst nn_integral_density)
       (auto intro!: nn_integral_mono simp: space_pair_measure ennreal_mult[symmetric])
  also have "\<dots> = (\<integral>\<^sup>+(y, z). (\<integral>\<^sup>+ x. ennreal (Pxz (x, z)) * ennreal (Pyz (y, z) / Pz z) \<partial>S) \<partial>(T \<Otimes>\<^sub>M P))"
    by (subst STP.nn_integral_snd[symmetric])
       (auto simp add: split_beta' ennreal_mult[symmetric] space_pair_measure intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (Pyz x) * 1 \<partial>T \<Otimes>\<^sub>M P)"
    apply (rule nn_integral_cong_AE)
    using aeX1 aeX2 aeX3 AE_space
    apply eventually_elim
  proof (case_tac x, simp add: space_pair_measure)
    fix a b assume "Pz b = 0 \<longrightarrow> Pyz (a, b) = 0" "a \<in> space T \<and> b \<in> space P"
      "(\<integral>\<^sup>+ x. ennreal (Pxz (x, b)) \<partial>S) = ennreal (Pz b)"
    then show "(\<integral>\<^sup>+ x. ennreal (Pxz (x, b)) * ennreal (Pyz (a, b) / Pz b) \<partial>S) = ennreal (Pyz (a, b))"
      by (subst nn_integral_multc) (auto split: prod.split simp: ennreal_mult[symmetric])
  qed
  also have "\<dots> = 1"
    using Q.emeasure_space_1 distributed_distr_eq_density[OF Pyz]
    by (subst nn_integral_density[symmetric]) auto
  finally have le1: "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<le> 1" .
  also have "\<dots> < \<infinity>" by simp
  finally have fin: "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<noteq> \<infinity>" by simp

  have pos: "(\<integral>\<^sup>+x. ?f x \<partial>?P) \<noteq> 0"
    apply (subst nn_integral_density)
    apply (simp_all add: split_beta')
  proof
    let ?g = "\<lambda>x. ennreal (Pxyz x) * (Pxz (fst x, snd (snd x)) * Pyz (snd x) / (Pz (snd (snd x)) * Pxyz x))"
    assume "(\<integral>\<^sup>+x. ?g x \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P)) = 0"
    then have "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. ?g x = 0"
      by (intro nn_integral_0_iff_AE[THEN iffD1]) auto
    then have "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pxyz x = 0"
      using ae1 ae2 ae3 ae4 AE_space
      by eventually_elim (auto split: if_split_asm simp: mult_le_0_iff divide_le_0_iff space_pair_measure)
    then have "(\<integral>\<^sup>+ x. ennreal (Pxyz x) \<partial>S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) = 0"
      by (subst nn_integral_cong_AE[of _ "\<lambda>x. 0"]) auto
    with P.emeasure_space_1 show False
      by (subst (asm) emeasure_density) (auto cong: nn_integral_cong)
  qed

  have neg: "(\<integral>\<^sup>+ x. - ?f x \<partial>?P) = 0"
    apply (rule nn_integral_0_iff_AE[THEN iffD2])
    apply simp
    apply (subst AE_density)
    apply (auto simp: space_pair_measure ennreal_neg)
    done

  have I3: "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))))"
    apply (rule integrable_cong_AE[THEN iffD1, OF _ _ _ Bochner_Integration.integrable_diff[OF I1 I2]])
    using ae
    apply (auto simp: split_beta')
    done

  have "- log b 1 \<le> - log b (integral\<^sup>L ?P ?f)"
  proof (intro le_imp_neg_le log_le[OF b_gt_1])
    have If: "integrable ?P ?f"
      unfolding real_integrable_def
    proof (intro conjI)
      from neg show "(\<integral>\<^sup>+ x. - ?f x \<partial>?P) \<noteq> \<infinity>"
        by simp
      from fin show "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<noteq> \<infinity>"
        by simp
    qed simp
    then have "(\<integral>\<^sup>+ x. ?f x \<partial>?P) = (\<integral>x. ?f x \<partial>?P)"
      apply (rule nn_integral_eq_integral)
      apply (subst AE_density)
      apply simp
      apply (auto simp: space_pair_measure ennreal_neg)
      done
    with pos le1
    show "0 < (\<integral>x. ?f x \<partial>?P)" "(\<integral>x. ?f x \<partial>?P) \<le> 1"
      by (simp_all add: one_ennreal.rep_eq zero_less_iff_neq_zero[symmetric])
  qed
  also have "- log b (integral\<^sup>L ?P ?f) \<le> (\<integral> x. - log b (?f x) \<partial>?P)"
  proof (rule P.jensens_inequality[where a=0 and b=1 and I="{0<..}"])
    show "AE x in ?P. ?f x \<in> {0<..}"
      unfolding AE_density[OF distributed_borel_measurable[OF Pxyz]]
      using ae1 ae2 ae3 ae4 AE_space
      by eventually_elim (auto simp: space_pair_measure less_le)
    show "integrable ?P ?f"
      unfolding real_integrable_def
      using fin neg by (auto simp: split_beta')
    show "integrable ?P (\<lambda>x. - log b (?f x))"
      apply (subst integrable_real_density)
      apply simp
      apply (auto simp: space_pair_measure) []
      apply simp
      apply (rule integrable_cong_AE[THEN iffD1, OF _ _ _ I3])
      apply simp
      apply simp
      using ae1 ae2 ae3 ae4 AE_space
      apply eventually_elim
      apply (auto simp: log_divide_eq log_mult_eq zero_le_mult_iff zero_less_mult_iff zero_less_divide_iff field_simps
        less_le space_pair_measure)
      done
  qed (auto simp: b_gt_1 minus_log_convex)
  also have "\<dots> = conditional_mutual_information b S T P X Y Z"
    unfolding \<open>?eq\<close>
    apply (subst integral_real_density)
    apply simp
    apply (auto simp: space_pair_measure) []
    apply simp
    apply (intro integral_cong_AE)
    using ae1 ae2 ae3 ae4
    apply (auto simp: log_divide_eq zero_less_mult_iff zero_less_divide_iff field_simps
      space_pair_measure less_le)
    done
  finally show ?nonneg
    by simp
qed

lemma (in information_space)
  fixes Px :: "_ \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T" and P: "sigma_finite_measure P"
  assumes Fx: "finite_entropy S X Px"
  assumes Fz: "finite_entropy P Z Pz"
  assumes Fyz: "finite_entropy (T \<Otimes>\<^sub>M P) (\<lambda>x. (Y x, Z x)) Pyz"
  assumes Fxz: "finite_entropy (S \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Z x)) Pxz"
  assumes Fxyz: "finite_entropy (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Y x, Z x)) Pxyz"
  shows conditional_mutual_information_generic_eq': "conditional_mutual_information b S T P X Y Z
    = (\<integral>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))" (is "?eq")
    and conditional_mutual_information_generic_nonneg': "0 \<le> conditional_mutual_information b S T P X Y Z" (is "?nonneg")
proof -
  note Px = Fx[THEN finite_entropy_distributed, measurable]
  note Pz = Fz[THEN finite_entropy_distributed, measurable]
  note Pyz = Fyz[THEN finite_entropy_distributed, measurable]
  note Pxz = Fxz[THEN finite_entropy_distributed, measurable]
  note Pxyz = Fxyz[THEN finite_entropy_distributed, measurable]

  note Px_nn = Fx[THEN finite_entropy_nn]
  note Pz_nn = Fz[THEN finite_entropy_nn]
  note Pyz_nn = Fyz[THEN finite_entropy_nn]
  note Pxz_nn = Fxz[THEN finite_entropy_nn]
  note Pxyz_nn = Fxyz[THEN finite_entropy_nn]

  note Px' = Fx[THEN finite_entropy_measurable, measurable]
  note Pz' = Fz[THEN finite_entropy_measurable, measurable]
  note Pyz' = Fyz[THEN finite_entropy_measurable, measurable]
  note Pxz' = Fxz[THEN finite_entropy_measurable, measurable]
  note Pxyz' = Fxyz[THEN finite_entropy_measurable, measurable]

  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret P: sigma_finite_measure P by fact
  interpret TP: pair_sigma_finite T P ..
  interpret SP: pair_sigma_finite S P ..
  interpret ST: pair_sigma_finite S T ..
  interpret SPT: pair_sigma_finite "S \<Otimes>\<^sub>M P" T ..
  interpret STP: pair_sigma_finite S "T \<Otimes>\<^sub>M P" ..
  interpret TPS: pair_sigma_finite "T \<Otimes>\<^sub>M P" S ..
  have TP: "sigma_finite_measure (T \<Otimes>\<^sub>M P)" ..
  have SP: "sigma_finite_measure (S \<Otimes>\<^sub>M P)" ..

  from Pxz Pxyz have distr_eq: "distr M (S \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Z x)) =
    distr (distr M (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>x. (X x, Y x, Z x))) (S \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). (x, z))"
    by (simp add: distr_distr comp_def)

  have "mutual_information b S P X Z =
    (\<integral>x. Pxz x * log b (Pxz x / (Px (fst x) * Pz (snd x))) \<partial>(S \<Otimes>\<^sub>M P))"
    using Px Px_nn Pz Pz_nn Pxz Pxz_nn
    by (rule mutual_information_distr[OF S P]) (auto simp: space_pair_measure)
  also have "\<dots> = (\<integral>(x,y,z). Pxyz (x,y,z) * log b (Pxz (x,z) / (Px x * Pz z)) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))"
    using b_gt_1 Pxz Pxz_nn Pxyz Pxyz_nn
    by (subst distributed_transform_integral[OF Pxyz _ Pxz, where T="\<lambda>(x, y, z). (x, z)"])
       (auto simp: split_beta')
  finally have mi_eq:
    "mutual_information b S P X Z = (\<integral>(x,y,z). Pxyz (x,y,z) * log b (Pxz (x,z) / (Px x * Pz z)) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))" .

  have ae1: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Px (fst x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_finite_entropy[of fst, OF _ Fxyz Fx]) auto
  moreover have ae2: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pz (snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_finite_entropy[of "\<lambda>x. snd (snd x)", OF _ Fxyz Fz]) auto
  moreover have ae3: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pxz (fst x, snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_finite_entropy[of "\<lambda>x. (fst x, snd (snd x))", OF _ Fxyz Fxz]) auto
  moreover have ae4: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pyz (snd x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_finite_entropy[of snd, OF _ Fxyz Fyz]) auto
  ultimately have ae: "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P.
    Pxyz x * log b (Pxyz x / (Px (fst x) * Pyz (snd x))) -
    Pxyz x * log b (Pxz (fst x, snd (snd x)) / (Px (fst x) * Pz (snd (snd x)))) =
    Pxyz x * log b (Pxyz x * Pz (snd (snd x)) / (Pxz (fst x, snd (snd x)) * Pyz (snd x))) "
    using AE_space
  proof eventually_elim
    case (elim x)
    show ?case
    proof cases
      assume "Pxyz x \<noteq> 0"
      with elim have "0 < Px (fst x)" "0 < Pz (snd (snd x))" "0 < Pxz (fst x, snd (snd x))"
        "0 < Pyz (snd x)" "0 < Pxyz x"
        using Px_nn Pz_nn Pxz_nn Pyz_nn Pxyz_nn
        by (auto simp: space_pair_measure less_le)
      then show ?thesis
        using b_gt_1 by (simp add: log_simps less_imp_le field_simps)
    qed simp
  qed

  have "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P)
    (\<lambda>x. Pxyz x * log b (Pxyz x) - Pxyz x * log b (Px (fst x)) - Pxyz x * log b (Pyz (snd x)))"
    using finite_entropy_integrable[OF Fxyz]
    using finite_entropy_integrable_transform[OF Fx Pxyz Pxyz_nn, of fst]
    using finite_entropy_integrable_transform[OF Fyz Pxyz Pxyz_nn, of snd]
    by simp
  moreover have "(\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Px x * Pyz (y, z)))) \<in> borel_measurable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P)"
    using Pxyz Px Pyz by simp
  ultimately have I1: "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Px x * Pyz (y, z))))"
    apply (rule integrable_cong_AE_imp)
    using ae1 ae4 AE_space
    by eventually_elim
       (insert Px_nn Pyz_nn Pxyz_nn,
        auto simp: log_divide_eq log_mult_eq field_simps zero_less_mult_iff space_pair_measure less_le)

  have "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P)
    (\<lambda>x. Pxyz x * log b (Pxz (fst x, snd (snd x))) - Pxyz x * log b (Px (fst x)) - Pxyz x * log b (Pz (snd (snd x))))"
    using finite_entropy_integrable_transform[OF Fxz Pxyz Pxyz_nn, of "\<lambda>x. (fst x, snd (snd x))"]
    using finite_entropy_integrable_transform[OF Fx Pxyz Pxyz_nn, of fst]
    using finite_entropy_integrable_transform[OF Fz Pxyz Pxyz_nn, of "snd \<circ> snd"]
    by simp
  moreover have "(\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxz (x, z) / (Px x * Pz z))) \<in> borel_measurable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P)"
    using Pxyz Px Pz
    by auto
  ultimately have I2: "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxz (x, z) / (Px x * Pz z)))"
    apply (rule integrable_cong_AE_imp)
    using ae1 ae2 ae3 ae4 AE_space
    by eventually_elim
       (insert Px_nn Pz_nn Pxz_nn Pyz_nn Pxyz_nn,
         auto simp: log_divide_eq log_mult_eq field_simps zero_less_mult_iff less_le space_pair_measure)

  from ae I1 I2 show ?eq
    unfolding conditional_mutual_information_def
    apply (subst mi_eq)
    apply (subst mutual_information_distr[OF S TP Px Px_nn Pyz Pyz_nn Pxyz Pxyz_nn])
    apply simp
    apply simp
    apply (simp add: space_pair_measure)
    apply (subst Bochner_Integration.integral_diff[symmetric])
    apply (auto intro!: integral_cong_AE simp: split_beta' simp del: Bochner_Integration.integral_diff)
    done

  let ?P = "density (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) Pxyz"
  interpret P: prob_space ?P
    unfolding distributed_distr_eq_density[OF Pxyz, symmetric] by (rule prob_space_distr) simp

  let ?Q = "density (T \<Otimes>\<^sub>M P) Pyz"
  interpret Q: prob_space ?Q
    unfolding distributed_distr_eq_density[OF Pyz, symmetric] by (rule prob_space_distr) simp

  let ?f = "\<lambda>(x, y, z). Pxz (x, z) * (Pyz (y, z) / Pz z) / Pxyz (x, y, z)"

  from subdensity_finite_entropy[of snd, OF _ Fyz Fz]
  have aeX1: "AE x in T \<Otimes>\<^sub>M P. Pz (snd x) = 0 \<longrightarrow> Pyz x = 0" by (auto simp: comp_def)
  have aeX2: "AE x in T \<Otimes>\<^sub>M P. 0 \<le> Pz (snd x)"
    using Pz by (intro TP.AE_pair_measure) (auto intro: Pz_nn)

  have aeX3: "AE y in T \<Otimes>\<^sub>M P. (\<integral>\<^sup>+ x. ennreal (Pxz (x, snd y)) \<partial>S) = ennreal (Pz (snd y))"
    using Pz distributed_marginal_eq_joint2[OF P S Pz Pxz]
    by (intro TP.AE_pair_measure) (auto )
  have "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<le> (\<integral>\<^sup>+ (x, y, z). Pxz (x, z) * (Pyz (y, z) / Pz z) \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P))"
    using Px_nn Pz_nn Pxz_nn Pyz_nn Pxyz_nn
    by (subst nn_integral_density)
       (auto intro!: nn_integral_mono simp: space_pair_measure ennreal_mult[symmetric])
  also have "\<dots> = (\<integral>\<^sup>+(y, z). \<integral>\<^sup>+ x. ennreal (Pxz (x, z)) * ennreal (Pyz (y, z) / Pz z) \<partial>S \<partial>T \<Otimes>\<^sub>M P)"
    using Px_nn Pz_nn Pxz_nn Pyz_nn Pxyz_nn
    by (subst STP.nn_integral_snd[symmetric])
       (auto simp add: split_beta' ennreal_mult[symmetric] space_pair_measure intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (Pyz x) * 1 \<partial>T \<Otimes>\<^sub>M P)"
    apply (rule nn_integral_cong_AE)
    using aeX1 aeX2 aeX3 AE_space
    apply eventually_elim
  proof (case_tac x, simp add: space_pair_measure)
    fix a b assume "Pz b = 0 \<longrightarrow> Pyz (a, b) = 0" "0 \<le> Pz b" "a \<in> space T \<and> b \<in> space P"
      "(\<integral>\<^sup>+ x. ennreal (Pxz (x, b)) \<partial>S) = ennreal (Pz b)"
    then show "(\<integral>\<^sup>+ x. ennreal (Pxz (x, b)) * ennreal (Pyz (a, b) / Pz b) \<partial>S) = ennreal (Pyz (a, b))"
      using Pyz_nn[of "(a,b)"]
      by (subst nn_integral_multc) (auto simp: space_pair_measure ennreal_mult[symmetric])
  qed
  also have "\<dots> = 1"
    using Q.emeasure_space_1 Pyz_nn distributed_distr_eq_density[OF Pyz]
    by (subst nn_integral_density[symmetric]) auto
  finally have le1: "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<le> 1" .
  also have "\<dots> < \<infinity>" by simp
  finally have fin: "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<noteq> \<infinity>" by simp

  have "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<noteq> 0"
    using Pxyz_nn
    apply (subst nn_integral_density)
    apply (simp_all add: split_beta'  ennreal_mult'[symmetric] cong: nn_integral_cong)
  proof
    let ?g = "\<lambda>x. ennreal (if Pxyz x = 0 then 0 else Pxz (fst x, snd (snd x)) * Pyz (snd x) / Pz (snd (snd x)))"
    assume "(\<integral>\<^sup>+ x. ?g x \<partial>(S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P)) = 0"
    then have "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. ?g x = 0"
      by (intro nn_integral_0_iff_AE[THEN iffD1]) auto
    then have "AE x in S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P. Pxyz x = 0"
      using ae1 ae2 ae3 ae4 AE_space
      by eventually_elim
         (insert Px_nn Pz_nn Pxz_nn Pyz_nn,
           auto split: if_split_asm simp: mult_le_0_iff divide_le_0_iff space_pair_measure)
    then have "(\<integral>\<^sup>+ x. ennreal (Pxyz x) \<partial>S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) = 0"
      by (subst nn_integral_cong_AE[of _ "\<lambda>x. 0"]) auto
    with P.emeasure_space_1 show False
      by (subst (asm) emeasure_density) (auto cong: nn_integral_cong)
  qed
  then have pos: "0 < (\<integral>\<^sup>+ x. ?f x \<partial>?P)"
    by (simp add: zero_less_iff_neq_zero)

  have neg: "(\<integral>\<^sup>+ x. - ?f x \<partial>?P) = 0"
    using Pz_nn Pxz_nn Pyz_nn Pxyz_nn
    by (intro nn_integral_0_iff_AE[THEN iffD2])
       (auto simp: split_beta' AE_density space_pair_measure intro!: AE_I2 ennreal_neg)

  have I3: "integrable (S \<Otimes>\<^sub>M T \<Otimes>\<^sub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))))"
    apply (rule integrable_cong_AE[THEN iffD1, OF _ _ _ Bochner_Integration.integrable_diff[OF I1 I2]])
    using ae
    apply (auto simp: split_beta')
    done

  have "- log b 1 \<le> - log b (integral\<^sup>L ?P ?f)"
  proof (intro le_imp_neg_le log_le[OF b_gt_1])
    have If: "integrable ?P ?f"
      unfolding real_integrable_def
    proof (intro conjI)
      from neg show "(\<integral>\<^sup>+ x. - ?f x \<partial>?P) \<noteq> \<infinity>"
        by simp
      from fin show "(\<integral>\<^sup>+ x. ?f x \<partial>?P) \<noteq> \<infinity>"
        by simp
    qed simp
    then have "(\<integral>\<^sup>+ x. ?f x \<partial>?P) = (\<integral>x. ?f x \<partial>?P)"
      using Pz_nn Pxz_nn Pyz_nn Pxyz_nn
      by (intro nn_integral_eq_integral)
         (auto simp: AE_density space_pair_measure)
    with pos le1
    show "0 < (\<integral>x. ?f x \<partial>?P)" "(\<integral>x. ?f x \<partial>?P) \<le> 1"
      by (simp_all add: )
  qed
  also have "- log b (integral\<^sup>L ?P ?f) \<le> (\<integral> x. - log b (?f x) \<partial>?P)"
  proof (rule P.jensens_inequality[where a=0 and b=1 and I="{0<..}"])
    show "AE x in ?P. ?f x \<in> {0<..}"
      unfolding AE_density[OF distributed_borel_measurable[OF Pxyz]]
      using ae1 ae2 ae3 ae4 AE_space
      by eventually_elim (insert Pxyz_nn Pyz_nn Pz_nn Pxz_nn, auto simp: space_pair_measure less_le)
    show "integrable ?P ?f"
      unfolding real_integrable_def
      using fin neg by (auto simp: split_beta')
    show "integrable ?P (\<lambda>x. - log b (?f x))"
      using Pz_nn Pxz_nn Pyz_nn Pxyz_nn
      apply (subst integrable_real_density)
      apply simp
      apply simp
      apply simp
      apply (rule integrable_cong_AE[THEN iffD1, OF _ _ _ I3])
      apply simp
      apply simp
      using ae1 ae2 ae3 ae4 AE_space
      apply eventually_elim
      apply (auto simp: log_divide_eq log_mult_eq zero_le_mult_iff zero_less_mult_iff
                        zero_less_divide_iff field_simps space_pair_measure less_le)
      done
  qed (auto simp: b_gt_1 minus_log_convex)
  also have "\<dots> = conditional_mutual_information b S T P X Y Z"
    unfolding \<open>?eq\<close>
    using Pz_nn Pxz_nn Pyz_nn Pxyz_nn
    apply (subst integral_real_density)
    apply simp
    apply simp
    apply simp
    apply (intro integral_cong_AE)
    using ae1 ae2 ae3 ae4 AE_space
    apply (auto simp: log_divide_eq zero_less_mult_iff zero_less_divide_iff
                      field_simps space_pair_measure less_le)
    done
  finally show ?nonneg
    by simp
qed

lemma (in information_space) conditional_mutual_information_eq:
  assumes Pz: "simple_distributed M Z Pz"
  assumes Pyz: "simple_distributed M (\<lambda>x. (Y x, Z x)) Pyz"
  assumes Pxz: "simple_distributed M (\<lambda>x. (X x, Z x)) Pxz"
  assumes Pxyz: "simple_distributed M (\<lambda>x. (X x, Y x, Z x)) Pxyz"
  shows "\<I>(X ; Y | Z) =
   (\<Sum>(x, y, z)\<in>(\<lambda>x. (X x, Y x, Z x))`space M. Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))))"
proof (subst conditional_mutual_information_generic_eq[OF _ _ _ _ _
    simple_distributed[OF Pz] _ simple_distributed_joint[OF Pyz] _ simple_distributed_joint[OF Pxz] _
    simple_distributed_joint2[OF Pxyz]])
  note simple_distributed_joint2_finite[OF Pxyz, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Z ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  have "count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M) \<Otimes>\<^sub>M count_space (Z ` space M) =
      count_space (X`space M \<times> Y`space M \<times> Z`space M)"
    (is "?P = ?C")
    by (simp add: pair_measure_count_space)

  let ?Px = "\<lambda>x. measure M (X -` {x} \<inter> space M)"
  have "(\<lambda>x. (X x, Z x)) \<in> measurable M (count_space (X ` space M) \<Otimes>\<^sub>M count_space (Z ` space M))"
    using simple_distributed_joint[OF Pxz] by (rule distributed_measurable)
  from measurable_comp[OF this measurable_fst]
  have "random_variable (count_space (X ` space M)) X"
    by (simp add: comp_def)
  then have "simple_function M X"
    unfolding simple_function_def by (auto simp: measurable_count_space_eq2)
  then have "simple_distributed M X ?Px"
    by (rule simple_distributedI) (auto simp: measure_nonneg)
  then show "distributed M (count_space (X ` space M)) X ?Px"
    by (rule simple_distributed)

  let ?f = "(\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x, Z x)) ` space M then Pxyz x else 0)"
  let ?g = "(\<lambda>x. if x \<in> (\<lambda>x. (Y x, Z x)) ` space M then Pyz x else 0)"
  let ?h = "(\<lambda>x. if x \<in> (\<lambda>x. (X x, Z x)) ` space M then Pxz x else 0)"
  show
      "integrable ?P (\<lambda>(x, y, z). ?f (x, y, z) * log b (?f (x, y, z) / (?Px x * ?g (y, z))))"
      "integrable ?P (\<lambda>(x, y, z). ?f (x, y, z) * log b (?h (x, z) / (?Px x * Pz z)))"
    by (auto intro!: integrable_count_space simp: pair_measure_count_space)
  let ?i = "\<lambda>x y z. ?f (x, y, z) * log b (?f (x, y, z) / (?h (x, z) * (?g (y, z) / Pz z)))"
  let ?j = "\<lambda>x y z. Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z)))"
  have "(\<lambda>(x, y, z). ?i x y z) = (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x, Z x)) ` space M then ?j (fst x) (fst (snd x)) (snd (snd x)) else 0)"
    by (auto intro!: ext)
  then show "(\<integral> (x, y, z). ?i x y z \<partial>?P) = (\<Sum>(x, y, z)\<in>(\<lambda>x. (X x, Y x, Z x)) ` space M. ?j x y z)"
    by (auto intro!: sum.cong simp add: \<open>?P = ?C\<close> lebesgue_integral_count_space_finite simple_distributed_finite sum.If_cases split_beta')
qed (insert Pz Pyz Pxz Pxyz, auto intro: measure_nonneg)

lemma (in information_space) conditional_mutual_information_nonneg:
  assumes X: "simple_function M X" and Y: "simple_function M Y" and Z: "simple_function M Z"
  shows "0 \<le> \<I>(X ; Y | Z)"
proof -
  have [simp]: "count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M) \<Otimes>\<^sub>M count_space (Z ` space M) =
      count_space (X`space M \<times> Y`space M \<times> Z`space M)"
    by (simp add: pair_measure_count_space X Y Z simple_functionD)
  note sf = sigma_finite_measure_count_space_finite[OF simple_functionD(1)]
  note sd = simple_distributedI[OF _ _ refl]
  note sp = simple_function_Pair
  show ?thesis
   apply (rule conditional_mutual_information_generic_nonneg[OF sf[OF X] sf[OF Y] sf[OF Z]])
   apply (rule simple_distributed[OF sd[OF X]])
   apply simp
   apply simp
   apply (rule simple_distributed[OF sd[OF Z]])
   apply simp
   apply simp
   apply (rule simple_distributed_joint[OF sd[OF sp[OF Y Z]]])
   apply simp
   apply simp
   apply (rule simple_distributed_joint[OF sd[OF sp[OF X Z]]])
   apply simp
   apply simp
   apply (rule simple_distributed_joint2[OF sd[OF sp[OF X sp[OF Y Z]]]])
   apply simp
   apply simp
   apply (auto intro!: integrable_count_space simp: X Y Z simple_functionD)
   done
qed

subsection \<open>Conditional Entropy\<close>

definition (in prob_space)
  "conditional_entropy b S T X Y = - (\<integral>(x, y). log b (enn2real (RN_deriv (S \<Otimes>\<^sub>M T) (distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))) (x, y)) /
    enn2real (RN_deriv T (distr M T Y) y)) \<partial>distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)))"

abbreviation (in information_space)
  conditional_entropy_Pow ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> conditional_entropy b (count_space (X`space M)) (count_space (Y`space M)) X Y"

lemma (in information_space) conditional_entropy_generic_eq:
  fixes Pxy :: "_ \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Py[measurable]: "distributed M T Y Py" and Py_nn[simp]: "\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x"
  assumes Pxy[measurable]: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    and Pxy_nn[simp]: "\<And>x y. x \<in> space S \<Longrightarrow> y \<in> space T \<Longrightarrow> 0 \<le> Pxy (x, y)"
  shows "conditional_entropy b S T X Y = - (\<integral>(x, y). Pxy (x, y) * log b (Pxy (x, y) / Py y) \<partial>(S \<Otimes>\<^sub>M T))"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  have [measurable]: "Py \<in> T \<rightarrow>\<^sub>M borel"
    using Py Py_nn by (intro distributed_real_measurable)
  have measurable_Pxy[measurable]: "Pxy \<in> (S \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M borel"
    using Pxy Pxy_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)

  have "AE x in density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Pxy x)). Pxy x = enn2real (RN_deriv (S \<Otimes>\<^sub>M T) (distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))) x)"
    unfolding AE_density[OF distributed_borel_measurable, OF Pxy]
    unfolding distributed_distr_eq_density[OF Pxy]
    using distributed_RN_deriv[OF Pxy]
    by auto
  moreover
  have "AE x in density (S \<Otimes>\<^sub>M T) (\<lambda>x. ennreal (Pxy x)). Py (snd x) = enn2real (RN_deriv T (distr M T Y) (snd x))"
    unfolding AE_density[OF distributed_borel_measurable, OF Pxy]
    unfolding distributed_distr_eq_density[OF Py]
    apply (rule ST.AE_pair_measure)
    apply auto
    using distributed_RN_deriv[OF Py]
    apply auto
    done
  ultimately
  have "conditional_entropy b S T X Y = - (\<integral>x. Pxy x * log b (Pxy x / Py (snd x)) \<partial>(S \<Otimes>\<^sub>M T))"
    unfolding conditional_entropy_def neg_equal_iff_equal
    apply (subst integral_real_density[symmetric])
    apply (auto simp: distributed_distr_eq_density[OF Pxy] space_pair_measure
                intro!: integral_cong_AE)
    done
  then show ?thesis by (simp add: split_beta')
qed

lemma (in information_space) conditional_entropy_eq_entropy:
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Py[measurable]: "distributed M T Y Py"
    and Py_nn[simp]: "\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x"
  assumes Pxy[measurable]: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    and Pxy_nn[simp]: "\<And>x y. x \<in> space S \<Longrightarrow> y \<in> space T \<Longrightarrow> 0 \<le> Pxy (x, y)"
  assumes I1: "integrable (S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Pxy x))"
  assumes I2: "integrable (S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Py (snd x)))"
  shows "conditional_entropy b S T X Y = entropy b (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) - entropy b T Y"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  have [measurable]: "Py \<in> T \<rightarrow>\<^sub>M borel"
    using Py Py_nn by (intro distributed_real_measurable)
  have measurable_Pxy[measurable]: "Pxy \<in> (S \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M borel"
    using Pxy Pxy_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)

  have "entropy b T Y = - (\<integral>y. Py y * log b (Py y) \<partial>T)"
    by (rule entropy_distr[OF Py Py_nn])
  also have "\<dots> = - (\<integral>(x,y). Pxy (x,y) * log b (Py y) \<partial>(S \<Otimes>\<^sub>M T))"
    using b_gt_1
    by (subst distributed_transform_integral[OF Pxy _ Py, where T=snd])
       (auto intro!: Bochner_Integration.integral_cong simp: space_pair_measure)
  finally have e_eq: "entropy b T Y = - (\<integral>(x,y). Pxy (x,y) * log b (Py y) \<partial>(S \<Otimes>\<^sub>M T))" .

  have **: "\<And>x. x \<in> space (S \<Otimes>\<^sub>M T) \<Longrightarrow> 0 \<le> Pxy x"
    by (auto simp: space_pair_measure)

  have ae2: "AE x in S \<Otimes>\<^sub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of snd, OF _ Pxy Py])
       (auto intro: measurable_Pair simp: space_pair_measure)
  moreover have ae4: "AE x in S \<Otimes>\<^sub>M T. 0 \<le> Py (snd x)"
    using Py by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'')
  ultimately have "AE x in S \<Otimes>\<^sub>M T. 0 \<le> Pxy x \<and> 0 \<le> Py (snd x) \<and>
    (Pxy x = 0 \<or> (Pxy x \<noteq> 0 \<longrightarrow> 0 < Pxy x \<and> 0 < Py (snd x)))"
    using AE_space by eventually_elim (auto simp: space_pair_measure less_le)
  then have ae: "AE x in S \<Otimes>\<^sub>M T.
     Pxy x * log b (Pxy x) - Pxy x * log b (Py (snd x)) = Pxy x * log b (Pxy x / Py (snd x))"
    by eventually_elim (auto simp: log_simps field_simps b_gt_1)
  have "conditional_entropy b S T X Y =
    - (\<integral>x. Pxy x * log b (Pxy x) - Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^sub>M T))"
    unfolding conditional_entropy_generic_eq[OF S T Py Py_nn Pxy Pxy_nn, simplified] neg_equal_iff_equal
    apply (intro integral_cong_AE)
    using ae
    apply auto
    done
  also have "\<dots> = - (\<integral>x. Pxy x * log b (Pxy x) \<partial>(S \<Otimes>\<^sub>M T)) - - (\<integral>x.  Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^sub>M T))"
    by (simp add: Bochner_Integration.integral_diff[OF I1 I2])
  finally show ?thesis
    using conditional_entropy_generic_eq[OF S T Py Py_nn Pxy Pxy_nn, simplified]
      entropy_distr[OF Pxy **, simplified] e_eq
    by (simp add: split_beta')
qed

lemma (in information_space) conditional_entropy_eq_entropy_simple:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<H>(X | Y) = entropy b (count_space (X`space M) \<Otimes>\<^sub>M count_space (Y`space M)) (\<lambda>x. (X x, Y x)) - \<H>(Y)"
proof -
  have "count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M) = count_space (X`space M \<times> Y`space M)"
    (is "?P = ?C") using X Y by (simp add: simple_functionD pair_measure_count_space)
  show ?thesis
    by (rule conditional_entropy_eq_entropy sigma_finite_measure_count_space_finite
             simple_functionD  X Y simple_distributed simple_distributedI[OF _ _ refl]
             simple_distributed_joint simple_function_Pair integrable_count_space measure_nonneg)+
       (auto simp: \<open>?P = ?C\<close> measure_nonneg intro!: integrable_count_space simple_functionD  X Y)
qed

lemma (in information_space) conditional_entropy_eq:
  assumes Y: "simple_distributed M Y Py"
  assumes XY: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
    shows "\<H>(X | Y) = - (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / Py y))"
proof (subst conditional_entropy_generic_eq[OF _ _
  simple_distributed[OF Y] _ simple_distributed_joint[OF XY]])
  have "finite ((\<lambda>x. (X x, Y x))`space M)"
    using XY unfolding simple_distributed_def by auto
  from finite_imageI[OF this, of fst]
  have [simp]: "finite (X`space M)"
    by (simp add: image_comp comp_def)
  note Y[THEN simple_distributed_finite, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  let ?f = "(\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x else 0)"
  have "count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M) = count_space (X`space M \<times> Y`space M)"
    (is "?P = ?C")
    using Y by (simp add: simple_distributed_finite pair_measure_count_space)
  have eq: "(\<lambda>(x, y). ?f (x, y) * log b (?f (x, y) / Py y)) =
    (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x * log b (Pxy x / Py (snd x)) else 0)"
    by auto
  from Y show "- (\<integral> (x, y). ?f (x, y) * log b (?f (x, y) / Py y) \<partial>?P) =
    - (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / Py y))"
    by (auto intro!: sum.cong simp add: \<open>?P = ?C\<close> lebesgue_integral_count_space_finite simple_distributed_finite eq sum.If_cases split_beta')
qed (insert Y XY, auto)

lemma (in information_space) conditional_mutual_information_eq_conditional_entropy:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<I>(X ; X | Y) = \<H>(X | Y)"
proof -
  define Py where "Py x = (if x \<in> Y`space M then measure M (Y -` {x} \<inter> space M) else 0)" for x
  define Pxy where "Pxy x =
      (if x \<in> (\<lambda>x. (X x, Y x))`space M then measure M ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M) else 0)"
    for x
  define Pxxy where "Pxxy x =
      (if x \<in> (\<lambda>x. (X x, X x, Y x))`space M then measure M ((\<lambda>x. (X x, X x, Y x)) -` {x} \<inter> space M)
       else 0)"
    for x
  let ?M = "X`space M \<times> X`space M \<times> Y`space M"

  note XY = simple_function_Pair[OF X Y]
  note XXY = simple_function_Pair[OF X XY]
  have Py: "simple_distributed M Y Py"
    using Y by (rule simple_distributedI) (auto simp: Py_def measure_nonneg)
  have Pxy: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
    using XY by (rule simple_distributedI) (auto simp: Pxy_def measure_nonneg)
  have Pxxy: "simple_distributed M (\<lambda>x. (X x, X x, Y x)) Pxxy"
    using XXY by (rule simple_distributedI) (auto simp: Pxxy_def measure_nonneg)
  have eq: "(\<lambda>x. (X x, X x, Y x)) ` space M = (\<lambda>(x, y). (x, x, y)) ` (\<lambda>x. (X x, Y x)) ` space M"
    by auto
  have inj: "\<And>A. inj_on (\<lambda>(x, y). (x, x, y)) A"
    by (auto simp: inj_on_def)
  have Pxxy_eq: "\<And>x y. Pxxy (x, x, y) = Pxy (x, y)"
    by (auto simp: Pxxy_def Pxy_def intro!: arg_cong[where f=prob])
  have "AE x in count_space ((\<lambda>x. (X x, Y x))`space M). Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    using Py Pxy
    by (intro subdensity_real[of snd, OF _ Pxy[THEN simple_distributed] Py[THEN simple_distributed]])
       (auto intro: measurable_Pair simp: AE_count_space)
  then show ?thesis
    apply (subst conditional_mutual_information_eq[OF Py Pxy Pxy Pxxy])
    apply (subst conditional_entropy_eq[OF Py Pxy])
    apply (auto intro!: sum.cong simp: Pxxy_eq sum_negf[symmetric] eq sum.reindex[OF inj]
                log_simps zero_less_mult_iff zero_le_mult_iff field_simps mult_less_0_iff AE_count_space)
    using Py[THEN simple_distributed] Pxy[THEN simple_distributed]
    apply (auto simp add: not_le AE_count_space less_le antisym
      simple_distributed_nonneg[OF Py] simple_distributed_nonneg[OF Pxy])
    done
qed

lemma (in information_space) conditional_entropy_nonneg:
  assumes X: "simple_function M X" and Y: "simple_function M Y" shows "0 \<le> \<H>(X | Y)"
  using conditional_mutual_information_eq_conditional_entropy[OF X Y] conditional_mutual_information_nonneg[OF X X Y]
  by simp

subsection \<open>Equalities\<close>

lemma (in information_space) mutual_information_eq_entropy_conditional_entropy_distr:
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real" and Pxy :: "('b \<times> 'c) \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Px[measurable]: "distributed M S X Px"
    and Px_nn[simp]: "\<And>x. x \<in> space S \<Longrightarrow> 0 \<le> Px x"
    and Py[measurable]: "distributed M T Y Py"
    and Py_nn[simp]: "\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x"
    and Pxy[measurable]: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    and Pxy_nn[simp]: "\<And>x y. x \<in> space S \<Longrightarrow> y \<in> space T \<Longrightarrow> 0 \<le> Pxy (x, y)"
  assumes Ix: "integrable(S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Px (fst x)))"
  assumes Iy: "integrable(S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Py (snd x)))"
  assumes Ixy: "integrable(S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Pxy x))"
  shows  "mutual_information b S T X Y = entropy b S X + entropy b T Y - entropy b (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
proof -
  have [measurable]: "Px \<in> S \<rightarrow>\<^sub>M borel"
    using Px Px_nn by (intro distributed_real_measurable)
  have [measurable]: "Py \<in> T \<rightarrow>\<^sub>M borel"
    using Py Py_nn by (intro distributed_real_measurable)
  have measurable_Pxy[measurable]: "Pxy \<in> (S \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M borel"
    using Pxy Pxy_nn by (intro distributed_real_measurable) (auto simp: space_pair_measure)

  have X: "entropy b S X = - (\<integral>x. Pxy x * log b (Px (fst x)) \<partial>(S \<Otimes>\<^sub>M T))"
    using b_gt_1
    apply (subst entropy_distr[OF Px Px_nn], simp)
    apply (subst distributed_transform_integral[OF Pxy _ Px, where T=fst])
    apply (auto intro!: integral_cong simp: space_pair_measure)
    done

  have Y: "entropy b T Y = - (\<integral>x. Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^sub>M T))"
    using b_gt_1
    apply (subst entropy_distr[OF Py Py_nn], simp)
    apply (subst distributed_transform_integral[OF Pxy _ Py, where T=snd])
    apply (auto intro!: integral_cong simp: space_pair_measure)
    done

  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  have ST: "sigma_finite_measure (S \<Otimes>\<^sub>M T)" ..

  have XY: "entropy b (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) = - (\<integral>x. Pxy x * log b (Pxy x) \<partial>(S \<Otimes>\<^sub>M T))"
    by (subst entropy_distr[OF Pxy]) (auto intro!: integral_cong simp: space_pair_measure)

  have "AE x in S \<Otimes>\<^sub>M T. Px (fst x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of fst, OF _ Pxy Px]) (auto intro: measurable_Pair simp: space_pair_measure)
  moreover have "AE x in S \<Otimes>\<^sub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of snd, OF _ Pxy Py]) (auto intro: measurable_Pair simp: space_pair_measure)
  moreover have "AE x in S \<Otimes>\<^sub>M T. 0 \<le> Px (fst x)"
    using Px by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_fst'')
  moreover have "AE x in S \<Otimes>\<^sub>M T. 0 \<le> Py (snd x)"
    using Py by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'')
  ultimately have "AE x in S \<Otimes>\<^sub>M T. Pxy x * log b (Pxy x) - Pxy x * log b (Px (fst x)) - Pxy x * log b (Py (snd x)) =
    Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x)))"
    (is "AE x in _. ?f x = ?g x")
    using AE_space
  proof eventually_elim
    case (elim x)
    show ?case
    proof cases
      assume "Pxy x \<noteq> 0"
      with elim have "0 < Px (fst x)" "0 < Py (snd x)" "0 < Pxy x"
        by (auto simp: space_pair_measure less_le)
      then show ?thesis
        using b_gt_1 by (simp add: log_simps less_imp_le field_simps)
    qed simp
  qed

  have "entropy b S X + entropy b T Y - entropy b (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) = integral\<^sup>L (S \<Otimes>\<^sub>M T) ?f"
    unfolding X Y XY
    apply (subst Bochner_Integration.integral_diff)
    apply (intro Bochner_Integration.integrable_diff Ixy Ix Iy)+
    apply (subst Bochner_Integration.integral_diff)
    apply (intro Ixy Ix Iy)+
    apply (simp add: field_simps)
    done
  also have "\<dots> = integral\<^sup>L (S \<Otimes>\<^sub>M T) ?g"
    using \<open>AE x in _. ?f x = ?g x\<close> by (intro integral_cong_AE) auto
  also have "\<dots> = mutual_information b S T X Y"
    by (rule mutual_information_distr[OF S T Px _ Py _ Pxy _ , symmetric])
       (auto simp: space_pair_measure)
  finally show ?thesis ..
qed

lemma (in information_space) mutual_information_eq_entropy_conditional_entropy':
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real" and Pxy :: "('b \<times> 'c) \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Px: "distributed M S X Px" "\<And>x. x \<in> space S \<Longrightarrow> 0 \<le> Px x"
    and Py: "distributed M T Y Py" "\<And>x. x \<in> space T \<Longrightarrow> 0 \<le> Py x"
  assumes Pxy: "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
    "\<And>x. x \<in> space (S \<Otimes>\<^sub>M T) \<Longrightarrow> 0 \<le> Pxy x"
  assumes Ix: "integrable(S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Px (fst x)))"
  assumes Iy: "integrable(S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Py (snd x)))"
  assumes Ixy: "integrable(S \<Otimes>\<^sub>M T) (\<lambda>x. Pxy x * log b (Pxy x))"
  shows  "mutual_information b S T X Y = entropy b S X - conditional_entropy b S T X Y"
  using
    mutual_information_eq_entropy_conditional_entropy_distr[OF S T Px Py Pxy Ix Iy Ixy]
    conditional_entropy_eq_entropy[OF S T Py Pxy Ixy Iy]
  by (simp add: space_pair_measure)

lemma (in information_space) mutual_information_eq_entropy_conditional_entropy:
  assumes sf_X: "simple_function M X" and sf_Y: "simple_function M Y"
  shows  "\<I>(X ; Y) = \<H>(X) - \<H>(X | Y)"
proof -
  have X: "simple_distributed M X (\<lambda>x. measure M (X -` {x} \<inter> space M))"
    using sf_X by (rule simple_distributedI) (auto simp: measure_nonneg)
  have Y: "simple_distributed M Y (\<lambda>x. measure M (Y -` {x} \<inter> space M))"
    using sf_Y by (rule simple_distributedI) (auto simp: measure_nonneg)
  have sf_XY: "simple_function M (\<lambda>x. (X x, Y x))"
    using sf_X sf_Y by (rule simple_function_Pair)
  then have XY: "simple_distributed M (\<lambda>x. (X x, Y x)) (\<lambda>x. measure M ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M))"
    by (rule simple_distributedI) (auto simp: measure_nonneg)
  from simple_distributed_joint_finite[OF this, simp]
  have eq: "count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M) = count_space (X ` space M \<times> Y ` space M)"
    by (simp add: pair_measure_count_space)

  have "\<I>(X ; Y) = \<H>(X) + \<H>(Y) - entropy b (count_space (X`space M) \<Otimes>\<^sub>M count_space (Y`space M)) (\<lambda>x. (X x, Y x))"
    using sigma_finite_measure_count_space_finite
      sigma_finite_measure_count_space_finite
      simple_distributed[OF X] measure_nonneg simple_distributed[OF Y] measure_nonneg simple_distributed_joint[OF XY]
    by (rule mutual_information_eq_entropy_conditional_entropy_distr)
       (auto simp: eq integrable_count_space measure_nonneg)
  then show ?thesis
    unfolding conditional_entropy_eq_entropy_simple[OF sf_X sf_Y] by simp
qed

lemma (in information_space) mutual_information_nonneg_simple:
  assumes sf_X: "simple_function M X" and sf_Y: "simple_function M Y"
  shows  "0 \<le> \<I>(X ; Y)"
proof -
  have X: "simple_distributed M X (\<lambda>x. measure M (X -` {x} \<inter> space M))"
    using sf_X by (rule simple_distributedI) (auto simp: measure_nonneg)
  have Y: "simple_distributed M Y (\<lambda>x. measure M (Y -` {x} \<inter> space M))"
    using sf_Y by (rule simple_distributedI) (auto simp: measure_nonneg)

  have sf_XY: "simple_function M (\<lambda>x. (X x, Y x))"
    using sf_X sf_Y by (rule simple_function_Pair)
  then have XY: "simple_distributed M (\<lambda>x. (X x, Y x)) (\<lambda>x. measure M ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M))"
    by (rule simple_distributedI) (auto simp: measure_nonneg)

  from simple_distributed_joint_finite[OF this, simp]
  have eq: "count_space (X ` space M) \<Otimes>\<^sub>M count_space (Y ` space M) = count_space (X ` space M \<times> Y ` space M)"
    by (simp add: pair_measure_count_space)

  show ?thesis
    by (rule mutual_information_nonneg[OF _ _ simple_distributed[OF X] _ simple_distributed[OF Y] _ simple_distributed_joint[OF XY]])
       (simp_all add: eq integrable_count_space sigma_finite_measure_count_space_finite measure_nonneg)
qed

lemma (in information_space) conditional_entropy_less_eq_entropy:
  assumes X: "simple_function M X" and Z: "simple_function M Z"
  shows "\<H>(X | Z) \<le> \<H>(X)"
proof -
  have "0 \<le> \<I>(X ; Z)" using X Z by (rule mutual_information_nonneg_simple)
  also have "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)" using mutual_information_eq_entropy_conditional_entropy[OF assms] .
  finally show ?thesis by auto
qed

lemma (in information_space)
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real" and Pxy :: "('b \<times> 'c) \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Px: "finite_entropy S X Px" and Py: "finite_entropy T Y Py"
  assumes Pxy: "finite_entropy (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "conditional_entropy b S T X Y \<le> entropy b S X"
proof -

  have "0 \<le> mutual_information b S T X Y"
    by (rule mutual_information_nonneg') fact+
  also have "\<dots> = entropy b S X - conditional_entropy b S T X Y"
    apply (rule mutual_information_eq_entropy_conditional_entropy')
    using assms
    by (auto intro!: finite_entropy_integrable finite_entropy_distributed
      finite_entropy_integrable_transform[OF Px]
      finite_entropy_integrable_transform[OF Py]
      intro: finite_entropy_nn)
  finally show ?thesis by auto
qed

lemma (in information_space) entropy_chain_rule:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows  "\<H>(\<lambda>x. (X x, Y x)) = \<H>(X) + \<H>(Y|X)"
proof -
  note XY = simple_distributedI[OF simple_function_Pair[OF X Y] measure_nonneg refl]
  note YX = simple_distributedI[OF simple_function_Pair[OF Y X] measure_nonneg refl]
  note simple_distributed_joint_finite[OF this, simp]
  let ?f = "\<lambda>x. prob ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M)"
  let ?g = "\<lambda>x. prob ((\<lambda>x. (Y x, X x)) -` {x} \<inter> space M)"
  let ?h = "\<lambda>x. if x \<in> (\<lambda>x. (Y x, X x)) ` space M then prob ((\<lambda>x. (Y x, X x)) -` {x} \<inter> space M) else 0"
  have "\<H>(\<lambda>x. (X x, Y x)) = - (\<Sum>x\<in>(\<lambda>x. (X x, Y x)) ` space M. ?f x * log b (?f x))"
    using XY by (rule entropy_simple_distributed)
  also have "\<dots> = - (\<Sum>x\<in>(\<lambda>(x, y). (y, x)) ` (\<lambda>x. (X x, Y x)) ` space M. ?g x * log b (?g x))"
    by (subst (2) sum.reindex) (auto simp: inj_on_def intro!: sum.cong arg_cong[where f="\<lambda>A. prob A * log b (prob A)"])
  also have "\<dots> = - (\<Sum>x\<in>(\<lambda>x. (Y x, X x)) ` space M. ?h x * log b (?h x))"
    by (auto intro!: sum.cong)
  also have "\<dots> = entropy b (count_space (Y ` space M) \<Otimes>\<^sub>M count_space (X ` space M)) (\<lambda>x. (Y x, X x))"
    by (subst entropy_distr[OF simple_distributed_joint[OF YX]])
       (auto simp: pair_measure_count_space sigma_finite_measure_count_space_finite lebesgue_integral_count_space_finite
             cong del: sum.cong_simp intro!: sum.mono_neutral_left measure_nonneg)
  finally have "\<H>(\<lambda>x. (X x, Y x)) = entropy b (count_space (Y ` space M) \<Otimes>\<^sub>M count_space (X ` space M)) (\<lambda>x. (Y x, X x))" .
  then show ?thesis
    unfolding conditional_entropy_eq_entropy_simple[OF Y X] by simp
qed

lemma (in information_space) entropy_partition:
  assumes X: "simple_function M X"
  shows "\<H>(X) = \<H>(f \<circ> X) + \<H>(X|f \<circ> X)"
proof -
  note fX = simple_function_compose[OF X, of f]
  have eq: "(\<lambda>x. ((f \<circ> X) x, X x)) ` space M = (\<lambda>x. (f x, x)) ` X ` space M" by auto
  have inj: "\<And>A. inj_on (\<lambda>x. (f x, x)) A"
    by (auto simp: inj_on_def)
  show ?thesis
    apply (subst entropy_chain_rule[symmetric, OF fX X])
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF simple_function_Pair[OF fX X] measure_nonneg refl]])
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF X measure_nonneg refl]])
    unfolding eq
    apply (subst sum.reindex[OF inj])
    apply (auto intro!: sum.cong arg_cong[where f="\<lambda>A. prob A * log b (prob A)"])
    done
qed

corollary (in information_space) entropy_data_processing:
  assumes X: "simple_function M X" shows "\<H>(f \<circ> X) \<le> \<H>(X)"
proof -
  note fX = simple_function_compose[OF X, of f]
  from X have "\<H>(X) = \<H>(f\<circ>X) + \<H>(X|f\<circ>X)" by (rule entropy_partition)
  then show "\<H>(f \<circ> X) \<le> \<H>(X)"
    by (simp only: conditional_entropy_nonneg [OF X fX] le_add_same_cancel1)
qed

corollary (in information_space) entropy_of_inj:
  assumes X: "simple_function M X" and inj: "inj_on f (X`space M)"
  shows "\<H>(f \<circ> X) = \<H>(X)"
proof (rule antisym)
  show "\<H>(f \<circ> X) \<le> \<H>(X)" using entropy_data_processing[OF X] .
next
  have sf: "simple_function M (f \<circ> X)"
    using X by auto
  have "\<H>(X) = \<H>(the_inv_into (X`space M) f \<circ> (f \<circ> X))"
    unfolding o_assoc
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF X measure_nonneg refl]])
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF simple_function_compose[OF X]], where f="\<lambda>x. prob (X -` {x} \<inter> space M)"])
    apply (auto intro!: sum.cong arg_cong[where f=prob] image_eqI simp: the_inv_into_f_f[OF inj] comp_def measure_nonneg)
    done
  also have "... \<le> \<H>(f \<circ> X)"
    using entropy_data_processing[OF sf] .
  finally show "\<H>(X) \<le> \<H>(f \<circ> X)" .
qed

end
