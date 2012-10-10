(*  Title:      HOL/Probability/Information.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Information theory*}

theory Information
imports
  Independent_Family
  Radon_Nikodym
  "~~/src/HOL/Library/Convex"
begin

lemma log_le: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log a x \<le> log a y"
  by (subst log_le_cancel_iff) auto

lemma log_less: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> x < y \<Longrightarrow> log a x < log a y"
  by (subst log_less_cancel_iff) auto

lemma setsum_cartesian_product':
  "(\<Sum>x\<in>A \<times> B. f x) = (\<Sum>x\<in>A. setsum (\<lambda>y. f (x, y)) B)"
  unfolding setsum_cartesian_product by simp

lemma split_pairs:
  "((A, B) = X) \<longleftrightarrow> (fst X = A \<and> snd X = B)" and
  "(X = (A, B)) \<longleftrightarrow> (fst X = A \<and> snd X = B)" by auto

section "Information theory"

locale information_space = prob_space +
  fixes b :: real assumes b_gt_1: "1 < b"

context information_space
begin

text {* Introduce some simplification rules for logarithm of base @{term b}. *}

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
    by (simp add: log_def ln_def)
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

text {* The Kullback$-$Leibler divergence is also known as relative entropy or
Kullback$-$Leibler distance. *}

definition
  "entropy_density b M N = log b \<circ> real \<circ> RN_deriv M N"

definition
  "KL_divergence b M N = integral\<^isup>L N (entropy_density b M N)"

lemma (in information_space) measurable_entropy_density:
  assumes ac: "absolutely_continuous M N" "sets N = events"
  shows "entropy_density b M N \<in> borel_measurable M"
proof -
  from borel_measurable_RN_deriv[OF ac] b_gt_1 show ?thesis
    unfolding entropy_density_def
    by (intro measurable_comp) auto
qed

lemma (in sigma_finite_measure) KL_density:
  fixes f :: "'a \<Rightarrow> real"
  assumes "1 < b"
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  shows "KL_divergence b M (density M f) = (\<integral>x. f x * log b (f x) \<partial>M)"
  unfolding KL_divergence_def
proof (subst integral_density)
  show "entropy_density b M (density M (\<lambda>x. ereal (f x))) \<in> borel_measurable M"
    using f
    by (auto simp: comp_def entropy_density_def intro!: borel_measurable_log borel_measurable_RN_deriv_density)
  have "density M (RN_deriv M (density M f)) = density M f"
    using f by (intro density_RN_deriv_density) auto
  then have eq: "AE x in M. RN_deriv M (density M f) x = f x"
    using f
    by (intro density_unique)
       (auto intro!: borel_measurable_log borel_measurable_RN_deriv_density simp: RN_deriv_density_nonneg)
  show "(\<integral>x. f x * entropy_density b M (density M (\<lambda>x. ereal (f x))) x \<partial>M) = (\<integral>x. f x * log b (f x) \<partial>M)"
    apply (intro integral_cong_AE)
    using eq
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
    using f g `1 < b` by (intro Mf.KL_density) (auto simp: AE_density divide_nonneg_nonneg)
  also have "\<dots> = (\<integral>x. g x * log b (g x / f x) \<partial>M)"
    using ac f g `1 < b` by (subst integral_density) (auto intro!: integral_cong_AE)
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
    using measure_eqI[of "density M D" M] `density M D \<noteq> M` by auto

  let ?D_set = "{x\<in>space M. D x \<noteq> 0}"
  have [simp, intro]: "?D_set \<in> sets M"
    using D by auto

  have D_neg: "(\<integral>\<^isup>+ x. ereal (- D x) \<partial>M) = 0"
    using D by (subst positive_integral_0_iff_AE) auto

  have "(\<integral>\<^isup>+ x. ereal (D x) \<partial>M) = emeasure (density M D) (space M)"
    using D by (simp add: emeasure_density cong: positive_integral_cong)
  then have D_pos: "(\<integral>\<^isup>+ x. ereal (D x) \<partial>M) = 1"
    using N.emeasure_space_1 by simp

  have "integrable M D" "integral\<^isup>L M D = 1"
    using D D_pos D_neg unfolding integrable_def lebesgue_integral_def by simp_all

  have "0 \<le> 1 - measure M ?D_set"
    using prob_le_1 by (auto simp: field_simps)
  also have "\<dots> = (\<integral> x. D x - indicator ?D_set x \<partial>M)"
    using `integrable M D` `integral\<^isup>L M D = 1`
    by (simp add: emeasure_eq_measure)
  also have "\<dots> < (\<integral> x. D x * (ln b * log b (D x)) \<partial>M)"
  proof (rule integral_less_AE)
    show "integrable M (\<lambda>x. D x - indicator ?D_set x)"
      using `integrable M D`
      by (intro integral_diff integral_indicator) auto
  next
    from integral_cmult(1)[OF int, of "ln b"]
    show "integrable M (\<lambda>x. D x * (ln b * log b (D x)))" 
      by (simp add: ac_simps)
  next
    show "emeasure M {x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} \<noteq> 0"
    proof
      assume eq_0: "emeasure M {x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} = 0"
      then have disj: "AE x in M. D x = 1 \<or> D x = 0"
        using D(1) by (auto intro!: AE_I[OF subset_refl] sets_Collect)

      have "emeasure M {x\<in>space M. D x = 1} = (\<integral>\<^isup>+ x. indicator {x\<in>space M. D x = 1} x \<partial>M)"
        using D(1) by auto
      also have "\<dots> = (\<integral>\<^isup>+ x. ereal (D x) \<partial>M)"
        using disj by (auto intro!: positive_integral_cong_AE simp: indicator_def one_ereal_def)
      finally have "AE x in M. D x = 1"
        using D D_pos by (intro AE_I_eq_1) auto
      then have "(\<integral>\<^isup>+x. indicator A x\<partial>M) = (\<integral>\<^isup>+x. ereal (D x) * indicator A x\<partial>M)"
        by (intro positive_integral_cong_AE) (auto simp: one_ereal_def[symmetric])
      also have "\<dots> = density M D A"
        using `A \<in> sets M` D by (simp add: emeasure_density)
      finally show False using `A \<in> sets M` `emeasure (density M D) A \<noteq> emeasure M A` by simp
    qed
    show "{x\<in>space M. D x \<noteq> 1 \<and> D x \<noteq> 0} \<in> sets M"
      using D(1) by (auto intro: sets_Collect_conj)

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
        using b_gt_1 `D t \<noteq> 0` `0 \<le> D t`
        by (simp add: log_def ln_div less_le)
      finally have "ln (1 / D t) = 1 / D t - 1"
        using `D t \<noteq> 0` by (auto simp: field_simps)
      from ln_eq_minus_one[OF _ this] `D t \<noteq> 0` `0 \<le> D t` `D t \<noteq> 1`
      show False by auto
    qed

    show "AE t in M. D t - indicator ?D_set t \<le> D t * (ln b * log b (D t))"
      using D(2) AE_space
    proof eventually_elim
      fix t assume "t \<in> space M" "0 \<le> D t"
      show "D t - indicator ?D_set t \<le> D t * (ln b * log b (D t))"
      proof cases
        assume asm: "D t \<noteq> 0"
        then have "0 < D t" using `0 \<le> D t` by auto
        then have "0 < 1 / D t" by auto
        have "D t - indicator ?D_set t \<le> - D t * (1 / D t - 1)"
          using asm `t \<in> space M` by (simp add: field_simps)
        also have "- D t * (1 / D t - 1) \<le> - D t * ln (1 / D t)"
          using ln_le_minus_one `0 < 1 / D t` by (intro mult_left_mono_neg) auto
        also have "\<dots> = D t * (ln b * log b (D t))"
          using `0 < D t` b_gt_1
          by (simp_all add: log_def ln_div)
        finally show ?thesis by simp
      qed simp
    qed
  qed
  also have "\<dots> = (\<integral> x. ln b * (D x * log b (D x)) \<partial>M)"
    by (simp add: ac_simps)
  also have "\<dots> = ln b * (\<integral> x. D x * log b (D x) \<partial>M)"
    using int by (rule integral_cmult)
  finally show ?thesis
    using b_gt_1 D by (subst KL_density) (auto simp: zero_less_mult_iff)
qed

lemma (in sigma_finite_measure) KL_same_eq_0: "KL_divergence b M M = 0"
proof -
  have "AE x in M. 1 = RN_deriv M M x"
  proof (rule RN_deriv_unique)
    show "(\<lambda>x. 1) \<in> borel_measurable M" "AE x in M. 0 \<le> (1 :: ereal)" by auto
    show "density M (\<lambda>x. 1) = M"
      apply (auto intro!: measure_eqI emeasure_density)
      apply (subst emeasure_density)
      apply auto
      done
  qed
  then have "AE x in M. log b (real (RN_deriv M M x)) = 0"
    by (elim AE_mp) simp
  from integral_cong_AE[OF this]
  have "integral\<^isup>L M (entropy_density b M M) = 0"
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
  from real_RN_deriv[OF this ac] guess D . note D = this
  
  have "N = density M (RN_deriv M N)"
    using ac by (rule density_RN_deriv[symmetric])
  also have "\<dots> = density M D"
    using borel_measurable_RN_deriv[OF ac] D by (auto intro!: density_cong)
  finally have N: "N = density M D" .

  from absolutely_continuous_AE[OF ac(2,1) D(2)] D b_gt_1 ac measurable_entropy_density
  have "integrable N (\<lambda>x. log b (D x))"
    by (intro integrable_cong_AE[THEN iffD2, OF _ _ _ int])
       (auto simp: N entropy_density_def)
  with D b_gt_1 have "integrable M (\<lambda>x. D x * log b (D x))"
    by (subst integral_density(2)[symmetric]) (auto simp: N[symmetric] comp_def)
  with `prob_space N` D show ?thesis
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
  interpret Mf: information_space "density M f" b by default fact
  have eq: "density (density M f) (\<lambda>x. g x / f x) = density M g" (is "?DD = _")
    using f g ac by (subst density_density_divide) simp_all

  have "0 \<le> KL_divergence b (density M f) (density (density M f) (\<lambda>x. g x / f x))"
  proof (rule Mf.KL_nonneg)
    show "prob_space ?DD" unfolding eq by fact
    from f g show "(\<lambda>x. g x / f x) \<in> borel_measurable (density M f)"
      by auto
    show "AE x in density M f. 0 \<le> g x / f x"
      using f g by (auto simp: AE_density divide_nonneg_nonneg)
    show "integrable (density M f) (\<lambda>x. g x / f x * log b (g x / f x))"
      using `1 < b` f g ac
      by (subst integral_density)
         (auto intro!: integrable_cong_AE[THEN iffD2, OF _ _ _ int] measurable_If)
  qed
  also have "\<dots> = KL_divergence b (density M f) (density M g)"
    using f g ac by (subst density_density_divide) simp_all
  finally show ?thesis .
qed

subsection {* Mutual Information *}

definition (in prob_space)
  "mutual_information b S T X Y =
    KL_divergence b (distr M S X \<Otimes>\<^isub>M distr M T Y) (distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)))"

lemma (in information_space) mutual_information_indep_vars:
  fixes S T X Y
  defines "P \<equiv> distr M S X \<Otimes>\<^isub>M distr M T Y"
  defines "Q \<equiv> distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
  shows "indep_var S X T Y \<longleftrightarrow>
    (random_variable S X \<and> random_variable T Y \<and>
      absolutely_continuous P Q \<and> integrable Q (entropy_density b P Q) \<and>
      mutual_information b S T X Y = 0)"
  unfolding indep_var_distribution_eq
proof safe
  assume rv: "random_variable S X" "random_variable T Y"

  interpret X: prob_space "distr M S X"
    by (rule prob_space_distr) fact
  interpret Y: prob_space "distr M T Y"
    by (rule prob_space_distr) fact
  interpret XY: pair_prob_space "distr M S X" "distr M T Y" by default
  interpret P: information_space P b unfolding P_def by default (rule b_gt_1)

  interpret Q: prob_space Q unfolding Q_def
    by (rule prob_space_distr) (simp add: comp_def measurable_pair_iff rv)

  { assume "distr M S X \<Otimes>\<^isub>M distr M T Y = distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
    then have [simp]: "Q = P"  unfolding Q_def P_def by simp

    show ac: "absolutely_continuous P Q" by (simp add: absolutely_continuous_def)
    then have ed: "entropy_density b P Q \<in> borel_measurable P"
      by (rule P.measurable_entropy_density) simp

    have "AE x in P. 1 = RN_deriv P Q x"
    proof (rule P.RN_deriv_unique)
      show "density P (\<lambda>x. 1) = Q"
        unfolding `Q = P` by (intro measure_eqI) (auto simp: emeasure_density)
    qed auto
    then have ae_0: "AE x in P. entropy_density b P Q x = 0"
      by eventually_elim (auto simp: entropy_density_def)
    then have "integrable P (entropy_density b P Q) \<longleftrightarrow> integrable Q (\<lambda>x. 0)"
      using ed unfolding `Q = P` by (intro integrable_cong_AE) auto
    then show "integrable Q (entropy_density b P Q)" by simp

    show "mutual_information b S T X Y = 0"
      unfolding mutual_information_def KL_divergence_def P_def[symmetric] Q_def[symmetric] `Q = P`
      using ae_0 by (simp cong: integral_cong_AE) }

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
    then show "distr M S X \<Otimes>\<^isub>M distr M T Y = distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
      unfolding P_def Q_def .. }
qed

abbreviation (in information_space)
  mutual_information_Pow ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> mutual_information b (count_space (X`space M)) (count_space (Y`space M)) X Y"

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Px: "distributed M S X Px" and Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  defines "f \<equiv> \<lambda>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x)))"
  shows mutual_information_distr: "mutual_information b S T X Y = integral\<^isup>L (S \<Otimes>\<^isub>M T) f" (is "?M = ?R")
    and mutual_information_nonneg: "integrable (S \<Otimes>\<^isub>M T) f \<Longrightarrow> 0 \<le> mutual_information b S T X Y"
proof -
  have X: "random_variable S X"
    using Px by (auto simp: distributed_def)
  have Y: "random_variable T Y"
    using Py by (auto simp: distributed_def)
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  interpret X: prob_space "distr M S X" using X by (rule prob_space_distr)
  interpret Y: prob_space "distr M T Y" using Y by (rule prob_space_distr)
  interpret XY: pair_prob_space "distr M S X" "distr M T Y" ..
  let ?P = "S \<Otimes>\<^isub>M T"
  let ?D = "distr M ?P (\<lambda>x. (X x, Y x))"

  { fix A assume "A \<in> sets S"
    with X Y have "emeasure (distr M S X) A = emeasure ?D (A \<times> space T)"
      by (auto simp: emeasure_distr measurable_Pair measurable_space
               intro!: arg_cong[where f="emeasure M"]) }
  note marginal_eq1 = this
  { fix A assume "A \<in> sets T"
    with X Y have "emeasure (distr M T Y) A = emeasure ?D (space S \<times> A)"
      by (auto simp: emeasure_distr measurable_Pair measurable_space
               intro!: arg_cong[where f="emeasure M"]) }
  note marginal_eq2 = this

  have eq: "(\<lambda>x. ereal (Px (fst x) * Py (snd x))) = (\<lambda>(x, y). ereal (Px x) * ereal (Py y))"
    by auto

  have distr_eq: "distr M S X \<Otimes>\<^isub>M distr M T Y = density ?P (\<lambda>x. ereal (Px (fst x) * Py (snd x)))"
    unfolding Px(1)[THEN distributed_distr_eq_density] Py(1)[THEN distributed_distr_eq_density] eq
  proof (subst pair_measure_density)
    show "(\<lambda>x. ereal (Px x)) \<in> borel_measurable S" "(\<lambda>y. ereal (Py y)) \<in> borel_measurable T"
      "AE x in S. 0 \<le> ereal (Px x)" "AE y in T. 0 \<le> ereal (Py y)"
      using Px Py by (auto simp: distributed_def)
    show "sigma_finite_measure (density S Px)" unfolding Px(1)[THEN distributed_distr_eq_density, symmetric] ..
    show "sigma_finite_measure (density T Py)" unfolding Py(1)[THEN distributed_distr_eq_density, symmetric] ..
  qed (fact | simp)+
  
  have M: "?M = KL_divergence b (density ?P (\<lambda>x. ereal (Px (fst x) * Py (snd x)))) (density ?P (\<lambda>x. ereal (Pxy x)))"
    unfolding mutual_information_def distr_eq Pxy(1)[THEN distributed_distr_eq_density] ..

  from Px Py have f: "(\<lambda>x. Px (fst x) * Py (snd x)) \<in> borel_measurable ?P"
    by (intro borel_measurable_times) (auto intro: distributed_real_measurable measurable_fst'' measurable_snd'')
  have PxPy_nonneg: "AE x in ?P. 0 \<le> Px (fst x) * Py (snd x)"
  proof (rule ST.AE_pair_measure)
    show "{x \<in> space ?P. 0 \<le> Px (fst x) * Py (snd x)} \<in> sets ?P"
      using f by auto
    show "AE x in S. AE y in T. 0 \<le> Px (fst (x, y)) * Py (snd (x, y))"
      using Px Py by (auto simp: zero_le_mult_iff dest!: distributed_real_AE)
  qed

  have "(AE x in ?P. Px (fst x) = 0 \<longrightarrow> Pxy x = 0)"
    by (rule subdensity_real[OF measurable_fst Pxy Px]) auto
  moreover
  have "(AE x in ?P. Py (snd x) = 0 \<longrightarrow> Pxy x = 0)"
    by (rule subdensity_real[OF measurable_snd Pxy Py]) auto
  ultimately have ac: "AE x in ?P. Px (fst x) * Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by eventually_elim auto

  show "?M = ?R"
    unfolding M f_def
    using b_gt_1 f PxPy_nonneg Pxy[THEN distributed_real_measurable] Pxy[THEN distributed_real_AE] ac
    by (rule ST.KL_density_density)

  assume int: "integrable (S \<Otimes>\<^isub>M T) f"
  show "0 \<le> ?M" unfolding M
  proof (rule ST.KL_density_density_nonneg
    [OF b_gt_1 f PxPy_nonneg _ Pxy[THEN distributed_real_measurable] Pxy[THEN distributed_real_AE] _ ac int[unfolded f_def]])
    show "prob_space (density (S \<Otimes>\<^isub>M T) (\<lambda>x. ereal (Pxy x))) "
      unfolding distributed_distr_eq_density[OF Pxy, symmetric]
      using distributed_measurable[OF Pxy] by (rule prob_space_distr)
    show "prob_space (density (S \<Otimes>\<^isub>M T) (\<lambda>x. ereal (Px (fst x) * Py (snd x))))"
      unfolding distr_eq[symmetric] by unfold_locales
  qed
qed

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes "sigma_finite_measure S" "sigma_finite_measure T"
  assumes Px: "distributed M S X Px" and Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  assumes ae: "AE x in S. AE y in T. Pxy (x, y) = Px x * Py y"
  shows mutual_information_eq_0: "mutual_information b S T X Y = 0"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  have "AE x in S \<Otimes>\<^isub>M T. Px (fst x) = 0 \<longrightarrow> Pxy x = 0"
    by (rule subdensity_real[OF measurable_fst Pxy Px]) auto
  moreover
  have "AE x in S \<Otimes>\<^isub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (rule subdensity_real[OF measurable_snd Pxy Py]) auto
  moreover 
  have "AE x in S \<Otimes>\<^isub>M T. Pxy x = Px (fst x) * Py (snd x)"
    using distributed_real_measurable[OF Px] distributed_real_measurable[OF Py] distributed_real_measurable[OF Pxy]
    by (intro ST.AE_pair_measure) (auto simp: ae intro!: measurable_snd'' measurable_fst'')
  ultimately have "AE x in S \<Otimes>\<^isub>M T. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))) = 0"
    by eventually_elim simp
  then have "(\<integral>x. Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))) \<partial>(S \<Otimes>\<^isub>M T)) = (\<integral>x. 0 \<partial>(S \<Otimes>\<^isub>M T))"
    by (rule integral_cong_AE)
  then show ?thesis
    by (subst mutual_information_distr[OF assms(1-5)]) simp
qed

lemma (in information_space) mutual_information_simple_distributed:
  assumes X: "simple_distributed M X Px" and Y: "simple_distributed M Y Py"
  assumes XY: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
  shows "\<I>(X ; Y) = (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x))`space M. Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y)))"
proof (subst mutual_information_distr[OF _ _ simple_distributed[OF X] simple_distributed[OF Y] simple_distributed_joint[OF XY]])
  note fin = simple_distributed_joint_finite[OF XY, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  let ?Pxy = "\<lambda>x. (if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x else 0)"
  let ?f = "\<lambda>x. ?Pxy x * log b (?Pxy x / (Px (fst x) * Py (snd x)))"
  have "\<And>x. ?f x = (if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x))) else 0)"
    by auto
  with fin show "(\<integral> x. ?f x \<partial>(count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M))) =
    (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y)))"
    by (auto simp add: pair_measure_count_space lebesgue_integral_count_space_finite setsum_cases split_beta'
             intro!: setsum_cong)
qed

lemma (in information_space)
  fixes Pxy :: "'b \<times> 'c \<Rightarrow> real" and Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes Px: "simple_distributed M X Px" and Py: "simple_distributed M Y Py"
  assumes Pxy: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
  assumes ae: "\<forall>x\<in>space M. Pxy (X x, Y x) = Px (X x) * Py (Y x)"
  shows mutual_information_eq_0_simple: "\<I>(X ; Y) = 0"
proof (subst mutual_information_simple_distributed[OF Px Py Pxy])
  have "(\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y))) =
    (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. 0)"
    by (intro setsum_cong) (auto simp: ae)
  then show "(\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M.
    Pxy (x, y) * log b (Pxy (x, y) / (Px x * Py y))) = 0" by simp
qed

subsection {* Entropy *}

definition (in prob_space) entropy :: "real \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "entropy b S X = - KL_divergence b S (distr M S X)"

abbreviation (in information_space)
  entropy_Pow ("\<H>'(_')") where
  "\<H>(X) \<equiv> entropy b (count_space (X`space M)) X"

lemma (in prob_space) distributed_RN_deriv:
  assumes X: "distributed M S X Px"
  shows "AE x in S. RN_deriv S (density S Px) x = Px x"
proof -
  note D = distributed_measurable[OF X] distributed_borel_measurable[OF X] distributed_AE[OF X]
  interpret X: prob_space "distr M S X"
    using D(1) by (rule prob_space_distr)

  have sf: "sigma_finite_measure (distr M S X)" by default
  show ?thesis
    using D
    apply (subst eq_commute)
    apply (intro RN_deriv_unique_sigma_finite)
    apply (auto intro: divide_nonneg_nonneg measure_nonneg
             simp: distributed_distr_eq_density[symmetric, OF X] sf)
    done
qed

lemma (in information_space)
  fixes X :: "'a \<Rightarrow> 'b"
  assumes X: "distributed M MX X f"
  shows entropy_distr: "entropy b MX X = - (\<integral>x. f x * log b (f x) \<partial>MX)" (is ?eq)
proof -
  note D = distributed_measurable[OF X] distributed_borel_measurable[OF X] distributed_AE[OF X]
  note ae = distributed_RN_deriv[OF X]

  have ae_eq: "AE x in distr M MX X. log b (real (RN_deriv MX (distr M MX X) x)) =
    log b (f x)"
    unfolding distributed_distr_eq_density[OF X]
    apply (subst AE_density)
    using D apply simp
    using ae apply eventually_elim
    apply auto
    done

  have int_eq: "- (\<integral> x. log b (f x) \<partial>distr M MX X) = - (\<integral> x. f x * log b (f x) \<partial>MX)"
    unfolding distributed_distr_eq_density[OF X]
    using D
    by (subst integral_density)
       (auto simp: borel_measurable_ereal_iff)

  show ?eq
    unfolding entropy_def KL_divergence_def entropy_density_def comp_def
    apply (subst integral_cong_AE)
    apply (rule ae_eq)
    apply (rule int_eq)
    done
qed

lemma (in prob_space) distributed_imp_emeasure_nonzero:
  assumes X: "distributed M MX X Px"
  shows "emeasure MX {x \<in> space MX. Px x \<noteq> 0} \<noteq> 0"
proof
  note Px = distributed_borel_measurable[OF X] distributed_AE[OF X]
  interpret X: prob_space "distr M MX X"
    using distributed_measurable[OF X] by (rule prob_space_distr)

  assume "emeasure MX {x \<in> space MX. Px x \<noteq> 0} = 0"
  with Px have "AE x in MX. Px x = 0"
    by (intro AE_I[OF subset_refl]) (auto simp: borel_measurable_ereal_iff)
  moreover
  from X.emeasure_space_1 have "(\<integral>\<^isup>+x. Px x \<partial>MX) = 1"
    unfolding distributed_distr_eq_density[OF X] using Px
    by (subst (asm) emeasure_density)
       (auto simp: borel_measurable_ereal_iff intro!: integral_cong cong: positive_integral_cong)
  ultimately show False
    by (simp add: positive_integral_cong_AE)
qed

lemma (in information_space) entropy_le:
  fixes Px :: "'b \<Rightarrow> real" and MX :: "'b measure"
  assumes X: "distributed M MX X Px"
  and fin: "emeasure MX {x \<in> space MX. Px x \<noteq> 0} \<noteq> \<infinity>"
  and int: "integrable MX (\<lambda>x. - Px x * log b (Px x))"
  shows "entropy b MX X \<le> log b (measure MX {x \<in> space MX. Px x \<noteq> 0})"
proof -
  note Px = distributed_borel_measurable[OF X] distributed_AE[OF X]
  interpret X: prob_space "distr M MX X"
    using distributed_measurable[OF X] by (rule prob_space_distr)

  have " - log b (measure MX {x \<in> space MX. Px x \<noteq> 0}) = 
    - log b (\<integral> x. indicator {x \<in> space MX. Px x \<noteq> 0} x \<partial>MX)"
    using Px fin
    by (subst integral_indicator) (auto simp: measure_def borel_measurable_ereal_iff)
  also have "- log b (\<integral> x. indicator {x \<in> space MX. Px x \<noteq> 0} x \<partial>MX) = - log b (\<integral> x. 1 / Px x \<partial>distr M MX X)"
    unfolding distributed_distr_eq_density[OF X] using Px
    apply (intro arg_cong[where f="log b"] arg_cong[where f=uminus])
    by (subst integral_density) (auto simp: borel_measurable_ereal_iff intro!: integral_cong)
  also have "\<dots> \<le> (\<integral> x. - log b (1 / Px x) \<partial>distr M MX X)"
  proof (rule X.jensens_inequality[of "\<lambda>x. 1 / Px x" "{0<..}" 0 1 "\<lambda>x. - log b x"])
    show "AE x in distr M MX X. 1 / Px x \<in> {0<..}"
      unfolding distributed_distr_eq_density[OF X]
      using Px by (auto simp: AE_density)
    have [simp]: "\<And>x. x \<in> space MX \<Longrightarrow> ereal (if Px x = 0 then 0 else 1) = indicator {x \<in> space MX. Px x \<noteq> 0} x"
      by (auto simp: one_ereal_def)
    have "(\<integral>\<^isup>+ x. max 0 (ereal (- (if Px x = 0 then 0 else 1))) \<partial>MX) = (\<integral>\<^isup>+ x. 0 \<partial>MX)"
      by (intro positive_integral_cong) (auto split: split_max)
    then show "integrable (distr M MX X) (\<lambda>x. 1 / Px x)"
      unfolding distributed_distr_eq_density[OF X] using Px
      by (auto simp: positive_integral_density integrable_def borel_measurable_ereal_iff fin positive_integral_max_0
              cong: positive_integral_cong)
    have "integrable MX (\<lambda>x. Px x * log b (1 / Px x)) =
      integrable MX (\<lambda>x. - Px x * log b (Px x))"
      using Px
      by (intro integrable_cong_AE)
         (auto simp: borel_measurable_ereal_iff log_divide_eq
                  intro!: measurable_If)
    then show "integrable (distr M MX X) (\<lambda>x. - log b (1 / Px x))"
      unfolding distributed_distr_eq_density[OF X]
      using Px int
      by (subst integral_density) (auto simp: borel_measurable_ereal_iff)
  qed (auto simp: minus_log_convex[OF b_gt_1])
  also have "\<dots> = (\<integral> x. log b (Px x) \<partial>distr M MX X)"
    unfolding distributed_distr_eq_density[OF X] using Px
    by (intro integral_cong_AE) (auto simp: AE_density log_divide_eq)
  also have "\<dots> = - entropy b MX X"
    unfolding distributed_distr_eq_density[OF X] using Px
    by (subst entropy_distr[OF X]) (auto simp: borel_measurable_ereal_iff integral_density)
  finally show ?thesis
    by simp
qed

lemma (in information_space) entropy_le_space:
  fixes Px :: "'b \<Rightarrow> real" and MX :: "'b measure"
  assumes X: "distributed M MX X Px"
  and fin: "finite_measure MX"
  and int: "integrable MX (\<lambda>x. - Px x * log b (Px x))"
  shows "entropy b MX X \<le> log b (measure MX (space MX))"
proof -
  note Px = distributed_borel_measurable[OF X] distributed_AE[OF X]
  interpret finite_measure MX by fact
  have "entropy b MX X \<le> log b (measure MX {x \<in> space MX. Px x \<noteq> 0})"
    using int X by (intro entropy_le) auto
  also have "\<dots> \<le> log b (measure MX (space MX))"
    using Px distributed_imp_emeasure_nonzero[OF X]
    by (intro log_le)
       (auto intro!: borel_measurable_ereal_iff finite_measure_mono b_gt_1
                     less_le[THEN iffD2] measure_nonneg simp: emeasure_eq_measure)
  finally show ?thesis .
qed

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
      by (simp add: emeasure_density zero_ereal_def[symmetric])
  qed
  with measure_notin_sets[of A MX] show "A \<in> sets MX"
    by blast
qed

lemma (in information_space) entropy_uniform:
  assumes X: "distributed M MX X (\<lambda>x. indicator A x / measure MX A)" (is "distributed _ _ _ ?f")
  shows "entropy b MX X = log b (measure MX A)"
proof (subst entropy_distr[OF X])
  have [simp]: "emeasure MX A \<noteq> \<infinity>"
    using uniform_distributed_params[OF X] by (auto simp add: measure_def)
  have eq: "(\<integral> x. indicator A x / measure MX A * log b (indicator A x / measure MX A) \<partial>MX) =
    (\<integral> x. (- log b (measure MX A) / measure MX A) * indicator A x \<partial>MX)"
    using measure_nonneg[of MX A] uniform_distributed_params[OF X]
    by (auto intro!: integral_cong split: split_indicator simp: log_divide_eq)
  show "- (\<integral> x. indicator A x / measure MX A * log b (indicator A x / measure MX A) \<partial>MX) =
    log b (measure MX A)"
    unfolding eq using uniform_distributed_params[OF X]
    by (subst lebesgue_integral_cmult) (auto simp: measure_def)
qed

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
       (simp_all add: simple_distributed_finite[OF X] subset_eq integrable_count_space emeasure_count_space)
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
       (simp_all add: simple_distributed_finite[OF X] subset_eq integrable_count_space emeasure_count_space finite_measure_count_space)
  also have "measure ?X (space ?X) = card (X ` space M)"
    by (simp_all add: simple_distributed_finite[OF X] subset_eq emeasure_count_space measure_def)
  finally show ?thesis .
qed

subsection {* Conditional Mutual Information *}

definition (in prob_space)
  "conditional_mutual_information b MX MY MZ X Y Z \<equiv>
    mutual_information b MX (MY \<Otimes>\<^isub>M MZ) X (\<lambda>x. (Y x, Z x)) -
    mutual_information b MX MZ X Z"

abbreviation (in information_space)
  conditional_mutual_information_Pow ("\<I>'( _ ; _ | _ ')") where
  "\<I>(X ; Y | Z) \<equiv> conditional_mutual_information b
    (count_space (X ` space M)) (count_space (Y ` space M)) (count_space (Z ` space M)) X Y Z"

lemma (in pair_sigma_finite) borel_measurable_positive_integral_fst:
  "(\<lambda>(x, y). f x y) \<in> borel_measurable (M1 \<Otimes>\<^isub>M M2) \<Longrightarrow> (\<lambda>x. \<integral>\<^isup>+ y. f x y \<partial>M2) \<in> borel_measurable M1"
  using positive_integral_fst_measurable(1)[of "\<lambda>(x, y). f x y"] by simp

lemma (in pair_sigma_finite) borel_measurable_positive_integral_snd:
  assumes "(\<lambda>(x, y). f x y) \<in> borel_measurable (M2 \<Otimes>\<^isub>M M1)" shows "(\<lambda>x. \<integral>\<^isup>+ y. f x y \<partial>M1) \<in> borel_measurable M2"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  from Q.borel_measurable_positive_integral_fst assms show ?thesis by simp
qed

lemma (in information_space)
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T" and P: "sigma_finite_measure P"
  assumes Px: "distributed M S X Px"
  assumes Pz: "distributed M P Z Pz"
  assumes Pyz: "distributed M (T \<Otimes>\<^isub>M P) (\<lambda>x. (Y x, Z x)) Pyz"
  assumes Pxz: "distributed M (S \<Otimes>\<^isub>M P) (\<lambda>x. (X x, Z x)) Pxz"
  assumes Pxyz: "distributed M (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>x. (X x, Y x, Z x)) Pxyz"
  assumes I1: "integrable (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Px x * Pyz (y, z))))"
  assumes I2: "integrable (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxz (x, z) / (Px x * Pz z)))"
  shows conditional_mutual_information_generic_eq: "conditional_mutual_information b S T P X Y Z
    = (\<integral>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))) \<partial>(S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P))" (is "?eq")
    and conditional_mutual_information_generic_nonneg: "0 \<le> conditional_mutual_information b S T P X Y Z" (is "?nonneg")
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret P: sigma_finite_measure P by fact
  interpret TP: pair_sigma_finite T P ..
  interpret SP: pair_sigma_finite S P ..
  interpret ST: pair_sigma_finite S T ..
  interpret SPT: pair_sigma_finite "S \<Otimes>\<^isub>M P" T ..
  interpret STP: pair_sigma_finite S "T \<Otimes>\<^isub>M P" ..
  interpret TPS: pair_sigma_finite "T \<Otimes>\<^isub>M P" S ..
  have TP: "sigma_finite_measure (T \<Otimes>\<^isub>M P)" ..
  have SP: "sigma_finite_measure (S \<Otimes>\<^isub>M P)" ..
  have YZ: "random_variable (T \<Otimes>\<^isub>M P) (\<lambda>x. (Y x, Z x))"
    using Pyz by (simp add: distributed_measurable)

  have Pxyz_f: "\<And>M f. f \<in> measurable M (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) \<Longrightarrow> (\<lambda>x. Pxyz (f x)) \<in> borel_measurable M"
    using measurable_comp[OF _ Pxyz[THEN distributed_real_measurable]] by (auto simp: comp_def)

  { fix f g h M
    assume f: "f \<in> measurable M S" and g: "g \<in> measurable M P" and h: "h \<in> measurable M (S \<Otimes>\<^isub>M P)"
    from measurable_comp[OF h Pxz[THEN distributed_real_measurable]]
         measurable_comp[OF f Px[THEN distributed_real_measurable]]
         measurable_comp[OF g Pz[THEN distributed_real_measurable]]
    have "(\<lambda>x. log b (Pxz (h x) / (Px (f x) * Pz (g x)))) \<in> borel_measurable M"
      by (simp add: comp_def b_gt_1) }
  note borel_log = this

  have measurable_cut: "(\<lambda>(x, y, z). (x, z)) \<in> measurable (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (S \<Otimes>\<^isub>M P)"
    by (auto simp add: split_beta' comp_def intro!: measurable_Pair measurable_snd')
  
  from Pxz Pxyz have distr_eq: "distr M (S \<Otimes>\<^isub>M P) (\<lambda>x. (X x, Z x)) =
    distr (distr M (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>x. (X x, Y x, Z x))) (S \<Otimes>\<^isub>M P) (\<lambda>(x, y, z). (x, z))"
    by (subst distr_distr[OF measurable_cut]) (auto dest: distributed_measurable simp: comp_def)

  have "mutual_information b S P X Z =
    (\<integral>x. Pxz x * log b (Pxz x / (Px (fst x) * Pz (snd x))) \<partial>(S \<Otimes>\<^isub>M P))"
    by (rule mutual_information_distr[OF S P Px Pz Pxz])
  also have "\<dots> = (\<integral>(x,y,z). Pxyz (x,y,z) * log b (Pxz (x,z) / (Px x * Pz z)) \<partial>(S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P))"
    using b_gt_1 Pxz Px Pz
    by (subst distributed_transform_integral[OF Pxyz Pxz, where T="\<lambda>(x, y, z). (x, z)"])
       (auto simp: split_beta' intro!: measurable_Pair measurable_snd' measurable_snd'' measurable_fst'' borel_measurable_times
             dest!: distributed_real_measurable)
  finally have mi_eq:
    "mutual_information b S P X Z = (\<integral>(x,y,z). Pxyz (x,y,z) * log b (Pxz (x,z) / (Px x * Pz z)) \<partial>(S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P))" .
  
  have ae1: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Px (fst x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of fst, OF _ Pxyz Px]) auto
  moreover have ae2: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pz (snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of "\<lambda>x. snd (snd x)", OF _ Pxyz Pz]) (auto intro: measurable_snd')
  moreover have ae3: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pxz (fst x, snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of "\<lambda>x. (fst x, snd (snd x))", OF _ Pxyz Pxz]) (auto intro: measurable_Pair measurable_snd')
  moreover have ae4: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pyz (snd x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of snd, OF _ Pxyz Pyz]) (auto intro: measurable_Pair)
  moreover have ae5: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Px (fst x)"
    using Px by (intro STP.AE_pair_measure) (auto simp: comp_def intro!: measurable_fst'' dest: distributed_real_AE distributed_real_measurable)
  moreover have ae6: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Pyz (snd x)"
    using Pyz by (intro STP.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'' dest: distributed_real_AE distributed_real_measurable)
  moreover have ae7: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Pz (snd (snd x))"
    using Pz Pz[THEN distributed_real_measurable] by (auto intro!: measurable_snd'' TP.AE_pair_measure STP.AE_pair_measure AE_I2[of S] dest: distributed_real_AE)
  moreover have ae8: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Pxz (fst x, snd (snd x))"
    using Pxz[THEN distributed_real_AE, THEN SP.AE_pair]
    using measurable_comp[OF measurable_Pair[OF measurable_fst measurable_comp[OF measurable_snd measurable_snd]] Pxz[THEN distributed_real_measurable], of T]
    using measurable_comp[OF measurable_snd measurable_Pair2[OF Pxz[THEN distributed_real_measurable]], of _ T]
    by (auto intro!: TP.AE_pair_measure STP.AE_pair_measure simp: comp_def)
  moreover note Pxyz[THEN distributed_real_AE]
  ultimately have ae: "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P.
    Pxyz x * log b (Pxyz x / (Px (fst x) * Pyz (snd x))) -
    Pxyz x * log b (Pxz (fst x, snd (snd x)) / (Px (fst x) * Pz (snd (snd x)))) =
    Pxyz x * log b (Pxyz x * Pz (snd (snd x)) / (Pxz (fst x, snd (snd x)) * Pyz (snd x))) "
  proof eventually_elim
    case (goal1 x)
    show ?case
    proof cases
      assume "Pxyz x \<noteq> 0"
      with goal1 have "0 < Px (fst x)" "0 < Pz (snd (snd x))" "0 < Pxz (fst x, snd (snd x))" "0 < Pyz (snd x)" "0 < Pxyz x"
        by auto
      then show ?thesis
        using b_gt_1 by (simp add: log_simps mult_pos_pos less_imp_le field_simps)
    qed simp
  qed
  with I1 I2 show ?eq
    unfolding conditional_mutual_information_def
    apply (subst mi_eq)
    apply (subst mutual_information_distr[OF S TP Px Pyz Pxyz])
    apply (subst integral_diff(2)[symmetric])
    apply (auto intro!: integral_cong_AE simp: split_beta' simp del: integral_diff)
    done

  let ?P = "density (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) Pxyz"
  interpret P: prob_space ?P
    unfolding distributed_distr_eq_density[OF Pxyz, symmetric]
    using distributed_measurable[OF Pxyz] by (rule prob_space_distr)

  let ?Q = "density (T \<Otimes>\<^isub>M P) Pyz"
  interpret Q: prob_space ?Q
    unfolding distributed_distr_eq_density[OF Pyz, symmetric]
    using distributed_measurable[OF Pyz] by (rule prob_space_distr)

  let ?f = "\<lambda>(x, y, z). Pxz (x, z) * (Pyz (y, z) / Pz z) / Pxyz (x, y, z)"

  from subdensity_real[of snd, OF _ Pyz Pz]
  have aeX1: "AE x in T \<Otimes>\<^isub>M P. Pz (snd x) = 0 \<longrightarrow> Pyz x = 0" by (auto simp: comp_def)
  have aeX2: "AE x in T \<Otimes>\<^isub>M P. 0 \<le> Pz (snd x)"
    using Pz by (intro TP.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'' dest: distributed_real_AE distributed_real_measurable)

  have aeX3: "AE y in T \<Otimes>\<^isub>M P. (\<integral>\<^isup>+ x. ereal (Pxz (x, snd y)) \<partial>S) = ereal (Pz (snd y))"
    using Pz distributed_marginal_eq_joint2[OF P S Pz Pxz]
    apply (intro TP.AE_pair_measure)
    apply (auto simp: comp_def measurable_split_conv
                intro!: measurable_snd'' borel_measurable_ereal_eq borel_measurable_ereal
                        SP.borel_measurable_positive_integral_snd measurable_compose[OF _ Pxz[THEN distributed_real_measurable]]
                        measurable_Pair
                dest: distributed_real_AE distributed_real_measurable)
    done

  note M = borel_measurable_divide borel_measurable_diff borel_measurable_times borel_measurable_ereal
           measurable_compose[OF _ measurable_snd]
           measurable_Pair
           measurable_compose[OF _ Pxyz[THEN distributed_real_measurable]]
           measurable_compose[OF _ Pxz[THEN distributed_real_measurable]]
           measurable_compose[OF _ Pyz[THEN distributed_real_measurable]]
           measurable_compose[OF _ Pz[THEN distributed_real_measurable]]
           measurable_compose[OF _ Px[THEN distributed_real_measurable]]
           STP.borel_measurable_positive_integral_snd
  have "(\<integral>\<^isup>+ x. ?f x \<partial>?P) \<le> (\<integral>\<^isup>+ (x, y, z). Pxz (x, z) * (Pyz (y, z) / Pz z) \<partial>(S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P))"
    apply (subst positive_integral_density)
    apply (rule distributed_borel_measurable[OF Pxyz])
    apply (rule distributed_AE[OF Pxyz])
    apply (auto simp add: borel_measurable_ereal_iff split_beta' intro!: M) []
    apply (rule positive_integral_mono_AE)
    using ae5 ae6 ae7 ae8
    apply eventually_elim
    apply (auto intro!: divide_nonneg_nonneg mult_nonneg_nonneg)
    done
  also have "\<dots> = (\<integral>\<^isup>+(y, z). \<integral>\<^isup>+ x. ereal (Pxz (x, z)) * ereal (Pyz (y, z) / Pz z) \<partial>S \<partial>T \<Otimes>\<^isub>M P)"
    by (subst STP.positive_integral_snd_measurable[symmetric])
       (auto simp add: borel_measurable_ereal_iff split_beta' intro!: M)
  also have "\<dots> = (\<integral>\<^isup>+x. ereal (Pyz x) * 1 \<partial>T \<Otimes>\<^isub>M P)"
    apply (rule positive_integral_cong_AE)
    using aeX1 aeX2 aeX3 distributed_AE[OF Pyz] AE_space
    apply eventually_elim
  proof (case_tac x, simp del: times_ereal.simps add: space_pair_measure)
    fix a b assume "Pz b = 0 \<longrightarrow> Pyz (a, b) = 0" "0 \<le> Pz b" "a \<in> space T \<and> b \<in> space P"
      "(\<integral>\<^isup>+ x. ereal (Pxz (x, b)) \<partial>S) = ereal (Pz b)" "0 \<le> Pyz (a, b)" 
    then show "(\<integral>\<^isup>+ x. ereal (Pxz (x, b)) * ereal (Pyz (a, b) / Pz b) \<partial>S) = ereal (Pyz (a, b))"
      apply (subst positive_integral_multc)
      apply (auto intro!: borel_measurable_ereal divide_nonneg_nonneg
                          measurable_compose[OF _ Pxz[THEN distributed_real_measurable]] measurable_Pair
                  split: prod.split)
      done
  qed
  also have "\<dots> = 1"
    using Q.emeasure_space_1 distributed_AE[OF Pyz] distributed_distr_eq_density[OF Pyz]
    by (subst positive_integral_density[symmetric]) (auto intro!: M)
  finally have le1: "(\<integral>\<^isup>+ x. ?f x \<partial>?P) \<le> 1" .
  also have "\<dots> < \<infinity>" by simp
  finally have fin: "(\<integral>\<^isup>+ x. ?f x \<partial>?P) \<noteq> \<infinity>" by simp

  have pos: "(\<integral>\<^isup>+ x. ?f x \<partial>?P) \<noteq> 0"
    apply (subst positive_integral_density)
    apply (rule distributed_borel_measurable[OF Pxyz])
    apply (rule distributed_AE[OF Pxyz])
    apply (auto simp add: borel_measurable_ereal_iff split_beta' intro!: M) []
    apply (simp add: split_beta')
  proof
    let ?g = "\<lambda>x. ereal (if Pxyz x = 0 then 0 else Pxz (fst x, snd (snd x)) * Pyz (snd x) / Pz (snd (snd x)))"
    assume "(\<integral>\<^isup>+ x. ?g x \<partial>(S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P)) = 0"
    then have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. ?g x \<le> 0"
      by (intro positive_integral_0_iff_AE[THEN iffD1]) (auto intro!: M borel_measurable_ereal measurable_If)
    then have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pxyz x = 0"
      using ae1 ae2 ae3 ae4 ae5 ae6 ae7 ae8 Pxyz[THEN distributed_real_AE]
      by eventually_elim (auto split: split_if_asm simp: mult_le_0_iff divide_le_0_iff)
    then have "(\<integral>\<^isup>+ x. ereal (Pxyz x) \<partial>S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) = 0"
      by (subst positive_integral_cong_AE[of _ "\<lambda>x. 0"]) auto
    with P.emeasure_space_1 show False
      by (subst (asm) emeasure_density) (auto intro!: M cong: positive_integral_cong)
  qed

  have neg: "(\<integral>\<^isup>+ x. - ?f x \<partial>?P) = 0"
    apply (rule positive_integral_0_iff_AE[THEN iffD2])
    apply (auto intro!: M simp: split_beta') []
    apply (subst AE_density)
    apply (auto intro!: M simp: split_beta') []
    using ae5 ae6 ae7 ae8
    apply eventually_elim
    apply (auto intro!: mult_nonneg_nonneg divide_nonneg_nonneg)
    done

  have I3: "integrable (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))))"
    apply (rule integrable_cong_AE[THEN iffD1, OF _ _ _ integral_diff(1)[OF I1 I2]])
    using ae
    apply (auto intro!: M simp: split_beta')
    done

  have "- log b 1 \<le> - log b (integral\<^isup>L ?P ?f)"
  proof (intro le_imp_neg_le log_le[OF b_gt_1])
    show "0 < integral\<^isup>L ?P ?f"
      using neg pos fin positive_integral_positive[of ?P ?f]
      by (cases "(\<integral>\<^isup>+ x. ?f x \<partial>?P)") (auto simp add: lebesgue_integral_def less_le split_beta')
    show "integral\<^isup>L ?P ?f \<le> 1"
      using neg le1 fin positive_integral_positive[of ?P ?f]
      by (cases "(\<integral>\<^isup>+ x. ?f x \<partial>?P)") (auto simp add: lebesgue_integral_def split_beta' one_ereal_def)
  qed
  also have "- log b (integral\<^isup>L ?P ?f) \<le> (\<integral> x. - log b (?f x) \<partial>?P)"
  proof (rule P.jensens_inequality[where a=0 and b=1 and I="{0<..}"])
    show "AE x in ?P. ?f x \<in> {0<..}"
      unfolding AE_density[OF distributed_borel_measurable[OF Pxyz]]
      using ae1 ae2 ae3 ae4 ae5 ae6 ae7 ae8 Pxyz[THEN distributed_real_AE]
      by eventually_elim (auto simp: divide_pos_pos mult_pos_pos)
    show "integrable ?P ?f"
      unfolding integrable_def 
      using fin neg by (auto intro!: M simp: split_beta')
    show "integrable ?P (\<lambda>x. - log b (?f x))"
      apply (subst integral_density)
      apply (auto intro!: M) []
      apply (auto intro!: M distributed_real_AE[OF Pxyz]) []
      apply (auto intro!: M borel_measurable_uminus borel_measurable_log simp: split_beta') []
      apply (rule integrable_cong_AE[THEN iffD1, OF _ _ _ I3])
      apply (auto intro!: M borel_measurable_uminus borel_measurable_log simp: split_beta') []
      apply (auto intro!: M borel_measurable_uminus borel_measurable_log simp: split_beta') []
      using ae1 ae2 ae3 ae4 ae5 ae6 ae7 ae8 Pxyz[THEN distributed_real_AE]
      apply eventually_elim
      apply (auto simp: log_divide_eq log_mult_eq zero_le_mult_iff zero_less_mult_iff zero_less_divide_iff field_simps)
      done
  qed (auto simp: b_gt_1 minus_log_convex)
  also have "\<dots> = conditional_mutual_information b S T P X Y Z"
    unfolding `?eq`
    apply (subst integral_density)
    apply (auto intro!: M) []
    apply (auto intro!: M distributed_real_AE[OF Pxyz]) []
    apply (auto intro!: M borel_measurable_uminus borel_measurable_log simp: split_beta') []
    apply (intro integral_cong_AE)
    using ae1 ae2 ae3 ae4 ae5 ae6 ae7 ae8 Pxyz[THEN distributed_real_AE]
    apply eventually_elim
    apply (auto simp: log_divide_eq zero_less_mult_iff zero_less_divide_iff field_simps)
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
proof (subst conditional_mutual_information_generic_eq[OF _ _ _ _
    simple_distributed[OF Pz] simple_distributed_joint[OF Pyz] simple_distributed_joint[OF Pxz]
    simple_distributed_joint2[OF Pxyz]])
  note simple_distributed_joint2_finite[OF Pxyz, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Z ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  have "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) \<Otimes>\<^isub>M count_space (Z ` space M) =
      count_space (X`space M \<times> Y`space M \<times> Z`space M)"
    (is "?P = ?C")
    by (simp add: pair_measure_count_space)

  let ?Px = "\<lambda>x. measure M (X -` {x} \<inter> space M)"
  have "(\<lambda>x. (X x, Z x)) \<in> measurable M (count_space (X ` space M) \<Otimes>\<^isub>M count_space (Z ` space M))"
    using simple_distributed_joint[OF Pxz] by (rule distributed_measurable)
  from measurable_comp[OF this measurable_fst]
  have "random_variable (count_space (X ` space M)) X"
    by (simp add: comp_def)
  then have "simple_function M X"    
    unfolding simple_function_def by auto
  then have "simple_distributed M X ?Px"
    by (rule simple_distributedI) auto
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
    by (auto intro!: setsum_cong simp add: `?P = ?C` lebesgue_integral_count_space_finite simple_distributed_finite setsum_cases split_beta')
qed

lemma (in information_space) conditional_mutual_information_nonneg:
  assumes X: "simple_function M X" and Y: "simple_function M Y" and Z: "simple_function M Z"
  shows "0 \<le> \<I>(X ; Y | Z)"
proof -
  have [simp]: "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) \<Otimes>\<^isub>M count_space (Z ` space M) =
      count_space (X`space M \<times> Y`space M \<times> Z`space M)"
    by (simp add: pair_measure_count_space X Y Z simple_functionD)
  note sf = sigma_finite_measure_count_space_finite[OF simple_functionD(1)]
  note sd = simple_distributedI[OF _ refl]
  note sp = simple_function_Pair
  show ?thesis
   apply (rule conditional_mutual_information_generic_nonneg[OF sf[OF X] sf[OF Y] sf[OF Z]])
   apply (rule simple_distributed[OF sd[OF X]])
   apply (rule simple_distributed[OF sd[OF Z]])
   apply (rule simple_distributed_joint[OF sd[OF sp[OF Y Z]]])
   apply (rule simple_distributed_joint[OF sd[OF sp[OF X Z]]])
   apply (rule simple_distributed_joint2[OF sd[OF sp[OF X sp[OF Y Z]]]])
   apply (auto intro!: integrable_count_space simp: X Y Z simple_functionD)
   done
qed

subsection {* Conditional Entropy *}

definition (in prob_space)
  "conditional_entropy b S T X Y = - (\<integral>(x, y). log b (real (RN_deriv (S \<Otimes>\<^isub>M T) (distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))) (x, y)) / 
    real (RN_deriv T (distr M T Y) y)) \<partial>distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)))"

abbreviation (in information_space)
  conditional_entropy_Pow ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> conditional_entropy b (count_space (X`space M)) (count_space (Y`space M)) X Y"

lemma (in information_space) conditional_entropy_generic_eq:
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  shows "conditional_entropy b S T X Y = - (\<integral>(x, y). Pxy (x, y) * log b (Pxy (x, y) / Py y) \<partial>(S \<Otimes>\<^isub>M T))"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  have "AE x in density (S \<Otimes>\<^isub>M T) (\<lambda>x. ereal (Pxy x)). Pxy x = real (RN_deriv (S \<Otimes>\<^isub>M T) (distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))) x)"
    unfolding AE_density[OF distributed_borel_measurable, OF Pxy]
    unfolding distributed_distr_eq_density[OF Pxy]
    using distributed_RN_deriv[OF Pxy]
    by auto
  moreover
  have "AE x in density (S \<Otimes>\<^isub>M T) (\<lambda>x. ereal (Pxy x)). Py (snd x) = real (RN_deriv T (distr M T Y) (snd x))"
    unfolding AE_density[OF distributed_borel_measurable, OF Pxy]
    unfolding distributed_distr_eq_density[OF Py]
    apply (rule ST.AE_pair_measure)
    apply (auto intro!: sets_Collect borel_measurable_eq measurable_compose[OF _ distributed_real_measurable[OF Py]]
                        distributed_real_measurable[OF Pxy] distributed_real_AE[OF Py]
                        borel_measurable_real_of_ereal measurable_compose[OF _ borel_measurable_RN_deriv_density])
    using distributed_RN_deriv[OF Py]
    apply auto
    done    
  ultimately
  have "conditional_entropy b S T X Y = - (\<integral>x. Pxy x * log b (Pxy x / Py (snd x)) \<partial>(S \<Otimes>\<^isub>M T))"
    unfolding conditional_entropy_def neg_equal_iff_equal
    apply (subst integral_density(1)[symmetric])
    apply (auto simp: distributed_real_measurable[OF Pxy] distributed_real_AE[OF Pxy]
                      measurable_compose[OF _ distributed_real_measurable[OF Py]]
                      distributed_distr_eq_density[OF Pxy]
                intro!: integral_cong_AE)
    done
  then show ?thesis by (simp add: split_beta')
qed

lemma (in information_space) conditional_entropy_eq_entropy:
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  assumes I1: "integrable (S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Pxy x))"
  assumes I2: "integrable (S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Py (snd x)))"
  shows "conditional_entropy b S T X Y = entropy b (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) - entropy b T Y"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..

  have "entropy b T Y = - (\<integral>y. Py y * log b (Py y) \<partial>T)"
    by (rule entropy_distr[OF Py])
  also have "\<dots> = - (\<integral>(x,y). Pxy (x,y) * log b (Py y) \<partial>(S \<Otimes>\<^isub>M T))"
    using b_gt_1 Py[THEN distributed_real_measurable]
    by (subst distributed_transform_integral[OF Pxy Py, where T=snd]) (auto intro!: integral_cong)
  finally have e_eq: "entropy b T Y = - (\<integral>(x,y). Pxy (x,y) * log b (Py y) \<partial>(S \<Otimes>\<^isub>M T))" .

  have ae2: "AE x in S \<Otimes>\<^isub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of snd, OF _ Pxy Py]) (auto intro: measurable_Pair)
  moreover have ae4: "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Py (snd x)"
    using Py by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'' dest: distributed_real_AE distributed_real_measurable)
  moreover note ae5 = Pxy[THEN distributed_real_AE]
  ultimately have "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Pxy x \<and> 0 \<le> Py (snd x) \<and>
    (Pxy x = 0 \<or> (Pxy x \<noteq> 0 \<longrightarrow> 0 < Pxy x \<and> 0 < Py (snd x)))"
    by eventually_elim auto
  then have ae: "AE x in S \<Otimes>\<^isub>M T.
     Pxy x * log b (Pxy x) - Pxy x * log b (Py (snd x)) = Pxy x * log b (Pxy x / Py (snd x))"
    by eventually_elim (auto simp: log_simps mult_pos_pos field_simps b_gt_1)
  have "conditional_entropy b S T X Y = 
    - (\<integral>x. Pxy x * log b (Pxy x) - Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^isub>M T))"
    unfolding conditional_entropy_generic_eq[OF S T Py Pxy] neg_equal_iff_equal
    apply (intro integral_cong_AE)
    using ae
    apply eventually_elim
    apply auto
    done
  also have "\<dots> = - (\<integral>x. Pxy x * log b (Pxy x) \<partial>(S \<Otimes>\<^isub>M T)) - - (\<integral>x.  Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^isub>M T))"
    by (simp add: integral_diff[OF I1 I2])
  finally show ?thesis 
    unfolding conditional_entropy_generic_eq[OF S T Py Pxy] entropy_distr[OF Pxy] e_eq
    by (simp add: split_beta')
qed

lemma (in information_space) conditional_entropy_eq_entropy_simple:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<H>(X | Y) = entropy b (count_space (X`space M) \<Otimes>\<^isub>M count_space (Y`space M)) (\<lambda>x. (X x, Y x)) - \<H>(Y)"
proof -
  have "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) = count_space (X`space M \<times> Y`space M)"
    (is "?P = ?C") using X Y by (simp add: simple_functionD pair_measure_count_space)
  show ?thesis
    by (rule conditional_entropy_eq_entropy sigma_finite_measure_count_space_finite
                 simple_functionD  X Y simple_distributed simple_distributedI[OF _ refl]
                 simple_distributed_joint simple_function_Pair integrable_count_space)+
       (auto simp: `?P = ?C` intro!: integrable_count_space simple_functionD  X Y)
qed

lemma (in information_space) conditional_entropy_eq:
  assumes Y: "simple_distributed M Y Py"
  assumes XY: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
    shows "\<H>(X | Y) = - (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / Py y))"
proof (subst conditional_entropy_generic_eq[OF _ _
  simple_distributed[OF Y] simple_distributed_joint[OF XY]])
  have "finite ((\<lambda>x. (X x, Y x))`space M)"
    using XY unfolding simple_distributed_def by auto
  from finite_imageI[OF this, of fst]
  have [simp]: "finite (X`space M)"
    by (simp add: image_compose[symmetric] comp_def)
  note Y[THEN simple_distributed_finite, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  let ?f = "(\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x else 0)"
  have "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) = count_space (X`space M \<times> Y`space M)"
    (is "?P = ?C")
    using Y by (simp add: simple_distributed_finite pair_measure_count_space)
  have eq: "(\<lambda>(x, y). ?f (x, y) * log b (?f (x, y) / Py y)) =
    (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x * log b (Pxy x / Py (snd x)) else 0)"
    by auto
  from Y show "- (\<integral> (x, y). ?f (x, y) * log b (?f (x, y) / Py y) \<partial>?P) =
    - (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / Py y))"
    by (auto intro!: setsum_cong simp add: `?P = ?C` lebesgue_integral_count_space_finite simple_distributed_finite eq setsum_cases split_beta')
qed

lemma (in information_space) conditional_mutual_information_eq_conditional_entropy:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<I>(X ; X | Y) = \<H>(X | Y)"
proof -
  def Py \<equiv> "\<lambda>x. if x \<in> Y`space M then measure M (Y -` {x} \<inter> space M) else 0"
  def Pxy \<equiv> "\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x))`space M then measure M ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M) else 0"
  def Pxxy \<equiv> "\<lambda>x. if x \<in> (\<lambda>x. (X x, X x, Y x))`space M then measure M ((\<lambda>x. (X x, X x, Y x)) -` {x} \<inter> space M) else 0"
  let ?M = "X`space M \<times> X`space M \<times> Y`space M"

  note XY = simple_function_Pair[OF X Y]
  note XXY = simple_function_Pair[OF X XY]
  have Py: "simple_distributed M Y Py"
    using Y by (rule simple_distributedI) (auto simp: Py_def)
  have Pxy: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
    using XY by (rule simple_distributedI) (auto simp: Pxy_def)
  have Pxxy: "simple_distributed M (\<lambda>x. (X x, X x, Y x)) Pxxy"
    using XXY by (rule simple_distributedI) (auto simp: Pxxy_def)
  have eq: "(\<lambda>x. (X x, X x, Y x)) ` space M = (\<lambda>(x, y). (x, x, y)) ` (\<lambda>x. (X x, Y x)) ` space M"
    by auto
  have inj: "\<And>A. inj_on (\<lambda>(x, y). (x, x, y)) A"
    by (auto simp: inj_on_def)
  have Pxxy_eq: "\<And>x y. Pxxy (x, x, y) = Pxy (x, y)"
    by (auto simp: Pxxy_def Pxy_def intro!: arg_cong[where f=prob])
  have "AE x in count_space ((\<lambda>x. (X x, Y x))`space M). Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of snd, OF _ Pxy[THEN simple_distributed] Py[THEN simple_distributed]]) (auto intro: measurable_Pair)
  then show ?thesis
    apply (subst conditional_mutual_information_eq[OF Py Pxy Pxy Pxxy])
    apply (subst conditional_entropy_eq[OF Py Pxy])
    apply (auto intro!: setsum_cong simp: Pxxy_eq setsum_negf[symmetric] eq setsum_reindex[OF inj]
                log_simps zero_less_mult_iff zero_le_mult_iff field_simps mult_less_0_iff AE_count_space)
    using Py[THEN simple_distributed, THEN distributed_real_AE] Pxy[THEN simple_distributed, THEN distributed_real_AE]
  apply (auto simp add: not_le[symmetric] AE_count_space)
    done
qed

lemma (in information_space) conditional_entropy_nonneg:
  assumes X: "simple_function M X" and Y: "simple_function M Y" shows "0 \<le> \<H>(X | Y)"
  using conditional_mutual_information_eq_conditional_entropy[OF X Y] conditional_mutual_information_nonneg[OF X X Y]
  by simp

subsection {* Equalities *}

lemma (in information_space) mutual_information_eq_entropy_conditional_entropy_distr:
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real" and Pxy :: "('b \<times> 'c) \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Px: "distributed M S X Px" and Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  assumes Ix: "integrable(S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Px (fst x)))"
  assumes Iy: "integrable(S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Py (snd x)))"
  assumes Ixy: "integrable(S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Pxy x))"
  shows  "mutual_information b S T X Y = entropy b S X + entropy b T Y - entropy b (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
proof -
  have X: "entropy b S X = - (\<integral>x. Pxy x * log b (Px (fst x)) \<partial>(S \<Otimes>\<^isub>M T))"
    using b_gt_1 Px[THEN distributed_real_measurable]
    apply (subst entropy_distr[OF Px])
    apply (subst distributed_transform_integral[OF Pxy Px, where T=fst])
    apply (auto intro!: integral_cong)
    done

  have Y: "entropy b T Y = - (\<integral>x. Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^isub>M T))"
    using b_gt_1 Py[THEN distributed_real_measurable]
    apply (subst entropy_distr[OF Py])
    apply (subst distributed_transform_integral[OF Pxy Py, where T=snd])
    apply (auto intro!: integral_cong)
    done

  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  have ST: "sigma_finite_measure (S \<Otimes>\<^isub>M T)" ..

  have XY: "entropy b (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) = - (\<integral>x. Pxy x * log b (Pxy x) \<partial>(S \<Otimes>\<^isub>M T))"
    by (subst entropy_distr[OF Pxy]) (auto intro!: integral_cong)
  
  have "AE x in S \<Otimes>\<^isub>M T. Px (fst x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of fst, OF _ Pxy Px]) (auto intro: measurable_Pair)
  moreover have "AE x in S \<Otimes>\<^isub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of snd, OF _ Pxy Py]) (auto intro: measurable_Pair)
  moreover have "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Px (fst x)"
    using Px by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_fst'' dest: distributed_real_AE distributed_real_measurable)
  moreover have "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Py (snd x)"
    using Py by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'' dest: distributed_real_AE distributed_real_measurable)
  moreover note Pxy[THEN distributed_real_AE]
  ultimately have "AE x in S \<Otimes>\<^isub>M T. Pxy x * log b (Pxy x) - Pxy x * log b (Px (fst x)) - Pxy x * log b (Py (snd x)) = 
    Pxy x * log b (Pxy x / (Px (fst x) * Py (snd x)))"
    (is "AE x in _. ?f x = ?g x")
  proof eventually_elim
    case (goal1 x)
    show ?case
    proof cases
      assume "Pxy x \<noteq> 0"
      with goal1 have "0 < Px (fst x)" "0 < Py (snd x)" "0 < Pxy x"
        by auto
      then show ?thesis
        using b_gt_1 by (simp add: log_simps mult_pos_pos less_imp_le field_simps)
    qed simp
  qed

  have "entropy b S X + entropy b T Y - entropy b (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) = integral\<^isup>L (S \<Otimes>\<^isub>M T) ?f"
    unfolding X Y XY
    apply (subst integral_diff)
    apply (intro integral_diff Ixy Ix Iy)+
    apply (subst integral_diff)
    apply (intro integral_diff Ixy Ix Iy)+
    apply (simp add: field_simps)
    done
  also have "\<dots> = integral\<^isup>L (S \<Otimes>\<^isub>M T) ?g"
    using `AE x in _. ?f x = ?g x` by (rule integral_cong_AE)
  also have "\<dots> = mutual_information b S T X Y"
    by (rule mutual_information_distr[OF S T Px Py Pxy, symmetric])
  finally show ?thesis ..
qed

lemma (in information_space) mutual_information_eq_entropy_conditional_entropy:
  assumes sf_X: "simple_function M X" and sf_Y: "simple_function M Y"
  shows  "\<I>(X ; Y) = \<H>(X) - \<H>(X | Y)"
proof -
  have X: "simple_distributed M X (\<lambda>x. measure M (X -` {x} \<inter> space M))"
    using sf_X by (rule simple_distributedI) auto
  have Y: "simple_distributed M Y (\<lambda>x. measure M (Y -` {x} \<inter> space M))"
    using sf_Y by (rule simple_distributedI) auto
  have sf_XY: "simple_function M (\<lambda>x. (X x, Y x))"
    using sf_X sf_Y by (rule simple_function_Pair)
  then have XY: "simple_distributed M (\<lambda>x. (X x, Y x)) (\<lambda>x. measure M ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M))"
    by (rule simple_distributedI) auto
  from simple_distributed_joint_finite[OF this, simp]
  have eq: "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) = count_space (X ` space M \<times> Y ` space M)"
    by (simp add: pair_measure_count_space)

  have "\<I>(X ; Y) = \<H>(X) + \<H>(Y) - entropy b (count_space (X`space M) \<Otimes>\<^isub>M count_space (Y`space M)) (\<lambda>x. (X x, Y x))"
    using sigma_finite_measure_count_space_finite sigma_finite_measure_count_space_finite simple_distributed[OF X] simple_distributed[OF Y] simple_distributed_joint[OF XY]
    by (rule mutual_information_eq_entropy_conditional_entropy_distr) (auto simp: eq integrable_count_space)
  then show ?thesis
    unfolding conditional_entropy_eq_entropy_simple[OF sf_X sf_Y] by simp
qed

lemma (in information_space) mutual_information_nonneg_simple:
  assumes sf_X: "simple_function M X" and sf_Y: "simple_function M Y"
  shows  "0 \<le> \<I>(X ; Y)"
proof -
  have X: "simple_distributed M X (\<lambda>x. measure M (X -` {x} \<inter> space M))"
    using sf_X by (rule simple_distributedI) auto
  have Y: "simple_distributed M Y (\<lambda>x. measure M (Y -` {x} \<inter> space M))"
    using sf_Y by (rule simple_distributedI) auto

  have sf_XY: "simple_function M (\<lambda>x. (X x, Y x))"
    using sf_X sf_Y by (rule simple_function_Pair)
  then have XY: "simple_distributed M (\<lambda>x. (X x, Y x)) (\<lambda>x. measure M ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M))"
    by (rule simple_distributedI) auto

  from simple_distributed_joint_finite[OF this, simp]
  have eq: "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) = count_space (X ` space M \<times> Y ` space M)"
    by (simp add: pair_measure_count_space)

  show ?thesis
    by (rule mutual_information_nonneg[OF _ _ simple_distributed[OF X] simple_distributed[OF Y] simple_distributed_joint[OF XY]])
       (simp_all add: eq integrable_count_space sigma_finite_measure_count_space_finite)
qed

lemma (in information_space) conditional_entropy_less_eq_entropy:
  assumes X: "simple_function M X" and Z: "simple_function M Z"
  shows "\<H>(X | Z) \<le> \<H>(X)"
proof -
  have "0 \<le> \<I>(X ; Z)" using X Z by (rule mutual_information_nonneg_simple)
  also have "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)" using mutual_information_eq_entropy_conditional_entropy[OF assms] .
  finally show ?thesis by auto
qed

lemma (in information_space) entropy_chain_rule:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows  "\<H>(\<lambda>x. (X x, Y x)) = \<H>(X) + \<H>(Y|X)"
proof -
  note XY = simple_distributedI[OF simple_function_Pair[OF X Y] refl]
  note YX = simple_distributedI[OF simple_function_Pair[OF Y X] refl]
  note simple_distributed_joint_finite[OF this, simp]
  let ?f = "\<lambda>x. prob ((\<lambda>x. (X x, Y x)) -` {x} \<inter> space M)"
  let ?g = "\<lambda>x. prob ((\<lambda>x. (Y x, X x)) -` {x} \<inter> space M)"
  let ?h = "\<lambda>x. if x \<in> (\<lambda>x. (Y x, X x)) ` space M then prob ((\<lambda>x. (Y x, X x)) -` {x} \<inter> space M) else 0"
  have "\<H>(\<lambda>x. (X x, Y x)) = - (\<Sum>x\<in>(\<lambda>x. (X x, Y x)) ` space M. ?f x * log b (?f x))"
    using XY by (rule entropy_simple_distributed)
  also have "\<dots> = - (\<Sum>x\<in>(\<lambda>(x, y). (y, x)) ` (\<lambda>x. (X x, Y x)) ` space M. ?g x * log b (?g x))"
    by (subst (2) setsum_reindex) (auto simp: inj_on_def intro!: setsum_cong arg_cong[where f="\<lambda>A. prob A * log b (prob A)"])
  also have "\<dots> = - (\<Sum>x\<in>(\<lambda>x. (Y x, X x)) ` space M. ?h x * log b (?h x))"
    by (auto intro!: setsum_cong)
  also have "\<dots> = entropy b (count_space (Y ` space M) \<Otimes>\<^isub>M count_space (X ` space M)) (\<lambda>x. (Y x, X x))"
    by (subst entropy_distr[OF simple_distributed_joint[OF YX]])
       (auto simp: pair_measure_count_space sigma_finite_measure_count_space_finite lebesgue_integral_count_space_finite
             cong del: setsum_cong  intro!: setsum_mono_zero_left)
  finally have "\<H>(\<lambda>x. (X x, Y x)) = entropy b (count_space (Y ` space M) \<Otimes>\<^isub>M count_space (X ` space M)) (\<lambda>x. (Y x, X x))" .
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
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF simple_function_Pair[OF fX X] refl]])
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF X refl]])
    unfolding eq
    apply (subst setsum_reindex[OF inj])
    apply (auto intro!: setsum_cong arg_cong[where f="\<lambda>A. prob A * log b (prob A)"])
    done
qed

corollary (in information_space) entropy_data_processing:
  assumes X: "simple_function M X" shows "\<H>(f \<circ> X) \<le> \<H>(X)"
proof -
  note fX = simple_function_compose[OF X, of f]
  from X have "\<H>(X) = \<H>(f\<circ>X) + \<H>(X|f\<circ>X)" by (rule entropy_partition)
  then show "\<H>(f \<circ> X) \<le> \<H>(X)"
    by (auto intro: conditional_entropy_nonneg[OF X fX])
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
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF X refl]])
    apply (subst entropy_simple_distributed[OF simple_distributedI[OF simple_function_compose[OF X]], where f="\<lambda>x. prob (X -` {x} \<inter> space M)"])
    apply (auto intro!: setsum_cong arg_cong[where f=prob] image_eqI simp: the_inv_into_f_f[OF inj] comp_def)
    done
  also have "... \<le> \<H>(f \<circ> X)"
    using entropy_data_processing[OF sf] .
  finally show "\<H>(X) \<le> \<H>(f \<circ> X)" .
qed

end
