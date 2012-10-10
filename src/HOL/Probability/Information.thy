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

section "Convex theory"

lemma log_setsum:
  assumes "finite s" "s \<noteq> {}"
  assumes "b > 1"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And> i. i \<in> s \<Longrightarrow> a i \<ge> 0"
  assumes "\<And> i. i \<in> s \<Longrightarrow> y i \<in> {0 <..}"
  shows "log b (\<Sum> i \<in> s. a i * y i) \<ge> (\<Sum> i \<in> s. a i * log b (y i))"
proof -
  have "convex_on {0 <..} (\<lambda> x. - log b x)"
    by (rule minus_log_convex[OF `b > 1`])
  hence "- log b (\<Sum> i \<in> s. a i * y i) \<le> (\<Sum> i \<in> s. a i * - log b (y i))"
    using convex_on_setsum[of _ _ "\<lambda> x. - log b x"] assms pos_is_convex by fastforce
  thus ?thesis by (auto simp add:setsum_negf le_imp_neg_le)
qed

lemma log_setsum':
  assumes "finite s" "s \<noteq> {}"
  assumes "b > 1"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes pos: "\<And> i. i \<in> s \<Longrightarrow> 0 \<le> a i"
          "\<And> i. \<lbrakk> i \<in> s ; 0 < a i \<rbrakk> \<Longrightarrow> 0 < y i"
  shows "log b (\<Sum> i \<in> s. a i * y i) \<ge> (\<Sum> i \<in> s. a i * log b (y i))"
proof -
  have "\<And>y. (\<Sum> i \<in> s - {i. a i = 0}. a i * y i) = (\<Sum> i \<in> s. a i * y i)"
    using assms by (auto intro!: setsum_mono_zero_cong_left)
  moreover have "log b (\<Sum> i \<in> s - {i. a i = 0}. a i * y i) \<ge> (\<Sum> i \<in> s - {i. a i = 0}. a i * log b (y i))"
  proof (rule log_setsum)
    have "setsum a (s - {i. a i = 0}) = setsum a s"
      using assms(1) by (rule setsum_mono_zero_cong_left) auto
    thus sum_1: "setsum a (s - {i. a i = 0}) = 1"
      "finite (s - {i. a i = 0})" using assms by simp_all

    show "s - {i. a i = 0} \<noteq> {}"
    proof
      assume *: "s - {i. a i = 0} = {}"
      hence "setsum a (s - {i. a i = 0}) = 0" by (simp add: * setsum_empty)
      with sum_1 show False by simp
    qed

    fix i assume "i \<in> s - {i. a i = 0}"
    hence "i \<in> s" "a i \<noteq> 0" by simp_all
    thus "0 \<le> a i" "y i \<in> {0<..}" using pos[of i] by auto
  qed fact+
  ultimately show ?thesis by simp
qed

lemma log_setsum_divide:
  assumes "finite S" and "S \<noteq> {}" and "1 < b"
  assumes "(\<Sum>x\<in>S. g x) = 1"
  assumes pos: "\<And>x. x \<in> S \<Longrightarrow> g x \<ge> 0" "\<And>x. x \<in> S \<Longrightarrow> f x \<ge> 0"
  assumes g_pos: "\<And>x. \<lbrakk> x \<in> S ; 0 < g x \<rbrakk> \<Longrightarrow> 0 < f x"
  shows "- (\<Sum>x\<in>S. g x * log b (g x / f x)) \<le> log b (\<Sum>x\<in>S. f x)"
proof -
  have log_mono: "\<And>x y. 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log b x \<le> log b y"
    using `1 < b` by (subst log_le_cancel_iff) auto

  have "- (\<Sum>x\<in>S. g x * log b (g x / f x)) = (\<Sum>x\<in>S. g x * log b (f x / g x))"
  proof (unfold setsum_negf[symmetric], rule setsum_cong)
    fix x assume x: "x \<in> S"
    show "- (g x * log b (g x / f x)) = g x * log b (f x / g x)"
    proof (cases "g x = 0")
      case False
      with pos[OF x] g_pos[OF x] have "0 < f x" "0 < g x" by simp_all
      thus ?thesis using `1 < b` by (simp add: log_divide field_simps)
    qed simp
  qed rule
  also have "... \<le> log b (\<Sum>x\<in>S. g x * (f x / g x))"
  proof (rule log_setsum')
    fix x assume x: "x \<in> S" "0 < g x"
    with g_pos[OF x] show "0 < f x / g x" by (safe intro!: divide_pos_pos)
  qed fact+
  also have "... = log b (\<Sum>x\<in>S - {x. g x = 0}. f x)" using `finite S`
    by (auto intro!: setsum_mono_zero_cong_right arg_cong[where f="log b"]
        split: split_if_asm)
  also have "... \<le> log b (\<Sum>x\<in>S. f x)"
  proof (rule log_mono)
    have "0 = (\<Sum>x\<in>S - {x. g x = 0}. 0)" by simp
    also have "... < (\<Sum>x\<in>S - {x. g x = 0}. f x)" (is "_ < ?sum")
    proof (rule setsum_strict_mono)
      show "finite (S - {x. g x = 0})" using `finite S` by simp
      show "S - {x. g x = 0} \<noteq> {}"
      proof
        assume "S - {x. g x = 0} = {}"
        hence "(\<Sum>x\<in>S. g x) = 0" by (subst setsum_0') auto
        with `(\<Sum>x\<in>S. g x) = 1` show False by simp
      qed
      fix x assume "x \<in> S - {x. g x = 0}"
      thus "0 < f x" using g_pos[of x] pos(1)[of x] by auto
    qed
    finally show "0 < ?sum" .
    show "(\<Sum>x\<in>S - {x. g x = 0}. f x) \<le> (\<Sum>x\<in>S. f x)"
      using `finite S` pos by (auto intro!: setsum_mono2)
  qed
  finally show ?thesis .
qed

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

lemma (in information_space) entropy_distr:
  fixes X :: "'a \<Rightarrow> 'b"
  assumes "sigma_finite_measure MX" and X: "distributed M MX X f"
  shows "entropy b MX X = - (\<integral>x. f x * log b (f x) \<partial>MX)"
proof -
  interpret MX: sigma_finite_measure MX by fact
  from X show ?thesis
    unfolding entropy_def X[THEN distributed_distr_eq_density]
    by (subst MX.KL_density[OF b_gt_1]) (simp_all add: distributed_real_AE distributed_real_measurable)
qed

lemma (in information_space) entropy_uniform:
  assumes "sigma_finite_measure MX"
  assumes A: "A \<in> sets MX" "emeasure MX A \<noteq> 0" "emeasure MX A \<noteq> \<infinity>"
  assumes X: "distributed M MX X (\<lambda>x. 1 / measure MX A * indicator A x)"
  shows "entropy b MX X = log b (measure MX A)"
proof (subst entropy_distr[OF _ X])
  let ?f = "\<lambda>x. 1 / measure MX A * indicator A x"
  have "- (\<integral>x. ?f x * log b (?f x) \<partial>MX) = 
    - (\<integral>x. (log b (1 / measure MX A) / measure MX A) * indicator A x \<partial>MX)"
    by (auto intro!: integral_cong simp: indicator_def)
  also have "\<dots> = - log b (inverse (measure MX A))"
    using A by (subst integral_cmult(2))
               (simp_all add: measure_def real_of_ereal_eq_0 integral_cmult inverse_eq_divide)
  also have "\<dots> = log b (measure MX A)"
    using b_gt_1 A by (subst log_inverse) (auto simp add: measure_def less_le real_of_ereal_eq_0
                                                          emeasure_nonneg real_of_ereal_pos)
  finally show "- (\<integral>x. ?f x * log b (?f x) \<partial>MX) = log b (measure MX A)" by simp
qed fact+

lemma (in information_space) entropy_simple_distributed:
  fixes X :: "'a \<Rightarrow> 'b"
  assumes X: "simple_distributed M X f"
  shows "\<H>(X) = - (\<Sum>x\<in>X`space M. f x * log b (f x))"
proof (subst entropy_distr[OF _ simple_distributed[OF X]])
  show "sigma_finite_measure (count_space (X ` space M))"
    using X by (simp add: sigma_finite_measure_count_space_finite simple_distributed_def)
  show "- (\<integral>x. f x * log b (f x) \<partial>(count_space (X`space M))) = - (\<Sum>x\<in>X ` space M. f x * log b (f x))"
    using X by (auto simp add: lebesgue_integral_count_space_finite)
qed

lemma (in information_space) entropy_le_card_not_0:
  assumes X: "simple_distributed M X f"
  shows "\<H>(X) \<le> log b (card (X ` space M \<inter> {x. f x \<noteq> 0}))"
proof -
  have "\<H>(X) = (\<Sum>x\<in>X`space M. f x * log b (1 / f x))"
    unfolding entropy_simple_distributed[OF X] setsum_negf[symmetric]
    using X by (auto dest: simple_distributed_nonneg intro!: setsum_cong simp: log_simps less_le)
  also have "\<dots> \<le> log b (\<Sum>x\<in>X`space M. f x * (1 / f x))"
    using not_empty b_gt_1 `simple_distributed M X f`
    by (intro log_setsum') (auto simp: simple_distributed_nonneg simple_distributed_setsum_space)
  also have "\<dots> = log b (\<Sum>x\<in>X`space M. if f x \<noteq> 0 then 1 else 0)"
    by (intro arg_cong[where f="\<lambda>X. log b X"] setsum_cong) auto
  finally show ?thesis
    using `simple_distributed M X f` by (auto simp: setsum_cases real_eq_of_nat)
qed

lemma (in information_space) entropy_le_card:
  assumes "simple_distributed M X f"
  shows "\<H>(X) \<le> log b (real (card (X ` space M)))"
proof cases
  assume "X ` space M \<inter> {x. f x \<noteq> 0} = {}"
  then have "\<And>x. x\<in>X`space M \<Longrightarrow> f x = 0" by auto
  moreover
  have "0 < card (X`space M)"
    using `simple_distributed M X f` not_empty by (auto simp: card_gt_0_iff)
  then have "log b 1 \<le> log b (real (card (X`space M)))"
    using b_gt_1 by (intro log_le) auto
  ultimately show ?thesis using assms by (simp add: entropy_simple_distributed)
next
  assume False: "X ` space M \<inter> {x. f x \<noteq> 0} \<noteq> {}"
  have "card (X ` space M \<inter> {x. f x \<noteq> 0}) \<le> card (X ` space M)"
    (is "?A \<le> ?B") using assms not_empty
    by (auto intro!: card_mono simp: simple_function_def simple_distributed_def)
  note entropy_le_card_not_0[OF assms]
  also have "log b (real ?A) \<le> log b (real ?B)"
    using b_gt_1 False not_empty `?A \<le> ?B` assms
    by (auto intro!: log_le simp: card_gt_0_iff simp: simple_distributed_def)
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

lemma (in information_space) conditional_mutual_information_generic_eq:
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T" and P: "sigma_finite_measure P"
  assumes Px: "distributed M S X Px"
  assumes Pz: "distributed M P Z Pz"
  assumes Pyz: "distributed M (T \<Otimes>\<^isub>M P) (\<lambda>x. (Y x, Z x)) Pyz"
  assumes Pxz: "distributed M (S \<Otimes>\<^isub>M P) (\<lambda>x. (X x, Z x)) Pxz"
  assumes Pxyz: "distributed M (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>x. (X x, Y x, Z x)) Pxyz"
  assumes I1: "integrable (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Px x * Pyz (y, z))))"
  assumes I2: "integrable (S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P) (\<lambda>(x, y, z). Pxyz (x, y, z) * log b (Pxz (x, z) / (Px x * Pz z)))"
  shows "conditional_mutual_information b S T P X Y Z
    = (\<integral>(x, y, z). Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))) \<partial>(S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P))"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret P: sigma_finite_measure P by fact
  interpret TP: pair_sigma_finite T P ..
  interpret SP: pair_sigma_finite S P ..
  interpret SPT: pair_sigma_finite "S \<Otimes>\<^isub>M P" T ..
  interpret STP: pair_sigma_finite S "T \<Otimes>\<^isub>M P" ..
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
  
  have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Px (fst x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of fst, OF _ Pxyz Px]) auto
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pz (snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of "\<lambda>x. snd (snd x)", OF _ Pxyz Pz]) (auto intro: measurable_snd')
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pxz (fst x, snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of "\<lambda>x. (fst x, snd (snd x))", OF _ Pxyz Pxz]) (auto intro: measurable_Pair measurable_snd')
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. Pyz (snd x) = 0 \<longrightarrow> Pxyz x = 0"
    by (intro subdensity_real[of snd, OF _ Pxyz Pyz]) (auto intro: measurable_Pair)
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Px (fst x)"
    using Px by (intro STP.AE_pair_measure) (auto simp: comp_def intro!: measurable_fst'' dest: distributed_real_AE distributed_real_measurable)
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Pyz (snd x)"
    using Pyz by (intro STP.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'' dest: distributed_real_AE distributed_real_measurable)
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Pz (snd (snd x))"
    using Pz Pz[THEN distributed_real_measurable] by (auto intro!: measurable_snd'' TP.AE_pair_measure STP.AE_pair_measure AE_I2[of S] dest: distributed_real_AE)
  moreover have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P. 0 \<le> Pxz (fst x, snd (snd x))"
    using Pxz[THEN distributed_real_AE, THEN SP.AE_pair]
    using measurable_comp[OF measurable_Pair[OF measurable_fst measurable_comp[OF measurable_snd measurable_snd]] Pxz[THEN distributed_real_measurable], of T]
    using measurable_comp[OF measurable_snd measurable_Pair2[OF Pxz[THEN distributed_real_measurable]], of _ T]
    by (auto intro!: TP.AE_pair_measure STP.AE_pair_measure simp: comp_def)
  moreover note Pxyz[THEN distributed_real_AE]
  ultimately have "AE x in S \<Otimes>\<^isub>M T \<Otimes>\<^isub>M P.
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
  with I1 I2 show ?thesis
    unfolding conditional_mutual_information_def
    apply (subst mi_eq)
    apply (subst mutual_information_distr[OF S TP Px Pyz Pxyz])
    apply (subst integral_diff(2)[symmetric])
    apply (auto intro!: integral_cong_AE simp: split_beta' simp del: integral_diff)
    done
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
  def Pz \<equiv> "\<lambda>x. if x \<in> Z`space M then measure M (Z -` {x} \<inter> space M) else 0"
  def Pxz \<equiv> "\<lambda>x. if x \<in> (\<lambda>x. (X x, Z x))`space M then measure M ((\<lambda>x. (X x, Z x)) -` {x} \<inter> space M) else 0"
  def Pyz \<equiv> "\<lambda>x. if x \<in> (\<lambda>x. (Y x, Z x))`space M then measure M ((\<lambda>x. (Y x, Z x)) -` {x} \<inter> space M) else 0"
  def Pxyz \<equiv> "\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x, Z x))`space M then measure M ((\<lambda>x. (X x, Y x, Z x)) -` {x} \<inter> space M) else 0"
  let ?M = "X`space M \<times> Y`space M \<times> Z`space M"

  note XZ = simple_function_Pair[OF X Z]
  note YZ = simple_function_Pair[OF Y Z]
  note XYZ = simple_function_Pair[OF X simple_function_Pair[OF Y Z]]
  have Pz: "simple_distributed M Z Pz"
    using Z by (rule simple_distributedI) (auto simp: Pz_def)
  have Pxz: "simple_distributed M (\<lambda>x. (X x, Z x)) Pxz"
    using XZ by (rule simple_distributedI) (auto simp: Pxz_def)
  have Pyz: "simple_distributed M (\<lambda>x. (Y x, Z x)) Pyz"
    using YZ by (rule simple_distributedI) (auto simp: Pyz_def)
  have Pxyz: "simple_distributed M (\<lambda>x. (X x, Y x, Z x)) Pxyz"
    using XYZ by (rule simple_distributedI) (auto simp: Pxyz_def)

  { fix z assume z: "z \<in> Z ` space M" then have "(\<Sum>x\<in>X ` space M. Pxz (x, z)) = Pz z"
      using distributed_marginal_eq_joint_simple[OF X Pz Pxz z]
      by (auto intro!: setsum_cong simp: Pxz_def) }
  note marginal1 = this

  { fix z assume z: "z \<in> Z ` space M" then have "(\<Sum>y\<in>Y ` space M. Pyz (y, z)) = Pz z"
      using distributed_marginal_eq_joint_simple[OF Y Pz Pyz z]
      by (auto intro!: setsum_cong simp: Pyz_def) }
  note marginal2 = this

  have "- \<I>(X ; Y | Z) = - (\<Sum>(x, y, z) \<in> ?M. Pxyz (x, y, z) * log b (Pxyz (x, y, z) / (Pxz (x, z) * (Pyz (y,z) / Pz z))))"
    unfolding conditional_mutual_information_eq[OF Pz Pyz Pxz Pxyz]
    using X Y Z by (auto intro!: setsum_mono_zero_left simp: Pxyz_def simple_functionD)
  also have "\<dots> \<le> log b (\<Sum>(x, y, z) \<in> ?M. Pxz (x, z) * (Pyz (y,z) / Pz z))"
    unfolding split_beta'
  proof (rule log_setsum_divide)
    show "?M \<noteq> {}" using not_empty by simp
    show "1 < b" using b_gt_1 .

    show "finite ?M" using X Y Z by (auto simp: simple_functionD)

    then show "(\<Sum>x\<in>?M. Pxyz (fst x, fst (snd x), snd (snd x))) = 1"
      apply (subst Pxyz[THEN simple_distributed_setsum_space, symmetric])
      apply simp
      apply (intro setsum_mono_zero_right)
      apply (auto simp: Pxyz_def)
      done
    let ?N = "(\<lambda>x. (X x, Y x, Z x)) ` space M"
    fix x assume x: "x \<in> ?M"
    let ?Q = "Pxyz (fst x, fst (snd x), snd (snd x))"
    let ?P = "Pxz (fst x, snd (snd x)) * (Pyz (fst (snd x), snd (snd x)) / Pz (snd (snd x)))"
    from x show "0 \<le> ?Q" "0 \<le> ?P"
      using Pxyz[THEN simple_distributed, THEN distributed_real_AE]
      using Pxz[THEN simple_distributed, THEN distributed_real_AE]
      using Pyz[THEN simple_distributed, THEN distributed_real_AE]
      using Pz[THEN simple_distributed, THEN distributed_real_AE]
      by (auto intro!: mult_nonneg_nonneg divide_nonneg_nonneg simp: AE_count_space Pxyz_def Pxz_def Pyz_def Pz_def)
    moreover assume "0 < ?Q"
    moreover have "AE x in count_space ?N. Pz (snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
      by (intro subdensity_real[of "\<lambda>x. snd (snd x)", OF _ Pxyz[THEN simple_distributed] Pz[THEN simple_distributed]]) (auto intro: measurable_snd')
    then have "\<And>x. Pz (snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
      by (auto simp: Pz_def Pxyz_def AE_count_space)
    moreover have "AE x in count_space ?N. Pxz (fst x, snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
      by (intro subdensity_real[of "\<lambda>x. (fst x, snd (snd x))", OF _ Pxyz[THEN simple_distributed] Pxz[THEN simple_distributed]]) (auto intro: measurable_Pair measurable_snd')
    then have "\<And>x. Pxz (fst x, snd (snd x)) = 0 \<longrightarrow> Pxyz x = 0"
      by (auto simp: Pz_def Pxyz_def AE_count_space)
    moreover have "AE x in count_space ?N. Pyz (snd x) = 0 \<longrightarrow> Pxyz x = 0"
      by (intro subdensity_real[of snd, OF _ Pxyz[THEN simple_distributed] Pyz[THEN simple_distributed]]) (auto intro: measurable_Pair)
    then have "\<And>x. Pyz (snd x) = 0 \<longrightarrow> Pxyz x = 0"
      by (auto simp: Pz_def Pxyz_def AE_count_space)
    ultimately show "0 < ?P" using x by (auto intro!: divide_pos_pos mult_pos_pos simp: less_le)
  qed
  also have "(\<Sum>(x, y, z) \<in> ?M. Pxz (x, z) * (Pyz (y,z) / Pz z)) = (\<Sum>z\<in>Z`space M. Pz z)"
    apply (simp add: setsum_cartesian_product')
    apply (subst setsum_commute)
    apply (subst (2) setsum_commute)
    apply (auto simp: setsum_divide_distrib[symmetric] setsum_product[symmetric] marginal1 marginal2
          intro!: setsum_cong)
    done
  also have "log b (\<Sum>z\<in>Z`space M. Pz z) = 0"
    using Pz[THEN simple_distributed_setsum_space] by simp
  finally show ?thesis by simp
qed

subsection {* Conditional Entropy *}

definition (in prob_space)
  "conditional_entropy b S T X Y = entropy b (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) - entropy b T Y"

abbreviation (in information_space)
  conditional_entropy_Pow ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> conditional_entropy b (count_space (X`space M)) (count_space (Y`space M)) X Y"

lemma (in information_space) conditional_entropy_generic_eq:
  fixes Px :: "'b \<Rightarrow> real" and Py :: "'c \<Rightarrow> real"
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes Px: "distributed M S X Px"
  assumes Py: "distributed M T Y Py"
  assumes Pxy: "distributed M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) Pxy"
  assumes I1: "integrable (S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Pxy x))"
  assumes I2: "integrable (S \<Otimes>\<^isub>M T) (\<lambda>x. Pxy x * log b (Py (snd x)))"
  shows "conditional_entropy b S T X Y = - (\<integral>(x, y). Pxy (x, y) * log b (Pxy (x, y) / Py y) \<partial>(S \<Otimes>\<^isub>M T))"
proof -
  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  have ST: "sigma_finite_measure (S \<Otimes>\<^isub>M T)" ..

  interpret Pxy: prob_space "density (S \<Otimes>\<^isub>M T) Pxy"
    unfolding Pxy[THEN distributed_distr_eq_density, symmetric]
    using Pxy[THEN distributed_measurable] by (rule prob_space_distr)

  from Py Pxy have distr_eq: "distr M T Y =
    distr (distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))) T snd"
    by (subst distr_distr[OF measurable_snd]) (auto dest: distributed_measurable simp: comp_def)

  have "entropy b T Y = - (\<integral>y. Py y * log b (Py y) \<partial>T)"
    by (rule entropy_distr[OF T Py])
  also have "\<dots> = - (\<integral>(x,y). Pxy (x,y) * log b (Py y) \<partial>(S \<Otimes>\<^isub>M T))"
    using b_gt_1 Py[THEN distributed_real_measurable]
    by (subst distributed_transform_integral[OF Pxy Py, where T=snd]) (auto intro!: integral_cong)
  finally have e_eq: "entropy b T Y = - (\<integral>(x,y). Pxy (x,y) * log b (Py y) \<partial>(S \<Otimes>\<^isub>M T))" .
  
  have "AE x in S \<Otimes>\<^isub>M T. Px (fst x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of fst, OF _ Pxy Px]) (auto intro: measurable_Pair)
  moreover have "AE x in S \<Otimes>\<^isub>M T. Py (snd x) = 0 \<longrightarrow> Pxy x = 0"
    by (intro subdensity_real[of snd, OF _ Pxy Py]) (auto intro: measurable_Pair)
  moreover have "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Px (fst x)"
    using Px by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_fst'' dest: distributed_real_AE distributed_real_measurable)
  moreover have "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Py (snd x)"
    using Py by (intro ST.AE_pair_measure) (auto simp: comp_def intro!: measurable_snd'' dest: distributed_real_AE distributed_real_measurable)
  moreover note Pxy[THEN distributed_real_AE]
  ultimately have pos: "AE x in S \<Otimes>\<^isub>M T. 0 \<le> Pxy x \<and> 0 \<le> Px (fst x) \<and> 0 \<le> Py (snd x) \<and>
    (Pxy x = 0 \<or> (Pxy x \<noteq> 0 \<longrightarrow> 0 < Pxy x \<and> 0 < Px (fst x) \<and> 0 < Py (snd x)))"
    by eventually_elim auto

  from pos have "AE x in S \<Otimes>\<^isub>M T.
     Pxy x * log b (Pxy x) - Pxy x * log b (Py (snd x)) = Pxy x * log b (Pxy x / Py (snd x))"
    by eventually_elim (auto simp: log_simps mult_pos_pos field_simps b_gt_1)
  with I1 I2 show ?thesis
    unfolding conditional_entropy_def
    apply (subst e_eq)
    apply (subst entropy_distr[OF ST Pxy])
    unfolding minus_diff_minus
    apply (subst integral_diff(2)[symmetric])
    apply (auto intro!: integral_cong_AE simp: split_beta' simp del: integral_diff)
    done
qed

lemma (in information_space) conditional_entropy_eq:
  assumes Y: "simple_distributed M Y Py" and X: "simple_function M X"
  assumes XY: "simple_distributed M (\<lambda>x. (X x, Y x)) Pxy"
    shows "\<H>(X | Y) = - (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` space M. Pxy (x, y) * log b (Pxy (x, y) / Py y))"
proof (subst conditional_entropy_generic_eq[OF _ _
  simple_distributed[OF simple_distributedI[OF X refl]] simple_distributed[OF Y] simple_distributed_joint[OF XY]])
  have [simp]: "finite (X`space M)" using X by (simp add: simple_function_def)
  note Y[THEN simple_distributed_finite, simp]
  show "sigma_finite_measure (count_space (X ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  show "sigma_finite_measure (count_space (Y ` space M))"
    by (simp add: sigma_finite_measure_count_space_finite)
  let ?f = "(\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x else 0)"
  have "count_space (X ` space M) \<Otimes>\<^isub>M count_space (Y ` space M) = count_space (X`space M \<times> Y`space M)"
    (is "?P = ?C")
    using X Y by (simp add: simple_distributed_finite pair_measure_count_space)
  with X Y show
      "integrable ?P (\<lambda>x. ?f x * log b (?f x))"
      "integrable ?P (\<lambda>x. ?f x * log b (Py (snd x)))"
    by (auto intro!: integrable_count_space simp: simple_distributed_finite)
  have eq: "(\<lambda>(x, y). ?f (x, y) * log b (?f (x, y) / Py y)) =
    (\<lambda>x. if x \<in> (\<lambda>x. (X x, Y x)) ` space M then Pxy x * log b (Pxy x / Py (snd x)) else 0)"
    by auto
  from X Y show "- (\<integral> (x, y). ?f (x, y) * log b (?f (x, y) / Py y) \<partial>?P) =
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
    apply (subst conditional_entropy_eq[OF Py X Pxy])
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
    apply (subst entropy_distr[OF S Px])
    apply (subst distributed_transform_integral[OF Pxy Px, where T=fst])
    apply (auto intro!: integral_cong)
    done

  have Y: "entropy b T Y = - (\<integral>x. Pxy x * log b (Py (snd x)) \<partial>(S \<Otimes>\<^isub>M T))"
    using b_gt_1 Py[THEN distributed_real_measurable]
    apply (subst entropy_distr[OF T Py])
    apply (subst distributed_transform_integral[OF Pxy Py, where T=snd])
    apply (auto intro!: integral_cong)
    done

  interpret S: sigma_finite_measure S by fact
  interpret T: sigma_finite_measure T by fact
  interpret ST: pair_sigma_finite S T ..
  have ST: "sigma_finite_measure (S \<Otimes>\<^isub>M T)" ..

  have XY: "entropy b (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x)) = - (\<integral>x. Pxy x * log b (Pxy x) \<partial>(S \<Otimes>\<^isub>M T))"
    by (subst entropy_distr[OF ST Pxy]) (auto intro!: integral_cong)
  
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
    unfolding conditional_entropy_def by simp
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
    by (subst entropy_distr[OF _ simple_distributed_joint[OF YX]])
       (auto simp: pair_measure_count_space sigma_finite_measure_count_space_finite lebesgue_integral_count_space_finite
             cong del: setsum_cong  intro!: setsum_mono_zero_left)
  finally have "\<H>(\<lambda>x. (X x, Y x)) = entropy b (count_space (Y ` space M) \<Otimes>\<^isub>M count_space (X ` space M)) (\<lambda>x. (Y x, X x))" .
  then show ?thesis
    unfolding conditional_entropy_def by simp
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
