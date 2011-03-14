theory Information
imports
  Probability_Space
  "~~/src/HOL/Library/Convex"
begin

lemma (in prob_space) not_zero_less_distribution[simp]:
  "(\<not> 0 < distribution X A) \<longleftrightarrow> distribution X A = 0"
  using distribution_positive[of X A] by arith

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
    using convex_on_setsum[of _ _ "\<lambda> x. - log b x"] assms pos_is_convex by fastsimp
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
  "KL_divergence b M \<nu> = \<integral>x. log b (real (RN_deriv M \<nu> x)) \<partial>M\<lparr>measure := \<nu>\<rparr>"

lemma (in sigma_finite_measure) KL_divergence_vimage:
  assumes T: "T \<in> measure_preserving M M'"
    and T': "T' \<in> measure_preserving (M'\<lparr> measure := \<nu>' \<rparr>) (M\<lparr> measure := \<nu> \<rparr>)"
    and inv: "\<And>x. x \<in> space M \<Longrightarrow> T' (T x) = x"
    and inv': "\<And>x. x \<in> space M' \<Longrightarrow> T (T' x) = x"
  and \<nu>': "measure_space (M'\<lparr>measure := \<nu>'\<rparr>)" "measure_space.absolutely_continuous M' \<nu>'"
  and "1 < b"
  shows "KL_divergence b M' \<nu>' = KL_divergence b M \<nu>"
proof -
  interpret \<nu>': measure_space "M'\<lparr>measure := \<nu>'\<rparr>" by fact
  have M: "measure_space (M\<lparr> measure := \<nu>\<rparr>)"
    by (rule \<nu>'.measure_space_vimage[OF _ T'], simp) default
  have "sigma_algebra (M'\<lparr> measure := \<nu>'\<rparr>)" by default
  then have saM': "sigma_algebra M'" by simp
  then interpret M': measure_space M' by (rule measure_space_vimage) fact
  have ac: "absolutely_continuous \<nu>" unfolding absolutely_continuous_def
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

  have sa: "sigma_algebra (M\<lparr>measure := \<nu>\<rparr>)" by simp default
  have AE: "AE x. RN_deriv M' \<nu>' (T x) = RN_deriv M \<nu> x"
    by (rule RN_deriv_vimage[OF T T' inv \<nu>'])
  show ?thesis
    unfolding KL_divergence_def
  proof (subst \<nu>'.integral_vimage[OF sa T'])
    show "(\<lambda>x. log b (real (RN_deriv M \<nu> x))) \<in> borel_measurable (M\<lparr>measure := \<nu>\<rparr>)"
      by (auto intro!: RN_deriv[OF M ac] borel_measurable_log[OF _ `1 < b`])
    have "(\<integral> x. log b (real (RN_deriv M' \<nu>' x)) \<partial>M'\<lparr>measure := \<nu>'\<rparr>) =
      (\<integral> x. log b (real (RN_deriv M' \<nu>' (T (T' x)))) \<partial>M'\<lparr>measure := \<nu>'\<rparr>)" (is "?l = _")
      using inv' by (auto intro!: \<nu>'.integral_cong)
    also have "\<dots> = (\<integral> x. log b (real (RN_deriv M \<nu> (T' x))) \<partial>M'\<lparr>measure := \<nu>'\<rparr>)" (is "_ = ?r")
      using M ac AE
      by (intro \<nu>'.integral_cong_AE \<nu>'.almost_everywhere_vimage[OF sa T'] absolutely_continuous_AE[OF M])
         (auto elim!: AE_mp)
    finally show "?l = ?r" .
  qed
qed

lemma (in sigma_finite_measure) KL_divergence_cong:
  assumes "measure_space (M\<lparr>measure := \<nu>\<rparr>)" (is "measure_space ?\<nu>")
  assumes [simp]: "sets N = sets M" "space N = space M"
    "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A"
    "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = \<nu>' A"
  shows "KL_divergence b M \<nu> = KL_divergence b N \<nu>'"
proof -
  interpret \<nu>: measure_space ?\<nu> by fact
  have "KL_divergence b M \<nu> = \<integral>x. log b (real (RN_deriv N \<nu>' x)) \<partial>?\<nu>"
    by (simp cong: RN_deriv_cong \<nu>.integral_cong add: KL_divergence_def)
  also have "\<dots> = KL_divergence b N \<nu>'"
    by (auto intro!: \<nu>.integral_cong_measure[symmetric] simp: KL_divergence_def)
  finally show ?thesis .
qed

lemma (in finite_measure_space) KL_divergence_eq_finite:
  assumes v: "finite_measure_space (M\<lparr>measure := \<nu>\<rparr>)"
  assumes ac: "absolutely_continuous \<nu>"
  shows "KL_divergence b M \<nu> = (\<Sum>x\<in>space M. real (\<nu> {x}) * log b (real (\<nu> {x}) / real (\<mu> {x})))" (is "_ = ?sum")
proof (simp add: KL_divergence_def finite_measure_space.integral_finite_singleton[OF v])
  interpret v: finite_measure_space "M\<lparr>measure := \<nu>\<rparr>" by fact
  have ms: "measure_space (M\<lparr>measure := \<nu>\<rparr>)" by default
  show "(\<Sum>x \<in> space M. log b (real (RN_deriv M \<nu> x)) * real (\<nu> {x})) = ?sum"
    using RN_deriv_finite_measure[OF ms ac]
    by (auto intro!: setsum_cong simp: field_simps)
qed

lemma (in finite_prob_space) KL_divergence_positive_finite:
  assumes v: "finite_prob_space (M\<lparr>measure := \<nu>\<rparr>)"
  assumes ac: "absolutely_continuous \<nu>"
  and "1 < b"
  shows "0 \<le> KL_divergence b M \<nu>"
proof -
  interpret v: finite_prob_space "M\<lparr>measure := \<nu>\<rparr>" by fact
  have ms: "finite_measure_space (M\<lparr>measure := \<nu>\<rparr>)" by default

  have "- (KL_divergence b M \<nu>) \<le> log b (\<Sum>x\<in>space M. real (\<mu> {x}))"
  proof (subst KL_divergence_eq_finite[OF ms ac], safe intro!: log_setsum_divide not_empty)
    show "finite (space M)" using finite_space by simp
    show "1 < b" by fact
    show "(\<Sum>x\<in>space M. real (\<nu> {x})) = 1"
      using v.finite_sum_over_space_eq_1 by (simp add: v.\<mu>'_def)

    fix x assume "x \<in> space M"
    then have x: "{x} \<in> sets M" unfolding sets_eq_Pow by auto
    { assume "0 < real (\<nu> {x})"
      then have "\<nu> {x} \<noteq> 0" by auto
      then have "\<mu> {x} \<noteq> 0"
        using ac[unfolded absolutely_continuous_def, THEN bspec, of "{x}"] x by auto
      thus "0 < real (\<mu> {x})" using real_measure[OF x] by auto }
    show "0 \<le> real (\<mu> {x})" "0 \<le> real (\<nu> {x})"
      using real_measure[OF x] v.real_measure[of "{x}"] x by auto
  qed
  thus "0 \<le> KL_divergence b M \<nu>" using finite_sum_over_space_eq_1 by (simp add: \<mu>'_def)
qed

subsection {* Mutual Information *}

definition (in prob_space)
  "mutual_information b S T X Y =
    KL_divergence b (S\<lparr>measure := extreal\<circ>distribution X\<rparr> \<Otimes>\<^isub>M T\<lparr>measure := extreal\<circ>distribution Y\<rparr>)
      (extreal\<circ>joint_distribution X Y)"

definition (in prob_space)
  "entropy b s X = mutual_information b s s X X"

abbreviation (in information_space)
  mutual_information_Pow ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M), measure = extreal\<circ>distribution X \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M), measure = extreal\<circ>distribution Y \<rparr> X Y"

lemma (in prob_space) finite_variables_absolutely_continuous:
  assumes X: "finite_random_variable S X" and Y: "finite_random_variable T Y"
  shows "measure_space.absolutely_continuous
    (S\<lparr>measure := extreal\<circ>distribution X\<rparr> \<Otimes>\<^isub>M T\<lparr>measure := extreal\<circ>distribution Y\<rparr>)
    (extreal\<circ>joint_distribution X Y)"
proof -
  interpret X: finite_prob_space "S\<lparr>measure := extreal\<circ>distribution X\<rparr>"
    using X by (rule distribution_finite_prob_space)
  interpret Y: finite_prob_space "T\<lparr>measure := extreal\<circ>distribution Y\<rparr>"
    using Y by (rule distribution_finite_prob_space)
  interpret XY: pair_finite_prob_space
    "S\<lparr>measure := extreal\<circ>distribution X\<rparr>" "T\<lparr> measure := extreal\<circ>distribution Y\<rparr>" by default
  interpret P: finite_prob_space "XY.P\<lparr> measure := extreal\<circ>joint_distribution X Y\<rparr>"
    using assms by (auto intro!: joint_distribution_finite_prob_space)
  note rv = assms[THEN finite_random_variableD]
  show "XY.absolutely_continuous (extreal\<circ>joint_distribution X Y)"
  proof (rule XY.absolutely_continuousI)
    show "finite_measure_space (XY.P\<lparr> measure := extreal\<circ>joint_distribution X Y\<rparr>)" by default
    fix x assume "x \<in> space XY.P" and "XY.\<mu> {x} = 0"
    then obtain a b where "x = (a, b)"
      and "distribution X {a} = 0 \<or> distribution Y {b} = 0"
      by (cases x) (auto simp: space_pair_measure)
    with finite_distribution_order(5,6)[OF X Y]
    show "(extreal \<circ> joint_distribution X Y) {x} = 0" by auto
  qed
qed

lemma (in information_space)
  assumes MX: "finite_random_variable MX X"
  assumes MY: "finite_random_variable MY Y"
  shows mutual_information_generic_eq:
    "mutual_information b MX MY X Y = (\<Sum> (x,y) \<in> space MX \<times> space MY.
      joint_distribution X Y {(x,y)} *
      log b (joint_distribution X Y {(x,y)} /
      (distribution X {x} * distribution Y {y})))"
    (is ?sum)
  and mutual_information_positive_generic:
     "0 \<le> mutual_information b MX MY X Y" (is ?positive)
proof -
  interpret X: finite_prob_space "MX\<lparr>measure := extreal\<circ>distribution X\<rparr>"
    using MX by (rule distribution_finite_prob_space)
  interpret Y: finite_prob_space "MY\<lparr>measure := extreal\<circ>distribution Y\<rparr>"
    using MY by (rule distribution_finite_prob_space)
  interpret XY: pair_finite_prob_space "MX\<lparr>measure := extreal\<circ>distribution X\<rparr>" "MY\<lparr>measure := extreal\<circ>distribution Y\<rparr>" by default
  interpret P: finite_prob_space "XY.P\<lparr>measure := extreal\<circ>joint_distribution X Y\<rparr>"
    using assms by (auto intro!: joint_distribution_finite_prob_space)

  have P_ms: "finite_measure_space (XY.P\<lparr>measure := extreal\<circ>joint_distribution X Y\<rparr>)" by default
  have P_ps: "finite_prob_space (XY.P\<lparr>measure := extreal\<circ>joint_distribution X Y\<rparr>)" by default

  show ?sum
    unfolding Let_def mutual_information_def
    by (subst XY.KL_divergence_eq_finite[OF P_ms finite_variables_absolutely_continuous[OF MX MY]])
       (auto simp add: space_pair_measure setsum_cartesian_product')

  show ?positive
    using XY.KL_divergence_positive_finite[OF P_ps finite_variables_absolutely_continuous[OF MX MY] b_gt_1]
    unfolding mutual_information_def .
qed

lemma (in information_space) mutual_information_commute_generic:
  assumes X: "random_variable S X" and Y: "random_variable T Y"
  assumes ac: "measure_space.absolutely_continuous
    (S\<lparr>measure := extreal\<circ>distribution X\<rparr> \<Otimes>\<^isub>M T\<lparr>measure := extreal\<circ>distribution Y\<rparr>) (extreal\<circ>joint_distribution X Y)"
  shows "mutual_information b S T X Y = mutual_information b T S Y X"
proof -
  let ?S = "S\<lparr>measure := extreal\<circ>distribution X\<rparr>" and ?T = "T\<lparr>measure := extreal\<circ>distribution Y\<rparr>"
  interpret S: prob_space ?S using X by (rule distribution_prob_space)
  interpret T: prob_space ?T using Y by (rule distribution_prob_space)
  interpret P: pair_prob_space ?S ?T ..
  interpret Q: pair_prob_space ?T ?S ..
  show ?thesis
    unfolding mutual_information_def
  proof (intro Q.KL_divergence_vimage[OF Q.measure_preserving_swap _ _ _ _ ac b_gt_1])
    show "(\<lambda>(x,y). (y,x)) \<in> measure_preserving
      (P.P \<lparr> measure := extreal\<circ>joint_distribution X Y\<rparr>) (Q.P \<lparr> measure := extreal\<circ>joint_distribution Y X\<rparr>)"
      using X Y unfolding measurable_def
      unfolding measure_preserving_def using P.pair_sigma_algebra_swap_measurable
      by (auto simp add: space_pair_measure distribution_def intro!: arg_cong[where f=\<mu>'])
    have "prob_space (P.P\<lparr> measure := extreal\<circ>joint_distribution X Y\<rparr>)"
      using X Y by (auto intro!: distribution_prob_space random_variable_pairI)
    then show "measure_space (P.P\<lparr> measure := extreal\<circ>joint_distribution X Y\<rparr>)"
      unfolding prob_space_def by simp
  qed auto
qed

lemma (in information_space) mutual_information_commute:
  assumes X: "finite_random_variable S X" and Y: "finite_random_variable T Y"
  shows "mutual_information b S T X Y = mutual_information b T S Y X"
  unfolding mutual_information_generic_eq[OF X Y] mutual_information_generic_eq[OF Y X]
  unfolding joint_distribution_commute_singleton[of X Y]
  by (auto simp add: ac_simps intro!: setsum_reindex_cong[OF swap_inj_on])

lemma (in information_space) mutual_information_commute_simple:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<I>(X;Y) = \<I>(Y;X)"
  by (intro mutual_information_commute X Y simple_function_imp_finite_random_variable)

lemma (in information_space) mutual_information_eq:
  assumes "simple_function M X" "simple_function M Y"
  shows "\<I>(X;Y) = (\<Sum> (x,y) \<in> X ` space M \<times> Y ` space M.
    distribution (\<lambda>x. (X x, Y x)) {(x,y)} * log b (distribution (\<lambda>x. (X x, Y x)) {(x,y)} /
                                                   (distribution X {x} * distribution Y {y})))"
  using assms by (simp add: mutual_information_generic_eq)

lemma (in information_space) mutual_information_generic_cong:
  assumes X: "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes Y: "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "mutual_information b MX MY X Y = mutual_information b MX MY X' Y'"
  unfolding mutual_information_def using X Y
  by (simp cong: distribution_cong)

lemma (in information_space) mutual_information_cong:
  assumes X: "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes Y: "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "\<I>(X; Y) = \<I>(X'; Y')"
  unfolding mutual_information_def using X Y
  by (simp cong: distribution_cong image_cong)

lemma (in information_space) mutual_information_positive:
  assumes "simple_function M X" "simple_function M Y"
  shows "0 \<le> \<I>(X;Y)"
  using assms by (simp add: mutual_information_positive_generic)

subsection {* Entropy *}

abbreviation (in information_space)
  entropy_Pow ("\<H>'(_')") where
  "\<H>(X) \<equiv> entropy b \<lparr> space = X`space M, sets = Pow (X`space M), measure = extreal\<circ>distribution X \<rparr> X"

lemma (in information_space) entropy_generic_eq:
  fixes X :: "'a \<Rightarrow> 'c"
  assumes MX: "finite_random_variable MX X"
  shows "entropy b MX X = -(\<Sum> x \<in> space MX. distribution X {x} * log b (distribution X {x}))"
proof -
  interpret MX: finite_prob_space "MX\<lparr>measure := extreal\<circ>distribution X\<rparr>"
    using MX by (rule distribution_finite_prob_space)
  let "?X x" = "distribution X {x}"
  let "?XX x y" = "joint_distribution X X {(x, y)}"

  { fix x y :: 'c
    { assume "x \<noteq> y"
      then have "(\<lambda>x. (X x, X x)) -` {(x,y)} \<inter> space M = {}" by auto
      then have "joint_distribution X X {(x, y)} = 0" by (simp add: distribution_def) }
    then have "?XX x y * log b (?XX x y / (?X x * ?X y)) =
        (if x = y then - ?X y * log b (?X y) else 0)"
      by (auto simp: log_simps zero_less_mult_iff) }
  note remove_XX = this

  show ?thesis
    unfolding entropy_def mutual_information_generic_eq[OF MX MX]
    unfolding setsum_cartesian_product[symmetric] setsum_negf[symmetric] remove_XX
    using MX.finite_space by (auto simp: setsum_cases)
qed

lemma (in information_space) entropy_eq:
  assumes "simple_function M X"
  shows "\<H>(X) = -(\<Sum> x \<in> X ` space M. distribution X {x} * log b (distribution X {x}))"
  using assms by (simp add: entropy_generic_eq)

lemma (in information_space) entropy_positive:
  "simple_function M X \<Longrightarrow> 0 \<le> \<H>(X)"
  unfolding entropy_def by (simp add: mutual_information_positive)

lemma (in information_space) entropy_certainty_eq_0:
  assumes X: "simple_function M X" and "x \<in> X ` space M" and "distribution X {x} = 1"
  shows "\<H>(X) = 0"
proof -
  let ?X = "\<lparr> space = X ` space M, sets = Pow (X ` space M), measure = extreal\<circ>distribution X\<rparr>"
  note simple_function_imp_finite_random_variable[OF `simple_function M X`]
  from distribution_finite_prob_space[OF this, of "\<lparr> measure = extreal\<circ>distribution X \<rparr>"]
  interpret X: finite_prob_space ?X by simp
  have "distribution X (X ` space M - {x}) = distribution X (X ` space M) - distribution X {x}"
    using X.measure_compl[of "{x}"] assms by auto
  also have "\<dots> = 0" using X.prob_space assms by auto
  finally have X0: "distribution X (X ` space M - {x}) = 0" by auto
  { fix y assume *: "y \<in> X ` space M"
    { assume asm: "y \<noteq> x"
      with * have "{y} \<subseteq> X ` space M - {x}" by auto
      from X.measure_mono[OF this] X0 asm *
      have "distribution X {y} = 0"  by (auto intro: antisym) }
    then have "distribution X {y} = (if x = y then 1 else 0)"
      using assms by auto }
  note fi = this
  have y: "\<And>y. (if x = y then 1 else 0) * log b (if x = y then 1 else 0) = 0" by simp
  show ?thesis unfolding entropy_eq[OF `simple_function M X`] by (auto simp: y fi)
qed

lemma (in information_space) entropy_le_card_not_0:
  assumes X: "simple_function M X"
  shows "\<H>(X) \<le> log b (card (X ` space M \<inter> {x. distribution X {x} \<noteq> 0}))"
proof -
  let "?p x" = "distribution X {x}"
  have "\<H>(X) = (\<Sum>x\<in>X`space M. ?p x * log b (1 / ?p x))"
    unfolding entropy_eq[OF X] setsum_negf[symmetric]
    by (auto intro!: setsum_cong simp: log_simps)
  also have "\<dots> \<le> log b (\<Sum>x\<in>X`space M. ?p x * (1 / ?p x))"
    using not_empty b_gt_1 `simple_function M X` sum_over_space_real_distribution[OF X]
    by (intro log_setsum') (auto simp: simple_function_def)
  also have "\<dots> = log b (\<Sum>x\<in>X`space M. if ?p x \<noteq> 0 then 1 else 0)"
    by (intro arg_cong[where f="\<lambda>X. log b X"] setsum_cong) auto
  finally show ?thesis
    using `simple_function M X` by (auto simp: setsum_cases real_eq_of_nat simple_function_def)
qed

lemma (in prob_space) measure'_translate:
  assumes X: "random_variable S X" and A: "A \<in> sets S"
  shows "finite_measure.\<mu>' (S\<lparr> measure := extreal\<circ>distribution X \<rparr>) A = distribution X A"
proof -
  interpret S: prob_space "S\<lparr> measure := extreal\<circ>distribution X \<rparr>"
    using distribution_prob_space[OF X] .
  from A show "S.\<mu>' A = distribution X A"
    unfolding S.\<mu>'_def by (simp add: distribution_def_raw \<mu>'_def)
qed

lemma (in information_space) entropy_uniform_max:
  assumes X: "simple_function M X"
  assumes "\<And>x y. \<lbrakk> x \<in> X ` space M ; y \<in> X ` space M \<rbrakk> \<Longrightarrow> distribution X {x} = distribution X {y}"
  shows "\<H>(X) = log b (real (card (X ` space M)))"
proof -
  let ?X = "\<lparr> space = X ` space M, sets = Pow (X ` space M), measure = undefined\<rparr>\<lparr> measure := extreal\<circ>distribution X\<rparr>"
  note frv = simple_function_imp_finite_random_variable[OF X]
  from distribution_finite_prob_space[OF this, of "\<lparr> measure = extreal\<circ>distribution X \<rparr>"]
  interpret X: finite_prob_space ?X by simp
  note rv = finite_random_variableD[OF frv]
  have card_gt0: "0 < card (X ` space M)" unfolding card_gt_0_iff
    using `simple_function M X` not_empty by (auto simp: simple_function_def)
  { fix x assume "x \<in> space ?X"
    moreover then have "X.\<mu>' {x} = 1 / card (space ?X)"
    proof (rule X.uniform_prob)
      fix x y assume "x \<in> space ?X" "y \<in> space ?X"
      with assms(2)[of x y] show "X.\<mu>' {x} = X.\<mu>' {y}"
        by (subst (1 2) measure'_translate[OF rv]) auto
    qed
    ultimately have "distribution X {x} = 1 / card (space ?X)"
      by (subst (asm) measure'_translate[OF rv]) auto }
  thus ?thesis
    using not_empty X.finite_space b_gt_1 card_gt0
    by (simp add: entropy_eq[OF `simple_function M X`] real_eq_of_nat[symmetric] log_simps)
qed

lemma (in information_space) entropy_le_card:
  assumes "simple_function M X"
  shows "\<H>(X) \<le> log b (real (card (X ` space M)))"
proof cases
  assume "X ` space M \<inter> {x. distribution X {x} \<noteq> 0} = {}"
  then have "\<And>x. x\<in>X`space M \<Longrightarrow> distribution X {x} = 0" by auto
  moreover
  have "0 < card (X`space M)"
    using `simple_function M X` not_empty
    by (auto simp: card_gt_0_iff simple_function_def)
  then have "log b 1 \<le> log b (real (card (X`space M)))"
    using b_gt_1 by (intro log_le) auto
  ultimately show ?thesis using assms by (simp add: entropy_eq)
next
  assume False: "X ` space M \<inter> {x. distribution X {x} \<noteq> 0} \<noteq> {}"
  have "card (X ` space M \<inter> {x. distribution X {x} \<noteq> 0}) \<le> card (X ` space M)"
    (is "?A \<le> ?B") using assms not_empty by (auto intro!: card_mono simp: simple_function_def)
  note entropy_le_card_not_0[OF assms]
  also have "log b (real ?A) \<le> log b (real ?B)"
    using b_gt_1 False not_empty `?A \<le> ?B` assms
    by (auto intro!: log_le simp: card_gt_0_iff simp: simple_function_def)
  finally show ?thesis .
qed

lemma (in information_space) entropy_commute:
  assumes "simple_function M X" "simple_function M Y"
  shows "\<H>(\<lambda>x. (X x, Y x)) = \<H>(\<lambda>x. (Y x, X x))"
proof -
  have sf: "simple_function M (\<lambda>x. (X x, Y x))" "simple_function M (\<lambda>x. (Y x, X x))"
    using assms by (auto intro: simple_function_Pair)
  have *: "(\<lambda>x. (Y x, X x))`space M = (\<lambda>(a,b). (b,a))`(\<lambda>x. (X x, Y x))`space M"
    by auto
  have inj: "\<And>X. inj_on (\<lambda>(a,b). (b,a)) X"
    by (auto intro!: inj_onI)
  show ?thesis
    unfolding sf[THEN entropy_eq] unfolding * setsum_reindex[OF inj]
    by (simp add: joint_distribution_commute[of Y X] split_beta)
qed

lemma (in information_space) entropy_eq_cartesian_product:
  assumes "simple_function M X" "simple_function M Y"
  shows "\<H>(\<lambda>x. (X x, Y x)) = -(\<Sum>x\<in>X`space M. \<Sum>y\<in>Y`space M.
    joint_distribution X Y {(x,y)} * log b (joint_distribution X Y {(x,y)}))"
proof -
  have sf: "simple_function M (\<lambda>x. (X x, Y x))"
    using assms by (auto intro: simple_function_Pair)
  { fix x assume "x\<notin>(\<lambda>x. (X x, Y x))`space M"
    then have "(\<lambda>x. (X x, Y x)) -` {x} \<inter> space M = {}" by auto
    then have "joint_distribution X Y {x} = 0"
      unfolding distribution_def by auto }
  then show ?thesis using sf assms
    unfolding entropy_eq[OF sf] neg_equal_iff_equal setsum_cartesian_product
    by (auto intro!: setsum_mono_zero_cong_left simp: simple_function_def)
qed

subsection {* Conditional Mutual Information *}

definition (in prob_space)
  "conditional_mutual_information b MX MY MZ X Y Z \<equiv>
    mutual_information b MX (MY \<Otimes>\<^isub>M MZ) X (\<lambda>x. (Y x, Z x)) -
    mutual_information b MX MZ X Z"

abbreviation (in information_space)
  conditional_mutual_information_Pow ("\<I>'( _ ; _ | _ ')") where
  "\<I>(X ; Y | Z) \<equiv> conditional_mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M), measure = extreal\<circ>distribution X \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M), measure = extreal\<circ>distribution Y \<rparr>
    \<lparr> space = Z`space M, sets = Pow (Z`space M), measure = extreal\<circ>distribution Z \<rparr>
    X Y Z"

lemma (in information_space) conditional_mutual_information_generic_eq:
  assumes MX: "finite_random_variable MX X"
    and MY: "finite_random_variable MY Y"
    and MZ: "finite_random_variable MZ Z"
  shows "conditional_mutual_information b MX MY MZ X Y Z = (\<Sum>(x, y, z) \<in> space MX \<times> space MY \<times> space MZ.
             distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} *
             log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} /
    (joint_distribution X Z {(x, z)} * (joint_distribution Y Z {(y,z)} / distribution Z {z}))))"
  (is "_ = (\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * log b (?XYZ x y z / (?XZ x z * (?YZ y z / ?Z z))))")
proof -
  let ?X = "\<lambda>x. distribution X {x}"
  note finite_var = MX MY MZ
  note YZ = finite_random_variable_pairI[OF finite_var(2,3)]
  note XYZ = finite_random_variable_pairI[OF MX YZ]
  note XZ = finite_random_variable_pairI[OF finite_var(1,3)]
  note ZX = finite_random_variable_pairI[OF finite_var(3,1)]
  note YZX = finite_random_variable_pairI[OF finite_var(2) ZX]
  note order1 =
    finite_distribution_order(5,6)[OF finite_var(1) YZ]
    finite_distribution_order(5,6)[OF finite_var(1,3)]

  note random_var = finite_var[THEN finite_random_variableD]
  note finite = finite_var(1) YZ finite_var(3) XZ YZX

  have order2: "\<And>x y z. \<lbrakk>x \<in> space MX; y \<in> space MY; z \<in> space MZ; joint_distribution X Z {(x, z)} = 0\<rbrakk>
          \<Longrightarrow> joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)} = 0"
    unfolding joint_distribution_commute_singleton[of X]
    unfolding joint_distribution_assoc_singleton[symmetric]
    using finite_distribution_order(6)[OF finite_var(2) ZX]
    by auto

  have "(\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * log b (?XYZ x y z / (?XZ x z * (?YZ y z / ?Z z)))) =
    (\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * (log b (?XYZ x y z / (?X x * ?YZ y z)) - log b (?XZ x z / (?X x * ?Z z))))"
    (is "(\<Sum>(x, y, z)\<in>?S. ?L x y z) = (\<Sum>(x, y, z)\<in>?S. ?R x y z)")
  proof (safe intro!: setsum_cong)
    fix x y z assume space: "x \<in> space MX" "y \<in> space MY" "z \<in> space MZ"
    show "?L x y z = ?R x y z"
    proof cases
      assume "?XYZ x y z \<noteq> 0"
      with space have "0 < ?X x" "0 < ?Z z" "0 < ?XZ x z" "0 < ?YZ y z" "0 < ?XYZ x y z"
        using order1 order2 by (auto simp: less_le)
      with b_gt_1 show ?thesis
        by (simp add: log_mult log_divide zero_less_mult_iff zero_less_divide_iff)
    qed simp
  qed
  also have "\<dots> = (\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * log b (?XYZ x y z / (?X x * ?YZ y z))) -
                  (\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * log b (?XZ x z / (?X x * ?Z z)))"
    by (auto simp add: setsum_subtractf[symmetric] field_simps intro!: setsum_cong)
  also have "(\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * log b (?XZ x z / (?X x * ?Z z))) =
             (\<Sum>(x, z)\<in>space MX \<times> space MZ. ?XZ x z * log b (?XZ x z / (?X x * ?Z z)))"
    unfolding setsum_cartesian_product[symmetric] setsum_commute[of _ _ "space MY"]
              setsum_left_distrib[symmetric]
    unfolding joint_distribution_commute_singleton[of X]
    unfolding joint_distribution_assoc_singleton[symmetric]
    using setsum_joint_distribution_singleton[OF finite_var(2) ZX]
    by (intro setsum_cong refl) (simp add: space_pair_measure)
  also have "(\<Sum>(x, y, z)\<in>?S. ?XYZ x y z * log b (?XYZ x y z / (?X x * ?YZ y z))) -
             (\<Sum>(x, z)\<in>space MX \<times> space MZ. ?XZ x z * log b (?XZ x z / (?X x * ?Z z))) =
             conditional_mutual_information b MX MY MZ X Y Z"
    unfolding conditional_mutual_information_def
    unfolding mutual_information_generic_eq[OF finite_var(1,3)]
    unfolding mutual_information_generic_eq[OF finite_var(1) YZ]
    by (simp add: space_sigma space_pair_measure setsum_cartesian_product')
  finally show ?thesis by simp
qed

lemma (in information_space) conditional_mutual_information_eq:
  assumes "simple_function M X" "simple_function M Y" "simple_function M Z"
  shows "\<I>(X;Y|Z) = (\<Sum>(x, y, z) \<in> X`space M \<times> Y`space M \<times> Z`space M.
             distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} *
             log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} /
    (joint_distribution X Z {(x, z)} * joint_distribution Y Z {(y,z)} / distribution Z {z})))"
  by (subst conditional_mutual_information_generic_eq[OF assms[THEN simple_function_imp_finite_random_variable]])
     simp

lemma (in information_space) conditional_mutual_information_eq_mutual_information:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<I>(X ; Y) = \<I>(X ; Y | (\<lambda>x. ()))"
proof -
  have [simp]: "(\<lambda>x. ()) ` space M = {()}" using not_empty by auto
  have C: "simple_function M (\<lambda>x. ())" by auto
  show ?thesis
    unfolding conditional_mutual_information_eq[OF X Y C]
    unfolding mutual_information_eq[OF X Y]
    by (simp add: setsum_cartesian_product' distribution_remove_const)
qed

lemma (in prob_space) distribution_unit[simp]: "distribution (\<lambda>x. ()) {()} = 1"
  unfolding distribution_def using prob_space by auto

lemma (in prob_space) joint_distribution_unit[simp]: "distribution (\<lambda>x. (X x, ())) {(a, ())} = distribution X {a}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>'])

lemma (in prob_space) setsum_distribution:
  assumes X: "finite_random_variable MX X" shows "(\<Sum>a\<in>space MX. distribution X {a}) = 1"
  using setsum_joint_distribution[OF assms, of "\<lparr> space = UNIV, sets = Pow UNIV \<rparr>" "\<lambda>x. ()" "{()}"]
  using sigma_algebra_Pow[of "UNIV::unit set" "()"] by simp

lemma (in prob_space) setsum_real_distribution:
  fixes MX :: "('c, 'd) measure_space_scheme"
  assumes X: "finite_random_variable MX X" shows "(\<Sum>a\<in>space MX. distribution X {a}) = 1"
  using setsum_joint_distribution[OF assms, of "\<lparr> space = UNIV, sets = Pow UNIV, measure = undefined \<rparr>" "\<lambda>x. ()" "{()}"]
  using sigma_algebra_Pow[of "UNIV::unit set" "\<lparr> measure = undefined \<rparr>"]
  by auto

lemma (in information_space) conditional_mutual_information_generic_positive:
  assumes X: "finite_random_variable MX X" and Y: "finite_random_variable MY Y" and Z: "finite_random_variable MZ Z"
  shows "0 \<le> conditional_mutual_information b MX MY MZ X Y Z"
proof (cases "space MX \<times> space MY \<times> space MZ = {}")
  case True show ?thesis
    unfolding conditional_mutual_information_generic_eq[OF assms] True
    by simp
next
  case False
  let ?dXYZ = "distribution (\<lambda>x. (X x, Y x, Z x))"
  let ?dXZ = "joint_distribution X Z"
  let ?dYZ = "joint_distribution Y Z"
  let ?dX = "distribution X"
  let ?dZ = "distribution Z"
  let ?M = "space MX \<times> space MY \<times> space MZ"

  note YZ = finite_random_variable_pairI[OF Y Z]
  note XZ = finite_random_variable_pairI[OF X Z]
  note ZX = finite_random_variable_pairI[OF Z X]
  note YZ = finite_random_variable_pairI[OF Y Z]
  note XYZ = finite_random_variable_pairI[OF X YZ]
  note finite = Z YZ XZ XYZ
  have order: "\<And>x y z. \<lbrakk>x \<in> space MX; y \<in> space MY; z \<in> space MZ; joint_distribution X Z {(x, z)} = 0\<rbrakk>
          \<Longrightarrow> joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)} = 0"
    unfolding joint_distribution_commute_singleton[of X]
    unfolding joint_distribution_assoc_singleton[symmetric]
    using finite_distribution_order(6)[OF Y ZX]
    by auto

  note order = order
    finite_distribution_order(5,6)[OF X YZ]
    finite_distribution_order(5,6)[OF Y Z]

  have "- conditional_mutual_information b MX MY MZ X Y Z = - (\<Sum>(x, y, z) \<in> ?M. ?dXYZ {(x, y, z)} *
    log b (?dXYZ {(x, y, z)} / (?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z})))"
    unfolding conditional_mutual_information_generic_eq[OF assms] neg_equal_iff_equal by auto
  also have "\<dots> \<le> log b (\<Sum>(x, y, z) \<in> ?M. ?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z})"
    unfolding split_beta'
  proof (rule log_setsum_divide)
    show "?M \<noteq> {}" using False by simp
    show "1 < b" using b_gt_1 .

    show "finite ?M" using assms
      unfolding finite_sigma_algebra_def finite_sigma_algebra_axioms_def by auto

    show "(\<Sum>x\<in>?M. ?dXYZ {(fst x, fst (snd x), snd (snd x))}) = 1"
      unfolding setsum_cartesian_product'
      unfolding setsum_commute[of _ "space MY"]
      unfolding setsum_commute[of _ "space MZ"]
      by (simp_all add: space_pair_measure
                        setsum_joint_distribution_singleton[OF X YZ]
                        setsum_joint_distribution_singleton[OF Y Z]
                        setsum_distribution[OF Z])

    fix x assume "x \<in> ?M"
    let ?x = "(fst x, fst (snd x), snd (snd x))"

    show "0 \<le> ?dXYZ {?x}"
      "0 \<le> ?dXZ {(fst x, snd (snd x))} * ?dYZ {(fst (snd x), snd (snd x))} / ?dZ {snd (snd x)}"
     by (simp_all add: mult_nonneg_nonneg divide_nonneg_nonneg)

    assume *: "0 < ?dXYZ {?x}"
    with `x \<in> ?M` finite order show "0 < ?dXZ {(fst x, snd (snd x))} * ?dYZ {(fst (snd x), snd (snd x))} / ?dZ {snd (snd x)}"
      by (cases x) (auto simp add: zero_le_mult_iff zero_le_divide_iff less_le)
  qed
  also have "(\<Sum>(x, y, z) \<in> ?M. ?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z}) = (\<Sum>z\<in>space MZ. ?dZ {z})"
    apply (simp add: setsum_cartesian_product')
    apply (subst setsum_commute)
    apply (subst (2) setsum_commute)
    by (auto simp: setsum_divide_distrib[symmetric] setsum_product[symmetric]
                   setsum_joint_distribution_singleton[OF X Z]
                   setsum_joint_distribution_singleton[OF Y Z]
          intro!: setsum_cong)
  also have "log b (\<Sum>z\<in>space MZ. ?dZ {z}) = 0"
    unfolding setsum_real_distribution[OF Z] by simp
  finally show ?thesis by simp
qed

lemma (in information_space) conditional_mutual_information_positive:
  assumes "simple_function M X" and "simple_function M Y" and "simple_function M Z"
  shows "0 \<le> \<I>(X;Y|Z)"
  by (rule conditional_mutual_information_generic_positive[OF assms[THEN simple_function_imp_finite_random_variable]])

subsection {* Conditional Entropy *}

definition (in prob_space)
  "conditional_entropy b S T X Y = conditional_mutual_information b S S T X X Y"

abbreviation (in information_space)
  conditional_entropy_Pow ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> conditional_entropy b
    \<lparr> space = X`space M, sets = Pow (X`space M), measure = extreal\<circ>distribution X \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M), measure = extreal\<circ>distribution Y \<rparr> X Y"

lemma (in information_space) conditional_entropy_positive:
  "simple_function M X \<Longrightarrow> simple_function M Y \<Longrightarrow> 0 \<le> \<H>(X | Y)"
  unfolding conditional_entropy_def by (auto intro!: conditional_mutual_information_positive)

lemma (in information_space) conditional_entropy_generic_eq:
  fixes MX :: "('c, 'd) measure_space_scheme" and MY :: "('e, 'f) measure_space_scheme"
  assumes MX: "finite_random_variable MX X"
  assumes MZ: "finite_random_variable MZ Z"
  shows "conditional_entropy b MX MZ X Z =
     - (\<Sum>(x, z)\<in>space MX \<times> space MZ.
         joint_distribution X Z {(x, z)} * log b (joint_distribution X Z {(x, z)} / distribution Z {z}))"
proof -
  interpret MX: finite_sigma_algebra MX using MX by simp
  interpret MZ: finite_sigma_algebra MZ using MZ by simp
  let "?XXZ x y z" = "joint_distribution X (\<lambda>x. (X x, Z x)) {(x, y, z)}"
  let "?XZ x z" = "joint_distribution X Z {(x, z)}"
  let "?Z z" = "distribution Z {z}"
  let "?f x y z" = "log b (?XXZ x y z * ?Z z / (?XZ x z * ?XZ y z))"
  { fix x z have "?XXZ x x z = ?XZ x z"
      unfolding distribution_def by (auto intro!: arg_cong[where f=\<mu>']) }
  note this[simp]
  { fix x x' :: 'c and z assume "x' \<noteq> x"
    then have "?XXZ x x' z = 0"
      by (auto simp: distribution_def empty_measure'[symmetric]
               simp del: empty_measure' intro!: arg_cong[where f=\<mu>']) }
  note this[simp]
  { fix x x' z assume *: "x \<in> space MX" "z \<in> space MZ"
    then have "(\<Sum>x'\<in>space MX. ?XXZ x x' z * ?f x x' z)
      = (\<Sum>x'\<in>space MX. if x = x' then ?XZ x z * ?f x x z else 0)"
      by (auto intro!: setsum_cong)
    also have "\<dots> = ?XZ x z * ?f x x z"
      using `x \<in> space MX` by (simp add: setsum_cases[OF MX.finite_space])
    also have "\<dots> = ?XZ x z * log b (?Z z / ?XZ x z)" by auto
    also have "\<dots> = - ?XZ x z * log b (?XZ x z / ?Z z)"
      using finite_distribution_order(6)[OF MX MZ]
      by (auto simp: log_simps field_simps zero_less_mult_iff)
    finally have "(\<Sum>x'\<in>space MX. ?XXZ x x' z * ?f x x' z) = - ?XZ x z * log b (?XZ x z / ?Z z)" . }
  note * = this
  show ?thesis
    unfolding conditional_entropy_def
    unfolding conditional_mutual_information_generic_eq[OF MX MX MZ]
    by (auto simp: setsum_cartesian_product' setsum_negf[symmetric]
                   setsum_commute[of _ "space MZ"] *
             intro!: setsum_cong)
qed

lemma (in information_space) conditional_entropy_eq:
  assumes "simple_function M X" "simple_function M Z"
  shows "\<H>(X | Z) =
     - (\<Sum>(x, z)\<in>X ` space M \<times> Z ` space M.
         joint_distribution X Z {(x, z)} *
         log b (joint_distribution X Z {(x, z)} / distribution Z {z}))"
  by (subst conditional_entropy_generic_eq[OF assms[THEN simple_function_imp_finite_random_variable]])
     simp

lemma (in information_space) conditional_entropy_eq_ce_with_hypothesis:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows "\<H>(X | Y) =
    -(\<Sum>y\<in>Y`space M. distribution Y {y} *
      (\<Sum>x\<in>X`space M. joint_distribution X Y {(x,y)} / distribution Y {(y)} *
              log b (joint_distribution X Y {(x,y)} / distribution Y {(y)})))"
  unfolding conditional_entropy_eq[OF assms]
  using finite_distribution_order(5,6)[OF assms[THEN simple_function_imp_finite_random_variable]]
  by (auto simp: setsum_cartesian_product'  setsum_commute[of _ "Y`space M"] setsum_right_distrib
           intro!: setsum_cong)

lemma (in information_space) conditional_entropy_eq_cartesian_product:
  assumes "simple_function M X" "simple_function M Y"
  shows "\<H>(X | Y) = -(\<Sum>x\<in>X`space M. \<Sum>y\<in>Y`space M.
    joint_distribution X Y {(x,y)} *
    log b (joint_distribution X Y {(x,y)} / distribution Y {y}))"
  unfolding conditional_entropy_eq[OF assms]
  by (auto intro!: setsum_cong simp: setsum_cartesian_product')

subsection {* Equalities *}

lemma (in information_space) mutual_information_eq_entropy_conditional_entropy:
  assumes X: "simple_function M X" and Z: "simple_function M Z"
  shows  "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)"
proof -
  let "?XZ x z" = "joint_distribution X Z {(x, z)}"
  let "?Z z" = "distribution Z {z}"
  let "?X x" = "distribution X {x}"
  note fX = X[THEN simple_function_imp_finite_random_variable]
  note fZ = Z[THEN simple_function_imp_finite_random_variable]
  note finite_distribution_order[OF fX fZ, simp]
  { fix x z assume "x \<in> X`space M" "z \<in> Z`space M"
    have "?XZ x z * log b (?XZ x z / (?X x * ?Z z)) =
          ?XZ x z * log b (?XZ x z / ?Z z) - ?XZ x z * log b (?X x)"
      by (auto simp: log_simps zero_le_mult_iff field_simps less_le) }
  note * = this
  show ?thesis
    unfolding entropy_eq[OF X] conditional_entropy_eq[OF X Z] mutual_information_eq[OF X Z]
    using setsum_joint_distribution_singleton[OF fZ fX, unfolded joint_distribution_commute_singleton[of Z X]]
    by (simp add: * setsum_cartesian_product' setsum_subtractf setsum_left_distrib[symmetric]
                     setsum_distribution)
qed

lemma (in information_space) conditional_entropy_less_eq_entropy:
  assumes X: "simple_function M X" and Z: "simple_function M Z"
  shows "\<H>(X | Z) \<le> \<H>(X)"
proof -
  have "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)" using mutual_information_eq_entropy_conditional_entropy[OF assms] .
  with mutual_information_positive[OF X Z] entropy_positive[OF X]
  show ?thesis by auto
qed

lemma (in information_space) entropy_chain_rule:
  assumes X: "simple_function M X" and Y: "simple_function M Y"
  shows  "\<H>(\<lambda>x. (X x, Y x)) = \<H>(X) + \<H>(Y|X)"
proof -
  let "?XY x y" = "joint_distribution X Y {(x, y)}"
  let "?Y y" = "distribution Y {y}"
  let "?X x" = "distribution X {x}"
  note fX = X[THEN simple_function_imp_finite_random_variable]
  note fY = Y[THEN simple_function_imp_finite_random_variable]
  note finite_distribution_order[OF fX fY, simp]
  { fix x y assume "x \<in> X`space M" "y \<in> Y`space M"
    have "?XY x y * log b (?XY x y / ?X x) =
          ?XY x y * log b (?XY x y) - ?XY x y * log b (?X x)"
      by (auto simp: log_simps zero_le_mult_iff field_simps less_le) }
  note * = this
  show ?thesis
    using setsum_joint_distribution_singleton[OF fY fX]
    unfolding entropy_eq[OF X] conditional_entropy_eq_cartesian_product[OF Y X] entropy_eq_cartesian_product[OF X Y]
    unfolding joint_distribution_commute_singleton[of Y X] setsum_commute[of _ "X`space M"]
    by (simp add: * setsum_subtractf setsum_left_distrib[symmetric])
qed

section {* Partitioning *}

definition "subvimage A f g \<longleftrightarrow> (\<forall>x \<in> A. f -` {f x} \<inter> A \<subseteq> g -` {g x} \<inter> A)"

lemma subvimageI:
  assumes "\<And>x y. \<lbrakk> x \<in> A ; y \<in> A ; f x = f y \<rbrakk> \<Longrightarrow> g x = g y"
  shows "subvimage A f g"
  using assms unfolding subvimage_def by blast

lemma subvimageE[consumes 1]:
  assumes "subvimage A f g"
  obtains "\<And>x y. \<lbrakk> x \<in> A ; y \<in> A ; f x = f y \<rbrakk> \<Longrightarrow> g x = g y"
  using assms unfolding subvimage_def by blast

lemma subvimageD:
  "\<lbrakk> subvimage A f g ; x \<in> A ; y \<in> A ; f x = f y \<rbrakk> \<Longrightarrow> g x = g y"
  using assms unfolding subvimage_def by blast

lemma subvimage_subset:
  "\<lbrakk> subvimage B f g ; A \<subseteq> B \<rbrakk> \<Longrightarrow> subvimage A f g"
  unfolding subvimage_def by auto

lemma subvimage_idem[intro]: "subvimage A g g"
  by (safe intro!: subvimageI)

lemma subvimage_comp_finer[intro]:
  assumes svi: "subvimage A g h"
  shows "subvimage A g (f \<circ> h)"
proof (rule subvimageI, simp)
  fix x y assume "x \<in> A" "y \<in> A" "g x = g y"
  from svi[THEN subvimageD, OF this]
  show "f (h x) = f (h y)" by simp
qed

lemma subvimage_comp_gran:
  assumes svi: "subvimage A g h"
  assumes inj: "inj_on f (g ` A)"
  shows "subvimage A (f \<circ> g) h"
  by (rule subvimageI) (auto intro!: subvimageD[OF svi] simp: inj_on_iff[OF inj])

lemma subvimage_comp:
  assumes svi: "subvimage (f ` A) g h"
  shows "subvimage A (g \<circ> f) (h \<circ> f)"
  by (rule subvimageI) (auto intro!: svi[THEN subvimageD])

lemma subvimage_trans:
  assumes fg: "subvimage A f g"
  assumes gh: "subvimage A g h"
  shows "subvimage A f h"
  by (rule subvimageI) (auto intro!: fg[THEN subvimageD] gh[THEN subvimageD])

lemma subvimage_translator:
  assumes svi: "subvimage A f g"
  shows "\<exists>h. \<forall>x \<in> A. h (f x)  = g x"
proof (safe intro!: exI[of _ "\<lambda>x. (THE z. z \<in> (g ` (f -` {x} \<inter> A)))"])
  fix x assume "x \<in> A"
  show "(THE x'. x' \<in> (g ` (f -` {f x} \<inter> A))) = g x"
    by (rule theI2[of _ "g x"])
      (insert `x \<in> A`, auto intro!: svi[THEN subvimageD])
qed

lemma subvimage_translator_image:
  assumes svi: "subvimage A f g"
  shows "\<exists>h. h ` f ` A = g ` A"
proof -
  from subvimage_translator[OF svi]
  obtain h where "\<And>x. x \<in> A \<Longrightarrow> h (f x) = g x" by auto
  thus ?thesis
    by (auto intro!: exI[of _ h]
      simp: image_compose[symmetric] comp_def cong: image_cong)
qed

lemma subvimage_finite:
  assumes svi: "subvimage A f g" and fin: "finite (f`A)"
  shows "finite (g`A)"
proof -
  from subvimage_translator_image[OF svi]
  obtain h where "g`A = h`f`A" by fastsimp
  with fin show "finite (g`A)" by simp
qed

lemma subvimage_disj:
  assumes svi: "subvimage A f g"
  shows "f -` {x} \<inter> A \<subseteq> g -` {y} \<inter> A \<or>
      f -` {x} \<inter> g -` {y} \<inter> A = {}" (is "?sub \<or> ?dist")
proof (rule disjCI)
  assume "\<not> ?dist"
  then obtain z where "z \<in> A" and "x = f z" and "y = g z" by auto
  thus "?sub" using svi unfolding subvimage_def by auto
qed

lemma setsum_image_split:
  assumes svi: "subvimage A f g" and fin: "finite (f ` A)"
  shows "(\<Sum>x\<in>f`A. h x) = (\<Sum>y\<in>g`A. \<Sum>x\<in>f`(g -` {y} \<inter> A). h x)"
    (is "?lhs = ?rhs")
proof -
  have "f ` A =
      snd ` (SIGMA x : g ` A. f ` (g -` {x} \<inter> A))"
      (is "_ = snd ` ?SIGMA")
    unfolding image_split_eq_Sigma[symmetric]
    by (simp add: image_compose[symmetric] comp_def)
  moreover
  have snd_inj: "inj_on snd ?SIGMA"
    unfolding image_split_eq_Sigma[symmetric]
    by (auto intro!: inj_onI subvimageD[OF svi])
  ultimately
  have "(\<Sum>x\<in>f`A. h x) = (\<Sum>(x,y)\<in>?SIGMA. h y)"
    by (auto simp: setsum_reindex intro: setsum_cong)
  also have "... = ?rhs"
    using subvimage_finite[OF svi fin] fin
    apply (subst setsum_Sigma[symmetric])
    by (auto intro!: finite_subset[of _ "f`A"])
  finally show ?thesis .
qed

lemma (in information_space) entropy_partition:
  assumes sf: "simple_function M X" "simple_function M P"
  assumes svi: "subvimage (space M) X P"
  shows "\<H>(X) = \<H>(P) + \<H>(X|P)"
proof -
  let "?XP x p" = "joint_distribution X P {(x, p)}"
  let "?X x" = "distribution X {x}"
  let "?P p" = "distribution P {p}"
  note fX = sf(1)[THEN simple_function_imp_finite_random_variable]
  note fP = sf(2)[THEN simple_function_imp_finite_random_variable]
  note finite_distribution_order[OF fX fP, simp]
  have "(\<Sum>x\<in>X ` space M. ?X x * log b (?X x)) =
    (\<Sum>y\<in>P `space M. \<Sum>x\<in>X ` space M. ?XP x y * log b (?XP x y))"
  proof (subst setsum_image_split[OF svi],
      safe intro!: setsum_mono_zero_cong_left imageI)
    show "finite (X ` space M)" "finite (X ` space M)" "finite (P ` space M)"
      using sf unfolding simple_function_def by auto
  next
    fix p x assume in_space: "p \<in> space M" "x \<in> space M"
    assume "?XP (X x) (P p) * log b (?XP (X x) (P p)) \<noteq> 0"
    hence "(\<lambda>x. (X x, P x)) -` {(X x, P p)} \<inter> space M \<noteq> {}" by (auto simp: distribution_def)
    with svi[unfolded subvimage_def, rule_format, OF `x \<in> space M`]
    show "x \<in> P -` {P p}" by auto
  next
    fix p x assume in_space: "p \<in> space M" "x \<in> space M"
    assume "P x = P p"
    from this[symmetric] svi[unfolded subvimage_def, rule_format, OF `x \<in> space M`]
    have "X -` {X x} \<inter> space M \<subseteq> P -` {P p} \<inter> space M"
      by auto
    hence "(\<lambda>x. (X x, P x)) -` {(X x, P p)} \<inter> space M = X -` {X x} \<inter> space M"
      by auto
    thus "?X (X x) * log b (?X (X x)) = ?XP (X x) (P p) * log b (?XP (X x) (P p))"
      by (auto simp: distribution_def)
  qed
  moreover have "\<And>x y. ?XP x y * log b (?XP x y / ?P y) =
      ?XP x y * log b (?XP x y) - ?XP x y * log b (?P y)"
    by (auto simp add: log_simps zero_less_mult_iff field_simps)
  ultimately show ?thesis
    unfolding sf[THEN entropy_eq] conditional_entropy_eq[OF sf]
    using setsum_joint_distribution_singleton[OF fX fP]
    by (simp add: setsum_cartesian_product' setsum_subtractf setsum_distribution
      setsum_left_distrib[symmetric] setsum_commute[where B="P`space M"])
qed

corollary (in information_space) entropy_data_processing:
  assumes X: "simple_function M X" shows "\<H>(f \<circ> X) \<le> \<H>(X)"
proof -
  note X
  moreover have fX: "simple_function M (f \<circ> X)" using X by auto
  moreover have "subvimage (space M) X (f \<circ> X)" by auto
  ultimately have "\<H>(X) = \<H>(f\<circ>X) + \<H>(X|f\<circ>X)" by (rule entropy_partition)
  then show "\<H>(f \<circ> X) \<le> \<H>(X)"
    by (auto intro: conditional_entropy_positive[OF X fX])
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
    by (auto intro!: mutual_information_cong simp: entropy_def the_inv_into_f_f[OF inj])
  also have "... \<le> \<H>(f \<circ> X)"
    using entropy_data_processing[OF sf] .
  finally show "\<H>(X) \<le> \<H>(f \<circ> X)" .
qed

end
