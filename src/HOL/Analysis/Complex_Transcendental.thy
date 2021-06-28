section \<open>Complex Transcendental Functions\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Complex_Transcendental
imports
  Complex_Analysis_Basics Summation_Tests "HOL-Library.Periodic_Fun"
begin

subsection\<open>Möbius transformations\<close>

(* TODO: Figure out what to do with Möbius transformations *)
definition\<^marker>\<open>tag important\<close> "moebius a b c d \<equiv> (\<lambda>z. (a*z+b) / (c*z+d :: 'a :: field))"

theorem moebius_inverse:
  assumes "a * d \<noteq> b * c" "c * z + d \<noteq> 0"
  shows   "moebius d (-b) (-c) a (moebius a b c d z) = z"
proof -
  from assms have "(-c) * moebius a b c d z + a \<noteq> 0" unfolding moebius_def
    by (simp add: field_simps)
  with assms show ?thesis
    unfolding moebius_def by (simp add: moebius_def divide_simps) (simp add: algebra_simps)?
qed

lemma moebius_inverse':
  assumes "a * d \<noteq> b * c" "c * z - a \<noteq> 0"
  shows   "moebius a b c d (moebius d (-b) (-c) a z) = z"
  using assms moebius_inverse[of d a "-b" "-c" z]
  by (auto simp: algebra_simps)

lemma cmod_add_real_less:
  assumes "Im z \<noteq> 0" "r\<noteq>0"
    shows "cmod (z + r) < cmod z + \<bar>r\<bar>"
proof (cases z)
  case (Complex x y)
  then have "0 < y * y"
    using assms mult_neg_neg by force
  with assms have "r * x / \<bar>r\<bar> < sqrt (x*x + y*y)"
    by (simp add: real_less_rsqrt power2_eq_square)
  then show ?thesis using assms Complex
    apply (simp add: cmod_def)
    apply (rule power2_less_imp_less, auto)
    apply (simp add: power2_eq_square field_simps)
    done
qed

lemma cmod_diff_real_less: "Im z \<noteq> 0 \<Longrightarrow> x\<noteq>0 \<Longrightarrow> cmod (z - x) < cmod z + \<bar>x\<bar>"
  using cmod_add_real_less [of z "-x"]
  by simp

lemma cmod_square_less_1_plus:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
    shows "(cmod z)\<^sup>2 < 1 + cmod (1 - z\<^sup>2)"
proof (cases "Im z = 0 \<or> Re z = 0")
  case True
  with assms abs_square_less_1 show ?thesis
    by (force simp add: Re_power2 Im_power2 cmod_def)
next
  case False
  with cmod_diff_real_less [of "1 - z\<^sup>2" "1"] show ?thesis
    by (simp add: norm_power Im_power2)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>The Exponential Function\<close>

lemma norm_exp_i_times [simp]: "norm (exp(\<i> * of_real y)) = 1"
  by simp

lemma norm_exp_imaginary: "norm(exp z) = 1 \<Longrightarrow> Re z = 0"
  by simp

lemma field_differentiable_within_exp: "exp field_differentiable (at z within s)"
  using DERIV_exp field_differentiable_at_within field_differentiable_def by blast

lemma continuous_within_exp:
  fixes z::"'a::{real_normed_field,banach}"
  shows "continuous (at z within s) exp"
by (simp add: continuous_at_imp_continuous_within)

lemma holomorphic_on_exp [holomorphic_intros]: "exp holomorphic_on s"
  by (simp add: field_differentiable_within_exp holomorphic_on_def)

lemma holomorphic_on_exp' [holomorphic_intros]:
  "f holomorphic_on s \<Longrightarrow> (\<lambda>x. exp (f x)) holomorphic_on s"
  using holomorphic_on_compose[OF _ holomorphic_on_exp] by (simp add: o_def)

subsection\<open>Euler and de Moivre formulas\<close>

text\<open>The sine series times \<^term>\<open>i\<close>\<close>
lemma sin_i_eq: "(\<lambda>n. (\<i> * sin_coeff n) * z^n) sums (\<i> * sin z)"
proof -
  have "(\<lambda>n. \<i> * sin_coeff n *\<^sub>R z^n) sums (\<i> * sin z)"
    using sin_converges sums_mult by blast
  then show ?thesis
    by (simp add: scaleR_conv_of_real field_simps)
qed

theorem exp_Euler: "exp(\<i> * z) = cos(z) + \<i> * sin(z)"
proof -
  have "(\<lambda>n. (cos_coeff n + \<i> * sin_coeff n) * z^n) = (\<lambda>n. (\<i> * z) ^ n /\<^sub>R (fact n))"
  proof
    fix n
    show "(cos_coeff n + \<i> * sin_coeff n) * z^n = (\<i> * z) ^ n /\<^sub>R (fact n)"
      by (auto simp: cos_coeff_def sin_coeff_def scaleR_conv_of_real field_simps elim!: evenE oddE)
  qed
  also have "... sums (exp (\<i> * z))"
    by (rule exp_converges)
  finally have "(\<lambda>n. (cos_coeff n + \<i> * sin_coeff n) * z^n) sums (exp (\<i> * z))" .
  moreover have "(\<lambda>n. (cos_coeff n + \<i> * sin_coeff n) * z^n) sums (cos z + \<i> * sin z)"
    using sums_add [OF cos_converges [of z] sin_i_eq [of z]]
    by (simp add: field_simps scaleR_conv_of_real)
  ultimately show ?thesis
    using sums_unique2 by blast
qed

corollary\<^marker>\<open>tag unimportant\<close> exp_minus_Euler: "exp(-(\<i> * z)) = cos(z) - \<i> * sin(z)"
  using exp_Euler [of "-z"]
  by simp

lemma sin_exp_eq: "sin z = (exp(\<i> * z) - exp(-(\<i> * z))) / (2*\<i>)"
  by (simp add: exp_Euler exp_minus_Euler)

lemma sin_exp_eq': "sin z = \<i> * (exp(-(\<i> * z)) - exp(\<i> * z)) / 2"
  by (simp add: exp_Euler exp_minus_Euler)

lemma cos_exp_eq:  "cos z = (exp(\<i> * z) + exp(-(\<i> * z))) / 2"
  by (simp add: exp_Euler exp_minus_Euler)

theorem Euler: "exp(z) = of_real(exp(Re z)) *
              (of_real(cos(Im z)) + \<i> * of_real(sin(Im z)))"
by (cases z) (simp add: exp_add exp_Euler cos_of_real exp_of_real sin_of_real Complex_eq)

lemma Re_sin: "Re(sin z) = sin(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by (simp add: sin_exp_eq field_simps Re_divide Im_exp)

lemma Im_sin: "Im(sin z) = cos(Re z) * (exp(Im z) - exp(-(Im z))) / 2"
  by (simp add: sin_exp_eq field_simps Im_divide Re_exp)

lemma Re_cos: "Re(cos z) = cos(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by (simp add: cos_exp_eq field_simps Re_divide Re_exp)

lemma Im_cos: "Im(cos z) = sin(Re z) * (exp(-(Im z)) - exp(Im z)) / 2"
  by (simp add: cos_exp_eq field_simps Im_divide Im_exp)

lemma Re_sin_pos: "0 < Re z \<Longrightarrow> Re z < pi \<Longrightarrow> Re (sin z) > 0"
  by (auto simp: Re_sin Im_sin add_pos_pos sin_gt_zero)

lemma Im_sin_nonneg: "Re z = 0 \<Longrightarrow> 0 \<le> Im z \<Longrightarrow> 0 \<le> Im (sin z)"
  by (simp add: Re_sin Im_sin algebra_simps)

lemma Im_sin_nonneg2: "Re z = pi \<Longrightarrow> Im z \<le> 0 \<Longrightarrow> 0 \<le> Im (sin z)"
  by (simp add: Re_sin Im_sin algebra_simps)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relationships between real and complex trigonometric and hyperbolic functions\<close>

lemma real_sin_eq [simp]: "Re(sin(of_real x)) = sin x"
  by (simp add: sin_of_real)

lemma real_cos_eq [simp]: "Re(cos(of_real x)) = cos x"
  by (simp add: cos_of_real)

lemma DeMoivre: "(cos z + \<i> * sin z) ^ n = cos(n * z) + \<i> * sin(n * z)"
  by (metis exp_Euler [symmetric] exp_of_nat_mult mult.left_commute)

lemma exp_cnj: "cnj (exp z) = exp (cnj z)"
proof -
  have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) = (\<lambda>n. (cnj z)^n /\<^sub>R (fact n))"
    by auto
  also have "... sums (exp (cnj z))"
    by (rule exp_converges)
  finally have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) sums (exp (cnj z))" .
  moreover have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) sums (cnj (exp z))"
    by (metis exp_converges sums_cnj)
  ultimately show ?thesis
    using sums_unique2
    by blast
qed

lemma cnj_sin: "cnj(sin z) = sin(cnj z)"
  by (simp add: sin_exp_eq exp_cnj field_simps)

lemma cnj_cos: "cnj(cos z) = cos(cnj z)"
  by (simp add: cos_exp_eq exp_cnj field_simps)

lemma field_differentiable_at_sin: "sin field_differentiable at z"
  using DERIV_sin field_differentiable_def by blast

lemma field_differentiable_within_sin: "sin field_differentiable (at z within S)"
  by (simp add: field_differentiable_at_sin field_differentiable_at_within)

lemma field_differentiable_at_cos: "cos field_differentiable at z"
  using DERIV_cos field_differentiable_def by blast

lemma field_differentiable_within_cos: "cos field_differentiable (at z within S)"
  by (simp add: field_differentiable_at_cos field_differentiable_at_within)

lemma holomorphic_on_sin: "sin holomorphic_on S"
  by (simp add: field_differentiable_within_sin holomorphic_on_def)

lemma holomorphic_on_cos: "cos holomorphic_on S"
  by (simp add: field_differentiable_within_cos holomorphic_on_def)

lemma holomorphic_on_sin' [holomorphic_intros]:
  assumes "f holomorphic_on A"
  shows   "(\<lambda>x. sin (f x)) holomorphic_on A"
  using holomorphic_on_compose[OF assms holomorphic_on_sin] by (simp add: o_def)

lemma holomorphic_on_cos' [holomorphic_intros]:
  assumes "f holomorphic_on A"
  shows   "(\<lambda>x. cos (f x)) holomorphic_on A"
  using holomorphic_on_compose[OF assms holomorphic_on_cos] by (simp add: o_def)

subsection\<^marker>\<open>tag unimportant\<close>\<open>More on the Polar Representation of Complex Numbers\<close>

lemma exp_Complex: "exp(Complex r t) = of_real(exp r) * Complex (cos t) (sin t)"
  by (simp add: Complex_eq exp_add exp_Euler exp_of_real sin_of_real cos_of_real)

lemma exp_eq_1: "exp z = 1 \<longleftrightarrow> Re(z) = 0 \<and> (\<exists>n::int. Im(z) = of_int (2 * n) * pi)"
                 (is "?lhs = ?rhs")
proof
  assume "exp z = 1"
  then have "Re z = 0"
    by (metis exp_eq_one_iff norm_exp_eq_Re norm_one)
  with \<open>?lhs\<close> show ?rhs
    by (metis Re_exp complex_Re_of_int cos_one_2pi_int exp_zero mult.commute mult_numeral_1 numeral_One of_int_mult of_int_numeral)
next
  assume ?rhs then show ?lhs
    using Im_exp Re_exp complex_eq_iff
    by (simp add: cos_one_2pi_int cos_one_sin_zero mult.commute)
qed

lemma exp_eq: "exp w = exp z \<longleftrightarrow> (\<exists>n::int. w = z + (of_int (2 * n) * pi) * \<i>)"
                (is "?lhs = ?rhs")
proof -
  have "exp w = exp z \<longleftrightarrow> exp (w-z) = 1"
    by (simp add: exp_diff)
  also have "... \<longleftrightarrow> (Re w = Re z \<and> (\<exists>n::int. Im w - Im z = of_int (2 * n) * pi))"
    by (simp add: exp_eq_1)
  also have "... \<longleftrightarrow> ?rhs"
    by (auto simp: algebra_simps intro!: complex_eqI)
  finally show ?thesis .
qed

lemma exp_complex_eqI: "\<bar>Im w - Im z\<bar> < 2*pi \<Longrightarrow> exp w = exp z \<Longrightarrow> w = z"
  by (auto simp: exp_eq abs_mult)

lemma exp_integer_2pi:
  assumes "n \<in> \<int>"
  shows "exp((2 * n * pi) * \<i>) = 1"
proof -
  have "exp((2 * n * pi) * \<i>) = exp 0"
    using assms unfolding Ints_def exp_eq by auto
  also have "... = 1"
    by simp
  finally show ?thesis .
qed

lemma exp_plus_2pin [simp]: "exp (z + \<i> * (of_int n * (of_real pi * 2))) = exp z"
  by (simp add: exp_eq)

lemma exp_integer_2pi_plus1:
  assumes "n \<in> \<int>"
  shows "exp(((2 * n + 1) * pi) * \<i>) = - 1"
proof -
  from assms obtain n' where [simp]: "n = of_int n'"
    by (auto simp: Ints_def)
  have "exp(((2 * n + 1) * pi) * \<i>) = exp (pi * \<i>)"
    using assms by (subst exp_eq) (auto intro!: exI[of _ n'] simp: algebra_simps)
  also have "... = - 1"
    by simp
  finally show ?thesis .
qed

lemma inj_on_exp_pi:
  fixes z::complex shows "inj_on exp (ball z pi)"
proof (clarsimp simp: inj_on_def exp_eq)
  fix y n
  assume "dist z (y + 2 * of_int n * of_real pi * \<i>) < pi"
         "dist z y < pi"
  then have "dist y (y + 2 * of_int n * of_real pi * \<i>) < pi+pi"
    using dist_commute_lessI dist_triangle_less_add by blast
  then have "norm (2 * of_int n * of_real pi * \<i>) < 2*pi"
    by (simp add: dist_norm)
  then show "n = 0"
    by (auto simp: norm_mult)
qed

lemma cmod_add_squared:
  fixes r1 r2::real
  assumes "r1 \<ge> 0" "r2 \<ge> 0"
  shows "(cmod (r1 * exp (\<i> * \<theta>1) + r2 * exp (\<i> * \<theta>2)))\<^sup>2 = r1\<^sup>2 + r2\<^sup>2 + 2 * r1 * r2 * cos (\<theta>1 - \<theta>2)" (is "(cmod (?z1 + ?z2))\<^sup>2 = ?rhs")
proof -
  have "(cmod (?z1 + ?z2))\<^sup>2 = (?z1 + ?z2) * cnj (?z1 + ?z2)"
    by (rule complex_norm_square)
  also have "\<dots> = (?z1 * cnj ?z1 + ?z2 * cnj ?z2) + (?z1 * cnj ?z2 + cnj ?z1 * ?z2)"
    by (simp add: algebra_simps)
  also have "\<dots> = (norm ?z1)\<^sup>2 + (norm ?z2)\<^sup>2 + 2 * Re (?z1 * cnj ?z2)"
    unfolding complex_norm_square [symmetric] cnj_add_mult_eq_Re by simp
  also have "\<dots> = ?rhs"
    by (simp add: norm_mult) (simp add: exp_Euler complex_is_Real_iff [THEN iffD1] cos_diff algebra_simps)
  finally show ?thesis
    using of_real_eq_iff by blast
qed

lemma cmod_diff_squared:
  fixes r1 r2::real
  assumes "r1 \<ge> 0" "r2 \<ge> 0"
  shows "(cmod (r1 * exp (\<i> * \<theta>1) - r2 * exp (\<i> * \<theta>2)))\<^sup>2 = r1\<^sup>2 + r2\<^sup>2 - 2*r1*r2*cos (\<theta>1 - \<theta>2)" (is "(cmod (?z1 - ?z2))\<^sup>2 = ?rhs")
proof -
  have "exp (\<i> * (\<theta>2 + pi)) = - exp (\<i> * \<theta>2)"
    by (simp add: exp_Euler cos_plus_pi sin_plus_pi)
  then have "(cmod (?z1 - ?z2))\<^sup>2 = cmod (?z1 + r2 * exp (\<i> * (\<theta>2 + pi))) ^2"
    by simp
  also have "\<dots> = r1\<^sup>2 + r2\<^sup>2 + 2*r1*r2*cos (\<theta>1 - (\<theta>2 + pi))"
    using assms cmod_add_squared by blast
  also have "\<dots> = ?rhs"
    by (simp add: add.commute diff_add_eq_diff_diff_swap)
  finally show ?thesis .
qed

lemma polar_convergence:
  fixes R::real
  assumes "\<And>j. r j > 0" "R > 0"
  shows "((\<lambda>j. r j * exp (\<i> * \<theta> j)) \<longlonglongrightarrow> (R * exp (\<i> * \<Theta>))) \<longleftrightarrow>
         (r \<longlonglongrightarrow> R) \<and> (\<exists>k. (\<lambda>j. \<theta> j - of_int (k j) * (2 * pi)) \<longlonglongrightarrow> \<Theta>)"    (is "(?z \<longlonglongrightarrow> ?Z) = ?rhs")
proof
  assume L: "?z \<longlonglongrightarrow> ?Z"
  have rR: "r \<longlonglongrightarrow> R"
    using tendsto_norm [OF L] assms by (auto simp: norm_mult abs_of_pos)
  moreover obtain k where "(\<lambda>j. \<theta> j - of_int (k j) * (2 * pi)) \<longlonglongrightarrow> \<Theta>"
  proof -
    have "cos (\<theta> j - \<Theta>) = ((r j)\<^sup>2 + R\<^sup>2 - (norm(?z j - ?Z))\<^sup>2) / (2 * R * r j)" for j
      apply (subst cmod_diff_squared)
      using assms by (auto simp: field_split_simps less_le)
    moreover have "(\<lambda>j. ((r j)\<^sup>2 + R\<^sup>2 - (norm(?z j - ?Z))\<^sup>2) / (2 * R * r j)) \<longlonglongrightarrow> ((R\<^sup>2 + R\<^sup>2 - (norm(?Z - ?Z))\<^sup>2) / (2 * R * R))"
      by (intro L rR tendsto_intros) (use \<open>R > 0\<close> in force)
    moreover have "((R\<^sup>2 + R\<^sup>2 - (norm(?Z - ?Z))\<^sup>2) / (2 * R * R)) = 1"
      using \<open>R > 0\<close> by (simp add: power2_eq_square field_split_simps)
    ultimately have "(\<lambda>j. cos (\<theta> j - \<Theta>)) \<longlonglongrightarrow> 1"
      by auto
    then show ?thesis
      using that cos_diff_limit_1 by blast
  qed
  ultimately show ?rhs
    by metis
next
  assume R: ?rhs
  show "?z \<longlonglongrightarrow> ?Z"
  proof (rule tendsto_mult)
    show "(\<lambda>x. complex_of_real (r x)) \<longlonglongrightarrow> of_real R"
      using R by (auto simp: tendsto_of_real_iff)
    obtain k where "(\<lambda>j. \<theta> j - of_int (k j) * (2 * pi)) \<longlonglongrightarrow> \<Theta>"
      using R by metis
    then have "(\<lambda>j. complex_of_real (\<theta> j - of_int (k j) * (2 * pi))) \<longlonglongrightarrow> of_real \<Theta>"
      using tendsto_of_real_iff by force
    then have "(\<lambda>j.  exp (\<i> * of_real (\<theta> j - of_int (k j) * (2 * pi)))) \<longlonglongrightarrow> exp (\<i> * \<Theta>)"
      using tendsto_mult [OF tendsto_const] isCont_exp isCont_tendsto_compose by blast
    moreover have "exp (\<i> * of_real (\<theta> j - of_int (k j) * (2 * pi))) = exp (\<i> * \<theta> j)" for j
      unfolding exp_eq
      by (rule_tac x="- k j" in exI) (auto simp: algebra_simps)
    ultimately show "(\<lambda>j. exp (\<i> * \<theta> j)) \<longlonglongrightarrow> exp (\<i> * \<Theta>)"
      by auto
  qed
qed

lemma sin_cos_eq_iff: "sin y = sin x \<and> cos y = cos x \<longleftrightarrow> (\<exists>n::int. y = x + 2 * pi * n)"
proof -
  { assume "sin y = sin x" "cos y = cos x"
    then have "cos (y-x) = 1"
      using cos_add [of y "-x"] by simp
    then have "\<exists>n::int. y-x = 2 * pi * n"
      using cos_one_2pi_int by auto }
  then show ?thesis
  apply (auto simp: sin_add cos_add)
  apply (metis add.commute diff_add_cancel)
  done
qed

lemma exp_i_ne_1:
  assumes "0 < x" "x < 2*pi"
  shows "exp(\<i> * of_real x) \<noteq> 1"
proof
  assume "exp (\<i> * of_real x) = 1"
  then have "exp (\<i> * of_real x) = exp 0"
    by simp
  then obtain n where "\<i> * of_real x = (of_int (2 * n) * pi) * \<i>"
    by (simp only: Ints_def exp_eq) auto
  then have "of_real x = (of_int (2 * n) * pi)"
    by (metis complex_i_not_zero mult.commute mult_cancel_left of_real_eq_iff real_scaleR_def scaleR_conv_of_real)
  then have "x = (of_int (2 * n) * pi)"
    by simp
  then show False using assms
    by (cases n) (auto simp: zero_less_mult_iff mult_less_0_iff)
qed

lemma sin_eq_0:
  fixes z::complex
  shows "sin z = 0 \<longleftrightarrow> (\<exists>n::int. z = of_real(n * pi))"
  by (simp add: sin_exp_eq exp_eq)

lemma cos_eq_0:
  fixes z::complex
  shows "cos z = 0 \<longleftrightarrow> (\<exists>n::int. z = of_real(n * pi) + of_real pi/2)"
  using sin_eq_0 [of "z - of_real pi/2"]
  by (simp add: sin_diff algebra_simps)

lemma cos_eq_1:
  fixes z::complex
  shows "cos z = 1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi))"
proof -
  have "cos z = cos (2*(z/2))"
    by simp
  also have "... = 1 - 2 * sin (z/2) ^ 2"
    by (simp only: cos_double_sin)
  finally have [simp]: "cos z = 1 \<longleftrightarrow> sin (z/2) = 0"
    by simp
  show ?thesis
    by (auto simp: sin_eq_0)
qed

lemma csin_eq_1:
  fixes z::complex
  shows "sin z = 1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + of_real pi/2)"
  using cos_eq_1 [of "z - of_real pi/2"]
  by (simp add: cos_diff algebra_simps)

lemma csin_eq_minus1:
  fixes z::complex
  shows "sin z = -1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + 3/2*pi)"
        (is "_ = ?rhs")
proof -
  have "sin z = -1 \<longleftrightarrow> sin (-z) = 1"
    by (simp add: equation_minus_iff)
  also have "... \<longleftrightarrow> (\<exists>n::int. -z = of_real(2 * n * pi) + of_real pi/2)"
    by (simp only: csin_eq_1)
  also have "... \<longleftrightarrow> (\<exists>n::int. z = - of_real(2 * n * pi) - of_real pi/2)"
    by (rule iff_exI) (metis add.inverse_inverse add_uminus_conv_diff minus_add_distrib)
  also have "... = ?rhs"
    apply safe
    apply (rule_tac [2] x="-(x+1)" in exI)
    apply (rule_tac x="-(x+1)" in exI)
    apply (simp_all add: algebra_simps)
    done
  finally show ?thesis .
qed

lemma ccos_eq_minus1:
  fixes z::complex
  shows "cos z = -1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + pi)"
  using csin_eq_1 [of "z - of_real pi/2"]
  by (simp add: sin_diff algebra_simps equation_minus_iff)

lemma sin_eq_1: "sin x = 1 \<longleftrightarrow> (\<exists>n::int. x = (2 * n + 1 / 2) * pi)"
                (is "_ = ?rhs")
proof -
  have "sin x = 1 \<longleftrightarrow> sin (complex_of_real x) = 1"
    by (metis of_real_1 one_complex.simps(1) real_sin_eq sin_of_real)
  also have "... \<longleftrightarrow> (\<exists>n::int. complex_of_real x = of_real(2 * n * pi) + of_real pi/2)"
    by (simp only: csin_eq_1)
  also have "... \<longleftrightarrow> (\<exists>n::int. x = of_real(2 * n * pi) + of_real pi/2)"
    by (rule iff_exI) (auto simp: algebra_simps intro: injD [OF inj_of_real [where 'a = complex]])
  also have "... = ?rhs"
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma sin_eq_minus1: "sin x = -1 \<longleftrightarrow> (\<exists>n::int. x = (2*n + 3/2) * pi)"  (is "_ = ?rhs")
proof -
  have "sin x = -1 \<longleftrightarrow> sin (complex_of_real x) = -1"
    by (metis Re_complex_of_real of_real_def scaleR_minus1_left sin_of_real)
  also have "... \<longleftrightarrow> (\<exists>n::int. complex_of_real x = of_real(2 * n * pi) + 3/2*pi)"
    by (simp only: csin_eq_minus1)
  also have "... \<longleftrightarrow> (\<exists>n::int. x = of_real(2 * n * pi) + 3/2*pi)"
    by (rule iff_exI) (auto simp: algebra_simps intro: injD [OF inj_of_real [where 'a = complex]])
  also have "... = ?rhs"
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma cos_eq_minus1: "cos x = -1 \<longleftrightarrow> (\<exists>n::int. x = (2*n + 1) * pi)"
                      (is "_ = ?rhs")
proof -
  have "cos x = -1 \<longleftrightarrow> cos (complex_of_real x) = -1"
    by (metis Re_complex_of_real of_real_def scaleR_minus1_left cos_of_real)
  also have "... \<longleftrightarrow> (\<exists>n::int. complex_of_real x = of_real(2 * n * pi) + pi)"
    by (simp only: ccos_eq_minus1)
  also have "... \<longleftrightarrow> (\<exists>n::int. x = of_real(2 * n * pi) + pi)"
    by (rule iff_exI) (auto simp: algebra_simps intro: injD [OF inj_of_real [where 'a = complex]])
  also have "... = ?rhs"
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma dist_exp_i_1: "norm(exp(\<i> * of_real t) - 1) = 2 * \<bar>sin(t / 2)\<bar>"
proof -
  have "sqrt (2 - cos t * 2) = 2 * \<bar>sin (t / 2)\<bar>"
    using cos_double_sin [of "t/2"] by (simp add: real_sqrt_mult)
  then show ?thesis
    by (simp add: exp_Euler cmod_def power2_diff sin_of_real cos_of_real algebra_simps)
qed

lemma sin_cx_2pi [simp]: "\<lbrakk>z = of_int m; even m\<rbrakk> \<Longrightarrow> sin (z * complex_of_real pi) = 0"
  by (simp add: sin_eq_0)

lemma cos_cx_2pi [simp]: "\<lbrakk>z = of_int m; even m\<rbrakk> \<Longrightarrow> cos (z * complex_of_real pi) = 1"
  using cos_eq_1 by auto

lemma complex_sin_eq:
  fixes w :: complex
  shows "sin w = sin z \<longleftrightarrow> (\<exists>n \<in> \<int>. w = z + of_real(2*n*pi) \<or> w = -z + of_real((2*n + 1)*pi))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "sin w - sin z = 0"
    by (auto simp: algebra_simps)
  then have "sin ((w - z) / 2)*cos ((w + z) / 2) = 0"
    by (auto simp: sin_diff_sin)
  then consider "sin ((w - z) / 2) = 0" | "cos ((w + z) / 2) = 0"
    using mult_eq_0_iff by blast
  then show ?rhs
  proof cases
    case 1
    then show ?thesis
      by (simp add: sin_eq_0 algebra_simps) (metis Ints_of_int of_real_of_int_eq)
  next
    case 2
    then show ?thesis
      by (simp add: cos_eq_0 algebra_simps) (metis Ints_of_int of_real_of_int_eq)
  qed
next
  assume ?rhs
  then consider n::int where "w = z + of_real (2 * of_int n * pi)" 
              | n::int where  " w = -z + of_real ((2 * of_int n + 1) * pi)"
    using Ints_cases by blast
  then show ?lhs
  proof cases
    case 1
    then show ?thesis
      using Periodic_Fun.sin.plus_of_int [of z n]
      by (auto simp: algebra_simps)
  next
    case 2
    then show ?thesis 
      using Periodic_Fun.sin.plus_of_int [of "-z" "n"]
      apply (simp add: algebra_simps)
      by (metis add.commute add.inverse_inverse add_diff_cancel_left diff_add_cancel sin_plus_pi)
  qed
qed

lemma complex_cos_eq:
  fixes w :: complex
  shows "cos w = cos z \<longleftrightarrow> (\<exists>n \<in> \<int>. w = z + of_real(2*n*pi) \<or> w = -z + of_real(2*n*pi))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "cos w - cos z = 0"
    by (auto simp: algebra_simps)
  then have "sin ((w + z) / 2) * sin ((z - w) / 2) = 0"
    by (auto simp: cos_diff_cos)
  then consider "sin ((w + z) / 2) = 0" | "sin ((z - w) / 2) = 0"
    using mult_eq_0_iff by blast
  then show ?rhs
  proof cases
    case 1
    then obtain n where "w + z = of_int n * (complex_of_real pi * 2)"
      by (auto simp: sin_eq_0 algebra_simps)
    then have "w = -z + of_real(2 * of_int n * pi)"
      by (auto simp: algebra_simps)
    then show ?thesis
      using Ints_of_int by blast
  next
    case 2
    then obtain n where "z = w + of_int n * (complex_of_real pi * 2)"
      by (auto simp: sin_eq_0 algebra_simps)
    then have "w = z + complex_of_real (2 * of_int(-n) * pi)"
      by (auto simp: algebra_simps)
    then show ?thesis
      using Ints_of_int by blast
  qed
next
  assume ?rhs
  then obtain n::int where w: "w = z + of_real (2* of_int n*pi) \<or>
                               w = -z + of_real(2*n*pi)"
    using Ints_cases  by (metis of_int_mult of_int_numeral)
  then show ?lhs
    using Periodic_Fun.cos.plus_of_int [of z n]
    apply (simp add: algebra_simps)
    by (metis cos.plus_of_int cos_minus minus_add_cancel mult.commute)
qed

lemma sin_eq:
   "sin x = sin y \<longleftrightarrow> (\<exists>n \<in> \<int>. x = y + 2*n*pi \<or> x = -y + (2*n + 1)*pi)"
  using complex_sin_eq [of x y]
  by (simp only: sin_of_real Re_complex_of_real of_real_add [symmetric] of_real_minus [symmetric] of_real_mult [symmetric] of_real_eq_iff)

lemma cos_eq:
   "cos x = cos y \<longleftrightarrow> (\<exists>n \<in> \<int>. x = y + 2*n*pi \<or> x = -y + 2*n*pi)"
  using complex_cos_eq [of x y]
  by (simp only: cos_of_real Re_complex_of_real of_real_add [symmetric] of_real_minus [symmetric] of_real_mult [symmetric] of_real_eq_iff)

lemma sinh_complex:
  fixes z :: complex
  shows "(exp z - inverse (exp z)) / 2 = -\<i> * sin(\<i> * z)"
  by (simp add: sin_exp_eq field_split_simps exp_minus)

lemma sin_i_times:
  fixes z :: complex
  shows "sin(\<i> * z) = \<i> * ((exp z - inverse (exp z)) / 2)"
  using sinh_complex by auto

lemma sinh_real:
  fixes x :: real
  shows "of_real((exp x - inverse (exp x)) / 2) = -\<i> * sin(\<i> * of_real x)"
  by (simp add: exp_of_real sin_i_times)

lemma cosh_complex:
  fixes z :: complex
  shows "(exp z + inverse (exp z)) / 2 = cos(\<i> * z)"
  by (simp add: cos_exp_eq field_split_simps exp_minus exp_of_real)

lemma cosh_real:
  fixes x :: real
  shows "of_real((exp x + inverse (exp x)) / 2) = cos(\<i> * of_real x)"
  by (simp add: cos_exp_eq field_split_simps exp_minus exp_of_real)

lemmas cos_i_times = cosh_complex [symmetric]

lemma norm_cos_squared:
  "norm(cos z) ^ 2 = cos(Re z) ^ 2 + (exp(Im z) - inverse(exp(Im z))) ^ 2 / 4"
proof (cases z)
  case (Complex x1 x2)
  then show ?thesis
    apply (simp only: cos_add cmod_power2 cos_of_real sin_of_real Complex_eq)
    apply (simp add: cos_exp_eq sin_exp_eq exp_minus exp_of_real Re_divide Im_divide power_divide)
    apply (simp only: left_diff_distrib [symmetric] power_mult_distrib sin_squared_eq)
    apply (simp add: power2_eq_square field_split_simps)
    done
qed

lemma norm_sin_squared:
  "norm(sin z) ^ 2 = (exp(2 * Im z) + inverse(exp(2 * Im z)) - 2 * cos(2 * Re z)) / 4"
proof (cases z)
  case (Complex x1 x2)
  then show ?thesis
    apply (simp only: sin_add cmod_power2 cos_of_real sin_of_real cos_double_cos exp_double Complex_eq)
    apply (simp add: cos_exp_eq sin_exp_eq exp_minus exp_of_real Re_divide Im_divide power_divide)
    apply (simp only: left_diff_distrib [symmetric] power_mult_distrib cos_squared_eq)
    apply (simp add: power2_eq_square field_split_simps)
    done
qed

lemma exp_uminus_Im: "exp (- Im z) \<le> exp (cmod z)"
  using abs_Im_le_cmod linear order_trans by fastforce

lemma norm_cos_le:
  fixes z::complex
  shows "norm(cos z) \<le> exp(norm z)"
proof -
  have "Im z \<le> cmod z"
    using abs_Im_le_cmod abs_le_D1 by auto
  then have "exp (- Im z) + exp (Im z) \<le> exp (cmod z) * 2"
    by (metis exp_uminus_Im add_mono exp_le_cancel_iff mult_2_right)
  then show ?thesis
    by (force simp add: cos_exp_eq norm_divide intro: order_trans [OF norm_triangle_ineq])
qed

lemma norm_cos_plus1_le:
  fixes z::complex
  shows "norm(1 + cos z) \<le> 2 * exp(norm z)"
proof -
  have mono: "\<And>u w z::real. (1 \<le> w | 1 \<le> z) \<Longrightarrow> (w \<le> u & z \<le> u) \<Longrightarrow> 2 + w + z \<le> 4 * u"
      by arith
  have *: "Im z \<le> cmod z"
    using abs_Im_le_cmod abs_le_D1 by auto
  have triangle3: "\<And>x y z. norm(x + y + z) \<le> norm(x) + norm(y) + norm(z)"
    by (simp add: norm_add_rule_thm)
  have "norm(1 + cos z) = cmod (1 + (exp (\<i> * z) + exp (- (\<i> * z))) / 2)"
    by (simp add: cos_exp_eq)
  also have "... = cmod ((2 + exp (\<i> * z) + exp (- (\<i> * z))) / 2)"
    by (simp add: field_simps)
  also have "... = cmod (2 + exp (\<i> * z) + exp (- (\<i> * z))) / 2"
    by (simp add: norm_divide)
  finally show ?thesis
    by (metis exp_eq_one_iff exp_le_cancel_iff mult_2 norm_cos_le norm_ge_zero norm_one norm_triangle_mono)
qed

lemma sinh_conv_sin: "sinh z = -\<i> * sin (\<i>*z)"
  by (simp add: sinh_field_def sin_i_times exp_minus)

lemma cosh_conv_cos: "cosh z = cos (\<i>*z)"
  by (simp add: cosh_field_def cos_i_times exp_minus)

lemma tanh_conv_tan: "tanh z = -\<i> * tan (\<i>*z)"
  by (simp add: tanh_def sinh_conv_sin cosh_conv_cos tan_def)

lemma sin_conv_sinh: "sin z = -\<i> * sinh (\<i>*z)"
  by (simp add: sinh_conv_sin)

lemma cos_conv_cosh: "cos z = cosh (\<i>*z)"
  by (simp add: cosh_conv_cos)

lemma tan_conv_tanh: "tan z = -\<i> * tanh (\<i>*z)"
  by (simp add: tan_def sin_conv_sinh cos_conv_cosh tanh_def)

lemma sinh_complex_eq_iff:
  "sinh (z :: complex) = sinh w \<longleftrightarrow>
      (\<exists>n\<in>\<int>. z = w - 2 * \<i> * of_real n * of_real pi \<or>
              z = -(2 * complex_of_real n + 1) * \<i> * complex_of_real pi - w)" (is "_ = ?rhs")
proof -
  have "sinh z = sinh w \<longleftrightarrow> sin (\<i> * z) = sin (\<i> * w)"
    by (simp add: sinh_conv_sin)
  also have "\<dots> \<longleftrightarrow> ?rhs"
    by (subst complex_sin_eq) (force simp: field_simps complex_eq_iff)
  finally show ?thesis .
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Taylor series for complex exponential, sine and cosine\<close>

declare power_Suc [simp del]

lemma Taylor_exp_field:
  fixes z::"'a::{banach,real_normed_field}"
  shows "norm (exp z - (\<Sum>i\<le>n. z ^ i / fact i)) \<le> exp (norm z) * (norm z ^ Suc n) / fact n"
proof (rule field_Taylor[of _ n "\<lambda>k. exp" "exp (norm z)" 0 z, simplified])
  show "convex (closed_segment 0 z)"
    by (rule convex_closed_segment [of 0 z])
next
  fix k x
  assume "x \<in> closed_segment 0 z" "k \<le> n"
  show "(exp has_field_derivative exp x) (at x within closed_segment 0 z)"
    using DERIV_exp DERIV_subset by blast
next
  fix x
  assume x: "x \<in> closed_segment 0 z"
  have "norm (exp x) \<le> exp (norm x)"
    by (rule norm_exp)
  also have "norm x \<le> norm z"
    using x by (auto simp: closed_segment_def intro!: mult_left_le_one_le)
  finally show "norm (exp x) \<le> exp (norm z)"
    by simp
qed auto

lemma Taylor_exp:
  "norm(exp z - (\<Sum>k\<le>n. z ^ k / (fact k))) \<le> exp\<bar>Re z\<bar> * (norm z) ^ (Suc n) / (fact n)"
proof (rule complex_Taylor [of _ n "\<lambda>k. exp" "exp\<bar>Re z\<bar>" 0 z, simplified])
  show "convex (closed_segment 0 z)"
    by (rule convex_closed_segment [of 0 z])
next
  fix k x
  assume "x \<in> closed_segment 0 z" "k \<le> n"
  show "(exp has_field_derivative exp x) (at x within closed_segment 0 z)"
    using DERIV_exp DERIV_subset by blast
next
  fix x
  assume "x \<in> closed_segment 0 z"
  then obtain u where u: "x = complex_of_real u * z" "0 \<le> u" "u \<le> 1"
    by (auto simp: closed_segment_def scaleR_conv_of_real)
  then have "u * Re z \<le> \<bar>Re z\<bar>"
    by (metis abs_ge_self abs_ge_zero mult.commute mult.right_neutral mult_mono)
  then show "Re x \<le> \<bar>Re z\<bar>"
    by (simp add: u)
qed auto

lemma
  assumes "0 \<le> u" "u \<le> 1"
  shows cmod_sin_le_exp: "cmod (sin (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>"
    and cmod_cos_le_exp: "cmod (cos (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>"
proof -
  have mono: "\<And>u w z::real. w \<le> u \<Longrightarrow> z \<le> u \<Longrightarrow> (w + z)/2 \<le> u"
    by simp
  have *: "(cmod (exp (\<i> * (u * z))) + cmod (exp (- (\<i> * (u * z)))) ) / 2 \<le> exp \<bar>Im z\<bar>"
  proof (rule mono)
    show "cmod (exp (\<i> * (u * z))) \<le> exp \<bar>Im z\<bar>"
      using assms
      by (auto simp: abs_if mult_left_le_one_le not_less intro: order_trans [of _ 0])
    show "cmod (exp (- (\<i> * (u * z)))) \<le> exp \<bar>Im z\<bar>"
      using assms
      by (auto simp: abs_if mult_left_le_one_le mult_nonneg_nonpos intro: order_trans [of _ 0])
  qed
  have "cmod (sin (u *\<^sub>R z)) = cmod (exp (\<i> * (u * z)) - exp (- (\<i> * (u * z)))) / 2"
    by (auto simp: scaleR_conv_of_real norm_mult norm_power sin_exp_eq norm_divide)
  also have "... \<le> (cmod (exp (\<i> * (u * z))) + cmod (exp (- (\<i> * (u * z)))) ) / 2"
    by (intro divide_right_mono norm_triangle_ineq4) simp
  also have "... \<le> exp \<bar>Im z\<bar>"
    by (rule *)
  finally show "cmod (sin (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>" .
  have "cmod (cos (u *\<^sub>R z)) = cmod (exp (\<i> * (u * z)) + exp (- (\<i> * (u * z)))) / 2"
    by (auto simp: scaleR_conv_of_real norm_mult norm_power cos_exp_eq norm_divide)
  also have "... \<le> (cmod (exp (\<i> * (u * z))) + cmod (exp (- (\<i> * (u * z)))) ) / 2"
    by (intro divide_right_mono norm_triangle_ineq) simp
  also have "... \<le> exp \<bar>Im z\<bar>"
    by (rule *)
  finally show "cmod (cos (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>" .
qed

lemma Taylor_sin:
  "norm(sin z - (\<Sum>k\<le>n. complex_of_real (sin_coeff k) * z ^ k))
   \<le> exp\<bar>Im z\<bar> * (norm z) ^ (Suc n) / (fact n)"
proof -
  have mono: "\<And>u w z::real. w \<le> u \<Longrightarrow> z \<le> u \<Longrightarrow> w + z \<le> u*2"
      by arith
  have *: "cmod (sin z -
                 (\<Sum>i\<le>n. (-1) ^ (i div 2) * (if even i then sin 0 else cos 0) * z ^ i / (fact i)))
           \<le> exp \<bar>Im z\<bar> * cmod z ^ Suc n / (fact n)"
  proof (rule complex_Taylor [of "closed_segment 0 z" n
                                 "\<lambda>k x. (-1)^(k div 2) * (if even k then sin x else cos x)"
                                 "exp\<bar>Im z\<bar>" 0 z,  simplified])
    fix k x
    show "((\<lambda>x. (- 1) ^ (k div 2) * (if even k then sin x else cos x)) has_field_derivative
            (- 1) ^ (Suc k div 2) * (if odd k then sin x else cos x))
            (at x within closed_segment 0 z)"
      apply (auto simp: power_Suc)
      apply (intro derivative_eq_intros | simp)+
      done
  next
    fix x
    assume "x \<in> closed_segment 0 z"
    then show "cmod ((- 1) ^ (Suc n div 2) * (if odd n then sin x else cos x)) \<le> exp \<bar>Im z\<bar>"
      by (auto simp: closed_segment_def norm_mult norm_power cmod_sin_le_exp cmod_cos_le_exp)
  qed
  have **: "\<And>k. complex_of_real (sin_coeff k) * z ^ k
            = (-1)^(k div 2) * (if even k then sin 0 else cos 0) * z^k / of_nat (fact k)"
    by (auto simp: sin_coeff_def elim!: oddE)
  show ?thesis
    by (simp add: ** order_trans [OF _ *])
qed

lemma Taylor_cos:
  "norm(cos z - (\<Sum>k\<le>n. complex_of_real (cos_coeff k) * z ^ k))
   \<le> exp\<bar>Im z\<bar> * (norm z) ^ Suc n / (fact n)"
proof -
  have mono: "\<And>u w z::real. w \<le> u \<Longrightarrow> z \<le> u \<Longrightarrow> w + z \<le> u*2"
      by arith
  have *: "cmod (cos z -
                 (\<Sum>i\<le>n. (-1) ^ (Suc i div 2) * (if even i then cos 0 else sin 0) * z ^ i / (fact i)))
           \<le> exp \<bar>Im z\<bar> * cmod z ^ Suc n / (fact n)"
  proof (rule complex_Taylor [of "closed_segment 0 z" n "\<lambda>k x. (-1)^(Suc k div 2) * (if even k then cos x else sin x)" "exp\<bar>Im z\<bar>" 0 z,
simplified])
    fix k x
    assume "x \<in> closed_segment 0 z" "k \<le> n"
    show "((\<lambda>x. (- 1) ^ (Suc k div 2) * (if even k then cos x else sin x)) has_field_derivative
            (- 1) ^ Suc (k div 2) * (if odd k then cos x else sin x))
             (at x within closed_segment 0 z)"
      apply (auto simp: power_Suc)
      apply (intro derivative_eq_intros | simp)+
      done
  next
    fix x
    assume "x \<in> closed_segment 0 z"
    then show "cmod ((- 1) ^ Suc (n div 2) * (if odd n then cos x else sin x)) \<le> exp \<bar>Im z\<bar>"
      by (auto simp: closed_segment_def norm_mult norm_power cmod_sin_le_exp cmod_cos_le_exp)
  qed
  have **: "\<And>k. complex_of_real (cos_coeff k) * z ^ k
            = (-1)^(Suc k div 2) * (if even k then cos 0 else sin 0) * z^k / of_nat (fact k)"
    by (auto simp: cos_coeff_def elim!: evenE)
  show ?thesis
    by (simp add: ** order_trans [OF _ *])
qed

declare power_Suc [simp]

text\<open>32-bit Approximation to e\<close>
lemma e_approx_32: "\<bar>exp(1) - 5837465777 / 2147483648\<bar> \<le> (inverse(2 ^ 32)::real)"
  using Taylor_exp [of 1 14] exp_le
  apply (simp add: sum_distrib_right in_Reals_norm Re_exp atMost_nat_numeral fact_numeral)
  apply (simp only: pos_le_divide_eq [symmetric])
  done

lemma e_less_272: "exp 1 < (272/100::real)"
  using e_approx_32
  by (simp add: abs_if split: if_split_asm)

lemma ln_272_gt_1: "ln (272/100) > (1::real)"
  by (metis e_less_272 exp_less_cancel_iff exp_ln_iff less_trans ln_exp)

text\<open>Apparently redundant. But many arguments involve integers.\<close>
lemma ln3_gt_1: "ln 3 > (1::real)"
  by (simp add: less_trans [OF ln_272_gt_1])

subsection\<open>The argument of a complex number (HOL Light version)\<close>

definition\<^marker>\<open>tag important\<close> is_Arg :: "[complex,real] \<Rightarrow> bool"
  where "is_Arg z r \<equiv> z = of_real(norm z) * exp(\<i> * of_real r)"

definition\<^marker>\<open>tag important\<close> Arg2pi :: "complex \<Rightarrow> real"
  where "Arg2pi z \<equiv> if z = 0 then 0 else THE t. 0 \<le> t \<and> t < 2*pi \<and> is_Arg z t"

lemma is_Arg_2pi_iff: "is_Arg z (r + of_int k * (2 * pi)) \<longleftrightarrow> is_Arg z r"
  by (simp add: algebra_simps is_Arg_def)

lemma is_Arg_eqI:
  assumes r: "is_Arg z r" and s: "is_Arg z s" and rs: "abs (r-s) < 2*pi" and "z \<noteq> 0"
  shows "r = s"
proof -
  have zr: "z = (cmod z) * exp (\<i> * r)" and zs: "z = (cmod z) * exp (\<i> * s)"
    using r s by (auto simp: is_Arg_def)
  with \<open>z \<noteq> 0\<close> have eq: "exp (\<i> * r) = exp (\<i> * s)"
    by (metis mult_eq_0_iff mult_left_cancel)
  have  "\<i> * r = \<i> * s"
    by (rule exp_complex_eqI) (use rs in \<open>auto simp: eq exp_complex_eqI\<close>)
  then show ?thesis
    by simp
qed

text\<open>This function returns the angle of a complex number from its representation in polar coordinates.
Due to periodicity, its range is arbitrary. \<^term>\<open>Arg2pi\<close> follows HOL Light in adopting the interval \<open>[0,2\<pi>)\<close>.
But we have the same periodicity issue with logarithms, and it is usual to adopt the same interval
for the complex logarithm and argument functions. Further on down, we shall define both functions for the interval \<open>(-\<pi>,\<pi>]\<close>.
The present version is provided for compatibility.\<close>

lemma Arg2pi_0 [simp]: "Arg2pi(0) = 0"
  by (simp add: Arg2pi_def)

lemma Arg2pi_unique_lemma:
  assumes z:  "is_Arg z t"
      and z': "is_Arg z t'"
      and t:  "0 \<le> t"  "t < 2*pi"
      and t': "0 \<le> t'" "t' < 2*pi"
      and nz: "z \<noteq> 0"
  shows "t' = t"
proof -
  have [dest]: "\<And>x y z::real. x\<ge>0 \<Longrightarrow> x+y < z \<Longrightarrow> y<z"
    by arith
  have "of_real (cmod z) * exp (\<i> * of_real t') = of_real (cmod z) * exp (\<i> * of_real t)"
    by (metis z z' is_Arg_def)
  then have "exp (\<i> * of_real t') = exp (\<i> * of_real t)"
    by (metis nz mult_left_cancel mult_zero_left z is_Arg_def)
  then have "sin t' = sin t \<and> cos t' = cos t"
    by (metis cis.simps cis_conv_exp)
  then obtain n::int where n: "t' = t + 2 * n * pi"
    by (auto simp: sin_cos_eq_iff)
  then have "n=0"
    by (cases n) (use t t' in \<open>auto simp: mult_less_0_iff algebra_simps\<close>)
  then show "t' = t"
    by (simp add: n)
qed

lemma Arg2pi: "0 \<le> Arg2pi z \<and> Arg2pi z < 2*pi \<and> is_Arg z (Arg2pi z)"
proof (cases "z=0")
  case True then show ?thesis
    by (simp add: Arg2pi_def is_Arg_def)
next
  case False
  obtain t where t: "0 \<le> t" "t < 2*pi"
             and ReIm: "Re z / cmod z = cos t" "Im z / cmod z = sin t"
    using sincos_total_2pi [OF complex_unit_circle [OF False]]
    by blast
  have z: "is_Arg z t"
    unfolding is_Arg_def
    using t False ReIm
    by (intro complex_eqI) (auto simp: exp_Euler sin_of_real cos_of_real field_split_simps)
  show ?thesis
    apply (simp add: Arg2pi_def False)
    apply (rule theI [where a=t])
    using t z False
    apply (auto intro: Arg2pi_unique_lemma)
    done
qed

corollary\<^marker>\<open>tag unimportant\<close>
  shows Arg2pi_ge_0: "0 \<le> Arg2pi z"
    and Arg2pi_lt_2pi: "Arg2pi z < 2*pi"
    and Arg2pi_eq: "z = of_real(norm z) * exp(\<i> * of_real(Arg2pi z))"
  using Arg2pi is_Arg_def by auto

lemma complex_norm_eq_1_exp: "norm z = 1 \<longleftrightarrow> exp(\<i> * of_real (Arg2pi z)) = z"
  by (metis Arg2pi_eq cis_conv_exp mult.left_neutral norm_cis of_real_1)

lemma Arg2pi_unique: "\<lbrakk>of_real r * exp(\<i> * of_real a) = z; 0 < r; 0 \<le> a; a < 2*pi\<rbrakk> \<Longrightarrow> Arg2pi z = a"
  by (rule Arg2pi_unique_lemma [unfolded is_Arg_def, OF _ Arg2pi_eq]) (use Arg2pi [of z] in \<open>auto simp: norm_mult\<close>)

lemma cos_Arg2pi: "cmod z * cos (Arg2pi z) = Re z" and sin_Arg2pi: "cmod z * sin (Arg2pi z) = Im z"
  using Arg2pi_eq [of z] cis_conv_exp Re_rcis Im_rcis unfolding rcis_def by metis+

lemma Arg2pi_minus:
  assumes "z \<noteq> 0" shows "Arg2pi (-z) = (if Arg2pi z < pi then Arg2pi z + pi else Arg2pi z - pi)"
  apply (rule Arg2pi_unique [of "norm z", OF complex_eqI])
  using cos_Arg2pi sin_Arg2pi Arg2pi_ge_0 Arg2pi_lt_2pi [of z] assms
  by (auto simp: Re_exp Im_exp)

lemma Arg2pi_times_of_real [simp]:
  assumes "0 < r" shows "Arg2pi (of_real r * z) = Arg2pi z"
proof (cases "z=0")
  case False
  show ?thesis
    by (rule Arg2pi_unique [of "r * norm z"]) (use Arg2pi False assms is_Arg_def in auto)
qed auto

lemma Arg2pi_times_of_real2 [simp]: "0 < r \<Longrightarrow> Arg2pi (z * of_real r) = Arg2pi z"
  by (metis Arg2pi_times_of_real mult.commute)

lemma Arg2pi_divide_of_real [simp]: "0 < r \<Longrightarrow> Arg2pi (z / of_real r) = Arg2pi z"
  by (metis Arg2pi_times_of_real2 less_numeral_extra(3) nonzero_eq_divide_eq of_real_eq_0_iff)

lemma Arg2pi_le_pi: "Arg2pi z \<le> pi \<longleftrightarrow> 0 \<le> Im z"
proof (cases "z=0")
  case False
  have "0 \<le> Im z \<longleftrightarrow> 0 \<le> Im (of_real (cmod z) * exp (\<i> * complex_of_real (Arg2pi z)))"
    by (metis Arg2pi_eq)
  also have "... = (0 \<le> Im (exp (\<i> * complex_of_real (Arg2pi z))))"
    using False  by (simp add: zero_le_mult_iff)
  also have "... \<longleftrightarrow> Arg2pi z \<le> pi"
    by (simp add: Im_exp) (metis Arg2pi_ge_0 Arg2pi_lt_2pi sin_lt_zero sin_ge_zero not_le)
  finally show ?thesis
    by blast
qed auto

lemma Arg2pi_lt_pi: "0 < Arg2pi z \<and> Arg2pi z < pi \<longleftrightarrow> 0 < Im z"
proof (cases "z=0")
  case False
  have "0 < Im z \<longleftrightarrow> 0 < Im (of_real (cmod z) * exp (\<i> * complex_of_real (Arg2pi z)))"
    by (metis Arg2pi_eq)
  also have "... = (0 < Im (exp (\<i> * complex_of_real (Arg2pi z))))"
    using False by (simp add: zero_less_mult_iff)
  also have "... \<longleftrightarrow> 0 < Arg2pi z \<and> Arg2pi z < pi" (is "_ = ?rhs")
  proof -
    have "0 < sin (Arg2pi z) \<Longrightarrow> ?rhs"
      by (meson Arg2pi_ge_0 Arg2pi_lt_2pi less_le_trans not_le sin_le_zero sin_x_le_x)
    then show ?thesis
      by (auto simp: Im_exp sin_gt_zero)
  qed
  finally show ?thesis
    by blast
qed auto

lemma Arg2pi_eq_0: "Arg2pi z = 0 \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re z"
proof (cases "z=0")
  case False
  have "z \<in> \<real> \<and> 0 \<le> Re z \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re (of_real (cmod z) * exp (\<i> * complex_of_real (Arg2pi z)))"
    by (metis Arg2pi_eq)
  also have "... \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re (exp (\<i> * complex_of_real (Arg2pi z)))"
    using False  by (simp add: zero_le_mult_iff)
  also have "... \<longleftrightarrow> Arg2pi z = 0"
  proof -
    have [simp]: "Arg2pi z = 0 \<Longrightarrow> z \<in> \<real>"
      using Arg2pi_eq [of z] by (auto simp: Reals_def)
    moreover have "\<lbrakk>z \<in> \<real>; 0 \<le> cos (Arg2pi z)\<rbrakk> \<Longrightarrow> Arg2pi z = 0"
      by (metis Arg2pi_lt_pi Arg2pi_ge_0 Arg2pi_le_pi cos_pi complex_is_Real_iff leD less_linear less_minus_one_simps(2) minus_minus neg_less_eq_nonneg order_refl)
    ultimately show ?thesis
      by (auto simp: Re_exp)
  qed
  finally show ?thesis
    by blast
qed auto

corollary\<^marker>\<open>tag unimportant\<close> Arg2pi_gt_0:
  assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0"
    shows "Arg2pi z > 0"
  using Arg2pi_eq_0 Arg2pi_ge_0 assms dual_order.strict_iff_order
  unfolding nonneg_Reals_def by fastforce

lemma Arg2pi_eq_pi: "Arg2pi z = pi \<longleftrightarrow> z \<in> \<real> \<and> Re z < 0"
    using Arg2pi_le_pi [of z] Arg2pi_lt_pi [of z] Arg2pi_eq_0 [of z] Arg2pi_ge_0 [of z] 
    by (fastforce simp: complex_is_Real_iff)

lemma Arg2pi_eq_0_pi: "Arg2pi z = 0 \<or> Arg2pi z = pi \<longleftrightarrow> z \<in> \<real>"
  using Arg2pi_eq_0 Arg2pi_eq_pi not_le by auto

lemma Arg2pi_of_real: "Arg2pi (of_real r) = (if r<0 then pi else 0)"
  using Arg2pi_eq_0_pi Arg2pi_eq_pi by fastforce

lemma Arg2pi_real: "z \<in> \<real> \<Longrightarrow> Arg2pi z = (if 0 \<le> Re z then 0 else pi)"
  using Arg2pi_eq_0 Arg2pi_eq_0_pi by auto

lemma Arg2pi_inverse: "Arg2pi(inverse z) = (if z \<in> \<real> then Arg2pi z else 2*pi - Arg2pi z)"
proof (cases "z=0")
  case False
  show ?thesis
    apply (rule Arg2pi_unique [of "inverse (norm z)"])
    using Arg2pi_eq False Arg2pi_ge_0 [of z] Arg2pi_lt_2pi [of z] Arg2pi_eq_0 [of z]
    by (auto simp: Arg2pi_real in_Reals_norm exp_diff field_simps)
qed auto

lemma Arg2pi_eq_iff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
     shows "Arg2pi w = Arg2pi z \<longleftrightarrow> (\<exists>x. 0 < x & w = of_real x * z)"
  using assms Arg2pi_eq [of z] Arg2pi_eq [of w]
  apply auto
  apply (rule_tac x="norm w / norm z" in exI)
  apply (simp add: field_split_simps)
  by (metis mult.commute mult.left_commute)

lemma Arg2pi_inverse_eq_0: "Arg2pi(inverse z) = 0 \<longleftrightarrow> Arg2pi z = 0"
  by (metis Arg2pi_eq_0 Arg2pi_inverse inverse_inverse_eq)

lemma Arg2pi_divide:
  assumes "w \<noteq> 0" "z \<noteq> 0" "Arg2pi w \<le> Arg2pi z"
    shows "Arg2pi(z / w) = Arg2pi z - Arg2pi w"
  apply (rule Arg2pi_unique [of "norm(z / w)"])
  using assms Arg2pi_eq Arg2pi_ge_0 [of w] Arg2pi_lt_2pi [of z]
  apply (auto simp: exp_diff norm_divide field_simps)
  done

lemma Arg2pi_le_div_sum:
  assumes "w \<noteq> 0" "z \<noteq> 0" "Arg2pi w \<le> Arg2pi z"
    shows "Arg2pi z = Arg2pi w + Arg2pi(z / w)"
  by (simp add: Arg2pi_divide assms)

lemma Arg2pi_le_div_sum_eq:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi w \<le> Arg2pi z \<longleftrightarrow> Arg2pi z = Arg2pi w + Arg2pi(z / w)"
  using assms by (auto simp: Arg2pi_ge_0 intro: Arg2pi_le_div_sum)

lemma Arg2pi_diff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi w - Arg2pi z = (if Arg2pi z \<le> Arg2pi w then Arg2pi(w / z) else Arg2pi(w/z) - 2*pi)"
  using assms Arg2pi_divide Arg2pi_inverse [of "w/z"] Arg2pi_eq_0_pi
  by (force simp add: Arg2pi_ge_0 Arg2pi_divide not_le split: if_split_asm)

lemma Arg2pi_add:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi w + Arg2pi z = (if Arg2pi w + Arg2pi z < 2*pi then Arg2pi(w * z) else Arg2pi(w * z) + 2*pi)"
  using assms Arg2pi_diff [of "w*z" z] Arg2pi_le_div_sum_eq [of z "w*z"]
  apply (auto simp: Arg2pi_ge_0 Arg2pi_divide not_le)
  apply (metis Arg2pi_lt_2pi add.commute)
  apply (metis (no_types) Arg2pi add.commute diff_0 diff_add_cancel diff_less_eq diff_minus_eq_add not_less)
  done

lemma Arg2pi_times:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi (w * z) = (if Arg2pi w + Arg2pi z < 2*pi then Arg2pi w + Arg2pi z
                            else (Arg2pi w + Arg2pi z) - 2*pi)"
  using Arg2pi_add [OF assms]
  by auto

lemma Arg2pi_cnj_eq_inverse: "z\<noteq>0 \<Longrightarrow> Arg2pi (cnj z) = Arg2pi (inverse z)"
  apply (simp add: Arg2pi_eq_iff field_split_simps complex_norm_square [symmetric])
  by (metis of_real_power zero_less_norm_iff zero_less_power)

lemma Arg2pi_cnj: "Arg2pi(cnj z) = (if z \<in> \<real> then Arg2pi z else 2*pi - Arg2pi z)"
proof (cases "z=0")
  case False
  then show ?thesis
    by (simp add: Arg2pi_cnj_eq_inverse Arg2pi_inverse)
qed auto

lemma Arg2pi_exp: "0 \<le> Im z \<Longrightarrow> Im z < 2*pi \<Longrightarrow> Arg2pi(exp z) = Im z"
  by (rule Arg2pi_unique [of "exp(Re z)"]) (auto simp: exp_eq_polar)

lemma complex_split_polar:
  obtains r a::real where "z = complex_of_real r * (cos a + \<i> * sin a)" "0 \<le> r" "0 \<le> a" "a < 2*pi"
  using Arg2pi cis.ctr cis_conv_exp unfolding Complex_eq is_Arg_def by fastforce

lemma Re_Im_le_cmod: "Im w * sin \<phi> + Re w * cos \<phi> \<le> cmod w"
proof (cases w rule: complex_split_polar)
  case (1 r a) with sin_cos_le1 [of a \<phi>] show ?thesis
    apply (simp add: norm_mult cmod_unit_one)
    by (metis (no_types, hide_lams) abs_le_D1 distrib_left mult.commute mult.left_commute mult_left_le)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Analytic properties of tangent function\<close>

lemma cnj_tan: "cnj(tan z) = tan(cnj z)"
  by (simp add: cnj_cos cnj_sin tan_def)

lemma field_differentiable_at_tan: "cos z \<noteq> 0 \<Longrightarrow> tan field_differentiable at z"
  unfolding field_differentiable_def
  using DERIV_tan by blast

lemma field_differentiable_within_tan: "cos z \<noteq> 0
         \<Longrightarrow> tan field_differentiable (at z within s)"
  using field_differentiable_at_tan field_differentiable_at_within by blast

lemma continuous_within_tan: "cos z \<noteq> 0 \<Longrightarrow> continuous (at z within s) tan"
  using continuous_at_imp_continuous_within isCont_tan by blast

lemma continuous_on_tan [continuous_intros]: "(\<And>z. z \<in> s \<Longrightarrow> cos z \<noteq> 0) \<Longrightarrow> continuous_on s tan"
  by (simp add: continuous_at_imp_continuous_on)

lemma holomorphic_on_tan: "(\<And>z. z \<in> s \<Longrightarrow> cos z \<noteq> 0) \<Longrightarrow> tan holomorphic_on s"
  by (simp add: field_differentiable_within_tan holomorphic_on_def)


subsection\<open>The principal branch of the Complex logarithm\<close>

instantiation complex :: ln
begin

definition\<^marker>\<open>tag important\<close> ln_complex :: "complex \<Rightarrow> complex"
  where "ln_complex \<equiv> \<lambda>z. THE w. exp w = z & -pi < Im(w) & Im(w) \<le> pi"

text\<open>NOTE: within this scope, the constant Ln is not yet available!\<close>
lemma
  assumes "z \<noteq> 0"
    shows exp_Ln [simp]:  "exp(ln z) = z"
      and mpi_less_Im_Ln: "-pi < Im(ln z)"
      and Im_Ln_le_pi:    "Im(ln z) \<le> pi"
proof -
  obtain \<psi> where z: "z / (cmod z) = Complex (cos \<psi>) (sin \<psi>)"
    using complex_unimodular_polar [of "z / (norm z)"] assms
    by (auto simp: norm_divide field_split_simps)
  obtain \<phi> where \<phi>: "- pi < \<phi>" "\<phi> \<le> pi" "sin \<phi> = sin \<psi>" "cos \<phi> = cos \<psi>"
    using sincos_principal_value [of "\<psi>"] assms
    by (auto simp: norm_divide field_split_simps)
  have "exp(ln z) = z & -pi < Im(ln z) & Im(ln z) \<le> pi" unfolding ln_complex_def
    apply (rule theI [where a = "Complex (ln(norm z)) \<phi>"])
    using z assms \<phi>
    apply (auto simp: field_simps exp_complex_eqI exp_eq_polar cis.code)
    done
  then show "exp(ln z) = z" "-pi < Im(ln z)" "Im(ln z) \<le> pi"
    by auto
qed

lemma Ln_exp [simp]:
  assumes "-pi < Im(z)" "Im(z) \<le> pi"
    shows "ln(exp z) = z"
proof (rule exp_complex_eqI)
  show "\<bar>Im (ln (exp z)) - Im z\<bar> < 2 * pi"
    using assms mpi_less_Im_Ln  [of "exp z"] Im_Ln_le_pi [of "exp z"] by auto
qed auto

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relation to Real Logarithm\<close>

lemma Ln_of_real:
  assumes "0 < z"
    shows "ln(of_real z::complex) = of_real(ln z)"
proof -
  have "ln(of_real (exp (ln z))::complex) = ln (exp (of_real (ln z)))"
    by (simp add: exp_of_real)
  also have "... = of_real(ln z)"
    using assms by (subst Ln_exp) auto
  finally show ?thesis
    using assms by simp
qed

corollary\<^marker>\<open>tag unimportant\<close> Ln_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> Re z > 0 \<Longrightarrow> ln z \<in> \<real>"
  by (auto simp: Ln_of_real elim: Reals_cases)

corollary\<^marker>\<open>tag unimportant\<close> Im_Ln_of_real [simp]: "r > 0 \<Longrightarrow> Im (ln (of_real r)) = 0"
  by (simp add: Ln_of_real)

lemma cmod_Ln_Reals [simp]: "z \<in> \<real> \<Longrightarrow> 0 < Re z \<Longrightarrow> cmod (ln z) = norm (ln (Re z))"
  using Ln_of_real by force

lemma Ln_Reals_eq: "\<lbrakk>x \<in> \<real>; Re x > 0\<rbrakk> \<Longrightarrow> ln x = of_real (ln (Re x))"
  using Ln_of_real by force

lemma Ln_1 [simp]: "ln 1 = (0::complex)"
proof -
  have "ln (exp 0) = (0::complex)"
    by (simp add: del: exp_zero)
  then show ?thesis
    by simp
qed


lemma Ln_eq_zero_iff [simp]: "x \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> ln x = 0 \<longleftrightarrow> x = 1" for x::complex
  by auto (metis exp_Ln exp_zero nonpos_Reals_zero_I)

instance
  by intro_classes (rule ln_complex_def Ln_1)

end

abbreviation Ln :: "complex \<Rightarrow> complex"
  where "Ln \<equiv> ln"

lemma Ln_eq_iff: "w \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> (Ln w = Ln z \<longleftrightarrow> w = z)"
  by (metis exp_Ln)

lemma Ln_unique: "exp(z) = w \<Longrightarrow> -pi < Im(z) \<Longrightarrow> Im(z) \<le> pi \<Longrightarrow> Ln w = z"
  using Ln_exp by blast

lemma Re_Ln [simp]: "z \<noteq> 0 \<Longrightarrow> Re(Ln z) = ln(norm z)"
  by (metis exp_Ln ln_exp norm_exp_eq_Re)

corollary\<^marker>\<open>tag unimportant\<close> ln_cmod_le:
  assumes z: "z \<noteq> 0"
    shows "ln (cmod z) \<le> cmod (Ln z)"
  using norm_exp [of "Ln z", simplified exp_Ln [OF z]]
  by (metis Re_Ln complex_Re_le_cmod z)

proposition\<^marker>\<open>tag unimportant\<close> exists_complex_root:
  fixes z :: complex
  assumes "n \<noteq> 0"  obtains w where "z = w ^ n"
proof (cases "z=0")
  case False
  then show ?thesis
    by (rule_tac w = "exp(Ln z / n)" in that) (simp add: assms exp_of_nat_mult [symmetric])
qed (use assms in auto)

corollary\<^marker>\<open>tag unimportant\<close> exists_complex_root_nonzero:
  fixes z::complex
  assumes "z \<noteq> 0" "n \<noteq> 0"
  obtains w where "w \<noteq> 0" "z = w ^ n"
  by (metis exists_complex_root [of n z] assms power_0_left)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Derivative of Ln away from the branch cut\<close>

lemma
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows has_field_derivative_Ln: "(Ln has_field_derivative inverse(z)) (at z)"
    and Im_Ln_less_pi:           "Im (Ln z) < pi"
proof -
  have znz [simp]: "z \<noteq> 0"
    using assms by auto
  then have "Im (Ln z) \<noteq> pi"
    by (metis (no_types) Im_exp Ln_in_Reals assms complex_nonpos_Reals_iff complex_is_Real_iff exp_Ln mult_zero_right not_less pi_neq_zero sin_pi znz)
  then show *: "Im (Ln z) < pi" using assms Im_Ln_le_pi
    by (simp add: le_neq_trans)
  let ?U = "{w. -pi < Im(w) \<and> Im(w) < pi}"
  have 1: "open ?U"
    by (simp add: open_Collect_conj open_halfspace_Im_gt open_halfspace_Im_lt)
  have 2: "\<And>x. x \<in> ?U \<Longrightarrow> (exp has_derivative blinfun_apply(Blinfun ((*) (exp x)))) (at x)"
    by (simp add: bounded_linear_Blinfun_apply bounded_linear_mult_right has_field_derivative_imp_has_derivative)   
  have 3: "continuous_on ?U (\<lambda>x. Blinfun ((*) (exp x)))"
    unfolding blinfun_mult_right.abs_eq [symmetric] by (intro continuous_intros)
  have 4: "Ln z \<in> ?U"
    by (auto simp: mpi_less_Im_Ln *)
  have 5: "Blinfun ((*) (inverse z)) o\<^sub>L Blinfun ((*) (exp (Ln z))) = id_blinfun"
    by (rule blinfun_eqI) (simp add: bounded_linear_mult_right bounded_linear_Blinfun_apply)
  obtain U' V g g' where "open U'" and sub: "U' \<subseteq> ?U"
    and "Ln z \<in> U'" "open V" "z \<in> V"
    and hom: "homeomorphism U' V exp g"
    and g: "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (g' y)) (at y)"
    and g': "\<And>y. y \<in> V \<Longrightarrow> g' y = inv ((*) (exp (g y)))"
    and bij: "\<And>y. y \<in> V \<Longrightarrow> bij ((*) (exp (g y)))"
    using inverse_function_theorem [OF 1 2 3 4 5]
    by (simp add: bounded_linear_Blinfun_apply bounded_linear_mult_right) blast
  show "(Ln has_field_derivative inverse(z)) (at z)"
    unfolding has_field_derivative_def
  proof (rule has_derivative_transform_within_open)
    show g_eq_Ln: "g y = Ln y" if "y \<in> V" for y
    proof -
      obtain x where "y = exp x" "x \<in> U'"
        using hom homeomorphism_image1 that \<open>y \<in> V\<close> by blast
      then show ?thesis
        using sub hom homeomorphism_apply1 by fastforce
    qed
    have "0 \<notin> V"
      by (meson exp_not_eq_zero hom homeomorphism_def)
    then have "\<And>y. y \<in> V \<Longrightarrow> g' y = inv ((*) y)"
      by (metis exp_Ln g' g_eq_Ln)
    then have g': "g' z = (\<lambda>x. x/z)"
      by (metis (no_types, hide_lams) bij \<open>z \<in> V\<close> bij_inv_eq_iff exp_Ln g_eq_Ln nonzero_mult_div_cancel_left znz)
    show "(g has_derivative (*) (inverse z)) (at z)"
      using g [OF \<open>z \<in> V\<close>] g'
      by (simp add: \<open>z \<in> V\<close> field_class.field_divide_inverse has_derivative_imp_has_field_derivative has_field_derivative_imp_has_derivative)
  qed (auto simp: \<open>z \<in> V\<close> \<open>open V\<close>)
qed

declare has_field_derivative_Ln [derivative_intros]
declare has_field_derivative_Ln [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Ln field_differentiable at z"
  using field_differentiable_def has_field_derivative_Ln by blast

lemma field_differentiable_within_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0
         \<Longrightarrow> Ln field_differentiable (at z within S)"
  using field_differentiable_at_Ln field_differentiable_within_subset by blast

lemma continuous_at_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z) Ln"
  by (simp add: field_differentiable_imp_continuous_at field_differentiable_within_Ln)

lemma isCont_Ln' [simp,continuous_intros]:
   "\<lbrakk>isCont f z; f z \<notin> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. Ln (f x)) z"
  by (blast intro: isCont_o2 [OF _ continuous_at_Ln])

lemma continuous_within_Ln [continuous_intros]: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within S) Ln"
  using continuous_at_Ln continuous_at_imp_continuous_within by blast

lemma continuous_on_Ln [continuous_intros]: "(\<And>z. z \<in> S \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on S Ln"
  by (simp add: continuous_at_imp_continuous_on continuous_within_Ln)

lemma continuous_on_Ln' [continuous_intros]:
  "continuous_on S f \<Longrightarrow> (\<And>z. z \<in> S \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on S (\<lambda>x. Ln (f x))"
  by (rule continuous_on_compose2[OF continuous_on_Ln, of "UNIV - nonpos_Reals" S f]) auto

lemma holomorphic_on_Ln [holomorphic_intros]: "(\<And>z. z \<in> S \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> Ln holomorphic_on S"
  by (simp add: field_differentiable_within_Ln holomorphic_on_def)

lemma holomorphic_on_Ln' [holomorphic_intros]:
  "(\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> f holomorphic_on A \<Longrightarrow> (\<lambda>z. Ln (f z)) holomorphic_on A"
  using holomorphic_on_compose_gen[OF _ holomorphic_on_Ln, of f A "- \<real>\<^sub>\<le>\<^sub>0"]
  by (auto simp: o_def)

lemma tendsto_Ln [tendsto_intros]:
  fixes L F
  assumes "(f \<longlongrightarrow> L) F" "L \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Ln (f x)) \<longlongrightarrow> Ln L) F"
proof -
  have "nhds L \<ge> filtermap f F"
    using assms(1) by (simp add: filterlim_def)
  moreover have "\<forall>\<^sub>F y in nhds L. y \<in> - \<real>\<^sub>\<le>\<^sub>0"
    using eventually_nhds_in_open[of "- \<real>\<^sub>\<le>\<^sub>0" L] assms by (auto simp: open_Compl)
  ultimately have "\<forall>\<^sub>F y in filtermap f F. y \<in> - \<real>\<^sub>\<le>\<^sub>0" by (rule filter_leD)
  moreover have "continuous_on (-\<real>\<^sub>\<le>\<^sub>0) Ln" by (rule continuous_on_Ln) auto
  ultimately show ?thesis using continuous_on_tendsto_compose[of "- \<real>\<^sub>\<le>\<^sub>0" Ln f L F] assms
    by (simp add: eventually_filtermap)
qed

lemma divide_ln_mono:
  fixes x y::real
  assumes "3 \<le> x" "x \<le> y"
  shows "x / ln x \<le> y / ln y"
proof (rule exE [OF complex_mvt_line [of x y "\<lambda>z. z / Ln z" "\<lambda>z. 1/(Ln z) - 1/(Ln z)^2"]];
    clarsimp simp add: closed_segment_Reals closed_segment_eq_real_ivl assms)
  show "\<And>u. \<lbrakk>x \<le> u; u \<le> y\<rbrakk> \<Longrightarrow> ((\<lambda>z. z / Ln z) has_field_derivative 1 / Ln u - 1 / (Ln u)\<^sup>2) (at u)"
    using \<open>3 \<le> x\<close> by (force intro!: derivative_eq_intros simp: field_simps power_eq_if)
  show "x / ln x \<le> y / ln y"
    if "Re (y / Ln y) - Re (x / Ln x) = (Re (1 / Ln u) - Re (1 / (Ln u)\<^sup>2)) * (y - x)"
    and x: "x \<le> u" "u \<le> y" for u
  proof -
    have eq: "y / ln y = (1 / ln u - 1 / (ln u)\<^sup>2) * (y - x) + x / ln x"
      using that \<open>3 \<le> x\<close> by (auto simp: Ln_Reals_eq in_Reals_norm group_add_class.diff_eq_eq)
    show ?thesis
      using exp_le \<open>3 \<le> x\<close> x by (simp add: eq) (simp add: power_eq_if divide_simps ln_ge_iff)
  qed
qed

theorem Ln_series:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "(\<lambda>n. (-1)^Suc n / of_nat n * z^n) sums ln (1 + z)" (is "(\<lambda>n. ?f n * z^n) sums _")
proof -
  let ?F = "\<lambda>z. \<Sum>n. ?f n * z^n" and ?F' = "\<lambda>z. \<Sum>n. diffs ?f n * z^n"
  have r: "conv_radius ?f = 1"
    by (intro conv_radius_ratio_limit_nonzero[of _ 1])
       (simp_all add: norm_divide LIMSEQ_Suc_n_over_n del: of_nat_Suc)

  have "\<exists>c. \<forall>z\<in>ball 0 1. ln (1 + z) - ?F z = c"
  proof (rule has_field_derivative_zero_constant)
    fix z :: complex assume z': "z \<in> ball 0 1"
    hence z: "norm z < 1" by simp
    define t :: complex where "t = of_real (1 + norm z) / 2"
    from z have t: "norm z < norm t" "norm t < 1" unfolding t_def
      by (simp_all add: field_simps norm_divide del: of_real_add)

    have "Re (-z) \<le> norm (-z)" by (rule complex_Re_le_cmod)
    also from z have "... < 1" by simp
    finally have "((\<lambda>z. ln (1 + z)) has_field_derivative inverse (1+z)) (at z)"
      by (auto intro!: derivative_eq_intros simp: complex_nonpos_Reals_iff)
    moreover have "(?F has_field_derivative ?F' z) (at z)" using t r
      by (intro termdiffs_strong[of _ t] summable_in_conv_radius) simp_all
    ultimately have "((\<lambda>z. ln (1 + z) - ?F z) has_field_derivative (inverse (1 + z) - ?F' z))
                       (at z within ball 0 1)"
      by (intro derivative_intros) (simp_all add: at_within_open[OF z'])
    also have "(\<lambda>n. of_nat n * ?f n * z ^ (n - Suc 0)) sums ?F' z" using t r
      by (intro diffs_equiv termdiff_converges[OF t(1)] summable_in_conv_radius) simp_all
    from sums_split_initial_segment[OF this, of 1]
      have "(\<lambda>i. (-z) ^ i) sums ?F' z" by (simp add: power_minus[of z] del: of_nat_Suc)
    hence "?F' z = inverse (1 + z)" using z by (simp add: sums_iff suminf_geometric divide_inverse)
    also have "inverse (1 + z) - inverse (1 + z) = 0" by simp
    finally show "((\<lambda>z. ln (1 + z) - ?F z) has_field_derivative 0) (at z within ball 0 1)" .
  qed simp_all
  then obtain c where c: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> ln (1 + z) - ?F z = c" by blast
  from c[of 0] have "c = 0" by (simp only: powser_zero) simp
  with c[of z] assms have "ln (1 + z) = ?F z" by simp
  moreover have "summable (\<lambda>n. ?f n * z^n)" using assms r
    by (intro summable_in_conv_radius) simp_all
  ultimately show ?thesis by (simp add: sums_iff)
qed

lemma Ln_series': "cmod z < 1 \<Longrightarrow> (\<lambda>n. - ((-z)^n) / of_nat n) sums ln (1 + z)"
  by (drule Ln_series) (simp add: power_minus')

lemma ln_series':
  assumes "abs (x::real) < 1"
  shows   "(\<lambda>n. - ((-x)^n) / of_nat n) sums ln (1 + x)"
proof -
  from assms have "(\<lambda>n. - ((-of_real x)^n) / of_nat n) sums ln (1 + complex_of_real x)"
    by (intro Ln_series') simp_all
  also have "(\<lambda>n. - ((-of_real x)^n) / of_nat n) = (\<lambda>n. complex_of_real (- ((-x)^n) / of_nat n))"
    by (rule ext) simp
  also from assms have "ln (1 + complex_of_real x) = of_real (ln (1 + x))"
    by (subst Ln_of_real [symmetric]) simp_all
  finally show ?thesis by (subst (asm) sums_of_real_iff)
qed

lemma Ln_approx_linear:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "norm (ln (1 + z) - z) \<le> norm z^2 / (1 - norm z)"
proof -
  let ?f = "\<lambda>n. (-1)^Suc n / of_nat n"
  from assms have "(\<lambda>n. ?f n * z^n) sums ln (1 + z)" using Ln_series by simp
  moreover have "(\<lambda>n. (if n = 1 then 1 else 0) * z^n) sums z" using powser_sums_if[of 1] by simp
  ultimately have "(\<lambda>n. (?f n - (if n = 1 then 1 else 0)) * z^n) sums (ln (1 + z) - z)"
    by (subst left_diff_distrib, intro sums_diff) simp_all
  from sums_split_initial_segment[OF this, of "Suc 1"]
    have "(\<lambda>i. (-(z^2)) * inverse (2 + of_nat i) * (- z)^i) sums (Ln (1 + z) - z)"
    by (simp add: power2_eq_square mult_ac power_minus[of z] divide_inverse)
  hence "(Ln (1 + z) - z) = (\<Sum>i. (-(z^2)) * inverse (of_nat (i+2)) * (-z)^i)"
    by (simp add: sums_iff)
  also have A: "summable (\<lambda>n. norm z^2 * (inverse (real_of_nat (Suc (Suc n))) * cmod z ^ n))"
    by (rule summable_mult, rule summable_comparison_test_ev[OF _ summable_geometric[of "norm z"]])
       (auto simp: assms field_simps intro!: always_eventually)
  hence "norm (\<Sum>i. (-(z^2)) * inverse (of_nat (i+2)) * (-z)^i) 
      \<le> (\<Sum>i. norm (-(z^2) * inverse (of_nat (i+2)) * (-z)^i))"
    by (intro summable_norm)
       (auto simp: norm_power norm_inverse norm_mult mult_ac simp del: of_nat_add of_nat_Suc)
  also have "norm ((-z)^2 * (-z)^i) * inverse (of_nat (i+2)) \<le> norm ((-z)^2 * (-z)^i) * 1" for i
    by (intro mult_left_mono) (simp_all add: field_split_simps)
  hence "(\<Sum>i. norm (-(z^2) * inverse (of_nat (i+2)) * (-z)^i))
       \<le> (\<Sum>i. norm (-(z^2) * (-z)^i))"
    using A assms
    unfolding norm_power norm_inverse norm_divide norm_mult
    apply (intro suminf_le summable_mult summable_geometric)
    apply (auto simp: norm_power field_simps simp del: of_nat_add of_nat_Suc)
    done
  also have "... = norm z^2 * (\<Sum>i. norm z^i)" using assms
    by (subst suminf_mult [symmetric]) (auto intro!: summable_geometric simp: norm_mult norm_power)
  also have "(\<Sum>i. norm z^i) = inverse (1 - norm z)" using assms
    by (subst suminf_geometric) (simp_all add: divide_inverse)
  also have "norm z^2 * ... = norm z^2 / (1 - norm z)" by (simp add: divide_inverse)
  finally show ?thesis .
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Quadrant-type results for Ln\<close>

lemma cos_lt_zero_pi: "pi/2 < x \<Longrightarrow> x < 3*pi/2 \<Longrightarrow> cos x < 0"
  using cos_minus_pi cos_gt_zero_pi [of "x-pi"]
  by simp

lemma Re_Ln_pos_lt:
  assumes "z \<noteq> 0"
    shows "\<bar>Im(Ln z)\<bar> < pi/2 \<longleftrightarrow> 0 < Re(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    have "\<bar>Im w\<bar> < pi/2 \<longleftrightarrow> 0 < Re(exp w)"
    proof
      assume "\<bar>Im w\<bar> < pi/2" then show "0 < Re(exp w)" 
        by (auto simp: Re_exp cos_gt_zero_pi split: if_split_asm)
    next
      assume R: "0 < Re(exp w)" then 
      have "\<bar>Im w\<bar> \<noteq> pi/2"
        by (metis cos_minus cos_pi_half mult_eq_0_iff Re_exp abs_if order_less_irrefl)
      then show "\<bar>Im w\<bar> < pi/2"
        using cos_lt_zero_pi [of "-(Im w)"] cos_lt_zero_pi [of "(Im w)"] w R
        by (force simp: Re_exp zero_less_mult_iff abs_if not_less_iff_gr_or_eq)
    qed
  }
  then show ?thesis using assms
    by auto
qed

lemma Re_Ln_pos_le:
  assumes "z \<noteq> 0"
    shows "\<bar>Im(Ln z)\<bar> \<le> pi/2 \<longleftrightarrow> 0 \<le> Re(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "\<bar>Im w\<bar> \<le> pi/2 \<longleftrightarrow> 0 \<le> Re(exp w)"
      using cos_lt_zero_pi [of "- (Im w)"] cos_lt_zero_pi [of "(Im w)"] not_le
      by (auto simp: Re_exp zero_le_mult_iff abs_if intro: cos_ge_zero)
  }
  then show ?thesis using assms
    by auto
qed

lemma Im_Ln_pos_lt:
  assumes "z \<noteq> 0"
    shows "0 < Im(Ln z) \<and> Im(Ln z) < pi \<longleftrightarrow> 0 < Im(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "0 < Im w \<and> Im w < pi \<longleftrightarrow> 0 < Im(exp w)"
      using sin_gt_zero [of "- (Im w)"] sin_gt_zero [of "(Im w)"] less_linear
      by (fastforce simp add: Im_exp zero_less_mult_iff)
  }
  then show ?thesis using assms
    by auto
qed


lemma Im_Ln_pos_le:
  assumes "z \<noteq> 0"
    shows "0 \<le> Im(Ln z) \<and> Im(Ln z) \<le> pi \<longleftrightarrow> 0 \<le> Im(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "0 \<le> Im w \<and> Im w \<le> pi \<longleftrightarrow> 0 \<le> Im(exp w)"
      using sin_ge_zero [of "- (Im w)"] sin_ge_zero [of "abs(Im w)"] sin_zero_pi_iff [of "Im w"]
      by (force simp: Im_exp zero_le_mult_iff sin_ge_zero) }
  then show ?thesis using assms
    by auto
qed

lemma Re_Ln_pos_lt_imp: "0 < Re(z) \<Longrightarrow> \<bar>Im(Ln z)\<bar> < pi/2"
  by (metis Re_Ln_pos_lt less_irrefl zero_complex.simps(1))

lemma Im_Ln_pos_lt_imp: "0 < Im(z) \<Longrightarrow> 0 < Im(Ln z) \<and> Im(Ln z) < pi"
  by (metis Im_Ln_pos_lt not_le order_refl zero_complex.simps(2))

text\<open>A reference to the set of positive real numbers\<close>
lemma Im_Ln_eq_0: "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = 0 \<longleftrightarrow> 0 < Re(z) \<and> Im(z) = 0)"
by (metis Im_complex_of_real Im_exp Ln_in_Reals Re_Ln_pos_lt Re_Ln_pos_lt_imp
          Re_complex_of_real complex_is_Real_iff exp_Ln exp_of_real pi_gt_zero)

lemma Im_Ln_eq_pi: "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = pi \<longleftrightarrow> Re(z) < 0 \<and> Im(z) = 0)"
by (metis Im_Ln_eq_0 Im_Ln_pos_le Im_Ln_pos_lt add.left_neutral complex_eq less_eq_real_def
    mult_zero_right not_less_iff_gr_or_eq pi_ge_zero pi_neq_zero rcis_zero_arg rcis_zero_mod)


subsection\<^marker>\<open>tag unimportant\<close>\<open>More Properties of Ln\<close>

lemma cnj_Ln: assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0" shows "cnj(Ln z) = Ln(cnj z)"
proof (cases "z=0")
  case False
  show ?thesis
  proof (rule exp_complex_eqI)
    have "\<bar>Im (cnj (Ln z)) - Im (Ln (cnj z))\<bar> \<le> \<bar>Im (cnj (Ln z))\<bar> + \<bar>Im (Ln (cnj z))\<bar>"
      by (rule abs_triangle_ineq4)
    also have "... < pi + pi"
    proof -
      have "\<bar>Im (cnj (Ln z))\<bar> < pi"
        by (simp add: False Im_Ln_less_pi abs_if assms minus_less_iff mpi_less_Im_Ln)
      moreover have "\<bar>Im (Ln (cnj z))\<bar> \<le> pi"
        by (meson abs_le_iff complex_cnj_zero_iff less_eq_real_def minus_less_iff  False Im_Ln_le_pi mpi_less_Im_Ln)
      ultimately show ?thesis
        by simp
    qed
    finally show "\<bar>Im (cnj (Ln z)) - Im (Ln (cnj z))\<bar> < 2 * pi"
      by simp
    show "exp (cnj (Ln z)) = exp (Ln (cnj z))"
      by (metis False complex_cnj_zero_iff exp_Ln exp_cnj)
  qed
qed (use assms in auto)


lemma Ln_inverse: assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0" shows "Ln(inverse z) = -(Ln z)"
proof (cases "z=0")
  case False
  show ?thesis
  proof (rule exp_complex_eqI)
    have "\<bar>Im (Ln (inverse z)) - Im (- Ln z)\<bar> \<le> \<bar>Im (Ln (inverse z))\<bar> + \<bar>Im (- Ln z)\<bar>"
      by (rule abs_triangle_ineq4)
    also have "... < pi + pi"
    proof -
      have "\<bar>Im (Ln (inverse z))\<bar> < pi"
        by (simp add: False Im_Ln_less_pi abs_if assms minus_less_iff mpi_less_Im_Ln)
      moreover have "\<bar>Im (- Ln z)\<bar> \<le> pi"
        using False Im_Ln_le_pi mpi_less_Im_Ln by fastforce
      ultimately show ?thesis
        by simp
    qed
    finally show "\<bar>Im (Ln (inverse z)) - Im (- Ln z)\<bar> < 2 * pi"
      by simp
    show "exp (Ln (inverse z)) = exp (- Ln z)"
      by (simp add: False exp_minus)
  qed
qed (use assms in auto)

lemma Ln_minus1 [simp]: "Ln(-1) = \<i> * pi"
proof (rule exp_complex_eqI)
  show "\<bar>Im (Ln (- 1)) - Im (\<i> * pi)\<bar> < 2 * pi"
    using Im_Ln_le_pi [of "-1"] mpi_less_Im_Ln [of "-1"] by auto
qed auto

lemma Ln_ii [simp]: "Ln \<i> = \<i> * of_real pi/2"
  using Ln_exp [of "\<i> * (of_real pi/2)"]
  unfolding exp_Euler
  by simp

lemma Ln_minus_ii [simp]: "Ln(-\<i>) = - (\<i> * pi/2)"
proof -
  have  "Ln(-\<i>) = Ln(inverse \<i>)"    by simp
  also have "... = - (Ln \<i>)"         using Ln_inverse by blast
  also have "... = - (\<i> * pi/2)"     by simp
  finally show ?thesis .
qed

lemma Ln_times:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Ln(w * z) =
           (if Im(Ln w + Ln z) \<le> -pi then (Ln(w) + Ln(z)) + \<i> * of_real(2*pi)
            else if Im(Ln w + Ln z) > pi then (Ln(w) + Ln(z)) - \<i> * of_real(2*pi)
            else Ln(w) + Ln(z))"
  using pi_ge_zero Im_Ln_le_pi [of w] Im_Ln_le_pi [of z]
  using assms mpi_less_Im_Ln [of w] mpi_less_Im_Ln [of z]
  by (auto simp: exp_add exp_diff sin_double cos_double exp_Euler intro!: Ln_unique)

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_simple:
    "\<lbrakk>w \<noteq> 0; z \<noteq> 0; -pi < Im(Ln w) + Im(Ln z); Im(Ln w) + Im(Ln z) \<le> pi\<rbrakk>
         \<Longrightarrow> Ln(w * z) = Ln(w) + Ln(z)"
  by (simp add: Ln_times)

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_of_real:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(of_real r * z) = ln r + Ln(z)"
  using mpi_less_Im_Ln Im_Ln_le_pi
  by (force simp: Ln_times)

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_Reals:
    "\<lbrakk>r \<in> Reals; Re r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(r * z) = ln (Re r) + Ln(z)"
  using Ln_Reals_eq Ln_times_of_real by fastforce

corollary\<^marker>\<open>tag unimportant\<close> Ln_divide_of_real:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(z / of_real r) = Ln(z) - ln r"
using Ln_times_of_real [of "inverse r" z]
by (simp add: ln_inverse Ln_of_real mult.commute divide_inverse of_real_inverse [symmetric]
         del: of_real_inverse)

corollary\<^marker>\<open>tag unimportant\<close> Ln_prod:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows "\<exists>n. Ln (prod f A) = (\<Sum>x \<in> A. Ln (f x) + (of_int (n x) * (2 * pi)) * \<i>)"
  using assms
proof (induction A)
  case (insert x A)
  then obtain n where n: "Ln (prod f A) = (\<Sum>x\<in>A. Ln (f x) + of_real (of_int (n x) * (2 * pi)) * \<i>)"
    by auto
  define D where "D \<equiv> Im (Ln (f x)) + Im (Ln (prod f A))"
  define q::int where "q \<equiv> (if D \<le> -pi then 1 else if D > pi then -1 else 0)"
  have "prod f A \<noteq> 0" "f x \<noteq> 0"
    by (auto simp: insert.hyps insert.prems)
  with insert.hyps pi_ge_zero show ?case
    by (rule_tac x="n(x:=q)" in exI) (force simp: Ln_times q_def D_def n intro!: sum.cong)
qed auto

lemma Ln_minus:
  assumes "z \<noteq> 0"
    shows "Ln(-z) = (if Im(z) \<le> 0 \<and> \<not>(Re(z) < 0 \<and> Im(z) = 0)
                     then Ln(z) + \<i> * pi
                     else Ln(z) - \<i> * pi)" (is "_ = ?rhs")
  using Im_Ln_le_pi [of z] mpi_less_Im_Ln [of z] assms
        Im_Ln_eq_pi [of z] Im_Ln_pos_lt [of z]
    by (fastforce simp: exp_add exp_diff exp_Euler intro!: Ln_unique)

lemma Ln_inverse_if:
  assumes "z \<noteq> 0"
    shows "Ln (inverse z) = (if z \<in> \<real>\<^sub>\<le>\<^sub>0 then -(Ln z) + \<i> * 2 * complex_of_real pi else -(Ln z))"
proof (cases "z \<in> \<real>\<^sub>\<le>\<^sub>0")
  case False then show ?thesis
    by (simp add: Ln_inverse)
next
  case True
  then have z: "Im z = 0" "Re z < 0" "- z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using assms complex_eq_iff complex_nonpos_Reals_iff by auto
  have "Ln(inverse z) = Ln(- (inverse (-z)))"
    by simp
  also have "... = Ln (inverse (-z)) + \<i> * complex_of_real pi"
    using assms z by (simp add: Ln_minus divide_less_0_iff)
  also have "... = - Ln (- z) + \<i> * complex_of_real pi"
    using z Ln_inverse by presburger
  also have "... = - (Ln z) + \<i> * 2 * complex_of_real pi"
    using Ln_minus assms z by auto
  finally show ?thesis by (simp add: True)
qed

lemma Ln_times_ii:
  assumes "z \<noteq> 0"
    shows  "Ln(\<i> * z) = (if 0 \<le> Re(z) | Im(z) < 0
                          then Ln(z) + \<i> * of_real pi/2
                          else Ln(z) - \<i> * of_real(3 * pi/2))"
  using Im_Ln_le_pi [of z] mpi_less_Im_Ln [of z] assms
        Im_Ln_eq_pi [of z] Im_Ln_pos_lt [of z] Re_Ln_pos_le [of z]
  by (simp add: Ln_times) auto

lemma Ln_of_nat [simp]: "0 < n \<Longrightarrow> Ln (of_nat n) = of_real (ln (of_nat n))"
  by (subst of_real_of_nat_eq[symmetric], subst Ln_of_real[symmetric]) simp_all

lemma Ln_of_nat_over_of_nat:
  assumes "m > 0" "n > 0"
  shows   "Ln (of_nat m / of_nat n) = of_real (ln (of_nat m) - ln (of_nat n))"
proof -
  have "of_nat m / of_nat n = (of_real (of_nat m / of_nat n) :: complex)" by simp
  also from assms have "Ln ... = of_real (ln (of_nat m / of_nat n))"
    by (simp add: Ln_of_real[symmetric])
  also from assms have "... = of_real (ln (of_nat m) - ln (of_nat n))"
    by (simp add: ln_div)
  finally show ?thesis .
qed

subsection\<open>The Argument of a Complex Number\<close>

text\<open>Unlike in HOL Light, it's defined for the same interval as the complex logarithm: \<open>(-\<pi>,\<pi>]\<close>.\<close>

lemma Arg_eq_Im_Ln:
  assumes "z \<noteq> 0" shows "arg z = Im (Ln z)"
proof (rule arg_unique)
  show "sgn z = cis (Im (Ln z))"
    by (metis assms exp_Ln exp_eq_polar nonzero_mult_div_cancel_left norm_eq_zero 
              norm_exp_eq_Re of_real_eq_0_iff sgn_eq)
  show "- pi < Im (Ln z)"
    by (simp add: assms mpi_less_Im_Ln)
  show "Im (Ln z) \<le> pi"
    by (simp add: Im_Ln_le_pi assms)
qed

text \<open>The 1990s definition of argument coincides with the more recent one\<close>
lemma Arg_definition_equivalence:
  shows "arg z = (if z = 0 then 0 else Im (Ln z))"
  by (simp add: Arg_eq_Im_Ln arg_zero)

definition\<^marker>\<open>tag important\<close> Arg :: "complex \<Rightarrow> real" where "Arg z \<equiv> (if z = 0 then 0 else Im (Ln z))"

lemma Arg_of_real: "Arg (of_real r) = (if r<0 then pi else 0)"
  by (simp add: Im_Ln_eq_pi Arg_def)

lemma mpi_less_Arg: "-pi < Arg z"
    and Arg_le_pi: "Arg z \<le> pi"
  by (auto simp: Arg_def mpi_less_Im_Ln Im_Ln_le_pi)

lemma
  assumes "z \<noteq> 0"
  shows Arg_eq: "z = of_real(norm z) * exp(\<i> * Arg z)"
  using assms exp_Ln exp_eq_polar
  by (auto simp:  Arg_def)

lemma is_Arg_Arg: "z \<noteq> 0 \<Longrightarrow> is_Arg z (Arg z)"
  by (simp add: Arg_eq is_Arg_def)

lemma Argument_exists:
  assumes "z \<noteq> 0" and R: "R = {r-pi<..r+pi}"
  obtains s where "is_Arg z s" "s\<in>R"
proof -
  let ?rp = "r - Arg z + pi"
  define k where "k \<equiv> \<lfloor>?rp / (2 * pi)\<rfloor>"
  have "(Arg z + of_int k * (2 * pi)) \<in> R"
    using floor_divide_lower [of "2*pi" ?rp] floor_divide_upper [of "2*pi" ?rp]
    by (auto simp: k_def algebra_simps R)
  then show ?thesis
    using Arg_eq \<open>z \<noteq> 0\<close> is_Arg_2pi_iff is_Arg_def that by blast
qed

lemma Argument_exists_unique:
  assumes "z \<noteq> 0" and R: "R = {r-pi<..r+pi}"
  obtains s where "is_Arg z s" "s\<in>R" "\<And>t. \<lbrakk>is_Arg z t; t\<in>R\<rbrakk> \<Longrightarrow> s=t"
proof -
  obtain s where s: "is_Arg z s" "s\<in>R"
    using Argument_exists [OF assms] .
  moreover have "\<And>t. \<lbrakk>is_Arg z t; t\<in>R\<rbrakk> \<Longrightarrow> s=t"
    using assms s  by (auto simp: is_Arg_eqI)
  ultimately show thesis
    using that by blast
qed

lemma Argument_Ex1:
  assumes "z \<noteq> 0" and R: "R = {r-pi<..r+pi}"
  shows "\<exists>!s. is_Arg z s \<and> s \<in> R"
  using Argument_exists_unique [OF assms]  by metis

lemma Arg_divide:
  assumes "w \<noteq> 0" "z \<noteq> 0"
  shows "is_Arg (z / w) (Arg z - Arg w)"
  using Arg_eq [of z] Arg_eq [of w] Arg_eq [of "norm(z / w)"] assms
  by (auto simp: is_Arg_def norm_divide field_simps exp_diff Arg_of_real)

lemma Arg_unique_lemma:
  assumes z:  "is_Arg z t"
      and z': "is_Arg z t'"
      and t:  "- pi < t"  "t \<le> pi"
      and t': "- pi < t'" "t' \<le> pi"
      and nz: "z \<noteq> 0"
    shows "t' = t"
  using Arg2pi_unique_lemma [of "- (inverse z)"]
proof -
  have "pi - t' = pi - t"
  proof (rule Arg2pi_unique_lemma [of "- (inverse z)"])
    have "- (inverse z) = - (inverse (of_real(norm z) * exp(\<i> * t)))"
      by (metis is_Arg_def z)
    also have "... = (cmod (- inverse z)) * exp (\<i> * (pi - t))"
      by (auto simp: field_simps exp_diff norm_divide)
    finally show "is_Arg (- inverse z) (pi - t)"
      unfolding is_Arg_def .
    have "- (inverse z) = - (inverse (of_real(norm z) * exp(\<i> * t')))"
      by (metis is_Arg_def z')
    also have "... = (cmod (- inverse z)) * exp (\<i> * (pi - t'))"
      by (auto simp: field_simps exp_diff norm_divide)
    finally show "is_Arg (- inverse z) (pi - t')"
      unfolding is_Arg_def .
  qed (use assms in auto)
  then show ?thesis
    by simp
qed

lemma complex_norm_eq_1_exp_eq: "norm z = 1 \<longleftrightarrow> exp(\<i> * (Arg z)) = z"
  by (metis Arg_eq exp_not_eq_zero exp_zero mult.left_neutral norm_zero of_real_1 norm_exp_i_times)

lemma Arg_unique: "\<lbrakk>of_real r * exp(\<i> * a) = z; 0 < r; -pi < a; a \<le> pi\<rbrakk> \<Longrightarrow> Arg z = a"
  by (rule Arg_unique_lemma [unfolded is_Arg_def, OF _ Arg_eq])
     (use mpi_less_Arg Arg_le_pi in \<open>auto simp: norm_mult\<close>)

lemma Arg_minus:
  assumes "z \<noteq> 0"
  shows "Arg (-z) = (if Arg z \<le> 0 then Arg z + pi else Arg z - pi)"
proof -
  have [simp]: "cmod z * cos (Arg z) = Re z"
    using assms Arg_eq [of z] by (metis Re_exp exp_Ln norm_exp_eq_Re Arg_def)
  have [simp]: "cmod z * sin (Arg z) = Im z"
    using assms Arg_eq [of z] by (metis Im_exp exp_Ln norm_exp_eq_Re Arg_def)
  show ?thesis
    apply (rule Arg_unique [of "norm z", OF complex_eqI])
    using mpi_less_Arg [of z] Arg_le_pi [of z] assms
    by (auto simp: Re_exp Im_exp)
qed

lemma Arg_times_of_real [simp]:
  assumes "0 < r" shows "Arg (of_real r * z) = Arg z"
proof (cases "z=0")
  case True
  then show ?thesis
    by (simp add: Arg_def)
next
  case False
  with Arg_eq assms show ?thesis
  by (auto simp: mpi_less_Arg Arg_le_pi intro!:  Arg_unique [of "r * norm z"])
qed

lemma Arg_times_of_real2 [simp]: "0 < r \<Longrightarrow> Arg (z * of_real r) = Arg z"
  by (metis Arg_times_of_real mult.commute)

lemma Arg_divide_of_real [simp]: "0 < r \<Longrightarrow> Arg (z / of_real r) = Arg z"
  by (metis Arg_times_of_real2 less_numeral_extra(3) nonzero_eq_divide_eq of_real_eq_0_iff)

lemma Arg_less_0: "0 \<le> Arg z \<longleftrightarrow> 0 \<le> Im z"
  using Im_Ln_le_pi Im_Ln_pos_le
  by (simp add: Arg_def)

lemma Arg_eq_pi: "Arg z = pi \<longleftrightarrow> Re z < 0 \<and> Im z = 0"
  by (auto simp: Arg_def Im_Ln_eq_pi)

lemma Arg_lt_pi: "0 < Arg z \<and> Arg z < pi \<longleftrightarrow> 0 < Im z"
  using Arg_less_0 [of z] Im_Ln_pos_lt
  by (auto simp: order.order_iff_strict Arg_def)

lemma Arg_eq_0: "Arg z = 0 \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re z"
  using complex_is_Real_iff
  by (simp add: Arg_def Im_Ln_eq_0) (metis less_eq_real_def of_real_Re of_real_def scale_zero_left)

corollary\<^marker>\<open>tag unimportant\<close> Arg_ne_0: assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0" shows "Arg z \<noteq> 0"
  using assms by (auto simp: nonneg_Reals_def Arg_eq_0)

lemma Arg_eq_pi_iff: "Arg z = pi \<longleftrightarrow> z \<in> \<real> \<and> Re z < 0"
proof (cases "z=0")
  case False
  then show ?thesis
    using Arg_eq_0 [of "-z"] Arg_eq_pi complex_is_Real_iff by blast
qed (simp add: Arg_def)

lemma Arg_eq_0_pi: "Arg z = 0 \<or> Arg z = pi \<longleftrightarrow> z \<in> \<real>"
  using Arg_eq_pi_iff Arg_eq_0 by force

lemma Arg_real: "z \<in> \<real> \<Longrightarrow> Arg z = (if 0 \<le> Re z then 0 else pi)"
  using Arg_eq_0 Arg_eq_0_pi by auto

lemma Arg_inverse: "Arg(inverse z) = (if z \<in> \<real> then Arg z else - Arg z)"
proof (cases "z \<in> \<real>")
  case True
  then show ?thesis
    by simp (metis Arg2pi_inverse Arg2pi_real Arg_real Reals_inverse)
next
  case False
  then have z: "Arg z < pi" "z \<noteq> 0"
    using Arg_eq_0_pi Arg_le_pi by (auto simp: less_eq_real_def)
  show ?thesis
    apply (rule Arg_unique [of "inverse (norm z)"])
    using False z mpi_less_Arg [of z] Arg_eq [of z]
    by (auto simp: exp_minus field_simps)
qed

lemma Arg_eq_iff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
  shows "Arg w = Arg z \<longleftrightarrow> (\<exists>x. 0 < x \<and> w = of_real x * z)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "w = complex_of_real (cmod w / cmod z) * z"
    by (metis Arg_eq assms divide_divide_eq_right eq_divide_eq exp_not_eq_zero of_real_divide)
  then show ?rhs
    using assms divide_pos_pos zero_less_norm_iff by blast
qed auto

lemma Arg_inverse_eq_0: "Arg(inverse z) = 0 \<longleftrightarrow> Arg z = 0"
  by (metis Arg_eq_0 Arg_inverse inverse_inverse_eq)

lemma Arg_cnj_eq_inverse: "z\<noteq>0 \<Longrightarrow> Arg (cnj z) = Arg (inverse z)"
  using Arg2pi_cnj_eq_inverse Arg2pi_eq_iff Arg_eq_iff by auto

lemma Arg_cnj: "Arg(cnj z) = (if z \<in> \<real> then Arg z else - Arg z)"
  by (metis Arg_cnj_eq_inverse Arg_inverse Reals_0 complex_cnj_zero)

lemma Arg_exp: "-pi < Im z \<Longrightarrow> Im z \<le> pi \<Longrightarrow> Arg(exp z) = Im z"
  by (rule Arg_unique [of "exp(Re z)"]) (auto simp: exp_eq_polar)

lemma Ln_Arg: "z\<noteq>0 \<Longrightarrow> Ln(z) = ln(norm z) + \<i> * Arg(z)"
  by (metis Arg_def Re_Ln complex_eq)

lemma continuous_at_Arg:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "continuous (at z) Arg"
proof -
  have [simp]: "(\<lambda>z. Im (Ln z)) \<midarrow>z\<rightarrow> Arg z"
    using Arg_def assms continuous_at by fastforce
  show ?thesis
    unfolding continuous_at
  proof (rule Lim_transform_within_open)
    show "\<And>w. \<lbrakk>w \<in> - \<real>\<^sub>\<le>\<^sub>0; w \<noteq> z\<rbrakk> \<Longrightarrow> Im (Ln w) = Arg w"
      by (metis Arg_def Compl_iff nonpos_Reals_zero_I)
  qed (use assms in auto)
qed

lemma continuous_within_Arg: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within S) Arg"
  using continuous_at_Arg continuous_at_imp_continuous_within by blast


subsection\<open>The Unwinding Number and the Ln product Formula\<close>

text\<open>Note that in this special case the unwinding number is -1, 0 or 1. But it's always an integer.\<close>

lemma is_Arg_exp_Im: "is_Arg (exp z) (Im z)"
  using exp_eq_polar is_Arg_def norm_exp_eq_Re by auto

lemma is_Arg_exp_diff_2pi:
  assumes "is_Arg (exp z) \<theta>"
  shows "\<exists>k. Im z - of_int k * (2 * pi) = \<theta>"
proof (intro exI is_Arg_eqI)
  let ?k = "\<lfloor>(Im z - \<theta>) / (2 * pi)\<rfloor>"
  show "is_Arg (exp z) (Im z - real_of_int ?k * (2 * pi))"
    by (metis diff_add_cancel is_Arg_2pi_iff is_Arg_exp_Im)
  show "\<bar>Im z - real_of_int ?k * (2 * pi) - \<theta>\<bar> < 2 * pi"
    using floor_divide_upper [of "2*pi" "Im z - \<theta>"] floor_divide_lower [of "2*pi" "Im z - \<theta>"]
    by (auto simp: algebra_simps abs_if)
qed (auto simp: is_Arg_exp_Im assms)

lemma Arg_exp_diff_2pi: "\<exists>k. Im z - of_int k * (2 * pi) = Arg (exp z)"
  using is_Arg_exp_diff_2pi [OF is_Arg_Arg] by auto

lemma unwinding_in_Ints: "(z - Ln(exp z)) / (of_real(2*pi) * \<i>) \<in> \<int>"
  using Arg_exp_diff_2pi [of z]
  by (force simp: Ints_def image_def field_simps Arg_def intro!: complex_eqI)

definition\<^marker>\<open>tag important\<close> unwinding :: "complex \<Rightarrow> int" where
   "unwinding z \<equiv> THE k. of_int k = (z - Ln(exp z)) / (of_real(2*pi) * \<i>)"

lemma unwinding: "of_int (unwinding z) = (z - Ln(exp z)) / (of_real(2*pi) * \<i>)"
  using unwinding_in_Ints [of z]
  unfolding unwinding_def Ints_def by force

lemma unwinding_2pi: "(2*pi) * \<i> * unwinding(z) = z - Ln(exp z)"
  by (simp add: unwinding)

lemma Ln_times_unwinding:
    "w \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> Ln(w * z) = Ln(w) + Ln(z) - (2*pi) * \<i> * unwinding(Ln w + Ln z)"
  using unwinding_2pi by (simp add: exp_add)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relation between Ln and Arg2pi, and hence continuity of Arg2pi\<close>

lemma Arg2pi_Ln:
  assumes "0 < Arg2pi z" shows "Arg2pi z = Im(Ln(-z)) + pi"
proof (cases "z = 0")
  case True
  with assms show ?thesis
    by simp
next
  case False
  then have "z / of_real(norm z) = exp(\<i> * of_real(Arg2pi z))"
    using Arg2pi [of z]
    by (metis is_Arg_def abs_norm_cancel nonzero_mult_div_cancel_left norm_of_real zero_less_norm_iff)
  then have "- z / of_real(norm z) = exp (\<i> * (of_real (Arg2pi z) - pi))"
    using cis_conv_exp cis_pi
    by (auto simp: exp_diff algebra_simps)
  then have "ln (- z / of_real(norm z)) = ln (exp (\<i> * (of_real (Arg2pi z) - pi)))"
    by simp
  also have "... = \<i> * (of_real(Arg2pi z) - pi)"
    using Arg2pi [of z] assms pi_not_less_zero
    by auto
  finally have "Arg2pi z =  Im (Ln (- z / of_real (cmod z))) + pi"
    by simp
  also have "... = Im (Ln (-z) - ln (cmod z)) + pi"
    by (metis diff_0_right minus_diff_eq zero_less_norm_iff Ln_divide_of_real False)
  also have "... = Im (Ln (-z)) + pi"
    by simp
  finally show ?thesis .
qed

lemma continuous_at_Arg2pi:
  assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0"
    shows "continuous (at z) Arg2pi"
proof -
  have *: "isCont (\<lambda>z. Im (Ln (- z)) + pi) z"
    by (rule Complex.isCont_Im isCont_Ln' continuous_intros | simp add: assms complex_is_Real_iff)+
  have [simp]: "Im x \<noteq> 0 \<Longrightarrow> Im (Ln (- x)) + pi = Arg2pi x" for x
    using Arg2pi_Ln  by (simp add: Arg2pi_gt_0 complex_nonneg_Reals_iff)
  consider "Re z < 0" | "Im z \<noteq> 0" using assms
    using complex_nonneg_Reals_iff not_le by blast
  then have [simp]: "(\<lambda>z. Im (Ln (- z)) + pi) \<midarrow>z\<rightarrow> Arg2pi z"
    using "*" by (simp add: Arg2pi_Ln Arg2pi_gt_0 assms continuous_within) 
  show ?thesis
    unfolding continuous_at
  proof (rule Lim_transform_within_open)
    show "\<And>x. \<lbrakk>x \<in> - \<real>\<^sub>\<ge>\<^sub>0; x \<noteq> z\<rbrakk> \<Longrightarrow> Im (Ln (- x)) + pi = Arg2pi x"
      by (auto simp add: Arg2pi_Ln [OF Arg2pi_gt_0] complex_nonneg_Reals_iff)
  qed (use assms in auto)
qed


text\<open>Relation between Arg2pi and arctangent in upper halfplane\<close>
lemma Arg2pi_arctan_upperhalf:
  assumes "0 < Im z"
    shows "Arg2pi z = pi/2 - arctan(Re z / Im z)"
proof (cases "z = 0")
  case False
  show ?thesis
  proof (rule Arg2pi_unique [of "norm z"])
    show "(cmod z) * exp (\<i> * (pi / 2 - arctan (Re z / Im z))) = z"
      apply (rule complex_eqI)
      using assms norm_complex_def [of z, symmetric]
      unfolding exp_Euler cos_diff sin_diff sin_of_real cos_of_real
      by (simp_all add: field_simps real_sqrt_divide sin_arctan cos_arctan)
  qed (use False arctan [of "Re z / Im z"] in auto)
qed (use assms in auto)

lemma Arg2pi_eq_Im_Ln:
  assumes "0 \<le> Im z" "0 < Re z"
    shows "Arg2pi z = Im (Ln z)"
proof (cases "Im z = 0")
  case True then show ?thesis
    using Arg2pi_eq_0 Ln_in_Reals assms(2) complex_is_Real_iff by auto
next
  case False
  then have *: "Arg2pi z > 0"
    using Arg2pi_gt_0 complex_is_Real_iff by blast
  then have "z \<noteq> 0"
    by auto
  with * assms False show ?thesis
    by (subst Arg2pi_Ln) (auto simp: Ln_minus)
qed

lemma continuous_within_upperhalf_Arg2pi:
  assumes "z \<noteq> 0"
    shows "continuous (at z within {z. 0 \<le> Im z}) Arg2pi"
proof (cases "z \<in> \<real>\<^sub>\<ge>\<^sub>0")
  case False then show ?thesis
    using continuous_at_Arg2pi continuous_at_imp_continuous_within by auto
next
  case True
  then have z: "z \<in> \<real>" "0 < Re z"
    using assms  by (auto simp: complex_nonneg_Reals_iff complex_is_Real_iff complex_neq_0)
  then have [simp]: "Arg2pi z = 0" "Im (Ln z) = 0"
    by (auto simp: Arg2pi_eq_0 Im_Ln_eq_0 assms complex_is_Real_iff)
  show ?thesis
  proof (clarsimp simp add: continuous_within Lim_within dist_norm)
    fix e::real
    assume "0 < e"
    moreover have "continuous (at z) (\<lambda>x. Im (Ln x))"
      using z by (simp add: continuous_at_Ln complex_nonpos_Reals_iff)
    ultimately
    obtain d where d: "d>0" "\<And>x. x \<noteq> z \<Longrightarrow> cmod (x - z) < d \<Longrightarrow> \<bar>Im (Ln x)\<bar> < e"
      by (auto simp: continuous_within Lim_within dist_norm)
    { fix x
      assume "cmod (x - z) < Re z / 2"
      then have "\<bar>Re x - Re z\<bar> < Re z / 2"
        by (metis le_less_trans abs_Re_le_cmod minus_complex.simps(1))
      then have "0 < Re x"
        using z by linarith
    }
    then show "\<exists>d>0. \<forall>x. 0 \<le> Im x \<longrightarrow> x \<noteq> z \<and> cmod (x - z) < d \<longrightarrow> \<bar>Arg2pi x\<bar> < e"
      apply (rule_tac x="min d (Re z / 2)" in exI)
      using z d by (auto simp: Arg2pi_eq_Im_Ln)
  qed
qed

lemma continuous_on_upperhalf_Arg2pi: "continuous_on ({z. 0 \<le> Im z} - {0}) Arg2pi"
  unfolding continuous_on_eq_continuous_within
  by (metis DiffE Diff_subset continuous_within_subset continuous_within_upperhalf_Arg2pi insertCI)

lemma open_Arg2pi2pi_less_Int:
  assumes "0 \<le> s" "t \<le> 2*pi"
    shows "open ({y. s < Arg2pi y} \<inter> {y. Arg2pi y < t})"
proof -
  have 1: "continuous_on (UNIV - \<real>\<^sub>\<ge>\<^sub>0) Arg2pi"
    using continuous_at_Arg2pi continuous_at_imp_continuous_within
    by (auto simp: continuous_on_eq_continuous_within)
  have 2: "open (UNIV - \<real>\<^sub>\<ge>\<^sub>0 :: complex set)"  by (simp add: open_Diff)
  have "open ({z. s < z} \<inter> {z. z < t})"
    using open_lessThan [of t] open_greaterThan [of s]
    by (metis greaterThan_def lessThan_def open_Int)
  moreover have "{y. s < Arg2pi y} \<inter> {y. Arg2pi y < t} \<subseteq> - \<real>\<^sub>\<ge>\<^sub>0"
    using assms by (auto simp: Arg2pi_real complex_nonneg_Reals_iff complex_is_Real_iff)
  ultimately show ?thesis
    using continuous_imp_open_vimage [OF 1 2, of  "{z. Re z > s} \<inter> {z. Re z < t}"]
    by auto
qed

lemma open_Arg2pi2pi_gt: "open {z. t < Arg2pi z}"
proof (cases "t < 0")
  case True then have "{z. t < Arg2pi z} = UNIV"
    using Arg2pi_ge_0 less_le_trans by auto
  then show ?thesis
    by simp
next
  case False then show ?thesis
    using open_Arg2pi2pi_less_Int [of t "2*pi"] Arg2pi_lt_2pi
    by auto
qed

lemma closed_Arg2pi2pi_le: "closed {z. Arg2pi z \<le> t}"
  using open_Arg2pi2pi_gt [of t]
  by (simp add: closed_def Set.Collect_neg_eq [symmetric] not_le)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Complex Powers\<close>

lemma powr_to_1 [simp]: "z powr 1 = (z::complex)"
  by (simp add: powr_def)

lemma powr_nat:
  fixes n::nat and z::complex shows "z powr n = (if z = 0 then 0 else z^n)"
  by (simp add: exp_of_nat_mult powr_def)

lemma norm_powr_real: "w \<in> \<real> \<Longrightarrow> 0 < Re w \<Longrightarrow> norm(w powr z) = exp(Re z * ln(Re w))"
  using Ln_Reals_eq norm_exp_eq_Re by (auto simp: Im_Ln_eq_0 powr_def norm_complex_def)

lemma powr_complexpow [simp]:
  fixes x::complex shows "x \<noteq> 0 \<Longrightarrow> x powr (of_nat n) = x^n"
  by (induct n) (auto simp: ac_simps powr_add)

lemma powr_complexnumeral [simp]:
  fixes x::complex shows "x \<noteq> 0 \<Longrightarrow> x powr (numeral n) = x ^ (numeral n)"
  by (metis of_nat_numeral powr_complexpow)

lemma cnj_powr:
  assumes "Im a = 0 \<Longrightarrow> Re a \<ge> 0"
  shows   "cnj (a powr b) = cnj a powr cnj b"
proof (cases "a = 0")
  case False
  with assms have "a \<notin> \<real>\<^sub>\<le>\<^sub>0" by (auto simp: complex_eq_iff complex_nonpos_Reals_iff)
  with False show ?thesis by (simp add: powr_def exp_cnj cnj_Ln)
qed simp

lemma powr_real_real:
  assumes "w \<in> \<real>" "z \<in> \<real>" "0 < Re w"
  shows "w powr z = exp(Re z * ln(Re w))"
proof -
  have "w \<noteq> 0"
    using assms by auto
  with assms show ?thesis
    by (simp add: powr_def Ln_Reals_eq of_real_exp)
qed

lemma powr_of_real:
  fixes x::real and y::real
  shows "0 \<le> x \<Longrightarrow> of_real x powr (of_real y::complex) = of_real (x powr y)"
  by (simp_all add: powr_def exp_eq_polar)

lemma powr_of_int:
  fixes z::complex and n::int
  assumes "z\<noteq>(0::complex)"
  shows "z powr of_int n = (if n\<ge>0 then z^nat n else inverse (z^nat (-n)))"
  by (metis assms not_le of_int_of_nat powr_complexpow powr_minus)

lemma powr_Reals_eq: "\<lbrakk>x \<in> \<real>; y \<in> \<real>; Re x \<ge> 0\<rbrakk> \<Longrightarrow> x powr y = of_real (Re x powr Re y)"
  by (metis of_real_Re powr_of_real)

lemma norm_powr_real_mono:
    "\<lbrakk>w \<in> \<real>; 1 < Re w\<rbrakk>
     \<Longrightarrow> cmod(w powr z1) \<le> cmod(w powr z2) \<longleftrightarrow> Re z1 \<le> Re z2"
  by (auto simp: powr_def algebra_simps Reals_def Ln_of_real)

lemma powr_times_real:
    "\<lbrakk>x \<in> \<real>; y \<in> \<real>; 0 \<le> Re x; 0 \<le> Re y\<rbrakk>
           \<Longrightarrow> (x * y) powr z = x powr z * y powr z"
  by (auto simp: Reals_def powr_def Ln_times exp_add algebra_simps less_eq_real_def Ln_of_real)

lemma Re_powr_le: "r \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> Re (r powr z) \<le> Re r powr Re z"
  by (auto simp: powr_def nonneg_Reals_def order_trans [OF complex_Re_le_cmod])

lemma
  fixes w::complex
  shows Reals_powr [simp]: "\<lbrakk>w \<in> \<real>\<^sub>\<ge>\<^sub>0; z \<in> \<real>\<rbrakk> \<Longrightarrow> w powr z \<in> \<real>"
  and nonneg_Reals_powr [simp]: "\<lbrakk>w \<in> \<real>\<^sub>\<ge>\<^sub>0; z \<in> \<real>\<rbrakk> \<Longrightarrow> w powr z \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (auto simp: nonneg_Reals_def Reals_def powr_of_real)

lemma powr_neg_real_complex:
  "(- of_real x) powr a = (-1) powr (of_real (sgn x) * a) * of_real x powr (a :: complex)"
proof (cases "x = 0")
  assume x: "x \<noteq> 0"
  hence "(-x) powr a = exp (a * ln (-of_real x))" by (simp add: powr_def)
  also from x have "ln (-of_real x) = Ln (of_real x) + of_real (sgn x) * pi * \<i>"
    by (simp add: Ln_minus Ln_of_real)
  also from x have "exp (a * ...) = cis pi powr (of_real (sgn x) * a) * of_real x powr a"
    by (simp add: powr_def exp_add algebra_simps Ln_of_real cis_conv_exp)
  also note cis_pi
  finally show ?thesis by simp
qed simp_all

lemma has_field_derivative_powr:
  fixes z :: complex
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows "((\<lambda>z. z powr s) has_field_derivative (s * z powr (s - 1))) (at z)"
proof (cases "z=0")
  case False
  then have \<section>: "exp (s * Ln z) * inverse z = exp ((s - 1) * Ln z)"
    by (simp add: divide_complex_def exp_diff left_diff_distrib')
  show ?thesis
    unfolding powr_def
  proof (rule has_field_derivative_transform_within)
    show "((\<lambda>z. exp (s * Ln z)) has_field_derivative s * (if z = 0 then 0 else exp ((s - 1) * Ln z)))
           (at z)"
      by (intro derivative_eq_intros | simp add: assms False \<section>)+
  qed (use False in auto)
qed (use assms in auto)

declare has_field_derivative_powr[THEN DERIV_chain2, derivative_intros]

lemma has_field_derivative_powr_of_int:
  fixes z :: complex
  assumes gderiv:"(g has_field_derivative gd) (at z within S)" and "g z\<noteq>0"
  shows "((\<lambda>z. g z powr of_int n) has_field_derivative (n * g z powr (of_int n - 1) * gd)) (at z within S)"
proof -
  define dd where "dd = of_int n * g z powr (of_int (n - 1)) * gd"
  obtain e where "e>0" and e_dist:"\<forall>y\<in>S. dist z y < e \<longrightarrow> g y \<noteq> 0"
    using DERIV_continuous[OF gderiv,THEN continuous_within_avoid] \<open>g z\<noteq>0\<close> by auto
  have ?thesis when "n\<ge>0"
  proof -
    define dd' where "dd' = of_int n * g z ^ (nat n - 1) * gd"
    have "dd=dd'"
    proof (cases "n=0")
      case False
      then have "n-1 \<ge>0" using \<open>n\<ge>0\<close> by auto
      then have "g z powr (of_int (n - 1)) = g z ^ (nat n - 1)"
        using powr_of_int[OF \<open>g z\<noteq>0\<close>,of "n-1"] by (simp add: nat_diff_distrib')
      then show ?thesis unfolding dd_def dd'_def by simp
    qed (simp add:dd_def dd'_def)
    then have "((\<lambda>z. g z powr of_int n) has_field_derivative dd) (at z within S)
                \<longleftrightarrow> ((\<lambda>z. g z powr of_int n) has_field_derivative dd') (at z within S)"
      by simp
    also have "... \<longleftrightarrow> ((\<lambda>z. g z ^ nat n) has_field_derivative dd') (at z within S)"
    proof (rule has_field_derivative_cong_eventually)
      show "\<forall>\<^sub>F x in at z within S. g x powr of_int n = g x ^ nat n"
        unfolding eventually_at
        apply (rule exI[where x=e])
        using powr_of_int that \<open>e>0\<close> e_dist by (simp add: dist_commute)
    qed (use powr_of_int \<open>g z\<noteq>0\<close> that in simp)
    also have "..." unfolding dd'_def using gderiv that
      by (auto intro!: derivative_eq_intros)
    finally have "((\<lambda>z. g z powr of_int n) has_field_derivative dd) (at z within S)" .
    then show ?thesis unfolding dd_def by simp
  qed
  moreover have ?thesis when "n<0"
  proof -
    define dd' where "dd' = of_int n / g z ^ (nat (1 - n)) * gd"
    have "dd=dd'"
    proof -
      have "g z powr of_int (n - 1) = inverse (g z ^ nat (1-n))"
        using powr_of_int[OF \<open>g z\<noteq>0\<close>,of "n-1"] that by auto
      then show ?thesis
        unfolding dd_def dd'_def by (simp add: divide_inverse)
    qed
    then have "((\<lambda>z. g z powr of_int n) has_field_derivative dd) (at z within S)
                \<longleftrightarrow> ((\<lambda>z. g z powr of_int n) has_field_derivative dd') (at z within S)"
      by simp
    also have "... \<longleftrightarrow> ((\<lambda>z. inverse (g z ^ nat (-n))) has_field_derivative dd') (at z within S)"
    proof (rule has_field_derivative_cong_eventually)
      show "\<forall>\<^sub>F x in at z within S. g x powr of_int n = inverse (g x ^ nat (- n))"
         unfolding eventually_at
        apply (rule exI[where x=e])
        using powr_of_int that \<open>e>0\<close> e_dist by (simp add: dist_commute)
    qed (use powr_of_int \<open>g z\<noteq>0\<close> that in simp)
    also have "..."
    proof -
      have "nat (- n) + nat (1 - n) - Suc 0 = nat (- n) + nat (- n)"
        by auto
      then show ?thesis
        unfolding dd'_def using gderiv that \<open>g z\<noteq>0\<close>
        by (auto intro!: derivative_eq_intros simp add:field_split_simps power_add[symmetric])
    qed
    finally have "((\<lambda>z. g z powr of_int n) has_field_derivative dd) (at z within S)" .
    then show ?thesis unfolding dd_def by simp
  qed
  ultimately show ?thesis by force
qed

lemma field_differentiable_powr_of_int:
  fixes z :: complex
  assumes gderiv: "g field_differentiable (at z within S)" and "g z \<noteq> 0"
  shows "(\<lambda>z. g z powr of_int n) field_differentiable (at z within S)"
using has_field_derivative_powr_of_int assms(2) field_differentiable_def gderiv by blast

lemma holomorphic_on_powr_of_int [holomorphic_intros]:
  assumes holf: "f holomorphic_on S" and 0: "\<And>z. z\<in>S \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>z. (f z) powr of_int n) holomorphic_on S"
proof (cases "n\<ge>0")
  case True
  then have "?thesis \<longleftrightarrow> (\<lambda>z. (f z) ^ nat n) holomorphic_on S"
    by (metis (no_types, lifting) 0 holomorphic_cong powr_of_int)
  moreover have "(\<lambda>z. (f z) ^ nat n) holomorphic_on S"
    using holf by (auto intro: holomorphic_intros)
  ultimately show ?thesis by auto
next
  case False
  then have "?thesis \<longleftrightarrow> (\<lambda>z. inverse (f z) ^ nat (-n)) holomorphic_on S"
    by (metis (no_types, lifting) "0" holomorphic_cong power_inverse powr_of_int)
  moreover have "(\<lambda>z. inverse (f z) ^ nat (-n)) holomorphic_on S"
    using assms by (auto intro!:holomorphic_intros)
  ultimately show ?thesis by auto
qed

lemma has_field_derivative_powr_right [derivative_intros]:
    "w \<noteq> 0 \<Longrightarrow> ((\<lambda>z. w powr z) has_field_derivative Ln w * w powr z) (at z)"
  unfolding powr_def by (intro derivative_eq_intros | simp)+

lemma field_differentiable_powr_right [derivative_intros]:
  fixes w::complex
  shows "w \<noteq> 0 \<Longrightarrow> (\<lambda>z. w powr z) field_differentiable (at z)"
using field_differentiable_def has_field_derivative_powr_right by blast

lemma holomorphic_on_powr_right [holomorphic_intros]:
  assumes "f holomorphic_on s"
  shows "(\<lambda>z. w powr (f z)) holomorphic_on s"
proof (cases "w = 0")
  case False
  with assms show ?thesis
    unfolding holomorphic_on_def field_differentiable_def
    by (metis (full_types) DERIV_chain' has_field_derivative_powr_right)
qed simp

lemma holomorphic_on_divide_gen [holomorphic_intros]:
  assumes f: "f holomorphic_on s" and g: "g holomorphic_on s" and 0: "\<And>z z'. \<lbrakk>z \<in> s; z' \<in> s\<rbrakk> \<Longrightarrow> g z = 0 \<longleftrightarrow> g z' = 0"
shows "(\<lambda>z. f z / g z) holomorphic_on s"
proof (cases "\<exists>z\<in>s. g z = 0")
  case True
  with 0 have "g z = 0" if "z \<in> s" for z
    using that by blast
  then show ?thesis
    using g holomorphic_transform by auto
next
  case False
  with 0 have "g z \<noteq> 0" if "z \<in> s" for z
    using that by blast
  with holomorphic_on_divide show ?thesis
    using f g by blast
qed

lemma norm_powr_real_powr:
  "w \<in> \<real> \<Longrightarrow> 0 \<le> Re w \<Longrightarrow> cmod (w powr z) = Re w powr Re z"
  by (metis dual_order.order_iff_strict norm_powr_real norm_zero of_real_0 of_real_Re powr_def)

lemma tendsto_powr_complex:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes a: "a \<notin> \<real>\<^sub>\<le>\<^sub>0"
  assumes f: "(f \<longlongrightarrow> a) F" and g: "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
proof -
  from a have [simp]: "a \<noteq> 0" by auto
  from f g a have "((\<lambda>z. exp (g z * ln (f z))) \<longlongrightarrow> a powr b) F" (is ?P)
    by (auto intro!: tendsto_intros simp: powr_def)
  also {
    have "eventually (\<lambda>z. z \<noteq> 0) (nhds a)"
      by (intro t1_space_nhds) simp_all
    with f have "eventually (\<lambda>z. f z \<noteq> 0) F" using filterlim_iff by blast
  }
  hence "?P \<longleftrightarrow> ((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
    by (intro tendsto_cong refl) (simp_all add: powr_def mult_ac)
  finally show ?thesis .
qed

lemma tendsto_powr_complex_0:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "(g \<longlongrightarrow> b) F" and b: "Re b > 0"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> 0) F"
proof (rule tendsto_norm_zero_cancel)
  define h where
    "h = (\<lambda>z. if f z = 0 then 0 else exp (Re (g z) * ln (cmod (f z)) + abs (Im (g z)) * pi))"
  {
    fix z :: 'a assume z: "f z \<noteq> 0"
    define c where "c = abs (Im (g z)) * pi"
    from mpi_less_Im_Ln[OF z] Im_Ln_le_pi[OF z]
      have "abs (Im (Ln (f z))) \<le> pi" by simp
    from mult_left_mono[OF this, of "abs (Im (g z))"]
      have "abs (Im (g z) * Im (ln (f z))) \<le> c" by (simp add: abs_mult c_def)
    hence "-Im (g z) * Im (ln (f z)) \<le> c" by simp
    hence "norm (f z powr g z) \<le> h z" by (simp add: powr_def field_simps h_def c_def)
  }
  hence le: "norm (f z powr g z) \<le> h z" for z by (cases "f x = 0") (simp_all add: h_def)

  have g': "(g \<longlongrightarrow> b) (inf F (principal {z. f z \<noteq> 0}))"
    by (rule tendsto_mono[OF _ g]) simp_all
  have "((\<lambda>x. norm (f x)) \<longlongrightarrow> 0) (inf F (principal {z. f z \<noteq> 0}))"
    by (subst tendsto_norm_zero_iff, rule tendsto_mono[OF _ f]) simp_all
  moreover {
    have "filterlim (\<lambda>x. norm (f x)) (principal {0<..}) (principal {z. f z \<noteq> 0})"
      by (auto simp: filterlim_def)
    hence "filterlim (\<lambda>x. norm (f x)) (principal {0<..})
             (inf F (principal {z. f z \<noteq> 0}))"
      by (rule filterlim_mono) simp_all
  }
  ultimately have norm: "filterlim (\<lambda>x. norm (f x)) (at_right 0) (inf F (principal {z. f z \<noteq> 0}))"
    by (simp add: filterlim_inf at_within_def)

  have A: "LIM x inf F (principal {z. f z \<noteq> 0}). Re (g x) * -ln (cmod (f x)) :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top tendsto_intros g' b
          filterlim_compose[OF filterlim_uminus_at_top_at_bot] filterlim_compose[OF ln_at_0] norm)+
  have B: "LIM x inf F (principal {z. f z \<noteq> 0}).
          -\<bar>Im (g x)\<bar> * pi + -(Re (g x) * ln (cmod (f x))) :> at_top"
    by (rule filterlim_tendsto_add_at_top tendsto_intros g')+ (insert A, simp_all)
  have C: "(h \<longlongrightarrow> 0) F" unfolding h_def
    by (intro filterlim_If tendsto_const filterlim_compose[OF exp_at_bot])
       (insert B, auto simp: filterlim_uminus_at_bot algebra_simps)
  show "((\<lambda>x. norm (f x powr g x)) \<longlongrightarrow> 0) F"
    by (rule Lim_null_comparison[OF always_eventually C]) (insert le, auto)
qed

lemma tendsto_powr_complex' [tendsto_intros]:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes "a \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> (a = 0 \<and> Re b > 0)" and "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
  using assms tendsto_powr_complex tendsto_powr_complex_0 by fastforce

lemma tendsto_neg_powr_complex_of_real:
  assumes "filterlim f at_top F" and "Re s < 0"
  shows   "((\<lambda>x. complex_of_real (f x) powr s) \<longlongrightarrow> 0) F"
proof -
  have "((\<lambda>x. norm (complex_of_real (f x) powr s)) \<longlongrightarrow> 0) F"
  proof (rule Lim_transform_eventually)
    from assms(1) have "eventually (\<lambda>x. f x \<ge> 0) F"
      by (auto simp: filterlim_at_top)
    thus "eventually (\<lambda>x. f x powr Re s = norm (of_real (f x) powr s)) F"
      by eventually_elim (simp add: norm_powr_real_powr)
    from assms show "((\<lambda>x. f x powr Re s) \<longlongrightarrow> 0) F"
      by (intro tendsto_neg_powr)
  qed
  thus ?thesis by (simp add: tendsto_norm_zero_iff)
qed

lemma tendsto_neg_powr_complex_of_nat:
  assumes "filterlim f at_top F" and "Re s < 0"
  shows   "((\<lambda>x. of_nat (f x) powr s) \<longlongrightarrow> 0) F"
proof -
  have "((\<lambda>x. of_real (real (f x)) powr s) \<longlongrightarrow> 0) F" using assms(2)
    by (intro filterlim_compose[OF _ tendsto_neg_powr_complex_of_real]
              filterlim_compose[OF _ assms(1)] filterlim_real_sequentially filterlim_ident) auto
  thus ?thesis by simp
qed

lemma continuous_powr_complex:
  assumes "f (netlimit F) \<notin> \<real>\<^sub>\<le>\<^sub>0" "continuous F f" "continuous F g"
  shows   "continuous F (\<lambda>z. f z powr g z :: complex)"
  using assms unfolding continuous_def by (intro tendsto_powr_complex) simp_all

lemma isCont_powr_complex [continuous_intros]:
  assumes "f z \<notin> \<real>\<^sub>\<le>\<^sub>0" "isCont f z" "isCont g z"
  shows   "isCont (\<lambda>z. f z powr g z :: complex) z"
  using assms unfolding isCont_def by (intro tendsto_powr_complex) simp_all

lemma continuous_on_powr_complex [continuous_intros]:
  assumes "A \<subseteq> {z. Re (f z) \<ge> 0 \<or> Im (f z) \<noteq> 0}"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z = 0 \<Longrightarrow> Re (g z) > 0"
  assumes "continuous_on A f" "continuous_on A g"
  shows   "continuous_on A (\<lambda>z. f z powr g z)"
  unfolding continuous_on_def
proof
  fix z assume z: "z \<in> A"
  show "((\<lambda>z. f z powr g z) \<longlongrightarrow> f z powr g z) (at z within A)"
  proof (cases "f z = 0")
    case False
    from assms(1,2) z have "Re (f z) \<ge> 0 \<or> Im (f z) \<noteq> 0" "f z = 0 \<longrightarrow> Re (g z) > 0" by auto
    with assms(3,4) z show ?thesis
      by (intro tendsto_powr_complex')
         (auto elim!: nonpos_Reals_cases simp: complex_eq_iff continuous_on_def)
  next
    case True
    with assms z show ?thesis
      by (auto intro!: tendsto_powr_complex_0 simp: continuous_on_def)
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Some Limits involving Logarithms\<close>

lemma lim_Ln_over_power:
  fixes s::complex
  assumes "0 < Re s"
    shows "(\<lambda>n. Ln (of_nat n) / of_nat n powr s) \<longlonglongrightarrow> 0"
proof (simp add: lim_sequentially dist_norm, clarify)
  fix e::real
  assume e: "0 < e"
  have "\<exists>xo>0. \<forall>x\<ge>xo. 0 < e * 2 + (e * Re s * 2 - 2) * x + e * (Re s)\<^sup>2 * x\<^sup>2"
  proof (rule_tac x="2/(e * (Re s)\<^sup>2)" in exI, safe)
    show "0 < 2 / (e * (Re s)\<^sup>2)"
      using e assms by (simp add: field_simps)
  next
    fix x::real
    assume x: "2 / (e * (Re s)\<^sup>2) \<le> x"
    have "2 / (e * (Re s)\<^sup>2) > 0"
      using e assms by simp
    with x have "x > 0"
      by linarith
    then have "x * 2 \<le> e * (x\<^sup>2 * (Re s)\<^sup>2)"
      using e assms x by (auto simp: power2_eq_square field_simps)
    also have "... < e * (2 + (x * (Re s * 2) + x\<^sup>2 * (Re s)\<^sup>2))"
      using e assms \<open>x > 0\<close>
      by (auto simp: power2_eq_square field_simps add_pos_pos)
    finally show "0 < e * 2 + (e * Re s * 2 - 2) * x + e * (Re s)\<^sup>2 * x\<^sup>2"
      by (auto simp: algebra_simps)
  qed
  then have "\<exists>xo>0. \<forall>x\<ge>xo. x / e < 1 + (Re s * x) + (1/2) * (Re s * x)^2"
    using e  by (simp add: field_simps)
  then have "\<exists>xo>0. \<forall>x\<ge>xo. x / e < exp (Re s * x)"
    using assms
    by (force intro: less_le_trans [OF _ exp_lower_Taylor_quadratic])
  then obtain xo where "xo > 0" and xo: "\<And>x. x \<ge> xo \<Longrightarrow> x < e * exp (Re s * x)"
    using e  by (auto simp: field_simps)
  have "norm (Ln (of_nat n) / of_nat n powr s) < e" if "n \<ge> nat \<lceil>exp xo\<rceil>" for n
  proof -
    have "ln (real n) \<ge> xo"
      using that exp_gt_zero ln_ge_iff [of n] nat_ceiling_le_eq by fastforce
    then show ?thesis
      using e xo [of "ln n"]  by (auto simp: norm_divide norm_powr_real field_split_simps)
  qed
  then show "\<exists>no. \<forall>n\<ge>no. norm (Ln (of_nat n) / of_nat n powr s) < e"
    by blast
qed

lemma lim_Ln_over_n: "((\<lambda>n. Ln(of_nat n) / of_nat n) \<longlongrightarrow> 0) sequentially"
  using lim_Ln_over_power [of 1] by simp

lemma lim_ln_over_power:
  fixes s :: real
  assumes "0 < s"
  shows "((\<lambda>n. ln n / (n powr s)) \<longlongrightarrow> 0) sequentially"
proof -
  have "(\<lambda>n. ln (Suc n) / (Suc n) powr s) \<longlonglongrightarrow> 0"
    using lim_Ln_over_power [of "of_real s", THEN filterlim_sequentially_Suc [THEN iffD2]] assms
    by (simp add: lim_sequentially dist_norm Ln_Reals_eq norm_powr_real_powr norm_divide)
  then show ?thesis
    using filterlim_sequentially_Suc[of "\<lambda>n::nat. ln n / n powr s"] by auto
qed

lemma lim_ln_over_n [tendsto_intros]: "((\<lambda>n. ln(real_of_nat n) / of_nat n) \<longlongrightarrow> 0) sequentially"
  using lim_ln_over_power [of 1] by auto

lemma lim_log_over_n [tendsto_intros]:
  "(\<lambda>n. log k n/n) \<longlonglongrightarrow> 0"
proof -
  have *: "log k n/n = (1/ln k) * (ln n / n)" for n
    unfolding log_def by auto
  have "(\<lambda>n. (1/ln k) * (ln n / n)) \<longlonglongrightarrow> (1/ln k) * 0"
    by (intro tendsto_intros)
  then show ?thesis
    unfolding * by auto
qed

lemma lim_1_over_complex_power:
  assumes "0 < Re s"
  shows "(\<lambda>n. 1 / of_nat n powr s) \<longlonglongrightarrow> 0"
proof (rule Lim_null_comparison)
  have "\<forall>n>0. 3 \<le> n \<longrightarrow> 1 \<le> ln (real_of_nat n)"
    using ln_272_gt_1
    by (force intro: order_trans [of _ "ln (272/100)"])
  then show "\<forall>\<^sub>F x in sequentially. cmod (1 / of_nat x powr s) \<le> cmod (Ln (of_nat x) / of_nat x powr s)"
    by (auto simp: norm_divide field_split_simps eventually_sequentially)
  show "(\<lambda>n. cmod (Ln (of_nat n) / of_nat n powr s)) \<longlonglongrightarrow> 0"
    using lim_Ln_over_power [OF assms] by (metis tendsto_norm_zero_iff)
qed

lemma lim_1_over_real_power:
  fixes s :: real
  assumes "0 < s"
  shows "((\<lambda>n. 1 / (of_nat n powr s)) \<longlongrightarrow> 0) sequentially"
  using lim_1_over_complex_power [of "of_real s", THEN filterlim_sequentially_Suc [THEN iffD2]] assms
  apply (subst filterlim_sequentially_Suc [symmetric])
  by (simp add: lim_sequentially dist_norm Ln_Reals_eq norm_powr_real_powr norm_divide)

lemma lim_1_over_Ln: "((\<lambda>n. 1 / Ln(of_nat n)) \<longlongrightarrow> 0) sequentially"
proof (clarsimp simp add: lim_sequentially dist_norm norm_divide field_split_simps)
  fix r::real
  assume "0 < r"
  have ir: "inverse (exp (inverse r)) > 0"
    by simp
  obtain n where n: "1 < of_nat n * inverse (exp (inverse r))"
    using ex_less_of_nat_mult [of _ 1, OF ir]
    by auto
  then have "exp (inverse r) < of_nat n"
    by (simp add: field_split_simps)
  then have "ln (exp (inverse r)) < ln (of_nat n)"
    by (metis exp_gt_zero less_trans ln_exp ln_less_cancel_iff)
  with \<open>0 < r\<close> have "1 < r * ln (real_of_nat n)"
    by (simp add: field_simps)
  moreover have "n > 0" using n
    using neq0_conv by fastforce
  ultimately show "\<exists>no. \<forall>k. Ln (of_nat k) \<noteq> 0 \<longrightarrow> no \<le> k \<longrightarrow> 1 < r * cmod (Ln (of_nat k))"
    using n \<open>0 < r\<close>
    by (rule_tac x=n in exI) (force simp: field_split_simps intro: less_le_trans)
qed

lemma lim_1_over_ln: "((\<lambda>n. 1 / ln(real_of_nat n)) \<longlongrightarrow> 0) sequentially"
  using lim_1_over_Ln [THEN filterlim_sequentially_Suc [THEN iffD2]]
  apply (subst filterlim_sequentially_Suc [symmetric])
  by (simp add: lim_sequentially dist_norm Ln_Reals_eq norm_powr_real_powr norm_divide)

lemma lim_ln1_over_ln: "(\<lambda>n. ln(Suc n) / ln n) \<longlonglongrightarrow> 1"
proof (rule Lim_transform_eventually)
  have "(\<lambda>n. ln(1 + 1/n) / ln n) \<longlonglongrightarrow> 0"
  proof (rule Lim_transform_bound)
    show "(inverse o real) \<longlonglongrightarrow> 0"
      by (metis comp_def lim_inverse_n lim_explicit)
    show "\<forall>\<^sub>F n in sequentially. norm (ln (1 + 1 / n) / ln n) \<le> norm ((inverse \<circ> real) n)"
    proof
      fix n::nat
      assume n: "3 \<le> n"
      then have "ln 3 \<le> ln n" and ln0: "0 \<le> ln n"
        by auto
      with ln3_gt_1 have "1/ ln n \<le> 1"
        by (simp add: field_split_simps)
      moreover have "ln (1 + 1 / real n) \<le> 1/n"
        by (simp add: ln_add_one_self_le_self)
      ultimately have "ln (1 + 1 / real n) * (1 / ln n) \<le> (1/n) * 1"
        by (intro mult_mono) (use n in auto)
      then show "norm (ln (1 + 1 / n) / ln n) \<le> norm ((inverse \<circ> real) n)"
        by (simp add: field_simps ln0)
      qed
  qed
  then show "(\<lambda>n. 1 + ln(1 + 1/n) / ln n) \<longlonglongrightarrow> 1"
    by (metis (full_types) add.right_neutral tendsto_add_const_iff)
  show "\<forall>\<^sub>F k in sequentially. 1 + ln (1 + 1 / k) / ln k = ln(Suc k) / ln k"
    by (simp add: field_split_simps ln_div eventually_sequentiallyI [of 2])
qed

lemma lim_ln_over_ln1: "(\<lambda>n. ln n / ln(Suc n)) \<longlonglongrightarrow> 1"
proof -
  have "(\<lambda>n. inverse (ln(Suc n) / ln n)) \<longlonglongrightarrow> inverse 1"
    by (rule tendsto_inverse [OF lim_ln1_over_ln]) auto
  then show ?thesis
    by simp
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relation between Square Root and exp/ln, hence its derivative\<close>

lemma csqrt_exp_Ln:
  assumes "z \<noteq> 0"
    shows "csqrt z = exp(Ln(z) / 2)"
proof -
  have "(exp (Ln z / 2))\<^sup>2 = (exp (Ln z))"
    by (metis exp_double nonzero_mult_div_cancel_left times_divide_eq_right zero_neq_numeral)
  also have "... = z"
    using assms exp_Ln by blast
  finally have "csqrt z = csqrt ((exp (Ln z / 2))\<^sup>2)"
    by simp
  also have "... = exp (Ln z / 2)"
    apply (rule csqrt_square)
    using cos_gt_zero_pi [of "(Im (Ln z) / 2)"] Im_Ln_le_pi mpi_less_Im_Ln assms
    by (fastforce simp: Re_exp Im_exp )
  finally show ?thesis using assms csqrt_square
    by simp
qed

lemma csqrt_inverse:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "csqrt (inverse z) = inverse (csqrt z)"
proof (cases "z=0")
  case False
  then show ?thesis
    using assms csqrt_exp_Ln Ln_inverse exp_minus
    by (simp add: csqrt_exp_Ln Ln_inverse exp_minus)
qed auto

lemma cnj_csqrt:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "cnj(csqrt z) = csqrt(cnj z)"
proof (cases "z=0")
  case False
  then show ?thesis
     by (simp add: assms cnj_Ln csqrt_exp_Ln exp_cnj)
qed auto

lemma has_field_derivative_csqrt:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "(csqrt has_field_derivative inverse(2 * csqrt z)) (at z)"
proof -
  have z: "z \<noteq> 0"
    using assms by auto
  then have *: "inverse z = inverse (2*z) * 2"
    by (simp add: field_split_simps)
  have [simp]: "exp (Ln z / 2) * inverse z = inverse (csqrt z)"
    by (simp add: z field_simps csqrt_exp_Ln [symmetric]) (metis power2_csqrt power2_eq_square)
  have "Im z = 0 \<Longrightarrow> 0 < Re z"
    using assms complex_nonpos_Reals_iff not_less by blast
  with z have "((\<lambda>z. exp (Ln z / 2)) has_field_derivative inverse (2 * csqrt z)) (at z)"
    by (force intro: derivative_eq_intros * simp add: assms)
  then show ?thesis
  proof (rule has_field_derivative_transform_within)
    show "\<And>x. dist x z < cmod z \<Longrightarrow> exp (Ln x / 2) = csqrt x"
      by (metis csqrt_exp_Ln dist_0_norm less_irrefl)
  qed (use z in auto)
qed

lemma field_differentiable_at_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt field_differentiable at z"
  using field_differentiable_def has_field_derivative_csqrt by blast

lemma field_differentiable_within_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt field_differentiable (at z within s)"
  using field_differentiable_at_csqrt field_differentiable_within_subset by blast

lemma continuous_at_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z) csqrt"
  by (simp add: field_differentiable_within_csqrt field_differentiable_imp_continuous_at)

corollary\<^marker>\<open>tag unimportant\<close> isCont_csqrt' [simp]:
   "\<lbrakk>isCont f z; f z \<notin> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. csqrt (f x)) z"
  by (blast intro: isCont_o2 [OF _ continuous_at_csqrt])

lemma continuous_within_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within s) csqrt"
  by (simp add: field_differentiable_imp_continuous_at field_differentiable_within_csqrt)

lemma continuous_on_csqrt [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on s csqrt"
  by (simp add: continuous_at_imp_continuous_on continuous_within_csqrt)

lemma holomorphic_on_csqrt:
    "(\<And>z. z \<in> s \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> csqrt holomorphic_on s"
  by (simp add: field_differentiable_within_csqrt holomorphic_on_def)

lemma continuous_within_closed_nontrivial:
    "closed s \<Longrightarrow> a \<notin> s ==> continuous (at a within s) f"
  using open_Compl
  by (force simp add: continuous_def eventually_at_topological filterlim_iff open_Collect_neg)

lemma continuous_within_csqrt_posreal:
    "continuous (at z within (\<real> \<inter> {w. 0 \<le> Re(w)})) csqrt"
proof (cases "z \<in> \<real>\<^sub>\<le>\<^sub>0")
  case True
  have [simp]: "Im z = 0" and 0: "Re z < 0 \<or> z = 0"
    using True cnj.code complex_cnj_zero_iff  by (auto simp: Complex_eq complex_nonpos_Reals_iff) fastforce
  show ?thesis
    using 0
  proof
    assume "Re z < 0"
    then show ?thesis
      by (auto simp: continuous_within_closed_nontrivial [OF closed_Real_halfspace_Re_ge])
  next
    assume "z = 0"
    moreover
    have "\<And>e. 0 < e
         \<Longrightarrow> \<forall>x'\<in>\<real> \<inter> {w. 0 \<le> Re w}. cmod x' < e^2 \<longrightarrow> cmod (csqrt x') < e"
      by (auto simp: Reals_def real_less_lsqrt)
    ultimately show ?thesis
      using zero_less_power by (fastforce simp: continuous_within_eps_delta)
  qed
qed (blast intro: continuous_within_csqrt)

subsection\<open>Complex arctangent\<close>

text\<open>The branch cut gives standard bounds in the real case.\<close>

definition\<^marker>\<open>tag important\<close> Arctan :: "complex \<Rightarrow> complex" where
    "Arctan \<equiv> \<lambda>z. (\<i>/2) * Ln((1 - \<i>*z) / (1 + \<i>*z))"

lemma Arctan_def_moebius: "Arctan z = \<i>/2 * Ln (moebius (-\<i>) 1 \<i> 1 z)"
  by (simp add: Arctan_def moebius_def add_ac)

lemma Ln_conv_Arctan:
  assumes "z \<noteq> -1"
  shows   "Ln z = -2*\<i> * Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z)"
proof -
  have "Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z) =
             \<i>/2 * Ln (moebius (- \<i>) 1 \<i> 1 (moebius 1 (- 1) (- \<i>) (- \<i>) z))"
    by (simp add: Arctan_def_moebius)
  also from assms have "\<i> * z \<noteq> \<i> * (-1)" by (subst mult_left_cancel) simp
  hence "\<i> * z - -\<i> \<noteq> 0" by (simp add: eq_neg_iff_add_eq_0)
  from moebius_inverse'[OF _ this, of 1 1]
    have "moebius (- \<i>) 1 \<i> 1 (moebius 1 (- 1) (- \<i>) (- \<i>) z) = z" by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma Arctan_0 [simp]: "Arctan 0 = 0"
  by (simp add: Arctan_def)

lemma Im_complex_div_lemma: "Im((1 - \<i>*z) / (1 + \<i>*z)) = 0 \<longleftrightarrow> Re z = 0"
  by (auto simp: Im_complex_div_eq_0 algebra_simps)

lemma Re_complex_div_lemma: "0 < Re((1 - \<i>*z) / (1 + \<i>*z)) \<longleftrightarrow> norm z < 1"
  by (simp add: Re_complex_div_gt_0 algebra_simps cmod_def power2_eq_square)

lemma tan_Arctan:
  assumes "z\<^sup>2 \<noteq> -1"
    shows [simp]:"tan(Arctan z) = z"
proof -
  have "1 + \<i>*z \<noteq> 0"
    by (metis assms complex_i_mult_minus i_squared minus_unique power2_eq_square power2_minus)
  moreover
  have "1 - \<i>*z \<noteq> 0"
    by (metis assms complex_i_mult_minus i_squared power2_eq_square power2_minus right_minus_eq)
  ultimately
  show ?thesis
    by (simp add: Arctan_def tan_def sin_exp_eq cos_exp_eq exp_minus csqrt_exp_Ln [symmetric]
                  divide_simps power2_eq_square [symmetric])
qed

lemma Arctan_tan [simp]:
  assumes "\<bar>Re z\<bar> < pi/2"
    shows "Arctan(tan z) = z"
proof -
  have "Ln ((1 - \<i> * tan z) / (1 + \<i> * tan z)) = 2 * z / \<i>"
  proof (rule Ln_unique)
    have ge_pi2: "\<And>n::int. \<bar>of_int (2*n + 1) * pi/2\<bar> \<ge> pi/2"
      by (case_tac n rule: int_cases) (auto simp: abs_mult)
    have "exp (\<i>*z)*exp (\<i>*z) = -1 \<longleftrightarrow> exp (2*\<i>*z) = -1"
      by (metis distrib_right exp_add mult_2)
    also have "... \<longleftrightarrow> exp (2*\<i>*z) = exp (\<i>*pi)"
      using cis_conv_exp cis_pi by auto
    also have "... \<longleftrightarrow> exp (2*\<i>*z - \<i>*pi) = 1"
      by (metis (no_types) diff_add_cancel diff_minus_eq_add exp_add exp_minus_inverse mult.commute)
    also have "... \<longleftrightarrow> Re(\<i>*2*z - \<i>*pi) = 0 \<and> (\<exists>n::int. Im(\<i>*2*z - \<i>*pi) = of_int (2 * n) * pi)"
      by (simp add: exp_eq_1)
    also have "... \<longleftrightarrow> Im z = 0 \<and> (\<exists>n::int. 2 * Re z = of_int (2*n + 1) * pi)"
      by (simp add: algebra_simps)
    also have "... \<longleftrightarrow> False"
      using assms ge_pi2
      apply (auto simp: algebra_simps)
      by (metis abs_mult_pos not_less of_nat_less_0_iff of_nat_numeral)
    finally have "exp (\<i>*z)*exp (\<i>*z) + 1 \<noteq> 0"
      by (auto simp: add.commute minus_unique)
    then show "exp (2 * z / \<i>) = (1 - \<i> * tan z) / (1 + \<i> * tan z)"
      apply (simp add: tan_def sin_exp_eq cos_exp_eq exp_minus divide_simps)
      by (simp add: algebra_simps flip: power2_eq_square exp_double)
  qed (use assms in auto)
  then show ?thesis
    by (auto simp: Arctan_def)
qed

lemma
  assumes "Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1"
  shows Re_Arctan_bounds: "\<bar>Re(Arctan z)\<bar> < pi/2"
    and has_field_derivative_Arctan: "(Arctan has_field_derivative inverse(1 + z\<^sup>2)) (at z)"
proof -
  have nz0: "1 + \<i>*z \<noteq> 0"
    using assms
    by (metis abs_one add_diff_cancel_left' complex_i_mult_minus diff_0 i_squared imaginary_unit.simps
                less_asym neg_equal_iff_equal)
  have "z \<noteq> -\<i>" using assms
    by auto
  then have zz: "1 + z * z \<noteq> 0"
    by (metis abs_one assms i_squared imaginary_unit.simps less_irrefl minus_unique square_eq_iff)
  have nz1: "1 - \<i>*z \<noteq> 0"
    using assms by (force simp add: i_times_eq_iff)
  have nz2: "inverse (1 + \<i>*z) \<noteq> 0"
    using assms
    by (metis Im_complex_div_lemma Re_complex_div_lemma cmod_eq_Im divide_complex_def
              less_irrefl mult_zero_right zero_complex.simps(1) zero_complex.simps(2))
  have nzi: "((1 - \<i>*z) * inverse (1 + \<i>*z)) \<noteq> 0"
    using nz1 nz2 by auto
  have "Im ((1 - \<i>*z) / (1 + \<i>*z)) = 0 \<Longrightarrow> 0 < Re ((1 - \<i>*z) / (1 + \<i>*z))"
    apply (simp add: divide_complex_def)
    apply (simp add: divide_simps split: if_split_asm)
    using assms
    apply (auto simp: algebra_simps abs_square_less_1 [unfolded power2_eq_square])
    done
  then have *: "((1 - \<i>*z) / (1 + \<i>*z)) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (auto simp add: complex_nonpos_Reals_iff)
  show "\<bar>Re(Arctan z)\<bar> < pi/2"
    unfolding Arctan_def divide_complex_def
    using mpi_less_Im_Ln [OF nzi]
    by (auto simp: abs_if intro!: Im_Ln_less_pi * [unfolded divide_complex_def])
  show "(Arctan has_field_derivative inverse(1 + z\<^sup>2)) (at z)"
    unfolding Arctan_def scaleR_conv_of_real
    apply (intro derivative_eq_intros | simp add: nz0 *)+
    using nz1 zz
    apply (simp add: field_split_simps power2_eq_square)
    apply algebra
    done
qed

lemma field_differentiable_at_Arctan: "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan field_differentiable at z"
  using has_field_derivative_Arctan
  by (auto simp: field_differentiable_def)

lemma field_differentiable_within_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan field_differentiable (at z within s)"
  using field_differentiable_at_Arctan field_differentiable_at_within by blast

declare has_field_derivative_Arctan [derivative_intros]
declare has_field_derivative_Arctan [THEN DERIV_chain2, derivative_intros]

lemma continuous_at_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous (at z) Arctan"
  by (simp add: field_differentiable_imp_continuous_at field_differentiable_within_Arctan)

lemma continuous_within_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arctan"
  using continuous_at_Arctan continuous_at_imp_continuous_within by blast

lemma continuous_on_Arctan [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous_on s Arctan"
  by (auto simp: continuous_at_imp_continuous_on continuous_within_Arctan)

lemma holomorphic_on_Arctan:
    "(\<And>z. z \<in> s \<Longrightarrow> Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan holomorphic_on s"
  by (simp add: field_differentiable_within_Arctan holomorphic_on_def)

theorem Arctan_series:
  assumes z: "norm (z :: complex) < 1"
  defines "g \<equiv> \<lambda>n. if odd n then -\<i>*\<i>^n / n else 0"
  defines "h \<equiv> \<lambda>z n. (-1)^n / of_nat (2*n+1) * (z::complex)^(2*n+1)"
  shows   "(\<lambda>n. g n * z^n) sums Arctan z"
  and     "h z sums Arctan z"
proof -
  define G where [abs_def]: "G z = (\<Sum>n. g n * z^n)" for z
  have summable: "summable (\<lambda>n. g n * u^n)" if "norm u < 1" for u
  proof (cases "u = 0")
    assume u: "u \<noteq> 0"
    have "(\<lambda>n. ereal (norm (h u n) / norm (h u (Suc n)))) = (\<lambda>n. ereal (inverse (norm u)^2) *
              ereal ((2 + inverse (real (Suc n))) / (2 - inverse (real (Suc n)))))"
    proof
      fix n
      have "ereal (norm (h u n) / norm (h u (Suc n))) =
             ereal (inverse (norm u)^2) * ereal (((2*Suc n+1) / (Suc n)) /
                 ((2*Suc n-1) / (Suc n)))"
      by (simp add: h_def norm_mult norm_power norm_divide field_split_simps
                    power2_eq_square eval_nat_numeral del: of_nat_add of_nat_Suc)
      also have "of_nat (2*Suc n+1) / of_nat (Suc n) = (2::real) + inverse (real (Suc n))"
        by (auto simp: field_split_simps simp del: of_nat_Suc) simp_all?
      also have "of_nat (2*Suc n-1) / of_nat (Suc n) = (2::real) - inverse (real (Suc n))"
        by (auto simp: field_split_simps simp del: of_nat_Suc) simp_all?
      finally show "ereal (norm (h u n) / norm (h u (Suc n))) = ereal (inverse (norm u)^2) *
              ereal ((2 + inverse (real (Suc n))) / (2 - inverse (real (Suc n))))" .
    qed
    also have "\<dots> \<longlonglongrightarrow> ereal (inverse (norm u)^2) * ereal ((2 + 0) / (2 - 0))"
      by (intro tendsto_intros LIMSEQ_inverse_real_of_nat) simp_all
    finally have "liminf (\<lambda>n. ereal (cmod (h u n) / cmod (h u (Suc n)))) = inverse (norm u)^2"
      by (intro lim_imp_Liminf) simp_all
    moreover from power_strict_mono[OF that, of 2] u have "inverse (norm u)^2 > 1"
      by (simp add: field_split_simps)
    ultimately have A: "liminf (\<lambda>n. ereal (cmod (h u n) / cmod (h u (Suc n)))) > 1" by simp
    from u have "summable (h u)"
      by (intro summable_norm_cancel[OF ratio_test_convergence[OF _ A]])
         (auto simp: h_def norm_divide norm_mult norm_power simp del: of_nat_Suc
               intro!: mult_pos_pos divide_pos_pos always_eventually)
    thus "summable (\<lambda>n. g n * u^n)"
      by (subst summable_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
         (auto simp: power_mult strict_mono_def g_def h_def elim!: oddE)
  qed (simp add: h_def)

  have "\<exists>c. \<forall>u\<in>ball 0 1. Arctan u - G u = c"
  proof (rule has_field_derivative_zero_constant)
    fix u :: complex assume "u \<in> ball 0 1"
    hence u: "norm u < 1" by (simp)
    define K where "K = (norm u + 1) / 2"
    from u and abs_Im_le_cmod[of u] have Im_u: "\<bar>Im u\<bar> < 1" by linarith
    from u have K: "0 \<le> K" "norm u < K" "K < 1" by (simp_all add: K_def)
    hence "(G has_field_derivative (\<Sum>n. diffs g n * u ^ n)) (at u)" unfolding G_def
      by (intro termdiffs_strong[of _ "of_real K"] summable) simp_all
    also have "(\<lambda>n. diffs g n * u^n) = (\<lambda>n. if even n then (\<i>*u)^n else 0)"
      by (intro ext) (simp_all del: of_nat_Suc add: g_def diffs_def power_mult_distrib)
    also have "suminf \<dots> = (\<Sum>n. (-(u^2))^n)"
      by (subst suminf_mono_reindex[of "\<lambda>n. 2*n", symmetric])
         (auto elim!: evenE simp: strict_mono_def power_mult power_mult_distrib)
    also from u have "norm u^2 < 1^2" by (intro power_strict_mono) simp_all
    hence "(\<Sum>n. (-(u^2))^n) = inverse (1 + u^2)"
      by (subst suminf_geometric) (simp_all add: norm_power inverse_eq_divide)
    finally have "(G has_field_derivative inverse (1 + u\<^sup>2)) (at u)" .
    from DERIV_diff[OF has_field_derivative_Arctan this] Im_u u
      show "((\<lambda>u. Arctan u - G u) has_field_derivative 0) (at u within ball 0 1)"
      by (simp_all add: at_within_open[OF _ open_ball])
  qed simp_all
  then obtain c where c: "\<And>u. norm u < 1 \<Longrightarrow> Arctan u - G u = c" by auto
  from this[of 0] have "c = 0" by (simp add: G_def g_def)
  with c z have "Arctan z = G z" by simp
  with summable[OF z] show "(\<lambda>n. g n * z^n) sums Arctan z" unfolding G_def by (simp add: sums_iff)
  thus "h z sums Arctan z" by (subst (asm) sums_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
                              (auto elim!: oddE simp: strict_mono_def power_mult g_def h_def)
qed

text \<open>A quickly-converging series for the logarithm, based on the arctangent.\<close>
theorem ln_series_quadratic:
  assumes x: "x > (0::real)"
  shows "(\<lambda>n. (2*((x - 1) / (x + 1)) ^ (2*n+1) / of_nat (2*n+1))) sums ln x"
proof -
  define y :: complex where "y = of_real ((x-1)/(x+1))"
  from x have x': "complex_of_real x \<noteq> of_real (-1)"  by (subst of_real_eq_iff) auto
  from x have "\<bar>x - 1\<bar> < \<bar>x + 1\<bar>" by linarith
  hence "norm (complex_of_real (x - 1) / complex_of_real (x + 1)) < 1"
    by (simp add: norm_divide del: of_real_add of_real_diff)
  hence "norm (\<i> * y) < 1" unfolding y_def by (subst norm_mult) simp
  hence "(\<lambda>n. (-2*\<i>) * ((-1)^n / of_nat (2*n+1) * (\<i>*y)^(2*n+1))) sums ((-2*\<i>) * Arctan (\<i>*y))"
    by (intro Arctan_series sums_mult) simp_all
  also have "(\<lambda>n. (-2*\<i>) * ((-1)^n / of_nat (2*n+1) * (\<i>*y)^(2*n+1))) =
                 (\<lambda>n. (-2*\<i>) * ((-1)^n * (\<i>*y*(-y\<^sup>2)^n)/of_nat (2*n+1)))"
    by (intro ext) (simp_all add: power_mult power_mult_distrib)
  also have "\<dots> = (\<lambda>n. 2*y* ((-1) * (-y\<^sup>2))^n/of_nat (2*n+1))"
    by (intro ext, subst power_mult_distrib) (simp add: algebra_simps power_mult)
  also have "\<dots> = (\<lambda>n. 2*y^(2*n+1) / of_nat (2*n+1))"
    by (subst power_add, subst power_mult) (simp add: mult_ac)
  also have "\<dots> = (\<lambda>n. of_real (2*((x-1)/(x+1))^(2*n+1) / of_nat (2*n+1)))"
    by (intro ext) (simp add: y_def)
  also have "\<i> * y = (of_real x - 1) / (-\<i> * (of_real x + 1))"
    by (subst divide_divide_eq_left [symmetric]) (simp add: y_def)
  also have "\<dots> = moebius 1 (-1) (-\<i>) (-\<i>) (of_real x)" by (simp add: moebius_def algebra_simps)
  also from x' have "-2*\<i>*Arctan \<dots> = Ln (of_real x)" by (intro Ln_conv_Arctan [symmetric]) simp_all
  also from x have "\<dots> = ln x" by (rule Ln_of_real)
  finally show ?thesis by (subst (asm) sums_of_real_iff)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Real arctangent\<close>

lemma Im_Arctan_of_real [simp]: "Im (Arctan (of_real x)) = 0"
proof -
  have ne: "1 + x\<^sup>2 \<noteq> 0"
    by (metis power_one sum_power2_eq_zero_iff zero_neq_one)
  have ne1: "1 + \<i> * complex_of_real x \<noteq> 0"
    using Complex_eq complex_eq_cancel_iff2 by fastforce 
  have "Re (Ln ((1 - \<i> * x) * inverse (1 + \<i> * x))) = 0"
    apply (rule norm_exp_imaginary)
    using ne
    apply (simp add: ne1 cmod_def)
    apply (auto simp: field_split_simps)
    apply algebra
    done
  then show ?thesis
    unfolding Arctan_def divide_complex_def by (simp add: complex_eq_iff)
qed

lemma arctan_eq_Re_Arctan: "arctan x = Re (Arctan (of_real x))"
proof (rule arctan_unique)
  have "(1 - \<i> * x) / (1 + \<i> * x) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (auto simp: Im_complex_div_lemma complex_nonpos_Reals_iff)
  then show "- (pi / 2) < Re (Arctan (complex_of_real x))"
    by (simp add: Arctan_def Im_Ln_less_pi)
next
  have *: " (1 - \<i>*x) / (1 + \<i>*x) \<noteq> 0"
    by (simp add: field_split_simps) ( simp add: complex_eq_iff)
  show "Re (Arctan (complex_of_real x)) < pi / 2"
    using mpi_less_Im_Ln [OF *]
    by (simp add: Arctan_def)
next
  have "tan (Re (Arctan (of_real x))) = Re (tan (Arctan (of_real x)))"
    by (auto simp: tan_def Complex.Re_divide Re_sin Re_cos Im_sin Im_cos field_simps power2_eq_square)
  also have "... = x"
  proof -
    have "(complex_of_real x)\<^sup>2 \<noteq> - 1"
      by (metis diff_0_right minus_diff_eq mult_zero_left not_le of_real_1 of_real_eq_iff of_real_minus of_real_power power2_eq_square real_minus_mult_self_le zero_less_one)
    then show ?thesis
      by simp
  qed
  finally show "tan (Re (Arctan (complex_of_real x))) = x" .
qed

lemma Arctan_of_real: "Arctan (of_real x) = of_real (arctan x)"
  unfolding arctan_eq_Re_Arctan divide_complex_def
  by (simp add: complex_eq_iff)

lemma Arctan_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> Arctan z \<in> \<real>"
  by (metis Reals_cases Reals_of_real Arctan_of_real)

declare arctan_one [simp]

lemma arctan_less_pi4_pos: "x < 1 \<Longrightarrow> arctan x < pi/4"
  by (metis arctan_less_iff arctan_one)

lemma arctan_less_pi4_neg: "-1 < x \<Longrightarrow> -(pi/4) < arctan x"
  by (metis arctan_less_iff arctan_minus arctan_one)

lemma arctan_less_pi4: "\<bar>x\<bar> < 1 \<Longrightarrow> \<bar>arctan x\<bar> < pi/4"
  by (metis abs_less_iff arctan_less_pi4_pos arctan_minus)

lemma arctan_le_pi4: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>arctan x\<bar> \<le> pi/4"
  by (metis abs_le_iff arctan_le_iff arctan_minus arctan_one)

lemma abs_arctan: "\<bar>arctan x\<bar> = arctan \<bar>x\<bar>"
  by (simp add: abs_if arctan_minus)

lemma arctan_add_raw:
  assumes "\<bar>arctan x + arctan y\<bar> < pi/2"
    shows "arctan x + arctan y = arctan((x + y) / (1 - x * y))"
proof (rule arctan_unique [symmetric])
  show 12: "- (pi / 2) < arctan x + arctan y" "arctan x + arctan y < pi / 2"
    using assms by linarith+
  show "tan (arctan x + arctan y) = (x + y) / (1 - x * y)"
    using cos_gt_zero_pi [OF 12]
    by (simp add: arctan tan_add)
qed

lemma arctan_inverse:
  assumes "0 < x"
    shows "arctan(inverse x) = pi/2 - arctan x"
proof -
  have "arctan(inverse x) = arctan(inverse(tan(arctan x)))"
    by (simp add: arctan)
  also have "... = arctan (tan (pi / 2 - arctan x))"
    by (simp add: tan_cot)
  also have "... = pi/2 - arctan x"
  proof -
    have "0 < pi - arctan x"
    using arctan_ubound [of x] pi_gt_zero by linarith
    with assms show ?thesis
      by (simp add: Transcendental.arctan_tan)
  qed
  finally show ?thesis .
qed

lemma arctan_add_small:
  assumes "\<bar>x * y\<bar> < 1"
    shows "(arctan x + arctan y = arctan((x + y) / (1 - x * y)))"
proof (cases "x = 0 \<or> y = 0")
  case False
  with assms have "\<bar>x\<bar> < inverse \<bar>y\<bar>"
    by (simp add: field_split_simps abs_mult)
  with False have "\<bar>arctan x\<bar> < pi / 2 - \<bar>arctan y\<bar>" using assms
    by (auto simp add: abs_arctan arctan_inverse [symmetric] arctan_less_iff)
  then show ?thesis
    by (intro arctan_add_raw) linarith
qed auto

lemma abs_arctan_le:
  fixes x::real shows "\<bar>arctan x\<bar> \<le> \<bar>x\<bar>"
proof -
  have 1: "\<And>x. x \<in> \<real> \<Longrightarrow> cmod (inverse (1 + x\<^sup>2)) \<le> 1"
    by (simp add: norm_divide divide_simps in_Reals_norm complex_is_Real_iff power2_eq_square)
  have "cmod (Arctan w - Arctan z) \<le> 1 * cmod (w-z)" if "w \<in> \<real>" "z \<in> \<real>" for w z
    apply (rule field_differentiable_bound [OF convex_Reals, of Arctan _ 1])
       apply (rule has_field_derivative_at_within [OF has_field_derivative_Arctan])
    using 1 that by (auto simp: Reals_def)
  then have "cmod (Arctan (of_real x) - Arctan 0) \<le> 1 * cmod (of_real x - 0)"
    using Reals_0 Reals_of_real by blast
  then show ?thesis
    by (simp add: Arctan_of_real)
qed

lemma arctan_le_self: "0 \<le> x \<Longrightarrow> arctan x \<le> x"
  by (metis abs_arctan_le abs_of_nonneg zero_le_arctan_iff)

lemma abs_tan_ge: "\<bar>x\<bar> < pi/2 \<Longrightarrow> \<bar>x\<bar> \<le> \<bar>tan x\<bar>"
  by (metis abs_arctan_le abs_less_iff arctan_tan minus_less_iff)

lemma arctan_bounds:
  assumes "0 \<le> x" "x < 1"
  shows arctan_lower_bound:
    "(\<Sum>k<2 * n. (- 1) ^ k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1))) \<le> arctan x"
    (is "(\<Sum>k<_. (- 1)^ k * ?a k) \<le> _")
    and arctan_upper_bound:
    "arctan x \<le> (\<Sum>k<2 * n + 1. (- 1) ^ k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1)))"
proof -
  have tendsto_zero: "?a \<longlonglongrightarrow> 0"
  proof (rule tendsto_eq_rhs)
    show "(\<lambda>k. 1 / real (k * 2 + 1) * x ^ (k * 2 + 1)) \<longlonglongrightarrow> 0 * 0"
      using assms
      by (intro tendsto_mult real_tendsto_divide_at_top)
        (auto simp: filterlim_real_sequentially filterlim_sequentially_iff_filterlim_real
          intro!: real_tendsto_divide_at_top tendsto_power_zero filterlim_real_sequentially
          tendsto_eq_intros filterlim_at_top_mult_tendsto_pos filterlim_tendsto_add_at_top)
  qed simp
  have nonneg: "0 \<le> ?a n" for n
    by (force intro!: divide_nonneg_nonneg mult_nonneg_nonneg zero_le_power assms)
  have le: "?a (Suc n) \<le> ?a n" for n
    by (rule mult_mono[OF _ power_decreasing]) (auto simp: field_split_simps assms less_imp_le)
  from summable_Leibniz'(4)[of ?a, OF tendsto_zero nonneg le, of n]
    summable_Leibniz'(2)[of ?a, OF tendsto_zero nonneg le, of n]
    assms
  show "(\<Sum>k<2*n. (- 1)^ k * ?a k) \<le> arctan x" "arctan x \<le> (\<Sum>k<2 * n + 1. (- 1)^ k * ?a k)"
    by (auto simp: arctan_series)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounds on pi using real arctangent\<close>

lemma pi_machin: "pi = 16 * arctan (1 / 5) - 4 * arctan (1 / 239)"
  using machin by simp

lemma pi_approx: "3.141592653588 \<le> pi" "pi \<le> 3.1415926535899"
  unfolding pi_machin
  using arctan_bounds[of "1/5"   4]
        arctan_bounds[of "1/239" 4]
  by (simp_all add: eval_nat_numeral)

lemma pi_gt3: "pi > 3"
  using pi_approx by simp


subsection\<open>Inverse Sine\<close>

definition\<^marker>\<open>tag important\<close> Arcsin :: "complex \<Rightarrow> complex" where
   "Arcsin \<equiv> \<lambda>z. -\<i> * Ln(\<i> * z + csqrt(1 - z\<^sup>2))"

lemma Arcsin_body_lemma: "\<i> * z + csqrt(1 - z\<^sup>2) \<noteq> 0"
  using power2_csqrt [of "1 - z\<^sup>2"]
  by (metis add.inverse_inverse complex_i_mult_minus diff_0 diff_add_cancel diff_minus_eq_add mult.assoc mult.commute numeral_One power2_eq_square zero_neq_numeral)

lemma Arcsin_range_lemma: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Re(\<i> * z + csqrt(1 - z\<^sup>2))"
  using Complex.cmod_power2 [of z, symmetric]
  by (simp add: real_less_rsqrt algebra_simps Re_power2 cmod_square_less_1_plus)

lemma Re_Arcsin: "Re(Arcsin z) = Im (Ln (\<i> * z + csqrt(1 - z\<^sup>2)))"
  by (simp add: Arcsin_def)

lemma Im_Arcsin: "Im(Arcsin z) = - ln (cmod (\<i> * z + csqrt (1 - z\<^sup>2)))"
  by (simp add: Arcsin_def Arcsin_body_lemma)

lemma one_minus_z2_notin_nonpos_Reals:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
  shows "1 - z\<^sup>2 \<notin> \<real>\<^sub>\<le>\<^sub>0"
proof (cases "Im z = 0")
  case True
  with assms show ?thesis
    by (simp add: complex_nonpos_Reals_iff flip: abs_square_less_1)
next
  case False
  have "\<not> (Im z)\<^sup>2 \<le> - 1"
    using False power2_less_eq_zero_iff by fastforce
  with False show ?thesis
    by (auto simp add: complex_nonpos_Reals_iff Re_power2 Im_power2)
qed

lemma isCont_Arcsin_lemma:
  assumes le0: "Re (\<i> * z + csqrt (1 - z\<^sup>2)) \<le> 0" and "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows False
proof (cases "Im z = 0")
  case True
  then show ?thesis
    using assms by (fastforce simp: cmod_def abs_square_less_1 [symmetric])
next
  case False
  have leim: "(cmod (1 - z\<^sup>2) + (1 - Re (z\<^sup>2))) / 2 \<le> (Im z)\<^sup>2"
    using le0 sqrt_le_D by fastforce
  have neq: "(cmod z)\<^sup>2 \<noteq> 1 + cmod (1 - z\<^sup>2)"
  proof (clarsimp simp add: cmod_def)
    assume "(Re z)\<^sup>2 + (Im z)\<^sup>2 = 1 + sqrt ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
    then have "((Re z)\<^sup>2 + (Im z)\<^sup>2 - 1)\<^sup>2 = ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
      by simp
    then show False using False
      by (simp add: power2_eq_square algebra_simps)
  qed
  moreover have 2: "(Im z)\<^sup>2 = (1 + ((Im z)\<^sup>2 + cmod (1 - z\<^sup>2)) - (Re z)\<^sup>2) / 2"
    using leim cmod_power2 [of z] norm_triangle_ineq2 [of "z^2" 1]
    by (simp add: norm_power Re_power2 norm_minus_commute [of 1])
  ultimately show False
    by (simp add: Re_power2 Im_power2 cmod_power2)
qed

lemma isCont_Arcsin:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "isCont Arcsin z"
proof -
  have 1: "\<i> * z + csqrt (1 - z\<^sup>2) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (metis isCont_Arcsin_lemma assms complex_nonpos_Reals_iff)
  have 2: "1 - z\<^sup>2 \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (simp add: one_minus_z2_notin_nonpos_Reals assms)
  show ?thesis
    using assms unfolding Arcsin_def by (intro isCont_Ln' isCont_csqrt' continuous_intros 1 2)
qed

lemma isCont_Arcsin' [simp]:
  shows "isCont f z \<Longrightarrow> (Im (f z) = 0 \<Longrightarrow> \<bar>Re (f z)\<bar> < 1) \<Longrightarrow> isCont (\<lambda>x. Arcsin (f x)) z"
  by (blast intro: isCont_o2 [OF _ isCont_Arcsin])

lemma sin_Arcsin [simp]: "sin(Arcsin z) = z"
proof -
  have "\<i>*z*2 + csqrt (1 - z\<^sup>2)*2 = 0 \<longleftrightarrow> (\<i>*z)*2 + csqrt (1 - z\<^sup>2)*2 = 0"
    by (simp add: algebra_simps)  \<comment> \<open>Cancelling a factor of 2\<close>
  moreover have "... \<longleftrightarrow> (\<i>*z) + csqrt (1 - z\<^sup>2) = 0"
    by (metis Arcsin_body_lemma distrib_right no_zero_divisors zero_neq_numeral)
  ultimately show ?thesis
    apply (simp add: sin_exp_eq Arcsin_def Arcsin_body_lemma exp_minus divide_simps)
    apply (simp add: algebra_simps)
    apply (simp add: power2_eq_square [symmetric] algebra_simps)
    done
qed

lemma Re_eq_pihalf_lemma:
    "\<bar>Re z\<bar> = pi/2 \<Longrightarrow> Im z = 0 \<Longrightarrow>
      Re ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2) = 0 \<and> 0 \<le> Im ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2)"
  apply (simp add: cos_i_times [symmetric] Re_cos Im_cos abs_if del: eq_divide_eq_numeral1)
  by (metis cos_minus cos_pi_half)

lemma Re_less_pihalf_lemma:
  assumes "\<bar>Re z\<bar> < pi / 2"
    shows "0 < Re ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2)"
proof -
  have "0 < cos (Re z)" using assms
    using cos_gt_zero_pi by auto
  then show ?thesis
    by (simp add: cos_i_times [symmetric] Re_cos Im_cos add_pos_pos)
qed

lemma Arcsin_sin:
    assumes "\<bar>Re z\<bar> < pi/2 \<or> (\<bar>Re z\<bar> = pi/2 \<and> Im z = 0)"
      shows "Arcsin(sin z) = z"
proof -
  have "Arcsin(sin z) = - (\<i> * Ln (csqrt (1 - (\<i> * (exp (\<i>*z) - inverse (exp (\<i>*z))))\<^sup>2 / 4) - (inverse (exp (\<i>*z)) - exp (\<i>*z)) / 2))"
    by (simp add: sin_exp_eq Arcsin_def exp_minus power_divide)
  also have "... = - (\<i> * Ln (csqrt (((exp (\<i>*z) + inverse (exp (\<i>*z)))/2)\<^sup>2) - (inverse (exp (\<i>*z)) - exp (\<i>*z)) / 2))"
    by (simp add: field_simps power2_eq_square)
  also have "... = - (\<i> * Ln (((exp (\<i>*z) + inverse (exp (\<i>*z)))/2) - (inverse (exp (\<i>*z)) - exp (\<i>*z)) / 2))"
    apply (subst csqrt_square)
    using assms Re_eq_pihalf_lemma Re_less_pihalf_lemma by auto
  also have "... =  - (\<i> * Ln (exp (\<i>*z)))"
    by (simp add: field_simps power2_eq_square)
  also have "... = z"
    using assms by (auto simp: abs_if simp del: eq_divide_eq_numeral1 split: if_split_asm)
  finally show ?thesis .
qed

lemma Arcsin_unique:
    "\<lbrakk>sin z = w; \<bar>Re z\<bar> < pi/2 \<or> (\<bar>Re z\<bar> = pi/2 \<and> Im z = 0)\<rbrakk> \<Longrightarrow> Arcsin w = z"
  by (metis Arcsin_sin)

lemma Arcsin_0 [simp]: "Arcsin 0 = 0"
  by (metis Arcsin_sin norm_zero pi_half_gt_zero real_norm_def sin_zero zero_complex.simps(1))

lemma Arcsin_1 [simp]: "Arcsin 1 = pi/2"
  by (metis Arcsin_sin Im_complex_of_real Re_complex_of_real numeral_One of_real_numeral pi_half_ge_zero real_sqrt_abs real_sqrt_pow2 real_sqrt_power sin_of_real sin_pi_half)

lemma Arcsin_minus_1 [simp]: "Arcsin(-1) = - (pi/2)"
  by (metis Arcsin_1 Arcsin_sin Im_complex_of_real Re_complex_of_real abs_of_nonneg of_real_minus pi_half_ge_zero power2_minus real_sqrt_abs sin_Arcsin sin_minus)

lemma has_field_derivative_Arcsin:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
    shows "(Arcsin has_field_derivative inverse(cos(Arcsin z))) (at z)"
proof -
  have "(sin (Arcsin z))\<^sup>2 \<noteq> 1"
    using assms one_minus_z2_notin_nonpos_Reals by force
  then have "cos (Arcsin z) \<noteq> 0"
    by (metis diff_0_right power_zero_numeral sin_squared_eq)
  then show ?thesis
    by (rule has_field_derivative_inverse_basic [OF DERIV_sin _ _ open_ball [of z 1]]) (auto intro: isCont_Arcsin assms)
qed

declare has_field_derivative_Arcsin [derivative_intros]
declare has_field_derivative_Arcsin [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin field_differentiable at z"
  using field_differentiable_def has_field_derivative_Arcsin by blast

lemma field_differentiable_within_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin field_differentiable (at z within s)"
  using field_differentiable_at_Arcsin field_differentiable_within_subset by blast

lemma continuous_within_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arcsin"
  using continuous_at_imp_continuous_within isCont_Arcsin by blast

lemma continuous_on_Arcsin [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous_on s Arcsin"
  by (simp add: continuous_at_imp_continuous_on)

lemma holomorphic_on_Arcsin: "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin holomorphic_on s"
  by (simp add: field_differentiable_within_Arcsin holomorphic_on_def)


subsection\<open>Inverse Cosine\<close>

definition\<^marker>\<open>tag important\<close> Arccos :: "complex \<Rightarrow> complex" where
   "Arccos \<equiv> \<lambda>z. -\<i> * Ln(z + \<i> * csqrt(1 - z\<^sup>2))"

lemma Arccos_range_lemma: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Im(z + \<i> * csqrt(1 - z\<^sup>2))"
  using Arcsin_range_lemma [of "-z"]  by simp

lemma Arccos_body_lemma: "z + \<i> * csqrt(1 - z\<^sup>2) \<noteq> 0"
  using Arcsin_body_lemma [of z]
  by (metis Arcsin_body_lemma complex_i_mult_minus diff_minus_eq_add power2_minus right_minus_eq)

lemma Re_Arccos: "Re(Arccos z) = Im (Ln (z + \<i> * csqrt(1 - z\<^sup>2)))"
  by (simp add: Arccos_def)

lemma Im_Arccos: "Im(Arccos z) = - ln (cmod (z + \<i> * csqrt (1 - z\<^sup>2)))"
  by (simp add: Arccos_def Arccos_body_lemma)

text\<open>A very tricky argument to find!\<close>
lemma isCont_Arccos_lemma:
  assumes eq0: "Im (z + \<i> * csqrt (1 - z\<^sup>2)) = 0" and "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows False
proof (cases "Im z = 0")
  case True
  then show ?thesis
    using assms by (fastforce simp add: cmod_def abs_square_less_1 [symmetric])
next
  case False
  have Imz: "Im z = - sqrt ((1 + ((Im z)\<^sup>2 + cmod (1 - z\<^sup>2)) - (Re z)\<^sup>2) / 2)"
    using eq0 abs_Re_le_cmod [of "1-z\<^sup>2"]
    by (simp add: Re_power2 algebra_simps)
  have "(cmod z)\<^sup>2 - 1 \<noteq> cmod (1 - z\<^sup>2)"
  proof (clarsimp simp add: cmod_def)
    assume "(Re z)\<^sup>2 + (Im z)\<^sup>2 - 1 = sqrt ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
    then have "((Re z)\<^sup>2 + (Im z)\<^sup>2 - 1)\<^sup>2 = ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
      by simp
    then show False using False
      by (simp add: power2_eq_square algebra_simps)
  qed
  moreover have "(Im z)\<^sup>2 = (1 + ((Im z)\<^sup>2 + cmod (1 - z\<^sup>2)) - (Re z)\<^sup>2) / 2"
    using abs_Re_le_cmod [of "1-z\<^sup>2"] by (subst Imz) (simp add: Re_power2)
  ultimately show False
    by (simp add: cmod_power2)
qed

lemma isCont_Arccos:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "isCont Arccos z"
proof -
  have "z + \<i> * csqrt (1 - z\<^sup>2) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (metis complex_nonpos_Reals_iff isCont_Arccos_lemma assms)
  with assms show ?thesis
    unfolding Arccos_def
    by (simp_all add: one_minus_z2_notin_nonpos_Reals assms)
qed

lemma isCont_Arccos' [simp]:
  "isCont f z \<Longrightarrow> (Im (f z) = 0 \<Longrightarrow> \<bar>Re (f z)\<bar> < 1) \<Longrightarrow> isCont (\<lambda>x. Arccos (f x)) z"
  by (blast intro: isCont_o2 [OF _ isCont_Arccos])

lemma cos_Arccos [simp]: "cos(Arccos z) = z"
proof -
  have "z*2 + \<i> * (2 * csqrt (1 - z\<^sup>2)) = 0 \<longleftrightarrow> z*2 + \<i> * csqrt (1 - z\<^sup>2)*2 = 0"
    by (simp add: algebra_simps)  \<comment> \<open>Cancelling a factor of 2\<close>
  moreover have "... \<longleftrightarrow> z + \<i> * csqrt (1 - z\<^sup>2) = 0"
    by (metis distrib_right mult_eq_0_iff zero_neq_numeral)
  ultimately show ?thesis
    by (simp add: cos_exp_eq Arccos_def Arccos_body_lemma exp_minus field_simps flip: power2_eq_square)
qed

lemma Arccos_cos:
    assumes "0 < Re z \<and> Re z < pi \<or>
             Re z = 0 \<and> 0 \<le> Im z \<or>
             Re z = pi \<and> Im z \<le> 0"
      shows "Arccos(cos z) = z"
proof -
  have *: "((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z))) = sin z"
    by (simp add: sin_exp_eq exp_minus field_simps power2_eq_square)
  have "1 - (exp (\<i> * z) + inverse (exp (\<i> * z)))\<^sup>2 / 4 = ((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z)))\<^sup>2"
    by (simp add: field_simps power2_eq_square)
  then have "Arccos(cos z) = - (\<i> * Ln ((exp (\<i> * z) + inverse (exp (\<i> * z))) / 2 +
                           \<i> * csqrt (((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z)))\<^sup>2)))"
    by (simp add: cos_exp_eq Arccos_def exp_minus power_divide)
  also have "... = - (\<i> * Ln ((exp (\<i> * z) + inverse (exp (\<i> * z))) / 2 +
                              \<i> * ((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z)))))"
    apply (subst csqrt_square)
    using assms Re_sin_pos [of z] Im_sin_nonneg [of z] Im_sin_nonneg2 [of z]
    by (auto simp: * Re_sin Im_sin)
  also have "... =  - (\<i> * Ln (exp (\<i>*z)))"
    by (simp add: field_simps power2_eq_square)
  also have "... = z"
    using assms
    by (subst Complex_Transcendental.Ln_exp, auto)
  finally show ?thesis .
qed

lemma Arccos_unique:
    "\<lbrakk>cos z = w;
      0 < Re z \<and> Re z < pi \<or>
      Re z = 0 \<and> 0 \<le> Im z \<or>
      Re z = pi \<and> Im z \<le> 0\<rbrakk> \<Longrightarrow> Arccos w = z"
  using Arccos_cos by blast

lemma Arccos_0 [simp]: "Arccos 0 = pi/2"
  by (rule Arccos_unique) auto

lemma Arccos_1 [simp]: "Arccos 1 = 0"
  by (rule Arccos_unique) auto

lemma Arccos_minus1: "Arccos(-1) = pi"
  by (rule Arccos_unique) auto

lemma has_field_derivative_Arccos:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "(Arccos has_field_derivative - inverse(sin(Arccos z))) (at z)"
proof -
  have "x\<^sup>2 \<noteq> -1" for x::real
    by (sos "((R<1 + (([~1] * A=0) + (R<1 * (R<1 * [x__]^2)))))")
  with assms have "(cos (Arccos z))\<^sup>2 \<noteq> 1"
    by (auto simp: complex_eq_iff Re_power2 Im_power2 abs_square_eq_1)
  then have "- sin (Arccos z) \<noteq> 0"
    by (metis cos_squared_eq diff_0_right mult_zero_left neg_0_equal_iff_equal power2_eq_square)
  then have "(Arccos has_field_derivative inverse(- sin(Arccos z))) (at z)"
    by (rule has_field_derivative_inverse_basic [OF DERIV_cos _ _ open_ball [of z 1]])
       (auto intro: isCont_Arccos assms)
  then show ?thesis
    by simp
qed

declare has_field_derivative_Arcsin [derivative_intros]
declare has_field_derivative_Arcsin [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos field_differentiable at z"
  using field_differentiable_def has_field_derivative_Arccos by blast

lemma field_differentiable_within_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos field_differentiable (at z within s)"
  using field_differentiable_at_Arccos field_differentiable_within_subset by blast

lemma continuous_within_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arccos"
  using continuous_at_imp_continuous_within isCont_Arccos by blast

lemma continuous_on_Arccos [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous_on s Arccos"
  by (simp add: continuous_at_imp_continuous_on)

lemma holomorphic_on_Arccos: "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos holomorphic_on s"
  by (simp add: field_differentiable_within_Arccos holomorphic_on_def)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Upper and Lower Bounds for Inverse Sine and Cosine\<close>

lemma Arcsin_bounds: "\<bar>Re z\<bar> < 1 \<Longrightarrow> \<bar>Re(Arcsin z)\<bar> < pi/2"
  unfolding Re_Arcsin
  by (blast intro: Re_Ln_pos_lt_imp Arcsin_range_lemma)

lemma Arccos_bounds: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Re(Arccos z) \<and> Re(Arccos z) < pi"
  unfolding Re_Arccos
  by (blast intro!: Im_Ln_pos_lt_imp Arccos_range_lemma)

lemma Re_Arccos_bounds: "-pi < Re(Arccos z) \<and> Re(Arccos z) \<le> pi"
  unfolding Re_Arccos
  by (blast intro!: mpi_less_Im_Ln Im_Ln_le_pi Arccos_body_lemma)

lemma Re_Arccos_bound: "\<bar>Re(Arccos z)\<bar> \<le> pi"
  by (meson Re_Arccos_bounds abs_le_iff less_eq_real_def minus_less_iff)

lemma Im_Arccos_bound: "\<bar>Im (Arccos w)\<bar> \<le> cmod w"
proof -
  have "(Im (Arccos w))\<^sup>2 \<le> (cmod (cos (Arccos w)))\<^sup>2 - (cos (Re (Arccos w)))\<^sup>2"
    using norm_cos_squared [of "Arccos w"] real_le_abs_sinh [of "Im (Arccos w)"]
    by (simp only: abs_le_square_iff) (simp add: field_split_simps)
  also have "... \<le> (cmod w)\<^sup>2"
    by (auto simp: cmod_power2)
  finally show ?thesis
    using abs_le_square_iff by force
qed

lemma Re_Arcsin_bounds: "-pi < Re(Arcsin z) & Re(Arcsin z) \<le> pi"
  unfolding Re_Arcsin
  by (blast intro!: mpi_less_Im_Ln Im_Ln_le_pi Arcsin_body_lemma)

lemma Re_Arcsin_bound: "\<bar>Re(Arcsin z)\<bar> \<le> pi"
  by (meson Re_Arcsin_bounds abs_le_iff less_eq_real_def minus_less_iff)

lemma norm_Arccos_bounded:
  fixes w :: complex
  shows "norm (Arccos w) \<le> pi + norm w"
proof -
  have Re: "(Re (Arccos w))\<^sup>2 \<le> pi\<^sup>2" "(Im (Arccos w))\<^sup>2 \<le> (cmod w)\<^sup>2"
    using Re_Arccos_bound [of w] Im_Arccos_bound [of w] abs_le_square_iff by force+
  have "Arccos w \<bullet> Arccos w \<le> pi\<^sup>2 + (cmod w)\<^sup>2"
    using Re by (simp add: dot_square_norm cmod_power2 [of "Arccos w"])
  then have "cmod (Arccos w) \<le> pi + cmod (cos (Arccos w))"
    apply (simp add: norm_le_square)
    by (metis dot_square_norm norm_ge_zero norm_le_square pi_ge_zero triangle_lemma)
  then show "cmod (Arccos w) \<le> pi + cmod w"
    by auto
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Interrelations between Arcsin and Arccos\<close>

lemma cos_Arcsin_nonzero:
  assumes "z\<^sup>2 \<noteq> 1" shows "cos(Arcsin z) \<noteq> 0"
proof -
  have eq: "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = z\<^sup>2 * (z\<^sup>2 - 1)"
    by (simp add: algebra_simps)
  have "\<i> * z * (csqrt (1 - z\<^sup>2)) \<noteq> z\<^sup>2 - 1"
  proof
    assume "\<i> * z * (csqrt (1 - z\<^sup>2)) = z\<^sup>2 - 1"
    then have "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = (z\<^sup>2 - 1)\<^sup>2"
      by simp
    then have "z\<^sup>2 * (z\<^sup>2 - 1) = (z\<^sup>2 - 1)*(z\<^sup>2 - 1)"
      using eq power2_eq_square by auto
    then show False
      using assms by simp
  qed
  then have "1 + \<i> * z * (csqrt (1 - z * z)) \<noteq> z\<^sup>2"
    by (metis add_minus_cancel power2_eq_square uminus_add_conv_diff)
  then have "2*(1 + \<i> * z * (csqrt (1 - z * z))) \<noteq> 2*z\<^sup>2"  (*FIXME cancel_numeral_factor*)
    by (metis mult_cancel_left zero_neq_numeral)
  then have "(\<i> * z + csqrt (1 - z\<^sup>2))\<^sup>2 \<noteq> -1"
    using assms
    apply (simp add: power2_sum)
    apply (simp add: power2_eq_square algebra_simps)
    done
  then show ?thesis
    apply (simp add: cos_exp_eq Arcsin_def exp_minus)
    apply (simp add: divide_simps Arcsin_body_lemma)
    apply (metis add.commute minus_unique power2_eq_square)
    done
qed

lemma sin_Arccos_nonzero:
  assumes "z\<^sup>2 \<noteq> 1" shows "sin(Arccos z) \<noteq> 0"
proof -
  have eq: "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = -(z\<^sup>2) * (1 - z\<^sup>2)"
    by (simp add: algebra_simps)
  have "\<i> * z * (csqrt (1 - z\<^sup>2)) \<noteq> 1 - z\<^sup>2"
  proof
    assume "\<i> * z * (csqrt (1 - z\<^sup>2)) = 1 - z\<^sup>2"
    then have "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = (1 - z\<^sup>2)\<^sup>2"
      by simp
    then have "-(z\<^sup>2) * (1 - z\<^sup>2) = (1 - z\<^sup>2)*(1 - z\<^sup>2)"
      using eq power2_eq_square by auto
    then have "-(z\<^sup>2) = (1 - z\<^sup>2)"
      using assms
      by (metis add.commute add.right_neutral diff_add_cancel mult_right_cancel)
    then show False
      using assms by simp
  qed
  then have "z\<^sup>2 + \<i> * z * (csqrt (1 - z\<^sup>2)) \<noteq> 1"
    by (simp add: algebra_simps)
  then have "2*(z\<^sup>2 + \<i> * z * (csqrt (1 - z\<^sup>2))) \<noteq> 2*1"
    by (metis mult_cancel_left2 zero_neq_numeral)  (*FIXME cancel_numeral_factor*)
  then have "(z + \<i> * csqrt (1 - z\<^sup>2))\<^sup>2 \<noteq> 1"
    using assms
    by (metis Arccos_def add.commute add.left_neutral cancel_comm_monoid_add_class.diff_cancel cos_Arccos csqrt_0 mult_zero_right)
  then show ?thesis
    apply (simp add: sin_exp_eq Arccos_def exp_minus)
    apply (simp add: divide_simps Arccos_body_lemma)
    apply (simp add: power2_eq_square)
    done
qed

lemma cos_sin_csqrt:
  assumes "0 < cos(Re z)  \<or>  cos(Re z) = 0 \<and> Im z * sin(Re z) \<le> 0"
    shows "cos z = csqrt(1 - (sin z)\<^sup>2)"
proof (rule csqrt_unique [THEN sym])
  show "(cos z)\<^sup>2 = 1 - (sin z)\<^sup>2"
    by (simp add: cos_squared_eq)
qed (use assms in \<open>auto simp: Re_cos Im_cos add_pos_pos mult_le_0_iff zero_le_mult_iff\<close>)

lemma sin_cos_csqrt:
  assumes "0 < sin(Re z)  \<or>  sin(Re z) = 0 \<and> 0 \<le> Im z * cos(Re z)"
    shows "sin z = csqrt(1 - (cos z)\<^sup>2)"
proof (rule csqrt_unique [THEN sym])
  show "(sin z)\<^sup>2 = 1 - (cos z)\<^sup>2"
    by (simp add: sin_squared_eq)
qed (use assms in \<open>auto simp: Re_sin Im_sin add_pos_pos mult_le_0_iff zero_le_mult_iff\<close>)

lemma Arcsin_Arccos_csqrt_pos:
    "(0 < Re z | Re z = 0 & 0 \<le> Im z) \<Longrightarrow> Arcsin z = Arccos(csqrt(1 - z\<^sup>2))"
  by (simp add: Arcsin_def Arccos_def Complex.csqrt_square add.commute)

lemma Arccos_Arcsin_csqrt_pos:
    "(0 < Re z | Re z = 0 & 0 \<le> Im z) \<Longrightarrow> Arccos z = Arcsin(csqrt(1 - z\<^sup>2))"
  by (simp add: Arcsin_def Arccos_def Complex.csqrt_square add.commute)

lemma sin_Arccos:
    "0 < Re z | Re z = 0 & 0 \<le> Im z \<Longrightarrow> sin(Arccos z) = csqrt(1 - z\<^sup>2)"
  by (simp add: Arccos_Arcsin_csqrt_pos)

lemma cos_Arcsin:
    "0 < Re z | Re z = 0 & 0 \<le> Im z \<Longrightarrow> cos(Arcsin z) = csqrt(1 - z\<^sup>2)"
  by (simp add: Arcsin_Arccos_csqrt_pos)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relationship with Arcsin on the Real Numbers\<close>

lemma Im_Arcsin_of_real:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "Im (Arcsin (of_real x)) = 0"
proof -
  have "csqrt (1 - (of_real x)\<^sup>2) = (if x^2 \<le> 1 then sqrt (1 - x^2) else \<i> * sqrt (x^2 - 1))"
    by (simp add: of_real_sqrt del: csqrt_of_real_nonneg)
  then have "cmod (\<i> * of_real x + csqrt (1 - (of_real x)\<^sup>2))^2 = 1"
    using assms abs_square_le_1
    by (force simp add: Complex.cmod_power2)
  then have "cmod (\<i> * of_real x + csqrt (1 - (of_real x)\<^sup>2)) = 1"
    by (simp add: norm_complex_def)
  then show ?thesis
    by (simp add: Im_Arcsin exp_minus)
qed

corollary\<^marker>\<open>tag unimportant\<close> Arcsin_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> \<bar>Re z\<bar> \<le> 1 \<Longrightarrow> Arcsin z \<in> \<real>"
  by (metis Im_Arcsin_of_real Re_complex_of_real Reals_cases complex_is_Real_iff)

lemma arcsin_eq_Re_Arcsin:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "arcsin x = Re (Arcsin (of_real x))"
unfolding arcsin_def
proof (rule the_equality, safe)
  show "- (pi / 2) \<le> Re (Arcsin (complex_of_real x))"
    using Re_Ln_pos_le [OF Arcsin_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arcsin)
next
  show "Re (Arcsin (complex_of_real x)) \<le> pi / 2"
    using Re_Ln_pos_le [OF Arcsin_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arcsin)
next
  show "sin (Re (Arcsin (complex_of_real x))) = x"
    using Re_sin [of "Arcsin (of_real x)"] Arcsin_body_lemma [of "of_real x"]
    by (simp add: Im_Arcsin_of_real assms)
next
  fix x'
  assume "- (pi / 2) \<le> x'" "x' \<le> pi / 2" "x = sin x'"
  then show "x' = Re (Arcsin (complex_of_real (sin x')))"
    unfolding sin_of_real [symmetric] 
    by (subst Arcsin_sin) auto
qed

lemma of_real_arcsin: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> of_real(arcsin x) = Arcsin(of_real x)"
  by (metis Im_Arcsin_of_real add.right_neutral arcsin_eq_Re_Arcsin complex_eq mult_zero_right of_real_0)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relationship with Arccos on the Real Numbers\<close>

lemma Im_Arccos_of_real:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "Im (Arccos (of_real x)) = 0"
proof -
  have "csqrt (1 - (of_real x)\<^sup>2) = (if x^2 \<le> 1 then sqrt (1 - x^2) else \<i> * sqrt (x^2 - 1))"
    by (simp add: of_real_sqrt del: csqrt_of_real_nonneg)
  then have "cmod (of_real x + \<i> * csqrt (1 - (of_real x)\<^sup>2))^2 = 1"
    using assms abs_square_le_1
    by (force simp add: Complex.cmod_power2)
  then have "cmod (of_real x + \<i> * csqrt (1 - (of_real x)\<^sup>2)) = 1"
    by (simp add: norm_complex_def)
  then show ?thesis
    by (simp add: Im_Arccos exp_minus)
qed

corollary\<^marker>\<open>tag unimportant\<close> Arccos_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> \<bar>Re z\<bar> \<le> 1 \<Longrightarrow> Arccos z \<in> \<real>"
  by (metis Im_Arccos_of_real Re_complex_of_real Reals_cases complex_is_Real_iff)

lemma arccos_eq_Re_Arccos:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "arccos x = Re (Arccos (of_real x))"
unfolding arccos_def
proof (rule the_equality, safe)
  show "0 \<le> Re (Arccos (complex_of_real x))"
    using Im_Ln_pos_le [OF Arccos_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arccos)
next
  show "Re (Arccos (complex_of_real x)) \<le> pi"
    using Im_Ln_pos_le [OF Arccos_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arccos)
next
  show "cos (Re (Arccos (complex_of_real x))) = x"
    using Re_cos [of "Arccos (of_real x)"] Arccos_body_lemma [of "of_real x"]
    by (simp add: Im_Arccos_of_real assms)
next
  fix x'
  assume "0 \<le> x'" "x' \<le> pi" "x = cos x'"
  then show "x' = Re (Arccos (complex_of_real (cos x')))"
    unfolding cos_of_real [symmetric]
    by (subst Arccos_cos) auto
qed

lemma of_real_arccos: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> of_real(arccos x) = Arccos(of_real x)"
  by (metis Im_Arccos_of_real add.right_neutral arccos_eq_Re_Arccos complex_eq mult_zero_right of_real_0)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Some interrelationships among the real inverse trig functions\<close>

lemma arccos_arctan:
  assumes "-1 < x" "x < 1"
    shows "arccos x = pi/2 - arctan(x / sqrt(1 - x\<^sup>2))"
proof -
  have "arctan(x / sqrt(1 - x\<^sup>2)) - (pi/2 - arccos x) = 0"
  proof (rule sin_eq_0_pi)
    show "- pi < arctan (x / sqrt (1 - x\<^sup>2)) - (pi / 2 - arccos x)"
      using arctan_lbound [of "x / sqrt(1 - x\<^sup>2)"]  arccos_bounded [of x] assms
      by (simp add: algebra_simps)
  next
    show "arctan (x / sqrt (1 - x\<^sup>2)) - (pi / 2 - arccos x) < pi"
      using arctan_ubound [of "x / sqrt(1 - x\<^sup>2)"]  arccos_bounded [of x] assms
      by (simp add: algebra_simps)
  next
    show "sin (arctan (x / sqrt (1 - x\<^sup>2)) - (pi / 2 - arccos x)) = 0"
      using assms
      by (simp add: algebra_simps sin_diff cos_add sin_arccos sin_arctan cos_arctan
                    power2_eq_square square_eq_1_iff)
  qed
  then show ?thesis
    by simp
qed

lemma arcsin_plus_arccos:
  assumes "-1 \<le> x" "x \<le> 1"
    shows "arcsin x + arccos x = pi/2"
proof -
  have "arcsin x = pi/2 - arccos x"
    apply (rule sin_inj_pi)
    using assms arcsin [OF assms] arccos [OF assms]
    by (auto simp: algebra_simps sin_diff)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma arcsin_arccos_eq: "-1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arcsin x = pi/2 - arccos x"
  using arcsin_plus_arccos by force

lemma arccos_arcsin_eq: "-1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arccos x = pi/2 - arcsin x"
  using arcsin_plus_arccos by force

lemma arcsin_arctan: "-1 < x \<Longrightarrow> x < 1 \<Longrightarrow> arcsin x = arctan(x / sqrt(1 - x\<^sup>2))"
  by (simp add: arccos_arctan arcsin_arccos_eq)

lemma csqrt_1_diff_eq: "csqrt (1 - (of_real x)\<^sup>2) = (if x^2 \<le> 1 then sqrt (1 - x^2) else \<i> * sqrt (x^2 - 1))"
  by ( simp add: of_real_sqrt del: csqrt_of_real_nonneg)

lemma arcsin_arccos_sqrt_pos: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arcsin x = arccos(sqrt(1 - x\<^sup>2))"
  apply (simp add: abs_square_le_1 arcsin_eq_Re_Arcsin arccos_eq_Re_Arccos)
  apply (subst Arcsin_Arccos_csqrt_pos)
  apply (auto simp: power_le_one csqrt_1_diff_eq)
  done

lemma arcsin_arccos_sqrt_neg: "-1 \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> arcsin x = -arccos(sqrt(1 - x\<^sup>2))"
  using arcsin_arccos_sqrt_pos [of "-x"]
  by (simp add: arcsin_minus)

lemma arccos_arcsin_sqrt_pos: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arccos x = arcsin(sqrt(1 - x\<^sup>2))"
  apply (simp add: abs_square_le_1 arcsin_eq_Re_Arcsin arccos_eq_Re_Arccos)
  apply (subst Arccos_Arcsin_csqrt_pos)
  apply (auto simp: power_le_one csqrt_1_diff_eq)
  done

lemma arccos_arcsin_sqrt_neg: "-1 \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> arccos x = pi - arcsin(sqrt(1 - x\<^sup>2))"
  using arccos_arcsin_sqrt_pos [of "-x"]
  by (simp add: arccos_minus)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Continuity results for arcsin and arccos\<close>

lemma continuous_on_Arcsin_real [continuous_intros]:
    "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} Arcsin"
proof -
  have "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (arcsin (Re x))) =
        continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (Re (Arcsin (of_real (Re x)))))"
    by (rule continuous_on_cong [OF refl]) (simp add: arcsin_eq_Re_Arcsin)
  also have "... = ?thesis"
    by (rule continuous_on_cong [OF refl]) simp
  finally show ?thesis
    using continuous_on_arcsin [OF continuous_on_Re [OF continuous_on_id], of "{w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}"]
          continuous_on_of_real
    by fastforce
qed

lemma continuous_within_Arcsin_real:
    "continuous (at z within {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}) Arcsin"
proof (cases "z \<in> {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}")
  case True then show ?thesis
    using continuous_on_Arcsin_real continuous_on_eq_continuous_within
    by blast
next
  case False
  with closed_real_abs_le [of 1] show ?thesis
    by (rule continuous_within_closed_nontrivial)
qed

lemma continuous_on_Arccos_real:
    "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} Arccos"
proof -
  have "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (arccos (Re x))) =
        continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (Re (Arccos (of_real (Re x)))))"
    by (rule continuous_on_cong [OF refl]) (simp add: arccos_eq_Re_Arccos)
  also have "... = ?thesis"
    by (rule continuous_on_cong [OF refl]) simp
  finally show ?thesis
    using continuous_on_arccos [OF continuous_on_Re [OF continuous_on_id], of "{w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}"]
          continuous_on_of_real
    by fastforce
qed

lemma continuous_within_Arccos_real:
    "continuous (at z within {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}) Arccos"
proof (cases "z \<in> {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}")
  case True then show ?thesis
    using continuous_on_Arccos_real continuous_on_eq_continuous_within
    by blast
next
  case False
  with closed_real_abs_le [of 1] show ?thesis
    by (rule continuous_within_closed_nontrivial)
qed

lemma sinh_ln_complex: "x \<noteq> 0 \<Longrightarrow> sinh (ln x :: complex) = (x - inverse x) / 2"
  by (simp add: sinh_def exp_minus scaleR_conv_of_real exp_of_real)

lemma cosh_ln_complex: "x \<noteq> 0 \<Longrightarrow> cosh (ln x :: complex) = (x + inverse x) / 2"
  by (simp add: cosh_def exp_minus scaleR_conv_of_real)

lemma tanh_ln_complex: "x \<noteq> 0 \<Longrightarrow> tanh (ln x :: complex) = (x ^ 2 - 1) / (x ^ 2 + 1)"
  by (simp add: tanh_def sinh_ln_complex cosh_ln_complex divide_simps power2_eq_square)


subsection\<open>Roots of unity\<close>

theorem complex_root_unity:
  fixes j::nat
  assumes "n \<noteq> 0"
    shows "exp(2 * of_real pi * \<i> * of_nat j / of_nat n)^n = 1"
proof -
  have *: "of_nat j * (complex_of_real pi * 2) = complex_of_real (2 * real j * pi)"
    by (simp)
  then show ?thesis
    apply (simp add: exp_of_nat_mult [symmetric] mult_ac exp_Euler)
    apply (simp only: * cos_of_real sin_of_real)
    apply simp
    done
qed

lemma complex_root_unity_eq:
  fixes j::nat and k::nat
  assumes "1 \<le> n"
    shows "(exp(2 * of_real pi * \<i> * of_nat j / of_nat n) = exp(2 * of_real pi * \<i> * of_nat k / of_nat n)
           \<longleftrightarrow> j mod n = k mod n)"
proof -
    have "(\<exists>z::int. \<i> * (of_nat j * (of_real pi * 2)) =
               \<i> * (of_nat k * (of_real pi * 2)) + \<i> * (of_int z * (of_nat n * (of_real pi * 2)))) \<longleftrightarrow>
          (\<exists>z::int. of_nat j * (\<i> * (of_real pi * 2)) =
              (of_nat k + of_nat n * of_int z) * (\<i> * (of_real pi * 2)))"
      by (simp add: algebra_simps)
    also have "... \<longleftrightarrow> (\<exists>z::int. of_nat j = of_nat k + of_nat n * (of_int z :: complex))"
      by simp
    also have "... \<longleftrightarrow> (\<exists>z::int. of_nat j = of_nat k + of_nat n * z)"
      by (metis (mono_tags, hide_lams) of_int_add of_int_eq_iff of_int_mult of_int_of_nat_eq)
    also have "... \<longleftrightarrow> int j mod int n = int k mod int n"
      by (auto simp: mod_eq_dvd_iff dvd_def algebra_simps)
    also have "... \<longleftrightarrow> j mod n = k mod n"
      by (metis of_nat_eq_iff zmod_int)
    finally have "(\<exists>z. \<i> * (of_nat j * (of_real pi * 2)) =
             \<i> * (of_nat k * (of_real pi * 2)) + \<i> * (of_int z * (of_nat n * (of_real pi * 2)))) \<longleftrightarrow> j mod n = k mod n" .
   note * = this
  show ?thesis
    using assms
    by (simp add: exp_eq field_split_simps *)
qed

corollary bij_betw_roots_unity:
    "bij_betw (\<lambda>j. exp(2 * of_real pi * \<i> * of_nat j / of_nat n))
              {..<n}  {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j. j < n}"
  by (auto simp: bij_betw_def inj_on_def complex_root_unity_eq)

lemma complex_root_unity_eq_1:
  fixes j::nat and k::nat
  assumes "1 \<le> n"
    shows "exp(2 * of_real pi * \<i> * of_nat j / of_nat n) = 1 \<longleftrightarrow> n dvd j"
proof -
  have "1 = exp(2 * of_real pi * \<i> * (of_nat n / of_nat n))"
    using assms by simp
  then have "exp(2 * of_real pi * \<i> * (of_nat j / of_nat n)) = 1 \<longleftrightarrow> j mod n = n mod n"
     using complex_root_unity_eq [of n j n] assms
     by simp
  then show ?thesis
    by auto
qed

lemma finite_complex_roots_unity_explicit:
     "finite {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n}"
by simp

lemma card_complex_roots_unity_explicit:
     "card {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n} = n"
  by (simp add:  Finite_Set.bij_betw_same_card [OF bij_betw_roots_unity, symmetric])

lemma complex_roots_unity:
  assumes "1 \<le> n"
    shows "{z::complex. z^n = 1} = {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j. j < n}"
  apply (rule Finite_Set.card_seteq [symmetric])
  using assms
  apply (auto simp: card_complex_roots_unity_explicit finite_roots_unity complex_root_unity card_roots_unity)
  done

lemma card_complex_roots_unity: "1 \<le> n \<Longrightarrow> card {z::complex. z^n = 1} = n"
  by (simp add: card_complex_roots_unity_explicit complex_roots_unity)

lemma complex_not_root_unity:
    "1 \<le> n \<Longrightarrow> \<exists>u::complex. norm u = 1 \<and> u^n \<noteq> 1"
  apply (rule_tac x="exp (of_real pi * \<i> * of_real (1 / n))" in exI)
  apply (auto simp: Re_complex_div_eq_0 exp_of_nat_mult [symmetric] mult_ac exp_Euler)
  done

end
