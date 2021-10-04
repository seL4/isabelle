(*
   File:     HOL/Analysis/Ball_Volume.thy
   Author:   Manuel Eberl, TU München
*)

section \<open>The Volume of an \<open>n\<close>-Dimensional Ball\<close>

theory Ball_Volume
  imports Gamma_Function Lebesgue_Integral_Substitution
begin

text \<open>
  We define the volume of the unit ball in terms of the Gamma function. Note that the
  dimension need not be an integer; we also allow fractional dimensions, although we do
  not use this case or prove anything about it for now.
\<close>
definition\<^marker>\<open>tag important\<close> unit_ball_vol :: "real \<Rightarrow> real" where
  "unit_ball_vol n = pi powr (n / 2) / Gamma (n / 2 + 1)"

lemma unit_ball_vol_pos [simp]: "n \<ge> 0 \<Longrightarrow> unit_ball_vol n > 0"
  by (force simp: unit_ball_vol_def intro: divide_nonneg_pos)

lemma unit_ball_vol_nonneg [simp]: "n \<ge> 0 \<Longrightarrow> unit_ball_vol n \<ge> 0"
  by (simp add: dual_order.strict_implies_order)

text \<open>
  We first need the value of the following integral, which is at the core of
  computing the measure of an \<open>n + 1\<close>-dimensional ball in terms of the measure of an
  \<open>n\<close>-dimensional one.
\<close>
lemma emeasure_cball_aux_integral:
  "(\<integral>\<^sup>+x. indicator {-1..1} x * sqrt (1 - x\<^sup>2) ^ n \<partial>lborel) =
      ennreal (Beta (1 / 2) (real n / 2 + 1))"
proof -
  have "((\<lambda>t. t powr (-1 / 2) * (1 - t) powr (real n / 2)) has_integral
          Beta (1 / 2) (real n / 2 + 1)) {0..1}"
    using has_integral_Beta_real[of "1/2" "n / 2 + 1"] by simp
  from nn_integral_has_integral_lebesgue[OF _ this] have
     "ennreal (Beta (1 / 2) (real n / 2 + 1)) =
        nn_integral lborel (\<lambda>t. ennreal (t powr (-1 / 2) * (1 - t) powr (real n / 2) *
                                indicator {0^2..1^2} t))"
    by (simp add: mult_ac ennreal_mult' ennreal_indicator)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (x\<^sup>2 powr - (1 / 2) * (1 - x\<^sup>2) powr (real n / 2) * (2 * x) *
                          indicator {0..1} x) \<partial>lborel)"
    by (subst nn_integral_substitution[where g = "\<lambda>x. x ^ 2" and g' = "\<lambda>x. 2 * x"])
       (auto intro!: derivative_eq_intros continuous_intros simp: set_borel_measurable_def)
  also have "\<dots> = (\<integral>\<^sup>+ x. 2 * ennreal ((1 - x\<^sup>2) powr (real n / 2) * indicator {0..1} x) \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[of _ _ "{0}"])
       (auto simp: indicator_def powr_minus powr_half_sqrt field_split_simps ennreal_mult')
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal ((1 - x\<^sup>2) powr (real n / 2) * indicator {0..1} x) \<partial>lborel) +
                    (\<integral>\<^sup>+ x. ennreal ((1 - x\<^sup>2) powr (real n / 2) * indicator {0..1} x) \<partial>lborel)"
    (is "_ = ?I + _") by (simp add: mult_2 nn_integral_add)
  also have "?I = (\<integral>\<^sup>+ x. ennreal ((1 - x\<^sup>2) powr (real n / 2) * indicator {-1..0} x) \<partial>lborel)"
    by (subst nn_integral_real_affine[of _ "-1" 0])
       (auto simp: indicator_def intro!: nn_integral_cong)
  hence "?I + ?I = \<dots> + ?I" by simp
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal ((1 - x\<^sup>2) powr (real n / 2) *
                    (indicator {-1..0} x + indicator{0..1} x)) \<partial>lborel)"
    by (subst nn_integral_add [symmetric]) (auto simp: algebra_simps)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal ((1 - x\<^sup>2) powr (real n / 2) * indicator {-1..1} x) \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[of _ _ "{0}"]) (auto simp: indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (indicator {-1..1} x * sqrt (1 - x\<^sup>2) ^ n) \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[of _ _ "{1, -1}"])
       (auto simp: powr_half_sqrt [symmetric] indicator_def abs_square_le_1
          abs_square_eq_1 powr_def exp_of_nat_mult [symmetric] emeasure_lborel_countable)
  finally show ?thesis ..
qed

lemma real_sqrt_le_iff': "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> sqrt x \<le> y \<longleftrightarrow> x \<le> y ^ 2"
  using real_le_lsqrt sqrt_le_D by blast

text \<open>
  Isabelle's type system makes it very difficult to do an induction over the dimension
  of a Euclidean space type, because the type would change in the inductive step. To avoid
  this problem, we instead formulate the problem in a more concrete way by unfolding the
  definition of the Euclidean norm.
\<close>
lemma emeasure_cball_aux:
  assumes "finite A" "r > 0"
  shows   "emeasure (Pi\<^sub>M A (\<lambda>_. lborel))
             ({f. sqrt (\<Sum>i\<in>A. (f i)\<^sup>2) \<le> r} \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))) =
             ennreal (unit_ball_vol (real (card A)) * r ^ card A)"
  using assms
proof (induction arbitrary: r)
  case (empty r)
  thus ?case
    by (simp add: unit_ball_vol_def space_PiM)
next
  case (insert i A r)
  interpret product_sigma_finite "\<lambda>_. lborel"
    by standard
  have "emeasure (Pi\<^sub>M (insert i A) (\<lambda>_. lborel))
            ({f. sqrt (\<Sum>i\<in>insert i A. (f i)\<^sup>2) \<le> r} \<inter> space (Pi\<^sub>M (insert i A) (\<lambda>_. lborel))) =
        nn_integral (Pi\<^sub>M (insert i A) (\<lambda>_. lborel))
          (indicator ({f. sqrt (\<Sum>i\<in>insert i A. (f i)\<^sup>2) \<le> r} \<inter>
          space (Pi\<^sub>M (insert i A) (\<lambda>_. lborel))))"
    by (subst nn_integral_indicator) auto
  also have "\<dots> = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. indicator ({f. sqrt ((f i)\<^sup>2 + (\<Sum>i\<in>A. (f i)\<^sup>2)) \<le> r} \<inter>
                                space (Pi\<^sub>M (insert i A) (\<lambda>_. lborel))) (x(i := y))
                   \<partial>Pi\<^sub>M A (\<lambda>_. lborel) \<partial>lborel)"
    using insert.prems insert.hyps by (subst product_nn_integral_insert_rev) auto
  also have "\<dots> = (\<integral>\<^sup>+ (y::real). \<integral>\<^sup>+ x. indicator {-r..r} y * indicator ({f. sqrt ((\<Sum>i\<in>A. (f i)\<^sup>2)) \<le>
               sqrt (r ^ 2 - y ^ 2)} \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))) x \<partial>Pi\<^sub>M A (\<lambda>_. lborel) \<partial>lborel)"
  proof (intro nn_integral_cong, goal_cases)
    case (1 y f)
    have *: "y \<in> {-r..r}" if "y ^ 2 + c \<le> r ^ 2" "c \<ge> 0" for c
    proof -
      have "y ^ 2 \<le> y ^ 2 + c" using that by simp
      also have "\<dots> \<le> r ^ 2" by fact
      finally show ?thesis
        using \<open>r > 0\<close> by (simp add: power2_le_iff_abs_le abs_if split: if_splits)
    qed
    have "(\<Sum>x\<in>A. (if x = i then y else f x)\<^sup>2) = (\<Sum>x\<in>A. (f x)\<^sup>2)"
      using insert.hyps by (intro sum.cong) auto
    thus ?case using 1 \<open>r > 0\<close>
      by (auto simp: sum_nonneg real_sqrt_le_iff' indicator_def PiE_def space_PiM dest!: *)
  qed
  also have "\<dots> = (\<integral>\<^sup>+ (y::real). indicator {-r..r} y * (\<integral>\<^sup>+ x. indicator ({f. sqrt ((\<Sum>i\<in>A. (f i)\<^sup>2))
                                   \<le> sqrt (r ^ 2 - y ^ 2)} \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))) x
                  \<partial>Pi\<^sub>M A (\<lambda>_. lborel)) \<partial>lborel)" by (subst nn_integral_cmult) auto
  also have "\<dots> = (\<integral>\<^sup>+ (y::real). indicator {-r..r} y * emeasure (PiM A (\<lambda>_. lborel))
      ({f. sqrt ((\<Sum>i\<in>A. (f i)\<^sup>2)) \<le> sqrt (r ^ 2 - y ^ 2)} \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))) \<partial>lborel)"
    using \<open>finite A\<close> by (intro nn_integral_cong, subst nn_integral_indicator) auto
  also have "\<dots> = (\<integral>\<^sup>+ (y::real). indicator {-r..r} y * ennreal (unit_ball_vol (real (card A)) *
                                  (sqrt (r ^ 2 - y ^ 2)) ^ card A) \<partial>lborel)"
  proof (intro nn_integral_cong_AE, goal_cases)
    case 1
    have "AE y in lborel. y \<notin> {-r,r}"
      by (intro AE_not_in countable_imp_null_set_lborel) auto
    thus ?case
    proof eventually_elim
      case (elim y)
      show ?case
      proof (cases "y \<in> {-r<..<r}")
        case True
        hence "y\<^sup>2 < r\<^sup>2" by (subst real_sqrt_less_iff [symmetric]) auto
        thus ?thesis by (subst insert.IH) (auto)
      qed (insert elim, auto)
    qed
  qed
  also have "\<dots> = ennreal (unit_ball_vol (real (card A))) *
                    (\<integral>\<^sup>+ (y::real). indicator {-r..r} y * (sqrt (r ^ 2 - y ^ 2)) ^ card A \<partial>lborel)"
    by (subst nn_integral_cmult [symmetric])
       (auto simp: mult_ac ennreal_mult' [symmetric] indicator_def intro!: nn_integral_cong)
  also have "(\<integral>\<^sup>+ (y::real). indicator {-r..r} y * (sqrt (r ^ 2 - y ^ 2)) ^ card A \<partial>lborel) =
               (\<integral>\<^sup>+ (y::real). r ^ card A * indicator {-1..1} y * (sqrt (1 - y ^ 2)) ^ card A
               \<partial>(distr lborel borel ((*) (1/r))))" using \<open>r > 0\<close>
    by (subst nn_integral_distr)
       (auto simp: indicator_def field_simps real_sqrt_divide intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (r ^ Suc (card A)) *
               (indicator {- 1..1} x * sqrt (1 - x\<^sup>2) ^ card A) \<partial>lborel)" using \<open>r > 0\<close>
    by (subst lborel_distr_mult) (auto simp: nn_integral_density ennreal_mult' [symmetric] mult_ac)
  also have "\<dots> = ennreal (r ^ Suc (card A)) * (\<integral>\<^sup>+ x. indicator {- 1..1} x *
                    sqrt (1 - x\<^sup>2) ^ card A \<partial>lborel)"
    by (subst nn_integral_cmult) auto
  also note emeasure_cball_aux_integral
  also have "ennreal (unit_ball_vol (real (card A))) * (ennreal (r ^ Suc (card A)) *
                 ennreal (Beta (1/2) (card A / 2 + 1))) =
               ennreal (unit_ball_vol (card A) * Beta (1/2) (card A / 2 + 1) * r ^ Suc (card A))"
    using \<open>r > 0\<close> by (simp add: ennreal_mult' [symmetric] mult_ac)
  also have "unit_ball_vol (card A) * Beta (1/2) (card A / 2 + 1) = unit_ball_vol (Suc (card A))"
    by (auto simp: unit_ball_vol_def Beta_def Gamma_eq_zero_iff field_simps
          Gamma_one_half_real powr_half_sqrt [symmetric] powr_add [symmetric])
  also have "Suc (card A) = card (insert i A)" using insert.hyps by simp
  finally show ?case .
qed


text \<open>
  We now get the main theorem very easily by just applying the above lemma.
\<close>
context
  fixes c :: "'a :: euclidean_space" and r :: real
  assumes r: "r \<ge> 0"
begin

theorem\<^marker>\<open>tag unimportant\<close> emeasure_cball:
  "emeasure lborel (cball c r) = ennreal (unit_ball_vol (DIM('a)) * r ^ DIM('a))"
proof (cases "r = 0")
  case False
  with r have r: "r > 0" by simp
  have "(lborel :: 'a measure) =
          distr (Pi\<^sub>M Basis (\<lambda>_. lborel)) borel (\<lambda>f. \<Sum>b\<in>Basis. f b *\<^sub>R b)"
    by (rule lborel_eq)
  also have "emeasure \<dots> (cball 0 r) =
               emeasure (Pi\<^sub>M Basis (\<lambda>_. lborel))
               ({y. dist 0 (\<Sum>b\<in>Basis. y b *\<^sub>R b :: 'a) \<le> r} \<inter> space (Pi\<^sub>M Basis (\<lambda>_. lborel)))"
    by (subst emeasure_distr) (auto simp: cball_def)
  also have "{f. dist 0 (\<Sum>b\<in>Basis. f b *\<^sub>R b :: 'a) \<le> r} = {f. sqrt (\<Sum>i\<in>Basis. (f i)\<^sup>2) \<le> r}"
    by (subst euclidean_dist_l2) (auto simp: L2_set_def)
  also have "emeasure (Pi\<^sub>M Basis (\<lambda>_. lborel)) (\<dots> \<inter> space (Pi\<^sub>M Basis (\<lambda>_. lborel))) =
               ennreal (unit_ball_vol (real DIM('a)) * r ^ DIM('a))"
    using r by (subst emeasure_cball_aux) simp_all
  also have "emeasure lborel (cball 0 r :: 'a set) =
               emeasure (distr lborel borel (\<lambda>x. c + x)) (cball c r)"
    by (subst emeasure_distr) (auto simp: cball_def dist_norm norm_minus_commute)
  also have "distr lborel borel (\<lambda>x. c + x) = lborel"
    using lborel_affine[of 1 c] by (simp add: density_1)
  finally show ?thesis .
qed auto

corollary\<^marker>\<open>tag unimportant\<close> content_cball:
  "content (cball c r) = unit_ball_vol (DIM('a)) * r ^ DIM('a)"
  by (simp add: measure_def emeasure_cball r)

corollary\<^marker>\<open>tag unimportant\<close> emeasure_ball:
  "emeasure lborel (ball c r) = ennreal (unit_ball_vol (DIM('a)) * r ^ DIM('a))"
proof -
  from negligible_sphere[of c r] have "sphere c r \<in> null_sets lborel"
    by (auto simp: null_sets_completion_iff negligible_iff_null_sets negligible_convex_frontier)
  hence "emeasure lborel (ball c r \<union> sphere c r :: 'a set) = emeasure lborel (ball c r :: 'a set)"
    by (intro emeasure_Un_null_set) auto
  also have "ball c r \<union> sphere c r = (cball c r :: 'a set)" by auto
  also have "emeasure lborel \<dots> = ennreal (unit_ball_vol (real DIM('a)) * r ^ DIM('a))"
    by (rule emeasure_cball)
  finally show ?thesis ..
qed

corollary\<^marker>\<open>tag important\<close> content_ball:
  "content (ball c r) = unit_ball_vol (DIM('a)) * r ^ DIM('a)"
  by (simp add: measure_def r emeasure_ball)

end


text \<open>
  Lastly, we now prove some nicer explicit formulas for the volume of the unit balls in
  the cases of even and odd integer dimensions.
\<close>
lemma unit_ball_vol_even:
  "unit_ball_vol (real (2 * n)) = pi ^ n / fact n"
  by (simp add: unit_ball_vol_def add_ac powr_realpow Gamma_fact)

lemma unit_ball_vol_odd':
        "unit_ball_vol (real (2 * n + 1)) = pi ^ n / pochhammer (1 / 2) (Suc n)"
  and unit_ball_vol_odd:
        "unit_ball_vol (real (2 * n + 1)) =
           (2 ^ (2 * Suc n) * fact (Suc n)) / fact (2 * Suc n) * pi ^ n"
proof -
  have "unit_ball_vol (real (2 * n + 1)) =
          pi powr (real n + 1 / 2) / Gamma (1 / 2 + real (Suc n))"
    by (simp add: unit_ball_vol_def field_simps)
  also have "pochhammer (1 / 2) (Suc n) = Gamma (1 / 2 + real (Suc n)) / Gamma (1 / 2)"
    by (intro pochhammer_Gamma) auto
  hence "Gamma (1 / 2 + real (Suc n)) = sqrt pi * pochhammer (1 / 2) (Suc n)"
    by (simp add: Gamma_one_half_real)
  also have "pi powr (real n + 1 / 2) / \<dots> = pi ^ n / pochhammer (1 / 2) (Suc n)"
    by (simp add: powr_add powr_half_sqrt powr_realpow)
  finally show "unit_ball_vol (real (2 * n + 1)) = \<dots>" .
  also have "pochhammer (1 / 2 :: real) (Suc n) =
               fact (2 * Suc n) / (2 ^ (2 * Suc n) * fact (Suc n))"
    using fact_double[of "Suc n", where ?'a = real] by (simp add: divide_simps mult_ac)
  also have "pi ^n / \<dots> = (2 ^ (2 * Suc n) * fact (Suc n)) / fact (2 * Suc n) * pi ^ n"
    by simp
  finally show "unit_ball_vol (real (2 * n + 1)) = \<dots>" .
qed

lemma unit_ball_vol_numeral:
  "unit_ball_vol (numeral (Num.Bit0 n)) = pi ^ numeral n / fact (numeral n)" (is ?th1)
  "unit_ball_vol (numeral (Num.Bit1 n)) = 2 ^ (2 * Suc (numeral n)) * fact (Suc (numeral n)) /
    fact (2 * Suc (numeral n)) * pi ^ numeral n" (is ?th2)
proof -
  have "numeral (Num.Bit0 n) = (2 * numeral n :: nat)"
    by (simp only: numeral_Bit0 mult_2 ring_distribs)
  also have "unit_ball_vol \<dots> = pi ^ numeral n / fact (numeral n)"
    by (rule unit_ball_vol_even)
  finally show ?th1 by simp
next
  have "numeral (Num.Bit1 n) = (2 * numeral n + 1 :: nat)"
    by (simp only: numeral_Bit1 mult_2)
  also have "unit_ball_vol \<dots> = 2 ^ (2 * Suc (numeral n)) * fact (Suc (numeral n)) /
                                  fact (2 * Suc (numeral n)) * pi ^ numeral n"
    by (rule unit_ball_vol_odd)
  finally show ?th2 by simp
qed

lemmas eval_unit_ball_vol = unit_ball_vol_numeral fact_numeral


text \<open>
  Just for fun, we compute the volume of unit balls for a few dimensions.
\<close>
lemma unit_ball_vol_0 [simp]: "unit_ball_vol 0 = 1"
  using unit_ball_vol_even[of 0] by simp

lemma unit_ball_vol_1 [simp]: "unit_ball_vol 1 = 2"
  using unit_ball_vol_odd[of 0] by simp

corollary\<^marker>\<open>tag unimportant\<close>
          unit_ball_vol_2: "unit_ball_vol 2 = pi"
      and unit_ball_vol_3: "unit_ball_vol 3 = 4 / 3 * pi"
      and unit_ball_vol_4: "unit_ball_vol 4 = pi\<^sup>2 / 2"
      and unit_ball_vol_5: "unit_ball_vol 5 = 8 / 15 * pi\<^sup>2"
  by (simp_all add: eval_unit_ball_vol)

corollary\<^marker>\<open>tag unimportant\<close> circle_area:
  "r \<ge> 0 \<Longrightarrow> content (ball c r :: (real ^ 2) set) = r ^ 2 * pi"
  by (simp add: content_ball unit_ball_vol_2)

corollary\<^marker>\<open>tag unimportant\<close> sphere_volume:
  "r \<ge> 0 \<Longrightarrow> content (ball c r :: (real ^ 3) set) = 4 / 3 * r ^ 3 * pi"
  by (simp add: content_ball unit_ball_vol_3)

text \<open>
  Useful equivalent forms
\<close>
corollary\<^marker>\<open>tag unimportant\<close> content_ball_eq_0_iff [simp]: "content (ball c r) = 0 \<longleftrightarrow> r \<le> 0"
proof -
  have "r > 0 \<Longrightarrow> content (ball c r) > 0"
    by (simp add: content_ball unit_ball_vol_def)
  then show ?thesis
    by (fastforce simp: ball_empty)
qed

corollary\<^marker>\<open>tag unimportant\<close> content_ball_gt_0_iff [simp]: "0 < content (ball z r) \<longleftrightarrow> 0 < r"
  by (auto simp: zero_less_measure_iff)

corollary\<^marker>\<open>tag unimportant\<close> content_cball_eq_0_iff [simp]: "content (cball c r) = 0 \<longleftrightarrow> r \<le> 0"
proof (cases "r = 0")
  case False
  moreover have "r > 0 \<Longrightarrow> content (cball c r) > 0"
    by (simp add: content_cball unit_ball_vol_def)
  ultimately show ?thesis
    by fastforce
qed auto

corollary\<^marker>\<open>tag unimportant\<close> content_cball_gt_0_iff [simp]: "0 < content (cball z r) \<longleftrightarrow> 0 < r"
  by (auto simp: zero_less_measure_iff)

end
