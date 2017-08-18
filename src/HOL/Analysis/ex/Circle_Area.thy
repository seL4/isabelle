(*  Title:      HOL/Analysis/ex/Circle_Area.thy
    Author:     Manuel Eberl, TU Muenchen

A proof that the area of a circle with radius R is R\<^sup>2\<pi>.
*)

section \<open>The area of a circle\<close>

theory Circle_Area
imports Complex_Main "HOL-Analysis.Interval_Integral"
begin

lemma plus_emeasure':
  assumes "A \<in> sets M" "B \<in> sets M" "A \<inter> B \<in> null_sets M"
  shows "emeasure M A + emeasure M B = emeasure M (A \<union> B)"
proof-
  let ?C = "A \<inter> B"
  have "A \<union> B = A \<union> (B - ?C)" by blast
  with assms have "emeasure M (A \<union> B) = emeasure M A + emeasure M (B - ?C)"
    by (subst plus_emeasure) auto
  also from assms(3,2) have "emeasure M (B - ?C) = emeasure M B"
    by (rule emeasure_Diff_null_set)
  finally show ?thesis ..
qed

lemma real_sqrt_square:
  "x \<ge> 0 \<Longrightarrow> sqrt (x^2) = (x::real)" by simp

lemma unit_circle_area_aux:
  "LBINT x=-1..1. 2 * sqrt (1 - x^2) = pi"
proof-
  have "LBINT x=-1..1. 2 * sqrt (1 - x^2) =
            LBINT x=ereal (sin (-pi/2))..ereal (sin (pi/2)). 2 * sqrt (1 - x^2)"
    by (simp_all add: one_ereal_def)
  also have "... = LBINT x=-pi/2..pi/2. cos x *\<^sub>R (2 * sqrt (1 - (sin x)\<^sup>2))"
    by (rule interval_integral_substitution_finite[symmetric])
       (auto intro: DERIV_subset[OF DERIV_sin] intro!: continuous_intros)
  also have "... = LBINT x=-pi/2..pi/2. 2 * cos x * sqrt ((cos x)^2)"
    by (simp add: cos_squared_eq field_simps)
  also {
    fix x assume "x \<in> {-pi/2<..<pi/2}"
    hence "cos x \<ge> 0" by (intro cos_ge_zero) simp_all
    hence "sqrt ((cos x)^2) = cos x" by simp
  } note A = this
  have "LBINT x=-pi/2..pi/2. 2 * cos x * sqrt ((cos x)^2) = LBINT x=-pi/2..pi/2. 2 * (cos x)^2"
    by (intro interval_integral_cong, subst A) (simp_all add: min_def max_def power2_eq_square)
  also let ?F = "\<lambda>x. x + sin x * cos x"
   {
    fix x A
    have "(?F has_real_derivative 1 - (sin x)^2 + (cos x)^2) (at x)"
      by (auto simp: power2_eq_square intro!: derivative_eq_intros)
    also have "1 - (sin x)^2 + (cos x)^2 = 2 * (cos x)^2" by (simp add: cos_squared_eq)
    finally have "(?F has_real_derivative 2 * (cos x)^2) (at x within A)"
      by (rule DERIV_subset) simp
  }
  hence "LBINT x=-pi/2..pi/2. 2 * (cos x)^2 = ?F (pi/2) - ?F (-pi/2)"
    by (intro interval_integral_FTC_finite)
       (auto simp: has_field_derivative_iff_has_vector_derivative intro!: continuous_intros)
  also have "... = pi" by simp
  finally show ?thesis .
qed

lemma unit_circle_area:
  "emeasure lborel {z::real\<times>real. norm z \<le> 1} = pi" (is "emeasure _ ?A = _")
proof-
  let ?A1 = "{(x,y)\<in>?A. y \<ge> 0}" and ?A2 = "{(x,y)\<in>?A. y \<le> 0}"
  have [measurable]: "(\<lambda>x. snd (x :: real \<times> real)) \<in> measurable borel borel"
    by (simp add: borel_prod[symmetric])

  have "?A1 = ?A \<inter> {x\<in>space lborel. snd x \<ge> 0}" by auto
  also have "?A \<inter> {x\<in>space lborel. snd x \<ge> 0} \<in> sets borel"
    by (intro sets.Int pred_Collect_borel) simp_all
  finally have A1_in_sets: "?A1 \<in> sets lborel" by (subst sets_lborel)

  have "?A2 = ?A \<inter> {x\<in>space lborel. snd x \<le> 0}" by auto
  also have "... \<in> sets borel"
    by (intro sets.Int pred_Collect_borel) simp_all
  finally have A2_in_sets: "?A2 \<in> sets lborel" by (subst sets_lborel)

  have A12: "?A = ?A1 \<union> ?A2" by auto
  have sq_le_1_iff: "\<And>x. x\<^sup>2 \<le> 1 \<longleftrightarrow> abs (x::real) \<le> 1"
    by (simp add: abs_square_le_1)
  have "?A1 \<inter> ?A2 = {x. abs x \<le> 1} \<times> {0}" by (auto simp: norm_Pair field_simps sq_le_1_iff)
  also have "... \<in> null_sets lborel"
    by (subst lborel_prod[symmetric]) (auto simp: lborel.emeasure_pair_measure_Times)
  finally have "emeasure lborel ?A = emeasure lborel ?A1 + emeasure lborel ?A2"
    by (subst A12, rule plus_emeasure'[OF A1_in_sets A2_in_sets, symmetric])

  also have "emeasure lborel ?A1 = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel \<partial>lborel"
    by (subst lborel_prod[symmetric], subst lborel.emeasure_pair_measure)
       (simp_all only: lborel_prod A1_in_sets)
  also have "emeasure lborel ?A2 = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A2 (x,y) \<partial>lborel \<partial>lborel"
    by (subst lborel_prod[symmetric], subst lborel.emeasure_pair_measure)
       (simp_all only: lborel_prod A2_in_sets)
  also have "distr lborel lborel uminus = (lborel :: real measure)"
    by (subst (3) lborel_real_affine[of "-1" 0])
       (simp_all add: one_ereal_def[symmetric] density_1 cong: distr_cong)
  hence "(\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A2 (x,y) \<partial>lborel \<partial>lborel) =
             \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A2 (x,y) \<partial>distr lborel lborel uminus \<partial>lborel" by simp
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A2 (x,-y) \<partial>lborel \<partial>lborel"
    apply (intro nn_integral_cong nn_integral_distr, simp)
    apply (intro measurable_compose[OF _ borel_measurable_indicator[OF A2_in_sets]], simp)
    done
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel \<partial>lborel"
    by (intro nn_integral_cong) (auto split: split_indicator simp: norm_Pair)
  also have "... + ... = (1+1) * ..." by (subst ring_distribs) simp_all
  also have "... = \<integral>\<^sup>+x. 2 * \<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel \<partial>lborel"
    by (subst nn_integral_cmult) simp_all
  also {
    fix x y :: real assume "x \<notin> {-1..1}"
    hence "abs x > 1" by auto
    also have "norm (x,y) \<ge> abs x" by (simp add: norm_Pair)
    finally have "(x,y) \<notin> ?A1" by auto
  }
  hence "... = \<integral>\<^sup>+x. 2 * (\<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel) * indicator {-1..1} x \<partial>lborel"
    by (intro nn_integral_cong) (auto split: split_indicator)
  also {
    fix x :: real assume "x \<in> {-1..1}"
    hence x: "1 - x\<^sup>2 \<ge> 0" by (simp add: field_simps sq_le_1_iff abs_real_def)
    have "\<And>y. (y::real) \<ge> 0 \<Longrightarrow> norm (x,y) \<le> 1 \<longleftrightarrow> y \<le> sqrt (1-x\<^sup>2)"
      by (subst (5) real_sqrt_square[symmetric], simp, subst real_sqrt_le_iff)
         (simp_all add: norm_Pair field_simps)
    hence "(\<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel) = (\<integral>\<^sup>+y. indicator {0..sqrt (1-x\<^sup>2)} y \<partial>lborel)"
      by (intro nn_integral_cong) (auto split: split_indicator)
    also from x have "... = sqrt (1-x\<^sup>2)" using x by simp
    finally have "(\<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel) = sqrt (1-x\<^sup>2)" .
  }
  hence "(\<integral>\<^sup>+x. 2 * (\<integral>\<^sup>+y. indicator ?A1 (x,y) \<partial>lborel) * indicator {-1..1} x \<partial>lborel) =
            \<integral>\<^sup>+x. 2 * sqrt (1-x\<^sup>2) * indicator {-1..1} x \<partial>lborel"
    by (intro nn_integral_cong) (simp split: split_indicator add: ennreal_mult')
  also have A: "\<And>x. -1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> \<not>x^2 > (1::real)"
    by (subst not_less, subst sq_le_1_iff) (simp add: abs_real_def)
  have "integrable lborel (\<lambda>x. 2 * sqrt (1-x\<^sup>2) * indicator {-1..1::real} x)"
    by (intro borel_integrable_atLeastAtMost continuous_intros)
  hence "(\<integral>\<^sup>+x. 2 * sqrt (1-x\<^sup>2) * indicator {-1..1} x \<partial>lborel) =
             ennreal (\<integral>x. 2 * sqrt (1-x\<^sup>2) * indicator {-1..1} x \<partial>lborel)"
    by (intro nn_integral_eq_integral AE_I2)
       (auto split: split_indicator simp: field_simps sq_le_1_iff)
  also have "(\<integral>x. 2 * sqrt (1-x\<^sup>2) * indicator {-1..1} x \<partial>lborel) =
               LBINT x:{-1..1}. 2 * sqrt (1-x\<^sup>2)" by (simp add: field_simps)
  also have "... = LBINT x=-1..1. 2 * sqrt (1-x\<^sup>2)"
    by (subst interval_integral_Icc[symmetric]) (simp_all add: one_ereal_def)
  also have "... = pi" by (rule unit_circle_area_aux)
  finally show ?thesis .
qed

lemma circle_area:
  assumes "R \<ge> 0"
  shows   "emeasure lborel {z::real\<times>real. norm z \<le> R} = R^2 * pi" (is "emeasure _ ?A = _")
proof (cases "R = 0")
  assume "R \<noteq> 0"
  with assms have R: "R > 0" by simp
  let ?A' = "{z::real\<times>real. norm z \<le> 1}"
  have "emeasure lborel ?A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A (x,y) \<partial>lborel \<partial>lborel"
    by (subst lborel_prod[symmetric], subst lborel.emeasure_pair_measure, subst lborel_prod)
       simp_all
  also have "... = \<integral>\<^sup>+x. R * \<integral>\<^sup>+y. indicator ?A (x,R*y) \<partial>lborel \<partial>lborel"
  proof (rule nn_integral_cong)
    fix x from R show "(\<integral>\<^sup>+y. indicator ?A (x,y) \<partial>lborel) = R * \<integral>\<^sup>+y. indicator ?A (x,R*y) \<partial>lborel"
      by (subst nn_integral_real_affine[OF _ \<open>R \<noteq> 0\<close>, of _ 0]) simp_all
  qed
  also have "... = R * \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A (x,R*y) \<partial>lborel \<partial>lborel"
    using R by (intro nn_integral_cmult) simp_all
  also from R have "(\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A (x,R*y) \<partial>lborel \<partial>lborel) =
                        R * \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A (R*x,R*y) \<partial>lborel \<partial>lborel"
    by (subst nn_integral_real_affine[OF _ \<open>R \<noteq> 0\<close>, of _ 0]) simp_all
  also {
    fix x y
    have A: "(R*x, R*y) = R *\<^sub>R (x,y)" by simp
    from R have "norm (R*x, R*y) = R * norm (x,y)" by (subst A, subst norm_scaleR) simp_all
    with R have "(R*x, R*y) \<in> ?A \<longleftrightarrow> (x, y) \<in> ?A'" by (auto simp: field_simps)
  }
  hence "(\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A (R*x,R*y) \<partial>lborel \<partial>lborel) =
               \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator ?A' (x,y) \<partial>lborel \<partial>lborel"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also have "... = emeasure lborel ?A'"
    by (subst lborel_prod[symmetric], subst lborel.emeasure_pair_measure, subst lborel_prod)
       simp_all
  also have "... = pi" by (rule unit_circle_area)
  finally show ?thesis using assms by (simp add: power2_eq_square ennreal_mult mult_ac)
qed simp

end
