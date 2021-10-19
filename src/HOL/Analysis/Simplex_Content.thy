(*
   File:      Analysis/Simplex_Content.thy
   Author:    Manuel Eberl <manuel@pruvisto.org>

   The content of an n-dimensional simplex, including the formula for the content of a
   triangle and Heron's formula.
*)
section \<open>Volume of a Simplex\<close>

theory Simplex_Content
imports Change_Of_Vars
begin

lemma fact_neq_top_ennreal [simp]: "fact n \<noteq> (top :: ennreal)"
  by (induction n) (auto simp: ennreal_mult_eq_top_iff)

lemma ennreal_fact: "ennreal (fact n) = fact n"
  by (induction n) (auto simp: ennreal_mult algebra_simps ennreal_of_nat_eq_real_of_nat)

context
  fixes S :: "'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real) set"
  defines "S \<equiv> (\<lambda>A t. {x. (\<forall>i\<in>A. 0 \<le> x i) \<and> sum x A \<le> t})"
begin

lemma emeasure_std_simplex_aux_step:
  assumes "b \<notin> A" "finite A"
  shows   "x(b := y) \<in> S (insert b A) t \<longleftrightarrow> y \<in> {0..t} \<and> x \<in> S A (t - y)"
  using assms sum_nonneg[of A x] unfolding S_def
  by (force simp: sum_delta_notmem algebra_simps)

lemma emeasure_std_simplex_aux:
  fixes t :: real
  assumes "finite (A :: 'a set)" "t \<ge> 0"
  shows   "emeasure (Pi\<^sub>M A (\<lambda>_. lborel)) 
             (S A t \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))) = t ^ card A / fact (card A)"
  using assms(1,2)
proof (induction arbitrary: t rule: finite_induct)
  case (empty t)
  thus ?case by (simp add: PiM_empty S_def)
next
  case (insert b A t)
  define n where "n = Suc (card A)"
  have n_pos: "n > 0" by (simp add: n_def)
  let ?M = "\<lambda>A. (Pi\<^sub>M A (\<lambda>_. lborel))"
  {
    fix A :: "'a set" and t :: real assume "finite A" 
    have "S A t \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel)) =
            Pi\<^sub>E A (\<lambda>_. {0..}) \<inter> (\<lambda>x. sum x A) -` {..t} \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))"
      by (auto simp: S_def space_PiM)
    also have "\<dots> \<in> sets (Pi\<^sub>M A (\<lambda>_. lborel))"
      using \<open>finite A\<close> by measurable
    finally have "S A t \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel)) \<in> sets (Pi\<^sub>M A (\<lambda>_. lborel))" .
  } note meas [measurable] = this

  interpret product_sigma_finite "\<lambda>_. lborel"
    by standard
  have "emeasure (?M (insert b A)) (S (insert b A) t \<inter> space (?M (insert b A))) =
        nn_integral (?M (insert b A))
          (\<lambda>x. indicator (S (insert b A) t \<inter> space (?M (insert b A))) x)"
    using insert.hyps by (subst nn_integral_indicator) auto
  also have "\<dots> = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. indicator (S (insert b A) t \<inter> space (?M (insert b A)))
                    (x(b := y)) \<partial>?M A \<partial>lborel)"
    using insert.prems insert.hyps by (intro product_nn_integral_insert_rev) auto
  also have "\<dots> = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. indicator {0..t} y * indicator (S A (t - y) \<inter> space (?M A)) x
                    \<partial>?M A \<partial>lborel)"
    using insert.hyps insert.prems emeasure_std_simplex_aux_step[of b A]
    by (intro nn_integral_cong)
       (auto simp: fun_eq_iff indicator_def space_PiM PiE_def extensional_def)
  also have "\<dots> = (\<integral>\<^sup>+ y. indicator {0..t} y * (\<integral>\<^sup>+ x. indicator (S A (t - y) \<inter> space (?M A)) x
                    \<partial>?M A) \<partial>lborel)" using \<open>finite A\<close>
    by (subst nn_integral_cmult) auto
  also have "\<dots> = (\<integral>\<^sup>+ y. indicator {0..t} y * emeasure (?M A) (S A (t - y) \<inter> space (?M A)) \<partial>lborel)"
    using \<open>finite A\<close> by (subst nn_integral_indicator) auto
  also have "\<dots> = (\<integral>\<^sup>+ y. indicator {0..t} y * (t - y) ^ card A / ennreal (fact (card A)) \<partial>lborel)"
    using insert.IH by (intro nn_integral_cong) (auto simp: indicator_def divide_ennreal)
  also have "\<dots> = (\<integral>\<^sup>+ y. indicator {0..t} y * (t - y) ^ card A \<partial>lborel) / ennreal (fact (card A))"
    using \<open>finite A\<close> by (subst nn_integral_divide) auto
  also have "(\<integral>\<^sup>+ y. indicator {0..t} y * (t - y) ^ card A \<partial>lborel) = 
               (\<integral>\<^sup>+y\<in>{0..t}. ennreal ((t - y) ^ (n - 1)) \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: indicator_def n_def)
  also have "((\<lambda>x. - ((t - x) ^ n / n)) has_real_derivative (t - x) ^ (n - 1)) (at x)" 
    if "x \<in> {0..t}" for x by (rule derivative_eq_intros refl | simp add: n_pos)+
  hence "(\<integral>\<^sup>+y\<in>{0..t}. ennreal ((t - y) ^ (n - 1)) \<partial>lborel) = 
           ennreal (-((t - t) ^ n / n) - (-((t - 0) ^ n / n)))"
    using insert.prems insert.hyps by (intro nn_integral_FTC_Icc) auto
  also have "\<dots> = ennreal (t ^ n / n)" using n_pos by (simp add: zero_power)
  also have "\<dots> / ennreal (fact (card A)) = ennreal (t ^ n / n / fact (card A))"
    using n_pos \<open>t \<ge> 0\<close> by (subst divide_ennreal) auto
  also have "t ^ n / n / fact (card A) = t ^ n / fact n"
    by (simp add: n_def)
  also have "n = card (insert b A)"
    using insert.hyps by (subst card.insert_remove) (auto simp: n_def)
  finally show ?case .
qed

end

lemma emeasure_std_simplex:
  "emeasure lborel (convex hull (insert 0 Basis :: 'a :: euclidean_space set)) =
     ennreal (1 / fact DIM('a))"
proof -
  have "emeasure lborel {x::'a. (\<forall>i\<in>Basis. 0 \<le> x \<bullet> i) \<and> sum ((\<bullet>) x) Basis \<le> 1} =
               emeasure (distr (Pi\<^sub>M Basis (\<lambda>b. lborel)) borel (\<lambda>f. \<Sum>b\<in>Basis. f b *\<^sub>R b))
                 {x::'a. (\<forall>i\<in>Basis. 0 \<le> x \<bullet> i) \<and> sum ((\<bullet>) x) Basis \<le> 1}"
    by (subst lborel_eq) simp
  also have "\<dots> = emeasure (Pi\<^sub>M Basis (\<lambda>b. lborel))
                    ({y::'a \<Rightarrow> real. (\<forall>i\<in>Basis. 0 \<le> y i) \<and> sum y Basis \<le> 1} \<inter>
                      space (Pi\<^sub>M Basis (\<lambda>b. lborel)))"
    by (subst emeasure_distr) auto
  also have "\<dots> = ennreal (1 / fact DIM('a))"
    by (subst emeasure_std_simplex_aux) auto
  finally show ?thesis by (simp only: std_simplex)
qed

theorem content_std_simplex:
  "measure lborel (convex hull (insert 0 Basis :: 'a :: euclidean_space set)) =
     1 / fact DIM('a)"
  by (simp add: measure_def emeasure_std_simplex)

(* TODO: move to Change_of_Vars *)
proposition measure_lebesgue_linear_transformation:
  fixes A :: "(real ^ 'n :: {finite, wellorder}) set"
  fixes f :: "_ \<Rightarrow> real ^ 'n :: {finite, wellorder}"
  assumes "bounded A" "A \<in> sets lebesgue" "linear f"
  shows   "measure lebesgue (f ` A) = \<bar>det (matrix f)\<bar> * measure lebesgue A"
proof -
  from assms have [intro]: "A \<in> lmeasurable"
    by (intro bounded_set_imp_lmeasurable) auto
  hence [intro]: "f ` A \<in> lmeasurable"
    by (intro lmeasure_integral measurable_linear_image assms)
  have "measure lebesgue (f ` A) = integral (f ` A) (\<lambda>_. 1)"
    by (intro lmeasure_integral measurable_linear_image assms) auto
  also have "\<dots> = integral (f ` A) (\<lambda>_. 1 :: real ^ 1) $ 0"
    by (subst integral_component_eq_cart [symmetric]) (auto intro: integrable_on_const)
  also have "\<dots> = \<bar>det (matrix f)\<bar> * integral A (\<lambda>x. 1 :: real ^ 1) $ 0"
    using assms
    by (subst integral_change_of_variables_linear)
       (auto simp: o_def absolutely_integrable_on_def intro: integrable_on_const)
  also have "integral A (\<lambda>x. 1 :: real ^ 1) $ 0 = integral A (\<lambda>x. 1)"
    by (subst integral_component_eq_cart [symmetric]) (auto intro: integrable_on_const)
  also have "\<dots> = measure lebesgue A"
    by (intro lmeasure_integral [symmetric]) auto
  finally show ?thesis .
qed

theorem content_simplex:
  fixes X :: "(real ^ 'n :: {finite, wellorder}) set" and f :: "'n :: _ \<Rightarrow> real ^ ('n :: _)"
  assumes "finite X" "card X = Suc CARD('n)" and x0: "x0 \<in> X" and bij: "bij_betw f UNIV (X - {x0})"
  defines "M \<equiv> (\<chi> i. \<chi> j. f j $ i - x0 $ i)"
  shows "content (convex hull X) = \<bar>det M\<bar> / fact (CARD('n))"
proof -
  define g where "g = (\<lambda>x. M *v x)"
  have [simp]: "M *v axis i 1 = f i - x0" for i :: 'n
    by (simp add: M_def matrix_vector_mult_basis column_def vec_eq_iff)
  define std where "std = (convex hull insert 0 Basis :: (real ^ 'n :: _) set)"
  have compact: "compact std" unfolding std_def
    by (intro finite_imp_compact_convex_hull) auto

  have "measure lebesgue (convex hull X) = measure lebesgue (((+) (-x0)) ` (convex hull X))"
    by (rule measure_translation [symmetric])
  also have "((+) (-x0)) ` (convex hull X) = convex hull (((+) (-x0)) ` X)"
    by (rule convex_hull_translation [symmetric])
  also have "((+) (-x0)) ` X = insert 0 ((\<lambda>x. x - x0) ` (X - {x0}))"
    using x0 by (auto simp: image_iff)
  finally have eq: "measure lebesgue (convex hull X) = measure lebesgue (convex hull \<dots>)" .
  
  from compact have "measure lebesgue (g ` std) = \<bar>det M\<bar> * measure lebesgue std"
    by (subst measure_lebesgue_linear_transformation)
       (auto intro: finite_imp_bounded_convex_hull dest: compact_imp_closed simp: g_def std_def)
  also have "measure lebesgue std = content std" using compact
    by (intro measure_completion) (auto dest: compact_imp_closed)
  also have "content std = 1 / fact CARD('n)" unfolding std_def
    by (simp add: content_std_simplex)
  also have "g ` std = convex hull (g ` insert 0 Basis)" unfolding std_def
    by (rule convex_hull_linear_image) (auto simp: g_def)
  also have "g ` insert 0 Basis = insert 0 (g ` Basis)"
    by (auto simp: g_def)
  also have "g ` Basis = (\<lambda>x. x - x0) ` range f"
    by (auto simp: g_def Basis_vec_def image_iff)
  also have "range f = X - {x0}" using bij
    using bij_betw_imp_surj_on by blast
  also note eq [symmetric]
  finally show ?thesis 
    using finite_imp_compact_convex_hull[OF \<open>finite X\<close>] by (auto dest: compact_imp_closed)
qed

theorem content_triangle:
  fixes A B C :: "real ^ 2"
  shows "content (convex hull {A, B, C}) =
           \<bar>(C $ 1 - A $ 1) * (B $ 2 - A $ 2) - (B $ 1 - A $ 1) * (C $ 2 - A $ 2)\<bar> / 2"
proof -
  define M :: "real ^ 2 ^ 2" where "M \<equiv> (\<chi> i. \<chi> j. (if j = 1 then B else C) $ i - A $ i)"
  define g where "g = (\<lambda>x. M *v x)"
  define std where "std = (convex hull insert 0 Basis :: (real ^ 2) set)"
  have [simp]: "M *v axis i 1 = (if i = 1 then B - A else C - A)" for i
    by (auto simp: M_def matrix_vector_mult_basis column_def vec_eq_iff)
  have compact: "compact std" unfolding std_def
    by (intro finite_imp_compact_convex_hull) auto

  have "measure lebesgue (convex hull {A, B, C}) =
          measure lebesgue (((+) (-A)) ` (convex hull {A, B, C}))"
    by (rule measure_translation [symmetric])
  also have "((+) (-A)) ` (convex hull {A, B, C}) = convex hull (((+) (-A)) ` {A, B, C})"
    by (rule convex_hull_translation [symmetric])
  also have "((+) (-A)) ` {A, B, C} = {0, B - A, C - A}"
    by (auto simp: image_iff)
  finally have eq: "measure lebesgue (convex hull {A, B, C}) =
                      measure lebesgue (convex hull {0, B - A, C - A})" .
  
  from compact have "measure lebesgue (g ` std) = \<bar>det M\<bar> * measure lebesgue std"
    by (subst measure_lebesgue_linear_transformation)
       (auto intro: finite_imp_bounded_convex_hull dest: compact_imp_closed simp: g_def std_def)
  also have "measure lebesgue std = content std" using compact
    by (intro measure_completion) (auto dest: compact_imp_closed)
  also have "content std = 1 / 2" unfolding std_def
    by (simp add: content_std_simplex)
  also have "g ` std = convex hull (g ` insert 0 Basis)" unfolding std_def
    by (rule convex_hull_linear_image) (auto simp: g_def)
  also have "g ` insert 0 Basis = insert 0 (g ` Basis)"
    by (auto simp: g_def)
  also have "(2 :: 2) \<noteq> 1" by auto
  hence "\<not>(\<forall>y::2. y = 1)" by blast
  hence "g ` Basis = {B - A, C - A}"
    by (auto simp: g_def Basis_vec_def image_iff)
  also note eq [symmetric]
  finally show ?thesis 
    using finite_imp_compact_convex_hull[of "{A, B, C}"]
    by (auto dest!: compact_imp_closed simp: det_2 M_def)
qed

theorem heron:
  fixes A B C :: "real ^ 2"
  defines "a \<equiv> dist B C" and "b \<equiv> dist A C" and "c \<equiv> dist A B"
  defines "s \<equiv> (a + b + c) / 2"
  shows   "content (convex hull {A, B, C}) = sqrt (s * (s - a) * (s - b) * (s - c))"
proof -
  have [simp]: "(UNIV :: 2 set) = {1, 2}"
    using exhaust_2 by auto
  have dist_eq: "dist (A :: real ^ 2) B ^ 2 = (A $ 1 - B $ 1) ^ 2 + (A $ 2 - B $ 2) ^ 2"
    for A B by (simp add: dist_vec_def dist_real_def)
  have nonneg: "s * (s - a) * (s - b) * (s - c) \<ge> 0"
    using dist_triangle[of A B C] dist_triangle[of A C B] dist_triangle[of B C A]
    by (intro mult_nonneg_nonneg) (auto simp: s_def a_def b_def c_def dist_commute)

  have "16 * content (convex hull {A, B, C}) ^ 2 =
          4 * ((C $ 1 - A $ 1) * (B $ 2 - A $ 2) - (B $ 1 - A $ 1) * (C $ 2 - A $ 2)) ^ 2"
    by (subst content_triangle) (simp add: power_divide)
  also have "\<dots> = (2 * (dist A B ^ 2 * dist A C ^ 2 + dist A B ^ 2 * dist B C ^ 2 + 
      dist A C ^ 2 * dist B C ^ 2) - (dist A B ^ 2) ^ 2 - (dist A C ^ 2) ^ 2 - (dist B C ^ 2) ^ 2)"
    unfolding dist_eq unfolding power2_eq_square by algebra
  also have "\<dots> = (a + b + c) * ((a + b + c) - 2 * a) * ((a + b + c) - 2 * b) *
                    ((a + b + c) - 2 * c)"
    unfolding power2_eq_square by (simp add: s_def a_def b_def c_def algebra_simps)
  also have "\<dots> = 16 * s * (s - a) * (s - b) * (s - c)"
    by (simp add: s_def field_split_simps)
  finally have "content (convex hull {A, B, C}) ^ 2 = s * (s - a) * (s - b) * (s - c)"
    by simp
  also have "\<dots> = sqrt (s * (s - a) * (s - b) * (s - c)) ^ 2"
    by (intro real_sqrt_pow2 [symmetric] nonneg)
  finally show ?thesis using nonneg
    by (subst (asm) power2_eq_iff_nonneg) auto
qed

end
