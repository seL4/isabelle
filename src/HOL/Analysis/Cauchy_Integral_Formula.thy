section \<open>Cauchy's Integral Formula\<close>

theory Cauchy_Integral_Formula
  imports Winding_Numbers
begin

subsection\<open>Cauchy's integral formula, again for a convex enclosing set\<close>

lemma Cauchy_integral_formula_weak:
    assumes s: "convex s" and "finite k" and conf: "continuous_on s f"
        and fcd: "(\<And>x. x \<in> interior s - k \<Longrightarrow> f field_differentiable at x)"
        and z: "z \<in> interior s - k" and vpg: "valid_path \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> s - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  obtain f' where f': "(f has_field_derivative f') (at z)"
    using fcd [OF z] by (auto simp: field_differentiable_def)
  have pas: "path_image \<gamma> \<subseteq> s" and znotin: "z \<notin> path_image \<gamma>" using pasz by blast+
  have c: "continuous (at x within s) (\<lambda>w. if w = z then f' else (f w - f z) / (w - z))" if "x \<in> s" for x
  proof (cases "x = z")
    case True then show ?thesis
      apply (simp add: continuous_within)
      apply (rule Lim_transform_away_within [of _ "z+1" _ "\<lambda>w::complex. (f w - f z)/(w - z)"])
      using has_field_derivative_at_within has_field_derivative_iff f'
      apply (fastforce simp add:)+
      done
  next
    case False
    then have dxz: "dist x z > 0" by auto
    have cf: "continuous (at x within s) f"
      using conf continuous_on_eq_continuous_within that by blast
    have "continuous (at x within s) (\<lambda>w. (f w - f z) / (w - z))"
      by (rule cf continuous_intros | simp add: False)+
    then show ?thesis
      apply (rule continuous_transform_within [OF _ dxz that, of "\<lambda>w::complex. (f w - f z)/(w - z)"])
      apply (force simp: dist_commute)
      done
  qed
  have fink': "finite (insert z k)" using \<open>finite k\<close> by blast
  have *: "((\<lambda>w. if w = z then f' else (f w - f z) / (w - z)) has_contour_integral 0) \<gamma>"
    apply (rule Cauchy_theorem_convex [OF _ s fink' _ vpg pas loop])
    using c apply (force simp: continuous_on_eq_continuous_within)
    apply (rename_tac w)
    apply (rule_tac d="dist w z" and f = "\<lambda>w. (f w - f z)/(w - z)" in field_differentiable_transform_within)
    apply (simp_all add: dist_pos_lt dist_commute)
    apply (metis less_irrefl)
    apply (rule derivative_intros fcd | simp)+
    done
  show ?thesis
    apply (rule has_contour_integral_eq)
    using znotin has_contour_integral_add [OF has_contour_integral_lmul [OF has_contour_integral_winding_number [OF vpg znotin], of "f z"] *]
    apply (auto simp: ac_simps divide_simps)
    done
qed

text\<open> Hence the Cauchy formula for points inside a circle.\<close>

theorem Cauchy_integral_circlepath:
  assumes contf: "continuous_on (cball z r) f" and holf: "f holomorphic_on (ball z r)" and wz: "norm(w - z) < r"
  shows "((\<lambda>u. f u/(u - w)) has_contour_integral (2 * of_real pi * \<i> * f w))
         (circlepath z r)"
proof -
  have "r > 0"
    using assms le_less_trans norm_ge_zero by blast
  have "((\<lambda>u. f u / (u - w)) has_contour_integral (2 * pi) * \<i> * winding_number (circlepath z r) w * f w)
        (circlepath z r)"
  proof (rule Cauchy_integral_formula_weak [where s = "cball z r" and k = "{}"])
    show "\<And>x. x \<in> interior (cball z r) - {} \<Longrightarrow>
         f field_differentiable at x"
      using holf holomorphic_on_imp_differentiable_at by auto
    have "w \<notin> sphere z r"
      by simp (metis dist_commute dist_norm not_le order_refl wz)
    then show "path_image (circlepath z r) \<subseteq> cball z r - {w}"
      using \<open>r > 0\<close> by (auto simp add: cball_def sphere_def)
  qed (use wz in \<open>simp_all add: dist_norm norm_minus_commute contf\<close>)
  then show ?thesis
    by (simp add: winding_number_circlepath assms)
qed

theorem Cauchy_integral_formula_convex_simple:
    "\<lbrakk>convex s; f holomorphic_on s; z \<in> interior s; valid_path \<gamma>; path_image \<gamma> \<subseteq> s - {z};
      pathfinish \<gamma> = pathstart \<gamma>\<rbrakk>
     \<Longrightarrow> ((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
  apply (rule Cauchy_integral_formula_weak [where k = "{}"])
  using holomorphic_on_imp_continuous_on
  by auto (metis at_within_interior holomorphic_on_def interiorE subsetCE)

corollary\<^marker>\<open>tag unimportant\<close> Cauchy_integral_circlepath_simple:
  assumes "f holomorphic_on cball z r" "norm(w - z) < r"
  shows "((\<lambda>u. f u/(u - w)) has_contour_integral (2 * of_real pi * \<i> * f w))
         (circlepath z r)"
using assms by (force simp: holomorphic_on_imp_continuous_on holomorphic_on_subset Cauchy_integral_circlepath)

text\<open> In particular, the first derivative formula.\<close>

lemma Cauchy_derivative_integral_circlepath:
  assumes contf: "continuous_on (cball z r) f"
      and holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "(\<lambda>u. f u/(u - w)^2) contour_integrable_on (circlepath z r)"
           (is "?thes1")
      and "(f has_field_derivative (1 / (2 * of_real pi * \<i>) * contour_integral(circlepath z r) (\<lambda>u. f u / (u - w)^2))) (at w)"
           (is "?thes2")
proof -
  have [simp]: "r \<ge> 0" using w
    using ball_eq_empty by fastforce
  have f: "continuous_on (path_image (circlepath z r)) f"
    by (rule continuous_on_subset [OF contf]) (force simp: cball_def sphere_def)
  have int: "\<And>w. dist z w < r \<Longrightarrow>
                 ((\<lambda>u. f u / (u - w)) has_contour_integral (\<lambda>x. 2 * of_real pi * \<i> * f x) w) (circlepath z r)"
    by (rule Cauchy_integral_circlepath [OF contf holf]) (simp add: dist_norm norm_minus_commute)
  show ?thes1
    apply (simp add: power2_eq_square)
    apply (rule Cauchy_next_derivative_circlepath [OF f _ _ w, where k=1, simplified])
    apply (blast intro: int)
    done
  have "((\<lambda>x. 2 * of_real pi * \<i> * f x) has_field_derivative contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)^2)) (at w)"
    apply (simp add: power2_eq_square)
    apply (rule Cauchy_next_derivative_circlepath [OF f _ _ w, where k=1 and g = "\<lambda>x. 2 * of_real pi * \<i> * f x", simplified])
    apply (blast intro: int)
    done
  then have fder: "(f has_field_derivative contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)^2) / (2 * of_real pi * \<i>)) (at w)"
    by (rule DERIV_cdivide [where f = "\<lambda>x. 2 * of_real pi * \<i> * f x" and c = "2 * of_real pi * \<i>", simplified])
  show ?thes2
    by simp (rule fder)
qed


proposition derivative_is_holomorphic:
  assumes "open S"
      and fder: "\<And>z. z \<in> S \<Longrightarrow> (f has_field_derivative f' z) (at z)"
    shows "f' holomorphic_on S"
proof -
  have *: "\<exists>h. (f' has_field_derivative h) (at z)" if "z \<in> S" for z
  proof -
    obtain r where "r > 0" and r: "cball z r \<subseteq> S"
      using open_contains_cball \<open>z \<in> S\<close> \<open>open S\<close> by blast
    then have holf_cball: "f holomorphic_on cball z r"
      apply (simp add: holomorphic_on_def)
      using field_differentiable_at_within field_differentiable_def fder by blast
    then have "continuous_on (path_image (circlepath z r)) f"
      using \<open>r > 0\<close> by (force elim: holomorphic_on_subset [THEN holomorphic_on_imp_continuous_on])
    then have contfpi: "continuous_on (path_image (circlepath z r)) (\<lambda>x. 1/(2 * of_real pi*\<i>) * f x)"
      by (auto intro: continuous_intros)+
    have contf_cball: "continuous_on (cball z r) f" using holf_cball
      by (simp add: holomorphic_on_imp_continuous_on holomorphic_on_subset)
    have holf_ball: "f holomorphic_on ball z r" using holf_cball
      using ball_subset_cball holomorphic_on_subset by blast
    { fix w  assume w: "w \<in> ball z r"
      have intf: "(\<lambda>u. f u / (u - w)\<^sup>2) contour_integrable_on circlepath z r"
        by (blast intro: w Cauchy_derivative_integral_circlepath [OF contf_cball holf_ball])
      have fder': "(f has_field_derivative 1 / (2 * of_real pi * \<i>) * contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2))
                  (at w)"
        by (blast intro: w Cauchy_derivative_integral_circlepath [OF contf_cball holf_ball])
      have f'_eq: "f' w = contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2) / (2 * of_real pi * \<i>)"
        using fder' ball_subset_cball r w by (force intro: DERIV_unique [OF fder])
      have "((\<lambda>u. f u / (u - w)\<^sup>2 / (2 * of_real pi * \<i>)) has_contour_integral
                contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2) / (2 * of_real pi * \<i>))
                (circlepath z r)"
        by (rule has_contour_integral_div [OF has_contour_integral_integral [OF intf]])
      then have "((\<lambda>u. f u / (2 * of_real pi * \<i> * (u - w)\<^sup>2)) has_contour_integral
                contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2) / (2 * of_real pi * \<i>))
                (circlepath z r)"
        by (simp add: algebra_simps)
      then have "((\<lambda>u. f u / (2 * of_real pi * \<i> * (u - w)\<^sup>2)) has_contour_integral f' w) (circlepath z r)"
        by (simp add: f'_eq)
    } note * = this
    show ?thesis
      apply (rule exI)
      apply (rule Cauchy_next_derivative_circlepath [OF contfpi, of 2 f', simplified])
      apply (simp_all add: \<open>0 < r\<close> * dist_norm)
      done
  qed
  show ?thesis
    by (simp add: holomorphic_on_open [OF \<open>open S\<close>] *)
qed


subsection\<open>Existence of all higher derivatives\<close>

lemma holomorphic_deriv [holomorphic_intros]:
    "\<lbrakk>f holomorphic_on S; open S\<rbrakk> \<Longrightarrow> (deriv f) holomorphic_on S"
  by (metis DERIV_deriv_iff_field_differentiable at_within_open derivative_is_holomorphic holomorphic_on_def)

lemma analytic_deriv [analytic_intros]: "f analytic_on S \<Longrightarrow> (deriv f) analytic_on S"
  using analytic_on_holomorphic holomorphic_deriv by auto

lemma holomorphic_higher_deriv [holomorphic_intros]: "\<lbrakk>f holomorphic_on S; open S\<rbrakk> \<Longrightarrow> (deriv ^^ n) f holomorphic_on S"
  by (induction n) (auto simp: holomorphic_deriv)

lemma analytic_higher_deriv [analytic_intros]: "f analytic_on S \<Longrightarrow> (deriv ^^ n) f analytic_on S"
  unfolding analytic_on_def using holomorphic_higher_deriv by blast

lemma has_field_derivative_higher_deriv:
     "\<lbrakk>f holomorphic_on S; open S; x \<in> S\<rbrakk>
      \<Longrightarrow> ((deriv ^^ n) f has_field_derivative (deriv ^^ (Suc n)) f x) (at x)"
by (metis (no_types, hide_lams) DERIV_deriv_iff_field_differentiable at_within_open comp_apply
         funpow.simps(2) holomorphic_higher_deriv holomorphic_on_def)

lemma valid_path_compose_holomorphic:
  assumes "valid_path g" and holo:"f holomorphic_on S" and "open S" "path_image g \<subseteq> S"
  shows "valid_path (f \<circ> g)"
proof (rule valid_path_compose[OF \<open>valid_path g\<close>])
  fix x assume "x \<in> path_image g"
  then show "f field_differentiable at x"
    using analytic_on_imp_differentiable_at analytic_on_open assms holo by blast
next
  have "deriv f holomorphic_on S"
    using holomorphic_deriv holo \<open>open S\<close> by auto
  then show "continuous_on (path_image g) (deriv f)"
    using assms(4) holomorphic_on_imp_continuous_on holomorphic_on_subset by auto
qed

proposition\<^marker>\<open>tag unimportant\<close> holomorphic_logarithm_exists:
  assumes A: "convex A" "open A"
      and f: "f holomorphic_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
      and z0: "z0 \<in> A"
    obtains g where "g holomorphic_on A" and "\<And>x. x \<in> A \<Longrightarrow> exp (g x) = f x"
proof -
  note f' = holomorphic_derivI [OF f(1) A(2)]
  obtain g where g: "\<And>x. x \<in> A \<Longrightarrow> (g has_field_derivative deriv f x / f x) (at x)"
  proof (rule holomorphic_convex_primitive' [OF A])
    show "(\<lambda>x. deriv f x / f x) holomorphic_on A"
      by (intro holomorphic_intros f A)
  qed (auto simp: A at_within_open[of _ A])
  define h where "h = (\<lambda>x. -g z0 + ln (f z0) + g x)"
  from g and A have g_holo: "g holomorphic_on A"
    by (auto simp: holomorphic_on_def at_within_open[of _ A] field_differentiable_def)
  hence h_holo: "h holomorphic_on A"
    by (auto simp: h_def intro!: holomorphic_intros)
  have "\<exists>c. \<forall>x\<in>A. f x / exp (h x) - 1 = c"
  proof (rule has_field_derivative_zero_constant, goal_cases)
    case (2 x)
    note [simp] = at_within_open[OF _ \<open>open A\<close>]
    from 2 and z0 and f show ?case
      by (auto simp: h_def exp_diff field_simps intro!: derivative_eq_intros g f')
  qed fact+
  then obtain c where c: "\<And>x. x \<in> A \<Longrightarrow> f x / exp (h x) - 1 = c"
    by blast
  from c[OF z0] and z0 and f have "c = 0"
    by (simp add: h_def)
  with c have "\<And>x. x \<in> A \<Longrightarrow> exp (h x) = f x" by simp
  from that[OF h_holo this] show ?thesis .
qed

subsection\<open>Morera's theorem\<close>

lemma Morera_local_triangle_ball:
  assumes "\<And>z. z \<in> S
          \<Longrightarrow> \<exists>e a. 0 < e \<and> z \<in> ball a e \<and> continuous_on (ball a e) f \<and>
                    (\<forall>b c. closed_segment b c \<subseteq> ball a e
                           \<longrightarrow> contour_integral (linepath a b) f +
                               contour_integral (linepath b c) f +
                               contour_integral (linepath c a) f = 0)"
  shows "f analytic_on S"
proof -
  { fix z  assume "z \<in> S"
    with assms obtain e a where
            "0 < e" and z: "z \<in> ball a e" and contf: "continuous_on (ball a e) f"
        and 0: "\<And>b c. closed_segment b c \<subseteq> ball a e
                      \<Longrightarrow> contour_integral (linepath a b) f +
                          contour_integral (linepath b c) f +
                          contour_integral (linepath c a) f = 0"
      by fastforce
    have az: "dist a z < e" using mem_ball z by blast
    have sb_ball: "ball z (e - dist a z) \<subseteq> ball a e"
      by (simp add: dist_commute ball_subset_ball_iff)
    have "\<exists>e>0. f holomorphic_on ball z e"
    proof (intro exI conjI)
      have sub_ball: "\<And>y. dist a y < e \<Longrightarrow> closed_segment a y \<subseteq> ball a e"
        by (meson \<open>0 < e\<close> centre_in_ball convex_ball convex_contains_segment mem_ball)
      show "f holomorphic_on ball z (e - dist a z)"
        apply (rule holomorphic_on_subset [OF _ sb_ball])
        apply (rule derivative_is_holomorphic[OF open_ball])
        apply (rule triangle_contour_integrals_starlike_primitive [OF contf _ open_ball, of a])
           apply (simp_all add: 0 \<open>0 < e\<close> sub_ball)
        done
    qed (simp add: az)
  }
  then show ?thesis
    by (simp add: analytic_on_def)
qed

lemma Morera_local_triangle:
  assumes "\<And>z. z \<in> S
          \<Longrightarrow> \<exists>t. open t \<and> z \<in> t \<and> continuous_on t f \<and>
                  (\<forall>a b c. convex hull {a,b,c} \<subseteq> t
                              \<longrightarrow> contour_integral (linepath a b) f +
                                  contour_integral (linepath b c) f +
                                  contour_integral (linepath c a) f = 0)"
  shows "f analytic_on S"
proof -
  { fix z  assume "z \<in> S"
    with assms obtain t where
            "open t" and z: "z \<in> t" and contf: "continuous_on t f"
        and 0: "\<And>a b c. convex hull {a,b,c} \<subseteq> t
                      \<Longrightarrow> contour_integral (linepath a b) f +
                          contour_integral (linepath b c) f +
                          contour_integral (linepath c a) f = 0"
      by force
    then obtain e where "e>0" and e: "ball z e \<subseteq> t"
      using open_contains_ball by blast
    have [simp]: "continuous_on (ball z e) f" using contf
      using continuous_on_subset e by blast
    have eq0: "\<And>b c. closed_segment b c \<subseteq> ball z e \<Longrightarrow>
                         contour_integral (linepath z b) f +
                         contour_integral (linepath b c) f +
                         contour_integral (linepath c z) f = 0"
      by (meson 0 z \<open>0 < e\<close> centre_in_ball closed_segment_subset convex_ball dual_order.trans e starlike_convex_subset)
    have "\<exists>e a. 0 < e \<and> z \<in> ball a e \<and> continuous_on (ball a e) f \<and>
                (\<forall>b c. closed_segment b c \<subseteq> ball a e \<longrightarrow>
                       contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c a) f = 0)"
      using \<open>e > 0\<close> eq0 by force
  }
  then show ?thesis
    by (simp add: Morera_local_triangle_ball)
qed

proposition Morera_triangle:
    "\<lbrakk>continuous_on S f; open S;
      \<And>a b c. convex hull {a,b,c} \<subseteq> S
              \<longrightarrow> contour_integral (linepath a b) f +
                  contour_integral (linepath b c) f +
                  contour_integral (linepath c a) f = 0\<rbrakk>
     \<Longrightarrow> f analytic_on S"
  using Morera_local_triangle by blast

subsection\<open>Combining theorems for higher derivatives including Leibniz rule\<close>

lemma higher_deriv_linear [simp]:
    "(deriv ^^ n) (\<lambda>w. c*w) = (\<lambda>z. if n = 0 then c*z else if n = 1 then c else 0)"
  by (induction n) auto

lemma higher_deriv_const [simp]: "(deriv ^^ n) (\<lambda>w. c) = (\<lambda>w. if n=0 then c else 0)"
  by (induction n) auto

lemma higher_deriv_ident [simp]:
     "(deriv ^^ n) (\<lambda>w. w) z = (if n = 0 then z else if n = 1 then 1 else 0)"
  apply (induction n, simp)
  apply (metis higher_deriv_linear lambda_one)
  done

lemma higher_deriv_id [simp]:
     "(deriv ^^ n) id z = (if n = 0 then z else if n = 1 then 1 else 0)"
  by (simp add: id_def)

lemma has_complex_derivative_funpow_1:
     "\<lbrakk>(f has_field_derivative 1) (at z); f z = z\<rbrakk> \<Longrightarrow> (f^^n has_field_derivative 1) (at z)"
  apply (induction n, auto)
  apply (simp add: id_def)
  by (metis DERIV_chain comp_funpow comp_id funpow_swap1 mult.right_neutral)

lemma higher_deriv_uminus:
  assumes "f holomorphic_on S" "open S" and z: "z \<in> S"
    shows "(deriv ^^ n) (\<lambda>w. -(f w)) z = - ((deriv ^^ n) f z)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have *: "((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) z) (at z)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  have "((deriv ^^ n) (\<lambda>w. - f w) has_field_derivative - deriv ((deriv ^^ n) f) z) (at z)"
    apply (rule has_field_derivative_transform_within_open [of "\<lambda>w. -((deriv ^^ n) f w)"])
       apply (rule derivative_eq_intros | rule * refl assms)+
     apply (auto simp add: Suc)
    done
  then show ?case
    by (simp add: DERIV_imp_deriv)
qed

lemma higher_deriv_add:
  fixes z::complex
  assumes "f holomorphic_on S" "g holomorphic_on S" "open S" and z: "z \<in> S"
    shows "(deriv ^^ n) (\<lambda>w. f w + g w) z = (deriv ^^ n) f z + (deriv ^^ n) g z"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have *: "((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) z) (at z)"
          "((deriv ^^ n) g has_field_derivative deriv ((deriv ^^ n) g) z) (at z)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  have "((deriv ^^ n) (\<lambda>w. f w + g w) has_field_derivative
        deriv ((deriv ^^ n) f) z + deriv ((deriv ^^ n) g) z) (at z)"
    apply (rule has_field_derivative_transform_within_open [of "\<lambda>w. (deriv ^^ n) f w + (deriv ^^ n) g w"])
       apply (rule derivative_eq_intros | rule * refl assms)+
     apply (auto simp add: Suc)
    done
  then show ?case
    by (simp add: DERIV_imp_deriv)
qed

lemma higher_deriv_diff:
  fixes z::complex
  assumes "f holomorphic_on S" "g holomorphic_on S" "open S" and z: "z \<in> S"
    shows "(deriv ^^ n) (\<lambda>w. f w - g w) z = (deriv ^^ n) f z - (deriv ^^ n) g z"
  apply (simp only: Groups.group_add_class.diff_conv_add_uminus higher_deriv_add)
  apply (subst higher_deriv_add)
  using assms holomorphic_on_minus apply (auto simp: higher_deriv_uminus)
  done

lemma bb: "Suc n choose k = (n choose k) + (if k = 0 then 0 else (n choose (k - 1)))"
  by (cases k) simp_all

lemma higher_deriv_mult:
  fixes z::complex
  assumes "f holomorphic_on S" "g holomorphic_on S" "open S" and z: "z \<in> S"
    shows "(deriv ^^ n) (\<lambda>w. f w * g w) z =
           (\<Sum>i = 0..n. of_nat (n choose i) * (deriv ^^ i) f z * (deriv ^^ (n - i)) g z)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have *: "\<And>n. ((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) z) (at z)"
          "\<And>n. ((deriv ^^ n) g has_field_derivative deriv ((deriv ^^ n) g) z) (at z)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  have sumeq: "(\<Sum>i = 0..n.
               of_nat (n choose i) * (deriv ((deriv ^^ i) f) z * (deriv ^^ (n - i)) g z + deriv ((deriv ^^ (n - i)) g) z * (deriv ^^ i) f z)) =
            g z * deriv ((deriv ^^ n) f) z + (\<Sum>i = 0..n. (deriv ^^ i) f z * (of_nat (Suc n choose i) * (deriv ^^ (Suc n - i)) g z))"
    apply (simp add: bb algebra_simps sum.distrib)
    apply (subst (4) sum_Suc_reindex)
    apply (auto simp: algebra_simps Suc_diff_le intro: sum.cong)
    done
  have "((deriv ^^ n) (\<lambda>w. f w * g w) has_field_derivative
         (\<Sum>i = 0..Suc n. (Suc n choose i) * (deriv ^^ i) f z * (deriv ^^ (Suc n - i)) g z))
        (at z)"
    apply (rule has_field_derivative_transform_within_open
        [of "\<lambda>w. (\<Sum>i = 0..n. of_nat (n choose i) * (deriv ^^ i) f w * (deriv ^^ (n - i)) g w)"])
       apply (simp add: algebra_simps)
       apply (rule DERIV_cong [OF DERIV_sum])
        apply (rule DERIV_cmult)
        apply (auto intro: DERIV_mult * sumeq \<open>open S\<close> Suc.prems Suc.IH [symmetric])
    done
  then show ?case
    unfolding funpow.simps o_apply
    by (simp add: DERIV_imp_deriv)
qed

lemma higher_deriv_transform_within_open:
  fixes z::complex
  assumes "f holomorphic_on S" "g holomorphic_on S" "open S" and z: "z \<in> S"
      and fg: "\<And>w. w \<in> S \<Longrightarrow> f w = g w"
    shows "(deriv ^^ i) f z = (deriv ^^ i) g z"
using z
by (induction i arbitrary: z)
   (auto simp: fg intro: complex_derivative_transform_within_open holomorphic_higher_deriv assms)

lemma higher_deriv_compose_linear:
  fixes z::complex
  assumes f: "f holomorphic_on T" and S: "open S" and T: "open T" and z: "z \<in> S"
      and fg: "\<And>w. w \<in> S \<Longrightarrow> u * w \<in> T"
    shows "(deriv ^^ n) (\<lambda>w. f (u * w)) z = u^n * (deriv ^^ n) f (u * z)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have holo0: "f holomorphic_on (*) u ` S"
    by (meson fg f holomorphic_on_subset image_subset_iff)
  have holo2: "(deriv ^^ n) f holomorphic_on (*) u ` S"
    by (meson f fg holomorphic_higher_deriv holomorphic_on_subset image_subset_iff T)
  have holo3: "(\<lambda>z. u ^ n * (deriv ^^ n) f (u * z)) holomorphic_on S"
    by (intro holo2 holomorphic_on_compose [where g="(deriv ^^ n) f", unfolded o_def] holomorphic_intros)
  have holo1: "(\<lambda>w. f (u * w)) holomorphic_on S"
    apply (rule holomorphic_on_compose [where g=f, unfolded o_def])
    apply (rule holo0 holomorphic_intros)+
    done
  have "deriv ((deriv ^^ n) (\<lambda>w. f (u * w))) z = deriv (\<lambda>z. u^n * (deriv ^^ n) f (u*z)) z"
    apply (rule complex_derivative_transform_within_open [OF _ holo3 S Suc.prems])
    apply (rule holomorphic_higher_deriv [OF holo1 S])
    apply (simp add: Suc.IH)
    done
  also have "\<dots> = u^n * deriv (\<lambda>z. (deriv ^^ n) f (u * z)) z"
    apply (rule deriv_cmult)
    apply (rule analytic_on_imp_differentiable_at [OF _ Suc.prems])
    apply (rule analytic_on_compose_gen [where g="(deriv ^^ n) f" and T=T, unfolded o_def])
      apply (simp)
     apply (simp add: analytic_on_open f holomorphic_higher_deriv T)
    apply (blast intro: fg)
    done
  also have "\<dots> = u * u ^ n * deriv ((deriv ^^ n) f) (u * z)"
      apply (subst complex_derivative_chain [where g = "(deriv ^^ n) f" and f = "(*) u", unfolded o_def])
      apply (rule derivative_intros)
      using Suc.prems field_differentiable_def f fg has_field_derivative_higher_deriv T apply blast
      apply (simp)
      done
  finally show ?case
    by simp
qed

lemma higher_deriv_add_at:
  assumes "f analytic_on {z}" "g analytic_on {z}"
    shows "(deriv ^^ n) (\<lambda>w. f w + g w) z = (deriv ^^ n) f z + (deriv ^^ n) g z"
proof -
  have "f analytic_on {z} \<and> g analytic_on {z}"
    using assms by blast
  with higher_deriv_add show ?thesis
    by (auto simp: analytic_at_two)
qed

lemma higher_deriv_diff_at:
  assumes "f analytic_on {z}" "g analytic_on {z}"
    shows "(deriv ^^ n) (\<lambda>w. f w - g w) z = (deriv ^^ n) f z - (deriv ^^ n) g z"
proof -
  have "f analytic_on {z} \<and> g analytic_on {z}"
    using assms by blast
  with higher_deriv_diff show ?thesis
    by (auto simp: analytic_at_two)
qed

lemma higher_deriv_uminus_at:
   "f analytic_on {z}  \<Longrightarrow> (deriv ^^ n) (\<lambda>w. -(f w)) z = - ((deriv ^^ n) f z)"
  using higher_deriv_uminus
    by (auto simp: analytic_at)

lemma higher_deriv_mult_at:
  assumes "f analytic_on {z}" "g analytic_on {z}"
    shows "(deriv ^^ n) (\<lambda>w. f w * g w) z =
           (\<Sum>i = 0..n. of_nat (n choose i) * (deriv ^^ i) f z * (deriv ^^ (n - i)) g z)"
proof -
  have "f analytic_on {z} \<and> g analytic_on {z}"
    using assms by blast
  with higher_deriv_mult show ?thesis
    by (auto simp: analytic_at_two)
qed


text\<open> Nonexistence of isolated singularities and a stronger integral formula.\<close>

proposition no_isolated_singularity:
  fixes z::complex
  assumes f: "continuous_on S f" and holf: "f holomorphic_on (S - K)" and S: "open S" and K: "finite K"
    shows "f holomorphic_on S"
proof -
  { fix z
    assume "z \<in> S" and cdf: "\<And>x. x \<in> S - K \<Longrightarrow> f field_differentiable at x"
    have "f field_differentiable at z"
    proof (cases "z \<in> K")
      case False then show ?thesis by (blast intro: cdf \<open>z \<in> S\<close>)
    next
      case True
      with finite_set_avoid [OF K, of z]
      obtain d where "d>0" and d: "\<And>x. \<lbrakk>x\<in>K; x \<noteq> z\<rbrakk> \<Longrightarrow> d \<le> dist z x"
        by blast
      obtain e where "e>0" and e: "ball z e \<subseteq> S"
        using  S \<open>z \<in> S\<close> by (force simp: open_contains_ball)
      have fde: "continuous_on (ball z (min d e)) f"
        by (metis Int_iff ball_min_Int continuous_on_subset e f subsetI)
      have cont: "{a,b,c} \<subseteq> ball z (min d e) \<Longrightarrow> continuous_on (convex hull {a, b, c}) f" for a b c
        by (simp add: hull_minimal continuous_on_subset [OF fde])
      have fd: "\<lbrakk>{a,b,c} \<subseteq> ball z (min d e); x \<in> interior (convex hull {a, b, c}) - K\<rbrakk>
            \<Longrightarrow> f field_differentiable at x" for a b c x
        by (metis cdf Diff_iff Int_iff ball_min_Int subsetD convex_ball e interior_mono interior_subset subset_hull)
      obtain g where "\<And>w. w \<in> ball z (min d e) \<Longrightarrow> (g has_field_derivative f w) (at w within ball z (min d e))"
        apply (rule contour_integral_convex_primitive
                     [OF convex_ball fde Cauchy_theorem_triangle_cofinite [OF _ K]])
        using cont fd by auto
      then have "f holomorphic_on ball z (min d e)"
        by (metis open_ball at_within_open derivative_is_holomorphic)
      then show ?thesis
        unfolding holomorphic_on_def
        by (metis open_ball \<open>0 < d\<close> \<open>0 < e\<close> at_within_open centre_in_ball min_less_iff_conj)
    qed
  }
  with holf S K show ?thesis
    by (simp add: holomorphic_on_open open_Diff finite_imp_closed field_differentiable_def [symmetric])
qed

lemma no_isolated_singularity':
  fixes z::complex
  assumes f: "\<And>z. z \<in> K \<Longrightarrow> (f \<longlongrightarrow> f z) (at z within S)"
      and holf: "f holomorphic_on (S - K)" and S: "open S" and K: "finite K"
    shows "f holomorphic_on S"
proof (rule no_isolated_singularity[OF _ assms(2-)])
  show "continuous_on S f" unfolding continuous_on_def
  proof
    fix z assume z: "z \<in> S"
    show "(f \<longlongrightarrow> f z) (at z within S)"
    proof (cases "z \<in> K")
      case False
      from holf have "continuous_on (S - K) f"
        by (rule holomorphic_on_imp_continuous_on)
      with z False have "(f \<longlongrightarrow> f z) (at z within (S - K))"
        by (simp add: continuous_on_def)
      also from z K S False have "at z within (S - K) = at z within S"
        by (subst (1 2) at_within_open) (auto intro: finite_imp_closed)
      finally show "(f \<longlongrightarrow> f z) (at z within S)" .
    qed (insert assms z, simp_all)
  qed
qed

proposition Cauchy_integral_formula_convex:
  assumes S: "convex S" and K: "finite K" and contf: "continuous_on S f"
    and fcd: "(\<And>x. x \<in> interior S - K \<Longrightarrow> f field_differentiable at x)"
    and z: "z \<in> interior S" and vpg: "valid_path \<gamma>"
    and pasz: "path_image \<gamma> \<subseteq> S - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
  shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  have *: "\<And>x. x \<in> interior S \<Longrightarrow> f field_differentiable at x"
    unfolding holomorphic_on_open [symmetric] field_differentiable_def
    using no_isolated_singularity [where S = "interior S"]
    by (meson K contf continuous_at_imp_continuous_on continuous_on_interior fcd
          field_differentiable_at_within field_differentiable_def holomorphic_onI
          holomorphic_on_imp_differentiable_at open_interior)
  show ?thesis
    by (rule Cauchy_integral_formula_weak [OF S finite.emptyI contf]) (use * assms in auto)
qed

text\<open> Formula for higher derivatives.\<close>

lemma Cauchy_has_contour_integral_higher_derivative_circlepath:
  assumes contf: "continuous_on (cball z r) f"
      and holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "((\<lambda>u. f u / (u - w) ^ (Suc k)) has_contour_integral ((2 * pi * \<i>) / (fact k) * (deriv ^^ k) f w))
           (circlepath z r)"
using w
proof (induction k arbitrary: w)
  case 0 then show ?case
    using assms by (auto simp: Cauchy_integral_circlepath dist_commute dist_norm)
next
  case (Suc k)
  have [simp]: "r > 0" using w
    using ball_eq_empty by fastforce
  have f: "continuous_on (path_image (circlepath z r)) f"
    by (rule continuous_on_subset [OF contf]) (force simp: cball_def sphere_def less_imp_le)
  obtain X where X: "((\<lambda>u. f u / (u - w) ^ Suc (Suc k)) has_contour_integral X) (circlepath z r)"
    using Cauchy_next_derivative_circlepath(1) [OF f Suc.IH _ Suc.prems]
    by (auto simp: contour_integrable_on_def)
  then have con: "contour_integral (circlepath z r) ((\<lambda>u. f u / (u - w) ^ Suc (Suc k))) = X"
    by (rule contour_integral_unique)
  have "\<And>n. ((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) w) (at w)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  then have dnf_diff: "\<And>n. (deriv ^^ n) f field_differentiable (at w)"
    by (force simp: field_differentiable_def)
  have "deriv (\<lambda>w. complex_of_real (2 * pi) * \<i> / (fact k) * (deriv ^^ k) f w) w =
          of_nat (Suc k) * contour_integral (circlepath z r) (\<lambda>u. f u / (u - w) ^ Suc (Suc k))"
    by (force intro!: DERIV_imp_deriv Cauchy_next_derivative_circlepath [OF f Suc.IH _ Suc.prems])
  also have "\<dots> = of_nat (Suc k) * X"
    by (simp only: con)
  finally have "deriv (\<lambda>w. ((2 * pi) * \<i> / (fact k)) * (deriv ^^ k) f w) w = of_nat (Suc k) * X" .
  then have "((2 * pi) * \<i> / (fact k)) * deriv (\<lambda>w. (deriv ^^ k) f w) w = of_nat (Suc k) * X"
    by (metis deriv_cmult dnf_diff)
  then have "deriv (\<lambda>w. (deriv ^^ k) f w) w = of_nat (Suc k) * X / ((2 * pi) * \<i> / (fact k))"
    by (simp add: field_simps)
  then show ?case
  using of_nat_eq_0_iff X by fastforce
qed

lemma Cauchy_higher_derivative_integral_circlepath:
  assumes contf: "continuous_on (cball z r) f"
      and holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "(\<lambda>u. f u / (u - w)^(Suc k)) contour_integrable_on (circlepath z r)"
           (is "?thes1")
      and "(deriv ^^ k) f w = (fact k) / (2 * pi * \<i>) * contour_integral(circlepath z r) (\<lambda>u. f u/(u - w)^(Suc k))"
           (is "?thes2")
proof -
  have *: "((\<lambda>u. f u / (u - w) ^ Suc k) has_contour_integral (2 * pi) * \<i> / (fact k) * (deriv ^^ k) f w)
           (circlepath z r)"
    using Cauchy_has_contour_integral_higher_derivative_circlepath [OF assms]
    by simp
  show ?thes1 using *
    using contour_integrable_on_def by blast
  show ?thes2
    unfolding contour_integral_unique [OF *] by (simp add: field_split_simps)
qed

corollary Cauchy_contour_integral_circlepath:
  assumes "continuous_on (cball z r) f" "f holomorphic_on ball z r" "w \<in> ball z r"
    shows "contour_integral(circlepath z r) (\<lambda>u. f u/(u - w)^(Suc k)) = (2 * pi * \<i>) * (deriv ^^ k) f w / (fact k)"
by (simp add: Cauchy_higher_derivative_integral_circlepath [OF assms])

lemma Cauchy_contour_integral_circlepath_2:
  assumes "continuous_on (cball z r) f" "f holomorphic_on ball z r" "w \<in> ball z r"
    shows "contour_integral(circlepath z r) (\<lambda>u. f u/(u - w)^2) = (2 * pi * \<i>) * deriv f w"
  using Cauchy_contour_integral_circlepath [OF assms, of 1]
  by (simp add: power2_eq_square)


subsection\<open>A holomorphic function is analytic, i.e. has local power series\<close>

theorem holomorphic_power_series:
  assumes holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "((\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n) sums f w)"
proof -
  \<comment> \<open>Replacing \<^term>\<open>r\<close> and the original (weak) premises with stronger ones\<close>
  obtain r where "r > 0" and holfc: "f holomorphic_on cball z r" and w: "w \<in> ball z r"
  proof
    have "cball z ((r + dist w z) / 2) \<subseteq> ball z r"
      using w by (simp add: dist_commute field_sum_of_halves subset_eq)
    then show "f holomorphic_on cball z ((r + dist w z) / 2)"
      by (rule holomorphic_on_subset [OF holf])
    have "r > 0"
      using w by clarsimp (metis dist_norm le_less_trans norm_ge_zero)
    then show "0 < (r + dist w z) / 2"
      by simp (use zero_le_dist [of w z] in linarith)
  qed (use w in \<open>auto simp: dist_commute\<close>)
  then have holf: "f holomorphic_on ball z r"
    using ball_subset_cball holomorphic_on_subset by blast
  have contf: "continuous_on (cball z r) f"
    by (simp add: holfc holomorphic_on_imp_continuous_on)
  have cint: "\<And>k. (\<lambda>u. f u / (u - z) ^ Suc k) contour_integrable_on circlepath z r"
    by (rule Cauchy_higher_derivative_integral_circlepath [OF contf holf]) (simp add: \<open>0 < r\<close>)
  obtain B where "0 < B" and B: "\<And>u. u \<in> cball z r \<Longrightarrow> norm(f u) \<le> B"
    by (metis (no_types) bounded_pos compact_cball compact_continuous_image compact_imp_bounded contf image_eqI)
  obtain k where k: "0 < k" "k \<le> r" and wz_eq: "norm(w - z) = r - k"
             and kle: "\<And>u. norm(u - z) = r \<Longrightarrow> k \<le> norm(u - w)"
  proof
    show "\<And>u. cmod (u - z) = r \<Longrightarrow> r - dist z w \<le> cmod (u - w)"
      by (metis add_diff_eq diff_add_cancel dist_norm norm_diff_ineq)
  qed (use w in \<open>auto simp: dist_norm norm_minus_commute\<close>)
  have ul: "uniform_limit (sphere z r) (\<lambda>n x. (\<Sum>k<n. (w - z) ^ k * (f x / (x - z) ^ Suc k))) (\<lambda>x. f x / (x - w)) sequentially"
    unfolding uniform_limit_iff dist_norm
  proof clarify
    fix e::real
    assume "0 < e"
    have rr: "0 \<le> (r - k) / r" "(r - k) / r < 1" using  k by auto
    obtain n where n: "((r - k) / r) ^ n < e / B * k"
      using real_arch_pow_inv [of "e/B*k" "(r - k)/r"] \<open>0 < e\<close> \<open>0 < B\<close> k by force
    have "norm ((\<Sum>k<N. (w - z) ^ k * f u / (u - z) ^ Suc k) - f u / (u - w)) < e"
         if "n \<le> N" and r: "r = dist z u"  for N u
    proof -
      have N: "((r - k) / r) ^ N < e / B * k"
        apply (rule le_less_trans [OF power_decreasing n])
        using  \<open>n \<le> N\<close> k by auto
      have u [simp]: "(u \<noteq> z) \<and> (u \<noteq> w)"
        using \<open>0 < r\<close> r w by auto
      have wzu_not1: "(w - z) / (u - z) \<noteq> 1"
        by (metis (no_types) dist_norm divide_eq_1_iff less_irrefl mem_ball norm_minus_commute r w)
      have "norm ((\<Sum>k<N. (w - z) ^ k * f u / (u - z) ^ Suc k) * (u - w) - f u)
            = norm ((\<Sum>k<N. (((w - z) / (u - z)) ^ k)) * f u * (u - w) / (u - z) - f u)"
        unfolding sum_distrib_right sum_divide_distrib power_divide by (simp add: algebra_simps)
      also have "\<dots> = norm ((((w - z) / (u - z)) ^ N - 1) * (u - w) / (((w - z) / (u - z) - 1) * (u - z)) - 1) * norm (f u)"
        using \<open>0 < B\<close>
        apply (auto simp: geometric_sum [OF wzu_not1])
        apply (simp add: field_simps norm_mult [symmetric])
        done
      also have "\<dots> = norm ((u-z) ^ N * (w - u) - ((w - z) ^ N - (u-z) ^ N) * (u-w)) / (r ^ N * norm (u-w)) * norm (f u)"
        using \<open>0 < r\<close> r by (simp add: divide_simps norm_mult norm_divide norm_power dist_norm norm_minus_commute)
      also have "\<dots> = norm ((w - z) ^ N * (w - u)) / (r ^ N * norm (u - w)) * norm (f u)"
        by (simp add: algebra_simps)
      also have "\<dots> = norm (w - z) ^ N * norm (f u) / r ^ N"
        by (simp add: norm_mult norm_power norm_minus_commute)
      also have "\<dots> \<le> (((r - k)/r)^N) * B"
        using \<open>0 < r\<close> w k
        apply (simp add: divide_simps)
        apply (rule mult_mono [OF power_mono])
        apply (auto simp: norm_divide wz_eq norm_power dist_norm norm_minus_commute B r)
        done
      also have "\<dots> < e * k"
        using \<open>0 < B\<close> N by (simp add: divide_simps)
      also have "\<dots> \<le> e * norm (u - w)"
        using r kle \<open>0 < e\<close> by (simp add: dist_commute dist_norm)
      finally show ?thesis
        by (simp add: field_split_simps norm_divide del: power_Suc)
    qed
    with \<open>0 < r\<close> show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>sphere z r.
                norm ((\<Sum>k<n. (w - z) ^ k * (f x / (x - z) ^ Suc k)) - f x / (x - w)) < e"
      by (auto simp: mult_ac less_imp_le eventually_sequentially Ball_def)
  qed
  have eq: "\<forall>\<^sub>F x in sequentially.
             contour_integral (circlepath z r) (\<lambda>u. \<Sum>k<x. (w - z) ^ k * (f u / (u - z) ^ Suc k)) =
             (\<Sum>k<x. contour_integral (circlepath z r) (\<lambda>u. f u / (u - z) ^ Suc k) * (w - z) ^ k)"
    apply (rule eventuallyI)
    apply (subst contour_integral_sum, simp)
    using contour_integrable_lmul [OF cint, of "(w - z) ^ a" for a] apply (simp add: field_simps)
    apply (simp only: contour_integral_lmul cint algebra_simps)
    done
  have cic: "\<And>u. (\<lambda>y. \<Sum>k<u. (w - z) ^ k * (f y / (y - z) ^ Suc k)) contour_integrable_on circlepath z r"
    apply (intro contour_integrable_sum contour_integrable_lmul, simp)
    using \<open>0 < r\<close> by (force intro!: Cauchy_higher_derivative_integral_circlepath [OF contf holf])
  have "(\<lambda>k. contour_integral (circlepath z r) (\<lambda>u. f u/(u - z)^(Suc k)) * (w - z)^k)
        sums contour_integral (circlepath z r) (\<lambda>u. f u/(u - w))"
    unfolding sums_def
    apply (intro Lim_transform_eventually [OF _ eq] contour_integral_uniform_limit_circlepath [OF eventuallyI ul] cic)
    using \<open>0 < r\<close> apply auto
    done
  then have "(\<lambda>k. contour_integral (circlepath z r) (\<lambda>u. f u/(u - z)^(Suc k)) * (w - z)^k)
             sums (2 * of_real pi * \<i> * f w)"
    using w by (auto simp: dist_commute dist_norm contour_integral_unique [OF Cauchy_integral_circlepath_simple [OF holfc]])
  then have "(\<lambda>k. contour_integral (circlepath z r) (\<lambda>u. f u / (u - z) ^ Suc k) * (w - z)^k / (\<i> * (of_real pi * 2)))
            sums ((2 * of_real pi * \<i> * f w) / (\<i> * (complex_of_real pi * 2)))"
    by (rule sums_divide)
  then have "(\<lambda>n. (w - z) ^ n * contour_integral (circlepath z r) (\<lambda>u. f u / (u - z) ^ Suc n) / (\<i> * (of_real pi * 2)))
            sums f w"
    by (simp add: field_simps)
  then show ?thesis
    by (simp add: field_simps \<open>0 < r\<close> Cauchy_higher_derivative_integral_circlepath [OF contf holf])
qed


subsection\<open>The Liouville theorem and the Fundamental Theorem of Algebra\<close>

text\<open> These weak Liouville versions don't even need the derivative formula.\<close>

lemma Liouville_weak_0:
  assumes holf: "f holomorphic_on UNIV" and inf: "(f \<longlongrightarrow> 0) at_infinity"
    shows "f z = 0"
proof (rule ccontr)
  assume fz: "f z \<noteq> 0"
  with inf [unfolded Lim_at_infinity, rule_format, of "norm(f z)/2"]
  obtain B where B: "\<And>x. B \<le> cmod x \<Longrightarrow> norm (f x) * 2 < cmod (f z)"
    by (auto simp: dist_norm)
  define R where "R = 1 + \<bar>B\<bar> + norm z"
  have "R > 0" unfolding R_def
  proof -
    have "0 \<le> cmod z + \<bar>B\<bar>"
      by (metis (full_types) add_nonneg_nonneg norm_ge_zero real_norm_def)
    then show "0 < 1 + \<bar>B\<bar> + cmod z"
      by linarith
  qed
  have *: "((\<lambda>u. f u / (u - z)) has_contour_integral 2 * complex_of_real pi * \<i> * f z) (circlepath z R)"
    apply (rule Cauchy_integral_circlepath)
    using \<open>R > 0\<close> apply (auto intro: holomorphic_on_subset [OF holf] holomorphic_on_imp_continuous_on)+
    done
  have "cmod (x - z) = R \<Longrightarrow> cmod (f x) * 2 < cmod (f z)" for x
    unfolding R_def
    by (rule B) (use norm_triangle_ineq4 [of x z] in auto)
  with \<open>R > 0\<close> fz show False
    using has_contour_integral_bound_circlepath [OF *, of "norm(f z)/2/R"]
    by (auto simp: less_imp_le norm_mult norm_divide field_split_simps)
qed

proposition Liouville_weak:
  assumes "f holomorphic_on UNIV" and "(f \<longlongrightarrow> l) at_infinity"
    shows "f z = l"
  using Liouville_weak_0 [of "\<lambda>z. f z - l"]
  by (simp add: assms holomorphic_on_diff LIM_zero)

proposition Liouville_weak_inverse:
  assumes "f holomorphic_on UNIV" and unbounded: "\<And>B. eventually (\<lambda>x. norm (f x) \<ge> B) at_infinity"
    obtains z where "f z = 0"
proof -
  { assume f: "\<And>z. f z \<noteq> 0"
    have 1: "(\<lambda>x. 1 / f x) holomorphic_on UNIV"
      by (simp add: holomorphic_on_divide assms f)
    have 2: "((\<lambda>x. 1 / f x) \<longlongrightarrow> 0) at_infinity"
      apply (rule tendstoI [OF eventually_mono])
      apply (rule_tac B="2/e" in unbounded)
      apply (simp add: dist_norm norm_divide field_split_simps)
      done
    have False
      using Liouville_weak_0 [OF 1 2] f by simp
  }
  then show ?thesis
    using that by blast
qed

text\<open>In particular we get the Fundamental Theorem of Algebra.\<close>

theorem fundamental_theorem_of_algebra:
    fixes a :: "nat \<Rightarrow> complex"
  assumes "a 0 = 0 \<or> (\<exists>i \<in> {1..n}. a i \<noteq> 0)"
  obtains z where "(\<Sum>i\<le>n. a i * z^i) = 0"
using assms
proof (elim disjE bexE)
  assume "a 0 = 0" then show ?thesis
    by (auto simp: that [of 0])
next
  fix i
  assume i: "i \<in> {1..n}" and nz: "a i \<noteq> 0"
  have 1: "(\<lambda>z. \<Sum>i\<le>n. a i * z^i) holomorphic_on UNIV"
    by (rule holomorphic_intros)+
  show thesis
  proof (rule Liouville_weak_inverse [OF 1])
    show "\<forall>\<^sub>F x in at_infinity. B \<le> cmod (\<Sum>i\<le>n. a i * x ^ i)" for B
      using i polyfun_extremal nz by force
  qed (use that in auto)
qed

subsection\<open>Weierstrass convergence theorem\<close>

lemma holomorphic_uniform_limit:
  assumes cont: "eventually (\<lambda>n. continuous_on (cball z r) (f n) \<and> (f n) holomorphic_on ball z r) F"
      and ulim: "uniform_limit (cball z r) f g F"
      and F:  "\<not> trivial_limit F"
  obtains "continuous_on (cball z r) g" "g holomorphic_on ball z r"
proof (cases r "0::real" rule: linorder_cases)
  case less then show ?thesis by (force simp: ball_empty less_imp_le continuous_on_def holomorphic_on_def intro: that)
next
  case equal then show ?thesis
    by (force simp: holomorphic_on_def intro: that)
next
  case greater
  have contg: "continuous_on (cball z r) g"
    using cont uniform_limit_theorem [OF eventually_mono ulim F]  by blast
  have "path_image (circlepath z r) \<subseteq> cball z r"
    using \<open>0 < r\<close> by auto
  then have 1: "continuous_on (path_image (circlepath z r)) (\<lambda>x. 1 / (2 * complex_of_real pi * \<i>) * g x)"
    by (intro continuous_intros continuous_on_subset [OF contg])
  have 2: "((\<lambda>u. 1 / (2 * of_real pi * \<i>) * g u / (u - w) ^ 1) has_contour_integral g w) (circlepath z r)"
       if w: "w \<in> ball z r" for w
  proof -
    define d where "d = (r - norm(w - z))"
    have "0 < d"  "d \<le> r" using w by (auto simp: norm_minus_commute d_def dist_norm)
    have dle: "\<And>u. cmod (z - u) = r \<Longrightarrow> d \<le> cmod (u - w)"
      unfolding d_def by (metis add_diff_eq diff_add_cancel norm_diff_ineq norm_minus_commute)
    have ev_int: "\<forall>\<^sub>F n in F. (\<lambda>u. f n u / (u - w)) contour_integrable_on circlepath z r"
      apply (rule eventually_mono [OF cont])
      using w
      apply (auto intro: Cauchy_higher_derivative_integral_circlepath [where k=0, simplified])
      done
    have ul_less: "uniform_limit (sphere z r) (\<lambda>n x. f n x / (x - w)) (\<lambda>x. g x / (x - w)) F"
      using greater \<open>0 < d\<close>
      apply (clarsimp simp add: uniform_limit_iff dist_norm norm_divide diff_divide_distrib [symmetric] divide_simps)
      apply (rule_tac e1="e * d" in eventually_mono [OF uniform_limitD [OF ulim]])
       apply (force simp: dist_norm intro: dle mult_left_mono less_le_trans)+
      done
    have g_cint: "(\<lambda>u. g u/(u - w)) contour_integrable_on circlepath z r"
      by (rule contour_integral_uniform_limit_circlepath [OF ev_int ul_less F \<open>0 < r\<close>])
    have cif_tends_cig: "((\<lambda>n. contour_integral(circlepath z r) (\<lambda>u. f n u / (u - w))) \<longlongrightarrow> contour_integral(circlepath z r) (\<lambda>u. g u/(u - w))) F"
      by (rule contour_integral_uniform_limit_circlepath [OF ev_int ul_less F \<open>0 < r\<close>])
    have f_tends_cig: "((\<lambda>n. 2 * of_real pi * \<i> * f n w) \<longlongrightarrow> contour_integral (circlepath z r) (\<lambda>u. g u / (u - w))) F"
    proof (rule Lim_transform_eventually)
      show "\<forall>\<^sub>F x in F. contour_integral (circlepath z r) (\<lambda>u. f x u / (u - w))
                     = 2 * of_real pi * \<i> * f x w"
        apply (rule eventually_mono [OF cont contour_integral_unique [OF Cauchy_integral_circlepath]])
        using w\<open>0 < d\<close> d_def by auto
    qed (auto simp: cif_tends_cig)
    have "\<And>e. 0 < e \<Longrightarrow> \<forall>\<^sub>F n in F. dist (f n w) (g w) < e"
      by (rule eventually_mono [OF uniform_limitD [OF ulim]]) (use w in auto)
    then have "((\<lambda>n. 2 * of_real pi * \<i> * f n w) \<longlongrightarrow> 2 * of_real pi * \<i> * g w) F"
      by (rule tendsto_mult_left [OF tendstoI])
    then have "((\<lambda>u. g u / (u - w)) has_contour_integral 2 * of_real pi * \<i> * g w) (circlepath z r)"
      using has_contour_integral_integral [OF g_cint] tendsto_unique [OF F f_tends_cig] w
      by fastforce
    then have "((\<lambda>u. g u / (2 * of_real pi * \<i> * (u - w))) has_contour_integral g w) (circlepath z r)"
      using has_contour_integral_div [where c = "2 * of_real pi * \<i>"]
      by (force simp: field_simps)
    then show ?thesis
      by (simp add: dist_norm)
  qed
  show ?thesis
    using Cauchy_next_derivative_circlepath(2) [OF 1 2, simplified]
    by (fastforce simp add: holomorphic_on_open contg intro: that)
qed


text\<open> Version showing that the limit is the limit of the derivatives.\<close>

proposition has_complex_derivative_uniform_limit:
  fixes z::complex
  assumes cont: "eventually (\<lambda>n. continuous_on (cball z r) (f n) \<and>
                               (\<forall>w \<in> ball z r. ((f n) has_field_derivative (f' n w)) (at w))) F"
      and ulim: "uniform_limit (cball z r) f g F"
      and F:  "\<not> trivial_limit F" and "0 < r"
  obtains g' where
      "continuous_on (cball z r) g"
      "\<And>w. w \<in> ball z r \<Longrightarrow> (g has_field_derivative (g' w)) (at w) \<and> ((\<lambda>n. f' n w) \<longlongrightarrow> g' w) F"
proof -
  let ?conint = "contour_integral (circlepath z r)"
  have g: "continuous_on (cball z r) g" "g holomorphic_on ball z r"
    by (rule holomorphic_uniform_limit [OF eventually_mono [OF cont] ulim F];
             auto simp: holomorphic_on_open field_differentiable_def)+
  then obtain g' where g': "\<And>x. x \<in> ball z r \<Longrightarrow> (g has_field_derivative g' x) (at x)"
    using DERIV_deriv_iff_has_field_derivative
    by (fastforce simp add: holomorphic_on_open)
  then have derg: "\<And>x. x \<in> ball z r \<Longrightarrow> deriv g x = g' x"
    by (simp add: DERIV_imp_deriv)
  have tends_f'n_g': "((\<lambda>n. f' n w) \<longlongrightarrow> g' w) F" if w: "w \<in> ball z r" for w
  proof -
    have eq_f': "?conint (\<lambda>x. f n x / (x - w)\<^sup>2) - ?conint (\<lambda>x. g x / (x - w)\<^sup>2) = (f' n w - g' w) * (2 * of_real pi * \<i>)"
             if cont_fn: "continuous_on (cball z r) (f n)"
             and fnd: "\<And>w. w \<in> ball z r \<Longrightarrow> (f n has_field_derivative f' n w) (at w)" for n
    proof -
      have hol_fn: "f n holomorphic_on ball z r"
        using fnd by (force simp: holomorphic_on_open)
      have "(f n has_field_derivative 1 / (2 * of_real pi * \<i>) * ?conint (\<lambda>u. f n u / (u - w)\<^sup>2)) (at w)"
        by (rule Cauchy_derivative_integral_circlepath [OF cont_fn hol_fn w])
      then have f': "f' n w = 1 / (2 * of_real pi * \<i>) * ?conint (\<lambda>u. f n u / (u - w)\<^sup>2)"
        using DERIV_unique [OF fnd] w by blast
      show ?thesis
        by (simp add: f' Cauchy_contour_integral_circlepath_2 [OF g w] derg [OF w] field_split_simps)
    qed
    define d where "d = (r - norm(w - z))^2"
    have "d > 0"
      using w by (simp add: dist_commute dist_norm d_def)
    have dle: "d \<le> cmod ((y - w)\<^sup>2)" if "r = cmod (z - y)" for y
    proof -
      have "w \<in> ball z (cmod (z - y))"
        using that w by fastforce
      then have "cmod (w - z) \<le> cmod (z - y)"
        by (simp add: dist_complex_def norm_minus_commute)
      moreover have "cmod (z - y) - cmod (w - z) \<le> cmod (y - w)"
        by (metis diff_add_cancel diff_add_eq_diff_diff_swap norm_minus_commute norm_triangle_ineq2)
      ultimately show ?thesis
        using that by (simp add: d_def norm_power power_mono)
    qed
    have 1: "\<forall>\<^sub>F n in F. (\<lambda>x. f n x / (x - w)\<^sup>2) contour_integrable_on circlepath z r"
      by (force simp: holomorphic_on_open intro: w Cauchy_derivative_integral_circlepath eventually_mono [OF cont])
    have 2: "uniform_limit (sphere z r) (\<lambda>n x. f n x / (x - w)\<^sup>2) (\<lambda>x. g x / (x - w)\<^sup>2) F"
      unfolding uniform_limit_iff
    proof clarify
      fix e::real
      assume "0 < e"
      with \<open>r > 0\<close> show "\<forall>\<^sub>F n in F. \<forall>x\<in>sphere z r. dist (f n x / (x - w)\<^sup>2) (g x / (x - w)\<^sup>2) < e"
        apply (simp add: norm_divide field_split_simps sphere_def dist_norm)
        apply (rule eventually_mono [OF uniform_limitD [OF ulim], of "e*d"])
         apply (simp add: \<open>0 < d\<close>)
        apply (force simp: dist_norm dle intro: less_le_trans)
        done
    qed
    have "((\<lambda>n. contour_integral (circlepath z r) (\<lambda>x. f n x / (x - w)\<^sup>2))
             \<longlongrightarrow> contour_integral (circlepath z r) ((\<lambda>x. g x / (x - w)\<^sup>2))) F"
      by (rule contour_integral_uniform_limit_circlepath [OF 1 2 F \<open>0 < r\<close>])
    then have tendsto_0: "((\<lambda>n. 1 / (2 * of_real pi * \<i>) * (?conint (\<lambda>x. f n x / (x - w)\<^sup>2) - ?conint (\<lambda>x. g x / (x - w)\<^sup>2))) \<longlongrightarrow> 0) F"
      using Lim_null by (force intro!: tendsto_mult_right_zero)
    have "((\<lambda>n. f' n w - g' w) \<longlongrightarrow> 0) F"
      apply (rule Lim_transform_eventually [OF tendsto_0])
      apply (force simp: divide_simps intro: eq_f' eventually_mono [OF cont])
      done
    then show ?thesis using Lim_null by blast
  qed
  obtain g' where "\<And>w. w \<in> ball z r \<Longrightarrow> (g has_field_derivative (g' w)) (at w) \<and> ((\<lambda>n. f' n w) \<longlongrightarrow> g' w) F"
      by (blast intro: tends_f'n_g' g')
  then show ?thesis using g
    using that by blast
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some more simple/convenient versions for applications\<close>

lemma holomorphic_uniform_sequence:
  assumes S: "open S"
      and hol_fn: "\<And>n. (f n) holomorphic_on S"
      and ulim_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d. 0 < d \<and> cball x d \<subseteq> S \<and> uniform_limit (cball x d) f g sequentially"
  shows "g holomorphic_on S"
proof -
  have "\<exists>f'. (g has_field_derivative f') (at z)" if "z \<in> S" for z
  proof -
    obtain r where "0 < r" and r: "cball z r \<subseteq> S"
               and ul: "uniform_limit (cball z r) f g sequentially"
      using ulim_g [OF \<open>z \<in> S\<close>] by blast
    have *: "\<forall>\<^sub>F n in sequentially. continuous_on (cball z r) (f n) \<and> f n holomorphic_on ball z r"
    proof (intro eventuallyI conjI)
      show "continuous_on (cball z r) (f x)" for x
        using hol_fn holomorphic_on_imp_continuous_on holomorphic_on_subset r by blast
      show "f x holomorphic_on ball z r" for x
        by (metis hol_fn holomorphic_on_subset interior_cball interior_subset r)
    qed
    show ?thesis
      apply (rule holomorphic_uniform_limit [OF *])
      using \<open>0 < r\<close> centre_in_ball ul
      apply (auto simp: holomorphic_on_open)
      done
  qed
  with S show ?thesis
    by (simp add: holomorphic_on_open)
qed

lemma has_complex_derivative_uniform_sequence:
  fixes S :: "complex set"
  assumes S: "open S"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_field_derivative f' n x) (at x)"
      and ulim_g: "\<And>x. x \<in> S
             \<Longrightarrow> \<exists>d. 0 < d \<and> cball x d \<subseteq> S \<and> uniform_limit (cball x d) f g sequentially"
  shows "\<exists>g'. \<forall>x \<in> S. (g has_field_derivative g' x) (at x) \<and> ((\<lambda>n. f' n x) \<longlongrightarrow> g' x) sequentially"
proof -
  have y: "\<exists>y. (g has_field_derivative y) (at z) \<and> (\<lambda>n. f' n z) \<longlonglongrightarrow> y" if "z \<in> S" for z
  proof -
    obtain r where "0 < r" and r: "cball z r \<subseteq> S"
               and ul: "uniform_limit (cball z r) f g sequentially"
      using ulim_g [OF \<open>z \<in> S\<close>] by blast
    have *: "\<forall>\<^sub>F n in sequentially. continuous_on (cball z r) (f n) \<and>
                                   (\<forall>w \<in> ball z r. ((f n) has_field_derivative (f' n w)) (at w))"
    proof (intro eventuallyI conjI ballI)
      show "continuous_on (cball z r) (f x)" for x
        by (meson S continuous_on_subset hfd holomorphic_on_imp_continuous_on holomorphic_on_open r)
      show "w \<in> ball z r \<Longrightarrow> (f x has_field_derivative f' x w) (at w)" for w x
        using ball_subset_cball hfd r by blast
    qed
    show ?thesis
      by (rule has_complex_derivative_uniform_limit [OF *, of g]) (use \<open>0 < r\<close> ul in \<open>force+\<close>)
  qed
  show ?thesis
    by (rule bchoice) (blast intro: y)
qed

subsection\<open>On analytic functions defined by a series\<close>

lemma series_and_derivative_comparison:
  fixes S :: "complex set"
  assumes S: "open S"
      and h: "summable h"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      and to_g: "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. norm (f n x) \<le> h n"
  obtains g g' where "\<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
proof -
  obtain g where g: "uniform_limit S (\<lambda>n x. \<Sum>i<n. f i x) g sequentially"
    using Weierstrass_m_test_ev [OF to_g h]  by force
  have *: "\<exists>d>0. cball x d \<subseteq> S \<and> uniform_limit (cball x d) (\<lambda>n x. \<Sum>i<n. f i x) g sequentially"
         if "x \<in> S" for x
  proof -
    obtain d where "d>0" and d: "cball x d \<subseteq> S"
      using open_contains_cball [of "S"] \<open>x \<in> S\<close> S by blast
    show ?thesis
    proof (intro conjI exI)
      show "uniform_limit (cball x d) (\<lambda>n x. \<Sum>i<n. f i x) g sequentially"
        using d g uniform_limit_on_subset by (force simp: dist_norm eventually_sequentially)
    qed (use \<open>d > 0\<close> d in auto)
  qed
  have "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>n. \<Sum>i<n. f i x) \<longlonglongrightarrow> g x"
    by (metis tendsto_uniform_limitI [OF g])
  moreover have "\<exists>g'. \<forall>x\<in>S. (g has_field_derivative g' x) (at x) \<and> (\<lambda>n. \<Sum>i<n. f' i x) \<longlonglongrightarrow> g' x"
    by (rule has_complex_derivative_uniform_sequence [OF S]) (auto intro: * hfd DERIV_sum)+
  ultimately show ?thesis
    by (metis sums_def that)
qed

text\<open>A version where we only have local uniform/comparative convergence.\<close>

lemma series_and_derivative_comparison_local:
  fixes S :: "complex set"
  assumes S: "open S"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      and to_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d h. 0 < d \<and> summable h \<and> (\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball x d \<inter> S. norm (f n y) \<le> h n)"
  shows "\<exists>g g'. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
proof -
  have "\<exists>y. (\<lambda>n. f n z) sums (\<Sum>n. f n z) \<and> (\<lambda>n. f' n z) sums y \<and> ((\<lambda>x. \<Sum>n. f n x) has_field_derivative y) (at z)"
       if "z \<in> S" for z
  proof -
    obtain d h where "0 < d" "summable h" and le_h: "\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball z d \<inter> S. norm (f n y) \<le> h n"
      using to_g \<open>z \<in> S\<close> by meson
    then obtain r where "r>0" and r: "ball z r \<subseteq> ball z d \<inter> S" using \<open>z \<in> S\<close> S
      by (metis Int_iff open_ball centre_in_ball open_Int open_contains_ball_eq)
    have 1: "open (ball z d \<inter> S)"
      by (simp add: open_Int S)
    have 2: "\<And>n x. x \<in> ball z d \<inter> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      by (auto simp: hfd)
    obtain g g' where gg': "\<forall>x \<in> ball z d \<inter> S. ((\<lambda>n. f n x) sums g x) \<and>
                                    ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
      by (auto intro: le_h series_and_derivative_comparison [OF 1 \<open>summable h\<close> hfd])
    then have "(\<lambda>n. f' n z) sums g' z"
      by (meson \<open>0 < r\<close> centre_in_ball contra_subsetD r)
    moreover have "(\<lambda>n. f n z) sums (\<Sum>n. f n z)"
      using  summable_sums centre_in_ball \<open>0 < d\<close> \<open>summable h\<close> le_h
      by (metis (full_types) Int_iff gg' summable_def that)
    moreover have "((\<lambda>x. \<Sum>n. f n x) has_field_derivative g' z) (at z)"
    proof (rule has_field_derivative_transform_within)
      show "\<And>x. dist x z < r \<Longrightarrow> g x = (\<Sum>n. f n x)"
        by (metis subsetD dist_commute gg' mem_ball r sums_unique)
    qed (use \<open>0 < r\<close> gg' \<open>z \<in> S\<close> \<open>0 < d\<close> in auto)
    ultimately show ?thesis by auto
  qed
  then show ?thesis
    by (rule_tac x="\<lambda>x. suminf (\<lambda>n. f n x)" in exI) meson
qed


text\<open>Sometimes convenient to compare with a complex series of positive reals. (?)\<close>

lemma series_and_derivative_comparison_complex:
  fixes S :: "complex set"
  assumes S: "open S"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      and to_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d h. 0 < d \<and> summable h \<and> range h \<subseteq> \<real>\<^sub>\<ge>\<^sub>0 \<and> (\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball x d \<inter> S. cmod(f n y) \<le> cmod (h n))"
  shows "\<exists>g g'. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
apply (rule series_and_derivative_comparison_local [OF S hfd], assumption)
apply (rule ex_forward [OF to_g], assumption)
apply (erule exE)
apply (rule_tac x="Re \<circ> h" in exI)
apply (force simp: summable_Re o_def nonneg_Reals_cmod_eq_Re image_subset_iff)
done

text\<open>Sometimes convenient to compare with a complex series of positive reals. (?)\<close>
lemma series_differentiable_comparison_complex:
  fixes S :: "complex set"
  assumes S: "open S"
    and hfd: "\<And>n x. x \<in> S \<Longrightarrow> f n field_differentiable (at x)"
    and to_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d h. 0 < d \<and> summable h \<and> range h \<subseteq> \<real>\<^sub>\<ge>\<^sub>0 \<and> (\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball x d \<inter> S. cmod(f n y) \<le> cmod (h n))"
  obtains g where "\<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> g field_differentiable (at x)"
proof -
  have hfd': "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative deriv (f n) x) (at x)"
    using hfd field_differentiable_derivI by blast
  have "\<exists>g g'. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. deriv (f n) x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
    by (metis series_and_derivative_comparison_complex [OF S hfd' to_g])
  then show ?thesis
    using field_differentiable_def that by blast
qed

text\<open>In particular, a power series is analytic inside circle of convergence.\<close>

lemma power_series_and_derivative_0:
  fixes a :: "nat \<Rightarrow> complex" and r::real
  assumes "summable (\<lambda>n. a n * r^n)"
    shows "\<exists>g g'. \<forall>z. cmod z < r \<longrightarrow>
             ((\<lambda>n. a n * z^n) sums g z) \<and> ((\<lambda>n. of_nat n * a n * z^(n - 1)) sums g' z) \<and> (g has_field_derivative g' z) (at z)"
proof (cases "0 < r")
  case True
    have der: "\<And>n z. ((\<lambda>x. a n * x ^ n) has_field_derivative of_nat n * a n * z ^ (n - 1)) (at z)"
      by (rule derivative_eq_intros | simp)+
    have y_le: "\<lbrakk>cmod (z - y) * 2 < r - cmod z\<rbrakk> \<Longrightarrow> cmod y \<le> cmod (of_real r + of_real (cmod z)) / 2" for z y
      using \<open>r > 0\<close>
      apply (auto simp: algebra_simps norm_mult norm_divide norm_power simp flip: of_real_add)
      using norm_triangle_ineq2 [of y z]
      apply (simp only: diff_le_eq norm_minus_commute mult_2)
      done
    have "summable (\<lambda>n. a n * complex_of_real r ^ n)"
      using assms \<open>r > 0\<close> by simp
    moreover have "\<And>z. cmod z < r \<Longrightarrow> cmod ((of_real r + of_real (cmod z)) / 2) < cmod (of_real r)"
      using \<open>r > 0\<close>
      by (simp flip: of_real_add)
    ultimately have sum: "\<And>z. cmod z < r \<Longrightarrow> summable (\<lambda>n. of_real (cmod (a n)) * ((of_real r + complex_of_real (cmod z)) / 2) ^ n)"
      by (rule power_series_conv_imp_absconv_weak)
    have "\<exists>g g'. \<forall>z \<in> ball 0 r. (\<lambda>n.  (a n) * z ^ n) sums g z \<and>
               (\<lambda>n. of_nat n * (a n) * z ^ (n - 1)) sums g' z \<and> (g has_field_derivative g' z) (at z)"
      apply (rule series_and_derivative_comparison_complex [OF open_ball der])
      apply (rule_tac x="(r - norm z)/2" in exI)
      apply (rule_tac x="\<lambda>n. of_real(norm(a n)*((r + norm z)/2)^n)" in exI)
      using \<open>r > 0\<close>
      apply (auto simp: sum eventually_sequentially norm_mult norm_power dist_norm intro!: mult_left_mono power_mono y_le)
      done
  then show ?thesis
    by (simp add: ball_def)
next
  case False then show ?thesis
    apply (simp add: not_less)
    using less_le_trans norm_not_less_zero by blast
qed

proposition\<^marker>\<open>tag unimportant\<close> power_series_and_derivative:
  fixes a :: "nat \<Rightarrow> complex" and r::real
  assumes "summable (\<lambda>n. a n * r^n)"
    obtains g g' where "\<forall>z \<in> ball w r.
             ((\<lambda>n. a n * (z - w) ^ n) sums g z) \<and> ((\<lambda>n. of_nat n * a n * (z - w) ^ (n - 1)) sums g' z) \<and>
              (g has_field_derivative g' z) (at z)"
  using power_series_and_derivative_0 [OF assms]
  apply clarify
  apply (rule_tac g="(\<lambda>z. g(z - w))" in that)
  using DERIV_shift [where z="-w"]
  apply (auto simp: norm_minus_commute Ball_def dist_norm)
  done

proposition\<^marker>\<open>tag unimportant\<close> power_series_holomorphic:
  assumes "\<And>w. w \<in> ball z r \<Longrightarrow> ((\<lambda>n. a n*(w - z)^n) sums f w)"
    shows "f holomorphic_on ball z r"
proof -
  have "\<exists>f'. (f has_field_derivative f') (at w)" if w: "dist z w < r" for w
  proof -
    have inb: "z + complex_of_real ((dist z w + r) / 2) \<in> ball z r"
    proof -
      have wz: "cmod (w - z) < r" using w
        by (auto simp: field_split_simps dist_norm norm_minus_commute)
      then have "0 \<le> r"
        by (meson less_eq_real_def norm_ge_zero order_trans)
      show ?thesis
        using w by (simp add: dist_norm \<open>0\<le>r\<close> flip: of_real_add)
    qed
    have sum: "summable (\<lambda>n. a n * of_real (((cmod (z - w) + r) / 2) ^ n))"
      using assms [OF inb] by (force simp: summable_def dist_norm)
    obtain g g' where gg': "\<And>u. u \<in> ball z ((cmod (z - w) + r) / 2) \<Longrightarrow>
                               (\<lambda>n. a n * (u - z) ^ n) sums g u \<and>
                               (\<lambda>n. of_nat n * a n * (u - z) ^ (n - 1)) sums g' u \<and> (g has_field_derivative g' u) (at u)"
      by (rule power_series_and_derivative [OF sum, of z]) fastforce
    have [simp]: "g u = f u" if "cmod (u - w) < (r - cmod (z - w)) / 2" for u
    proof -
      have less: "cmod (z - u) * 2 < cmod (z - w) + r"
        using that dist_triangle2 [of z u w]
        by (simp add: dist_norm [symmetric] algebra_simps)
      show ?thesis
        apply (rule sums_unique2 [of "\<lambda>n. a n*(u - z)^n"])
        using gg' [of u] less w
        apply (auto simp: assms dist_norm)
        done
    qed
    have "(f has_field_derivative g' w) (at w)"
      by (rule has_field_derivative_transform_within [where d="(r - norm(z - w))/2"])
      (use w gg' [of w] in \<open>(force simp: dist_norm)+\<close>)
    then show ?thesis ..
  qed
  then show ?thesis by (simp add: holomorphic_on_open)
qed

corollary holomorphic_iff_power_series:
     "f holomorphic_on ball z r \<longleftrightarrow>
      (\<forall>w \<in> ball z r. (\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n) sums f w)"
  apply (intro iffI ballI holomorphic_power_series, assumption+)
  apply (force intro: power_series_holomorphic [where a = "\<lambda>n. (deriv ^^ n) f z / (fact n)"])
  done

lemma power_series_analytic:
     "(\<And>w. w \<in> ball z r \<Longrightarrow> (\<lambda>n. a n*(w - z)^n) sums f w) \<Longrightarrow> f analytic_on ball z r"
  by (force simp: analytic_on_open intro!: power_series_holomorphic)

lemma analytic_iff_power_series:
     "f analytic_on ball z r \<longleftrightarrow>
      (\<forall>w \<in> ball z r. (\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n) sums f w)"
  by (simp add: analytic_on_open holomorphic_iff_power_series)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Equality between holomorphic functions, on open ball then connected set\<close>

lemma holomorphic_fun_eq_on_ball:
   "\<lbrakk>f holomorphic_on ball z r; g holomorphic_on ball z r;
     w \<in> ball z r;
     \<And>n. (deriv ^^ n) f z = (deriv ^^ n) g z\<rbrakk>
     \<Longrightarrow> f w = g w"
  apply (rule sums_unique2 [of "\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n"])
  apply (auto simp: holomorphic_iff_power_series)
  done

lemma holomorphic_fun_eq_0_on_ball:
   "\<lbrakk>f holomorphic_on ball z r;  w \<in> ball z r;
     \<And>n. (deriv ^^ n) f z = 0\<rbrakk>
     \<Longrightarrow> f w = 0"
  apply (rule sums_unique2 [of "\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n"])
  apply (auto simp: holomorphic_iff_power_series)
  done

lemma holomorphic_fun_eq_0_on_connected:
  assumes holf: "f holomorphic_on S" and "open S"
      and cons: "connected S"
      and der: "\<And>n. (deriv ^^ n) f z = 0"
      and "z \<in> S" "w \<in> S"
    shows "f w = 0"
proof -
  have *: "ball x e \<subseteq> (\<Inter>n. {w \<in> S. (deriv ^^ n) f w = 0})"
    if "\<forall>u. (deriv ^^ u) f x = 0" "ball x e \<subseteq> S" for x e
  proof -
    have "\<And>x' n. dist x x' < e \<Longrightarrow> (deriv ^^ n) f x' = 0"
      apply (rule holomorphic_fun_eq_0_on_ball [OF holomorphic_higher_deriv])
         apply (rule holomorphic_on_subset [OF holf])
      using that apply simp_all
      by (metis funpow_add o_apply)
    with that show ?thesis by auto
  qed
  have 1: "openin (top_of_set S) (\<Inter>n. {w \<in> S. (deriv ^^ n) f w = 0})"
    apply (rule open_subset, force)
    using \<open>open S\<close>
    apply (simp add: open_contains_ball Ball_def)
    apply (erule all_forward)
    using "*" by auto blast+
  have 2: "closedin (top_of_set S) (\<Inter>n. {w \<in> S. (deriv ^^ n) f w = 0})"
    using assms
    by (auto intro: continuous_closedin_preimage_constant holomorphic_on_imp_continuous_on holomorphic_higher_deriv)
  obtain e where "e>0" and e: "ball w e \<subseteq> S" using openE [OF \<open>open S\<close> \<open>w \<in> S\<close>] .
  then have holfb: "f holomorphic_on ball w e"
    using holf holomorphic_on_subset by blast
  have 3: "(\<Inter>n. {w \<in> S. (deriv ^^ n) f w = 0}) = S \<Longrightarrow> f w = 0"
    using \<open>e>0\<close> e by (force intro: holomorphic_fun_eq_0_on_ball [OF holfb])
  show ?thesis
    using cons der \<open>z \<in> S\<close>
    apply (simp add: connected_clopen)
    apply (drule_tac x="\<Inter>n. {w \<in> S. (deriv ^^ n) f w = 0}" in spec)
    apply (auto simp: 1 2 3)
    done
qed

lemma holomorphic_fun_eq_on_connected:
  assumes "f holomorphic_on S" "g holomorphic_on S" and "open S"  "connected S"
      and "\<And>n. (deriv ^^ n) f z = (deriv ^^ n) g z"
      and "z \<in> S" "w \<in> S"
    shows "f w = g w"
proof (rule holomorphic_fun_eq_0_on_connected [of "\<lambda>x. f x - g x" S z, simplified])
  show "(\<lambda>x. f x - g x) holomorphic_on S"
    by (intro assms holomorphic_intros)
  show "\<And>n. (deriv ^^ n) (\<lambda>x. f x - g x) z = 0"
    using assms higher_deriv_diff by auto
qed (use assms in auto)

lemma holomorphic_fun_eq_const_on_connected:
  assumes holf: "f holomorphic_on S" and "open S"
      and cons: "connected S"
      and der: "\<And>n. 0 < n \<Longrightarrow> (deriv ^^ n) f z = 0"
      and "z \<in> S" "w \<in> S"
    shows "f w = f z"
proof (rule holomorphic_fun_eq_0_on_connected [of "\<lambda>w. f w - f z" S z, simplified])
  show "(\<lambda>w. f w - f z) holomorphic_on S"
    by (intro assms holomorphic_intros)
  show "\<And>n. (deriv ^^ n) (\<lambda>w. f w - f z) z = 0"
    by (subst higher_deriv_diff) (use assms in \<open>auto intro: holomorphic_intros\<close>)
qed (use assms in auto)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Some basic lemmas about poles/singularities\<close>

lemma pole_lemma:
  assumes holf: "f holomorphic_on S" and a: "a \<in> interior S"
    shows "(\<lambda>z. if z = a then deriv f a
                 else (f z - f a) / (z - a)) holomorphic_on S" (is "?F holomorphic_on S")
proof -
  have F1: "?F field_differentiable (at u within S)" if "u \<in> S" "u \<noteq> a" for u
  proof -
    have fcd: "f field_differentiable at u within S"
      using holf holomorphic_on_def by (simp add: \<open>u \<in> S\<close>)
    have cd: "(\<lambda>z. (f z - f a) / (z - a)) field_differentiable at u within S"
      by (rule fcd derivative_intros | simp add: that)+
    have "0 < dist a u" using that dist_nz by blast
    then show ?thesis
      by (rule field_differentiable_transform_within [OF _ _ _ cd]) (auto simp: \<open>u \<in> S\<close>)
  qed
  have F2: "?F field_differentiable at a" if "0 < e" "ball a e \<subseteq> S" for e
  proof -
    have holfb: "f holomorphic_on ball a e"
      by (rule holomorphic_on_subset [OF holf \<open>ball a e \<subseteq> S\<close>])
    have 2: "?F holomorphic_on ball a e - {a}"
      apply (simp add: holomorphic_on_def flip: field_differentiable_def)
      using mem_ball that
      apply (auto intro: F1 field_differentiable_within_subset)
      done
    have "isCont (\<lambda>z. if z = a then deriv f a else (f z - f a) / (z - a)) x"
            if "dist a x < e" for x
    proof (cases "x=a")
      case True
      then have "f field_differentiable at a"
        using holfb \<open>0 < e\<close> holomorphic_on_imp_differentiable_at by auto
      with True show ?thesis
        by (auto simp: continuous_at has_field_derivative_iff simp flip: DERIV_deriv_iff_field_differentiable
                elim: rev_iffD1 [OF _ LIM_equal])
    next
      case False with 2 that show ?thesis
        by (force simp: holomorphic_on_open open_Diff field_differentiable_def [symmetric] field_differentiable_imp_continuous_at)
    qed
    then have 1: "continuous_on (ball a e) ?F"
      by (clarsimp simp:  continuous_on_eq_continuous_at)
    have "?F holomorphic_on ball a e"
      by (auto intro: no_isolated_singularity [OF 1 2])
    with that show ?thesis
      by (simp add: holomorphic_on_open field_differentiable_def [symmetric]
                    field_differentiable_at_within)
  qed
  show ?thesis
  proof
    fix x assume "x \<in> S" show "?F field_differentiable at x within S"
    proof (cases "x=a")
      case True then show ?thesis
      using a by (auto simp: mem_interior intro: field_differentiable_at_within F2)
    next
      case False with F1 \<open>x \<in> S\<close>
      show ?thesis by blast
    qed
  qed
qed

lemma pole_theorem:
  assumes holg: "g holomorphic_on S" and a: "a \<in> interior S"
      and eq: "\<And>z. z \<in> S - {a} \<Longrightarrow> g z = (z - a) * f z"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) holomorphic_on S"
  using pole_lemma [OF holg a]
  by (rule holomorphic_transform) (simp add: eq field_split_simps)

lemma pole_lemma_open:
  assumes "f holomorphic_on S" "open S"
    shows "(\<lambda>z. if z = a then deriv f a else (f z - f a)/(z - a)) holomorphic_on S"
proof (cases "a \<in> S")
  case True with assms interior_eq pole_lemma
    show ?thesis by fastforce
next
  case False with assms show ?thesis
    apply (simp add: holomorphic_on_def field_differentiable_def [symmetric], clarify)
    apply (rule field_differentiable_transform_within [where f = "\<lambda>z. (f z - f a)/(z - a)" and d = 1])
    apply (rule derivative_intros | force)+
    done
qed

lemma pole_theorem_open:
  assumes holg: "g holomorphic_on S" and S: "open S"
      and eq: "\<And>z. z \<in> S - {a} \<Longrightarrow> g z = (z - a) * f z"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) holomorphic_on S"
  using pole_lemma_open [OF holg S]
  by (rule holomorphic_transform) (auto simp: eq divide_simps)

lemma pole_theorem_0:
  assumes holg: "g holomorphic_on S" and a: "a \<in> interior S"
      and eq: "\<And>z. z \<in> S - {a} \<Longrightarrow> g z = (z - a) * f z"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f holomorphic_on S"
  using pole_theorem [OF holg a eq]
  by (rule holomorphic_transform) (auto simp: eq field_split_simps)

lemma pole_theorem_open_0:
  assumes holg: "g holomorphic_on S" and S: "open S"
      and eq: "\<And>z. z \<in> S - {a} \<Longrightarrow> g z = (z - a) * f z"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f holomorphic_on S"
  using pole_theorem_open [OF holg S eq]
  by (rule holomorphic_transform) (auto simp: eq field_split_simps)

lemma pole_theorem_analytic:
  assumes g: "g analytic_on S"
      and eq: "\<And>z. z \<in> S
             \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>w \<in> ball z d - {a}. g w = (w - a) * f w)"
    shows "(\<lambda>z. if z = a then deriv g a else f z - g a/(z - a)) analytic_on S" (is "?F analytic_on S")
  unfolding analytic_on_def
proof
  fix x
  assume "x \<in> S"
  with g obtain e where "0 < e" and e: "g holomorphic_on ball x e"
    by (auto simp add: analytic_on_def)
  obtain d where "0 < d" and d: "\<And>w. w \<in> ball x d - {a} \<Longrightarrow> g w = (w - a) * f w"
    using \<open>x \<in> S\<close> eq by blast
  have "?F holomorphic_on ball x (min d e)"
    using d e \<open>x \<in> S\<close> by (fastforce simp: holomorphic_on_subset subset_ball intro!: pole_theorem_open)
  then show "\<exists>e>0. ?F holomorphic_on ball x e"
    using \<open>0 < d\<close> \<open>0 < e\<close> not_le by fastforce
qed

lemma pole_theorem_analytic_0:
  assumes g: "g analytic_on S"
      and eq: "\<And>z. z \<in> S \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>w \<in> ball z d - {a}. g w = (w - a) * f w)"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f analytic_on S"
proof -
  have [simp]: "(\<lambda>z. if z = a then deriv g a else f z - g a / (z - a)) = f"
    by auto
  show ?thesis
    using pole_theorem_analytic [OF g eq] by simp
qed

lemma pole_theorem_analytic_open_superset:
  assumes g: "g analytic_on S" and "S \<subseteq> T" "open T"
      and eq: "\<And>z. z \<in> T - {a} \<Longrightarrow> g z = (z - a) * f z"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) analytic_on S"
proof (rule pole_theorem_analytic [OF g])
  fix z
  assume "z \<in> S"
  then obtain e where "0 < e" and e: "ball z e \<subseteq> T"
    using assms openE by blast
  then show "\<exists>d>0. \<forall>w\<in>ball z d - {a}. g w = (w - a) * f w"
    using eq by auto
qed

lemma pole_theorem_analytic_open_superset_0:
  assumes g: "g analytic_on S" "S \<subseteq> T" "open T" "\<And>z. z \<in> T - {a} \<Longrightarrow> g z = (z - a) * f z"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f analytic_on S"
proof -
  have [simp]: "(\<lambda>z. if z = a then deriv g a else f z - g a / (z - a)) = f"
    by auto
  have "(\<lambda>z. if z = a then deriv g a else f z - g a/(z - a)) analytic_on S"
    by (rule pole_theorem_analytic_open_superset [OF g])
  then show ?thesis by simp
qed


subsection\<open>General, homology form of Cauchy's integral formula\<close>

text\<open>Proof is based on Dixon's, as presented in Lang's "Complex Analysis" book (page 147).\<close>

lemma contour_integral_continuous_on_linepath_2D:
  assumes "open U" and cont_dw: "\<And>w. w \<in> U \<Longrightarrow> F w contour_integrable_on (linepath a b)"
      and cond_uu: "continuous_on (U \<times> U) (\<lambda>(x,y). F x y)"
      and abu: "closed_segment a b \<subseteq> U"
    shows "continuous_on U (\<lambda>w. contour_integral (linepath a b) (F w))"
proof -
  have *: "\<exists>d>0. \<forall>x'\<in>U. dist x' w < d \<longrightarrow>
                         dist (contour_integral (linepath a b) (F x'))
                              (contour_integral (linepath a b) (F w)) \<le> \<epsilon>"
          if "w \<in> U" "0 < \<epsilon>" "a \<noteq> b" for w \<epsilon>
  proof -
    obtain \<delta> where "\<delta>>0" and \<delta>: "cball w \<delta> \<subseteq> U" using open_contains_cball \<open>open U\<close> \<open>w \<in> U\<close> by force
    let ?TZ = "cball w \<delta>  \<times> closed_segment a b"
    have "uniformly_continuous_on ?TZ (\<lambda>(x,y). F x y)"
    proof (rule compact_uniformly_continuous)
      show "continuous_on ?TZ (\<lambda>(x,y). F x y)"
        by (rule continuous_on_subset[OF cond_uu]) (use SigmaE \<delta> abu in blast)
      show "compact ?TZ"
        by (simp add: compact_Times)
    qed
    then obtain \<eta> where "\<eta>>0"
        and \<eta>: "\<And>x x'. \<lbrakk>x\<in>?TZ; x'\<in>?TZ; dist x' x < \<eta>\<rbrakk> \<Longrightarrow>
                         dist ((\<lambda>(x,y). F x y) x') ((\<lambda>(x,y). F x y) x) < \<epsilon>/norm(b - a)"
      apply (rule uniformly_continuous_onE [where e = "\<epsilon>/norm(b - a)"])
      using \<open>0 < \<epsilon>\<close> \<open>a \<noteq> b\<close> by auto
    have \<eta>: "\<lbrakk>norm (w - x1) \<le> \<delta>;   x2 \<in> closed_segment a b;
              norm (w - x1') \<le> \<delta>;  x2' \<in> closed_segment a b; norm ((x1', x2') - (x1, x2)) < \<eta>\<rbrakk>
              \<Longrightarrow> norm (F x1' x2' - F x1 x2) \<le> \<epsilon> / cmod (b - a)"
             for x1 x2 x1' x2'
      using \<eta> [of "(x1,x2)" "(x1',x2')"] by (force simp: dist_norm)
    have le_ee: "cmod (contour_integral (linepath a b) (\<lambda>x. F x' x - F w x)) \<le> \<epsilon>"
                if "x' \<in> U" "cmod (x' - w) < \<delta>" "cmod (x' - w) < \<eta>"  for x'
    proof -
      have "(\<lambda>x. F x' x - F w x) contour_integrable_on linepath a b"
        by (simp add: \<open>w \<in> U\<close> cont_dw contour_integrable_diff that)
      then have "cmod (contour_integral (linepath a b) (\<lambda>x. F x' x - F w x)) \<le> \<epsilon>/norm(b - a) * norm(b - a)"
        apply (rule has_contour_integral_bound_linepath [OF has_contour_integral_integral _ \<eta>])
        using \<open>0 < \<epsilon>\<close> \<open>0 < \<delta>\<close> that apply (auto simp: norm_minus_commute)
        done
      also have "\<dots> = \<epsilon>" using \<open>a \<noteq> b\<close> by simp
      finally show ?thesis .
    qed
    show ?thesis
      apply (rule_tac x="min \<delta> \<eta>" in exI)
      using \<open>0 < \<delta>\<close> \<open>0 < \<eta>\<close>
      apply (auto simp: dist_norm contour_integral_diff [OF cont_dw cont_dw, symmetric] \<open>w \<in> U\<close> intro: le_ee)
      done
  qed
  show ?thesis
  proof (cases "a=b")
    case True
    then show ?thesis by simp
  next
    case False
    show ?thesis
      by (rule continuous_onI) (use False in \<open>auto intro: *\<close>)
  qed
qed

text\<open>This version has \<^term>\<open>polynomial_function \<gamma>\<close> as an additional assumption.\<close>
lemma Cauchy_integral_formula_global_weak:
  assumes "open U" and holf: "f holomorphic_on U"
        and z: "z \<in> U" and \<gamma>: "polynomial_function \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> U - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
        and zero: "\<And>w. w \<notin> U \<Longrightarrow> winding_number \<gamma> w = 0"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  obtain \<gamma>' where pf\<gamma>': "polynomial_function \<gamma>'" and \<gamma>': "\<And>x. (\<gamma> has_vector_derivative (\<gamma>' x)) (at x)"
    using has_vector_derivative_polynomial_function [OF \<gamma>] by blast
  then have "bounded(path_image \<gamma>')"
    by (simp add: path_image_def compact_imp_bounded compact_continuous_image continuous_on_polymonial_function)
  then obtain B where "B>0" and B: "\<And>x. x \<in> path_image \<gamma>' \<Longrightarrow> norm x \<le> B"
    using bounded_pos by force
  define d where [abs_def]: "d z w = (if w = z then deriv f z else (f w - f z)/(w - z))" for z w
  define v where "v = {w. w \<notin> path_image \<gamma> \<and> winding_number \<gamma> w = 0}"
  have "path \<gamma>" "valid_path \<gamma>" using \<gamma>
    by (auto simp: path_polynomial_function valid_path_polynomial_function)
  then have ov: "open v"
    by (simp add: v_def open_winding_number_levelsets loop)
  have uv_Un: "U \<union> v = UNIV"
    using pasz zero by (auto simp: v_def)
  have conf: "continuous_on U f"
    by (metis holf holomorphic_on_imp_continuous_on)
  have hol_d: "(d y) holomorphic_on U" if "y \<in> U" for y
  proof -
    have *: "(\<lambda>c. if c = y then deriv f y else (f c - f y) / (c - y)) holomorphic_on U"
      by (simp add: holf pole_lemma_open \<open>open U\<close>)
    then have "isCont (\<lambda>x. if x = y then deriv f y else (f x - f y) / (x - y)) y"
      using at_within_open field_differentiable_imp_continuous_at holomorphic_on_def that \<open>open U\<close> by fastforce
    then have "continuous_on U (d y)"
      apply (simp add: d_def continuous_on_eq_continuous_at \<open>open U\<close>, clarify)
      using * holomorphic_on_def
      by (meson field_differentiable_within_open field_differentiable_imp_continuous_at \<open>open U\<close>)
    moreover have "d y holomorphic_on U - {y}"
    proof -
      have "\<And>w. w \<in> U - {y} \<Longrightarrow>
                 (\<lambda>w. if w = y then deriv f y else (f w - f y) / (w - y)) field_differentiable at w"
        apply (rule_tac d="dist w y" and f = "\<lambda>w. (f w - f y)/(w - y)" in field_differentiable_transform_within)
           apply (auto simp: dist_pos_lt dist_commute intro!: derivative_intros)
        using \<open>open U\<close> holf holomorphic_on_imp_differentiable_at by blast
      then show ?thesis
        unfolding field_differentiable_def by (simp add: d_def holomorphic_on_open \<open>open U\<close> open_delete)
    qed
    ultimately show ?thesis
      by (rule no_isolated_singularity) (auto simp: \<open>open U\<close>)
  qed
  have cint_fxy: "(\<lambda>x. (f x - f y) / (x - y)) contour_integrable_on \<gamma>" if "y \<notin> path_image \<gamma>" for y
  proof (rule contour_integrable_holomorphic_simple [where S = "U-{y}"])
    show "(\<lambda>x. (f x - f y) / (x - y)) holomorphic_on U - {y}"
      by (force intro: holomorphic_intros holomorphic_on_subset [OF holf])
    show "path_image \<gamma> \<subseteq> U - {y}"
      using pasz that by blast
  qed (auto simp: \<open>open U\<close> open_delete \<open>valid_path \<gamma>\<close>)
  define h where
    "h z = (if z \<in> U then contour_integral \<gamma> (d z) else contour_integral \<gamma> (\<lambda>w. f w/(w - z)))" for z
  have U: "((d z) has_contour_integral h z) \<gamma>" if "z \<in> U" for z
  proof -
    have "d z holomorphic_on U"
      by (simp add: hol_d that)
    with that show ?thesis
    apply (simp add: h_def)
      by (meson Diff_subset \<open>open U\<close> \<open>valid_path \<gamma>\<close> contour_integrable_holomorphic_simple has_contour_integral_integral pasz subset_trans)
  qed
  have V: "((\<lambda>w. f w / (w - z)) has_contour_integral h z) \<gamma>" if z: "z \<in> v" for z
  proof -
    have 0: "0 = (f z) * 2 * of_real (2 * pi) * \<i> * winding_number \<gamma> z"
      using v_def z by auto
    then have "((\<lambda>x. 1 / (x - z)) has_contour_integral 0) \<gamma>"
     using z v_def  has_contour_integral_winding_number [OF \<open>valid_path \<gamma>\<close>] by fastforce
    then have "((\<lambda>x. f z * (1 / (x - z))) has_contour_integral 0) \<gamma>"
      using has_contour_integral_lmul by fastforce
    then have "((\<lambda>x. f z / (x - z)) has_contour_integral 0) \<gamma>"
      by (simp add: field_split_simps)
    moreover have "((\<lambda>x. (f x - f z) / (x - z)) has_contour_integral contour_integral \<gamma> (d z)) \<gamma>"
      using z
      apply (auto simp: v_def)
      apply (metis (no_types, lifting) contour_integrable_eq d_def has_contour_integral_eq has_contour_integral_integral cint_fxy)
      done
    ultimately have *: "((\<lambda>x. f z / (x - z) + (f x - f z) / (x - z)) has_contour_integral (0 + contour_integral \<gamma> (d z))) \<gamma>"
      by (rule has_contour_integral_add)
    have "((\<lambda>w. f w / (w - z)) has_contour_integral contour_integral \<gamma> (d z)) \<gamma>"
            if  "z \<in> U"
      using * by (auto simp: divide_simps has_contour_integral_eq)
    moreover have "((\<lambda>w. f w / (w - z)) has_contour_integral contour_integral \<gamma> (\<lambda>w. f w / (w - z))) \<gamma>"
            if "z \<notin> U"
      apply (rule has_contour_integral_integral [OF contour_integrable_holomorphic_simple [where S=U]])
      using U pasz \<open>valid_path \<gamma>\<close> that
      apply (auto intro: holomorphic_on_imp_continuous_on hol_d)
       apply (rule continuous_intros conf holomorphic_intros holf assms | force)+
      done
    ultimately show ?thesis
      using z by (simp add: h_def)
  qed
  have znot: "z \<notin> path_image \<gamma>"
    using pasz by blast
  obtain d0 where "d0>0" and d0: "\<And>x y. x \<in> path_image \<gamma> \<Longrightarrow> y \<in> - U \<Longrightarrow> d0 \<le> dist x y"
    using separate_compact_closed [of "path_image \<gamma>" "-U"] pasz \<open>open U\<close>
    by (fastforce simp add: \<open>path \<gamma>\<close> compact_path_image)
  obtain dd where "0 < dd" and dd: "{y + k | y k. y \<in> path_image \<gamma> \<and> k \<in> ball 0 dd} \<subseteq> U"
    apply (rule that [of "d0/2"])
    using \<open>0 < d0\<close>
    apply (auto simp: dist_norm dest: d0)
    done
  have "\<And>x x'. \<lbrakk>x \<in> path_image \<gamma>; dist x x' * 2 < dd\<rbrakk> \<Longrightarrow> \<exists>y k. x' = y + k \<and> y \<in> path_image \<gamma> \<and> dist 0 k * 2 \<le> dd"
    apply (rule_tac x=x in exI)
    apply (rule_tac x="x'-x" in exI)
    apply (force simp: dist_norm)
    done
  then have 1: "path_image \<gamma> \<subseteq> interior {y + k |y k. y \<in> path_image \<gamma> \<and> k \<in> cball 0 (dd / 2)}"
    apply (clarsimp simp add: mem_interior)
    using \<open>0 < dd\<close>
    apply (rule_tac x="dd/2" in exI, auto)
    done
  obtain T where "compact T" and subt: "path_image \<gamma> \<subseteq> interior T" and T: "T \<subseteq> U"
    apply (rule that [OF _ 1])
    apply (fastforce simp add: \<open>valid_path \<gamma>\<close> compact_valid_path_image intro!: compact_sums)
    apply (rule order_trans [OF _ dd])
    using \<open>0 < dd\<close> by fastforce
  obtain L where "L>0"
           and L: "\<And>f B. \<lbrakk>f holomorphic_on interior T; \<And>z. z\<in>interior T \<Longrightarrow> cmod (f z) \<le> B\<rbrakk> \<Longrightarrow>
                         cmod (contour_integral \<gamma> f) \<le> L * B"
      using contour_integral_bound_exists [OF open_interior \<open>valid_path \<gamma>\<close> subt]
      by blast
  have "bounded(f ` T)"
    by (meson \<open>compact T\<close> compact_continuous_image compact_imp_bounded conf continuous_on_subset T)
  then obtain D where "D>0" and D: "\<And>x. x \<in> T \<Longrightarrow> norm (f x) \<le> D"
    by (auto simp: bounded_pos)
  obtain C where "C>0" and C: "\<And>x. x \<in> T \<Longrightarrow> norm x \<le> C"
    using \<open>compact T\<close> bounded_pos compact_imp_bounded by force
  have "dist (h y) 0 \<le> e" if "0 < e" and le: "D * L / e + C \<le> cmod y" for e y
  proof -
    have "D * L / e > 0"  using \<open>D>0\<close> \<open>L>0\<close> \<open>e>0\<close> by simp
    with le have ybig: "norm y > C" by force
    with C have "y \<notin> T"  by force
    then have ynot: "y \<notin> path_image \<gamma>"
      using subt interior_subset by blast
    have [simp]: "winding_number \<gamma> y = 0"
      apply (rule winding_number_zero_outside [of _ "cball 0 C"])
      using ybig interior_subset subt
      apply (force simp: loop \<open>path \<gamma>\<close> dist_norm intro!: C)+
      done
    have [simp]: "h y = contour_integral \<gamma> (\<lambda>w. f w/(w - y))"
      by (rule contour_integral_unique [symmetric]) (simp add: v_def ynot V)
    have holint: "(\<lambda>w. f w / (w - y)) holomorphic_on interior T"
      apply (rule holomorphic_on_divide)
      using holf holomorphic_on_subset interior_subset T apply blast
      apply (rule holomorphic_intros)+
      using \<open>y \<notin> T\<close> interior_subset by auto
    have leD: "cmod (f z / (z - y)) \<le> D * (e / L / D)" if z: "z \<in> interior T" for z
    proof -
      have "D * L / e + cmod z \<le> cmod y"
        using le C [of z] z using interior_subset by force
      then have DL2: "D * L / e \<le> cmod (z - y)"
        using norm_triangle_ineq2 [of y z] by (simp add: norm_minus_commute)
      have "cmod (f z / (z - y)) = cmod (f z) * inverse (cmod (z - y))"
        by (simp add: norm_mult norm_inverse Fields.field_class.field_divide_inverse)
      also have "\<dots> \<le> D * (e / L / D)"
        apply (rule mult_mono)
        using that D interior_subset apply blast
        using \<open>L>0\<close> \<open>e>0\<close> \<open>D>0\<close> DL2
        apply (auto simp: norm_divide field_split_simps)
        done
      finally show ?thesis .
    qed
    have "dist (h y) 0 = cmod (contour_integral \<gamma> (\<lambda>w. f w / (w - y)))"
      by (simp add: dist_norm)
    also have "\<dots> \<le> L * (D * (e / L / D))"
      by (rule L [OF holint leD])
    also have "\<dots> = e"
      using  \<open>L>0\<close> \<open>0 < D\<close> by auto
    finally show ?thesis .
  qed
  then have "(h \<longlongrightarrow> 0) at_infinity"
    by (meson Lim_at_infinityI)
  moreover have "h holomorphic_on UNIV"
  proof -
    have con_ff: "continuous (at (x,z)) (\<lambda>(x,y). (f y - f x) / (y - x))"
                 if "x \<in> U" "z \<in> U" "x \<noteq> z" for x z
      using that conf
      apply (simp add: split_def continuous_on_eq_continuous_at \<open>open U\<close>)
      apply (simp | rule continuous_intros continuous_within_compose2 [where g=f])+
      done
    have con_fstsnd: "continuous_on UNIV (\<lambda>x. (fst x - snd x) ::complex)"
      by (rule continuous_intros)+
    have open_uu_Id: "open (U \<times> U - Id)"
      apply (rule open_Diff)
      apply (simp add: open_Times \<open>open U\<close>)
      using continuous_closed_preimage_constant [OF con_fstsnd closed_UNIV, of 0]
      apply (auto simp: Id_fstsnd_eq algebra_simps)
      done
    have con_derf: "continuous (at z) (deriv f)" if "z \<in> U" for z
      apply (rule continuous_on_interior [of U])
      apply (simp add: holf holomorphic_deriv holomorphic_on_imp_continuous_on \<open>open U\<close>)
      by (simp add: interior_open that \<open>open U\<close>)
    have tendsto_f': "((\<lambda>(x,y). if y = x then deriv f (x)
                                else (f (y) - f (x)) / (y - x)) \<longlongrightarrow> deriv f x)
                      (at (x, x) within U \<times> U)" if "x \<in> U" for x
    proof (rule Lim_withinI)
      fix e::real assume "0 < e"
      obtain k1 where "k1>0" and k1: "\<And>x'. norm (x' - x) \<le> k1 \<Longrightarrow> norm (deriv f x' - deriv f x) < e"
        using \<open>0 < e\<close> continuous_within_E [OF con_derf [OF \<open>x \<in> U\<close>]]
        by (metis UNIV_I dist_norm)
      obtain k2 where "k2>0" and k2: "ball x k2 \<subseteq> U"
        by (blast intro: openE [OF \<open>open U\<close>] \<open>x \<in> U\<close>)
      have neq: "norm ((f z' - f x') / (z' - x') - deriv f x) \<le> e"
                    if "z' \<noteq> x'" and less_k1: "norm (x'-x, z'-x) < k1" and less_k2: "norm (x'-x, z'-x) < k2"
                 for x' z'
      proof -
        have cs_less: "w \<in> closed_segment x' z' \<Longrightarrow> cmod (w - x) \<le> norm (x'-x, z'-x)" for w
          apply (drule segment_furthest_le [where y=x])
          by (metis (no_types) dist_commute dist_norm norm_fst_le norm_snd_le order_trans)
        have derf_le: "w \<in> closed_segment x' z' \<Longrightarrow> z' \<noteq> x' \<Longrightarrow> cmod (deriv f w - deriv f x) \<le> e" for w
          by (blast intro: cs_less less_k1 k1 [unfolded divide_const_simps dist_norm] less_imp_le le_less_trans)
        have f_has_der: "\<And>x. x \<in> U \<Longrightarrow> (f has_field_derivative deriv f x) (at x within U)"
          by (metis DERIV_deriv_iff_field_differentiable at_within_open holf holomorphic_on_def \<open>open U\<close>)
        have "closed_segment x' z' \<subseteq> U"
          by (rule order_trans [OF _ k2]) (simp add: cs_less  le_less_trans [OF _ less_k2] dist_complex_def norm_minus_commute subset_iff)
        then have cint_derf: "(deriv f has_contour_integral f z' - f x') (linepath x' z')"
          using contour_integral_primitive [OF f_has_der valid_path_linepath] pasz  by simp
        then have *: "((\<lambda>x. deriv f x / (z' - x')) has_contour_integral (f z' - f x') / (z' - x')) (linepath x' z')"
          by (rule has_contour_integral_div)
        have "norm ((f z' - f x') / (z' - x') - deriv f x) \<le> e/norm(z' - x') * norm(z' - x')"
          apply (rule has_contour_integral_bound_linepath [OF has_contour_integral_diff [OF *]])
          using has_contour_integral_div [where c = "z' - x'", OF has_contour_integral_const_linepath [of "deriv f x" z' x']]
                 \<open>e > 0\<close>  \<open>z' \<noteq> x'\<close>
          apply (auto simp: norm_divide divide_simps derf_le)
          done
        also have "\<dots> \<le> e" using \<open>0 < e\<close> by simp
        finally show ?thesis .
      qed
      show "\<exists>d>0. \<forall>xa\<in>U \<times> U.
                  0 < dist xa (x, x) \<and> dist xa (x, x) < d \<longrightarrow>
                  dist (case xa of (x, y) \<Rightarrow> if y = x then deriv f x else (f y - f x) / (y - x)) (deriv f x) \<le> e"
        apply (rule_tac x="min k1 k2" in exI)
        using \<open>k1>0\<close> \<open>k2>0\<close> \<open>e>0\<close>
        apply (force simp: dist_norm neq intro: dual_order.strict_trans2 k1 less_imp_le norm_fst_le)
        done
    qed
    have con_pa_f: "continuous_on (path_image \<gamma>) f"
      by (meson holf holomorphic_on_imp_continuous_on holomorphic_on_subset interior_subset subt T)
    have le_B: "\<And>T. T \<in> {0..1} \<Longrightarrow> cmod (vector_derivative \<gamma> (at T)) \<le> B"
      apply (rule B)
      using \<gamma>' using path_image_def vector_derivative_at by fastforce
    have f_has_cint: "\<And>w. w \<in> v - path_image \<gamma> \<Longrightarrow> ((\<lambda>u. f u / (u - w) ^ 1) has_contour_integral h w) \<gamma>"
      by (simp add: V)
    have cond_uu: "continuous_on (U \<times> U) (\<lambda>(x,y). d x y)"
      apply (simp add: continuous_on_eq_continuous_within d_def continuous_within tendsto_f')
      apply (simp add: tendsto_within_open_NO_MATCH open_Times \<open>open U\<close>, clarify)
      apply (rule Lim_transform_within_open [OF _ open_uu_Id, where f = "(\<lambda>(x,y). (f y - f x) / (y - x))"])
      using con_ff
      apply (auto simp: continuous_within)
      done
    have hol_dw: "(\<lambda>z. d z w) holomorphic_on U" if "w \<in> U" for w
    proof -
      have "continuous_on U ((\<lambda>(x,y). d x y) \<circ> (\<lambda>z. (w,z)))"
        by (rule continuous_on_compose continuous_intros continuous_on_subset [OF cond_uu] | force intro: that)+
      then have *: "continuous_on U (\<lambda>z. if w = z then deriv f z else (f w - f z) / (w - z))"
        by (rule rev_iffD1 [OF _ continuous_on_cong [OF refl]]) (simp add: d_def field_simps)
      have **: "\<And>x. \<lbrakk>x \<in> U; x \<noteq> w\<rbrakk> \<Longrightarrow> (\<lambda>z. if w = z then deriv f z else (f w - f z) / (w - z)) field_differentiable at x"
        apply (rule_tac f = "\<lambda>x. (f w - f x)/(w - x)" and d = "dist x w" in field_differentiable_transform_within)
        apply (rule \<open>open U\<close> derivative_intros holomorphic_on_imp_differentiable_at [OF holf] | force simp: dist_commute)+
        done
      show ?thesis
        unfolding d_def
        apply (rule no_isolated_singularity [OF * _ \<open>open U\<close>, where K = "{w}"])
        apply (auto simp: field_differentiable_def [symmetric] holomorphic_on_open open_Diff \<open>open U\<close> **)
        done
    qed
    { fix a b
      assume abu: "closed_segment a b \<subseteq> U"
      then have "\<And>w. w \<in> U \<Longrightarrow> (\<lambda>z. d z w) contour_integrable_on (linepath a b)"
        by (metis hol_dw continuous_on_subset contour_integrable_continuous_linepath holomorphic_on_imp_continuous_on)
      then have cont_cint_d: "continuous_on U (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))"
        apply (rule contour_integral_continuous_on_linepath_2D [OF \<open>open U\<close> _ _ abu])
        apply (auto intro: continuous_on_swap_args cond_uu)
        done
      have cont_cint_d\<gamma>: "continuous_on {0..1} ((\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w)) \<circ> \<gamma>)"
      proof (rule continuous_on_compose)
        show "continuous_on {0..1} \<gamma>"
          using \<open>path \<gamma>\<close> path_def by blast
        show "continuous_on (\<gamma> ` {0..1}) (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))"
          using pasz unfolding path_image_def
          by (auto intro!: continuous_on_subset [OF cont_cint_d])
      qed
      have cint_cint: "(\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w)) contour_integrable_on \<gamma>"
        apply (simp add: contour_integrable_on)
        apply (rule integrable_continuous_real)
        apply (rule continuous_on_mult [OF cont_cint_d\<gamma> [unfolded o_def]])
        using pf\<gamma>'
        by (simp add: continuous_on_polymonial_function vector_derivative_at [OF \<gamma>'])
      have "contour_integral (linepath a b) h = contour_integral (linepath a b) (\<lambda>z. contour_integral \<gamma> (d z))"
        using abu  by (force simp: h_def intro: contour_integral_eq)
      also have "\<dots> =  contour_integral \<gamma> (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))"
        apply (rule contour_integral_swap)
        apply (rule continuous_on_subset [OF cond_uu])
        using abu pasz \<open>valid_path \<gamma>\<close>
        apply (auto intro!: continuous_intros)
        by (metis \<gamma>' continuous_on_eq path_def path_polynomial_function pf\<gamma>' vector_derivative_at)
      finally have cint_h_eq:
          "contour_integral (linepath a b) h =
                    contour_integral \<gamma> (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))" .
      note cint_cint cint_h_eq
    } note cint_h = this
    have conthu: "continuous_on U h"
    proof (simp add: continuous_on_sequentially, clarify)
      fix a x
      assume x: "x \<in> U" and au: "\<forall>n. a n \<in> U" and ax: "a \<longlonglongrightarrow> x"
      then have A1: "\<forall>\<^sub>F n in sequentially. d (a n) contour_integrable_on \<gamma>"
        by (meson U contour_integrable_on_def eventuallyI)
      obtain dd where "dd>0" and dd: "cball x dd \<subseteq> U" using open_contains_cball \<open>open U\<close> x by force
      have A2: "uniform_limit (path_image \<gamma>) (\<lambda>n. d (a n)) (d x) sequentially"
        unfolding uniform_limit_iff dist_norm
      proof clarify
        fix ee::real
        assume "0 < ee"
        show "\<forall>\<^sub>F n in sequentially. \<forall>\<xi>\<in>path_image \<gamma>. cmod (d (a n) \<xi> - d x \<xi>) < ee"
        proof -
          let ?ddpa = "{(w,z) |w z. w \<in> cball x dd \<and> z \<in> path_image \<gamma>}"
          have "uniformly_continuous_on ?ddpa (\<lambda>(x,y). d x y)"
            apply (rule compact_uniformly_continuous [OF continuous_on_subset[OF cond_uu]])
            using dd pasz \<open>valid_path \<gamma>\<close>
             apply (auto simp: compact_Times compact_valid_path_image simp del: mem_cball)
            done
          then obtain kk where "kk>0"
            and kk: "\<And>x x'. \<lbrakk>x \<in> ?ddpa; x' \<in> ?ddpa; dist x' x < kk\<rbrakk> \<Longrightarrow>
                             dist ((\<lambda>(x,y). d x y) x') ((\<lambda>(x,y). d x y) x) < ee"
            by (rule uniformly_continuous_onE [where e = ee]) (use \<open>0 < ee\<close> in auto)
          have kk: "\<lbrakk>norm (w - x) \<le> dd; z \<in> path_image \<gamma>; norm ((w, z) - (x, z)) < kk\<rbrakk> \<Longrightarrow> norm (d w z - d x z) < ee"
            for  w z
            using \<open>dd>0\<close> kk [of "(x,z)" "(w,z)"] by (force simp: norm_minus_commute dist_norm)
          show ?thesis
            using ax unfolding lim_sequentially eventually_sequentially
            apply (drule_tac x="min dd kk" in spec)
            using \<open>dd > 0\<close> \<open>kk > 0\<close>
            apply (fastforce simp: kk dist_norm)
            done
        qed
      qed
      have "(\<lambda>n. contour_integral \<gamma> (d (a n))) \<longlonglongrightarrow> contour_integral \<gamma> (d x)"
        by (rule contour_integral_uniform_limit [OF A1 A2 le_B]) (auto simp: \<open>valid_path \<gamma>\<close>)
      then have tendsto_hx: "(\<lambda>n. contour_integral \<gamma> (d (a n))) \<longlonglongrightarrow> h x"
        by (simp add: h_def x)
      then show "(h \<circ> a) \<longlonglongrightarrow> h x"
        by (simp add: h_def x au o_def)
    qed
    show ?thesis
    proof (simp add: holomorphic_on_open field_differentiable_def [symmetric], clarify)
      fix z0
      consider "z0 \<in> v" | "z0 \<in> U" using uv_Un by blast
      then show "h field_differentiable at z0"
      proof cases
        assume "z0 \<in> v" then show ?thesis
          using Cauchy_next_derivative [OF con_pa_f le_B f_has_cint _ ov] V f_has_cint \<open>valid_path \<gamma>\<close>
          by (auto simp: field_differentiable_def v_def)
      next
        assume "z0 \<in> U" then
        obtain e where "e>0" and e: "ball z0 e \<subseteq> U" by (blast intro: openE [OF \<open>open U\<close>])
        have *: "contour_integral (linepath a b) h + contour_integral (linepath b c) h + contour_integral (linepath c a) h = 0"
                if abc_subset: "convex hull {a, b, c} \<subseteq> ball z0 e"  for a b c
        proof -
          have *: "\<And>x1 x2 z. z \<in> U \<Longrightarrow> closed_segment x1 x2 \<subseteq> U \<Longrightarrow> (\<lambda>w. d w z) contour_integrable_on linepath x1 x2"
            using  hol_dw holomorphic_on_imp_continuous_on \<open>open U\<close>
            by (auto intro!: contour_integrable_holomorphic_simple)
          have abc: "closed_segment a b \<subseteq> U"  "closed_segment b c \<subseteq> U"  "closed_segment c a \<subseteq> U"
            using that e segments_subset_convex_hull by fastforce+
          have eq0: "\<And>w. w \<in> U \<Longrightarrow> contour_integral (linepath a b +++ linepath b c +++ linepath c a) (\<lambda>z. d z w) = 0"
            apply (rule contour_integral_unique [OF Cauchy_theorem_triangle])
            apply (rule holomorphic_on_subset [OF hol_dw])
            using e abc_subset by auto
          have "contour_integral \<gamma>
                   (\<lambda>x. contour_integral (linepath a b) (\<lambda>z. d z x) +
                        (contour_integral (linepath b c) (\<lambda>z. d z x) +
                         contour_integral (linepath c a) (\<lambda>z. d z x)))  =  0"
            apply (rule contour_integral_eq_0)
            using abc pasz U
            apply (subst contour_integral_join [symmetric], auto intro: eq0 *)+
            done
          then show ?thesis
            by (simp add: cint_h abc contour_integrable_add contour_integral_add [symmetric] add_ac)
        qed
        show ?thesis
          using e \<open>e > 0\<close>
          by (auto intro!: holomorphic_on_imp_differentiable_at [OF _ open_ball] analytic_imp_holomorphic
                           Morera_triangle continuous_on_subset [OF conthu] *)
      qed
    qed
  qed
  ultimately have [simp]: "h z = 0" for z
    by (meson Liouville_weak)
  have "((\<lambda>w. 1 / (w - z)) has_contour_integral complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z) \<gamma>"
    by (rule has_contour_integral_winding_number [OF \<open>valid_path \<gamma>\<close> znot])
  then have "((\<lambda>w. f z * (1 / (w - z))) has_contour_integral complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z * f z) \<gamma>"
    by (metis mult.commute has_contour_integral_lmul)
  then have 1: "((\<lambda>w. f z / (w - z)) has_contour_integral complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z * f z) \<gamma>"
    by (simp add: field_split_simps)
  moreover have 2: "((\<lambda>w. (f w - f z) / (w - z)) has_contour_integral 0) \<gamma>"
    using U [OF z] pasz d_def by (force elim: has_contour_integral_eq [where g = "\<lambda>w. (f w - f z)/(w - z)"])
  show ?thesis
    using has_contour_integral_add [OF 1 2]  by (simp add: diff_divide_distrib)
qed

theorem Cauchy_integral_formula_global:
    assumes S: "open S" and holf: "f holomorphic_on S"
        and z: "z \<in> S" and vpg: "valid_path \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> S - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
        and zero: "\<And>w. w \<notin> S \<Longrightarrow> winding_number \<gamma> w = 0"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  have "path \<gamma>" using vpg by (blast intro: valid_path_imp_path)
  have hols: "(\<lambda>w. f w / (w - z)) holomorphic_on S - {z}" "(\<lambda>w. 1 / (w - z)) holomorphic_on S - {z}"
    by (rule holomorphic_intros holomorphic_on_subset [OF holf] | force)+
  then have cint_fw: "(\<lambda>w. f w / (w - z)) contour_integrable_on \<gamma>"
    by (meson contour_integrable_holomorphic_simple holomorphic_on_imp_continuous_on open_delete S vpg pasz)
  obtain d where "d>0"
      and d: "\<And>g h. \<lbrakk>valid_path g; valid_path h; \<forall>t\<in>{0..1}. cmod (g t - \<gamma> t) < d \<and> cmod (h t - \<gamma> t) < d;
                     pathstart h = pathstart g \<and> pathfinish h = pathfinish g\<rbrakk>
                     \<Longrightarrow> path_image h \<subseteq> S - {z} \<and> (\<forall>f. f holomorphic_on S - {z} \<longrightarrow> contour_integral h f = contour_integral g f)"
    using contour_integral_nearby_ends [OF _ \<open>path \<gamma>\<close> pasz] S by (simp add: open_Diff) metis
  obtain p where polyp: "polynomial_function p"
             and ps: "pathstart p = pathstart \<gamma>" and pf: "pathfinish p = pathfinish \<gamma>" and led: "\<forall>t\<in>{0..1}. cmod (p t - \<gamma> t) < d"
    using path_approx_polynomial_function [OF \<open>path \<gamma>\<close> \<open>d > 0\<close>] by blast
  then have ploop: "pathfinish p = pathstart p" using loop by auto
  have vpp: "valid_path p"  using polyp valid_path_polynomial_function by blast
  have [simp]: "z \<notin> path_image \<gamma>" using pasz by blast
  have paps: "path_image p \<subseteq> S - {z}" and cint_eq: "(\<And>f. f holomorphic_on S - {z} \<Longrightarrow> contour_integral p f = contour_integral \<gamma> f)"
    using pf ps led d [OF vpg vpp] \<open>d > 0\<close> by auto
  have wn_eq: "winding_number p z = winding_number \<gamma> z"
    using vpp paps
    by (simp add: subset_Diff_insert vpg valid_path_polynomial_function winding_number_valid_path cint_eq hols)
  have "winding_number p w = winding_number \<gamma> w" if "w \<notin> S" for w
  proof -
    have hol: "(\<lambda>v. 1 / (v - w)) holomorphic_on S - {z}"
      using that by (force intro: holomorphic_intros holomorphic_on_subset [OF holf])
   have "w \<notin> path_image p" "w \<notin> path_image \<gamma>" using paps pasz that by auto
   then show ?thesis
    using vpp vpg by (simp add: subset_Diff_insert valid_path_polynomial_function winding_number_valid_path cint_eq [OF hol])
  qed
  then have wn0: "\<And>w. w \<notin> S \<Longrightarrow> winding_number p w = 0"
    by (simp add: zero)
  show ?thesis
    using Cauchy_integral_formula_global_weak [OF S holf z polyp paps ploop wn0] hols
    by (metis wn_eq cint_eq has_contour_integral_eqpath cint_fw cint_eq)
qed

subsection \<open>Generalised Cauchy's integral theorem\<close>

theorem Cauchy_theorem_global:
    assumes S: "open S" and holf: "f holomorphic_on S"
        and vpg: "valid_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
        and pas: "path_image \<gamma> \<subseteq> S"
        and zero: "\<And>w. w \<notin> S \<Longrightarrow> winding_number \<gamma> w = 0"
      shows "(f has_contour_integral 0) \<gamma>"
proof -
  obtain z where "z \<in> S" and znot: "z \<notin> path_image \<gamma>"
  proof -
    have "compact (path_image \<gamma>)"
      using compact_valid_path_image vpg by blast
    then have "path_image \<gamma> \<noteq> S"
      by (metis (no_types) compact_open path_image_nonempty S)
    with pas show ?thesis by (blast intro: that)
  qed
  then have pasz: "path_image \<gamma> \<subseteq> S - {z}" using pas by blast
  have hol: "(\<lambda>w. (w - z) * f w) holomorphic_on S"
    by (rule holomorphic_intros holf)+
  show ?thesis
    using Cauchy_integral_formula_global [OF S hol \<open>z \<in> S\<close> vpg pasz loop zero]
    by (auto simp: znot elim!: has_contour_integral_eq)
qed

corollary Cauchy_theorem_global_outside:
    assumes "open S" "f holomorphic_on S" "valid_path \<gamma>"  "pathfinish \<gamma> = pathstart \<gamma>" "path_image \<gamma> \<subseteq> S"
            "\<And>w. w \<notin> S \<Longrightarrow> w \<in> outside(path_image \<gamma>)"
      shows "(f has_contour_integral 0) \<gamma>"
by (metis Cauchy_theorem_global assms winding_number_zero_in_outside valid_path_imp_path)

lemma Cauchy_theorem_simply_connected:
  assumes "open S" "simply_connected S" "f holomorphic_on S" "valid_path g"
           "path_image g \<subseteq> S" "pathfinish g = pathstart g"
    shows "(f has_contour_integral 0) g"
using assms
apply (simp add: simply_connected_eq_contractible_path)
apply (auto intro!: Cauchy_theorem_null_homotopic [where a = "pathstart g"]
                         homotopic_paths_imp_homotopic_loops)
using valid_path_imp_path by blast

end