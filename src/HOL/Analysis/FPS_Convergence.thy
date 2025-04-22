(*  
  Title:    HOL/Analysis/FPS_Convergence.thy
  Author:   Manuel Eberl, TU München

  Connection of formal power series and actual convergent power series on Banach spaces
  (most notably the complex numbers).
*)
section \<open>Convergence of Formal Power Series\<close>

theory FPS_Convergence
imports
  Generalised_Binomial_Theorem
  "HOL-Computational_Algebra.Formal_Power_Series" 
  "HOL-Computational_Algebra.Polynomial_FPS"

begin

text \<open>
  In this theory, we will connect formal power series (which are algebraic objects) with analytic
  functions. This will become more important in complex analysis, and indeed some of the less
  trivial results will only be proven there.
\<close>

subsection\<^marker>\<open>tag unimportant\<close> \<open>Balls with extended real radius\<close>

(* TODO: This should probably go somewhere else *)

text \<open>
  The following is a variant of \<^const>\<open>ball\<close> that also allows an infinite radius.
\<close>
definition eball :: "'a :: metric_space \<Rightarrow> ereal \<Rightarrow> 'a set" where
  "eball z r = {z'. ereal (dist z z') < r}"

lemma in_eball_iff [simp]: "z \<in> eball z0 r \<longleftrightarrow> ereal (dist z0 z) < r"
  by (simp add: eball_def)

lemma eball_ereal [simp]: "eball z (ereal r) = ball z r"
  by auto

lemma eball_inf [simp]: "eball z \<infinity> = UNIV"
  by auto

lemma eball_empty [simp]: "r \<le> 0 \<Longrightarrow> eball z r = {}"
proof safe
  fix x assume "r \<le> 0" "x \<in> eball z r"
  hence "dist z x < r" by simp
  also have "\<dots> \<le> ereal 0" using \<open>r \<le> 0\<close> by (simp add: zero_ereal_def)
  finally show "x \<in> {}" by simp
qed

lemma eball_conv_UNION_balls:
  "eball z r = (\<Union>r'\<in>{r'. ereal r' < r}. ball z r')"
  by (cases r) (use dense gt_ex in force)+

lemma eball_mono: "r \<le> r' \<Longrightarrow> eball z r \<le> eball z r'"
  by auto

lemma ball_eball_mono: "ereal r \<le> r' \<Longrightarrow> ball z r \<le> eball z r'"
  using eball_mono[of "ereal r" r'] by simp

lemma open_eball [simp, intro]: "open (eball z r)" 
  by (cases r) auto

lemma connected_eball [intro]: "connected (eball (z :: 'a :: real_normed_vector) r)"
  by (cases r) auto


subsection \<open>Basic properties of convergent power series\<close>

definition\<^marker>\<open>tag important\<close> fps_conv_radius :: "'a :: {banach, real_normed_div_algebra} fps \<Rightarrow> ereal" where
  "fps_conv_radius f = conv_radius (fps_nth f)"

definition\<^marker>\<open>tag important\<close> eval_fps :: "'a :: {banach, real_normed_div_algebra} fps \<Rightarrow> 'a \<Rightarrow> 'a" where
  "eval_fps f z = (\<Sum>n. fps_nth f n * z ^ n)"

lemma norm_summable_fps:
  fixes f :: "'a :: {banach, real_normed_div_algebra} fps"
  shows "norm z < fps_conv_radius f \<Longrightarrow> summable (\<lambda>n. norm (fps_nth f n * z ^ n))"
  by (rule abs_summable_in_conv_radius) (simp_all add: fps_conv_radius_def)

lemma summable_fps:
  fixes f :: "'a :: {banach, real_normed_div_algebra} fps"
  shows "norm z < fps_conv_radius f \<Longrightarrow> summable (\<lambda>n. fps_nth f n * z ^ n)"
  by (rule summable_in_conv_radius) (simp_all add: fps_conv_radius_def)

theorem sums_eval_fps:
  fixes f :: "'a :: {banach, real_normed_div_algebra} fps"
  assumes "norm z < fps_conv_radius f"
  shows   "(\<lambda>n. fps_nth f n * z ^ n) sums eval_fps f z"
  using assms unfolding eval_fps_def fps_conv_radius_def
  by (intro summable_sums summable_in_conv_radius) simp_all

lemma continuous_on_eval_fps:
  fixes f :: "'a :: {banach, real_normed_div_algebra} fps"
  shows "continuous_on (eball 0 (fps_conv_radius f)) (eval_fps f)"
proof (subst continuous_on_eq_continuous_at [OF open_eball], safe)
  fix x :: 'a assume x: "x \<in> eball 0 (fps_conv_radius f)"
  define r where "r = (if fps_conv_radius f = \<infinity> then norm x + 1 else
                        (norm x + real_of_ereal (fps_conv_radius f)) / 2)"
  have r: "norm x < r \<and> ereal r < fps_conv_radius f"
    using x by (cases "fps_conv_radius f") 
               (auto simp: r_def eball_def split: if_splits)

  have "continuous_on (cball 0 r) (\<lambda>x. \<Sum>i. fps_nth f i * (x - 0) ^ i)"
    by (rule powser_continuous_suminf) (insert r, auto simp: fps_conv_radius_def)
  hence "continuous_on (cball 0 r) (eval_fps f)"
    by (simp add: eval_fps_def)
  thus "isCont (eval_fps f) x"
    by (rule continuous_on_interior) (use r in auto)
qed

lemma continuous_on_eval_fps' [continuous_intros]:
  assumes "continuous_on A g"
  assumes "g ` A \<subseteq> eball 0 (fps_conv_radius f)"
  shows   "continuous_on A (\<lambda>x. eval_fps f (g x))"
  using continuous_on_compose2[OF continuous_on_eval_fps assms] .

lemma has_field_derivative_powser:
  fixes z :: "'a :: {banach, real_normed_field}"
  assumes "ereal (norm z) < conv_radius f"
  shows   "((\<lambda>z. \<Sum>n. f n * z ^ n) has_field_derivative (\<Sum>n. diffs f n * z ^ n)) (at z within A)"
proof -
  define K where "K = (if conv_radius f = \<infinity> then norm z + 1 
                         else (norm z + real_of_ereal (conv_radius f)) / 2)"
  have K: "norm z < K \<and> ereal K < conv_radius f"
    using assms by (cases "conv_radius f") (auto simp: K_def)
  have "0 \<le> norm z" by simp
  also from K have "\<dots> < K" by simp
  finally have K_pos: "K > 0" by simp

  have "summable (\<lambda>n. f n * of_real K ^ n)"
    using K and K_pos by (intro summable_in_conv_radius) auto
  moreover from K and K_pos have "norm z < norm (of_real K :: 'a)" by auto
  ultimately show ?thesis
    by (rule has_field_derivative_at_within [OF termdiffs_strong])
qed

lemma has_field_derivative_eval_fps:
  fixes z :: "'a :: {banach, real_normed_field}"
  assumes "norm z < fps_conv_radius f"
  shows   "(eval_fps f has_field_derivative eval_fps (fps_deriv f) z) (at z within A)"
proof -
  have "(eval_fps f has_field_derivative eval_fps (Abs_fps (diffs (fps_nth f))) z) (at z within A)"
    using assms unfolding eval_fps_def fps_nth_Abs_fps fps_conv_radius_def
    by (intro has_field_derivative_powser) auto
  also have "Abs_fps (diffs (fps_nth f)) = fps_deriv f"
    by (simp add: fps_eq_iff diffs_def)
  finally show ?thesis .
qed

lemma holomorphic_on_eval_fps [holomorphic_intros]:
  fixes z :: "'a :: {banach, real_normed_field}"
  assumes "A \<subseteq> eball 0 (fps_conv_radius f)"
  shows   "eval_fps f holomorphic_on A"
proof (rule holomorphic_on_subset [OF _ assms])
  show "eval_fps f holomorphic_on eball 0 (fps_conv_radius f)"
  proof (subst holomorphic_on_open [OF open_eball], safe, goal_cases)
    case (1 x)
    thus ?case
      by (intro exI[of _ "eval_fps (fps_deriv f) x"]) (auto intro: has_field_derivative_eval_fps)
  qed
qed

lemma analytic_on_eval_fps:
  fixes z :: "'a :: {banach, real_normed_field}"
  assumes "A \<subseteq> eball 0 (fps_conv_radius f)"
  shows   "eval_fps f analytic_on A"
proof (rule analytic_on_subset [OF _ assms])
  show "eval_fps f analytic_on eball 0 (fps_conv_radius f)"
    using holomorphic_on_eval_fps[of "eball 0 (fps_conv_radius f)"] 
    by (subst analytic_on_open) auto
qed

lemma continuous_eval_fps [continuous_intros]:
  fixes z :: "'a::{real_normed_field,banach}"
  assumes "norm z < fps_conv_radius F"
  shows   "continuous (at z within A) (eval_fps F)"
proof -
  from ereal_dense2[OF assms] obtain K :: real where K: "norm z < K" "K < fps_conv_radius F"
    by auto
  have "0 \<le> norm z" by simp
  also have "norm z < K" by fact
  finally have "K > 0" .
  from K and \<open>K > 0\<close> have "summable (\<lambda>n. fps_nth F n * of_real K ^ n)"
    by (intro summable_fps) auto
  from this have "isCont (eval_fps F) z" unfolding eval_fps_def
    by (rule isCont_powser) (use K in auto)
  thus "continuous (at z within A)  (eval_fps F)"
    by (simp add: continuous_at_imp_continuous_within)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Lower bounds on radius of convergence\<close>

lemma fps_conv_radius_deriv:
  fixes f :: "'a :: {banach, real_normed_field} fps"
  shows "fps_conv_radius (fps_deriv f) \<ge> fps_conv_radius f"
  unfolding fps_conv_radius_def
proof (rule conv_radius_geI_ex)
  fix r :: real assume r: "r > 0" "ereal r < conv_radius (fps_nth f)"
  define K where "K = (if conv_radius (fps_nth f) = \<infinity> then r + 1 
                         else (real_of_ereal (conv_radius (fps_nth f)) + r) / 2)"
  have K: "r < K \<and> ereal K < conv_radius (fps_nth f)"
    using r by (cases "conv_radius (fps_nth f)") (auto simp: K_def)
  have "summable (\<lambda>n. diffs (fps_nth f) n * of_real r ^ n)"
  proof (rule termdiff_converges)
    fix x :: 'a assume "norm x < K"
    hence "ereal (norm x) < ereal K" by simp
    also have "\<dots> < conv_radius (fps_nth f)" using K by simp
    finally show "summable (\<lambda>n. fps_nth f n * x ^ n)"
      by (intro summable_in_conv_radius) auto
  qed (insert K r, auto)
  also have "\<dots> = (\<lambda>n. fps_nth (fps_deriv f) n * of_real r ^ n)"
    by (simp add: fps_deriv_def diffs_def)
  finally show "\<exists>z::'a. norm z = r \<and> summable (\<lambda>n. fps_nth (fps_deriv f) n * z ^ n)"
    using r by (intro exI[of _ "of_real r"]) auto
qed

lemma eval_fps_at_0: "eval_fps f 0 = fps_nth f 0"
  by (simp add: eval_fps_def)

lemma fps_conv_radius_norm [simp]: 
  "fps_conv_radius (Abs_fps (\<lambda>n. norm (fps_nth f n))) = fps_conv_radius f"
  by (simp add: fps_conv_radius_def)

lemma fps_conv_radius_const [simp]: "fps_conv_radius (fps_const c) = \<infinity>"
proof -
  have "fps_conv_radius (fps_const c) = conv_radius (\<lambda>_. 0 :: 'a)"
    unfolding fps_conv_radius_def
    by (intro conv_radius_cong eventually_mono[OF eventually_gt_at_top[of 0]]) auto
  thus ?thesis by simp
qed

lemma fps_conv_radius_0 [simp]: "fps_conv_radius 0 = \<infinity>"
  by (simp only: fps_const_0_eq_0 [symmetric] fps_conv_radius_const)

lemma fps_conv_radius_1 [simp]: "fps_conv_radius 1 = \<infinity>"
  by (simp only: fps_const_1_eq_1 [symmetric] fps_conv_radius_const)

lemma fps_conv_radius_numeral [simp]: "fps_conv_radius (numeral n) = \<infinity>"
  by (simp add: numeral_fps_const)

lemma fps_conv_radius_fps_X_power [simp]: "fps_conv_radius (fps_X ^ n) = \<infinity>"
proof -
  have "fps_conv_radius (fps_X ^ n :: 'a fps) = conv_radius (\<lambda>_. 0 :: 'a)"
    unfolding fps_conv_radius_def 
    by (intro conv_radius_cong eventually_mono[OF eventually_gt_at_top[of n]]) 
       (auto simp: fps_X_power_iff)
  thus ?thesis by simp
qed

lemma fps_conv_radius_fps_X [simp]: "fps_conv_radius fps_X = \<infinity>"
  using fps_conv_radius_fps_X_power[of 1] by (simp only: power_one_right)

lemma fps_conv_radius_shift [simp]:
  "fps_conv_radius (fps_shift n f) = fps_conv_radius f"
  by (simp add: fps_conv_radius_def fps_shift_def conv_radius_shift)

lemma fps_conv_radius_cmult_left:
  "c \<noteq> 0 \<Longrightarrow> fps_conv_radius (fps_const c * f) = fps_conv_radius f"
  unfolding fps_conv_radius_def by (simp add: conv_radius_cmult_left)

lemma fps_conv_radius_cmult_right:
  "c \<noteq> 0 \<Longrightarrow> fps_conv_radius (f * fps_const c) = fps_conv_radius f"
  unfolding fps_conv_radius_def by (simp add: conv_radius_cmult_right)

lemma fps_conv_radius_uminus [simp]:
  "fps_conv_radius (-f) = fps_conv_radius f"
  using fps_conv_radius_cmult_left[of "-1" f]
  by (simp flip: fps_const_neg)

lemma fps_conv_radius_add: "fps_conv_radius (f + g) \<ge> min (fps_conv_radius f) (fps_conv_radius g)"
  unfolding fps_conv_radius_def using conv_radius_add_ge[of "fps_nth f" "fps_nth g"]
  by simp

lemma fps_conv_radius_diff: "fps_conv_radius (f - g) \<ge> min (fps_conv_radius f) (fps_conv_radius g)"
  using fps_conv_radius_add[of f "-g"] by simp

lemma fps_conv_radius_mult: "fps_conv_radius (f * g) \<ge> min (fps_conv_radius f) (fps_conv_radius g)"
  using conv_radius_mult_ge[of "fps_nth f" "fps_nth g"]
  by (simp add: fps_mult_nth fps_conv_radius_def atLeast0AtMost)

lemma fps_conv_radius_power: "fps_conv_radius (f ^ n) \<ge> fps_conv_radius f"
proof (induction n)
  case (Suc n)
  hence "fps_conv_radius f \<le> min (fps_conv_radius f) (fps_conv_radius (f ^ n))"
    by simp
  also have "\<dots> \<le> fps_conv_radius (f * f ^ n)" 
    by (rule fps_conv_radius_mult)
  finally show ?case by simp
qed simp_all

context
begin

lemma natfun_inverse_bound:
  fixes f :: "'a :: {real_normed_field} fps"
  assumes "fps_nth f 0 = 1" and "\<delta> > 0" 
      and summable: "summable (\<lambda>n. norm (fps_nth f (Suc n)) * \<delta> ^ Suc n)"
      and le: "(\<Sum>n. norm (fps_nth f (Suc n)) * \<delta> ^ Suc n) \<le> 1"
  shows   "norm (natfun_inverse f n) \<le> inverse (\<delta> ^ n)"
proof (induction n rule: less_induct)
  case (less m)
  show ?case
  proof (cases m)
    case 0
    thus ?thesis using assms by (simp add: field_split_simps norm_inverse norm_divide)
  next
    case [simp]: (Suc n)
    have "norm (natfun_inverse f (Suc n)) = 
            norm (\<Sum>i = Suc 0..Suc n. fps_nth f i * natfun_inverse f (Suc n - i))"
      (is "_ = norm ?S") using assms 
      by (simp add: field_simps norm_mult norm_divide del: sum.cl_ivl_Suc)
    also have "norm ?S \<le> (\<Sum>i = Suc 0..Suc n. norm (fps_nth f i * natfun_inverse f (Suc n - i)))"
      by (rule norm_sum)
    also have "\<dots> \<le> (\<Sum>i = Suc 0..Suc n. norm (fps_nth f i) / \<delta> ^ (Suc n - i))"
    proof (intro sum_mono, goal_cases)
      case (1 i)
      have "norm (fps_nth f i * natfun_inverse f (Suc n - i)) =
              norm (fps_nth f i) * norm (natfun_inverse f (Suc n - i))"
        by (simp add: norm_mult)
      also have "\<dots> \<le> norm (fps_nth f i) * inverse (\<delta> ^ (Suc n - i))"
        using 1 by (intro mult_left_mono less.IH) auto
      also have "\<dots> = norm (fps_nth f i) / \<delta> ^ (Suc n - i)"
        by (simp add: field_split_simps)
      finally show ?case .
    qed
    also have "\<dots> = (\<Sum>i = Suc 0..Suc n. norm (fps_nth f i) * \<delta> ^ i) / \<delta> ^ Suc n"
      by (subst sum_divide_distrib, rule sum.cong)
         (insert \<open>\<delta> > 0\<close>, auto simp: field_simps power_diff)
    also have "(\<Sum>i = Suc 0..Suc n. norm (fps_nth f i) * \<delta> ^ i) =
                 (\<Sum>i=0..n. norm (fps_nth f (Suc i)) * \<delta> ^ (Suc i))"
      by (subst sum.atLeast_Suc_atMost_Suc_shift) simp_all
    also have "{0..n} = {..<Suc n}" by auto
    also have "(\<Sum>i< Suc n. norm (fps_nth f (Suc i)) * \<delta> ^ (Suc i)) \<le> 
                 (\<Sum>n. norm (fps_nth f (Suc n)) * \<delta> ^ (Suc n))"
      using \<open>\<delta> > 0\<close> by (intro sum_le_suminf ballI mult_nonneg_nonneg zero_le_power summable) auto
    also have "\<dots> \<le> 1" by fact
    finally show ?thesis using \<open>\<delta> > 0\<close> 
      by (simp add: divide_right_mono field_split_simps)
  qed
qed

private lemma fps_conv_radius_inverse_pos_aux:
  fixes f :: "'a :: {banach, real_normed_field} fps"
  assumes "fps_nth f 0 = 1" "fps_conv_radius f > 0"
  shows   "fps_conv_radius (inverse f) > 0"
proof -
  let ?R = "fps_conv_radius f"
  define h where "h = Abs_fps (\<lambda>n. norm (fps_nth f n))"
  have [simp]: "fps_conv_radius h = ?R" by (simp add: h_def)
  have "continuous_on (eball 0 (fps_conv_radius h)) (eval_fps h)"
    by (intro continuous_on_eval_fps)
  hence *: "open (eval_fps h -` A \<inter> eball 0 ?R)" if "open A" for A
    using that by (subst (asm) continuous_on_open_vimage) auto
  have "open (eval_fps h -` {..<2} \<inter> eball 0 ?R)"
    by (rule *) auto
  moreover have "0 \<in> eval_fps h -` {..<2} \<inter> eball 0 ?R"
    using assms by (auto simp: eball_def zero_ereal_def eval_fps_at_0 h_def)
  ultimately obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "ball 0 \<epsilon> \<subseteq> eval_fps h -` {..<2} \<inter> eball 0 ?R"
    by (subst (asm) open_contains_ball_eq) blast+

  define \<delta> where "\<delta> = real_of_ereal (min (ereal \<epsilon> / 2) (?R / 2))"
  have \<delta>: "0 < \<delta> \<and> \<delta> < \<epsilon> \<and> ereal \<delta> < ?R"
    using \<open>\<epsilon> > 0\<close> and assms by (cases ?R) (auto simp: \<delta>_def min_def)

  have summable: "summable (\<lambda>n. norm (fps_nth f n) * \<delta> ^ n)"
    using \<delta> by (intro summable_in_conv_radius) (simp_all add: fps_conv_radius_def)
  hence "(\<lambda>n. norm (fps_nth f n) * \<delta> ^ n) sums eval_fps h \<delta>"
    by (simp add: eval_fps_def summable_sums h_def)
  hence "(\<lambda>n. norm (fps_nth f (Suc n)) * \<delta> ^ Suc n) sums (eval_fps h \<delta> - 1)"
    by (subst sums_Suc_iff) (auto simp: assms)
  moreover {
    from \<delta> have "\<delta> \<in> ball 0 \<epsilon>" by auto
    also have "\<dots> \<subseteq> eval_fps h -` {..<2} \<inter> eball 0 ?R" by fact
    finally have "eval_fps h \<delta> < 2" by simp
  }
  ultimately have le: "(\<Sum>n. norm (fps_nth f (Suc n)) * \<delta> ^ Suc n) \<le> 1"
    by (simp add: sums_iff)
  from summable have summable: "summable (\<lambda>n. norm (fps_nth f (Suc n)) * \<delta> ^ Suc n)"
    by (subst summable_Suc_iff)

  have "0 < \<delta>" using \<delta> by blast
  also have "\<delta> = inverse (limsup (\<lambda>n. ereal (inverse \<delta>)))"
    using \<delta> by (subst Limsup_const) auto
  also have "\<dots> \<le> conv_radius (natfun_inverse f)"
    unfolding conv_radius_def
  proof (intro ereal_inverse_antimono Limsup_mono
           eventually_mono[OF eventually_gt_at_top[of 0]])
    fix n :: nat assume n: "n > 0"
    have "root n (norm (natfun_inverse f n)) \<le> root n (inverse (\<delta> ^ n))"
      using n assms \<delta> le summable 
      by (intro real_root_le_mono natfun_inverse_bound) auto
    also have "\<dots> = inverse \<delta>"
      using n \<delta> by (simp add: power_inverse [symmetric] real_root_pos2)
    finally show "ereal (inverse \<delta>) \<ge> ereal (root n (norm (natfun_inverse f n)))" 
      by (subst ereal_less_eq)
  next
    have "0 = limsup (\<lambda>n. 0::ereal)" 
      by (rule Limsup_const [symmetric]) auto
    also have "\<dots> \<le> limsup (\<lambda>n. ereal (root n (norm (natfun_inverse f n))))"
      by (intro Limsup_mono) (auto simp: real_root_ge_zero)
    finally show "0 \<le> \<dots>" by simp
  qed
  also have "\<dots> = fps_conv_radius (inverse f)"
    using assms by (simp add: fps_conv_radius_def fps_inverse_def)
  finally show ?thesis by (simp add: zero_ereal_def)
qed

lemma fps_conv_radius_inverse_pos:
  fixes f :: "'a :: {banach, real_normed_field} fps"
  assumes "fps_nth f 0 \<noteq> 0" and "fps_conv_radius f > 0"
  shows   "fps_conv_radius (inverse f) > 0"
proof -
  let ?c = "fps_nth f 0"
  have "fps_conv_radius (inverse f) = fps_conv_radius (fps_const ?c * inverse f)"
    using assms by (subst fps_conv_radius_cmult_left) auto
  also have "fps_const ?c * inverse f = inverse (fps_const (inverse ?c) * f)"
    using assms by (simp add: fps_inverse_mult fps_const_inverse)
  also have "fps_conv_radius \<dots> > 0" using assms
    by (intro fps_conv_radius_inverse_pos_aux)
       (auto simp: fps_conv_radius_cmult_left)
  finally show ?thesis .
qed

end

lemma fps_conv_radius_exp [simp]: 
  fixes c :: "'a :: {banach, real_normed_field}"
  shows "fps_conv_radius (fps_exp c) = \<infinity>"
  unfolding fps_conv_radius_def
proof (rule conv_radius_inftyI'')
  fix z :: 'a
  have "(\<lambda>n. norm (c * z) ^ n /\<^sub>R fact n) sums exp (norm (c * z))"
    by (rule exp_converges)
  also have "(\<lambda>n. norm (c * z) ^ n /\<^sub>R fact n) = (\<lambda>n. norm (fps_nth (fps_exp c) n * z ^ n))"
    by (rule ext) (simp add: norm_divide norm_mult norm_power field_split_simps)
  finally have "summable \<dots>" by (simp add: sums_iff)
  thus "summable (\<lambda>n. fps_nth (fps_exp c) n * z ^ n)"
    by (rule summable_norm_cancel)
qed


subsection \<open>Evaluating power series\<close>

theorem eval_fps_deriv:
  assumes "norm z < fps_conv_radius f"
  shows   "eval_fps (fps_deriv f) z = deriv (eval_fps f) z"
  by (intro DERIV_imp_deriv [symmetric] has_field_derivative_eval_fps assms)

theorem fps_nth_conv_deriv:
  fixes f :: "complex fps"
  assumes "fps_conv_radius f > 0"
  shows   "fps_nth f n = (deriv ^^ n) (eval_fps f) 0 / fact n"
  using assms
proof (induction n arbitrary: f)
  case 0
  thus ?case by (simp add: eval_fps_def)
next
  case (Suc n f)
  have "(deriv ^^ Suc n) (eval_fps f) 0 = (deriv ^^ n) (deriv (eval_fps f)) 0"
    unfolding funpow_Suc_right o_def ..
  also have "eventually (\<lambda>z::complex. z \<in> eball 0 (fps_conv_radius f)) (nhds 0)"
    using Suc.prems by (intro eventually_nhds_in_open) (auto simp: zero_ereal_def)
  hence "eventually (\<lambda>z. deriv (eval_fps f) z = eval_fps (fps_deriv f) z) (nhds 0)"
    by eventually_elim (simp add: eval_fps_deriv)
  hence "(deriv ^^ n) (deriv (eval_fps f)) 0 = (deriv ^^ n) (eval_fps (fps_deriv f)) 0"
    by (intro higher_deriv_cong_ev refl)
  also have "\<dots> / fact n = fps_nth (fps_deriv f) n"
    using Suc.prems fps_conv_radius_deriv[of f] 
    by (intro Suc.IH [symmetric]) auto
  also have "\<dots> / of_nat (Suc n) = fps_nth f (Suc n)"
    by (simp add: fps_deriv_def del: of_nat_Suc)
  finally show ?case by (simp add: field_split_simps)
qed

theorem eval_fps_eqD:
  fixes f g :: "complex fps"
  assumes "fps_conv_radius f > 0" "fps_conv_radius g > 0"
  assumes "eventually (\<lambda>z. eval_fps f z = eval_fps g z) (nhds 0)"
  shows   "f = g"
proof (rule fps_ext)
  fix n :: nat
  have "fps_nth f n = (deriv ^^ n) (eval_fps f) 0 / fact n"
    using assms by (intro fps_nth_conv_deriv)
  also have "(deriv ^^ n) (eval_fps f) 0 = (deriv ^^ n) (eval_fps g) 0"
    by (intro higher_deriv_cong_ev refl assms)
  also have "\<dots> / fact n = fps_nth g n"
    using assms by (intro fps_nth_conv_deriv [symmetric])
  finally show "fps_nth f n = fps_nth g n" .
qed

lemma eval_fps_const [simp]: 
  fixes c :: "'a :: {banach, real_normed_div_algebra}"
  shows "eval_fps (fps_const c) z = c"
proof -
  have "(\<lambda>n::nat. if n \<in> {0} then c else 0) sums (\<Sum>n\<in>{0::nat}. c)"
    by (rule sums_If_finite_set) auto
  also have "?this \<longleftrightarrow> (\<lambda>n::nat. fps_nth (fps_const c) n * z ^ n) sums (\<Sum>n\<in>{0::nat}. c)"
    by (intro sums_cong) auto
  also have "(\<Sum>n\<in>{0::nat}. c) = c" 
    by simp
  finally show ?thesis
    by (simp add: eval_fps_def sums_iff)
qed

lemma eval_fps_0 [simp]:
  "eval_fps (0 :: 'a :: {banach, real_normed_div_algebra} fps) z = 0"
  by (simp only: fps_const_0_eq_0 [symmetric] eval_fps_const)

lemma eval_fps_1 [simp]:
  "eval_fps (1 :: 'a :: {banach, real_normed_div_algebra} fps) z = 1"
  by (simp only: fps_const_1_eq_1 [symmetric] eval_fps_const)

lemma eval_fps_numeral [simp]:
  "eval_fps (numeral n :: 'a :: {banach, real_normed_div_algebra} fps) z = numeral n"
  by (simp only: numeral_fps_const eval_fps_const)

lemma eval_fps_X_power [simp]:
  "eval_fps (fps_X ^ m :: 'a :: {banach, real_normed_div_algebra} fps) z = z ^ m"
proof -
  have "(\<lambda>n::nat. if n \<in> {m} then z ^ n else 0 :: 'a) sums (\<Sum>n\<in>{m::nat}. z ^ n)"
    by (rule sums_If_finite_set) auto
  also have "?this \<longleftrightarrow> (\<lambda>n::nat. fps_nth (fps_X ^ m) n * z ^ n) sums (\<Sum>n\<in>{m::nat}. z ^ n)"
    by (intro sums_cong) (auto simp: fps_X_power_iff)
  also have "(\<Sum>n\<in>{m::nat}. z ^ n) = z ^ m"
    by simp
  finally show ?thesis
    by (simp add: eval_fps_def sums_iff)
qed

lemma eval_fps_X [simp]:
  "eval_fps (fps_X :: 'a :: {banach, real_normed_div_algebra} fps) z = z"
  using eval_fps_X_power[of 1 z] by (simp only: power_one_right)

lemma eval_fps_minus:
  fixes f :: "'a :: {banach, real_normed_div_algebra} fps"
  assumes "norm z < fps_conv_radius f"
  shows   "eval_fps (-f) z = -eval_fps f z"
  using assms unfolding eval_fps_def
  by (subst suminf_minus [symmetric]) (auto intro!: summable_fps)

lemma eval_fps_add:
  fixes f g :: "'a :: {banach, real_normed_div_algebra} fps"
  assumes "norm z < fps_conv_radius f" "norm z < fps_conv_radius g"
  shows   "eval_fps (f + g) z = eval_fps f z + eval_fps g z"
  using assms unfolding eval_fps_def
  by (subst suminf_add) (auto simp: ring_distribs intro!: summable_fps)

lemma eval_fps_diff:
  fixes f g :: "'a :: {banach, real_normed_div_algebra} fps"
  assumes "norm z < fps_conv_radius f" "norm z < fps_conv_radius g"
  shows   "eval_fps (f - g) z = eval_fps f z - eval_fps g z"
  using assms unfolding eval_fps_def
  by (subst suminf_diff) (auto simp: ring_distribs intro!: summable_fps)

lemma eval_fps_mult:
  fixes f g :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "norm z < fps_conv_radius f" "norm z < fps_conv_radius g"
  shows   "eval_fps (f * g) z = eval_fps f z * eval_fps g z"
proof -
  have "eval_fps f z * eval_fps g z = 
          (\<Sum>k. \<Sum>i\<le>k. fps_nth f i * fps_nth g (k - i) * (z ^ i * z ^ (k - i)))"
    unfolding eval_fps_def
  proof (subst Cauchy_product)
    show "summable (\<lambda>k. norm (fps_nth f k * z ^ k))" "summable (\<lambda>k. norm (fps_nth g k * z ^ k))"
      by (rule norm_summable_fps assms)+
  qed (simp_all add: algebra_simps)
  also have "(\<lambda>k. \<Sum>i\<le>k. fps_nth f i * fps_nth g (k - i) * (z ^ i * z ^ (k - i))) =
               (\<lambda>k. \<Sum>i\<le>k. fps_nth f i * fps_nth g (k - i) * z ^ k)"
    by (intro ext sum.cong refl) (simp add: power_add [symmetric])
  also have "suminf \<dots> = eval_fps (f * g) z"
    by (simp add: eval_fps_def fps_mult_nth atLeast0AtMost sum_distrib_right)
  finally show ?thesis ..
qed

lemma eval_fps_shift:
  fixes f :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "n \<le> subdegree f" "norm z < fps_conv_radius f"
  shows   "eval_fps (fps_shift n f) z = (if z = 0 then fps_nth f n else eval_fps f z / z ^ n)"
proof (cases "z = 0")
  case False
  have "eval_fps (fps_shift n f * fps_X ^ n) z = eval_fps (fps_shift n f) z * z ^ n"
    using assms by (subst eval_fps_mult) simp_all
  also from assms have "fps_shift n f * fps_X ^ n = f"
    by (simp add: fps_shift_times_fps_X_power)
  finally show ?thesis using False by (simp add: field_simps)
qed (simp_all add: eval_fps_at_0)

lemma eval_fps_exp [simp]:
  fixes c :: "'a :: {banach, real_normed_field}"
  shows "eval_fps (fps_exp c) z = exp (c * z)" unfolding eval_fps_def exp_def
  by (simp add: eval_fps_def exp_def scaleR_conv_of_real field_split_simps)

text \<open>
  The case of division is more complicated and will therefore not be handled here.
  Handling division becomes much more easy using complex analysis, and we will do so once
  that is available.
\<close>

subsection \<open>FPS of a polynomial\<close>

lemma fps_conv_radius_fps_of_poly [simp]:
  fixes p :: "'a :: {banach, real_normed_div_algebra} poly"
  shows "fps_conv_radius (fps_of_poly p) = \<infinity>"
proof -
  have "conv_radius (poly.coeff p) = conv_radius (\<lambda>_. 0 :: 'a)"
    using MOST_coeff_eq_0 unfolding cofinite_eq_sequentially by (rule conv_radius_cong')
  also have "\<dots> = \<infinity>"
    by simp
  finally show ?thesis
    by (simp add: fps_conv_radius_def)
qed

lemma eval_fps_power: 
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes z: "norm z < fps_conv_radius F"
  shows      "eval_fps (F ^ n) z = eval_fps F z ^ n"
proof (induction n)
  case 0
  thus ?case
    by (auto simp: eval_fps_mult)
next
  case (Suc n)
  have "eval_fps (F ^ Suc n) z = eval_fps (F * F ^ n) z"
    by simp
  also from z have "\<dots> = eval_fps F z * eval_fps (F ^ n) z"
    by (subst eval_fps_mult) (auto intro!: less_le_trans[OF _ fps_conv_radius_power])
  finally show ?case
    using Suc.IH by simp
qed   

lemma eval_fps_of_poly [simp]: "eval_fps (fps_of_poly p) z = poly p z"
proof -
  have "(\<lambda>n. poly.coeff p n * z ^ n) sums poly p z"
    unfolding poly_altdef by (rule sums_finite) (auto simp: coeff_eq_0)
  moreover have "(\<lambda>n. poly.coeff p n * z ^ n) sums eval_fps (fps_of_poly p) z"
    using sums_eval_fps[of z "fps_of_poly p"] by simp
  ultimately show ?thesis
    using sums_unique2 by blast
qed

lemma poly_holomorphic_on [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A"
  shows   "(\<lambda>z. poly p (f z)) holomorphic_on A"
  unfolding poly_altdef by (intro holomorphic_intros)

subsection \<open>Power series expansions of analytic functions\<close>

text \<open>
  This predicate contains the notion that the given formal power series converges
  in some disc of positive radius around the origin and is equal to the given complex
  function there.

  This relationship is unique in the sense that no complex function can have more than
  one formal power series to which it expands, and if two holomorphic functions that are
  holomorphic on a connected open set around the origin and have the same power series
  expansion, they must be equal on that set.

  More concrete statements about the radius of convergence can usually be made, but for
  many purposes, the statment that the series converges to the function in some neighbourhood
  of the origin is enough, and that can be shown almost fully automatically in most cases,
  as there are straightforward introduction rules to show this.

  In particular, when one wants to relate the coefficients of the power series to the 
  values of the derivatives of the function at the origin, or if one wants to approximate
  the coefficients of the series with the singularities of the function, this predicate
  is enough.
\<close>
definition\<^marker>\<open>tag important\<close>
  has_fps_expansion :: "('a :: {banach,real_normed_div_algebra} \<Rightarrow> 'a) \<Rightarrow> 'a fps \<Rightarrow> bool"
  (infixl \<open>has'_fps'_expansion\<close> 60) 
  where "(f has_fps_expansion F) \<longleftrightarrow> 
            fps_conv_radius F > 0 \<and> eventually (\<lambda>z. eval_fps F z = f z) (nhds 0)"

named_theorems fps_expansion_intros

lemma has_fps_expansion_schematicI:
  "f has_fps_expansion A \<Longrightarrow> A = B \<Longrightarrow> f has_fps_expansion B"
  by simp

lemma fps_nth_fps_expansion:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "f has_fps_expansion F"
  shows   "fps_nth F n = (deriv ^^ n) f 0 / fact n"
proof -
  have "fps_nth F n = (deriv ^^ n) (eval_fps F) 0 / fact n"
    using assms by (intro fps_nth_conv_deriv) (auto simp: has_fps_expansion_def)
  also have "(deriv ^^ n) (eval_fps F) 0 = (deriv ^^ n) f 0"
    using assms by (intro higher_deriv_cong_ev) (auto simp: has_fps_expansion_def)
  finally show ?thesis .
qed

lemma eval_fps_has_fps_expansion:
  "fps_conv_radius F > 0 \<Longrightarrow> eval_fps F has_fps_expansion F"
  unfolding has_fps_expansion_def by simp

lemma has_fps_expansion_imp_continuous:
  fixes F :: "'a::{real_normed_field,banach} fps"
  assumes "f has_fps_expansion F"
  shows   "continuous (at 0 within A) f"
proof -
  from assms have "isCont (eval_fps F) 0"
    by (intro continuous_eval_fps) (auto simp: has_fps_expansion_def zero_ereal_def)
  also have "?this \<longleftrightarrow> isCont f 0" using assms
    by (intro isCont_cong) (auto simp: has_fps_expansion_def)
  finally have "isCont f 0" .
  thus "continuous (at 0 within A) f"
    by (simp add: continuous_at_imp_continuous_within)
qed

lemma has_fps_expansion_const [simp, intro, fps_expansion_intros]:
  "(\<lambda>_. c) has_fps_expansion fps_const c"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_0 [simp, intro, fps_expansion_intros]: 
  "(\<lambda>_. 0) has_fps_expansion 0"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_1 [simp, intro, fps_expansion_intros]:
  "(\<lambda>_. 1) has_fps_expansion 1"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_numeral [simp, intro, fps_expansion_intros]:
  "(\<lambda>_. numeral n) has_fps_expansion numeral n"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_fps_X_power [fps_expansion_intros]: 
  "(\<lambda>x. x ^ n) has_fps_expansion (fps_X ^ n)"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_fps_X [fps_expansion_intros]: 
  "(\<lambda>x. x) has_fps_expansion fps_X"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_cmult_left [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_div_algebra, comm_ring_1}"
  assumes "f has_fps_expansion F"
  shows   "(\<lambda>x. c * f x) has_fps_expansion fps_const c * F"
proof (cases "c = 0")
  case False
  from assms have "eventually (\<lambda>z. z \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
    by (intro eventually_nhds_in_open) (auto simp: has_fps_expansion_def zero_ereal_def)
  moreover from assms have "eventually (\<lambda>z. eval_fps F z = f z) (nhds 0)"
    by (auto simp: has_fps_expansion_def)
  ultimately have "eventually (\<lambda>z. eval_fps (fps_const c * F) z = c * f z) (nhds 0)"
    by eventually_elim (simp_all add: eval_fps_mult)
  with assms and False show ?thesis
    by (auto simp: has_fps_expansion_def fps_conv_radius_cmult_left)
qed auto

lemma has_fps_expansion_cmult_right [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_div_algebra, comm_ring_1}"
  assumes "f has_fps_expansion F"
  shows   "(\<lambda>x. f x * c) has_fps_expansion F * fps_const c"
proof -
  have "F * fps_const c = fps_const c * F"
    by (intro fps_ext) (auto simp: mult.commute)
  with has_fps_expansion_cmult_left [OF assms] show ?thesis 
    by (simp add: mult.commute)
qed

lemma has_fps_expansion_minus [fps_expansion_intros]:
  assumes "f has_fps_expansion F"
  shows   "(\<lambda>x. - f x) has_fps_expansion -F"
proof -
  from assms have "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
    by (intro eventually_nhds_in_open) (auto simp: has_fps_expansion_def zero_ereal_def)
  moreover from assms have "eventually (\<lambda>x. eval_fps F x = f x) (nhds 0)"
    by (auto simp: has_fps_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fps (-F) x = -f x) (nhds 0)"
    by eventually_elim (auto simp: eval_fps_minus)
  thus ?thesis using assms by (auto simp: has_fps_expansion_def)
qed

lemma has_fps_expansion_add [fps_expansion_intros]:
  assumes "f has_fps_expansion F" "g has_fps_expansion G"
  shows   "(\<lambda>x. f x + g x) has_fps_expansion F + G"
proof -
  from assms have "0 < min (fps_conv_radius F) (fps_conv_radius G)"
    by (auto simp: has_fps_expansion_def)
  also have "\<dots> \<le> fps_conv_radius (F + G)"
    by (rule fps_conv_radius_add)
  finally have radius: "\<dots> > 0" .

  from assms have "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
                  "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius G)) (nhds 0)"
    by (intro eventually_nhds_in_open; force simp: has_fps_expansion_def zero_ereal_def)+
  moreover have "eventually (\<lambda>x. eval_fps F x = f x) (nhds 0)"
            and "eventually (\<lambda>x. eval_fps G x = g x) (nhds 0)"
    using assms by (auto simp: has_fps_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fps (F + G) x = f x + g x) (nhds 0)"
    by eventually_elim (auto simp: eval_fps_add)
  with radius show ?thesis by (auto simp: has_fps_expansion_def)
qed

lemma has_fps_expansion_diff [fps_expansion_intros]:
  assumes "f has_fps_expansion F" "g has_fps_expansion G"
  shows   "(\<lambda>x. f x - g x) has_fps_expansion F - G"
  using has_fps_expansion_add[of f F "\<lambda>x. - g x" "-G"] assms 
  by (simp add: has_fps_expansion_minus)

lemma has_fps_expansion_mult [fps_expansion_intros]:
  fixes F G :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F" "g has_fps_expansion G"
  shows   "(\<lambda>x. f x * g x) has_fps_expansion F * G"
proof -
  from assms have "0 < min (fps_conv_radius F) (fps_conv_radius G)"
    by (auto simp: has_fps_expansion_def)
  also have "\<dots> \<le> fps_conv_radius (F * G)"
    by (rule fps_conv_radius_mult)
  finally have radius: "\<dots> > 0" .

  from assms have "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
                  "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius G)) (nhds 0)"
    by (intro eventually_nhds_in_open; force simp: has_fps_expansion_def zero_ereal_def)+
  moreover have "eventually (\<lambda>x. eval_fps F x = f x) (nhds 0)"
            and "eventually (\<lambda>x. eval_fps G x = g x) (nhds 0)"
    using assms by (auto simp: has_fps_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fps (F * G) x = f x * g x) (nhds 0)"
    by eventually_elim (auto simp: eval_fps_mult)
  with radius show ?thesis by (auto simp: has_fps_expansion_def)
qed

lemma has_fps_expansion_inverse [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_field} fps"
  assumes "f has_fps_expansion F"
  assumes "fps_nth F 0 \<noteq> 0"
  shows   "(\<lambda>x. inverse (f x)) has_fps_expansion inverse F"
proof -
  have radius: "fps_conv_radius (inverse F) > 0"
    using assms unfolding has_fps_expansion_def
    by (intro fps_conv_radius_inverse_pos) auto
  let ?R = "min (fps_conv_radius F) (fps_conv_radius (inverse F))"
  from assms radius
    have "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
         "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius (inverse F))) (nhds 0)"
    by (intro eventually_nhds_in_open; force simp: has_fps_expansion_def zero_ereal_def)+
  moreover have "eventually (\<lambda>z. eval_fps F z = f z) (nhds 0)"
    using assms by (auto simp: has_fps_expansion_def)
  ultimately have "eventually (\<lambda>z. eval_fps (inverse F) z = inverse (f z)) (nhds 0)"
  proof eventually_elim
    case (elim z)
    hence "eval_fps (inverse F * F) z = eval_fps (inverse F) z * f z"
      by (subst eval_fps_mult) auto
    also have "eval_fps (inverse F * F) z = 1"
      using assms by (simp add: inverse_mult_eq_1)
    finally show ?case by (auto simp: field_split_simps)
  qed
  with radius show ?thesis by (auto simp: has_fps_expansion_def)
qed

lemma has_fps_expansion_sum [fps_expansion_intros]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x has_fps_expansion F x"
  shows   "(\<lambda>z. \<Sum>x\<in>A. f x z) has_fps_expansion (\<Sum>x\<in>A. F x)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: fps_expansion_intros)

lemma has_fps_expansion_prod [fps_expansion_intros]:
  fixes F :: "'a \<Rightarrow> 'b :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x has_fps_expansion F x"
  shows   "(\<lambda>z. \<Prod>x\<in>A. f x z) has_fps_expansion (\<Prod>x\<in>A. F x)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: fps_expansion_intros)

lemma has_fps_expansion_exp [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_field}"
  shows "(\<lambda>x. exp (c * x)) has_fps_expansion fps_exp c"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_exp1 [fps_expansion_intros]:
  "(\<lambda>x::'a :: {banach, real_normed_field}. exp x) has_fps_expansion fps_exp 1"
  using has_fps_expansion_exp[of 1] by simp

lemma has_fps_expansion_exp_neg1 [fps_expansion_intros]:
  "(\<lambda>x::'a :: {banach, real_normed_field}. exp (-x)) has_fps_expansion fps_exp (-1)"
  using has_fps_expansion_exp[of "-1"] by simp

lemma has_fps_expansion_deriv [fps_expansion_intros]:
  assumes "f has_fps_expansion F"
  shows   "deriv f has_fps_expansion fps_deriv F"
proof -
  have "eventually (\<lambda>z. z \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
    using assms by (intro eventually_nhds_in_open)
                   (auto simp: has_fps_expansion_def zero_ereal_def)
  moreover from assms have "eventually (\<lambda>z. eval_fps F z = f z) (nhds 0)"
    by (auto simp: has_fps_expansion_def)
  then obtain s where "open s" "0 \<in> s" and s: "\<And>w. w \<in> s \<Longrightarrow> eval_fps F w = f w"
    by (auto simp: eventually_nhds)
  hence "eventually (\<lambda>w. w \<in> s) (nhds 0)"
    by (intro eventually_nhds_in_open) auto
  ultimately have "eventually (\<lambda>z. eval_fps (fps_deriv F) z = deriv f z) (nhds 0)"
  proof eventually_elim
    case (elim z)
    hence "eval_fps (fps_deriv F) z = deriv (eval_fps F) z"
      by (simp add: eval_fps_deriv)
    also have "eventually (\<lambda>w. w \<in> s) (nhds z)"
      using elim and \<open>open s\<close> by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>w. eval_fps F w = f w) (nhds z)"
      by eventually_elim (simp add: s)
    hence "deriv (eval_fps F) z = deriv f z"
      by (intro deriv_cong_ev refl)
    finally show ?case .
  qed
  with assms and fps_conv_radius_deriv[of F] show ?thesis
    by (auto simp: has_fps_expansion_def)
qed

lemma fps_conv_radius_binomial:
  fixes c :: "'a :: {real_normed_field,banach}"
  shows "fps_conv_radius (fps_binomial c) = (if c \<in> \<nat> then \<infinity> else 1)"
  unfolding fps_conv_radius_def by (simp add: conv_radius_gchoose)

lemma fps_conv_radius_ln:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "fps_conv_radius (fps_ln c) = (if c = 0 then \<infinity> else 1)"
proof (cases "c = 0")
  case False
  have "conv_radius (\<lambda>n. 1 / of_nat n :: 'a) = 1"
  proof (rule conv_radius_ratio_limit_nonzero)
    show "(\<lambda>n. norm (1 / of_nat n :: 'a) / norm (1 / of_nat (Suc n) :: 'a)) \<longlonglongrightarrow> 1"
      using LIMSEQ_Suc_n_over_n by (simp add: norm_divide del: of_nat_Suc)
  qed auto
  also have "conv_radius (\<lambda>n. 1 / of_nat n :: 'a) =
               conv_radius (\<lambda>n. if n = 0 then 0 else (- 1) ^ (n - 1) / of_nat n :: 'a)"
    by (intro conv_radius_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (simp add: norm_mult norm_divide norm_power)
  finally show ?thesis using False unfolding fps_ln_def
    by (subst  fps_conv_radius_cmult_left) (simp_all add: fps_conv_radius_def)
qed (auto simp: fps_ln_def)

lemma fps_conv_radius_ln_nonzero [simp]:
  assumes "c \<noteq> (0 :: 'a :: {banach,real_normed_field,field_char_0})"
  shows   "fps_conv_radius (fps_ln c) = 1"
  using assms by (simp add: fps_conv_radius_ln)

lemma fps_conv_radius_sin [simp]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "fps_conv_radius (fps_sin c) = \<infinity>"
proof (cases "c = 0")
  case False
  have "\<infinity> = conv_radius (\<lambda>n. of_real (sin_coeff n) :: 'a)"
  proof (rule sym, rule conv_radius_inftyI'', rule summable_norm_cancel, goal_cases)
    case (1 z)
    show ?case using summable_norm_sin[of z] by (simp add: norm_mult)
  qed
  also have "\<dots> / norm c = conv_radius (\<lambda>n. c ^ n * of_real (sin_coeff n) :: 'a)"
    using False by (subst conv_radius_mult_power) auto
  also have "\<dots> = fps_conv_radius (fps_sin c)" unfolding fps_conv_radius_def
    by (rule conv_radius_cong_weak) (auto simp add: fps_sin_def sin_coeff_def)
  finally show ?thesis by simp
qed simp_all

lemma fps_conv_radius_cos [simp]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "fps_conv_radius (fps_cos c) = \<infinity>"
proof (cases "c = 0")
  case False
  have "\<infinity> = conv_radius (\<lambda>n. of_real (cos_coeff n) :: 'a)"
  proof (rule sym, rule conv_radius_inftyI'', rule summable_norm_cancel, goal_cases)
    case (1 z)
    show ?case using summable_norm_cos[of z] by (simp add: norm_mult)
  qed
  also have "\<dots> / norm c = conv_radius (\<lambda>n. c ^ n * of_real (cos_coeff n) :: 'a)"
    using False by (subst conv_radius_mult_power) auto
  also have "\<dots> = fps_conv_radius (fps_cos c)" unfolding fps_conv_radius_def
    by (rule conv_radius_cong_weak) (auto simp add: fps_cos_def cos_coeff_def)
  finally show ?thesis by simp
qed simp_all

lemma eval_fps_sin [simp]:
  fixes z :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "eval_fps (fps_sin c) z = sin (c * z)"
proof -
  have "(\<lambda>n. sin_coeff n *\<^sub>R (c * z) ^ n) sums sin (c * z)" by (rule sin_converges)
  also have "(\<lambda>n. sin_coeff n *\<^sub>R (c * z) ^ n) = (\<lambda>n. fps_nth (fps_sin c) n * z ^ n)"
    by (rule ext) (auto simp: sin_coeff_def fps_sin_def power_mult_distrib scaleR_conv_of_real)
  finally show ?thesis by (simp add: sums_iff eval_fps_def)
qed

lemma eval_fps_cos [simp]:
  fixes z :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "eval_fps (fps_cos c) z = cos (c * z)"
proof -
  have "(\<lambda>n. cos_coeff n *\<^sub>R (c * z) ^ n) sums cos (c * z)" by (rule cos_converges)
  also have "(\<lambda>n. cos_coeff n *\<^sub>R (c * z) ^ n) = (\<lambda>n. fps_nth (fps_cos c) n * z ^ n)"
    by (rule ext) (auto simp: cos_coeff_def fps_cos_def power_mult_distrib scaleR_conv_of_real)
  finally show ?thesis by (simp add: sums_iff eval_fps_def)
qed

lemma cos_eq_zero_imp_norm_ge:
  assumes "cos (z :: complex) = 0"
  shows   "norm z \<ge> pi / 2"
proof -
  from assms obtain n where "z = complex_of_real ((of_int n + 1 / 2) * pi)"
    by (auto simp: cos_eq_0 algebra_simps)
  also have "norm \<dots> = \<bar>real_of_int n + 1 / 2\<bar> * pi"
    by (subst norm_of_real) (simp_all add: abs_mult)
  also have "real_of_int n + 1 / 2 = of_int (2 * n + 1) / 2" by simp
  also have "\<bar>\<dots>\<bar> = of_int \<bar>2 * n + 1\<bar> / 2" by (subst abs_divide) simp_all
  also have "\<dots> * pi = of_int \<bar>2 * n + 1\<bar> * (pi / 2)" by simp
  also have "\<dots> \<ge> of_int 1 * (pi / 2)"
    by (intro mult_right_mono, subst of_int_le_iff) (auto simp: abs_if)
  finally show ?thesis by simp
qed



lemma eval_fps_binomial:
  fixes c :: complex
  assumes "norm z < 1"
  shows   "eval_fps (fps_binomial c) z = (1 + z) powr c"
  using gen_binomial_complex[OF assms] by (simp add: sums_iff eval_fps_def)

lemma has_fps_expansion_binomial_complex [fps_expansion_intros]:
  fixes c :: complex
  shows "(\<lambda>x. (1 + x) powr c) has_fps_expansion fps_binomial c"
proof -
  have *: "eventually (\<lambda>z::complex. z \<in> eball 0 1) (nhds 0)"
    by (intro eventually_nhds_in_open) auto
  thus ?thesis
    by (auto simp: has_fps_expansion_def eval_fps_binomial fps_conv_radius_binomial
             intro!: eventually_mono [OF *])
qed

lemma has_fps_expansion_sin [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "(\<lambda>x. sin (c * x)) has_fps_expansion fps_sin c"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_sin' [fps_expansion_intros]:
  "(\<lambda>x::'a :: {banach, real_normed_field}. sin x) has_fps_expansion fps_sin 1"
  using has_fps_expansion_sin[of 1] by simp

lemma has_fps_expansion_cos [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "(\<lambda>x. cos (c * x)) has_fps_expansion fps_cos c"
  by (auto simp: has_fps_expansion_def)

lemma has_fps_expansion_cos' [fps_expansion_intros]:
  "(\<lambda>x::'a :: {banach, real_normed_field}. cos x) has_fps_expansion fps_cos 1"
  using has_fps_expansion_cos[of 1] by simp

lemma has_fps_expansion_shift [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_field} fps"
  assumes "f has_fps_expansion F" and "n \<le> subdegree F"
  assumes "c = fps_nth F n"
  shows   "(\<lambda>x. if x = 0 then c else f x / x ^ n) has_fps_expansion (fps_shift n F)"
proof -
  have "eventually (\<lambda>x. x \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
    using assms by (intro eventually_nhds_in_open) (auto simp: has_fps_expansion_def zero_ereal_def)
  moreover have "eventually (\<lambda>x. eval_fps F x = f x) (nhds 0)"
    using assms by (auto simp: has_fps_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fps (fps_shift n F) x = 
                     (if x = 0 then c else f x / x ^ n)) (nhds 0)"
    by eventually_elim (auto simp: eval_fps_shift assms)
  with assms show ?thesis by (auto simp: has_fps_expansion_def)
qed

lemma has_fps_expansion_divide [fps_expansion_intros]:
  fixes F G :: "'a :: {banach, real_normed_field} fps"
  assumes "f has_fps_expansion F" and "g has_fps_expansion G" and 
          "subdegree G \<le> subdegree F" "G \<noteq> 0"
          "c = fps_nth F (subdegree G) / fps_nth G (subdegree G)"
  shows   "(\<lambda>x. if x = 0 then c else f x / g x) has_fps_expansion (F / G)"
proof -
  define n where "n = subdegree G"
  define F' and G' where "F' = fps_shift n F" and "G' = fps_shift n G"
  have "F = F' * fps_X ^ n" "G = G' * fps_X ^ n" unfolding F'_def G'_def n_def 
    by (rule fps_shift_times_fps_X_power [symmetric] le_refl | fact)+
  moreover from assms have "fps_nth G' 0 \<noteq> 0"
    by (simp add: G'_def n_def)
  ultimately have FG: "F / G = F' * inverse G'"
    by (simp add: fps_divide_unit)

  have "(\<lambda>x. (if x = 0 then fps_nth F n else f x / x ^ n) * 
          inverse (if x = 0 then fps_nth G n else g x / x ^ n)) has_fps_expansion F / G"
    (is "?h has_fps_expansion _") unfolding FG F'_def G'_def n_def using \<open>G \<noteq> 0\<close>
    by (intro has_fps_expansion_mult has_fps_expansion_inverse
              has_fps_expansion_shift assms) auto
  also have "?h = (\<lambda>x. if x = 0 then c else f x / g x)"
    using assms(5) unfolding n_def 
    by (intro ext) (auto split: if_splits simp: field_simps)
  finally show ?thesis .
qed

lemma has_fps_expansion_divide' [fps_expansion_intros]:
  fixes F G :: "'a :: {banach, real_normed_field} fps"
  assumes "f has_fps_expansion F" and "g has_fps_expansion G" and "fps_nth G 0 \<noteq> 0"
  shows   "(\<lambda>x. f x / g x) has_fps_expansion (F / G)"
proof -
  have "(\<lambda>x. if x = 0 then fps_nth F 0 / fps_nth G 0 else f x / g x) has_fps_expansion (F / G)"
    (is "?h has_fps_expansion _") using assms(3) by (intro has_fps_expansion_divide assms) auto
  also from assms have "fps_nth F 0 = f 0" "fps_nth G 0 = g 0"
    by (auto simp: has_fps_expansion_def eval_fps_at_0 dest: eventually_nhds_x_imp_x)
  hence "?h = (\<lambda>x. f x / g x)" by auto
  finally show ?thesis .
qed

lemma has_fps_expansion_tan [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "(\<lambda>x. tan (c * x)) has_fps_expansion fps_tan c"
proof -
  have "(\<lambda>x. sin (c * x) / cos (c * x)) has_fps_expansion fps_sin c / fps_cos c"
    by (intro fps_expansion_intros) auto
  thus ?thesis by (simp add: tan_def fps_tan_def)
qed

lemma has_fps_expansion_tan' [fps_expansion_intros]:
  "tan has_fps_expansion fps_tan (1 :: 'a :: {banach, real_normed_field, field_char_0})"
  using has_fps_expansion_tan[of 1] by simp

lemma has_fps_expansion_imp_holomorphic:
  assumes "f has_fps_expansion F"
  obtains s where "open s" "0 \<in> s" "f holomorphic_on s" "\<And>z. z \<in> s \<Longrightarrow> f z = eval_fps F z"
proof -
  from assms obtain s where s: "open s" "0 \<in> s" "\<And>z. z \<in> s \<Longrightarrow> eval_fps F z = f z"
    unfolding has_fps_expansion_def eventually_nhds by blast
  let ?s' = "eball 0 (fps_conv_radius F) \<inter> s"
  have "eval_fps F holomorphic_on ?s'"
    by (intro holomorphic_intros) auto
  also have "?this \<longleftrightarrow> f holomorphic_on ?s'"
    using s by (intro holomorphic_cong) auto
  finally show ?thesis using s assms
    by (intro that[of ?s']) (auto simp: has_fps_expansion_def zero_ereal_def)
qed

lemma has_fps_expansionI:
  fixes f :: "'a :: {banach, real_normed_div_algebra} \<Rightarrow> 'a"
  assumes "eventually (\<lambda>u. (\<lambda>n. fps_nth F n * u ^ n) sums f u) (nhds 0)"
  shows   "f has_fps_expansion F"
proof -
  from assms obtain X where X: "open X" "0 \<in> X" "\<And>u. u \<in> X \<Longrightarrow> (\<lambda>n. fps_nth F n * u ^ n) sums f u"
    unfolding eventually_nhds by blast
  obtain r where r: "r > 0" "cball 0 r \<subseteq> X"
    using X(1,2) open_contains_cball by blast
  have "0 < norm (of_real r :: 'a)"
    using r(1) by simp
  also have "fps_conv_radius F \<ge> norm (of_real r :: 'a)"
    unfolding fps_conv_radius_def
  proof (rule conv_radius_geI)
    have "of_real r \<in> X"
      using r by auto
    from X(3)[OF this] show "summable (\<lambda>n. fps_nth F n * of_real r ^ n)"
      by (simp add: sums_iff)
  qed
  finally have "fps_conv_radius F > 0"
    by (simp_all add: zero_ereal_def)
  moreover have "(\<forall>\<^sub>F z in nhds 0. eval_fps F z = f z)"
    using assms by eventually_elim (auto simp: sums_iff eval_fps_def)
  ultimately show ?thesis
    unfolding has_fps_expansion_def ..
qed

lemma fps_mult_numeral_left [simp]: "fps_nth (numeral c * f) n = numeral c * fps_nth f n"
  by (simp add: fps_numeral_fps_const)

end