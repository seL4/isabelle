(*  Title:      HOL/Multivariate_Analysis/Derivative.thy
    Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (translation from HOL Light)
*)

header {* Multivariate calculus in Euclidean space *}

theory Derivative
imports Brouwer_Fixpoint Operator_Norm
begin

lemma bounded_linear_imp_linear: (* TODO: move elsewhere *)
  assumes "bounded_linear f"
  shows "linear f"
proof -
  interpret f: bounded_linear f
    using assms .
  show ?thesis
    by (simp add: f.add f.scaleR linear_iff)
qed

lemma netlimit_at_vector: (* TODO: move *)
  fixes a :: "'a::real_normed_vector"
  shows "netlimit (at a) = a"
proof (cases "\<exists>x. x \<noteq> a")
  case True then obtain x where x: "x \<noteq> a" ..
  have "\<not> trivial_limit (at a)"
    unfolding trivial_limit_def eventually_at dist_norm
    apply clarsimp
    apply (rule_tac x="a + scaleR (d / 2) (sgn (x - a))" in exI)
    apply (simp add: norm_sgn sgn_zero_iff x)
    done
  then show ?thesis
    by (rule netlimit_within [of a UNIV])
qed simp

(* Because I do not want to type this all the time *)
lemmas linear_linear = linear_conv_bounded_linear[symmetric]

lemma derivative_linear[dest]: "(f has_derivative f') net \<Longrightarrow> bounded_linear f'"
  unfolding has_derivative_def by auto

lemma derivative_is_linear: "(f has_derivative f') net \<Longrightarrow> linear f'"
  by (rule derivative_linear [THEN bounded_linear_imp_linear])

subsection {* Derivatives *}

subsubsection {* Combining theorems. *}

lemmas has_derivative_id = has_derivative_ident
lemmas has_derivative_const = has_derivative_const
lemmas has_derivative_neg = has_derivative_minus
lemmas has_derivative_add = has_derivative_add
lemmas has_derivative_sub = has_derivative_diff
lemmas has_derivative_setsum = has_derivative_setsum
lemmas scaleR_right_has_derivative = has_derivative_scaleR_right
lemmas scaleR_left_has_derivative = has_derivative_scaleR_left
lemmas inner_right_has_derivative = has_derivative_inner_right
lemmas inner_left_has_derivative = has_derivative_inner_left
lemmas mult_right_has_derivative = has_derivative_mult_right
lemmas mult_left_has_derivative = has_derivative_mult_left

lemma has_derivative_add_const:
  "(f has_derivative f') net \<Longrightarrow> ((\<lambda>x. f x + c) has_derivative f') net"
  by (intro has_derivative_eq_intros) auto


subsection {* Derivative with composed bilinear function. *}

lemma has_derivative_bilinear_within:
  assumes "(f has_derivative f') (at x within s)"
    and "(g has_derivative g') (at x within s)"
    and "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_derivative (\<lambda>d. h (f x) (g' d) + h (f' d) (g x))) (at x within s)"
  using bounded_bilinear.FDERIV[OF assms(3,1,2)] .

lemma has_derivative_bilinear_at:
  assumes "(f has_derivative f') (at x)"
    and "(g has_derivative g') (at x)"
    and "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_derivative (\<lambda>d. h (f x) (g' d) + h (f' d) (g x))) (at x)"
  using has_derivative_bilinear_within[of f f' x UNIV g g' h] assms by simp

text {* These are the only cases we'll care about, probably. *}

lemma has_derivative_within: "(f has_derivative f') (at x within s) \<longleftrightarrow>
    bounded_linear f' \<and> ((\<lambda>y. (1 / norm(y - x)) *\<^sub>R (f y - (f x + f' (y - x)))) ---> 0) (at x within s)"
  unfolding has_derivative_def Lim
  by (auto simp add: netlimit_within inverse_eq_divide field_simps)

lemma has_derivative_at: "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and> ((\<lambda>y. (1 / (norm(y - x))) *\<^sub>R (f y - (f x + f' (y - x)))) ---> 0) (at x)"
  using has_derivative_within [of f f' x UNIV]
  by simp

text {* More explicit epsilon-delta forms. *}

lemma has_derivative_within':
  "(f has_derivative f')(at x within s) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. 0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
      norm (f x' - f x - f'(x' - x)) / norm (x' - x) < e)"
  unfolding has_derivative_within Lim_within dist_norm
  unfolding diff_0_right
  by (simp add: diff_diff_eq)

lemma has_derivative_at':
  "(f has_derivative f') (at x) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>x'. 0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
      norm (f x' - f x - f'(x' - x)) / norm (x' - x) < e)"
  using has_derivative_within' [of f f' x UNIV]
  by simp

lemma has_derivative_at_within:
  "(f has_derivative f') (at x) \<Longrightarrow> (f has_derivative f') (at x within s)"
  unfolding has_derivative_within' has_derivative_at'
  by blast

lemma has_derivative_within_open:
  "a \<in> s \<Longrightarrow> open s \<Longrightarrow>
    (f has_derivative f') (at a within s) \<longleftrightarrow> (f has_derivative f') (at a)"
  by (simp only: at_within_interior interior_open)

lemma has_derivative_right:
  fixes f :: "real \<Rightarrow> real"
    and y :: "real"
  shows "(f has_derivative (op * y)) (at x within ({x <..} \<inter> I)) \<longleftrightarrow>
    ((\<lambda>t. (f x - f t) / (x - t)) ---> y) (at x within ({x <..} \<inter> I))"
proof -
  have "((\<lambda>t. (f t - (f x + y * (t - x))) / \<bar>t - x\<bar>) ---> 0) (at x within ({x<..} \<inter> I)) \<longleftrightarrow>
    ((\<lambda>t. (f t - f x) / (t - x) - y) ---> 0) (at x within ({x<..} \<inter> I))"
    by (intro Lim_cong_within) (auto simp add: diff_divide_distrib add_divide_distrib)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. (f t - f x) / (t - x)) ---> y) (at x within ({x<..} \<inter> I))"
    by (simp add: Lim_null[symmetric])
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. (f x - f t) / (x - t)) ---> y) (at x within ({x<..} \<inter> I))"
    by (intro Lim_cong_within) (simp_all add: field_simps)
  finally show ?thesis
    by (simp add: bounded_linear_mult_right has_derivative_within)
qed

subsubsection {*Caratheodory characterization*}

lemma DERIV_within_iff:
  "(f has_field_derivative D) (at a within s) \<longleftrightarrow> ((\<lambda>z. (f z - f a) / (z - a)) ---> D) (at a within s)"
proof -
  have 1: "\<And>w y. ~(w = a) ==> y / (w - a) - D = (y - (w - a)*D)/(w - a)"
    by (metis divide_diff_eq_iff eq_iff_diff_eq_0)
  show ?thesis
    apply (simp add: has_field_derivative_def has_derivative_within bounded_linear_mult_right)
    apply (simp add: LIM_zero_iff [where l = D, symmetric])
    apply (simp add: Lim_within dist_norm)
    apply (simp add: nonzero_norm_divide [symmetric])
    apply (simp add: 1 diff_add_eq_diff_diff ac_simps)
    done
qed

lemma DERIV_caratheodory_within:
  "(f has_field_derivative l) (at x within s) \<longleftrightarrow> 
   (\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> continuous (at x within s) g \<and> g x = l)"
      (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
  proof (intro exI conjI)
    let ?g = "(%z. if z = x then l else (f z - f x) / (z-x))"
    show "\<forall>z. f z - f x = ?g z * (z-x)" by simp
    show "continuous (at x within s) ?g" using `?lhs`
      by (auto simp add: continuous_within DERIV_within_iff cong: Lim_cong_within)
    show "?g x = l" by simp
  qed
next
  assume ?rhs
  then obtain g where
    "(\<forall>z. f z - f x = g z * (z-x))" and "continuous (at x within s) g" and "g x = l" by blast
  thus ?lhs
    by (auto simp add: continuous_within DERIV_within_iff cong: Lim_cong_within)
qed

lemma CARAT_DERIV: (*FIXME: REPLACES THE ONE IN Deriv.thy*)
  "(DERIV f x :> l) \<longleftrightarrow> (\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> isCont g x \<and> g x = l)"
by (rule DERIV_caratheodory_within)


subsubsection {* Limit transformation for derivatives *}

lemma has_derivative_transform_within:
  assumes "0 < d"
    and "x \<in> s"
    and "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'"
    and "(f has_derivative f') (at x within s)"
  shows "(g has_derivative f') (at x within s)"
  using assms
  unfolding has_derivative_within
  apply clarify
  apply (rule Lim_transform_within, auto)
  done

lemma has_derivative_transform_at:
  assumes "0 < d"
    and "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'"
    and "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using has_derivative_transform_within [of d x UNIV f g f'] assms
  by simp

lemma has_derivative_transform_within_open:
  assumes "open s"
    and "x \<in> s"
    and "\<forall>y\<in>s. f y = g y"
    and "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using assms
  unfolding has_derivative_at
  apply clarify
  apply (rule Lim_transform_within_open[OF assms(1,2)], auto)
  done

subsection {* Differentiability *}

definition
  differentiable_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
    (infixr "differentiable'_on" 30)
  where "f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable (at x within s))"

lemma differentiableI: "(f has_derivative f') net \<Longrightarrow> f differentiable net"
  unfolding differentiable_def
  by auto

lemma differentiable_at_withinI: "f differentiable (at x) \<Longrightarrow> f differentiable (at x within s)"
  unfolding differentiable_def
  using has_derivative_at_within
  by blast

lemma differentiable_within_open: (* TODO: delete *)
  assumes "a \<in> s"
    and "open s"
  shows "f differentiable (at a within s) \<longleftrightarrow> f differentiable (at a)"
  using assms
  by (simp only: at_within_interior interior_open)

lemma differentiable_on_eq_differentiable_at:
  "open s \<Longrightarrow> f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable at x)"
  unfolding differentiable_on_def
  by (metis at_within_interior interior_open)

lemma differentiable_transform_within:
  assumes "0 < d"
    and "x \<in> s"
    and "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'"
  assumes "f differentiable (at x within s)"
  shows "g differentiable (at x within s)"
  using assms(4)
  unfolding differentiable_def
  by (auto intro!: has_derivative_transform_within[OF assms(1-3)])

lemma differentiable_transform_at:
  assumes "0 < d"
    and "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'"
    and "f differentiable at x"
  shows "g differentiable at x"
  using assms(3)
  unfolding differentiable_def
  using has_derivative_transform_at[OF assms(1-2)]
  by auto


subsection {* Frechet derivative and Jacobian matrix *}

definition "frechet_derivative f net = (SOME f'. (f has_derivative f') net)"

lemma frechet_derivative_works:
  "f differentiable net \<longleftrightarrow> (f has_derivative (frechet_derivative f net)) net"
  unfolding frechet_derivative_def differentiable_def
  unfolding some_eq_ex[of "\<lambda> f' . (f has_derivative f') net"] ..

lemma linear_frechet_derivative: "f differentiable net \<Longrightarrow> linear (frechet_derivative f net)"
  unfolding frechet_derivative_works has_derivative_def
  by (auto intro: bounded_linear_imp_linear)


subsection {* Differentiability implies continuity *}

lemma differentiable_imp_continuous_within:
  "f differentiable (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by (auto simp: differentiable_def intro: has_derivative_continuous)

lemma differentiable_imp_continuous_on:
  "f differentiable_on s \<Longrightarrow> continuous_on s f"
  unfolding differentiable_on_def continuous_on_eq_continuous_within
  using differentiable_imp_continuous_within by blast

lemma has_derivative_within_subset:
  "(f has_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (f has_derivative f') (at x within t)"
  unfolding has_derivative_within
  using tendsto_within_subset
  by blast

lemma differentiable_within_subset:
  "f differentiable (at x within t) \<Longrightarrow> s \<subseteq> t \<Longrightarrow>
    f differentiable (at x within s)"
  unfolding differentiable_def
  using has_derivative_within_subset
  by blast

lemma differentiable_on_subset:
  "f differentiable_on t \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f differentiable_on s"
  unfolding differentiable_on_def
  using differentiable_within_subset
  by blast

lemma differentiable_on_empty: "f differentiable_on {}"
  unfolding differentiable_on_def
  by auto

text {* Results about neighborhoods filter. *}

lemma eventually_nhds_metric_le:
  "eventually P (nhds a) = (\<exists>d>0. \<forall>x. dist x a \<le> d \<longrightarrow> P x)"
  unfolding eventually_nhds_metric by (safe, rule_tac x="d / 2" in exI, auto)

lemma le_nhds: "F \<le> nhds a \<longleftrightarrow> (\<forall>S. open S \<and> a \<in> S \<longrightarrow> eventually (\<lambda>x. x \<in> S) F)"
  unfolding le_filter_def eventually_nhds by (fast elim: eventually_elim1)

lemma le_nhds_metric: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a < e) F)"
  unfolding le_filter_def eventually_nhds_metric by (fast elim: eventually_elim1)

lemma le_nhds_metric_le: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a \<le> e) F)"
  unfolding le_filter_def eventually_nhds_metric_le by (fast elim: eventually_elim1)

text {* Several results are easier using a "multiplied-out" variant.
(I got this idea from Dieudonne's proof of the chain rule). *}

lemma has_derivative_within_alt:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm(y - x) < d \<longrightarrow> norm (f y - f x - f' (y - x)) \<le> e * norm (y - x))"
  unfolding has_derivative_within filterlim_def le_nhds_metric_le eventually_filtermap
    eventually_at dist_norm diff_add_eq_diff_diff
  by (force simp add: linear_0 bounded_linear_imp_linear pos_divide_le_eq)

lemma has_derivative_at_alt:
  "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y. norm(y - x) < d \<longrightarrow> norm (f y - f x - f'(y - x)) \<le> e * norm (y - x))"
  using has_derivative_within_alt[where s=UNIV]
  by simp


subsection {* The chain rule *}

lemma diff_chain_within[has_derivative_intros]:
  assumes "(f has_derivative f') (at x within s)"
    and "(g has_derivative g') (at (f x) within (f ` s))"
  shows "((g \<circ> f) has_derivative (g' \<circ> f'))(at x within s)"
  using has_derivative_in_compose[OF assms]
  by (simp add: comp_def)

lemma diff_chain_at[has_derivative_intros]:
  "(f has_derivative f') (at x) \<Longrightarrow>
    (g has_derivative g') (at (f x)) \<Longrightarrow> ((g \<circ> f) has_derivative (g' \<circ> f')) (at x)"
  using has_derivative_compose[of f f' x UNIV g g']
  by (simp add: comp_def)


subsection {* Composition rules stated just for differentiability *}

lemma differentiable_chain_at:
  "f differentiable (at x) \<Longrightarrow>
    g differentiable (at (f x)) \<Longrightarrow> (g \<circ> f) differentiable (at x)"
  unfolding differentiable_def
  by (meson diff_chain_at)

lemma differentiable_chain_within:
  "f differentiable (at x within s) \<Longrightarrow>
    g differentiable (at(f x) within (f ` s)) \<Longrightarrow> (g \<circ> f) differentiable (at x within s)"
  unfolding differentiable_def
  by (meson diff_chain_within)


subsection {* Uniqueness of derivative *}

text {*
 The general result is a bit messy because we need approachability of the
 limit point from any direction. But OK for nontrivial intervals etc.
*}

lemma frechet_derivative_unique_within:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_derivative f') (at x within s)"
    and "(f has_derivative f'') (at x within s)"
    and "\<forall>i\<in>Basis. \<forall>e>0. \<exists>d. 0 < abs d \<and> abs d < e \<and> (x + d *\<^sub>R i) \<in> s"
  shows "f' = f''"
proof -
  note as = assms(1,2)[unfolded has_derivative_def]
  then interpret f': bounded_linear f' by auto
  from as interpret f'': bounded_linear f'' by auto
  have "x islimpt s" unfolding islimpt_approachable
  proof (rule, rule)
    fix e :: real
    assume "e > 0"
    obtain d where "0 < \<bar>d\<bar>" and "\<bar>d\<bar> < e" and "x + d *\<^sub>R (SOME i. i \<in> Basis) \<in> s"
      using assms(3) SOME_Basis `e>0` by blast
    then show "\<exists>x'\<in>s. x' \<noteq> x \<and> dist x' x < e"
      apply (rule_tac x="x + d *\<^sub>R (SOME i. i \<in> Basis)" in bexI)
      unfolding dist_norm
      apply (auto simp: SOME_Basis nonzero_Basis)
      done
  qed
  then have *: "netlimit (at x within s) = x"
    apply (auto intro!: netlimit_within)
    by (metis trivial_limit_within)
  show ?thesis
    apply (rule linear_eq_stdbasis)
    unfolding linear_conv_bounded_linear
    apply (rule as(1,2)[THEN conjunct1])+
  proof (rule, rule ccontr)
    fix i :: 'a
    assume i: "i \<in> Basis"
    def e \<equiv> "norm (f' i - f'' i)"
    assume "f' i \<noteq> f'' i"
    then have "e > 0"
      unfolding e_def by auto
    obtain d where d:
      "0 < d"
      "(\<And>xa. xa\<in>s \<longrightarrow> 0 < dist xa x \<and> dist xa x < d \<longrightarrow>
          dist ((f xa - f x - f' (xa - x)) /\<^sub>R norm (xa - x) -
              (f xa - f x - f'' (xa - x)) /\<^sub>R norm (xa - x)) (0 - 0) < e)"
      using tendsto_diff [OF as(1,2)[THEN conjunct2]]
      unfolding * Lim_within
      using `e>0` by blast
    obtain c where c: "0 < \<bar>c\<bar>" "\<bar>c\<bar> < d \<and> x + c *\<^sub>R i \<in> s"
      using assms(3) i d(1) by blast
    have *: "norm (- ((1 / \<bar>c\<bar>) *\<^sub>R f' (c *\<^sub>R i)) + (1 / \<bar>c\<bar>) *\<^sub>R f'' (c *\<^sub>R i)) =
        norm ((1 / abs c) *\<^sub>R (- (f' (c *\<^sub>R i)) + f'' (c *\<^sub>R i)))"
      unfolding scaleR_right_distrib by auto
    also have "\<dots> = norm ((1 / abs c) *\<^sub>R (c *\<^sub>R (- (f' i) + f'' i)))"
      unfolding f'.scaleR f''.scaleR
      unfolding scaleR_right_distrib scaleR_minus_right
      by auto
    also have "\<dots> = e"
      unfolding e_def
      using c(1)
      using norm_minus_cancel[of "f' i - f'' i"]
      by auto
    finally show False
      using c
      using d(2)[of "x + c *\<^sub>R i"]
      unfolding dist_norm
      unfolding f'.scaleR f''.scaleR f'.add f''.add f'.diff f''.diff
        scaleR_scaleR scaleR_right_diff_distrib scaleR_right_distrib
      using i
      by (auto simp: inverse_eq_divide)
  qed
qed

lemma frechet_derivative_unique_at:
  "(f has_derivative f') (at x) \<Longrightarrow> (f has_derivative f'') (at x) \<Longrightarrow> f' = f''"
  by (rule has_derivative_unique)

lemma frechet_derivative_unique_within_closed_interval:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"
    and "x \<in> {a..b}"
    and "(f has_derivative f' ) (at x within {a..b})"
    and "(f has_derivative f'') (at x within {a..b})"
  shows "f' = f''"
  apply(rule frechet_derivative_unique_within)
  apply(rule assms(3,4))+
proof (rule, rule, rule)
  fix e :: real
  fix i :: 'a
  assume "e > 0" and i: "i \<in> Basis"
  then show "\<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> x + d *\<^sub>R i \<in> {a..b}"
  proof (cases "x\<bullet>i = a\<bullet>i")
    case True
    then show ?thesis
      apply (rule_tac x="(min (b\<bullet>i - a\<bullet>i)  e) / 2" in exI)
      using assms(1)[THEN bspec[where x=i]] and `e>0` and assms(2)
      unfolding mem_interval
      using i
      apply (auto simp add: field_simps inner_simps inner_Basis)
      done
  next
    note * = assms(2)[unfolded mem_interval, THEN bspec, OF i]
    case False
    moreover have "a \<bullet> i < x \<bullet> i"
      using False * by auto
    moreover {
      have "a \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e \<le> a\<bullet>i *2 + x\<bullet>i - a\<bullet>i"
        by auto
      also have "\<dots> = a\<bullet>i + x\<bullet>i"
        by auto
      also have "\<dots> \<le> 2 * (x\<bullet>i)"
        using * by auto
      finally have "a \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e \<le> x \<bullet> i * 2"
        by auto
    }
    moreover have "min (x \<bullet> i - a \<bullet> i) e \<ge> 0"
      using * and `e>0` by auto
    then have "x \<bullet> i * 2 \<le> b \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e"
      using * by auto
    ultimately show ?thesis
      apply (rule_tac x="- (min (x\<bullet>i - a\<bullet>i) e) / 2" in exI)
      using assms(1)[THEN bspec, OF i] and `e>0` and assms(2)
      unfolding mem_interval
      using i
      apply (auto simp add: field_simps inner_simps inner_Basis)
      done
  qed
qed

lemma frechet_derivative_unique_within_open_interval:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "x \<in> box a b"
    and "(f has_derivative f' ) (at x within box a b)"
    and "(f has_derivative f'') (at x within box a b)"
  shows "f' = f''"
proof -
  from assms(1) have *: "at x within box a b = at x"
    by (metis at_within_interior interior_open open_interval)
  from assms(2,3) [unfolded *] show "f' = f''"
    by (rule frechet_derivative_unique_at)
qed

lemma frechet_derivative_at:
  "(f has_derivative f') (at x) \<Longrightarrow> f' = frechet_derivative f (at x)"
  apply (rule frechet_derivative_unique_at[of f])
  apply assumption
  unfolding frechet_derivative_works[symmetric]
  using differentiable_def
  apply auto
  done

lemma frechet_derivative_within_closed_interval:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"
    and "x \<in> {a..b}"
    and "(f has_derivative f') (at x within {a..b})"
  shows "frechet_derivative f (at x within {a..b}) = f'"
  using assms
  by (metis Derivative.differentiableI frechet_derivative_unique_within_closed_interval frechet_derivative_works)


subsection {* The traditional Rolle theorem in one dimension *}

lemma linear_componentwise:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lf: "linear f"
  shows "(f x) \<bullet> j = (\<Sum>i\<in>Basis. (x\<bullet>i) * (f i\<bullet>j))" (is "?lhs = ?rhs")
proof -
  have fA: "finite Basis"
    by simp
  have "?rhs = (\<Sum>i\<in>Basis. (x\<bullet>i) *\<^sub>R (f i))\<bullet>j"
    by (simp add: inner_setsum_left)
  then show ?thesis
    unfolding linear_setsum_mul[OF lf fA, symmetric]
    unfolding euclidean_representation ..
qed

text {* Derivatives of local minima and maxima are zero. *}

lemma has_derivative_local_min:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes deriv: "(f has_derivative f') (at x)"
  assumes min: "eventually (\<lambda>y. f x \<le> f y) (at x)"
  shows "f' = (\<lambda>h. 0)"
proof
  fix h :: 'a
  interpret f': bounded_linear f'
    using deriv by (rule FDERIV_bounded_linear)
  show "f' h = 0"
  proof (cases "h = 0")
    assume "h \<noteq> 0"
    from min obtain d where d1: "0 < d" and d2: "\<forall>y\<in>ball x d. f x \<le> f y"
      unfolding eventually_at by (force simp: dist_commute)
    have "FDERIV (\<lambda>r. x + r *\<^sub>R h) 0 :> (\<lambda>r. r *\<^sub>R h)"
      by (intro FDERIV_eq_intros, auto)
    then have "FDERIV (\<lambda>r. f (x + r *\<^sub>R h)) 0 :> (\<lambda>k. f' (k *\<^sub>R h))"
      by (rule FDERIV_compose, simp add: deriv)
    then have "DERIV (\<lambda>r. f (x + r *\<^sub>R h)) 0 :> f' h"
      unfolding deriv_fderiv by (simp add: f'.scaleR)
    moreover have "0 < d / norm h"
      using d1 and `h \<noteq> 0` by (simp add: divide_pos_pos)
    moreover have "\<forall>y. \<bar>0 - y\<bar> < d / norm h \<longrightarrow> f (x + 0 *\<^sub>R h) \<le> f (x + y *\<^sub>R h)"
      using `h \<noteq> 0` by (auto simp add: d2 dist_norm pos_less_divide_eq)
    ultimately show "f' h = 0"
      by (rule DERIV_local_min)
  qed (simp add: f'.zero)
qed

lemma has_derivative_local_max:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "(f has_derivative f') (at x)"
  assumes "eventually (\<lambda>y. f y \<le> f x) (at x)"
  shows "f' = (\<lambda>h. 0)"
  using has_derivative_local_min [of "\<lambda>x. - f x" "\<lambda>h. - f' h" "x"]
  using assms unfolding fun_eq_iff by simp

lemma differential_zero_maxmin:
  fixes f::"'a::real_normed_vector \<Rightarrow> real"
  assumes "x \<in> s"
    and "open s"
    and deriv: "(f has_derivative f') (at x)"
    and mono: "(\<forall>y\<in>s. f y \<le> f x) \<or> (\<forall>y\<in>s. f x \<le> f y)"
  shows "f' = (\<lambda>v. 0)"
  using mono
proof
  assume "\<forall>y\<in>s. f y \<le> f x"
  with `x \<in> s` and `open s` have "eventually (\<lambda>y. f y \<le> f x) (at x)"
    unfolding eventually_at_topological by auto
  with deriv show ?thesis
    by (rule has_derivative_local_max)
next
  assume "\<forall>y\<in>s. f x \<le> f y"
  with `x \<in> s` and `open s` have "eventually (\<lambda>y. f x \<le> f y) (at x)"
    unfolding eventually_at_topological by auto
  with deriv show ?thesis
    by (rule has_derivative_local_min)
qed

lemma differential_zero_maxmin_component: (* TODO: delete? *)
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
    and ball: "0 < e" "(\<forall>y \<in> ball x e. (f y)\<bullet>k \<le> (f x)\<bullet>k) \<or> (\<forall>y\<in>ball x e. (f x)\<bullet>k \<le> (f y)\<bullet>k)"
    and diff: "f differentiable (at x)"
  shows "(\<Sum>j\<in>Basis. (frechet_derivative f (at x) j \<bullet> k) *\<^sub>R j) = (0::'a)" (is "?D k = 0")
proof -
  let ?f' = "frechet_derivative f (at x)"
  have "x \<in> ball x e" using `0 < e` by simp
  moreover have "open (ball x e)" by simp
  moreover have "((\<lambda>x. f x \<bullet> k) has_derivative (\<lambda>h. ?f' h \<bullet> k)) (at x)"
    using bounded_linear_inner_left diff[unfolded frechet_derivative_works]
    by (rule bounded_linear.FDERIV)
  ultimately have "(\<lambda>h. frechet_derivative f (at x) h \<bullet> k) = (\<lambda>v. 0)"
    using ball(2) by (rule differential_zero_maxmin)
  then show ?thesis
    unfolding fun_eq_iff by simp
qed

lemma rolle:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "f a = f b"
    and "continuous_on {a..b} f"
    and "\<forall>x\<in>box a b. (f has_derivative f' x) (at x)"
  shows "\<exists>x\<in>box a b. f' x = (\<lambda>v. 0)"
proof -
  have "\<exists>x\<in>box a b. (\<forall>y\<in>box a b. f x \<le> f y) \<or> (\<forall>y\<in>box a b. f y \<le> f x)"
  proof -
    have "(a + b) / 2 \<in> {a .. b}"
      using assms(1) by auto
    then have *: "{a..b} \<noteq> {}"
      by auto
    obtain d where d:
        "d \<in> {a..b}"
        "\<forall>y\<in>{a..b}. f y \<le> f d"
      using continuous_attains_sup[OF compact_interval * assms(3)] ..
    obtain c where c:
        "c \<in> {a..b}"
        "\<forall>y\<in>{a..b}. f c \<le> f y"
      using continuous_attains_inf[OF compact_interval * assms(3)] ..
    show ?thesis
    proof (cases "d \<in> box a b \<or> c \<in> box a b")
      case True
      then show ?thesis
        by (metis c(2) d(2) interval_open_subset_closed subset_iff)
    next
      def e \<equiv> "(a + b) /2"
      case False
      then have "f d = f c"
        using d c assms(2) by (auto simp: box_real)
      then have "\<And>x. x \<in> {a..b} \<Longrightarrow> f x = f d"
        using c d
        by force
      then show ?thesis
        apply (rule_tac x=e in bexI)
        unfolding e_def
        using assms(1)
        apply (auto simp: box_real)
        done
    qed
  qed
  then obtain x where x: "x \<in> box a b" "(\<forall>y\<in>box a b. f x \<le> f y) \<or> (\<forall>y\<in>box a b. f y \<le> f x)" ..
  then have "f' x = (\<lambda>v. 0)"
    apply (rule_tac differential_zero_maxmin[of x "box a b" f "f' x"])
    using assms
    apply auto
    done
  then show ?thesis
    by (metis x(1))
qed


subsection {* One-dimensional mean value theorem *}

lemma mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "continuous_on {a..b} f"
  assumes "\<forall>x\<in>{a<..<b}. (f has_derivative (f' x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. f b - f a = (f' x) (b - a)"
proof -
  have "\<exists>x\<in>box a b. (\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa) = (\<lambda>v. 0)"
  proof (intro rolle[OF assms(1), of "\<lambda>x. f x - (f b - f a) / (b - a) * x"] ballI)
    fix x
    assume "x \<in> box a b" hence x: "x \<in> {a<..<b}" by (simp add: box_real)
    show "((\<lambda>x. f x - (f b - f a) / (b - a) * x) has_derivative
        (\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa)) (at x)"
      by (intro has_derivative_intros assms(3)[rule_format,OF x] mult_right_has_derivative)
  qed (insert assms(1,2), auto intro!: continuous_on_intros simp: field_simps)
  then obtain x where
    "x \<in> box a b"
    "(\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa) = (\<lambda>v. 0)" ..
  then show ?thesis
    by (metis (erased, hide_lams) assms(1) box_real diff_less_iff(1) eq_iff_diff_eq_0 linordered_field_class.sign_simps(41) nonzero_mult_divide_cancel_right not_real_square_gt_zero times_divide_eq_left)
qed

lemma mvt_simple:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "\<forall>x\<in>{a..b}. (f has_derivative f' x) (at x within {a..b})"
  shows "\<exists>x\<in>{a<..<b}. f b - f a = f' x (b - a)"
  apply (rule mvt)
  apply (rule assms(1))
  apply (rule differentiable_imp_continuous_on)
  unfolding differentiable_on_def differentiable_def
  defer
proof
  fix x
  assume x: "x \<in> {a<..<b}" hence x: "x \<in> box a b" by (simp add: box_real)
  show "(f has_derivative f' x) (at x)"
    unfolding has_derivative_within_open[OF x open_interval,symmetric]
    apply (rule has_derivative_within_subset)
    apply (rule assms(2)[rule_format])
    using x
    apply (auto simp: box_real)
    done
qed (insert assms(2), auto)

lemma mvt_very_simple:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<forall>x\<in>{a..b}. (f has_derivative f' x) (at x within {a..b})"
  shows "\<exists>x\<in>{a..b}. f b - f a = f' x (b - a)"
proof (cases "a = b")
  interpret bounded_linear "f' b"
    using assms(2) assms(1) by auto
  case True
  then show ?thesis
    apply (rule_tac x=a in bexI)
    using assms(2)[THEN bspec[where x=a]]
    unfolding has_derivative_def
    unfolding True
    using zero
    apply auto
    done
next
  case False
  then show ?thesis
    using mvt_simple[OF _ assms(2)]
    using assms(1)
    by auto
qed

text {* A nice generalization (see Havin's proof of 5.19 from Rudin's book). *}

lemma mvt_general:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "\<forall>x\<in>{a<..<b}. (f has_derivative f'(x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. norm (f b - f a) \<le> norm (f' x (b - a))"
proof -
  have "\<exists>x\<in>{a<..<b}. (op \<bullet> (f b - f a) \<circ> f) b - (op \<bullet> (f b - f a) \<circ> f) a = (f b - f a) \<bullet> f' x (b - a)"
    apply (rule mvt)
    apply (rule assms(1))
    apply (rule continuous_on_inner continuous_on_intros assms(2) ballI)+
    unfolding o_def
    apply (rule has_derivative_inner_right)
    using assms(3)
    apply auto
    done
  then obtain x where x:
    "x \<in> {a<..<b}"
    "(op \<bullet> (f b - f a) \<circ> f) b - (op \<bullet> (f b - f a) \<circ> f) a = (f b - f a) \<bullet> f' x (b - a)" ..
  show ?thesis
  proof (cases "f a = f b")
    case False
    have "norm (f b - f a) * norm (f b - f a) = (norm (f b - f a))\<^sup>2"
      by (simp add: power2_eq_square)
    also have "\<dots> = (f b - f a) \<bullet> (f b - f a)"
      unfolding power2_norm_eq_inner ..
    also have "\<dots> = (f b - f a) \<bullet> f' x (b - a)"
      using x
      unfolding inner_simps
      by (auto simp add: inner_diff_left)
    also have "\<dots> \<le> norm (f b - f a) * norm (f' x (b - a))"
      by (rule norm_cauchy_schwarz)
    finally show ?thesis
      using False x(1)
      by (auto simp add: real_mult_left_cancel)
  next
    case True
    then show ?thesis
      using assms(1)
      apply (rule_tac x="(a + b) /2" in bexI)
      apply auto
      done
  qed
qed

text {* Still more general bound theorem. *}

lemma differentiable_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "convex s"
    and "\<forall>x\<in>s. (f has_derivative f' x) (at x within s)"
    and "\<forall>x\<in>s. onorm (f' x) \<le> B"
    and x: "x \<in> s"
    and y: "y \<in> s"
  shows "norm (f x - f y) \<le> B * norm (x - y)"
proof -
  let ?p = "\<lambda>u. x + u *\<^sub>R (y - x)"
  have *: "\<And>u. u\<in>{0..1} \<Longrightarrow> x + u *\<^sub>R (y - x) \<in> s"
    using assms(1)[unfolded convex_alt,rule_format,OF x y]
    unfolding scaleR_left_diff_distrib scaleR_right_diff_distrib
    by (auto simp add: algebra_simps)
  then have 1: "continuous_on {0..1} (f \<circ> ?p)"
    apply -
    apply (rule continuous_on_intros)+
    unfolding continuous_on_eq_continuous_within
    apply rule
    apply (rule differentiable_imp_continuous_within)
    unfolding differentiable_def
    apply (rule_tac x="f' xa" in exI)
    apply (rule has_derivative_within_subset)
    apply (rule assms(2)[rule_format])
    apply auto
    done
  have 2: "\<forall>u\<in>{0<..<1}.
    ((f \<circ> ?p) has_derivative f' (x + u *\<^sub>R (y - x)) \<circ> (\<lambda>u. 0 + u *\<^sub>R (y - x))) (at u)"
  proof rule
    case goal1
    let ?u = "x + u *\<^sub>R (y - x)"
    have "(f \<circ> ?p has_derivative (f' ?u) \<circ> (\<lambda>u. 0 + u *\<^sub>R (y - x))) (at u within {0<..<1})"
      apply (rule diff_chain_within)
      apply (rule has_derivative_intros)+
      apply (rule has_derivative_within_subset)
      apply (rule assms(2)[rule_format])
      using goal1 *
      apply auto
      done
    then show ?case
      unfolding has_derivative_within_open[OF goal1 open_greaterThanLessThan] .
  qed
  obtain u where u:
      "u \<in> {0<..<1}"
      "norm ((f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 1 - (f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 0)
        \<le> norm ((f' (x + u *\<^sub>R (y - x)) \<circ> (\<lambda>u. 0 + u *\<^sub>R (y - x))) (1 - 0))"
    using mvt_general[OF zero_less_one 1 2] ..
  have **: "\<And>x y. x \<in> s \<Longrightarrow> norm (f' x y) \<le> B * norm y"
  proof -
    case goal1
    have "norm (f' x y) \<le> onorm (f' x) * norm y"
      by (rule onorm(1)[OF derivative_is_linear[OF assms(2)[rule_format,OF goal1]]])
    also have "\<dots> \<le> B * norm y"
      apply (rule mult_right_mono)
      using assms(3)[rule_format,OF goal1]
      apply (auto simp add: field_simps)
      done
    finally show ?case
      by simp
  qed
  have "norm (f x - f y) = norm ((f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 1 - (f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 0)"
    by (auto simp add: norm_minus_commute)
  also have "\<dots> \<le> norm (f' (x + u *\<^sub>R (y - x)) (y - x))"
    using u by auto
  also have "\<dots> \<le> B * norm(y - x)"
    apply (rule **)
    using * and u
    apply auto
    done
  finally show ?thesis
    by (auto simp add: norm_minus_commute)
qed

lemma differentiable_bound_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex s"
    and "\<forall>x\<in>s. (f has_derivative f' x) (at x within s)"
    and "\<forall>x\<in>s. onorm (f' x) \<le> B"
    and x: "x \<in> s"
    and y: "y \<in> s"
  shows "norm (f x - f y) \<le> B * norm (x - y)"
  using differentiable_bound[of s f f' B x y]
  unfolding Ball_def image_iff o_def
  using assms
  by auto

text {* In particular. *}

lemma has_derivative_zero_constant:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex s"
    and "\<forall>x\<in>s. (f has_derivative (\<lambda>h. 0)) (at x within s)"
  shows "\<exists>c. \<forall>x\<in>s. f x = c"
proof (cases "s={}")
  case False
  then obtain x where "x \<in> s"
    by auto
  have "\<And>y. y \<in> s \<Longrightarrow> f x = f y"
  proof -
    case goal1
    then show ?case
      using differentiable_bound_real[OF assms(1-2), of 0 x y] and `x \<in> s`
      unfolding onorm_const
      by auto
  qed
  then show ?thesis
    apply (rule_tac x="f x" in exI)
    apply auto
    done
next
  case True
  then show ?thesis by auto
qed

lemma has_derivative_zero_unique:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex s"
    and "a \<in> s"
    and "f a = c"
    and "\<forall>x\<in>s. (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x \<in> s"
  shows "f x = c"
  using has_derivative_zero_constant[OF assms(1,4)]
  using assms(2-3,5)
  by auto


subsection {* Differentiability of inverse function (most basic form) *}

lemma has_derivative_inverse_basic:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'c::euclidean_space"
  assumes "(f has_derivative f') (at (g y))"
    and "bounded_linear g'"
    and "g' \<circ> f' = id"
    and "continuous (at y) g"
    and "open t"
    and "y \<in> t"
    and "\<forall>z\<in>t. f (g z) = z"
  shows "(g has_derivative g') (at y)"
proof -
  interpret f': bounded_linear f'
    using assms unfolding has_derivative_def by auto
  interpret g': bounded_linear g'
    using assms by auto
  obtain C where C: "0 < C" "\<And>x. norm (g' x) \<le> norm x * C"
    using bounded_linear.pos_bounded[OF assms(2)] by blast
  have lem1: "\<forall>e>0. \<exists>d>0. \<forall>z.
    norm (z - y) < d \<longrightarrow> norm (g z - g y - g'(z - y)) \<le> e * norm (g z - g y)"
  proof (rule, rule)
    case goal1
    have *: "e / C > 0"
      apply (rule divide_pos_pos)
      using `e > 0` C(1)
      apply auto
      done
    obtain d0 where d0:
        "0 < d0"
        "\<forall>ya. norm (ya - g y) < d0 \<longrightarrow> norm (f ya - f (g y) - f' (ya - g y)) \<le> e / C * norm (ya - g y)"
      using assms(1)
      unfolding has_derivative_at_alt
      using * by blast
    obtain d1 where d1:
        "0 < d1"
        "\<forall>x. 0 < dist x y \<and> dist x y < d1 \<longrightarrow> dist (g x) (g y) < d0"
      using assms(4)
      unfolding continuous_at Lim_at
      using d0(1) by blast
    obtain d2 where d2:
        "0 < d2"
        "\<forall>ya. dist ya y < d2 \<longrightarrow> ya \<in> t"
      using assms(5)
      unfolding open_dist
      using assms(6) by blast
    obtain d where d: "0 < d" "d < d1" "d < d2"
      using real_lbound_gt_zero[OF d1(1) d2(1)] by blast
    then show ?case
      apply (rule_tac x=d in exI)
      apply rule
      defer
      apply rule
      apply rule
    proof -
      fix z
      assume as: "norm (z - y) < d"
      then have "z \<in> t"
        using d2 d unfolding dist_norm by auto
      have "norm (g z - g y - g' (z - y)) \<le> norm (g' (f (g z) - y - f' (g z - g y)))"
        unfolding g'.diff f'.diff
        unfolding assms(3)[unfolded o_def id_def, THEN fun_cong]
        unfolding assms(7)[rule_format,OF `z\<in>t`]
        apply (subst norm_minus_cancel[symmetric])
        apply auto
        done
      also have "\<dots> \<le> norm (f (g z) - y - f' (g z - g y)) * C"
        by (rule C(2))
      also have "\<dots> \<le> (e / C) * norm (g z - g y) * C"
        apply (rule mult_right_mono)
        apply (rule d0(2)[rule_format,unfolded assms(7)[rule_format,OF `y\<in>t`]])
        apply (cases "z = y")
        defer
        apply (rule d1(2)[unfolded dist_norm,rule_format])
        using as d C d0
        apply auto
        done
      also have "\<dots> \<le> e * norm (g z - g y)"
        using C by (auto simp add: field_simps)
      finally show "norm (g z - g y - g' (z - y)) \<le> e * norm (g z - g y)"
        by simp
    qed auto
  qed
  have *: "(0::real) < 1 / 2"
    by auto
  obtain d where d:
      "0 < d"
      "\<forall>z. norm (z - y) < d \<longrightarrow> norm (g z - g y - g' (z - y)) \<le> 1 / 2 * norm (g z - g y)"
    using lem1 * by blast
  def B \<equiv> "C * 2"
  have "B > 0"
    unfolding B_def using C by auto
  have lem2: "\<forall>z. norm(z - y) < d \<longrightarrow> norm (g z - g y) \<le> B * norm (z - y)"
  proof (rule, rule)
    case goal1
    have "norm (g z - g y) \<le> norm(g' (z - y)) + norm ((g z - g y) - g'(z - y))"
      by (rule norm_triangle_sub)
    also have "\<dots> \<le> norm (g' (z - y)) + 1 / 2 * norm (g z - g y)"
      apply (rule add_left_mono)
      using d and goal1
      apply auto
      done
    also have "\<dots> \<le> norm (z - y) * C + 1 / 2 * norm (g z - g y)"
      apply (rule add_right_mono)
      using C
      apply auto
      done
    finally show ?case
      unfolding B_def
      by (auto simp add: field_simps)
  qed
  show ?thesis
    unfolding has_derivative_at_alt
    apply rule
    apply (rule assms)
    apply rule
    apply rule
  proof -
    case goal1
    then have *: "e / B >0"
      by (metis `0 < B` divide_pos_pos)
    obtain d' where d':
        "0 < d'"
        "\<forall>z. norm (z - y) < d' \<longrightarrow> norm (g z - g y - g' (z - y)) \<le> e / B * norm (g z - g y)"
      using lem1 * by blast
    obtain k where k: "0 < k" "k < d" "k < d'"
      using real_lbound_gt_zero[OF d(1) d'(1)] by blast
    show ?case
      apply (rule_tac x=k in exI)
      apply auto
    proof -
      fix z
      assume as: "norm (z - y) < k"
      then have "norm (g z - g y - g' (z - y)) \<le> e / B * norm(g z - g y)"
        using d' k by auto
      also have "\<dots> \<le> e * norm (z - y)"
        unfolding times_divide_eq_left pos_divide_le_eq[OF `B>0`]
        using lem2[THEN spec[where x=z]]
        using k as using `e > 0`
        by (auto simp add: field_simps)
      finally show "norm (g z - g y - g' (z - y)) \<le> e * norm (z - y)"
        by simp
    qed(insert k, auto)
  qed
qed

text {* Simply rewrite that based on the domain point x. *}

lemma has_derivative_inverse_basic_x:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'c::euclidean_space"
  assumes "(f has_derivative f') (at x)"
    and "bounded_linear g'"
    and "g' \<circ> f' = id"
    and "continuous (at (f x)) g"
    and "g (f x) = x"
    and "open t"
    and "f x \<in> t"
    and "\<forall>y\<in>t. f (g y) = y"
  shows "(g has_derivative g') (at (f x))"
  apply (rule has_derivative_inverse_basic)
  using assms
  apply auto
  done

text {* This is the version in Dieudonne', assuming continuity of f and g. *}

lemma has_derivative_inverse_dieudonne:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open s"
    and "open (f ` s)"
    and "continuous_on s f"
    and "continuous_on (f ` s) g"
    and "\<forall>x\<in>s. g (f x) = x"
    and "x \<in> s"
    and "(f has_derivative f') (at x)"
    and "bounded_linear g'"
    and "g' \<circ> f' = id"
  shows "(g has_derivative g') (at (f x))"
  apply (rule has_derivative_inverse_basic_x[OF assms(7-9) _ _ assms(2)])
  using assms(3-6)
  unfolding continuous_on_eq_continuous_at[OF assms(1)] continuous_on_eq_continuous_at[OF assms(2)]
  apply auto
  done

text {* Here's the simplest way of not assuming much about g. *}

lemma has_derivative_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact s"
    and "x \<in> s"
    and "f x \<in> interior (f ` s)"
    and "continuous_on s f"
    and "\<forall>y\<in>s. g (f y) = y"
    and "(f has_derivative f') (at x)"
    and "bounded_linear g'"
    and "g' \<circ> f' = id"
  shows "(g has_derivative g') (at (f x))"
proof -
  {
    fix y
    assume "y \<in> interior (f ` s)"
    then obtain x where "x \<in> s" and *: "y = f x"
      unfolding image_iff
      using interior_subset
      by auto
    have "f (g y) = y"
      unfolding * and assms(5)[rule_format,OF `x\<in>s`] ..
  } note * = this
  show ?thesis
    apply (rule has_derivative_inverse_basic_x[OF assms(6-8)])
    apply (rule continuous_on_interior[OF _ assms(3)])
    apply (rule continuous_on_inv[OF assms(4,1)])
    apply (rule assms(2,5) assms(5)[rule_format] open_interior assms(3))+
    apply (metis *)
    done
qed


subsection {* Proving surjectivity via Brouwer fixpoint theorem *}

lemma brouwer_surjective:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "compact t"
    and "convex t"
    and "t \<noteq> {}"
    and "continuous_on t f"
    and "\<forall>x\<in>s. \<forall>y\<in>t. x + (y - f y) \<in> t"
    and "x \<in> s"
  shows "\<exists>y\<in>t. f y = x"
proof -
  have *: "\<And>x y. f y = x \<longleftrightarrow> x + (y - f y) = y"
    by (auto simp add: algebra_simps)
  show ?thesis
    unfolding *
    apply (rule brouwer[OF assms(1-3), of "\<lambda>y. x + (y - f y)"])
    apply (rule continuous_on_intros assms)+
    using assms(4-6)
    apply auto
    done
qed

lemma brouwer_surjective_cball:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "e > 0"
    and "continuous_on (cball a e) f"
    and "\<forall>x\<in>s. \<forall>y\<in>cball a e. x + (y - f y) \<in> cball a e"
    and "x \<in> s"
  shows "\<exists>y\<in>cball a e. f y = x"
  apply (rule brouwer_surjective)
  apply (rule compact_cball convex_cball)+
  unfolding cball_eq_empty
  using assms
  apply auto
  done

text {* See Sussmann: "Multidifferential calculus", Theorem 2.1.1 *}

lemma sussmann_open_mapping:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open s"
    and "continuous_on s f"
    and "x \<in> s"
    and "(f has_derivative f') (at x)"
    and "bounded_linear g'" "f' \<circ> g' = id"
    and "t \<subseteq> s"
    and "x \<in> interior t"
  shows "f x \<in> interior (f ` t)"
proof -
  interpret f': bounded_linear f'
    using assms
    unfolding has_derivative_def
    by auto
  interpret g': bounded_linear g'
    using assms
    by auto
  obtain B where B: "0 < B" "\<forall>x. norm (g' x) \<le> norm x * B"
    using bounded_linear.pos_bounded[OF assms(5)] by blast
  then have *: "1 / (2 * B) > 0"
    by (auto intro!: divide_pos_pos)
  obtain e0 where e0:
      "0 < e0"
      "\<forall>y. norm (y - x) < e0 \<longrightarrow> norm (f y - f x - f' (y - x)) \<le> 1 / (2 * B) * norm (y - x)"
    using assms(4)
    unfolding has_derivative_at_alt
    using * by blast
  obtain e1 where e1: "0 < e1" "cball x e1 \<subseteq> t"
    using assms(8)
    unfolding mem_interior_cball
    by blast
  have *: "0 < e0 / B" "0 < e1 / B"
    apply (rule_tac[!] divide_pos_pos)
    using e0 e1 B
    apply auto
    done
  obtain e where e: "0 < e" "e < e0 / B" "e < e1 / B"
    using real_lbound_gt_zero[OF *] by blast
  have "\<forall>z\<in>cball (f x) (e / 2). \<exists>y\<in>cball (f x) e. f (x + g' (y - f x)) = z"
    apply rule
    apply (rule brouwer_surjective_cball[where s="cball (f x) (e/2)"])
    prefer 3
    apply rule
    apply rule
  proof-
    show "continuous_on (cball (f x) e) (\<lambda>y. f (x + g' (y - f x)))"
      unfolding g'.diff
      apply (rule continuous_on_compose[of _ _ f, unfolded o_def])
      apply (rule continuous_on_intros linear_continuous_on[OF assms(5)])+
      apply (rule continuous_on_subset[OF assms(2)])
      apply rule
      apply (unfold image_iff)
      apply (erule bexE)
    proof-
      fix y z
      assume as: "y \<in>cball (f x) e" "z = x + (g' y - g' (f x))"
      have "dist x z = norm (g' (f x) - g' y)"
        unfolding as(2) and dist_norm by auto
      also have "\<dots> \<le> norm (f x - y) * B"
        unfolding g'.diff[symmetric]
        using B
        by auto
      also have "\<dots> \<le> e * B"
        using as(1)[unfolded mem_cball dist_norm]
        using B
        by auto
      also have "\<dots> \<le> e1"
        using e
        unfolding less_divide_eq
        using B
        by auto
      finally have "z \<in> cball x e1"
        unfolding mem_cball
        by force
      then show "z \<in> s"
        using e1 assms(7) by auto
    qed
  next
    fix y z
    assume as: "y \<in> cball (f x) (e / 2)" "z \<in> cball (f x) e"
    have "norm (g' (z - f x)) \<le> norm (z - f x) * B"
      using B by auto
    also have "\<dots> \<le> e * B"
      apply (rule mult_right_mono)
      using as(2)[unfolded mem_cball dist_norm] and B
      unfolding norm_minus_commute
      apply auto
      done
    also have "\<dots> < e0"
      using e and B
      unfolding less_divide_eq
      by auto
    finally have *: "norm (x + g' (z - f x) - x) < e0"
      by auto
    have **: "f x + f' (x + g' (z - f x) - x) = z"
      using assms(6)[unfolded o_def id_def,THEN cong]
      by auto
    have "norm (f x - (y + (z - f (x + g' (z - f x))))) \<le>
        norm (f (x + g' (z - f x)) - z) + norm (f x - y)"
      using norm_triangle_ineq[of "f (x + g'(z - f x)) - z" "f x - y"]
      by (auto simp add: algebra_simps)
    also have "\<dots> \<le> 1 / (B * 2) * norm (g' (z - f x)) + norm (f x - y)"
      using e0(2)[rule_format, OF *]
      unfolding algebra_simps **
      by auto
    also have "\<dots> \<le> 1 / (B * 2) * norm (g' (z - f x)) + e/2"
      using as(1)[unfolded mem_cball dist_norm]
      by auto
    also have "\<dots> \<le> 1 / (B * 2) * B * norm (z - f x) + e/2"
      using * and B
      by (auto simp add: field_simps)
    also have "\<dots> \<le> 1 / 2 * norm (z - f x) + e/2"
      by auto
    also have "\<dots> \<le> e/2 + e/2"
      apply (rule add_right_mono)
      using as(2)[unfolded mem_cball dist_norm]
      unfolding norm_minus_commute
      apply auto
      done
    finally show "y + (z - f (x + g' (z - f x))) \<in> cball (f x) e"
      unfolding mem_cball dist_norm
      by auto
  qed (insert e, auto) note lem = this
  show ?thesis
    unfolding mem_interior
    apply (rule_tac x="e/2" in exI)
    apply rule
    apply (rule divide_pos_pos)
    prefer 3
  proof
    fix y
    assume "y \<in> ball (f x) (e / 2)"
    then have *: "y \<in> cball (f x) (e / 2)"
      by auto
    obtain z where z: "z \<in> cball (f x) e" "f (x + g' (z - f x)) = y"
      using lem * by blast
    then have "norm (g' (z - f x)) \<le> norm (z - f x) * B"
      using B
      by (auto simp add: field_simps)
    also have "\<dots> \<le> e * B"
      apply (rule mult_right_mono)
      using z(1)
      unfolding mem_cball dist_norm norm_minus_commute
      using B
      apply auto
      done
    also have "\<dots> \<le> e1"
      using e B unfolding less_divide_eq by auto
    finally have "x + g'(z - f x) \<in> t"
      apply -
      apply (rule e1(2)[unfolded subset_eq,rule_format])
      unfolding mem_cball dist_norm
      apply auto
      done
    then show "y \<in> f ` t"
      using z by auto
  qed (insert e, auto)
qed

text {* Hence the following eccentric variant of the inverse function theorem.
  This has no continuity assumptions, but we do need the inverse function.
  We could put @{text "f' \<circ> g = I"} but this happens to fit with the minimal linear
  algebra theory I've set up so far. *}

(* move  before left_inverse_linear in Euclidean_Space*)

lemma right_inverse_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lf: "linear f"
    and gf: "f \<circ> g = id"
  shows "linear g"
proof -
  from gf have fi: "surj f"
    by (auto simp add: surj_def o_def id_def) metis
  from linear_surjective_isomorphism[OF lf fi]
  obtain h:: "'a \<Rightarrow> 'a" where h: "linear h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x"
    by blast
  have "h = g"
    apply (rule ext)
    using gf h(2,3)
    apply (simp add: o_def id_def fun_eq_iff)
    apply metis
    done
  with h(1) show ?thesis by blast
qed

lemma has_derivative_inverse_strong:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "open s"
    and "x \<in> s"
    and "continuous_on s f"
    and "\<forall>x\<in>s. g (f x) = x"
    and "(f has_derivative f') (at x)"
    and "f' \<circ> g' = id"
  shows "(g has_derivative g') (at (f x))"
proof -
  have linf: "bounded_linear f'"
    using assms(5) unfolding has_derivative_def by auto
  then have ling: "bounded_linear g'"
    unfolding linear_conv_bounded_linear[symmetric]
    apply -
    apply (rule right_inverse_linear)
    using assms(6)
    apply auto
    done
  moreover have "g' \<circ> f' = id"
    using assms(6) linf ling
    unfolding linear_conv_bounded_linear[symmetric]
    using linear_inverse_left
    by auto
  moreover have *:"\<forall>t\<subseteq>s. x \<in> interior t \<longrightarrow> f x \<in> interior (f ` t)"
    apply clarify
    apply (rule sussmann_open_mapping)
    apply (rule assms ling)+
    apply auto
    done
  have "continuous (at (f x)) g"
    unfolding continuous_at Lim_at
  proof (rule, rule)
    fix e :: real
    assume "e > 0"
    then have "f x \<in> interior (f ` (ball x e \<inter> s))"
      using *[rule_format,of "ball x e \<inter> s"] `x \<in> s`
      by (auto simp add: interior_open[OF open_ball] interior_open[OF assms(1)])
    then obtain d where d: "0 < d" "ball (f x) d \<subseteq> f ` (ball x e \<inter> s)"
      unfolding mem_interior by blast
    show "\<exists>d>0. \<forall>y. 0 < dist y (f x) \<and> dist y (f x) < d \<longrightarrow> dist (g y) (g (f x)) < e"
      apply (rule_tac x=d in exI)
      apply rule
      apply (rule d(1))
      apply rule
      apply rule
    proof -
      case goal1
      then have "g y \<in> g ` f ` (ball x e \<inter> s)"
        using d(2)[unfolded subset_eq,THEN bspec[where x=y]]
        by (auto simp add: dist_commute)
      then have "g y \<in> ball x e \<inter> s"
        using assms(4) by auto
      then show "dist (g y) (g (f x)) < e"
        using assms(4)[rule_format,OF `x \<in> s`]
        by (auto simp add: dist_commute)
    qed
  qed
  moreover have "f x \<in> interior (f ` s)"
    apply (rule sussmann_open_mapping)
    apply (rule assms ling)+
    using interior_open[OF assms(1)] and `x \<in> s`
    apply auto
    done
  moreover have "\<And>y. y \<in> interior (f ` s) \<Longrightarrow> f (g y) = y"
  proof -
    case goal1
    then have "y \<in> f ` s"
      using interior_subset by auto
    then obtain z where "z \<in> s" "y = f z" unfolding image_iff ..
    then show ?case
      using assms(4) by auto
  qed
  ultimately show ?thesis using assms
    by (metis has_derivative_inverse_basic_x open_interior)
qed

text {* A rewrite based on the other domain. *}

lemma has_derivative_inverse_strong_x:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "open s"
    and "g y \<in> s"
    and "continuous_on s f"
    and "\<forall>x\<in>s. g (f x) = x"
    and "(f has_derivative f') (at (g y))"
    and "f' \<circ> g' = id"
    and "f (g y) = y"
  shows "(g has_derivative g') (at y)"
  using has_derivative_inverse_strong[OF assms(1-6)]
  unfolding assms(7)
  by simp

text {* On a region. *}

lemma has_derivative_inverse_on:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "open s"
    and "\<forall>x\<in>s. (f has_derivative f'(x)) (at x)"
    and "\<forall>x\<in>s. g (f x) = x"
    and "f' x \<circ> g' x = id"
    and "x \<in> s"
  shows "(g has_derivative g'(x)) (at (f x))"
  apply (rule has_derivative_inverse_strong[where g'="g' x" and f=f])
  apply (rule assms)+
  unfolding continuous_on_eq_continuous_at[OF assms(1)]
  apply rule
  apply (rule differentiable_imp_continuous_within)
  unfolding differentiable_def
  using assms
  apply auto
  done

text {* Invertible derivative continous at a point implies local
injectivity. It's only for this we need continuity of the derivative,
except of course if we want the fact that the inverse derivative is
also continuous. So if we know for some other reason that the inverse
function exists, it's OK. *}

lemma bounded_linear_sub: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_linear (\<lambda>x. f x - g x)"
  using bounded_linear_add[of f "\<lambda>x. - g x"] bounded_linear_minus[of g]
  by (auto simp add: algebra_simps)

lemma has_derivative_locally_injective:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "a \<in> s"
    and "open s"
    and "bounded_linear g'"
    and "g' \<circ> f' a = id"
    and "\<forall>x\<in>s. (f has_derivative f' x) (at x)"
    and "\<forall>e>0. \<exists>d>0. \<forall>x. dist a x < d \<longrightarrow> onorm (\<lambda>v. f' x v - f' a v) < e"
  obtains t where "a \<in> t" "open t" "\<forall>x\<in>t. \<forall>x'\<in>t. f x' = f x \<longrightarrow> x' = x"
proof -
  interpret bounded_linear g'
    using assms by auto
  note f'g' = assms(4)[unfolded id_def o_def,THEN cong]
  have "g' (f' a (\<Sum>Basis)) = (\<Sum>Basis)" "(\<Sum>Basis) \<noteq> (0::'n)"
    defer
    apply (subst euclidean_eq_iff)
    using f'g'
    apply auto
    done
  then have *: "0 < onorm g'"
    unfolding onorm_pos_lt[OF assms(3)[unfolded linear_linear]]
    by fastforce
  def k \<equiv> "1 / onorm g' / 2"
  have *: "k > 0"
    unfolding k_def using * by auto
  obtain d1 where d1:
      "0 < d1"
      "\<And>x. dist a x < d1 \<Longrightarrow> onorm (\<lambda>v. f' x v - f' a v) < k"
    using assms(6) * by blast
  from `open s` obtain d2 where "d2 > 0" "ball a d2 \<subseteq> s"
    using `a\<in>s` ..
  obtain d2 where "d2 > 0" "ball a d2 \<subseteq> s"
    using assms(2,1) ..
  obtain d2 where d2: "0 < d2" "ball a d2 \<subseteq> s"
    using assms(2)
    unfolding open_contains_ball
    using `a\<in>s` by blast
  obtain d where d: "0 < d" "d < d1" "d < d2"
    using real_lbound_gt_zero[OF d1(1) d2(1)] by blast
  show ?thesis
  proof
    show "a \<in> ball a d"
      using d by auto
    show "\<forall>x\<in>ball a d. \<forall>x'\<in>ball a d. f x' = f x \<longrightarrow> x' = x"
    proof (intro strip)
      fix x y
      assume as: "x \<in> ball a d" "y \<in> ball a d" "f x = f y"
      def ph \<equiv> "\<lambda>w. w - g' (f w - f x)"
      have ph':"ph = g' \<circ> (\<lambda>w. f' a w - (f w - f x))"
        unfolding ph_def o_def
        unfolding diff
        using f'g'
        by (auto simp add: algebra_simps)
      have "norm (ph x - ph y) \<le> (1 / 2) * norm (x - y)"
        apply (rule differentiable_bound[OF convex_ball _ _ as(1-2), where f'="\<lambda>x v. v - g'(f' x v)"])
        apply (rule_tac[!] ballI)
      proof -
        fix u
        assume u: "u \<in> ball a d"
        then have "u \<in> s"
          using d d2 by auto
        have *: "(\<lambda>v. v - g' (f' u v)) = g' \<circ> (\<lambda>w. f' a w - f' u w)"
          unfolding o_def and diff
          using f'g' by auto
        show "(ph has_derivative (\<lambda>v. v - g' (f' u v))) (at u within ball a d)"
          unfolding ph' *
          apply (simp add: comp_def)
          apply (rule bounded_linear.has_derivative[OF assms(3)])
          apply (rule has_derivative_intros)
          defer
          apply (rule has_derivative_sub[where g'="\<lambda>x.0",unfolded diff_0_right])
          apply (rule has_derivative_at_within)
          using assms(5) and `u \<in> s` `a \<in> s`
          apply (auto intro!: has_derivative_intros bounded_linear.has_derivative[of _ "\<lambda>x. x"] derivative_linear)
          done
        have **: "bounded_linear (\<lambda>x. f' u x - f' a x)" "bounded_linear (\<lambda>x. f' a x - f' u x)"
          apply (rule_tac[!] bounded_linear_sub)
          apply (rule_tac[!] derivative_linear)
          using assms(5) `u \<in> s` `a \<in> s`
          apply auto
          done
        have "onorm (\<lambda>v. v - g' (f' u v)) \<le> onorm g' * onorm (\<lambda>w. f' a w - f' u w)"
          unfolding *
          apply (rule onorm_compose)
          unfolding linear_conv_bounded_linear
          apply (rule assms(3) **)+
          done
        also have "\<dots> \<le> onorm g' * k"
          apply (rule mult_left_mono)
          using d1(2)[of u]
          using onorm_neg[OF **(1)[unfolded linear_linear]]
          using d and u and onorm_pos_le[OF assms(3)[unfolded linear_linear]]
          apply (auto simp add: algebra_simps)
          done
        also have "\<dots> \<le> 1 / 2"
          unfolding k_def by auto
        finally show "onorm (\<lambda>v. v - g' (f' u v)) \<le> 1 / 2" .
      qed
      moreover have "norm (ph y - ph x) = norm (y - x)"
        apply (rule arg_cong[where f=norm])
        unfolding ph_def
        using diff
        unfolding as
        apply auto
        done
      ultimately show "x = y"
        unfolding norm_minus_commute by auto
    qed
  qed auto
qed


subsection {* Uniformly convergent sequence of derivatives *}

lemma has_derivative_sequence_lipschitz_lemma:
  fixes f :: "nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
  shows "\<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm ((f m x - f n x) - (f m y - f n y)) \<le> 2 * e * norm (x - y)"
proof rule+
  fix m n x y
  assume as: "N \<le> m" "N \<le> n" "x \<in> s" "y \<in> s"
  show "norm ((f m x - f n x) - (f m y - f n y)) \<le> 2 * e * norm (x - y)"
    apply (rule differentiable_bound[where f'="\<lambda>x h. f' m x h - f' n x h", OF assms(1) _ _ as(3-4)])
    apply (rule_tac[!] ballI)
  proof -
    fix x
    assume "x \<in> s"
    show "((\<lambda>a. f m a - f n a) has_derivative (\<lambda>h. f' m x h - f' n x h)) (at x within s)"
      by (rule has_derivative_intros assms(2)[rule_format] `x\<in>s`)+
    {
      fix h
      have "norm (f' m x h - f' n x h) \<le> norm (f' m x h - g' x h) + norm (f' n x h - g' x h)"
        using norm_triangle_ineq[of "f' m x h - g' x h" "- f' n x h + g' x h"]
        unfolding norm_minus_commute
        by (auto simp add: algebra_simps)
      also have "\<dots> \<le> e * norm h + e * norm h"
        using assms(3)[rule_format,OF `N \<le> m` `x \<in> s`, of h]
        using assms(3)[rule_format,OF `N \<le> n` `x \<in> s`, of h]
        by (auto simp add: field_simps)
      finally have "norm (f' m x h - f' n x h) \<le> 2 * e * norm h"
        by auto
    }
    then show "onorm (\<lambda>h. f' m x h - f' n x h) \<le> 2 * e"
      apply -
      apply (rule onorm(2))
      apply (rule linear_compose_sub)
      unfolding linear_conv_bounded_linear
      using assms(2)[rule_format,OF `x \<in> s`, THEN derivative_linear]
      apply auto
      done
  qed
qed

lemma has_derivative_sequence_lipschitz:
  fixes f :: "nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
    and "e > 0"
  shows "\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s.
    norm ((f m x - f n x) - (f m y - f n y)) \<le> e * norm (x - y)"
proof (rule, rule)
  case goal1 have *: "2 * (1/2* e) = e" "1/2 * e >0"
    using `e > 0` by auto
  obtain N where "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> 1 / 2 * e * norm h"
    using assms(3) *(2) by blast
  then show ?case
    apply (rule_tac x=N in exI)
    apply (rule has_derivative_sequence_lipschitz_lemma[where e="1/2 *e", unfolded *])
    using assms
    apply auto
    done
qed

lemma has_derivative_sequence:
  fixes f::"nat\<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
    and "x0 \<in> s"
    and "((\<lambda>n. f n x0) ---> l) sequentially"
  shows "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) ---> g x) sequentially \<and> (g has_derivative g'(x)) (at x within s)"
proof -
  have lem1: "\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s.
      norm ((f m x - f n x) - (f m y - f n y)) \<le> e * norm (x - y)"
    apply (rule has_derivative_sequence_lipschitz[where e="42::nat"])
    apply (rule assms)+
    apply auto
    done
  have "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) ---> g x) sequentially"
    apply (rule bchoice)
    unfolding convergent_eq_cauchy
  proof
    fix x
    assume "x \<in> s"
    show "Cauchy (\<lambda>n. f n x)"
    proof (cases "x = x0")
      case True
      then show ?thesis
        using LIMSEQ_imp_Cauchy[OF assms(5)] by auto
    next
      case False
      show ?thesis
        unfolding Cauchy_def
      proof (rule, rule)
        fix e :: real
        assume "e > 0"
        then have *: "e / 2 > 0" "e / 2 / norm (x - x0) > 0"
          using False by (auto intro!: divide_pos_pos)
        obtain M where M: "\<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x0) (f n x0) < e / 2"
          using LIMSEQ_imp_Cauchy[OF assms(5)]
          unfolding Cauchy_def
          using *(1) by blast
        obtain N where N:
          "\<forall>m\<ge>N. \<forall>n\<ge>N.
            \<forall>xa\<in>s. \<forall>y\<in>s. norm (f m xa - f n xa - (f m y - f n y)) \<le>
              e / 2 / norm (x - x0) * norm (xa - y)"
        using lem1 *(2) by blast
        show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e"
          apply (rule_tac x="max M N" in exI)
        proof rule+
          fix m n
          assume as: "max M N \<le>m" "max M N\<le>n"
          have "dist (f m x) (f n x) \<le>
              norm (f m x0 - f n x0) + norm (f m x - f n x - (f m x0 - f n x0))"
            unfolding dist_norm
            by (rule norm_triangle_sub)
          also have "\<dots> \<le> norm (f m x0 - f n x0) + e / 2"
            using N[rule_format,OF _ _ `x\<in>s` `x0\<in>s`, of m n] and as and False
            by auto
          also have "\<dots> < e / 2 + e / 2"
            apply (rule add_strict_right_mono)
            using as and M[rule_format]
            unfolding dist_norm
            apply auto
            done
          finally show "dist (f m x) (f n x) < e"
            by auto
        qed
      qed
    qed
  qed
  then obtain g where g: "\<forall>x\<in>s. (\<lambda>n. f n x) ----> g x" ..
  have lem2: "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm ((f n x - f n y) - (g x - g y)) \<le> e * norm (x - y)"
  proof (rule, rule)
    fix e :: real
    assume *: "e > 0"
    obtain N where
      N: "\<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm (f m x - f n x - (f m y - f n y)) \<le> e * norm (x - y)"
      using lem1 * by blast
    show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm (f n x - f n y - (g x - g y)) \<le> e * norm (x - y)"
      apply (rule_tac x=N in exI)
    proof rule+
      fix n x y
      assume as: "N \<le> n" "x \<in> s" "y \<in> s"
      have "eventually (\<lambda>xa. norm (f n x - f n y - (f xa x - f xa y)) \<le> e * norm (x - y)) sequentially"
        unfolding eventually_sequentially
        apply (rule_tac x=N in exI)
        apply rule
        apply rule
      proof -
        fix m
        assume "N \<le> m"
        then show "norm (f n x - f n y - (f m x - f m y)) \<le> e * norm (x - y)"
          using N[rule_format, of n m x y] and as
          by (auto simp add: algebra_simps)
      qed
      then show "norm (f n x - f n y - (g x - g y)) \<le> e * norm (x - y)"
        apply -
        apply (rule Lim_norm_ubound[OF trivial_limit_sequentially, where f="\<lambda>m. (f n x - f n y) - (f m x - f m y)"])
        apply (rule tendsto_intros g[rule_format] as)+
        apply assumption
        done
    qed
  qed
  show ?thesis
    unfolding has_derivative_within_alt
    apply (rule_tac x=g in exI)
    apply rule
    apply rule
    apply (rule g[rule_format])
    apply assumption
  proof
    fix x
    assume "x \<in> s"
    have lem3: "\<forall>u. ((\<lambda>n. f' n x u) ---> g' x u) sequentially"
      unfolding LIMSEQ_def
    proof (rule, rule, rule)
      fix u
      fix e :: real
      assume "e > 0"
      show "\<exists>N. \<forall>n\<ge>N. dist (f' n x u) (g' x u) < e"
      proof (cases "u = 0")
        case True
        obtain N where N: "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
          using assms(3) `e>0` by blast
        show ?thesis
          apply (rule_tac x=N in exI)
          unfolding True
          using N[rule_format,OF _ `x\<in>s`,of _ 0] and `e>0`
          apply auto
          done
      next
        case False
        then have *: "e / 2 / norm u > 0"
          using `e > 0`
          by (auto intro!: divide_pos_pos)
        obtain N where N: "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e / 2 / norm u * norm h"
          using assms(3) * by blast
        show ?thesis
          apply (rule_tac x=N in exI)
          apply rule
          apply rule
        proof -
          case goal1
          show ?case
            unfolding dist_norm
            using N[rule_format,OF goal1 `x\<in>s`, of u] False `e>0`
            by (auto simp add: field_simps)
        qed
      qed
    qed
    show "bounded_linear (g' x)"
      unfolding linear_linear linear_iff
      apply rule
      apply rule
      apply rule
      defer
      apply rule
      apply rule
    proof -
      fix x' y z :: 'm
      fix c :: real
      note lin = assms(2)[rule_format,OF `x\<in>s`,THEN derivative_linear]
      show "g' x (c *\<^sub>R x') = c *\<^sub>R g' x x'"
        apply (rule tendsto_unique[OF trivial_limit_sequentially])
        apply (rule lem3[rule_format])
        unfolding lin[THEN bounded_linear_imp_linear, THEN linear_cmul]
        apply (intro tendsto_intros)
        apply (rule lem3[rule_format])
        done
      show "g' x (y + z) = g' x y + g' x z"
        apply (rule tendsto_unique[OF trivial_limit_sequentially])
        apply (rule lem3[rule_format])
        unfolding lin[THEN bounded_linear_imp_linear, THEN linear_add]
        apply (rule tendsto_add)
        apply (rule lem3[rule_format])+
        done
    qed
    show "\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm (y - x) < d \<longrightarrow> norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)"
    proof (rule, rule)
      case goal1
      have *: "e / 3 > 0"
        using goal1 by auto
      obtain N1 where N1: "\<forall>n\<ge>N1. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e / 3 * norm h"
        using assms(3) * by blast
      obtain N2 where
          N2: "\<forall>n\<ge>N2. \<forall>x\<in>s. \<forall>y\<in>s. norm (f n x - f n y - (g x - g y)) \<le> e / 3 * norm (x - y)"
        using lem2 * by blast
      obtain d1 where d1:
          "0 < d1"
          "\<forall>y\<in>s. norm (y - x) < d1 \<longrightarrow>
            norm (f (max N1 N2) y - f (max N1 N2) x - f' (max N1 N2) x (y - x)) \<le>
            e / 3 * norm (y - x)"
        using assms(2)[unfolded has_derivative_within_alt, rule_format,
            OF `x\<in>s`, of "max N1 N2", THEN conjunct2, rule_format, OF *]
        by blast
      show ?case
        apply (rule_tac x=d1 in exI)
        apply rule
        apply (rule d1(1))
        apply rule
        apply rule
      proof -
        fix y
        assume as: "y \<in> s" "norm (y - x) < d1"
        let ?N = "max N1 N2"
        have "norm (g y - g x - (f ?N y - f ?N x)) \<le> e /3 * norm (y - x)"
          apply (subst norm_minus_cancel[symmetric])
          using N2[rule_format, OF _ `y \<in> s` `x \<in> s`, of ?N]
          apply auto
          done
        moreover
        have "norm (f ?N y - f ?N x - f' ?N x (y - x)) \<le> e / 3 * norm (y - x)"
          using d1 and as
          by auto
        ultimately
        have "norm (g y - g x - f' ?N x (y - x)) \<le> 2 * e / 3 * norm (y - x)"
          using norm_triangle_le[of "g y - g x - (f ?N y - f ?N x)" "f ?N y - f ?N x - f' ?N x (y - x)" "2 * e / 3 * norm (y - x)"]
          by (auto simp add: algebra_simps)
        moreover
        have " norm (f' ?N x (y - x) - g' x (y - x)) \<le> e / 3 * norm (y - x)"
          using N1 `x \<in> s` by auto
        ultimately show "norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)"
          using norm_triangle_le[of "g y - g x - f' (max N1 N2) x (y - x)" "f' (max N1 N2) x (y - x) - g' x (y - x)"]
          by (auto simp add: algebra_simps)
      qed
    qed
  qed
qed

text {* Can choose to line up antiderivatives if we want. *}

lemma has_antiderivative_sequence:
  fixes f :: "nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
  shows "\<exists>g. \<forall>x\<in>s. (g has_derivative g' x) (at x within s)"
proof (cases "s = {}")
  case False
  then obtain a where "a \<in> s"
    by auto
  have *: "\<And>P Q. \<exists>g. \<forall>x\<in>s. P g x \<and> Q g x \<Longrightarrow> \<exists>g. \<forall>x\<in>s. Q g x"
    by auto
  show ?thesis
    apply (rule *)
    apply (rule has_derivative_sequence[OF assms(1) _ assms(3), of "\<lambda>n x. f n x + (f 0 a - f n a)"])
    apply (metis assms(2) has_derivative_add_const)
    apply (rule `a \<in> s`)
    apply auto
    done
qed auto

lemma has_antiderivative_limit:
  fixes g' :: "'m::euclidean_space \<Rightarrow> 'm \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
    and "\<forall>e>0. \<exists>f f'. \<forall>x\<in>s.
      (f has_derivative (f' x)) (at x within s) \<and> (\<forall>h. norm (f' x h - g' x h) \<le> e * norm h)"
  shows "\<exists>g. \<forall>x\<in>s. (g has_derivative g' x) (at x within s)"
proof -
  have *: "\<forall>n. \<exists>f f'. \<forall>x\<in>s.
    (f has_derivative (f' x)) (at x within s) \<and>
    (\<forall>h. norm(f' x h - g' x h) \<le> inverse (real (Suc n)) * norm h)"
    by (metis assms(2) inverse_positive_iff_positive real_of_nat_Suc_gt_zero)
  obtain f where
    *: "\<forall>x. \<exists>f'. \<forall>xa\<in>s. (f x has_derivative f' xa) (at xa within s) \<and>
      (\<forall>h. norm (f' xa h - g' xa h) \<le> inverse (real (Suc x)) * norm h)"
    using *[THEN choice] ..
  obtain f' where
    f: "\<forall>x. \<forall>xa\<in>s. (f x has_derivative f' x xa) (at xa within s) \<and>
      (\<forall>h. norm (f' x xa h - g' xa h) \<le> inverse (real (Suc x)) * norm h)"
    using *[THEN choice] ..
  show ?thesis
    apply (rule has_antiderivative_sequence[OF assms(1), of f f'])
    defer
    apply rule
    apply rule
  proof -
    fix e :: real
    assume "e > 0"
    obtain N where N: "inverse (real (Suc N)) < e"
      using reals_Archimedean[OF `e>0`] ..
    show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
      apply (rule_tac x=N in exI)
    proof rule+
      case goal1
      have *: "inverse (real (Suc n)) \<le> e"
        apply (rule order_trans[OF _ N[THEN less_imp_le]])
        using goal1(1)
        apply (auto simp add: field_simps)
        done
      show ?case
        using f[rule_format,THEN conjunct2,OF goal1(2), of n, THEN spec[where x=h]]
        apply (rule order_trans)
        using N *
        apply (cases "h = 0")
        apply auto
        done
    qed
  qed (insert f, auto)
qed


subsection {* Differentiation of a series *}

definition sums_seq :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> nat set \<Rightarrow> bool"
    (infixl "sums'_seq" 12)
  where "(f sums_seq l) s \<longleftrightarrow> ((\<lambda>n. setsum f (s \<inter> {0..n})) ---> l) sequentially"

lemma has_derivative_series:
  fixes f :: "nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (setsum (\<lambda>i. f' i x h) (k \<inter> {0..n}) - g' x h) \<le> e * norm h"
    and "x \<in> s"
    and "((\<lambda>n. f n x) sums_seq l) k"
  shows "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) sums_seq (g x)) k \<and> (g has_derivative g' x) (at x within s)"
  unfolding sums_seq_def
  apply (rule has_derivative_sequence[OF assms(1) _ assms(3)])
  apply (metis assms(2) has_derivative_setsum)
  using assms(4-5)
  unfolding sums_seq_def
  apply auto
  done


text {* Considering derivative @{typ "real \<Rightarrow> 'b\<Colon>real_normed_vector"} as a vector. *}

definition has_vector_derivative :: "(real \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> real filter \<Rightarrow> bool"
    (infixl "has'_vector'_derivative" 12)
  where "(f has_vector_derivative f') net \<longleftrightarrow> (f has_derivative (\<lambda>x. x *\<^sub>R f')) net"

definition "vector_derivative f net = (SOME f'. (f has_vector_derivative f') net)"

lemma vector_derivative_works:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "f differentiable net \<longleftrightarrow> (f has_vector_derivative (vector_derivative f net)) net"
    (is "?l = ?r")
proof
  assume ?l
  obtain f' where f': "(f has_derivative f') net"
    using `?l` unfolding differentiable_def ..
  then interpret bounded_linear f'
    by auto
  show ?r
    unfolding vector_derivative_def has_vector_derivative_def
    apply -
    apply (rule someI_ex,rule_tac x="f' 1" in exI)
    using f'
    unfolding scaleR[symmetric]
    apply auto
    done
next
  assume ?r
  then show ?l
    unfolding vector_derivative_def has_vector_derivative_def differentiable_def
    by auto
qed

lemma has_field_derivative_iff_has_vector_derivative:
  "(f has_field_derivative y) F \<longleftrightarrow> (f has_vector_derivative y) F"
  unfolding has_vector_derivative_def has_field_derivative_def real_scaleR_def mult_commute_abs ..

lemma vector_derivative_unique_at:
  assumes "(f has_vector_derivative f') (at x)"
    and "(f has_vector_derivative f'') (at x)"
  shows "f' = f''"
proof -
  have "(\<lambda>x. x *\<^sub>R f') = (\<lambda>x. x *\<^sub>R f'')"
    using assms [unfolded has_vector_derivative_def]
    by (rule frechet_derivative_unique_at)
  then show ?thesis
    unfolding fun_eq_iff by auto
qed

lemma vector_derivative_unique_within_closed_interval:
  assumes "a < b"
    and "x \<in> {a..b}"
  assumes "(f has_vector_derivative f') (at x within {a..b})"
  assumes "(f has_vector_derivative f'') (at x within {a..b})"
  shows "f' = f''"
proof -
  have *: "(\<lambda>x. x *\<^sub>R f') = (\<lambda>x. x *\<^sub>R f'')"
    apply (rule frechet_derivative_unique_within_closed_interval[of "a" "b"])
    using assms(3-)[unfolded has_vector_derivative_def]
    using assms(1-2)
    apply auto
    done
  show ?thesis
  proof (rule ccontr)
    assume **: "f' \<noteq> f''"
    with * have "(\<lambda>x. x *\<^sub>R f') 1 = (\<lambda>x. x *\<^sub>R f'') 1"
      by (auto simp: fun_eq_iff)
    with ** show False
      unfolding o_def by auto
  qed
qed

lemma vector_derivative_at:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> vector_derivative f (at x) = f'"
  apply (rule vector_derivative_unique_at)
  defer
  apply assumption
  unfolding vector_derivative_works[symmetric] differentiable_def
  unfolding has_vector_derivative_def
  apply auto
  done

lemma vector_derivative_within_closed_interval:
  assumes "a < b"
    and "x \<in> {a..b}"
  assumes "(f has_vector_derivative f') (at x within {a..b})"
  shows "vector_derivative f (at x within {a..b}) = f'"
  apply (rule vector_derivative_unique_within_closed_interval)
  using vector_derivative_works[unfolded differentiable_def]
  using assms
  apply (auto simp add:has_vector_derivative_def)
  done

lemma has_vector_derivative_within_subset:
  "(f has_vector_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (f has_vector_derivative f') (at x within t)"
  unfolding has_vector_derivative_def
  apply (rule has_derivative_within_subset)
  apply auto
  done

lemma has_vector_derivative_const: "((\<lambda>x. c) has_vector_derivative 0) net"
  unfolding has_vector_derivative_def
  using has_derivative_const
  by auto

lemma has_vector_derivative_id: "((\<lambda>x::real. x) has_vector_derivative 1) net"
  unfolding has_vector_derivative_def
  using has_derivative_id
  by auto

lemma has_vector_derivative_cmul:
  "(f has_vector_derivative f') net \<Longrightarrow>
    ((\<lambda>x. c *\<^sub>R f x) has_vector_derivative (c *\<^sub>R f')) net"
  unfolding has_vector_derivative_def
  apply (drule scaleR_right_has_derivative)
  apply (auto simp add: algebra_simps)
  done

lemma has_vector_derivative_cmul_eq:
  assumes "c \<noteq> 0"
  shows "(((\<lambda>x. c *\<^sub>R f x) has_vector_derivative (c *\<^sub>R f')) net \<longleftrightarrow> (f has_vector_derivative f') net)"
  apply (rule iffI)
  apply (drule has_vector_derivative_cmul[where c="1/c"])
  apply (rule_tac [2] has_vector_derivative_cmul)
  using assms
  apply auto
  done

lemma has_vector_derivative_neg:
  "(f has_vector_derivative f') net \<Longrightarrow> ((\<lambda>x. - f x) has_vector_derivative (- f')) net"
  unfolding has_vector_derivative_def
  apply (drule has_derivative_neg)
  apply auto
  done

lemma has_vector_derivative_add:
  assumes "(f has_vector_derivative f') net"
    and "(g has_vector_derivative g') net"
  shows "((\<lambda>x. f x + g x) has_vector_derivative (f' + g')) net"
  using has_derivative_add[OF assms[unfolded has_vector_derivative_def]]
  unfolding has_vector_derivative_def
  unfolding scaleR_right_distrib
  by auto

lemma has_vector_derivative_sub:
  assumes "(f has_vector_derivative f') net"
    and "(g has_vector_derivative g') net"
  shows "((\<lambda>x. f x - g x) has_vector_derivative (f' - g')) net"
  using has_derivative_sub[OF assms[unfolded has_vector_derivative_def]]
  unfolding has_vector_derivative_def scaleR_right_diff_distrib
  by auto

lemma has_vector_derivative_bilinear_within:
  assumes "(f has_vector_derivative f') (at x within s)"
    and "(g has_vector_derivative g') (at x within s)"
  assumes "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_vector_derivative (h (f x) g' + h f' (g x))) (at x within s)"
proof -
  interpret bounded_bilinear h
    using assms by auto
  show ?thesis
    using has_derivative_bilinear_within[OF assms(1-2)[unfolded has_vector_derivative_def], of h]
    unfolding o_def has_vector_derivative_def
    using assms(3)
    unfolding scaleR_right scaleR_left scaleR_right_distrib
    by auto
qed

lemma has_vector_derivative_bilinear_at:
  assumes "(f has_vector_derivative f') (at x)"
    and "(g has_vector_derivative g') (at x)"
  assumes "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_vector_derivative (h (f x) g' + h f' (g x))) (at x)"
  using has_vector_derivative_bilinear_within[OF assms] .

lemma has_vector_derivative_at_within:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> (f has_vector_derivative f') (at x within s)"
  unfolding has_vector_derivative_def
  by (rule has_derivative_at_within)

lemma has_vector_derivative_transform_within:
  assumes "0 < d"
    and "x \<in> s"
    and "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'"
  assumes "(f has_vector_derivative f') (at x within s)"
  shows "(g has_vector_derivative f') (at x within s)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform_within)

lemma has_vector_derivative_transform_at:
  assumes "0 < d"
    and "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'"
    and "(f has_vector_derivative f') (at x)"
  shows "(g has_vector_derivative f') (at x)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform_at)

lemma has_vector_derivative_transform_within_open:
  assumes "open s"
    and "x \<in> s"
    and "\<forall>y\<in>s. f y = g y"
    and "(f has_vector_derivative f') (at x)"
  shows "(g has_vector_derivative f') (at x)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform_within_open)

lemma vector_diff_chain_at:
  assumes "(f has_vector_derivative f') (at x)"
    and "(g has_vector_derivative g') (at (f x))"
  shows "((g \<circ> f) has_vector_derivative (f' *\<^sub>R g')) (at x)"
  using assms(2)
  unfolding has_vector_derivative_def
  apply -
  apply (drule diff_chain_at[OF assms(1)[unfolded has_vector_derivative_def]])
  apply (simp only: o_def real_scaleR_def scaleR_scaleR)
  done

lemma vector_diff_chain_within:
  assumes "(f has_vector_derivative f') (at x within s)"
    and "(g has_vector_derivative g') (at (f x) within f ` s)"
  shows "((g \<circ> f) has_vector_derivative (f' *\<^sub>R g')) (at x within s)"
  using assms(2)
  unfolding has_vector_derivative_def
  apply -
  apply (drule diff_chain_within[OF assms(1)[unfolded has_vector_derivative_def]])
  apply (simp only: o_def real_scaleR_def scaleR_scaleR)
  done

end
