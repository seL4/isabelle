(*  Title:      HOL/Analysis/Derivative.thy
    Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (translation from HOL Light)
*)

section \<open>Multivariate calculus in Euclidean space\<close>

theory Derivative
imports Brouwer_Fixpoint Operator_Norm Uniform_Limit Bounded_Linear_Function
begin

declare bounded_linear_inner_left [intro]

declare has_derivative_bounded_linear[dest]

subsection \<open>Derivatives\<close>

subsubsection \<open>Combining theorems\<close>

lemmas has_derivative_id = has_derivative_ident
lemmas has_derivative_neg = has_derivative_minus
lemmas has_derivative_sub = has_derivative_diff
lemmas scaleR_right_has_derivative = has_derivative_scaleR_right
lemmas scaleR_left_has_derivative = has_derivative_scaleR_left
lemmas inner_right_has_derivative = has_derivative_inner_right
lemmas inner_left_has_derivative = has_derivative_inner_left
lemmas mult_right_has_derivative = has_derivative_mult_right
lemmas mult_left_has_derivative = has_derivative_mult_left

lemma has_derivative_add_const:
  "(f has_derivative f') net \<Longrightarrow> ((\<lambda>x. f x + c) has_derivative f') net"
  by (intro derivative_eq_intros) auto


subsection \<open>Derivative with composed bilinear function\<close>

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

text \<open>More explicit epsilon-delta forms.\<close>

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

lemma has_derivative_at_withinI:
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
  shows "(f has_derivative (( * ) y)) (at x within ({x <..} \<inter> I)) \<longleftrightarrow>
    ((\<lambda>t. (f x - f t) / (x - t)) \<longlongrightarrow> y) (at x within ({x <..} \<inter> I))"
proof -
  have "((\<lambda>t. (f t - (f x + y * (t - x))) / \<bar>t - x\<bar>) \<longlongrightarrow> 0) (at x within ({x<..} \<inter> I)) \<longleftrightarrow>
    ((\<lambda>t. (f t - f x) / (t - x) - y) \<longlongrightarrow> 0) (at x within ({x<..} \<inter> I))"
    by (intro Lim_cong_within) (auto simp add: diff_divide_distrib add_divide_distrib)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. (f t - f x) / (t - x)) \<longlongrightarrow> y) (at x within ({x<..} \<inter> I))"
    by (simp add: Lim_null[symmetric])
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. (f x - f t) / (x - t)) \<longlongrightarrow> y) (at x within ({x<..} \<inter> I))"
    by (intro Lim_cong_within) (simp_all add: field_simps)
  finally show ?thesis
    by (simp add: bounded_linear_mult_right has_derivative_within)
qed

subsubsection \<open>Caratheodory characterization\<close>

lemmas DERIV_within_iff = has_field_derivative_iff

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
    show "continuous (at x within s) ?g" using \<open>?lhs\<close>
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

subsection \<open>Differentiability\<close>

definition
  differentiable_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
    (infix "differentiable'_on" 50)
  where "f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable (at x within s))"

lemma differentiableI: "(f has_derivative f') net \<Longrightarrow> f differentiable net"
  unfolding differentiable_def
  by auto

lemma differentiable_onD: "\<lbrakk>f differentiable_on S; x \<in> S\<rbrakk> \<Longrightarrow> f differentiable (at x within S)"
  using differentiable_on_def by blast

lemma differentiable_at_withinI: "f differentiable (at x) \<Longrightarrow> f differentiable (at x within s)"
  unfolding differentiable_def
  using has_derivative_at_withinI
  by blast

lemma differentiable_at_imp_differentiable_on:
  "(\<And>x. x \<in> s \<Longrightarrow> f differentiable at x) \<Longrightarrow> f differentiable_on s"
  by (metis differentiable_at_withinI differentiable_on_def)

corollary differentiable_iff_scaleR:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "f differentiable F \<longleftrightarrow> (\<exists>d. (f has_derivative (\<lambda>x. x *\<^sub>R d)) F)"
  by (auto simp: differentiable_def dest: has_derivative_linear linear_imp_scaleR)

lemma differentiable_on_eq_differentiable_at:
  "open s \<Longrightarrow> f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable at x)"
  unfolding differentiable_on_def
  by (metis at_within_interior interior_open)

lemma differentiable_transform_within:
  assumes "f differentiable (at x within s)"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "g differentiable (at x within s)"
   using assms has_derivative_transform_within unfolding differentiable_def
   by blast

lemma differentiable_on_ident [simp, derivative_intros]: "(\<lambda>x. x) differentiable_on S"
  by (simp add: differentiable_at_imp_differentiable_on)

lemma differentiable_on_id [simp, derivative_intros]: "id differentiable_on S"
  by (simp add: id_def)

lemma differentiable_on_const [simp, derivative_intros]: "(\<lambda>z. c) differentiable_on S"
  by (simp add: differentiable_on_def)

lemma differentiable_on_mult [simp, derivative_intros]:
  fixes f :: "'M::real_normed_vector \<Rightarrow> 'a::real_normed_algebra"
  shows "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) differentiable_on S"
  apply (simp add: differentiable_on_def differentiable_def)
  using differentiable_def differentiable_mult by blast

lemma differentiable_on_compose:
   "\<lbrakk>g differentiable_on S; f differentiable_on (g ` S)\<rbrakk> \<Longrightarrow> (\<lambda>x. f (g x)) differentiable_on S"
by (simp add: differentiable_in_compose differentiable_on_def)

lemma bounded_linear_imp_differentiable_on: "bounded_linear f \<Longrightarrow> f differentiable_on S"
  by (simp add: differentiable_on_def bounded_linear_imp_differentiable)

lemma linear_imp_differentiable_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable_on S"
by (simp add: differentiable_on_def linear_imp_differentiable)

lemma differentiable_on_minus [simp, derivative_intros]:
   "f differentiable_on S \<Longrightarrow> (\<lambda>z. -(f z)) differentiable_on S"
by (simp add: differentiable_on_def)

lemma differentiable_on_add [simp, derivative_intros]:
   "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) differentiable_on S"
by (simp add: differentiable_on_def)

lemma differentiable_on_diff [simp, derivative_intros]:
   "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) differentiable_on S"
by (simp add: differentiable_on_def)

lemma differentiable_on_inverse [simp, derivative_intros]:
  fixes f :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_field"
  shows "f differentiable_on S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow> (\<lambda>x. inverse (f x)) differentiable_on S"
by (simp add: differentiable_on_def)

lemma differentiable_on_scaleR [derivative_intros, simp]:
   "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) differentiable_on S"
  unfolding differentiable_on_def
  by (blast intro: differentiable_scaleR)

lemma has_derivative_sqnorm_at [derivative_intros, simp]:
   "((\<lambda>x. (norm x)\<^sup>2) has_derivative (\<lambda>x. 2 *\<^sub>R (a \<bullet> x))) (at a)"
using has_derivative_bilinear_at [of id id a id id "(\<bullet>)"]
by (auto simp: inner_commute dot_square_norm bounded_bilinear_inner)

lemma differentiable_sqnorm_at [derivative_intros, simp]:
  fixes a :: "'a :: {real_normed_vector,real_inner}"
  shows "(\<lambda>x. (norm x)\<^sup>2) differentiable (at a)"
by (force simp add: differentiable_def intro: has_derivative_sqnorm_at)

lemma differentiable_on_sqnorm [derivative_intros, simp]:
  fixes S :: "'a :: {real_normed_vector,real_inner} set"
  shows "(\<lambda>x. (norm x)\<^sup>2) differentiable_on S"
by (simp add: differentiable_at_imp_differentiable_on)

lemma differentiable_norm_at [derivative_intros, simp]:
  fixes a :: "'a :: {real_normed_vector,real_inner}"
  shows "a \<noteq> 0 \<Longrightarrow> norm differentiable (at a)"
using differentiableI has_derivative_norm by blast

lemma differentiable_on_norm [derivative_intros, simp]:
  fixes S :: "'a :: {real_normed_vector,real_inner} set"
  shows "0 \<notin> S \<Longrightarrow> norm differentiable_on S"
by (metis differentiable_at_imp_differentiable_on differentiable_norm_at)


subsection \<open>Frechet derivative and Jacobian matrix\<close>

definition "frechet_derivative f net = (SOME f'. (f has_derivative f') net)"

lemma frechet_derivative_works:
  "f differentiable net \<longleftrightarrow> (f has_derivative (frechet_derivative f net)) net"
  unfolding frechet_derivative_def differentiable_def
  unfolding some_eq_ex[of "\<lambda> f' . (f has_derivative f') net"] ..

lemma linear_frechet_derivative: "f differentiable net \<Longrightarrow> linear (frechet_derivative f net)"
  unfolding frechet_derivative_works has_derivative_def
  by (auto intro: bounded_linear.linear)


subsection \<open>Differentiability implies continuity\<close>

lemma differentiable_imp_continuous_within:
  "f differentiable (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by (auto simp: differentiable_def intro: has_derivative_continuous)

lemma differentiable_imp_continuous_on:
  "f differentiable_on s \<Longrightarrow> continuous_on s f"
  unfolding differentiable_on_def continuous_on_eq_continuous_within
  using differentiable_imp_continuous_within by blast

lemma differentiable_on_subset:
  "f differentiable_on t \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f differentiable_on s"
  unfolding differentiable_on_def
  using differentiable_within_subset
  by blast

lemma differentiable_on_empty: "f differentiable_on {}"
  unfolding differentiable_on_def
  by auto

lemma has_derivative_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x within s)) \<Longrightarrow> continuous_on s f"
  by (auto intro!: differentiable_imp_continuous_on differentiableI simp: differentiable_on_def)

text \<open>Results about neighborhoods filter.\<close>

lemma eventually_nhds_metric_le:
  "eventually P (nhds a) = (\<exists>d>0. \<forall>x. dist x a \<le> d \<longrightarrow> P x)"
  unfolding eventually_nhds_metric by (safe, rule_tac x="d / 2" in exI, auto)

lemma le_nhds: "F \<le> nhds a \<longleftrightarrow> (\<forall>S. open S \<and> a \<in> S \<longrightarrow> eventually (\<lambda>x. x \<in> S) F)"
  unfolding le_filter_def eventually_nhds by (fast elim: eventually_mono)

lemma le_nhds_metric: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a < e) F)"
  unfolding le_filter_def eventually_nhds_metric by (fast elim: eventually_mono)

lemma le_nhds_metric_le: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a \<le> e) F)"
  unfolding le_filter_def eventually_nhds_metric_le by (fast elim: eventually_mono)

text \<open>Several results are easier using a "multiplied-out" variant.
(I got this idea from Dieudonne's proof of the chain rule).\<close>

lemma has_derivative_within_alt:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm(y - x) < d \<longrightarrow> norm (f y - f x - f' (y - x)) \<le> e * norm (y - x))"
  unfolding has_derivative_within filterlim_def le_nhds_metric_le eventually_filtermap
    eventually_at dist_norm diff_diff_eq
  by (force simp add: linear_0 bounded_linear.linear pos_divide_le_eq)

lemma has_derivative_within_alt2:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. eventually (\<lambda>y. norm (f y - f x - f' (y - x)) \<le> e * norm (y - x)) (at x within s))"
  unfolding has_derivative_within filterlim_def le_nhds_metric_le eventually_filtermap
    eventually_at dist_norm diff_diff_eq
  by (force simp add: linear_0 bounded_linear.linear pos_divide_le_eq)

lemma has_derivative_at_alt:
  "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y. norm(y - x) < d \<longrightarrow> norm (f y - f x - f'(y - x)) \<le> e * norm (y - x))"
  using has_derivative_within_alt[where s=UNIV]
  by simp


subsection \<open>The chain rule\<close>

lemma diff_chain_within[derivative_intros]:
  assumes "(f has_derivative f') (at x within s)"
    and "(g has_derivative g') (at (f x) within (f ` s))"
  shows "((g \<circ> f) has_derivative (g' \<circ> f'))(at x within s)"
  using has_derivative_in_compose[OF assms]
  by (simp add: comp_def)

lemma diff_chain_at[derivative_intros]:
  "(f has_derivative f') (at x) \<Longrightarrow>
    (g has_derivative g') (at (f x)) \<Longrightarrow> ((g \<circ> f) has_derivative (g' \<circ> f')) (at x)"
  using has_derivative_compose[of f f' x UNIV g g']
  by (simp add: comp_def)

lemma field_vector_diff_chain_within:
 assumes Df: "(f has_vector_derivative f') (at x within s)"
     and Dg: "(g has_field_derivative g') (at (f x) within f`s)"
 shows "((g \<circ> f) has_vector_derivative (f' * g')) (at x within s)"
using diff_chain_within[OF Df[unfolded has_vector_derivative_def]
                       Dg [unfolded has_field_derivative_def]]
 by (auto simp: o_def mult.commute has_vector_derivative_def)

lemma vector_derivative_diff_chain_within:
  assumes Df: "(f has_vector_derivative f') (at x within s)"
     and Dg: "(g has_derivative g') (at (f x) within f`s)"
  shows "((g \<circ> f) has_vector_derivative (g' f')) (at x within s)"
using diff_chain_within[OF Df[unfolded has_vector_derivative_def] Dg]
  linear.scaleR[OF has_derivative_linear[OF Dg]]
  unfolding has_vector_derivative_def o_def
  by (auto simp: o_def mult.commute has_vector_derivative_def)


subsection \<open>Composition rules stated just for differentiability\<close>

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


subsection \<open>Uniqueness of derivative\<close>


text \<open>
 The general result is a bit messy because we need approachability of the
 limit point from any direction. But OK for nontrivial intervals etc.
\<close>

lemma frechet_derivative_unique_within:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_derivative f') (at x within s)"
    and "(f has_derivative f'') (at x within s)"
    and "\<forall>i\<in>Basis. \<forall>e>0. \<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> (x + d *\<^sub>R i) \<in> s"
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
      using assms(3) SOME_Basis \<open>e>0\<close> by blast
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
    define e where "e = norm (f' i - f'' i)"
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
      using \<open>e>0\<close> by blast
    obtain c where c: "0 < \<bar>c\<bar>" "\<bar>c\<bar> < d \<and> x + c *\<^sub>R i \<in> s"
      using assms(3) i d(1) by blast
    have *: "norm (- ((1 / \<bar>c\<bar>) *\<^sub>R f' (c *\<^sub>R i)) + (1 / \<bar>c\<bar>) *\<^sub>R f'' (c *\<^sub>R i)) =
        norm ((1 / \<bar>c\<bar>) *\<^sub>R (- (f' (c *\<^sub>R i)) + f'' (c *\<^sub>R i)))"
      unfolding scaleR_right_distrib by auto
    also have "\<dots> = norm ((1 / \<bar>c\<bar>) *\<^sub>R (c *\<^sub>R (- (f' i) + f'' i)))"
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
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"
    and "x \<in> cbox a b"
    and "(f has_derivative f' ) (at x within cbox a b)"
    and "(f has_derivative f'') (at x within cbox a b)"
  shows "f' = f''"
  apply(rule frechet_derivative_unique_within)
  apply(rule assms(3,4))+
proof (rule, rule, rule)
  fix e :: real
  fix i :: 'a
  assume "e > 0" and i: "i \<in> Basis"
  then show "\<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> x + d *\<^sub>R i \<in> cbox a b"
  proof (cases "x\<bullet>i = a\<bullet>i")
    case True
    then show ?thesis
      apply (rule_tac x="(min (b\<bullet>i - a\<bullet>i)  e) / 2" in exI)
      using assms(1)[THEN bspec[where x=i]] and \<open>e>0\<close> and assms(2)
      unfolding mem_box
      using i
      apply (auto simp add: field_simps inner_simps inner_Basis)
      done
  next
    note * = assms(2)[unfolded mem_box, THEN bspec, OF i]
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
      using * and \<open>e>0\<close> by auto
    then have "x \<bullet> i * 2 \<le> b \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e"
      using * by auto
    ultimately show ?thesis
      apply (rule_tac x="- (min (x\<bullet>i - a\<bullet>i) e) / 2" in exI)
      using assms(1)[THEN bspec, OF i] and \<open>e>0\<close> and assms(2)
      unfolding mem_box
      using i
      apply (auto simp add: field_simps inner_simps inner_Basis)
      done
  qed
qed

lemma frechet_derivative_unique_within_open_interval:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "x \<in> box a b"
    and "(f has_derivative f' ) (at x within box a b)"
    and "(f has_derivative f'') (at x within box a b)"
  shows "f' = f''"
proof -
  from assms(1) have *: "at x within box a b = at x"
    by (metis at_within_interior interior_open open_box)
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

lemma frechet_derivative_within_cbox:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"
    and "x \<in> cbox a b"
    and "(f has_derivative f') (at x within cbox a b)"
  shows "frechet_derivative f (at x within cbox a b) = f'"
  using assms
  by (metis Derivative.differentiableI frechet_derivative_unique_within_closed_interval frechet_derivative_works)


subsection \<open>The traditional Rolle theorem in one dimension\<close>

text \<open>Derivatives of local minima and maxima are zero.\<close>

lemma has_derivative_local_min:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes deriv: "(f has_derivative f') (at x)"
  assumes min: "eventually (\<lambda>y. f x \<le> f y) (at x)"
  shows "f' = (\<lambda>h. 0)"
proof
  fix h :: 'a
  interpret f': bounded_linear f'
    using deriv by (rule has_derivative_bounded_linear)
  show "f' h = 0"
  proof (cases "h = 0")
    assume "h \<noteq> 0"
    from min obtain d where d1: "0 < d" and d2: "\<forall>y\<in>ball x d. f x \<le> f y"
      unfolding eventually_at by (force simp: dist_commute)
    have "FDERIV (\<lambda>r. x + r *\<^sub>R h) 0 :> (\<lambda>r. r *\<^sub>R h)"
      by (intro derivative_eq_intros) auto
    then have "FDERIV (\<lambda>r. f (x + r *\<^sub>R h)) 0 :> (\<lambda>k. f' (k *\<^sub>R h))"
      by (rule has_derivative_compose, simp add: deriv)
    then have "DERIV (\<lambda>r. f (x + r *\<^sub>R h)) 0 :> f' h"
      unfolding has_field_derivative_def by (simp add: f'.scaleR mult_commute_abs)
    moreover have "0 < d / norm h" using d1 and \<open>h \<noteq> 0\<close> by simp
    moreover have "\<forall>y. \<bar>0 - y\<bar> < d / norm h \<longrightarrow> f (x + 0 *\<^sub>R h) \<le> f (x + y *\<^sub>R h)"
      using \<open>h \<noteq> 0\<close> by (auto simp add: d2 dist_norm pos_less_divide_eq)
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
  with \<open>x \<in> s\<close> and \<open>open s\<close> have "eventually (\<lambda>y. f y \<le> f x) (at x)"
    unfolding eventually_at_topological by auto
  with deriv show ?thesis
    by (rule has_derivative_local_max)
next
  assume "\<forall>y\<in>s. f x \<le> f y"
  with \<open>x \<in> s\<close> and \<open>open s\<close> have "eventually (\<lambda>y. f x \<le> f y) (at x)"
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
  have "x \<in> ball x e" using \<open>0 < e\<close> by simp
  moreover have "open (ball x e)" by simp
  moreover have "((\<lambda>x. f x \<bullet> k) has_derivative (\<lambda>h. ?f' h \<bullet> k)) (at x)"
    using bounded_linear_inner_left diff[unfolded frechet_derivative_works]
    by (rule bounded_linear.has_derivative)
  ultimately have "(\<lambda>h. frechet_derivative f (at x) h \<bullet> k) = (\<lambda>v. 0)"
    using ball(2) by (rule differential_zero_maxmin)
  then show ?thesis
    unfolding fun_eq_iff by simp
qed

lemma rolle:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "f a = f b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a <..< b}. (f has_derivative f' x) (at x)"
  shows "\<exists>x\<in>{a <..< b}. f' x = (\<lambda>v. 0)"
proof -
  have "\<exists>x\<in>box a b. (\<forall>y\<in>box a b. f x \<le> f y) \<or> (\<forall>y\<in>box a b. f y \<le> f x)"
  proof -
    have "(a + b) / 2 \<in> {a .. b}"
      using assms(1) by auto
    then have *: "{a .. b} \<noteq> {}"
      by auto
    obtain d where d:
        "d \<in>cbox a b"
        "\<forall>y\<in>cbox a b. f y \<le> f d"
      using continuous_attains_sup[OF compact_Icc * assms(3)] by auto
    obtain c where c:
        "c \<in> cbox a b"
        "\<forall>y\<in>cbox a b. f c \<le> f y"
      using continuous_attains_inf[OF compact_Icc * assms(3)] by auto
    show ?thesis
    proof (cases "d \<in> box a b \<or> c \<in> box a b")
      case True
      then show ?thesis
        by (metis c(2) d(2) box_subset_cbox subset_iff)
    next
      define e where "e = (a + b) /2"
      case False
      then have "f d = f c"
        using d c assms(2) by auto
      then have "\<And>x. x \<in> {a..b} \<Longrightarrow> f x = f d"
        using c d
        by force
      then show ?thesis
        apply (rule_tac x=e in bexI)
        unfolding e_def
        using assms(1)
        apply auto
        done
    qed
  qed
  then obtain x where x: "x \<in> {a <..< b}" "(\<forall>y\<in>{a <..< b}. f x \<le> f y) \<or> (\<forall>y\<in>{a <..< b}. f y \<le> f x)"
    by auto
  then have "f' x = (\<lambda>v. 0)"
    apply (rule_tac differential_zero_maxmin[of x "box a b" f "f' x"])
    using assms
    apply auto
    done
  then show ?thesis
    by (metis x(1))
qed


subsection \<open>One-dimensional mean value theorem\<close>

lemma mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "continuous_on {a..b} f"
  assumes "\<forall>x\<in>{a<..<b}. (f has_derivative (f' x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. f b - f a = (f' x) (b - a)"
proof -
  have "\<exists>x\<in>{a <..< b}. (\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa) = (\<lambda>v. 0)"
  proof (intro rolle[OF assms(1), of "\<lambda>x. f x - (f b - f a) / (b - a) * x"] ballI)
    fix x
    assume x: "x \<in> {a <..< b}"
    show "((\<lambda>x. f x - (f b - f a) / (b - a) * x) has_derivative
        (\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa)) (at x)"
      by (intro derivative_intros assms(3)[rule_format,OF x])
  qed (insert assms(1,2), auto intro!: continuous_intros simp: field_simps)
  then obtain x where
    "x \<in> {a <..< b}"
    "(\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa) = (\<lambda>v. 0)" ..
  then show ?thesis
    by (metis (hide_lams) assms(1) diff_gt_0_iff_gt eq_iff_diff_eq_0
      zero_less_mult_iff nonzero_mult_div_cancel_right not_real_square_gt_zero
      times_divide_eq_left)
qed

lemma mvt_simple:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "\<forall>x\<in>{a..b}. (f has_derivative f' x) (at x within {a..b})"
  shows "\<exists>x\<in>{a<..<b}. f b - f a = f' x (b - a)"
proof (rule mvt)
  have "f differentiable_on {a..b}"
    using assms(2) unfolding differentiable_on_def differentiable_def by fast
  then show "continuous_on {a..b} f"
    by (rule differentiable_imp_continuous_on)
  show "\<forall>x\<in>{a<..<b}. (f has_derivative f' x) (at x)"
  proof
    fix x
    assume x: "x \<in> {a <..< b}"
    show "(f has_derivative f' x) (at x)"
      unfolding at_within_open[OF x open_greaterThanLessThan,symmetric]
      apply (rule has_derivative_within_subset)
      apply (rule assms(2)[rule_format])
      using x
      apply auto
      done
  qed
qed (rule assms(1))

lemma mvt_very_simple:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<forall>x\<in>{a .. b}. (f has_derivative f' x) (at x within {a .. b})"
  shows "\<exists>x\<in>{a .. b}. f b - f a = f' x (b - a)"
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

text \<open>A nice generalization (see Havin's proof of 5.19 from Rudin's book).\<close>

lemma mvt_general:
  fixes f :: "real \<Rightarrow> 'a::real_inner"
  assumes "a < b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a<..<b}. (f has_derivative f'(x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. norm (f b - f a) \<le> norm (f' x (b - a))"
proof -
  have "\<exists>x\<in>{a<..<b}. (f b - f a) \<bullet> f b - (f b - f a) \<bullet> f a = (f b - f a) \<bullet> f' x (b - a)"
    apply (rule mvt)
    apply (rule assms(1))
    apply (intro continuous_intros assms(2))
    using assms(3)
    apply (fast intro: has_derivative_inner_right)
    done
  then obtain x where x:
    "x \<in> {a<..<b}"
    "(f b - f a) \<bullet> f b - (f b - f a) \<bullet> f a = (f b - f a) \<bullet> f' x (b - a)" ..
  show ?thesis
  proof (cases "f a = f b")
    case False
    have "norm (f b - f a) * norm (f b - f a) = (norm (f b - f a))\<^sup>2"
      by (simp add: power2_eq_square)
    also have "\<dots> = (f b - f a) \<bullet> (f b - f a)"
      unfolding power2_norm_eq_inner ..
    also have "\<dots> = (f b - f a) \<bullet> f' x (b - a)"
      using x(2) by (simp only: inner_diff_right)
    also have "\<dots> \<le> norm (f b - f a) * norm (f' x (b - a))"
      by (rule norm_cauchy_schwarz)
    finally show ?thesis
      using False x(1)
      by (auto simp add: mult_left_cancel)
  next
    case True
    then show ?thesis
      using assms(1)
      apply (rule_tac x="(a + b) /2" in bexI)
      apply auto
      done
  qed
qed


subsection \<open>More general bound theorems\<close>

lemma differentiable_bound_general:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a < b"
    and f_cont: "continuous_on {a .. b} f"
    and phi_cont: "continuous_on {a .. b} \<phi>"
    and f': "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
    and phi': "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (\<phi> has_vector_derivative \<phi>' x) (at x)"
    and bnd: "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> norm (f' x) \<le> \<phi>' x"
  shows "norm (f b - f a) \<le> \<phi> b - \<phi> a"
proof -
  {
    fix x assume x: "a < x" "x < b"
    have "0 \<le> norm (f' x)" by simp
    also have "\<dots> \<le> \<phi>' x" using x by (auto intro!: bnd)
    finally have "0 \<le> \<phi>' x" .
  } note phi'_nonneg = this
  note f_tendsto = assms(2)[simplified continuous_on_def, rule_format]
  note phi_tendsto = assms(3)[simplified continuous_on_def, rule_format]
  {
    fix e::real assume "e > 0"
    define e2 where "e2 = e / 2"
    with \<open>e > 0\<close> have "e2 > 0" by simp
    let ?le = "\<lambda>x1. norm (f x1 - f a) \<le> \<phi> x1 - \<phi> a + e * (x1 - a) + e"
    define A where "A = {x2. a \<le> x2 \<and> x2 \<le> b \<and> (\<forall>x1\<in>{a ..< x2}. ?le x1)}"
    have A_subset: "A \<subseteq> {a .. b}" by (auto simp: A_def)
    {
      fix x2
      assume a: "a \<le> x2" "x2 \<le> b" and le: "\<forall>x1\<in>{a..<x2}. ?le x1"
      have "?le x2" using \<open>e > 0\<close>
      proof cases
        assume "x2 \<noteq> a" with a have "a < x2" by simp
        have "at x2 within {a <..<x2}\<noteq> bot"
          using \<open>a < x2\<close>
          by (auto simp: trivial_limit_within islimpt_in_closure)
        moreover
        have "((\<lambda>x1. (\<phi> x1 - \<phi> a) + e * (x1 - a) + e) \<longlongrightarrow> (\<phi> x2 - \<phi> a) + e * (x2 - a) + e) (at x2 within {a <..<x2})"
          "((\<lambda>x1. norm (f x1 - f a)) \<longlongrightarrow> norm (f x2 - f a)) (at x2 within {a <..<x2})"
          using a
          by (auto intro!: tendsto_eq_intros f_tendsto phi_tendsto
            intro: tendsto_within_subset[where S="{a .. b}"])
        moreover
        have "eventually (\<lambda>x. x > a) (at x2 within {a <..<x2})"
          by (auto simp: eventually_at_filter)
        hence "eventually ?le (at x2 within {a <..<x2})"
          unfolding eventually_at_filter
          by eventually_elim (insert le, auto)
        ultimately
        show ?thesis
          by (rule tendsto_le)
      qed simp
    } note le_cont = this
    have "a \<in> A"
      using assms by (auto simp: A_def)
    hence [simp]: "A \<noteq> {}" by auto
    have A_ivl: "\<And>x1 x2. x2 \<in> A \<Longrightarrow> x1 \<in> {a ..x2} \<Longrightarrow> x1 \<in> A"
      by (simp add: A_def)
    have [simp]: "bdd_above A" by (auto simp: A_def)
    define y where "y = Sup A"
    have "y \<le> b"
      unfolding y_def
      by (simp add: cSup_le_iff) (simp add: A_def)
     have leI: "\<And>x x1. a \<le> x1 \<Longrightarrow> x \<in> A \<Longrightarrow> x1 < x \<Longrightarrow> ?le x1"
       by (auto simp: A_def intro!: le_cont)
    have y_all_le: "\<forall>x1\<in>{a..<y}. ?le x1"
      by (auto simp: y_def less_cSup_iff leI)
    have "a \<le> y"
      by (metis \<open>a \<in> A\<close> \<open>bdd_above A\<close> cSup_upper y_def)
    have "y \<in> A"
      using y_all_le \<open>a \<le> y\<close> \<open>y \<le> b\<close>
      by (auto simp: A_def)
    hence "A = {a .. y}"
      using A_subset
      by (auto simp: subset_iff y_def cSup_upper intro: A_ivl)
    from le_cont[OF \<open>a \<le> y\<close> \<open>y \<le> b\<close> y_all_le] have le_y: "?le y" .
    {
      assume "a \<noteq> y" with \<open>a \<le> y\<close> have "a < y" by simp
      have "y = b"
      proof (rule ccontr)
        assume "y \<noteq> b"
        hence "y < b" using \<open>y \<le> b\<close> by simp
        let ?F = "at y within {y..<b}"
        from f' phi'
        have "(f has_vector_derivative f' y) ?F"
          and "(\<phi> has_vector_derivative \<phi>' y) ?F"
          using \<open>a < y\<close> \<open>y < b\<close>
          by (auto simp add: at_within_open[of _ "{a<..<b}"] has_vector_derivative_def
            intro!: has_derivative_subset[where s="{a<..<b}" and t="{y..<b}"])
        hence "\<forall>\<^sub>F x1 in ?F. norm (f x1 - f y - (x1 - y) *\<^sub>R f' y) \<le> e2 * \<bar>x1 - y\<bar>"
            "\<forall>\<^sub>F x1 in ?F. norm (\<phi> x1 - \<phi> y - (x1 - y) *\<^sub>R \<phi>' y) \<le> e2 * \<bar>x1 - y\<bar>"
          using \<open>e2 > 0\<close>
          by (auto simp: has_derivative_within_alt2 has_vector_derivative_def)
        moreover
        have "\<forall>\<^sub>F x1 in ?F. y \<le> x1" "\<forall>\<^sub>F x1 in ?F. x1 < b"
          by (auto simp: eventually_at_filter)
        ultimately
        have "\<forall>\<^sub>F x1 in ?F. norm (f x1 - f y) \<le> (\<phi> x1 - \<phi> y) + e * \<bar>x1 - y\<bar>"
          (is "\<forall>\<^sub>F x1 in ?F. ?le' x1")
        proof eventually_elim
          case (elim x1)
          from norm_triangle_ineq2[THEN order_trans, OF elim(1)]
          have "norm (f x1 - f y) \<le> norm (f' y) * \<bar>x1 - y\<bar> + e2 * \<bar>x1 - y\<bar>"
            by (simp add: ac_simps)
          also have "norm (f' y) \<le> \<phi>' y" using bnd \<open>a < y\<close> \<open>y < b\<close> by simp
          also
          from elim have "\<phi>' y * \<bar>x1 - y\<bar> \<le> \<phi> x1 - \<phi> y + e2 * \<bar>x1 - y\<bar>"
            by (simp add: ac_simps)
          finally
          have "norm (f x1 - f y) \<le> \<phi> x1 - \<phi> y + e2 * \<bar>x1 - y\<bar> + e2 * \<bar>x1 - y\<bar>"
            by (auto simp: mult_right_mono)
          thus ?case by (simp add: e2_def)
        qed
        moreover have "?le' y" by simp
        ultimately obtain S
        where S: "open S" "y \<in> S" "\<And>x. x\<in>S \<Longrightarrow> x \<in> {y..<b} \<Longrightarrow> ?le' x"
          unfolding eventually_at_topological
          by metis
        from \<open>open S\<close> obtain d where d: "\<And>x. dist x y < d \<Longrightarrow> x \<in> S" "d > 0"
          by (force simp: dist_commute open_dist ball_def dest!: bspec[OF _ \<open>y \<in> S\<close>])
        define d' where "d' = min ((y + b)/2) (y + (d/2))"
        have "d' \<in> A"
          unfolding A_def
        proof safe
          show "a \<le> d'" using \<open>a < y\<close> \<open>0 < d\<close> \<open>y < b\<close> by (simp add: d'_def)
          show "d' \<le> b" using \<open>y < b\<close> by (simp add: d'_def min_def)
          fix x1
          assume x1: "x1 \<in> {a..<d'}"
          {
            assume "x1 < y"
            hence "?le x1"
              using \<open>x1 \<in> {a..<d'}\<close> y_all_le by auto
          } moreover {
            assume "x1 \<ge> y"
            hence x1': "x1 \<in> S" "x1 \<in> {y..<b}" using x1
              by (auto simp: d'_def dist_real_def intro!: d)
            have "norm (f x1 - f a) \<le> norm (f x1 - f y) + norm (f y - f a)"
              by (rule order_trans[OF _ norm_triangle_ineq]) simp
            also note S(3)[OF x1']
            also note le_y
            finally have "?le x1"
              using \<open>x1 \<ge> y\<close> by (auto simp: algebra_simps)
          } ultimately show "?le x1" by arith
        qed
        hence "d' \<le> y"
          unfolding y_def
          by (rule cSup_upper) simp
        thus False using \<open>d > 0\<close> \<open>y < b\<close>
          by (simp add: d'_def min_def split: if_split_asm)
      qed
    } moreover {
      assume "a = y"
      with \<open>a < b\<close> have "y < b" by simp
      with \<open>a = y\<close> f_cont phi_cont \<open>e2 > 0\<close>
      have 1: "\<forall>\<^sub>F x in at y within {y..b}. dist (f x) (f y) < e2"
       and 2: "\<forall>\<^sub>F x in at y within {y..b}. dist (\<phi> x) (\<phi> y) < e2"
        by (auto simp: continuous_on_def tendsto_iff)
      have 3: "eventually (\<lambda>x. y < x) (at y within {y..b})"
        by (auto simp: eventually_at_filter)
      have 4: "eventually (\<lambda>x::real. x < b) (at y within {y..b})"
        using _ \<open>y < b\<close>
        by (rule order_tendstoD) (auto intro!: tendsto_eq_intros)
      from 1 2 3 4
      have eventually_le: "eventually (\<lambda>x. ?le x) (at y within {y .. b})"
      proof eventually_elim
        case (elim x1)
        have "norm (f x1 - f a) = norm (f x1 - f y)"
          by (simp add: \<open>a = y\<close>)
        also have "norm (f x1 - f y) \<le> e2"
          using elim \<open>a = y\<close> by (auto simp : dist_norm intro!:  less_imp_le)
        also have "\<dots> \<le> e2 + (\<phi> x1 - \<phi> a + e2 + e * (x1 - a))"
          using \<open>0 < e\<close> elim
          by (intro add_increasing2[OF add_nonneg_nonneg order.refl])
            (auto simp: \<open>a = y\<close> dist_norm intro!: mult_nonneg_nonneg)
        also have "\<dots> = \<phi> x1 - \<phi> a + e * (x1 - a) + e"
          by (simp add: e2_def)
        finally show "?le x1" .
      qed
      from this[unfolded eventually_at_topological] \<open>?le y\<close>
      obtain S
      where S: "open S" "y \<in> S" "\<And>x. x\<in>S \<Longrightarrow> x \<in> {y..b} \<Longrightarrow> ?le x"
        by metis
      from \<open>open S\<close> obtain d where d: "\<And>x. dist x y < d \<Longrightarrow> x \<in> S" "d > 0"
        by (force simp: dist_commute open_dist ball_def dest!: bspec[OF _ \<open>y \<in> S\<close>])
      define d' where "d' = min b (y + (d/2))"
      have "d' \<in> A"
        unfolding A_def
      proof safe
        show "a \<le> d'" using \<open>a = y\<close> \<open>0 < d\<close> \<open>y < b\<close> by (simp add: d'_def)
        show "d' \<le> b" by (simp add: d'_def)
        fix x1
        assume "x1 \<in> {a..<d'}"
        hence "x1 \<in> S" "x1 \<in> {y..b}"
          by (auto simp: \<open>a = y\<close> d'_def dist_real_def intro!: d )
        thus "?le x1"
          by (rule S)
      qed
      hence "d' \<le> y"
        unfolding y_def
        by (rule cSup_upper) simp
      hence "y = b" using \<open>d > 0\<close> \<open>y < b\<close>
        by (simp add: d'_def)
    } ultimately have "y = b"
      by auto
    with le_y have "norm (f b - f a) \<le> \<phi> b - \<phi> a + e * (b - a + 1)"
      by (simp add: algebra_simps)
  } note * = this
  {
    fix e::real assume "e > 0"
    hence "norm (f b - f a) \<le> \<phi> b - \<phi> a + e"
      using *[of "e / (b - a + 1)"] \<open>a < b\<close> by simp
  } thus ?thesis
    by (rule field_le_epsilon)
qed

lemma differentiable_bound:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<forall>x\<in>s. (f has_derivative f' x) (at x within s)"
    and "\<forall>x\<in>s. onorm (f' x) \<le> B"
    and x: "x \<in> s"
    and y: "y \<in> s"
  shows "norm (f x - f y) \<le> B * norm (x - y)"
proof -
  let ?p = "\<lambda>u. x + u *\<^sub>R (y - x)"
  let ?\<phi> = "\<lambda>h. h * B * norm (x - y)"
  have *: "\<And>u. u\<in>{0..1} \<Longrightarrow> x + u *\<^sub>R (y - x) \<in> s"
    using assms(1)[unfolded convex_alt,rule_format,OF x y]
    unfolding scaleR_left_diff_distrib scaleR_right_diff_distrib
    by (auto simp add: algebra_simps)
  have 0: "continuous_on (?p ` {0..1}) f"
    using *
    unfolding continuous_on_eq_continuous_within
    apply -
    apply rule
    apply (rule differentiable_imp_continuous_within)
    unfolding differentiable_def
    apply (rule_tac x="f' xa" in exI)
    apply (rule has_derivative_within_subset)
    apply (rule assms(2)[rule_format])
    apply auto
    done
  from * have 1: "continuous_on {0 .. 1} (f \<circ> ?p)"
    by (intro continuous_intros 0)+
  {
    fix u::real assume u: "u \<in>{0 <..< 1}"
    let ?u = "?p u"
    interpret linear "(f' ?u)"
      using u by (auto intro!: has_derivative_linear assms(2)[rule_format] *)
    have "(f \<circ> ?p has_derivative (f' ?u) \<circ> (\<lambda>u. 0 + u *\<^sub>R (y - x))) (at u within box 0 1)"
      apply (rule diff_chain_within)
      apply (rule derivative_intros)+
      apply (rule has_derivative_within_subset)
      apply (rule assms(2)[rule_format])
      using u *
      apply auto
      done
    hence "((f \<circ> ?p) has_vector_derivative f' ?u (y - x)) (at u)"
      by (simp add: has_derivative_within_open[OF u open_greaterThanLessThan]
        scaleR has_vector_derivative_def o_def)
  } note 2 = this
  {
    have "continuous_on {0..1} ?\<phi>"
      by (rule continuous_intros)+
  } note 3 = this
  {
    fix u::real assume u: "u \<in>{0 <..< 1}"
    have "(?\<phi> has_vector_derivative B * norm (x - y)) (at u)"
      by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros)
  } note 4 = this
  {
    fix u::real assume u: "u \<in>{0 <..< 1}"
    let ?u = "?p u"
    interpret bounded_linear "(f' ?u)"
      using u by (auto intro!: has_derivative_bounded_linear assms(2)[rule_format] *)
    have "norm (f' ?u (y - x)) \<le> onorm (f' ?u) * norm (y - x)"
      by (rule onorm) (rule bounded_linear)
    also have "onorm (f' ?u) \<le> B"
      using u by (auto intro!: assms(3)[rule_format] *)
    finally have "norm ((f' ?u) (y - x)) \<le> B * norm (x - y)"
      by (simp add: mult_right_mono norm_minus_commute)
  } note 5 = this
  have "norm (f x - f y) = norm ((f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 1 - (f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 0)"
    by (auto simp add: norm_minus_commute)
  also
  from differentiable_bound_general[OF zero_less_one 1, OF 3 2 4 5]
  have "norm ((f \<circ> ?p) 1 - (f \<circ> ?p) 0) \<le> B * norm (x - y)"
    by simp
  finally show ?thesis .
qed

lemma
  differentiable_bound_segment:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>t. t \<in> {0..1} \<Longrightarrow> x0 + t *\<^sub>R a \<in> G"
  assumes f': "\<And>x. x \<in> G \<Longrightarrow> (f has_derivative f' x) (at x within G)"
  assumes B: "\<forall>x\<in>{0..1}. onorm (f' (x0 + x *\<^sub>R a)) \<le> B"
  shows "norm (f (x0 + a) - f x0) \<le> norm a * B"
proof -
  let ?G = "(\<lambda>x. x0 + x *\<^sub>R a) ` {0..1}"
  have "?G = (+) x0 ` (\<lambda>x. x *\<^sub>R a) ` {0..1}" by auto
  also have "convex \<dots>"
    by (intro convex_translation convex_scaled convex_real_interval)
  finally have "convex ?G" .
  moreover have "?G \<subseteq> G" "x0 \<in> ?G" "x0 + a \<in> ?G" using assms by (auto intro: image_eqI[where x=1])
  ultimately show ?thesis
    using has_derivative_subset[OF f' \<open>?G \<subseteq> G\<close>] B
      differentiable_bound[of "(\<lambda>x. x0 + x *\<^sub>R a) ` {0..1}" f f' B "x0 + a" x0]
    by (auto simp: ac_simps)
qed

lemma differentiable_bound_linearization:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>t. t \<in> {0..1} \<Longrightarrow> a + t *\<^sub>R (b - a) \<in> S"
  assumes f'[derivative_intros]: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes B: "\<forall>x\<in>S. onorm (f' x - f' x0) \<le> B"
  assumes "x0 \<in> S"
  shows "norm (f b - f a - f' x0 (b - a)) \<le> norm (b - a) * B"
proof -
  define g where [abs_def]: "g x = f x - f' x0 x" for x
  have g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative (\<lambda>i. f' x i - f' x0 i)) (at x within S)"
    unfolding g_def using assms
    by (auto intro!: derivative_eq_intros
      bounded_linear.has_derivative[OF has_derivative_bounded_linear, OF f'])
  from B have B: "\<forall>x\<in>{0..1}. onorm (\<lambda>i. f' (a + x *\<^sub>R (b - a)) i - f' x0 i) \<le> B"
     using assms by (auto simp: fun_diff_def)
  from differentiable_bound_segment[OF assms(1) g B] \<open>x0 \<in> S\<close>
  show ?thesis
    by (simp add: g_def field_simps linear_diff[OF has_derivative_linear[OF f']])
qed

lemma vector_differentiable_bound_linearization:
  fixes f::"real \<Rightarrow> 'b::real_normed_vector"
  assumes f': "\<And>x. x \<in> S \<Longrightarrow> (f has_vector_derivative f' x) (at x within S)"
  assumes "closed_segment a b \<subseteq> S"
  assumes B: "\<forall>x\<in>S. norm (f' x - f' x0) \<le> B"
  assumes "x0 \<in> S"
  shows "norm (f b - f a - (b - a) *\<^sub>R f' x0) \<le> norm (b - a) * B"
  using assms
  by (intro differentiable_bound_linearization[of a b S f "\<lambda>x h. h *\<^sub>R f' x" x0 B])
    (force simp: closed_segment_real_eq has_vector_derivative_def
      scaleR_diff_right[symmetric] mult.commute[of B]
      intro!: onorm_le mult_left_mono)+


text \<open>In particular.\<close>

lemma has_derivative_zero_constant:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within s)"
  shows "\<exists>c. \<forall>x\<in>s. f x = c"
proof -
  { fix x y assume "x \<in> s" "y \<in> s"
    then have "norm (f x - f y) \<le> 0 * norm (x - y)"
      using assms by (intro differentiable_bound[of s]) (auto simp: onorm_zero)
    then have "f x = f y"
      by simp }
  then show ?thesis
    by metis
qed

lemma has_field_derivative_zero_constant:
  assumes "convex s" "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative 0) (at x within s)"
  shows   "\<exists>c. \<forall>x\<in>s. f (x) = (c :: 'a :: real_normed_field)"
proof (rule has_derivative_zero_constant)
  have A: "( * ) 0 = (\<lambda>_. 0 :: 'a)" by (intro ext) simp
  fix x assume "x \<in> s" thus "(f has_derivative (\<lambda>h. 0)) (at x within s)"
    using assms(2)[of x] by (simp add: has_field_derivative_def A)
qed fact

lemma
  has_vector_derivative_zero_constant:
  assumes "convex s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative 0) (at x within s)"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_derivative_zero_constant[of s f] assms
  by (auto simp: has_vector_derivative_def)

lemma has_derivative_zero_unique:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x \<in> s" "y \<in> s"
  shows "f x = f y"
  using has_derivative_zero_constant[OF assms(1,2)] assms(3-) by force

lemma has_derivative_zero_unique_connected:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "open s" "connected s"
  assumes f: "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative (\<lambda>x. 0)) (at x)"
  assumes "x \<in> s" "y \<in> s"
  shows "f x = f y"
proof (rule connected_local_const[where f=f, OF \<open>connected s\<close> \<open>x\<in>s\<close> \<open>y\<in>s\<close>])
  show "\<forall>a\<in>s. eventually (\<lambda>b. f a = f b) (at a within s)"
  proof
    fix a assume "a \<in> s"
    with \<open>open s\<close> obtain e where "0 < e" "ball a e \<subseteq> s"
      by (rule openE)
    then have "\<exists>c. \<forall>x\<in>ball a e. f x = c"
      by (intro has_derivative_zero_constant)
         (auto simp: at_within_open[OF _ open_ball] f convex_ball)
    with \<open>0<e\<close> have "\<forall>x\<in>ball a e. f a = f x"
      by auto
    then show "eventually (\<lambda>b. f a = f b) (at a within s)"
      using \<open>0<e\<close> unfolding eventually_at_topological
      by (intro exI[of _ "ball a e"]) auto
  qed
qed

subsection \<open>Differentiability of inverse function (most basic form)\<close>

lemma has_derivative_inverse_basic:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
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
    fix e :: real
    assume "e > 0"
    with C(1) have *: "e / C > 0" by auto
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
    then show "\<exists>d>0. \<forall>z. norm (z - y) < d \<longrightarrow> norm (g z - g y - g' (z - y)) \<le> e * norm (g z - g y)"
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
        unfolding assms(7)[rule_format,OF \<open>z\<in>t\<close>]
        apply (subst norm_minus_cancel[symmetric])
        apply auto
        done
      also have "\<dots> \<le> norm (f (g z) - y - f' (g z - g y)) * C"
        by (rule C(2))
      also have "\<dots> \<le> (e / C) * norm (g z - g y) * C"
        apply (rule mult_right_mono)
        apply (rule d0(2)[rule_format,unfolded assms(7)[rule_format,OF \<open>y\<in>t\<close>]])
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
  define B where "B = C * 2"
  have "B > 0"
    unfolding B_def using C by auto
  have lem2: "norm (g z - g y) \<le> B * norm (z - y)" if z: "norm(z - y) < d" for z
  proof -
    have "norm (g z - g y) \<le> norm(g' (z - y)) + norm ((g z - g y) - g'(z - y))"
      by (rule norm_triangle_sub)
    also have "\<dots> \<le> norm (g' (z - y)) + 1 / 2 * norm (g z - g y)"
      apply (rule add_left_mono)
      using d and z
      apply auto
      done
    also have "\<dots> \<le> norm (z - y) * C + 1 / 2 * norm (g z - g y)"
      apply (rule add_right_mono)
      using C
      apply auto
      done
    finally show "norm (g z - g y) \<le> B * norm (z - y)"
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
    fix e :: real
    assume "e > 0"
    then have *: "e / B > 0" by (metis \<open>B > 0\<close> divide_pos_pos)
    obtain d' where d':
        "0 < d'"
        "\<forall>z. norm (z - y) < d' \<longrightarrow> norm (g z - g y - g' (z - y)) \<le> e / B * norm (g z - g y)"
      using lem1 * by blast
    obtain k where k: "0 < k" "k < d" "k < d'"
      using real_lbound_gt_zero[OF d(1) d'(1)] by blast
    show "\<exists>d>0. \<forall>ya. norm (ya - y) < d \<longrightarrow> norm (g ya - g y - g' (ya - y)) \<le> e * norm (ya - y)"
      apply (rule_tac x=k in exI)
      apply auto
    proof -
      fix z
      assume as: "norm (z - y) < k"
      then have "norm (g z - g y - g' (z - y)) \<le> e / B * norm(g z - g y)"
        using d' k by auto
      also have "\<dots> \<le> e * norm (z - y)"
        unfolding times_divide_eq_left pos_divide_le_eq[OF \<open>B>0\<close>]
        using lem2[of z]
        using k as using \<open>e > 0\<close>
        by (auto simp add: field_simps)
      finally show "norm (g z - g y - g' (z - y)) \<le> e * norm (z - y)"
        by simp
    qed(insert k, auto)
  qed
qed

text \<open>Simply rewrite that based on the domain point x.\<close>

lemma has_derivative_inverse_basic_x:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
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

text \<open>This is the version in Dieudonne', assuming continuity of f and g.\<close>

lemma has_derivative_inverse_dieudonne:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
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

text \<open>Here's the simplest way of not assuming much about g.\<close>

lemma has_derivative_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
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
      unfolding * and assms(5)[rule_format,OF \<open>x\<in>s\<close>] ..
  } note * = this
  show ?thesis
    apply (rule has_derivative_inverse_basic_x[OF assms(6-8)])
    apply (rule continuous_on_interior[OF _ assms(3)])
    apply (rule continuous_on_inv[OF assms(4,1)])
    apply (rule assms(2,5) assms(5)[rule_format] open_interior assms(3))+
    apply (metis *)
    done
qed


subsection \<open>Proving surjectivity via Brouwer fixpoint theorem\<close>

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
    apply (rule continuous_intros assms)+
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

text \<open>See Sussmann: "Multidifferential calculus", Theorem 2.1.1\<close>

lemma sussmann_open_mapping:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
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
  hence *: "1 / (2 * B) > 0" by auto
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
  have *: "0 < e0 / B" "0 < e1 / B" using e0 e1 B by auto
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
      apply (rule continuous_intros linear_continuous_on[OF assms(5)])+
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
      by (simp only: algebra_simps **) auto
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

text \<open>Hence the following eccentric variant of the inverse function theorem.
  This has no continuity assumptions, but we do need the inverse function.
  We could put \<open>f' \<circ> g = I\<close> but this happens to fit with the minimal linear
  algebra theory I've set up so far.\<close>

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
      using *[rule_format,of "ball x e \<inter> s"] \<open>x \<in> s\<close>
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
      fix y
      assume "0 < dist y (f x) \<and> dist y (f x) < d"
      then have "g y \<in> g ` f ` (ball x e \<inter> s)"
        using d(2)[unfolded subset_eq,THEN bspec[where x=y]]
        by (auto simp add: dist_commute)
      then have "g y \<in> ball x e \<inter> s"
        using assms(4) by auto
      then show "dist (g y) (g (f x)) < e"
        using assms(4)[rule_format,OF \<open>x \<in> s\<close>]
        by (auto simp add: dist_commute)
    qed
  qed
  moreover have "f x \<in> interior (f ` s)"
    apply (rule sussmann_open_mapping)
    apply (rule assms ling)+
    using interior_open[OF assms(1)] and \<open>x \<in> s\<close>
    apply auto
    done
  moreover have "f (g y) = y" if "y \<in> interior (f ` s)" for y
  proof -
    from that have "y \<in> f ` s"
      using interior_subset by auto
    then obtain z where "z \<in> s" "y = f z" unfolding image_iff ..
    then show ?thesis
      using assms(4) by auto
  qed
  ultimately show ?thesis using assms
    by (metis has_derivative_inverse_basic_x open_interior)
qed

text \<open>A rewrite based on the other domain.\<close>

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

text \<open>On a region.\<close>

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

text \<open>Invertible derivative continous at a point implies local
injectivity. It's only for this we need continuity of the derivative,
except of course if we want the fact that the inverse derivative is
also continuous. So if we know for some other reason that the inverse
function exists, it's OK.\<close>

proposition has_derivative_locally_injective:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "a \<in> s"
      and "open s"
      and "bounded_linear g'"
      and "g' \<circ> f' a = id"
      and "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x)"
      and "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x. dist a x < d \<longrightarrow> onorm (\<lambda>v. f' x v - f' a v) < e"
  obtains r where "r > 0" "ball a r \<subseteq> s" "inj_on f (ball a r)"
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
    unfolding onorm_pos_lt[OF assms(3)]
    by fastforce
  define k where "k = 1 / onorm g' / 2"
  have *: "k > 0"
    unfolding k_def using * by auto
  obtain d1 where d1:
      "0 < d1"
      "\<And>x. dist a x < d1 \<Longrightarrow> onorm (\<lambda>v. f' x v - f' a v) < k"
    using assms(6) * by blast
  from \<open>open s\<close> obtain d2 where "d2 > 0" "ball a d2 \<subseteq> s"
    using \<open>a\<in>s\<close> ..
  obtain d2 where "d2 > 0" "ball a d2 \<subseteq> s"
    using assms(2,1) ..
  obtain d2 where d2: "0 < d2" "ball a d2 \<subseteq> s"
    using assms(2)
    unfolding open_contains_ball
    using \<open>a\<in>s\<close> by blast
  obtain d where d: "0 < d" "d < d1" "d < d2"
    using real_lbound_gt_zero[OF d1(1) d2(1)] by blast
  show ?thesis
  proof
    show "0 < d" by (fact d)
    show "ball a d \<subseteq> s"
      using \<open>d < d2\<close> \<open>ball a d2 \<subseteq> s\<close> by auto
    show "inj_on f (ball a d)"
    unfolding inj_on_def
    proof (intro strip)
      fix x y
      assume as: "x \<in> ball a d" "y \<in> ball a d" "f x = f y"
      define ph where [abs_def]: "ph w = w - g' (f w - f x)" for w
      have ph':"ph = g' \<circ> (\<lambda>w. f' a w - (f w - f x))"
        unfolding ph_def o_def
        unfolding diff
        using f'g'
        by (auto simp: algebra_simps)
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
          apply (rule derivative_intros)
          defer
          apply (rule has_derivative_sub[where g'="\<lambda>x.0",unfolded diff_0_right])
          apply (rule has_derivative_at_withinI)
          using assms(5) and \<open>u \<in> s\<close> \<open>a \<in> s\<close>
          apply (auto intro!: derivative_intros bounded_linear.has_derivative[of _ "\<lambda>x. x"] has_derivative_bounded_linear)
          done
        have **: "bounded_linear (\<lambda>x. f' u x - f' a x)" "bounded_linear (\<lambda>x. f' a x - f' u x)"
          apply (rule_tac[!] bounded_linear_sub)
          apply (rule_tac[!] has_derivative_bounded_linear)
          using assms(5) \<open>u \<in> s\<close> \<open>a \<in> s\<close>
          apply auto
          done
        have "onorm (\<lambda>v. v - g' (f' u v)) \<le> onorm g' * onorm (\<lambda>w. f' a w - f' u w)"
          unfolding *
          apply (rule onorm_compose)
          apply (rule assms(3) **)+
          done
        also have "\<dots> \<le> onorm g' * k"
          apply (rule mult_left_mono)
          using d1(2)[of u]
          using onorm_neg[where f="\<lambda>x. f' u x - f' a x"]
          using d and u and onorm_pos_le[OF assms(3)]
          apply (auto simp: algebra_simps)
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
  qed
qed


subsection \<open>Uniformly convergent sequence of derivatives\<close>

lemma has_derivative_sequence_lipschitz_lemma:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
    and "0 \<le> e"
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
      by (rule derivative_intros assms(2)[rule_format] \<open>x\<in>s\<close>)+
    show "onorm (\<lambda>h. f' m x h - f' n x h) \<le> 2 * e"
    proof (rule onorm_bound)
      fix h
      have "norm (f' m x h - f' n x h) \<le> norm (f' m x h - g' x h) + norm (f' n x h - g' x h)"
        using norm_triangle_ineq[of "f' m x h - g' x h" "- f' n x h + g' x h"]
        unfolding norm_minus_commute
        by (auto simp add: algebra_simps)
      also have "\<dots> \<le> e * norm h + e * norm h"
        using assms(3)[rule_format,OF \<open>N \<le> m\<close> \<open>x \<in> s\<close>, of h]
        using assms(3)[rule_format,OF \<open>N \<le> n\<close> \<open>x \<in> s\<close>, of h]
        by (auto simp add: field_simps)
      finally show "norm (f' m x h - f' n x h) \<le> 2 * e * norm h"
        by auto
    qed (simp add: \<open>0 \<le> e\<close>)
  qed
qed

lemma has_derivative_sequence_lipschitz:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
  shows "\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s.
    norm ((f m x - f n x) - (f m y - f n y)) \<le> e * norm (x - y)"
proof (rule, rule)
  fix e :: real
  assume "e > 0"
  then have *: "2 * (1/2* e) = e" "1/2 * e >0"
    by auto
  obtain N where "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> 1 / 2 * e * norm h"
    using assms(3) *(2) by blast
  then show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm (f m x - f n x - (f m y - f n y)) \<le> e * norm (x - y)"
    apply (rule_tac x=N in exI)
    apply (rule has_derivative_sequence_lipschitz_lemma[where e="1/2 *e", unfolded *])
    using assms \<open>e > 0\<close>
    apply auto
    done
qed

lemma has_derivative_sequence:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::banach"
  assumes "convex s"
    and "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
    and "x0 \<in> s"
    and "((\<lambda>n. f n x0) \<longlongrightarrow> l) sequentially"
  shows "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially \<and> (g has_derivative g'(x)) (at x within s)"
proof -
  have lem1: "\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s.
      norm ((f m x - f n x) - (f m y - f n y)) \<le> e * norm (x - y)"
    using assms(1,2,3) by (rule has_derivative_sequence_lipschitz)
  have "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially"
    apply (rule bchoice)
    unfolding convergent_eq_Cauchy
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
        hence *: "e / 2 > 0" "e / 2 / norm (x - x0) > 0" using False by auto
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
            using N[rule_format,OF _ _ \<open>x\<in>s\<close> \<open>x0\<in>s\<close>, of m n] and as and False
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
  then obtain g where g: "\<forall>x\<in>s. (\<lambda>n. f n x) \<longlonglongrightarrow> g x" ..
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
      have "((\<lambda>m. norm (f n x - f n y - (f m x - f m y))) \<longlongrightarrow> norm (f n x - f n y - (g x - g y))) sequentially"
        by (intro tendsto_intros g[rule_format] as)
      moreover have "eventually (\<lambda>m. norm (f n x - f n y - (f m x - f m y)) \<le> e * norm (x - y)) sequentially"
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
      ultimately show "norm (f n x - f n y - (g x - g y)) \<le> e * norm (x - y)"
        by (simp add: tendsto_upperbound)
    qed
  qed
  have "\<forall>x\<in>s. ((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially \<and> (g has_derivative g' x) (at x within s)"
    unfolding has_derivative_within_alt2
  proof (intro ballI conjI)
    fix x
    assume "x \<in> s"
    then show "((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially"
      by (simp add: g)
    have lem3: "\<forall>u. ((\<lambda>n. f' n x u) \<longlongrightarrow> g' x u) sequentially"
      unfolding filterlim_def le_nhds_metric_le eventually_filtermap dist_norm
    proof (intro allI impI)
      fix u
      fix e :: real
      assume "e > 0"
      show "eventually (\<lambda>n. norm (f' n x u - g' x u) \<le> e) sequentially"
      proof (cases "u = 0")
        case True
        have "eventually (\<lambda>n. norm (f' n x u - g' x u) \<le> e * norm u) sequentially"
          using assms(3)[folded eventually_sequentially] and \<open>0 < e\<close> and \<open>x \<in> s\<close>
          by (fast elim: eventually_mono)
        then show ?thesis
          using \<open>u = 0\<close> and \<open>0 < e\<close> by (auto elim: eventually_mono)
      next
        case False
        with \<open>0 < e\<close> have "0 < e / norm u" by simp
        then have "eventually (\<lambda>n. norm (f' n x u - g' x u) \<le> e / norm u * norm u) sequentially"
          using assms(3)[folded eventually_sequentially] and \<open>x \<in> s\<close>
          by (fast elim: eventually_mono)
        then show ?thesis
          using \<open>u \<noteq> 0\<close> by simp
      qed
    qed
    show "bounded_linear (g' x)"
    proof
      fix x' y z :: 'a
      fix c :: real
      note lin = assms(2)[rule_format,OF \<open>x\<in>s\<close>,THEN has_derivative_bounded_linear]
      show "g' x (c *\<^sub>R x') = c *\<^sub>R g' x x'"
        apply (rule tendsto_unique[OF trivial_limit_sequentially])
        apply (rule lem3[rule_format])
        unfolding lin[THEN bounded_linear.linear, THEN linear_cmul]
        apply (intro tendsto_intros)
        apply (rule lem3[rule_format])
        done
      show "g' x (y + z) = g' x y + g' x z"
        apply (rule tendsto_unique[OF trivial_limit_sequentially])
        apply (rule lem3[rule_format])
        unfolding lin[THEN bounded_linear.linear, THEN linear_add]
        apply (rule tendsto_add)
        apply (rule lem3[rule_format])+
        done
      obtain N where N: "\<forall>h. norm (f' N x h - g' x h) \<le> 1 * norm h"
        using assms(3) \<open>x \<in> s\<close> by (fast intro: zero_less_one)
      have "bounded_linear (f' N x)"
        using assms(2) \<open>x \<in> s\<close> by fast
      from bounded_linear.bounded [OF this]
      obtain K where K: "\<forall>h. norm (f' N x h) \<le> norm h * K" ..
      {
        fix h
        have "norm (g' x h) = norm (f' N x h - (f' N x h - g' x h))"
          by simp
        also have "\<dots> \<le> norm (f' N x h) + norm (f' N x h - g' x h)"
          by (rule norm_triangle_ineq4)
        also have "\<dots> \<le> norm h * K + 1 * norm h"
          using N K by (fast intro: add_mono)
        finally have "norm (g' x h) \<le> norm h * (K + 1)"
          by (simp add: ring_distribs)
      }
      then show "\<exists>K. \<forall>h. norm (g' x h) \<le> norm h * K" by fast
    qed
    show "\<forall>e>0. eventually (\<lambda>y. norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)) (at x within s)"
    proof (rule, rule)
      fix e :: real
      assume "e > 0"
      then have *: "e / 3 > 0"
        by auto
      obtain N1 where N1: "\<forall>n\<ge>N1. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e / 3 * norm h"
        using assms(3) * by blast
      obtain N2 where
          N2: "\<forall>n\<ge>N2. \<forall>x\<in>s. \<forall>y\<in>s. norm (f n x - f n y - (g x - g y)) \<le> e / 3 * norm (x - y)"
        using lem2 * by blast
      let ?N = "max N1 N2"
      have "eventually (\<lambda>y. norm (f ?N y - f ?N x - f' ?N x (y - x)) \<le> e / 3 * norm (y - x)) (at x within s)"
        using assms(2)[unfolded has_derivative_within_alt2] and \<open>x \<in> s\<close> and * by fast
      moreover have "eventually (\<lambda>y. y \<in> s) (at x within s)"
        unfolding eventually_at by (fast intro: zero_less_one)
      ultimately show "\<forall>\<^sub>F y in at x within s. norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)"
      proof (rule eventually_elim2)
        fix y
        assume "y \<in> s"
        assume "norm (f ?N y - f ?N x - f' ?N x (y - x)) \<le> e / 3 * norm (y - x)"
        moreover have "norm (g y - g x - (f ?N y - f ?N x)) \<le> e / 3 * norm (y - x)"
          using N2[rule_format, OF _ \<open>y \<in> s\<close> \<open>x \<in> s\<close>]
          by (simp add: norm_minus_commute)
        ultimately have "norm (g y - g x - f' ?N x (y - x)) \<le> 2 * e / 3 * norm (y - x)"
          using norm_triangle_le[of "g y - g x - (f ?N y - f ?N x)" "f ?N y - f ?N x - f' ?N x (y - x)" "2 * e / 3 * norm (y - x)"]
          by (auto simp add: algebra_simps)
        moreover
        have " norm (f' ?N x (y - x) - g' x (y - x)) \<le> e / 3 * norm (y - x)"
          using N1 \<open>x \<in> s\<close> by auto
        ultimately show "norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)"
          using norm_triangle_le[of "g y - g x - f' (max N1 N2) x (y - x)" "f' (max N1 N2) x (y - x) - g' x (y - x)"]
          by (auto simp add: algebra_simps)
      qed
    qed
  qed
  then show ?thesis by fast
qed

text \<open>Can choose to line up antiderivatives if we want.\<close>

lemma has_antiderivative_sequence:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::banach"
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
    apply (rule \<open>a \<in> s\<close>)
    apply auto
    done
qed auto

lemma has_antiderivative_limit:
  fixes g' :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'b::banach"
  assumes "convex s"
    and "\<forall>e>0. \<exists>f f'. \<forall>x\<in>s.
      (f has_derivative (f' x)) (at x within s) \<and> (\<forall>h. norm (f' x h - g' x h) \<le> e * norm h)"
  shows "\<exists>g. \<forall>x\<in>s. (g has_derivative g' x) (at x within s)"
proof -
  have *: "\<forall>n. \<exists>f f'. \<forall>x\<in>s.
    (f has_derivative (f' x)) (at x within s) \<and>
    (\<forall>h. norm(f' x h - g' x h) \<le> inverse (real (Suc n)) * norm h)"
    by (simp add: assms(2))
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
      using reals_Archimedean[OF \<open>e>0\<close>] ..
    show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
      apply (rule_tac x=N in exI)
      apply rule
      apply rule
      apply rule
      apply rule
    proof -
      fix n x h
      assume n: "N \<le> n" and x: "x \<in> s"
      have *: "inverse (real (Suc n)) \<le> e"
        apply (rule order_trans[OF _ N[THEN less_imp_le]])
        using n
        apply (auto simp add: field_simps)
        done
      show "norm (f' n x h - g' x h) \<le> e * norm h"
        using f[rule_format,THEN conjunct2, OF x, of n, THEN spec[where x=h]]
        apply (rule order_trans)
        using N *
        apply (cases "h = 0")
        apply auto
        done
    qed
  qed (insert f, auto)
qed


subsection \<open>Differentiation of a series\<close>

lemma has_derivative_series:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::banach"
  assumes "convex s"
    and "\<And>n x. x \<in> s \<Longrightarrow> ((f n) has_derivative (f' n x)) (at x within s)"
    and "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (sum (\<lambda>i. f' i x h) {..<n} - g' x h) \<le> e * norm h"
    and "x \<in> s"
    and "(\<lambda>n. f n x) sums l"
  shows "\<exists>g. \<forall>x\<in>s. (\<lambda>n. f n x) sums (g x) \<and> (g has_derivative g' x) (at x within s)"
  unfolding sums_def
  apply (rule has_derivative_sequence[OF assms(1) _ assms(3)])
  apply (metis assms(2) has_derivative_sum)
  using assms(4-5)
  unfolding sums_def
  apply auto
  done

lemma has_field_derivative_series:
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex s"
  assumes "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x within s)"
  assumes "uniform_limit s (\<lambda>n x. \<Sum>i<n. f' i x) g' sequentially"
  assumes "x0 \<in> s" "summable (\<lambda>n. f n x0)"
  shows   "\<exists>g. \<forall>x\<in>s. (\<lambda>n. f n x) sums g x \<and> (g has_field_derivative g' x) (at x within s)"
unfolding has_field_derivative_def
proof (rule has_derivative_series)
  show "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm ((\<Sum>i<n. f' i x * h) - g' x * h) \<le> e * norm h"
  proof (intro allI impI)
    fix e :: real assume "e > 0"
    with assms(3) obtain N where N: "\<And>n x. n \<ge> N \<Longrightarrow> x \<in> s \<Longrightarrow> norm ((\<Sum>i<n. f' i x) - g' x) < e"
      unfolding uniform_limit_iff eventually_at_top_linorder dist_norm by blast
    {
      fix n :: nat and x h :: 'a assume nx: "n \<ge> N" "x \<in> s"
      have "norm ((\<Sum>i<n. f' i x * h) - g' x * h) = norm ((\<Sum>i<n. f' i x) - g' x) * norm h"
        by (simp add: norm_mult [symmetric] ring_distribs sum_distrib_right)
      also from N[OF nx] have "norm ((\<Sum>i<n. f' i x) - g' x) \<le> e" by simp
      hence "norm ((\<Sum>i<n. f' i x) - g' x) * norm h \<le> e * norm h"
        by (intro mult_right_mono) simp_all
      finally have "norm ((\<Sum>i<n. f' i x * h) - g' x * h) \<le> e * norm h" .
    }
    thus "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm ((\<Sum>i<n. f' i x * h) - g' x * h) \<le> e * norm h" by blast
  qed
qed (insert assms, auto simp: has_field_derivative_def)

lemma has_field_derivative_series':
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex s"
  assumes "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x within s)"
  assumes "uniformly_convergent_on s (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> s" "summable (\<lambda>n. f n x0)" "x \<in> interior s"
  shows   "summable (\<lambda>n. f n x)" "((\<lambda>x. \<Sum>n. f n x) has_field_derivative (\<Sum>n. f' n x)) (at x)"
proof -
  from \<open>x \<in> interior s\<close> have "x \<in> s" using interior_subset by blast
  define g' where [abs_def]: "g' x = (\<Sum>i. f' i x)" for x
  from assms(3) have "uniform_limit s (\<lambda>n x. \<Sum>i<n. f' i x) g' sequentially"
    by (simp add: uniformly_convergent_uniform_limit_iff suminf_eq_lim g'_def)
  from has_field_derivative_series[OF assms(1,2) this assms(4,5)] obtain g where g:
    "\<And>x. x \<in> s \<Longrightarrow> (\<lambda>n. f n x) sums g x"
    "\<And>x. x \<in> s \<Longrightarrow> (g has_field_derivative g' x) (at x within s)" by blast
  from g(1)[OF \<open>x \<in> s\<close>] show "summable (\<lambda>n. f n x)" by (simp add: sums_iff)
  from g(2)[OF \<open>x \<in> s\<close>] \<open>x \<in> interior s\<close> have "(g has_field_derivative g' x) (at x)"
    by (simp add: at_within_interior[of x s])
  also have "(g has_field_derivative g' x) (at x) \<longleftrightarrow>
                ((\<lambda>x. \<Sum>n. f n x) has_field_derivative g' x) (at x)"
    using eventually_nhds_in_nhd[OF \<open>x \<in> interior s\<close>] interior_subset[of s] g(1)
    by (intro DERIV_cong_ev) (auto elim!: eventually_mono simp: sums_iff)
  finally show "((\<lambda>x. \<Sum>n. f n x) has_field_derivative g' x) (at x)" .
qed

lemma differentiable_series:
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex s" "open s"
  assumes "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on s (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> s" "summable (\<lambda>n. f n x0)" and x: "x \<in> s"
  shows   "summable (\<lambda>n. f n x)" and "(\<lambda>x. \<Sum>n. f n x) differentiable (at x)"
proof -
  from assms(4) obtain g' where A: "uniform_limit s (\<lambda>n x. \<Sum>i<n. f' i x) g' sequentially"
    unfolding uniformly_convergent_on_def by blast
  from x and \<open>open s\<close> have s: "at x within s = at x" by (rule at_within_open)
  have "\<exists>g. \<forall>x\<in>s. (\<lambda>n. f n x) sums g x \<and> (g has_field_derivative g' x) (at x within s)"
    by (intro has_field_derivative_series[of s f f' g' x0] assms A has_field_derivative_at_within)
  then obtain g where g: "\<And>x. x \<in> s \<Longrightarrow> (\<lambda>n. f n x) sums g x"
    "\<And>x. x \<in> s \<Longrightarrow> (g has_field_derivative g' x) (at x within s)" by blast
  from g[OF x] show "summable (\<lambda>n. f n x)" by (auto simp: summable_def)
  from g(2)[OF x] have g': "(g has_derivative ( * ) (g' x)) (at x)"
    by (simp add: has_field_derivative_def s)
  have "((\<lambda>x. \<Sum>n. f n x) has_derivative ( * ) (g' x)) (at x)"
    by (rule has_derivative_transform_within_open[OF g' \<open>open s\<close> x])
       (insert g, auto simp: sums_iff)
  thus "(\<lambda>x. \<Sum>n. f n x) differentiable (at x)" unfolding differentiable_def
    by (auto simp: summable_def differentiable_def has_field_derivative_def)
qed

lemma differentiable_series':
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex s" "open s"
  assumes "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on s (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> s" "summable (\<lambda>n. f n x0)"
  shows   "(\<lambda>x. \<Sum>n. f n x) differentiable (at x0)"
  using differentiable_series[OF assms, of x0] \<open>x0 \<in> s\<close> by blast+

text \<open>Considering derivative @{typ "real \<Rightarrow> 'b::real_normed_vector"} as a vector.\<close>

definition "vector_derivative f net = (SOME f'. (f has_vector_derivative f') net)"

lemma vector_derivative_unique_within:
  assumes not_bot: "at x within s \<noteq> bot"
    and f': "(f has_vector_derivative f') (at x within s)"
    and f'': "(f has_vector_derivative f'') (at x within s)"
  shows "f' = f''"
proof -
  have "(\<lambda>x. x *\<^sub>R f') = (\<lambda>x. x *\<^sub>R f'')"
  proof (rule frechet_derivative_unique_within)
    show "\<forall>i\<in>Basis. \<forall>e>0. \<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> x + d *\<^sub>R i \<in> s"
    proof clarsimp
      fix e :: real assume "0 < e"
      with islimpt_approachable_real[of x s] not_bot
      obtain x' where "x' \<in> s" "x' \<noteq> x" "\<bar>x' - x\<bar> < e"
        by (auto simp add: trivial_limit_within)
      then show "\<exists>d. d \<noteq> 0 \<and> \<bar>d\<bar> < e \<and> x + d \<in> s"
        by (intro exI[of _ "x' - x"]) auto
    qed
  qed (insert f' f'', auto simp: has_vector_derivative_def)
  then show ?thesis
    unfolding fun_eq_iff by (metis scaleR_one)
qed

lemma vector_derivative_unique_at:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> (f has_vector_derivative f'') (at x) \<Longrightarrow> f' = f''"
  by (rule vector_derivative_unique_within) auto

lemma differentiableI_vector: "(f has_vector_derivative y) F \<Longrightarrow> f differentiable F"
  by (auto simp: differentiable_def has_vector_derivative_def)

lemma vector_derivative_works:
  "f differentiable net \<longleftrightarrow> (f has_vector_derivative (vector_derivative f net)) net"
    (is "?l = ?r")
proof
  assume ?l
  obtain f' where f': "(f has_derivative f') net"
    using \<open>?l\<close> unfolding differentiable_def ..
  then interpret bounded_linear f'
    by auto
  show ?r
    unfolding vector_derivative_def has_vector_derivative_def
    by (rule someI[of _ "f' 1"]) (simp add: scaleR[symmetric] f')
qed (auto simp: vector_derivative_def has_vector_derivative_def differentiable_def)

lemma vector_derivative_within:
  assumes not_bot: "at x within s \<noteq> bot" and y: "(f has_vector_derivative y) (at x within s)"
  shows "vector_derivative f (at x within s) = y"
  using y
  by (intro vector_derivative_unique_within[OF not_bot vector_derivative_works[THEN iffD1] y])
     (auto simp: differentiable_def has_vector_derivative_def)

lemma frechet_derivative_eq_vector_derivative:
  assumes "f differentiable (at x)"
    shows  "(frechet_derivative f (at x)) = (\<lambda>r. r *\<^sub>R vector_derivative f (at x))"
using assms
by (auto simp: differentiable_iff_scaleR vector_derivative_def has_vector_derivative_def
         intro: someI frechet_derivative_at [symmetric])

lemma has_real_derivative:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_derivative f') F"
  obtains c where "(f has_real_derivative c) F"
proof -
  obtain c where "f' = (\<lambda>x. x * c)"
    by (metis assms has_derivative_bounded_linear real_bounded_linear)
  then show ?thesis
    by (metis assms that has_field_derivative_def mult_commute_abs)
qed

lemma has_real_derivative_iff:
  fixes f :: "real \<Rightarrow> real"
  shows "(\<exists>c. (f has_real_derivative c) F) = (\<exists>D. (f has_derivative D) F)"
  by (metis has_field_derivative_def has_real_derivative)

lemma has_vector_derivative_cong_ev:
  assumes *: "eventually (\<lambda>x. x \<in> s \<longrightarrow> f x = g x) (nhds x)" "f x = g x"
  shows "(f has_vector_derivative f') (at x within s) = (g has_vector_derivative f') (at x within s)"
  unfolding has_vector_derivative_def has_derivative_def
  using *
  apply (cases "at x within s \<noteq> bot")
  apply (intro refl conj_cong filterlim_cong)
  apply (auto simp: netlimit_within eventually_at_filter elim: eventually_mono)
  done

definition deriv :: "('a \<Rightarrow> 'a::real_normed_field) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "deriv f x \<equiv> SOME D. DERIV f x :> D"

lemma DERIV_imp_deriv: "DERIV f x :> f' \<Longrightarrow> deriv f x = f'"
  unfolding deriv_def by (metis some_equality DERIV_unique)

lemma DERIV_deriv_iff_has_field_derivative:
  "DERIV f x :> deriv f x \<longleftrightarrow> (\<exists>f'. (f has_field_derivative f') (at x))"
  by (auto simp: has_field_derivative_def DERIV_imp_deriv)

lemma DERIV_deriv_iff_real_differentiable:
  fixes x :: real
  shows "DERIV f x :> deriv f x \<longleftrightarrow> f differentiable at x"
  unfolding differentiable_def by (metis DERIV_imp_deriv has_real_derivative_iff)

lemma deriv_cong_ev:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)" "x = y"
  shows   "deriv f x = deriv g y"
proof -
  have "(\<lambda>D. (f has_field_derivative D) (at x)) = (\<lambda>D. (g has_field_derivative D) (at y))"
    by (intro ext DERIV_cong_ev refl assms)
  thus ?thesis by (simp add: deriv_def assms)
qed

lemma higher_deriv_cong_ev:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)" "x = y"
  shows   "(deriv ^^ n) f x = (deriv ^^ n) g y"
proof -
  from assms(1) have "eventually (\<lambda>x. (deriv ^^ n) f x = (deriv ^^ n) g x) (nhds x)"
  proof (induction n arbitrary: f g)
    case (Suc n)
    from Suc.prems have "eventually (\<lambda>y. eventually (\<lambda>z. f z = g z) (nhds y)) (nhds x)"
      by (simp add: eventually_eventually)
    hence "eventually (\<lambda>x. deriv f x = deriv g x) (nhds x)"
      by eventually_elim (rule deriv_cong_ev, simp_all)
    thus ?case by (auto intro!: deriv_cong_ev Suc simp: funpow_Suc_right simp del: funpow.simps)
  qed auto
  from eventually_nhds_x_imp_x[OF this] assms(2) show ?thesis by simp
qed

lemma real_derivative_chain:
  fixes x :: real
  shows "f differentiable at x \<Longrightarrow> g differentiable at (f x)
    \<Longrightarrow> deriv (g o f) x = deriv g (f x) * deriv f x"
  by (metis DERIV_deriv_iff_real_differentiable DERIV_chain DERIV_imp_deriv)
lemma field_derivative_eq_vector_derivative:
   "(deriv f x) = vector_derivative f (at x)"
by (simp add: mult.commute deriv_def vector_derivative_def has_vector_derivative_def has_field_derivative_def)

lemma islimpt_closure_open:
  fixes s :: "'a::perfect_space set"
  assumes "open s" and t: "t = closure s" "x \<in> t"
  shows "x islimpt t"
proof cases
  assume "x \<in> s"
  { fix T assume "x \<in> T" "open T"
    then have "open (s \<inter> T)"
      using \<open>open s\<close> by auto
    then have "s \<inter> T \<noteq> {x}"
      using not_open_singleton[of x] by auto
    with \<open>x \<in> T\<close> \<open>x \<in> s\<close> have "\<exists>y\<in>t. y \<in> T \<and> y \<noteq> x"
      using closure_subset[of s] by (auto simp: t) }
  then show ?thesis
    by (auto intro!: islimptI)
next
  assume "x \<notin> s" with t show ?thesis
    unfolding t closure_def by (auto intro: islimpt_subset)
qed

lemma vector_derivative_unique_within_closed_interval:
  assumes ab: "a < b" "x \<in> cbox a b"
  assumes D: "(f has_vector_derivative f') (at x within cbox a b)" "(f has_vector_derivative f'') (at x within cbox a b)"
  shows "f' = f''"
  using ab
  by (intro vector_derivative_unique_within[OF _ D])
     (auto simp: trivial_limit_within intro!: islimpt_closure_open[where s="{a <..< b}"])

lemma vector_derivative_at:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> vector_derivative f (at x) = f'"
  by (intro vector_derivative_within at_neq_bot)

lemma has_vector_derivative_id_at [simp]: "vector_derivative (\<lambda>x. x) (at a) = 1"
  by (simp add: vector_derivative_at)

lemma vector_derivative_minus_at [simp]:
  "f differentiable at a
   \<Longrightarrow> vector_derivative (\<lambda>x. - f x) (at a) = - vector_derivative f (at a)"
  by (simp add: vector_derivative_at has_vector_derivative_minus vector_derivative_works [symmetric])

lemma vector_derivative_add_at [simp]:
  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x + g x) (at a) = vector_derivative f (at a) + vector_derivative g (at a)"
  by (simp add: vector_derivative_at has_vector_derivative_add vector_derivative_works [symmetric])

lemma vector_derivative_diff_at [simp]:
  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x - g x) (at a) = vector_derivative f (at a) - vector_derivative g (at a)"
  by (simp add: vector_derivative_at has_vector_derivative_diff vector_derivative_works [symmetric])

lemma vector_derivative_mult_at [simp]:
  fixes f g :: "real \<Rightarrow> 'a :: real_normed_algebra"
  shows  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x * g x) (at a) = f a * vector_derivative g (at a) + vector_derivative f (at a) * g a"
  by (simp add: vector_derivative_at has_vector_derivative_mult vector_derivative_works [symmetric])

lemma vector_derivative_scaleR_at [simp]:
    "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x *\<^sub>R g x) (at a) = f a *\<^sub>R vector_derivative g (at a) + vector_derivative f (at a) *\<^sub>R g a"
apply (rule vector_derivative_at)
apply (rule has_vector_derivative_scaleR)
apply (auto simp: vector_derivative_works has_vector_derivative_def has_field_derivative_def mult_commute_abs)
done

lemma vector_derivative_within_cbox:
  assumes ab: "a < b" "x \<in> cbox a b"
  assumes f: "(f has_vector_derivative f') (at x within cbox a b)"
  shows "vector_derivative f (at x within cbox a b) = f'"
  by (intro vector_derivative_unique_within_closed_interval[OF ab _ f]
            vector_derivative_works[THEN iffD1] differentiableI_vector)
     fact

lemma vector_derivative_within_closed_interval:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "a < b" and "x \<in> {a .. b}"
  assumes "(f has_vector_derivative f') (at x within {a .. b})"
  shows "vector_derivative f (at x within {a .. b}) = f'"
  using assms vector_derivative_within_cbox
  by fastforce

lemma has_vector_derivative_within_subset:
  "(f has_vector_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (f has_vector_derivative f') (at x within t)"
  by (auto simp: has_vector_derivative_def intro: has_derivative_within_subset)

lemma has_vector_derivative_at_within:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> (f has_vector_derivative f') (at x within s)"
  unfolding has_vector_derivative_def
  by (rule has_derivative_at_withinI)

lemma has_vector_derivative_weaken:
  fixes x D and f g s t
  assumes f: "(f has_vector_derivative D) (at x within t)"
    and "x \<in> s" "s \<subseteq> t"
    and "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(g has_vector_derivative D) (at x within s)"
proof -
  have "(f has_vector_derivative D) (at x within s) \<longleftrightarrow> (g has_vector_derivative D) (at x within s)"
    unfolding has_vector_derivative_def has_derivative_iff_norm
    using assms by (intro conj_cong Lim_cong_within refl) auto
  then show ?thesis
    using has_vector_derivative_within_subset[OF f \<open>s \<subseteq> t\<close>] by simp
qed

lemma has_vector_derivative_transform_within:
  assumes "(f has_vector_derivative f') (at x within s)"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
    shows "(g has_vector_derivative f') (at x within s)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform_within)

lemma has_vector_derivative_transform_within_open:
  assumes "(f has_vector_derivative f') (at x)"
    and "open s"
    and "x \<in> s"
    and "\<And>y. y\<in>s \<Longrightarrow> f y = g y"
  shows "(g has_vector_derivative f') (at x)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform_within_open)

lemma has_vector_derivative_transform:
  assumes "x \<in> s" "\<And>x. x \<in> s \<Longrightarrow> g x = f x"
  assumes f': "(f has_vector_derivative f') (at x within s)"
  shows "(g has_vector_derivative f') (at x within s)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform)

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

lemma vector_derivative_const_at [simp]: "vector_derivative (\<lambda>x. c) (at a) = 0"
  by (simp add: vector_derivative_at)

lemma vector_derivative_at_within_ivl:
  "(f has_vector_derivative f') (at x) \<Longrightarrow>
    a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> a<b \<Longrightarrow> vector_derivative f (at x within {a..b}) = f'"
  using has_vector_derivative_at_within vector_derivative_within_cbox by fastforce

lemma vector_derivative_chain_at:
  assumes "f differentiable at x" "(g differentiable at (f x))"
  shows "vector_derivative (g \<circ> f) (at x) =
         vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x))"
by (metis vector_diff_chain_at vector_derivative_at vector_derivative_works assms)

lemma field_vector_diff_chain_at:  (*thanks to Wenda Li*)
 assumes Df: "(f has_vector_derivative f') (at x)"
     and Dg: "(g has_field_derivative g') (at (f x))"
 shows "((g \<circ> f) has_vector_derivative (f' * g')) (at x)"
using diff_chain_at[OF Df[unfolded has_vector_derivative_def]
                       Dg [unfolded has_field_derivative_def]]
 by (auto simp: o_def mult.commute has_vector_derivative_def)

lemma vector_derivative_chain_within: 
  assumes "at x within s \<noteq> bot" "f differentiable (at x within s)" 
    "(g has_derivative g') (at (f x) within f ` s)" 
  shows "vector_derivative (g \<circ> f) (at x within s) =
        g' (vector_derivative f (at x within s)) "
  apply (rule vector_derivative_within [OF \<open>at x within s \<noteq> bot\<close>])
  apply (rule vector_derivative_diff_chain_within)
  using assms(2-3) vector_derivative_works
  by auto

subsection\<open>The notion of being field differentiable\<close>

definition field_differentiable :: "['a \<Rightarrow> 'a::real_normed_field, 'a filter] \<Rightarrow> bool"
           (infixr "(field'_differentiable)" 50)
  where "f field_differentiable F \<equiv> \<exists>f'. (f has_field_derivative f') F"

lemma field_differentiable_imp_differentiable:
  "f field_differentiable F \<Longrightarrow> f differentiable F"
  unfolding field_differentiable_def differentiable_def 
  using has_field_derivative_imp_has_derivative by auto

lemma field_differentiable_derivI:
    "f field_differentiable (at x) \<Longrightarrow> (f has_field_derivative deriv f x) (at x)"
by (simp add: field_differentiable_def DERIV_deriv_iff_has_field_derivative)

lemma field_differentiable_imp_continuous_at:
    "f field_differentiable (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by (metis DERIV_continuous field_differentiable_def)

lemma field_differentiable_within_subset:
    "\<lbrakk>f field_differentiable (at x within s); t \<subseteq> s\<rbrakk>
     \<Longrightarrow> f field_differentiable (at x within t)"
  by (metis DERIV_subset field_differentiable_def)

lemma field_differentiable_at_within:
    "\<lbrakk>f field_differentiable (at x)\<rbrakk>
     \<Longrightarrow> f field_differentiable (at x within s)"
  unfolding field_differentiable_def
  by (metis DERIV_subset top_greatest)

lemma field_differentiable_linear [simp,derivative_intros]: "(( * ) c) field_differentiable F"
proof -
  show ?thesis
    unfolding field_differentiable_def has_field_derivative_def mult_commute_abs
    by (force intro: has_derivative_mult_right)
qed

lemma field_differentiable_const [simp,derivative_intros]: "(\<lambda>z. c) field_differentiable F"
  unfolding field_differentiable_def has_field_derivative_def
  using DERIV_const has_field_derivative_imp_has_derivative by blast

lemma field_differentiable_ident [simp,derivative_intros]: "(\<lambda>z. z) field_differentiable F"
  unfolding field_differentiable_def has_field_derivative_def
  using DERIV_ident has_field_derivative_def by blast

lemma field_differentiable_id [simp,derivative_intros]: "id field_differentiable F"
  unfolding id_def by (rule field_differentiable_ident)

lemma field_differentiable_minus [derivative_intros]:
  "f field_differentiable F \<Longrightarrow> (\<lambda>z. - (f z)) field_differentiable F"
  unfolding field_differentiable_def
  by (metis field_differentiable_minus)

lemma field_differentiable_add [derivative_intros]:
  assumes "f field_differentiable F" "g field_differentiable F"
    shows "(\<lambda>z. f z + g z) field_differentiable F"
  using assms unfolding field_differentiable_def
  by (metis field_differentiable_add)

lemma field_differentiable_add_const [simp,derivative_intros]:
     "(+) c field_differentiable F"
  by (simp add: field_differentiable_add)

lemma field_differentiable_sum [derivative_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) field_differentiable F) \<Longrightarrow> (\<lambda>z. \<Sum>i\<in>I. f i z) field_differentiable F"
  by (induct I rule: infinite_finite_induct)
     (auto intro: field_differentiable_add field_differentiable_const)

lemma field_differentiable_diff [derivative_intros]:
  assumes "f field_differentiable F" "g field_differentiable F"
    shows "(\<lambda>z. f z - g z) field_differentiable F"
  using assms unfolding field_differentiable_def
  by (metis field_differentiable_diff)

lemma field_differentiable_inverse [derivative_intros]:
  assumes "f field_differentiable (at a within s)" "f a \<noteq> 0"
  shows "(\<lambda>z. inverse (f z)) field_differentiable (at a within s)"
  using assms unfolding field_differentiable_def
  by (metis DERIV_inverse_fun)

lemma field_differentiable_mult [derivative_intros]:
  assumes "f field_differentiable (at a within s)"
          "g field_differentiable (at a within s)"
    shows "(\<lambda>z. f z * g z) field_differentiable (at a within s)"
  using assms unfolding field_differentiable_def
  by (metis DERIV_mult [of f _ a s g])

lemma field_differentiable_divide [derivative_intros]:
  assumes "f field_differentiable (at a within s)"
          "g field_differentiable (at a within s)"
          "g a \<noteq> 0"
    shows "(\<lambda>z. f z / g z) field_differentiable (at a within s)"
  using assms unfolding field_differentiable_def
  by (metis DERIV_divide [of f _ a s g])

lemma field_differentiable_power [derivative_intros]:
  assumes "f field_differentiable (at a within s)"
    shows "(\<lambda>z. f z ^ n) field_differentiable (at a within s)"
  using assms unfolding field_differentiable_def
  by (metis DERIV_power)

lemma field_differentiable_transform_within:
  "0 < d \<Longrightarrow>
        x \<in> s \<Longrightarrow>
        (\<And>x'. x' \<in> s \<Longrightarrow> dist x' x < d \<Longrightarrow> f x' = g x') \<Longrightarrow>
        f field_differentiable (at x within s)
        \<Longrightarrow> g field_differentiable (at x within s)"
  unfolding field_differentiable_def has_field_derivative_def
  by (blast intro: has_derivative_transform_within)

lemma field_differentiable_compose_within:
  assumes "f field_differentiable (at a within s)"
          "g field_differentiable (at (f a) within f`s)"
    shows "(g o f) field_differentiable (at a within s)"
  using assms unfolding field_differentiable_def
  by (metis DERIV_image_chain)

lemma field_differentiable_compose:
  "f field_differentiable at z \<Longrightarrow> g field_differentiable at (f z)
          \<Longrightarrow> (g o f) field_differentiable at z"
by (metis field_differentiable_at_within field_differentiable_compose_within)

lemma field_differentiable_within_open:
     "\<lbrakk>a \<in> s; open s\<rbrakk> \<Longrightarrow> f field_differentiable at a within s \<longleftrightarrow>
                          f field_differentiable at a"
  unfolding field_differentiable_def
  by (metis at_within_open)

lemma vector_derivative_chain_at_general: 
  assumes "f differentiable at x" "g field_differentiable at (f x)"
  shows "vector_derivative (g \<circ> f) (at x) = vector_derivative f (at x) * deriv g (f x)"
  apply (rule vector_derivative_at [OF field_vector_diff_chain_at])
  using assms vector_derivative_works by (auto simp: field_differentiable_derivI)

lemma exp_scaleR_has_vector_derivative_right:
  "((\<lambda>t. exp (t *\<^sub>R A)) has_vector_derivative exp (t *\<^sub>R A) * A) (at t within T)"
  unfolding has_vector_derivative_def
proof (rule has_derivativeI)
  let ?F = "at t within (T \<inter> {t - 1 <..< t + 1})"
  have *: "at t within T = ?F"
    by (rule at_within_nhd[where S="{t - 1 <..< t + 1}"]) auto
  let ?e = "\<lambda>i x. (inverse (1 + real i) * inverse (fact i) * (x - t) ^ i) *\<^sub>R (A * A ^ i)"
  have "\<forall>\<^sub>F n in sequentially.
      \<forall>x\<in>T \<inter> {t - 1<..<t + 1}. norm (?e n x) \<le> norm (A ^ (n + 1) /\<^sub>R fact (n + 1))"
    by (auto simp: divide_simps power_abs intro!: mult_left_le_one_le power_le_one eventuallyI)
  then have "uniform_limit (T \<inter> {t - 1<..<t + 1}) (\<lambda>n x. \<Sum>i<n. ?e i x) (\<lambda>x. \<Sum>i. ?e i x) sequentially"
    by (rule weierstrass_m_test_ev) (intro summable_ignore_initial_segment summable_norm_exp)
  moreover
  have "\<forall>\<^sub>F x in sequentially. x > 0"
    by (metis eventually_gt_at_top)
  then have
    "\<forall>\<^sub>F n in sequentially. ((\<lambda>x. \<Sum>i<n. ?e i x) \<longlongrightarrow> A) ?F"
    by eventually_elim
      (auto intro!: tendsto_eq_intros
        simp: power_0_left if_distrib cond_application_beta sum.delta
        cong: if_cong)
  ultimately
  have [tendsto_intros]: "((\<lambda>x. \<Sum>i. ?e i x) \<longlongrightarrow> A) ?F"
    by (auto intro!: swap_uniform_limit[where f="\<lambda>n x. \<Sum>i < n. ?e i x" and F = sequentially])
  have [tendsto_intros]: "((\<lambda>x. if x = t then 0 else 1) \<longlongrightarrow> 1) ?F"
    by (rule Lim_eventually) (simp add: eventually_at_filter)
  have "((\<lambda>y. ((y - t) / abs (y - t)) *\<^sub>R ((\<Sum>n. ?e n y) - A)) \<longlongrightarrow> 0) (at t within T)"
    unfolding *
    by (rule tendsto_norm_zero_cancel) (auto intro!: tendsto_eq_intros)

  moreover

  have "\<forall>\<^sub>F x in at t within T. x \<noteq> t"
    by (simp add: eventually_at_filter)
  then have "\<forall>\<^sub>F x in at t within T. ((x - t) / \<bar>x - t\<bar>) *\<^sub>R ((\<Sum>n. ?e n x) - A) =
    (exp ((x - t) *\<^sub>R A) - 1 - (x - t) *\<^sub>R A) /\<^sub>R norm (x - t)"
  proof eventually_elim
    case (elim x)
    have "(exp ((x - t) *\<^sub>R A) - 1 - (x - t) *\<^sub>R A) /\<^sub>R norm (x - t) =
      ((\<Sum>n. (x - t) *\<^sub>R ?e n x) - (x - t) *\<^sub>R A) /\<^sub>R norm (x - t)"
      unfolding exp_first_term
      by (simp add: ac_simps)
    also
    have "summable (\<lambda>n. ?e n x)"
    proof -
      from elim have "?e n x = (((x - t) *\<^sub>R A) ^ (n + 1)) /\<^sub>R fact (n + 1) /\<^sub>R (x - t)" for n
        by simp
      then show ?thesis
        by (auto simp only:
          intro!: summable_scaleR_right summable_ignore_initial_segment summable_exp_generic)
    qed
    then have "(\<Sum>n. (x - t) *\<^sub>R ?e n x) = (x - t) *\<^sub>R (\<Sum>n. ?e n x)"
      by (rule suminf_scaleR_right[symmetric])
    also have "(\<dots> - (x - t) *\<^sub>R A) /\<^sub>R norm (x - t) = (x - t) *\<^sub>R ((\<Sum>n. ?e n x) - A) /\<^sub>R norm (x - t)"
      by (simp add: algebra_simps)
    finally show ?case
      by (simp add: divide_simps)
  qed

  ultimately

  have "((\<lambda>y. (exp ((y - t) *\<^sub>R A) - 1 - (y - t) *\<^sub>R A) /\<^sub>R norm (y - t)) \<longlongrightarrow> 0) (at t within T)"
    by (rule Lim_transform_eventually[rotated])
  from tendsto_mult_right_zero[OF this, where c="exp (t *\<^sub>R A)"]
  show "((\<lambda>y. (exp (y *\<^sub>R A) - exp (t *\<^sub>R A) - (y - t) *\<^sub>R (exp (t *\<^sub>R A) * A)) /\<^sub>R norm (y - t)) \<longlongrightarrow> 0)
      (at t within T)"
    by (rule Lim_transform_eventually[rotated])
      (auto simp: algebra_simps divide_simps exp_add_commuting[symmetric])
qed (rule bounded_linear_scaleR_left)

lemma exp_times_scaleR_commute: "exp (t *\<^sub>R A) * A = A * exp (t *\<^sub>R A)"
  using exp_times_arg_commute[symmetric, of "t *\<^sub>R A"]
  by (auto simp: algebra_simps)

lemma exp_scaleR_has_vector_derivative_left: "((\<lambda>t. exp (t *\<^sub>R A)) has_vector_derivative A * exp (t *\<^sub>R A)) (at t)"
  using exp_scaleR_has_vector_derivative_right[of A t]
  by (simp add: exp_times_scaleR_commute)


subsection \<open>Relation between convexity and derivative\<close>

(* TODO: Generalise to real vector spaces? *)
lemma convex_on_imp_above_tangent:
  assumes convex: "convex_on A f" and connected: "connected A"
  assumes c: "c \<in> interior A" and x : "x \<in> A"
  assumes deriv: "(f has_field_derivative f') (at c within A)"
  shows   "f x - f c \<ge> f' * (x - c)"
proof (cases x c rule: linorder_cases)
  assume xc: "x > c"
  let ?A' = "interior A \<inter> {c<..}"
  from c have "c \<in> interior A \<inter> closure {c<..}" by auto
  also have "\<dots> \<subseteq> closure (interior A \<inter> {c<..})" by (intro open_Int_closure_subset) auto
  finally have "at c within ?A' \<noteq> bot" by (subst at_within_eq_bot_iff) auto
  moreover from deriv have "((\<lambda>y. (f y - f c) / (y - c)) \<longlongrightarrow> f') (at c within ?A')"
    unfolding DERIV_within_iff using interior_subset[of A] by (blast intro: tendsto_mono at_le)
  moreover from eventually_at_right_real[OF xc]
    have "eventually (\<lambda>y. (f y - f c) / (y - c) \<le> (f x - f c) / (x - c)) (at_right c)"
  proof eventually_elim
    fix y assume y: "y \<in> {c<..<x}"
    with convex connected x c have "f y \<le> (f x - f c) / (x - c) * (y - c) + f c"
      using interior_subset[of A]
      by (intro convex_onD_Icc' convex_on_subset[OF convex] connected_contains_Icc) auto
    hence "f y - f c \<le> (f x - f c) / (x - c) * (y - c)" by simp
    thus "(f y - f c) / (y - c) \<le> (f x - f c) / (x - c)" using y xc by (simp add: divide_simps)
  qed
  hence "eventually (\<lambda>y. (f y - f c) / (y - c) \<le> (f x - f c) / (x - c)) (at c within ?A')"
    by (blast intro: filter_leD at_le)
  ultimately have "f' \<le> (f x - f c) / (x - c)" by (simp add: tendsto_upperbound)
  thus ?thesis using xc by (simp add: field_simps)
next
  assume xc: "x < c"
  let ?A' = "interior A \<inter> {..<c}"
  from c have "c \<in> interior A \<inter> closure {..<c}" by auto
  also have "\<dots> \<subseteq> closure (interior A \<inter> {..<c})" by (intro open_Int_closure_subset) auto
  finally have "at c within ?A' \<noteq> bot" by (subst at_within_eq_bot_iff) auto
  moreover from deriv have "((\<lambda>y. (f y - f c) / (y - c)) \<longlongrightarrow> f') (at c within ?A')"
    unfolding DERIV_within_iff using interior_subset[of A] by (blast intro: tendsto_mono at_le)
  moreover from eventually_at_left_real[OF xc]
    have "eventually (\<lambda>y. (f y - f c) / (y - c) \<ge> (f x - f c) / (x - c)) (at_left c)"
  proof eventually_elim
    fix y assume y: "y \<in> {x<..<c}"
    with convex connected x c have "f y \<le> (f x - f c) / (c - x) * (c - y) + f c"
      using interior_subset[of A]
      by (intro convex_onD_Icc'' convex_on_subset[OF convex] connected_contains_Icc) auto
    hence "f y - f c \<le> (f x - f c) * ((c - y) / (c - x))" by simp
    also have "(c - y) / (c - x) = (y - c) / (x - c)" using y xc by (simp add: field_simps)
    finally show "(f y - f c) / (y - c) \<ge> (f x - f c) / (x - c)" using y xc
      by (simp add: divide_simps)
  qed
  hence "eventually (\<lambda>y. (f y - f c) / (y - c) \<ge> (f x - f c) / (x - c)) (at c within ?A')"
    by (blast intro: filter_leD at_le)
  ultimately have "f' \<ge> (f x - f c) / (x - c)" by (simp add: tendsto_lowerbound)
  thus ?thesis using xc by (simp add: field_simps)
qed simp_all


subsection \<open>Partial derivatives\<close>

lemma eventually_at_Pair_within_TimesI1:
  fixes x::"'a::metric_space"
  assumes "\<forall>\<^sub>F x' in at x within X. P x'"
  assumes "P x"
  shows "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. P x'"
proof -
  from assms[unfolded eventually_at_topological]
  obtain S where S: "open S" "x \<in> S" "\<And>x'. x' \<in> X \<Longrightarrow> x' \<in> S \<Longrightarrow> P x'"
    by metis
  show "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. P x'"
    unfolding eventually_at_topological
    by (auto intro!: exI[where x="S \<times> UNIV"] S open_Times)
qed

lemma eventually_at_Pair_within_TimesI2:
  fixes x::"'a::metric_space"
  assumes "\<forall>\<^sub>F y' in at y within Y. P y'"
  assumes "P y"
  shows "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. P y'"
proof -
  from assms[unfolded eventually_at_topological]
  obtain S where S: "open S" "y \<in> S" "\<And>y'. y' \<in> Y \<Longrightarrow> y' \<in> S \<Longrightarrow> P y'"
    by metis
  show "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. P y'"
    unfolding eventually_at_topological
    by (auto intro!: exI[where x="UNIV \<times> S"] S open_Times)
qed

lemma has_derivative_partialsI:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes fx: "((\<lambda>x. f x y) has_derivative fx) (at x within X)"
  assumes fy: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> ((\<lambda>y. f x y) has_derivative blinfun_apply (fy x y)) (at y within Y)"
  assumes fy_cont[unfolded continuous_within]: "continuous (at (x, y) within X \<times> Y) (\<lambda>(x, y). fy x y)"
  assumes "y \<in> Y" "convex Y"
  shows "((\<lambda>(x, y). f x y) has_derivative (\<lambda>(tx, ty). fx tx + fy x y ty)) (at (x, y) within X \<times> Y)"
proof (safe intro!: has_derivativeI tendstoI, goal_cases)
  case (2 e')
  interpret fx: bounded_linear "fx" using fx by (rule has_derivative_bounded_linear)
  define e where "e = e' / 9"
  have "e > 0" using \<open>e' > 0\<close> by (simp add: e_def)

  from fy_cont[THEN tendstoD, OF \<open>e > 0\<close>]
  have "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. dist (fy x' y') (fy x y) < e"
    by (auto simp: split_beta')
  from this[unfolded eventually_at] obtain d' where
    "d' > 0"
    "\<And>x' y'. x' \<in> X \<Longrightarrow> y' \<in> Y \<Longrightarrow> (x', y') \<noteq> (x, y) \<Longrightarrow> dist (x', y') (x, y) < d' \<Longrightarrow>
      dist (fy x' y') (fy x y) < e"
    by auto
  then
  have d': "x' \<in> X \<Longrightarrow> y' \<in> Y \<Longrightarrow> dist (x', y') (x, y) < d' \<Longrightarrow> dist (fy x' y') (fy x y) < e"
    for x' y'
    using \<open>0 < e\<close>
    by (cases "(x', y') = (x, y)") auto
  define d where "d = d' / sqrt 2"
  have "d > 0" using \<open>0 < d'\<close> by (simp add: d_def)
  have d: "x' \<in> X \<Longrightarrow> y' \<in> Y \<Longrightarrow> dist x' x < d \<Longrightarrow> dist y' y < d \<Longrightarrow> dist (fy x' y') (fy x y) < e"
    for x' y'
    by (auto simp: dist_prod_def d_def intro!: d' real_sqrt_sum_squares_less)

  let ?S = "ball y d \<inter> Y"
  have "convex ?S"
    by (auto intro!: convex_Int \<open>convex Y\<close>)
  {
    fix x'::'a and y'::'b
    assume x': "x' \<in> X" and y': "y' \<in> Y"
    assume dx': "dist x' x < d" and dy': "dist y' y < d"
    have "norm (fy x' y' - fy x' y) \<le> dist (fy x' y') (fy x y) + dist (fy x' y) (fy x y)"
      by norm
    also have "dist (fy x' y') (fy x y) < e"
      by (rule d; fact)
    also have "dist (fy x' y) (fy x y) < e"
      by (auto intro!: d simp: dist_prod_def x' \<open>d > 0\<close> \<open>y \<in> Y\<close> dx')
    finally
    have "norm (fy x' y' - fy x' y) < e + e"
      by arith
    then have "onorm (blinfun_apply (fy x' y') - blinfun_apply (fy x' y)) < e + e"
      by (auto simp: norm_blinfun.rep_eq blinfun.diff_left[abs_def] fun_diff_def)
  } note onorm = this

  have ev_mem: "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. (x', y') \<in> X \<times> Y"
    using \<open>y \<in> Y\<close>
    by (auto simp: eventually_at intro!: zero_less_one)
  moreover
  have ev_dist: "\<forall>\<^sub>F xy in at (x, y) within X \<times> Y. dist xy (x, y) < d" if "d > 0" for d
    using eventually_at_ball[OF that]
    by (rule eventually_elim2) (auto simp: dist_commute mem_ball intro!: eventually_True)
  note ev_dist[OF \<open>0 < d\<close>]
  ultimately
  have "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y.
    norm (f x' y' - f x' y - (fy x' y) (y' - y)) \<le> norm (y' - y) * (e + e)"
  proof (eventually_elim, safe)
    fix x' y'
    assume "x' \<in> X" and y': "y' \<in> Y"
    assume dist: "dist (x', y') (x, y) < d"
    then have dx: "dist x' x < d" and dy: "dist y' y < d"
      unfolding dist_prod_def fst_conv snd_conv atomize_conj
      by (metis le_less_trans real_sqrt_sum_squares_ge1 real_sqrt_sum_squares_ge2)
    {
      fix t::real
      assume "t \<in> {0 .. 1}"
      then have "y + t *\<^sub>R (y' - y) \<in> closed_segment y y'"
        by (auto simp: closed_segment_def algebra_simps intro!: exI[where x=t])
      also
      have "\<dots> \<subseteq> ball y d \<inter> Y"
        using \<open>y \<in> Y\<close> \<open>0 < d\<close> dy y'
        by (intro \<open>convex ?S\<close>[unfolded convex_contains_segment, rule_format, of y y'])
          (auto simp: dist_commute mem_ball)
      finally have "y + t *\<^sub>R (y' - y) \<in> ?S" .
    } note seg = this

    have "\<forall>x\<in>ball y d \<inter> Y. onorm (blinfun_apply (fy x' x) - blinfun_apply (fy x' y)) \<le> e + e"
      by (safe intro!: onorm less_imp_le \<open>x' \<in> X\<close> dx) (auto simp: mem_ball dist_commute \<open>0 < d\<close> \<open>y \<in> Y\<close>)
    with seg has_derivative_within_subset[OF assms(2)[OF \<open>x' \<in> X\<close>]]
    show "norm (f x' y' - f x' y - (fy x' y) (y' - y)) \<le> norm (y' - y) * (e + e)"
      by (rule differentiable_bound_linearization[where S="?S"])
        (auto intro!: \<open>0 < d\<close> \<open>y \<in> Y\<close>)
  qed
  moreover
  let ?le = "\<lambda>x'. norm (f x' y - f x y - (fx) (x' - x)) \<le> norm (x' - x) * e"
  from fx[unfolded has_derivative_within, THEN conjunct2, THEN tendstoD, OF \<open>0 < e\<close>]
  have "\<forall>\<^sub>F x' in at x within X. ?le x'"
    by eventually_elim
       (auto simp: dist_norm divide_simps blinfun.bilinear_simps field_simps fx.zero split: if_split_asm)
  then have "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. ?le x'"
    by (rule eventually_at_Pair_within_TimesI1)
       (simp add: blinfun.bilinear_simps fx.zero)
  moreover have "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. norm ((x', y') - (x, y)) \<noteq> 0"
    unfolding norm_eq_zero right_minus_eq
    by (auto simp: eventually_at intro!: zero_less_one)
  moreover
  from fy_cont[THEN tendstoD, OF \<open>0 < e\<close>]
  have "\<forall>\<^sub>F x' in at x within X. norm (fy x' y - fy x y) < e"
    unfolding eventually_at
    using \<open>y \<in> Y\<close>
    by (auto simp: dist_prod_def dist_norm)
  then have "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. norm (fy x' y - fy x y) < e"
    by (rule eventually_at_Pair_within_TimesI1)
       (simp add: blinfun.bilinear_simps \<open>0 < e\<close>)
  ultimately
  have "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y.
            norm ((f x' y' - f x y - (fx (x' - x) + fy x y (y' - y))) /\<^sub>R
              norm ((x', y') - (x, y)))
            < e'"
    apply eventually_elim
  proof safe
    fix x' y'
    have "norm (f x' y' - f x y - (fx (x' - x) + fy x y (y' - y))) \<le>
        norm (f x' y' - f x' y - fy x' y (y' - y)) +
        norm (fy x y (y' - y) - fy x' y (y' - y)) +
        norm (f x' y - f x y - fx (x' - x))"
      by norm
    also
    assume nz: "norm ((x', y') - (x, y)) \<noteq> 0"
      and nfy: "norm (fy x' y - fy x y) < e"
    assume "norm (f x' y' - f x' y - blinfun_apply (fy x' y) (y' - y)) \<le> norm (y' - y) * (e + e)"
    also assume "norm (f x' y - f x y - (fx) (x' - x)) \<le> norm (x' - x) * e"
    also
    have "norm ((fy x y) (y' - y) - (fy x' y) (y' - y)) \<le> norm ((fy x y) - (fy x' y)) * norm (y' - y)"
      by (auto simp: blinfun.bilinear_simps[symmetric] intro!: norm_blinfun)
    also have "\<dots> \<le> (e + e) * norm (y' - y)"
      using \<open>e > 0\<close> nfy
      by (auto simp: norm_minus_commute intro!: mult_right_mono)
    also have "norm (x' - x) * e \<le> norm (x' - x) * (e + e)"
      using \<open>0 < e\<close> by simp
    also have "norm (y' - y) * (e + e) + (e + e) * norm (y' - y) + norm (x' - x) * (e + e) \<le>
        (norm (y' - y) + norm (x' - x)) * (4 * e)"
      using \<open>e > 0\<close>
      by (simp add: algebra_simps)
    also have "\<dots> \<le> 2 * norm ((x', y') - (x, y)) * (4 * e)"
      using \<open>0 < e\<close> real_sqrt_sum_squares_ge1[of "norm (x' - x)" "norm (y' - y)"]
        real_sqrt_sum_squares_ge2[of "norm (y' - y)" "norm (x' - x)"]
      by (auto intro!: mult_right_mono simp: norm_prod_def
        simp del: real_sqrt_sum_squares_ge1 real_sqrt_sum_squares_ge2)
    also have "\<dots> \<le> norm ((x', y') - (x, y)) * (8 * e)"
      by simp
    also have "\<dots> < norm ((x', y') - (x, y)) * e'"
      using \<open>0 < e'\<close> nz
      by (auto simp: e_def)
    finally show "norm ((f x' y' - f x y - (fx (x' - x) + fy x y (y' - y))) /\<^sub>R norm ((x', y') - (x, y))) < e'"
      by (auto simp: divide_simps dist_norm mult.commute)
  qed
  then show ?case
    by eventually_elim (auto simp: dist_norm field_simps)
next
  from has_derivative_bounded_linear[OF fx]
  obtain fxb where "fx = blinfun_apply fxb"
    by (metis bounded_linear_Blinfun_apply)
  then show "bounded_linear (\<lambda>(tx, ty). fx tx + blinfun_apply (fy x y) ty)"
    by (auto intro!: bounded_linear_intros simp: split_beta')
qed


subsection \<open>Differentiable case distinction\<close>

lemma has_derivative_within_If_eq:
  "((\<lambda>x. if P x then f x else g x) has_derivative f') (at x within s) =
    (bounded_linear f' \<and>
     ((\<lambda>y.(if P y then (f y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)
           else (g y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)))
      \<longlongrightarrow> 0) (at x within s))"
  (is "_ = (_ \<and> (?if \<longlongrightarrow> 0) _)")
proof -
  have "(\<lambda>y. (1 / norm (y - x)) *\<^sub>R
           ((if P y then f y else g y) -
            ((if P x then f x else g x) + f' (y - x)))) = ?if"
    by (auto simp: inverse_eq_divide)
  thus ?thesis by (auto simp: has_derivative_within)
qed

lemma has_derivative_If_within_closures:
  assumes f': "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (f has_derivative f' x) (at x within s \<union> (closure s \<inter> closure t))"
  assumes g': "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (g has_derivative g' x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes connect: "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f' x = g' x"
  assumes x_in: "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_derivative
      (if x \<in> s then f' x else g' x)) (at x within (s \<union> t))"
proof -
  from f' x_in interpret f': bounded_linear "if x \<in> s then f' x else (\<lambda>x. 0)"
    by (auto simp add: has_derivative_within)
  from g' interpret g': bounded_linear "if x \<in> t then g' x else (\<lambda>x. 0)"
    by (auto simp add: has_derivative_within)
  have bl: "bounded_linear (if x \<in> s then f' x else g' x)"
    using f'.scaleR f'.bounded f'.add g'.scaleR g'.bounded g'.add x_in
    by (unfold_locales; force)
  show ?thesis
    using f' g' closure_subset[of t] closure_subset[of s]
    unfolding has_derivative_within_If_eq
    by (intro conjI bl tendsto_If_within_closures x_in)
      (auto simp: has_derivative_within inverse_eq_divide connect connect' set_mp)
qed

lemma has_vector_derivative_If_within_closures:
  assumes x_in: "x \<in> s \<union> t"
  assumes "u = s \<union> t"
  assumes f': "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (f has_vector_derivative f' x) (at x within s \<union> (closure s \<inter> closure t))"
  assumes g': "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (g has_vector_derivative g' x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes connect: "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f' x = g' x"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_vector_derivative
    (if x \<in> s then f' x else g' x)) (at x within u)"
  unfolding has_vector_derivative_def assms
  using x_in
  apply (intro has_derivative_If_within_closures[where
        ?f' = "\<lambda>x a. a *\<^sub>R f' x" and ?g' = "\<lambda>x a. a *\<^sub>R g' x",
        THEN has_derivative_eq_rhs])
  subgoal by (rule f'[unfolded has_vector_derivative_def]; assumption)
  subgoal by (rule g'[unfolded has_vector_derivative_def]; assumption)
  by (auto simp: assms)

end
