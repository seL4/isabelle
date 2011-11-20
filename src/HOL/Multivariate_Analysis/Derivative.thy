(*  Title:                       HOL/Multivariate_Analysis/Derivative.thy
    Author:                      John Harrison
    Translation from HOL Light:  Robert Himmelmann, TU Muenchen
*)

header {* Multivariate calculus in Euclidean space. *}

theory Derivative
imports Brouwer_Fixpoint Operator_Norm
begin

(* Because I do not want to type this all the time *)
lemmas linear_linear = linear_conv_bounded_linear[THEN sym]

subsection {* Derivatives *}

text {* The definition is slightly tricky since we make it work over
  nets of a particular form. This lets us prove theorems generally and use 
  "at a" or "at a within s" for restriction to a set (1-sided on R etc.) *}

definition has_derivative :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a filter \<Rightarrow> bool)"
(infixl "(has'_derivative)" 12) where
 "(f has_derivative f') net \<equiv> bounded_linear f' \<and> ((\<lambda>y. (1 / (norm (y - netlimit net))) *\<^sub>R
   (f y - (f (netlimit net) + f'(y - netlimit net)))) ---> 0) net"

lemma derivative_linear[dest]:
  "(f has_derivative f') net \<Longrightarrow> bounded_linear f'"
  unfolding has_derivative_def by auto

lemma netlimit_at_vector:
  (* TODO: move *)
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
  thus ?thesis
    by (rule netlimit_within [of a UNIV, unfolded within_UNIV])
qed simp

lemma FDERIV_conv_has_derivative:
  shows "FDERIV f x :> f' = (f has_derivative f') (at x)"
  unfolding fderiv_def has_derivative_def netlimit_at_vector
  by (simp add: diff_diff_eq Lim_at_zero [where a=x]
    tendsto_norm_zero_iff [where 'b='b, symmetric])

lemma DERIV_conv_has_derivative:
  "(DERIV f x :> f') = (f has_derivative op * f') (at x)"
  unfolding deriv_fderiv FDERIV_conv_has_derivative
  by (subst mult_commute, rule refl)

text {* These are the only cases we'll care about, probably. *}

lemma has_derivative_within: "(f has_derivative f') (at x within s) \<longleftrightarrow>
         bounded_linear f' \<and> ((\<lambda>y. (1 / norm(y - x)) *\<^sub>R (f y - (f x + f' (y - x)))) ---> 0) (at x within s)"
  unfolding has_derivative_def and Lim by(auto simp add:netlimit_within)

lemma has_derivative_at: "(f has_derivative f') (at x) \<longleftrightarrow>
         bounded_linear f' \<and> ((\<lambda>y. (1 / (norm(y - x))) *\<^sub>R (f y - (f x + f' (y - x)))) ---> 0) (at x)"
  using has_derivative_within [of f f' x UNIV] by simp

text {* More explicit epsilon-delta forms. *}

lemma has_derivative_within':
  "(f has_derivative f')(at x within s) \<longleftrightarrow> bounded_linear f' \<and>
        (\<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. 0 < norm(x' - x) \<and> norm(x' - x) < d
        \<longrightarrow> norm(f x' - f x - f'(x' - x)) / norm(x' - x) < e)"
  unfolding has_derivative_within Lim_within dist_norm
  unfolding diff_0_right by (simp add: diff_diff_eq)

lemma has_derivative_at':
 "(f has_derivative f') (at x) \<longleftrightarrow> bounded_linear f' \<and>
   (\<forall>e>0. \<exists>d>0. \<forall>x'. 0 < norm(x' - x) \<and> norm(x' - x) < d
        \<longrightarrow> norm(f x' - f x - f'(x' - x)) / norm(x' - x) < e)"
  using has_derivative_within' [of f f' x UNIV] by simp

lemma has_derivative_at_within: "(f has_derivative f') (at x) \<Longrightarrow> (f has_derivative f') (at x within s)"
  unfolding has_derivative_within' has_derivative_at' by meson

lemma has_derivative_within_open:
  "a \<in> s \<Longrightarrow> open s \<Longrightarrow> ((f has_derivative f') (at a within s) \<longleftrightarrow> (f has_derivative f') (at a))"
  by (simp only: at_within_interior interior_open)

lemma has_derivative_right:
  fixes f :: "real \<Rightarrow> real" and y :: "real"
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

lemma bounded_linear_imp_linear: "bounded_linear f \<Longrightarrow> linear f" (* TODO: move elsewhere *)
proof -
  assume "bounded_linear f"
  then interpret f: bounded_linear f .
  show "linear f"
    by (simp add: f.add f.scaleR linear_def)
qed

lemma derivative_is_linear:
  "(f has_derivative f') net \<Longrightarrow> linear f'"
  by (rule derivative_linear [THEN bounded_linear_imp_linear])

subsubsection {* Combining theorems. *}

lemma has_derivative_id: "((\<lambda>x. x) has_derivative (\<lambda>h. h)) net"
  unfolding has_derivative_def
  by (simp add: bounded_linear_ident tendsto_const)

lemma has_derivative_const: "((\<lambda>x. c) has_derivative (\<lambda>h. 0)) net"
  unfolding has_derivative_def
  by (simp add: bounded_linear_zero tendsto_const)

lemma (in bounded_linear) has_derivative': "(f has_derivative f) net"
  unfolding has_derivative_def apply(rule,rule bounded_linear_axioms)
  unfolding diff by (simp add: tendsto_const)

lemma (in bounded_linear) bounded_linear: "bounded_linear f" ..

lemma (in bounded_linear) has_derivative:
  assumes "((\<lambda>x. g x) has_derivative (\<lambda>h. g' h)) net"
  shows "((\<lambda>x. f (g x)) has_derivative (\<lambda>h. f (g' h))) net"
  using assms unfolding has_derivative_def
  apply safe
  apply (erule bounded_linear_compose [OF local.bounded_linear])
  apply (drule local.tendsto)
  apply (simp add: local.scaleR local.diff local.add local.zero)
  done

lemmas scaleR_right_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_scaleR_right]

lemmas scaleR_left_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_scaleR_left]

lemmas inner_right_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_inner_right]

lemmas inner_left_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_inner_left]

lemmas mult_right_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_mult_right]

lemmas mult_left_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_mult_left]

lemmas euclidean_component_has_derivative =
  bounded_linear.has_derivative [OF bounded_linear_euclidean_component]

lemma has_derivative_neg:
  assumes "(f has_derivative f') net"
  shows "((\<lambda>x. -(f x)) has_derivative (\<lambda>h. -(f' h))) net"
  using scaleR_right_has_derivative [where r="-1", OF assms] by auto

lemma has_derivative_add:
  assumes "(f has_derivative f') net" and "(g has_derivative g') net"
  shows "((\<lambda>x. f(x) + g(x)) has_derivative (\<lambda>h. f'(h) + g'(h))) net"
proof-
  note as = assms[unfolded has_derivative_def]
  show ?thesis unfolding has_derivative_def apply(rule,rule bounded_linear_add)
    using tendsto_add[OF as(1)[THEN conjunct2] as(2)[THEN conjunct2]] and as
    by (auto simp add: algebra_simps)
qed

lemma has_derivative_add_const:
  "(f has_derivative f') net \<Longrightarrow> ((\<lambda>x. f x + c) has_derivative f') net"
  by (drule has_derivative_add, rule has_derivative_const, auto)

lemma has_derivative_sub:
  assumes "(f has_derivative f') net" and "(g has_derivative g') net"
  shows "((\<lambda>x. f(x) - g(x)) has_derivative (\<lambda>h. f'(h) - g'(h))) net"
  unfolding diff_minus by (intro has_derivative_add has_derivative_neg assms)

lemma has_derivative_setsum:
  assumes "finite s" and "\<forall>a\<in>s. ((f a) has_derivative (f' a)) net"
  shows "((\<lambda>x. setsum (\<lambda>a. f a x) s) has_derivative (\<lambda>h. setsum (\<lambda>a. f' a h) s)) net"
  using assms by (induct, simp_all add: has_derivative_const has_derivative_add)
text {* Somewhat different results for derivative of scalar multiplier. *}

(** move **)
lemma linear_vmul_component: (* TODO: delete *)
  assumes lf: "linear f"
  shows "linear (\<lambda>x. f x $$ k *\<^sub>R v)"
  using lf
  by (auto simp add: linear_def algebra_simps)

lemmas has_derivative_intros =
  has_derivative_id has_derivative_const
  has_derivative_add has_derivative_sub has_derivative_neg
  has_derivative_add_const
  scaleR_left_has_derivative scaleR_right_has_derivative
  inner_left_has_derivative inner_right_has_derivative
  euclidean_component_has_derivative

subsubsection {* Limit transformation for derivatives *}

lemma has_derivative_transform_within:
  assumes "0 < d" "x \<in> s" "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'" "(f has_derivative f') (at x within s)"
  shows "(g has_derivative f') (at x within s)"
  using assms(4) unfolding has_derivative_within apply- apply(erule conjE,rule,assumption)
  apply(rule Lim_transform_within[OF assms(1)]) defer apply assumption
  apply(rule,rule) apply(drule assms(3)[rule_format]) using assms(3)[rule_format, OF assms(2)] by auto

lemma has_derivative_transform_at:
  assumes "0 < d" "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'" "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using has_derivative_transform_within [of d x UNIV f g f'] assms by simp

lemma has_derivative_transform_within_open:
  assumes "open s" "x \<in> s" "\<forall>y\<in>s. f y = g y" "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using assms(4) unfolding has_derivative_at apply- apply(erule conjE,rule,assumption)
  apply(rule Lim_transform_within_open[OF assms(1,2)]) defer apply assumption
  apply(rule,rule) apply(drule assms(3)[rule_format]) using assms(3)[rule_format, OF assms(2)] by auto

subsection {* Differentiability *}

no_notation Deriv.differentiable (infixl "differentiable" 60)

definition differentiable :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool" (infixr "differentiable" 30) where
  "f differentiable net \<equiv> (\<exists>f'. (f has_derivative f') net)"

definition differentiable_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "differentiable'_on" 30) where
  "f differentiable_on s \<equiv> (\<forall>x\<in>s. f differentiable (at x within s))"

lemma differentiableI: "(f has_derivative f') net \<Longrightarrow> f differentiable net"
  unfolding differentiable_def by auto

lemma differentiable_at_withinI: "f differentiable (at x) \<Longrightarrow> f differentiable (at x within s)"
  unfolding differentiable_def using has_derivative_at_within by blast

lemma differentiable_within_open: (* TODO: delete *)
  assumes "a \<in> s" and "open s"
  shows "f differentiable (at a within s) \<longleftrightarrow> (f differentiable (at a))"
  using assms by (simp only: at_within_interior interior_open)

lemma differentiable_on_eq_differentiable_at:
  "open s \<Longrightarrow> (f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable at x))"
  unfolding differentiable_on_def
  by (auto simp add: at_within_interior interior_open)

lemma differentiable_transform_within:
  assumes "0 < d" and "x \<in> s" and "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'"
  assumes "f differentiable (at x within s)"
  shows "g differentiable (at x within s)"
  using assms(4) unfolding differentiable_def
  by (auto intro!: has_derivative_transform_within[OF assms(1-3)])

lemma differentiable_transform_at:
  assumes "0 < d" "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'" "f differentiable at x"
  shows "g differentiable at x"
  using assms(3) unfolding differentiable_def
  using has_derivative_transform_at[OF assms(1-2)] by auto

subsection {* Frechet derivative and Jacobian matrix. *}

definition "frechet_derivative f net = (SOME f'. (f has_derivative f') net)"

lemma frechet_derivative_works:
 "f differentiable net \<longleftrightarrow> (f has_derivative (frechet_derivative f net)) net"
  unfolding frechet_derivative_def differentiable_def and some_eq_ex[of "\<lambda> f' . (f has_derivative f') net"] ..

lemma linear_frechet_derivative:
  shows "f differentiable net \<Longrightarrow> linear(frechet_derivative f net)"
  unfolding frechet_derivative_works has_derivative_def
  by (auto intro: bounded_linear_imp_linear)

subsection {* Differentiability implies continuity *}

lemma Lim_mul_norm_within:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> 0) (at a within s) \<Longrightarrow> ((\<lambda>x. norm(x - a) *\<^sub>R f(x)) ---> 0) (at a within s)"
  unfolding Lim_within apply(rule,rule)
  apply(erule_tac x=e in allE,erule impE,assumption,erule exE,erule conjE)
  apply(rule_tac x="min d 1" in exI) apply rule defer
  apply(rule,erule_tac x=x in ballE) unfolding dist_norm diff_0_right
  by(auto intro!: mult_strict_mono[of _ "1::real", unfolded mult_1_left])

lemma differentiable_imp_continuous_within:
  assumes "f differentiable (at x within s)" 
  shows "continuous (at x within s) f"
proof-
  from assms guess f' unfolding differentiable_def has_derivative_within ..
  note f'=this
  then interpret bounded_linear f' by auto
  have *:"\<And>xa. x\<noteq>xa \<Longrightarrow> (f' \<circ> (\<lambda>y. y - x)) xa + norm (xa - x) *\<^sub>R ((1 / norm (xa - x)) *\<^sub>R (f xa - (f x + f' (xa - x)))) - ((f' \<circ> (\<lambda>y. y - x)) x + 0) = f xa - f x"
    using zero by auto
  have **:"continuous (at x within s) (f' \<circ> (\<lambda>y. y - x))"
    apply(rule continuous_within_compose) apply(rule continuous_intros)+
    by(rule linear_continuous_within[OF f'[THEN conjunct1]])
  show ?thesis unfolding continuous_within
    using f'[THEN conjunct2, THEN Lim_mul_norm_within]
    apply- apply(drule tendsto_add)
    apply(rule **[unfolded continuous_within])
    unfolding Lim_within and dist_norm
    apply (rule, rule)
    apply (erule_tac x=e in allE)
    apply (erule impE | assumption)+
    apply (erule exE, rule_tac x=d in exI)
    by (auto simp add: zero *)
qed

lemma differentiable_imp_continuous_at:
  "f differentiable at x \<Longrightarrow> continuous (at x) f"
 by(rule differentiable_imp_continuous_within[of _ x UNIV, unfolded within_UNIV])

lemma differentiable_imp_continuous_on:
  "f differentiable_on s \<Longrightarrow> continuous_on s f"
  unfolding differentiable_on_def continuous_on_eq_continuous_within
  using differentiable_imp_continuous_within by blast

lemma has_derivative_within_subset:
 "(f has_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (f has_derivative f') (at x within t)"
  unfolding has_derivative_within using Lim_within_subset by blast

lemma differentiable_within_subset:
  "f differentiable (at x within t) \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f differentiable (at x within s)"
  unfolding differentiable_def using has_derivative_within_subset by blast

lemma differentiable_on_subset:
  "f differentiable_on t \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f differentiable_on s"
  unfolding differentiable_on_def using differentiable_within_subset by blast

lemma differentiable_on_empty: "f differentiable_on {}"
  unfolding differentiable_on_def by auto

text {* Several results are easier using a "multiplied-out" variant.
(I got this idea from Dieudonne's proof of the chain rule). *}

lemma has_derivative_within_alt:
 "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
  (\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm(y - x) < d \<longrightarrow> norm(f(y) - f(x) - f'(y - x)) \<le> e * norm(y - x))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
    unfolding has_derivative_within apply-apply(erule conjE,rule,assumption)
    unfolding Lim_within
    apply(rule,erule_tac x=e in allE,rule,erule impE,assumption)
    apply(erule exE,rule_tac x=d in exI)
    apply(erule conjE,rule,assumption,rule,rule)
  proof-
    fix x y e d assume as:"0 < e" "0 < d" "norm (y - x) < d" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow>
      dist ((1 / norm (xa - x)) *\<^sub>R (f xa - (f x + f' (xa - x)))) 0 < e" "y \<in> s" "bounded_linear f'"
    then interpret bounded_linear f' by auto
    show "norm (f y - f x - f' (y - x)) \<le> e * norm (y - x)" proof(cases "y=x")
      case True thus ?thesis using `bounded_linear f'` by(auto simp add: zero)
    next
      case False hence "norm (f y - (f x + f' (y - x))) < e * norm (y - x)" using as(4)[rule_format, OF `y\<in>s`]
        unfolding dist_norm diff_0_right using as(3)
        using pos_divide_less_eq[OF False[unfolded dist_nz], unfolded dist_norm]
        by (auto simp add: linear_0 linear_sub)
      thus ?thesis by(auto simp add:algebra_simps)
    qed
  qed
next
  assume ?rhs thus ?lhs unfolding has_derivative_within Lim_within
    apply-apply(erule conjE,rule,assumption)
    apply(rule,erule_tac x="e/2" in allE,rule,erule impE) defer
    apply(erule exE,rule_tac x=d in exI)
    apply(erule conjE,rule,assumption,rule,rule)
    unfolding dist_norm diff_0_right norm_scaleR
    apply(erule_tac x=xa in ballE,erule impE)
  proof-
    fix e d y assume "bounded_linear f'" "0 < e" "0 < d" "y \<in> s" "0 < norm (y - x) \<and> norm (y - x) < d"
        "norm (f y - f x - f' (y - x)) \<le> e / 2 * norm (y - x)"
    thus "\<bar>1 / norm (y - x)\<bar> * norm (f y - (f x + f' (y - x))) < e"
      apply(rule_tac le_less_trans[of _ "e/2"])
      by(auto intro!:mult_imp_div_pos_le simp add:algebra_simps)
  qed auto
qed

lemma has_derivative_at_alt:
  "(f has_derivative f') (at x) \<longleftrightarrow> bounded_linear f' \<and>
  (\<forall>e>0. \<exists>d>0. \<forall>y. norm(y - x) < d \<longrightarrow> norm(f y - f x - f'(y - x)) \<le> e * norm(y - x))"
  using has_derivative_within_alt[where s=UNIV] by simp

subsection {* The chain rule. *}

lemma diff_chain_within:
  assumes "(f has_derivative f') (at x within s)"
  assumes "(g has_derivative g') (at (f x) within (f ` s))"
  shows "((g o f) has_derivative (g' o f'))(at x within s)"
  unfolding has_derivative_within_alt
  apply(rule,rule bounded_linear_compose[unfolded o_def[THEN sym]])
  apply(rule assms(2)[unfolded has_derivative_def,THEN conjE],assumption)
  apply(rule assms(1)[unfolded has_derivative_def,THEN conjE],assumption)
proof(rule,rule)
  note assms = assms[unfolded has_derivative_within_alt]
  fix e::real assume "0<e"
  guess B1 using bounded_linear.pos_bounded[OF assms(1)[THEN conjunct1, rule_format]] .. note B1 = this
  guess B2 using bounded_linear.pos_bounded[OF assms(2)[THEN conjunct1, rule_format]] .. note B2 = this
  have *:"e / 2 / B2 > 0" using `e>0` B2 apply-apply(rule divide_pos_pos) by auto
  guess d1 using assms(1)[THEN conjunct2, rule_format, OF *] .. note d1 = this
  have *:"e / 2 / (1 + B1) > 0" using `e>0` B1 apply-apply(rule divide_pos_pos) by auto
  guess de using assms(2)[THEN conjunct2, rule_format, OF *] .. note de = this
  guess d2 using assms(1)[THEN conjunct2, rule_format, OF zero_less_one] .. note d2 = this

  def d0 \<equiv> "(min d1 d2)/2" have d0:"d0>0" "d0 < d1" "d0 < d2" unfolding d0_def using d1 d2 by auto
  def d \<equiv> "(min d0 (de / (B1 + 1))) / 2" have "de * 2 / (B1 + 1) > de / (B1 + 1)" apply(rule divide_strict_right_mono) using B1 de by auto
  hence d:"d>0" "d < d1" "d < d2" "d < (de / (B1 + 1))" unfolding d_def using d0 d1 d2 de B1 by(auto intro!: divide_pos_pos simp add:min_less_iff_disj not_less)

  show "\<exists>d>0. \<forall>y\<in>s. norm (y - x) < d \<longrightarrow> norm ((g \<circ> f) y - (g \<circ> f) x - (g' \<circ> f') (y - x)) \<le> e * norm (y - x)" apply(rule_tac x=d in exI)
    proof(rule,rule `d>0`,rule,rule) 
    fix y assume as:"y \<in> s" "norm (y - x) < d"
    hence 1:"norm (f y - f x - f' (y - x)) \<le> min (norm (y - x)) (e / 2 / B2 * norm (y - x))" using d1 d2 d by auto

    have "norm (f y - f x) \<le> norm (f y - f x - f' (y - x)) + norm (f' (y - x))"
      using norm_triangle_sub[of "f y - f x" "f' (y - x)"]
      by(auto simp add:algebra_simps)
    also have "\<dots> \<le> norm (f y - f x - f' (y - x)) + B1 * norm (y - x)"
      apply(rule add_left_mono) using B1 by(auto simp add:algebra_simps)
    also have "\<dots> \<le> min (norm (y - x)) (e / 2 / B2 * norm (y - x)) + B1 * norm (y - x)"
      apply(rule add_right_mono) using d1 d2 d as by auto
    also have "\<dots> \<le> norm (y - x) + B1 * norm (y - x)" by auto
    also have "\<dots> = norm (y - x) * (1 + B1)" by(auto simp add:field_simps)
    finally have 3:"norm (f y - f x) \<le> norm (y - x) * (1 + B1)" by auto 

    hence "norm (f y - f x) \<le> d * (1 + B1)" apply-
      apply(rule order_trans,assumption,rule mult_right_mono)
      using as B1 by auto 
    also have "\<dots> < de" using d B1 by(auto simp add:field_simps) 
    finally have "norm (g (f y) - g (f x) - g' (f y - f x)) \<le> e / 2 / (1 + B1) * norm (f y - f x)"
      apply-apply(rule de[THEN conjunct2,rule_format])
      using `y\<in>s` using d as by auto 
    also have "\<dots> = (e / 2) * (1 / (1 + B1) * norm (f y - f x))" by auto 
    also have "\<dots> \<le> e / 2 * norm (y - x)" apply(rule mult_left_mono)
      using `e>0` and 3 using B1 and `e>0` by(auto simp add:divide_le_eq)
    finally have 4:"norm (g (f y) - g (f x) - g' (f y - f x)) \<le> e / 2 * norm (y - x)" by auto
    
    interpret g': bounded_linear g' using assms(2) by auto
    interpret f': bounded_linear f' using assms(1) by auto
    have "norm (- g' (f' (y - x)) + g' (f y - f x)) = norm (g' (f y - f x - f' (y - x)))"
      by(auto simp add:algebra_simps f'.diff g'.diff g'.add)
    also have "\<dots> \<le> B2 * norm (f y - f x - f' (y - x))" using B2
      by (auto simp add: algebra_simps)
    also have "\<dots> \<le> B2 * (e / 2 / B2 * norm (y - x))"
      apply (rule mult_left_mono) using as d1 d2 d B2 by auto 
    also have "\<dots> \<le> e / 2 * norm (y - x)" using B2 by auto
    finally have 5:"norm (- g' (f' (y - x)) + g' (f y - f x)) \<le> e / 2 * norm (y - x)" by auto
    
    have "norm (g (f y) - g (f x) - g' (f y - f x)) + norm (g (f y) - g (f x) - g' (f' (y - x)) - (g (f y) - g (f x) - g' (f y - f x))) \<le> e * norm (y - x)"
      using 5 4 by auto
    thus "norm ((g \<circ> f) y - (g \<circ> f) x - (g' \<circ> f') (y - x)) \<le> e * norm (y - x)"
      unfolding o_def apply- apply(rule order_trans, rule norm_triangle_sub)
      by assumption
  qed
qed

lemma diff_chain_at:
  "(f has_derivative f') (at x) \<Longrightarrow> (g has_derivative g') (at (f x)) \<Longrightarrow> ((g o f) has_derivative (g' o f')) (at x)"
  using diff_chain_within[of f f' x UNIV g g']
  using has_derivative_within_subset[of g g' "f x" UNIV "range f"]
  by simp

subsection {* Composition rules stated just for differentiability. *}

lemma differentiable_const [intro]:
  "(\<lambda>z. c) differentiable (net::'a::real_normed_vector filter)"
  unfolding differentiable_def using has_derivative_const by auto

lemma differentiable_id [intro]:
  "(\<lambda>z. z) differentiable (net::'a::real_normed_vector filter)"
    unfolding differentiable_def using has_derivative_id by auto

lemma differentiable_cmul [intro]:
  "f differentiable net \<Longrightarrow>
  (\<lambda>x. c *\<^sub>R f(x)) differentiable (net::'a::real_normed_vector filter)"
  unfolding differentiable_def
  apply(erule exE, drule scaleR_right_has_derivative) by auto

lemma differentiable_neg [intro]:
  "f differentiable net \<Longrightarrow>
  (\<lambda>z. -(f z)) differentiable (net::'a::real_normed_vector filter)"
  unfolding differentiable_def
  apply(erule exE, drule has_derivative_neg) by auto

lemma differentiable_add: "f differentiable net \<Longrightarrow> g differentiable net
   \<Longrightarrow> (\<lambda>z. f z + g z) differentiable (net::'a::real_normed_vector filter)"
    unfolding differentiable_def apply(erule exE)+ apply(rule_tac x="\<lambda>z. f' z + f'a z" in exI)
    apply(rule has_derivative_add) by auto

lemma differentiable_sub: "f differentiable net \<Longrightarrow> g differentiable net
  \<Longrightarrow> (\<lambda>z. f z - g z) differentiable (net::'a::real_normed_vector filter)"
  unfolding differentiable_def apply(erule exE)+
  apply(rule_tac x="\<lambda>z. f' z - f'a z" in exI)
  apply(rule has_derivative_sub) by auto

lemma differentiable_setsum:
  assumes "finite s" "\<forall>a\<in>s. (f a) differentiable net"
  shows "(\<lambda>x. setsum (\<lambda>a. f a x) s) differentiable net"
proof-
  guess f' using bchoice[OF assms(2)[unfolded differentiable_def]] ..
  thus ?thesis unfolding differentiable_def apply-
    apply(rule,rule has_derivative_setsum[where f'=f'],rule assms(1)) by auto
qed

lemma differentiable_setsum_numseg:
  shows "\<forall>i. m \<le> i \<and> i \<le> n \<longrightarrow> (f i) differentiable net \<Longrightarrow> (\<lambda>x. setsum (\<lambda>a. f a x) {m::nat..n}) differentiable net"
  apply(rule differentiable_setsum) using finite_atLeastAtMost[of n m] by auto

lemma differentiable_chain_at:
  "f differentiable (at x) \<Longrightarrow> g differentiable (at(f x)) \<Longrightarrow> (g o f) differentiable (at x)"
  unfolding differentiable_def by(meson diff_chain_at)

lemma differentiable_chain_within:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable (at(f x) within (f ` s))
   \<Longrightarrow> (g o f) differentiable (at x within s)"
  unfolding differentiable_def by(meson diff_chain_within)

subsection {* Uniqueness of derivative *}

text {*
 The general result is a bit messy because we need approachability of the
 limit point from any direction. But OK for nontrivial intervals etc.
*}
    
lemma frechet_derivative_unique_within:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_derivative f') (at x within s)"
  assumes "(f has_derivative f'') (at x within s)"
  assumes "(\<forall>i<DIM('a). \<forall>e>0. \<exists>d. 0 < abs(d) \<and> abs(d) < e \<and> (x + d *\<^sub>R basis i) \<in> s)"
  shows "f' = f''"
proof-
  note as = assms(1,2)[unfolded has_derivative_def]
  then interpret f': bounded_linear f' by auto
  from as interpret f'': bounded_linear f'' by auto
  have "x islimpt s" unfolding islimpt_approachable
  proof(rule,rule)
    fix e::real assume "0<e" guess d
      using assms(3)[rule_format,OF DIM_positive `e>0`] ..
    thus "\<exists>x'\<in>s. x' \<noteq> x \<and> dist x' x < e"
      apply(rule_tac x="x + d *\<^sub>R basis 0" in bexI)
      unfolding dist_norm by auto
  qed
  hence *:"netlimit (at x within s) = x" apply-apply(rule netlimit_within)
    unfolding trivial_limit_within by simp
  show ?thesis  apply(rule linear_eq_stdbasis)
    unfolding linear_conv_bounded_linear
    apply(rule as(1,2)[THEN conjunct1])+
  proof(rule,rule,rule ccontr)
    fix i assume i:"i<DIM('a)" def e \<equiv> "norm (f' (basis i) - f'' (basis i))"
    assume "f' (basis i) \<noteq> f'' (basis i)"
    hence "e>0" unfolding e_def by auto
    guess d using tendsto_diff [OF as(1,2)[THEN conjunct2], unfolded * Lim_within,rule_format,OF `e>0`] .. note d=this
    guess c using assms(3)[rule_format,OF i d[THEN conjunct1]] .. note c=this
    have *:"norm (- ((1 / \<bar>c\<bar>) *\<^sub>R f' (c *\<^sub>R basis i)) + (1 / \<bar>c\<bar>) *\<^sub>R f'' (c *\<^sub>R basis i)) = norm ((1 / abs c) *\<^sub>R (- (f' (c *\<^sub>R basis i)) + f'' (c *\<^sub>R basis i)))"
      unfolding scaleR_right_distrib by auto
    also have "\<dots> = norm ((1 / abs c) *\<^sub>R (c *\<^sub>R (- (f' (basis i)) + f'' (basis i))))"  
      unfolding f'.scaleR f''.scaleR
      unfolding scaleR_right_distrib scaleR_minus_right by auto
    also have "\<dots> = e" unfolding e_def using c[THEN conjunct1]
      using norm_minus_cancel[of "f' (basis i) - f'' (basis i)"]
      by (auto simp add: add.commute ab_diff_minus)
    finally show False using c
      using d[THEN conjunct2,rule_format,of "x + c *\<^sub>R basis i"]
      unfolding dist_norm
      unfolding f'.scaleR f''.scaleR f'.add f''.add f'.diff f''.diff
        scaleR_scaleR scaleR_right_diff_distrib scaleR_right_distrib
      using i by auto
  qed
qed

lemma frechet_derivative_unique_at:
  shows "(f has_derivative f') (at x) \<Longrightarrow> (f has_derivative f'') (at x) \<Longrightarrow> f' = f''"
  unfolding FDERIV_conv_has_derivative [symmetric]
  by (rule FDERIV_unique)

lemma continuous_isCont: "isCont f x = continuous (at x) f"
  unfolding isCont_def LIM_def
  unfolding continuous_at Lim_at unfolding dist_nz by auto

lemma frechet_derivative_unique_within_closed_interval:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<forall>i<DIM('a). a$$i < b$$i" "x \<in> {a..b}" (is "x\<in>?I")
  assumes "(f has_derivative f' ) (at x within {a..b})"
  assumes "(f has_derivative f'') (at x within {a..b})"
  shows "f' = f''"
  apply(rule frechet_derivative_unique_within)
  apply(rule assms(3,4))+
proof(rule,rule,rule,rule)
  fix e::real and i assume "e>0" and i:"i<DIM('a)"
  thus "\<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> x + d *\<^sub>R basis i \<in> {a..b}"
  proof(cases "x$$i=a$$i")
    case True thus ?thesis
      apply(rule_tac x="(min (b$$i - a$$i)  e) / 2" in exI)
      using assms(1)[THEN spec[where x=i]] and `e>0` and assms(2)
      unfolding mem_interval euclidean_simps
      using i by (auto simp add: field_simps)
  next note * = assms(2)[unfolded mem_interval,THEN spec[where x=i]]
    case False moreover have "a $$ i < x $$ i" using False * by auto
    moreover {
      have "a $$ i * 2 + min (x $$ i - a $$ i) e \<le> a$$i *2 + x$$i - a$$i"
        by auto
      also have "\<dots> = a$$i + x$$i" by auto
      also have "\<dots> \<le> 2 * x$$i" using * by auto 
      finally have "a $$ i * 2 + min (x $$ i - a $$ i) e \<le> x $$ i * 2" by auto
    }
    moreover have "min (x $$ i - a $$ i) e \<ge> 0" using * and `e>0` by auto
    hence "x $$ i * 2 \<le> b $$ i * 2 + min (x $$ i - a $$ i) e" using * by auto
    ultimately show ?thesis
      apply(rule_tac x="- (min (x$$i - a$$i) e) / 2" in exI)
      using assms(1)[THEN spec[where x=i]] and `e>0` and assms(2)
      unfolding mem_interval euclidean_simps
      using i by (auto simp add: field_simps)
  qed
qed

lemma frechet_derivative_unique_within_open_interval:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "x \<in> {a<..<b}"
  assumes "(f has_derivative f' ) (at x within {a<..<b})"
  assumes "(f has_derivative f'') (at x within {a<..<b})"
  shows "f' = f''"
proof -
  from assms(1) have *: "at x within {a<..<b} = at x"
    by (simp add: at_within_interior interior_open open_interval)
  from assms(2,3) [unfolded *] show "f' = f''"
    by (rule frechet_derivative_unique_at)
qed

lemma frechet_derivative_at:
  shows "(f has_derivative f') (at x) \<Longrightarrow> (f' = frechet_derivative f (at x))"
  apply(rule frechet_derivative_unique_at[of f],assumption)
  unfolding frechet_derivative_works[THEN sym] using differentiable_def by auto

lemma frechet_derivative_within_closed_interval:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<forall>i<DIM('a). a$$i < b$$i" and "x \<in> {a..b}"
  assumes "(f has_derivative f') (at x within {a.. b})"
  shows "frechet_derivative f (at x within {a.. b}) = f'"
  apply(rule frechet_derivative_unique_within_closed_interval[where f=f]) 
  apply(rule assms(1,2))+ unfolding frechet_derivative_works[THEN sym]
  unfolding differentiable_def using assms(3) by auto 

subsection {* The traditional Rolle theorem in one dimension. *}

lemma linear_componentwise:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lf: "linear f"
  shows "(f x) $$ j = (\<Sum>i<DIM('a). (x$$i) * (f (basis i)$$j))" (is "?lhs = ?rhs")
proof -
  have fA: "finite {..<DIM('a)}" by simp
  have "?rhs = (\<Sum>i<DIM('a). x$$i *\<^sub>R f (basis i))$$j"
    by simp
  then show ?thesis
    unfolding linear_setsum_mul[OF lf fA, symmetric]
    unfolding euclidean_representation[symmetric] ..
qed

text {* We do not introduce @{text jacobian}, which is defined on matrices, instead we use
  the unfolding of it. *}

lemma jacobian_works:
  "(f::('a::euclidean_space) \<Rightarrow> ('b::euclidean_space)) differentiable net \<longleftrightarrow>
   (f has_derivative (\<lambda>h. \<chi>\<chi> i.
      \<Sum>j<DIM('a). frechet_derivative f net (basis j) $$ i * h $$ j)) net"
  (is "?differentiable \<longleftrightarrow> (f has_derivative (\<lambda>h. \<chi>\<chi> i. ?SUM h i)) net")
proof
  assume *: ?differentiable
  { fix h i
    have "?SUM h i = frechet_derivative f net h $$ i" using *
      by (auto intro!: setsum_cong
               simp: linear_componentwise[of _ h i] linear_frechet_derivative) }
  thus "(f has_derivative (\<lambda>h. \<chi>\<chi> i. ?SUM h i)) net"
    using * by (simp add: frechet_derivative_works)
qed (auto intro!: differentiableI)

lemma differential_zero_maxmin_component:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k < DIM('b)"
    and ball: "0 < e" "((\<forall>y \<in> ball x e. (f y)$$k \<le> (f x)$$k) \<or> (\<forall>y\<in>ball x e. (f x)$$k \<le> (f y)$$k))"
    and diff: "f differentiable (at x)"
  shows "(\<chi>\<chi> j. frechet_derivative f (at x) (basis j) $$ k) = (0::'a)" (is "?D k = 0")
proof (rule ccontr)
  assume "?D k \<noteq> 0"
  then obtain j where j: "?D k $$ j \<noteq> 0" "j < DIM('a)"
    unfolding euclidean_lambda_beta euclidean_eq[of _ "0::'a"] by auto
  hence *: "\<bar>?D k $$ j\<bar> / 2 > 0" by auto
  note as = diff[unfolded jacobian_works has_derivative_at_alt]
  guess e' using as[THEN conjunct2, rule_format, OF *] .. note e' = this
  guess d using real_lbound_gt_zero[OF ball(1) e'[THEN conjunct1]] .. note d = this
  { fix c assume "abs c \<le> d"
    hence *:"norm (x + c *\<^sub>R basis j - x) < e'" using norm_basis[of j] d by auto
    let ?v = "(\<chi>\<chi> i. \<Sum>l<DIM('a). ?D i $$ l * (c *\<^sub>R basis j :: 'a) $$ l)"
    have if_dist: "\<And> P a b c. a * (if P then b else c) = (if P then a * b else a * c)" by auto
    have "\<bar>(f (x + c *\<^sub>R basis j) - f x - ?v) $$ k\<bar> \<le>
        norm (f (x + c *\<^sub>R basis j) - f x - ?v)" by (rule component_le_norm)
    also have "\<dots> \<le> \<bar>?D k $$ j\<bar> / 2 * \<bar>c\<bar>"
      using e'[THEN conjunct2, rule_format, OF *] and norm_basis[of j] by fastforce
    finally have "\<bar>(f (x + c *\<^sub>R basis j) - f x - ?v) $$ k\<bar> \<le> \<bar>?D k $$ j\<bar> / 2 * \<bar>c\<bar>" by simp
    hence "\<bar>f (x + c *\<^sub>R basis j) $$ k - f x $$ k - c * ?D k $$ j\<bar> \<le> \<bar>?D k $$ j\<bar> / 2 * \<bar>c\<bar>"
      unfolding euclidean_simps euclidean_lambda_beta using j k
      by (simp add: if_dist setsum_cases field_simps) } note * = this
  have "x + d *\<^sub>R basis j \<in> ball x e" "x - d *\<^sub>R basis j \<in> ball x e"
    unfolding mem_ball dist_norm using norm_basis[of j] d by auto
  hence **:"((f (x - d *\<^sub>R basis j))$$k \<le> (f x)$$k \<and> (f (x + d *\<^sub>R basis j))$$k \<le> (f x)$$k) \<or>
         ((f (x - d *\<^sub>R basis j))$$k \<ge> (f x)$$k \<and> (f (x + d *\<^sub>R basis j))$$k \<ge> (f x)$$k)" using ball by auto
  have ***: "\<And>y y1 y2 d dx::real.
    (y1\<le>y\<and>y2\<le>y) \<or> (y\<le>y1\<and>y\<le>y2) \<Longrightarrow> d < abs dx \<Longrightarrow> abs(y1 - y - - dx) \<le> d \<Longrightarrow> (abs (y2 - y - dx) \<le> d) \<Longrightarrow> False" by arith
  show False apply(rule ***[OF **, where dx="d * ?D k $$ j" and d="\<bar>?D k $$ j\<bar> / 2 * \<bar>d\<bar>"])
    using *[of "-d"] and *[of d] and d[THEN conjunct1] and j
    unfolding mult_minus_left
    unfolding abs_mult diff_minus_eq_add scaleR_minus_left
    unfolding algebra_simps by (auto intro: mult_pos_pos)
qed

text {* In particular if we have a mapping into @{typ "real"}. *}

lemma differential_zero_maxmin:
  fixes f::"'a\<Colon>euclidean_space \<Rightarrow> real"
  assumes "x \<in> s" "open s"
  and deriv: "(f has_derivative f') (at x)"
  and mono: "(\<forall>y\<in>s. f y \<le> f x) \<or> (\<forall>y\<in>s. f x \<le> f y)"
  shows "f' = (\<lambda>v. 0)"
proof -
  obtain e where e:"e>0" "ball x e \<subseteq> s"
    using `open s`[unfolded open_contains_ball] and `x \<in> s` by auto
  with differential_zero_maxmin_component[where 'b=real, of 0 e x f, simplified]
  have "(\<chi>\<chi> j. frechet_derivative f (at x) (basis j)) = (0::'a)"
    unfolding differentiable_def using mono deriv by auto
  with frechet_derivative_at[OF deriv, symmetric]
  have "\<forall>i<DIM('a). f' (basis i) = 0"
    by (simp add: euclidean_eq[of _ "0::'a"])
  with derivative_is_linear[OF deriv, THEN linear_componentwise, of _ 0]
  show ?thesis by (simp add: fun_eq_iff)
qed

lemma rolle: fixes f::"real\<Rightarrow>real"
  assumes "a < b" and "f a = f b" and "continuous_on {a..b} f"
  assumes "\<forall>x\<in>{a<..<b}. (f has_derivative f'(x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. f' x = (\<lambda>v. 0)"
proof-
  have "\<exists>x\<in>{a<..<b}. ((\<forall>y\<in>{a<..<b}. f x \<le> f y) \<or> (\<forall>y\<in>{a<..<b}. f y \<le> f x))"
  proof-
    have "(a + b) / 2 \<in> {a .. b}" using assms(1) by auto
    hence *:"{a .. b}\<noteq>{}" by auto
    guess d using continuous_attains_sup[OF compact_interval * assms(3)] .. note d=this
    guess c using continuous_attains_inf[OF compact_interval * assms(3)] .. note c=this
    show ?thesis
    proof(cases "d\<in>{a<..<b} \<or> c\<in>{a<..<b}")
      case True thus ?thesis
        apply(erule_tac disjE) apply(rule_tac x=d in bexI)
        apply(rule_tac[3] x=c in bexI)
        using d c by auto
    next
      def e \<equiv> "(a + b) /2"
      case False hence "f d = f c" using d c assms(2) by auto
      hence "\<And>x. x\<in>{a..b} \<Longrightarrow> f x = f d"
        using c d apply- apply(erule_tac x=x in ballE)+ by auto
      thus ?thesis
        apply(rule_tac x=e in bexI) unfolding e_def using assms(1) by auto
    qed
  qed
  then guess x .. note x=this
  hence "f' x = (\<lambda>v. 0)"
    apply(rule_tac differential_zero_maxmin[of x "{a<..<b}" f "f' x"])
    defer apply(rule open_interval)
    apply(rule assms(4)[unfolded has_derivative_at[THEN sym],THEN bspec[where x=x]],assumption)
    unfolding o_def apply(erule disjE,rule disjI2) by auto
  thus ?thesis apply(rule_tac x=x in bexI) unfolding o_def apply rule
    apply(drule_tac x=v in fun_cong) using x(1) by auto
qed

subsection {* One-dimensional mean value theorem. *}

lemma mvt: fixes f::"real \<Rightarrow> real"
  assumes "a < b" and "continuous_on {a .. b} f"
  assumes "\<forall>x\<in>{a<..<b}. (f has_derivative (f' x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. (f b - f a = (f' x) (b - a))"
proof-
  have "\<exists>x\<in>{a<..<b}. (\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa) = (\<lambda>v. 0)"
    apply(rule rolle[OF assms(1), of "\<lambda>x. f x - (f b - f a) / (b - a) * x"])
    defer
    apply(rule continuous_on_intros assms(2))+
  proof
    fix x assume x:"x \<in> {a<..<b}"
    show "((\<lambda>x. f x - (f b - f a) / (b - a) * x) has_derivative (\<lambda>xa. f' x xa - (f b - f a) / (b - a) * xa)) (at x)"
      by (intro has_derivative_intros assms(3)[rule_format,OF x]
        mult_right_has_derivative)
  qed(insert assms(1), auto simp add:field_simps)
  then guess x ..
  thus ?thesis apply(rule_tac x=x in bexI)
    apply(drule fun_cong[of _ _ "b - a"]) by auto
qed

lemma mvt_simple:
  fixes f::"real \<Rightarrow> real"
  assumes "a<b" and "\<forall>x\<in>{a..b}. (f has_derivative f' x) (at x within {a..b})"
  shows "\<exists>x\<in>{a<..<b}. f b - f a = f' x (b - a)"
  apply(rule mvt)
  apply(rule assms(1), rule differentiable_imp_continuous_on)
  unfolding differentiable_on_def differentiable_def defer
proof
  fix x assume x:"x \<in> {a<..<b}" show "(f has_derivative f' x) (at x)"
    unfolding has_derivative_within_open[OF x open_interval,THEN sym] 
    apply(rule has_derivative_within_subset)
    apply(rule assms(2)[rule_format])
    using x by auto
qed(insert assms(2), auto)

lemma mvt_very_simple:
  fixes f::"real \<Rightarrow> real"
  assumes "a \<le> b" and "\<forall>x\<in>{a..b}. (f has_derivative f'(x)) (at x within {a..b})"
  shows "\<exists>x\<in>{a..b}. f b - f a = f' x (b - a)"
proof (cases "a = b")
  interpret bounded_linear "f' b" using assms(2) assms(1) by auto
  case True thus ?thesis apply(rule_tac x=a in bexI)
    using assms(2)[THEN bspec[where x=a]] unfolding has_derivative_def
    unfolding True using zero by auto next
  case False thus ?thesis using mvt_simple[OF _ assms(2)] using assms(1) by auto
qed

text {* A nice generalization (see Havin's proof of 5.19 from Rudin's book). *}

lemma mvt_general:
  fixes f::"real\<Rightarrow>'a::euclidean_space"
  assumes "a<b" and "continuous_on {a..b} f"
  assumes "\<forall>x\<in>{a<..<b}. (f has_derivative f'(x)) (at x)"
  shows "\<exists>x\<in>{a<..<b}. norm(f b - f a) \<le> norm(f'(x) (b - a))"
proof-
  have "\<exists>x\<in>{a<..<b}. (op \<bullet> (f b - f a) \<circ> f) b - (op \<bullet> (f b - f a) \<circ> f) a = (f b - f a) \<bullet> f' x (b - a)"
    apply(rule mvt) apply(rule assms(1))
    apply(rule continuous_on_inner continuous_on_intros assms(2))+
    unfolding o_def apply(rule,rule has_derivative_intros)
    using assms(3) by auto
  then guess x .. note x=this
  show ?thesis proof(cases "f a = f b")
    case False
    have "norm (f b - f a) * norm (f b - f a) = norm (f b - f a)^2"
      by (simp add: power2_eq_square)
    also have "\<dots> = (f b - f a) \<bullet> (f b - f a)" unfolding power2_norm_eq_inner ..
    also have "\<dots> = (f b - f a) \<bullet> f' x (b - a)"
      using x unfolding inner_simps by (auto simp add: inner_diff_left)
    also have "\<dots> \<le> norm (f b - f a) * norm (f' x (b - a))"
      by (rule norm_cauchy_schwarz)
    finally show ?thesis using False x(1)
      by (auto simp add: real_mult_left_cancel)
  next
    case True thus ?thesis using assms(1)
      apply (rule_tac x="(a + b) /2" in bexI) by auto
  qed
qed

text {* Still more general bound theorem. *}

lemma differentiable_bound:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "convex s" and "\<forall>x\<in>s. (f has_derivative f'(x)) (at x within s)"
  assumes "\<forall>x\<in>s. onorm(f' x) \<le> B" and x:"x\<in>s" and y:"y\<in>s"
  shows "norm(f x - f y) \<le> B * norm(x - y)"
proof-
  let ?p = "\<lambda>u. x + u *\<^sub>R (y - x)"
  have *:"\<And>u. u\<in>{0..1} \<Longrightarrow> x + u *\<^sub>R (y - x) \<in> s"
    using assms(1)[unfolded convex_alt,rule_format,OF x y]
    unfolding scaleR_left_diff_distrib scaleR_right_diff_distrib
    by (auto simp add: algebra_simps)
  hence 1:"continuous_on {0..1} (f \<circ> ?p)" apply-
    apply(rule continuous_on_intros)+
    unfolding continuous_on_eq_continuous_within
    apply(rule,rule differentiable_imp_continuous_within)
    unfolding differentiable_def apply(rule_tac x="f' xa" in exI)
    apply(rule has_derivative_within_subset)
    apply(rule assms(2)[rule_format]) by auto
  have 2:"\<forall>u\<in>{0<..<1}. ((f \<circ> ?p) has_derivative f' (x + u *\<^sub>R (y - x)) \<circ> (\<lambda>u. 0 + u *\<^sub>R (y - x))) (at u)"
  proof rule
    case goal1
    let ?u = "x + u *\<^sub>R (y - x)"
    have "(f \<circ> ?p has_derivative (f' ?u) \<circ> (\<lambda>u. 0 + u *\<^sub>R (y - x))) (at u within {0<..<1})" 
      apply(rule diff_chain_within) apply(rule has_derivative_intros)+ 
      apply(rule has_derivative_within_subset)
      apply(rule assms(2)[rule_format]) using goal1 * by auto
    thus ?case
      unfolding has_derivative_within_open[OF goal1 open_interval] by auto
  qed
  guess u using mvt_general[OF zero_less_one 1 2] .. note u = this
  have **:"\<And>x y. x\<in>s \<Longrightarrow> norm (f' x y) \<le> B * norm y"
  proof-
    case goal1
    have "norm (f' x y) \<le> onorm (f' x) * norm y"
      using onorm(1)[OF derivative_is_linear[OF assms(2)[rule_format,OF goal1]]] by assumption
    also have "\<dots> \<le> B * norm y"
      apply(rule mult_right_mono)
      using assms(3)[rule_format,OF goal1]
      by(auto simp add:field_simps)
    finally show ?case by simp
  qed
  have "norm (f x - f y) = norm ((f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 1 - (f \<circ> (\<lambda>u. x + u *\<^sub>R (y - x))) 0)"
    by(auto simp add:norm_minus_commute) 
  also have "\<dots> \<le> norm (f' (x + u *\<^sub>R (y - x)) (y - x))" using u by auto
  also have "\<dots> \<le> B * norm(y - x)" apply(rule **) using * and u by auto
  finally show ?thesis by(auto simp add:norm_minus_commute)
qed

lemma differentiable_bound_real:
  fixes f::"real \<Rightarrow> real"
  assumes "convex s" and "\<forall>x\<in>s. (f has_derivative f' x) (at x within s)"
  assumes "\<forall>x\<in>s. onorm(f' x) \<le> B" and x:"x\<in>s" and y:"y\<in>s"
  shows "norm(f x - f y) \<le> B * norm(x - y)"
  using differentiable_bound[of s f f' B x y]
  unfolding Ball_def image_iff o_def using assms by auto

text {* In particular. *}

lemma has_derivative_zero_constant:
  fixes f::"real\<Rightarrow>real"
  assumes "convex s" "\<forall>x\<in>s. (f has_derivative (\<lambda>h. 0)) (at x within s)"
  shows "\<exists>c. \<forall>x\<in>s. f x = c"
proof(cases "s={}")
  case False then obtain x where "x\<in>s" by auto
  have "\<And>y. y\<in>s \<Longrightarrow> f x = f y" proof- case goal1
    thus ?case
      using differentiable_bound_real[OF assms(1-2), of 0 x y] and `x\<in>s`
      unfolding onorm_const by auto qed
  thus ?thesis apply(rule_tac x="f x" in exI) by auto
qed auto

lemma has_derivative_zero_unique: fixes f::"real\<Rightarrow>real"
  assumes "convex s" and "a \<in> s" and "f a = c"
  assumes "\<forall>x\<in>s. (f has_derivative (\<lambda>h. 0)) (at x within s)" and "x\<in>s"
  shows "f x = c"
  using has_derivative_zero_constant[OF assms(1,4)] using assms(2-3,5) by auto

subsection {* Differentiability of inverse function (most basic form). *}

lemma has_derivative_inverse_basic:
  fixes f::"'b::euclidean_space \<Rightarrow> 'c::euclidean_space"
  assumes "(f has_derivative f') (at (g y))"
  assumes "bounded_linear g'" and "g' \<circ> f' = id" and "continuous (at y) g"
  assumes "open t" and "y \<in> t" and "\<forall>z\<in>t. f(g z) = z"
  shows "(g has_derivative g') (at y)"
proof-
  interpret f': bounded_linear f'
    using assms unfolding has_derivative_def by auto
  interpret g': bounded_linear g' using assms by auto
  guess C using bounded_linear.pos_bounded[OF assms(2)] .. note C = this
(*  have fgid:"\<And>x. g' (f' x) = x" using assms(3) unfolding o_def id_def apply()*)
  have lem1:"\<forall>e>0. \<exists>d>0. \<forall>z. norm(z - y) < d \<longrightarrow> norm(g z - g y - g'(z - y)) \<le> e * norm(g z - g y)"
  proof(rule,rule)
    case goal1
    have *:"e / C > 0" apply(rule divide_pos_pos) using `e>0` C by auto
    guess d0 using assms(1)[unfolded has_derivative_at_alt,THEN conjunct2,rule_format,OF *] .. note d0=this
    guess d1 using assms(4)[unfolded continuous_at Lim_at,rule_format,OF d0[THEN conjunct1]] .. note d1=this
    guess d2 using assms(5)[unfolded open_dist,rule_format,OF assms(6)] .. note d2=this
    guess d using real_lbound_gt_zero[OF d1[THEN conjunct1] d2[THEN conjunct1]] .. note d=this
    thus ?case apply(rule_tac x=d in exI) apply rule defer
    proof(rule,rule)
      fix z assume as:"norm (z - y) < d" hence "z\<in>t"
        using d2 d unfolding dist_norm by auto
      have "norm (g z - g y - g' (z - y)) \<le> norm (g' (f (g z) - y - f' (g z - g y)))"
        unfolding g'.diff f'.diff
        unfolding assms(3)[unfolded o_def id_def, THEN fun_cong] 
        unfolding assms(7)[rule_format,OF `z\<in>t`]
        apply(subst norm_minus_cancel[THEN sym]) by auto
      also have "\<dots> \<le> norm(f (g z) - y - f' (g z - g y)) * C"
        by (rule C [THEN conjunct2, rule_format])
      also have "\<dots> \<le> (e / C) * norm (g z - g y) * C"
        apply(rule mult_right_mono)
        apply(rule d0[THEN conjunct2,rule_format,unfolded assms(7)[rule_format,OF `y\<in>t`]])
        apply(cases "z=y") defer
        apply(rule d1[THEN conjunct2, unfolded dist_norm,rule_format])
        using as d C d0 by auto
      also have "\<dots> \<le> e * norm (g z - g y)"
        using C by (auto simp add: field_simps)
      finally show "norm (g z - g y - g' (z - y)) \<le> e * norm (g z - g y)"
        by simp
    qed auto
  qed
  have *:"(0::real) < 1 / 2" by auto
  guess d using lem1[rule_format,OF *] .. note d=this
  def B\<equiv>"C*2"
  have "B>0" unfolding B_def using C by auto
  have lem2:"\<forall>z. norm(z - y) < d \<longrightarrow> norm(g z - g y) \<le> B * norm(z - y)"
  proof(rule,rule) case goal1
    have "norm (g z - g y) \<le> norm(g' (z - y)) + norm ((g z - g y) - g'(z - y))"
      by(rule norm_triangle_sub)
    also have "\<dots> \<le> norm(g' (z - y)) + 1 / 2 * norm (g z - g y)"
      apply(rule add_left_mono) using d and goal1 by auto
    also have "\<dots> \<le> norm (z - y) * C + 1 / 2 * norm (g z - g y)"
      apply(rule add_right_mono) using C by auto
    finally show ?case unfolding B_def by(auto simp add:field_simps)
  qed
  show ?thesis unfolding has_derivative_at_alt
  proof(rule,rule assms,rule,rule) case goal1
    hence *:"e/B >0" apply-apply(rule divide_pos_pos) using `B>0` by auto
    guess d' using lem1[rule_format,OF *] .. note d'=this
    guess k using real_lbound_gt_zero[OF d[THEN conjunct1] d'[THEN conjunct1]] .. note k=this
    show ?case
      apply(rule_tac x=k in exI,rule) defer
    proof(rule,rule)
      fix z assume as:"norm(z - y) < k"
      hence "norm (g z - g y - g' (z - y)) \<le> e / B * norm(g z - g y)"
        using d' k by auto
      also have "\<dots> \<le> e * norm(z - y)"
        unfolding times_divide_eq_left pos_divide_le_eq[OF `B>0`]
        using lem2[THEN spec[where x=z]] using k as using `e>0`
        by (auto simp add: field_simps)
      finally show "norm (g z - g y - g' (z - y)) \<le> e * norm (z - y)"
        by simp qed(insert k, auto)
  qed
qed

text {* Simply rewrite that based on the domain point x. *}

lemma has_derivative_inverse_basic_x:
  fixes f::"'b::euclidean_space \<Rightarrow> 'c::euclidean_space"
  assumes "(f has_derivative f') (at x)" "bounded_linear g'" "g' o f' = id"
  "continuous (at (f x)) g" "g(f x) = x" "open t" "f x \<in> t" "\<forall>y\<in>t. f(g y) = y"
  shows "(g has_derivative g') (at (f(x)))"
  apply(rule has_derivative_inverse_basic) using assms by auto

text {* This is the version in Dieudonne', assuming continuity of f and g. *}

lemma has_derivative_inverse_dieudonne:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open s" "open (f ` s)" "continuous_on s f" "continuous_on (f ` s) g" "\<forall>x\<in>s. g(f x) = x"
  (**) "x\<in>s" "(f has_derivative f') (at x)"  "bounded_linear g'" "g' o f' = id"
  shows "(g has_derivative g') (at (f x))"
  apply(rule has_derivative_inverse_basic_x[OF assms(7-9) _ _ assms(2)])
  using assms(3-6) unfolding continuous_on_eq_continuous_at[OF assms(1)]
    continuous_on_eq_continuous_at[OF assms(2)] by auto

text {* Here's the simplest way of not assuming much about g. *}

lemma has_derivative_inverse:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact s" "x \<in> s" "f x \<in> interior(f ` s)" "continuous_on s f"
  "\<forall>y\<in>s. g(f y) = y" "(f has_derivative f') (at x)" "bounded_linear g'" "g' \<circ> f' = id"
  shows "(g has_derivative g') (at (f x))"
proof-
  { fix y assume "y\<in>interior (f ` s)" 
    then obtain x where "x\<in>s" and *:"y = f x"
      unfolding image_iff using interior_subset by auto
    have "f (g y) = y" unfolding * and assms(5)[rule_format,OF `x\<in>s`] ..
  } note * = this
  show ?thesis
    apply(rule has_derivative_inverse_basic_x[OF assms(6-8)])
    apply(rule continuous_on_interior[OF _ assms(3)])
    apply(rule continuous_on_inv[OF assms(4,1)])
    apply(rule assms(2,5) assms(5)[rule_format] open_interior assms(3))+
    by(rule, rule *, assumption)
qed

subsection {* Proving surjectivity via Brouwer fixpoint theorem. *}

lemma brouwer_surjective:
  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'n"
  assumes "compact t" "convex t"  "t \<noteq> {}" "continuous_on t f"
  "\<forall>x\<in>s. \<forall>y\<in>t. x + (y - f y) \<in> t" "x\<in>s"
  shows "\<exists>y\<in>t. f y = x"
proof-
  have *:"\<And>x y. f y = x \<longleftrightarrow> x + (y - f y) = y"
    by(auto simp add:algebra_simps)
  show ?thesis
    unfolding *
    apply(rule brouwer[OF assms(1-3), of "\<lambda>y. x + (y - f y)"])
    apply(rule continuous_on_intros assms)+ using assms(4-6) by auto
qed

lemma brouwer_surjective_cball:
  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'n"
  assumes "0 < e" "continuous_on (cball a e) f"
  "\<forall>x\<in>s. \<forall>y\<in>cball a e. x + (y - f y) \<in> cball a e" "x\<in>s"
  shows "\<exists>y\<in>cball a e. f y = x"
  apply(rule brouwer_surjective)
  apply(rule compact_cball convex_cball)+
  unfolding cball_eq_empty using assms by auto

text {* See Sussmann: "Multidifferential calculus", Theorem 2.1.1 *}

lemma sussmann_open_mapping:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "open s" "continuous_on s f" "x \<in> s" 
  "(f has_derivative f') (at x)" "bounded_linear g'" "f' \<circ> g' = id"
  "t \<subseteq> s" "x \<in> interior t"
  shows "f x \<in> interior (f ` t)"
proof- 
  interpret f':bounded_linear f'
    using assms unfolding has_derivative_def by auto
  interpret g':bounded_linear g' using assms by auto
  guess B using bounded_linear.pos_bounded[OF assms(5)] .. note B=this
  hence *:"1/(2*B)>0" by (auto intro!: divide_pos_pos)
  guess e0 using assms(4)[unfolded has_derivative_at_alt,THEN conjunct2,rule_format,OF *] .. note e0=this
  guess e1 using assms(8)[unfolded mem_interior_cball] .. note e1=this
  have *:"0<e0/B" "0<e1/B"
    apply(rule_tac[!] divide_pos_pos) using e0 e1 B by auto
  guess e using real_lbound_gt_zero[OF *] .. note e=this
  have "\<forall>z\<in>cball (f x) (e/2). \<exists>y\<in>cball (f x) e. f (x + g' (y - f x)) = z"
    apply(rule,rule brouwer_surjective_cball[where s="cball (f x) (e/2)"])
    prefer 3 apply(rule,rule)
  proof-
    show "continuous_on (cball (f x) e) (\<lambda>y. f (x + g' (y - f x)))"
      unfolding g'.diff
      apply(rule continuous_on_compose[of _ _ f, unfolded o_def])
      apply(rule continuous_on_intros linear_continuous_on[OF assms(5)])+
      apply(rule continuous_on_subset[OF assms(2)])
      apply(rule,unfold image_iff,erule bexE)
    proof-
      fix y z assume as:"y \<in>cball (f x) e"  "z = x + (g' y - g' (f x))"
      have "dist x z = norm (g' (f x) - g' y)"
        unfolding as(2) and dist_norm by auto
      also have "\<dots> \<le> norm (f x - y) * B"
        unfolding g'.diff[THEN sym] using B by auto
      also have "\<dots> \<le> e * B"
        using as(1)[unfolded mem_cball dist_norm] using B by auto
      also have "\<dots> \<le> e1" using e unfolding less_divide_eq using B by auto
      finally have "z\<in>cball x e1" unfolding mem_cball by force
      thus "z \<in> s" using e1 assms(7) by auto
    qed
  next
    fix y z assume as:"y \<in> cball (f x) (e / 2)" "z \<in> cball (f x) e"
    have "norm (g' (z - f x)) \<le> norm (z - f x) * B" using B by auto
    also have "\<dots> \<le> e * B" apply(rule mult_right_mono)
      using as(2)[unfolded mem_cball dist_norm] and B
      unfolding norm_minus_commute by auto
    also have "\<dots> < e0" using e and B unfolding less_divide_eq by auto
    finally have *:"norm (x + g' (z - f x) - x) < e0" by auto
    have **:"f x + f' (x + g' (z - f x) - x) = z"
      using assms(6)[unfolded o_def id_def,THEN cong] by auto
    have "norm (f x - (y + (z - f (x + g' (z - f x))))) \<le> norm (f (x + g' (z - f x)) - z) + norm (f x - y)"
      using norm_triangle_ineq[of "f (x + g'(z - f x)) - z" "f x - y"]
      by (auto simp add: algebra_simps)
    also have "\<dots> \<le> 1 / (B * 2) * norm (g' (z - f x)) + norm (f x - y)"
      using e0[THEN conjunct2,rule_format,OF *]
      unfolding algebra_simps ** by auto
    also have "\<dots> \<le> 1 / (B * 2) * norm (g' (z - f x)) + e/2"
      using as(1)[unfolded mem_cball dist_norm] by auto
    also have "\<dots> \<le> 1 / (B * 2) * B * norm (z - f x) + e/2"
      using * and B by (auto simp add: field_simps)
    also have "\<dots> \<le> 1 / 2 * norm (z - f x) + e/2" by auto
    also have "\<dots> \<le> e/2 + e/2" apply(rule add_right_mono)
      using as(2)[unfolded mem_cball dist_norm]
      unfolding norm_minus_commute by auto
    finally show "y + (z - f (x + g' (z - f x))) \<in> cball (f x) e"
      unfolding mem_cball dist_norm by auto
  qed(insert e, auto) note lem = this
  show ?thesis unfolding mem_interior apply(rule_tac x="e/2" in exI)
    apply(rule,rule divide_pos_pos) prefer 3
  proof
    fix y assume "y \<in> ball (f x) (e/2)"
    hence *:"y\<in>cball (f x) (e/2)" by auto
    guess z using lem[rule_format,OF *] .. note z=this
    hence "norm (g' (z - f x)) \<le> norm (z - f x) * B"
      using B by (auto simp add: field_simps)
    also have "\<dots> \<le> e * B"
      apply (rule mult_right_mono) using z(1)
      unfolding mem_cball dist_norm norm_minus_commute using B by auto
    also have "\<dots> \<le> e1"  using e B unfolding less_divide_eq by auto
    finally have "x + g'(z - f x) \<in> t" apply-
      apply(rule e1[THEN conjunct2,unfolded subset_eq,rule_format])
      unfolding mem_cball dist_norm by auto
    thus "y \<in> f ` t" using z by auto
  qed(insert e, auto)
qed

text {* Hence the following eccentric variant of the inverse function theorem.    *)
(* This has no continuity assumptions, but we do need the inverse function.  *)
(* We could put f' o g = I but this happens to fit with the minimal linear   *)
(* algebra theory I've set up so far. *}

(* move  before left_inverse_linear in Euclidean_Space*)

 lemma right_inverse_linear:
   fixes f::"'a::euclidean_space => 'a"
   assumes lf: "linear f" and gf: "f o g = id"
   shows "linear g"
 proof-
   from gf have fi: "surj f" by (auto simp add: surj_def o_def id_def) metis
   from linear_surjective_isomorphism[OF lf fi]
   obtain h:: "'a => 'a" where
     h: "linear h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x" by blast
   have "h = g" apply (rule ext) using gf h(2,3)
     by (simp add: o_def id_def fun_eq_iff) metis
   with h(1) show ?thesis by blast
 qed
 
lemma has_derivative_inverse_strong:
  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'n"
  assumes "open s" and "x \<in> s" and "continuous_on s f"
  assumes "\<forall>x\<in>s. g(f x) = x" "(f has_derivative f') (at x)" and "f' o g' = id"
  shows "(g has_derivative g') (at (f x))"
proof-
  have linf:"bounded_linear f'"
    using assms(5) unfolding has_derivative_def by auto
  hence ling:"bounded_linear g'"
    unfolding linear_conv_bounded_linear[THEN sym]
    apply- apply(rule right_inverse_linear) using assms(6) by auto
  moreover have "g' \<circ> f' = id" using assms(6) linf ling
    unfolding linear_conv_bounded_linear[THEN sym]
    using linear_inverse_left by auto
  moreover have *:"\<forall>t\<subseteq>s. x\<in>interior t \<longrightarrow> f x \<in> interior (f ` t)"
    apply(rule,rule,rule,rule sussmann_open_mapping )
    apply(rule assms ling)+ by auto
  have "continuous (at (f x)) g" unfolding continuous_at Lim_at
  proof(rule,rule)
    fix e::real assume "e>0"
    hence "f x \<in> interior (f ` (ball x e \<inter> s))"
      using *[rule_format,of "ball x e \<inter> s"] `x\<in>s`
      by(auto simp add: interior_open[OF open_ball] interior_open[OF assms(1)])
    then guess d unfolding mem_interior .. note d=this
    show "\<exists>d>0. \<forall>y. 0 < dist y (f x) \<and> dist y (f x) < d \<longrightarrow> dist (g y) (g (f x)) < e"
      apply(rule_tac x=d in exI)
      apply(rule,rule d[THEN conjunct1])
    proof(rule,rule) case goal1
      hence "g y \<in> g ` f ` (ball x e \<inter> s)"
        using d[THEN conjunct2,unfolded subset_eq,THEN bspec[where x=y]]
        by(auto simp add:dist_commute)
      hence "g y \<in> ball x e \<inter> s" using assms(4) by auto
      thus "dist (g y) (g (f x)) < e"
        using assms(4)[rule_format,OF `x\<in>s`]
        by (auto simp add: dist_commute)
    qed
  qed
  moreover have "f x \<in> interior (f ` s)"
    apply(rule sussmann_open_mapping)
    apply(rule assms ling)+
    using interior_open[OF assms(1)] and `x\<in>s` by auto
  moreover have "\<And>y. y \<in> interior (f ` s) \<Longrightarrow> f (g y) = y"
  proof- case goal1
    hence "y\<in>f ` s" using interior_subset by auto
    then guess z unfolding image_iff ..
    thus ?case using assms(4) by auto
  qed
  ultimately show ?thesis
    apply- apply(rule has_derivative_inverse_basic_x[OF assms(5)])
    using assms by auto
qed

text {* A rewrite based on the other domain. *}

lemma has_derivative_inverse_strong_x:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'a"
  assumes "open s" and "g y \<in> s" and "continuous_on s f"
  assumes "\<forall>x\<in>s. g(f x) = x" "(f has_derivative f') (at (g y))"
  assumes "f' o g' = id" and "f(g y) = y"
  shows "(g has_derivative g') (at y)"
  using has_derivative_inverse_strong[OF assms(1-6)] unfolding assms(7) by simp

text {* On a region. *}

lemma has_derivative_inverse_on:
  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'n"
  assumes "open s" and "\<forall>x\<in>s. (f has_derivative f'(x)) (at x)"
  assumes "\<forall>x\<in>s. g(f x) = x" and "f'(x) o g'(x) = id" and "x\<in>s"
  shows "(g has_derivative g'(x)) (at (f x))"
  apply(rule has_derivative_inverse_strong[where g'="g' x" and f=f])
  apply(rule assms)+
  unfolding continuous_on_eq_continuous_at[OF assms(1)]
  apply(rule,rule differentiable_imp_continuous_at)
  unfolding differentiable_def using assms by auto

text {* Invertible derivative continous at a point implies local
injectivity. It's only for this we need continuity of the derivative,
except of course if we want the fact that the inverse derivative is
also continuous. So if we know for some other reason that the inverse
function exists, it's OK. *}

lemma bounded_linear_sub:
  "bounded_linear f \<Longrightarrow> bounded_linear g ==> bounded_linear (\<lambda>x. f x - g x)"
  using bounded_linear_add[of f "\<lambda>x. - g x"] bounded_linear_minus[of g]
  by (auto simp add: algebra_simps)

lemma has_derivative_locally_injective:
  fixes f::"'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "a \<in> s" "open s" "bounded_linear g'" "g' o f'(a) = id"
  "\<forall>x\<in>s. (f has_derivative f'(x)) (at x)"
  "\<forall>e>0. \<exists>d>0. \<forall>x. dist a x < d \<longrightarrow> onorm(\<lambda>v. f' x v - f' a v) < e"
  obtains t where "a \<in> t" "open t" "\<forall>x\<in>t. \<forall>x'\<in>t. (f x' = f x) \<longrightarrow> (x' = x)"
proof-
  interpret bounded_linear g' using assms by auto
  note f'g' = assms(4)[unfolded id_def o_def,THEN cong]
  have "g' (f' a (\<chi>\<chi> i.1)) = (\<chi>\<chi> i.1)" "(\<chi>\<chi> i.1) \<noteq> (0::'n)" defer 
    apply(subst euclidean_eq) using f'g' by auto
  hence *:"0 < onorm g'"
    unfolding onorm_pos_lt[OF assms(3)[unfolded linear_linear]] by fastforce
  def k \<equiv> "1 / onorm g' / 2" have *:"k>0" unfolding k_def using * by auto
  guess d1 using assms(6)[rule_format,OF *] .. note d1=this
  from `open s` obtain d2 where "d2>0" "ball a d2 \<subseteq> s" using `a\<in>s` ..
  obtain d2 where "d2>0" "ball a d2 \<subseteq> s" using assms(2,1) ..
  guess d2 using assms(2)[unfolded open_contains_ball,rule_format,OF `a\<in>s`] ..
  note d2=this
  guess d using real_lbound_gt_zero[OF d1[THEN conjunct1] d2[THEN conjunct1]] ..
  note d = this
  show ?thesis
  proof
    show "a\<in>ball a d" using d by auto
    show "\<forall>x\<in>ball a d. \<forall>x'\<in>ball a d. f x' = f x \<longrightarrow> x' = x"
    proof (intro strip)
      fix x y assume as:"x\<in>ball a d" "y\<in>ball a d" "f x = f y"
      def ph \<equiv> "\<lambda>w. w - g'(f w - f x)"
      have ph':"ph = g' \<circ> (\<lambda>w. f' a w - (f w - f x))"
        unfolding ph_def o_def unfolding diff using f'g'
        by (auto simp add: algebra_simps)
      have "norm (ph x - ph y) \<le> (1/2) * norm (x - y)"
        apply(rule differentiable_bound[OF convex_ball _ _ as(1-2), where f'="\<lambda>x v. v - g'(f' x v)"])
        apply(rule_tac[!] ballI)
      proof-
        fix u assume u:"u \<in> ball a d"
        hence "u\<in>s" using d d2 by auto
        have *:"(\<lambda>v. v - g' (f' u v)) = g' \<circ> (\<lambda>w. f' a w - f' u w)"
          unfolding o_def and diff using f'g' by auto
        show "(ph has_derivative (\<lambda>v. v - g' (f' u v))) (at u within ball a d)"
          unfolding ph' * apply(rule diff_chain_within) defer
          apply(rule bounded_linear.has_derivative'[OF assms(3)])
          apply(rule has_derivative_intros) defer
          apply(rule has_derivative_sub[where g'="\<lambda>x.0",unfolded diff_0_right])
          apply(rule has_derivative_at_within)
          using assms(5) and `u\<in>s` `a\<in>s`
          by(auto intro!: has_derivative_intros bounded_linear.has_derivative' derivative_linear)
        have **:"bounded_linear (\<lambda>x. f' u x - f' a x)"
          "bounded_linear (\<lambda>x. f' a x - f' u x)"
          apply(rule_tac[!] bounded_linear_sub)
          apply(rule_tac[!] derivative_linear)
          using assms(5) `u\<in>s` `a\<in>s` by auto
        have "onorm (\<lambda>v. v - g' (f' u v)) \<le> onorm g' * onorm (\<lambda>w. f' a w - f' u w)"
          unfolding * apply(rule onorm_compose)
          unfolding linear_conv_bounded_linear by(rule assms(3) **)+
        also have "\<dots> \<le> onorm g' * k"
          apply(rule mult_left_mono) 
          using d1[THEN conjunct2,rule_format,of u]
          using onorm_neg[OF **(1)[unfolded linear_linear]]
          using d and u and onorm_pos_le[OF assms(3)[unfolded linear_linear]]
          by (auto simp add: algebra_simps)
        also have "\<dots> \<le> 1/2" unfolding k_def by auto
        finally show "onorm (\<lambda>v. v - g' (f' u v)) \<le> 1 / 2" by assumption
      qed
      moreover have "norm (ph y - ph x) = norm (y - x)"
        apply(rule arg_cong[where f=norm])
        unfolding ph_def using diff unfolding as by auto
      ultimately show "x = y" unfolding norm_minus_commute by auto
    qed
  qed auto
qed

subsection {* Uniformly convergent sequence of derivatives. *}

lemma has_derivative_sequence_lipschitz_lemma:
  fixes f::"nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
  assumes "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
  assumes "\<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm(f' n x h - g' x h) \<le> e * norm(h)"
  shows "\<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm((f m x - f n x) - (f m y - f n y)) \<le> 2 * e * norm(x - y)"
proof (default)+
  fix m n x y assume as:"N\<le>m" "N\<le>n" "x\<in>s" "y\<in>s"
  show "norm((f m x - f n x) - (f m y - f n y)) \<le> 2 * e * norm(x - y)"
    apply(rule differentiable_bound[where f'="\<lambda>x h. f' m x h - f' n x h", OF assms(1) _ _ as(3-4)])
    apply(rule_tac[!] ballI)
  proof-
    fix x assume "x\<in>s"
    show "((\<lambda>a. f m a - f n a) has_derivative (\<lambda>h. f' m x h - f' n x h)) (at x within s)"
      by(rule has_derivative_intros assms(2)[rule_format] `x\<in>s`)+
    { fix h
      have "norm (f' m x h - f' n x h) \<le> norm (f' m x h - g' x h) + norm (f' n x h - g' x h)"
        using norm_triangle_ineq[of "f' m x h - g' x h" "- f' n x h + g' x h"]
        unfolding norm_minus_commute by (auto simp add: algebra_simps)
      also have "\<dots> \<le> e * norm h+ e * norm h"
        using assms(3)[rule_format,OF `N\<le>m` `x\<in>s`, of h]
        using assms(3)[rule_format,OF `N\<le>n` `x\<in>s`, of h]
        by(auto simp add:field_simps)
      finally have "norm (f' m x h - f' n x h) \<le> 2 * e * norm h" by auto }
    thus "onorm (\<lambda>h. f' m x h - f' n x h) \<le> 2 * e"
      apply-apply(rule onorm(2)) apply(rule linear_compose_sub)
      unfolding linear_conv_bounded_linear
      using assms(2)[rule_format,OF `x\<in>s`, THEN derivative_linear]
      by auto
  qed
qed

lemma has_derivative_sequence_lipschitz:
  fixes f::"nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
  assumes "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
  assumes "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm(f' n x h - g' x h) \<le> e * norm(h)"
  assumes "0 < e"
  shows "\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm((f m x - f n x) - (f m y - f n y)) \<le> e * norm(x - y)"
proof(rule,rule)
  case goal1 have *:"2 * (1/2* e) = e" "1/2 * e >0" using `e>0` by auto
  guess N using assms(3)[rule_format,OF *(2)] ..
  thus ?case
    apply(rule_tac x=N in exI)
    apply(rule has_derivative_sequence_lipschitz_lemma[where e="1/2 *e", unfolded *])
    using assms by auto
qed

lemma has_derivative_sequence:
  fixes f::"nat\<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
  assumes "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
  assumes "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm(f' n x h - g' x h) \<le> e * norm(h)"
  assumes "x0 \<in> s" and "((\<lambda>n. f n x0) ---> l) sequentially"
  shows "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) ---> g x) sequentially \<and>
    (g has_derivative g'(x)) (at x within s)"
proof-
  have lem1:"\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm((f m x - f n x) - (f m y - f n y)) \<le> e * norm(x - y)"
    apply(rule has_derivative_sequence_lipschitz[where e="42::nat"])
    apply(rule assms)+ by auto
  have "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) ---> g x) sequentially"
    apply(rule bchoice) unfolding convergent_eq_cauchy
  proof
    fix x assume "x\<in>s" show "Cauchy (\<lambda>n. f n x)"
    proof(cases "x=x0")
      case True thus ?thesis using convergent_imp_cauchy[OF assms(5)] by auto
    next
      case False show ?thesis unfolding Cauchy_def
      proof(rule,rule)
        fix e::real assume "e>0"
        hence *:"e/2>0" "e/2/norm(x-x0)>0"
          using False by (auto intro!: divide_pos_pos)
        guess M using convergent_imp_cauchy[OF assms(5), unfolded Cauchy_def, rule_format,OF *(1)] .. note M=this
        guess N using lem1[rule_format,OF *(2)] .. note N = this
        show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e"
          apply(rule_tac x="max M N" in exI)
        proof(default+)
          fix m n assume as:"max M N \<le>m" "max M N\<le>n"
          have "dist (f m x) (f n x) \<le> norm (f m x0 - f n x0) + norm (f m x - f n x - (f m x0 - f n x0))"
            unfolding dist_norm by(rule norm_triangle_sub)
          also have "\<dots> \<le> norm (f m x0 - f n x0) + e / 2"
            using N[rule_format,OF _ _ `x\<in>s` `x0\<in>s`, of m n] and as and False
            by auto
          also have "\<dots> < e / 2 + e / 2"
            apply(rule add_strict_right_mono)
            using as and M[rule_format] unfolding dist_norm by auto
          finally show "dist (f m x) (f n x) < e" by auto
        qed
      qed
    qed
  qed
  then guess g .. note g = this
  have lem2:"\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm((f n x - f n y) - (g x - g y)) \<le> e * norm(x - y)"
  proof(rule,rule)
    fix e::real assume *:"e>0"
    guess N using lem1[rule_format,OF *] .. note N=this
    show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>y\<in>s. norm (f n x - f n y - (g x - g y)) \<le> e * norm (x - y)"
      apply(rule_tac x=N in exI)
    proof(default+)
      fix n x y assume as:"N \<le> n" "x \<in> s" "y \<in> s"
      have "eventually (\<lambda>xa. norm (f n x - f n y - (f xa x - f xa y)) \<le> e * norm (x - y)) sequentially"
        unfolding eventually_sequentially
        apply(rule_tac x=N in exI)
      proof(rule,rule)
        fix m assume "N\<le>m"
        thus "norm (f n x - f n y - (f m x - f m y)) \<le> e * norm (x - y)"
          using N[rule_format, of n m x y] and as
          by (auto simp add: algebra_simps)
      qed
      thus "norm (f n x - f n y - (g x - g y)) \<le> e * norm (x - y)"
        apply-
        apply(rule Lim_norm_ubound[OF trivial_limit_sequentially, where f="\<lambda>m. (f n x - f n y) - (f m x - f m y)"])
        apply(rule tendsto_intros g[rule_format] as)+ by assumption
    qed
  qed
  show ?thesis unfolding has_derivative_within_alt apply(rule_tac x=g in exI)
    apply(rule,rule,rule g[rule_format],assumption)
  proof fix x assume "x\<in>s"
    have lem3:"\<forall>u. ((\<lambda>n. f' n x u) ---> g' x u) sequentially"
      unfolding LIMSEQ_def
    proof(rule,rule,rule)
      fix u and e::real assume "e>0"
      show "\<exists>N. \<forall>n\<ge>N. dist (f' n x u) (g' x u) < e"
      proof(cases "u=0")
        case True guess N using assms(3)[rule_format,OF `e>0`] .. note N=this
        show ?thesis apply(rule_tac x=N in exI) unfolding True 
          using N[rule_format,OF _ `x\<in>s`,of _ 0] and `e>0` by auto
      next
        case False hence *:"e / 2 / norm u > 0"
          using `e>0` by (auto intro!: divide_pos_pos)
        guess N using assms(3)[rule_format,OF *] .. note N=this
        show ?thesis apply(rule_tac x=N in exI)
        proof(rule,rule) case goal1
          show ?case unfolding dist_norm
            using N[rule_format,OF goal1 `x\<in>s`, of u] False `e>0`
            by (auto simp add:field_simps)
        qed
      qed
    qed
    show "bounded_linear (g' x)"
      unfolding linear_linear linear_def
      apply(rule,rule,rule) defer
    proof(rule,rule)
      fix x' y z::"'m" and c::real
      note lin = assms(2)[rule_format,OF `x\<in>s`,THEN derivative_linear]
      show "g' x (c *\<^sub>R x') = c *\<^sub>R g' x x'"
        apply(rule tendsto_unique[OF trivial_limit_sequentially])
        apply(rule lem3[rule_format])
        unfolding lin[unfolded bounded_linear_def bounded_linear_axioms_def,THEN conjunct2,THEN conjunct1,rule_format]
        apply (intro tendsto_intros) by(rule lem3[rule_format])
      show "g' x (y + z) = g' x y + g' x z"
        apply(rule tendsto_unique[OF trivial_limit_sequentially])
        apply(rule lem3[rule_format])
        unfolding lin[unfolded bounded_linear_def additive_def,THEN conjunct1,rule_format]
        apply(rule tendsto_add) by(rule lem3[rule_format])+
    qed
    show "\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm (y - x) < d \<longrightarrow> norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)"
    proof(rule,rule) case goal1
      have *:"e/3>0" using goal1 by auto
      guess N1 using assms(3)[rule_format,OF *] .. note N1=this
      guess N2 using lem2[rule_format,OF *] .. note N2=this
      guess d1 using assms(2)[unfolded has_derivative_within_alt, rule_format,OF `x\<in>s`, of "max N1 N2",THEN conjunct2,rule_format,OF *] .. note d1=this
      show ?case apply(rule_tac x=d1 in exI) apply(rule,rule d1[THEN conjunct1])
      proof(rule,rule)
        fix y assume as:"y \<in> s" "norm (y - x) < d1"
        let ?N ="max N1 N2"
        have "norm (g y - g x - (f ?N y - f ?N x)) \<le> e /3 * norm (y - x)"
          apply(subst norm_minus_cancel[THEN sym])
          using N2[rule_format, OF _ `y\<in>s` `x\<in>s`, of ?N] by auto
        moreover
        have "norm (f ?N y - f ?N x - f' ?N x (y - x)) \<le> e / 3 * norm (y - x)"
          using d1 and as by auto
        ultimately
        have "norm (g y - g x - f' ?N x (y - x)) \<le> 2 * e / 3 * norm (y - x)" 
          using norm_triangle_le[of "g y - g x - (f ?N y - f ?N x)" "f ?N y - f ?N x - f' ?N x (y - x)" "2 * e / 3 * norm (y - x)"]
          by (auto simp add:algebra_simps)
        moreover
        have " norm (f' ?N x (y - x) - g' x (y - x)) \<le> e / 3 * norm (y - x)"
          using N1 `x\<in>s` by auto
        ultimately show "norm (g y - g x - g' x (y - x)) \<le> e * norm (y - x)"
          using norm_triangle_le[of "g y - g x - f' (max N1 N2) x (y - x)" "f' (max N1 N2) x (y - x) - g' x (y - x)"]
          by(auto simp add:algebra_simps)
      qed
    qed
  qed
qed

text {* Can choose to line up antiderivatives if we want. *}

lemma has_antiderivative_sequence:
  fixes f::"nat\<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
  assumes "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
  assumes "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm(f' n x h - g' x h) \<le> e * norm h"
  shows "\<exists>g. \<forall>x\<in>s. (g has_derivative g'(x)) (at x within s)"
proof(cases "s={}")
  case False then obtain a where "a\<in>s" by auto
  have *:"\<And>P Q. \<exists>g. \<forall>x\<in>s. P g x \<and> Q g x \<Longrightarrow> \<exists>g. \<forall>x\<in>s. Q g x" by auto
  show ?thesis
    apply(rule *)
    apply(rule has_derivative_sequence[OF assms(1) _ assms(3), of "\<lambda>n x. f n x + (f 0 a - f n a)"])
    apply(rule,rule)
    apply(rule has_derivative_add_const, rule assms(2)[rule_format], assumption)  
    apply(rule `a\<in>s`) by auto
qed auto

lemma has_antiderivative_limit:
  fixes g'::"'m::euclidean_space \<Rightarrow> 'm \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
  assumes "\<forall>e>0. \<exists>f f'. \<forall>x\<in>s. (f has_derivative (f' x)) (at x within s) \<and> (\<forall>h. norm(f' x h - g' x h) \<le> e * norm(h))"
  shows "\<exists>g. \<forall>x\<in>s. (g has_derivative g'(x)) (at x within s)"
proof-
  have *:"\<forall>n. \<exists>f f'. \<forall>x\<in>s. (f has_derivative (f' x)) (at x within s) \<and> (\<forall>h. norm(f' x h - g' x h) \<le> inverse (real (Suc n)) * norm(h))"
    apply(rule) using assms(2)
    apply(erule_tac x="inverse (real (Suc n))" in allE) by auto
  guess f using *[THEN choice] .. note * = this
  guess f' using *[THEN choice] .. note f=this
  show ?thesis apply(rule has_antiderivative_sequence[OF assms(1), of f f']) defer
  proof(rule,rule)
    fix e::real assume "0<e" guess  N using reals_Archimedean[OF `e>0`] .. note N=this 
    show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
      apply(rule_tac x=N in exI)
    proof(default+)
      case goal1
      have *:"inverse (real (Suc n)) \<le> e" apply(rule order_trans[OF _ N[THEN less_imp_le]])
        using goal1(1) by(auto simp add:field_simps) 
      show ?case
        using f[rule_format,THEN conjunct2,OF goal1(2), of n, THEN spec[where x=h]] 
        apply(rule order_trans) using N * apply(cases "h=0") by auto
    qed
  qed(insert f,auto)
qed

subsection {* Differentiation of a series. *}

definition sums_seq :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> (nat set) \<Rightarrow> bool"
(infixl "sums'_seq" 12) where "(f sums_seq l) s \<equiv> ((\<lambda>n. setsum f (s \<inter> {0..n})) ---> l) sequentially"

lemma has_derivative_series:
  fixes f::"nat \<Rightarrow> 'm::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "convex s"
  assumes "\<forall>n. \<forall>x\<in>s. ((f n) has_derivative (f' n x)) (at x within s)"
  assumes "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. norm(setsum (\<lambda>i. f' i x h) (k \<inter> {0..n}) - g' x h) \<le> e * norm(h)"
  assumes "x\<in>s" and "((\<lambda>n. f n x) sums_seq l) k"
  shows "\<exists>g. \<forall>x\<in>s. ((\<lambda>n. f n x) sums_seq (g x)) k \<and> (g has_derivative g'(x)) (at x within s)"
  unfolding sums_seq_def
  apply(rule has_derivative_sequence[OF assms(1) _ assms(3)])
  apply(rule,rule)
  apply(rule has_derivative_setsum) defer
  apply(rule,rule assms(2)[rule_format],assumption)
  using assms(4-5) unfolding sums_seq_def by auto

subsection {* Derivative with composed bilinear function. *}

lemma has_derivative_bilinear_within:
  assumes "(f has_derivative f') (at x within s)"
  assumes "(g has_derivative g') (at x within s)"
  assumes "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_derivative (\<lambda>d. h (f x) (g' d) + h (f' d) (g x))) (at x within s)"
proof-
  have "(g ---> g x) (at x within s)"
    apply(rule differentiable_imp_continuous_within[unfolded continuous_within])
    using assms(2) unfolding differentiable_def by auto
  moreover
  interpret f':bounded_linear f'
    using assms unfolding has_derivative_def by auto
  interpret g':bounded_linear g'
    using assms unfolding has_derivative_def by auto
  interpret h:bounded_bilinear h
    using assms by auto
  have "((\<lambda>y. f' (y - x)) ---> 0) (at x within s)"
    unfolding f'.zero[THEN sym]
    using bounded_linear.tendsto [of f' "\<lambda>y. y - x" 0 "at x within s"]
    using tendsto_diff [OF Lim_within_id tendsto_const, of x x s]
    unfolding id_def using assms(1) unfolding has_derivative_def by auto
  hence "((\<lambda>y. f x + f' (y - x)) ---> f x) (at x within s)"
    using tendsto_add[OF tendsto_const, of "\<lambda>y. f' (y - x)" 0 "at x within s" "f x"]
    by auto
  ultimately
  have *:"((\<lambda>x'. h (f x + f' (x' - x)) ((1/(norm (x' - x))) *\<^sub>R (g x' - (g x + g' (x' - x))))
             + h ((1/ (norm (x' - x))) *\<^sub>R (f x' - (f x + f' (x' - x)))) (g x')) ---> h (f x) 0 + h 0 (g x)) (at x within s)"
    apply-apply(rule tendsto_add) apply(rule_tac[!] Lim_bilinear[OF _ _ assms(3)])
    using assms(1-2)  unfolding has_derivative_within by auto
  guess B using bounded_bilinear.pos_bounded[OF assms(3)] .. note B=this
  guess C using f'.pos_bounded .. note C=this
  guess D using g'.pos_bounded .. note D=this
  have bcd:"B * C * D > 0" using B C D by (auto intro!: mult_pos_pos)
  have **:"((\<lambda>y. (1/(norm(y - x))) *\<^sub>R (h (f'(y - x)) (g'(y - x)))) ---> 0) (at x within s)"
    unfolding Lim_within
  proof(rule,rule) case goal1
    hence "e/(B*C*D)>0" using B C D by(auto intro!:divide_pos_pos mult_pos_pos)
    thus ?case apply(rule_tac x="e/(B*C*D)" in exI,rule)
    proof(rule,rule,erule conjE)
      fix y assume as:"y \<in> s" "0 < dist y x" "dist y x < e / (B * C * D)"
      have "norm (h (f' (y - x)) (g' (y - x))) \<le> norm (f' (y - x)) * norm (g' (y - x)) * B" using B by auto
      also have "\<dots> \<le> (norm (y - x) * C) * (D * norm (y - x)) * B"
        apply(rule mult_right_mono)
        apply(rule mult_mono) using B C D
        by (auto simp add: field_simps intro!:mult_nonneg_nonneg)
      also have "\<dots> = (B * C * D * norm (y - x)) * norm (y - x)"
        by (auto simp add: field_simps)
      also have "\<dots> < e * norm (y - x)"
        apply(rule mult_strict_right_mono)
        using as(3)[unfolded dist_norm] and as(2)
        unfolding pos_less_divide_eq[OF bcd] by (auto simp add: field_simps)
      finally show "dist ((1 / norm (y - x)) *\<^sub>R h (f' (y - x)) (g' (y - x))) 0 < e"
        unfolding dist_norm apply-apply(cases "y = x")
        by(auto simp add: field_simps)
    qed
  qed
  have "bounded_linear (\<lambda>d. h (f x) (g' d) + h (f' d) (g x))"
    apply (rule bounded_linear_add)
    apply (rule bounded_linear_compose [OF h.bounded_linear_right `bounded_linear g'`])
    apply (rule bounded_linear_compose [OF h.bounded_linear_left `bounded_linear f'`])
    done
  thus ?thesis using tendsto_add[OF * **] unfolding has_derivative_within 
    unfolding g'.add f'.scaleR f'.add g'.scaleR f'.diff g'.diff
     h.add_right h.add_left scaleR_right_distrib h.scaleR_left h.scaleR_right h.diff_right h.diff_left
    scaleR_right_diff_distrib h.zero_right h.zero_left
    by(auto simp add:field_simps)
qed

lemma has_derivative_bilinear_at:
  assumes "(f has_derivative f') (at x)"
  assumes "(g has_derivative g') (at x)"
  assumes "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_derivative (\<lambda>d. h (f x) (g' d) + h (f' d) (g x))) (at x)"
  using has_derivative_bilinear_within[of f f' x UNIV g g' h] assms by simp

subsection {* Considering derivative @{typ "real \<Rightarrow> 'b\<Colon>real_normed_vector"} as a vector. *}

definition has_vector_derivative :: "(real \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> (real filter \<Rightarrow> bool)"
(infixl "has'_vector'_derivative" 12) where
 "(f has_vector_derivative f') net \<equiv> (f has_derivative (\<lambda>x. x *\<^sub>R f')) net"

definition "vector_derivative f net \<equiv> (SOME f'. (f has_vector_derivative f') net)"

lemma vector_derivative_works:
  fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  shows "f differentiable net \<longleftrightarrow> (f has_vector_derivative (vector_derivative f net)) net" (is "?l = ?r")
proof
  assume ?l guess f' using `?l`[unfolded differentiable_def] .. note f' = this
  then interpret bounded_linear f' by auto
  thus ?r unfolding vector_derivative_def has_vector_derivative_def
    apply-apply(rule someI_ex,rule_tac x="f' 1" in exI)
    using f' unfolding scaleR[THEN sym] by auto
next
  assume ?r thus ?l
    unfolding vector_derivative_def has_vector_derivative_def differentiable_def
    by auto
qed

lemma vector_derivative_unique_at:
  assumes "(f has_vector_derivative f') (at x)"
  assumes "(f has_vector_derivative f'') (at x)"
  shows "f' = f''"
proof-
  have "(\<lambda>x. x *\<^sub>R f') = (\<lambda>x. x *\<^sub>R f'')"
    using assms [unfolded has_vector_derivative_def]
    by (rule frechet_derivative_unique_at)
  thus ?thesis unfolding fun_eq_iff by auto
qed

lemma vector_derivative_unique_within_closed_interval:
  fixes f::"real \<Rightarrow> 'n::ordered_euclidean_space"
  assumes "a < b" and "x \<in> {a..b}"
  assumes "(f has_vector_derivative f') (at x within {a..b})"
  assumes "(f has_vector_derivative f'') (at x within {a..b})"
  shows "f' = f''"
proof-
  have *:"(\<lambda>x. x *\<^sub>R f') = (\<lambda>x. x *\<^sub>R f'')"
    apply(rule frechet_derivative_unique_within_closed_interval[of "a" "b"])
    using assms(3-)[unfolded has_vector_derivative_def] using assms(1-2)
    by auto
  show ?thesis
  proof(rule ccontr)
    assume "f' \<noteq> f''"
    moreover
    hence "(\<lambda>x. x *\<^sub>R f') 1 = (\<lambda>x. x *\<^sub>R f'') 1"
      using * by (auto simp: fun_eq_iff)
    ultimately show False unfolding o_def by auto
  qed
qed

lemma vector_derivative_at:
  shows "(f has_vector_derivative f') (at x) \<Longrightarrow> vector_derivative f (at x) = f'"
  apply(rule vector_derivative_unique_at) defer apply assumption
  unfolding vector_derivative_works[THEN sym] differentiable_def
  unfolding has_vector_derivative_def by auto

lemma vector_derivative_within_closed_interval:
  fixes f::"real \<Rightarrow> 'a::ordered_euclidean_space"
  assumes "a < b" and "x \<in> {a..b}"
  assumes "(f has_vector_derivative f') (at x within {a..b})"
  shows "vector_derivative f (at x within {a..b}) = f'"
  apply(rule vector_derivative_unique_within_closed_interval)
  using vector_derivative_works[unfolded differentiable_def]
  using assms by(auto simp add:has_vector_derivative_def)

lemma has_vector_derivative_within_subset: 
 "(f has_vector_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (f has_vector_derivative f') (at x within t)"
  unfolding has_vector_derivative_def apply(rule has_derivative_within_subset) by auto

lemma has_vector_derivative_const: 
 "((\<lambda>x. c) has_vector_derivative 0) net"
  unfolding has_vector_derivative_def using has_derivative_const by auto

lemma has_vector_derivative_id: "((\<lambda>x::real. x) has_vector_derivative 1) net"
  unfolding has_vector_derivative_def using has_derivative_id by auto

lemma has_vector_derivative_cmul:
  "(f has_vector_derivative f') net \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_vector_derivative (c *\<^sub>R f')) net"
  unfolding has_vector_derivative_def
  apply (drule scaleR_right_has_derivative)
  by (auto simp add: algebra_simps)

lemma has_vector_derivative_cmul_eq:
  assumes "c \<noteq> 0"
  shows "(((\<lambda>x. c *\<^sub>R f x) has_vector_derivative (c *\<^sub>R f')) net \<longleftrightarrow> (f has_vector_derivative f') net)"
  apply rule apply(drule has_vector_derivative_cmul[where c="1/c"]) defer
  apply(rule has_vector_derivative_cmul) using assms by auto

lemma has_vector_derivative_neg:
  "(f has_vector_derivative f') net \<Longrightarrow> ((\<lambda>x. -(f x)) has_vector_derivative (- f')) net"
  unfolding has_vector_derivative_def apply(drule has_derivative_neg) by auto

lemma has_vector_derivative_add:
  assumes "(f has_vector_derivative f') net"
  assumes "(g has_vector_derivative g') net"
  shows "((\<lambda>x. f(x) + g(x)) has_vector_derivative (f' + g')) net"
  using has_derivative_add[OF assms[unfolded has_vector_derivative_def]]
  unfolding has_vector_derivative_def unfolding scaleR_right_distrib by auto

lemma has_vector_derivative_sub:
  assumes "(f has_vector_derivative f') net"
  assumes "(g has_vector_derivative g') net"
  shows "((\<lambda>x. f(x) - g(x)) has_vector_derivative (f' - g')) net"
  using has_derivative_sub[OF assms[unfolded has_vector_derivative_def]]
  unfolding has_vector_derivative_def scaleR_right_diff_distrib by auto

lemma has_vector_derivative_bilinear_within:
  assumes "(f has_vector_derivative f') (at x within s)"
  assumes "(g has_vector_derivative g') (at x within s)"
  assumes "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_vector_derivative (h (f x) g' + h f' (g x))) (at x within s)"
proof-
  interpret bounded_bilinear h using assms by auto 
  show ?thesis using has_derivative_bilinear_within[OF assms(1-2)[unfolded has_vector_derivative_def], of h]
    unfolding o_def has_vector_derivative_def
    using assms(3) unfolding scaleR_right scaleR_left scaleR_right_distrib
    by auto
qed

lemma has_vector_derivative_bilinear_at:
  assumes "(f has_vector_derivative f') (at x)"
  assumes "(g has_vector_derivative g') (at x)"
  assumes "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) has_vector_derivative (h (f x) g' + h f' (g x))) (at x)"
  using has_vector_derivative_bilinear_within[where s=UNIV] assms by simp

lemma has_vector_derivative_at_within:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> (f has_vector_derivative f') (at x within s)"
  unfolding has_vector_derivative_def
  by (rule has_derivative_at_within)

lemma has_vector_derivative_transform_within:
  assumes "0 < d" and "x \<in> s" and "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'"
  assumes "(f has_vector_derivative f') (at x within s)"
  shows "(g has_vector_derivative f') (at x within s)"
  using assms unfolding has_vector_derivative_def
  by (rule has_derivative_transform_within)

lemma has_vector_derivative_transform_at:
  assumes "0 < d" and "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'"
  assumes "(f has_vector_derivative f') (at x)"
  shows "(g has_vector_derivative f') (at x)"
  using assms unfolding has_vector_derivative_def
  by (rule has_derivative_transform_at)

lemma has_vector_derivative_transform_within_open:
  assumes "open s" and "x \<in> s" and "\<forall>y\<in>s. f y = g y"
  assumes "(f has_vector_derivative f') (at x)"
  shows "(g has_vector_derivative f') (at x)"
  using assms unfolding has_vector_derivative_def
  by (rule has_derivative_transform_within_open)

lemma vector_diff_chain_at:
  assumes "(f has_vector_derivative f') (at x)"
  assumes "(g has_vector_derivative g') (at (f x))"
  shows "((g \<circ> f) has_vector_derivative (f' *\<^sub>R g')) (at x)"
  using assms(2) unfolding has_vector_derivative_def apply-
  apply(drule diff_chain_at[OF assms(1)[unfolded has_vector_derivative_def]])
  unfolding o_def real_scaleR_def scaleR_scaleR .

lemma vector_diff_chain_within:
  assumes "(f has_vector_derivative f') (at x within s)"
  assumes "(g has_vector_derivative g') (at (f x) within f ` s)"
  shows "((g o f) has_vector_derivative (f' *\<^sub>R g')) (at x within s)"
  using assms(2) unfolding has_vector_derivative_def apply-
  apply(drule diff_chain_within[OF assms(1)[unfolded has_vector_derivative_def]])
  unfolding o_def real_scaleR_def scaleR_scaleR .

end
