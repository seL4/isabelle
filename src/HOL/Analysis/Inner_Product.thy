(*  Title:      HOL/Analysis/Inner_Product.thy
    Author:     Brian Huffman
*)

section \<open>Inner Product Spaces and Gradient Derivative\<close>

theory Inner_Product
imports Complex_Main
begin

subsection \<open>Real inner product spaces\<close>

text \<open>
  Temporarily relax type constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::open set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::dist \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>

class real_inner = real_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  fixes inner :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes inner_commute: "inner x y = inner y x"
  and inner_add_left: "inner (x + y) z = inner x z + inner y z"
  and inner_scaleR_left [simp]: "inner (scaleR r x) y = r * (inner x y)"
  and inner_ge_zero [simp]: "0 \<le> inner x x"
  and inner_eq_zero_iff [simp]: "inner x x = 0 \<longleftrightarrow> x = 0"
  and norm_eq_sqrt_inner: "norm x = sqrt (inner x x)"
begin

lemma inner_zero_left [simp]: "inner 0 x = 0"
  using inner_add_left [of 0 0 x] by simp

lemma inner_minus_left [simp]: "inner (- x) y = - inner x y"
  using inner_add_left [of x "- x" y] by simp

lemma inner_diff_left: "inner (x - y) z = inner x z - inner y z"
  using inner_add_left [of x "- y" z] by simp

lemma inner_sum_left: "inner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. inner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: inner_add_left)

lemma all_zero_iff [simp]: "(\<forall>u. inner x u = 0) \<longleftrightarrow> (x = 0)"
  by auto (use inner_eq_zero_iff in blast)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma inner_add_right: "inner x (y + z) = inner x y + inner x z"
  using inner_add_left [of y z x] by (simp only: inner_commute)

lemma inner_scaleR_right [simp]: "inner x (scaleR r y) = r * (inner x y)"
  using inner_scaleR_left [of r y x] by (simp only: inner_commute)

lemma inner_zero_right [simp]: "inner x 0 = 0"
  using inner_zero_left [of x] by (simp only: inner_commute)

lemma inner_minus_right [simp]: "inner x (- y) = - inner x y"
  using inner_minus_left [of y x] by (simp only: inner_commute)

lemma inner_diff_right: "inner x (y - z) = inner x y - inner x z"
  using inner_diff_left [of y z x] by (simp only: inner_commute)

lemma inner_sum_right: "inner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. inner x (f y))"
  using inner_sum_left [of f A x] by (simp only: inner_commute)

lemmas inner_add [algebra_simps] = inner_add_left inner_add_right
lemmas inner_diff [algebra_simps]  = inner_diff_left inner_diff_right
lemmas inner_scaleR = inner_scaleR_left inner_scaleR_right

text \<open>Legacy theorem names\<close>
lemmas inner_left_distrib = inner_add_left
lemmas inner_right_distrib = inner_add_right
lemmas inner_distrib = inner_left_distrib inner_right_distrib

lemma inner_gt_zero_iff [simp]: "0 < inner x x \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma power2_norm_eq_inner: "(norm x)\<^sup>2 = inner x x"
  by (simp add: norm_eq_sqrt_inner)

text \<open>Identities involving real multiplication and division.\<close>

lemma inner_mult_left: "inner (of_real m * a) b = m * (inner a b)"
  by (metis real_inner_class.inner_scaleR_left scaleR_conv_of_real)

lemma inner_mult_right: "inner a (of_real m * b) = m * (inner a b)"
  by (metis real_inner_class.inner_scaleR_right scaleR_conv_of_real)

lemma inner_mult_left': "inner (a * of_real m) b = m * (inner a b)"
  by (simp add: of_real_def)

lemma inner_mult_right': "inner a (b * of_real m) = (inner a b) * m"
  by (simp add: of_real_def real_inner_class.inner_scaleR_right)

lemma Cauchy_Schwarz_ineq:
  "(inner x y)\<^sup>2 \<le> inner x x * inner y y"
proof (cases)
  assume "y = 0"
  thus ?thesis by simp
next
  assume y: "y \<noteq> 0"
  let ?r = "inner x y / inner y y"
  have "0 \<le> inner (x - scaleR ?r y) (x - scaleR ?r y)"
    by (rule inner_ge_zero)
  also have "\<dots> = inner x x - inner y x * ?r"
    by (simp add: inner_diff)
  also have "\<dots> = inner x x - (inner x y)\<^sup>2 / inner y y"
    by (simp add: power2_eq_square inner_commute)
  finally have "0 \<le> inner x x - (inner x y)\<^sup>2 / inner y y" .
  hence "(inner x y)\<^sup>2 / inner y y \<le> inner x x"
    by (simp add: le_diff_eq)
  thus "(inner x y)\<^sup>2 \<le> inner x x * inner y y"
    by (simp add: pos_divide_le_eq y)
qed

lemma Cauchy_Schwarz_ineq2:
  "\<bar>inner x y\<bar> \<le> norm x * norm y"
proof (rule power2_le_imp_le)
  have "(inner x y)\<^sup>2 \<le> inner x x * inner y y"
    using Cauchy_Schwarz_ineq .
  thus "\<bar>inner x y\<bar>\<^sup>2 \<le> (norm x * norm y)\<^sup>2"
    by (simp add: power_mult_distrib power2_norm_eq_inner)
  show "0 \<le> norm x * norm y"
    unfolding norm_eq_sqrt_inner
    by (intro mult_nonneg_nonneg real_sqrt_ge_zero inner_ge_zero)
qed

lemma norm_cauchy_schwarz: "inner x y \<le> norm x * norm y"
  using Cauchy_Schwarz_ineq2 [of x y] by auto

subclass real_normed_vector
proof
  fix a :: real and x y :: 'a
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_eq_sqrt_inner by simp
  show "norm (x + y) \<le> norm x + norm y"
    proof (rule power2_le_imp_le)
      have "inner x y \<le> norm x * norm y"
        by (rule norm_cauchy_schwarz)
      thus "(norm (x + y))\<^sup>2 \<le> (norm x + norm y)\<^sup>2"
        unfolding power2_sum power2_norm_eq_inner
        by (simp add: inner_add inner_commute)
      show "0 \<le> norm x + norm y"
        unfolding norm_eq_sqrt_inner by simp
    qed
  have "sqrt (a\<^sup>2 * inner x x) = \<bar>a\<bar> * sqrt (inner x x)"
    by (simp add: real_sqrt_mult)
  then show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
    unfolding norm_eq_sqrt_inner
    by (simp add: power2_eq_square mult.assoc)
qed

end

lemma square_bound_lemma:
  fixes x :: real
  shows "x < (1 + x) * (1 + x)"
proof -
  have "(x + 1/2)\<^sup>2 + 3/4 > 0"
    using zero_le_power2[of "x+1/2"] by arith
  then show ?thesis
    by (simp add: field_simps power2_eq_square)
qed

lemma square_continuous:
  fixes e :: real
  shows "e > 0 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>y. \<bar>y - x\<bar> < d \<longrightarrow> \<bar>y * y - x * x\<bar> < e)"
  using isCont_power[OF continuous_ident, of x, unfolded isCont_def LIM_eq, rule_format, of e 2]
  by (force simp add: power2_eq_square)

lemma norm_le: "norm x \<le> norm y \<longleftrightarrow> inner x x \<le> inner y y"
  by (simp add: norm_eq_sqrt_inner)

lemma norm_lt: "norm x < norm y \<longleftrightarrow> inner x x < inner y y"
  by (simp add: norm_eq_sqrt_inner)

lemma norm_eq: "norm x = norm y \<longleftrightarrow> inner x x = inner y y"
  apply (subst order_eq_iff)
  apply (auto simp: norm_le)
  done

lemma norm_eq_1: "norm x = 1 \<longleftrightarrow> inner x x = 1"
  by (simp add: norm_eq_sqrt_inner)

lemma inner_divide_left:
  fixes a :: "'a :: {real_inner,real_div_algebra}"
  shows "inner (a / of_real m) b = (inner a b) / m"
  by (metis (no_types) divide_inverse inner_commute inner_scaleR_right mult.left_neutral mult.right_neutral mult_scaleR_right of_real_inverse scaleR_conv_of_real times_divide_eq_left)

lemma inner_divide_right:
  fixes a :: "'a :: {real_inner,real_div_algebra}"
  shows "inner a (b / of_real m) = (inner a b) / m"
  by (metis inner_commute inner_divide_left)

text \<open>
  Re-enable constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniform_space \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>

lemma bounded_bilinear_inner:
  "bounded_bilinear (inner::'a::real_inner \<Rightarrow> 'a \<Rightarrow> real)"
proof
  fix x y z :: 'a and r :: real
  show "inner (x + y) z = inner x z + inner y z"
    by (rule inner_add_left)
  show "inner x (y + z) = inner x y + inner x z"
    by (rule inner_add_right)
  show "inner (scaleR r x) y = scaleR r (inner x y)"
    unfolding real_scaleR_def by (rule inner_scaleR_left)
  show "inner x (scaleR r y) = scaleR r (inner x y)"
    unfolding real_scaleR_def by (rule inner_scaleR_right)
  show "\<exists>K. \<forall>x y::'a. norm (inner x y) \<le> norm x * norm y * K"
  proof
    show "\<forall>x y::'a. norm (inner x y) \<le> norm x * norm y * 1"
      by (simp add: Cauchy_Schwarz_ineq2)
  qed
qed

lemmas tendsto_inner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_inner]

lemmas isCont_inner [simp] =
  bounded_bilinear.isCont [OF bounded_bilinear_inner]

lemmas has_derivative_inner [derivative_intros] =
  bounded_bilinear.FDERIV [OF bounded_bilinear_inner]

lemmas bounded_linear_inner_left =
  bounded_bilinear.bounded_linear_left [OF bounded_bilinear_inner]

lemmas bounded_linear_inner_right =
  bounded_bilinear.bounded_linear_right [OF bounded_bilinear_inner]

lemmas bounded_linear_inner_left_comp = bounded_linear_inner_left[THEN bounded_linear_compose]

lemmas bounded_linear_inner_right_comp = bounded_linear_inner_right[THEN bounded_linear_compose]

lemmas has_derivative_inner_right [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_linear_inner_right]

lemmas has_derivative_inner_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_linear_inner_left]

lemma differentiable_inner [simp]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable at x within s \<Longrightarrow> (\<lambda>x. inner (f x) (g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_inner)


subsection \<open>Class instances\<close>

instantiation real :: real_inner
begin

definition inner_real_def [simp]: "inner = (*)"

instance
proof
  fix x y z r :: real
  show "inner x y = inner y x"
    unfolding inner_real_def by (rule mult.commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_real_def by (rule distrib_right)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_real_def real_scaleR_def by (rule mult.assoc)
  show "0 \<le> inner x x"
    unfolding inner_real_def by simp
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_real_def by simp
  show "norm x = sqrt (inner x x)"
    unfolding inner_real_def by simp
qed

end

lemma
  shows real_inner_1_left[simp]: "inner 1 x = x"
    and real_inner_1_right[simp]: "inner x 1 = x"
  by simp_all

instantiation complex :: real_inner
begin

definition inner_complex_def:
  "inner x y = Re x * Re y + Im x * Im y"

instance
proof
  fix x y z :: complex and r :: real
  show "inner x y = inner y x"
    unfolding inner_complex_def by (simp add: mult.commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_complex_def by (simp add: distrib_right)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_complex_def by (simp add: distrib_left)
  show "0 \<le> inner x x"
    unfolding inner_complex_def by simp
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_complex_def
    by (simp add: add_nonneg_eq_0_iff complex_eq_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_complex_def norm_complex_def
    by (simp add: power2_eq_square)
qed

end

lemma complex_inner_1 [simp]: "inner 1 x = Re x"
  unfolding inner_complex_def by simp

lemma complex_inner_1_right [simp]: "inner x 1 = Re x"
  unfolding inner_complex_def by simp

lemma complex_inner_i_left [simp]: "inner \<i> x = Im x"
  unfolding inner_complex_def by simp

lemma complex_inner_i_right [simp]: "inner x \<i> = Im x"
  unfolding inner_complex_def by simp


lemma dot_square_norm: "inner x x = (norm x)\<^sup>2"
  by (simp only: power2_norm_eq_inner) (* TODO: move? *)

lemma norm_eq_square: "norm x = a \<longleftrightarrow> 0 \<le> a \<and> inner x x = a\<^sup>2"
  by (auto simp add: norm_eq_sqrt_inner)

lemma norm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> inner x x \<le> a\<^sup>2"
  apply (simp add: dot_square_norm abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_ge_square: "norm x \<ge> a \<longleftrightarrow> a \<le> 0 \<or> inner x x \<ge> a\<^sup>2"
  apply (simp add: dot_square_norm abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_lt_square: "norm x < a \<longleftrightarrow> 0 < a \<and> inner x x < a\<^sup>2"
  by (metis not_le norm_ge_square)

lemma norm_gt_square: "norm x > a \<longleftrightarrow> a < 0 \<or> inner x x > a\<^sup>2"
  by (metis norm_le_square not_less)

text\<open>Dot product in terms of the norm rather than conversely.\<close>

lemmas inner_simps = inner_add_left inner_add_right inner_diff_right inner_diff_left
  inner_scaleR_left inner_scaleR_right

lemma dot_norm: "inner x y = ((norm (x + y))\<^sup>2 - (norm x)\<^sup>2 - (norm y)\<^sup>2) / 2"
  by (simp only: power2_norm_eq_inner inner_simps inner_commute) auto

lemma dot_norm_neg: "inner x y = (((norm x)\<^sup>2 + (norm y)\<^sup>2) - (norm (x - y))\<^sup>2) / 2"
  by (simp only: power2_norm_eq_inner inner_simps inner_commute)
    (auto simp add: algebra_simps)

lemma of_real_inner_1 [simp]: 
  "inner (of_real x) (1 :: 'a :: {real_inner, real_normed_algebra_1}) = x"
  by (simp add: of_real_def dot_square_norm)
  
lemma summable_of_real_iff: 
  "summable (\<lambda>x. of_real (f x) :: 'a :: {real_normed_algebra_1,real_inner}) \<longleftrightarrow> summable f"
proof
  assume *: "summable (\<lambda>x. of_real (f x) :: 'a)"
  interpret bounded_linear "\<lambda>x::'a. inner x 1"
    by (rule bounded_linear_inner_left)
  from summable [OF *] show "summable f" by simp
qed (auto intro: summable_of_real)


subsection \<open>Gradient derivative\<close>

definition\<^marker>\<open>tag important\<close>
  gderiv ::
    "['a::real_inner \<Rightarrow> real, 'a, 'a] \<Rightarrow> bool"
          (\<open>(GDERIV (_)/ (_)/ :> (_))\<close> [1000, 1000, 60] 60)
where
  "GDERIV f x :> D \<longleftrightarrow> FDERIV f x :> (\<lambda>h. inner h D)"

lemma gderiv_deriv [simp]: "GDERIV f x :> D \<longleftrightarrow> DERIV f x :> D"
  by (simp only: gderiv_def has_field_derivative_def inner_real_def mult_commute_abs)

lemma GDERIV_DERIV_compose:
    "\<lbrakk>GDERIV f x :> df; DERIV g (f x) :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. g (f x)) x :> scaleR dg df"
  unfolding gderiv_def has_field_derivative_def
  apply (drule (1) has_derivative_compose)
  apply (simp add: ac_simps)
  done

lemma has_derivative_subst: "\<lbrakk>FDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> FDERIV f x :> d"
  by simp

lemma GDERIV_subst: "\<lbrakk>GDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> GDERIV f x :> d"
  by simp

lemma GDERIV_const: "GDERIV (\<lambda>x. k) x :> 0"
  unfolding gderiv_def inner_zero_right by (rule has_derivative_const)

lemma GDERIV_add:
    "\<lbrakk>GDERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. f x + g x) x :> df + dg"
  unfolding gderiv_def inner_add_right by (rule has_derivative_add)

lemma GDERIV_minus:
    "GDERIV f x :> df \<Longrightarrow> GDERIV (\<lambda>x. - f x) x :> - df"
  unfolding gderiv_def inner_minus_right by (rule has_derivative_minus)

lemma GDERIV_diff:
    "\<lbrakk>GDERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. f x - g x) x :> df - dg"
  unfolding gderiv_def inner_diff_right by (rule has_derivative_diff)

lemma GDERIV_scaleR:
    "\<lbrakk>DERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. scaleR (f x) (g x)) x
      :> (scaleR (f x) dg + scaleR df (g x))"
  unfolding gderiv_def has_field_derivative_def inner_add_right inner_scaleR_right
  apply (rule has_derivative_subst)
  apply (erule (1) has_derivative_scaleR)
  apply (simp add: ac_simps)
  done

lemma GDERIV_mult:
    "\<lbrakk>GDERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. f x * g x) x :> scaleR (f x) dg + scaleR (g x) df"
  unfolding gderiv_def
  apply (rule has_derivative_subst)
  apply (erule (1) has_derivative_mult)
  apply (simp add: inner_add ac_simps)
  done

lemma GDERIV_inverse:
    "\<lbrakk>GDERIV f x :> df; f x \<noteq> 0\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. inverse (f x)) x :> - (inverse (f x))\<^sup>2 *\<^sub>R df"
  by (metis DERIV_inverse GDERIV_DERIV_compose numerals(2))
  
lemma GDERIV_norm:
  assumes "x \<noteq> 0" shows "GDERIV (\<lambda>x. norm x) x :> sgn x"
    unfolding gderiv_def norm_eq_sqrt_inner
    by (rule derivative_eq_intros | force simp add: inner_commute sgn_div_norm norm_eq_sqrt_inner assms)+

lemmas has_derivative_norm = GDERIV_norm [unfolded gderiv_def]

bundle inner_syntax begin
notation inner (infix \<open>\<bullet>\<close> 70)
end

bundle no_inner_syntax begin
no_notation inner (infix \<open>\<bullet>\<close> 70)
end

end
