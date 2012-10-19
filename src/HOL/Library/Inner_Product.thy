(*  Title:      HOL/Library/Inner_Product.thy
    Author:     Brian Huffman
*)

header {* Inner Product Spaces and the Gradient Derivative *}

theory Inner_Product
imports FrechetDeriv
begin

subsection {* Real inner product spaces *}

text {*
  Temporarily relax type constraints for @{term "open"},
  @{term dist}, and @{term norm}.
*}

setup {* Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::open set \<Rightarrow> bool"}) *}

setup {* Sign.add_const_constraint
  (@{const_name dist}, SOME @{typ "'a::dist \<Rightarrow> 'a \<Rightarrow> real"}) *}

setup {* Sign.add_const_constraint
  (@{const_name norm}, SOME @{typ "'a::norm \<Rightarrow> real"}) *}

class real_inner = real_vector + sgn_div_norm + dist_norm + open_dist +
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
  by (simp add: diff_minus inner_add_left)

lemma inner_setsum_left: "inner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. inner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: inner_add_left)

text {* Transfer distributivity rules to right argument. *}

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

lemma inner_setsum_right: "inner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. inner x (f y))"
  using inner_setsum_left [of f A x] by (simp only: inner_commute)

lemmas inner_add [algebra_simps] = inner_add_left inner_add_right
lemmas inner_diff [algebra_simps]  = inner_diff_left inner_diff_right
lemmas inner_scaleR = inner_scaleR_left inner_scaleR_right

text {* Legacy theorem names *}
lemmas inner_left_distrib = inner_add_left
lemmas inner_right_distrib = inner_add_right
lemmas inner_distrib = inner_left_distrib inner_right_distrib

lemma inner_gt_zero_iff [simp]: "0 < inner x x \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma power2_norm_eq_inner: "(norm x)\<twosuperior> = inner x x"
  by (simp add: norm_eq_sqrt_inner)

lemma Cauchy_Schwarz_ineq:
  "(inner x y)\<twosuperior> \<le> inner x x * inner y y"
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
  also have "\<dots> = inner x x - (inner x y)\<twosuperior> / inner y y"
    by (simp add: power2_eq_square inner_commute)
  finally have "0 \<le> inner x x - (inner x y)\<twosuperior> / inner y y" .
  hence "(inner x y)\<twosuperior> / inner y y \<le> inner x x"
    by (simp add: le_diff_eq)
  thus "(inner x y)\<twosuperior> \<le> inner x x * inner y y"
    by (simp add: pos_divide_le_eq y)
qed

lemma Cauchy_Schwarz_ineq2:
  "\<bar>inner x y\<bar> \<le> norm x * norm y"
proof (rule power2_le_imp_le)
  have "(inner x y)\<twosuperior> \<le> inner x x * inner y y"
    using Cauchy_Schwarz_ineq .
  thus "\<bar>inner x y\<bar>\<twosuperior> \<le> (norm x * norm y)\<twosuperior>"
    by (simp add: power_mult_distrib power2_norm_eq_inner)
  show "0 \<le> norm x * norm y"
    unfolding norm_eq_sqrt_inner
    by (intro mult_nonneg_nonneg real_sqrt_ge_zero inner_ge_zero)
qed

subclass real_normed_vector
proof
  fix a :: real and x y :: 'a
  show "0 \<le> norm x"
    unfolding norm_eq_sqrt_inner by simp
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_eq_sqrt_inner by simp
  show "norm (x + y) \<le> norm x + norm y"
    proof (rule power2_le_imp_le)
      have "inner x y \<le> norm x * norm y"
        by (rule order_trans [OF abs_ge_self Cauchy_Schwarz_ineq2])
      thus "(norm (x + y))\<twosuperior> \<le> (norm x + norm y)\<twosuperior>"
        unfolding power2_sum power2_norm_eq_inner
        by (simp add: inner_add inner_commute)
      show "0 \<le> norm x + norm y"
        unfolding norm_eq_sqrt_inner by simp
    qed
  have "sqrt (a\<twosuperior> * inner x x) = \<bar>a\<bar> * sqrt (inner x x)"
    by (simp add: real_sqrt_mult_distrib)
  then show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
    unfolding norm_eq_sqrt_inner
    by (simp add: power2_eq_square mult_assoc)
qed

end

text {*
  Re-enable constraints for @{term "open"},
  @{term dist}, and @{term norm}.
*}

setup {* Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::topological_space set \<Rightarrow> bool"}) *}

setup {* Sign.add_const_constraint
  (@{const_name dist}, SOME @{typ "'a::metric_space \<Rightarrow> 'a \<Rightarrow> real"}) *}

setup {* Sign.add_const_constraint
  (@{const_name norm}, SOME @{typ "'a::real_normed_vector \<Rightarrow> real"}) *}

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

lemmas FDERIV_inner =
  bounded_bilinear.FDERIV [OF bounded_bilinear_inner]

lemmas bounded_linear_inner_left =
  bounded_bilinear.bounded_linear_left [OF bounded_bilinear_inner]

lemmas bounded_linear_inner_right =
  bounded_bilinear.bounded_linear_right [OF bounded_bilinear_inner]


subsection {* Class instances *}

instantiation real :: real_inner
begin

definition inner_real_def [simp]: "inner = op *"

instance proof
  fix x y z r :: real
  show "inner x y = inner y x"
    unfolding inner_real_def by (rule mult_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_real_def by (rule distrib_right)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_real_def real_scaleR_def by (rule mult_assoc)
  show "0 \<le> inner x x"
    unfolding inner_real_def by simp
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_real_def by simp
  show "norm x = sqrt (inner x x)"
    unfolding inner_real_def by simp
qed

end

instantiation complex :: real_inner
begin

definition inner_complex_def:
  "inner x y = Re x * Re y + Im x * Im y"

instance proof
  fix x y z :: complex and r :: real
  show "inner x y = inner y x"
    unfolding inner_complex_def by (simp add: mult_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_complex_def by (simp add: distrib_right)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_complex_def by (simp add: distrib_left)
  show "0 \<le> inner x x"
    unfolding inner_complex_def by simp
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_complex_def
    by (simp add: add_nonneg_eq_0_iff complex_Re_Im_cancel_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_complex_def complex_norm_def
    by (simp add: power2_eq_square)
qed

end

lemma complex_inner_1 [simp]: "inner 1 x = Re x"
  unfolding inner_complex_def by simp

lemma complex_inner_1_right [simp]: "inner x 1 = Re x"
  unfolding inner_complex_def by simp

lemma complex_inner_ii_left [simp]: "inner ii x = Im x"
  unfolding inner_complex_def by simp

lemma complex_inner_ii_right [simp]: "inner x ii = Im x"
  unfolding inner_complex_def by simp


subsection {* Gradient derivative *}

definition
  gderiv ::
    "['a::real_inner \<Rightarrow> real, 'a, 'a] \<Rightarrow> bool"
          ("(GDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
where
  "GDERIV f x :> D \<longleftrightarrow> FDERIV f x :> (\<lambda>h. inner h D)"

lemma deriv_fderiv: "DERIV f x :> D \<longleftrightarrow> FDERIV f x :> (\<lambda>h. h * D)"
  by (simp only: deriv_def field_fderiv_def)

lemma gderiv_deriv [simp]: "GDERIV f x :> D \<longleftrightarrow> DERIV f x :> D"
  by (simp only: gderiv_def deriv_fderiv inner_real_def)

lemma GDERIV_DERIV_compose:
    "\<lbrakk>GDERIV f x :> df; DERIV g (f x) :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. g (f x)) x :> scaleR dg df"
  unfolding gderiv_def deriv_fderiv
  apply (drule (1) FDERIV_compose)
  apply (simp add: mult_ac)
  done

lemma FDERIV_subst: "\<lbrakk>FDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> FDERIV f x :> d"
  by simp

lemma GDERIV_subst: "\<lbrakk>GDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> GDERIV f x :> d"
  by simp

lemma GDERIV_const: "GDERIV (\<lambda>x. k) x :> 0"
  unfolding gderiv_def inner_zero_right by (rule FDERIV_const)

lemma GDERIV_add:
    "\<lbrakk>GDERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. f x + g x) x :> df + dg"
  unfolding gderiv_def inner_add_right by (rule FDERIV_add)

lemma GDERIV_minus:
    "GDERIV f x :> df \<Longrightarrow> GDERIV (\<lambda>x. - f x) x :> - df"
  unfolding gderiv_def inner_minus_right by (rule FDERIV_minus)

lemma GDERIV_diff:
    "\<lbrakk>GDERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. f x - g x) x :> df - dg"
  unfolding gderiv_def inner_diff_right by (rule FDERIV_diff)

lemma GDERIV_scaleR:
    "\<lbrakk>DERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. scaleR (f x) (g x)) x
      :> (scaleR (f x) dg + scaleR df (g x))"
  unfolding gderiv_def deriv_fderiv inner_add_right inner_scaleR_right
  apply (rule FDERIV_subst)
  apply (erule (1) FDERIV_scaleR)
  apply (simp add: mult_ac)
  done

lemma GDERIV_mult:
    "\<lbrakk>GDERIV f x :> df; GDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. f x * g x) x :> scaleR (f x) dg + scaleR (g x) df"
  unfolding gderiv_def
  apply (rule FDERIV_subst)
  apply (erule (1) FDERIV_mult)
  apply (simp add: inner_add mult_ac)
  done

lemma GDERIV_inverse:
    "\<lbrakk>GDERIV f x :> df; f x \<noteq> 0\<rbrakk>
     \<Longrightarrow> GDERIV (\<lambda>x. inverse (f x)) x :> - (inverse (f x))\<twosuperior> *\<^sub>R df"
  apply (erule GDERIV_DERIV_compose)
  apply (erule DERIV_inverse [folded numeral_2_eq_2])
  done

lemma GDERIV_norm:
  assumes "x \<noteq> 0" shows "GDERIV (\<lambda>x. norm x) x :> sgn x"
proof -
  have 1: "FDERIV (\<lambda>x. inner x x) x :> (\<lambda>h. inner x h + inner h x)"
    by (intro FDERIV_inner FDERIV_ident)
  have 2: "(\<lambda>h. inner x h + inner h x) = (\<lambda>h. inner h (scaleR 2 x))"
    by (simp add: fun_eq_iff inner_commute)
  have "0 < inner x x" using `x \<noteq> 0` by simp
  then have 3: "DERIV sqrt (inner x x) :> (inverse (sqrt (inner x x)) / 2)"
    by (rule DERIV_real_sqrt)
  have 4: "(inverse (sqrt (inner x x)) / 2) *\<^sub>R 2 *\<^sub>R x = sgn x"
    by (simp add: sgn_div_norm norm_eq_sqrt_inner)
  show ?thesis
    unfolding norm_eq_sqrt_inner
    apply (rule GDERIV_subst [OF _ 4])
    apply (rule GDERIV_DERIV_compose [where g=sqrt and df="scaleR 2 x"])
    apply (subst gderiv_def)
    apply (rule FDERIV_subst [OF _ 2])
    apply (rule 1)
    apply (rule 3)
    done
qed

lemmas FDERIV_norm = GDERIV_norm [unfolded gderiv_def]

end
