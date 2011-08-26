(*  Title:      HOL/Multivariate_Analysis/Euclidean_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Brian Huffman, Portland State University
*)

header {* Finite-Dimensional Inner Product Spaces *}

theory Euclidean_Space
imports
  Complex_Main
  "~~/src/HOL/Library/Inner_Product"
  "~~/src/HOL/Library/Product_Vector"
begin

subsection {* Type class of Euclidean spaces *}

class euclidean_space = real_inner +
  fixes Basis :: "'a set"
  assumes nonempty_Basis [simp]: "Basis \<noteq> {}"
  assumes finite_Basis [simp]: "finite Basis"
  assumes inner_Basis:
    "\<lbrakk>u \<in> Basis; v \<in> Basis\<rbrakk> \<Longrightarrow> inner u v = (if u = v then 1 else 0)"
  assumes euclidean_all_zero_iff:
    "(\<forall>u\<in>Basis. inner x u = 0) \<longleftrightarrow> (x = 0)"

  -- "FIXME: make this a separate definition"
  fixes dimension :: "'a itself \<Rightarrow> nat"
  assumes dimension_def: "dimension TYPE('a) = card Basis"

  -- "FIXME: eventually basis function can be removed"
  fixes basis :: "nat \<Rightarrow> 'a"
  assumes image_basis: "basis ` {..<dimension TYPE('a)} = Basis"
  assumes basis_finite: "basis ` {dimension TYPE('a)..} = {0}"

syntax "_type_dimension" :: "type => nat" ("(1DIM/(1'(_')))")

translations "DIM('t)" == "CONST dimension (TYPE('t))"

lemma (in euclidean_space) norm_Basis: "u \<in> Basis \<Longrightarrow> norm u = 1"
  unfolding norm_eq_sqrt_inner by (simp add: inner_Basis)

lemma (in euclidean_space) sgn_Basis: "u \<in> Basis \<Longrightarrow> sgn u = u"
  unfolding sgn_div_norm by (simp add: norm_Basis scaleR_one)

lemma (in euclidean_space) Basis_zero [simp]: "0 \<notin> Basis"
proof
  assume "0 \<in> Basis" thus "False"
    using inner_Basis [of 0 0] by simp
qed

lemma (in euclidean_space) nonzero_Basis: "u \<in> Basis \<Longrightarrow> u \<noteq> 0"
  by clarsimp

text {* Lemmas related to @{text basis} function. *}

lemma (in euclidean_space) euclidean_all_zero:
  "(\<forall>i<DIM('a). inner (basis i) x = 0) \<longleftrightarrow> (x = 0)"
  using euclidean_all_zero_iff [of x, folded image_basis]
  unfolding ball_simps by (simp add: Ball_def inner_commute)

lemma (in euclidean_space) basis_zero [simp]:
  "DIM('a) \<le> i \<Longrightarrow> basis i = 0"
  using basis_finite by auto

lemma (in euclidean_space) DIM_positive [intro]: "0 < DIM('a)"
  unfolding dimension_def by (simp add: card_gt_0_iff)

lemma (in euclidean_space) basis_inj [simp, intro]: "inj_on basis {..<DIM('a)}"
  by (simp add: inj_on_iff_eq_card image_basis dimension_def [symmetric])

lemma (in euclidean_space) basis_in_Basis [simp]:
  "basis i \<in> Basis \<longleftrightarrow> i < DIM('a)"
  by (cases "i < DIM('a)", simp add: image_basis [symmetric], simp)

lemma (in euclidean_space) Basis_elim:
  assumes "u \<in> Basis" obtains i where "i < DIM('a)" and "u = basis i"
  using assms unfolding image_basis [symmetric] by fast

lemma (in euclidean_space) basis_orthonormal:
    "\<forall>i<DIM('a). \<forall>j<DIM('a).
      inner (basis i) (basis j) = (if i = j then 1 else 0)"
  apply clarify
  apply (simp add: inner_Basis)
  apply (simp add: basis_inj [unfolded inj_on_def])
  done

lemma (in euclidean_space) dot_basis:
  "inner (basis i) (basis j) = (if i = j \<and> i < DIM('a) then 1 else 0)"
proof (cases "(i < DIM('a) \<and> j < DIM('a))")
  case False
  hence "inner (basis i) (basis j) = 0" by auto
  thus ?thesis using False by auto
next
  case True thus ?thesis using basis_orthonormal by auto
qed

lemma (in euclidean_space) basis_eq_0_iff [simp]:
  "basis i = 0 \<longleftrightarrow> DIM('a) \<le> i"
proof -
  have "inner (basis i) (basis i) = 0 \<longleftrightarrow> DIM('a) \<le> i"
    by (simp add: dot_basis)
  thus ?thesis by simp
qed

lemma (in euclidean_space) norm_basis [simp]:
  "norm (basis i) = (if i < DIM('a) then 1 else 0)"
  unfolding norm_eq_sqrt_inner dot_basis by simp

lemma (in euclidean_space) basis_neq_0 [intro]:
  assumes "i<DIM('a)" shows "(basis i) \<noteq> 0"
  using assms by simp

subsubsection {* Projecting components *}

definition (in euclidean_space) euclidean_component (infixl "$$" 90)
  where "x $$ i = inner (basis i) x"

lemma bounded_linear_euclidean_component:
  "bounded_linear (\<lambda>x. euclidean_component x i)"
  unfolding euclidean_component_def
  by (rule bounded_linear_inner_right)

lemmas tendsto_euclidean_component [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_euclidean_component]

lemmas isCont_euclidean_component [simp] =
  bounded_linear.isCont [OF bounded_linear_euclidean_component]

lemma euclidean_component_zero [simp]: "0 $$ i = 0"
  unfolding euclidean_component_def by (rule inner_zero_right)

lemma euclidean_component_add [simp]: "(x + y) $$ i = x $$ i + y $$ i"
  unfolding euclidean_component_def by (rule inner_add_right)

lemma euclidean_component_diff [simp]: "(x - y) $$ i = x $$ i - y $$ i"
  unfolding euclidean_component_def by (rule inner_diff_right)

lemma euclidean_component_minus [simp]: "(- x) $$ i = - (x $$ i)"
  unfolding euclidean_component_def by (rule inner_minus_right)

lemma euclidean_component_scaleR [simp]: "(scaleR a x) $$ i = a * (x $$ i)"
  unfolding euclidean_component_def by (rule inner_scaleR_right)

lemma euclidean_component_setsum [simp]: "(\<Sum>x\<in>A. f x) $$ i = (\<Sum>x\<in>A. f x $$ i)"
  unfolding euclidean_component_def by (rule inner_setsum_right)

lemma euclidean_eqI:
  fixes x y :: "'a::euclidean_space"
  assumes "\<And>i. i < DIM('a) \<Longrightarrow> x $$ i = y $$ i" shows "x = y"
proof -
  from assms have "\<forall>i<DIM('a). (x - y) $$ i = 0"
    by simp
  then show "x = y"
    unfolding euclidean_component_def euclidean_all_zero by simp
qed

lemma euclidean_eq:
  fixes x y :: "'a::euclidean_space"
  shows "x = y \<longleftrightarrow> (\<forall>i<DIM('a). x $$ i = y $$ i)"
  by (auto intro: euclidean_eqI)

lemma (in euclidean_space) basis_component [simp]:
  "basis i $$ j = (if i = j \<and> i < DIM('a) then 1 else 0)"
  unfolding euclidean_component_def dot_basis by auto

lemma (in euclidean_space) basis_at_neq_0 [intro]:
  "i < DIM('a) \<Longrightarrow> basis i $$ i \<noteq> 0"
  by simp

lemma (in euclidean_space) euclidean_component_ge [simp]:
  assumes "i \<ge> DIM('a)" shows "x $$ i = 0"
  unfolding euclidean_component_def basis_zero[OF assms] by simp

lemmas euclidean_simps =
  euclidean_component_add
  euclidean_component_diff
  euclidean_component_scaleR
  euclidean_component_minus
  euclidean_component_setsum
  basis_component

lemma euclidean_representation:
  fixes x :: "'a::euclidean_space"
  shows "x = (\<Sum>i<DIM('a). (x$$i) *\<^sub>R basis i)"
  apply (rule euclidean_eqI)
  apply (simp add: if_distrib setsum_delta cong: if_cong)
  done

subsubsection {* Binder notation for vectors *}

definition (in euclidean_space) Chi (binder "\<chi>\<chi> " 10) where
  "(\<chi>\<chi> i. f i) = (\<Sum>i<DIM('a). f i *\<^sub>R basis i)"

lemma euclidean_lambda_beta [simp]:
  "((\<chi>\<chi> i. f i)::'a::euclidean_space) $$ j = (if j < DIM('a) then f j else 0)"
  by (auto simp: Chi_def if_distrib setsum_cases intro!: setsum_cong)

lemma euclidean_lambda_beta':
  "j < DIM('a) \<Longrightarrow> ((\<chi>\<chi> i. f i)::'a::euclidean_space) $$ j = f j"
  by simp

lemma euclidean_lambda_beta'':"(\<forall>j < DIM('a::euclidean_space). P j (((\<chi>\<chi> i. f i)::'a) $$ j)) \<longleftrightarrow>
  (\<forall>j < DIM('a::euclidean_space). P j (f j))" by auto

lemma euclidean_beta_reduce[simp]:
  "(\<chi>\<chi> i. x $$ i) = (x::'a::euclidean_space)"
  by (simp add: euclidean_eq)

lemma euclidean_lambda_beta_0[simp]:
    "((\<chi>\<chi> i. f i)::'a::euclidean_space) $$ 0 = f 0"
  by (simp add: DIM_positive)

lemma euclidean_inner:
  "inner x (y::'a) = (\<Sum>i<DIM('a::euclidean_space). (x $$ i) * (y $$ i))"
  by (subst (1 2) euclidean_representation,
    simp add: inner_setsum_left inner_setsum_right
    dot_basis if_distrib setsum_cases mult_commute)

lemma component_le_norm: "\<bar>x$$i\<bar> \<le> norm (x::'a::euclidean_space)"
  unfolding euclidean_component_def
  by (rule order_trans [OF Cauchy_Schwarz_ineq2]) simp

subsection {* Class instances *}

subsubsection {* Type @{typ real} *}

instantiation real :: euclidean_space
begin

definition
  "Basis = {1::real}"

definition
  "dimension (t::real itself) = 1"

definition [simp]:
  "basis i = (if i = 0 then 1 else (0::real))"

lemma DIM_real [simp]: "DIM(real) = 1"
  by (rule dimension_real_def)

instance
  by default (auto simp add: Basis_real_def)

end

subsubsection {* Type @{typ complex} *}

 (* TODO: move these to Complex.thy/Inner_Product.thy *)

lemma norm_ii [simp]: "norm ii = 1"
  unfolding i_def by simp

lemma complex_inner_1 [simp]: "inner 1 x = Re x"
  unfolding inner_complex_def by simp

lemma complex_inner_1_right [simp]: "inner x 1 = Re x"
  unfolding inner_complex_def by simp

lemma complex_inner_ii_left [simp]: "inner ii x = Im x"
  unfolding inner_complex_def by simp

lemma complex_inner_ii_right [simp]: "inner x ii = Im x"
  unfolding inner_complex_def by simp

instantiation complex :: euclidean_space
begin

definition Basis_complex_def:
  "Basis = {1, ii}"

definition
  "dimension (t::complex itself) = 2"

definition
  "basis i = (if i = 0 then 1 else if i = 1 then ii else 0)"

instance
  by default (auto simp add: Basis_complex_def dimension_complex_def
    basis_complex_def intro: complex_eqI split: split_if_asm)

end

lemma DIM_complex[simp]: "DIM(complex) = 2"
  by (rule dimension_complex_def)

subsubsection {* Type @{typ "'a \<times> 'b"} *}

instantiation prod :: (euclidean_space, euclidean_space) euclidean_space
begin

definition
  "Basis = (\<lambda>u. (u, 0)) ` Basis \<union> (\<lambda>v. (0, v)) ` Basis"

definition
  "dimension (t::('a \<times> 'b) itself) = DIM('a) + DIM('b)"

definition
  "basis i = (if i < DIM('a) then (basis i, 0) else (0, basis (i - DIM('a))))"

instance proof
  show "(Basis :: ('a \<times> 'b) set) \<noteq> {}"
    unfolding Basis_prod_def by simp
next
  show "finite (Basis :: ('a \<times> 'b) set)"
    unfolding Basis_prod_def by simp
next
  fix u v :: "'a \<times> 'b"
  assume "u \<in> Basis" and "v \<in> Basis"
  thus "inner u v = (if u = v then 1 else 0)"
    unfolding Basis_prod_def inner_prod_def
    by (auto simp add: inner_Basis split: split_if_asm)
next
  fix x :: "'a \<times> 'b"
  show "(\<forall>u\<in>Basis. inner x u = 0) \<longleftrightarrow> x = 0"
    unfolding Basis_prod_def ball_Un ball_simps
    by (simp add: inner_prod_def prod_eq_iff euclidean_all_zero_iff)
next
  show "DIM('a \<times> 'b) = card (Basis :: ('a \<times> 'b) set)"
    unfolding dimension_prod_def Basis_prod_def
    by (simp add: card_Un_disjoint disjoint_iff_not_equal
      card_image inj_on_def dimension_def)
next
  show "basis ` {..<DIM('a \<times> 'b)} = (Basis :: ('a \<times> 'b) set)"
    by (auto simp add: Basis_prod_def dimension_prod_def basis_prod_def
      image_def elim!: Basis_elim)
next
  show "basis ` {DIM('a \<times> 'b)..} = {0::('a \<times> 'b)}"
    by (auto simp add: dimension_prod_def basis_prod_def prod_eq_iff image_def)
qed

end

end
