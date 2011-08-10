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
  fixes dimension :: "'a itself \<Rightarrow> nat"
  fixes basis :: "nat \<Rightarrow> 'a"
  assumes DIM_positive [intro]:
    "0 < dimension TYPE('a)"
  assumes basis_zero [simp]:
    "dimension TYPE('a) \<le> i \<Longrightarrow> basis i = 0"
  assumes basis_orthonormal:
    "\<forall>i<dimension TYPE('a). \<forall>j<dimension TYPE('a).
      inner (basis i) (basis j) = (if i = j then 1 else 0)"
  assumes euclidean_all_zero:
    "(\<forall>i<dimension TYPE('a). inner (basis i) x = 0) \<longleftrightarrow> (x = 0)"

syntax "_type_dimension" :: "type => nat" ("(1DIM/(1'(_')))")

translations "DIM('t)" == "CONST dimension (TYPE('t))"

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
  by (rule inner.bounded_linear_right)

interpretation euclidean_component:
  bounded_linear "\<lambda>x. euclidean_component x i"
  by (rule bounded_linear_euclidean_component)

lemma euclidean_eqI:
  fixes x y :: "'a::euclidean_space"
  assumes "\<And>i. i < DIM('a) \<Longrightarrow> x $$ i = y $$ i" shows "x = y"
proof -
  from assms have "\<forall>i<DIM('a). (x - y) $$ i = 0"
    by (simp add: euclidean_component.diff)
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

lemma euclidean_scaleR:
  shows "(a *\<^sub>R x) $$ i = a * (x$$i)"
  unfolding euclidean_component_def by auto

lemmas euclidean_simps =
  euclidean_component.add
  euclidean_component.diff
  euclidean_scaleR
  euclidean_component.minus
  euclidean_component.setsum
  basis_component

lemma euclidean_representation:
  fixes x :: "'a::euclidean_space"
  shows "x = (\<Sum>i<DIM('a). (x$$i) *\<^sub>R basis i)"
  apply (rule euclidean_eqI)
  apply (simp add: euclidean_component.setsum euclidean_component.scaleR)
  apply (simp add: if_distrib setsum_delta cong: if_cong)
  done

subsubsection {* Binder notation for vectors *}

definition (in euclidean_space) Chi (binder "\<chi>\<chi> " 10) where
  "(\<chi>\<chi> i. f i) = (\<Sum>i<DIM('a). f i *\<^sub>R basis i)"

lemma euclidean_lambda_beta [simp]:
  "((\<chi>\<chi> i. f i)::'a::euclidean_space) $$ j = (if j < DIM('a) then f j else 0)"
  by (auto simp: euclidean_component.setsum euclidean_component.scaleR
    Chi_def if_distrib setsum_cases intro!: setsum_cong)

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
    simp add: inner_left.setsum inner_right.setsum
    dot_basis if_distrib setsum_cases mult_commute)

lemma component_le_norm: "\<bar>x$$i\<bar> \<le> norm (x::'a::euclidean_space)"
  unfolding euclidean_component_def
  by (rule order_trans [OF Cauchy_Schwarz_ineq2]) simp

subsection {* Class instances *}

subsubsection {* Type @{typ real} *}

instantiation real :: euclidean_space
begin

definition
  "dimension (t::real itself) = 1"

definition [simp]:
  "basis i = (if i = 0 then 1 else (0::real))"

lemma DIM_real [simp]: "DIM(real) = 1"
  by (rule dimension_real_def)

instance
  by default simp+

end

subsubsection {* Type @{typ complex} *}

instantiation complex :: euclidean_space
begin

definition
  "dimension (t::complex itself) = 2"

definition
  "basis i = (if i = 0 then 1 else if i = 1 then ii else 0)"

lemma all_less_Suc: "(\<forall>i<Suc n. P i) \<longleftrightarrow> (\<forall>i<n. P i) \<and> P n"
  by (auto simp add: less_Suc_eq)

instance proof
  show "0 < DIM(complex)"
    unfolding dimension_complex_def by simp
next
  fix i :: nat
  assume "DIM(complex) \<le> i" thus "basis i = (0::complex)"
    unfolding dimension_complex_def basis_complex_def by simp
next
  show "\<forall>i<DIM(complex). \<forall>j<DIM(complex).
    inner (basis i::complex) (basis j) = (if i = j then 1 else 0)"
    unfolding dimension_complex_def basis_complex_def inner_complex_def
    by (simp add: numeral_2_eq_2 all_less_Suc)
next
  fix x :: complex
  show "(\<forall>i<DIM(complex). inner (basis i) x = 0) \<longleftrightarrow> x = 0"
    unfolding dimension_complex_def basis_complex_def inner_complex_def
    by (simp add: numeral_2_eq_2 all_less_Suc complex_eq_iff)
qed

end

lemma DIM_complex[simp]: "DIM(complex) = 2"
  by (rule dimension_complex_def)

subsubsection {* Type @{typ "'a \<times> 'b"} *}

instantiation prod :: (euclidean_space, euclidean_space) euclidean_space
begin

definition
  "dimension (t::('a \<times> 'b) itself) = DIM('a) + DIM('b)"

definition
  "basis i = (if i < DIM('a) then (basis i, 0) else (0, basis (i - DIM('a))))"

lemma all_less_sum:
  fixes m n :: nat
  shows "(\<forall>i<(m + n). P i) \<longleftrightarrow> (\<forall>i<m. P i) \<and> (\<forall>i<n. P (m + i))"
  by (induct n, simp, simp add: all_less_Suc)

instance proof
  show "0 < DIM('a \<times> 'b)"
    unfolding dimension_prod_def by (intro add_pos_pos DIM_positive)
next
  fix i :: nat
  assume "DIM('a \<times> 'b) \<le> i" thus "basis i = (0::'a \<times> 'b)"
    unfolding dimension_prod_def basis_prod_def zero_prod_def
    by simp
next
  show "\<forall>i<DIM('a \<times> 'b). \<forall>j<DIM('a \<times> 'b).
    inner (basis i::'a \<times> 'b) (basis j) = (if i = j then 1 else 0)"
    unfolding dimension_prod_def basis_prod_def inner_prod_def
    unfolding all_less_sum prod_eq_iff
    by (simp add: basis_orthonormal)
next
  fix x :: "'a \<times> 'b"
  show "(\<forall>i<DIM('a \<times> 'b). inner (basis i) x = 0) \<longleftrightarrow> x = 0"
    unfolding dimension_prod_def basis_prod_def inner_prod_def
    unfolding all_less_sum prod_eq_iff
    by (simp add: euclidean_all_zero)
qed

end

end
