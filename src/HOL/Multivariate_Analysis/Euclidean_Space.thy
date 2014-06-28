(*  Title:      HOL/Multivariate_Analysis/Euclidean_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Brian Huffman, Portland State University
*)

header {* Finite-Dimensional Inner Product Spaces *}

theory Euclidean_Space
imports
  L2_Norm
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

abbreviation dimension :: "('a::euclidean_space) itself \<Rightarrow> nat" where
  "dimension TYPE('a) \<equiv> card (Basis :: 'a set)"

syntax "_type_dimension" :: "type => nat" ("(1DIM/(1'(_')))")

translations "DIM('t)" == "CONST dimension (TYPE('t))"

lemma (in euclidean_space) norm_Basis[simp]: "u \<in> Basis \<Longrightarrow> norm u = 1"
  unfolding norm_eq_sqrt_inner by (simp add: inner_Basis)

lemma (in euclidean_space) inner_same_Basis[simp]: "u \<in> Basis \<Longrightarrow> inner u u = 1"
  by (simp add: inner_Basis)

lemma (in euclidean_space) inner_not_same_Basis: "u \<in> Basis \<Longrightarrow> v \<in> Basis \<Longrightarrow> u \<noteq> v \<Longrightarrow> inner u v = 0"
  by (simp add: inner_Basis)

lemma (in euclidean_space) sgn_Basis: "u \<in> Basis \<Longrightarrow> sgn u = u"
  unfolding sgn_div_norm by (simp add: scaleR_one)

lemma (in euclidean_space) Basis_zero [simp]: "0 \<notin> Basis"
proof
  assume "0 \<in> Basis" thus "False"
    using inner_Basis [of 0 0] by simp
qed

lemma (in euclidean_space) nonzero_Basis: "u \<in> Basis \<Longrightarrow> u \<noteq> 0"
  by clarsimp

lemma (in euclidean_space) SOME_Basis: "(SOME i. i \<in> Basis) \<in> Basis"
  by (metis ex_in_conv nonempty_Basis someI_ex)

lemma (in euclidean_space) inner_setsum_left_Basis[simp]:
    "b \<in> Basis \<Longrightarrow> inner (\<Sum>i\<in>Basis. f i *\<^sub>R i) b = f b"
  by (simp add: inner_setsum_left inner_Basis if_distrib comm_monoid_add_class.setsum.If_cases)

lemma (in euclidean_space) euclidean_eqI:
  assumes b: "\<And>b. b \<in> Basis \<Longrightarrow> inner x b = inner y b" shows "x = y"
proof -
  from b have "\<forall>b\<in>Basis. inner (x - y) b = 0"
    by (simp add: inner_diff_left)
  then show "x = y"
    by (simp add: euclidean_all_zero_iff)
qed

lemma (in euclidean_space) euclidean_eq_iff:
  "x = y \<longleftrightarrow> (\<forall>b\<in>Basis. inner x b = inner y b)"
  by (auto intro: euclidean_eqI)

lemma (in euclidean_space) euclidean_representation_setsum:
  "(\<Sum>i\<in>Basis. f i *\<^sub>R i) = b \<longleftrightarrow> (\<forall>i\<in>Basis. f i = inner b i)"
  by (subst euclidean_eq_iff) simp

lemma (in euclidean_space) euclidean_representation_setsum':
  "b = (\<Sum>i\<in>Basis. f i *\<^sub>R i) \<longleftrightarrow> (\<forall>i\<in>Basis. f i = inner b i)"
  by (auto simp add: euclidean_representation_setsum[symmetric])

lemma (in euclidean_space) euclidean_representation: "(\<Sum>b\<in>Basis. inner x b *\<^sub>R b) = x"
  unfolding euclidean_representation_setsum by simp

lemma (in euclidean_space) choice_Basis_iff:
  fixes P :: "'a \<Rightarrow> real \<Rightarrow> bool"
  shows "(\<forall>i\<in>Basis. \<exists>x. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>Basis. P i (inner x i))"
  unfolding bchoice_iff
proof safe
  fix f assume "\<forall>i\<in>Basis. P i (f i)"
  then show "\<exists>x. \<forall>i\<in>Basis. P i (inner x i)"
    by (auto intro!: exI[of _ "\<Sum>i\<in>Basis. f i *\<^sub>R i"])
qed auto

lemma DIM_positive: "0 < DIM('a::euclidean_space)"
  by (simp add: card_gt_0_iff)

subsection {* Subclass relationships *}

instance euclidean_space \<subseteq> perfect_space
proof
  fix x :: 'a show "\<not> open {x}"
  proof
    assume "open {x}"
    then obtain e where "0 < e" and e: "\<forall>y. dist y x < e \<longrightarrow> y = x"
      unfolding open_dist by fast
    def y \<equiv> "x + scaleR (e/2) (SOME b. b \<in> Basis)"
    have [simp]: "(SOME b. b \<in> Basis) \<in> Basis"
      by (rule someI_ex) (auto simp: ex_in_conv)
    from `0 < e` have "y \<noteq> x"
      unfolding y_def by (auto intro!: nonzero_Basis)
    from `0 < e` have "dist y x < e"
      unfolding y_def by (simp add: dist_norm)
    from `y \<noteq> x` and `dist y x < e` show "False"
      using e by simp
  qed
qed

subsection {* Class instances *}

subsubsection {* Type @{typ real} *}

instantiation real :: euclidean_space
begin

definition 
  [simp]: "Basis = {1::real}"

instance
  by default auto

end

lemma DIM_real[simp]: "DIM(real) = 1"
  by simp

subsubsection {* Type @{typ complex} *}

instantiation complex :: euclidean_space
begin

definition Basis_complex_def:
  "Basis = {1, ii}"

instance
  by default (auto simp add: Basis_complex_def intro: complex_eqI split: split_if_asm)

end

lemma DIM_complex[simp]: "DIM(complex) = 2"
  unfolding Basis_complex_def by simp

subsubsection {* Type @{typ "'a \<times> 'b"} *}

instantiation prod :: (euclidean_space, euclidean_space) euclidean_space
begin

definition
  "Basis = (\<lambda>u. (u, 0)) ` Basis \<union> (\<lambda>v. (0, v)) ` Basis"

lemma setsum_Basis_prod_eq:
  fixes f::"('a*'b)\<Rightarrow>('a*'b)"
  shows "setsum f Basis = setsum (\<lambda>i. f (i, 0)) Basis + setsum (\<lambda>i. f (0, i)) Basis"
proof -
  have "inj_on (\<lambda>u. (u::'a, 0::'b)) Basis" "inj_on (\<lambda>u. (0::'a, u::'b)) Basis"
    by (auto intro!: inj_onI Pair_inject)
  thus ?thesis
    unfolding Basis_prod_def
    by (subst setsum.union_disjoint) (auto simp: Basis_prod_def setsum.reindex)
qed

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
qed

lemma DIM_prod[simp]: "DIM('a \<times> 'b) = DIM('a) + DIM('b)"
  unfolding Basis_prod_def
  by (subst card_Un_disjoint) (auto intro!: card_image arg_cong2[where f="op +"] inj_onI)

end

end
