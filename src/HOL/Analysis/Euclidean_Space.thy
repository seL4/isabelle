(*  Title:      HOL/Analysis/Euclidean_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Brian Huffman, Portland State University
*)

section \<open>Finite-Dimensional Inner Product Spaces\<close>

theory Euclidean_Space
imports
  L2_Norm Product_Vector
begin

subsection \<open>Type class of Euclidean spaces\<close>

class%important euclidean_space = real_inner +
  fixes Basis :: "'a set"
  assumes nonempty_Basis [simp]: "Basis \<noteq> {}"
  assumes finite_Basis [simp]: "finite Basis"
  assumes inner_Basis:
    "\<lbrakk>u \<in> Basis; v \<in> Basis\<rbrakk> \<Longrightarrow> inner u v = (if u = v then 1 else 0)"
  assumes euclidean_all_zero_iff:
    "(\<forall>u\<in>Basis. inner x u = 0) \<longleftrightarrow> (x = 0)"

syntax "_type_dimension" :: "type \<Rightarrow> nat"  ("(1DIM/(1'(_')))")
translations "DIM('a)" \<rightharpoonup> "CONST card (CONST Basis :: 'a set)"
typed_print_translation \<open>
  [(@{const_syntax card},
    fn ctxt => fn _ => fn [Const (@{const_syntax Basis}, Type (@{type_name set}, [T]))] =>
      Syntax.const @{syntax_const "_type_dimension"} $ Syntax_Phases.term_of_typ ctxt T)]
\<close>

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

lemma norm_some_Basis [simp]: "norm (SOME i. i \<in> Basis) = 1"
  by (simp add: SOME_Basis)

lemma (in euclidean_space) inner_sum_left_Basis[simp]:
    "b \<in> Basis \<Longrightarrow> inner (\<Sum>i\<in>Basis. f i *\<^sub>R i) b = f b"
  by (simp add: inner_sum_left inner_Basis if_distrib comm_monoid_add_class.sum.If_cases)

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

lemma (in euclidean_space) euclidean_representation_sum:
  "(\<Sum>i\<in>Basis. f i *\<^sub>R i) = b \<longleftrightarrow> (\<forall>i\<in>Basis. f i = inner b i)"
  by (subst euclidean_eq_iff) simp

lemma (in euclidean_space) euclidean_representation_sum':
  "b = (\<Sum>i\<in>Basis. f i *\<^sub>R i) \<longleftrightarrow> (\<forall>i\<in>Basis. f i = inner b i)"
  by (auto simp add: euclidean_representation_sum[symmetric])

lemma (in euclidean_space) euclidean_representation: "(\<Sum>b\<in>Basis. inner x b *\<^sub>R b) = x"
  unfolding euclidean_representation_sum by simp

lemma (in euclidean_space) euclidean_inner: "inner x y = (\<Sum>b\<in>Basis. (inner x b) * (inner y b))"
  by (subst (1 2) euclidean_representation [symmetric])
    (simp add: inner_sum_right inner_Basis ac_simps)

lemma (in euclidean_space) choice_Basis_iff:
  fixes P :: "'a \<Rightarrow> real \<Rightarrow> bool"
  shows "(\<forall>i\<in>Basis. \<exists>x. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>Basis. P i (inner x i))"
  unfolding bchoice_iff
proof safe
  fix f assume "\<forall>i\<in>Basis. P i (f i)"
  then show "\<exists>x. \<forall>i\<in>Basis. P i (inner x i)"
    by (auto intro!: exI[of _ "\<Sum>i\<in>Basis. f i *\<^sub>R i"])
qed auto

lemma (in euclidean_space) bchoice_Basis_iff:
  fixes P :: "'a \<Rightarrow> real \<Rightarrow> bool"
  shows "(\<forall>i\<in>Basis. \<exists>x\<in>A. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>Basis. inner x i \<in> A \<and> P i (inner x i))"
by (simp add: choice_Basis_iff Bex_def)

lemma (in euclidean_space) euclidean_representation_sum_fun:
    "(\<lambda>x. \<Sum>b\<in>Basis. inner (f x) b *\<^sub>R b) = f"
  by (rule ext) (simp add: euclidean_representation_sum)

lemma euclidean_isCont:
  assumes "\<And>b. b \<in> Basis \<Longrightarrow> isCont (\<lambda>x. (inner (f x) b) *\<^sub>R b) x"
    shows "isCont f x"
  apply (subst euclidean_representation_sum_fun [symmetric])
  apply (rule isCont_sum)
  apply (blast intro: assms)
  done

lemma DIM_positive [simp]: "0 < DIM('a::euclidean_space)"
  by (simp add: card_gt_0_iff)

lemma DIM_ge_Suc0 [simp]: "Suc 0 \<le> card Basis"
  by (meson DIM_positive Suc_leI)


lemma sum_inner_Basis_scaleR [simp]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_vector"
  assumes "b \<in> Basis" shows "(\<Sum>i\<in>Basis. (inner i b) *\<^sub>R f i) = f b"
  by (simp add: comm_monoid_add_class.sum.remove [OF finite_Basis assms]
         assms inner_not_same_Basis comm_monoid_add_class.sum.neutral)

lemma sum_inner_Basis_eq [simp]:
  assumes "b \<in> Basis" shows "(\<Sum>i\<in>Basis. (inner i b) * f i) = f b"
  by (simp add: comm_monoid_add_class.sum.remove [OF finite_Basis assms]
         assms inner_not_same_Basis comm_monoid_add_class.sum.neutral)

lemma sum_if_inner [simp]:
  assumes "i \<in> Basis" "j \<in> Basis"
    shows "inner (\<Sum>k\<in>Basis. if k = i then f i *\<^sub>R i else g k *\<^sub>R k) j = (if j=i then f j else g j)"
proof (cases "i=j")
  case True
  with assms show ?thesis
    by (auto simp: inner_sum_left if_distrib [of "\<lambda>x. inner x j"] inner_Basis cong: if_cong)
next
  case False
  have "(\<Sum>k\<in>Basis. inner (if k = i then f i *\<^sub>R i else g k *\<^sub>R k) j) =
        (\<Sum>k\<in>Basis. if k = j then g k else 0)"
    apply (rule sum.cong)
    using False assms by (auto simp: inner_Basis)
  also have "... = g j"
    using assms by auto
  finally show ?thesis
    using False by (auto simp: inner_sum_left)
qed

subsection%unimportant \<open>Subclass relationships\<close>

instance euclidean_space \<subseteq> perfect_space
proof
  fix x :: 'a show "\<not> open {x}"
  proof
    assume "open {x}"
    then obtain e where "0 < e" and e: "\<forall>y. dist y x < e \<longrightarrow> y = x"
      unfolding open_dist by fast
    define y where "y = x + scaleR (e/2) (SOME b. b \<in> Basis)"
    have [simp]: "(SOME b. b \<in> Basis) \<in> Basis"
      by (rule someI_ex) (auto simp: ex_in_conv)
    from \<open>0 < e\<close> have "y \<noteq> x"
      unfolding y_def by (auto intro!: nonzero_Basis)
    from \<open>0 < e\<close> have "dist y x < e"
      unfolding y_def by (simp add: dist_norm)
    from \<open>y \<noteq> x\<close> and \<open>dist y x < e\<close> show "False"
      using e by simp
  qed
qed

subsection \<open>Class instances\<close>

subsubsection%unimportant \<open>Type @{typ real}\<close>

instantiation%important real :: euclidean_space
begin

definition
  [simp]: "Basis = {1::real}"

instance
  by standard auto

end

lemma DIM_real[simp]: "DIM(real) = 1"
  by simp

subsubsection%unimportant \<open>Type @{typ complex}\<close>

instantiation%important complex :: euclidean_space
begin

definition Basis_complex_def: "Basis = {1, \<i>}"

instance
  by standard (auto simp add: Basis_complex_def intro: complex_eqI split: if_split_asm)

end

lemma DIM_complex[simp]: "DIM(complex) = 2"
  unfolding Basis_complex_def by simp

subsubsection%unimportant \<open>Type @{typ "'a \<times> 'b"}\<close>

instantiation%important prod :: (euclidean_space, euclidean_space) euclidean_space
begin

definition
  "Basis = (\<lambda>u. (u, 0)) ` Basis \<union> (\<lambda>v. (0, v)) ` Basis"

lemma sum_Basis_prod_eq:
  fixes f::"('a*'b)\<Rightarrow>('a*'b)"
  shows "sum f Basis = sum (\<lambda>i. f (i, 0)) Basis + sum (\<lambda>i. f (0, i)) Basis"
proof -
  have "inj_on (\<lambda>u. (u::'a, 0::'b)) Basis" "inj_on (\<lambda>u. (0::'a, u::'b)) Basis"
    by (auto intro!: inj_onI Pair_inject)
  thus ?thesis
    unfolding Basis_prod_def
    by (subst sum.union_disjoint) (auto simp: Basis_prod_def sum.reindex)
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
    by (auto simp add: inner_Basis split: if_split_asm)
next
  fix x :: "'a \<times> 'b"
  show "(\<forall>u\<in>Basis. inner x u = 0) \<longleftrightarrow> x = 0"
    unfolding Basis_prod_def ball_Un ball_simps
    by (simp add: inner_prod_def prod_eq_iff euclidean_all_zero_iff)
qed

lemma DIM_prod[simp]: "DIM('a \<times> 'b) = DIM('a) + DIM('b)"
  unfolding Basis_prod_def
  by (subst card_Un_disjoint) (auto intro!: card_image arg_cong2[where f="(+)"] inj_onI)

end

end
