(*  Title:      HOL/Analysis/Euclidean_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Brian Huffman, Portland State University
*)

section \<open>Finite-Dimensional Inner Product Spaces\<close>

theory Euclidean_Space
imports
  L2_Norm
  Inner_Product
  Product_Vector
begin


subsection\<^marker>\<open>tag unimportant\<close> \<open>Interlude: Some properties of real sets\<close>

lemma seq_mono_lemma:
  assumes "\<forall>(n::nat) \<ge> m. (d n :: real) < e n"
    and "\<forall>n \<ge> m. e n \<le> e m"
  shows "\<forall>n \<ge> m. d n < e m"
  using assms by force


subsection \<open>Type class of Euclidean spaces\<close>

class euclidean_space = real_inner +
  fixes Basis :: "'a set"
  assumes nonempty_Basis [simp]: "Basis \<noteq> {}"
  assumes finite_Basis [simp]: "finite Basis"
  assumes inner_Basis:
    "\<lbrakk>u \<in> Basis; v \<in> Basis\<rbrakk> \<Longrightarrow> inner u v = (if u = v then 1 else 0)"
  assumes euclidean_all_zero_iff:
    "(\<forall>u\<in>Basis. inner x u = 0) \<longleftrightarrow> (x = 0)"

syntax "_type_dimension" :: "type \<Rightarrow> nat"  ("(1DIM/(1'(_')))")
syntax_consts "_type_dimension" \<rightleftharpoons> card
translations "DIM('a)" \<rightharpoonup> "CONST card (CONST Basis :: 'a set)"
typed_print_translation \<open>
  [(\<^const_syntax>\<open>card\<close>,
    fn ctxt => fn _ => fn [Const (\<^const_syntax>\<open>Basis\<close>, Type (\<^type_name>\<open>set\<close>, [T]))] =>
      Syntax.const \<^syntax_const>\<open>_type_dimension\<close> $ Syntax_Phases.term_of_typ ctxt T)]
\<close>

lemma (in euclidean_space) norm_Basis[simp]: "u \<in> Basis \<Longrightarrow> norm u = 1"
  unfolding norm_eq_sqrt_inner by (simp add: inner_Basis)

lemma (in euclidean_space) inner_same_Basis[simp]: "u \<in> Basis \<Longrightarrow> inner u u = 1"
  by (simp add: inner_Basis)

lemma (in euclidean_space) inner_not_same_Basis: "u \<in> Basis \<Longrightarrow> v \<in> Basis \<Longrightarrow> u \<noteq> v \<Longrightarrow> inner u v = 0"
  by (simp add: inner_Basis)

lemma (in euclidean_space) sgn_Basis: "u \<in> Basis \<Longrightarrow> sgn u = u"
  unfolding sgn_div_norm by (simp add: scaleR_one)

lemma inner_sum_Basis[simp]: "i \<in> Basis \<Longrightarrow> inner (\<Sum>Basis) i = 1"
  by (simp add: inner_sum_left sum.If_cases inner_Basis)

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

lemma norm_le_componentwise:
   "(\<And>b. b \<in> Basis \<Longrightarrow> abs(inner x b) \<le> abs(inner y b)) \<Longrightarrow> norm x \<le> norm y"
  by (auto simp: norm_le euclidean_inner [of x x] euclidean_inner [of y y] abs_le_square_iff power2_eq_square intro!: sum_mono)

lemma Basis_le_norm: "b \<in> Basis \<Longrightarrow> \<bar>inner x b\<bar> \<le> norm x"
  by (rule order_trans [OF Cauchy_Schwarz_ineq2]) simp

lemma norm_bound_Basis_le: "b \<in> Basis \<Longrightarrow> norm x \<le> e \<Longrightarrow> \<bar>inner x b\<bar> \<le> e"
  by (metis Basis_le_norm order_trans)

lemma norm_bound_Basis_lt: "b \<in> Basis \<Longrightarrow> norm x < e \<Longrightarrow> \<bar>inner x b\<bar> < e"
  by (metis Basis_le_norm le_less_trans)

lemma norm_le_l1: "norm x \<le> (\<Sum>b\<in>Basis. \<bar>inner x b\<bar>)"
  apply (subst euclidean_representation[of x, symmetric])
  apply (rule order_trans[OF norm_sum])
  apply (auto intro!: sum_mono)
  done

lemma sum_norm_allsubsets_bound:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space"
  assumes fP: "finite P"
    and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (sum f Q) \<le> e"
  shows "(\<Sum>x\<in>P. norm (f x)) \<le> 2 * real DIM('n) * e"
proof -
  have "(\<Sum>x\<in>P. norm (f x)) \<le> (\<Sum>x\<in>P. \<Sum>b\<in>Basis. \<bar>inner (f x) b\<bar>)"
    by (rule sum_mono) (rule norm_le_l1)
  also have "(\<Sum>x\<in>P. \<Sum>b\<in>Basis. \<bar>inner (f x) b\<bar>) = (\<Sum>b\<in>Basis. \<Sum>x\<in>P. \<bar>inner (f x) b\<bar>)"
    by (rule sum.swap)
  also have "\<dots> \<le> of_nat (card (Basis :: 'n set)) * (2 * e)"
  proof (rule sum_bounded_above)
    fix i :: 'n
    assume i: "i \<in> Basis"
    have "norm (\<Sum>x\<in>P. \<bar>inner (f x) i\<bar>) \<le>
      norm (inner (\<Sum>x\<in>P \<inter> - {x. inner (f x) i < 0}. f x) i) + norm (inner (\<Sum>x\<in>P \<inter> {x. inner (f x) i < 0}. f x) i)"
      by (simp add: abs_real_def sum.If_cases[OF fP] sum_negf norm_triangle_ineq4 inner_sum_left
        del: real_norm_def)
    also have "\<dots> \<le> e + e"
      unfolding real_norm_def
      by (intro add_mono norm_bound_Basis_le i fPs) auto
    finally show "(\<Sum>x\<in>P. \<bar>inner (f x) i\<bar>) \<le> 2*e" by simp
  qed
  also have "\<dots> = 2 * real DIM('n) * e" by simp
  finally show ?thesis .
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Subclass relationships\<close>

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

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Type \<^typ>\<open>real\<close>\<close>

instantiation real :: euclidean_space
begin

definition
  [simp]: "Basis = {1::real}"

instance
  by standard auto

end

lemma DIM_real[simp]: "DIM(real) = 1"
  by simp

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Type \<^typ>\<open>complex\<close>\<close>

instantiation complex :: euclidean_space
begin

definition Basis_complex_def: "Basis = {1, \<i>}"

instance
  by standard (auto simp add: Basis_complex_def intro: complex_eqI split: if_split_asm)

end

lemma DIM_complex[simp]: "DIM(complex) = 2"
  unfolding Basis_complex_def by simp

lemma complex_Basis_1 [iff]: "(1::complex) \<in> Basis"
  by (simp add: Basis_complex_def)

lemma complex_Basis_i [iff]: "\<i> \<in> Basis"
  by (simp add: Basis_complex_def)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Type \<^typ>\<open>'a \<times> 'b\<close>\<close>

instantiation prod :: (real_inner, real_inner) real_inner
begin

definition inner_prod_def:
  "inner x y = inner (fst x) (fst y) + inner (snd x) (snd y)"

lemma inner_Pair [simp]: "inner (a, b) (c, d) = inner a c + inner b d"
  unfolding inner_prod_def by simp

instance
proof
  fix r :: real
  fix x y z :: "'a::real_inner \<times> 'b::real_inner"
  show "inner x y = inner y x"
    unfolding inner_prod_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_prod_def
    by (simp add: inner_add_left)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_prod_def
    by (simp add: distrib_left)
  show "0 \<le> inner x x"
    unfolding inner_prod_def
    by (intro add_nonneg_nonneg inner_ge_zero)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_prod_def prod_eq_iff
    by (simp add: add_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding norm_prod_def inner_prod_def
    by (simp add: power2_norm_eq_inner)
qed

end

lemma inner_Pair_0: "inner x (0, b) = inner (snd x) b" "inner x (a, 0) = inner (fst x) a"
    by (cases x, simp)+

instantiation prod :: (euclidean_space, euclidean_space) euclidean_space
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


subsection \<open>Locale instances\<close>

lemma finite_dimensional_vector_space_euclidean:
  "finite_dimensional_vector_space (*\<^sub>R) Basis"
proof unfold_locales
  show "finite (Basis::'a set)" by (metis finite_Basis)
  show "real_vector.independent (Basis::'a set)"
    unfolding dependent_def dependent_raw_def[symmetric]
    apply (subst span_finite)
    apply simp
    apply clarify
    apply (drule_tac f="inner a" in arg_cong)
    apply (simp add: inner_Basis inner_sum_right eq_commute)
    done
  show "module.span (*\<^sub>R) Basis = UNIV"
    unfolding span_finite [OF finite_Basis] span_raw_def[symmetric]
    by (auto intro!: euclidean_representation[symmetric])
qed

interpretation eucl?: finite_dimensional_vector_space "scaleR :: real => 'a => 'a::euclidean_space" "Basis"
  rewrites "module.dependent (*\<^sub>R) = dependent"
    and "module.representation (*\<^sub>R) = representation"
    and "module.subspace (*\<^sub>R) = subspace"
    and "module.span (*\<^sub>R) = span"
    and "vector_space.extend_basis (*\<^sub>R) = extend_basis"
    and "vector_space.dim (*\<^sub>R) = dim"
    and "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) = linear"
    and "Vector_Spaces.linear (*) (*\<^sub>R) = linear"
    and "finite_dimensional_vector_space.dimension Basis = DIM('a)"
    and "dimension = DIM('a)"
  by (auto simp add: dependent_raw_def representation_raw_def
      subspace_raw_def span_raw_def extend_basis_raw_def dim_raw_def linear_def
      real_scaleR_def[abs_def]
      finite_dimensional_vector_space.dimension_def
      intro!: finite_dimensional_vector_space.dimension_def
      finite_dimensional_vector_space_euclidean)

interpretation eucl?: finite_dimensional_vector_space_pair_1
  "scaleR::real\<Rightarrow>'a::euclidean_space\<Rightarrow>'a" Basis
  "scaleR::real\<Rightarrow>'b::real_vector \<Rightarrow> 'b"
  by unfold_locales

interpretation eucl?: finite_dimensional_vector_space_prod scaleR scaleR Basis Basis
  rewrites "Basis_pair = Basis"
    and "module_prod.scale (*\<^sub>R) (*\<^sub>R) = (scaleR::_\<Rightarrow>_\<Rightarrow>('a \<times> 'b))"
proof -
  show "finite_dimensional_vector_space_prod (*\<^sub>R) (*\<^sub>R) Basis Basis"
    by unfold_locales
  interpret finite_dimensional_vector_space_prod "(*\<^sub>R)" "(*\<^sub>R)" "Basis::'a set" "Basis::'b set"
    by fact
  show "Basis_pair = Basis"
    unfolding Basis_pair_def Basis_prod_def by auto
  show "module_prod.scale (*\<^sub>R) (*\<^sub>R) = scaleR"
    by (fact module_prod_scale_eq_scaleR)
qed

end
