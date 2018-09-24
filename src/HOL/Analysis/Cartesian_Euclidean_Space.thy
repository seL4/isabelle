(* Title:      HOL/Analysis/Cartesian_Euclidean_Space.thy
   Some material by Jose Divasón, Tim Makarios and L C Paulson
*)

section%important \<open>Instantiates the finite Cartesian product of Euclidean spaces as a Euclidean space\<close>

theory Cartesian_Euclidean_Space
imports Cartesian_Space Derivative
begin

lemma%unimportant subspace_special_hyperplane: "subspace {x. x $ k = 0}"
  by (simp add: subspace_def)

lemma%important sum_mult_product:
  "sum h {..<A * B :: nat} = (\<Sum>i\<in>{..<A}. \<Sum>j\<in>{..<B}. h (j + i * B))"
  unfolding sum_nat_group[of h B A, unfolded atLeast0LessThan, symmetric]
proof%unimportant (rule sum.cong, simp, rule sum.reindex_cong)
  fix i
  show "inj_on (\<lambda>j. j + i * B) {..<B}" by (auto intro!: inj_onI)
  show "{i * B..<i * B + B} = (\<lambda>j. j + i * B) ` {..<B}"
  proof safe
    fix j assume "j \<in> {i * B..<i * B + B}"
    then show "j \<in> (\<lambda>j. j + i * B) ` {..<B}"
      by (auto intro!: image_eqI[of _ _ "j - i * B"])
  qed simp
qed simp

lemma%unimportant interval_cbox_cart: "{a::real^'n..b} = cbox a b"
  by (auto simp add: less_eq_vec_def mem_box Basis_vec_def inner_axis)

lemma%unimportant differentiable_vec:
  fixes S :: "'a::euclidean_space set"
  shows "vec differentiable_on S"
  by (simp add: linear_linear bounded_linear_imp_differentiable_on)

lemma%unimportant continuous_vec [continuous_intros]:
  fixes x :: "'a::euclidean_space"
  shows "isCont vec x"
  apply (clarsimp simp add: continuous_def LIM_def dist_vec_def L2_set_def)
  apply (rule_tac x="r / sqrt (real CARD('b))" in exI)
  by (simp add: mult.commute pos_less_divide_eq real_sqrt_mult)

lemma%unimportant box_vec_eq_empty [simp]:
  shows "cbox (vec a) (vec b) = {} \<longleftrightarrow> cbox a b = {}"
        "box (vec a) (vec b) = {} \<longleftrightarrow> box a b = {}"
  by (auto simp: Basis_vec_def mem_box box_eq_empty inner_axis)

subsection%important\<open>Closures and interiors of halfspaces\<close>

lemma%important interior_halfspace_le [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x \<le> b} = {x. a \<bullet> x < b}"
proof%unimportant -
  have *: "a \<bullet> x < b" if x: "x \<in> S" and S: "S \<subseteq> {x. a \<bullet> x \<le> b}" and "open S" for S x
  proof -
    obtain e where "e>0" and e: "cball x e \<subseteq> S"
      using \<open>open S\<close> open_contains_cball x by blast
    then have "x + (e / norm a) *\<^sub>R a \<in> cball x e"
      by (simp add: dist_norm)
    then have "x + (e / norm a) *\<^sub>R a \<in> S"
      using e by blast
    then have "x + (e / norm a) *\<^sub>R a \<in> {x. a \<bullet> x \<le> b}"
      using S by blast
    moreover have "e * (a \<bullet> a) / norm a > 0"
      by (simp add: \<open>0 < e\<close> assms)
    ultimately show ?thesis
      by (simp add: algebra_simps)
  qed
  show ?thesis
    by (rule interior_unique) (auto simp: open_halfspace_lt *)
qed

lemma%unimportant interior_halfspace_ge [simp]:
   "a \<noteq> 0 \<Longrightarrow> interior {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x > b}"
using interior_halfspace_le [of "-a" "-b"] by simp

lemma%important interior_halfspace_component_le [simp]:
     "interior {x. x$k \<le> a} = {x :: (real^'n). x$k < a}" (is "?LE")
  and interior_halfspace_component_ge [simp]:
     "interior {x. x$k \<ge> a} = {x :: (real^'n). x$k > a}" (is "?GE")
proof%unimportant -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?LE ?GE
    using interior_halfspace_le [of "axis k (1::real)" a]
          interior_halfspace_ge [of "axis k (1::real)" a] by auto
qed

lemma%unimportant closure_halfspace_lt [simp]:
  assumes "a \<noteq> 0"
    shows "closure {x. a \<bullet> x < b} = {x. a \<bullet> x \<le> b}"
proof -
  have [simp]: "-{x. a \<bullet> x < b} = {x. a \<bullet> x \<ge> b}"
    by (force simp:)
  then show ?thesis
    using interior_halfspace_ge [of a b] assms
    by (force simp: closure_interior)
qed

lemma%unimportant closure_halfspace_gt [simp]:
   "a \<noteq> 0 \<Longrightarrow> closure {x. a \<bullet> x > b} = {x. a \<bullet> x \<ge> b}"
using closure_halfspace_lt [of "-a" "-b"] by simp

lemma%important closure_halfspace_component_lt [simp]:
     "closure {x. x$k < a} = {x :: (real^'n). x$k \<le> a}" (is "?LE")
  and closure_halfspace_component_gt [simp]:
     "closure {x. x$k > a} = {x :: (real^'n). x$k \<ge> a}" (is "?GE")
proof%unimportant -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?LE ?GE
    using closure_halfspace_lt [of "axis k (1::real)" a]
          closure_halfspace_gt [of "axis k (1::real)" a] by auto
qed

lemma%unimportant interior_hyperplane [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x = b} = {}"
proof%unimportant -
  have [simp]: "{x. a \<bullet> x = b} = {x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x \<ge> b}"
    by (force simp:)
  then show ?thesis
    by (auto simp: assms)
qed

lemma%unimportant frontier_halfspace_le:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<le> b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def closed_halfspace_le)
qed

lemma%unimportant frontier_halfspace_ge:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def closed_halfspace_ge)
qed

lemma%unimportant frontier_halfspace_lt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x < b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def interior_open open_halfspace_lt)
qed

lemma%important frontier_halfspace_gt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x > b} = {x. a \<bullet> x = b}"
proof%unimportant (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def interior_open open_halfspace_gt)
qed

lemma%important interior_standard_hyperplane:
   "interior {x :: (real^'n). x$k = a} = {}"
proof%unimportant -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?thesis
    using interior_hyperplane [of "axis k (1::real)" a]
    by force
qed

lemma%unimportant matrix_mult_transpose_dot_column:
  shows "transpose A ** A = (\<chi> i j. inner (column i A) (column j A))"
  by (simp add: matrix_matrix_mult_def vec_eq_iff transpose_def column_def inner_vec_def)

lemma%unimportant matrix_mult_transpose_dot_row:
  shows "A ** transpose A = (\<chi> i j. inner (row i A) (row j A))"
  by (simp add: matrix_matrix_mult_def vec_eq_iff transpose_def row_def inner_vec_def)

text\<open>Two sometimes fruitful ways of looking at matrix-vector multiplication.\<close>

lemma%important matrix_mult_dot: "A *v x = (\<chi> i. inner (A$i) x)"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma%unimportant adjoint_matrix: "adjoint(\<lambda>x. (A::real^'n^'m) *v x) = (\<lambda>x. transpose A *v x)"
  apply (rule adjoint_unique)
  apply (simp add: transpose_def inner_vec_def matrix_vector_mult_def
    sum_distrib_right sum_distrib_left)
  apply (subst sum.swap)
  apply (simp add:  ac_simps)
  done

lemma%important matrix_adjoint: assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'m)"
  shows "matrix(adjoint f) = transpose(matrix f)"
proof%unimportant -
  have "matrix(adjoint f) = matrix(adjoint ((*v) (matrix f)))"
    by (simp add: lf)
  also have "\<dots> = transpose(matrix f)"
    unfolding adjoint_matrix matrix_of_matrix_vector_mul
    apply rule
    done
  finally show ?thesis .
qed

lemma%unimportant matrix_vector_mul_bounded_linear[intro, simp]: "bounded_linear ((*v) A)" for A :: "'a::{euclidean_space,real_algebra_1}^'n^'m"
  using matrix_vector_mul_linear[of A]
  by (simp add: linear_conv_bounded_linear linear_matrix_vector_mul_eq)

lemma%unimportant (* FIX ME needs name*)
  fixes A :: "'a::{euclidean_space,real_algebra_1}^'n^'m"
  shows matrix_vector_mult_linear_continuous_at [continuous_intros]: "isCont ((*v) A) z"
    and matrix_vector_mult_linear_continuous_on [continuous_intros]: "continuous_on S ((*v) A)"
  by (simp_all add: linear_continuous_at linear_continuous_on)

lemma%unimportant scalar_invertible:
  fixes A :: "('a::real_algebra_1)^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A)"
proof -
  obtain A' where "A ** A' = mat 1" and "A' ** A = mat 1"
    using assms unfolding invertible_def by auto
  with `k \<noteq> 0`
  have "(k *\<^sub>R A) ** ((1/k) *\<^sub>R A') = mat 1" "((1/k) *\<^sub>R A') ** (k *\<^sub>R A) = mat 1"
    by (simp_all add: assms matrix_scalar_ac)
  thus "invertible (k *\<^sub>R A)"
    unfolding invertible_def by auto
qed

lemma%unimportant scalar_invertible_iff:
  fixes A :: "('a::real_algebra_1)^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A) \<longleftrightarrow> k \<noteq> 0 \<and> invertible A"
  by (simp add: assms scalar_invertible)

lemma%unimportant vector_transpose_matrix [simp]: "x v* transpose A = A *v x"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma%unimportant transpose_matrix_vector [simp]: "transpose A *v x = x v* A"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma%unimportant vector_scalar_commute:
  fixes A :: "'a::{field}^'m^'n"
  shows "A *v (c *s x) = c *s (A *v x)"
  by (simp add: vector_scalar_mult_def matrix_vector_mult_def mult_ac sum_distrib_left)

lemma%unimportant scalar_vector_matrix_assoc:
  fixes k :: "'a::{field}" and x :: "'a::{field}^'n" and A :: "'a^'m^'n"
  shows "(k *s x) v* A = k *s (x v* A)"
  by (metis transpose_matrix_vector vector_scalar_commute)
 
lemma%unimportant vector_matrix_mult_0 [simp]: "0 v* A = 0"
  unfolding vector_matrix_mult_def by (simp add: zero_vec_def)

lemma%unimportant vector_matrix_mult_0_right [simp]: "x v* 0 = 0"
  unfolding vector_matrix_mult_def by (simp add: zero_vec_def)

lemma%unimportant vector_matrix_mul_rid [simp]:
  fixes v :: "('a::semiring_1)^'n"
  shows "v v* mat 1 = v"
  by (metis matrix_vector_mul_lid transpose_mat vector_transpose_matrix)

lemma%unimportant scaleR_vector_matrix_assoc:
  fixes k :: real and x :: "real^'n" and A :: "real^'m^'n"
  shows "(k *\<^sub>R x) v* A = k *\<^sub>R (x v* A)"
  by (metis matrix_vector_mult_scaleR transpose_matrix_vector)

lemma%important vector_scaleR_matrix_ac:
  fixes k :: real and x :: "real^'n" and A :: "real^'m^'n"
  shows "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
proof%unimportant -
  have "x v* (k *\<^sub>R A) = (k *\<^sub>R x) v* A"
    unfolding vector_matrix_mult_def
    by (simp add: algebra_simps)
  with scaleR_vector_matrix_assoc
  show "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
    by auto
qed


subsection%important\<open>Some bounds on components etc. relative to operator norm\<close>

lemma%important norm_column_le_onorm:
  fixes A :: "real^'n^'m"
  shows "norm(column i A) \<le> onorm((*v) A)"
proof%unimportant -
  have "norm (\<chi> j. A $ j $ i) \<le> norm (A *v axis i 1)"
    by (simp add: matrix_mult_dot cart_eq_inner_axis)
  also have "\<dots> \<le> onorm ((*v) A)"
    using onorm [OF matrix_vector_mul_bounded_linear, of A "axis i 1"] by auto
  finally have "norm (\<chi> j. A $ j $ i) \<le> onorm ((*v) A)" .
  then show ?thesis
    unfolding column_def .
qed

lemma%important matrix_component_le_onorm:
  fixes A :: "real^'n^'m"
  shows "\<bar>A $ i $ j\<bar> \<le> onorm((*v) A)"
proof%unimportant -
  have "\<bar>A $ i $ j\<bar> \<le> norm (\<chi> n. (A $ n $ j))"
    by (metis (full_types, lifting) component_le_norm_cart vec_lambda_beta)
  also have "\<dots> \<le> onorm ((*v) A)"
    by (metis (no_types) column_def norm_column_le_onorm)
  finally show ?thesis .
qed

lemma%unimportant component_le_onorm:
  fixes f :: "real^'m \<Rightarrow> real^'n"
  shows "linear f \<Longrightarrow> \<bar>matrix f $ i $ j\<bar> \<le> onorm f"
  by (metis linear_matrix_vector_mul_eq matrix_component_le_onorm matrix_vector_mul)

lemma%important onorm_le_matrix_component_sum:
  fixes A :: "real^'n^'m"
  shows "onorm((*v) A) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)"
proof%unimportant (rule onorm_le)
  fix x
  have "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<bar>(A *v x) $ i\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)"
  proof (rule sum_mono)
    fix i
    have "\<bar>(A *v x) $ i\<bar> \<le> \<bar>\<Sum>j\<in>UNIV. A $ i $ j * x $ j\<bar>"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j * x $ j\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)"
      by (rule sum_mono) (simp add: abs_mult component_le_norm_cart mult_left_mono)
    finally show "\<bar>(A *v x) $ i\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)" .
  qed
  finally show "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>) * norm x"
    by (simp add: sum_distrib_right)
qed

lemma%important onorm_le_matrix_component:
  fixes A :: "real^'n^'m"
  assumes "\<And>i j. abs(A$i$j) \<le> B"
  shows "onorm((*v) A) \<le> real (CARD('m)) * real (CARD('n)) * B"
proof%unimportant (rule onorm_le)
  fix x :: "real^'n::_"
  have "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<bar>(A *v x) $ i\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i::'m \<in>UNIV. real (CARD('n)) * B * norm x)"
  proof (rule sum_mono)
    fix i
    have "\<bar>(A *v x) $ i\<bar> \<le> norm(A $ i) * norm x"
      by (simp add: matrix_mult_dot Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>) * norm x"
      by (simp add: mult_right_mono norm_le_l1_cart)
    also have "\<dots> \<le> real (CARD('n)) * B * norm x"
      by (simp add: assms sum_bounded_above mult_right_mono)
    finally show "\<bar>(A *v x) $ i\<bar> \<le> real (CARD('n)) * B * norm x" .
  qed
  also have "\<dots> \<le> CARD('m) * real (CARD('n)) * B * norm x"
    by simp
  finally show "norm (A *v x) \<le> CARD('m) * real (CARD('n)) * B * norm x" .
qed

subsection%important \<open>lambda skolemization on cartesian products\<close>

lemma%important lambda_skolem: "(\<forall>i. \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a ^ 'n. \<forall>i. P i (x $ i))" (is "?lhs \<longleftrightarrow> ?rhs")
proof%unimportant -
  let ?S = "(UNIV :: 'n set)"
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f where f:"\<forall>i. P i (f i)" unfolding choice_iff by metis
    let ?x = "(\<chi> i. (f i)) :: 'a ^ 'n"
    { fix i
      from f have "P i (f i)" by metis
      then have "P i (?x $ i)" by auto
    }
    hence "\<forall>i. P i (?x$i)" by metis
    hence ?rhs by metis }
  ultimately show ?thesis by metis
qed

lemma%unimportant rational_approximation:
  assumes "e > 0"
  obtains r::real where "r \<in> \<rat>" "\<bar>r - x\<bar> < e"
  using Rats_dense_in_real [of "x - e/2" "x + e/2"] assms by auto

lemma%important matrix_rational_approximation:
  fixes A :: "real^'n^'m"
  assumes "e > 0"
  obtains B where "\<And>i j. B$i$j \<in> \<rat>" "onorm(\<lambda>x. (A - B) *v x) < e"
proof%unimportant -
  have "\<forall>i j. \<exists>q \<in> \<rat>. \<bar>q - A $ i $ j\<bar> < e / (2 * CARD('m) * CARD('n))"
    using assms by (force intro: rational_approximation [of "e / (2 * CARD('m) * CARD('n))"])
  then obtain B where B: "\<And>i j. B$i$j \<in> \<rat>" and Bclo: "\<And>i j. \<bar>B$i$j - A $ i $ j\<bar> < e / (2 * CARD('m) * CARD('n))"
    by (auto simp: lambda_skolem Bex_def)
  show ?thesis
  proof
    have "onorm ((*v) (A - B)) \<le> real CARD('m) * real CARD('n) *
    (e / (2 * real CARD('m) * real CARD('n)))"
      apply (rule onorm_le_matrix_component)
      using Bclo by (simp add: abs_minus_commute less_imp_le)
    also have "\<dots> < e"
      using \<open>0 < e\<close> by (simp add: divide_simps)
    finally show "onorm ((*v) (A - B)) < e" .
  qed (use B in auto)
qed

lemma%unimportant vector_sub_project_orthogonal_cart: "(b::real^'n) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *s b) = 0"
  unfolding inner_simps scalar_mult_eq_scaleR by auto


text \<open>The same result in terms of square matrices.\<close>


text \<open>Considering an n-element vector as an n-by-1 or 1-by-n matrix.\<close>

definition%unimportant "rowvector v = (\<chi> i j. (v$j))"

definition%unimportant "columnvector v = (\<chi> i j. (v$i))"

lemma%unimportant transpose_columnvector: "transpose(columnvector v) = rowvector v"
  by (simp add: transpose_def rowvector_def columnvector_def vec_eq_iff)

lemma%unimportant transpose_rowvector: "transpose(rowvector v) = columnvector v"
  by (simp add: transpose_def columnvector_def rowvector_def vec_eq_iff)

lemma%unimportant dot_rowvector_columnvector: "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma%unimportant dot_matrix_product:
  "(x::real^'n) \<bullet> y = (((rowvector x ::real^'n^1) ** (columnvector y :: real^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def inner_vec_def)

lemma%unimportant dot_matrix_vector_mul:
  fixes A B :: "real ^'n ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transpose A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
  unfolding dot_matrix_product transpose_columnvector[symmetric]
    dot_rowvector_columnvector matrix_transpose_mul matrix_mul_assoc ..

lemma%unimportant infnorm_cart:"infnorm (x::real^'n) = Sup {\<bar>x$i\<bar> |i. i\<in>UNIV}"
  by (simp add: infnorm_def inner_axis Basis_vec_def) (metis (lifting) inner_axis real_inner_1_right)

lemma%unimportant component_le_infnorm_cart: "\<bar>x$i\<bar> \<le> infnorm (x::real^'n)"
  using Basis_le_infnorm[of "axis i 1" x]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis)

lemma%unimportant continuous_component[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x $ i)"
  unfolding continuous_def by (rule tendsto_vec_nth)

lemma%unimportant continuous_on_component[continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x $ i)"
  unfolding continuous_on_def by (fast intro: tendsto_vec_nth)

lemma%unimportant continuous_on_vec_lambda[continuous_intros]:
  "(\<And>i. continuous_on S (f i)) \<Longrightarrow> continuous_on S (\<lambda>x. \<chi> i. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_vec_lambda)

lemma%unimportant closed_positive_orthant: "closed {x::real^'n. \<forall>i. 0 \<le>x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant bounded_component_cart: "bounded s \<Longrightarrow> bounded ((\<lambda>x. x $ i) ` s)"
  unfolding bounded_def
  apply clarify
  apply (rule_tac x="x $ i" in exI)
  apply (rule_tac x="e" in exI)
  apply clarify
  apply (rule order_trans [OF dist_vec_nth_le], simp)
  done

lemma%important compact_lemma_cart:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel ^ 'n"
  assumes f: "bounded (range f)"
  shows "\<exists>l r. strict_mono r \<and>
        (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
    (is "?th d")
proof%unimportant -
  have "\<forall>d' \<subseteq> d. ?th d'"
    by (rule compact_lemma_general[where unproj=vec_lambda])
      (auto intro!: f bounded_component_cart simp: vec_lambda_eta)
  then show "?th d" by simp
qed

instance vec :: (heine_borel, finite) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a ^ 'b"
  assume f: "bounded (range f)"
  then obtain l r where r: "strict_mono r"
      and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>UNIV. dist (f (r n) $ i) (l $ i) < e) sequentially"
    using compact_lemma_cart [OF f] by blast
  let ?d = "UNIV::'b set"
  { fix e::real assume "e>0"
    hence "0 < e / (real_of_nat (card ?d))"
      using zero_less_card_finite divide_pos_pos[of e, of "real_of_nat (card ?d)"] by auto
    with l have "eventually (\<lambda>n. \<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))) sequentially"
      by simp
    moreover
    { fix n
      assume n: "\<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>?d. dist (f (r n) $ i) (l $ i))"
        unfolding dist_vec_def using zero_le_dist by (rule L2_set_le_sum)
      also have "\<dots> < (\<Sum>i\<in>?d. e / (real_of_nat (card ?d)))"
        by (rule sum_strict_mono) (simp_all add: n)
      finally have "dist (f (r n)) l < e" by simp
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_mono)
  }
  hence "((f \<circ> r) \<longlongrightarrow> l) sequentially" unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially" by auto
qed

lemma%unimportant interval_cart:
  fixes a :: "real^'n"
  shows "box a b = {x::real^'n. \<forall>i. a$i < x$i \<and> x$i < b$i}"
    and "cbox a b = {x::real^'n. \<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def mem_box Basis_vec_def inner_axis)

lemma%unimportant mem_box_cart:
  fixes a :: "real^'n"
  shows "x \<in> box a b \<longleftrightarrow> (\<forall>i. a$i < x$i \<and> x$i < b$i)"
    and "x \<in> cbox a b \<longleftrightarrow> (\<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval_cart[of a b] by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def)

lemma%unimportant interval_eq_empty_cart:
  fixes a :: "real^'n"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i. b$i \<le> a$i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i. b$i < a$i))" (is ?th2)
proof -
  { fix i x assume as:"b$i \<le> a$i" and x:"x\<in>box a b"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_box_cart by auto
    hence "a$i < b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i < b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i < ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i < b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "box a b \<noteq> {}" using mem_box_cart(1)[of "?x" a b] by auto }
  ultimately show ?th1 by blast

  { fix i x assume as:"b$i < a$i" and x:"x\<in>cbox a b"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_box_cart by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i < a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i \<le> b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i \<le> b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "cbox a b \<noteq> {}" using mem_box_cart(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma%unimportant interval_ne_empty_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i \<le> b$i)"
    and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  unfolding interval_eq_empty_cart[of a b] by (auto simp add: not_less not_le)
    (* BH: Why doesn't just "auto" work here? *)

lemma%unimportant subset_interval_imp_cart:
  fixes a :: "real^'n"
  shows "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box_cart
  by (auto intro: order_trans less_le_trans le_less_trans less_imp_le) (* BH: Why doesn't just "auto" work here? *)

lemma%unimportant interval_sing:
  fixes a :: "'a::linorder^'n"
  shows "{a .. a} = {a} \<and> {a<..<a} = {}"
  apply (auto simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
  done

lemma%unimportant subset_interval_cart:
  fixes a :: "real^'n"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i < c$i \<and> d$i < b$i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
  using subset_box[of c d a b] by (simp_all add: Basis_vec_def inner_axis)

lemma%unimportant disjoint_interval_cart:
  fixes a::"real^'n"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
  using disjoint_interval[of a b c d] by (simp_all add: Basis_vec_def inner_axis)

lemma%unimportant Int_interval_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<inter> cbox c d =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding Int_interval
  by (auto simp: mem_box less_eq_vec_def)
    (auto simp: Basis_vec_def inner_axis)

lemma%unimportant closed_interval_left_cart:
  fixes b :: "real^'n"
  shows "closed {x::real^'n. \<forall>i. x$i \<le> b$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant closed_interval_right_cart:
  fixes a::"real^'n"
  shows "closed {x::real^'n. \<forall>i. a$i \<le> x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant is_interval_cart:
  "is_interval (s::(real^'n) set) \<longleftrightarrow>
    (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i. ((a$i \<le> x$i \<and> x$i \<le> b$i) \<or> (b$i \<le> x$i \<and> x$i \<le> a$i))) \<longrightarrow> x \<in> s)"
  by (simp add: is_interval_def Ball_def Basis_vec_def inner_axis imp_ex)

lemma%unimportant closed_halfspace_component_le_cart: "closed {x::real^'n. x$i \<le> a}"
  by (simp add: closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant closed_halfspace_component_ge_cart: "closed {x::real^'n. x$i \<ge> a}"
  by (simp add: closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant open_halfspace_component_lt_cart: "open {x::real^'n. x$i < a}"
  by (simp add: open_Collect_less continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant open_halfspace_component_gt_cart: "open {x::real^'n. x$i  > a}"
  by (simp add: open_Collect_less continuous_on_const continuous_on_id continuous_on_component)

lemma%unimportant Lim_component_le_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f \<longlongrightarrow> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f x $i \<le> b) net"
  shows "l$i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_vec_nth, OF assms(1, 3)])

lemma%unimportant Lim_component_ge_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f \<longlongrightarrow> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  shows "b \<le> l$i"
  by (rule tendsto_le[OF assms(2) tendsto_vec_nth tendsto_const, OF assms(1, 3)])

lemma%unimportant Lim_component_eq_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes net: "(f \<longlongrightarrow> l) net" "~(trivial_limit net)" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff] and
    Lim_component_ge_cart[OF net, of b i] and
    Lim_component_le_cart[OF net, of i b] by auto

lemma%unimportant connected_ivt_component_cart:
  fixes x :: "real^'n"
  shows "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "axis k 1" a]
  by (auto simp add: inner_axis inner_commute)

lemma%unimportant subspace_substandard_cart: "vec.subspace {x. (\<forall>i. P i \<longrightarrow> x$i = 0)}"
  unfolding vec.subspace_def by auto

lemma%important closed_substandard_cart:
  "closed {x::'a::real_normed_vector ^ 'n. \<forall>i. P i \<longrightarrow> x$i = 0}"
proof%unimportant -
  { fix i::'n
    have "closed {x::'a ^ 'n. P i \<longrightarrow> x$i = 0}"
      by (cases "P i") (simp_all add: closed_Collect_eq continuous_on_const continuous_on_id continuous_on_component) }
  thus ?thesis
    unfolding Collect_all_eq by (simp add: closed_INT)
qed

lemma%important dim_substandard_cart: "vec.dim {x::'a::field^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0} = card d"
  (is "vec.dim ?A = _")
proof%unimportant (rule vec.dim_unique)
  let ?B = "((\<lambda>x. axis x 1) ` d)"
  have subset_basis: "?B \<subseteq> cart_basis"
    by (auto simp: cart_basis_def)
  show "?B \<subseteq> ?A"
    by (auto simp: axis_def)
  show "vec.independent ((\<lambda>x. axis x 1) ` d)"
    using subset_basis
    by (rule vec.independent_mono[OF vec.independent_Basis])
  have "x \<in> vec.span ?B" if "\<forall>i. i \<notin> d \<longrightarrow> x $ i = 0" for x::"'a^'n"
  proof -
    have "finite ?B"
      using subset_basis finite_cart_basis
      by (rule finite_subset)
    have "x = (\<Sum>i\<in>UNIV. x $ i *s axis i 1)"
      by (rule basis_expansion[symmetric])
    also have "\<dots> = (\<Sum>i\<in>d. (x $ i) *s axis i 1)"
      by (rule sum.mono_neutral_cong_right) (auto simp: that)
    also have "\<dots> \<in> vec.span ?B"
      by (simp add: vec.span_sum vec.span_clauses)
    finally show "x \<in> vec.span ?B" .
  qed
  then show "?A \<subseteq> vec.span ?B" by auto
qed (simp add: card_image inj_on_def axis_eq_axis)

lemma%unimportant dim_subset_UNIV_cart_gen:
  fixes S :: "('a::field^'n) set"
  shows "vec.dim S \<le> CARD('n)"
  by (metis vec.dim_eq_full vec.dim_subset_UNIV vec.span_UNIV vec_dim_card)

lemma%unimportant dim_subset_UNIV_cart:
  fixes S :: "(real^'n) set"
  shows "dim S \<le> CARD('n)"
  using dim_subset_UNIV_cart_gen[of S] by (simp add: dim_vec_eq)

lemma%unimportant affinity_inverses:
  assumes m0: "m \<noteq> (0::'a::field)"
  shows "(\<lambda>x. m *s x + c) \<circ> (\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) = id"
  "(\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) \<circ> (\<lambda>x. m *s x + c) = id"
  using m0
  by (auto simp add: fun_eq_iff vector_add_ldistrib diff_conv_add_uminus simp del: add_uminus_conv_diff)

lemma%important vector_affinity_eq:
  assumes m0: "(m::'a::field) \<noteq> 0"
  shows "m *s x + c = y \<longleftrightarrow> x = inverse m *s y + -(inverse m *s c)"
proof%unimportant
  assume h: "m *s x + c = y"
  hence "m *s x = y - c" by (simp add: field_simps)
  hence "inverse m *s (m *s x) = inverse m *s (y - c)" by simp
  then show "x = inverse m *s y + - (inverse m *s c)"
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
next
  assume h: "x = inverse m *s y + - (inverse m *s c)"
  show "m *s x + c = y" unfolding h
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
qed

lemma%unimportant vector_eq_affinity:
    "(m::'a::field) \<noteq> 0 ==> (y = m *s x + c \<longleftrightarrow> inverse(m) *s y + -(inverse(m) *s c) = x)"
  using vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma%unimportant vector_cart:
  fixes f :: "real^'n \<Rightarrow> real"
  shows "(\<chi> i. f (axis i 1)) = (\<Sum>i\<in>Basis. f i *\<^sub>R i)"
  unfolding euclidean_eq_iff[where 'a="real^'n"]
  by simp (simp add: Basis_vec_def inner_axis)

lemma%unimportant const_vector_cart:"((\<chi> i. d)::real^'n) = (\<Sum>i\<in>Basis. d *\<^sub>R i)"
  by (rule vector_cart)

subsection%important "Convex Euclidean Space"

lemma%unimportant Cart_1:"(1::real^'n) = \<Sum>Basis"
  using const_vector_cart[of 1] by (simp add: one_vec_def)

declare vector_add_ldistrib[simp] vector_ssub_ldistrib[simp] vector_smult_assoc[simp] vector_smult_rneg[simp]
declare vector_sadd_rdistrib[simp] vector_sub_rdistrib[simp]

lemmas%unimportant vector_component_simps = vector_minus_component vector_smult_component vector_add_component less_eq_vec_def vec_lambda_beta vector_uminus_component

lemma%unimportant convex_box_cart:
  assumes "\<And>i. convex {x. P i x}"
  shows "convex {x. \<forall>i. P i (x$i)}"
  using assms unfolding convex_def by auto

lemma%unimportant convex_positive_orthant_cart: "convex {x::real^'n. (\<forall>i. 0 \<le> x$i)}"
  by (rule convex_box_cart) (simp add: atLeast_def[symmetric])

lemma%unimportant unit_interval_convex_hull_cart:
  "cbox (0::real^'n) 1 = convex hull {x. \<forall>i. (x$i = 0) \<or> (x$i = 1)}"
  unfolding Cart_1 unit_interval_convex_hull[where 'a="real^'n"] box_real[symmetric]
  by (rule arg_cong[where f="\<lambda>x. convex hull x"]) (simp add: Basis_vec_def inner_axis)

lemma%important cube_convex_hull_cart:
  assumes "0 < d"
  obtains s::"(real^'n) set"
    where "finite s" "cbox (x - (\<chi> i. d)) (x + (\<chi> i. d)) = convex hull s"
proof%unimportant -
  from assms obtain s where "finite s"
    and "cbox (x - sum ((*\<^sub>R) d) Basis) (x + sum ((*\<^sub>R) d) Basis) = convex hull s"
    by (rule cube_convex_hull)
  with that[of s] show thesis
    by (simp add: const_vector_cart)
qed


subsection%important "Derivative"

definition%important "jacobian f net = matrix(frechet_derivative f net)"

lemma%important jacobian_works:
  "(f::(real^'a) \<Rightarrow> (real^'b)) differentiable net \<longleftrightarrow>
    (f has_derivative (\<lambda>h. (jacobian f net) *v h)) net" (is "?lhs = ?rhs")
proof%unimportant
  assume ?lhs then show ?rhs
    by (simp add: frechet_derivative_works has_derivative_linear jacobian_def)
next
  assume ?rhs then show ?lhs
    by (rule differentiableI)
qed


subsection%important \<open>Component of the differential must be zero if it exists at a local
  maximum or minimum for that corresponding component\<close>

lemma%important differential_zero_maxmin_cart:
  fixes f::"real^'a \<Rightarrow> real^'b"
  assumes "0 < e" "((\<forall>y \<in> ball x e. (f y)$k \<le> (f x)$k) \<or> (\<forall>y\<in>ball x e. (f x)$k \<le> (f y)$k))"
    "f differentiable (at x)"
  shows "jacobian f (at x) $ k = 0"
  using differential_zero_maxmin_component[of "axis k 1" e x f] assms
    vector_cart[of "\<lambda>j. frechet_derivative f (at x) j $ k"]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis jacobian_def matrix_def)

subsection%unimportant \<open>Lemmas for working on @{typ "real^1"}\<close>

lemma forall_1[simp]: "(\<forall>i::1. P i) \<longleftrightarrow> P 1"
  by (metis (full_types) num1_eq_iff)

lemma ex_1[simp]: "(\<exists>x::1. P x) \<longleftrightarrow> P 1"
  by auto (metis (full_types) num1_eq_iff)

lemma exhaust_2:
  fixes x :: 2
  shows "x = 1 \<or> x = 2"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 2" by simp_all
  then have "z = 0 | z = 1" by arith
  then show ?case by auto
qed

lemma forall_2: "(\<forall>i::2. P i) \<longleftrightarrow> P 1 \<and> P 2"
  by (metis exhaust_2)

lemma exhaust_3:
  fixes x :: 3
  shows "x = 1 \<or> x = 2 \<or> x = 3"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 3" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2" by arith
  then show ?case by auto
qed

lemma forall_3: "(\<forall>i::3. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
  by (metis exhaust_3)

lemma UNIV_1 [simp]: "UNIV = {1::1}"
  by (auto simp add: num1_eq_iff)

lemma UNIV_2: "UNIV = {1::2, 2::2}"
  using exhaust_2 by auto

lemma UNIV_3: "UNIV = {1::3, 2::3, 3::3}"
  using exhaust_3 by auto

lemma sum_1: "sum f (UNIV::1 set) = f 1"
  unfolding UNIV_1 by simp

lemma sum_2: "sum f (UNIV::2 set) = f 1 + f 2"
  unfolding UNIV_2 by simp

lemma sum_3: "sum f (UNIV::3 set) = f 1 + f 2 + f 3"
  unfolding UNIV_3 by (simp add: ac_simps)

lemma num1_eqI:
  fixes a::num1 shows "a = b"
  by (metis (full_types) UNIV_1 UNIV_I empty_iff insert_iff)

lemma num1_eq1 [simp]:
  fixes a::num1 shows "a = 1"
  by (rule num1_eqI)

instantiation num1 :: cart_one
begin

instance
proof
  show "CARD(1) = Suc 0" by auto
qed

end

instantiation num1 :: linorder begin
definition "a < b \<longleftrightarrow> Rep_num1 a < Rep_num1 b"
definition "a \<le> b \<longleftrightarrow> Rep_num1 a \<le> Rep_num1 b"
instance
  by intro_classes (auto simp: less_eq_num1_def less_num1_def intro: num1_eqI)
end

instance num1 :: wellorder
  by intro_classes (auto simp: less_eq_num1_def less_num1_def)

subsection%unimportant\<open>The collapse of the general concepts to dimension one\<close>

lemma vector_one: "(x::'a ^1) = (\<chi> i. (x$1))"
  by (simp add: vec_eq_iff)

lemma forall_one: "(\<forall>(x::'a ^1). P x) \<longleftrightarrow> (\<forall>x. P(\<chi> i. x))"
  apply auto
  apply (erule_tac x= "x$1" in allE)
  apply (simp only: vector_one[symmetric])
  done

lemma norm_vector_1: "norm (x :: _^1) = norm (x$1)"
  by (simp add: norm_vec_def)

lemma dist_vector_1:
  fixes x :: "'a::real_normed_vector^1"
  shows "dist x y = dist (x$1) (y$1)"
  by (simp add: dist_norm norm_vector_1)

lemma norm_real: "norm(x::real ^ 1) = \<bar>x$1\<bar>"
  by (simp add: norm_vector_1)

lemma dist_real: "dist(x::real ^ 1) y = \<bar>(x$1) - (y$1)\<bar>"
  by (auto simp add: norm_real dist_norm)

subsection%important\<open> Rank of a matrix\<close>

text\<open>Equivalence of row and column rank is taken from George Mackiw's paper, Mathematics Magazine 1995, p. 285.\<close>

lemma%unimportant matrix_vector_mult_in_columnspace_gen:
  fixes A :: "'a::field^'n^'m"
  shows "(A *v x) \<in> vec.span(columns A)"
  apply (simp add: matrix_vector_column columns_def transpose_def column_def)
  apply (intro vec.span_sum vec.span_scale)
  apply (force intro: vec.span_base)
  done

lemma%unimportant matrix_vector_mult_in_columnspace:
  fixes A :: "real^'n^'m"
  shows "(A *v x) \<in> span(columns A)"
  using matrix_vector_mult_in_columnspace_gen[of A x] by (simp add: span_vec_eq)

lemma%important orthogonal_nullspace_rowspace:
  fixes A :: "real^'n^'m"
  assumes 0: "A *v x = 0" and y: "y \<in> span(rows A)"
  shows "orthogonal x y"
  using y
proof%unimportant (induction rule: span_induct)
  case base
  then show ?case
    by (simp add: subspace_orthogonal_to_vector)
next
  case (step v)
  then obtain i where "v = row i A"
    by (auto simp: rows_def)
  with 0 show ?case
    unfolding orthogonal_def inner_vec_def matrix_vector_mult_def row_def
    by (simp add: mult.commute) (metis (no_types) vec_lambda_beta zero_index)
qed

lemma%unimportant nullspace_inter_rowspace:
  fixes A :: "real^'n^'m"
  shows "A *v x = 0 \<and> x \<in> span(rows A) \<longleftrightarrow> x = 0"
  using orthogonal_nullspace_rowspace orthogonal_self span_zero matrix_vector_mult_0_right
  by blast

lemma%unimportant matrix_vector_mul_injective_on_rowspace:
  fixes A :: "real^'n^'m"
  shows "\<lbrakk>A *v x = A *v y; x \<in> span(rows A); y \<in> span(rows A)\<rbrakk> \<Longrightarrow> x = y"
  using nullspace_inter_rowspace [of A "x-y"]
  by (metis diff_eq_diff_eq diff_self matrix_vector_mult_diff_distrib span_diff)

definition%important rank :: "'a::field^'n^'m=>nat"
  where row_rank_def_gen: "rank A \<equiv> vec.dim(rows A)"

lemma%important row_rank_def: "rank A = dim (rows A)" for A::"real^'n^'m"
  by%unimportant (auto simp: row_rank_def_gen dim_vec_eq)

lemma%important dim_rows_le_dim_columns:
  fixes A :: "real^'n^'m"
  shows "dim(rows A) \<le> dim(columns A)"
proof%unimportant -
  have "dim (span (rows A)) \<le> dim (span (columns A))"
  proof -
    obtain B where "independent B" "span(rows A) \<subseteq> span B"
              and B: "B \<subseteq> span(rows A)""card B = dim (span(rows A))"
      using basis_exists [of "span(rows A)"] by metis
    with span_subspace have eq: "span B = span(rows A)"
      by auto
    then have inj: "inj_on ((*v) A) (span B)"
      by (simp add: inj_on_def matrix_vector_mul_injective_on_rowspace)
    then have ind: "independent ((*v) A ` B)"
      by (rule linear_independent_injective_image [OF Finite_Cartesian_Product.matrix_vector_mul_linear \<open>independent B\<close>])
    have "dim (span (rows A)) \<le> card ((*v) A ` B)"
      unfolding B(2)[symmetric]
      using inj
      by (auto simp: card_image inj_on_subset span_superset)
    also have "\<dots> \<le> dim (span (columns A))"
      using _ ind
      by (rule independent_card_le_dim) (auto intro!: matrix_vector_mult_in_columnspace)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: dim_span)
qed

lemma%unimportant column_rank_def:
  fixes A :: "real^'n^'m"
  shows "rank A = dim(columns A)"
  unfolding row_rank_def
  by (metis columns_transpose dim_rows_le_dim_columns le_antisym rows_transpose)

lemma%unimportant rank_transpose:
  fixes A :: "real^'n^'m"
  shows "rank(transpose A) = rank A"
  by (metis column_rank_def row_rank_def rows_transpose)

lemma%unimportant matrix_vector_mult_basis:
  fixes A :: "real^'n^'m"
  shows "A *v (axis k 1) = column k A"
  by (simp add: cart_eq_inner_axis column_def matrix_mult_dot)

lemma%unimportant columns_image_basis:
  fixes A :: "real^'n^'m"
  shows "columns A = (*v) A ` (range (\<lambda>i. axis i 1))"
  by (force simp: columns_def matrix_vector_mult_basis [symmetric])

lemma%important rank_dim_range:
  fixes A :: "real^'n^'m"
  shows "rank A = dim(range (\<lambda>x. A *v x))"
  unfolding column_rank_def
proof%unimportant (rule span_eq_dim)
  have "span (columns A) \<subseteq> span (range ((*v) A))" (is "?l \<subseteq> ?r")
    by (simp add: columns_image_basis image_subsetI span_mono)
  then show "?l = ?r"
    by (metis (no_types, lifting) image_subset_iff matrix_vector_mult_in_columnspace
        span_eq span_span)
qed

lemma%unimportant rank_bound:
  fixes A :: "real^'n^'m"
  shows "rank A \<le> min CARD('m) (CARD('n))"
  by (metis (mono_tags, lifting) dim_subset_UNIV_cart min.bounded_iff
      column_rank_def row_rank_def)

lemma%unimportant full_rank_injective:
  fixes A :: "real^'n^'m"
  shows "rank A = CARD('n) \<longleftrightarrow> inj ((*v) A)"
  by (simp add: matrix_left_invertible_injective [symmetric] matrix_left_invertible_span_rows row_rank_def
      dim_eq_full [symmetric] card_cart_basis vec.dimension_def)

lemma%unimportant full_rank_surjective:
  fixes A :: "real^'n^'m"
  shows "rank A = CARD('m) \<longleftrightarrow> surj ((*v) A)"
  by (simp add: matrix_right_invertible_surjective [symmetric] left_invertible_transpose [symmetric]
                matrix_left_invertible_injective full_rank_injective [symmetric] rank_transpose)

lemma%unimportant rank_I: "rank(mat 1::real^'n^'n) = CARD('n)"
  by (simp add: full_rank_injective inj_on_def)

lemma%unimportant less_rank_noninjective:
  fixes A :: "real^'n^'m"
  shows "rank A < CARD('n) \<longleftrightarrow> \<not> inj ((*v) A)"
using less_le rank_bound by (auto simp: full_rank_injective [symmetric])

lemma%unimportant matrix_nonfull_linear_equations_eq:
  fixes A :: "real^'n^'m"
  shows "(\<exists>x. (x \<noteq> 0) \<and> A *v x = 0) \<longleftrightarrow> ~(rank A = CARD('n))"
  by (meson matrix_left_invertible_injective full_rank_injective matrix_left_invertible_ker)

lemma%unimportant rank_eq_0: "rank A = 0 \<longleftrightarrow> A = 0" and rank_0 [simp]: "rank (0::real^'n^'m) = 0"
  for A :: "real^'n^'m"
  by (auto simp: rank_dim_range matrix_eq)

lemma%important rank_mul_le_right:
  fixes A :: "real^'n^'m" and B :: "real^'p^'n"
  shows "rank(A ** B) \<le> rank B"
proof%unimportant -
  have "rank(A ** B) \<le> dim ((*v) A ` range ((*v) B))"
    by (auto simp: rank_dim_range image_comp o_def matrix_vector_mul_assoc)
  also have "\<dots> \<le> rank B"
    by (simp add: rank_dim_range dim_image_le)
  finally show ?thesis .
qed

lemma%unimportant rank_mul_le_left:
  fixes A :: "real^'n^'m" and B :: "real^'p^'n"
  shows "rank(A ** B) \<le> rank A"
  by (metis matrix_transpose_mul rank_mul_le_right rank_transpose)

subsection%unimportant\<open>Routine results connecting the types @{typ "real^1"} and @{typ real}\<close>

lemma vector_one_nth [simp]:
  fixes x :: "'a^1" shows "vec (x $ 1) = x"
  by (metis vec_def vector_one)

lemma vec_cbox_1_eq [simp]:
  shows "vec ` cbox u v = cbox (vec u) (vec v ::real^1)"
  by (force simp: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box)

lemma vec_nth_cbox_1_eq [simp]:
  fixes u v :: "'a::euclidean_space^1"
  shows "(\<lambda>x. x $ 1) ` cbox u v = cbox (u$1) (v$1)"
    by (auto simp: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box image_iff Bex_def inner_axis) (metis vec_component)

lemma vec_nth_1_iff_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "(\<lambda>x::'a^1. x $ 1) ` S = cbox a b \<longleftrightarrow> S = cbox (vec a) (vec b)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs show ?rhs
  proof (intro equalityI subsetI)
    fix x 
    assume "x \<in> S"
    then have "x $ 1 \<in> (\<lambda>v. v $ (1::1)) ` cbox (vec a) (vec b)"
      using L by auto
    then show "x \<in> cbox (vec a) (vec b)"
      by (metis (no_types, lifting) imageE vector_one_nth)
  next
    fix x :: "'a^1"
    assume "x \<in> cbox (vec a) (vec b)"
    then show "x \<in> S"
      by (metis (no_types, lifting) L imageE imageI vec_component vec_nth_cbox_1_eq vector_one_nth)
  qed
qed simp

lemma tendsto_at_within_vector_1:
  fixes S :: "'a :: metric_space set"
  assumes "(f \<longlongrightarrow> fx) (at x within S)"
  shows "((\<lambda>y::'a^1. \<chi> i. f (y $ 1)) \<longlongrightarrow> (vec fx::'a^1)) (at (vec x) within vec ` S)"
proof (rule topological_tendstoI)
  fix T :: "('a^1) set"
  assume "open T" "vec fx \<in> T"
  have "\<forall>\<^sub>F x in at x within S. f x \<in> (\<lambda>x. x $ 1) ` T"
    using \<open>open T\<close> \<open>vec fx \<in> T\<close> assms open_image_vec_nth tendsto_def by fastforce
  then show "\<forall>\<^sub>F x::'a^1 in at (vec x) within vec ` S. (\<chi> i. f (x $ 1)) \<in> T"
    unfolding eventually_at dist_norm [symmetric]
    by (rule ex_forward)
       (use \<open>open T\<close> in 
         \<open>fastforce simp: dist_norm dist_vec_def L2_set_def image_iff vector_one open_vec_def\<close>)
qed

lemma has_derivative_vector_1:
  assumes der_g: "(g has_derivative (\<lambda>x. x * g' a)) (at a within S)"
  shows "((\<lambda>x. vec (g (x $ 1))) has_derivative (*\<^sub>R) (g' a))
         (at ((vec a)::real^1) within vec ` S)"
    using der_g
    apply (auto simp: Deriv.has_derivative_within bounded_linear_scaleR_right norm_vector_1)
    apply (drule tendsto_at_within_vector_1, vector)
    apply (auto simp: algebra_simps eventually_at tendsto_def)
    done


subsection%unimportant\<open>Explicit vector construction from lists\<close>

definition "vector l = (\<chi> i. foldr (\<lambda>x f n. fun_upd (f (n+1)) n x) l (\<lambda>n x. 0) 1 i)"

lemma vector_1 [simp]: "(vector[x]) $1 = x"
  unfolding vector_def by simp

lemma vector_2 [simp]: "(vector[x,y]) $1 = x" "(vector[x,y] :: 'a^2)$2 = (y::'a::zero)"
  unfolding vector_def by simp_all

lemma vector_3 [simp]:
 "(vector [x,y,z] ::('a::zero)^3)$1 = x"
 "(vector [x,y,z] ::('a::zero)^3)$2 = y"
 "(vector [x,y,z] ::('a::zero)^3)$3 = z"
  unfolding vector_def by simp_all

lemma forall_vector_1: "(\<forall>v::'a::zero^1. P v) \<longleftrightarrow> (\<forall>x. P(vector[x]))"
  by (metis vector_1 vector_one)

lemma forall_vector_2: "(\<forall>v::'a::zero^2. P v) \<longleftrightarrow> (\<forall>x y. P(vector[x, y]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (subgoal_tac "vector [v$1, v$2] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_2)
  done

lemma forall_vector_3: "(\<forall>v::'a::zero^3. P v) \<longleftrightarrow> (\<forall>x y z. P(vector[x, y, z]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (erule_tac x="v$3" in allE)
  apply (subgoal_tac "vector [v$1, v$2, v$3] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_3)
  done

lemma bounded_linear_component_cart[intro]: "bounded_linear (\<lambda>x::real^'n. x $ k)"
  apply (rule bounded_linear_intro[where K=1])
  using component_le_norm_cart[of _ k] unfolding real_norm_def by auto

lemma interval_split_cart:
  "{a..b::real^'n} \<inter> {x. x$k \<le> c} = {a .. (\<chi> i. if i = k then min (b$k) c else b$i)}"
  "cbox a b \<inter> {x. x$k \<ge> c} = {(\<chi> i. if i = k then max (a$k) c else a$i) .. b}"
  apply (rule_tac[!] set_eqI)
  unfolding Int_iff mem_box_cart mem_Collect_eq interval_cbox_cart
  unfolding vec_lambda_beta
  by auto

lemmas cartesian_euclidean_space_uniform_limit_intros[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF blinfun.bounded_linear_right]
  bounded_linear.uniform_limit[OF bounded_linear_vec_nth]
  bounded_linear.uniform_limit[OF bounded_linear_component_cart]

end
