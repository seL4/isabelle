(*  Title:      HOL/Matrix/Matrix.thy
    ID:         $Id$
    Author:     Steven Obua
    License:    2004 Technische Universität München
*)

theory Matrix = MatrixGeneral:

axclass almost_matrix_element < zero, plus, times
matrix_add_assoc: "(a+b)+c = a + (b+c)"
matrix_add_commute: "a+b = b+a"

matrix_mult_assoc: "(a*b)*c = a*(b*c)"
matrix_mult_left_0[simp]: "0 * a = 0"
matrix_mult_right_0[simp]: "a * 0 = 0"

matrix_left_distrib: "(a+b)*c = a*c+b*c"
matrix_right_distrib: "a*(b+c) = a*b+a*c"

axclass matrix_element < almost_matrix_element
matrix_add_0[simp]: "0+0 = 0"

instance matrix :: (plus) plus ..
instance matrix :: (times) times ..

defs (overloaded)
plus_matrix_def: "A + B == combine_matrix (op +) A B"
times_matrix_def: "A * B == mult_matrix (op *) (op +) A B"

instance matrix :: (matrix_element) matrix_element
proof -
  note combine_matrix_assoc2 = combine_matrix_assoc[simplified associative_def, THEN spec, THEN spec, THEN spec]
  {
    fix A::"('a::matrix_element) matrix"
    fix B
    fix C
    have "(A + B) + C = A + (B + C)"
      apply (simp add: plus_matrix_def)
      apply (rule combine_matrix_assoc2)
      by (simp_all add: matrix_add_assoc)
  }
  note plus_assoc = this
  {
    fix A::"('a::matrix_element) matrix"
    fix B
    fix C
    have "(A * B) * C = A * (B * C)"
      apply (simp add: times_matrix_def)
      apply (rule mult_matrix_assoc_simple)
      apply (simp_all add: associative_def commutative_def distributive_def l_distributive_def r_distributive_def)
      apply (auto)
      apply (simp_all add: matrix_add_assoc)
      apply (simp_all add: matrix_add_commute)
      apply (simp_all add: matrix_mult_assoc)
      by (simp_all add: matrix_left_distrib matrix_right_distrib)
  }
  note mult_assoc = this
  note combine_matrix_commute2 = combine_matrix_commute[simplified commutative_def, THEN spec, THEN spec]
  {
    fix A::"('a::matrix_element) matrix"
    fix B
    have "A + B = B + A"
      apply (simp add: plus_matrix_def)
      apply (insert combine_matrix_commute2[of "op +"])
      apply (rule combine_matrix_commute2)
      by (simp add: matrix_add_commute)
  }
  note plus_commute = this
  have plus_zero: "(0::('a::matrix_element) matrix) + 0 = 0"
    apply (simp add: plus_matrix_def)
    apply (rule combine_matrix_zero)
    by (simp)
  have mult_left_zero: "!! A. (0::('a::matrix_element) matrix) * A = 0" by(simp add: times_matrix_def)
  have mult_right_zero: "!! A. A * (0::('a::matrix_element) matrix) = 0" by (simp add: times_matrix_def)
  note l_distributive_matrix2 = l_distributive_matrix[simplified l_distributive_def matrix_left_distrib, THEN spec, THEN spec, THEN spec]
  {
    fix A::"('a::matrix_element) matrix"
    fix B
    fix C
    have "(A + B) * C = A * C + B * C"
      apply (simp add: plus_matrix_def)
      apply (simp add: times_matrix_def)
      apply (rule l_distributive_matrix2)
      apply (simp_all add: associative_def commutative_def l_distributive_def)
      apply (auto)
      apply (simp_all add: matrix_add_assoc)
      apply (simp_all add: matrix_add_commute)
      by (simp_all add: matrix_left_distrib)
  }
  note left_distrib = this
  note r_distributive_matrix2 = r_distributive_matrix[simplified r_distributive_def matrix_right_distrib, THEN spec, THEN spec, THEN spec]
  {
    fix A::"('a::matrix_element) matrix"
    fix B
    fix C
    have "C * (A + B) = C * A + C * B"
      apply (simp add: plus_matrix_def)
      apply (simp add: times_matrix_def)
      apply (rule r_distributive_matrix2)
      apply (simp_all add: associative_def commutative_def r_distributive_def)
      apply (auto)
      apply (simp_all add: matrix_add_assoc)
      apply (simp_all add: matrix_add_commute)
      by (simp_all add: matrix_right_distrib)
  }
  note right_distrib = this
  show "OFCLASS('a matrix, matrix_element_class)"
    apply (intro_classes)
    apply (simp_all add: plus_assoc)
    apply (simp_all add: plus_commute)
    apply (simp_all add: plus_zero)
    apply (simp_all add: mult_assoc)
    apply (simp_all add: mult_left_zero mult_right_zero)
    by (simp_all add: left_distrib right_distrib)
qed

axclass g_almost_semiring < almost_matrix_element
g_add_left_0[simp]: "0 + a = a"

lemma g_add_right_0[simp]: "(a::'a::g_almost_semiring) + 0 = a"
by (simp add: matrix_add_commute)

axclass g_semiring < g_almost_semiring
g_add_leftimp_eq: "a+b = a+c \<Longrightarrow> b = c"

instance g_almost_semiring < matrix_element
  by intro_classes simp

instance matrix :: (g_almost_semiring) g_almost_semiring
apply (intro_classes)
by (simp add: plus_matrix_def combine_matrix_def combine_infmatrix_def)

lemma RepAbs_matrix_eq_left: " Rep_matrix(Abs_matrix f) = g \<Longrightarrow> \<exists>m. \<forall>j i. m \<le> j \<longrightarrow> f j i = 0 \<Longrightarrow> \<exists>n. \<forall>j i. n \<le> i \<longrightarrow> f j i = 0 \<Longrightarrow> f = g"
by (simp add: RepAbs_matrix)

lemma RepAbs_matrix_eq_right: "g = Rep_matrix(Abs_matrix f) \<Longrightarrow> \<exists>m. \<forall>j i. m \<le> j \<longrightarrow> f j i = 0 \<Longrightarrow> \<exists>n. \<forall>j i. n \<le> i \<longrightarrow> f j i = 0 \<Longrightarrow> g = f"
by (simp add: RepAbs_matrix)

instance matrix :: (g_semiring) g_semiring
apply (intro_classes)
apply (simp add: plus_matrix_def combine_matrix_def combine_infmatrix_def)
apply (subst Rep_matrix_inject[THEN sym])
apply (drule ssubst[OF Rep_matrix_inject, of "% x. x"])
apply (drule RepAbs_matrix_eq_left)
apply (auto)
apply (rule_tac x="max (nrows a) (nrows b)" in exI, simp add: nrows_le)
apply (rule_tac x="max (ncols a) (ncols b)" in exI, simp add: ncols_le)
apply (drule RepAbs_matrix_eq_right)
apply (rule_tac x="max (nrows a) (nrows c)" in exI, simp add: nrows_le)
apply (rule_tac x="max (ncols a) (ncols c)" in exI, simp add: ncols_le)
apply (rule ext)+
apply (drule_tac x="x" and y="x" in comb, simp)
apply (drule_tac x="xa" and y="xa" in comb, simp)
apply (drule g_add_leftimp_eq)
by simp

axclass pordered_matrix_element < matrix_element, order, zero
pordered_add_right_mono: "a <= b \<Longrightarrow> a + c <= b + c"
pordered_mult_left: "0 <= c \<Longrightarrow> a <= b \<Longrightarrow> c*a <= c*b"
pordered_mult_right: "0 <= c \<Longrightarrow> a <= b \<Longrightarrow> a*c <= b*c"

lemma pordered_add_left_mono: "(a::'a::pordered_matrix_element) <= b \<Longrightarrow> c + a <= c + b"
apply (insert pordered_add_right_mono[of a b c])
by (simp add: matrix_add_commute)

lemma pordered_add: "(a::'a::pordered_matrix_element) <= b \<Longrightarrow> (c::'a::pordered_matrix_element) <= d \<Longrightarrow> a+c <= b+d"
proof -
  assume p1:"a <= b"
  assume p2:"c <= d"
  have "a+c <= b+c" by (rule pordered_add_right_mono)
  also have "\<dots> <= b+d" by (rule pordered_add_left_mono)
  ultimately show "a+c <= b+d" by simp
qed

instance matrix :: (pordered_matrix_element) pordered_matrix_element
apply (intro_classes)
apply (simp_all add: plus_matrix_def times_matrix_def)
apply (rule le_combine_matrix)
apply (simp_all)
apply (simp_all add: pordered_add)
apply (rule le_left_mult)
apply (simp_all add: matrix_add_0 g_add_left_0 pordered_add pordered_mult_left matrix_mult_left_0 matrix_mult_right_0)
apply (rule le_right_mult)
by (simp_all add: pordered_add pordered_mult_right)

axclass pordered_g_semiring < g_semiring, pordered_matrix_element

instance matrix :: (pordered_g_semiring) pordered_g_semiring ..

lemma nrows_mult: "nrows ((A::('a::matrix_element) matrix) * B) <= nrows A"
by (simp add: times_matrix_def mult_nrows)

lemma ncols_mult: "ncols ((A::('a::matrix_element) matrix) * B) <= ncols B"
by (simp add: times_matrix_def mult_ncols)

(*
constdefs
  one_matrix :: "nat \<Rightarrow> ('a::comm_semiring_1_cancel) matrix"
  "one_matrix n == Abs_matrix (% j i. if j = i & j < n then 1 else 0)"

lemma Rep_one_matrix[simp]: "Rep_matrix (one_matrix n) j i = (if (j = i & j < n) then 1 else 0)"
apply (simp add: one_matrix_def)
apply (subst RepAbs_matrix)
apply (rule exI[of _ n], simp add: split_if)+
by (simp add: split_if, arith)

lemma nrows_one_matrix[simp]: "nrows (one_matrix n) = n" (is "?r = _")
proof -
  have "?r <= n" by (simp add: nrows_le)
  moreover have "n <= ?r" by (simp add: le_nrows, arith)
  ultimately show "?r = n" by simp
qed

lemma ncols_one_matrix[simp]: "ncols (one_matrix n) = n" (is "?r = _")
proof -
  have "?r <= n" by (simp add: ncols_le)
  moreover have "n <= ?r" by (simp add: le_ncols, arith)
  ultimately show "?r = n" by simp
qed

lemma one_matrix_mult_right: "ncols A <= n \<Longrightarrow> A * (one_matrix n) = A"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply (simp add: times_matrix_def Rep_mult_matrix)
apply (rule_tac j1="xa" in ssubst[OF foldseq_almostzero])
apply (simp_all)
by (simp add: max_def ncols)

lemma one_matrix_mult_left: "nrows A <= n \<Longrightarrow> (one_matrix n) * A = A"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply (simp add: times_matrix_def Rep_mult_matrix)
apply (rule_tac j1="x" in ssubst[OF foldseq_almostzero])
apply (simp_all)
by (simp add: max_def nrows)

constdefs
  right_inverse_matrix :: "('a::comm_semiring_1_cancel) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool"
  "right_inverse_matrix A X == (A * X = one_matrix (max (nrows A) (ncols X)))"
  inverse_matrix :: "('a::comm_semiring_1_cancel) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool"
  "inverse_matrix A X == (right_inverse_matrix A X) \<and> (right_inverse_matrix X A)"

lemma right_inverse_matrix_dim: "right_inverse_matrix A X \<Longrightarrow> nrows A = ncols X"
apply (insert ncols_mult[of A X], insert nrows_mult[of A X])
by (simp add: right_inverse_matrix_def)

text {* to be continued \dots *}
*)
end
