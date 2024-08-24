(*  Title:      HOL/Matrix_LP/Matrix.thy
    Author:     Steven Obua; updated to Isar by LCP
*)

theory Matrix
imports Main "HOL-Library.Lattice_Algebras"
begin

type_synonym 'a infmatrix = "nat \<Rightarrow> nat \<Rightarrow> 'a"

definition nonzero_positions :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::zero) \<Rightarrow> (nat \<times> nat) set" where
  "nonzero_positions A = {pos. A (fst pos) (snd pos) ~= 0}"

definition "matrix = {(f::(nat \<Rightarrow> nat \<Rightarrow> 'a::zero)). finite (nonzero_positions f)}"

typedef (overloaded) 'a matrix = "matrix :: (nat \<Rightarrow> nat \<Rightarrow> 'a::zero) set"
  unfolding matrix_def
proof
  show "(\<lambda>j i. 0) \<in> {(f::(nat \<Rightarrow> nat \<Rightarrow> 'a::zero)). finite (nonzero_positions f)}"
    by (simp add: nonzero_positions_def)
qed

declare Rep_matrix_inverse[simp]

lemma matrix_eqI:
  fixes A B :: "'a::zero matrix"
  assumes "\<And>m n. Rep_matrix A m n = Rep_matrix B m n"
  shows "A=B"
  using Rep_matrix_inject assms by blast

lemma finite_nonzero_positions : "finite (nonzero_positions (Rep_matrix A))"
  by (induct A) (simp add: Abs_matrix_inverse matrix_def)

definition nrows :: "('a::zero) matrix \<Rightarrow> nat" where
  "nrows A == if nonzero_positions(Rep_matrix A) = {} then 0 else Suc(Max ((image fst) (nonzero_positions (Rep_matrix A))))"

definition ncols :: "('a::zero) matrix \<Rightarrow> nat" where
  "ncols A == if nonzero_positions(Rep_matrix A) = {} then 0 else Suc(Max ((image snd) (nonzero_positions (Rep_matrix A))))"

lemma nrows:
  assumes hyp: "nrows A \<le> m"
  shows "(Rep_matrix A m n) = 0"
proof cases
  assume "nonzero_positions(Rep_matrix A) = {}"
  then show "(Rep_matrix A m n) = 0" by (simp add: nonzero_positions_def)
next
  assume a: "nonzero_positions(Rep_matrix A) \<noteq> {}"
  let ?S = "fst`(nonzero_positions(Rep_matrix A))"
  have c: "finite (?S)" by (simp add: finite_nonzero_positions)
  from hyp have d: "Max (?S) < m" by (simp add: a nrows_def)
  have "m \<notin> ?S"
    proof -
      have "m \<in> ?S \<Longrightarrow> m \<le> Max(?S)" by (simp add: Max_ge [OF c])
      moreover from d have "~(m \<le> Max ?S)" by (simp)
      ultimately show "m \<notin> ?S" by (auto)
    qed
  thus "Rep_matrix A m n = 0" by (simp add: nonzero_positions_def image_Collect)
qed

definition transpose_infmatrix :: "'a infmatrix \<Rightarrow> 'a infmatrix" where
  "transpose_infmatrix A j i == A i j"

definition transpose_matrix :: "('a::zero) matrix \<Rightarrow> 'a matrix" where
  "transpose_matrix == Abs_matrix o transpose_infmatrix o Rep_matrix"

declare transpose_infmatrix_def[simp]

lemma transpose_infmatrix_twice[simp]: "transpose_infmatrix (transpose_infmatrix A) = A"
by ((rule ext)+, simp)

lemma transpose_infmatrix: "transpose_infmatrix (\<lambda>j i. P j i) = (\<lambda>j i. P i j)"
  by force

lemma transpose_infmatrix_closed[simp]: "Rep_matrix (Abs_matrix (transpose_infmatrix (Rep_matrix x))) = transpose_infmatrix (Rep_matrix x)"
proof -
  let ?A = "{pos. Rep_matrix x (snd pos) (fst pos) \<noteq> 0}"
  let ?B = "{pos. Rep_matrix x (fst pos) (snd pos) \<noteq> 0}"
  let ?swap = "\<lambda>pos. (snd pos, fst pos)"
  have "finite ?A"
  proof -
    have swap_image: "?swap`?A = ?B"
      by (force simp add: image_def)
    then have "finite (?swap`?A)"
      by (metis (full_types) finite_nonzero_positions nonzero_positions_def)
    moreover
    have "inj_on ?swap ?A" by (simp add: inj_on_def)
    ultimately show "finite ?A"
      using finite_imageD by blast
  qed
  then show ?thesis
    by (simp add: Abs_matrix_inverse matrix_def nonzero_positions_def)
qed

lemma infmatrixforward: "(x::'a infmatrix) = y \<Longrightarrow> \<forall> a b. x a b = y a b"
  by auto

lemma transpose_infmatrix_inject: "(transpose_infmatrix A = transpose_infmatrix B) = (A = B)"
  by (metis transpose_infmatrix_twice)

lemma transpose_matrix_inject: "(transpose_matrix A = transpose_matrix B) = (A = B)"
  unfolding transpose_matrix_def o_def
  by (metis Rep_matrix_inject transpose_infmatrix_closed transpose_infmatrix_inject)

lemma transpose_matrix[simp]: "Rep_matrix(transpose_matrix A) j i = Rep_matrix A i j"
  by (simp add: transpose_matrix_def)

lemma transpose_transpose_id[simp]: "transpose_matrix (transpose_matrix A) = A"
  by (simp add: transpose_matrix_def)

lemma nrows_transpose[simp]: "nrows (transpose_matrix A) = ncols A"
  by (simp add: nrows_def ncols_def nonzero_positions_def transpose_matrix_def image_def)

lemma ncols_transpose[simp]: "ncols (transpose_matrix A) = nrows A"
  by (metis nrows_transpose transpose_transpose_id)

lemma ncols: "ncols A \<le> n \<Longrightarrow> Rep_matrix A m n = 0"
  by (metis nrows nrows_transpose transpose_matrix)

lemma ncols_le: "(ncols A \<le> n) \<longleftrightarrow> (\<forall>j i. n \<le> i \<longrightarrow> (Rep_matrix A j i) = 0)" (is "_ = ?st")
proof -
  have "Rep_matrix A j i = 0"
    if "ncols A \<le> n" "n \<le> i" for j i
    by (meson that le_trans ncols)
  moreover have "ncols A \<le> n"
    if "\<forall>j i. n \<le> i \<longrightarrow> Rep_matrix A j i = 0"
    unfolding ncols_def
  proof (clarsimp split: if_split_asm)
    assume \<section>: "nonzero_positions (Rep_matrix A) \<noteq> {}"
    let ?P = "nonzero_positions (Rep_matrix A)"
    let ?p = "snd`?P"
    have a:"finite ?p" by (simp add: finite_nonzero_positions)
    let ?m = "Max ?p"
    show "Suc (Max (snd ` nonzero_positions (Rep_matrix A))) \<le> n"
      using \<section> that  obtains_MAX [OF finite_nonzero_positions]
      by (metis (mono_tags, lifting) mem_Collect_eq nonzero_positions_def not_less_eq_eq)
  qed
  ultimately show ?thesis
    by auto
qed

lemma less_ncols: "(n < ncols A) = (\<exists>j i. n \<le> i \<and> (Rep_matrix A j i) \<noteq> 0)"
  by (meson linorder_not_le ncols_le)

lemma le_ncols: "(n \<le> ncols A) = (\<forall> m. (\<forall> j i. m \<le> i \<longrightarrow> (Rep_matrix A j i) = 0) \<longrightarrow> n \<le> m)"
  by (meson le_trans ncols ncols_le)

lemma nrows_le: "(nrows A \<le> n) = (\<forall>j i. n \<le> j \<longrightarrow> (Rep_matrix A j i) = 0)" (is ?s)
  by (metis ncols_le ncols_transpose transpose_matrix)

lemma less_nrows: "(m < nrows A) = (\<exists>j i. m \<le> j \<and> (Rep_matrix A j i) \<noteq> 0)"
  by (meson linorder_not_le nrows_le)

lemma le_nrows: "(n \<le> nrows A) = (\<forall> m. (\<forall> j i. m \<le> j \<longrightarrow> (Rep_matrix A j i) = 0) \<longrightarrow> n \<le> m)"
  by (meson order.trans nrows nrows_le)

lemma nrows_notzero: "Rep_matrix A m n \<noteq> 0 \<Longrightarrow> m < nrows A"
  by (meson leI nrows)

lemma ncols_notzero: "Rep_matrix A m n \<noteq> 0 \<Longrightarrow> n < ncols A"
  by (meson leI ncols)

lemma finite_natarray1: "finite {x. x < (n::nat)}"
  by simp

lemma finite_natarray2: "finite {(x, y). x < (m::nat) \<and> y < (n::nat)}"
  by simp

lemma RepAbs_matrix:
  assumes "\<exists>m. \<forall>j i. m \<le> j \<longrightarrow> x j i = 0"  
    and "\<exists>n. \<forall>j i. (n \<le> i \<longrightarrow> x j i = 0)" 
  shows "(Rep_matrix (Abs_matrix x)) = x"
proof -
  have "finite {pos. x (fst pos) (snd pos) \<noteq> 0}"
  proof -
    from assms obtain m n where a: "\<forall>j i. m \<le> j \<longrightarrow> x j i = 0" 
      and b: "\<forall>j i. n \<le> i \<longrightarrow> x j i = 0" by (blast)
    let ?u = "{(i, j). x i j \<noteq> 0}"
    let ?v = "{(i, j). i < m \<and> j < n}"
    have c: "\<And>(m::nat) a. ~(m \<le> a) \<Longrightarrow> a < m" by (arith)
    with a b have d: "?u \<subseteq> ?v" by blast
    moreover have "finite ?v" by (simp add: finite_natarray2)
    moreover have "{pos. x (fst pos) (snd pos) \<noteq> 0} = ?u" by auto
    ultimately show "finite {pos. x (fst pos) (snd pos) \<noteq> 0}"
      by (metis (lifting) finite_subset)
  qed
  then show ?thesis
    by (simp add: Abs_matrix_inverse matrix_def nonzero_positions_def)
qed

definition apply_infmatrix :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a infmatrix \<Rightarrow> 'b infmatrix" where
  "apply_infmatrix f == \<lambda>A. (\<lambda>j i. f (A j i))"

definition apply_matrix :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a::zero) matrix \<Rightarrow> ('b::zero) matrix" where
  "apply_matrix f == \<lambda>A. Abs_matrix (apply_infmatrix f (Rep_matrix A))"

definition combine_infmatrix :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a infmatrix \<Rightarrow> 'b infmatrix \<Rightarrow> 'c infmatrix" where
  "combine_infmatrix f == \<lambda>A B. (\<lambda>j i. f (A j i) (B j i))"

definition combine_matrix :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a::zero) matrix \<Rightarrow> ('b::zero) matrix \<Rightarrow> ('c::zero) matrix" where
  "combine_matrix f == \<lambda>A B. Abs_matrix (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))"

lemma expand_apply_infmatrix[simp]: "apply_infmatrix f A j i = f (A j i)"
  by (simp add: apply_infmatrix_def)

lemma expand_combine_infmatrix[simp]: "combine_infmatrix f A B j i = f (A j i) (B j i)"
  by (simp add: combine_infmatrix_def)

definition commutative :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "commutative f == \<forall>x y. f x y = f y x"

definition associative :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "associative f == \<forall>x y z. f (f x y) z = f x (f y z)"

text\<open>
To reason about associativity and commutativity of operations on matrices,
let's take a step back and look at the general situtation: Assume that we have
sets $A$ and $B$ with $B \subset A$ and an abstraction $u: A \rightarrow B$. This abstraction has to fulfill $u(b) = b$ for all $b \in B$, but is arbitrary otherwise.
Each function $f: A \times A \rightarrow A$ now induces a function $f': B \times B \rightarrow B$ by $f' = u \circ f$.
It is obvious that commutativity of $f$ implies commutativity of $f'$: $f' x y = u (f x y) = u (f y x) = f' y x.$
\<close>

lemma combine_infmatrix_commute:
  "commutative f \<Longrightarrow> commutative (combine_infmatrix f)"
by (simp add: commutative_def combine_infmatrix_def)

lemma combine_matrix_commute:
"commutative f \<Longrightarrow> commutative (combine_matrix f)"
by (simp add: combine_matrix_def commutative_def combine_infmatrix_def)

text\<open>
On the contrary, given an associative function $f$ we cannot expect $f'$ to be associative. A counterexample is given by $A=\bbbZ$, $B=\{-1, 0, 1\}$,
as $f$ we take addition on $\bbbZ$, which is clearly associative. The abstraction is given by  $u(a) = 0$ for $a \notin B$. Then we have
\[ f' (f' 1 1) -1 = u(f (u (f 1 1)) -1) = u(f (u 2) -1) = u (f 0 -1) = -1, \]
but on the other hand we have
\[ f' 1 (f' 1 -1) = u (f 1 (u (f 1 -1))) = u (f 1 0) = 1.\]
A way out of this problem is to assume that $f(A\times A)\subset A$ holds, and this is what we are going to do:
\<close>

lemma nonzero_positions_combine_infmatrix[simp]: "f 0 0 = 0 \<Longrightarrow> nonzero_positions (combine_infmatrix f A B) \<subseteq> (nonzero_positions A) \<union> (nonzero_positions B)"
  by (smt (verit) UnCI expand_combine_infmatrix mem_Collect_eq nonzero_positions_def subsetI)

lemma finite_nonzero_positions_Rep[simp]: "finite (nonzero_positions (Rep_matrix A))"
  by (simp add: finite_nonzero_positions)

lemma combine_infmatrix_closed [simp]:
  "f 0 0 = 0 \<Longrightarrow> Rep_matrix (Abs_matrix (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) = combine_infmatrix f (Rep_matrix A) (Rep_matrix B)"
  apply (rule Abs_matrix_inverse)
  apply (simp add: matrix_def)
  by (meson finite_Un finite_nonzero_positions_Rep finite_subset nonzero_positions_combine_infmatrix)

text \<open>We need the next two lemmas only later, but it is analog to the above one, so we prove them now:\<close>
lemma nonzero_positions_apply_infmatrix[simp]: "f 0 = 0 \<Longrightarrow> nonzero_positions (apply_infmatrix f A) \<subseteq> nonzero_positions A"
by (rule subsetI, simp add: nonzero_positions_def apply_infmatrix_def, auto)

lemma apply_infmatrix_closed [simp]:
  "f 0 = 0 \<Longrightarrow> Rep_matrix (Abs_matrix (apply_infmatrix f (Rep_matrix A))) = apply_infmatrix f (Rep_matrix A)"
apply (rule Abs_matrix_inverse)
apply (simp add: matrix_def)
  by (meson finite_nonzero_positions_Rep finite_subset nonzero_positions_apply_infmatrix)

lemma combine_infmatrix_assoc[simp]: "f 0 0 = 0 \<Longrightarrow> associative f \<Longrightarrow> associative (combine_infmatrix f)"
  by (simp add: associative_def combine_infmatrix_def)

lemma combine_matrix_assoc: "f 0 0 = 0 \<Longrightarrow> associative f \<Longrightarrow> associative (combine_matrix f)"
  by (smt (verit) associative_def combine_infmatrix_assoc combine_infmatrix_closed combine_matrix_def)

lemma Rep_apply_matrix[simp]: "f 0 = 0 \<Longrightarrow> Rep_matrix (apply_matrix f A) j i = f (Rep_matrix A j i)"
  by (simp add: apply_matrix_def)

lemma Rep_combine_matrix[simp]: "f 0 0 = 0 \<Longrightarrow> Rep_matrix (combine_matrix f A B) j i = f (Rep_matrix A j i) (Rep_matrix B j i)"
  by(simp add: combine_matrix_def)

lemma combine_nrows_max: "f 0 0 = 0  \<Longrightarrow> nrows (combine_matrix f A B) \<le> max (nrows A) (nrows B)"
  by (simp add: nrows_le)

lemma combine_ncols_max: "f 0 0 = 0 \<Longrightarrow> ncols (combine_matrix f A B) \<le> max (ncols A) (ncols B)"
  by (simp add: ncols_le)

lemma combine_nrows: "f 0 0 = 0 \<Longrightarrow> nrows A \<le> q \<Longrightarrow> nrows B \<le> q \<Longrightarrow> nrows(combine_matrix f A B) \<le> q"
  by (simp add: nrows_le)

lemma combine_ncols: "f 0 0 = 0 \<Longrightarrow> ncols A \<le> q \<Longrightarrow> ncols B \<le> q \<Longrightarrow> ncols(combine_matrix f A B) \<le> q"
  by (simp add: ncols_le)

definition zero_r_neutral :: "('a \<Rightarrow> 'b::zero \<Rightarrow> 'a) \<Rightarrow> bool" where
  "zero_r_neutral f == \<forall>a. f a 0 = a"

definition zero_l_neutral :: "('a::zero \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
  "zero_l_neutral f == \<forall>a. f 0 a = a"

definition zero_closed :: "(('a::zero) \<Rightarrow> ('b::zero) \<Rightarrow> ('c::zero)) \<Rightarrow> bool" where
  "zero_closed f == (\<forall>x. f x 0 = 0) \<and> (\<forall>y. f 0 y = 0)"

primrec foldseq :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
where
  "foldseq f s 0 = s 0"
| "foldseq f s (Suc n) = f (s 0) (foldseq f (\<lambda>k. s(Suc k)) n)"

primrec foldseq_transposed ::  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
where
  "foldseq_transposed f s 0 = s 0"
| "foldseq_transposed f s (Suc n) = f (foldseq_transposed f s n) (s (Suc n))"

lemma foldseq_assoc: 
  assumes a:"associative f"
  shows "associative f \<Longrightarrow> foldseq f = foldseq_transposed f"
proof -
  have "N \<le> n \<Longrightarrow> foldseq f s N = foldseq_transposed f s N" for N s n
  proof (induct n arbitrary: N s)
    case 0
    then show ?case
      by auto
  next
    case (Suc n)
    show ?case
    proof cases
      assume "N \<le> n"
      then show ?thesis
        by (simp add: Suc.hyps)
    next
      assume "~(N \<le> n)"
      then have Nsuceq: "N = Suc n"
        using Suc.prems by linarith
      have neqz: "n \<noteq> 0 \<Longrightarrow> \<exists>m. n = Suc m \<and> Suc m \<le> n" 
        by arith
      have assocf: "!! x y z. f x (f y z) = f (f x y) z"
        by (metis a associative_def) 
      have "f (f (s 0) (foldseq_transposed f (\<lambda>k. s (Suc k)) m)) (s (Suc (Suc m))) =
                f (f (foldseq_transposed f s m) (s (Suc m))) (s (Suc (Suc m)))"
        if "n = Suc m" for m
      proof -
        have \<section>: "foldseq_transposed f (\<lambda>k. s (Suc k)) m = foldseq f (\<lambda>k. s (Suc k)) m" (is "?T1 = ?T2")
          by (simp add: Suc.hyps that)
        have "f (s 0) ?T2 = foldseq f s (Suc m)" by simp
        also have "\<dots> = foldseq_transposed f s (Suc m)" 
          using Suc.hyps that by blast
        also have "\<dots> = f (foldseq_transposed f s m) (s (Suc m))"  
          by simp
        finally show ?thesis
          by (simp add: \<section>)
      qed
      then show "foldseq f s N = foldseq_transposed f s N"
        unfolding Nsuceq using assocf Suc.hyps neqz by force
    qed
  qed
  then show ?thesis
    by blast
qed

lemma foldseq_distr: 
  assumes assoc: "associative f" and comm: "commutative f"
  shows "foldseq f (\<lambda>k. f (u k) (v k)) n = f (foldseq f u n) (foldseq f v n)"
proof -
  from assoc have a:"!! x y z. f (f x y) z = f x (f y z)" by (simp add: associative_def)
  from comm have b: "!! x y. f x y = f y x" by (simp add: commutative_def)
  from assoc comm have c: "!! x y z. f x (f y z) = f y (f x z)" by (simp add: commutative_def associative_def)
  have "(\<forall>u v. foldseq f (\<lambda>k. f (u k) (v k)) n = f (foldseq f u n) (foldseq f v n))" for n
    by (induct n) (simp_all add: assoc b c foldseq_assoc)
  then show "foldseq f (\<lambda>k. f (u k) (v k)) n = f (foldseq f u n) (foldseq f v n)" by simp
qed

theorem "\<lbrakk>associative f; associative g; \<forall>a b c d. g (f a b) (f c d) = f (g a c) (g b d); \<exists>x y. (f x) \<noteq> (f y); \<exists>x y. (g x) \<noteq> (g y); f x x = x; g x x = x\<rbrakk> \<Longrightarrow> f=g | (\<forall>y. f y x = y) | (\<forall>y. g y x = y)"
oops
(* Model found

Trying to find a model that refutes: \<lbrakk>associative f; associative g;
 \<forall>a b c d. g (f a b) (f c d) = f (g a c) (g b d); \<exists>x y. f x \<noteq> f y;
 \<exists>x y. g x \<noteq> g y; f x x = x; g x x = x\<rbrakk>
\<Longrightarrow> f = g \<or> (\<forall>y. f y x = y) \<or> (\<forall>y. g y x = y)
Searching for a model of size 1, translating term... invoking SAT solver... no model found.
Searching for a model of size 2, translating term... invoking SAT solver... no model found.
Searching for a model of size 3, translating term... invoking SAT solver...
Model found:
Size of types: 'a: 3
x: a1
g: (a0\<mapsto>(a0\<mapsto>a1, a1\<mapsto>a0, a2\<mapsto>a1), a1\<mapsto>(a0\<mapsto>a0, a1\<mapsto>a1, a2\<mapsto>a0), a2\<mapsto>(a0\<mapsto>a1, a1\<mapsto>a0, a2\<mapsto>a1))
f: (a0\<mapsto>(a0\<mapsto>a0, a1\<mapsto>a0, a2\<mapsto>a0), a1\<mapsto>(a0\<mapsto>a1, a1\<mapsto>a1, a2\<mapsto>a1), a2\<mapsto>(a0\<mapsto>a0, a1\<mapsto>a0, a2\<mapsto>a0))
*)

lemma foldseq_zero:
  assumes fz: "f 0 0 = 0" and sz: "\<forall>i. i \<le> n \<longrightarrow> s i = 0"
  shows "foldseq f s n = 0"
proof -
  have "\<forall>s. (\<forall>i. i \<le> n \<longrightarrow> s i = 0) \<longrightarrow> foldseq f s n = 0" for n
    by (induct n) (simp_all add: fz)
  then show ?thesis 
    by (simp add: sz)
qed

lemma foldseq_significant_positions:
  assumes p: "\<forall>i. i \<le> N \<longrightarrow> S i = T i"
  shows "foldseq f S N = foldseq f T N"
  using assms
proof (induction N arbitrary: S T)
  case 0
  then show ?case by simp
next
  case (Suc N)
  then show ?case
    unfolding foldseq.simps by (metis not_less_eq_eq le0)
qed

lemma foldseq_tail:
  assumes "M \<le> N"
  shows "foldseq f S N = foldseq f (\<lambda>k. (if k < M then (S k) else (foldseq f (\<lambda>k. S(k+M)) (N-M)))) M"
  using assms
proof (induction N arbitrary: M S)
  case 0
  then show ?case by auto
next
  case (Suc N)
  show ?case
  proof (cases "M = Suc N")
    case True
    then show ?thesis
      by (auto intro!: arg_cong [of concl: "f (S 0)"] foldseq_significant_positions)
  next
    case False
    then have "M\<le>N"
      using Suc.prems by force
    show ?thesis
    proof (cases "M = 0")
      case True
      then show ?thesis
        by auto
    next
      case False
      then obtain M' where M': "M = Suc M'" "M' \<le> N"
        by (metis Suc_leD \<open>M \<le> N\<close> nat.nchotomy)
      then show ?thesis
        apply (simp add:  Suc.IH [OF \<open>M'\<le>N\<close>])
        using add_Suc_right diff_Suc_Suc by presburger
    qed
  qed
qed

lemma foldseq_zerotail:
  assumes fz: "f 0 0 = 0" and sz: "\<forall>i.  n \<le> i \<longrightarrow> s i = 0" and nm: "n \<le> m"
  shows "foldseq f s n = foldseq f s m"
  unfolding foldseq_tail[OF nm]
  by (metis (no_types, lifting) foldseq_zero fz le_add2 linorder_not_le sz)

lemma foldseq_zerotail2:
  assumes "\<forall>x. f x 0 = x"
  and "\<forall>i. n < i \<longrightarrow> s i = 0"
  and nm: "n \<le> m"
shows "foldseq f s n = foldseq f s m"
proof -
  have "s i = (if i < n then s i else foldseq f (\<lambda>k. s (k + n)) (m - n))"
    if "i\<le>n" for i
  proof (cases "m=n")
    case True
    then show ?thesis
      using that by auto
  next
    case False
    then obtain k where "m-n = Suc k"
      by (metis Suc_diff_Suc le_neq_implies_less nm)
    then show ?thesis
      apply simp
      by (simp add: assms(1,2) foldseq_zero nat_less_le that)
  qed
  then show ?thesis
    unfolding foldseq_tail[OF nm]
    by (auto intro: foldseq_significant_positions)
qed

lemma foldseq_zerostart:
  assumes f00x: "\<forall>x. f 0 (f 0 x) = f 0 x" and 0: "\<forall>i. i \<le> n \<longrightarrow> s i = 0"
  shows "foldseq f s (Suc n) = f 0 (s (Suc n))"
  using 0
proof (induction n arbitrary: s)
  case 0
  then show ?case by auto
next
  case (Suc n s)
  then show ?case 
    apply (simp add: le_Suc_eq)
    by (smt (verit, ccfv_threshold) Suc.prems Suc_le_mono f00x foldseq_significant_positions le0)
qed

lemma foldseq_zerostart2:
  assumes x: "\<forall>x. f 0 x = x" and 0: "\<forall>i. i < n \<longrightarrow> s i = 0"
  shows  "foldseq f s n = s n"
proof -
  show "foldseq f s n = s n"
  proof (cases n)
    case 0
    then show ?thesis
      by auto
  next
    case (Suc n')
    then show ?thesis
      by (metis "0" foldseq_zerostart le_imp_less_Suc x)
  qed
qed

lemma foldseq_almostzero:
  assumes f0x: "\<forall>x. f 0 x = x" and fx0: "\<forall>x. f x 0 = x" and s0: "\<forall>i. i \<noteq> j \<longrightarrow> s i = 0"
  shows "foldseq f s n = (if (j \<le> n) then (s j) else 0)"
  by (smt (verit, ccfv_SIG) f0x foldseq_zerostart2 foldseq_zerotail2 fx0 le_refl nat_less_le s0)

lemma foldseq_distr_unary:
  assumes "\<And>a b. g (f a b) = f (g a) (g b)"
  shows "g(foldseq f s n) = foldseq f (\<lambda>x. g(s x)) n"
proof (induction n arbitrary: s)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
    using assms by fastforce
qed

definition mult_matrix_n :: "nat \<Rightarrow> (('a::zero) \<Rightarrow> ('b::zero) \<Rightarrow> ('c::zero)) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'a matrix \<Rightarrow> 'b matrix \<Rightarrow> 'c matrix" where
  "mult_matrix_n n fmul fadd A B == Abs_matrix(\<lambda>j i. foldseq fadd (\<lambda>k. fmul (Rep_matrix A j k) (Rep_matrix B k i)) n)"

definition mult_matrix :: "(('a::zero) \<Rightarrow> ('b::zero) \<Rightarrow> ('c::zero)) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'a matrix \<Rightarrow> 'b matrix \<Rightarrow> 'c matrix" where
  "mult_matrix fmul fadd A B == mult_matrix_n (max (ncols A) (nrows B)) fmul fadd A B"

lemma mult_matrix_n:
  assumes "ncols A \<le>  n" "nrows B \<le> n" "fadd 0 0 = 0" "fmul 0 0 = 0"
  shows "mult_matrix fmul fadd A B = mult_matrix_n n fmul fadd A B"
proof -
  have "foldseq fadd (\<lambda>k. fmul (Rep_matrix A j k) (Rep_matrix B k i))
                (max (ncols A) (nrows B)) =
        foldseq fadd (\<lambda>k. fmul (Rep_matrix A j k) (Rep_matrix B k i)) n" for i j
    using assms by (simp add: foldseq_zerotail nrows_le ncols_le)
  then show ?thesis
    by (simp add: mult_matrix_def mult_matrix_n_def)
qed

lemma mult_matrix_nm:
  assumes "ncols A \<le> n" "nrows B \<le> n" "ncols A \<le> m" "nrows B \<le> m" "fadd 0 0 = 0" "fmul 0 0 = 0"
  shows "mult_matrix_n n fmul fadd A B = mult_matrix_n m fmul fadd A B"
proof -
  from assms have "mult_matrix_n n fmul fadd A B = mult_matrix fmul fadd A B"
    by (simp add: mult_matrix_n)
  also from assms have "\<dots> = mult_matrix_n m fmul fadd A B"
    by (simp add: mult_matrix_n[THEN sym])
  finally show "mult_matrix_n n fmul fadd A B = mult_matrix_n m fmul fadd A B" by simp
qed

definition r_distributive :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
  "r_distributive fmul fadd == \<forall>a u v. fmul a (fadd u v) = fadd (fmul a u) (fmul a v)"

definition l_distributive :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "l_distributive fmul fadd == \<forall>a u v. fmul (fadd u v) a = fadd (fmul u a) (fmul v a)"

definition distributive :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "distributive fmul fadd == l_distributive fmul fadd \<and> r_distributive fmul fadd"

lemma max1: "!! a x y. (a::nat) \<le> x \<Longrightarrow> a \<le> max x y" by (arith)
lemma max2: "!! b x y. (b::nat) \<le> y \<Longrightarrow> b \<le> max x y" by (arith)

lemma r_distributive_matrix:
 assumes
  "r_distributive fmul fadd"
  "associative fadd"
  "commutative fadd"
  "fadd 0 0 = 0"
  "\<forall>a. fmul a 0 = 0"
  "\<forall>a. fmul 0 a = 0"
 shows "r_distributive (mult_matrix fmul fadd) (combine_matrix fadd)"
proof -
  from assms show ?thesis
    apply (simp add: r_distributive_def mult_matrix_def, auto)
    proof -
      fix a::"'a matrix"
      fix u::"'b matrix"
      fix v::"'b matrix"
      let ?mx = "max (ncols a) (max (nrows u) (nrows v))"
      from assms show "mult_matrix_n (max (ncols a) (nrows (combine_matrix fadd u v))) fmul fadd a (combine_matrix fadd u v) =
        combine_matrix fadd (mult_matrix_n (max (ncols a) (nrows u)) fmul fadd a u) (mult_matrix_n (max (ncols a) (nrows v)) fmul fadd a v)"
        apply (subst mult_matrix_nm[of _ _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of _ _ v ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of _ _ u ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (simp add: mult_matrix_n_def r_distributive_def foldseq_distr[of fadd])
        apply (simp add: combine_matrix_def combine_infmatrix_def)
        apply (intro ext arg_cong[of concl: "Abs_matrix"])
        apply (simplesubst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows a"], simp add: nrows_le foldseq_zero)
        apply (rule exI[of _ "ncols v"], simp add: ncols_le foldseq_zero)
        apply (subst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows a"], simp add: nrows_le foldseq_zero)
        apply (rule exI[of _ "ncols u"], simp add: ncols_le foldseq_zero)
        done
    qed
qed

lemma l_distributive_matrix:
 assumes
  "l_distributive fmul fadd"
  "associative fadd"
  "commutative fadd"
  "fadd 0 0 = 0"
  "\<forall>a. fmul a 0 = 0"
  "\<forall>a. fmul 0 a = 0"
 shows "l_distributive (mult_matrix fmul fadd) (combine_matrix fadd)"
proof -
  from assms show ?thesis
    apply (simp add: l_distributive_def mult_matrix_def, auto)
    proof -
      fix a::"'b matrix"
      fix u::"'a matrix"
      fix v::"'a matrix"
      let ?mx = "max (nrows a) (max (ncols u) (ncols v))"
      from assms show "mult_matrix_n (max (ncols (combine_matrix fadd u v)) (nrows a)) fmul fadd (combine_matrix fadd u v) a =
               combine_matrix fadd (mult_matrix_n (max (ncols u) (nrows a)) fmul fadd u a) (mult_matrix_n (max (ncols v) (nrows a)) fmul fadd v a)"
        apply (subst mult_matrix_nm[of v _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of u _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of _ _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (simp add: mult_matrix_n_def l_distributive_def foldseq_distr[of fadd])
        apply (simp add: combine_matrix_def combine_infmatrix_def)
        apply (intro ext arg_cong[of concl: "Abs_matrix"])
        apply (simplesubst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows v"], simp add: nrows_le foldseq_zero)
        apply (rule exI[of _ "ncols a"], simp add: ncols_le foldseq_zero)
        apply (subst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows u"], simp add: nrows_le foldseq_zero)
        apply (rule exI[of _ "ncols a"], simp add: ncols_le foldseq_zero)
        done
    qed
qed

instantiation matrix :: (zero) zero
begin

definition zero_matrix_def: "0 = Abs_matrix (\<lambda>j i. 0)"

instance ..

end

lemma Rep_zero_matrix_def[simp]: "Rep_matrix 0 j i = 0"
  by (simp add: RepAbs_matrix zero_matrix_def)

lemma zero_matrix_def_nrows[simp]: "nrows 0 = 0"
  using nrows_le by force

lemma zero_matrix_def_ncols[simp]: "ncols 0 = 0"
  using ncols_le by fastforce

lemma combine_matrix_zero_l_neutral: "zero_l_neutral f \<Longrightarrow> zero_l_neutral (combine_matrix f)"
  by (simp add: zero_l_neutral_def combine_matrix_def combine_infmatrix_def)

lemma combine_matrix_zero_r_neutral: "zero_r_neutral f \<Longrightarrow> zero_r_neutral (combine_matrix f)"
  by (simp add: zero_r_neutral_def combine_matrix_def combine_infmatrix_def)

lemma mult_matrix_zero_closed: "\<lbrakk>fadd 0 0 = 0; zero_closed fmul\<rbrakk> \<Longrightarrow> zero_closed (mult_matrix fmul fadd)"
  apply (simp add: zero_closed_def mult_matrix_def mult_matrix_n_def)
  by (simp add: foldseq_zero zero_matrix_def)

lemma mult_matrix_n_zero_right[simp]: "\<lbrakk>fadd 0 0 = 0; \<forall>a. fmul a 0 = 0\<rbrakk> \<Longrightarrow> mult_matrix_n n fmul fadd A 0 = 0"
  by (simp add: RepAbs_matrix foldseq_zero matrix_eqI mult_matrix_n_def)

lemma mult_matrix_n_zero_left[simp]: "\<lbrakk>fadd 0 0 = 0; \<forall>a. fmul 0 a = 0\<rbrakk> \<Longrightarrow> mult_matrix_n n fmul fadd 0 A = 0"
  by (simp add: RepAbs_matrix foldseq_zero matrix_eqI mult_matrix_n_def)

lemma mult_matrix_zero_left[simp]: "\<lbrakk>fadd 0 0 = 0; \<forall>a. fmul 0 a = 0\<rbrakk> \<Longrightarrow> mult_matrix fmul fadd 0 A = 0"
  by (simp add: mult_matrix_def)

lemma mult_matrix_zero_right[simp]: "\<lbrakk>fadd 0 0 = 0; \<forall>a. fmul a 0 = 0\<rbrakk> \<Longrightarrow> mult_matrix fmul fadd A 0 = 0"
  by (simp add: mult_matrix_def)

lemma apply_matrix_zero[simp]: "f 0 = 0 \<Longrightarrow> apply_matrix f 0 = 0"
  by (simp add: matrix_eqI)

lemma combine_matrix_zero: "f 0 0 = 0 \<Longrightarrow> combine_matrix f 0 0 = 0"
  by (simp add: matrix_eqI)

lemma transpose_matrix_zero[simp]: "transpose_matrix 0 = 0"
  by (simp add: matrix_eqI)

lemma apply_zero_matrix_def[simp]: "apply_matrix (\<lambda>x. 0) A = 0"
  by (simp add: matrix_eqI)

definition singleton_matrix :: "nat \<Rightarrow> nat \<Rightarrow> ('a::zero) \<Rightarrow> 'a matrix" where
  "singleton_matrix j i a == Abs_matrix(\<lambda>m n. if j = m \<and> i = n then a else 0)"

definition move_matrix :: "('a::zero) matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a matrix" where
  "move_matrix A y x == Abs_matrix(\<lambda>j i. if (((int j)-y) < 0) | (((int i)-x) < 0) then 0 else Rep_matrix A (nat ((int j)-y)) (nat ((int i)-x)))"

definition take_rows :: "('a::zero) matrix \<Rightarrow> nat \<Rightarrow> 'a matrix" where
  "take_rows A r == Abs_matrix(\<lambda>j i. if (j < r) then (Rep_matrix A j i) else 0)"

definition take_columns :: "('a::zero) matrix \<Rightarrow> nat \<Rightarrow> 'a matrix" where
  "take_columns A c == Abs_matrix(\<lambda>j i. if (i < c) then (Rep_matrix A j i) else 0)"

definition column_of_matrix :: "('a::zero) matrix \<Rightarrow> nat \<Rightarrow> 'a matrix" where
  "column_of_matrix A n == take_columns (move_matrix A 0 (- int n)) 1"

definition row_of_matrix :: "('a::zero) matrix \<Rightarrow> nat \<Rightarrow> 'a matrix" where
  "row_of_matrix A m == take_rows (move_matrix A (- int m) 0) 1"

lemma Rep_singleton_matrix[simp]: "Rep_matrix (singleton_matrix j i e) m n = (if j = m \<and> i = n then e else 0)"
  unfolding singleton_matrix_def
  by (smt (verit, del_insts) RepAbs_matrix Suc_n_not_le_n)

lemma apply_singleton_matrix[simp]: "f 0 = 0 \<Longrightarrow> apply_matrix f (singleton_matrix j i x) = (singleton_matrix j i (f x))"
  by (simp add: matrix_eqI)

lemma singleton_matrix_zero[simp]: "singleton_matrix j i 0 = 0"
  by (simp add: singleton_matrix_def zero_matrix_def)

lemma nrows_singleton[simp]: "nrows(singleton_matrix j i e) = (if e = 0 then 0 else Suc j)"
proof -
  have "e \<noteq> 0 \<Longrightarrow> Suc j \<le> nrows (singleton_matrix j i e)"
    by (metis Rep_singleton_matrix not_less_eq_eq nrows)
  then show ?thesis
    by (simp add: le_antisym nrows_le)
qed

lemma ncols_singleton[simp]: "ncols(singleton_matrix j i e) = (if e = 0 then 0 else Suc i)"
  by (simp add: Suc_leI le_antisym ncols_le ncols_notzero)

lemma combine_singleton: "f 0 0 = 0 \<Longrightarrow> combine_matrix f (singleton_matrix j i a) (singleton_matrix j i b) = singleton_matrix j i (f a b)"
  apply (simp add: singleton_matrix_def combine_matrix_def combine_infmatrix_def)
  apply (intro ext arg_cong[of concl: "Abs_matrix"])
  by (metis Rep_singleton_matrix singleton_matrix_def)

lemma transpose_singleton[simp]: "transpose_matrix (singleton_matrix j i a) = singleton_matrix i j a"
  by (simp add: matrix_eqI)

lemma Rep_move_matrix[simp]:
  "Rep_matrix (move_matrix A y x) j i =
  (if (((int j)-y) < 0) | (((int i)-x) < 0) then 0 else Rep_matrix A (nat((int j)-y)) (nat((int i)-x)))"
  apply (simp add: move_matrix_def)
by (subst RepAbs_matrix,
  rule exI[of _ "(nrows A)+(nat \<bar>y\<bar>)"], auto, rule nrows, arith,
  rule exI[of _ "(ncols A)+(nat \<bar>x\<bar>)"], auto, rule ncols, arith)+

lemma move_matrix_0_0[simp]: "move_matrix A 0 0 = A"
  by (simp add: move_matrix_def)

lemma move_matrix_ortho: "move_matrix A j i = move_matrix (move_matrix A j 0) 0 i"
  by (simp add: matrix_eqI)

lemma transpose_move_matrix[simp]:
  "transpose_matrix (move_matrix A x y) = move_matrix (transpose_matrix A) y x"
  by (simp add: matrix_eqI)

lemma move_matrix_singleton[simp]: "move_matrix (singleton_matrix u v x) j i =
  (if (j + int u < 0) | (i + int v < 0) then 0 else (singleton_matrix (nat (j + int u)) (nat (i + int v)) x))"
  by (auto intro!: matrix_eqI split: if_split_asm)

lemma Rep_take_columns[simp]:
  "Rep_matrix (take_columns A c) j i = (if i < c then (Rep_matrix A j i) else 0)"
  unfolding take_columns_def
  by (smt (verit, best) RepAbs_matrix leD nrows)

lemma Rep_take_rows[simp]:
  "Rep_matrix (take_rows A r) j i = (if j < r then (Rep_matrix A j i) else 0)"
  unfolding take_rows_def
  by (smt (verit, best) RepAbs_matrix leD ncols)

lemma Rep_column_of_matrix[simp]:
  "Rep_matrix (column_of_matrix A c) j i = (if i = 0 then (Rep_matrix A j c) else 0)"
  by (simp add: column_of_matrix_def)

lemma Rep_row_of_matrix[simp]:
  "Rep_matrix (row_of_matrix A r) j i = (if j = 0 then (Rep_matrix A r i) else 0)"
  by (simp add: row_of_matrix_def)

lemma column_of_matrix: "ncols A \<le> n \<Longrightarrow> column_of_matrix A n = 0"
  by (simp add: matrix_eqI ncols)

lemma row_of_matrix: "nrows A \<le> n \<Longrightarrow> row_of_matrix A n = 0"
  by (simp add: matrix_eqI nrows)

lemma mult_matrix_singleton_right[simp]:
  assumes "\<forall>x. fmul x 0 = 0" "\<forall>x. fmul 0 x = 0" "\<forall>x. fadd 0 x = x" "\<forall>x. fadd x 0 = x"
  shows "(mult_matrix fmul fadd A (singleton_matrix j i e)) = apply_matrix (\<lambda>x. fmul x e) (move_matrix (column_of_matrix A j) 0 (int i))"
  using assms
  unfolding mult_matrix_def
  apply (subst mult_matrix_nm[of _ _ _ "max (ncols A) (Suc j)"];
         simp add: mult_matrix_n_def apply_matrix_def apply_infmatrix_def)
  apply (intro ext arg_cong[of concl: "Abs_matrix"])
  by (simp add: max_def assms foldseq_almostzero[of _ j])

lemma mult_matrix_ext:
  assumes
  eprem:
  "\<exists>e. (\<forall>a b. a \<noteq> b \<longrightarrow> fmul a e \<noteq> fmul b e)"
  and fprems:
  "\<forall>a. fmul 0 a = 0"
  "\<forall>a. fmul a 0 = 0"
  "\<forall>a. fadd a 0 = a"
  "\<forall>a. fadd 0 a = a"
  and contraprems: "mult_matrix fmul fadd A = mult_matrix fmul fadd B"
  shows "A = B"
proof(rule ccontr)
  assume "A \<noteq> B"
  then obtain J I where ne: "(Rep_matrix A J I) \<noteq> (Rep_matrix B J I)"
    by (meson matrix_eqI)
  from eprem obtain e where eprops:"(\<forall>a b. a \<noteq> b \<longrightarrow> fmul a e \<noteq> fmul b e)" by blast
  let ?S = "singleton_matrix I 0 e"
  let ?comp = "mult_matrix fmul fadd"
  have d: "!!x f g. f = g \<Longrightarrow> f x = g x" by blast
  have e: "(\<lambda>x. fmul x e) 0 = 0" by (simp add: assms)
  have "Rep_matrix (apply_matrix (\<lambda>x. fmul x e) (column_of_matrix A I)) \<noteq>
        Rep_matrix (apply_matrix (\<lambda>x. fmul x e) (column_of_matrix B I))"
    using fprems
    by (metis Rep_apply_matrix Rep_column_of_matrix eprops ne)
  then have "?comp A ?S \<noteq> ?comp B ?S"
    by (simp add: fprems eprops Rep_matrix_inject)
  with contraprems show "False" by simp
qed

definition foldmatrix :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a infmatrix) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "foldmatrix f g A m n == foldseq_transposed g (\<lambda>j. foldseq f (A j) n) m"

definition foldmatrix_transposed :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a infmatrix) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "foldmatrix_transposed f g A m n == foldseq g (\<lambda>j. foldseq_transposed f (A j) n) m"

lemma foldmatrix_transpose:
  assumes "\<forall>a b c d. g(f a b) (f c d) = f (g a c) (g b d)"
  shows "foldmatrix f g A m n = foldmatrix_transposed g f (transpose_infmatrix A) n m"
proof -
  have forall:"\<And>P x. (\<forall>x. P x) \<Longrightarrow> P x" by auto
  have tworows:"\<forall>A. foldmatrix f g A 1 n = foldmatrix_transposed g f (transpose_infmatrix A) n 1"
  proof (induct n)
    case 0
    then show ?case 
      by (simp add: foldmatrix_def foldmatrix_transposed_def)
  next
    case (Suc n)
    then show ?case
      apply (clarsimp simp: foldmatrix_def foldmatrix_transposed_def assms)
      apply (rule arg_cong [of concl: "f _"])
      by meson 
  qed
  have "foldseq_transposed g (\<lambda>j. foldseq f (A j) n) m =
    foldseq f (\<lambda>j. foldseq_transposed g (transpose_infmatrix A j) m) n"
  proof (induct m)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    then show ?case
      using tworows
      apply (drule_tac x="\<lambda>j i. (if j = 0 then (foldseq_transposed g (\<lambda>u. A u i) m) else (A (Suc m) i))" in spec)
      by (simp add: Suc foldmatrix_def foldmatrix_transposed_def)
  qed
  then show "foldmatrix f g A m n = foldmatrix_transposed g f (transpose_infmatrix A) n m"
    by (simp add: foldmatrix_def foldmatrix_transposed_def)
qed

lemma foldseq_foldseq:
assumes "associative f" "associative g" "\<forall>a b c d. g(f a b) (f c d) = f (g a c) (g b d)"
shows
  "foldseq g (\<lambda>j. foldseq f (A j) n) m = foldseq f (\<lambda>j. foldseq g ((transpose_infmatrix A) j) m) n"
  using foldmatrix_transpose[of g f A m n]
  by (simp add: foldmatrix_def foldmatrix_transposed_def foldseq_assoc[THEN sym] assms)

lemma mult_n_nrows:
  assumes "\<forall>a. fmul 0 a = 0" "\<forall>a. fmul a 0 = 0" "fadd 0 0 = 0"
  shows "nrows (mult_matrix_n n fmul fadd A B) \<le> nrows A"
  unfolding nrows_le mult_matrix_n_def
  apply (subst RepAbs_matrix)
    apply (rule_tac x="nrows A" in exI)
    apply (simp add: nrows assms foldseq_zero)
   apply (rule_tac x="ncols B" in exI)
   apply (simp add: ncols assms foldseq_zero)
  apply (simp add: nrows assms foldseq_zero)
  done

lemma mult_n_ncols:
  assumes "\<forall>a. fmul 0 a = 0" "\<forall>a. fmul a 0 = 0" "fadd 0 0 = 0"
  shows "ncols (mult_matrix_n n fmul fadd A B) \<le> ncols B"
  unfolding ncols_le mult_matrix_n_def
  apply (subst RepAbs_matrix)
    apply (rule_tac x="nrows A" in exI)
    apply (simp add: nrows assms foldseq_zero)
   apply (rule_tac x="ncols B" in exI)
   apply (simp add: ncols assms foldseq_zero)
  apply (simp add: ncols assms foldseq_zero)
  done

lemma mult_nrows:
  assumes
    "\<forall>a. fmul 0 a = 0"
    "\<forall>a. fmul a 0 = 0"
    "fadd 0 0 = 0"
  shows "nrows (mult_matrix fmul fadd A B) \<le> nrows A"
  by (simp add: mult_matrix_def mult_n_nrows assms)

lemma mult_ncols:
  assumes
    "\<forall>a. fmul 0 a = 0"
    "\<forall>a. fmul a 0 = 0"
    "fadd 0 0 = 0"
  shows "ncols (mult_matrix fmul fadd A B) \<le> ncols B"
  by (simp add: mult_matrix_def mult_n_ncols assms)

lemma nrows_move_matrix_le: "nrows (move_matrix A j i) \<le> nat((int (nrows A)) + j)"
  by (smt (verit) Rep_move_matrix int_nat_eq nrows nrows_le of_nat_le_iff)

lemma ncols_move_matrix_le: "ncols (move_matrix A j i) \<le> nat((int (ncols A)) + i)"
  by (metis nrows_move_matrix_le nrows_transpose transpose_move_matrix)

lemma mult_matrix_assoc:
  assumes
  "\<forall>a. fmul1 0 a = 0"
  "\<forall>a. fmul1 a 0 = 0"
  "\<forall>a. fmul2 0 a = 0"
  "\<forall>a. fmul2 a 0 = 0"
  "fadd1 0 0 = 0"
  "fadd2 0 0 = 0"
  "\<forall>a b c d. fadd2 (fadd1 a b) (fadd1 c d) = fadd1 (fadd2 a c) (fadd2 b d)"
  "associative fadd1"
  "associative fadd2"
  "\<forall>a b c. fmul2 (fmul1 a b) c = fmul1 a (fmul2 b c)"
  "\<forall>a b c. fmul2 (fadd1 a b) c = fadd1 (fmul2 a c) (fmul2 b c)"
  "\<forall>a b c. fmul1 c (fadd2 a b) = fadd2 (fmul1 c a) (fmul1 c b)"
  shows "mult_matrix fmul2 fadd2 (mult_matrix fmul1 fadd1 A B) C = mult_matrix fmul1 fadd1 A (mult_matrix fmul2 fadd2 B C)"
proof -
  have comb_left:  "!! A B x y. A = B \<Longrightarrow> (Rep_matrix (Abs_matrix A)) x y = (Rep_matrix(Abs_matrix B)) x y" by blast
  have fmul2fadd1fold: "!! x s n. fmul2 (foldseq fadd1 s n)  x = foldseq fadd1 (\<lambda>k. fmul2 (s k) x) n"
    by (rule_tac g1 = "\<lambda>y. fmul2 y x" in ssubst [OF foldseq_distr_unary], insert assms, simp_all)
  have fmul1fadd2fold: "!! x s n. fmul1 x (foldseq fadd2 s n) = foldseq fadd2 (\<lambda>k. fmul1 x (s k)) n"
    using assms by (rule_tac g1 = "\<lambda>y. fmul1 x y" in ssubst [OF foldseq_distr_unary], simp_all)
  let ?N = "max (ncols A) (max (ncols B) (max (nrows B) (nrows C)))"
  show ?thesis
    apply (intro matrix_eqI)
    apply (simp add: mult_matrix_def)
    apply (simplesubst mult_matrix_nm[of _ "max (ncols (mult_matrix_n (max (ncols A) (nrows B)) fmul1 fadd1 A B)) (nrows C)" _ "max (ncols B) (nrows C)"])
          apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ "max (ncols A) (nrows (mult_matrix_n (max (ncols B) (nrows C)) fmul2 fadd2 B C))" _ "max (ncols A) (nrows B)"])
          apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
          apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
          apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
          apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
          apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simp add: mult_matrix_n_def)
    apply (rule comb_left)
    apply ((rule ext)+, simp)
    apply (simplesubst RepAbs_matrix)
      apply (rule exI[of _ "nrows B"])
      apply (simp add: nrows assms foldseq_zero)
     apply (rule exI[of _ "ncols C"])
     apply (simp add: assms ncols foldseq_zero)
    apply (subst RepAbs_matrix)
      apply (rule exI[of _ "nrows A"])
      apply (simp add: nrows assms foldseq_zero)
     apply (rule exI[of _ "ncols B"])
     apply (simp add: assms ncols foldseq_zero)
    apply (simp add: fmul2fadd1fold fmul1fadd2fold assms)
    apply (subst foldseq_foldseq)
       apply (simp add: assms)+
    apply (simp add: transpose_infmatrix)
    done
qed

lemma mult_matrix_assoc_simple:
  assumes
  "\<forall>a. fmul 0 a = 0"
  "\<forall>a. fmul a 0 = 0"
  "associative fadd"
  "commutative fadd"
  "associative fmul"
  "distributive fmul fadd"
  shows "mult_matrix fmul fadd (mult_matrix fmul fadd A B) C = mult_matrix fmul fadd A (mult_matrix fmul fadd B C)"
  by (smt (verit) assms associative_def commutative_def distributive_def l_distributive_def mult_matrix_assoc r_distributive_def)

lemma transpose_apply_matrix: "f 0 = 0 \<Longrightarrow> transpose_matrix (apply_matrix f A) = apply_matrix f (transpose_matrix A)"
  by (simp add: matrix_eqI)

lemma transpose_combine_matrix: "f 0 0 = 0 \<Longrightarrow> transpose_matrix (combine_matrix f A B) = combine_matrix f (transpose_matrix A) (transpose_matrix B)"
  by (simp add: matrix_eqI)

lemma Rep_mult_matrix:
  assumes "\<forall>a. fmul 0 a = 0" "\<forall>a. fmul a 0 = 0" "fadd 0 0 = 0"
  shows
    "Rep_matrix(mult_matrix fmul fadd A B) j i =
  foldseq fadd (\<lambda>k. fmul (Rep_matrix A j k) (Rep_matrix B k i)) (max (ncols A) (nrows B))"
  using assms
  apply (simp add: mult_matrix_def mult_matrix_n_def)
  apply (subst RepAbs_matrix)
    apply (rule exI[of _ "nrows A"], simp add: nrows foldseq_zero)
   apply (rule exI[of _ "ncols B"], simp add: ncols foldseq_zero)
  apply simp
  done

lemma transpose_mult_matrix:
  assumes
  "\<forall>a. fmul 0 a = 0"
  "\<forall>a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  "\<forall>x y. fmul y x = fmul x y"
  shows
  "transpose_matrix (mult_matrix fmul fadd A B) = mult_matrix fmul fadd (transpose_matrix B) (transpose_matrix A)"
  using assms
  by (simp add: matrix_eqI Rep_mult_matrix ac_simps) 

lemma column_transpose_matrix: "column_of_matrix (transpose_matrix A) n = transpose_matrix (row_of_matrix A n)"
  by (simp add: matrix_eqI)

lemma take_columns_transpose_matrix: "take_columns (transpose_matrix A) n = transpose_matrix (take_rows A n)"
  by (simp add: matrix_eqI)

instantiation matrix :: ("{zero, ord}") ord
begin

definition
  le_matrix_def: "A \<le> B \<longleftrightarrow> (\<forall>j i. Rep_matrix A j i \<le> Rep_matrix B j i)"

definition
  less_def: "A < (B::'a matrix) \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> A"

instance ..

end

instance matrix :: ("{zero, order}") order
proof
  fix x y z :: "'a matrix"
  assume "x \<le> y" "y \<le> z"
  show "x \<le> z"
    by (meson \<open>x \<le> y\<close> \<open>y \<le> z\<close> le_matrix_def order_trans)
next
  fix x y :: "'a matrix"
  assume "x \<le> y" "y \<le> x"
  show "x = y"
    by (meson \<open>x \<le> y\<close> \<open>y \<le> x\<close> le_matrix_def matrix_eqI order_antisym)
qed (auto simp: less_def le_matrix_def)

lemma le_apply_matrix:
  assumes
  "f 0 = 0"
  "\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"
  "(a::('a::{ord, zero}) matrix) \<le> b"
  shows "apply_matrix f a \<le> apply_matrix f b"
  using assms by (simp add: le_matrix_def)

lemma le_combine_matrix:
  assumes
  "f 0 0 = 0"
  "\<forall>a b c d. a \<le> b \<and> c \<le> d \<longrightarrow> f a c \<le> f b d"
  "A \<le> B"
  "C \<le> D"
  shows "combine_matrix f A C \<le> combine_matrix f B D"
  using assms by (simp add: le_matrix_def)

lemma le_left_combine_matrix:
  assumes
  "f 0 0 = 0"
  "\<forall>a b c. a \<le> b \<longrightarrow> f c a \<le> f c b"
  "A \<le> B"
  shows "combine_matrix f C A \<le> combine_matrix f C B"
  using assms by (simp add: le_matrix_def)

lemma le_right_combine_matrix:
  assumes
  "f 0 0 = 0"
  "\<forall>a b c. a \<le> b \<longrightarrow> f a c \<le> f b c"
  "A \<le> B"
  shows "combine_matrix f A C \<le> combine_matrix f B C"
  using assms by (simp add: le_matrix_def)

lemma le_transpose_matrix: "(A \<le> B) = (transpose_matrix A \<le> transpose_matrix B)"
  by (simp add: le_matrix_def, auto)

lemma le_foldseq:
  assumes
  "\<forall>a b c d . a \<le> b \<and> c \<le> d \<longrightarrow> f a c \<le> f b d"
  "\<forall>i. i \<le> n \<longrightarrow> s i \<le> t i"
  shows "foldseq f s n \<le> foldseq f t n"
proof -
  have "\<forall>s t. (\<forall>i. i<=n \<longrightarrow> s i \<le> t i) \<longrightarrow> foldseq f s n \<le> foldseq f t n"
    by (induct n) (simp_all add: assms)
  then show "foldseq f s n \<le> foldseq f t n" using assms by simp
qed

lemma le_left_mult:
  assumes
  "\<forall>a b c d. a \<le> b \<and> c \<le> d \<longrightarrow> fadd a c \<le> fadd b d"
  "\<forall>c a b.   0 \<le> c \<and> a \<le> b \<longrightarrow> fmul c a \<le> fmul c b"
  "\<forall>a. fmul 0 a = 0"
  "\<forall>a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  "0 \<le> C"
  "A \<le> B"
  shows "mult_matrix fmul fadd C A \<le> mult_matrix fmul fadd C B"
  using assms
  apply (auto simp: le_matrix_def Rep_mult_matrix)
  apply (simplesubst foldseq_zerotail[of _ _ _ "max (ncols C) (max (nrows A) (nrows B))"], simp_all add: nrows ncols max1 max2)+
  apply (rule le_foldseq)
  apply (auto)
  done

lemma le_right_mult:
  assumes
  "\<forall>a b c d. a \<le> b \<and> c \<le> d \<longrightarrow> fadd a c \<le> fadd b d"
  "\<forall>c a b. 0 \<le> c \<and> a \<le> b \<longrightarrow> fmul a c \<le> fmul b c"
  "\<forall>a. fmul 0 a = 0"
  "\<forall>a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  "0 \<le> C"
  "A \<le> B"
  shows "mult_matrix fmul fadd A C \<le> mult_matrix fmul fadd B C"
  using assms
  apply (auto simp: le_matrix_def Rep_mult_matrix)
  apply (simplesubst foldseq_zerotail[of _ _ _ "max (nrows C) (max (ncols A) (ncols B))"], simp_all add: nrows ncols max1 max2)+
  apply (rule le_foldseq)
  apply (auto)
  done

lemma spec2: "\<forall>j i. P j i \<Longrightarrow> P j i" by blast

lemma singleton_matrix_le[simp]: "(singleton_matrix j i a \<le> singleton_matrix j i b) = (a \<le> (b::_::order))"
  by (auto simp: le_matrix_def)

lemma singleton_le_zero[simp]: "(singleton_matrix j i x \<le> 0) = (x \<le> (0::'a::{order,zero}))"
  by (metis singleton_matrix_le singleton_matrix_zero)

lemma singleton_ge_zero[simp]: "(0 \<le> singleton_matrix j i x) = ((0::'a::{order,zero}) \<le> x)"
  by (metis singleton_matrix_le singleton_matrix_zero)

lemma move_matrix_le_zero[simp]: 
  fixes A:: "'a::{order,zero} matrix"
  assumes "0 \<le> j" "0 \<le> i"
  shows "(move_matrix A j i \<le> 0) = (A \<le> 0)"
proof -
  have "Rep_matrix A j' i' \<le> 0"
    if "\<forall>n m. \<not> int n < j \<and> \<not> int m < i \<longrightarrow> Rep_matrix A (nat (int n - j)) (nat (int m - i)) \<le> 0"
    for j' i'
    using that[rule_format, of "j' + nat j" "i' + nat i"] by (simp add: assms)
  then show ?thesis
    by (auto simp: le_matrix_def)
qed

lemma move_matrix_zero_le[simp]:
  fixes A:: "'a::{order,zero} matrix"
  assumes "0 \<le> j" "0 \<le> i"
  shows  "(0 \<le> move_matrix A j i) = (0 \<le> A)"
proof -
  have "0 \<le> Rep_matrix A j' i'"
    if "\<forall>n m. \<not> int n < j \<and> \<not> int m < i \<longrightarrow> 0 \<le> Rep_matrix A (nat (int n - j)) (nat (int m - i))"
    for j' i'
    using that[rule_format, of "j' + nat j" "i' + nat i"] by (simp add: assms)
  then show ?thesis
    by (auto simp: le_matrix_def)
qed

lemma move_matrix_le_move_matrix_iff[simp]:
  fixes A:: "'a::{order,zero} matrix"
  assumes "0 \<le> j" "0 \<le> i"
  shows "(move_matrix A j i \<le> move_matrix B j i) = (A \<le> B)"
proof -
  have "Rep_matrix A j' i' \<le> Rep_matrix B j' i'"
    if "\<forall>n m. \<not> int n < j \<and> \<not> int m < i \<longrightarrow> Rep_matrix A (nat (int n - j)) (nat (int m - i)) \<le> Rep_matrix B (nat (int n - j)) (nat (int m - i))"
    for j' i'
    using that[rule_format, of "j' + nat j" "i' + nat i"] by (simp add: assms)
  then show ?thesis
    by (auto simp: le_matrix_def)
qed

instantiation matrix :: ("{lattice, zero}") lattice
begin

definition "inf = combine_matrix inf"

definition "sup = combine_matrix sup"

instance
  by standard (auto simp: le_infI le_matrix_def inf_matrix_def sup_matrix_def)

end

instantiation matrix :: ("{plus, zero}") plus
begin

definition
  plus_matrix_def: "A + B = combine_matrix (+) A B"

instance ..

end

instantiation matrix :: ("{uminus, zero}") uminus
begin

definition
  minus_matrix_def: "- A = apply_matrix uminus A"

instance ..

end

instantiation matrix :: ("{minus, zero}") minus
begin

definition
  diff_matrix_def: "A - B = combine_matrix (-) A B"

instance ..

end

instantiation matrix :: ("{plus, times, zero}") times
begin

definition
  times_matrix_def: "A * B = mult_matrix ((*)) (+) A B"

instance ..

end

instantiation matrix :: ("{lattice, uminus, zero}") abs
begin

definition
  abs_matrix_def: "\<bar>A :: 'a matrix\<bar> = sup A (- A)"

instance ..

end

instance matrix :: (monoid_add) monoid_add
proof
  fix A B C :: "'a matrix"
  show "A + B + C = A + (B + C)"
    by (simp add: add.assoc matrix_eqI plus_matrix_def)    
  show "0 + A = A"
    by (simp add: matrix_eqI plus_matrix_def)
  show "A + 0 = A"
    by (simp add: matrix_eqI plus_matrix_def)
qed

instance matrix :: (comm_monoid_add) comm_monoid_add
proof
  fix A B :: "'a matrix"
  show "A + B = B + A"
    by (simp add: add.commute matrix_eqI plus_matrix_def)
  show "0 + A = A"
    by (simp add: plus_matrix_def matrix_eqI)
qed

instance matrix :: (group_add) group_add
proof
  fix A B :: "'a matrix"
  show "- A + A = 0" 
    by (simp add: plus_matrix_def minus_matrix_def matrix_eqI)
  show "A + - B = A - B"
    by (simp add: plus_matrix_def diff_matrix_def minus_matrix_def matrix_eqI)
qed

instance matrix :: (ab_group_add) ab_group_add
proof
  fix A B :: "'a matrix"
  show "- A + A = 0" 
    by (simp add: plus_matrix_def minus_matrix_def matrix_eqI)
  show "A - B = A + - B" 
    by (simp add: plus_matrix_def diff_matrix_def minus_matrix_def matrix_eqI)
qed

instance matrix :: (ordered_ab_group_add) ordered_ab_group_add
proof
  fix A B C :: "'a matrix"
  assume "A \<le> B"
  then show "C + A \<le> C + B"
    by (simp add: le_matrix_def plus_matrix_def)
qed
  
instance matrix :: (lattice_ab_group_add) semilattice_inf_ab_group_add ..
instance matrix :: (lattice_ab_group_add) semilattice_sup_ab_group_add ..

instance matrix :: (semiring_0) semiring_0
proof
  fix A B C :: "'a matrix"
  show "A * B * C = A * (B * C)"
    unfolding times_matrix_def
    by (smt (verit, best) add.assoc associative_def distrib_left distrib_right group_cancel.add2 mult.assoc mult_matrix_assoc mult_not_zero)
  show "(A + B) * C = A * C + B * C"
    unfolding times_matrix_def plus_matrix_def
    using l_distributive_matrix
    by (metis (full_types) add.assoc add.commute associative_def commutative_def distrib_right l_distributive_def mult_not_zero)
  show "A * (B + C) = A * B + A * C"
    unfolding times_matrix_def plus_matrix_def
    using r_distributive_matrix
    by (metis (no_types, lifting) add.assoc add.commute associative_def commutative_def distrib_left mult_zero_left mult_zero_right r_distributive_def) 
qed (auto simp: times_matrix_def)

instance matrix :: (ring) ring ..

instance matrix :: (ordered_ring) ordered_ring
proof
  fix A B C :: "'a matrix"
  assume \<section>: "A \<le> B" "0 \<le> C"
  from \<section> show "C * A \<le> C * B"
    by (simp add: times_matrix_def add_mono le_left_mult mult_left_mono)
  from \<section> show "A * C \<le> B * C"
    by (simp add: times_matrix_def add_mono le_right_mult mult_right_mono)
qed

instance matrix :: (lattice_ring) lattice_ring
proof
  fix A B C :: "('a :: lattice_ring) matrix"
  show "\<bar>A\<bar> = sup A (-A)" 
    by (simp add: abs_matrix_def)
qed

instance matrix :: (lattice_ab_group_add_abs) lattice_ab_group_add_abs
proof
  show "\<And>a:: 'a matrix. \<bar>a\<bar> = sup a (- a)"
    by (simp add: abs_matrix_def)
qed

lemma Rep_matrix_add[simp]:
  "Rep_matrix ((a::('a::monoid_add)matrix)+b) j i  = (Rep_matrix a j i) + (Rep_matrix b j i)"
  by (simp add: plus_matrix_def)

lemma Rep_matrix_mult: "Rep_matrix ((a::('a::semiring_0) matrix) * b) j i = 
  foldseq (+) (\<lambda>k.  (Rep_matrix a j k) * (Rep_matrix b k i)) (max (ncols a) (nrows b))"
  by (simp add: times_matrix_def Rep_mult_matrix)

lemma apply_matrix_add: "\<forall>x y. f (x+y) = (f x) + (f y) \<Longrightarrow> f 0 = (0::'a)
  \<Longrightarrow> apply_matrix f ((a::('a::monoid_add) matrix) + b) = (apply_matrix f a) + (apply_matrix f b)"
  by (simp add: matrix_eqI)

lemma singleton_matrix_add: "singleton_matrix j i ((a::_::monoid_add)+b) = (singleton_matrix j i a) + (singleton_matrix j i b)"
  by (simp add: matrix_eqI)

lemma nrows_mult: "nrows ((A::('a::semiring_0) matrix) * B) \<le> nrows A"
  by (simp add: times_matrix_def mult_nrows)

lemma ncols_mult: "ncols ((A::('a::semiring_0) matrix) * B) \<le> ncols B"
  by (simp add: times_matrix_def mult_ncols)

definition
  one_matrix :: "nat \<Rightarrow> ('a::{zero,one}) matrix" where
  "one_matrix n = Abs_matrix (\<lambda>j i. if j = i \<and> j < n then 1 else 0)"

lemma Rep_one_matrix[simp]: "Rep_matrix (one_matrix n) j i = (if (j = i \<and> j < n) then 1 else 0)"
  unfolding one_matrix_def
  by (smt (verit, del_insts) RepAbs_matrix not_le)

lemma nrows_one_matrix[simp]: "nrows ((one_matrix n) :: ('a::zero_neq_one)matrix) = n" (is "?r = _")
proof -
  have "?r \<le> n" by (simp add: nrows_le)
  moreover have "n \<le> ?r" by (simp add:le_nrows, arith)
  ultimately show "?r = n" by simp
qed

lemma ncols_one_matrix[simp]: "ncols ((one_matrix n) :: ('a::zero_neq_one)matrix) = n" (is "?r = _")
proof -
  have "?r \<le> n" by (simp add: ncols_le)
  moreover have "n \<le> ?r" by (simp add: le_ncols, arith)
  ultimately show "?r = n" by simp
qed

lemma one_matrix_mult_right[simp]:
  fixes A :: "('a::semiring_1) matrix"
  shows "ncols A \<le> n \<Longrightarrow> A * (one_matrix n) = A"
  apply (intro matrix_eqI)
  apply (simp add: times_matrix_def Rep_mult_matrix)
  apply (subst foldseq_almostzero, auto simp: ncols)
  done

lemma one_matrix_mult_left[simp]: 
  fixes A :: "('a::semiring_1) matrix"
  shows "nrows A \<le> n \<Longrightarrow> (one_matrix n) * A = A"
  apply (intro matrix_eqI)
  apply (simp add: times_matrix_def Rep_mult_matrix)
  apply (subst foldseq_almostzero, auto simp: nrows)
  done

lemma transpose_matrix_mult:
  fixes A :: "('a::comm_ring) matrix"
  shows  "transpose_matrix (A*B) = (transpose_matrix B) * (transpose_matrix A)"
  by (simp add: times_matrix_def transpose_mult_matrix mult.commute)

lemma transpose_matrix_add:
  fixes A :: "('a::monoid_add) matrix"
  shows  "transpose_matrix (A+B) = transpose_matrix A + transpose_matrix B"
  by (simp add: plus_matrix_def transpose_combine_matrix)

lemma transpose_matrix_diff:
  fixes A :: "('a::group_add) matrix"
  shows "transpose_matrix (A-B) = transpose_matrix A - transpose_matrix B"
  by (simp add: diff_matrix_def transpose_combine_matrix)

lemma transpose_matrix_minus: 
  fixes A :: "('a::group_add) matrix"
  shows "transpose_matrix (-A) = - transpose_matrix (A::'a matrix)"
  by (simp add: minus_matrix_def transpose_apply_matrix)

definition right_inverse_matrix :: "('a::{ring_1}) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool" where
  "right_inverse_matrix A X == (A * X = one_matrix (max (nrows A) (ncols X))) \<and> nrows X \<le> ncols A" 

definition left_inverse_matrix :: "('a::{ring_1}) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool" where
  "left_inverse_matrix A X == (X * A = one_matrix (max(nrows X) (ncols A))) \<and> ncols X \<le> nrows A" 

definition inverse_matrix :: "('a::{ring_1}) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool" where
  "inverse_matrix A X == (right_inverse_matrix A X) \<and> (left_inverse_matrix A X)"

lemma right_inverse_matrix_dim: "right_inverse_matrix A X \<Longrightarrow> nrows A = ncols X"
  using ncols_mult[of A X] nrows_mult[of A X]
  by (simp add: right_inverse_matrix_def)

lemma left_inverse_matrix_dim: "left_inverse_matrix A Y \<Longrightarrow> ncols A = nrows Y"
  using ncols_mult[of Y A] nrows_mult[of Y A]
  by (simp add: left_inverse_matrix_def)

lemma left_right_inverse_matrix_unique: 
  assumes "left_inverse_matrix A Y" "right_inverse_matrix A X"
  shows "X = Y"
proof -
  have "Y = Y * one_matrix (nrows A)"
    by (metis assms(1) left_inverse_matrix_def one_matrix_mult_right) 
  also have "\<dots> = Y * (A * X)"
    by (metis assms(2) max.idem right_inverse_matrix_def right_inverse_matrix_dim) 
  also have "\<dots> = (Y * A) * X" by (simp add: mult.assoc)
  also have "\<dots> = X"
    using assms left_inverse_matrix_def right_inverse_matrix_def
    by (metis left_inverse_matrix_dim max.idem one_matrix_mult_left)
  ultimately show "X = Y" by (simp)
qed

lemma inverse_matrix_inject: "\<lbrakk> inverse_matrix A X; inverse_matrix A Y \<rbrakk> \<Longrightarrow> X = Y"
  by (auto simp: inverse_matrix_def left_right_inverse_matrix_unique)

lemma one_matrix_inverse: "inverse_matrix (one_matrix n) (one_matrix n)"
  by (simp add: inverse_matrix_def left_inverse_matrix_def right_inverse_matrix_def)

lemma zero_imp_mult_zero: "(a::'a::semiring_0) = 0 | b = 0 \<Longrightarrow> a * b = 0"
  by auto

lemma Rep_matrix_zero_imp_mult_zero:
  "\<forall>j i k. (Rep_matrix A j k = 0) | (Rep_matrix B k i) = 0  \<Longrightarrow> A * B = (0::('a::lattice_ring) matrix)"
  by (simp add: matrix_eqI Rep_matrix_mult foldseq_zero zero_imp_mult_zero)

lemma add_nrows: "nrows (A::('a::monoid_add) matrix) \<le> u \<Longrightarrow> nrows B \<le> u \<Longrightarrow> nrows (A + B) \<le> u"
  by (simp add: nrows_le)

lemma move_matrix_row_mult:
  fixes A :: "('a::semiring_0) matrix"
  shows "move_matrix (A * B) j 0 = (move_matrix A j 0) * B"
proof -
  have "\<And>m. \<not> int m < j \<Longrightarrow> ncols (move_matrix A j 0) \<le> max (ncols A) (nrows B)"
    by (smt (verit, best) max1 nat_int ncols_move_matrix_le)
  then show ?thesis
    apply (intro matrix_eqI)
    apply (auto simp: Rep_matrix_mult foldseq_zero)
    apply (rule_tac foldseq_zerotail[symmetric])
      apply (auto simp: nrows zero_imp_mult_zero max2)
    done
qed

lemma move_matrix_col_mult:
  fixes A :: "('a::semiring_0) matrix"
  shows  "move_matrix (A * B) 0 i = A * (move_matrix B 0 i)"
proof -
  have "\<And>n. \<not> int n < i \<Longrightarrow> nrows (move_matrix B 0 i) \<le> max (ncols A) (nrows B)"
    by (smt (verit, del_insts) max2 nat_int nrows_move_matrix_le)
  then show ?thesis
    apply (intro matrix_eqI)
    apply (auto simp: Rep_matrix_mult foldseq_zero)
    apply (rule_tac foldseq_zerotail[symmetric])
      apply (auto simp: ncols zero_imp_mult_zero max1)
    done
  qed

lemma move_matrix_add: "((move_matrix (A + B) j i)::(('a::monoid_add) matrix)) = (move_matrix A j i) + (move_matrix B j i)" 
  by (simp add: matrix_eqI)

lemma move_matrix_mult: "move_matrix ((A::('a::semiring_0) matrix)*B) j i = (move_matrix A j 0) * (move_matrix B 0 i)"
by (simp add: move_matrix_ortho[of "A*B"] move_matrix_col_mult move_matrix_row_mult)

definition scalar_mult :: "('a::ring) \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" where
  "scalar_mult a m == apply_matrix ((*) a) m"

lemma scalar_mult_zero[simp]: "scalar_mult y 0 = 0" 
  by (simp add: scalar_mult_def)

lemma scalar_mult_add: "scalar_mult y (a+b) = (scalar_mult y a) + (scalar_mult y b)"
  by (simp add: scalar_mult_def apply_matrix_add algebra_simps)

lemma Rep_scalar_mult[simp]: "Rep_matrix (scalar_mult y a) j i = y * (Rep_matrix a j i)" 
  by (simp add: scalar_mult_def)

lemma scalar_mult_singleton[simp]: "scalar_mult y (singleton_matrix j i x) = singleton_matrix j i (y * x)"
  by (simp add: scalar_mult_def)

lemma Rep_minus[simp]: "Rep_matrix (-(A::_::group_add)) x y = - (Rep_matrix A x y)"
  by (simp add: minus_matrix_def)

lemma Rep_abs[simp]: "Rep_matrix \<bar>A::_::lattice_ab_group_add\<bar> x y = \<bar>Rep_matrix A x y\<bar>"
  by (simp add: abs_lattice sup_matrix_def)

end
