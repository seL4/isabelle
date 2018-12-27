(*  Title:      HOL/Analysis/Linear_Algebra.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Elementary linear algebra on Euclidean spaces\<close>

theory Linear_Algebra
imports
  Euclidean_Space
  "HOL-Library.Infinite_Set"
begin

lemma linear_simps:
  assumes "bounded_linear f"
  shows
    "f (a + b) = f a + f b"
    "f (a - b) = f a - f b"
    "f 0 = 0"
    "f (- a) = - f a"
    "f (s *\<^sub>R v) = s *\<^sub>R (f v)"
proof -
  interpret f: bounded_linear f by fact
  show "f (a + b) = f a + f b" by (rule f.add)
  show "f (a - b) = f a - f b" by (rule f.diff)
  show "f 0 = 0" by (rule f.zero)
  show "f (- a) = - f a" by (rule f.neg)
  show "f (s *\<^sub>R v) = s *\<^sub>R (f v)" by (rule f.scale)
qed

lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x \<in> (UNIV::'a::finite set)}"
  using finite finite_image_set by blast


subsection%unimportant \<open>More interesting properties of the norm\<close>

notation inner (infix "\<bullet>" 70)

text\<open>Equality of vectors in terms of @{term "(\<bullet>)"} products.\<close>

lemma linear_componentwise:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes lf: "linear f"
  shows "(f x) \<bullet> j = (\<Sum>i\<in>Basis. (x\<bullet>i) * (f i\<bullet>j))" (is "?lhs = ?rhs")
proof -
  interpret linear f by fact
  have "?rhs = (\<Sum>i\<in>Basis. (x\<bullet>i) *\<^sub>R (f i))\<bullet>j"
    by (simp add: inner_sum_left)
  then show ?thesis
    by (simp add: euclidean_representation sum[symmetric] scale[symmetric])
qed

lemma vector_eq: "x = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y \<and> y \<bullet> y = x \<bullet> x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by simp
next
  assume ?rhs
  then have "x \<bullet> x - x \<bullet> y = 0 \<and> x \<bullet> y - y \<bullet> y = 0"
    by simp
  then have "x \<bullet> (x - y) = 0 \<and> y \<bullet> (x - y) = 0"
    by (simp add: inner_diff inner_commute)
  then have "(x - y) \<bullet> (x - y) = 0"
    by (simp add: field_simps inner_diff inner_commute)
  then show "x = y" by simp
qed

lemma norm_triangle_half_r:
  "norm (y - x1) < e / 2 \<Longrightarrow> norm (y - x2) < e / 2 \<Longrightarrow> norm (x1 - x2) < e"
  using dist_triangle_half_r unfolding dist_norm[symmetric] by auto

lemma norm_triangle_half_l:
  assumes "norm (x - y) < e / 2"
    and "norm (x' - y) < e / 2"
  shows "norm (x - x') < e"
  using dist_triangle_half_l[OF assms[unfolded dist_norm[symmetric]]]
  unfolding dist_norm[symmetric] .

lemma abs_triangle_half_r:
  fixes y :: "'a::linordered_field"
  shows "abs (y - x1) < e / 2 \<Longrightarrow> abs (y - x2) < e / 2 \<Longrightarrow> abs (x1 - x2) < e"
  by linarith

lemma abs_triangle_half_l:
  fixes y :: "'a::linordered_field"
  assumes "abs (x - y) < e / 2"
    and "abs (x' - y) < e / 2"
  shows "abs (x - x') < e"
  using assms by linarith

lemma sum_clauses:
  shows "sum f {} = 0"
    and "finite S \<Longrightarrow> sum f (insert x S) = (if x \<in> S then sum f S else f x + sum f S)"
  by (auto simp add: insert_absorb)

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = z"
proof
  assume "\<forall>x. x \<bullet> y = x \<bullet> z"
  then have "\<forall>x. x \<bullet> (y - z) = 0"
    by (simp add: inner_diff)
  then have "(y - z) \<bullet> (y - z) = 0" ..
  then show "y = z" by simp
qed simp

lemma vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = y"
proof
  assume "\<forall>z. x \<bullet> z = y \<bullet> z"
  then have "\<forall>z. (x - y) \<bullet> z = 0"
    by (simp add: inner_diff)
  then have "(x - y) \<bullet> (x - y) = 0" ..
  then show "x = y" by simp
qed simp


subsection \<open>Orthogonality\<close>

definition%important (in real_inner) "orthogonal x y \<longleftrightarrow> x \<bullet> y = 0"

context real_inner
begin

lemma orthogonal_self: "orthogonal x x \<longleftrightarrow> x = 0"
  by (simp add: orthogonal_def)

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x \<Longrightarrow> orthogonal a (c *\<^sub>R x)"
  "orthogonal a x \<Longrightarrow> orthogonal a (- x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a \<Longrightarrow> orthogonal (c *\<^sub>R x) a"
  "orthogonal x a \<Longrightarrow> orthogonal (- x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x - y) a"
  unfolding orthogonal_def inner_add inner_diff by auto

end

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  by (simp add: orthogonal_def inner_commute)

lemma orthogonal_scaleR [simp]: "c \<noteq> 0 \<Longrightarrow> orthogonal (c *\<^sub>R x) = orthogonal x"
  by (rule ext) (simp add: orthogonal_def)

lemma pairwise_ortho_scaleR:
    "pairwise (\<lambda>i j. orthogonal (f i) (g j)) B
    \<Longrightarrow> pairwise (\<lambda>i j. orthogonal (a i *\<^sub>R f i) (a j *\<^sub>R g j)) B"
  by (auto simp: pairwise_def orthogonal_clauses)

lemma orthogonal_rvsum:
    "\<lbrakk>finite s; \<And>y. y \<in> s \<Longrightarrow> orthogonal x (f y)\<rbrakk> \<Longrightarrow> orthogonal x (sum f s)"
  by (induction s rule: finite_induct) (auto simp: orthogonal_clauses)

lemma orthogonal_lvsum:
    "\<lbrakk>finite s; \<And>x. x \<in> s \<Longrightarrow> orthogonal (f x) y\<rbrakk> \<Longrightarrow> orthogonal (sum f s) y"
  by (induction s rule: finite_induct) (auto simp: orthogonal_clauses)

lemma norm_add_Pythagorean:
  assumes "orthogonal a b"
    shows "norm(a + b) ^ 2 = norm a ^ 2 + norm b ^ 2"
proof -
  from assms have "(a - (0 - b)) \<bullet> (a - (0 - b)) = a \<bullet> a - (0 - b \<bullet> b)"
    by (simp add: algebra_simps orthogonal_def inner_commute)
  then show ?thesis
    by (simp add: power2_norm_eq_inner)
qed

lemma norm_sum_Pythagorean:
  assumes "finite I" "pairwise (\<lambda>i j. orthogonal (f i) (f j)) I"
    shows "(norm (sum f I))\<^sup>2 = (\<Sum>i\<in>I. (norm (f i))\<^sup>2)"
using assms
proof (induction I rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert x I)
  then have "orthogonal (f x) (sum f I)"
    by (metis pairwise_insert orthogonal_rvsum)
  with insert show ?case
    by (simp add: pairwise_insert norm_add_Pythagorean)
qed


subsection \<open>Bilinear functions\<close>

definition%important "bilinear f \<longleftrightarrow> (\<forall>x. linear (\<lambda>y. f x y)) \<and> (\<forall>y. linear (\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h \<Longrightarrow> h (x + y) z = h x z + h y z"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_radd: "bilinear h \<Longrightarrow> h x (y + z) = h x y + h x z"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_lmul: "bilinear h \<Longrightarrow> h (c *\<^sub>R x) y = c *\<^sub>R h x y"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_rmul: "bilinear h \<Longrightarrow> h x (c *\<^sub>R y) = c *\<^sub>R h x y"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_lneg: "bilinear h \<Longrightarrow> h (- x) y = - h x y"
  by (drule bilinear_lmul [of _ "- 1"]) simp

lemma bilinear_rneg: "bilinear h \<Longrightarrow> h x (- y) = - h x y"
  by (drule bilinear_rmul [of _ _ "- 1"]) simp

lemma (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  using add_left_imp_eq[of x y 0] by auto

lemma bilinear_lzero:
  assumes "bilinear h"
  shows "h 0 x = 0"
  using bilinear_ladd [OF assms, of 0 0 x] by (simp add: eq_add_iff field_simps)

lemma bilinear_rzero:
  assumes "bilinear h"
  shows "h x 0 = 0"
  using bilinear_radd [OF assms, of x 0 0 ] by (simp add: eq_add_iff field_simps)

lemma bilinear_lsub: "bilinear h \<Longrightarrow> h (x - y) z = h x z - h y z"
  using bilinear_ladd [of h x "- y"] by (simp add: bilinear_lneg)

lemma bilinear_rsub: "bilinear h \<Longrightarrow> h z (x - y) = h z x - h z y"
  using bilinear_radd [of h _ x "- y"] by (simp add: bilinear_rneg)

lemma bilinear_sum:
  assumes "bilinear h"
  shows "h (sum f S) (sum g T) = sum (\<lambda>(i,j). h (f i) (g j)) (S \<times> T) "
proof -
  interpret l: linear "\<lambda>x. h x y" for y using assms by (simp add: bilinear_def)
  interpret r: linear "\<lambda>y. h x y" for x using assms by (simp add: bilinear_def)
  have "h (sum f S) (sum g T) = sum (\<lambda>x. h (f x) (sum g T)) S"
    by (simp add: l.sum)
  also have "\<dots> = sum (\<lambda>x. sum (\<lambda>y. h (f x) (g y)) T) S"
    by (rule sum.cong) (simp_all add: r.sum)
  finally show ?thesis
    unfolding sum.cartesian_product .
qed


subsection \<open>Adjoints\<close>

definition%important "adjoint f = (SOME f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y)"

lemma adjoint_unique:
  assumes "\<forall>x y. inner (f x) y = inner x (g y)"
  shows "adjoint f = g"
  unfolding adjoint_def
proof (rule some_equality)
  show "\<forall>x y. inner (f x) y = inner x (g y)"
    by (rule assms)
next
  fix h
  assume "\<forall>x y. inner (f x) y = inner x (h y)"
  then have "\<forall>x y. inner x (g y) = inner x (h y)"
    using assms by simp
  then have "\<forall>x y. inner x (g y - h y) = 0"
    by (simp add: inner_diff_right)
  then have "\<forall>y. inner (g y - h y) (g y - h y) = 0"
    by simp
  then have "\<forall>y. h y = g y"
    by simp
  then show "h = g" by (simp add: ext)
qed

text \<open>TODO: The following lemmas about adjoints should hold for any
  Hilbert space (i.e. complete inner product space).
  (see \<^url>\<open>https://en.wikipedia.org/wiki/Hermitian_adjoint\<close>)
\<close>

lemma adjoint_works:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
proof -
  interpret linear f by fact
  have "\<forall>y. \<exists>w. \<forall>x. f x \<bullet> y = x \<bullet> w"
  proof (intro allI exI)
    fix y :: "'m" and x
    let ?w = "(\<Sum>i\<in>Basis. (f i \<bullet> y) *\<^sub>R i) :: 'n"
    have "f x \<bullet> y = f (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i) \<bullet> y"
      by (simp add: euclidean_representation)
    also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) \<bullet> y"
      by (simp add: sum scale)
    finally show "f x \<bullet> y = x \<bullet> ?w"
      by (simp add: inner_sum_left inner_sum_right mult.commute)
  qed
  then show ?thesis
    unfolding adjoint_def choice_iff
    by (intro someI2_ex[where Q="\<lambda>f'. x \<bullet> f' y = f x \<bullet> y"]) auto
qed

lemma adjoint_clauses:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
    and "adjoint f y \<bullet> x = y \<bullet> f x"
  by (simp_all add: adjoint_works[OF lf] inner_commute)

lemma adjoint_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "linear (adjoint f)"
  by (simp add: lf linear_iff euclidean_eq_iff[where 'a='n] euclidean_eq_iff[where 'a='m]
    adjoint_clauses[OF lf] inner_distrib)

lemma adjoint_adjoint:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "adjoint (adjoint f) = f"
  by (rule adjoint_unique, simp add: adjoint_clauses [OF lf])


subsection \<open>Archimedean properties and useful consequences\<close>

text\<open>Bernoulli's inequality\<close>
proposition Bernoulli_inequality:
  fixes x :: real
  assumes "-1 \<le> x"
    shows "1 + n * x \<le> (1 + x) ^ n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "1 + Suc n * x \<le> 1 + (Suc n)*x + n * x^2"
    by (simp add: algebra_simps)
  also have "... = (1 + x) * (1 + n*x)"
    by (auto simp: power2_eq_square algebra_simps  of_nat_Suc)
  also have "... \<le> (1 + x) ^ Suc n"
    using Suc.hyps assms mult_left_mono by fastforce
  finally show ?case .
qed

corollary Bernoulli_inequality_even:
  fixes x :: real
  assumes "even n"
    shows "1 + n * x \<le> (1 + x) ^ n"
proof (cases "-1 \<le> x \<or> n=0")
  case True
  then show ?thesis
    by (auto simp: Bernoulli_inequality)
next
  case False
  then have "real n \<ge> 1"
    by simp
  with False have "n * x \<le> -1"
    by (metis linear minus_zero mult.commute mult.left_neutral mult_left_mono_neg neg_le_iff_le order_trans zero_le_one)
  then have "1 + n * x \<le> 0"
    by auto
  also have "... \<le> (1 + x) ^ n"
    using assms
    using zero_le_even_power by blast
  finally show ?thesis .
qed

corollary real_arch_pow:
  fixes x :: real
  assumes x: "1 < x"
  shows "\<exists>n. y < x^n"
proof -
  from x have x0: "x - 1 > 0"
    by arith
  from reals_Archimedean3[OF x0, rule_format, of y]
  obtain n :: nat where n: "y < real n * (x - 1)" by metis
  from x0 have x00: "x- 1 \<ge> -1" by arith
  from Bernoulli_inequality[OF x00, of n] n
  have "y < x^n" by auto
  then show ?thesis by metis
qed

corollary real_arch_pow_inv:
  fixes x y :: real
  assumes y: "y > 0"
    and x1: "x < 1"
  shows "\<exists>n. x^n < y"
proof (cases "x > 0")
  case True
  with x1 have ix: "1 < 1/x" by (simp add: field_simps)
  from real_arch_pow[OF ix, of "1/y"]
  obtain n where n: "1/y < (1/x)^n" by blast
  then show ?thesis using y \<open>x > 0\<close>
    by (auto simp add: field_simps)
next
  case False
  with y x1 show ?thesis
    by (metis less_le_trans not_less power_one_right)
qed

lemma forall_pos_mono:
  "(\<And>d e::real. d < e \<Longrightarrow> P d \<Longrightarrow> P e) \<Longrightarrow>
    (\<And>n::nat. n \<noteq> 0 \<Longrightarrow> P (inverse (real n))) \<Longrightarrow> (\<And>e. 0 < e \<Longrightarrow> P e)"
  by (metis real_arch_inverse)

lemma forall_pos_mono_1:
  "(\<And>d e::real. d < e \<Longrightarrow> P d \<Longrightarrow> P e) \<Longrightarrow>
    (\<And>n. P (inverse (real (Suc n)))) \<Longrightarrow> 0 < e \<Longrightarrow> P e"
  apply (rule forall_pos_mono)
  apply auto
  apply (metis Suc_pred of_nat_Suc)
  done


subsection%unimportant \<open>Euclidean Spaces as Typeclass\<close>

lemma independent_Basis: "independent Basis"
  by (rule independent_Basis)

lemma span_Basis [simp]: "span Basis = UNIV"
  by (rule span_Basis)

lemma in_span_Basis: "x \<in> span Basis"
  unfolding span_Basis ..


subsection%unimportant \<open>Linearity and Bilinearity continued\<close>

lemma linear_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
proof
  interpret linear f by fact
  let ?B = "\<Sum>b\<in>Basis. norm (f b)"
  show "\<forall>x. norm (f x) \<le> ?B * norm x"
  proof
    fix x :: 'a
    let ?g = "\<lambda>b. (x \<bullet> b) *\<^sub>R f b"
    have "norm (f x) = norm (f (\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b))"
      unfolding euclidean_representation ..
    also have "\<dots> = norm (sum ?g Basis)"
      by (simp add: sum scale)
    finally have th0: "norm (f x) = norm (sum ?g Basis)" .
    have th: "norm (?g i) \<le> norm (f i) * norm x" if "i \<in> Basis" for i
    proof -
      from Basis_le_norm[OF that, of x]
      show "norm (?g i) \<le> norm (f i) * norm x"
        unfolding norm_scaleR  by (metis mult.commute mult_left_mono norm_ge_zero)
    qed
    from sum_norm_le[of _ ?g, OF th]
    show "norm (f x) \<le> ?B * norm x"
      unfolding th0 sum_distrib_right by metis
  qed
qed

lemma linear_conv_bounded_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<longleftrightarrow> bounded_linear f"
proof
  assume "linear f"
  then interpret f: linear f .
  show "bounded_linear f"
  proof
    have "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
      using \<open>linear f\<close> by (rule linear_bounded)
    then show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (simp add: mult.commute)
  qed
next
  assume "bounded_linear f"
  then interpret f: bounded_linear f .
  show "linear f" ..
qed

lemmas linear_linear = linear_conv_bounded_linear[symmetric]

lemma linear_bounded_pos:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
 obtains B where "B > 0" "\<And>x. norm (f x) \<le> B * norm x"
proof -
  have "\<exists>B > 0. \<forall>x. norm (f x) \<le> norm x * B"
    using lf unfolding linear_conv_bounded_linear
    by (rule bounded_linear.pos_bounded)
  with that show ?thesis
    by (auto simp: mult.commute)
qed

lemma linear_invertible_bounded_below_pos:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "linear g" "g \<circ> f = id"
  obtains B where "B > 0" "\<And>x. B * norm x \<le> norm(f x)"
proof -
  obtain B where "B > 0" and B: "\<And>x. norm (g x) \<le> B * norm x"
    using linear_bounded_pos [OF \<open>linear g\<close>] by blast
  show thesis
  proof
    show "0 < 1/B"
      by (simp add: \<open>B > 0\<close>)
    show "1/B * norm x \<le> norm (f x)" for x
    proof -
      have "1/B * norm x = 1/B * norm (g (f x))"
        using assms by (simp add: pointfree_idE)
      also have "\<dots> \<le> norm (f x)"
        using B [of "f x"] by (simp add: \<open>B > 0\<close> mult.commute pos_divide_le_eq)
      finally show ?thesis .
    qed
  qed
qed

lemma linear_inj_bounded_below_pos:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  obtains B where "B > 0" "\<And>x. B * norm x \<le> norm(f x)"
  using linear_injective_left_inverse [OF assms]
    linear_invertible_bounded_below_pos assms by blast

lemma bounded_linearI':
  fixes f ::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "bounded_linear f"
  using assms linearI linear_conv_bounded_linear by blast

lemma bilinear_bounded:
  fixes h :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'k::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof (clarify intro!: exI[of _ "\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. norm (h i j)"])
  fix x :: 'm
  fix y :: 'n
  have "norm (h x y) = norm (h (sum (\<lambda>i. (x \<bullet> i) *\<^sub>R i) Basis) (sum (\<lambda>i. (y \<bullet> i) *\<^sub>R i) Basis))"
    by (simp add: euclidean_representation)
  also have "\<dots> = norm (sum (\<lambda> (i,j). h ((x \<bullet> i) *\<^sub>R i) ((y \<bullet> j) *\<^sub>R j)) (Basis \<times> Basis))"
    unfolding bilinear_sum[OF bh] ..
  finally have th: "norm (h x y) = \<dots>" .
  have "\<And>i j. \<lbrakk>i \<in> Basis; j \<in> Basis\<rbrakk>
           \<Longrightarrow> \<bar>x \<bullet> i\<bar> * (\<bar>y \<bullet> j\<bar> * norm (h i j)) \<le> norm x * (norm y * norm (h i j))"
    by (auto simp add: zero_le_mult_iff Basis_le_norm mult_mono)
  then show "norm (h x y) \<le> (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. norm (h i j)) * norm x * norm y"
    unfolding sum_distrib_right th sum.cartesian_product
    by (clarsimp simp add: bilinear_rmul[OF bh] bilinear_lmul[OF bh]
      field_simps simp del: scaleR_scaleR intro!: sum_norm_le)
qed

lemma bilinear_conv_bounded_bilinear:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  shows "bilinear h \<longleftrightarrow> bounded_bilinear h"
proof
  assume "bilinear h"
  show "bounded_bilinear h"
  proof
    fix x y z
    show "h (x + y) z = h x z + h y z"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff by simp
  next
    fix x y z
    show "h x (y + z) = h x y + h x z"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff by simp
  next
    show "h (scaleR r x) y = scaleR r (h x y)" "h x (scaleR r y) = scaleR r (h x y)" for r x y
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff
      by simp_all
  next
    have "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
      using \<open>bilinear h\<close> by (rule bilinear_bounded)
    then show "\<exists>K. \<forall>x y. norm (h x y) \<le> norm x * norm y * K"
      by (simp add: ac_simps)
  qed
next
  assume "bounded_bilinear h"
  then interpret h: bounded_bilinear h .
  show "bilinear h"
    unfolding bilinear_def linear_conv_bounded_linear
    using h.bounded_linear_left h.bounded_linear_right by simp
qed

lemma bilinear_bounded_pos:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof -
  have "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> norm x * norm y * B"
    using bh [unfolded bilinear_conv_bounded_bilinear]
    by (rule bounded_bilinear.pos_bounded)
  then show ?thesis
    by (simp only: ac_simps)
qed

lemma bounded_linear_imp_has_derivative: "bounded_linear f \<Longrightarrow> (f has_derivative f) net"
  by (auto simp add: has_derivative_def linear_diff linear_linear linear_def
      dest: bounded_linear.linear)

lemma linear_imp_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> (f has_derivative f) net"
  by (simp add: bounded_linear_imp_has_derivative linear_conv_bounded_linear)

lemma bounded_linear_imp_differentiable: "bounded_linear f \<Longrightarrow> f differentiable net"
  using bounded_linear_imp_has_derivative differentiable_def by blast

lemma linear_imp_differentiable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable net"
  by (metis linear_imp_has_derivative differentiable_def)


subsection%unimportant \<open>We continue\<close>

lemma independent_bound:
  fixes S :: "'a::euclidean_space set"
  shows "independent S \<Longrightarrow> finite S \<and> card S \<le> DIM('a)"
  by (metis dim_subset_UNIV finiteI_independent dim_span_eq_card_independent)

lemmas independent_imp_finite = finiteI_independent

corollary
  fixes S :: "'a::euclidean_space set"
  assumes "independent S"
  shows independent_card_le:"card S \<le> DIM('a)"
  using assms independent_bound by auto

lemma dependent_biggerset:
  fixes S :: "'a::euclidean_space set"
  shows "(finite S \<Longrightarrow> card S > DIM('a)) \<Longrightarrow> dependent S"
  by (metis independent_bound not_less)

text \<open>Picking an orthogonal replacement for a spanning set.\<close>

lemma vector_sub_project_orthogonal:
  fixes b x :: "'a::euclidean_space"
  shows "b \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *\<^sub>R b) = 0"
  unfolding inner_simps by auto

lemma pairwise_orthogonal_insert:
  assumes "pairwise orthogonal S"
    and "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
  shows "pairwise orthogonal (insert x S)"
  using assms unfolding pairwise_def
  by (auto simp add: orthogonal_commute)

lemma basis_orthogonal:
  fixes B :: "'a::real_inner set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
  using fB
proof (induct rule: finite_induct)
  case empty
  then show ?case
    apply (rule exI[where x="{}"])
    apply (auto simp add: pairwise_def)
    done
next
  case (insert a B)
  note fB = \<open>finite B\<close> and aB = \<open>a \<notin> B\<close>
  from \<open>\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C\<close>
  obtain C where C: "finite C" "card C \<le> card B"
    "span C = span B" "pairwise orthogonal C" by blast
  let ?a = "a - sum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C"
    by simp
  from fB aB C(1,2) have cC: "card ?C \<le> card (insert a B)"
    by (simp add: card_insert_if)
  {
    fix x k
    have th0: "\<And>(a::'a) b c. a - (b - c) = c + (a - b)"
      by (simp add: field_simps)
    have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x)) \<in> span C \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
      apply (simp only: scaleR_right_diff_distrib th0)
      apply (rule span_add_eq)
      apply (rule span_scale)
      apply (rule span_sum)
      apply (rule span_scale)
      apply (rule span_base)
      apply assumption
      done
  }
  then have SC: "span ?C = span (insert a B)"
    unfolding set_eq_iff span_breakdown_eq C(3)[symmetric] by auto
  {
    fix y
    assume yC: "y \<in> C"
    then have Cy: "C = insert y (C - {y})"
      by blast
    have fth: "finite (C - {y})"
      using C by simp
    have "orthogonal ?a y"
      unfolding orthogonal_def
      unfolding inner_diff inner_sum_left right_minus_eq
      unfolding sum.remove [OF \<open>finite C\<close> \<open>y \<in> C\<close>]
      apply (clarsimp simp add: inner_commute[of y a])
      apply (rule sum.neutral)
      apply clarsimp
      apply (rule C(4)[unfolded pairwise_def orthogonal_def, rule_format])
      using \<open>y \<in> C\<close> by auto
  }
  with \<open>pairwise orthogonal C\<close> have CPO: "pairwise orthogonal ?C"
    by (rule pairwise_orthogonal_insert)
  from fC cC SC CPO have "?P (insert a B) ?C"
    by blast
  then show ?case by blast
qed

lemma orthogonal_basis_exists:
  fixes V :: "('a::euclidean_space) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and>
  (card B = dim V) \<and> pairwise orthogonal B"
proof -
  from basis_exists[of V] obtain B where
    B: "B \<subseteq> V" "independent B" "V \<subseteq> span B" "card B = dim V"
    by force
  from B have fB: "finite B" "card B = dim V"
    using independent_bound by auto
  from basis_orthogonal[OF fB(1)] obtain C where
    C: "finite C" "card C \<le> card B" "span C = span B" "pairwise orthogonal C"
    by blast
  from C B have CSV: "C \<subseteq> span V"
    by (metis span_superset span_mono subset_trans)
  from span_mono[OF B(3)] C have SVC: "span V \<subseteq> span C"
    by (simp add: span_span)
  from card_le_dim_spanning[OF CSV SVC C(1)] C(2,3) fB
  have iC: "independent C"
    by (simp add: dim_span)
  from C fB have "card C \<le> dim V"
    by simp
  moreover have "dim V \<le> card C"
    using span_card_ge_dim[OF CSV SVC C(1)]
    by simp
  ultimately have CdV: "card C = dim V"
    using C(1) by simp
  from C B CSV CdV iC show ?thesis
    by auto
qed

text \<open>Low-dimensional subset is in a hyperplane (weak orthogonal complement).\<close>

lemma span_not_univ_orthogonal:
  fixes S :: "'a::euclidean_space set"
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
proof -
  from sU obtain a where a: "a \<notin> span S"
    by blast
  from orthogonal_basis_exists obtain B where
    B: "independent B" "B \<subseteq> span S" "S \<subseteq> span B"
    "card B = dim S" "pairwise orthogonal B"
    by blast
  from B have fB: "finite B" "card B = dim S"
    using independent_bound by auto
  from span_mono[OF B(2)] span_mono[OF B(3)]
  have sSB: "span S = span B"
    by (simp add: span_span)
  let ?a = "a - sum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B"
  have "sum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B \<in> span S"
    unfolding sSB
    apply (rule span_sum)
    apply (rule span_scale)
    apply (rule span_base)
    apply assumption
    done
  with a have a0:"?a  \<noteq> 0"
    by auto
  have "?a \<bullet> x = 0" if "x\<in>span B" for x
  proof (rule span_induct [OF that])
    show "subspace {x. ?a \<bullet> x = 0}"
      by (auto simp add: subspace_def inner_add)
  next
    {
      fix x
      assume x: "x \<in> B"
      from x have B': "B = insert x (B - {x})"
        by blast
      have fth: "finite (B - {x})"
        using fB by simp
      have "?a \<bullet> x = 0"
        apply (subst B')
        using fB fth
        unfolding sum_clauses(2)[OF fth]
        apply simp unfolding inner_simps
        apply (clarsimp simp add: inner_add inner_sum_left)
        apply (rule sum.neutral, rule ballI)
        apply (simp only: inner_commute)
        apply (auto simp add: x field_simps
          intro: B(5)[unfolded pairwise_def orthogonal_def, rule_format])
        done
    }
    then show "?a \<bullet> x = 0" if "x \<in> B" for x
      using that by blast
    qed
  with a0 show ?thesis
    unfolding sSB by (auto intro: exI[where x="?a"])
qed

lemma span_not_univ_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes SU: "span S \<noteq> UNIV"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using span_not_univ_orthogonal[OF SU] by auto

lemma lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes d: "dim S < DIM('a)"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
proof -
  {
    assume "span S = UNIV"
    then have "dim (span S) = dim (UNIV :: ('a) set)"
      by simp
    then have "dim S = DIM('a)"
      by (metis Euclidean_Space.dim_UNIV dim_span)
    with d have False by arith
  }
  then have th: "span S \<noteq> UNIV"
    by blast
  from span_not_univ_subset_hyperplane[OF th] show ?thesis .
qed

lemma linear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> _"
  assumes lf: "linear f"
    and lg: "linear g"
    and fg: "\<And>b. b \<in> Basis \<Longrightarrow> f b = g b"
  shows "f = g"
  using linear_eq_on_span[OF lf lg, of Basis] fg
  by auto


text \<open>Similar results for bilinear functions.\<close>

lemma bilinear_eq:
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and SB: "S \<subseteq> span B"
    and TC: "T \<subseteq> span C"
    and "x\<in>S" "y\<in>T"
    and fg: "\<And>x y. \<lbrakk>x \<in> B; y\<in> C\<rbrakk> \<Longrightarrow> f x y = g x y"
  shows "f x y = g x y"
proof -
  let ?P = "{x. \<forall>y\<in> span C. f x y = g x y}"
  from bf bg have sp: "subspace ?P"
    unfolding bilinear_def linear_iff subspace_def bf bg
    by (auto simp add: span_zero bilinear_lzero[OF bf] bilinear_lzero[OF bg]
        span_add Ball_def
      intro: bilinear_ladd[OF bf])
  have sfg: "\<And>x. x \<in> B \<Longrightarrow> subspace {a. f x a = g x a}"
    apply (auto simp add: subspace_def)
    using bf bg unfolding bilinear_def linear_iff
      apply (auto simp add: span_zero bilinear_rzero[OF bf] bilinear_rzero[OF bg]
        span_add Ball_def
      intro: bilinear_ladd[OF bf])
    done
  have "\<forall>y\<in> span C. f x y = g x y" if "x \<in> span B" for x
    apply (rule span_induct [OF that sp])
    using fg sfg span_induct by blast
  then show ?thesis
    using SB TC assms by auto
qed

lemma bilinear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> _"
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and fg: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> f i j = g i j"
  shows "f = g"
  using bilinear_eq[OF bf bg equalityD2[OF span_Basis] equalityD2[OF span_Basis]] fg by blast

subsection \<open>Infinity norm\<close>

definition%important "infnorm (x::'a::euclidean_space) = Sup {\<bar>x \<bullet> b\<bar> |b. b \<in> Basis}"

lemma infnorm_set_image:
  fixes x :: "'a::euclidean_space"
  shows "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} = (\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  by blast

lemma infnorm_Max:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis)"
  by (simp add: infnorm_def infnorm_set_image cSup_eq_Max)

lemma infnorm_set_lemma:
  fixes x :: "'a::euclidean_space"
  shows "finite {\<bar>x \<bullet> i\<bar> |i. i \<in> Basis}"
    and "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} \<noteq> {}"
  unfolding infnorm_set_image
  by auto

lemma infnorm_pos_le:
  fixes x :: "'a::euclidean_space"
  shows "0 \<le> infnorm x"
  by (simp add: infnorm_Max Max_ge_iff ex_in_conv)

lemma infnorm_triangle:
  fixes x :: "'a::euclidean_space"
  shows "infnorm (x + y) \<le> infnorm x + infnorm y"
proof -
  have *: "\<And>a b c d :: real. \<bar>a\<bar> \<le> c \<Longrightarrow> \<bar>b\<bar> \<le> d \<Longrightarrow> \<bar>a + b\<bar> \<le> c + d"
    by simp
  show ?thesis
    by (auto simp: infnorm_Max inner_add_left intro!: *)
qed

lemma infnorm_eq_0:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = 0 \<longleftrightarrow> x = 0"
proof -
  have "infnorm x \<le> 0 \<longleftrightarrow> x = 0"
    unfolding infnorm_Max by (simp add: euclidean_all_zero_iff)
  then show ?thesis
    using infnorm_pos_le[of x] by simp
qed

lemma infnorm_0: "infnorm 0 = 0"
  by (simp add: infnorm_eq_0)

lemma infnorm_neg: "infnorm (- x) = infnorm x"
  unfolding infnorm_def by simp

lemma infnorm_sub: "infnorm (x - y) = infnorm (y - x)"
  by (metis infnorm_neg minus_diff_eq)

lemma absdiff_infnorm: "\<bar>infnorm x - infnorm y\<bar> \<le> infnorm (x - y)"
proof -
  have *: "\<And>(nx::real) n ny. nx \<le> n + ny \<Longrightarrow> ny \<le> n + nx \<Longrightarrow> \<bar>nx - ny\<bar> \<le> n"
    by arith
  show ?thesis
  proof (rule *)
    from infnorm_triangle[of "x - y" " y"] infnorm_triangle[of "x - y" "-x"]
    show "infnorm x \<le> infnorm (x - y) + infnorm y" "infnorm y \<le> infnorm (x - y) + infnorm x"
      by (simp_all add: field_simps infnorm_neg)
  qed
qed

lemma real_abs_infnorm: "\<bar>infnorm x\<bar> = infnorm x"
  using infnorm_pos_le[of x] by arith

lemma Basis_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "b \<in> Basis \<Longrightarrow> \<bar>x \<bullet> b\<bar> \<le> infnorm x"
  by (simp add: infnorm_Max)

lemma infnorm_mul: "infnorm (a *\<^sub>R x) = \<bar>a\<bar> * infnorm x"
  unfolding infnorm_Max
proof (safe intro!: Max_eqI)
  let ?B = "(\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  { fix b :: 'a
    assume "b \<in> Basis"
    then show "\<bar>a *\<^sub>R x \<bullet> b\<bar> \<le> \<bar>a\<bar> * Max ?B"
      by (simp add: abs_mult mult_left_mono)
  next
    from Max_in[of ?B] obtain b where "b \<in> Basis" "Max ?B = \<bar>x \<bullet> b\<bar>"
      by (auto simp del: Max_in)
    then show "\<bar>a\<bar> * Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis) \<in> (\<lambda>i. \<bar>a *\<^sub>R x \<bullet> i\<bar>) ` Basis"
      by (intro image_eqI[where x=b]) (auto simp: abs_mult)
  }
qed simp

lemma infnorm_mul_lemma: "infnorm (a *\<^sub>R x) \<le> \<bar>a\<bar> * infnorm x"
  unfolding infnorm_mul ..

lemma infnorm_pos_lt: "infnorm x > 0 \<longleftrightarrow> x \<noteq> 0"
  using infnorm_pos_le[of x] infnorm_eq_0[of x] by arith

text \<open>Prove that it differs only up to a bound from Euclidean norm.\<close>

lemma infnorm_le_norm: "infnorm x \<le> norm x"
  by (simp add: Basis_le_norm infnorm_Max)

lemma norm_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "norm x \<le> sqrt DIM('a) * infnorm x"
  unfolding norm_eq_sqrt_inner id_def 
proof (rule real_le_lsqrt[OF inner_ge_zero])
  show "sqrt DIM('a) * infnorm x \<ge> 0"
    by (simp add: zero_le_mult_iff infnorm_pos_le)
  have "x \<bullet> x \<le> (\<Sum>b\<in>Basis. x \<bullet> b * (x \<bullet> b))"
    by (metis euclidean_inner order_refl)
  also have "... \<le> DIM('a) * \<bar>infnorm x\<bar>\<^sup>2"
    by (rule sum_bounded_above) (metis Basis_le_infnorm abs_le_square_iff power2_eq_square real_abs_infnorm)
  also have "... \<le> (sqrt DIM('a) * infnorm x)\<^sup>2"
    by (simp add: power_mult_distrib)
  finally show "x \<bullet> x \<le> (sqrt DIM('a) * infnorm x)\<^sup>2" .
qed

lemma tendsto_infnorm [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F"
  shows "((\<lambda>x. infnorm (f x)) \<longlongrightarrow> infnorm a) F"
proof (rule tendsto_compose [OF LIM_I assms])
  fix r :: real
  assume "r > 0"
  then show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (infnorm x - infnorm a) < r"
    by (metis real_norm_def le_less_trans absdiff_infnorm infnorm_le_norm)
qed

text \<open>Equality in Cauchy-Schwarz and triangle inequalities.\<close>

lemma norm_cauchy_schwarz_eq: "x \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "x=0")
  case True
  then show ?thesis 
    by auto
next
  case False
  from inner_eq_zero_iff[of "norm y *\<^sub>R x - norm x *\<^sub>R y"]
  have "?rhs \<longleftrightarrow>
      (norm y * (norm y * norm x * norm x - norm x * (x \<bullet> y)) -
        norm x * (norm y * (y \<bullet> x) - norm x * norm y * norm y) =  0)"
    using False unfolding inner_simps
    by (auto simp add: power2_norm_eq_inner[symmetric] power2_eq_square inner_commute field_simps)
  also have "\<dots> \<longleftrightarrow> (2 * norm x * norm y * (norm x * norm y - x \<bullet> y) = 0)" 
    using False  by (simp add: field_simps inner_commute)
  also have "\<dots> \<longleftrightarrow> ?lhs" 
    using False by auto
  finally show ?thesis by metis
qed

lemma norm_cauchy_schwarz_abs_eq:
  "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow>
    norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm x *\<^sub>R y = - norm y *\<^sub>R x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have th: "\<And>(x::real) a. a \<ge> 0 \<Longrightarrow> \<bar>x\<bar> = a \<longleftrightarrow> x = a \<or> x = - a"
    by arith
  have "?rhs \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm (- x) *\<^sub>R y = norm y *\<^sub>R (- x)"
    by simp
  also have "\<dots> \<longleftrightarrow> (x \<bullet> y = norm x * norm y \<or> (- x) \<bullet> y = norm x * norm y)"
    unfolding norm_cauchy_schwarz_eq[symmetric]
    unfolding norm_minus_cancel norm_scaleR ..
  also have "\<dots> \<longleftrightarrow> ?lhs"
    unfolding th[OF mult_nonneg_nonneg, OF norm_ge_zero[of x] norm_ge_zero[of y]] inner_simps
    by auto
  finally show ?thesis ..
qed

lemma norm_triangle_eq:
  fixes x y :: "'a::real_inner"
  shows "norm (x + y) = norm x + norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
proof (cases "x = 0 \<or> y = 0")
  case True
  then show ?thesis 
    by force
next
  case False
  then have n: "norm x > 0" "norm y > 0"
    by auto
  have "norm (x + y) = norm x + norm y \<longleftrightarrow> (norm (x + y))\<^sup>2 = (norm x + norm y)\<^sup>2"
    by simp
  also have "\<dots> \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
    unfolding norm_cauchy_schwarz_eq[symmetric]
    unfolding power2_norm_eq_inner inner_simps
    by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square inner_commute field_simps)
  finally show ?thesis .
qed


subsection \<open>Collinearity\<close>

definition%important collinear :: "'a::real_vector set \<Rightarrow> bool"
  where "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u)"

lemma collinear_alt:
     "collinear S \<longleftrightarrow> (\<exists>u v. \<forall>x \<in> S. \<exists>c. x = u + c *\<^sub>R v)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding collinear_def by (metis Groups.add_ac(2) diff_add_cancel)
next
  assume ?rhs
  then obtain u v where *: "\<And>x. x \<in> S \<Longrightarrow> \<exists>c. x = u + c *\<^sub>R v"
    by (auto simp: )
  have "\<exists>c. x - y = c *\<^sub>R v" if "x \<in> S" "y \<in> S" for x y
        by (metis *[OF \<open>x \<in> S\<close>] *[OF \<open>y \<in> S\<close>] scaleR_left.diff add_diff_cancel_left)
  then show ?lhs
    using collinear_def by blast
qed

lemma collinear:
  fixes S :: "'a::{perfect_space,real_vector} set"
  shows "collinear S \<longleftrightarrow> (\<exists>u. u \<noteq> 0 \<and> (\<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u))"
proof -
  have "\<exists>v. v \<noteq> 0 \<and> (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R v)"
    if "\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R u" "u=0" for u
  proof -
    have "\<forall>x\<in>S. \<forall>y\<in>S. x = y"
      using that by auto
    moreover
    obtain v::'a where "v \<noteq> 0"
      using UNIV_not_singleton [of 0] by auto
    ultimately have "\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R v"
      by auto
    then show ?thesis
      using \<open>v \<noteq> 0\<close> by blast
  qed
  then show ?thesis
    apply (clarsimp simp: collinear_def)
    by (metis scaleR_zero_right vector_fraction_eq_iff)
qed

lemma collinear_subset: "\<lbrakk>collinear T; S \<subseteq> T\<rbrakk> \<Longrightarrow> collinear S"
  by (meson collinear_def subsetCE)

lemma collinear_empty [iff]: "collinear {}"
  by (simp add: collinear_def)

lemma collinear_sing [iff]: "collinear {x}"
  by (simp add: collinear_def)

lemma collinear_2 [iff]: "collinear {x, y}"
  apply (simp add: collinear_def)
  apply (rule exI[where x="x - y"])
  by (metis minus_diff_eq scaleR_left.minus scaleR_one)

lemma collinear_lemma: "collinear {0, x, y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "x = 0 \<or> y = 0")
  case True
  then show ?thesis
    by (auto simp: insert_commute)
next
  case False
  show ?thesis 
  proof
    assume h: "?lhs"
    then obtain u where u: "\<forall> x\<in> {0,x,y}. \<forall>y\<in> {0,x,y}. \<exists>c. x - y = c *\<^sub>R u"
      unfolding collinear_def by blast
    from u[rule_format, of x 0] u[rule_format, of y 0]
    obtain cx and cy where
      cx: "x = cx *\<^sub>R u" and cy: "y = cy *\<^sub>R u"
      by auto
    from cx cy False have cx0: "cx \<noteq> 0" and cy0: "cy \<noteq> 0" by auto
    let ?d = "cy / cx"
    from cx cy cx0 have "y = ?d *\<^sub>R x"
      by simp
    then show ?rhs using False by blast
  next
    assume h: "?rhs"
    then obtain c where c: "y = c *\<^sub>R x"
      using False by blast
    show ?lhs
      unfolding collinear_def c
      apply (rule exI[where x=x])
      apply auto
          apply (rule exI[where x="- 1"], simp)
         apply (rule exI[where x= "-c"], simp)
        apply (rule exI[where x=1], simp)
       apply (rule exI[where x="1 - c"], simp add: scaleR_left_diff_distrib)
      apply (rule exI[where x="c - 1"], simp add: scaleR_left_diff_distrib)
      done
  qed
qed

lemma norm_cauchy_schwarz_equal: "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow> collinear {0, x, y}"
proof (cases "x=0")
  case True
  then show ?thesis
    by (auto simp: insert_commute)
next
  case False
  then have nnz: "norm x \<noteq> 0"
    by auto
  show ?thesis
  proof
    assume "\<bar>x \<bullet> y\<bar> = norm x * norm y"
    then show "collinear {0, x, y}"
      unfolding norm_cauchy_schwarz_abs_eq collinear_lemma 
      by (meson eq_vector_fraction_iff nnz)
  next
    assume "collinear {0, x, y}"
    with False show "\<bar>x \<bullet> y\<bar> = norm x * norm y"
      unfolding norm_cauchy_schwarz_abs_eq collinear_lemma  by (auto simp: abs_if)
  qed
qed

end
