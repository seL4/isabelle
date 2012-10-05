(*  Title:      HOL/Multivariate_Analysis/Linear_Algebra.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* Elementary linear algebra on Euclidean spaces *}

theory Linear_Algebra
imports
  Euclidean_Space
  "~~/src/HOL/Library/Infinite_Set"
begin

lemma cond_application_beta: "(if b then f else g) x = (if b then f x else g x)"
  by auto

notation inner (infix "\<bullet>" 70)

lemma square_bound_lemma: "(x::real) < (1 + x) * (1 + x)"
proof -
  have "(x + 1/2)^2 + 3/4 > 0" using zero_le_power2[of "x+1/2"] by arith
  then show ?thesis by (simp add: field_simps power2_eq_square)
qed

lemma square_continuous: "0 < (e::real) ==> \<exists>d. 0 < d \<and> (\<forall>y. abs(y - x) < d \<longrightarrow> abs(y * y - x * x) < e)"
  using isCont_power[OF isCont_ident, of 2, unfolded isCont_def LIM_eq, rule_format, of e x]
  apply (auto simp add: power2_eq_square)
  apply (rule_tac x="s" in exI)
  apply auto
  apply (erule_tac x=y in allE)
  apply auto
  done

lemma real_le_lsqrt: "0 <= x \<Longrightarrow> 0 <= y \<Longrightarrow> x <= y^2 ==> sqrt x <= y"
  using real_sqrt_le_iff[of x "y^2"] by simp

lemma real_le_rsqrt: "x^2 \<le> y \<Longrightarrow> x \<le> sqrt y"
  using real_sqrt_le_mono[of "x^2" y] by simp

lemma real_less_rsqrt: "x^2 < y \<Longrightarrow> x < sqrt y"
  using real_sqrt_less_mono[of "x^2" y] by simp

lemma sqrt_even_pow2:
  assumes n: "even n"
  shows "sqrt(2 ^ n) = 2 ^ (n div 2)"
proof -
  from n obtain m where m: "n = 2*m" unfolding even_mult_two_ex ..
  from m  have "sqrt(2 ^ n) = sqrt ((2 ^ m) ^ 2)"
    by (simp only: power_mult[symmetric] mult_commute)
  then show ?thesis  using m by simp
qed

lemma real_div_sqrt: "0 <= x ==> x / sqrt(x) = sqrt(x)"
  apply (cases "x = 0", simp_all)
  using sqrt_divide_self_eq[of x]
  apply (simp add: inverse_eq_divide field_simps)
  done

text{* Hence derive more interesting properties of the norm. *}

lemma norm_eq_0_dot: "(norm x = 0) \<longleftrightarrow> (inner x x = (0::real))"
  by simp (* TODO: delete *)

lemma norm_cauchy_schwarz: "inner x y <= norm x * norm y"
  (* TODO: move to Inner_Product.thy *)
  using Cauchy_Schwarz_ineq2[of x y] by auto

lemma norm_triangle_sub:
  fixes x y :: "'a::real_normed_vector"
  shows "norm x \<le> norm y  + norm (x - y)"
  using norm_triangle_ineq[of "y" "x - y"] by (simp add: field_simps)

lemma norm_le: "norm(x) <= norm(y) \<longleftrightarrow> x \<bullet> x <= y \<bullet> y"
  by (simp add: norm_eq_sqrt_inner) 

lemma norm_lt: "norm(x) < norm(y) \<longleftrightarrow> x \<bullet> x < y \<bullet> y"
  by (simp add: norm_eq_sqrt_inner)

lemma norm_eq: "norm(x) = norm (y) \<longleftrightarrow> x \<bullet> x = y \<bullet> y"
  apply (subst order_eq_iff)
  apply (auto simp: norm_le)
  done

lemma norm_eq_1: "norm(x) = 1 \<longleftrightarrow> x \<bullet> x = 1"
  by (simp add: norm_eq_sqrt_inner)

text{* Squaring equations and inequalities involving norms.  *}

lemma dot_square_norm: "x \<bullet> x = norm(x)^2"
  by (simp only: power2_norm_eq_inner) (* TODO: move? *)

lemma norm_eq_square: "norm(x) = a \<longleftrightarrow> 0 <= a \<and> x \<bullet> x = a^2"
  by (auto simp add: norm_eq_sqrt_inner)

lemma real_abs_le_square_iff: "\<bar>x\<bar> \<le> \<bar>y\<bar> \<longleftrightarrow> (x::real)^2 \<le> y^2"
proof
  assume "\<bar>x\<bar> \<le> \<bar>y\<bar>"
  then have "\<bar>x\<bar>\<twosuperior> \<le> \<bar>y\<bar>\<twosuperior>" by (rule power_mono, simp)
  then show "x\<twosuperior> \<le> y\<twosuperior>" by simp
next
  assume "x\<twosuperior> \<le> y\<twosuperior>"
  then have "sqrt (x\<twosuperior>) \<le> sqrt (y\<twosuperior>)" by (rule real_sqrt_le_mono)
  then show "\<bar>x\<bar> \<le> \<bar>y\<bar>" by simp
qed

lemma norm_le_square: "norm(x) <= a \<longleftrightarrow> 0 <= a \<and> x \<bullet> x <= a^2"
  apply (simp add: dot_square_norm real_abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_ge_square: "norm(x) >= a \<longleftrightarrow> a <= 0 \<or> x \<bullet> x >= a ^ 2"
  apply (simp add: dot_square_norm real_abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_lt_square: "norm(x) < a \<longleftrightarrow> 0 < a \<and> x \<bullet> x < a^2"
  by (metis not_le norm_ge_square)
lemma norm_gt_square: "norm(x) > a \<longleftrightarrow> a < 0 \<or> x \<bullet> x > a^2"
  by (metis norm_le_square not_less)

text{* Dot product in terms of the norm rather than conversely. *}

lemmas inner_simps = inner_add_left inner_add_right inner_diff_right inner_diff_left 
  inner_scaleR_left inner_scaleR_right

lemma dot_norm: "x \<bullet> y = (norm(x + y) ^2 - norm x ^ 2 - norm y ^ 2) / 2"
  unfolding power2_norm_eq_inner inner_simps inner_commute by auto 

lemma dot_norm_neg: "x \<bullet> y = ((norm x ^ 2 + norm y ^ 2) - norm(x - y) ^ 2) / 2"
  unfolding power2_norm_eq_inner inner_simps inner_commute
  by (auto simp add: algebra_simps)

text{* Equality of vectors in terms of @{term "op \<bullet>"} products.    *}

lemma vector_eq: "x = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y \<and> y \<bullet> y = x \<bullet> x" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by simp
next
  assume ?rhs
  then have "x \<bullet> x - x \<bullet> y = 0 \<and> x \<bullet> y - y \<bullet> y = 0" by simp
  then have "x \<bullet> (x - y) = 0 \<and> y \<bullet> (x - y) = 0" by (simp add: inner_diff inner_commute)
  then have "(x - y) \<bullet> (x - y) = 0" by (simp add: field_simps inner_diff inner_commute)
  then show "x = y" by (simp)
qed

lemma norm_triangle_half_r:
  shows "norm (y - x1) < e / 2 \<Longrightarrow> norm (y - x2) < e / 2 \<Longrightarrow> norm (x1 - x2) < e"
  using dist_triangle_half_r unfolding dist_norm[THEN sym] by auto

lemma norm_triangle_half_l:
  assumes "norm (x - y) < e / 2" "norm (x' - (y)) < e / 2" 
  shows "norm (x - x') < e"
  using dist_triangle_half_l[OF assms[unfolded dist_norm[THEN sym]]]
  unfolding dist_norm[THEN sym] .

lemma norm_triangle_le: "norm(x) + norm y <= e ==> norm(x + y) <= e"
  by (rule norm_triangle_ineq [THEN order_trans])

lemma norm_triangle_lt: "norm(x) + norm(y) < e ==> norm(x + y) < e"
  by (rule norm_triangle_ineq [THEN le_less_trans])

lemma setsum_clauses:
  shows "setsum f {} = 0"
    and "finite S \<Longrightarrow> setsum f (insert x S) = (if x \<in> S then setsum f S else f x + setsum f S)"
  by (auto simp add: insert_absorb)

lemma setsum_norm_le:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fg: "\<forall>x \<in> S. norm (f x) \<le> g x"
  shows "norm (setsum f S) \<le> setsum g S"
  by (rule order_trans [OF norm_setsum setsum_mono]) (simp add: fg)

lemma setsum_norm_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fS: "finite S"
    and K: "\<forall>x \<in> S. norm (f x) \<le> K"
  shows "norm (setsum f S) \<le> of_nat (card S) * K"
  using setsum_norm_le[OF K] setsum_constant[symmetric]
  by simp

lemma setsum_group:
  assumes fS: "finite S" and fT: "finite T" and fST: "f ` S \<subseteq> T"
  shows "setsum (\<lambda>y. setsum g {x. x\<in> S \<and> f x = y}) T = setsum g S"
  apply (subst setsum_image_gen[OF fS, of g f])
  apply (rule setsum_mono_zero_right[OF fT fST])
  apply (auto intro: setsum_0')
  done

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = z"
proof
  assume "\<forall>x. x \<bullet> y = x \<bullet> z"
  then have "\<forall>x. x \<bullet> (y - z) = 0" by (simp add: inner_diff)
  then have "(y - z) \<bullet> (y - z) = 0" ..
  then show "y = z" by simp
qed simp

lemma vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = y"
proof
  assume "\<forall>z. x \<bullet> z = y \<bullet> z"
  then have "\<forall>z. (x - y) \<bullet> z = 0" by (simp add: inner_diff)
  then have "(x - y) \<bullet> (x - y) = 0" ..
  then show "x = y" by simp
qed simp


subsection {* Orthogonality. *}

context real_inner
begin

definition "orthogonal x y \<longleftrightarrow> (x \<bullet> y = 0)"

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x \<Longrightarrow> orthogonal a (c *\<^sub>R x)"
  "orthogonal a x \<Longrightarrow> orthogonal a (-x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a \<Longrightarrow> orthogonal (c *\<^sub>R x) a"
  "orthogonal x a \<Longrightarrow> orthogonal (-x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x - y) a"
  unfolding orthogonal_def inner_add inner_diff by auto

end

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  by (simp add: orthogonal_def inner_commute)


subsection {* Linear functions. *}

definition linear :: "('a::real_vector \<Rightarrow> 'b::real_vector) \<Rightarrow> bool"
  where "linear f \<longleftrightarrow> (\<forall>x y. f(x + y) = f x + f y) \<and> (\<forall>c x. f(c *\<^sub>R x) = c *\<^sub>R f x)"

lemma linearI:
  assumes "\<And>x y. f (x + y) = f x + f y" "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "linear f"
  using assms unfolding linear_def by auto

lemma linear_compose_cmul: "linear f ==> linear (\<lambda>x. c *\<^sub>R f x)"
  by (simp add: linear_def algebra_simps)

lemma linear_compose_neg: "linear f ==> linear (\<lambda>x. -(f(x)))"
  by (simp add: linear_def)

lemma linear_compose_add: "linear f \<Longrightarrow> linear g ==> linear (\<lambda>x. f(x) + g(x))"
  by (simp add: linear_def algebra_simps)

lemma linear_compose_sub: "linear f \<Longrightarrow> linear g ==> linear (\<lambda>x. f x - g x)"
  by (simp add: linear_def algebra_simps)

lemma linear_compose: "linear f \<Longrightarrow> linear g ==> linear (g o f)"
  by (simp add: linear_def)

lemma linear_id: "linear id" by (simp add: linear_def id_def)

lemma linear_zero: "linear (\<lambda>x. 0)" by (simp add: linear_def)

lemma linear_compose_setsum:
  assumes fS: "finite S" and lS: "\<forall>a \<in> S. linear (f a)"
  shows "linear(\<lambda>x. setsum (\<lambda>a. f a x) S)"
  using lS
  apply (induct rule: finite_induct[OF fS])
  apply (auto simp add: linear_zero intro: linear_compose_add)
  done

lemma linear_0: "linear f \<Longrightarrow> f 0 = 0"
  unfolding linear_def
  apply clarsimp
  apply (erule allE[where x="0::'a"])
  apply simp
  done

lemma linear_cmul: "linear f ==> f(c *\<^sub>R x) = c *\<^sub>R f x"
  by (simp add: linear_def)

lemma linear_neg: "linear f ==> f (-x) = - f x"
  using linear_cmul [where c="-1"] by simp

lemma linear_add: "linear f ==> f(x + y) = f x + f y"
  by (metis linear_def)

lemma linear_sub: "linear f ==> f(x - y) = f x - f y"
  by (simp add: diff_minus linear_add linear_neg)

lemma linear_setsum:
  assumes lf: "linear f" and fS: "finite S"
  shows "f (setsum g S) = setsum (f o g) S"
  using fS
proof (induct rule: finite_induct)
  case empty
  then show ?case by (simp add: linear_0[OF lf])
next
  case (insert x F)
  have "f (setsum g (insert x F)) = f (g x + setsum g F)" using insert.hyps
    by simp
  also have "\<dots> = f (g x) + f (setsum g F)" using linear_add[OF lf] by simp
  also have "\<dots> = setsum (f o g) (insert x F)" using insert.hyps by simp
  finally show ?case .
qed

lemma linear_setsum_mul:
  assumes lf: "linear f" and fS: "finite S"
  shows "f (setsum (\<lambda>i. c i *\<^sub>R v i) S) = setsum (\<lambda>i. c i *\<^sub>R f (v i)) S"
  using linear_setsum[OF lf fS, of "\<lambda>i. c i *\<^sub>R v i" , unfolded o_def] linear_cmul[OF lf]
  by simp

lemma linear_injective_0:
  assumes lf: "linear f"
  shows "inj f \<longleftrightarrow> (\<forall>x. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj f \<longleftrightarrow> (\<forall> x y. f x = f y \<longrightarrow> x = y)" by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f x - f y = 0 \<longrightarrow> x - y = 0)" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear_sub[OF lf])
  also have "\<dots> \<longleftrightarrow> (\<forall> x. f x = 0 \<longrightarrow> x = 0)" by auto
  finally show ?thesis .
qed


subsection {* Bilinear functions. *}

definition "bilinear f \<longleftrightarrow> (\<forall>x. linear(\<lambda>y. f x y)) \<and> (\<forall>y. linear(\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h ==> h (x + y) z = (h x z) + (h y z)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_radd: "bilinear h ==> h x (y + z) = (h x y) + (h x z)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_lmul: "bilinear h ==> h (c *\<^sub>R x) y = c *\<^sub>R (h x y)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_rmul: "bilinear h ==> h x (c *\<^sub>R y) = c *\<^sub>R (h x y)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_lneg: "bilinear h ==> h (- x) y = -(h x y)"
  by (simp only: scaleR_minus1_left [symmetric] bilinear_lmul)

lemma bilinear_rneg: "bilinear h ==> h x (- y) = - h x y"
  by (simp only: scaleR_minus1_left [symmetric] bilinear_rmul)

lemma  (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  using add_imp_eq[of x y 0] by auto

lemma bilinear_lzero: assumes "bilinear h" shows "h 0 x = 0"
  using bilinear_ladd [OF assms, of 0 0 x] by (simp add: eq_add_iff field_simps)

lemma bilinear_rzero: assumes "bilinear h" shows "h x 0 = 0"
  using bilinear_radd [OF assms, of x 0 0 ] by (simp add: eq_add_iff field_simps)

lemma bilinear_lsub: "bilinear h ==> h (x - y) z = h x z - h y z"
  by (simp  add: diff_minus bilinear_ladd bilinear_lneg)

lemma bilinear_rsub: "bilinear h ==> h z (x - y) = h z x - h z y"
  by (simp  add: diff_minus bilinear_radd bilinear_rneg)

lemma bilinear_setsum:
  assumes bh: "bilinear h"
    and fS: "finite S"
    and fT: "finite T"
  shows "h (setsum f S) (setsum g T) = setsum (\<lambda>(i,j). h (f i) (g j)) (S \<times> T) "
proof -
  have "h (setsum f S) (setsum g T) = setsum (\<lambda>x. h (f x) (setsum g T)) S"
    apply (rule linear_setsum[unfolded o_def])
    using bh fS apply (auto simp add: bilinear_def)
    done
  also have "\<dots> = setsum (\<lambda>x. setsum (\<lambda>y. h (f x) (g y)) T) S"
    apply (rule setsum_cong, simp)
    apply (rule linear_setsum[unfolded o_def])
    using bh fT
    apply (auto simp add: bilinear_def)
    done
  finally show ?thesis unfolding setsum_cartesian_product .
qed


subsection {* Adjoints. *}

definition "adjoint f = (SOME f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y)"

lemma adjoint_unique:
  assumes "\<forall>x y. inner (f x) y = inner x (g y)"
  shows "adjoint f = g"
  unfolding adjoint_def
proof (rule some_equality)
  show "\<forall>x y. inner (f x) y = inner x (g y)" using assms .
next
  fix h assume "\<forall>x y. inner (f x) y = inner x (h y)"
  then have "\<forall>x y. inner x (g y) = inner x (h y)" using assms by simp
  then have "\<forall>x y. inner x (g y - h y) = 0" by (simp add: inner_diff_right)
  then have "\<forall>y. inner (g y - h y) (g y - h y) = 0" by simp
  then have "\<forall>y. h y = g y" by simp
  then show "h = g" by (simp add: ext)
qed

lemma choice_iff: "(\<forall>x. \<exists>y. P x y) \<longleftrightarrow> (\<exists>f. \<forall>x. P x (f x))" by metis

subsection {* Interlude: Some properties of real sets *}

lemma seq_mono_lemma: assumes "\<forall>(n::nat) \<ge> m. (d n :: real) < e n" and "\<forall>n \<ge> m. e n <= e m"
  shows "\<forall>n \<ge> m. d n < e m"
  using assms apply auto
  apply (erule_tac x="n" in allE)
  apply (erule_tac x="n" in allE)
  apply auto
  done


lemma infinite_enumerate: assumes fS: "infinite S"
  shows "\<exists>r. subseq r \<and> (\<forall>n. r n \<in> S)"
  unfolding subseq_def
  using enumerate_in_set[OF fS] enumerate_mono[of _ _ S] fS by auto

lemma approachable_lt_le: "(\<exists>(d::real)>0. \<forall>x. f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI)
  apply auto
  done


lemma triangle_lemma:
  assumes x: "0 <= (x::real)" and y:"0 <= y" and z: "0 <= z" and xy: "x^2 <= y^2 + z^2"
  shows "x <= y + z"
proof -
  have "y^2 + z^2 \<le> y^2 + 2*y*z + z^2" using z y by (simp add: mult_nonneg_nonneg)
  with xy have th: "x ^2 \<le> (y+z)^2" by (simp add: power2_eq_square field_simps)
  from y z have yz: "y + z \<ge> 0" by arith
  from power2_le_imp_le[OF th yz] show ?thesis .
qed


subsection {* A generic notion of "hull" (convex, affine, conic hull and closure). *}

definition hull :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "hull" 75)
  where "S hull s = Inter {t. S t \<and> s \<subseteq> t}"

lemma hull_same: "S s \<Longrightarrow> S hull s = s"
  unfolding hull_def by auto

lemma hull_in: "(\<And>T. Ball T S ==> S (Inter T)) ==> S (S hull s)"
  unfolding hull_def Ball_def by auto

lemma hull_eq: "(\<And>T. Ball T S ==> S (Inter T)) ==> (S hull s) = s \<longleftrightarrow> S s"
  using hull_same[of S s] hull_in[of S s] by metis


lemma hull_hull: "S hull (S hull s) = S hull s"
  unfolding hull_def by blast

lemma hull_subset[intro]: "s \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_mono: " s \<subseteq> t ==> (S hull s) \<subseteq> (S hull t)"
  unfolding hull_def by blast

lemma hull_antimono: "\<forall>x. S x \<longrightarrow> T x ==> (T hull s) \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_minimal: "s \<subseteq> t \<Longrightarrow> S t ==> (S hull s) \<subseteq> t"
  unfolding hull_def by blast

lemma subset_hull: "S t ==> S hull s \<subseteq> t \<longleftrightarrow>  s \<subseteq> t"
  unfolding hull_def by blast

lemma hull_unique: "s \<subseteq> t \<Longrightarrow> S t \<Longrightarrow>
    (\<And>t'. s \<subseteq> t' \<Longrightarrow> S t' \<Longrightarrow> t \<subseteq> t') \<Longrightarrow> (S hull s = t)"
  unfolding hull_def by auto

lemma hull_induct: "(\<And>x. x\<in> S \<Longrightarrow> P x) \<Longrightarrow> Q {x. P x} \<Longrightarrow> \<forall>x\<in> Q hull S. P x"
  using hull_minimal[of S "{x. P x}" Q]
  by (auto simp add: subset_eq)

lemma hull_inc: "x \<in> S \<Longrightarrow> x \<in> P hull S"
  by (metis hull_subset subset_eq)

lemma hull_union_subset: "(S hull s) \<union> (S hull t) \<subseteq> (S hull (s \<union> t))"
  unfolding Un_subset_iff by (metis hull_mono Un_upper1 Un_upper2)

lemma hull_union:
  assumes T: "\<And>T. Ball T S ==> S (Inter T)"
  shows "S hull (s \<union> t) = S hull (S hull s \<union> S hull t)"
  apply rule
  apply (rule hull_mono)
  unfolding Un_subset_iff
  apply (metis hull_subset Un_upper1 Un_upper2 subset_trans)
  apply (rule hull_minimal)
  apply (metis hull_union_subset)
  apply (metis hull_in T)
  done

lemma hull_redundant_eq: "a \<in> (S hull s) \<longleftrightarrow> (S hull (insert a s) = S hull s)"
  unfolding hull_def by blast

lemma hull_redundant: "a \<in> (S hull s) ==> (S hull (insert a s) = S hull s)"
  by (metis hull_redundant_eq)


subsection {* Archimedean properties and useful consequences *}

lemma real_arch_simple: "\<exists>n. x <= real (n::nat)"
  unfolding real_of_nat_def by (rule ex_le_of_nat)

lemma real_arch_inv: "0 < e \<longleftrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  using reals_Archimedean
  apply (auto simp add: field_simps)
  apply (subgoal_tac "inverse (real n) > 0")
  apply arith
  apply simp
  done

lemma real_pow_lbound: "0 <= x ==> 1 + real n * x <= (1 + x) ^ n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have h: "1 + real n * x \<le> (1 + x) ^ n" by simp
  from h have p: "1 \<le> (1 + x) ^ n" using Suc.prems by simp
  from h have "1 + real n * x + x \<le> (1 + x) ^ n + x" by simp
  also have "\<dots> \<le> (1 + x) ^ Suc n" apply (subst diff_le_0_iff_le[symmetric])
    apply (simp add: field_simps)
    using mult_left_mono[OF p Suc.prems] apply simp
    done
  finally show ?case  by (simp add: real_of_nat_Suc field_simps)
qed

lemma real_arch_pow: assumes x: "1 < (x::real)" shows "\<exists>n. y < x^n"
proof -
  from x have x0: "x - 1 > 0" by arith
  from reals_Archimedean3[OF x0, rule_format, of y]
  obtain n::nat where n:"y < real n * (x - 1)" by metis
  from x0 have x00: "x- 1 \<ge> 0" by arith
  from real_pow_lbound[OF x00, of n] n
  have "y < x^n" by auto
  then show ?thesis by metis
qed

lemma real_arch_pow2: "\<exists>n. (x::real) < 2^ n"
  using real_arch_pow[of 2 x] by simp

lemma real_arch_pow_inv:
  assumes y: "(y::real) > 0" and x1: "x < 1"
  shows "\<exists>n. x^n < y"
proof -
  { assume x0: "x > 0"
    from x0 x1 have ix: "1 < 1/x" by (simp add: field_simps)
    from real_arch_pow[OF ix, of "1/y"]
    obtain n where n: "1/y < (1/x)^n" by blast
    then have ?thesis using y x0
      by (auto simp add: field_simps power_divide) }
  moreover
  { assume "\<not> x > 0"
    with y x1 have ?thesis apply auto by (rule exI[where x=1], auto) }
  ultimately show ?thesis by metis
qed

lemma forall_pos_mono:
  "(\<And>d e::real. d < e \<Longrightarrow> P d ==> P e) \<Longrightarrow>
    (\<And>n::nat. n \<noteq> 0 ==> P(inverse(real n))) \<Longrightarrow> (\<And>e. 0 < e ==> P e)"
  by (metis real_arch_inv)

lemma forall_pos_mono_1:
  "(\<And>d e::real. d < e \<Longrightarrow> P d ==> P e) \<Longrightarrow>
    (\<And>n. P(inverse(real (Suc n)))) ==> 0 < e ==> P e"
  apply (rule forall_pos_mono)
  apply auto
  apply (atomize)
  apply (erule_tac x="n - 1" in allE)
  apply auto
  done

lemma real_archimedian_rdiv_eq_0:
  assumes x0: "x \<ge> 0" and c: "c \<ge> 0" and xc: "\<forall>(m::nat)>0. real m * x \<le> c"
  shows "x = 0"
proof -
  { assume "x \<noteq> 0" with x0 have xp: "x > 0" by arith
    from reals_Archimedean3[OF xp, rule_format, of c]
    obtain n::nat where n: "c < real n * x" by blast
    with xc[rule_format, of n] have "n = 0" by arith
    with n c have False by simp }
  then show ?thesis by blast
qed


subsection{* A bit of linear algebra. *}

definition (in real_vector) subspace :: "'a set \<Rightarrow> bool"
  where "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x\<in> S. \<forall>y \<in>S. x + y \<in> S) \<and> (\<forall>c. \<forall>x \<in>S. c *\<^sub>R x \<in>S )"

definition (in real_vector) "span S = (subspace hull S)"
definition (in real_vector) "dependent S \<longleftrightarrow> (\<exists>a \<in> S. a \<in> span(S - {a}))"
abbreviation (in real_vector) "independent s == ~(dependent s)"

text {* Closure properties of subspaces. *}

lemma subspace_UNIV[simp]: "subspace(UNIV)" by (simp add: subspace_def)

lemma (in real_vector) subspace_0: "subspace S ==> 0 \<in> S" by (metis subspace_def)

lemma (in real_vector) subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S ==> x + y \<in> S"
  by (metis subspace_def)

lemma (in real_vector) subspace_mul: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> c *\<^sub>R x \<in> S"
  by (metis subspace_def)

lemma subspace_neg: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> - x \<in> S"
  by (metis scaleR_minus1_left subspace_mul)

lemma subspace_sub: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x - y \<in> S"
  by (metis diff_minus subspace_add subspace_neg)

lemma (in real_vector) subspace_setsum:
  assumes sA: "subspace A" and fB: "finite B"
    and f: "\<forall>x\<in> B. f x \<in> A"
  shows "setsum f B \<in> A"
  using  fB f sA
  by (induct rule: finite_induct[OF fB])
    (simp add: subspace_def sA, auto simp add: sA subspace_add)

lemma subspace_linear_image:
  assumes lf: "linear f" and sS: "subspace S"
  shows "subspace(f ` S)"
  using lf sS linear_0[OF lf]
  unfolding linear_def subspace_def
  apply (auto simp add: image_iff)
  apply (rule_tac x="x + y" in bexI, auto)
  apply (rule_tac x="c *\<^sub>R x" in bexI, auto)
  done

lemma subspace_linear_vimage: "linear f \<Longrightarrow> subspace S \<Longrightarrow> subspace (f -` S)"
  by (auto simp add: subspace_def linear_def linear_0[of f])

lemma subspace_linear_preimage: "linear f ==> subspace S ==> subspace {x. f x \<in> S}"
  by (auto simp add: subspace_def linear_def linear_0[of f])

lemma subspace_trivial: "subspace {0}"
  by (simp add: subspace_def)

lemma (in real_vector) subspace_inter: "subspace A \<Longrightarrow> subspace B ==> subspace (A \<inter> B)"
  by (simp add: subspace_def)

lemma subspace_Times: "\<lbrakk>subspace A; subspace B\<rbrakk> \<Longrightarrow> subspace (A \<times> B)"
  unfolding subspace_def zero_prod_def by simp

text {* Properties of span. *}

lemma (in real_vector) span_mono: "A \<subseteq> B ==> span A \<subseteq> span B"
  by (metis span_def hull_mono)

lemma (in real_vector) subspace_span: "subspace(span S)"
  unfolding span_def
  apply (rule hull_in)
  apply (simp only: subspace_def Inter_iff Int_iff subset_eq)
  apply auto
  done

lemma (in real_vector) span_clauses:
  "a \<in> S ==> a \<in> span S"
  "0 \<in> span S"
  "x\<in> span S \<Longrightarrow> y \<in> span S ==> x + y \<in> span S"
  "x \<in> span S \<Longrightarrow> c *\<^sub>R x \<in> span S"
  by (metis span_def hull_subset subset_eq)
     (metis subspace_span subspace_def)+

lemma span_unique:
  "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> (\<And>T'. S \<subseteq> T' \<Longrightarrow> subspace T' \<Longrightarrow> T \<subseteq> T') \<Longrightarrow> span S = T"
  unfolding span_def by (rule hull_unique)

lemma span_minimal: "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> span S \<subseteq> T"
  unfolding span_def by (rule hull_minimal)

lemma (in real_vector) span_induct:
  assumes x: "x \<in> span S"
    and P: "subspace P"
    and SP: "\<And>x. x \<in> S ==> x \<in> P"
  shows "x \<in> P"
proof -
  from SP have SP': "S \<subseteq> P" by (simp add: subset_eq)
  from x hull_minimal[where S=subspace, OF SP' P, unfolded span_def[symmetric]]
  show "x \<in> P" by (metis subset_eq)
qed

lemma span_empty[simp]: "span {} = {0}"
  apply (simp add: span_def)
  apply (rule hull_unique)
  apply (auto simp add: subspace_def)
  done

lemma (in real_vector) independent_empty[intro]: "independent {}"
  by (simp add: dependent_def)

lemma dependent_single[simp]: "dependent {x} \<longleftrightarrow> x = 0"
  unfolding dependent_def by auto

lemma (in real_vector) independent_mono: "independent A \<Longrightarrow> B \<subseteq> A ==> independent B"
  apply (clarsimp simp add: dependent_def span_mono)
  apply (subgoal_tac "span (B - {a}) \<le> span (A - {a})")
  apply force
  apply (rule span_mono)
  apply auto
  done

lemma (in real_vector) span_subspace: "A \<subseteq> B \<Longrightarrow> B \<le> span A \<Longrightarrow>  subspace B \<Longrightarrow> span A = B"
  by (metis order_antisym span_def hull_minimal)

lemma (in real_vector) span_induct':
  assumes SP: "\<forall>x \<in> S. P x"
    and P: "subspace {x. P x}"
  shows "\<forall>x \<in> span S. P x"
  using span_induct SP P by blast

inductive_set (in real_vector) span_induct_alt_help for S:: "'a set"
  where
  span_induct_alt_help_0: "0 \<in> span_induct_alt_help S"
| span_induct_alt_help_S:
    "x \<in> S \<Longrightarrow> z \<in> span_induct_alt_help S \<Longrightarrow> (c *\<^sub>R x + z) \<in> span_induct_alt_help S"

lemma span_induct_alt':
  assumes h0: "h 0" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *\<^sub>R x + y)"
  shows "\<forall>x \<in> span S. h x"
proof -
  { fix x:: "'a" assume x: "x \<in> span_induct_alt_help S"
    have "h x"
      apply (rule span_induct_alt_help.induct[OF x])
      apply (rule h0)
      apply (rule hS, assumption, assumption)
      done }
  note th0 = this
  { fix x assume x: "x \<in> span S"
    have "x \<in> span_induct_alt_help S"
    proof (rule span_induct[where x=x and S=S])
      show "x \<in> span S" using x .
    next
      fix x assume xS : "x \<in> S"
        from span_induct_alt_help_S[OF xS span_induct_alt_help_0, of 1]
        show "x \<in> span_induct_alt_help S" by simp
    next
      have "0 \<in> span_induct_alt_help S" by (rule span_induct_alt_help_0)
      moreover
      { fix x y
        assume h: "x \<in> span_induct_alt_help S" "y \<in> span_induct_alt_help S"
        from h have "(x + y) \<in> span_induct_alt_help S"
          apply (induct rule: span_induct_alt_help.induct)
          apply simp
          unfolding add_assoc
          apply (rule span_induct_alt_help_S)
          apply assumption
          apply simp
          done }
      moreover
      { fix c x
        assume xt: "x \<in> span_induct_alt_help S"
        then have "(c *\<^sub>R x) \<in> span_induct_alt_help S"
          apply (induct rule: span_induct_alt_help.induct)
          apply (simp add: span_induct_alt_help_0)
          apply (simp add: scaleR_right_distrib)
          apply (rule span_induct_alt_help_S)
          apply assumption
          apply simp
          done }
      ultimately
      show "subspace (span_induct_alt_help S)"
        unfolding subspace_def Ball_def by blast
    qed }
  with th0 show ?thesis by blast
qed

lemma span_induct_alt:
  assumes h0: "h 0" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *\<^sub>R x + y)" and x: "x \<in> span S"
  shows "h x"
  using span_induct_alt'[of h S] h0 hS x by blast

text {* Individual closure properties. *}

lemma span_span: "span (span A) = span A"
  unfolding span_def hull_hull ..

lemma (in real_vector) span_superset: "x \<in> S ==> x \<in> span S" by (metis span_clauses(1))

lemma (in real_vector) span_0: "0 \<in> span S" by (metis subspace_span subspace_0)

lemma span_inc: "S \<subseteq> span S"
  by (metis subset_eq span_superset)

lemma (in real_vector) dependent_0: assumes "0\<in>A" shows "dependent A"
  unfolding dependent_def apply(rule_tac x=0 in bexI)
  using assms span_0 by auto

lemma (in real_vector) span_add: "x \<in> span S \<Longrightarrow> y \<in> span S ==> x + y \<in> span S"
  by (metis subspace_add subspace_span)

lemma (in real_vector) span_mul: "x \<in> span S ==> (c *\<^sub>R x) \<in> span S"
  by (metis subspace_span subspace_mul)

lemma span_neg: "x \<in> span S ==> - x \<in> span S"
  by (metis subspace_neg subspace_span)

lemma span_sub: "x \<in> span S \<Longrightarrow> y \<in> span S ==> x - y \<in> span S"
  by (metis subspace_span subspace_sub)

lemma (in real_vector) span_setsum: "finite A \<Longrightarrow> \<forall>x \<in> A. f x \<in> span S ==> setsum f A \<in> span S"
  by (rule subspace_setsum, rule subspace_span)

lemma span_add_eq: "x \<in> span S \<Longrightarrow> x + y \<in> span S \<longleftrightarrow> y \<in> span S"
  apply (auto simp only: span_add span_sub)
  apply (subgoal_tac "(x + y) - x \<in> span S", simp)
  apply (simp only: span_add span_sub)
  done

text {* Mapping under linear image. *}

lemma image_subset_iff_subset_vimage: "f ` A \<subseteq> B \<longleftrightarrow> A \<subseteq> f -` B"
  by auto (* TODO: move *)

lemma span_linear_image:
  assumes lf: "linear f"
  shows "span (f ` S) = f ` (span S)"
proof (rule span_unique)
  show "f ` S \<subseteq> f ` span S"
    by (intro image_mono span_inc)
  show "subspace (f ` span S)"
    using lf subspace_span by (rule subspace_linear_image)
next
  fix T assume "f ` S \<subseteq> T" and "subspace T"
  then show "f ` span S \<subseteq> T"
    unfolding image_subset_iff_subset_vimage
    by (intro span_minimal subspace_linear_vimage lf)
qed

lemma span_union: "span (A \<union> B) = (\<lambda>(a, b). a + b) ` (span A \<times> span B)"
proof (rule span_unique)
  show "A \<union> B \<subseteq> (\<lambda>(a, b). a + b) ` (span A \<times> span B)"
    by safe (force intro: span_clauses)+
next
  have "linear (\<lambda>(a, b). a + b)"
    by (simp add: linear_def scaleR_add_right)
  moreover have "subspace (span A \<times> span B)"
    by (intro subspace_Times subspace_span)
  ultimately show "subspace ((\<lambda>(a, b). a + b) ` (span A \<times> span B))"
    by (rule subspace_linear_image)
next
  fix T
  assume "A \<union> B \<subseteq> T" and "subspace T"
  then show "(\<lambda>(a, b). a + b) ` (span A \<times> span B) \<subseteq> T"
    by (auto intro!: subspace_add elim: span_induct)
qed

text {* The key breakdown property. *}

lemma span_singleton: "span {x} = range (\<lambda>k. k *\<^sub>R x)"
proof (rule span_unique)
  show "{x} \<subseteq> range (\<lambda>k. k *\<^sub>R x)"
    by (fast intro: scaleR_one [symmetric])
  show "subspace (range (\<lambda>k. k *\<^sub>R x))"
    unfolding subspace_def
    by (auto intro: scaleR_add_left [symmetric])
  fix T assume "{x} \<subseteq> T" and "subspace T" then show "range (\<lambda>k. k *\<^sub>R x) \<subseteq> T"
    unfolding subspace_def by auto
qed

lemma span_insert: "span (insert a S) = {x. \<exists>k. (x - k *\<^sub>R a) \<in> span S}"
proof -
  have "span ({a} \<union> S) = {x. \<exists>k. (x - k *\<^sub>R a) \<in> span S}"
    unfolding span_union span_singleton
    apply safe
    apply (rule_tac x=k in exI, simp)
    apply (erule rev_image_eqI [OF SigmaI [OF rangeI]])
    apply simp
    apply (rule right_minus)
    done
  then show ?thesis by simp
qed

lemma span_breakdown:
  assumes bS: "b \<in> S" and aS: "a \<in> span S"
  shows "\<exists>k. a - k *\<^sub>R b \<in> span (S - {b})"
  using assms span_insert [of b "S - {b}"]
  by (simp add: insert_absorb)

lemma span_breakdown_eq: "x \<in> span (insert a S) \<longleftrightarrow> (\<exists>k. (x - k *\<^sub>R a) \<in> span S)"
  by (simp add: span_insert)

text {* Hence some "reversal" results. *}

lemma in_span_insert:
  assumes a: "a \<in> span (insert b S)"
    and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof -
  from span_breakdown[of b "insert b S" a, OF insertI1 a]
  obtain k where k: "a - k*\<^sub>R b \<in> span (S - {b})" by auto
  { assume k0: "k = 0"
    with k have "a \<in> span S"
      apply (simp)
      apply (rule set_rev_mp)
      apply assumption
      apply (rule span_mono)
      apply blast
      done
    with na  have ?thesis by blast }
  moreover
  { assume k0: "k \<noteq> 0"
    have eq: "b = (1/k) *\<^sub>R a - ((1/k) *\<^sub>R a - b)" by simp
    from k0 have eq': "(1/k) *\<^sub>R (a - k*\<^sub>R b) = (1/k) *\<^sub>R a - b"
      by (simp add: algebra_simps)
    from k have "(1/k) *\<^sub>R (a - k*\<^sub>R b) \<in> span (S - {b})"
      by (rule span_mul)
    then have th: "(1/k) *\<^sub>R a - b \<in> span (S - {b})"
      unfolding eq' .

    from k
    have ?thesis
      apply (subst eq)
      apply (rule span_sub)
      apply (rule span_mul)
      apply (rule span_superset)
      apply blast
      apply (rule set_rev_mp)
      apply (rule th)
      apply (rule span_mono)
      using na by blast }
  ultimately show ?thesis by blast
qed

lemma in_span_delete:
  assumes a: "a \<in> span S"
    and na: "a \<notin> span (S-{b})"
  shows "b \<in> span (insert a (S - {b}))"
  apply (rule in_span_insert)
  apply (rule set_rev_mp)
  apply (rule a)
  apply (rule span_mono)
  apply blast
  apply (rule na)
  done

text {* Transitivity property. *}

lemma span_redundant: "x \<in> span S \<Longrightarrow> span (insert x S) = span S"
  unfolding span_def by (rule hull_redundant)

lemma span_trans:
  assumes x: "x \<in> span S" and y: "y \<in> span (insert x S)"
  shows "y \<in> span S"
  using assms by (simp only: span_redundant)

lemma span_insert_0[simp]: "span (insert 0 S) = span S"
  by (simp only: span_redundant span_0)

text {* An explicit expansion is sometimes needed. *}

lemma span_explicit:
  "span P = {y. \<exists>S u. finite S \<and> S \<subseteq> P \<and> setsum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?E" is "_ = {y. ?h y}" is "_ = {y. \<exists>S u. ?Q S u y}")
proof -
  { fix x assume x: "x \<in> ?E"
    then obtain S u where fS: "finite S" and SP: "S\<subseteq>P" and u: "setsum (\<lambda>v. u v *\<^sub>R v) S = x"
      by blast
    have "x \<in> span P"
      unfolding u[symmetric]
      apply (rule span_setsum[OF fS])
      using span_mono[OF SP]
      apply (auto intro: span_superset span_mul)
      done }
  moreover
  have "\<forall>x \<in> span P. x \<in> ?E"
  proof (rule span_induct_alt')
    show "0 \<in> Collect ?h"
      unfolding mem_Collect_eq
      apply (rule exI[where x="{}"])
      apply simp
      done
  next
    fix c x y
    assume x: "x \<in> P" and hy: "y \<in> Collect ?h"
    from hy obtain S u where fS: "finite S" and SP: "S\<subseteq>P"
      and u: "setsum (\<lambda>v. u v *\<^sub>R v) S = y" by blast
    let ?S = "insert x S"
    let ?u = "\<lambda>y. if y = x then (if x \<in> S then u y + c else c) else u y"
    from fS SP x have th0: "finite (insert x S)" "insert x S \<subseteq> P" by blast+
    { assume xS: "x \<in> S"
      have S1: "S = (S - {x}) \<union> {x}"
        and Sss:"finite (S - {x})" "finite {x}" "(S -{x}) \<inter> {x} = {}" using xS fS by auto
      have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S =(\<Sum>v\<in>S - {x}. u v *\<^sub>R v) + (u x + c) *\<^sub>R x"
        using xS
        by (simp add: setsum_Un_disjoint[OF Sss, unfolded S1[symmetric]]
          setsum_clauses(2)[OF fS] cong del: if_weak_cong)
      also have "\<dots> = (\<Sum>v\<in>S. u v *\<^sub>R v) + c *\<^sub>R x"
        apply (simp add: setsum_Un_disjoint[OF Sss, unfolded S1[symmetric]])
        apply (simp add: algebra_simps)
        done
      also have "\<dots> = c*\<^sub>R x + y"
        by (simp add: add_commute u)
      finally have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = c*\<^sub>R x + y" .
    then have "?Q ?S ?u (c*\<^sub>R x + y)" using th0 by blast }
    moreover
    { assume xS: "x \<notin> S"
      have th00: "(\<Sum>v\<in>S. (if v = x then c else u v) *\<^sub>R v) = y"
        unfolding u[symmetric]
        apply (rule setsum_cong2)
        using xS apply auto
        done
      have "?Q ?S ?u (c*\<^sub>R x + y)" using fS xS th0
        by (simp add: th00 setsum_clauses add_commute cong del: if_weak_cong) }
    ultimately have "?Q ?S ?u (c*\<^sub>R x + y)" by (cases "x \<in> S") simp_all
    then show "(c*\<^sub>R x + y) \<in> Collect ?h"
      unfolding mem_Collect_eq
      apply -
      apply (rule exI[where x="?S"])
      apply (rule exI[where x="?u"])
      apply metis
      done
  qed
  ultimately show ?thesis by blast
qed

lemma dependent_explicit:
  "dependent P \<longleftrightarrow> (\<exists>S u. finite S \<and> S \<subseteq> P \<and> (\<exists>v\<in>S. u v \<noteq> 0 \<and> setsum (\<lambda>v. u v *\<^sub>R v) S = 0))"
  (is "?lhs = ?rhs")
proof -
  { assume dP: "dependent P"
    then obtain a S u where aP: "a \<in> P" and fS: "finite S"
      and SP: "S \<subseteq> P - {a}" and ua: "setsum (\<lambda>v. u v *\<^sub>R v) S = a"
      unfolding dependent_def span_explicit by blast
    let ?S = "insert a S"
    let ?u = "\<lambda>y. if y = a then - 1 else u y"
    let ?v = a
    from aP SP have aS: "a \<notin> S" by blast
    from fS SP aP have th0: "finite ?S" "?S \<subseteq> P" "?v \<in> ?S" "?u ?v \<noteq> 0" by auto
    have s0: "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = 0"
      using fS aS
      apply (simp add: setsum_clauses field_simps)
      apply (subst (2) ua[symmetric])
      apply (rule setsum_cong2)
      apply auto
      done
    with th0 have ?rhs
      apply -
      apply (rule exI[where x= "?S"])
      apply (rule exI[where x= "?u"])
      apply auto
      done
  }
  moreover
  { fix S u v
    assume fS: "finite S"
      and SP: "S \<subseteq> P" and vS: "v \<in> S" and uv: "u v \<noteq> 0"
      and u: "setsum (\<lambda>v. u v *\<^sub>R v) S = 0"
    let ?a = v
    let ?S = "S - {v}"
    let ?u = "\<lambda>i. (- u i) / u v"
    have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P" using fS SP vS by auto
    have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = setsum (\<lambda>v. (- (inverse (u ?a))) *\<^sub>R (u v *\<^sub>R v)) S - ?u v *\<^sub>R v"
      using fS vS uv by (simp add: setsum_diff1 divide_inverse field_simps)
    also have "\<dots> = ?a" unfolding scaleR_right.setsum [symmetric] u using uv by simp
    finally  have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = ?a" .
    with th0 have ?lhs
      unfolding dependent_def span_explicit
      apply -
      apply (rule bexI[where x= "?a"])
      apply (simp_all del: scaleR_minus_left)
      apply (rule exI[where x= "?S"])
      apply (auto simp del: scaleR_minus_left)
      done
  }
  ultimately show ?thesis by blast
qed


lemma span_finite:
  assumes fS: "finite S"
  shows "span S = {y. \<exists>u. setsum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?rhs")
proof -
  { fix y
    assume y: "y \<in> span S"
    from y obtain S' u where fS': "finite S'" and SS': "S' \<subseteq> S" and
      u: "setsum (\<lambda>v. u v *\<^sub>R v) S' = y" unfolding span_explicit by blast
    let ?u = "\<lambda>x. if x \<in> S' then u x else 0"
    have "setsum (\<lambda>v. ?u v *\<^sub>R v) S = setsum (\<lambda>v. u v *\<^sub>R v) S'"
      using SS' fS by (auto intro!: setsum_mono_zero_cong_right)
    then have "setsum (\<lambda>v. ?u v *\<^sub>R v) S = y" by (metis u)
    then have "y \<in> ?rhs" by auto }
  moreover
  { fix y u
    assume u: "setsum (\<lambda>v. u v *\<^sub>R v) S = y"
    then have "y \<in> span S" using fS unfolding span_explicit by auto }
  ultimately show ?thesis by blast
qed

text {* This is useful for building a basis step-by-step. *}

lemma independent_insert:
  "independent(insert a S) \<longleftrightarrow>
      (if a \<in> S then independent S
                else independent S \<and> a \<notin> span S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  { assume aS: "a \<in> S"
    then have ?thesis using insert_absorb[OF aS] by simp }
  moreover
  { assume aS: "a \<notin> S"
    { assume i: ?lhs
      then have ?rhs using aS
        apply simp
        apply (rule conjI)
        apply (rule independent_mono)
        apply assumption
        apply blast
        apply (simp add: dependent_def)
        done }
    moreover
    { assume i: ?rhs
      have ?lhs using i aS
        apply simp
        apply (auto simp add: dependent_def)
        apply (case_tac "aa = a", auto)
        apply (subgoal_tac "insert a S - {aa} = insert a (S - {aa})")
        apply simp
        apply (subgoal_tac "a \<in> span (insert aa (S - {aa}))")
        apply (subgoal_tac "insert aa (S - {aa}) = S")
        apply simp
        apply blast
        apply (rule in_span_insert)
        apply assumption
        apply blast
        apply blast
        done }
    ultimately have ?thesis by blast }
  ultimately show ?thesis by blast
qed

text {* The degenerate case of the Exchange Lemma. *}

lemma mem_delete: "x \<in> (A - {a}) \<longleftrightarrow> x \<noteq> a \<and> x \<in> A"
  by blast

lemma spanning_subset_independent:
  assumes BA: "B \<subseteq> A"
    and iA: "independent A"
    and AsB: "A \<subseteq> span B"
  shows "A = B"
proof
  show "B \<subseteq> A" by (rule BA)

  from span_mono[OF BA] span_mono[OF AsB]
  have sAB: "span A = span B" unfolding span_span by blast

  { fix x assume x: "x \<in> A"
    from iA have th0: "x \<notin> span (A - {x})"
      unfolding dependent_def using x by blast
    from x have xsA: "x \<in> span A" by (blast intro: span_superset)
    have "A - {x} \<subseteq> A" by blast
    then have th1:"span (A - {x}) \<subseteq> span A" by (metis span_mono)
    { assume xB: "x \<notin> B"
      from xB BA have "B \<subseteq> A -{x}" by blast
      then have "span B \<subseteq> span (A - {x})" by (metis span_mono)
      with th1 th0 sAB have "x \<notin> span A" by blast
      with x have False by (metis span_superset) }
    then have "x \<in> B" by blast }
  then show "A \<subseteq> B" by blast
qed

text {* The general case of the Exchange Lemma, the key to what follows. *}

lemma exchange_lemma:
  assumes f:"finite t"
    and i: "independent s"
    and sp: "s \<subseteq> span t"
  shows "\<exists>t'. (card t' = card t) \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  using f i sp
proof (induct "card (t - s)" arbitrary: s t rule: less_induct)
  case less
  note ft = `finite t` and s = `independent s` and sp = `s \<subseteq> span t`
  let ?P = "\<lambda>t'. (card t' = card t) \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  let ?ths = "\<exists>t'. ?P t'"
  { assume st: "s \<subseteq> t"
    from st ft span_mono[OF st] have ?ths apply - apply (rule exI[where x=t])
      apply (auto intro: span_superset)
      done }
  moreover
  { assume st: "t \<subseteq> s"
    from spanning_subset_independent[OF st s sp]
      st ft span_mono[OF st] have ?ths
        apply -
        apply (rule exI[where x=t])
        apply (auto intro: span_superset)
        done }
  moreover
  { assume st: "\<not> s \<subseteq> t" "\<not> t \<subseteq> s"
    from st(2) obtain b where b: "b \<in> t" "b \<notin> s" by blast
      from b have "t - {b} - s \<subset> t - s" by blast
      then have cardlt: "card (t - {b} - s) < card (t - s)" using ft
        by (auto intro: psubset_card_mono)
      from b ft have ct0: "card t \<noteq> 0" by auto
    { assume stb: "s \<subseteq> span(t -{b})"
      from ft have ftb: "finite (t -{b})" by auto
      from less(1)[OF cardlt ftb s stb]
      obtain u where u: "card u = card (t-{b})" "s \<subseteq> u" "u \<subseteq> s \<union> (t - {b})" "s \<subseteq> span u"
        and fu: "finite u" by blast
      let ?w = "insert b u"
      have th0: "s \<subseteq> insert b u" using u by blast
      from u(3) b have "u \<subseteq> s \<union> t" by blast
      then have th1: "insert b u \<subseteq> s \<union> t" using u b by blast
      have bu: "b \<notin> u" using b u by blast
      from u(1) ft b have "card u = (card t - 1)" by auto
      then have th2: "card (insert b u) = card t"
        using card_insert_disjoint[OF fu bu] ct0 by auto
      from u(4) have "s \<subseteq> span u" .
      also have "\<dots> \<subseteq> span (insert b u)" apply (rule span_mono) by blast
      finally have th3: "s \<subseteq> span (insert b u)" .
      from th0 th1 th2 th3 fu have th: "?P ?w"  by blast
      from th have ?ths by blast }
    moreover
    { assume stb: "\<not> s \<subseteq> span(t -{b})"
      from stb obtain a where a: "a \<in> s" "a \<notin> span (t - {b})" by blast
      have ab: "a \<noteq> b" using a b by blast
      have at: "a \<notin> t" using a ab span_superset[of a "t- {b}"] by auto
      have mlt: "card ((insert a (t - {b})) - s) < card (t - s)"
        using cardlt ft a b by auto
      have ft': "finite (insert a (t - {b}))" using ft by auto
      { fix x assume xs: "x \<in> s"
        have t: "t \<subseteq> (insert b (insert a (t -{b})))" using b by auto
        from b(1) have "b \<in> span t" by (simp add: span_superset)
        have bs: "b \<in> span (insert a (t - {b}))" apply(rule in_span_delete)
          using a sp unfolding subset_eq apply auto done
        from xs sp have "x \<in> span t" by blast
        with span_mono[OF t]
        have x: "x \<in> span (insert b (insert a (t - {b})))" ..
        from span_trans[OF bs x] have "x \<in> span (insert a (t - {b}))" . }
      then have sp': "s \<subseteq> span (insert a (t - {b}))" by blast

      from less(1)[OF mlt ft' s sp'] obtain u where
        u: "card u = card (insert a (t -{b}))" "finite u" "s \<subseteq> u" "u \<subseteq> s \<union> insert a (t -{b})"
          "s \<subseteq> span u" by blast
      from u a b ft at ct0 have "?P u" by auto
      then have ?ths by blast }
    ultimately have ?ths by blast
  }
  ultimately show ?ths by blast
qed

text {* This implies corresponding size bounds. *}

lemma independent_span_bound:
  assumes f: "finite t" and i: "independent s" and sp:"s \<subseteq> span t"
  shows "finite s \<and> card s \<le> card t"
  by (metis exchange_lemma[OF f i sp] finite_subset card_mono)


lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x\<in> (UNIV::'a::finite set)}"
proof -
  have eq: "{f x |x. x\<in> UNIV} = f ` UNIV" by auto
  show ?thesis unfolding eq
    apply (rule finite_imageI)
    apply (rule finite)
    done
qed

subsection{* Euclidean Spaces as Typeclass*}

lemma independent_eq_inj_on:
  fixes D :: nat
    and f :: "nat \<Rightarrow> 'c::real_vector"
  assumes "inj_on f {..<D}"
  shows "independent (f ` {..<D}) \<longleftrightarrow> (\<forall>a u. a < D \<longrightarrow> (\<Sum>i\<in>{..<D}-{a}. u (f i) *\<^sub>R f i) \<noteq> f a)"
proof -
  from assms have eq: "\<And>i. i < D \<Longrightarrow> f ` {..<D} - {f i} = f`({..<D} - {i})"
    and inj: "\<And>i. inj_on f ({..<D} - {i})"
    by (auto simp: inj_on_def)
  have *: "\<And>i. finite (f ` {..<D} - {i})" by simp
  show ?thesis unfolding dependent_def span_finite[OF *]
    by (auto simp: eq setsum_reindex[OF inj])
qed

lemma independent_basis: "independent (basis ` {..<DIM('a)} :: 'a::euclidean_space set)"
  unfolding independent_eq_inj_on [OF basis_inj]
  apply clarify
  apply (drule_tac f="inner (basis a)" in arg_cong)
  apply (simp add: inner_setsum_right dot_basis)
  done

lemma (in euclidean_space) range_basis: "range basis = insert 0 (basis ` {..<DIM('a)})"
proof -
  have *: "UNIV = {..<DIM('a)} \<union> {DIM('a)..}" by auto
  show ?thesis unfolding * image_Un basis_finite by auto
qed

lemma (in euclidean_space) range_basis_finite[intro]: "finite (range basis)"
  unfolding range_basis by auto

lemma span_basis: "span (range basis) = (UNIV :: 'a::euclidean_space set)"
proof -
  { fix x :: 'a
    have "(\<Sum>i<DIM('a). (x $$ i) *\<^sub>R basis i) \<in> span (range basis :: 'a set)"
      by (simp add: span_setsum span_mul span_superset)
    then have "x \<in> span (range basis)"
      by (simp only: euclidean_representation [symmetric])
  } then show ?thesis by auto
qed

lemma basis_representation:
  "\<exists>u. x = (\<Sum>v\<in>basis ` {..<DIM('a)}. u v *\<^sub>R (v\<Colon>'a\<Colon>euclidean_space))"
proof -
  have "x\<in>UNIV" by auto from this[unfolded span_basis[THEN sym]]
  have "\<exists>u. (\<Sum>v\<in>basis ` {..<DIM('a)}. u v *\<^sub>R v) = x"
    unfolding range_basis span_insert_0 apply(subst (asm) span_finite) by auto
  then show ?thesis by fastforce
qed

lemma span_basis'[simp]:"span ((basis::nat=>'a) ` {..<DIM('a::euclidean_space)}) = UNIV"
  apply(subst span_basis[symmetric])
  unfolding range_basis
  apply auto
  done

lemma card_basis[simp]:"card ((basis::nat=>'a) ` {..<DIM('a::euclidean_space)}) = DIM('a)"
  apply (subst card_image)
  using basis_inj apply auto
  done

lemma in_span_basis: "(x::'a::euclidean_space) \<in> span (basis ` {..<DIM('a)})"
  unfolding span_basis' ..

lemma norm_bound_component_le: "norm (x::'a::euclidean_space) \<le> e \<Longrightarrow> \<bar>x$$i\<bar> <= e"
  by (metis component_le_norm order_trans)

lemma norm_bound_component_lt: "norm (x::'a::euclidean_space) < e \<Longrightarrow> \<bar>x$$i\<bar> < e"
  by (metis component_le_norm basic_trans_rules(21))

lemma norm_le_l1: "norm (x::'a::euclidean_space) \<le> (\<Sum>i<DIM('a). \<bar>x $$ i\<bar>)"
  apply (subst euclidean_representation[of x])
  apply (rule order_trans[OF norm_setsum])
  apply (auto intro!: setsum_mono)
  done

lemma setsum_norm_allsubsets_bound:
  fixes f:: "'a \<Rightarrow> 'n::euclidean_space"
  assumes fP: "finite P" and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (setsum f Q) \<le> e"
  shows "setsum (\<lambda>x. norm (f x)) P \<le> 2 * real DIM('n) *  e"
proof -
  let ?d = "real DIM('n)"
  let ?nf = "\<lambda>x. norm (f x)"
  let ?U = "{..<DIM('n)}"
  have th0: "setsum (\<lambda>x. setsum (\<lambda>i. \<bar>f x $$ i\<bar>) ?U) P = setsum (\<lambda>i. setsum (\<lambda>x. \<bar>f x $$ i\<bar>) P) ?U"
    by (rule setsum_commute)
  have th1: "2 * ?d * e = of_nat (card ?U) * (2 * e)" by (simp add: real_of_nat_def)
  have "setsum ?nf P \<le> setsum (\<lambda>x. setsum (\<lambda>i. \<bar>f x $$ i\<bar>) ?U) P"
    by (rule setsum_mono) (rule norm_le_l1)
  also have "\<dots> \<le> 2 * ?d * e"
    unfolding th0 th1
  proof (rule setsum_bounded)
    fix i assume i: "i \<in> ?U"
    let ?Pp = "{x. x\<in> P \<and> f x $$ i \<ge> 0}"
    let ?Pn = "{x. x \<in> P \<and> f x $$ i < 0}"
    have thp: "P = ?Pp \<union> ?Pn" by auto
    have thp0: "?Pp \<inter> ?Pn ={}" by auto
    have PpP: "?Pp \<subseteq> P" and PnP: "?Pn \<subseteq> P" by blast+
    have Ppe:"setsum (\<lambda>x. \<bar>f x $$ i\<bar>) ?Pp \<le> e"
      using component_le_norm[of "setsum (\<lambda>x. f x) ?Pp" i]  fPs[OF PpP]
      by(auto intro: abs_le_D1)
    have Pne: "setsum (\<lambda>x. \<bar>f x $$ i\<bar>) ?Pn \<le> e"
      using component_le_norm[of "setsum (\<lambda>x. - f x) ?Pn" i]  fPs[OF PnP]
      by(auto simp add: setsum_negf intro: abs_le_D1)
    have "setsum (\<lambda>x. \<bar>f x $$ i\<bar>) P = setsum (\<lambda>x. \<bar>f x $$ i\<bar>) ?Pp + setsum (\<lambda>x. \<bar>f x $$ i\<bar>) ?Pn"
      apply (subst thp)
      apply (rule setsum_Un_zero)
      using fP thp0 apply auto
      done
    also have "\<dots> \<le> 2*e" using Pne Ppe by arith
    finally show "setsum (\<lambda>x. \<bar>f x $$ i\<bar>) P \<le> 2*e" .
  qed
  finally show ?thesis .
qed

lemma choice_iff': "(\<forall>x<d. \<exists>y. P x y) \<longleftrightarrow> (\<exists>f. \<forall>x<d. P x (f x))" by metis

lemma lambda_skolem': "(\<forall>i<DIM('a::euclidean_space). \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a. \<forall>i<DIM('a). P i (x$$i))" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?S = "{..<DIM('a)}"
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f where f:"\<forall>i<DIM('a). P i (f i)" unfolding choice_iff' by metis
    let ?x = "(\<chi>\<chi> i. (f i)) :: 'a"
    { fix i assume i:"i<DIM('a)"
      with f have "P i (f i)" by metis
      then have "P i (?x$$i)" using i by auto }
    then have "\<forall>i<DIM('a). P i (?x$$i)" by metis
    then have ?rhs by metis }
  ultimately show ?thesis by metis
qed


subsection {* Linearity and Bilinearity continued *}

lemma linear_bounded:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
proof -
  let ?S = "{..<DIM('a)}"
  let ?B = "setsum (\<lambda>i. norm(f(basis i))) ?S"
  have fS: "finite ?S" by simp
  { fix x:: "'a"
    let ?g = "(\<lambda> i. (x$$i) *\<^sub>R (basis i) :: 'a)"
    have "norm (f x) = norm (f (setsum (\<lambda>i. (x$$i) *\<^sub>R (basis i)) ?S))"
      apply (subst euclidean_representation[of x])
      apply rule
      done
    also have "\<dots> = norm (setsum (\<lambda> i. (x$$i) *\<^sub>R f (basis i)) ?S)"
      using linear_setsum[OF lf fS, of ?g, unfolded o_def] linear_cmul[OF lf] by auto
    finally have th0: "norm (f x) = norm (setsum (\<lambda>i. (x$$i) *\<^sub>R f (basis i))?S)" .
    { fix i assume i: "i \<in> ?S"
      from component_le_norm[of x i]
      have "norm ((x$$i) *\<^sub>R f (basis i :: 'a)) \<le> norm (f (basis i)) * norm x"
        unfolding norm_scaleR
        apply (simp only: mult_commute)
        apply (rule mult_mono)
        apply (auto simp add: field_simps)
        done }
    then have th: "\<forall>i\<in> ?S. norm ((x$$i) *\<^sub>R f (basis i :: 'a)) \<le> norm (f (basis i)) * norm x"
      by metis
    from setsum_norm_le[of _ "\<lambda>i. (x$$i) *\<^sub>R (f (basis i))", OF th]
    have "norm (f x) \<le> ?B * norm x" unfolding th0 setsum_left_distrib by metis}
  then show ?thesis by blast
qed

lemma linear_bounded_pos:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B > 0. \<forall>x. norm (f x) \<le> B * norm x"
proof -
  from linear_bounded[OF lf] obtain B where
    B: "\<forall>x. norm (f x) \<le> B * norm x" by blast
  let ?K = "\<bar>B\<bar> + 1"
  have Kp: "?K > 0" by arith
  { assume C: "B < 0"
    have "((\<chi>\<chi> i. 1)::'a) \<noteq> 0" unfolding euclidean_eq[where 'a='a]
      by(auto intro!:exI[where x=0])
    then have "norm ((\<chi>\<chi> i. 1)::'a) > 0" by auto
    with C have "B * norm ((\<chi>\<chi> i. 1)::'a) < 0"
      by (simp add: mult_less_0_iff)
    with B[rule_format, of "(\<chi>\<chi> i. 1)::'a"] norm_ge_zero[of "f ((\<chi>\<chi> i. 1)::'a)"] have False by simp
  }
  then have Bp: "B \<ge> 0" by (metis not_leE)
  { fix x::"'a"
    have "norm (f x) \<le> ?K *  norm x"
      using B[rule_format, of x] norm_ge_zero[of x] norm_ge_zero[of "f x"] Bp
      apply (auto simp add: field_simps split add: abs_split)
      apply (erule order_trans, simp)
      done
  } then show ?thesis using Kp by blast
qed

lemma linear_conv_bounded_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<longleftrightarrow> bounded_linear f"
proof
  assume "linear f"
  show "bounded_linear f"
  proof
    fix x y show "f (x + y) = f x + f y"
      using `linear f` unfolding linear_def by simp
  next
    fix r x show "f (scaleR r x) = scaleR r (f x)"
      using `linear f` unfolding linear_def by simp
  next
    have "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
      using `linear f` by (rule linear_bounded)
    then show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (simp add: mult_commute)
  qed
next
  assume "bounded_linear f"
  then interpret f: bounded_linear f .
  show "linear f"
    by (simp add: f.add f.scaleR linear_def)
qed

lemma bounded_linearI':
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>x y. f (x + y) = f x + f y" "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "bounded_linear f"
  unfolding linear_conv_bounded_linear[THEN sym]
  by (rule linearI[OF assms])


lemma bilinear_bounded:
  fixes h:: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'k::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof -
  let ?M = "{..<DIM('m)}"
  let ?N = "{..<DIM('n)}"
  let ?B = "setsum (\<lambda>(i,j). norm (h (basis i) (basis j))) (?M \<times> ?N)"
  have fM: "finite ?M" and fN: "finite ?N" by simp_all
  { fix x:: "'m" and  y :: "'n"
    have "norm (h x y) = norm (h (setsum (\<lambda>i. (x$$i) *\<^sub>R basis i) ?M) (setsum (\<lambda>i. (y$$i) *\<^sub>R basis i) ?N))" 
      apply(subst euclidean_representation[where 'a='m])
      apply(subst euclidean_representation[where 'a='n])
      apply rule
      done
    also have "\<dots> = norm (setsum (\<lambda> (i,j). h ((x$$i) *\<^sub>R basis i) ((y$$j) *\<^sub>R basis j)) (?M \<times> ?N))"  
      unfolding bilinear_setsum[OF bh fM fN] ..
    finally have th: "norm (h x y) = \<dots>" .
    have "norm (h x y) \<le> ?B * norm x * norm y"
      apply (simp add: setsum_left_distrib th)
      apply (rule setsum_norm_le)
      using fN fM
      apply simp
      apply (auto simp add: bilinear_rmul[OF bh] bilinear_lmul[OF bh]
        field_simps simp del: scaleR_scaleR)
      apply (rule mult_mono)
      apply (auto simp add: zero_le_mult_iff component_le_norm)
      apply (rule mult_mono)
      apply (auto simp add: zero_le_mult_iff component_le_norm)
      done }
  then show ?thesis by metis
qed

lemma bilinear_bounded_pos:
  fixes h:: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof -
  from bilinear_bounded[OF bh] obtain B where
    B: "\<forall>x y. norm (h x y) \<le> B * norm x * norm y" by blast
  let ?K = "\<bar>B\<bar> + 1"
  have Kp: "?K > 0" by arith
  have KB: "B < ?K" by arith
  { fix x::'a and y::'b
    from KB Kp
    have "B * norm x * norm y \<le> ?K * norm x * norm y"
      apply -
      apply (rule mult_right_mono, rule mult_right_mono)
      apply auto
      done
    then have "norm (h x y) \<le> ?K * norm x * norm y"
      using B[rule_format, of x y] by simp }
  with Kp show ?thesis by blast
qed

lemma bilinear_conv_bounded_bilinear:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  shows "bilinear h \<longleftrightarrow> bounded_bilinear h"
proof
  assume "bilinear h"
  show "bounded_bilinear h"
  proof
    fix x y z show "h (x + y) z = h x z + h y z"
      using `bilinear h` unfolding bilinear_def linear_def by simp
  next
    fix x y z show "h x (y + z) = h x y + h x z"
      using `bilinear h` unfolding bilinear_def linear_def by simp
  next
    fix r x y show "h (scaleR r x) y = scaleR r (h x y)"
      using `bilinear h` unfolding bilinear_def linear_def
      by simp
  next
    fix r x y show "h x (scaleR r y) = scaleR r (h x y)"
      using `bilinear h` unfolding bilinear_def linear_def
      by simp
  next
    have "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
      using `bilinear h` by (rule bilinear_bounded)
    then show "\<exists>K. \<forall>x y. norm (h x y) \<le> norm x * norm y * K"
      by (simp add: mult_ac)
  qed
next
  assume "bounded_bilinear h"
  then interpret h: bounded_bilinear h .
  show "bilinear h"
    unfolding bilinear_def linear_conv_bounded_linear
    using h.bounded_linear_left h.bounded_linear_right by simp
qed


subsection {* We continue. *}

lemma independent_bound:
  fixes S:: "('a::euclidean_space) set"
  shows "independent S \<Longrightarrow> finite S \<and> card S <= DIM('a::euclidean_space)"
  using independent_span_bound[of "(basis::nat=>'a) ` {..<DIM('a)}" S] by auto

lemma dependent_biggerset:
  "(finite (S::('a::euclidean_space) set) ==> card S > DIM('a)) ==> dependent S"
  by (metis independent_bound not_less)

text {* Hence we can create a maximal independent subset. *}

lemma maximal_independent_subset_extend:
  assumes sv: "(S::('a::euclidean_space) set) \<subseteq> V"
    and iS: "independent S"
  shows "\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  using sv iS
proof (induct "DIM('a) - card S" arbitrary: S rule: less_induct)
  case less
  note sv = `S \<subseteq> V` and i = `independent S`
  let ?P = "\<lambda>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  let ?ths = "\<exists>x. ?P x"
  let ?d = "DIM('a)"
  { assume "V \<subseteq> span S"
    then have ?ths  using sv i by blast }
  moreover
  { assume VS: "\<not> V \<subseteq> span S"
    from VS obtain a where a: "a \<in> V" "a \<notin> span S" by blast
    from a have aS: "a \<notin> S" by (auto simp add: span_superset)
    have th0: "insert a S \<subseteq> V" using a sv by blast
    from independent_insert[of a S]  i a
    have th1: "independent (insert a S)" by auto
    have mlt: "?d - card (insert a S) < ?d - card S"
      using aS a independent_bound[OF th1] by auto

    from less(1)[OF mlt th0 th1]
    obtain B where B: "insert a S \<subseteq> B" "B \<subseteq> V" "independent B" " V \<subseteq> span B"
      by blast
    from B have "?P B" by auto
    then have ?ths by blast }
  ultimately show ?ths by blast
qed

lemma maximal_independent_subset:
  "\<exists>(B:: ('a::euclidean_space) set). B\<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}:: ('a::euclidean_space) set"]
    empty_subsetI independent_empty)


text {* Notion of dimension. *}

definition "dim V = (SOME n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = n))"

lemma basis_exists:
  "\<exists>B. (B :: ('a::euclidean_space) set) \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = dim V)"
  unfolding dim_def some_eq_ex[of "\<lambda>n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = n)"]
  using maximal_independent_subset[of V] independent_bound
  by auto

text {* Consequences of independence or spanning for cardinality. *}

lemma independent_card_le_dim: 
  assumes "(B::('a::euclidean_space) set) \<subseteq> V" and "independent B"
  shows "card B \<le> dim V"
proof -
  from basis_exists[of V] `B \<subseteq> V`
  obtain B' where "independent B'" and "B \<subseteq> span B'" and "card B' = dim V" by blast
  with independent_span_bound[OF _ `independent B` `B \<subseteq> span B'`] independent_bound[of B']
  show ?thesis by auto
qed

lemma span_card_ge_dim:
  "(B::('a::euclidean_space) set) \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> finite B \<Longrightarrow> dim V \<le> card B"
  by (metis basis_exists[of V] independent_span_bound subset_trans)

lemma basis_card_eq_dim:
  "B \<subseteq> (V:: ('a::euclidean_space) set) \<Longrightarrow> V \<subseteq> span B \<Longrightarrow>
    independent B \<Longrightarrow> finite B \<and> card B = dim V"
  by (metis order_eq_iff independent_card_le_dim span_card_ge_dim independent_bound)

lemma dim_unique: "(B::('a::euclidean_space) set) \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow>
    independent B \<Longrightarrow> card B = n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim)

text {* More lemmas about dimension. *}

lemma dim_UNIV: "dim (UNIV :: ('a::euclidean_space) set) = DIM('a)"
  apply (rule dim_unique[of "(basis::nat=>'a) ` {..<DIM('a)}"])
  using independent_basis apply auto
  done

lemma dim_subset:
  "(S:: ('a::euclidean_space) set) \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using basis_exists[of T] basis_exists[of S]
  by (metis independent_card_le_dim subset_trans)

lemma dim_subset_UNIV: "dim (S:: ('a::euclidean_space) set) \<le> DIM('a)"
  by (metis dim_subset subset_UNIV dim_UNIV)

text {* Converses to those. *}

lemma card_ge_dim_independent:
  assumes BV:"(B::('a::euclidean_space) set) \<subseteq> V"
    and iB:"independent B" and dVB:"dim V \<le> card B"
  shows "V \<subseteq> span B"
proof -
  { fix a assume aV: "a \<in> V"
    { assume aB: "a \<notin> span B"
      then have iaB: "independent (insert a B)" using iB aV  BV by (simp add: independent_insert)
      from aV BV have th0: "insert a B \<subseteq> V" by blast
      from aB have "a \<notin>B" by (auto simp add: span_superset)
      with independent_card_le_dim[OF th0 iaB] dVB independent_bound[OF iB] have False by auto }
    then have "a \<in> span B"  by blast }
  then show ?thesis by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "(B:: ('a::euclidean_space) set) \<subseteq> V"
    and VB: "V \<subseteq> span B"
    and fB: "finite B"
    and dVB: "dim V \<ge> card B"
  shows "independent B"
proof -
  { fix a assume a: "a \<in> B" "a \<in> span (B -{a})"
    from a fB have c0: "card B \<noteq> 0" by auto
    from a fB have cb: "card (B -{a}) = card B - 1" by auto
    from BV a have th0: "B -{a} \<subseteq> V" by blast
    { fix x assume x: "x \<in> V"
      from a have eq: "insert a (B -{a}) = B" by blast
      from x VB have x': "x \<in> span B" by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B -{a})" . }
    then have th1: "V \<subseteq> span (B -{a})" by blast
    have th2: "finite (B -{a})" using fB by auto
    from span_card_ge_dim[OF th0 th1 th2]
    have c: "dim V \<le> card (B -{a})" .
    from c c0 dVB cb have False by simp }
  then show ?thesis unfolding dependent_def by blast
qed

lemma card_eq_dim: "(B:: ('a::euclidean_space) set) \<subseteq> V \<Longrightarrow>
    card B = dim V \<Longrightarrow> finite B \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis order_eq_iff card_le_dim_spanning card_ge_dim_independent)

text {* More general size bound lemmas. *}

lemma independent_bound_general:
  "independent (S:: ('a::euclidean_space) set) \<Longrightarrow> finite S \<and> card S \<le> dim S"
  by (metis independent_card_le_dim independent_bound subset_refl)

lemma dependent_biggerset_general:
    "(finite (S:: ('a::euclidean_space) set) \<Longrightarrow> card S > dim S) \<Longrightarrow> dependent S"
  using independent_bound_general[of S] by (metis linorder_not_le)

lemma dim_span: "dim (span (S:: ('a::euclidean_space) set)) = dim S"
proof -
  have th0: "dim S \<le> dim (span S)"
    by (auto simp add: subset_eq intro: dim_subset span_superset)
  from basis_exists[of S]
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" by blast
  from B have fB: "finite B" "card B = dim S" using independent_bound by blast+
  have bSS: "B \<subseteq> span S" using B(1) by (metis subset_eq span_inc)
  have sssB: "span S \<subseteq> span B" using span_mono[OF B(3)] by (simp add: span_span)
  from span_card_ge_dim[OF bSS sssB fB(1)] th0 show ?thesis
    using fB(2) by arith
qed

lemma subset_le_dim: "(S:: ('a::euclidean_space) set) \<subseteq> span T \<Longrightarrow> dim S \<le> dim T"
  by (metis dim_span dim_subset)

lemma span_eq_dim: "span (S:: ('a::euclidean_space) set) = span T ==> dim S = dim T"
  by (metis dim_span)

lemma spans_image:
  assumes lf: "linear f"
    and VB: "V \<subseteq> span B"
  shows "f ` V \<subseteq> span (f ` B)"
  unfolding span_linear_image[OF lf] by (metis VB image_mono)

lemma dim_image_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lf: "linear f"
  shows "dim (f ` S) \<le> dim (S)"
proof -
  from basis_exists[of S] obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" by blast
  from B have fB: "finite B" "card B = dim S" using independent_bound by blast+
  have "dim (f ` S) \<le> card (f ` B)"
    apply (rule span_card_ge_dim)
    using lf B fB apply (auto simp add: span_linear_image spans_image subset_image_iff)
    done
  also have "\<dots> \<le> dim S" using card_image_le[OF fB(1)] fB by simp
  finally show ?thesis .
qed

text {* Relation between bases and injectivity/surjectivity of map. *}

lemma spanning_surjective_image:
  assumes us: "UNIV \<subseteq> span S"
    and lf: "linear f" and sf: "surj f"
  shows "UNIV \<subseteq> span (f ` S)"
proof -
  have "UNIV \<subseteq> f ` UNIV" using sf by (auto simp add: surj_def)
  also have " \<dots> \<subseteq> span (f ` S)" using spans_image[OF lf us] .
finally show ?thesis .
qed

lemma independent_injective_image:
  assumes iS: "independent S"
    and lf: "linear f"
    and fi: "inj f"
  shows "independent (f ` S)"
proof -
  { fix a
    assume a: "a \<in> S" "f a \<in> span (f ` S - {f a})"
    have eq: "f ` S - {f a} = f ` (S - {a})" using fi
      by (auto simp add: inj_on_def)
    from a have "f a \<in> f ` span (S -{a})"
      unfolding eq span_linear_image[OF lf, of "S - {a}"]  by blast
    then have "a \<in> span (S -{a})" using fi by (auto simp add: inj_on_def)
    with a(1) iS  have False by (simp add: dependent_def) }
  then show ?thesis unfolding dependent_def by blast
qed

text {* Picking an orthogonal replacement for a spanning set. *}

    (* FIXME : Move to some general theory ?*)
definition "pairwise R S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y\<in> S. x\<noteq>y \<longrightarrow> R x y)"

lemma vector_sub_project_orthogonal: "(b::'a::euclidean_space) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *\<^sub>R b) = 0"
  unfolding inner_simps by auto

lemma pairwise_orthogonal_insert:
  assumes "pairwise orthogonal S"
    and "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
  shows "pairwise orthogonal (insert x S)"
  using assms unfolding pairwise_def
  by (auto simp add: orthogonal_commute)

lemma basis_orthogonal:
  fixes B :: "('a::real_inner) set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
  using fB
proof (induct rule: finite_induct)
  case empty
  then show ?case apply (rule exI[where x="{}"]) by (auto simp add: pairwise_def)
next
  case (insert a B)
  note fB = `finite B` and aB = `a \<notin> B`
  from `\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C`
  obtain C where C: "finite C" "card C \<le> card B"
    "span C = span B" "pairwise orthogonal C" by blast
  let ?a = "a - setsum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C" by simp
  from fB aB C(1,2) have cC: "card ?C \<le> card (insert a B)"
    by (simp add: card_insert_if)
  { fix x k
    have th0: "\<And>(a::'a) b c. a - (b - c) = c + (a - b)"
      by (simp add: field_simps)
    have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x)) \<in> span C \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
      apply (simp only: scaleR_right_diff_distrib th0)
      apply (rule span_add_eq)
      apply (rule span_mul)
      apply (rule span_setsum[OF C(1)])
      apply clarify
      apply (rule span_mul)
      apply (rule span_superset)
      apply assumption
      done }
  then have SC: "span ?C = span (insert a B)"
    unfolding set_eq_iff span_breakdown_eq C(3)[symmetric] by auto
  { fix y assume yC: "y \<in> C"
    then have Cy: "C = insert y (C - {y})" by blast
    have fth: "finite (C - {y})" using C by simp
    have "orthogonal ?a y"
      unfolding orthogonal_def
      unfolding inner_diff inner_setsum_left diff_eq_0_iff_eq
      unfolding setsum_diff1' [OF `finite C` `y \<in> C`]
      apply (clarsimp simp add: inner_commute[of y a])
      apply (rule setsum_0')
      apply clarsimp
      apply (rule C(4)[unfolded pairwise_def orthogonal_def, rule_format])
      using `y \<in> C` by auto }
  with `pairwise orthogonal C` have CPO: "pairwise orthogonal ?C"
    by (rule pairwise_orthogonal_insert)
  from fC cC SC CPO have "?P (insert a B) ?C" by blast
  then show ?case by blast
qed

lemma orthogonal_basis_exists:
  fixes V :: "('a::euclidean_space) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and> (card B = dim V) \<and> pairwise orthogonal B"
proof -
  from basis_exists[of V] obtain B where
    B: "B \<subseteq> V" "independent B" "V \<subseteq> span B" "card B = dim V" by blast
  from B have fB: "finite B" "card B = dim V" using independent_bound by auto
  from basis_orthogonal[OF fB(1)] obtain C where
    C: "finite C" "card C \<le> card B" "span C = span B" "pairwise orthogonal C" by blast
  from C B have CSV: "C \<subseteq> span V" by (metis span_inc span_mono subset_trans)
  from span_mono[OF B(3)]  C have SVC: "span V \<subseteq> span C" by (simp add: span_span)
  from card_le_dim_spanning[OF CSV SVC C(1)] C(2,3) fB
  have iC: "independent C" by (simp add: dim_span)
  from C fB have "card C \<le> dim V" by simp
  moreover have "dim V \<le> card C" using span_card_ge_dim[OF CSV SVC C(1)]
    by (simp add: dim_span)
  ultimately have CdV: "card C = dim V" using C(1) by simp
  from C B CSV CdV iC show ?thesis by auto
qed

lemma span_eq: "span S = span T \<longleftrightarrow> S \<subseteq> span T \<and> T \<subseteq> span S"
  using span_inc[unfolded subset_eq] using span_mono[of T "span S"] span_mono[of S "span T"]
  by (auto simp add: span_span)

text {* Low-dimensional subset is in a hyperplane (weak orthogonal complement). *}

lemma span_not_univ_orthogonal:
  fixes S::"('a::euclidean_space) set"
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>(a::'a). a \<noteq>0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
proof -
  from sU obtain a where a: "a \<notin> span S" by blast
  from orthogonal_basis_exists obtain B where
    B: "independent B" "B \<subseteq> span S" "S \<subseteq> span B" "card B = dim S" "pairwise orthogonal B"
    by blast
  from B have fB: "finite B" "card B = dim S" using independent_bound by auto
  from span_mono[OF B(2)] span_mono[OF B(3)]
  have sSB: "span S = span B" by (simp add: span_span)
  let ?a = "a - setsum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B"
  have "setsum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B \<in> span S"
    unfolding sSB
    apply (rule span_setsum[OF fB(1)])
    apply clarsimp
    apply (rule span_mul)
    apply (rule span_superset)
    apply assumption
    done
  with a have a0:"?a  \<noteq> 0" by auto
  have "\<forall>x\<in>span B. ?a \<bullet> x = 0"
  proof (rule span_induct')
    show "subspace {x. ?a \<bullet> x = 0}"
      by (auto simp add: subspace_def inner_add)
  next
    { fix x assume x: "x \<in> B"
      from x have B': "B = insert x (B - {x})" by blast
      have fth: "finite (B - {x})" using fB by simp
      have "?a \<bullet> x = 0"
        apply (subst B') using fB fth
        unfolding setsum_clauses(2)[OF fth]
        apply simp unfolding inner_simps
        apply (clarsimp simp add: inner_add inner_setsum_left)
        apply (rule setsum_0', rule ballI)
        unfolding inner_commute
        apply (auto simp add: x field_simps
          intro: B(5)[unfolded pairwise_def orthogonal_def, rule_format])
        done }
    then show "\<forall>x \<in> B. ?a \<bullet> x = 0" by blast
  qed
  with a0 show ?thesis unfolding sSB by (auto intro: exI[where x="?a"])
qed

lemma span_not_univ_subset_hyperplane:
  assumes SU: "span S \<noteq> (UNIV ::('a::euclidean_space) set)"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using span_not_univ_orthogonal[OF SU] by auto

lemma lowdim_subset_hyperplane:
  fixes S::"('a::euclidean_space) set"
  assumes d: "dim S < DIM('a)"
  shows "\<exists>(a::'a). a  \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
proof -
  { assume "span S = UNIV"
    then have "dim (span S) = dim (UNIV :: ('a) set)" by simp
    then have "dim S = DIM('a)" by (simp add: dim_span dim_UNIV)
    with d have False by arith }
  then have th: "span S \<noteq> UNIV" by blast
  from span_not_univ_subset_hyperplane[OF th] show ?thesis .
qed

text {* We can extend a linear basis-basis injection to the whole set. *}

lemma linear_indep_image_lemma:
  assumes lf: "linear f"
    and fB: "finite B"
    and ifB: "independent (f ` B)"
    and fi: "inj_on f B"
    and xsB: "x \<in> span B"
    and fx: "f x = 0"
  shows "x = 0"
  using fB ifB fi xsB fx
proof (induct arbitrary: x rule: finite_induct[OF fB])
  case 1
  then show ?case by auto
next
  case (2 a b x)
  have fb: "finite b" using "2.prems" by simp
  have th0: "f ` b \<subseteq> f ` (insert a b)"
    apply (rule image_mono) by blast
  from independent_mono[ OF "2.prems"(2) th0]
  have ifb: "independent (f ` b)"  .
  have fib: "inj_on f b"
    apply (rule subset_inj_on [OF "2.prems"(3)])
    apply blast
    done
  from span_breakdown[of a "insert a b", simplified, OF "2.prems"(4)]
  obtain k where k: "x - k*\<^sub>R a \<in> span (b -{a})" by blast
  have "f (x - k*\<^sub>R a) \<in> span (f ` b)"
    unfolding span_linear_image[OF lf]
    apply (rule imageI)
    using k span_mono[of "b-{a}" b] apply blast
    done
  then have "f x - k*\<^sub>R f a \<in> span (f ` b)"
    by (simp add: linear_sub[OF lf] linear_cmul[OF lf])
  then have th: "-k *\<^sub>R f a \<in> span (f ` b)"
    using "2.prems"(5) by simp
  { assume k0: "k = 0"
    from k0 k have "x \<in> span (b -{a})" by simp
    then have "x \<in> span b" using span_mono[of "b-{a}" b]
      by blast }
  moreover
  { assume k0: "k \<noteq> 0"
    from span_mul[OF th, of "- 1/ k"] k0
    have th1: "f a \<in> span (f ` b)"
      by auto
    from inj_on_image_set_diff[OF "2.prems"(3), of "insert a b " "{a}", symmetric]
    have tha: "f ` insert a b - f ` {a} = f ` (insert a b - {a})" by blast
    from "2.prems"(2) [unfolded dependent_def bex_simps(8), rule_format, of "f a"]
    have "f a \<notin> span (f ` b)" using tha
      using "2.hyps"(2)
      "2.prems"(3) by auto
    with th1 have False by blast
    then have "x \<in> span b" by blast }
  ultimately have xsb: "x \<in> span b" by blast
  from "2.hyps"(3)[OF fb ifb fib xsb "2.prems"(5)]
  show "x = 0" .
qed

text {* We can extend a linear mapping from basis. *}

lemma linear_independent_extend_lemma:
  fixes f :: "'a::real_vector \<Rightarrow> 'b::real_vector"
  assumes fi: "finite B" and ib: "independent B"
  shows "\<exists>g. (\<forall>x\<in> span B. \<forall>y\<in> span B. g (x + y) = g x + g y)
           \<and> (\<forall>x\<in> span B. \<forall>c. g (c*\<^sub>R x) = c *\<^sub>R g x)
           \<and> (\<forall>x\<in> B. g x = f x)"
  using ib fi
proof (induct rule: finite_induct[OF fi])
  case 1
  then show ?case by auto
next
  case (2 a b)
  from "2.prems" "2.hyps" have ibf: "independent b" "finite b"
    by (simp_all add: independent_insert)
  from "2.hyps"(3)[OF ibf] obtain g where
    g: "\<forall>x\<in>span b. \<forall>y\<in>span b. g (x + y) = g x + g y"
    "\<forall>x\<in>span b. \<forall>c. g (c *\<^sub>R x) = c *\<^sub>R g x" "\<forall>x\<in>b. g x = f x" by blast
  let ?h = "\<lambda>z. SOME k. (z - k *\<^sub>R a) \<in> span b"
  { fix z assume z: "z \<in> span (insert a b)"
    have th0: "z - ?h z *\<^sub>R a \<in> span b"
      apply (rule someI_ex)
      unfolding span_breakdown_eq[symmetric]
      using z .
    { fix k assume k: "z - k *\<^sub>R a \<in> span b"
      have eq: "z - ?h z *\<^sub>R a - (z - k*\<^sub>R a) = (k - ?h z) *\<^sub>R a"
        by (simp add: field_simps scaleR_left_distrib [symmetric])
      from span_sub[OF th0 k]
      have khz: "(k - ?h z) *\<^sub>R a \<in> span b" by (simp add: eq)
      { assume "k \<noteq> ?h z" then have k0: "k - ?h z \<noteq> 0" by simp
        from k0 span_mul[OF khz, of "1 /(k - ?h z)"]
        have "a \<in> span b" by simp
        with "2.prems"(1) "2.hyps"(2) have False
          by (auto simp add: dependent_def)}
      then have "k = ?h z" by blast}
    with th0 have "z - ?h z *\<^sub>R a \<in> span b \<and> (\<forall>k. z - k *\<^sub>R a \<in> span b \<longrightarrow> k = ?h z)" by blast}
  note h = this
  let ?g = "\<lambda>z. ?h z *\<^sub>R f a + g (z - ?h z *\<^sub>R a)"
  { fix x y assume x: "x \<in> span (insert a b)" and y: "y \<in> span (insert a b)"
    have tha: "\<And>(x::'a) y a k l. (x + y) - (k + l) *\<^sub>R a = (x - k *\<^sub>R a) + (y - l *\<^sub>R a)"
      by (simp add: algebra_simps)
    have addh: "?h (x + y) = ?h x + ?h y"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (rule span_add[OF x y])
      unfolding tha
      by (metis span_add x y conjunct1[OF h, rule_format])
    have "?g (x + y) = ?g x + ?g y"
      unfolding addh tha
      g(1)[rule_format,OF conjunct1[OF h, OF x] conjunct1[OF h, OF y]]
      by (simp add: scaleR_left_distrib)}
  moreover
  { fix x:: "'a" and c:: real
    assume x: "x \<in> span (insert a b)"
    have tha: "\<And>(x::'a) c k a. c *\<^sub>R x - (c * k) *\<^sub>R a = c *\<^sub>R (x - k *\<^sub>R a)"
      by (simp add: algebra_simps)
    have hc: "?h (c *\<^sub>R x) = c * ?h x"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (metis span_mul x)
      apply (metis tha span_mul x conjunct1[OF h])
      done
    have "?g (c *\<^sub>R x) = c*\<^sub>R ?g x"
      unfolding hc tha g(2)[rule_format, OF conjunct1[OF h, OF x]]
      by (simp add: algebra_simps) }
  moreover
  { fix x assume x: "x \<in> (insert a b)"
    { assume xa: "x = a"
      have ha1: "1 = ?h a"
        apply (rule conjunct2[OF h, rule_format])
        apply (metis span_superset insertI1)
        using conjunct1[OF h, OF span_superset, OF insertI1]
        apply (auto simp add: span_0)
        done

      from xa ha1[symmetric] have "?g x = f x"
        apply simp
        using g(2)[rule_format, OF span_0, of 0]
        apply simp
        done }
    moreover
    { assume xb: "x \<in> b"
      have h0: "0 = ?h x"
        apply (rule conjunct2[OF h, rule_format])
        apply (metis  span_superset x)
        apply simp
        apply (metis span_superset xb)
        done
      have "?g x = f x"
        by (simp add: h0[symmetric] g(3)[rule_format, OF xb]) }
    ultimately have "?g x = f x" using x by blast }
  ultimately show ?case
    apply -
    apply (rule exI[where x="?g"])
    apply blast
    done
qed

lemma linear_independent_extend:
  assumes iB: "independent (B:: ('a::euclidean_space) set)"
  shows "\<exists>g. linear g \<and> (\<forall>x\<in>B. g x = f x)"
proof -
  from maximal_independent_subset_extend[of B UNIV] iB
  obtain C where C: "B \<subseteq> C" "independent C" "\<And>x. x \<in> span C" by auto

  from C(2) independent_bound[of C] linear_independent_extend_lemma[of C f]
  obtain g where g: "(\<forall>x\<in> span C. \<forall>y\<in> span C. g (x + y) = g x + g y)
           \<and> (\<forall>x\<in> span C. \<forall>c. g (c*\<^sub>R x) = c *\<^sub>R g x)
           \<and> (\<forall>x\<in> C. g x = f x)" by blast
  from g show ?thesis unfolding linear_def using C
    apply clarsimp
    apply blast
    done
qed

text {* Can construct an isomorphism between spaces of same dimension. *}

lemma card_le_inj:
  assumes fA: "finite A"
    and fB: "finite B"
    and c: "card A \<le> card B"
  shows "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A"
  using fA fB c
proof (induct arbitrary: B rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x s t)
  then show ?case
  proof (induct rule: finite_induct[OF "insert.prems"(1)])
    case 1
    then show ?case by simp
  next
    case (2 y t)
    from "2.prems"(1,2,5) "2.hyps"(1,2) have cst:"card s \<le> card t" by simp
    from "2.prems"(3) [OF "2.hyps"(1) cst] obtain f where
      f: "f ` s \<subseteq> t \<and> inj_on f s" by blast
    from f "2.prems"(2) "2.hyps"(2) show ?case
      apply -
      apply (rule exI[where x = "\<lambda>z. if z = x then y else f z"])
      apply (auto simp add: inj_on_def)
      done
  qed
qed

lemma card_subset_eq:
  assumes fB: "finite B"
    and AB: "A \<subseteq> B"
    and c: "card A = card B"
  shows "A = B"
proof -
  from fB AB have fA: "finite A" by (auto intro: finite_subset)
  from fA fB have fBA: "finite (B - A)" by auto
  have e: "A \<inter> (B - A) = {}" by blast
  have eq: "A \<union> (B - A) = B" using AB by blast
  from card_Un_disjoint[OF fA fBA e, unfolded eq c]
  have "card (B - A) = 0" by arith
  then have "B - A = {}" unfolding card_eq_0_iff using fA fB by simp
  with AB show "A = B" by blast
qed

lemma subspace_isomorphism:
  assumes s: "subspace (S:: ('a::euclidean_space) set)"
    and t: "subspace (T :: ('b::euclidean_space) set)"
    and d: "dim S = dim T"
  shows "\<exists>f. linear f \<and> f ` S = T \<and> inj_on f S"
proof -
  from basis_exists[of S] independent_bound obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" and fB: "finite B" by blast
  from basis_exists[of T] independent_bound obtain C where
    C: "C \<subseteq> T" "independent C" "T \<subseteq> span C" "card C = dim T" and fC: "finite C" by blast
  from B(4) C(4) card_le_inj[of B C] d obtain f where
    f: "f ` B \<subseteq> C" "inj_on f B" using `finite B` `finite C` by auto
  from linear_independent_extend[OF B(2)] obtain g where
    g: "linear g" "\<forall>x\<in> B. g x = f x" by blast
  from inj_on_iff_eq_card[OF fB, of f] f(2)
  have "card (f ` B) = card B" by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C" using d
    by simp
  have "g ` B = f ` B" using g(2)
    by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B" using f(2) g(2)
    by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  { fix x y assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> span B" and y': "y \<in> span B" by blast+
    from gxy have th0: "g (x - y) = 0" by (simp add: linear_sub[OF g(1)])
    have th1: "x - y \<in> span B" using x' y' by (metis span_sub)
    have "x=y" using g0[OF th1 th0] by simp }
  then have giS: "inj_on g S"
    unfolding inj_on_def by blast
  from span_subspace[OF B(1,3) s]
  have "g ` S = span (g ` B)" by (simp add: span_linear_image[OF g(1)])
  also have "\<dots> = span C" unfolding gBC ..
  also have "\<dots> = T" using span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS show ?thesis by blast
qed

text {* Linear functions are equal on a subspace if they are on a spanning set. *}

lemma subspace_kernel:
  assumes lf: "linear f"
  shows "subspace {x. f x = 0}"
  apply (simp add: subspace_def)
  apply (simp add: linear_add[OF lf] linear_cmul[OF lf] linear_0[OF lf])
  done

lemma linear_eq_0_span:
  assumes lf: "linear f" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> span B. f x = 0"
  using f0 subspace_kernel[OF lf]
  by (rule span_induct')

lemma linear_eq_0:
  assumes lf: "linear f"
    and SB: "S \<subseteq> span B"
    and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> S. f x = 0"
  by (metis linear_eq_0_span[OF lf] subset_eq SB f0)

lemma linear_eq:
  assumes lf: "linear f"
    and lg: "linear g"
    and S: "S \<subseteq> span B"
    and fg: "\<forall> x\<in> B. f x = g x"
  shows "\<forall>x\<in> S. f x = g x"
proof -
  let ?h = "\<lambda>x. f x - g x"
  from fg have fg': "\<forall>x\<in> B. ?h x = 0" by simp
  from linear_eq_0[OF linear_compose_sub[OF lf lg] S fg']
  show ?thesis by simp
qed

lemma linear_eq_stdbasis:
  assumes lf: "linear (f::'a::euclidean_space \<Rightarrow> _)"
    and lg: "linear g"
    and fg: "\<forall>i<DIM('a::euclidean_space). f (basis i) = g(basis i)"
  shows "f = g"
proof -
  let ?U = "{..<DIM('a)}"
  let ?I = "(basis::nat=>'a) ` {..<DIM('a)}"
  { fix x assume x: "x \<in> (UNIV :: 'a set)"
    from equalityD2[OF span_basis'[where 'a='a]]
    have IU: " (UNIV :: 'a set) \<subseteq> span ?I" by blast
    have "f x = g x"
      apply (rule linear_eq[OF lf lg IU,rule_format])
      using fg x apply auto
      done
  } then show ?thesis by auto
qed

text {* Similar results for bilinear functions. *}

lemma bilinear_eq:
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and SB: "S \<subseteq> span B" and TC: "T \<subseteq> span C"
    and fg: "\<forall>x\<in> B. \<forall>y\<in> C. f x y = g x y"
  shows "\<forall>x\<in>S. \<forall>y\<in>T. f x y = g x y "
proof -
  let ?P = "{x. \<forall>y\<in> span C. f x y = g x y}"
  from bf bg have sp: "subspace ?P"
    unfolding bilinear_def linear_def subspace_def bf bg
    by (auto simp add: span_0 bilinear_lzero[OF bf] bilinear_lzero[OF bg] span_add Ball_def
      intro: bilinear_ladd[OF bf])

  have "\<forall>x \<in> span B. \<forall>y\<in> span C. f x y = g x y"
    apply (rule span_induct' [OF _ sp])
    apply (rule ballI)
    apply (rule span_induct')
    apply (simp add: fg)
    apply (auto simp add: subspace_def)
    using bf bg unfolding bilinear_def linear_def
    apply (auto simp add: span_0 bilinear_rzero[OF bf] bilinear_rzero[OF bg] span_add Ball_def
      intro: bilinear_ladd[OF bf])
    done
  then show ?thesis using SB TC by auto
qed

lemma bilinear_eq_stdbasis:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> _"
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and fg: "\<forall>i<DIM('a). \<forall>j<DIM('b). f (basis i) (basis j) = g (basis i) (basis j)"
  shows "f = g"
proof -
  from fg have th: "\<forall>x \<in> (basis ` {..<DIM('a)}). \<forall>y\<in> (basis ` {..<DIM('b)}). f x y = g x y"
    by blast
  from bilinear_eq[OF bf bg equalityD2[OF span_basis'] equalityD2[OF span_basis'] th]
  show ?thesis by blast
qed

text {* Detailed theorems about left and right invertibility in general case. *}

lemma linear_injective_left_inverse:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes lf: "linear f" and fi: "inj f"
  shows "\<exists>g. linear g \<and> g o f = id"
proof -
  from linear_independent_extend[OF independent_injective_image, OF independent_basis, OF lf fi]
  obtain h:: "'b => 'a" where
    h: "linear h" "\<forall>x \<in> f ` basis ` {..<DIM('a)}. h x = inv f x" by blast
  from h(2) have th: "\<forall>i<DIM('a). (h \<circ> f) (basis i) = id (basis i)"
    using inv_o_cancel[OF fi, unfolded fun_eq_iff id_def o_def]
    by auto

  from linear_eq_stdbasis[OF linear_compose[OF lf h(1)] linear_id th]
  have "h o f = id" .
  then show ?thesis using h(1) by blast
qed

lemma linear_surjective_right_inverse:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes lf: "linear f" and sf: "surj f"
  shows "\<exists>g. linear g \<and> f o g = id"
proof -
  from linear_independent_extend[OF independent_basis[where 'a='b],of "inv f"]
  obtain h:: "'b \<Rightarrow> 'a" where
    h: "linear h" "\<forall> x\<in> basis ` {..<DIM('b)}. h x = inv f x" by blast
  from h(2)
  have th: "\<forall>i<DIM('b). (f o h) (basis i) = id (basis i)"
    using sf by(auto simp add: surj_iff_all)
  from linear_eq_stdbasis[OF linear_compose[OF h(1) lf] linear_id th]
  have "f o h = id" .
  then show ?thesis using h(1) by blast
qed

text {* An injective map @{typ "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"} is also surjective. *}

lemma linear_injective_imp_surjective:
  fixes f::"'a::euclidean_space => 'a::euclidean_space"
  assumes lf: "linear f" and fi: "inj f"
  shows "surj f"
proof -
  let ?U = "UNIV :: 'a set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" "card B = dim ?U"
    by blast
  from B(4) have d: "dim ?U = card B" by simp
  have th: "?U \<subseteq> span (f ` B)"
    apply (rule card_ge_dim_independent)
    apply blast
    apply (rule independent_injective_image[OF B(2) lf fi])
    apply (rule order_eq_refl)
    apply (rule sym)
    unfolding d
    apply (rule card_image)
    apply (rule subset_inj_on[OF fi])
    apply blast
    done
  from th show ?thesis
    unfolding span_linear_image[OF lf] surj_def
    using B(3) by blast
qed

text {* And vice versa. *}

lemma surjective_iff_injective_gen:
  assumes fS: "finite S"
    and fT: "finite T"
    and c: "card S = card T"
    and ST: "f ` S \<subseteq> T"
  shows "(\<forall>y \<in> T. \<exists>x \<in> S. f x = y) \<longleftrightarrow> inj_on f S" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  { assume h: "?lhs"
    { fix x y
      assume x: "x \<in> S" and y: "y \<in> S" and f: "f x = f y"
      from x fS have S0: "card S \<noteq> 0" by auto
      { assume xy: "x \<noteq> y"
        have th: "card S \<le> card (f ` (S - {y}))"
          unfolding c
          apply (rule card_mono)
          apply (rule finite_imageI)
          using fS apply simp
          using h xy x y f unfolding subset_eq image_iff
          apply auto
          apply (case_tac "xa = f x")
          apply (rule bexI[where x=x])
          apply auto
          done
        also have " \<dots> \<le> card (S -{y})"
          apply (rule card_image_le)
          using fS by simp
        also have "\<dots> \<le> card S - 1" using y fS by simp
        finally have False  using S0 by arith }
      then have "x = y" by blast}
    then have ?rhs unfolding inj_on_def by blast}
  moreover
  { assume h: ?rhs
    have "f ` S = T"
      apply (rule card_subset_eq[OF fT ST])
      unfolding card_image[OF h] using c .
    then have ?lhs by blast}
  ultimately show ?thesis by blast
qed

lemma linear_surjective_imp_injective:
  fixes f::"'a::euclidean_space => 'a::euclidean_space"
  assumes lf: "linear f" and sf: "surj f"
  shows "inj f"
proof -
  let ?U = "UNIV :: 'a set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" and d: "card B = dim ?U"
    by blast
  { fix x assume x: "x \<in> span B" and fx: "f x = 0"
    from B(2) have fB: "finite B" using independent_bound by auto
    have fBi: "independent (f ` B)"
      apply (rule card_le_dim_spanning[of "f ` B" ?U])
      apply blast
      using sf B(3)
      unfolding span_linear_image[OF lf] surj_def subset_eq image_iff
      apply blast
      using fB apply blast
      unfolding d[symmetric]
      apply (rule card_image_le)
      apply (rule fB)
      done
    have th0: "dim ?U \<le> card (f ` B)"
      apply (rule span_card_ge_dim)
      apply blast
      unfolding span_linear_image[OF lf]
      apply (rule subset_trans[where B = "f ` UNIV"])
      using sf unfolding surj_def apply blast
      apply (rule image_mono)
      apply (rule B(3))
      apply (metis finite_imageI fB)
      done

    moreover have "card (f ` B) \<le> card B"
      by (rule card_image_le, rule fB)
    ultimately have th1: "card B = card (f ` B)" unfolding d by arith
    have fiB: "inj_on f B"
      unfolding surjective_iff_injective_gen[OF fB finite_imageI[OF fB] th1 subset_refl, symmetric]
      by blast
    from linear_indep_image_lemma[OF lf fB fBi fiB x] fx
    have "x = 0" by blast}
  note th = this
  from th show ?thesis unfolding linear_injective_0[OF lf]
    using B(3) by blast
qed

text {* Hence either is enough for isomorphism. *}

lemma left_right_inverse_eq:
  assumes fg: "f o g = id" and gh: "g o h = id"
  shows "f = h"
proof -
  have "f = f o (g o h)" unfolding gh by simp
  also have "\<dots> = (f o g) o h" by (simp add: o_assoc)
  finally show "f = h" unfolding fg by simp
qed

lemma isomorphism_expand:
  "f o g = id \<and> g o f = id \<longleftrightarrow> (\<forall>x. f(g x) = x) \<and> (\<forall>x. g(f x) = x)"
  by (simp add: fun_eq_iff o_def id_def)

lemma linear_injective_isomorphism:
  fixes f::"'a::euclidean_space => 'a::euclidean_space"
  assumes lf: "linear f" and fi: "inj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  unfolding isomorphism_expand[symmetric]
  using linear_surjective_right_inverse[OF lf linear_injective_imp_surjective[OF lf fi]]
    linear_injective_left_inverse[OF lf fi]
  by (metis left_right_inverse_eq)

lemma linear_surjective_isomorphism: fixes f::"'a::euclidean_space => 'a::euclidean_space"
  assumes lf: "linear f" and sf: "surj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  unfolding isomorphism_expand[symmetric]
  using linear_surjective_right_inverse[OF lf sf]
    linear_injective_left_inverse[OF lf linear_surjective_imp_injective[OF lf sf]]
  by (metis left_right_inverse_eq)

text {* Left and right inverses are the same for @{typ "'a::euclidean_space => 'a::euclidean_space"}. *}

lemma linear_inverse_left:
  fixes f::"'a::euclidean_space => 'a::euclidean_space"
  assumes lf: "linear f" and lf': "linear f'"
  shows "f o f' = id \<longleftrightarrow> f' o f = id"
proof -
  { fix f f':: "'a => 'a"
    assume lf: "linear f" "linear f'" and f: "f o f' = id"
    from f have sf: "surj f"
      apply (auto simp add: o_def id_def surj_def)
      apply metis
      done
    from linear_surjective_isomorphism[OF lf(1) sf] lf f
    have "f' o f = id" unfolding fun_eq_iff o_def id_def
      by metis }
  then show ?thesis using lf lf' by metis
qed

text {* Moreover, a one-sided inverse is automatically linear. *}

lemma left_inverse_linear:
  fixes f::"'a::euclidean_space => 'a::euclidean_space"
  assumes lf: "linear f" and gf: "g o f = id"
  shows "linear g"
proof -
  from gf have fi: "inj f"
    apply (auto simp add: inj_on_def o_def id_def fun_eq_iff)
    apply metis
    done
  from linear_injective_isomorphism[OF lf fi]
  obtain h:: "'a \<Rightarrow> 'a" where
    h: "linear h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x" by blast
  have "h = g"
    apply (rule ext) using gf h(2,3)
    apply (simp add: o_def id_def fun_eq_iff)
    apply metis
    done
  with h(1) show ?thesis by blast
qed


subsection {* Infinity norm *}

definition "infnorm (x::'a::euclidean_space) = Sup {abs(x$$i) |i. i<DIM('a)}"

lemma numseg_dimindex_nonempty: "\<exists>i. i \<in> (UNIV :: 'n set)"
  by auto

lemma infnorm_set_image:
  "{abs((x::'a::euclidean_space)$$i) |i. i<DIM('a)} =
  (\<lambda>i. abs(x$$i)) ` {..<DIM('a)}" by blast

lemma infnorm_set_lemma:
  shows "finite {abs((x::'a::euclidean_space)$$i) |i. i<DIM('a)}"
  and "{abs(x$$i) |i. i<DIM('a::euclidean_space)} \<noteq> {}"
  unfolding infnorm_set_image
  by auto

lemma infnorm_pos_le: "0 \<le> infnorm (x::'a::euclidean_space)"
  unfolding infnorm_def
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma]
  unfolding infnorm_set_image
  by auto

lemma infnorm_triangle: "infnorm ((x::'a::euclidean_space) + y) \<le> infnorm x + infnorm y"
proof -
  have th: "\<And>x y (z::real). x - y <= z \<longleftrightarrow> x - z <= y" by arith
  have th1: "\<And>S f. f ` S = { f i| i. i \<in> S}" by blast
  have th2: "\<And>x (y::real). abs(x + y) - abs(x) <= abs(y)" by arith
  have *:"\<And>i. i \<in> {..<DIM('a)} \<longleftrightarrow> i <DIM('a)" by auto
  show ?thesis
  unfolding infnorm_def unfolding  Sup_finite_le_iff[ OF infnorm_set_lemma[where 'a='a]]
  apply (subst diff_le_eq[symmetric])
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma]
  unfolding infnorm_set_image bex_simps
  apply (subst th)
  unfolding th1 *
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma[where 'a='a]]
  unfolding infnorm_set_image ball_simps bex_simps
  unfolding euclidean_simps apply (metis th2)
  done
qed

lemma infnorm_eq_0: "infnorm x = 0 \<longleftrightarrow> (x::_::euclidean_space) = 0"
proof -
  have "infnorm x <= 0 \<longleftrightarrow> x = 0"
    unfolding infnorm_def
    unfolding Sup_finite_le_iff[OF infnorm_set_lemma]
    unfolding infnorm_set_image ball_simps
    apply (subst (1) euclidean_eq)
    apply auto
    done
  then show ?thesis using infnorm_pos_le[of x] by simp
qed

lemma infnorm_0: "infnorm 0 = 0"
  by (simp add: infnorm_eq_0)

lemma infnorm_neg: "infnorm (- x) = infnorm x"
  unfolding infnorm_def
  apply (rule cong[of "Sup" "Sup"])
  apply blast
  apply auto
  done

lemma infnorm_sub: "infnorm (x - y) = infnorm (y - x)"
proof -
  have "y - x = - (x - y)" by simp
  then show ?thesis  by (metis infnorm_neg)
qed

lemma real_abs_sub_infnorm: "\<bar> infnorm x - infnorm y\<bar> \<le> infnorm (x - y)"
proof -
  have th: "\<And>(nx::real) n ny. nx <= n + ny \<Longrightarrow> ny <= n + nx ==> \<bar>nx - ny\<bar> <= n"
    by arith
  from infnorm_triangle[of "x - y" " y"] infnorm_triangle[of "x - y" "-x"]
  have ths: "infnorm x \<le> infnorm (x - y) + infnorm y"
    "infnorm y \<le> infnorm (x - y) + infnorm x"
    by (simp_all add: field_simps infnorm_neg)
  from th[OF ths]  show ?thesis .
qed

lemma real_abs_infnorm: " \<bar>infnorm x\<bar> = infnorm x"
  using infnorm_pos_le[of x] by arith

lemma component_le_infnorm: "\<bar>x$$i\<bar> \<le> infnorm (x::'a::euclidean_space)"
proof (cases "i<DIM('a)")
  case False
  then show ?thesis using infnorm_pos_le by auto
next
  case True
  let ?U = "{..<DIM('a)}"
  let ?S = "{\<bar>x$$i\<bar> |i. i<DIM('a)}"
  have fS: "finite ?S" unfolding image_Collect[symmetric]
    apply (rule finite_imageI) apply simp done
  have S0: "?S \<noteq> {}" by blast
  have th1: "\<And>S f. f ` S = { f i| i. i \<in> S}" by blast
  show ?thesis unfolding infnorm_def  
    apply(subst Sup_finite_ge_iff) using Sup_finite_in[OF fS S0]
    using infnorm_set_image using True apply auto
    done
qed

lemma infnorm_mul_lemma: "infnorm(a *\<^sub>R x) <= \<bar>a\<bar> * infnorm x"
  apply (subst infnorm_def)
  unfolding Sup_finite_le_iff[OF infnorm_set_lemma]
  unfolding infnorm_set_image ball_simps euclidean_component_scaleR abs_mult
  using component_le_infnorm[of x]
  apply (auto intro: mult_mono)
  done

lemma infnorm_mul: "infnorm(a *\<^sub>R x) = abs a * infnorm x"
proof -
  { assume a0: "a = 0" then have ?thesis by (simp add: infnorm_0) }
  moreover
  { assume a0: "a \<noteq> 0"
    from a0 have th: "(1/a) *\<^sub>R (a *\<^sub>R x) = x" by simp
    from a0 have ap: "\<bar>a\<bar> > 0" by arith
    from infnorm_mul_lemma[of "1/a" "a *\<^sub>R x"]
    have "infnorm x \<le> 1/\<bar>a\<bar> * infnorm (a*\<^sub>R x)"
      unfolding th by simp
    with ap have "\<bar>a\<bar> * infnorm x \<le> \<bar>a\<bar> * (1/\<bar>a\<bar> * infnorm (a *\<^sub>R x))" by (simp add: field_simps)
    then have "\<bar>a\<bar> * infnorm x \<le> infnorm (a*\<^sub>R x)"
      using ap by (simp add: field_simps)
    with infnorm_mul_lemma[of a x] have ?thesis by arith }
  ultimately show ?thesis by blast
qed

lemma infnorm_pos_lt: "infnorm x > 0 \<longleftrightarrow> x \<noteq> 0"
  using infnorm_pos_le[of x] infnorm_eq_0[of x] by arith

text {* Prove that it differs only up to a bound from Euclidean norm. *}

lemma infnorm_le_norm: "infnorm x \<le> norm x"
  unfolding infnorm_def Sup_finite_le_iff[OF infnorm_set_lemma]
  unfolding infnorm_set_image  ball_simps
  by (metis component_le_norm)

lemma norm_le_infnorm: "norm(x) <= sqrt(real DIM('a)) * infnorm(x::'a::euclidean_space)"
proof -
  let ?d = "DIM('a)"
  have "real ?d \<ge> 0" by simp
  then have d2: "(sqrt (real ?d))^2 = real ?d"
    by (auto intro: real_sqrt_pow2)
  have th: "sqrt (real ?d) * infnorm x \<ge> 0"
    by (simp add: zero_le_mult_iff infnorm_pos_le)
  have th1: "x \<bullet> x \<le> (sqrt (real ?d) * infnorm x)^2"
    unfolding power_mult_distrib d2
    unfolding real_of_nat_def apply(subst euclidean_inner)
    apply (subst power2_abs[symmetric])
    apply (rule order_trans[OF setsum_bounded[where K="\<bar>infnorm x\<bar>\<twosuperior>"]])
    apply (auto simp add: power2_eq_square[symmetric])
    apply (subst power2_abs[symmetric])
    apply (rule power_mono)
    unfolding infnorm_def  Sup_finite_ge_iff[OF infnorm_set_lemma]
    unfolding infnorm_set_image bex_simps
    apply (rule_tac x=i in bexI)
    apply auto
    done
  from real_le_lsqrt[OF inner_ge_zero th th1]
  show ?thesis unfolding norm_eq_sqrt_inner id_def .
qed

lemma tendsto_infnorm [tendsto_intros]:
  assumes "(f ---> a) F"
  shows "((\<lambda>x. infnorm (f x)) ---> infnorm a) F"
proof (rule tendsto_compose [OF LIM_I assms])
  fix r :: real assume "0 < r"
  then show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (infnorm x - infnorm a) < r"
    by (metis real_norm_def le_less_trans real_abs_sub_infnorm infnorm_le_norm)
qed

text {* Equality in Cauchy-Schwarz and triangle inequalities. *}

lemma norm_cauchy_schwarz_eq: "x \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  { assume h: "x = 0"
    then have ?thesis by simp }
  moreover
  { assume h: "y = 0"
    then have ?thesis by simp }
  moreover
  { assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    from inner_eq_zero_iff[of "norm y *\<^sub>R x - norm x *\<^sub>R y"]
    have "?rhs \<longleftrightarrow>
      (norm y * (norm y * norm x * norm x - norm x * (x \<bullet> y)) -
        norm x * (norm y * (y \<bullet> x) - norm x * norm y * norm y) =  0)"
      using x y
      unfolding inner_simps
      unfolding power2_norm_eq_inner[symmetric] power2_eq_square diff_eq_0_iff_eq
      apply (simp add: inner_commute)
      apply (simp add: field_simps)
      apply metis
      done
    also have "\<dots> \<longleftrightarrow> (2 * norm x * norm y * (norm x * norm y - x \<bullet> y) = 0)" using x y
      by (simp add: field_simps inner_commute)
    also have "\<dots> \<longleftrightarrow> ?lhs" using x y
      apply simp
      apply metis
      done
    finally have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_abs_eq:
  "abs(x \<bullet> y) = norm x * norm y \<longleftrightarrow>
    norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm(x) *\<^sub>R y = - norm y *\<^sub>R x" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have th: "\<And>(x::real) a. a \<ge> 0 \<Longrightarrow> abs x = a \<longleftrightarrow> x = a \<or> x = - a" by arith
  have "?rhs \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm (- x) *\<^sub>R y = norm y *\<^sub>R (- x)"
    by simp
  also have "\<dots> \<longleftrightarrow>(x \<bullet> y = norm x * norm y \<or>
     (-x) \<bullet> y = norm x * norm y)"
    unfolding norm_cauchy_schwarz_eq[symmetric]
    unfolding norm_minus_cancel norm_scaleR ..
  also have "\<dots> \<longleftrightarrow> ?lhs"
    unfolding th[OF mult_nonneg_nonneg, OF norm_ge_zero[of x] norm_ge_zero[of y]] inner_simps by auto
  finally show ?thesis ..
qed

lemma norm_triangle_eq:
  fixes x y :: "'a::real_inner"
  shows "norm(x + y) = norm x + norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
proof -
  { assume x: "x = 0 \<or> y = 0"
    then have ?thesis by (cases "x = 0") simp_all }
  moreover
  { assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    then have "norm x \<noteq> 0" "norm y \<noteq> 0"
      by simp_all
    then have n: "norm x > 0" "norm y > 0"
      using norm_ge_zero[of x] norm_ge_zero[of y] by arith+
    have th: "\<And>(a::real) b c. a + b + c \<noteq> 0 ==> (a = b + c \<longleftrightarrow> a^2 = (b + c)^2)"
      by algebra
    have "norm(x + y) = norm x + norm y \<longleftrightarrow> norm(x + y)^ 2 = (norm x + norm y) ^2"
      apply (rule th) using n norm_ge_zero[of "x + y"]
      apply arith
      done
    also have "\<dots> \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
      unfolding norm_cauchy_schwarz_eq[symmetric]
      unfolding power2_norm_eq_inner inner_simps
      by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square inner_commute field_simps)
    finally have ?thesis .}
  ultimately show ?thesis by blast
qed


subsection {* Collinearity *}

definition collinear :: "'a::real_vector set \<Rightarrow> bool"
  where "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u)"

lemma collinear_empty:  "collinear {}" by (simp add: collinear_def)

lemma collinear_sing: "collinear {x}"
  by (simp add: collinear_def)

lemma collinear_2: "collinear {x, y}"
  apply (simp add: collinear_def)
  apply (rule exI[where x="x - y"])
  apply auto
  apply (rule exI[where x=1], simp)
  apply (rule exI[where x="- 1"], simp)
  done

lemma collinear_lemma:
  "collinear {0,x,y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  { assume "x=0 \<or> y = 0"
    then have ?thesis by (cases "x = 0") (simp_all add: collinear_2 insert_commute) }
  moreover
  { assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    { assume h: "?lhs"
      then obtain u where u: "\<forall> x\<in> {0,x,y}. \<forall>y\<in> {0,x,y}. \<exists>c. x - y = c *\<^sub>R u"
        unfolding collinear_def by blast
      from u[rule_format, of x 0] u[rule_format, of y 0]
      obtain cx and cy where
        cx: "x = cx *\<^sub>R u" and cy: "y = cy *\<^sub>R u"
        by auto
      from cx x have cx0: "cx \<noteq> 0" by auto
      from cy y have cy0: "cy \<noteq> 0" by auto
      let ?d = "cy / cx"
      from cx cy cx0 have "y = ?d *\<^sub>R x"
        by simp
      then have ?rhs using x y by blast }
    moreover
    { assume h: "?rhs"
      then obtain c where c: "y = c *\<^sub>R x" using x y by blast
      have ?lhs unfolding collinear_def c
        apply (rule exI[where x=x])
        apply auto
        apply (rule exI[where x="- 1"], simp)
        apply (rule exI[where x= "-c"], simp)
        apply (rule exI[where x=1], simp)
        apply (rule exI[where x="1 - c"], simp add: scaleR_left_diff_distrib)
        apply (rule exI[where x="c - 1"], simp add: scaleR_left_diff_distrib)
        done }
    ultimately have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_equal: "abs(x \<bullet> y) = norm x * norm y \<longleftrightarrow> collinear {0,x,y}"
  unfolding norm_cauchy_schwarz_abs_eq
  apply (cases "x=0", simp_all add: collinear_2)
  apply (cases "y=0", simp_all add: collinear_2 insert_commute)
  unfolding collinear_lemma
  apply simp
  apply (subgoal_tac "norm x \<noteq> 0")
  apply (subgoal_tac "norm y \<noteq> 0")
  apply (rule iffI)
  apply (cases "norm x *\<^sub>R y = norm y *\<^sub>R x")
  apply (rule exI[where x="(1/norm x) * norm y"])
  apply (drule sym)
  unfolding scaleR_scaleR[symmetric]
  apply (simp add: field_simps)
  apply (rule exI[where x="(1/norm x) * - norm y"])
  apply clarify
  apply (drule sym)
  unfolding scaleR_scaleR[symmetric]
  apply (simp add: field_simps)
  apply (erule exE)
  apply (erule ssubst)
  unfolding scaleR_scaleR
  unfolding norm_scaleR
  apply (subgoal_tac "norm x * c = \<bar>c\<bar> * norm x \<or> norm x * c = - \<bar>c\<bar> * norm x")
  apply (case_tac "c <= 0", simp add: field_simps)
  apply (simp add: field_simps)
  apply (case_tac "c <= 0", simp add: field_simps)
  apply (simp add: field_simps)
  apply simp
  apply simp
  done


subsection {* An ordering on euclidean spaces that will allow us to talk about intervals *}

class ordered_euclidean_space = ord + euclidean_space +
  assumes eucl_le: "x \<le> y \<longleftrightarrow> (\<forall>i < DIM('a). x $$ i \<le> y $$ i)"
    and eucl_less: "x < y \<longleftrightarrow> (\<forall>i < DIM('a). x $$ i < y $$ i)"

lemma eucl_less_not_refl[simp, intro!]: "\<not> x < (x::'a::ordered_euclidean_space)"
  unfolding eucl_less[where 'a='a] by auto

lemma euclidean_trans[trans]:
  fixes x y z :: "'a::ordered_euclidean_space"
  shows "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
    and "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
    and "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  unfolding eucl_less[where 'a='a] eucl_le[where 'a='a]
  by (fast intro: less_trans, fast intro: le_less_trans,
    fast intro: order_trans)

lemma basis_real_range: "basis ` {..<1} = {1::real}" by auto

instance real::ordered_euclidean_space
  by default (auto simp add: euclidean_component_def)

lemma Eucl_real_simps[simp]:
  "(x::real) $$ 0 = x"
  "(\<chi>\<chi> i. f i) = ((f 0)::real)"
  "\<And>i. i > 0 \<Longrightarrow> x $$ i = 0"
  defer apply(subst euclidean_eq) apply safe
  unfolding euclidean_lambda_beta'
  unfolding euclidean_component_def apply auto
  done

lemma complex_basis[simp]:
  shows "basis 0 = (1::complex)" and "basis 1 = ii" and "basis (Suc 0) = ii"
  unfolding basis_complex_def by auto

lemma DIM_prod[simp]: "DIM('a \<times> 'b) = DIM('b::euclidean_space) + DIM('a::euclidean_space)"
  (* FIXME: why this orientation? Why not "DIM('a) + DIM('b)" ? *)
  unfolding dimension_prod_def by (rule add_commute)

instantiation prod :: (ordered_euclidean_space, ordered_euclidean_space) ordered_euclidean_space
begin

definition "x \<le> (y::('a\<times>'b)) \<longleftrightarrow> (\<forall>i<DIM('a\<times>'b). x $$ i \<le> y $$ i)"
definition "x < (y::('a\<times>'b)) \<longleftrightarrow> (\<forall>i<DIM('a\<times>'b). x $$ i < y $$ i)"

instance
  by default (auto simp: less_prod_def less_eq_prod_def)

end

end
