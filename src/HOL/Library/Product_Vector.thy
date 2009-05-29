(*  Title:      HOL/Library/Product_Vector.thy
    Author:     Brian Huffman
*)

header {* Cartesian Products as Vector Spaces *}

theory Product_Vector
imports Inner_Product Product_plus
begin

subsection {* Product is a real vector space *}

instantiation "*" :: (real_vector, real_vector) real_vector
begin

definition scaleR_prod_def:
  "scaleR r A = (scaleR r (fst A), scaleR r (snd A))"

lemma fst_scaleR [simp]: "fst (scaleR r A) = scaleR r (fst A)"
  unfolding scaleR_prod_def by simp

lemma snd_scaleR [simp]: "snd (scaleR r A) = scaleR r (snd A)"
  unfolding scaleR_prod_def by simp

lemma scaleR_Pair [simp]: "scaleR r (a, b) = (scaleR r a, scaleR r b)"
  unfolding scaleR_prod_def by simp

instance proof
  fix a b :: real and x y :: "'a \<times> 'b"
  show "scaleR a (x + y) = scaleR a x + scaleR a y"
    by (simp add: expand_prod_eq scaleR_right_distrib)
  show "scaleR (a + b) x = scaleR a x + scaleR b x"
    by (simp add: expand_prod_eq scaleR_left_distrib)
  show "scaleR a (scaleR b x) = scaleR (a * b) x"
    by (simp add: expand_prod_eq)
  show "scaleR 1 x = x"
    by (simp add: expand_prod_eq)
qed

end

subsection {* Product is a normed vector space *}

instantiation
  "*" :: (real_normed_vector, real_normed_vector) real_normed_vector
begin

definition norm_prod_def:
  "norm x = sqrt ((norm (fst x))\<twosuperior> + (norm (snd x))\<twosuperior>)"

definition sgn_prod_def:
  "sgn (x::'a \<times> 'b) = scaleR (inverse (norm x)) x"

definition dist_prod_def:
  "dist (x::'a \<times> 'b) y = norm (x - y)"

lemma norm_Pair: "norm (a, b) = sqrt ((norm a)\<twosuperior> + (norm b)\<twosuperior>)"
  unfolding norm_prod_def by simp

instance proof
  fix r :: real and x y :: "'a \<times> 'b"
  show "0 \<le> norm x"
    unfolding norm_prod_def by simp
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_prod_def
    by (simp add: expand_prod_eq)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_prod_def
    apply (rule order_trans [OF _ real_sqrt_sum_squares_triangle_ineq])
    apply (simp add: add_mono power_mono norm_triangle_ineq)
    done
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    unfolding norm_prod_def
    apply (simp add: norm_scaleR power_mult_distrib)
    apply (simp add: right_distrib [symmetric])
    apply (simp add: real_sqrt_mult_distrib)
    done
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule sgn_prod_def)
  show "dist x y = norm (x - y)"
    by (rule dist_prod_def)
qed

end

subsection {* Product is an inner product space *}

instantiation "*" :: (real_inner, real_inner) real_inner
begin

definition inner_prod_def:
  "inner x y = inner (fst x) (fst y) + inner (snd x) (snd y)"

lemma inner_Pair [simp]: "inner (a, b) (c, d) = inner a c + inner b d"
  unfolding inner_prod_def by simp

instance proof
  fix r :: real
  fix x y z :: "'a::real_inner * 'b::real_inner"
  show "inner x y = inner y x"
    unfolding inner_prod_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_prod_def
    by (simp add: inner_left_distrib)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_prod_def
    by (simp add: inner_scaleR_left right_distrib)
  show "0 \<le> inner x x"
    unfolding inner_prod_def
    by (intro add_nonneg_nonneg inner_ge_zero)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_prod_def expand_prod_eq
    by (simp add: add_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding norm_prod_def inner_prod_def
    by (simp add: power2_norm_eq_inner)
qed

end

subsection {* Pair operations are linear and continuous *}

interpretation fst: bounded_linear fst
  apply (unfold_locales)
  apply (rule fst_add)
  apply (rule fst_scaleR)
  apply (rule_tac x="1" in exI, simp add: norm_Pair)
  done

interpretation snd: bounded_linear snd
  apply (unfold_locales)
  apply (rule snd_add)
  apply (rule snd_scaleR)
  apply (rule_tac x="1" in exI, simp add: norm_Pair)
  done

text {* TODO: move to NthRoot *}
lemma sqrt_add_le_add_sqrt:
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "sqrt (x + y) \<le> sqrt x + sqrt y"
apply (rule power2_le_imp_le)
apply (simp add: real_sum_squared_expand add_nonneg_nonneg x y)
apply (simp add: mult_nonneg_nonneg x y)
apply (simp add: add_nonneg_nonneg x y)
done

lemma bounded_linear_Pair:
  assumes f: "bounded_linear f"
  assumes g: "bounded_linear g"
  shows "bounded_linear (\<lambda>x. (f x, g x))"
proof
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  fix x y and r :: real
  show "(f (x + y), g (x + y)) = (f x, g x) + (f y, g y)"
    by (simp add: f.add g.add)
  show "(f (r *\<^sub>R x), g (r *\<^sub>R x)) = r *\<^sub>R (f x, g x)"
    by (simp add: f.scaleR g.scaleR)
  obtain Kf where "0 < Kf" and norm_f: "\<And>x. norm (f x) \<le> norm x * Kf"
    using f.pos_bounded by fast
  obtain Kg where "0 < Kg" and norm_g: "\<And>x. norm (g x) \<le> norm x * Kg"
    using g.pos_bounded by fast
  have "\<forall>x. norm (f x, g x) \<le> norm x * (Kf + Kg)"
    apply (rule allI)
    apply (simp add: norm_Pair)
    apply (rule order_trans [OF sqrt_add_le_add_sqrt], simp, simp)
    apply (simp add: right_distrib)
    apply (rule add_mono [OF norm_f norm_g])
    done
  then show "\<exists>K. \<forall>x. norm (f x, g x) \<le> norm x * K" ..
qed

text {*
  TODO: The next three proofs are nearly identical to each other.
  Is there a good way to factor out the common parts?
*}

lemma LIMSEQ_Pair:
  assumes "X ----> a" and "Y ----> b"
  shows "(\<lambda>n. (X n, Y n)) ----> (a, b)"
proof (rule LIMSEQ_I)
  fix r :: real assume "0 < r"
  then have "0 < r / sqrt 2" (is "0 < ?s")
    by (simp add: divide_pos_pos)
  obtain M where M: "\<forall>n\<ge>M. norm (X n - a) < ?s"
    using LIMSEQ_D [OF `X ----> a` `0 < ?s`] ..
  obtain N where N: "\<forall>n\<ge>N. norm (Y n - b) < ?s"
    using LIMSEQ_D [OF `Y ----> b` `0 < ?s`] ..
  have "\<forall>n\<ge>max M N. norm ((X n, Y n) - (a, b)) < r"
    using M N by (simp add: real_sqrt_sum_squares_less norm_Pair)
  then show "\<exists>n0. \<forall>n\<ge>n0. norm ((X n, Y n) - (a, b)) < r" ..
qed

lemma Cauchy_Pair:
  assumes "Cauchy X" and "Cauchy Y"
  shows "Cauchy (\<lambda>n. (X n, Y n))"
proof (rule CauchyI)
  fix r :: real assume "0 < r"
  then have "0 < r / sqrt 2" (is "0 < ?s")
    by (simp add: divide_pos_pos)
  obtain M where M: "\<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < ?s"
    using CauchyD [OF `Cauchy X` `0 < ?s`] ..
  obtain N where N: "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (Y m - Y n) < ?s"
    using CauchyD [OF `Cauchy Y` `0 < ?s`] ..
  have "\<forall>m\<ge>max M N. \<forall>n\<ge>max M N. norm ((X m, Y m) - (X n, Y n)) < r"
    using M N by (simp add: real_sqrt_sum_squares_less norm_Pair)
  then show "\<exists>n0. \<forall>m\<ge>n0. \<forall>n\<ge>n0. norm ((X m, Y m) - (X n, Y n)) < r" ..
qed

lemma LIM_Pair:
  assumes "f -- x --> a" and "g -- x --> b"
  shows "(\<lambda>x. (f x, g x)) -- x --> (a, b)"
proof (rule LIM_I)
  fix r :: real assume "0 < r"
  then have "0 < r / sqrt 2" (is "0 < ?e")
    by (simp add: divide_pos_pos)
  obtain s where s: "0 < s"
    "\<forall>z. z \<noteq> x \<and> norm (z - x) < s \<longrightarrow> norm (f z - a) < ?e"
    using LIM_D [OF `f -- x --> a` `0 < ?e`] by fast
  obtain t where t: "0 < t"
    "\<forall>z. z \<noteq> x \<and> norm (z - x) < t \<longrightarrow> norm (g z - b) < ?e"
    using LIM_D [OF `g -- x --> b` `0 < ?e`] by fast
  have "0 < min s t \<and>
    (\<forall>z. z \<noteq> x \<and> norm (z - x) < min s t \<longrightarrow> norm ((f z, g z) - (a, b)) < r)"
    using s t by (simp add: real_sqrt_sum_squares_less norm_Pair)
  then show
    "\<exists>s>0. \<forall>z. z \<noteq> x \<and> norm (z - x) < s \<longrightarrow> norm ((f z, g z) - (a, b)) < r" ..
qed

lemma isCont_Pair [simp]:
  "\<lbrakk>isCont f x; isCont g x\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. (f x, g x)) x"
  unfolding isCont_def by (rule LIM_Pair)


subsection {* Product is a complete vector space *}

instance "*" :: (banach, banach) banach
proof
  fix X :: "nat \<Rightarrow> 'a \<times> 'b" assume "Cauchy X"
  have 1: "(\<lambda>n. fst (X n)) ----> lim (\<lambda>n. fst (X n))"
    using fst.Cauchy [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have 2: "(\<lambda>n. snd (X n)) ----> lim (\<lambda>n. snd (X n))"
    using snd.Cauchy [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have "X ----> (lim (\<lambda>n. fst (X n)), lim (\<lambda>n. snd (X n)))"
    using LIMSEQ_Pair [OF 1 2] by simp
  then show "convergent X"
    by (rule convergentI)
qed

subsection {* Frechet derivatives involving pairs *}

lemma FDERIV_Pair:
  assumes f: "FDERIV f x :> f'" and g: "FDERIV g x :> g'"
  shows "FDERIV (\<lambda>x. (f x, g x)) x :> (\<lambda>h. (f' h, g' h))"
apply (rule FDERIV_I)
apply (rule bounded_linear_Pair)
apply (rule FDERIV_bounded_linear [OF f])
apply (rule FDERIV_bounded_linear [OF g])
apply (simp add: norm_Pair)
apply (rule real_LIM_sandwich_zero)
apply (rule LIM_add_zero)
apply (rule FDERIV_D [OF f])
apply (rule FDERIV_D [OF g])
apply (rename_tac h)
apply (simp add: divide_nonneg_pos)
apply (rename_tac h)
apply (subst add_divide_distrib [symmetric])
apply (rule divide_right_mono [OF _ norm_ge_zero])
apply (rule order_trans [OF sqrt_add_le_add_sqrt])
apply simp
apply simp
apply simp
done

end
