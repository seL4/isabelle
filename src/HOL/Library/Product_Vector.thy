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

subsection {* Product is a topological space *}

instantiation
  "*" :: (topological_space, topological_space) topological_space
begin

definition topo_prod_def:
  "topo = {S. \<forall>x\<in>S. \<exists>A\<in>topo. \<exists>B\<in>topo. x \<in> A \<times> B \<and> A \<times> B \<subseteq> S}"

instance proof
  show "(UNIV :: ('a \<times> 'b) set) \<in> topo"
    unfolding topo_prod_def by (auto intro: topo_UNIV)
next
  fix S T :: "('a \<times> 'b) set"
  assume "S \<in> topo" "T \<in> topo" thus "S \<inter> T \<in> topo"
    unfolding topo_prod_def
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac Sa Ta Sb Tb)
    apply (rule_tac x="Sa \<inter> Ta" in rev_bexI)
    apply (simp add: topo_Int)
    apply (rule_tac x="Sb \<inter> Tb" in rev_bexI)
    apply (simp add: topo_Int)
    apply fast
    done
next
  fix T :: "('a \<times> 'b) set set"
  assume "T \<subseteq> topo" thus "\<Union>T \<in> topo"
    unfolding topo_prod_def Bex_def by fast
qed

end

subsection {* Product is a metric space *}

instantiation
  "*" :: (metric_space, metric_space) metric_space
begin

definition dist_prod_def:
  "dist (x::'a \<times> 'b) y = sqrt ((dist (fst x) (fst y))\<twosuperior> + (dist (snd x) (snd y))\<twosuperior>)"

lemma dist_Pair_Pair: "dist (a, b) (c, d) = sqrt ((dist a c)\<twosuperior> + (dist b d)\<twosuperior>)"
  unfolding dist_prod_def by simp

instance proof
  fix x y :: "'a \<times> 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_prod_def
    by (simp add: expand_prod_eq)
next
  fix x y z :: "'a \<times> 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_prod_def
    apply (rule order_trans [OF _ real_sqrt_sum_squares_triangle_ineq])
    apply (rule real_sqrt_le_mono)
    apply (rule order_trans [OF add_mono])
    apply (rule power_mono [OF dist_triangle2 [of _ _ "fst z"] zero_le_dist])
    apply (rule power_mono [OF dist_triangle2 [of _ _ "snd z"] zero_le_dist])
    apply (simp only: real_sum_squared_expand)
    done
next
  (* FIXME: long proof! *)
  (* Maybe it would be easier to define topological spaces *)
  (* in terms of neighborhoods instead of open sets? *)
  show "topo = {S::('a \<times> 'b) set. \<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S}"
    unfolding topo_prod_def topo_dist
    apply (safe, rename_tac S a b)
    apply (drule (1) bspec)
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac r s)
    apply (rule_tac x="min r s" in exI, simp)
    apply (clarify, rename_tac c d)
    apply (erule subsetD)
    apply (simp add: dist_Pair_Pair)
    apply (rule conjI)
    apply (drule spec, erule mp)
    apply (erule le_less_trans [OF real_sqrt_sum_squares_ge1])
    apply (drule spec, erule mp)
    apply (erule le_less_trans [OF real_sqrt_sum_squares_ge2])

    apply (rename_tac S a b)
    apply (drule (1) bspec)
    apply clarify
    apply (subgoal_tac "\<exists>r>0. \<exists>s>0. e = sqrt (r\<twosuperior> + s\<twosuperior>)")
    apply clarify
    apply (rule_tac x="{y. dist y a < r}" in rev_bexI)
    apply clarify
    apply (rule_tac x="r - dist x a" in exI, rule conjI, simp)
    apply clarify
    apply (rule le_less_trans [OF dist_triangle])
    apply (erule less_le_trans [OF add_strict_right_mono], simp)
    apply (rule_tac x="{y. dist y b < s}" in rev_bexI)
    apply clarify
    apply (rule_tac x="s - dist x b" in exI, rule conjI, simp)
    apply clarify
    apply (rule le_less_trans [OF dist_triangle])
    apply (erule less_le_trans [OF add_strict_right_mono], simp)
    apply (rule conjI)
    apply simp
    apply (clarify, rename_tac c d)
    apply (drule spec, erule mp)
    apply (simp add: dist_Pair_Pair add_strict_mono power_strict_mono)
    apply (rule_tac x="e / sqrt 2" in exI, simp add: divide_pos_pos)
    apply (rule_tac x="e / sqrt 2" in exI, simp add: divide_pos_pos)
    apply (simp add: power_divide)
    done
qed

end

subsection {* Continuity of operations *}

lemma dist_fst_le: "dist (fst x) (fst y) \<le> dist x y"
unfolding dist_prod_def by simp

lemma dist_snd_le: "dist (snd x) (snd y) \<le> dist x y"
unfolding dist_prod_def by simp

lemma tendsto_fst:
  assumes "(f ---> a) net"
  shows "((\<lambda>x. fst (f x)) ---> fst a) net"
proof (rule topological_tendstoI)
  fix S assume "S \<in> topo" "fst a \<in> S"
  then have "fst -` S \<in> topo" "a \<in> fst -` S"
    unfolding topo_prod_def
    apply simp_all
    apply clarify
    apply (erule rev_bexI, simp)
    apply (rule rev_bexI [OF topo_UNIV])
    apply auto
    done
  with assms have "eventually (\<lambda>x. f x \<in> fst -` S) net"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. fst (f x) \<in> S) net"
    by simp
qed

lemma tendsto_snd:
  assumes "(f ---> a) net"
  shows "((\<lambda>x. snd (f x)) ---> snd a) net"
proof (rule topological_tendstoI)
  fix S assume "S \<in> topo" "snd a \<in> S"
  then have "snd -` S \<in> topo" "a \<in> snd -` S"
    unfolding topo_prod_def
    apply simp_all
    apply clarify
    apply (rule rev_bexI [OF topo_UNIV])
    apply (erule rev_bexI)
    apply auto
    done
  with assms have "eventually (\<lambda>x. f x \<in> snd -` S) net"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. snd (f x) \<in> S) net"
    by simp
qed

lemma tendsto_Pair:
  assumes "(f ---> a) net" and "(g ---> b) net"
  shows "((\<lambda>x. (f x, g x)) ---> (a, b)) net"
proof (rule topological_tendstoI)
  fix S assume "S \<in> topo" "(a, b) \<in> S"
  then obtain A B where "A \<in> topo" "B \<in> topo" "a \<in> A" "b \<in> B" "A \<times> B \<subseteq> S"
    unfolding topo_prod_def by auto
  have "eventually (\<lambda>x. f x \<in> A) net"
    using `(f ---> a) net` `A \<in> topo` `a \<in> A`
    by (rule topological_tendstoD)
  moreover
  have "eventually (\<lambda>x. g x \<in> B) net"
    using `(g ---> b) net` `B \<in> topo` `b \<in> B`
    by (rule topological_tendstoD)
  ultimately
  show "eventually (\<lambda>x. (f x, g x) \<in> S) net"
    by (rule eventually_elim2)
       (simp add: subsetD [OF `A \<times> B \<subseteq> S`])
qed

lemma LIMSEQ_fst: "(X ----> a) \<Longrightarrow> (\<lambda>n. fst (X n)) ----> fst a"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_fst)

lemma LIMSEQ_snd: "(X ----> a) \<Longrightarrow> (\<lambda>n. snd (X n)) ----> snd a"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_snd)

lemma LIMSEQ_Pair:
  assumes "X ----> a" and "Y ----> b"
  shows "(\<lambda>n. (X n, Y n)) ----> (a, b)"
using assms unfolding LIMSEQ_conv_tendsto
by (rule tendsto_Pair)

lemma LIM_fst: "f -- x --> a \<Longrightarrow> (\<lambda>x. fst (f x)) -- x --> fst a"
unfolding LIM_conv_tendsto by (rule tendsto_fst)

lemma LIM_snd: "f -- x --> a \<Longrightarrow> (\<lambda>x. snd (f x)) -- x --> snd a"
unfolding LIM_conv_tendsto by (rule tendsto_snd)

lemma LIM_Pair:
  assumes "f -- x --> a" and "g -- x --> b"
  shows "(\<lambda>x. (f x, g x)) -- x --> (a, b)"
using assms unfolding LIM_conv_tendsto
by (rule tendsto_Pair)

lemma Cauchy_fst: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. fst (X n))"
unfolding Cauchy_def by (fast elim: le_less_trans [OF dist_fst_le])

lemma Cauchy_snd: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. snd (X n))"
unfolding Cauchy_def by (fast elim: le_less_trans [OF dist_snd_le])

lemma Cauchy_Pair:
  assumes "Cauchy X" and "Cauchy Y"
  shows "Cauchy (\<lambda>n. (X n, Y n))"
proof (rule metric_CauchyI)
  fix r :: real assume "0 < r"
  then have "0 < r / sqrt 2" (is "0 < ?s")
    by (simp add: divide_pos_pos)
  obtain M where M: "\<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < ?s"
    using metric_CauchyD [OF `Cauchy X` `0 < ?s`] ..
  obtain N where N: "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (Y m) (Y n) < ?s"
    using metric_CauchyD [OF `Cauchy Y` `0 < ?s`] ..
  have "\<forall>m\<ge>max M N. \<forall>n\<ge>max M N. dist (X m, Y m) (X n, Y n) < r"
    using M N by (simp add: real_sqrt_sum_squares_less dist_Pair_Pair)
  then show "\<exists>n0. \<forall>m\<ge>n0. \<forall>n\<ge>n0. dist (X m, Y m) (X n, Y n) < r" ..
qed

lemma isCont_Pair [simp]:
  "\<lbrakk>isCont f x; isCont g x\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. (f x, g x)) x"
  unfolding isCont_def by (rule LIM_Pair)

subsection {* Product is a complete metric space *}

instance "*" :: (complete_space, complete_space) complete_space
proof
  fix X :: "nat \<Rightarrow> 'a \<times> 'b" assume "Cauchy X"
  have 1: "(\<lambda>n. fst (X n)) ----> lim (\<lambda>n. fst (X n))"
    using Cauchy_fst [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have 2: "(\<lambda>n. snd (X n)) ----> lim (\<lambda>n. snd (X n))"
    using Cauchy_snd [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have "X ----> (lim (\<lambda>n. fst (X n)), lim (\<lambda>n. snd (X n)))"
    using LIMSEQ_Pair [OF 1 2] by simp
  then show "convergent X"
    by (rule convergentI)
qed

subsection {* Product is a normed vector space *}

instantiation
  "*" :: (real_normed_vector, real_normed_vector) real_normed_vector
begin

definition norm_prod_def:
  "norm x = sqrt ((norm (fst x))\<twosuperior> + (norm (snd x))\<twosuperior>)"

definition sgn_prod_def:
  "sgn (x::'a \<times> 'b) = scaleR (inverse (norm x)) x"

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
    unfolding dist_prod_def norm_prod_def
    by (simp add: dist_norm)
qed

end

instance "*" :: (banach, banach) banach ..

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

subsection {* Pair operations are linear *}

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
