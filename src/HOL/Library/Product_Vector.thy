(*  Title:      HOL/Library/Product_Vector.thy
    Author:     Brian Huffman
*)

header {* Cartesian Products as Vector Spaces *}

theory Product_Vector
imports Inner_Product Product_plus
begin

subsection {* Product is a real vector space *}

instantiation prod :: (real_vector, real_vector) real_vector
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
    by (simp add: prod_eq_iff scaleR_right_distrib)
  show "scaleR (a + b) x = scaleR a x + scaleR b x"
    by (simp add: prod_eq_iff scaleR_left_distrib)
  show "scaleR a (scaleR b x) = scaleR (a * b) x"
    by (simp add: prod_eq_iff)
  show "scaleR 1 x = x"
    by (simp add: prod_eq_iff)
qed

end

subsection {* Product is a topological space *}

instantiation prod :: (topological_space, topological_space) topological_space
begin

definition open_prod_def:
  "open (S :: ('a \<times> 'b) set) \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S)"

lemma open_prod_elim:
  assumes "open S" and "x \<in> S"
  obtains A B where "open A" and "open B" and "x \<in> A \<times> B" and "A \<times> B \<subseteq> S"
using assms unfolding open_prod_def by fast

lemma open_prod_intro:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S"
  shows "open S"
using assms unfolding open_prod_def by fast

instance proof
  show "open (UNIV :: ('a \<times> 'b) set)"
    unfolding open_prod_def by auto
next
  fix S T :: "('a \<times> 'b) set"
  assume "open S" "open T"
  show "open (S \<inter> T)"
  proof (rule open_prod_intro)
    fix x assume x: "x \<in> S \<inter> T"
    from x have "x \<in> S" by simp
    obtain Sa Sb where A: "open Sa" "open Sb" "x \<in> Sa \<times> Sb" "Sa \<times> Sb \<subseteq> S"
      using `open S` and `x \<in> S` by (rule open_prod_elim)
    from x have "x \<in> T" by simp
    obtain Ta Tb where B: "open Ta" "open Tb" "x \<in> Ta \<times> Tb" "Ta \<times> Tb \<subseteq> T"
      using `open T` and `x \<in> T` by (rule open_prod_elim)
    let ?A = "Sa \<inter> Ta" and ?B = "Sb \<inter> Tb"
    have "open ?A \<and> open ?B \<and> x \<in> ?A \<times> ?B \<and> ?A \<times> ?B \<subseteq> S \<inter> T"
      using A B by (auto simp add: open_Int)
    thus "\<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S \<inter> T"
      by fast
  qed
next
  fix K :: "('a \<times> 'b) set set"
  assume "\<forall>S\<in>K. open S" thus "open (\<Union>K)"
    unfolding open_prod_def by fast
qed

end

lemma open_Times: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<times> T)"
unfolding open_prod_def by auto

lemma fst_vimage_eq_Times: "fst -` S = S \<times> UNIV"
by auto

lemma snd_vimage_eq_Times: "snd -` S = UNIV \<times> S"
by auto

lemma open_vimage_fst: "open S \<Longrightarrow> open (fst -` S)"
by (simp add: fst_vimage_eq_Times open_Times)

lemma open_vimage_snd: "open S \<Longrightarrow> open (snd -` S)"
by (simp add: snd_vimage_eq_Times open_Times)

lemma closed_vimage_fst: "closed S \<Longrightarrow> closed (fst -` S)"
unfolding closed_open vimage_Compl [symmetric]
by (rule open_vimage_fst)

lemma closed_vimage_snd: "closed S \<Longrightarrow> closed (snd -` S)"
unfolding closed_open vimage_Compl [symmetric]
by (rule open_vimage_snd)

lemma closed_Times: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<times> T)"
proof -
  have "S \<times> T = (fst -` S) \<inter> (snd -` T)" by auto
  thus "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<times> T)"
    by (simp add: closed_vimage_fst closed_vimage_snd closed_Int)
qed

lemma openI: (* TODO: move *)
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S"
  shows "open S"
proof -
  have "open (\<Union>{T. open T \<and> T \<subseteq> S})" by auto
  moreover have "\<Union>{T. open T \<and> T \<subseteq> S} = S" by (auto dest!: assms)
  ultimately show "open S" by simp
qed

lemma subset_fst_imageI: "A \<times> B \<subseteq> S \<Longrightarrow> y \<in> B \<Longrightarrow> A \<subseteq> fst ` S"
  unfolding image_def subset_eq by force

lemma subset_snd_imageI: "A \<times> B \<subseteq> S \<Longrightarrow> x \<in> A \<Longrightarrow> B \<subseteq> snd ` S"
  unfolding image_def subset_eq by force

lemma open_image_fst: assumes "open S" shows "open (fst ` S)"
proof (rule openI)
  fix x assume "x \<in> fst ` S"
  then obtain y where "(x, y) \<in> S" by auto
  then obtain A B where "open A" "open B" "x \<in> A" "y \<in> B" "A \<times> B \<subseteq> S"
    using `open S` unfolding open_prod_def by auto
  from `A \<times> B \<subseteq> S` `y \<in> B` have "A \<subseteq> fst ` S" by (rule subset_fst_imageI)
  with `open A` `x \<in> A` have "open A \<and> x \<in> A \<and> A \<subseteq> fst ` S" by simp
  then show "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> fst ` S" by - (rule exI)
qed

lemma open_image_snd: assumes "open S" shows "open (snd ` S)"
proof (rule openI)
  fix y assume "y \<in> snd ` S"
  then obtain x where "(x, y) \<in> S" by auto
  then obtain A B where "open A" "open B" "x \<in> A" "y \<in> B" "A \<times> B \<subseteq> S"
    using `open S` unfolding open_prod_def by auto
  from `A \<times> B \<subseteq> S` `x \<in> A` have "B \<subseteq> snd ` S" by (rule subset_snd_imageI)
  with `open B` `y \<in> B` have "open B \<and> y \<in> B \<and> B \<subseteq> snd ` S" by simp
  then show "\<exists>T. open T \<and> y \<in> T \<and> T \<subseteq> snd ` S" by - (rule exI)
qed

subsubsection {* Continuity of operations *}

lemma tendsto_fst [tendsto_intros]:
  assumes "(f ---> a) F"
  shows "((\<lambda>x. fst (f x)) ---> fst a) F"
proof (rule topological_tendstoI)
  fix S assume "open S" and "fst a \<in> S"
  then have "open (fst -` S)" and "a \<in> fst -` S"
    by (simp_all add: open_vimage_fst)
  with assms have "eventually (\<lambda>x. f x \<in> fst -` S) F"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. fst (f x) \<in> S) F"
    by simp
qed

lemma tendsto_snd [tendsto_intros]:
  assumes "(f ---> a) F"
  shows "((\<lambda>x. snd (f x)) ---> snd a) F"
proof (rule topological_tendstoI)
  fix S assume "open S" and "snd a \<in> S"
  then have "open (snd -` S)" and "a \<in> snd -` S"
    by (simp_all add: open_vimage_snd)
  with assms have "eventually (\<lambda>x. f x \<in> snd -` S) F"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. snd (f x) \<in> S) F"
    by simp
qed

lemma tendsto_Pair [tendsto_intros]:
  assumes "(f ---> a) F" and "(g ---> b) F"
  shows "((\<lambda>x. (f x, g x)) ---> (a, b)) F"
proof (rule topological_tendstoI)
  fix S assume "open S" and "(a, b) \<in> S"
  then obtain A B where "open A" "open B" "a \<in> A" "b \<in> B" "A \<times> B \<subseteq> S"
    unfolding open_prod_def by fast
  have "eventually (\<lambda>x. f x \<in> A) F"
    using `(f ---> a) F` `open A` `a \<in> A`
    by (rule topological_tendstoD)
  moreover
  have "eventually (\<lambda>x. g x \<in> B) F"
    using `(g ---> b) F` `open B` `b \<in> B`
    by (rule topological_tendstoD)
  ultimately
  show "eventually (\<lambda>x. (f x, g x) \<in> S) F"
    by (rule eventually_elim2)
       (simp add: subsetD [OF `A \<times> B \<subseteq> S`])
qed

lemma isCont_fst [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. fst (f x)) a"
  unfolding isCont_def by (rule tendsto_fst)

lemma isCont_snd [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. snd (f x)) a"
  unfolding isCont_def by (rule tendsto_snd)

lemma isCont_Pair [simp]:
  "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. (f x, g x)) a"
  unfolding isCont_def by (rule tendsto_Pair)

subsubsection {* Separation axioms *}

lemma mem_Times_iff: "x \<in> A \<times> B \<longleftrightarrow> fst x \<in> A \<and> snd x \<in> B"
  by (induct x) simp (* TODO: move elsewhere *)

instance prod :: (t0_space, t0_space) t0_space
proof
  fix x y :: "'a \<times> 'b" assume "x \<noteq> y"
  hence "fst x \<noteq> fst y \<or> snd x \<noteq> snd y"
    by (simp add: prod_eq_iff)
  thus "\<exists>U. open U \<and> (x \<in> U) \<noteq> (y \<in> U)"
    apply (rule disjE)
    apply (drule t0_space, erule exE, rule_tac x="U \<times> UNIV" in exI)
    apply (simp add: open_Times mem_Times_iff)
    apply (drule t0_space, erule exE, rule_tac x="UNIV \<times> U" in exI)
    apply (simp add: open_Times mem_Times_iff)
    done
qed

instance prod :: (t1_space, t1_space) t1_space
proof
  fix x y :: "'a \<times> 'b" assume "x \<noteq> y"
  hence "fst x \<noteq> fst y \<or> snd x \<noteq> snd y"
    by (simp add: prod_eq_iff)
  thus "\<exists>U. open U \<and> x \<in> U \<and> y \<notin> U"
    apply (rule disjE)
    apply (drule t1_space, erule exE, rule_tac x="U \<times> UNIV" in exI)
    apply (simp add: open_Times mem_Times_iff)
    apply (drule t1_space, erule exE, rule_tac x="UNIV \<times> U" in exI)
    apply (simp add: open_Times mem_Times_iff)
    done
qed

instance prod :: (t2_space, t2_space) t2_space
proof
  fix x y :: "'a \<times> 'b" assume "x \<noteq> y"
  hence "fst x \<noteq> fst y \<or> snd x \<noteq> snd y"
    by (simp add: prod_eq_iff)
  thus "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    apply (rule disjE)
    apply (drule hausdorff, clarify)
    apply (rule_tac x="U \<times> UNIV" in exI, rule_tac x="V \<times> UNIV" in exI)
    apply (simp add: open_Times mem_Times_iff disjoint_iff_not_equal)
    apply (drule hausdorff, clarify)
    apply (rule_tac x="UNIV \<times> U" in exI, rule_tac x="UNIV \<times> V" in exI)
    apply (simp add: open_Times mem_Times_iff disjoint_iff_not_equal)
    done
qed

subsection {* Product is a metric space *}

instantiation prod :: (metric_space, metric_space) metric_space
begin

definition dist_prod_def:
  "dist x y = sqrt ((dist (fst x) (fst y))\<twosuperior> + (dist (snd x) (snd y))\<twosuperior>)"

lemma dist_Pair_Pair: "dist (a, b) (c, d) = sqrt ((dist a c)\<twosuperior> + (dist b d)\<twosuperior>)"
  unfolding dist_prod_def by simp

lemma dist_fst_le: "dist (fst x) (fst y) \<le> dist x y"
unfolding dist_prod_def by (rule real_sqrt_sum_squares_ge1)

lemma dist_snd_le: "dist (snd x) (snd y) \<le> dist x y"
unfolding dist_prod_def by (rule real_sqrt_sum_squares_ge2)

instance proof
  fix x y :: "'a \<times> 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_prod_def prod_eq_iff by simp
next
  fix x y z :: "'a \<times> 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_prod_def
    by (intro order_trans [OF _ real_sqrt_sum_squares_triangle_ineq]
        real_sqrt_le_mono add_mono power_mono dist_triangle2 zero_le_dist)
next
  fix S :: "('a \<times> 'b) set"
  show "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  proof
    assume "open S" show "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S"
    proof
      fix x assume "x \<in> S"
      obtain A B where "open A" "open B" "x \<in> A \<times> B" "A \<times> B \<subseteq> S"
        using `open S` and `x \<in> S` by (rule open_prod_elim)
      obtain r where r: "0 < r" "\<forall>y. dist y (fst x) < r \<longrightarrow> y \<in> A"
        using `open A` and `x \<in> A \<times> B` unfolding open_dist by auto
      obtain s where s: "0 < s" "\<forall>y. dist y (snd x) < s \<longrightarrow> y \<in> B"
        using `open B` and `x \<in> A \<times> B` unfolding open_dist by auto
      let ?e = "min r s"
      have "0 < ?e \<and> (\<forall>y. dist y x < ?e \<longrightarrow> y \<in> S)"
      proof (intro allI impI conjI)
        show "0 < min r s" by (simp add: r(1) s(1))
      next
        fix y assume "dist y x < min r s"
        hence "dist y x < r" and "dist y x < s"
          by simp_all
        hence "dist (fst y) (fst x) < r" and "dist (snd y) (snd x) < s"
          by (auto intro: le_less_trans dist_fst_le dist_snd_le)
        hence "fst y \<in> A" and "snd y \<in> B"
          by (simp_all add: r(2) s(2))
        hence "y \<in> A \<times> B" by (induct y, simp)
        with `A \<times> B \<subseteq> S` show "y \<in> S" ..
      qed
      thus "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S" ..
    qed
  next
    assume *: "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S" show "open S"
    proof (rule open_prod_intro)
      fix x assume "x \<in> S"
      then obtain e where "0 < e" and S: "\<forall>y. dist y x < e \<longrightarrow> y \<in> S"
        using * by fast
      def r \<equiv> "e / sqrt 2" and s \<equiv> "e / sqrt 2"
      from `0 < e` have "0 < r" and "0 < s"
        unfolding r_def s_def by (simp_all add: divide_pos_pos)
      from `0 < e` have "e = sqrt (r\<twosuperior> + s\<twosuperior>)"
        unfolding r_def s_def by (simp add: power_divide)
      def A \<equiv> "{y. dist (fst x) y < r}" and B \<equiv> "{y. dist (snd x) y < s}"
      have "open A" and "open B"
        unfolding A_def B_def by (simp_all add: open_ball)
      moreover have "x \<in> A \<times> B"
        unfolding A_def B_def mem_Times_iff
        using `0 < r` and `0 < s` by simp
      moreover have "A \<times> B \<subseteq> S"
      proof (clarify)
        fix a b assume "a \<in> A" and "b \<in> B"
        hence "dist a (fst x) < r" and "dist b (snd x) < s"
          unfolding A_def B_def by (simp_all add: dist_commute)
        hence "dist (a, b) x < e"
          unfolding dist_prod_def `e = sqrt (r\<twosuperior> + s\<twosuperior>)`
          by (simp add: add_strict_mono power_strict_mono)
        thus "(a, b) \<in> S"
          by (simp add: S)
      qed
      ultimately show "\<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S" by fast
    qed
  qed
qed

end

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

subsection {* Product is a complete metric space *}

instance prod :: (complete_space, complete_space) complete_space
proof
  fix X :: "nat \<Rightarrow> 'a \<times> 'b" assume "Cauchy X"
  have 1: "(\<lambda>n. fst (X n)) ----> lim (\<lambda>n. fst (X n))"
    using Cauchy_fst [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have 2: "(\<lambda>n. snd (X n)) ----> lim (\<lambda>n. snd (X n))"
    using Cauchy_snd [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have "X ----> (lim (\<lambda>n. fst (X n)), lim (\<lambda>n. snd (X n)))"
    using tendsto_Pair [OF 1 2] by simp
  then show "convergent X"
    by (rule convergentI)
qed

subsection {* Product is a normed vector space *}

instantiation prod :: (real_normed_vector, real_normed_vector) real_normed_vector
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
    by (simp add: prod_eq_iff)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_prod_def
    apply (rule order_trans [OF _ real_sqrt_sum_squares_triangle_ineq])
    apply (simp add: add_mono power_mono norm_triangle_ineq)
    done
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    unfolding norm_prod_def
    apply (simp add: power_mult_distrib)
    apply (simp add: distrib_left [symmetric])
    apply (simp add: real_sqrt_mult_distrib)
    done
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule sgn_prod_def)
  show "dist x y = norm (x - y)"
    unfolding dist_prod_def norm_prod_def
    by (simp add: dist_norm)
qed

end

instance prod :: (banach, banach) banach ..

subsubsection {* Pair operations are linear *}

lemma bounded_linear_fst: "bounded_linear fst"
  using fst_add fst_scaleR
  by (rule bounded_linear_intro [where K=1], simp add: norm_prod_def)

lemma bounded_linear_snd: "bounded_linear snd"
  using snd_add snd_scaleR
  by (rule bounded_linear_intro [where K=1], simp add: norm_prod_def)

text {* TODO: move to NthRoot *}
lemma sqrt_add_le_add_sqrt:
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "sqrt (x + y) \<le> sqrt x + sqrt y"
apply (rule power2_le_imp_le)
apply (simp add: power2_sum x y)
apply (simp add: mult_nonneg_nonneg x y)
apply (simp add: x y)
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
    apply (simp add: distrib_left)
    apply (rule add_mono [OF norm_f norm_g])
    done
  then show "\<exists>K. \<forall>x. norm (f x, g x) \<le> norm x * K" ..
qed

subsubsection {* Frechet derivatives involving pairs *}

lemma FDERIV_Pair:
  assumes f: "FDERIV f x :> f'" and g: "FDERIV g x :> g'"
  shows "FDERIV (\<lambda>x. (f x, g x)) x :> (\<lambda>h. (f' h, g' h))"
proof (rule FDERIV_I)
  show "bounded_linear (\<lambda>h. (f' h, g' h))"
    using f g by (intro bounded_linear_Pair FDERIV_bounded_linear)
  let ?Rf = "\<lambda>h. f (x + h) - f x - f' h"
  let ?Rg = "\<lambda>h. g (x + h) - g x - g' h"
  let ?R = "\<lambda>h. ((f (x + h), g (x + h)) - (f x, g x) - (f' h, g' h))"
  show "(\<lambda>h. norm (?R h) / norm h) -- 0 --> 0"
  proof (rule real_LIM_sandwich_zero)
    show "(\<lambda>h. norm (?Rf h) / norm h + norm (?Rg h) / norm h) -- 0 --> 0"
      using f g by (intro tendsto_add_zero FDERIV_D)
    fix h :: 'a assume "h \<noteq> 0"
    thus "0 \<le> norm (?R h) / norm h"
      by (simp add: divide_nonneg_pos)
    show "norm (?R h) / norm h \<le> norm (?Rf h) / norm h + norm (?Rg h) / norm h"
      unfolding add_divide_distrib [symmetric]
      by (simp add: norm_Pair divide_right_mono
        order_trans [OF sqrt_add_le_add_sqrt])
  qed
qed

subsection {* Product is an inner product space *}

instantiation prod :: (real_inner, real_inner) real_inner
begin

definition inner_prod_def:
  "inner x y = inner (fst x) (fst y) + inner (snd x) (snd y)"

lemma inner_Pair [simp]: "inner (a, b) (c, d) = inner a c + inner b d"
  unfolding inner_prod_def by simp

instance proof
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

end
