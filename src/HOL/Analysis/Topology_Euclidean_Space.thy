(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

chapter \<open>Vector Analysis\<close>

theory Topology_Euclidean_Space
  imports
    Elementary_Normed_Spaces
    Linear_Algebra
    Norm_Arith
begin

section \<open>Elementary Topology in Euclidean Space\<close>

lemma euclidean_dist_l2:
  fixes x y :: "'a :: euclidean_space"
  shows "dist x y = L2_set (\<lambda>i. dist (x \<bullet> i) (y \<bullet> i)) Basis"
  unfolding dist_norm norm_eq_sqrt_inner L2_set_def
  by (subst euclidean_inner) (simp add: power2_eq_square inner_diff_left)

lemma norm_nth_le: "norm (x \<bullet> i) \<le> norm x" if "i \<in> Basis"
proof -
  have "(x \<bullet> i)\<^sup>2 = (\<Sum>i\<in>{i}. (x \<bullet> i)\<^sup>2)"
    by simp
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. (x \<bullet> i)\<^sup>2)"
    by (intro sum_mono2) (auto simp: that)
  finally show ?thesis
    unfolding norm_conv_dist euclidean_dist_l2[of x] L2_set_def
    by (auto intro!: real_le_rsqrt)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Continuity of the representation WRT an orthogonal basis\<close>

lemma orthogonal_Basis: "pairwise orthogonal Basis"
  by (simp add: inner_not_same_Basis orthogonal_def pairwise_def)

lemma representation_bound:
  fixes B :: "'N::real_inner set"
  assumes "finite B" "independent B" "b \<in> B" and orth: "pairwise orthogonal B"
  obtains m where "m > 0" "\<And>x. x \<in> span B \<Longrightarrow> \<bar>representation B x b\<bar> \<le> m * norm x"
proof 
  fix x
  assume x: "x \<in> span B"
  have "b \<noteq> 0"
    using \<open>independent B\<close> \<open>b \<in> B\<close> dependent_zero by blast
  have [simp]: "b \<bullet> b' = (if b' = b then (norm b)\<^sup>2 else 0)"
    if "b \<in> B" "b' \<in> B" for b b'
    using orth by (simp add: orthogonal_def pairwise_def norm_eq_sqrt_inner that)
  have "norm x = norm (\<Sum>b\<in>B. representation B x b *\<^sub>R b)"
    using real_vector.sum_representation_eq [OF \<open>independent B\<close> x \<open>finite B\<close> order_refl]
    by simp
  also have "\<dots> = sqrt ((\<Sum>b\<in>B. representation B x b *\<^sub>R b) \<bullet> (\<Sum>b\<in>B. representation B x b *\<^sub>R b))"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> = sqrt (\<Sum>b\<in>B. (representation B x b *\<^sub>R b) \<bullet> (representation B x b *\<^sub>R b))"
    using \<open>finite B\<close>
    by (simp add: inner_sum_left inner_sum_right if_distrib [of "\<lambda>x. _ * x"] cong: if_cong sum.cong_simp)
  also have "\<dots> = sqrt (\<Sum>b\<in>B. (norm (representation B x b *\<^sub>R b))\<^sup>2)"
    by (simp add: mult.commute mult.left_commute power2_eq_square)
  also have "\<dots> = sqrt (\<Sum>b\<in>B. (representation B x b)\<^sup>2 * (norm b)\<^sup>2)"
    by (simp add: norm_mult power_mult_distrib)
  finally have "norm x = sqrt (\<Sum>b\<in>B. (representation B x b)\<^sup>2 * (norm b)\<^sup>2)" .
  moreover
  have "sqrt ((representation B x b)\<^sup>2 * (norm b)\<^sup>2) \<le> sqrt (\<Sum>b\<in>B. (representation B x b)\<^sup>2 * (norm b)\<^sup>2)"
    using \<open>b \<in> B\<close> \<open>finite B\<close> by (auto intro: member_le_sum)
  then have "\<bar>representation B x b\<bar> \<le> (1 / norm b) * sqrt (\<Sum>b\<in>B. (representation B x b)\<^sup>2 * (norm b)\<^sup>2)"
    using \<open>b \<noteq> 0\<close> by (simp add: field_split_simps real_sqrt_mult del: real_sqrt_le_iff)
  ultimately show "\<bar>representation B x b\<bar> \<le> (1 / norm b) * norm x"
    by simp
next
  show "0 < 1 / norm b"
    using \<open>independent B\<close> \<open>b \<in> B\<close> dependent_zero by auto
qed 

lemma continuous_on_representation:
  fixes B :: "'N::euclidean_space set"
  assumes "finite B" "independent B" "b \<in> B" "pairwise orthogonal B" 
  shows "continuous_on (span B) (\<lambda>x. representation B x b)"
proof
  show "\<exists>d>0. \<forall>x'\<in>span B. dist x' x < d \<longrightarrow> dist (representation B x' b) (representation B x b) \<le> e"
    if "e > 0" "x \<in> span B" for x e
  proof -
    obtain m where "m > 0" and m: "\<And>x. x \<in> span B \<Longrightarrow> \<bar>representation B x b\<bar> \<le> m * norm x"
      using assms representation_bound by blast
    show ?thesis
      unfolding dist_norm
    proof (intro exI conjI ballI impI)
      show "e/m > 0"
        by (simp add: \<open>e > 0\<close> \<open>m > 0\<close>)
      show "norm (representation B x' b - representation B x b) \<le> e"
        if x': "x' \<in> span B" and less: "norm (x'-x) < e/m" for x' 
      proof -
        have "\<bar>representation B (x'-x) b\<bar> \<le> m * norm (x'-x)"
          using m [of "x'-x"] \<open>x \<in> span B\<close> span_diff x' by blast
        also have "\<dots> < e"
          by (metis \<open>m > 0\<close> less mult.commute pos_less_divide_eq)
        finally have "\<bar>representation B (x'-x) b\<bar> \<le> e" by simp
        then show ?thesis
          by (simp add: \<open>x \<in> span B\<close> \<open>independent B\<close> representation_diff x')
      qed
    qed
  qed
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Balls in Euclidean Space\<close>

lemma cball_subset_cball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "cball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r < 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "r < 0")
    case True
    then show ?rhs by simp
  next
    case False
    then have [simp]: "r \<ge> 0" by simp
    have "norm (a - a') + r \<le> r'"
    proof (cases "a = a'")
      case True
      then show ?thesis
        using subsetD [where c = "a + r *\<^sub>R (SOME i. i \<in> Basis)", OF \<open>?lhs\<close>] subsetD [where c = a, OF \<open>?lhs\<close>]
        by (force simp: SOME_Basis dist_norm)
    next
      case False
      have "norm (a' - (a + (r / norm (a - a')) *\<^sub>R (a - a'))) = norm (a' - a - (r / norm (a - a')) *\<^sub>R (a - a'))"
        by (simp add: algebra_simps)
      also have "... = norm ((-1 - (r / norm (a - a'))) *\<^sub>R (a - a'))"
        by (simp add: algebra_simps)
      also from \<open>a \<noteq> a'\<close> have "... = \<bar>- norm (a - a') - r\<bar>"
        by simp (simp add: field_simps)
      finally have [simp]: "norm (a' - (a + (r / norm (a - a')) *\<^sub>R (a - a'))) = \<bar>norm (a - a') + r\<bar>"
        by linarith
      from \<open>a \<noteq> a'\<close> show ?thesis
        using subsetD [where c = "a' + (1 + r / norm(a - a')) *\<^sub>R (a - a')", OF \<open>?lhs\<close>]
        by (simp add: dist_norm scaleR_add_left)
    qed
    then show ?rhs
      by (simp add: dist_norm)
  qed
qed metric

lemma cball_subset_ball_iff: "cball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r < r' \<or> r < 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for a :: "'a::euclidean_space"
proof
  assume ?lhs
  then show ?rhs
  proof (cases "r < 0")
    case True then
    show ?rhs by simp
  next
    case False
    then have [simp]: "r \<ge> 0" by simp
    have "norm (a - a') + r < r'"
    proof (cases "a = a'")
      case True
      then show ?thesis
        using subsetD [where c = "a + r *\<^sub>R (SOME i. i \<in> Basis)", OF \<open>?lhs\<close>] subsetD [where c = a, OF \<open>?lhs\<close>]
        by (force simp: SOME_Basis dist_norm)
    next
      case False
      have False if "norm (a - a') + r \<ge> r'"
      proof -
        from that have "\<bar>r' - norm (a - a')\<bar> \<le> r"
          by (simp split: abs_split)
            (metis \<open>0 \<le> r\<close> \<open>?lhs\<close> centre_in_cball dist_commute dist_norm less_asym mem_ball subset_eq)
        then show ?thesis
          using subsetD [where c = "a + (r' / norm(a - a') - 1) *\<^sub>R (a - a')", OF \<open>?lhs\<close>] \<open>a \<noteq> a'\<close>
          apply (simp add: dist_norm)
          apply (simp add: scaleR_left_diff_distrib)
          apply (simp add: field_simps)
          done
      qed
      then show ?thesis by force
    qed
    then show ?rhs by (simp add: dist_norm)
  qed
next
  assume ?rhs
  then show ?lhs
    by metric
qed

lemma ball_subset_cball_iff: "ball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
  (is "?lhs = ?rhs")
  for a :: "'a::euclidean_space"
proof (cases "r \<le> 0")
  case True
  then show ?thesis
    by metric
next
  case False
  show ?thesis
  proof
    assume ?lhs
    then have "(cball a r \<subseteq> cball a' r')"
      by (metis False closed_cball closure_ball closure_closed closure_mono not_less)
    with False show ?rhs
      by (fastforce iff: cball_subset_cball_iff)
  next
    assume ?rhs
    with False show ?lhs
      by metric
  qed
qed

lemma ball_subset_ball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "ball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
        (is "?lhs = ?rhs")
proof (cases "r \<le> 0")
  case True then show ?thesis
    by metric
next
  case False show ?thesis
  proof
    assume ?lhs
    then have "0 < r'"
      using False by metric
    then have "(cball a r \<subseteq> cball a' r')"
      by (metis False\<open>?lhs\<close> closure_ball closure_mono not_less)
    then show ?rhs
      using False cball_subset_cball_iff by fastforce
  qed metric
qed


lemma ball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = ball y e \<longleftrightarrow> d \<le> 0 \<and> e \<le> 0 \<or> x=y \<and> d=e"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "d \<le> 0 \<or> e \<le> 0")
    case True
      with \<open>?lhs\<close> show ?rhs
        by safe (simp_all only: ball_eq_empty [of y e, symmetric] ball_eq_empty [of x d, symmetric])
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      apply (auto simp: set_eq_subset ball_subset_ball_iff dist_norm norm_minus_commute algebra_simps)
      apply (metis add_le_same_cancel1 le_add_same_cancel1 norm_ge_zero norm_pths(2) order_trans)
      apply (metis add_increasing2 add_le_imp_le_right eq_iff norm_ge_zero)
      done
  qed
next
  assume ?rhs then show ?lhs
    by (auto simp: set_eq_subset ball_subset_ball_iff)
qed

lemma cball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = cball y e \<longleftrightarrow> d < 0 \<and> e < 0 \<or> x=y \<and> d=e"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "d < 0 \<or> e < 0")
    case True
      with \<open>?lhs\<close> show ?rhs
        by safe (simp_all only: cball_eq_empty [of y e, symmetric] cball_eq_empty [of x d, symmetric])
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      apply (auto simp: set_eq_subset cball_subset_cball_iff dist_norm norm_minus_commute algebra_simps)
      apply (metis add_le_same_cancel1 le_add_same_cancel1 norm_ge_zero norm_pths(2) order_trans)
      apply (metis add_increasing2 add_le_imp_le_right eq_iff norm_ge_zero)
      done
  qed
next
  assume ?rhs then show ?lhs
    by (auto simp: set_eq_subset cball_subset_cball_iff)
qed

lemma ball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = cball y e \<longleftrightarrow> d \<le> 0 \<and> e < 0" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (auto simp: set_eq_subset ball_subset_cball_iff cball_subset_ball_iff algebra_simps)
    apply (metis add_increasing2 add_le_cancel_right add_less_same_cancel1 dist_not_less_zero less_le_trans zero_le_dist)
    apply (metis add_less_same_cancel1 dist_not_less_zero less_le_trans not_le)
    using \<open>?lhs\<close> ball_eq_empty cball_eq_empty apply blast+
    done
next
  assume ?rhs then show ?lhs by auto
qed

lemma cball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = ball y e \<longleftrightarrow> d < 0 \<and> e \<le> 0"
  using ball_eq_cball_iff by blast

lemma finite_ball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>ball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
proof -
  obtain e1 where "0 < e1" and e1_b:"ball p e1 \<subseteq> S"
    using open_contains_ball_eq[OF \<open>open S\<close>] assms by auto
  obtain e2 where "0 < e2" and "\<forall>x\<in>X. x \<noteq> p \<longrightarrow> e2 \<le> dist p x"
    using finite_set_avoid[OF \<open>finite X\<close>,of p] by auto
  hence "\<forall>w\<in>ball p (min e1 e2). w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)" using e1_b by auto
  thus "\<exists>e>0. \<forall>w\<in>ball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> X)" using \<open>e2>0\<close> \<open>e1>0\<close>
    apply (rule_tac x="min e1 e2" in exI)
    by auto
qed

lemma finite_cball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>cball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
proof -
  obtain e1 where "e1>0" and e1: "\<forall>w\<in>ball p e1. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
    using finite_ball_avoid[OF assms] by auto
  define e2 where "e2 \<equiv> e1/2"
  have "e2>0" and "e2 < e1" unfolding e2_def using \<open>e1>0\<close> by auto
  then have "cball p e2 \<subseteq> ball p e1" by (subst cball_subset_ball_iff,auto)
  then show "\<exists>e>0. \<forall>w\<in>cball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> X)" using \<open>e2>0\<close> e1 by auto
qed

lemma dim_cball:
  assumes "e > 0"
  shows "dim (cball (0 :: 'n::euclidean_space) e) = DIM('n)"
proof -
  {
    fix x :: "'n::euclidean_space"
    define y where "y = (e / norm x) *\<^sub>R x"
    then have "y \<in> cball 0 e"
      using assms by auto
    moreover have *: "x = (norm x / e) *\<^sub>R y"
      using y_def assms by simp
    moreover from * have "x = (norm x/e) *\<^sub>R y"
      by auto
    ultimately have "x \<in> span (cball 0 e)"
      using span_scale[of y "cball 0 e" "norm x/e"]
        span_superset[of "cball 0 e"]
      by (simp add: span_base)
  }
  then have "span (cball 0 e) = (UNIV :: 'n::euclidean_space set)"
    by auto
  then show ?thesis
    using dim_span[of "cball (0 :: 'n::euclidean_space) e"] by (auto)
qed


subsection \<open>Boxes\<close>

abbreviation\<^marker>\<open>tag important\<close> One :: "'a::euclidean_space" where
"One \<equiv> \<Sum>Basis"

lemma One_non_0: assumes "One = (0::'a::euclidean_space)" shows False
proof -
  have "dependent (Basis :: 'a set)"
    apply (simp add: dependent_finite)
    apply (rule_tac x="\<lambda>i. 1" in exI)
    using SOME_Basis apply (auto simp: assms)
    done
  with independent_Basis show False by force
qed

corollary\<^marker>\<open>tag unimportant\<close> One_neq_0[iff]: "One \<noteq> 0"
  by (metis One_non_0)

corollary\<^marker>\<open>tag unimportant\<close> Zero_neq_One[iff]: "0 \<noteq> One"
  by (metis One_non_0)

definition\<^marker>\<open>tag important\<close> (in euclidean_space) eucl_less (infix "<e" 50) where 
"eucl_less a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i)"

definition\<^marker>\<open>tag important\<close> box_eucl_less: "box a b = {x. a <e x \<and> x <e b}"
definition\<^marker>\<open>tag important\<close> "cbox a b = {x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i}"

lemma box_def: "box a b = {x. \<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i}"
  and in_box_eucl_less: "x \<in> box a b \<longleftrightarrow> a <e x \<and> x <e b"
  and mem_box: "x \<in> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i)"
    "x \<in> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i)"
  by (auto simp: box_eucl_less eucl_less_def cbox_def)

lemma cbox_Pair_eq: "cbox (a, c) (b, d) = cbox a b \<times> cbox c d"
  by (force simp: cbox_def Basis_prod_def)

lemma cbox_Pair_iff [iff]: "(x, y) \<in> cbox (a, c) (b, d) \<longleftrightarrow> x \<in> cbox a b \<and> y \<in> cbox c d"
  by (force simp: cbox_Pair_eq)

lemma cbox_Complex_eq: "cbox (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (cbox a b \<times> cbox c d)"
  apply (auto simp: cbox_def Basis_complex_def)
  apply (rule_tac x = "(Re x, Im x)" in image_eqI)
  using complex_eq by auto

lemma cbox_Pair_eq_0: "cbox (a, c) (b, d) = {} \<longleftrightarrow> cbox a b = {} \<or> cbox c d = {}"
  by (force simp: cbox_Pair_eq)

lemma swap_cbox_Pair [simp]: "prod.swap ` cbox (c, a) (d, b) = cbox (a,c) (b,d)"
  by auto

lemma mem_box_real[simp]:
  "(x::real) \<in> box a b \<longleftrightarrow> a < x \<and> x < b"
  "(x::real) \<in> cbox a b \<longleftrightarrow> a \<le> x \<and> x \<le> b"
  by (auto simp: mem_box)

lemma box_real[simp]:
  fixes a b:: real
  shows "box a b = {a <..< b}" "cbox a b = {a .. b}"
  by auto

lemma box_Int_box:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<inter> box c d =
    box (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box by auto

lemma rational_boxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> box a b \<and> box a b \<subseteq> ball x e"
proof -
  define e' where "e' = e / (2 * sqrt (real (DIM ('a))))"
  then have e: "e' > 0"
    using assms by (auto)
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x \<bullet> i \<and> x \<bullet> i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i - e'" "x \<bullet> i"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain a where
    a: "\<forall>xa. a xa \<in> \<rat> \<and> a xa < x \<bullet> xa \<and> x \<bullet> xa - a xa < e'" ..
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x \<bullet> i < y \<and> y - x \<bullet> i < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i" "x \<bullet> i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain b where
    b: "\<forall>xa. b xa \<in> \<rat> \<and> x \<bullet> xa < b xa \<and> b xa - x \<bullet> xa < e'" ..
  let ?a = "\<Sum>i\<in>Basis. a i *\<^sub>R i" and ?b = "\<Sum>i\<in>Basis. b i *\<^sub>R i"
  show ?thesis
  proof (rule exI[of _ ?a], rule exI[of _ ?b], safe)
    fix y :: 'a
    assume *: "y \<in> box ?a ?b"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      unfolding L2_set_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>(i::'a)\<in>Basis. e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule sum_strict_mono)
      fix i :: "'a"
      assume i: "i \<in> Basis"
      have "a i < y\<bullet>i \<and> y\<bullet>i < b i"
        using * i by (auto simp: box_def)
      moreover have "a i < x\<bullet>i" "x\<bullet>i - a i < e'"
        using a by auto
      moreover have "x\<bullet>i < b i" "b i - x\<bullet>i < e'"
        using b by auto
      ultimately have "\<bar>x\<bullet>i - y\<bullet>i\<bar> < 2 * e'"
        by auto
      then have "dist (x \<bullet> i) (y \<bullet> i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < (e/sqrt (real (DIM('a))))\<^sup>2"
        by (rule power_strict_mono) auto
      then show "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < e\<^sup>2 / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e"
      using \<open>0 < e\<close> by simp
    finally show "y \<in> ball x e"
      by (auto simp: ball_def)
  qed (insert a b, auto simp: box_def)
qed

lemma open_UNION_box:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. box (a' f) (b' f))"
proof -
  have "x \<in> (\<Union>f\<in>I. box (a' f) (b' f))" if "x \<in> M" for x
  proof -
    obtain e where e: "e > 0" "ball x e \<subseteq> M"
      using openE[OF \<open>open M\<close> \<open>x \<in> M\<close>] by auto
    moreover obtain a b where ab:
      "x \<in> box a b"
      "\<forall>i \<in> Basis. a \<bullet> i \<in> \<rat>"
      "\<forall>i\<in>Basis. b \<bullet> i \<in> \<rat>"
      "box a b \<subseteq> ball x e"
      using rational_boxes[OF e(1)] by metis
    ultimately show ?thesis
       by (intro UN_I[of "\<lambda>i\<in>Basis. (a \<bullet> i, b \<bullet> i)"])
          (auto simp: euclidean_representation I_def a'_def b'_def)
  qed
  then show ?thesis by (auto simp: I_def)
qed

corollary open_countable_Union_open_box:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = box a b" "\<Union>\<D> = S"
proof -
  let ?a = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  let ?b = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  let ?I = "{f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (?a f) (?b f) \<subseteq> S}"
  let ?\<D> = "(\<lambda>f. box (?a f) (?b f)) ` ?I"
  show ?thesis
  proof
    have "countable ?I"
      by (simp add: countable_PiE countable_rat)
    then show "countable ?\<D>"
      by blast
    show "\<Union>?\<D> = S"
      using open_UNION_box [OF assms] by metis
  qed auto
qed

lemma rational_cboxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> cbox a b \<and> cbox a b \<subseteq> ball x e"
proof -
  define e' where "e' = e / (2 * sqrt (real (DIM ('a))))"
  then have e: "e' > 0"
    using assms by auto
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x \<bullet> i \<and> x \<bullet> i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i - e'" "x \<bullet> i"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain a where
    a: "\<forall>u. a u \<in> \<rat> \<and> a u < x \<bullet> u \<and> x \<bullet> u - a u < e'" ..
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x \<bullet> i < y \<and> y - x \<bullet> i < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i" "x \<bullet> i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain b where
    b: "\<forall>u. b u \<in> \<rat> \<and> x \<bullet> u < b u \<and> b u - x \<bullet> u < e'" ..
  let ?a = "\<Sum>i\<in>Basis. a i *\<^sub>R i" and ?b = "\<Sum>i\<in>Basis. b i *\<^sub>R i"
  show ?thesis
  proof (rule exI[of _ ?a], rule exI[of _ ?b], safe)
    fix y :: 'a
    assume *: "y \<in> cbox ?a ?b"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      unfolding L2_set_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>(i::'a)\<in>Basis. e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule sum_strict_mono)
      fix i :: "'a"
      assume i: "i \<in> Basis"
      have "a i \<le> y\<bullet>i \<and> y\<bullet>i \<le> b i"
        using * i by (auto simp: cbox_def)
      moreover have "a i < x\<bullet>i" "x\<bullet>i - a i < e'"
        using a by auto
      moreover have "x\<bullet>i < b i" "b i - x\<bullet>i < e'"
        using b by auto
      ultimately have "\<bar>x\<bullet>i - y\<bullet>i\<bar> < 2 * e'"
        by auto
      then have "dist (x \<bullet> i) (y \<bullet> i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < (e/sqrt (real (DIM('a))))\<^sup>2"
        by (rule power_strict_mono) auto
      then show "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < e\<^sup>2 / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e"
      using \<open>0 < e\<close> by simp
    finally show "y \<in> ball x e"
      by (auto simp: ball_def)
  next
    show "x \<in> cbox (\<Sum>i\<in>Basis. a i *\<^sub>R i) (\<Sum>i\<in>Basis. b i *\<^sub>R i)"
      using a b less_imp_le by (auto simp: cbox_def)
  qed (use a b cbox_def in auto)
qed

lemma open_UNION_cbox:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. cbox (a' f) (b' f))"
proof -
  have "x \<in> (\<Union>f\<in>I. cbox (a' f) (b' f))" if "x \<in> M" for x
  proof -
    obtain e where e: "e > 0" "ball x e \<subseteq> M"
      using openE[OF \<open>open M\<close> \<open>x \<in> M\<close>] by auto
    moreover obtain a b where ab: "x \<in> cbox a b" "\<forall>i \<in> Basis. a \<bullet> i \<in> \<rat>"
                                  "\<forall>i \<in> Basis. b \<bullet> i \<in> \<rat>" "cbox a b \<subseteq> ball x e"
      using rational_cboxes[OF e(1)] by metis
    ultimately show ?thesis
       by (intro UN_I[of "\<lambda>i\<in>Basis. (a \<bullet> i, b \<bullet> i)"])
          (auto simp: euclidean_representation I_def a'_def b'_def)
  qed
  then show ?thesis by (auto simp: I_def)
qed

corollary open_countable_Union_open_cbox:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" "\<Union>\<D> = S"
proof -
  let ?a = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  let ?b = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  let ?I = "{f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (?a f) (?b f) \<subseteq> S}"
  let ?\<D> = "(\<lambda>f. cbox (?a f) (?b f)) ` ?I"
  show ?thesis
  proof
    have "countable ?I"
      by (simp add: countable_PiE countable_rat)
    then show "countable ?\<D>"
      by blast
    show "\<Union>?\<D> = S"
      using open_UNION_cbox [OF assms] by metis
  qed auto
qed

lemma box_eq_empty:
  fixes a :: "'a::euclidean_space"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i < a\<bullet>i))" (is ?th2)
proof -
  {
    fix i x
    assume i: "i\<in>Basis" and as:"b\<bullet>i \<le> a\<bullet>i" and x:"x\<in>box a b"
    then have "a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i"
      unfolding mem_box by (auto simp: box_def)
    then have "a\<bullet>i < b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as: "\<forall>i\<in>Basis. \<not> (b\<bullet>i \<le> a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "a\<bullet>i < b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i < ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i < b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "box a b \<noteq> {}"
      using mem_box(1)[of "?x" a b] by auto
  }
  ultimately show ?th1 by blast

  {
    fix i x
    assume i: "i \<in> Basis" and as:"b\<bullet>i < a\<bullet>i" and x:"x\<in>cbox a b"
    then have "a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
      unfolding mem_box by auto
    then have "a\<bullet>i \<le> b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as:"\<forall>i\<in>Basis. \<not> (b\<bullet>i < a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i:"i \<in> Basis"
      have "a\<bullet>i \<le> b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i \<le> ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i \<le> b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "cbox a b \<noteq> {}"
      using mem_box(2)[of "?x" a b] by auto
  }
  ultimately show ?th2 by blast
qed

lemma box_ne_empty:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i)"
  and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  unfolding box_eq_empty[of a b] by fastforce+

lemma
  fixes a :: "'a::euclidean_space"
  shows cbox_sing [simp]: "cbox a a = {a}"
    and box_sing [simp]: "box a a = {}"
  unfolding set_eq_iff mem_box eq_iff [symmetric]
  by (auto intro!: euclidean_eqI[where 'a='a])
     (metis all_not_in_conv nonempty_Basis)

lemma subset_box_imp:
  fixes a :: "'a::euclidean_space"
  shows "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> cbox a b"
     and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box
  by (best intro: order_trans less_le_trans le_less_trans less_imp_le)+

lemma box_subset_cbox:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<subseteq> cbox a b"
  unfolding subset_eq [unfolded Ball_def] mem_box
  by (fast intro: less_imp_le)

lemma subset_box:
  fixes a :: "'a::euclidean_space"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th4)
proof -
  let ?lesscd = "\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i"
  let ?lerhs = "\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
  show ?th1 ?th2
    by (fastforce simp: mem_box)+
  have acdb: "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
    if i: "i \<in> Basis" and box: "box c d \<subseteq> cbox a b" and cd: "\<And>i. i \<in> Basis \<Longrightarrow> c\<bullet>i < d\<bullet>i" for i
  proof -
    have "box c d \<noteq> {}"
      using that
      unfolding box_eq_empty by force
    { let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((min (a\<bullet>j) (d\<bullet>j))+c\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume *: "a\<bullet>i > c\<bullet>i"
      then have "c \<bullet> j < ?x \<bullet> j \<and> ?x \<bullet> j < d \<bullet> j" if "j \<in> Basis" for j
        using cd that by (fastforce simp add: i *)
      then have "?x \<in> box c d"
        unfolding mem_box by auto
      moreover have "?x \<notin> cbox a b"
        using i cd * by (force simp: mem_box)
      ultimately have False using box by auto
    }
    then have "a\<bullet>i \<le> c\<bullet>i" by force
    moreover
    { let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((max (b\<bullet>j) (c\<bullet>j))+d\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume *: "b\<bullet>i < d\<bullet>i"
      then have "d \<bullet> j > ?x \<bullet> j \<and> ?x \<bullet> j > c \<bullet> j" if "j \<in> Basis" for j
        using cd that by (fastforce simp add: i *)
      then have "?x \<in> box c d"
        unfolding mem_box by auto
      moreover have "?x \<notin> cbox a b"
        using i cd * by (force simp: mem_box)
      ultimately have False using box by auto
    }
    then have "b\<bullet>i \<ge> d\<bullet>i" by (rule ccontr) auto
    ultimately show ?thesis by auto
  qed
  show ?th3
    using acdb by (fastforce simp add: mem_box)
  have acdb': "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
    if "i \<in> Basis" "box c d \<subseteq> box a b" "\<And>i. i \<in> Basis \<Longrightarrow> c\<bullet>i < d\<bullet>i" for i
      using box_subset_cbox[of a b] that acdb by auto
  show ?th4
    using acdb' by (fastforce simp add: mem_box)
qed

lemma eq_cbox: "cbox a b = cbox c d \<longleftrightarrow> cbox a b = {} \<and> cbox c d = {} \<or> a = c \<and> b = d"
      (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "cbox a b \<subseteq> cbox c d" "cbox c d \<subseteq> cbox a b"
    by auto
  then show ?rhs
    by (force simp: subset_box box_eq_empty intro: antisym euclidean_eqI)
next
  assume ?rhs
  then show ?lhs
    by force
qed

lemma eq_cbox_box [simp]: "cbox a b = box c d \<longleftrightarrow> cbox a b = {} \<and> box c d = {}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  then have "cbox a b \<subseteq> box c d" "box c d \<subseteq> cbox a b"
    by auto
  then show ?rhs
    apply (simp add: subset_box)
    using L box_ne_empty box_sing apply (fastforce simp add:)
    done
qed force

lemma eq_box_cbox [simp]: "box a b = cbox c d \<longleftrightarrow> box a b = {} \<and> cbox c d = {}"
  by (metis eq_cbox_box)

lemma eq_box: "box a b = box c d \<longleftrightarrow> box a b = {} \<and> box c d = {} \<or> a = c \<and> b = d"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  then have "box a b \<subseteq> box c d" "box c d \<subseteq> box a b"
    by auto
  then show ?rhs
    apply (simp add: subset_box)
    using box_ne_empty(2) L
    apply auto
     apply (meson euclidean_eqI less_eq_real_def not_less)+
    done
qed force

lemma subset_box_complex:
   "cbox a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "cbox a b \<subseteq> box c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a > Re c \<and> Im a > Im c \<and> Re b < Re d \<and> Im b < Im d"
   "box a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "box a b \<subseteq> box c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
  by (subst subset_box; force simp: Basis_complex_def)+

lemma in_cbox_complex_iff:
  "x \<in> cbox a b \<longleftrightarrow> Re x \<in> {Re a..Re b} \<and> Im x \<in> {Im a..Im b}"
  by (cases x; cases a; cases b) (auto simp: cbox_Complex_eq)

lemma box_Complex_eq:
  "box (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (box a b \<times> box c d)"
  by (auto simp: box_def Basis_complex_def image_iff complex_eq_iff)

lemma in_box_complex_iff:
  "x \<in> box a b \<longleftrightarrow> Re x \<in> {Re a<..<Re b} \<and> Im x \<in> {Im a<..<Im b}"
  by (cases x; cases a; cases b) (auto simp: box_Complex_eq)

lemma Int_interval:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d =
    cbox (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box
  by auto

lemma disjoint_interval:
  fixes a::"'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i < c\<bullet>i \<or> d\<bullet>i < a\<bullet>i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th4)
proof -
  let ?z = "(\<Sum>i\<in>Basis. (((max (a\<bullet>i) (c\<bullet>i)) + (min (b\<bullet>i) (d\<bullet>i))) / 2) *\<^sub>R i)::'a"
  have **: "\<And>P Q. (\<And>i :: 'a. i \<in> Basis \<Longrightarrow> Q ?z i \<Longrightarrow> P i) \<Longrightarrow>
      (\<And>i x :: 'a. i \<in> Basis \<Longrightarrow> P i \<Longrightarrow> Q x i) \<Longrightarrow> (\<forall>x. \<exists>i\<in>Basis. Q x i) \<longleftrightarrow> (\<exists>i\<in>Basis. P i)"
    by blast
  note * = set_eq_iff Int_iff empty_iff mem_box ball_conj_distrib[symmetric] eq_False ball_simps(10)
  show ?th1 unfolding * by (intro **) auto
  show ?th2 unfolding * by (intro **) auto
  show ?th3 unfolding * by (intro **) auto
  show ?th4 unfolding * by (intro **) auto
qed

lemma UN_box_eq_UNIV: "(\<Union>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One)) = UNIV"
proof -
  have "\<bar>x \<bullet> b\<bar> < real_of_int (\<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil> + 1)"
    if [simp]: "b \<in> Basis" for x b :: 'a
  proof -
    have "\<bar>x \<bullet> b\<bar> \<le> real_of_int \<lceil>\<bar>x \<bullet> b\<bar>\<rceil>"
      by (rule le_of_int_ceiling)
    also have "\<dots> \<le> real_of_int \<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil>"
      by (auto intro!: ceiling_mono)
    also have "\<dots> < real_of_int (\<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil> + 1)"
      by simp
    finally show ?thesis .
  qed
  then have "\<exists>n::nat. \<forall>b\<in>Basis. \<bar>x \<bullet> b\<bar> < real n" for x :: 'a
    by (metis order.strict_trans reals_Archimedean2)
  moreover have "\<And>x b::'a. \<And>n::nat.  \<bar>x \<bullet> b\<bar> < real n \<longleftrightarrow> - real n < x \<bullet> b \<and> x \<bullet> b < real n"
    by auto
  ultimately show ?thesis
    by (auto simp: box_def inner_sum_left inner_Basis sum.If_cases)
qed

lemma image_affinity_cbox: fixes m::real
  fixes a b c :: "'a::euclidean_space"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` cbox a b =
    (if cbox a b = {} then {}
     else (if 0 \<le> m then cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)
     else cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c)))"
proof (cases "m = 0")
  case True
  {
    fix x
    assume "\<forall>i\<in>Basis. x \<bullet> i \<le> c \<bullet> i" "\<forall>i\<in>Basis. c \<bullet> i \<le> x \<bullet> i"
    then have "x = c"
      by (simp add: dual_order.antisym euclidean_eqI)
  }
  moreover have "c \<in> cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)"
    unfolding True by (auto)
  ultimately show ?thesis using True by (auto simp: cbox_def)
next
  case False
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m > 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
      by (auto simp: inner_distrib)
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m < 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i"
      by (auto simp: mult_left_mono_neg inner_distrib)
  }
  moreover
  {
    fix y
    assume "m > 0" and "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> y \<bullet> i" and "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp: pos_le_divide_eq pos_divide_le_eq mult.commute inner_distrib inner_diff_left)
      done
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i" "m < 0"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp: neg_le_divide_eq neg_divide_le_eq mult.commute inner_distrib inner_diff_left)
      done
  }
  ultimately show ?thesis using False by (auto simp: cbox_def)
qed

lemma image_smult_cbox:"(\<lambda>x. m *\<^sub>R (x::_::euclidean_space)) ` cbox a b =
  (if cbox a b = {} then {} else if 0 \<le> m then cbox (m *\<^sub>R a) (m *\<^sub>R b) else cbox (m *\<^sub>R b) (m *\<^sub>R a))"
  using image_affinity_cbox[of m 0 a b] by auto

lemma swap_continuous:
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "continuous_on (cbox (c,a) (d,b)) (\<lambda>(x, y). f y x)"
proof -
  have "(\<lambda>(x, y). f y x) = (\<lambda>(x, y). f x y) \<circ> prod.swap"
    by auto
  then show ?thesis
    apply (rule ssubst)
    apply (rule continuous_on_compose)
    apply (simp add: split_def)
    apply (rule continuous_intros | simp add: assms)+
    done
qed


subsection \<open>General Intervals\<close>

definition\<^marker>\<open>tag important\<close> "is_interval (s::('a::euclidean_space) set) \<longleftrightarrow>
  (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i\<in>Basis. ((a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i) \<or> (b\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> a\<bullet>i))) \<longrightarrow> x \<in> s)"

lemma is_interval_1:
  "is_interval (s::real set) \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall> x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> s)"
  unfolding is_interval_def by auto

lemma is_interval_Int: "is_interval X \<Longrightarrow> is_interval Y \<Longrightarrow> is_interval (X \<inter> Y)"
  unfolding is_interval_def
  by blast

lemma is_interval_cbox [simp]: "is_interval (cbox a (b::'a::euclidean_space))" (is ?th1)
  and is_interval_box [simp]: "is_interval (box a b)" (is ?th2)
  unfolding is_interval_def mem_box Ball_def atLeastAtMost_iff
  by (meson order_trans le_less_trans less_le_trans less_trans)+

lemma is_interval_empty [iff]: "is_interval {}"
  unfolding is_interval_def  by simp

lemma is_interval_univ [iff]: "is_interval UNIV"
  unfolding is_interval_def  by simp

lemma mem_is_intervalI:
  assumes "is_interval s"
    and "a \<in> s" "b \<in> s"
    and "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i \<or> b \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i"
  shows "x \<in> s"
  by (rule assms(1)[simplified is_interval_def, rule_format, OF assms(2,3,4)])

lemma interval_subst:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
    and "x \<in> S" "y j \<in> S"
    and "j \<in> Basis"
  shows "(\<Sum>i\<in>Basis. (if i = j then y i \<bullet> i else x \<bullet> i) *\<^sub>R i) \<in> S"
  by (rule mem_is_intervalI[OF assms(1,2)]) (auto simp: assms)

lemma mem_box_componentwiseI:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<in> ((\<lambda>x. x \<bullet> i) ` S)"
  shows "x \<in> S"
proof -
  from assms have "\<forall>i \<in> Basis. \<exists>s \<in> S. x \<bullet> i = s \<bullet> i"
    by auto
  with finite_Basis obtain s and bs::"'a list"
    where s: "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i = s i \<bullet> i" "\<And>i. i \<in> Basis \<Longrightarrow> s i \<in> S"
      and bs: "set bs = Basis" "distinct bs"
    by (metis finite_distinct_list)
  from nonempty_Basis s obtain j where j: "j \<in> Basis" "s j \<in> S"
    by blast
  define y where
    "y = rec_list (s j) (\<lambda>j _ Y. (\<Sum>i\<in>Basis. (if i = j then s i \<bullet> i else Y \<bullet> i) *\<^sub>R i))"
  have "x = (\<Sum>i\<in>Basis. (if i \<in> set bs then s i \<bullet> i else s j \<bullet> i) *\<^sub>R i)"
    using bs by (auto simp: s(1)[symmetric] euclidean_representation)
  also have [symmetric]: "y bs = \<dots>"
    using bs(2) bs(1)[THEN equalityD1]
    by (induct bs) (auto simp: y_def euclidean_representation intro!: euclidean_eqI[where 'a='a])
  also have "y bs \<in> S"
    using bs(1)[THEN equalityD1]
    apply (induct bs)
     apply (auto simp: y_def j)
    apply (rule interval_subst[OF assms(1)])
      apply (auto simp: s)
    done
  finally show ?thesis .
qed

lemma cbox01_nonempty [simp]: "cbox 0 One \<noteq> {}"
  by (simp add: box_ne_empty inner_Basis inner_sum_left sum_nonneg)

lemma box01_nonempty [simp]: "box 0 One \<noteq> {}"
  by (simp add: box_ne_empty inner_Basis inner_sum_left)

lemma empty_as_interval: "{} = cbox One (0::'a::euclidean_space)"
  using nonempty_Basis box01_nonempty box_eq_empty(1) box_ne_empty(1) by blast

lemma interval_subset_is_interval:
  assumes "is_interval S"
  shows "cbox a b \<subseteq> S \<longleftrightarrow> cbox a b = {} \<or> a \<in> S \<and> b \<in> S" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs  using box_ne_empty(1) mem_box(2) by fastforce
next
  assume ?rhs
  have "cbox a b \<subseteq> S" if "a \<in> S" "b \<in> S"
    using assms unfolding is_interval_def
    apply (clarsimp simp add: mem_box)
    using that by blast
  with \<open>?rhs\<close> show ?lhs
    by blast
qed

lemma is_real_interval_union:
  "is_interval (X \<union> Y)"
  if X: "is_interval X" and Y: "is_interval Y" and I: "(X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> X \<inter> Y \<noteq> {})"
  for X Y::"real set"
proof -
  consider "X \<noteq> {}" "Y \<noteq> {}" | "X = {}" | "Y = {}" by blast
  then show ?thesis
  proof cases
    case 1
    then obtain r where "r \<in> X \<or> X \<inter> Y = {}" "r \<in> Y \<or> X \<inter> Y = {}"
      by blast
    then show ?thesis
      using I 1 X Y unfolding is_interval_1
      by (metis (full_types) Un_iff le_cases)
  qed (use that in auto)
qed

lemma is_interval_translationI:
  assumes "is_interval X"
  shows "is_interval ((+) x ` X)"
  unfolding is_interval_def
proof safe
  fix b d e
  assume "b \<in> X" "d \<in> X"
    "\<forall>i\<in>Basis. (x + b) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (x + d) \<bullet> i \<or>
       (x + d) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (x + b) \<bullet> i"
  hence "e - x \<in> X"
    by (intro mem_is_intervalI[OF assms \<open>b \<in> X\<close> \<open>d \<in> X\<close>, of "e - x"])
      (auto simp: algebra_simps)
  thus "e \<in> (+) x ` X" by force
qed

lemma is_interval_uminusI:
  assumes "is_interval X"
  shows "is_interval (uminus ` X)"
  unfolding is_interval_def
proof safe
  fix b d e
  assume "b \<in> X" "d \<in> X"
    "\<forall>i\<in>Basis. (- b) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (- d) \<bullet> i \<or>
       (- d) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (- b) \<bullet> i"
  hence "- e \<in> X"
    by (intro mem_is_intervalI[OF assms \<open>b \<in> X\<close> \<open>d \<in> X\<close>, of "- e"])
      (auto simp: algebra_simps)
  thus "e \<in> uminus ` X" by force
qed

lemma is_interval_uminus[simp]: "is_interval (uminus ` x) = is_interval x"
  using is_interval_uminusI[of x] is_interval_uminusI[of "uminus ` x"]
  by (auto simp: image_image)

lemma is_interval_neg_translationI:
  assumes "is_interval X"
  shows "is_interval ((-) x ` X)"
proof -
  have "(-) x ` X = (+) x ` uminus ` X"
    by (force simp: algebra_simps)
  also have "is_interval \<dots>"
    by (metis is_interval_uminusI is_interval_translationI assms)
  finally show ?thesis .
qed

lemma is_interval_translation[simp]:
  "is_interval ((+) x ` X) = is_interval X"
  using is_interval_neg_translationI[of "(+) x ` X" x]
  by (auto intro!: is_interval_translationI simp: image_image)

lemma is_interval_minus_translation[simp]:
  shows "is_interval ((-) x ` X) = is_interval X"
proof -
  have "(-) x ` X = (+) x ` uminus ` X"
    by (force simp: algebra_simps)
  also have "is_interval \<dots> = is_interval X"
    by simp
  finally show ?thesis .
qed

lemma is_interval_minus_translation'[simp]:
  shows "is_interval ((\<lambda>x. x - c) ` X) = is_interval X"
  using is_interval_translation[of "-c" X]
  by (metis image_cong uminus_add_conv_diff)

lemma is_interval_cball_1[intro, simp]: "is_interval (cball a b)" for a b::real
  by (simp add: cball_eq_atLeastAtMost is_interval_def)

lemma is_interval_ball_real: "is_interval (ball a b)" for a b::real
  by (simp add: ball_eq_greaterThanLessThan is_interval_def)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounded Projections\<close>

lemma bounded_inner_imp_bdd_above:
  assumes "bounded s"
    shows "bdd_above ((\<lambda>x. x \<bullet> a) ` s)"
by (simp add: assms bounded_imp_bdd_above bounded_linear_image bounded_linear_inner_left)

lemma bounded_inner_imp_bdd_below:
  assumes "bounded s"
    shows "bdd_below ((\<lambda>x. x \<bullet> a) ` s)"
by (simp add: assms bounded_imp_bdd_below bounded_linear_image bounded_linear_inner_left)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Structural rules for pointwise continuity\<close>

lemma continuous_infnorm[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. infnorm (f x))"
  unfolding continuous_def by (rule tendsto_infnorm)

lemma continuous_inner[continuous_intros]:
  assumes "continuous F f"
    and "continuous F g"
  shows "continuous F (\<lambda>x. inner (f x) (g x))"
  using assms unfolding continuous_def by (rule tendsto_inner)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Structural rules for setwise continuity\<close>

lemma continuous_on_infnorm[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. infnorm (f x))"
  unfolding continuous_on by (fast intro: tendsto_infnorm)

lemma continuous_on_inner[continuous_intros]:
  fixes g :: "'a::topological_space \<Rightarrow> 'b::real_inner"
  assumes "continuous_on s f"
    and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. inner (f x) (g x))"
  using bounded_bilinear_inner assms
  by (rule bounded_bilinear.continuous_on)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Openness of halfspaces.\<close>

lemma open_halfspace_lt: "open {x. inner a x < b}"
  by (simp add: open_Collect_less continuous_on_inner)

lemma open_halfspace_gt: "open {x. inner a x > b}"
  by (simp add: open_Collect_less continuous_on_inner)

lemma open_halfspace_component_lt: "open {x::'a::euclidean_space. x\<bullet>i < a}"
  by (simp add: open_Collect_less continuous_on_inner)

lemma open_halfspace_component_gt: "open {x::'a::euclidean_space. x\<bullet>i > a}"
  by (simp add: open_Collect_less continuous_on_inner)

lemma eucl_less_eq_halfspaces:
  fixes a :: "'a::euclidean_space"
  shows "{x. x <e a} = (\<Inter>i\<in>Basis. {x. x \<bullet> i < a \<bullet> i})"
        "{x. a <e x} = (\<Inter>i\<in>Basis. {x. a \<bullet> i < x \<bullet> i})"
  by (auto simp: eucl_less_def)

lemma open_Collect_eucl_less[simp, intro]:
  fixes a :: "'a::euclidean_space"
  shows "open {x. x <e a}" "open {x. a <e x}"
  by (auto simp: eucl_less_eq_halfspaces open_halfspace_component_lt open_halfspace_component_gt)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Closure and Interior of halfspaces and hyperplanes\<close>

lemma continuous_at_inner: "continuous (at x) (inner a)"
  unfolding continuous_at by (intro tendsto_intros)

lemma closed_halfspace_le: "closed {x. inner a x \<le> b}"
  by (simp add: closed_Collect_le continuous_on_inner)

lemma closed_halfspace_ge: "closed {x. inner a x \<ge> b}"
  by (simp add: closed_Collect_le continuous_on_inner)

lemma closed_hyperplane: "closed {x. inner a x = b}"
  by (simp add: closed_Collect_eq continuous_on_inner)

lemma closed_halfspace_component_le: "closed {x::'a::euclidean_space. x\<bullet>i \<le> a}"
  by (simp add: closed_Collect_le continuous_on_inner)

lemma closed_halfspace_component_ge: "closed {x::'a::euclidean_space. x\<bullet>i \<ge> a}"
  by (simp add: closed_Collect_le continuous_on_inner)

lemma closed_interval_left:
  fixes b :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. x\<bullet>i \<le> b\<bullet>i}"
  by (simp add: Collect_ball_eq closed_INT closed_Collect_le continuous_on_inner)

lemma closed_interval_right:
  fixes a :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. a\<bullet>i \<le> x\<bullet>i}"
  by (simp add: Collect_ball_eq closed_INT closed_Collect_le continuous_on_inner)

lemma interior_halfspace_le [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x \<le> b} = {x. a \<bullet> x < b}"
proof -
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

lemma interior_halfspace_ge [simp]:
   "a \<noteq> 0 \<Longrightarrow> interior {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x > b}"
using interior_halfspace_le [of "-a" "-b"] by simp

lemma closure_halfspace_lt [simp]:
  assumes "a \<noteq> 0"
    shows "closure {x. a \<bullet> x < b} = {x. a \<bullet> x \<le> b}"
proof -
  have [simp]: "-{x. a \<bullet> x < b} = {x. a \<bullet> x \<ge> b}"
    by (force simp:)
  then show ?thesis
    using interior_halfspace_ge [of a b] assms
    by (force simp: closure_interior)
qed

lemma closure_halfspace_gt [simp]:
   "a \<noteq> 0 \<Longrightarrow> closure {x. a \<bullet> x > b} = {x. a \<bullet> x \<ge> b}"
using closure_halfspace_lt [of "-a" "-b"] by simp

lemma interior_hyperplane [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x = b} = {}"
proof -
  have [simp]: "{x. a \<bullet> x = b} = {x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x \<ge> b}"
    by (force simp:)
  then show ?thesis
    by (auto simp: assms)
qed

lemma frontier_halfspace_le:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<le> b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def closed_halfspace_le)
qed

lemma frontier_halfspace_ge:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def closed_halfspace_ge)
qed

lemma frontier_halfspace_lt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x < b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def interior_open open_halfspace_lt)
qed

lemma frontier_halfspace_gt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x > b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def interior_open open_halfspace_gt)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Some more convenient intermediate-value theorem formulations\<close>

lemma connected_ivt_hyperplane:
  assumes "connected S" and xy: "x \<in> S" "y \<in> S" and b: "inner a x \<le> b" "b \<le> inner a y"
  shows "\<exists>z \<in> S. inner a z = b"
proof (rule ccontr)
  assume as:"\<not> (\<exists>z\<in>S. inner a z = b)"
  let ?A = "{x. inner a x < b}"
  let ?B = "{x. inner a x > b}"
  have "open ?A" "open ?B"
    using open_halfspace_lt and open_halfspace_gt by auto
  moreover have "?A \<inter> ?B = {}" by auto
  moreover have "S \<subseteq> ?A \<union> ?B" using as by auto
  ultimately show False
    using \<open>connected S\<close>[unfolded connected_def not_ex,
      THEN spec[where x="?A"], THEN spec[where x="?B"]]
    using xy b by auto
qed

lemma connected_ivt_component:
  fixes x::"'a::euclidean_space"
  shows "connected S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x\<bullet>k \<le> a \<Longrightarrow> a \<le> y\<bullet>k \<Longrightarrow> (\<exists>z\<in>S.  z\<bullet>k = a)"
  using connected_ivt_hyperplane[of S x y "k::'a" a]
  by (auto simp: inner_commute)


subsection \<open>Limit Component Bounds\<close>

lemma Lim_component_le:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. f(x)\<bullet>i \<le> b) net"
  shows "l\<bullet>i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_inner[OF assms(1) tendsto_const] assms(3)])

lemma Lim_component_ge:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. b \<le> (f x)\<bullet>i) net"
  shows "b \<le> l\<bullet>i"
  by (rule tendsto_le[OF assms(2) tendsto_inner[OF assms(1) tendsto_const] tendsto_const assms(3)])

lemma Lim_component_eq:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes net: "(f \<longlongrightarrow> l) net" "\<not> trivial_limit net"
    and ev:"eventually (\<lambda>x. f(x)\<bullet>i = b) net"
  shows "l\<bullet>i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff]
  using Lim_component_ge[OF net, of b i]
  using Lim_component_le[OF net, of i b]
  by auto

lemma open_box[intro]: "open (box a b)"
proof -
  have "open (\<Inter>i\<in>Basis. ((\<bullet>) i) -` {a \<bullet> i <..< b \<bullet> i})"
    by (auto intro!: continuous_open_vimage continuous_inner continuous_ident continuous_const)
  also have "(\<Inter>i\<in>Basis. ((\<bullet>) i) -` {a \<bullet> i <..< b \<bullet> i}) = box a b"
    by (auto simp: box_def inner_commute)
  finally show ?thesis .
qed

lemma closed_cbox[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "closed (cbox a b)"
proof -
  have "closed (\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i})"
    by (intro closed_INT ballI continuous_closed_vimage allI
      linear_continuous_at closed_real_atLeastAtMost finite_Basis bounded_linear_inner_left)
  also have "(\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i}) = cbox a b"
    by (auto simp: cbox_def)
  finally show "closed (cbox a b)" .
qed

lemma interior_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "interior (cbox a b) = box a b" (is "?L = ?R")
proof(rule subset_antisym)
  show "?R \<subseteq> ?L"
    using box_subset_cbox open_box
    by (rule interior_maximal)
  {
    fix x
    assume "x \<in> interior (cbox a b)"
    then obtain s where s: "open s" "x \<in> s" "s \<subseteq> cbox a b" ..
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> cbox a b"
      unfolding open_dist and subset_eq by auto
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "dist (x - (e / 2) *\<^sub>R i) x < e"
        and "dist (x + (e / 2) *\<^sub>R i) x < e"
        unfolding dist_norm
        apply auto
        unfolding norm_minus_cancel
        using norm_Basis[OF i] \<open>e>0\<close>
        apply auto
        done
      then have "a \<bullet> i \<le> (x - (e / 2) *\<^sub>R i) \<bullet> i" and "(x + (e / 2) *\<^sub>R i) \<bullet> i \<le> b \<bullet> i"
        using e[THEN spec[where x="x - (e/2) *\<^sub>R i"]]
          and e[THEN spec[where x="x + (e/2) *\<^sub>R i"]]
        unfolding mem_box
        using i
        by blast+
      then have "a \<bullet> i < x \<bullet> i" and "x \<bullet> i < b \<bullet> i"
        using \<open>e>0\<close> i
        by (auto simp: inner_diff_left inner_Basis inner_add_left)
    }
    then have "x \<in> box a b"
      unfolding mem_box by auto
  }
  then show "?L \<subseteq> ?R" ..
qed

lemma bounded_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (cbox a b)"
proof -
  let ?b = "\<Sum>i\<in>Basis. \<bar>a\<bullet>i\<bar> + \<bar>b\<bullet>i\<bar>"
  {
    fix x :: "'a"
    assume "\<And>i. i\<in>Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
    then have "(\<Sum>i\<in>Basis. \<bar>x \<bullet> i\<bar>) \<le> ?b"
      by (force simp: intro!: sum_mono)
    then have "norm x \<le> ?b"
      using norm_le_l1[of x] by auto
  }
  then show ?thesis
    unfolding cbox_def bounded_iff by force
qed

lemma bounded_box [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (box a b)"
  using bounded_cbox[of a b] box_subset_cbox[of a b] bounded_subset[of "cbox a b" "box a b"]
  by simp

lemma not_interval_UNIV [simp]:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> UNIV" "box a b \<noteq> UNIV"
  using bounded_box[of a b] bounded_cbox[of a b] by force+

lemma not_interval_UNIV2 [simp]:
  fixes a :: "'a::euclidean_space"
  shows "UNIV \<noteq> cbox a b" "UNIV \<noteq> box a b"
  using bounded_box[of a b] bounded_cbox[of a b] by force+

lemma box_midpoint:
  fixes a :: "'a::euclidean_space"
  assumes "box a b \<noteq> {}"
  shows "((1/2) *\<^sub>R (a + b)) \<in> box a b"
proof -
  have "a \<bullet> i < ((1 / 2) *\<^sub>R (a + b)) \<bullet> i \<and> ((1 / 2) *\<^sub>R (a + b)) \<bullet> i < b \<bullet> i" if "i \<in> Basis" for i
    using assms that by (auto simp: inner_add_left box_ne_empty)
  then show ?thesis unfolding mem_box by auto
qed

lemma open_cbox_convex:
  fixes x :: "'a::euclidean_space"
  assumes x: "x \<in> box a b"
    and y: "y \<in> cbox a b"
    and e: "0 < e" "e \<le> 1"
  shows "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<in> box a b"
proof -
  {
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "a \<bullet> i = e * (a \<bullet> i) + (1 - e) * (a \<bullet> i)"
      unfolding left_diff_distrib by simp
    also have "\<dots> < e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
    proof (rule add_less_le_mono)
      show "e * (a \<bullet> i) < e * (x \<bullet> i)"
        using \<open>0 < e\<close> i mem_box(1) x by auto
      show "(1 - e) * (a \<bullet> i) \<le> (1 - e) * (y \<bullet> i)"
        by (meson diff_ge_0_iff_ge \<open>e \<le> 1\<close> i mem_box(2) mult_left_mono y)
    qed
    finally have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i"
      unfolding inner_simps by auto
    moreover
    {
      have "b \<bullet> i = e * (b\<bullet>i) + (1 - e) * (b\<bullet>i)"
        unfolding left_diff_distrib by simp
      also have "\<dots> > e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
      proof (rule add_less_le_mono)
        show "e * (x \<bullet> i) < e * (b \<bullet> i)"
          using \<open>0 < e\<close> i mem_box(1) x by auto
        show "(1 - e) * (y \<bullet> i) \<le> (1 - e) * (b \<bullet> i)"
          by (meson diff_ge_0_iff_ge \<open>e \<le> 1\<close> i mem_box(2) mult_left_mono y)
      qed
      finally have "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
        unfolding inner_simps by auto
    }
    ultimately have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i \<and> (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
      by auto
  }
  then show ?thesis
    unfolding mem_box by auto
qed

lemma closure_cbox [simp]: "closure (cbox a b) = cbox a b"
  by (simp add: closed_cbox)

lemma closure_box [simp]:
  fixes a :: "'a::euclidean_space"
   assumes "box a b \<noteq> {}"
  shows "closure (box a b) = cbox a b"
proof -
  have ab: "a <e b"
    using assms by (simp add: eucl_less_def box_ne_empty)
  let ?c = "(1 / 2) *\<^sub>R (a + b)"
  {
    fix x
    assume as:"x \<in> cbox a b"
    define f where [abs_def]: "f n = x + (inverse (real n + 1)) *\<^sub>R (?c - x)" for n
    {
      fix n
      assume fn: "f n <e b \<longrightarrow> a <e f n \<longrightarrow> f n = x" and xc: "x \<noteq> ?c"
      have *: "0 < inverse (real n + 1)" "inverse (real n + 1) \<le> 1"
        unfolding inverse_le_1_iff by auto
      have "(inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b)) + (1 - inverse (real n + 1)) *\<^sub>R x =
        x + (inverse (real n + 1)) *\<^sub>R (((1 / 2) *\<^sub>R (a + b)) - x)"
        by (auto simp: algebra_simps)
      then have "f n <e b" and "a <e f n"
        using open_cbox_convex[OF box_midpoint[OF assms] as *]
        unfolding f_def by (auto simp: box_def eucl_less_def)
      then have False
        using fn unfolding f_def using xc by auto
    }
    moreover
    {
      assume "\<not> (f \<longlongrightarrow> x) sequentially"
      {
        fix e :: real
        assume "e > 0"
        then obtain N :: nat where N: "inverse (real (N + 1)) < e"
          using reals_Archimedean by auto
        have "inverse (real n + 1) < e" if "N \<le> n" for n
          by (auto intro!: that le_less_trans [OF _ N])
        then have "\<exists>N::nat. \<forall>n\<ge>N. inverse (real n + 1) < e" by auto
      }
      then have "((\<lambda>n. inverse (real n + 1)) \<longlongrightarrow> 0) sequentially"
        unfolding lim_sequentially by(auto simp: dist_norm)
      then have "(f \<longlongrightarrow> x) sequentially"
        unfolding f_def
        using tendsto_add[OF tendsto_const, of "\<lambda>n::nat. (inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x)" 0 sequentially x]
        using tendsto_scaleR [OF _ tendsto_const, of "\<lambda>n::nat. inverse (real n + 1)" 0 sequentially "((1 / 2) *\<^sub>R (a + b) - x)"]
        by auto
    }
    ultimately have "x \<in> closure (box a b)"
      using as box_midpoint[OF assms]
      unfolding closure_def islimpt_sequential
      by (cases "x=?c") (auto simp: in_box_eucl_less)
  }
  then show ?thesis
    using closure_minimal[OF box_subset_cbox, of a b] by blast
qed

lemma bounded_subset_box_symmetric:
  fixes S :: "('a::euclidean_space) set"
  assumes "bounded S"
  obtains a where "S \<subseteq> box (-a) a"
proof -
  obtain b where "b>0" and b: "\<forall>x\<in>S. norm x \<le> b"
    using assms[unfolded bounded_pos] by auto
  define a :: 'a where "a = (\<Sum>i\<in>Basis. (b + 1) *\<^sub>R i)"
  have "(-a)\<bullet>i < x\<bullet>i" and "x\<bullet>i < a\<bullet>i" if "x \<in> S" and i: "i \<in> Basis" for x i
    using b Basis_le_norm[OF i, of x] that by (auto simp: a_def)
  then have "S \<subseteq> box (-a) a"
    by (auto simp: simp add: box_def)
  then show ?thesis ..
qed

lemma bounded_subset_cbox_symmetric:
  fixes S :: "('a::euclidean_space) set"
  assumes "bounded S"
  obtains a where "S \<subseteq> cbox (-a) a"
proof -
  obtain a where "S \<subseteq> box (-a) a"
    using bounded_subset_box_symmetric[OF assms] by auto
  then show ?thesis
    by (meson box_subset_cbox dual_order.trans that)
qed

lemma frontier_cbox:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (cbox a b) = cbox a b - box a b"
  unfolding frontier_def unfolding interior_cbox and closure_closed[OF closed_cbox] ..

lemma frontier_box:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (box a b) = (if box a b = {} then {} else cbox a b - box a b)"
proof (cases "box a b = {}")
  case True
  then show ?thesis
    using frontier_empty by auto
next
  case False
  then show ?thesis
    unfolding frontier_def and closure_box[OF False] and interior_open[OF open_box]
    by auto
qed

lemma Int_interval_mixed_eq_empty:
  fixes a :: "'a::euclidean_space"
   assumes "box c d \<noteq> {}"
  shows "box a b \<inter> cbox c d = {} \<longleftrightarrow> box a b \<inter> box c d = {}"
  unfolding closure_box[OF assms, symmetric]
  unfolding open_Int_closure_eq_empty[OF open_box] ..

subsection \<open>Class Instances\<close>

lemma compact_lemma:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>Basis. \<exists>l::'a. \<exists> r.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially)"
  by (rule compact_lemma_general[where unproj="\<lambda>e. \<Sum>i\<in>Basis. e i *\<^sub>R i"])
     (auto intro!: assms bounded_linear_inner_left bounded_linear_image
       simp: euclidean_representation)

instance\<^marker>\<open>tag important\<close> euclidean_space \<subseteq> heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "bounded (range f)"
  then obtain l::'a and r where r: "strict_mono r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially"
    using compact_lemma [OF f] by blast
  {
    fix e::real
    assume "e > 0"
    hence "e / real_of_nat DIM('a) > 0" by (simp)
    with l have "eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))) sequentially"
      by simp
    moreover
    {
      fix n
      assume n: "\<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i))"
        apply (subst euclidean_dist_l2)
        using zero_le_dist
        apply (rule L2_set_le_sum)
        done
      also have "\<dots> < (\<Sum>i\<in>(Basis::'a set). e / (real_of_nat DIM('a)))"
        apply (rule sum_strict_mono)
        using n
        apply auto
        done
      finally have "dist (f (r n)) l < e"
        by auto
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_mono)
  }
  then have *: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    by auto
qed

instance\<^marker>\<open>tag important\<close> euclidean_space \<subseteq> banach ..

instance euclidean_space \<subseteq> second_countable_topology
proof
  define a where "a f = (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have a: "\<And>f. (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i) = a f"
    by simp
  define b where "b f = (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have b: "\<And>f. (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i) = b f"
    by simp
  define B where "B = (\<lambda>f. box (a f) (b f)) ` (Basis \<rightarrow>\<^sub>E (\<rat> \<times> \<rat>))"

  have "Ball B open" by (simp add: B_def open_box)
  moreover have "(\<forall>A. open A \<longrightarrow> (\<exists>B'\<subseteq>B. \<Union>B' = A))"
  proof safe
    fix A::"'a set"
    assume "open A"
    show "\<exists>B'\<subseteq>B. \<Union>B' = A"
      apply (rule exI[of _ "{b\<in>B. b \<subseteq> A}"])
      apply (subst (3) open_UNION_box[OF \<open>open A\<close>])
      apply (auto simp: a b B_def)
      done
  qed
  ultimately
  have "topological_basis B"
    unfolding topological_basis_def by blast
  moreover
  have "countable B"
    unfolding B_def
    by (intro countable_image countable_PiE finite_Basis countable_SIGMA countable_rat)
  ultimately show "\<exists>B::'a set set. countable B \<and> open = generate_topology B"
    by (blast intro: topological_basis_imp_subbasis)
qed

instance euclidean_space \<subseteq> polish_space ..


subsection \<open>Compact Boxes\<close>

lemma compact_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "compact (cbox a b)"
  using bounded_closed_imp_seq_compact[of "cbox a b"] using bounded_cbox[of a b]
  by (auto simp: compact_eq_seq_compact_metric)

proposition is_interval_compact:
   "is_interval S \<and> compact S \<longleftrightarrow> (\<exists>a b. S = cbox a b)"   (is "?lhs = ?rhs")
proof (cases "S = {}")
  case True
  with empty_as_interval show ?thesis by auto
next
  case False
  show ?thesis
  proof
    assume L: ?lhs
    then have "is_interval S" "compact S" by auto
    define a where "a \<equiv> \<Sum>i\<in>Basis. (INF x\<in>S. x \<bullet> i) *\<^sub>R i"
    define b where "b \<equiv> \<Sum>i\<in>Basis. (SUP x\<in>S. x \<bullet> i) *\<^sub>R i"
    have 1: "\<And>x i. \<lbrakk>x \<in> S; i \<in> Basis\<rbrakk> \<Longrightarrow> (INF x\<in>S. x \<bullet> i) \<le> x \<bullet> i"
      by (simp add: cInf_lower bounded_inner_imp_bdd_below compact_imp_bounded L)
    have 2: "\<And>x i. \<lbrakk>x \<in> S; i \<in> Basis\<rbrakk> \<Longrightarrow> x \<bullet> i \<le> (SUP x\<in>S. x \<bullet> i)"
      by (simp add: cSup_upper bounded_inner_imp_bdd_above compact_imp_bounded L)
    have 3: "x \<in> S" if inf: "\<And>i. i \<in> Basis \<Longrightarrow> (INF x\<in>S. x \<bullet> i) \<le> x \<bullet> i"
                   and sup: "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<le> (SUP x\<in>S. x \<bullet> i)" for x
    proof (rule mem_box_componentwiseI [OF \<open>is_interval S\<close>])
      fix i::'a
      assume i: "i \<in> Basis"
      have cont: "continuous_on S (\<lambda>x. x \<bullet> i)"
        by (intro continuous_intros)
      obtain a where "a \<in> S" and a: "\<And>y. y\<in>S \<Longrightarrow> a \<bullet> i \<le> y \<bullet> i"
        using continuous_attains_inf [OF \<open>compact S\<close> False cont] by blast
      obtain b where "b \<in> S" and b: "\<And>y. y\<in>S \<Longrightarrow> y \<bullet> i \<le> b \<bullet> i"
        using continuous_attains_sup [OF \<open>compact S\<close> False cont] by blast
      have "a \<bullet> i \<le> (INF x\<in>S. x \<bullet> i)"
        by (simp add: False a cINF_greatest)
      also have "\<dots> \<le> x \<bullet> i"
        by (simp add: i inf)
      finally have ai: "a \<bullet> i \<le> x \<bullet> i" .
      have "x \<bullet> i \<le> (SUP x\<in>S. x \<bullet> i)"
        by (simp add: i sup)
      also have "(SUP x\<in>S. x \<bullet> i) \<le> b \<bullet> i"
        by (simp add: False b cSUP_least)
      finally have bi: "x \<bullet> i \<le> b \<bullet> i" .
      show "x \<bullet> i \<in> (\<lambda>x. x \<bullet> i) ` S"
        apply (rule_tac x="\<Sum>j\<in>Basis. (if j = i then x \<bullet> i else a \<bullet> j) *\<^sub>R j" in image_eqI)
        apply (simp add: i)
        apply (rule mem_is_intervalI [OF \<open>is_interval S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close>])
        using i ai bi apply force
        done
    qed
    have "S = cbox a b"
      by (auto simp: a_def b_def mem_box intro: 1 2 3)
    then show ?rhs
      by blast
  next
    assume R: ?rhs
    then show ?lhs
      using compact_cbox is_interval_cbox by blast
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Componentwise limits and continuity\<close>

text\<open>But is the premise really necessary? Need to generalise @{thm euclidean_dist_l2}\<close>
lemma Euclidean_dist_upper: "i \<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  by (metis (no_types) member_le_L2_set euclidean_dist_l2 finite_Basis)

text\<open>But is the premise \<^term>\<open>i \<in> Basis\<close> really necessary?\<close>
lemma open_preimage_inner:
  assumes "open S" "i \<in> Basis"
    shows "open {x. x \<bullet> i \<in> S}"
proof (rule openI, simp)
  fix x
  assume x: "x \<bullet> i \<in> S"
  with assms obtain e where "0 < e" and e: "ball (x \<bullet> i) e \<subseteq> S"
    by (auto simp: open_contains_ball_eq)
  have "\<exists>e>0. ball (y \<bullet> i) e \<subseteq> S" if dxy: "dist x y < e / 2" for y
  proof (intro exI conjI)
    have "dist (x \<bullet> i) (y \<bullet> i) < e / 2"
      by (meson \<open>i \<in> Basis\<close> dual_order.trans Euclidean_dist_upper not_le that)
    then have "dist (x \<bullet> i) z < e" if "dist (y \<bullet> i) z < e / 2" for z
      by (metis dist_commute dist_triangle_half_l that)
    then have "ball (y \<bullet> i) (e / 2) \<subseteq> ball (x \<bullet> i) e"
      using mem_ball by blast
      with e show "ball (y \<bullet> i) (e / 2) \<subseteq> S"
        by (metis order_trans)
  qed (simp add: \<open>0 < e\<close>)
  then show "\<exists>e>0. ball x e \<subseteq> {s. s \<bullet> i \<in> S}"
    by (metis (no_types, lifting) \<open>0 < e\<close> \<open>open S\<close> half_gt_zero_iff mem_Collect_eq mem_ball open_contains_ball_eq subsetI)
qed

proposition tendsto_componentwise_iff:
  fixes f :: "_ \<Rightarrow> 'b::euclidean_space"
  shows "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>i \<in> Basis. ((\<lambda>x. (f x \<bullet> i)) \<longlongrightarrow> (l \<bullet> i)) F)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding tendsto_def
    apply clarify
    apply (drule_tac x="{s. s \<bullet> i \<in> S}" in spec)
    apply (auto simp: open_preimage_inner)
    done
next
  assume R: ?rhs
  then have "\<And>e. e > 0 \<Longrightarrow> \<forall>i\<in>Basis. \<forall>\<^sub>F x in F. dist (f x \<bullet> i) (l \<bullet> i) < e"
    unfolding tendsto_iff by blast
  then have R': "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F x in F. \<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e"
      by (simp add: eventually_ball_finite_distrib [symmetric])
  show ?lhs
  unfolding tendsto_iff
  proof clarify
    fix e::real
    assume "0 < e"
    have *: "L2_set (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis < e"
             if "\<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e / real DIM('b)" for x
    proof -
      have "L2_set (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis \<le> sum (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis"
        by (simp add: L2_set_le_sum)
      also have "... < DIM('b) * (e / real DIM('b))"
        apply (rule sum_bounded_above_strict)
        using that by auto
      also have "... = e"
        by (simp add: field_simps)
      finally show "L2_set (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis < e" .
    qed
    have "\<forall>\<^sub>F x in F. \<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e / DIM('b)"
      apply (rule R')
      using \<open>0 < e\<close> by simp
    then show "\<forall>\<^sub>F x in F. dist (f x) l < e"
      apply (rule eventually_mono)
      apply (subst euclidean_dist_l2)
      using * by blast
  qed
qed


corollary continuous_componentwise:
   "continuous F f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous F (\<lambda>x. (f x \<bullet> i)))"
by (simp add: continuous_def tendsto_componentwise_iff [symmetric])

corollary continuous_on_componentwise:
  fixes S :: "'a :: t2_space set"
  shows "continuous_on S f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous_on S (\<lambda>x. (f x \<bullet> i)))"
  apply (simp add: continuous_on_eq_continuous_within)
  using continuous_componentwise by blast

lemma linear_componentwise_iff:
     "(linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. linear (\<lambda>x. f' x \<bullet> i))"
  apply (auto simp: linear_iff inner_left_distrib)
   apply (metis inner_left_distrib euclidean_eq_iff)
  by (metis euclidean_eqI inner_scaleR_left)

lemma bounded_linear_componentwise_iff:
     "(bounded_linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. bounded_linear (\<lambda>x. f' x \<bullet> i))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: bounded_linear_inner_left_comp)
next
  assume ?rhs
  then have "(\<forall>i\<in>Basis. \<exists>K. \<forall>x. \<bar>f' x \<bullet> i\<bar> \<le> norm x * K)" "linear f'"
    by (auto simp: bounded_linear_def bounded_linear_axioms_def linear_componentwise_iff [symmetric] ball_conj_distrib)
  then obtain F where F: "\<And>i x. i \<in> Basis \<Longrightarrow> \<bar>f' x \<bullet> i\<bar> \<le> norm x * F i"
    by metis
  have "norm (f' x) \<le> norm x * sum F Basis" for x
  proof -
    have "norm (f' x) \<le> (\<Sum>i\<in>Basis. \<bar>f' x \<bullet> i\<bar>)"
      by (rule norm_le_l1)
    also have "... \<le> (\<Sum>i\<in>Basis. norm x * F i)"
      by (metis F sum_mono)
    also have "... = norm x * sum F Basis"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  then show ?lhs
    by (force simp: bounded_linear_def bounded_linear_axioms_def \<open>linear f'\<close>)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Continuous Extension\<close>

definition clamp :: "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "clamp a b x = (if (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)
    then (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i)
    else a)"

lemma clamp_in_interval[simp]:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  shows "clamp a b x \<in> cbox a b"
  unfolding clamp_def
  using box_ne_empty(1)[of a b] assms by (auto simp: cbox_def)

lemma clamp_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "clamp a b x = x"
  using assms
  by (auto simp: clamp_def mem_box intro!: euclidean_eqI[where 'a='a])

lemma clamp_empty_interval:
  assumes "i \<in> Basis" "a \<bullet> i > b \<bullet> i"
  shows "clamp a b = (\<lambda>_. a)"
  using assms
  by (force simp: clamp_def[abs_def] split: if_splits intro!: ext)

lemma dist_clamps_le_dist_args:
  fixes x :: "'a::euclidean_space"
  shows "dist (clamp a b y) (clamp a b x) \<le> dist y x"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  then have "(\<Sum>i\<in>Basis. (dist (clamp a b y \<bullet> i) (clamp a b x \<bullet> i))\<^sup>2) \<le>
    (\<Sum>i\<in>Basis. (dist (y \<bullet> i) (x \<bullet> i))\<^sup>2)"
    by (auto intro!: sum_mono simp: clamp_def dist_real_def abs_le_square_iff[symmetric])
  then show ?thesis
    by (auto intro: real_sqrt_le_mono
      simp: euclidean_dist_l2[where y=x] euclidean_dist_l2[where y="clamp a b x"] L2_set_def)
qed (auto simp: clamp_def)

lemma clamp_continuous_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
    and x :: 'a
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous (at x) (\<lambda>x. f (clamp a b x))"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  show ?thesis
    unfolding continuous_at_eps_delta
  proof safe
    fix x :: 'a
    fix e :: real
    assume "e > 0"
    moreover have "clamp a b x \<in> cbox a b"
      by (simp add: le)
    moreover note f_cont[simplified continuous_on_iff]
    ultimately
    obtain d where d: "0 < d"
      "\<And>x'. x' \<in> cbox a b \<Longrightarrow> dist x' (clamp a b x) < d \<Longrightarrow> dist (f x') (f (clamp a b x)) < e"
      by force
    show "\<exists>d>0. \<forall>x'. dist x' x < d \<longrightarrow>
      dist (f (clamp a b x')) (f (clamp a b x)) < e"
      using le
      by (auto intro!: d clamp_in_interval dist_clamps_le_dist_args[THEN le_less_trans])
  qed
qed (auto simp: clamp_empty_interval)

lemma clamp_continuous_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous_on S (\<lambda>x. f (clamp a b x))"
  using assms
  by (auto intro: continuous_at_imp_continuous_on clamp_continuous_at)

lemma clamp_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes bounded: "bounded (f ` (cbox a b))"
  shows "bounded (range (\<lambda>x. f (clamp a b x)))"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  from bounded obtain c where f_bound: "\<forall>x\<in>f ` cbox a b. dist undefined x \<le> c"
    by (auto simp: bounded_any_center[where a=undefined])
  then show ?thesis
    by (auto intro!: exI[where x=c] clamp_in_interval[OF le[rule_format]]
        simp: bounded_any_center[where a=undefined])
qed (auto simp: clamp_empty_interval image_def)


definition ext_cont :: "('a::euclidean_space \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  where "ext_cont f a b = (\<lambda>x. f (clamp a b x))"

lemma ext_cont_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "ext_cont f a b x = f x"
  using assms
  unfolding ext_cont_def
  by (auto simp: clamp_def mem_box intro!: euclidean_eqI[where 'a='a] arg_cong[where f=f])

lemma continuous_on_ext_cont[continuous_intros]:
  "continuous_on (cbox a b) f \<Longrightarrow> continuous_on S (ext_cont f a b)"
  by (auto intro!: clamp_continuous_on simp: ext_cont_def)


subsection \<open>Separability\<close>

lemma univ_second_countable_sequence:
  obtains B :: "nat \<Rightarrow> 'a::euclidean_space set"
    where "inj B" "\<And>n. open(B n)" "\<And>S. open S \<Longrightarrow> \<exists>k. S = \<Union>{B n |n. n \<in> k}"
proof -
  obtain \<B> :: "'a set set"
  where "countable \<B>"
    and opn: "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
    and Un: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
    using univ_second_countable by blast
  have *: "infinite (range (\<lambda>n. ball (0::'a) (inverse(Suc n))))"
    apply (rule Infinite_Set.range_inj_infinite)
    apply (simp add: inj_on_def ball_eq_ball_iff)
    done
  have "infinite \<B>"
  proof
    assume "finite \<B>"
    then have "finite (Union ` (Pow \<B>))"
      by simp
    then have "finite (range (\<lambda>n. ball (0::'a) (inverse(Suc n))))"
      apply (rule rev_finite_subset)
      by (metis (no_types, lifting) PowI image_eqI image_subset_iff Un [OF open_ball])
    with * show False by simp
  qed
  obtain f :: "nat \<Rightarrow> 'a set" where "\<B> = range f" "inj f"
    by (blast intro: countable_as_injective_image [OF \<open>countable \<B>\<close> \<open>infinite \<B>\<close>])
  have *: "\<exists>k. S = \<Union>{f n |n. n \<in> k}" if "open S" for S
    using Un [OF that]
    apply clarify
    apply (rule_tac x="f-`U" in exI)
    using \<open>inj f\<close> \<open>\<B> = range f\<close> apply force
    done
  show ?thesis
    apply (rule that [OF \<open>inj f\<close> _ *])
    apply (auto simp: \<open>\<B> = range f\<close> opn)
    done
qed

proposition separable:
  fixes S :: "'a::{metric_space, second_countable_topology} set"
  obtains T where "countable T" "T \<subseteq> S" "S \<subseteq> closure T"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>"
      and "{} \<notin> \<B>"
      and ope: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(top_of_set S) C"
      and if_ope: "\<And>T. openin(top_of_set S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
    by (meson subset_second_countable)
  then obtain f where f: "\<And>C. C \<in> \<B> \<Longrightarrow> f C \<in> C"
    by (metis equals0I)
  show ?thesis
  proof
    show "countable (f ` \<B>)"
      by (simp add: \<open>countable \<B>\<close>)
    show "f ` \<B> \<subseteq> S"
      using ope f openin_imp_subset by blast
    show "S \<subseteq> closure (f ` \<B>)"
    proof (clarsimp simp: closure_approachable)
      fix x and e::real
      assume "x \<in> S" "0 < e"
      have "openin (top_of_set S) (S \<inter> ball x e)"
        by (simp add: openin_Int_open)
      with if_ope obtain \<U> where  \<U>: "\<U> \<subseteq> \<B>" "S \<inter> ball x e = \<Union>\<U>"
        by meson
      show "\<exists>C \<in> \<B>. dist (f C) x < e"
      proof (cases "\<U> = {}")
        case True
        then show ?thesis
          using \<open>0 < e\<close>  \<U> \<open>x \<in> S\<close> by auto
      next
        case False
        then obtain C where "C \<in> \<U>" by blast
        show ?thesis
        proof
          show "dist (f C) x < e"
            by (metis Int_iff Union_iff \<U> \<open>C \<in> \<U>\<close> dist_commute f mem_ball subsetCE)
          show "C \<in> \<B>"
            using \<open>\<U> \<subseteq> \<B>\<close> \<open>C \<in> \<U>\<close> by blast
        qed
      qed
    qed
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Diameter\<close>

lemma diameter_cball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(cball a r) = (if r < 0 then 0 else 2*r)"
proof -
  have "diameter(cball a r) = 2*r" if "r \<ge> 0"
  proof (rule order_antisym)
    show "diameter (cball a r) \<le> 2*r"
    proof (rule diameter_le)
      fix x y assume "x \<in> cball a r" "y \<in> cball a r"
      then have "norm (x - a) \<le> r" "norm (a - y) \<le> r"
        by (auto simp: dist_norm norm_minus_commute)
      then have "norm (x - y) \<le> r+r"
        using norm_diff_triangle_le by blast
      then show "norm (x - y) \<le> 2*r" by simp
    qed (simp add: that)
    have "2*r = dist (a + r *\<^sub>R (SOME i. i \<in> Basis)) (a - r *\<^sub>R (SOME i. i \<in> Basis))"
      apply (simp add: dist_norm)
      by (metis abs_of_nonneg mult.right_neutral norm_numeral norm_scaleR norm_some_Basis real_norm_def scaleR_2 that)
    also have "... \<le> diameter (cball a r)"
      apply (rule diameter_bounded_bound)
      using that by (auto simp: dist_norm)
    finally show "2*r \<le> diameter (cball a r)" .
  qed
  then show ?thesis by simp
qed

lemma diameter_ball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(ball a r) = (if r < 0 then 0 else 2*r)"
proof -
  have "diameter(ball a r) = 2*r" if "r > 0"
    by (metis bounded_ball diameter_closure closure_ball diameter_cball less_eq_real_def linorder_not_less that)
  then show ?thesis
    by (simp add: diameter_def)
qed

lemma diameter_closed_interval [simp]: "diameter {a..b} = (if b < a then 0 else b-a)"
proof -
  have "{a .. b} = cball ((a+b)/2) ((b-a)/2)"
    by (auto simp: dist_norm abs_if field_split_simps split: if_split_asm)
  then show ?thesis
    by simp
qed

lemma diameter_open_interval [simp]: "diameter {a<..<b} = (if b < a then 0 else b-a)"
proof -
  have "{a <..< b} = ball ((a+b)/2) ((b-a)/2)"
    by (auto simp: dist_norm abs_if field_split_simps split: if_split_asm)
  then show ?thesis
    by simp
qed

lemma diameter_cbox:
  fixes a b::"'a::euclidean_space"
  shows "(\<forall>i \<in> Basis. a \<bullet> i \<le> b \<bullet> i) \<Longrightarrow> diameter (cbox a b) = dist a b"
  by (force simp: diameter_def intro!: cSup_eq_maximum L2_set_mono
     simp: euclidean_dist_l2[where 'a='a] cbox_def dist_norm)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relating linear images to open/closed/interior/closure/connected\<close>

proposition open_surjective_linear_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "open A" "linear f" "surj f"
    shows "open(f ` A)"
unfolding open_dist
proof clarify
  fix x
  assume "x \<in> A"
  have "bounded (inv f ` Basis)"
    by (simp add: finite_imp_bounded)
  with bounded_pos obtain B where "B > 0" and B: "\<And>x. x \<in> inv f ` Basis \<Longrightarrow> norm x \<le> B"
    by metis
  obtain e where "e > 0" and e: "\<And>z. dist z x < e \<Longrightarrow> z \<in> A"
    by (metis open_dist \<open>x \<in> A\<close> \<open>open A\<close>)
  define \<delta> where "\<delta> \<equiv> e / B / DIM('b)"
  show "\<exists>e>0. \<forall>y. dist y (f x) < e \<longrightarrow> y \<in> f ` A"
  proof (intro exI conjI)
    show "\<delta> > 0"
      using \<open>e > 0\<close> \<open>B > 0\<close>  by (simp add: \<delta>_def field_split_simps)
    have "y \<in> f ` A" if "dist y (f x) * (B * real DIM('b)) < e" for y
    proof -
      define u where "u \<equiv> y - f x"
      show ?thesis
      proof (rule image_eqI)
        show "y = f (x + (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R inv f i))"
          apply (simp add: linear_add linear_sum linear.scaleR \<open>linear f\<close> surj_f_inv_f \<open>surj f\<close>)
          apply (simp add: euclidean_representation u_def)
          done
        have "dist (x + (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R inv f i)) x \<le> (\<Sum>i\<in>Basis. norm ((u \<bullet> i) *\<^sub>R inv f i))"
          by (simp add: dist_norm sum_norm_le)
        also have "... = (\<Sum>i\<in>Basis. \<bar>u \<bullet> i\<bar> * norm (inv f i))"
          by simp
        also have "... \<le> (\<Sum>i\<in>Basis. \<bar>u \<bullet> i\<bar>) * B"
          by (simp add: B sum_distrib_right sum_mono mult_left_mono)
        also have "... \<le> DIM('b) * dist y (f x) * B"
          apply (rule mult_right_mono [OF sum_bounded_above])
          using \<open>0 < B\<close> by (auto simp: Basis_le_norm dist_norm u_def)
        also have "... < e"
          by (metis mult.commute mult.left_commute that)
        finally show "x + (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R inv f i) \<in> A"
          by (rule e)
      qed
    qed
    then show "\<forall>y. dist y (f x) < \<delta> \<longrightarrow> y \<in> f ` A"
      using \<open>e > 0\<close> \<open>B > 0\<close>
      by (auto simp: \<delta>_def field_split_simps)
  qed
qed

corollary open_bijective_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
    shows "open(f ` A) \<longleftrightarrow> open A"
proof
  assume "open(f ` A)"
  then have "open(f -` (f ` A))"
    using assms by (force simp: linear_continuous_at linear_conv_bounded_linear continuous_open_vimage)
  then show "open A"
    by (simp add: assms bij_is_inj inj_vimage_image_eq)
next
  assume "open A"
  then show "open(f ` A)"
    by (simp add: assms bij_is_surj open_surjective_linear_image)
qed

corollary interior_bijective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
  shows "interior (f ` S) = f ` interior S"  (is "?lhs = ?rhs")
proof safe
  fix x
  assume x: "x \<in> ?lhs"
  then obtain T where "open T" and "x \<in> T" and "T \<subseteq> f ` S"
    by (metis interiorE)
  then show "x \<in> ?rhs"
    by (metis (no_types, opaque_lifting) assms subsetD interior_maximal open_bijective_linear_image_eq subset_image_iff)
next
  fix x
  assume x: "x \<in> interior S"
  then show "f x \<in> interior (f ` S)"
    by (meson assms imageI image_mono interiorI interior_subset open_bijective_linear_image_eq open_interior)
qed

lemma interior_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "inj f"
   shows "interior(f ` S) = f ` (interior S)"
  by (simp add: linear_injective_imp_surjective assms bijI interior_bijective_linear_image)

lemma interior_surjective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "surj f"
   shows "interior(f ` S) = f ` (interior S)"
  by (simp add: assms interior_injective_linear_image linear_surjective_imp_injective)

lemma interior_negations:
  fixes S :: "'a::euclidean_space set"
  shows "interior(uminus ` S) = image uminus (interior S)"
  by (simp add: bij_uminus interior_bijective_linear_image linear_uminus)

lemma connected_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "linear f" and "connected s"
  shows "connected (f ` s)"
using connected_continuous_image assms linear_continuous_on linear_conv_bounded_linear by blast


subsection\<^marker>\<open>tag unimportant\<close> \<open>"Isometry" (up to constant bounds) of Injective Linear Map\<close>

proposition injective_imp_isometric:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes s: "closed s" "subspace s"
    and f: "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0"
  shows "\<exists>e>0. \<forall>x\<in>s. norm (f x) \<ge> e * norm x"
proof (cases "s \<subseteq> {0::'a}")
  case True
  have "norm x \<le> norm (f x)" if "x \<in> s" for x
  proof -
    from True that have "x = 0" by auto
    then show ?thesis by simp
  qed
  then show ?thesis
    by (auto intro!: exI[where x=1])
next
  case False
  interpret f: bounded_linear f by fact
  from False obtain a where a: "a \<noteq> 0" "a \<in> s"
    by auto
  from False have "s \<noteq> {}"
    by auto
  let ?S = "{f x| x. x \<in> s \<and> norm x = norm a}"
  let ?S' = "{x::'a. x\<in>s \<and> norm x = norm a}"
  let ?S'' = "{x::'a. norm x = norm a}"

  have "?S'' = frontier (cball 0 (norm a))"
    by (simp add: sphere_def dist_norm)
  then have "compact ?S''" by (metis compact_cball compact_frontier)
  moreover have "?S' = s \<inter> ?S''" by auto
  ultimately have "compact ?S'"
    using closed_Int_compact[of s ?S''] using s(1) by auto
  moreover have *:"f ` ?S' = ?S" by auto
  ultimately have "compact ?S"
    using compact_continuous_image[OF linear_continuous_on[OF f(1)], of ?S'] by auto
  then have "closed ?S"
    using compact_imp_closed by auto
  moreover from a have "?S \<noteq> {}" by auto
  ultimately obtain b' where "b'\<in>?S" "\<forall>y\<in>?S. norm b' \<le> norm y"
    using distance_attains_inf[of ?S 0] unfolding dist_0_norm by auto
  then obtain b where "b\<in>s"
    and ba: "norm b = norm a"
    and b: "\<forall>x\<in>{x \<in> s. norm x = norm a}. norm (f b) \<le> norm (f x)"
    unfolding *[symmetric] unfolding image_iff by auto

  let ?e = "norm (f b) / norm b"
  have "norm b > 0"
    using ba and a and norm_ge_zero by auto
  moreover have "norm (f b) > 0"
    using f(2)[THEN bspec[where x=b], OF \<open>b\<in>s\<close>]
    using \<open>norm b >0\<close> by simp
  ultimately have "0 < norm (f b) / norm b" by simp
  moreover
  have "norm (f b) / norm b * norm x \<le> norm (f x)" if "x\<in>s" for x
  proof (cases "x = 0")
    case True
    then show "norm (f b) / norm b * norm x \<le> norm (f x)"
      by auto
  next
    case False
    with \<open>a \<noteq> 0\<close> have *: "0 < norm a / norm x"
      unfolding zero_less_norm_iff[symmetric] by simp
    have "\<forall>x\<in>s. c *\<^sub>R x \<in> s" for c
      using s[unfolded subspace_def] by simp
    with \<open>x \<in> s\<close> \<open>x \<noteq> 0\<close> have "(norm a / norm x) *\<^sub>R x \<in> {x \<in> s. norm x = norm a}"
      by simp
    with \<open>x \<noteq> 0\<close> \<open>a \<noteq> 0\<close> show "norm (f b) / norm b * norm x \<le> norm (f x)"
      using b[THEN bspec[where x="(norm a / norm x) *\<^sub>R x"]]
      unfolding f.scaleR and ba
      by (auto simp: mult.commute pos_le_divide_eq pos_divide_le_eq)
  qed
  ultimately show ?thesis by auto
qed

proposition closed_injective_image_subspace:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace s" "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0" "closed s"
  shows "closed(f ` s)"
proof -
  obtain e where "e > 0" and e: "\<forall>x\<in>s. e * norm x \<le> norm (f x)"
    using injective_imp_isometric[OF assms(4,1,2,3)] by auto
  show ?thesis
    using complete_isometric_image[OF \<open>e>0\<close> assms(1,2) e] and assms(4)
    unfolding complete_eq_closed[symmetric] by auto
qed
                               

lemma closure_bounded_linear_image_subset:
  assumes f: "bounded_linear f"
  shows "f ` closure S \<subseteq> closure (f ` S)"
  using linear_continuous_on [OF f] closed_closure closure_subset
  by (rule image_closure_subset)

lemma closure_linear_image_subset:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::real_normed_vector"
  assumes "linear f"
  shows "f ` (closure S) \<subseteq> closure (f ` S)"
  using assms unfolding linear_conv_bounded_linear
  by (rule closure_bounded_linear_image_subset)

lemma closed_injective_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    assumes S: "closed S" and f: "linear f" "inj f"
    shows "closed (f ` S)"
proof -
  obtain g where g: "linear g" "g \<circ> f = id"
    using linear_injective_left_inverse [OF f] by blast
  then have confg: "continuous_on (range f) g"
    using linear_continuous_on linear_conv_bounded_linear by blast
  have [simp]: "g ` f ` S = S"
    using g by (simp add: image_comp)
  have cgf: "closed (g ` f ` S)"
    by (simp add: \<open>g \<circ> f = id\<close> S image_comp)
  have [simp]: "(range f \<inter> g -` S) = f ` S"
    using g unfolding o_def id_def image_def by auto metis+
  show ?thesis
  proof (rule closedin_closed_trans [of "range f"])
    show "closedin (top_of_set (range f)) (f ` S)"
      using continuous_closedin_preimage [OF confg cgf] by simp
    show "closed (range f)"
      apply (rule closed_injective_image_subspace)
      using f apply (auto simp: linear_linear linear_injective_0)
      done
  qed
qed

lemma closed_injective_linear_image_eq:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    assumes f: "linear f" "inj f"
      shows "(closed(image f s) \<longleftrightarrow> closed s)"
  by (metis closed_injective_linear_image closure_eq closure_linear_image_subset closure_subset_eq f(1) f(2) inj_image_subset_iff)

lemma closure_injective_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    shows "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> f ` (closure S) = closure (f ` S)"
  apply (rule subset_antisym)
  apply (simp add: closure_linear_image_subset)
  by (simp add: closure_minimal closed_injective_linear_image closure_subset image_mono)

lemma closure_bounded_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    shows "\<lbrakk>linear f; bounded S\<rbrakk> \<Longrightarrow> f ` (closure S) = closure (f ` S)"
  apply (rule subset_antisym, simp add: closure_linear_image_subset)
  apply (rule closure_minimal, simp add: closure_subset image_mono)
  by (meson bounded_closure closed_closure compact_continuous_image compact_eq_bounded_closed linear_continuous_on linear_conv_bounded_linear)

lemma closure_scaleR:
  fixes S :: "'a::real_normed_vector set"
  shows "((*\<^sub>R) c) ` (closure S) = closure (((*\<^sub>R) c) ` S)"
proof
  show "((*\<^sub>R) c) ` (closure S) \<subseteq> closure (((*\<^sub>R) c) ` S)"
    using bounded_linear_scaleR_right
    by (rule closure_bounded_linear_image_subset)
  show "closure (((*\<^sub>R) c) ` S) \<subseteq> ((*\<^sub>R) c) ` (closure S)"
    by (intro closure_minimal image_mono closure_subset closed_scaling closed_closure)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some properties of a canonical subspace\<close>

lemma closed_substandard: "closed {x::'a::euclidean_space. \<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0}"
  (is "closed ?A")
proof -
  let ?D = "{i\<in>Basis. P i}"
  have "closed (\<Inter>i\<in>?D. {x::'a. x\<bullet>i = 0})"
    by (simp add: closed_INT closed_Collect_eq continuous_on_inner)
  also have "(\<Inter>i\<in>?D. {x::'a. x\<bullet>i = 0}) = ?A"
    by auto
  finally show "closed ?A" .
qed

lemma closed_subspace:
  fixes s :: "'a::euclidean_space set"
  assumes "subspace s"
  shows "closed s"
proof -
  have "dim s \<le> card (Basis :: 'a set)"
    using dim_subset_UNIV by auto
  with ex_card[OF this] obtain d :: "'a set" where t: "card d = dim s" and d: "d \<subseteq> Basis"
    by auto
  let ?t = "{x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  have "\<exists>f. linear f \<and> f ` {x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} = s \<and>
      inj_on f {x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
    using dim_substandard[of d] t d assms
    by (intro subspace_isomorphism[OF subspace_substandard[of "\<lambda>i. i \<notin> d"]]) (auto simp: inner_Basis)
  then obtain f where f:
      "linear f"
      "f ` {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} = s"
      "inj_on f {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
    by blast
  interpret f: bounded_linear f
    using f by (simp add: linear_conv_bounded_linear)
  have "x \<in> ?t \<Longrightarrow> f x = 0 \<Longrightarrow> x = 0" for x
    using f.zero d f(3)[THEN inj_onD, of x 0] by auto
  moreover have "closed ?t" by (rule closed_substandard)
  moreover have "subspace ?t" by (rule subspace_substandard)
  ultimately show ?thesis
    using closed_injective_image_subspace[of ?t f]
    unfolding f(2) using f(1) unfolding linear_conv_bounded_linear by auto
qed

lemma complete_subspace: "subspace s \<Longrightarrow> complete s"
  for s :: "'a::euclidean_space set"
  using complete_eq_closed closed_subspace by auto

lemma closed_span [iff]: "closed (span s)"
  for s :: "'a::euclidean_space set"
  by (simp add: closed_subspace)

lemma dim_closure [simp]: "dim (closure s) = dim s" (is "?dc = ?d")
  for s :: "'a::euclidean_space set"
proof -
  have "?dc \<le> ?d"
    using closure_minimal[OF span_superset, of s]
    using closed_subspace[OF subspace_span, of s]
    using dim_subset[of "closure s" "span s"]
    by simp
  then show ?thesis
    using dim_subset[OF closure_subset, of s]
    by simp
qed


subsection \<open>Set Distance\<close>

lemma setdist_compact_closed:
  fixes A :: "'a::heine_borel set"
  assumes A: "compact A" and B: "closed B"
    and "A \<noteq> {}" "B \<noteq> {}"
  shows "\<exists>x \<in> A. \<exists>y \<in> B. dist x y = setdist A B"
proof -
  obtain x where "x \<in> A" "setdist A B = infdist x B"
    by (metis A assms(3) setdist_attains_inf setdist_sym)
  moreover
  obtain y where"y \<in> B" "infdist x B = dist x y"
    using B \<open>B \<noteq> {}\<close> infdist_attains_inf by blast
  ultimately show ?thesis
    using \<open>x \<in> A\<close> \<open>y \<in> B\<close> by auto
qed

lemma setdist_closed_compact:
  fixes S :: "'a::heine_borel set"
  assumes S: "closed S" and T: "compact T"
      and "S \<noteq> {}" "T \<noteq> {}"
    shows "\<exists>x \<in> S. \<exists>y \<in> T. dist x y = setdist S T"
  using setdist_compact_closed [OF T S \<open>T \<noteq> {}\<close> \<open>S \<noteq> {}\<close>]
  by (metis dist_commute setdist_sym)

lemma setdist_eq_0_compact_closed:
  assumes S: "compact S" and T: "closed T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> S \<inter> T \<noteq> {}"
proof (cases "S = {} \<or> T = {}")
  case True
  then show ?thesis
    by force
next
  case False
  then show ?thesis
    by (metis S T disjoint_iff_not_equal in_closed_iff_infdist_zero setdist_attains_inf setdist_eq_0I setdist_sym)
qed

corollary setdist_gt_0_compact_closed:
  assumes S: "compact S" and T: "closed T"
    shows "setdist S T > 0 \<longleftrightarrow> (S \<noteq> {} \<and> T \<noteq> {} \<and> S \<inter> T = {})"
  using setdist_pos_le [of S T] setdist_eq_0_compact_closed [OF assms] by linarith

lemma setdist_eq_0_closed_compact:
  assumes S: "closed S" and T: "compact T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> S \<inter> T \<noteq> {}"
  using setdist_eq_0_compact_closed [OF T S]
  by (metis Int_commute setdist_sym)

lemma setdist_eq_0_bounded:
  fixes S :: "'a::heine_borel set"
  assumes "bounded S \<or> bounded T"
  shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> closure S \<inter> closure T \<noteq> {}"
proof (cases "S = {} \<or> T = {}")
  case False
  then show ?thesis
    using setdist_eq_0_compact_closed [of "closure S" "closure T"]
          setdist_eq_0_closed_compact [of "closure S" "closure T"] assms
    by (force simp:  bounded_closure compact_eq_bounded_closed)
qed force

lemma setdist_eq_0_sing_1:
  "setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> closure S"
  by (metis in_closure_iff_infdist_zero infdist_def infdist_eq_setdist)

lemma setdist_eq_0_sing_2:
  "setdist S {x} = 0 \<longleftrightarrow> S = {} \<or> x \<in> closure S"
  by (metis setdist_eq_0_sing_1 setdist_sym)

lemma setdist_neq_0_sing_1:
  "\<lbrakk>setdist {x} S = a; a \<noteq> 0\<rbrakk> \<Longrightarrow> S \<noteq> {} \<and> x \<notin> closure S"
  by (metis setdist_closure_2 setdist_empty2 setdist_eq_0I singletonI)

lemma setdist_neq_0_sing_2:
  "\<lbrakk>setdist S {x} = a; a \<noteq> 0\<rbrakk> \<Longrightarrow> S \<noteq> {} \<and> x \<notin> closure S"
  by (simp add: setdist_neq_0_sing_1 setdist_sym)

lemma setdist_sing_in_set:
   "x \<in> S \<Longrightarrow> setdist {x} S = 0"
  by (simp add: setdist_eq_0I)

lemma setdist_eq_0_closed:
   "closed S \<Longrightarrow> (setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> S)"
by (simp add: setdist_eq_0_sing_1)

lemma setdist_eq_0_closedin:
  shows "\<lbrakk>closedin (top_of_set U) S; x \<in> U\<rbrakk>
         \<Longrightarrow> (setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> S)"
  by (auto simp: closedin_limpt setdist_eq_0_sing_1 closure_def)

lemma setdist_gt_0_closedin:
  shows "\<lbrakk>closedin (top_of_set U) S; x \<in> U; S \<noteq> {}; x \<notin> S\<rbrakk>
         \<Longrightarrow> setdist {x} S > 0"
  using less_eq_real_def setdist_eq_0_closedin by fastforce

no_notation
  eucl_less (infix "<e" 50)

end
