(* Title:      HOL/Analysis/Convex_Euclidean_Space.thy
   Author:     L C Paulson, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
   Author:     Bogdan Grechuk, University of Edinburgh
   Author:     Armin Heller, TU Muenchen
   Author:     Johannes Hoelzl, TU Muenchen
*)

section \<open>Convex Sets and Functions on (Normed) Euclidean Spaces\<close>

theory Convex_Euclidean_Space
imports
  Convex
  Topology_Euclidean_Space
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Topological Properties of Convex Sets and Functions\<close>

lemma aff_dim_cball:
  fixes a :: "'n::euclidean_space"
  assumes "e > 0"
  shows "aff_dim (cball a e) = int (DIM('n))"
proof -
  have "(\<lambda>x. a + x) ` (cball 0 e) \<subseteq> cball a e"
    unfolding cball_def dist_norm by auto
  then have "aff_dim (cball (0 :: 'n::euclidean_space) e) \<le> aff_dim (cball a e)"
    using aff_dim_translation_eq[of a "cball 0 e"]
          aff_dim_subset[of "(+) a ` cball 0 e" "cball a e"]
    by auto
  moreover have "aff_dim (cball (0 :: 'n::euclidean_space) e) = int (DIM('n))"
    using hull_inc[of "(0 :: 'n::euclidean_space)" "cball 0 e"]
      centre_in_cball[of "(0 :: 'n::euclidean_space)"] assms
    by (simp add: dim_cball[of e] aff_dim_zero[of "cball 0 e"])
  ultimately show ?thesis
    using aff_dim_le_DIM[of "cball a e"] by auto
qed

lemma aff_dim_open:
  fixes S :: "'n::euclidean_space set"
  assumes "open S"
    and "S \<noteq> {}"
  shows "aff_dim S = int (DIM('n))"
proof -
  obtain x where "x \<in> S"
    using assms by auto
  then obtain e where e: "e > 0" "cball x e \<subseteq> S"
    using open_contains_cball[of S] assms by auto
  then have "aff_dim (cball x e) \<le> aff_dim S"
    using aff_dim_subset by auto
  with e show ?thesis
    using aff_dim_cball[of e x] aff_dim_le_DIM[of S] by auto
qed

lemma low_dim_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "\<not> aff_dim S = int (DIM('n))"
  shows "interior S = {}"
proof -
  have "aff_dim(interior S) \<le> aff_dim S"
    using interior_subset aff_dim_subset[of "interior S" S] by auto
  then show ?thesis
    using aff_dim_open[of "interior S"] aff_dim_le_DIM[of S] assms by auto
qed

corollary empty_interior_lowdim:
  fixes S :: "'n::euclidean_space set"
  shows "dim S < DIM ('n) \<Longrightarrow> interior S = {}"
by (metis low_dim_interior affine_hull_UNIV dim_affine_hull less_not_refl dim_UNIV)

corollary aff_dim_nonempty_interior:
  fixes S :: "'a::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> aff_dim S = DIM('a)"
by (metis low_dim_interior)


subsection \<open>Relative interior of a set\<close>

definition\<^marker>\<open>tag important\<close> "rel_interior S =
  {x. \<exists>T. openin (top_of_set (affine hull S)) T \<and> x \<in> T \<and> T \<subseteq> S}"

lemma rel_interior_mono:
   "\<lbrakk>S \<subseteq> T; affine hull S = affine hull T\<rbrakk>
   \<Longrightarrow> (rel_interior S) \<subseteq> (rel_interior T)"
  by (auto simp: rel_interior_def)

lemma rel_interior_maximal:
   "\<lbrakk>T \<subseteq> S; openin(top_of_set (affine hull S)) T\<rbrakk> \<Longrightarrow> T \<subseteq> (rel_interior S)"
  by (auto simp: rel_interior_def)

lemma rel_interior: "rel_interior S = {x \<in> S. \<exists>T. open T \<and> x \<in> T \<and> T \<inter> affine hull S \<subseteq> S}"
       (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (force simp add: rel_interior_def openin_open)
  { fix x T
    assume *: "x \<in> S" "open T" "x \<in> T" "T \<inter> affine hull S \<subseteq> S"
    then have **: "x \<in> T \<inter> affine hull S"
      using hull_inc by auto
    with * have "\<exists>Tb. (\<exists>Ta. open Ta \<and> Tb = affine hull S \<inter> Ta) \<and> x \<in> Tb \<and> Tb \<subseteq> S"
      by (rule_tac x = "T \<inter> (affine hull S)" in exI) auto
  }
  then show "?rhs \<subseteq> ?lhs"
    by (force simp add: rel_interior_def openin_open)
qed

lemma mem_rel_interior: "x \<in> rel_interior S \<longleftrightarrow> (\<exists>T. open T \<and> x \<in> T \<inter> S \<and> T \<inter> affine hull S \<subseteq> S)"
  by (auto simp: rel_interior)

lemma mem_rel_interior_ball:
  "x \<in> rel_interior S \<longleftrightarrow> x \<in> S \<and> (\<exists>e. e > 0 \<and> ball x e \<inter> affine hull S \<subseteq> S)"
  (is "?lhs = ?rhs")
proof
  assume ?rhs then show ?lhs
  by (simp add: rel_interior) (meson Elementary_Metric_Spaces.open_ball centre_in_ball)
qed (force simp: rel_interior open_contains_ball)

lemma rel_interior_ball:
  "rel_interior S = {x \<in> S. \<exists>e. e > 0 \<and> ball x e \<inter> affine hull S \<subseteq> S}"
  using mem_rel_interior_ball [of _ S] by auto

lemma mem_rel_interior_cball:
  "x \<in> rel_interior S \<longleftrightarrow> x \<in> S \<and> (\<exists>e. e > 0 \<and> cball x e \<inter> affine hull S \<subseteq> S)"
  (is "?lhs = ?rhs")
proof
  assume ?rhs then obtain e where "x \<in> S" "e > 0" "cball x e \<inter> affine hull S \<subseteq> S"
    by (auto simp: rel_interior)
  then have "ball x e \<inter> affine hull S \<subseteq> S"
    by auto
  then show ?lhs
    using \<open>0 < e\<close> \<open>x \<in> S\<close> rel_interior_ball by auto
qed (force simp: rel_interior open_contains_cball)

lemma rel_interior_cball:
  "rel_interior S = {x \<in> S. \<exists>e. e > 0 \<and> cball x e \<inter> affine hull S \<subseteq> S}"
  using mem_rel_interior_cball [of _ S] by auto

lemma rel_interior_empty [simp]: "rel_interior {} = {}"
   by (auto simp: rel_interior_def)

lemma affine_hull_sing [simp]: "affine hull {a :: 'n::euclidean_space} = {a}"
  by (metis affine_hull_eq affine_sing)

lemma rel_interior_sing [simp]:
  fixes a :: "'n::euclidean_space"  shows "rel_interior {a} = {a}"
proof -
  have "\<exists>x::real. 0 < x"
    using zero_less_one by blast
  then show ?thesis
    by (auto simp: rel_interior_ball)
qed

lemma subset_rel_interior:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
    and "affine hull S = affine hull T"
  shows "rel_interior S \<subseteq> rel_interior T"
  using assms by (auto simp: rel_interior_def)

lemma rel_interior_subset: "rel_interior S \<subseteq> S"
  by (auto simp: rel_interior_def)

lemma rel_interior_subset_closure: "rel_interior S \<subseteq> closure S"
  using rel_interior_subset by (auto simp: closure_def)

lemma interior_subset_rel_interior: "interior S \<subseteq> rel_interior S"
  by (auto simp: rel_interior interior_def)

lemma interior_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "aff_dim S = int(DIM('n))"
  shows "rel_interior S = interior S"
proof -
  have "affine hull S = UNIV"
    using assms affine_hull_UNIV[of S] by auto
  then show ?thesis
    unfolding rel_interior interior_def by auto
qed

lemma rel_interior_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "affine hull S = UNIV"
  shows "rel_interior S = interior S"
  using assms unfolding rel_interior interior_def by auto

lemma rel_interior_open:
  fixes S :: "'n::euclidean_space set"
  assumes "open S"
  shows "rel_interior S = S"
  by (metis assms interior_eq interior_subset_rel_interior rel_interior_subset set_eq_subset)

lemma interior_rel_interior_gen:
  fixes S :: "'n::euclidean_space set"
  shows "interior S = (if aff_dim S = int(DIM('n)) then rel_interior S else {})"
  by (metis interior_rel_interior low_dim_interior)

lemma rel_interior_nonempty_interior:
  fixes S :: "'n::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> rel_interior S = interior S"
by (metis interior_rel_interior_gen)

lemma affine_hull_nonempty_interior:
  fixes S :: "'n::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> affine hull S = UNIV"
by (metis affine_hull_UNIV interior_rel_interior_gen)

lemma rel_interior_affine_hull [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "rel_interior (affine hull S) = affine hull S"
proof -
  have *: "rel_interior (affine hull S) \<subseteq> affine hull S"
    using rel_interior_subset by auto
  {
    fix x
    assume x: "x \<in> affine hull S"
    define e :: real where "e = 1"
    then have "e > 0" "ball x e \<inter> affine hull (affine hull S) \<subseteq> affine hull S"
      using hull_hull[of _ S] by auto
    then have "x \<in> rel_interior (affine hull S)"
      using x rel_interior_ball[of "affine hull S"] by auto
  }
  then show ?thesis using * by auto
qed

lemma rel_interior_UNIV [simp]: "rel_interior (UNIV :: ('n::euclidean_space) set) = UNIV"
  by (metis open_UNIV rel_interior_open)

lemma rel_interior_convex_shrink:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "c \<in> rel_interior S"
    and "x \<in> S"
    and "0 < e"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> rel_interior S"
proof -
  obtain d where "d > 0" and d: "ball c d \<inter> affine hull S \<subseteq> S"
    using assms(2) unfolding  mem_rel_interior_ball by auto
  {
    fix y
    assume as: "dist (x - e *\<^sub>R (x - c)) y < e * d" "y \<in> affine hull S"
    have *: "y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x"
      using \<open>e > 0\<close> by (auto simp: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "x \<in> affine hull S"
      using assms hull_subset[of S] by auto
    moreover have "1 / e + - ((1 - e) / e) = 1"
      using \<open>e > 0\<close> left_diff_distrib[of "1" "(1-e)" "1/e"] by auto
    ultimately have **: "(1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x \<in> affine hull S"
      using as affine_affine_hull[of S] mem_affine[of "affine hull S" y x "(1 / e)" "-((1 - e) / e)"]
      by (simp add: algebra_simps)
    have "c - ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = (1 / e) *\<^sub>R (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      using \<open>e > 0\<close>
      by (auto simp: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
    then have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = \<bar>1/e\<bar> * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm norm_scaleR[symmetric] by auto
    also have "\<dots> = \<bar>1/e\<bar> * norm (x - e *\<^sub>R (x - c) - y)"
      by (auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d"
      using as[unfolded dist_norm] and \<open>e > 0\<close>
      by (auto simp:pos_divide_less_eq[OF \<open>e > 0\<close>] mult.commute)
    finally have "(1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x \<in> S"
      using "**"  d by auto
    then have "y \<in> S"
      using * convexD [OF \<open>convex S\<close>] assms(3-5)
      by (metis diff_add_cancel diff_ge_0_iff_ge le_add_same_cancel1 less_eq_real_def)
  }
  then have "ball (x - e *\<^sub>R (x - c)) (e*d) \<inter> affine hull S \<subseteq> S"
    by auto
  moreover have "e * d > 0"
    using \<open>e > 0\<close> \<open>d > 0\<close> by simp
  moreover have c: "c \<in> S"
    using assms rel_interior_subset by auto
  moreover from c have "x - e *\<^sub>R (x - c) \<in> S"
    using convexD_alt[of S x c e] assms
    by (metis  diff_add_eq diff_diff_eq2 less_eq_real_def scaleR_diff_left scaleR_one scale_right_diff_distrib)
  ultimately show ?thesis
    using mem_rel_interior_ball[of "x - e *\<^sub>R (x - c)" S] \<open>e > 0\<close> by auto
qed

lemma interior_real_atLeast [simp]:
  fixes a :: real
  shows "interior {a..} = {a<..}"
proof -
  {
    fix y
    have "ball y (y - a) \<subseteq> {a..}"
      by (auto simp: dist_norm)
    moreover assume "a < y"
    ultimately have "y \<in> interior {a..}"
      by (force simp add: mem_interior)
  }
  moreover
  {
    fix y
    assume "y \<in> interior {a..}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {a..}"
      using mem_interior_cball[of y "{a..}"] by auto
    moreover from e have "y - e \<in> cball y e"
      by (auto simp: cball_def dist_norm)
    ultimately have "a \<le> y - e" by blast
    then have "a < y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma continuous_ge_on_Ioo:
  assumes "continuous_on {c..d} g" "\<And>x. x \<in> {c<..<d} \<Longrightarrow> g x \<ge> a" "c < d" "x \<in> {c..d}"
  shows "g (x::real) \<ge> (a::real)"
proof-
  from assms(3) have "{c..d} = closure {c<..<d}" by (rule closure_greaterThanLessThan[symmetric])
  also from assms(2) have "{c<..<d} \<subseteq> (g -` {a..} \<inter> {c..d})" by auto
  hence "closure {c<..<d} \<subseteq> closure (g -` {a..} \<inter> {c..d})" by (rule closure_mono)
  also from assms(1) have "closed (g -` {a..} \<inter> {c..d})"
    by (auto simp: continuous_on_closed_vimage)
  hence "closure (g -` {a..} \<inter> {c..d}) = g -` {a..} \<inter> {c..d}" by simp
  finally show ?thesis using \<open>x \<in> {c..d}\<close> by auto
qed

lemma interior_real_atMost [simp]:
  fixes a :: real
  shows "interior {..a} = {..<a}"
proof -
  {
    fix y
    have "ball y (a - y) \<subseteq> {..a}"
      by (auto simp: dist_norm)
    moreover assume "a > y"
    ultimately have "y \<in> interior {..a}"
      by (force simp add: mem_interior)
  }
  moreover
  {
    fix y
    assume "y \<in> interior {..a}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {..a}"
      using mem_interior_cball[of y "{..a}"] by auto
    moreover from e have "y + e \<in> cball y e"
      by (auto simp: cball_def dist_norm)
    ultimately have "a \<ge> y + e" by auto
    then have "a > y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma interior_atLeastAtMost_real [simp]: "interior {a..b} = {a<..<b :: real}"
proof-
  have "{a..b} = {a..} \<inter> {..b}" by auto
  also have "interior \<dots> = {a<..} \<inter> {..<b}"
    by (simp)
  also have "\<dots> = {a<..<b}" by auto
  finally show ?thesis .
qed

lemma interior_atLeastLessThan [simp]:
  fixes a::real shows "interior {a..<b} = {a<..<b}"
  by (metis atLeastLessThan_def greaterThanLessThan_def interior_atLeastAtMost_real interior_Int interior_interior interior_real_atLeast)

lemma interior_lessThanAtMost [simp]:
  fixes a::real shows "interior {a<..b} = {a<..<b}"
  by (metis atLeastAtMost_def greaterThanAtMost_def interior_atLeastAtMost_real interior_Int
            interior_interior interior_real_atLeast)

lemma interior_greaterThanLessThan_real [simp]: "interior {a<..<b} = {a<..<b :: real}"
  by (metis interior_atLeastAtMost_real interior_interior)

lemma frontier_real_atMost [simp]:
  fixes a :: real
  shows "frontier {..a} = {a}"
  unfolding frontier_def by auto

lemma frontier_real_atLeast [simp]: "frontier {a..} = {a::real}"
  by (auto simp: frontier_def)

lemma frontier_real_greaterThan [simp]: "frontier {a<..} = {a::real}"
  by (auto simp: interior_open frontier_def)

lemma frontier_real_lessThan [simp]: "frontier {..<a} = {a::real}"
  by (auto simp: interior_open frontier_def)

lemma rel_interior_real_box [simp]:
  fixes a b :: real
  assumes "a < b"
  shows "rel_interior {a .. b} = {a <..< b}"
proof -
  have "box a b \<noteq> {}"
    using assms
    unfolding set_eq_iff
    by (auto intro!: exI[of _ "(a + b) / 2"] simp: box_def)
  then show ?thesis
    using interior_rel_interior_gen[of "cbox a b", symmetric]
    by (simp split: if_split_asm del: box_real add: box_real[symmetric])
qed

lemma rel_interior_real_semiline [simp]:
  fixes a :: real
  shows "rel_interior {a..} = {a<..}"
proof -
  have *: "{a<..} \<noteq> {}"
    unfolding set_eq_iff by (auto intro!: exI[of _ "a + 1"])
  then show ?thesis using interior_real_atLeast interior_rel_interior_gen[of "{a..}"]
    by (auto split: if_split_asm)
qed

subsubsection \<open>Relative open sets\<close>

definition\<^marker>\<open>tag important\<close> "rel_open S \<longleftrightarrow> rel_interior S = S"

lemma rel_open: "rel_open S \<longleftrightarrow> openin (top_of_set (affine hull S)) S" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding rel_open_def rel_interior_def
    using openin_subopen[of "top_of_set (affine hull S)" S] by auto
qed (auto simp:  rel_open_def rel_interior_def)

lemma openin_rel_interior: "openin (top_of_set (affine hull S)) (rel_interior S)"
  using openin_subopen by (fastforce simp add: rel_interior_def)

lemma openin_set_rel_interior:
   "openin (top_of_set S) (rel_interior S)"
by (rule openin_subset_trans [OF openin_rel_interior rel_interior_subset hull_subset])

lemma affine_rel_open:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S"
  shows "rel_open S"
  unfolding rel_open_def
  using assms rel_interior_affine_hull[of S] affine_hull_eq[of S]
  by metis

lemma affine_closed:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S"
  shows "closed S"
proof -
  {
    assume "S \<noteq> {}"
    then obtain L where L: "subspace L" "affine_parallel S L"
      using assms affine_parallel_subspace[of S] by auto
    then obtain a where a: "S = ((+) a ` L)"
      using affine_parallel_def[of L S] affine_parallel_commut by auto
    from L have "closed L" using closed_subspace by auto
    then have "closed S"
      using closed_translation a by auto
  }
  then show ?thesis by auto
qed

lemma closure_affine_hull:
  fixes S :: "'n::euclidean_space set"
  shows "closure S \<subseteq> affine hull S"
  by (intro closure_minimal hull_subset affine_closed affine_affine_hull)

lemma closed_affine_hull [iff]:
  fixes S :: "'n::euclidean_space set"
  shows "closed (affine hull S)"
  by (metis affine_affine_hull affine_closed)

lemma closure_same_affine_hull [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "affine hull (closure S) = affine hull S"
proof -
  have "affine hull (closure S) \<subseteq> affine hull S"
    using hull_mono[of "closure S" "affine hull S" "affine"]
      closure_affine_hull[of S] hull_hull[of "affine" S]
    by auto
  moreover have "affine hull (closure S) \<supseteq> affine hull S"
    using hull_mono[of "S" "closure S" "affine"] closure_subset by auto
  ultimately show ?thesis by auto
qed

lemma closure_aff_dim [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim (closure S) = aff_dim S"
proof -
  have "aff_dim S \<le> aff_dim (closure S)"
    using aff_dim_subset closure_subset by auto
  moreover have "aff_dim (closure S) \<le> aff_dim (affine hull S)"
    using aff_dim_subset closure_affine_hull by blast
  moreover have "aff_dim (affine hull S) = aff_dim S"
    using aff_dim_affine_hull by auto
  ultimately show ?thesis by auto
qed

lemma rel_interior_closure_convex_shrink:
  fixes S :: "_::euclidean_space set"
  assumes "convex S"
    and "c \<in> rel_interior S"
    and "x \<in> closure S"
    and "e > 0"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> rel_interior S"
proof -
  obtain d where "d > 0" and d: "ball c d \<inter> affine hull S \<subseteq> S"
    using assms(2) unfolding mem_rel_interior_ball by auto
  have "\<exists>y \<in> S. norm (y - x) * (1 - e) < e * d"
  proof (cases "x \<in> S")
    case True
    then show ?thesis using \<open>e > 0\<close> \<open>d > 0\<close> by force
  next
    case False
    then have x: "x islimpt S"
      using assms(3)[unfolded closure_def] by auto
    show ?thesis
    proof (cases "e = 1")
      case True
      obtain y where "y \<in> S" "y \<noteq> x" "dist y x < 1"
        using x[unfolded islimpt_approachable,THEN spec[where x=1]] by auto
      then show ?thesis
        unfolding True using \<open>d > 0\<close> by (force simp add: )
    next
      case False
      then have "0 < e * d / (1 - e)" and *: "1 - e > 0"
        using \<open>e \<le> 1\<close> \<open>e > 0\<close> \<open>d > 0\<close> by auto
      then obtain y where "y \<in> S" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      then show ?thesis
        unfolding dist_norm using pos_less_divide_eq[OF *] by force
    qed
  qed
  then obtain y where "y \<in> S" and y: "norm (y - x) * (1 - e) < e * d"
    by auto
  define z where "z = c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *: "x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)"
    unfolding z_def using \<open>e > 0\<close>
    by (auto simp: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have zball: "z \<in> ball c d"
    using mem_ball z_def dist_norm[of c]
    using y and assms(4,5)
    by (simp add: norm_minus_commute) (simp add: field_simps)
  have "x \<in> affine hull S"
    using closure_affine_hull assms by auto
  moreover have "y \<in> affine hull S"
    using \<open>y \<in> S\<close> hull_subset[of S] by auto
  moreover have "c \<in> affine hull S"
    using assms rel_interior_subset hull_subset[of S] by auto
  ultimately have "z \<in> affine hull S"
    using z_def affine_affine_hull[of S]
      mem_affine_3_minus [of "affine hull S" c x y "(1 - e) / e"]
      assms
    by simp
  then have "z \<in> S" using d zball by auto
  obtain d1 where "d1 > 0" and d1: "ball z d1 \<le> ball c d"
    using zball open_ball[of c d] openE[of "ball c d" z] by auto
  then have "ball z d1 \<inter> affine hull S \<subseteq> ball c d \<inter> affine hull S"
    by auto
  then have "ball z d1 \<inter> affine hull S \<subseteq> S"
    using d by auto
  then have "z \<in> rel_interior S"
    using mem_rel_interior_ball using \<open>d1 > 0\<close> \<open>z \<in> S\<close> by auto
  then have "y - e *\<^sub>R (y - z) \<in> rel_interior S"
    using rel_interior_convex_shrink[of S z y e] assms \<open>y \<in> S\<close> by auto
  then show ?thesis using * by auto
qed

lemma rel_interior_eq:
   "rel_interior s = s \<longleftrightarrow> openin(top_of_set (affine hull s)) s"
using rel_open rel_open_def by blast

lemma rel_interior_openin:
   "openin(top_of_set (affine hull s)) s \<Longrightarrow> rel_interior s = s"
by (simp add: rel_interior_eq)

lemma rel_interior_affine:
  fixes S :: "'n::euclidean_space set"
  shows  "affine S \<Longrightarrow> rel_interior S = S"
using affine_rel_open rel_open_def by auto

lemma rel_interior_eq_closure:
  fixes S :: "'n::euclidean_space set"
  shows "rel_interior S = closure S \<longleftrightarrow> affine S"
proof (cases "S = {}")
  case True
 then show ?thesis
    by auto
next
  case False show ?thesis
  proof
    assume eq: "rel_interior S = closure S"
    have "openin (top_of_set (affine hull S)) S"
      by (metis eq closure_subset openin_rel_interior rel_interior_subset subset_antisym)
    moreover have "closedin (top_of_set (affine hull S)) S"
      by (metis closed_subset closure_subset_eq eq hull_subset rel_interior_subset)
    ultimately have "S = {} \<or> S = affine hull S"
      using convex_connected connected_clopen convex_affine_hull by metis
    with False have "affine hull S = S"
      by auto
    then show "affine S"
      by (metis affine_hull_eq)
  next
    assume "affine S"
    then show "rel_interior S = closure S"
      by (simp add: rel_interior_affine affine_closed)
  qed
qed


subsubsection\<^marker>\<open>tag unimportant\<close>\<open>Relative interior preserves under linear transformations\<close>

lemma rel_interior_translation_aux:
  fixes a :: "'n::euclidean_space"
  shows "((\<lambda>x. a + x) ` rel_interior S) \<subseteq> rel_interior ((\<lambda>x. a + x) ` S)"
proof -
  {
    fix x
    assume x: "x \<in> rel_interior S"
    then obtain T where "open T" "x \<in> T \<inter> S" "T \<inter> affine hull S \<subseteq> S"
      using mem_rel_interior[of x S] by auto
    then have "open ((\<lambda>x. a + x) ` T)"
      and "a + x \<in> ((\<lambda>x. a + x) ` T) \<inter> ((\<lambda>x. a + x) ` S)"
      and "((\<lambda>x. a + x) ` T) \<inter> affine hull ((\<lambda>x. a + x) ` S) \<subseteq> (\<lambda>x. a + x) ` S"
      using affine_hull_translation[of a S] open_translation[of T a] x by auto
    then have "a + x \<in> rel_interior ((\<lambda>x. a + x) ` S)"
      using mem_rel_interior[of "a+x" "((\<lambda>x. a + x) ` S)"] by auto
  }
  then show ?thesis by auto
qed

lemma rel_interior_translation:
  fixes a :: "'n::euclidean_space"
  shows "rel_interior ((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` rel_interior S"
proof -
  have "(\<lambda>x. (-a) + x) ` rel_interior ((\<lambda>x. a + x) ` S) \<subseteq> rel_interior S"
    using rel_interior_translation_aux[of "-a" "(\<lambda>x. a + x) ` S"]
      translation_assoc[of "-a" "a"]
    by auto
  then have "((\<lambda>x. a + x) ` rel_interior S) \<supseteq> rel_interior ((\<lambda>x. a + x) ` S)"
    using translation_inverse_subset[of a "rel_interior ((+) a ` S)" "rel_interior S"]
    by auto
  then show ?thesis
    using rel_interior_translation_aux[of a S] by auto
qed


lemma affine_hull_linear_image:
  assumes "bounded_linear f"
  shows "f ` (affine hull s) = affine hull f ` s"
proof -
  interpret f: bounded_linear f by fact
  have "affine {x. f x \<in> affine hull f ` s}"
    unfolding affine_def
    by (auto simp: f.scaleR f.add affine_affine_hull[unfolded affine_def, rule_format])
  moreover have "affine {x. x \<in> f ` (affine hull s)}"
    using affine_affine_hull[unfolded affine_def, of s]
    unfolding affine_def by (auto simp: f.scaleR [symmetric] f.add [symmetric])
  ultimately show ?thesis
    by (auto simp: hull_inc elim!: hull_induct)
qed 


lemma rel_interior_injective_on_span_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
    and S :: "'m::euclidean_space set"
  assumes "bounded_linear f"
    and "inj_on f (span S)"
  shows "rel_interior (f ` S) = f ` (rel_interior S)"
proof -
  {
    fix z
    assume z: "z \<in> rel_interior (f ` S)"
    then have "z \<in> f ` S"
      using rel_interior_subset[of "f ` S"] by auto
    then obtain x where x: "x \<in> S" "f x = z" by auto
    obtain e2 where e2: "e2 > 0" "cball z e2 \<inter> affine hull (f ` S) \<subseteq> (f ` S)"
      using z rel_interior_cball[of "f ` S"] by auto
    obtain K where K: "K > 0" "\<And>x. norm (f x) \<le> norm x * K"
     using assms Real_Vector_Spaces.bounded_linear.pos_bounded[of f] by auto
    define e1 where "e1 = 1 / K"
    then have e1: "e1 > 0" "\<And>x. e1 * norm (f x) \<le> norm x"
      using K pos_le_divide_eq[of e1] by auto
    define e where "e = e1 * e2"
    then have "e > 0" using e1 e2 by auto
    {
      fix y
      assume y: "y \<in> cball x e \<inter> affine hull S"
      then have h1: "f y \<in> affine hull (f ` S)"
        using affine_hull_linear_image[of f S] assms by auto
      from y have "norm (x-y) \<le> e1 * e2"
        using cball_def[of x e] dist_norm[of x y] e_def by auto
      moreover have "f x - f y = f (x - y)"
        using assms linear_diff[of f x y] linear_conv_bounded_linear[of f] by auto
      moreover have "e1 * norm (f (x-y)) \<le> norm (x - y)"
        using e1 by auto
      ultimately have "e1 * norm ((f x)-(f y)) \<le> e1 * e2"
        by auto
      then have "f y \<in> cball z e2"
        using cball_def[of "f x" e2] dist_norm[of "f x" "f y"] e1 x by auto
      then have "f y \<in> f ` S"
        using y e2 h1 by auto
      then have "y \<in> S"
        using assms y hull_subset[of S] affine_hull_subset_span
          inj_on_image_mem_iff [OF \<open>inj_on f (span S)\<close>]
        by (metis Int_iff span_superset subsetCE)
    }
    then have "z \<in> f ` (rel_interior S)"
      using mem_rel_interior_cball[of x S] \<open>e > 0\<close> x by auto
  }
  moreover
  {
    fix x
    assume x: "x \<in> rel_interior S"
    then obtain e2 where e2: "e2 > 0" "cball x e2 \<inter> affine hull S \<subseteq> S"
      using rel_interior_cball[of S] by auto
    have "x \<in> S" using x rel_interior_subset by auto
    then have *: "f x \<in> f ` S" by auto
    have "\<forall>x\<in>span S. f x = 0 \<longrightarrow> x = 0"
      using assms subspace_span linear_conv_bounded_linear[of f]
        linear_injective_on_subspace_0[of f "span S"]
      by auto
    then obtain e1 where e1: "e1 > 0" "\<forall>x \<in> span S. e1 * norm x \<le> norm (f x)"
      using assms injective_imp_isometric[of "span S" f]
        subspace_span[of S] closed_subspace[of "span S"]
      by auto
    define e where "e = e1 * e2"
    hence "e > 0" using e1 e2 by auto
    {
      fix y
      assume y: "y \<in> cball (f x) e \<inter> affine hull (f ` S)"
      then have "y \<in> f ` (affine hull S)"
        using affine_hull_linear_image[of f S] assms by auto
      then obtain xy where xy: "xy \<in> affine hull S" "f xy = y" by auto
      with y have "norm (f x - f xy) \<le> e1 * e2"
        using cball_def[of "f x" e] dist_norm[of "f x" y] e_def by auto
      moreover have "f x - f xy = f (x - xy)"
        using assms linear_diff[of f x xy] linear_conv_bounded_linear[of f] by auto
      moreover have *: "x - xy \<in> span S"
        using subspace_diff[of "span S" x xy] subspace_span \<open>x \<in> S\<close> xy
          affine_hull_subset_span[of S] span_superset
        by auto
      moreover from * have "e1 * norm (x - xy) \<le> norm (f (x - xy))"
        using e1 by auto
      ultimately have "e1 * norm (x - xy) \<le> e1 * e2"
        by auto
      then have "xy \<in> cball x e2"
        using cball_def[of x e2] dist_norm[of x xy] e1 by auto
      then have "y \<in> f ` S"
        using xy e2 by auto
    }
    then have "f x \<in> rel_interior (f ` S)"
      using mem_rel_interior_cball[of "(f x)" "(f ` S)"] * \<open>e > 0\<close> by auto
  }
  ultimately show ?thesis by auto
qed

lemma rel_interior_injective_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "bounded_linear f"
    and "inj f"
  shows "rel_interior (f ` S) = f ` (rel_interior S)"
  using assms rel_interior_injective_on_span_linear_image[of f S]
    subset_inj_on[of f "UNIV" "span S"]
  by auto


subsection\<^marker>\<open>tag unimportant\<close> \<open>Openness and compactness are preserved by convex hull operation\<close>

lemma open_convex_hull[intro]:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (convex hull S)"
proof (clarsimp simp: open_contains_cball convex_hull_explicit)
  fix T and u :: "'a\<Rightarrow>real"
  assume obt: "finite T" "T\<subseteq>S" "\<forall>x\<in>T. 0 \<le> u x" "sum u T = 1" 

  from assms[unfolded open_contains_cball] obtain b
    where b: "\<And>x. x\<in>S \<Longrightarrow> 0 < b x \<and> cball x (b x) \<subseteq> S" by metis
  have "b ` T \<noteq> {}"
    using obt by auto
  define i where "i = b ` T"
  let ?\<Phi> = "\<lambda>y. \<exists>F. finite F \<and> F \<subseteq> S \<and> (\<exists>u. (\<forall>x\<in>F. 0 \<le> u x) \<and> sum u F = 1 \<and> (\<Sum>v\<in>F. u v *\<^sub>R v) = y)"
  let ?a = "\<Sum>v\<in>T. u v *\<^sub>R v"
  show "\<exists>e > 0. cball ?a e \<subseteq> {y. ?\<Phi> y}"
  proof (intro exI subsetI conjI)
    show "0 < Min i"
      unfolding i_def and Min_gr_iff[OF finite_imageI[OF obt(1)] \<open>b ` T\<noteq>{}\<close>]
      using b \<open>T\<subseteq>S\<close> by auto
  next
    fix y
    assume "y \<in> cball ?a (Min i)"
    then have y: "norm (?a - y) \<le> Min i"
      unfolding dist_norm[symmetric] by auto
    { fix x
      assume "x \<in> T"
      then have "Min i \<le> b x"
        by (simp add: i_def obt(1))
      then have "x + (y - ?a) \<in> cball x (b x)"
        using y unfolding mem_cball dist_norm by auto
      moreover have "x \<in> S"
        using \<open>x\<in>T\<close> \<open>T\<subseteq>S\<close> by auto
      ultimately have "x + (y - ?a) \<in> S"
        using y b by blast
    }
    moreover
    have *: "inj_on (\<lambda>v. v + (y - ?a)) T"
      unfolding inj_on_def by auto
    have "(\<Sum>v\<in>(\<lambda>v. v + (y - ?a)) ` T. u (v - (y - ?a)) *\<^sub>R v) = y"
      unfolding sum.reindex[OF *] o_def using obt(4)
      by (simp add: sum.distrib sum_subtractf scaleR_left.sum[symmetric] scaleR_right_distrib)
    ultimately show "y \<in> {y. ?\<Phi> y}"
    proof (intro CollectI exI conjI)
      show "finite ((\<lambda>v. v + (y - ?a)) ` T)"
        by (simp add: obt(1))
      show "sum (\<lambda>v. u (v - (y - ?a))) ((\<lambda>v. v + (y - ?a)) ` T) = 1"
        unfolding sum.reindex[OF *] o_def using obt(4) by auto
    qed (use obt(1, 3) in auto)
  qed
qed

lemma compact_convex_combinations:
  fixes S T :: "'a::real_normed_vector set"
  assumes "compact S" "compact T"
  shows "compact { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> S \<and> y \<in> T}"
proof -
  let ?X = "{0..1} \<times> S \<times> T"
  let ?h = "(\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
  have *: "{ (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> S \<and> y \<in> T} = ?h ` ?X"
    by force
  have "continuous_on ?X (\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  with assms show ?thesis
    by (simp add: * compact_Times compact_continuous_image)
qed

lemma finite_imp_compact_convex_hull:
  fixes S :: "'a::real_normed_vector set"
  assumes "finite S"
  shows "compact (convex hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis by simp
next
  case False
  with assms show ?thesis
  proof (induct rule: finite_ne_induct)
    case (singleton x)
    show ?case by simp
  next
    case (insert x A)
    let ?f = "\<lambda>(u, y::'a). u *\<^sub>R x + (1 - u) *\<^sub>R y"
    let ?T = "{0..1::real} \<times> (convex hull A)"
    have "continuous_on ?T ?f"
      unfolding split_def continuous_on by (intro ballI tendsto_intros)
    moreover have "compact ?T"
      by (intro compact_Times compact_Icc insert)
    ultimately have "compact (?f ` ?T)"
      by (rule compact_continuous_image)
    also have "?f ` ?T = convex hull (insert x A)"
      unfolding convex_hull_insert [OF \<open>A \<noteq> {}\<close>]
      apply safe
      apply (rule_tac x=a in exI, simp)
      apply (rule_tac x="1 - a" in exI, simp, fast)
      apply (rule_tac x="(u, b)" in image_eqI, simp_all)
      done
    finally show "compact (convex hull (insert x A))" .
  qed
qed

lemma compact_convex_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S"
  shows "compact (convex hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis using compact_empty by simp
next
  case False
  then obtain w where "w \<in> S" by auto
  show ?thesis
    unfolding caratheodory[of S]
  proof (induct ("DIM('a) + 1"))
    case 0
    have *: "{x.\<exists>sa. finite sa \<and> sa \<subseteq> S \<and> card sa \<le> 0 \<and> x \<in> convex hull sa} = {}"
      using compact_empty by auto
    from 0 show ?case unfolding * by simp
  next
    case (Suc n)
    show ?case
    proof (cases "n = 0")
      case True
      have "{x. \<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T} = S"
        unfolding set_eq_iff and mem_Collect_eq
      proof (rule, rule)
        fix x
        assume "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
        then obtain T where T: "finite T" "T \<subseteq> S" "card T \<le> Suc n" "x \<in> convex hull T"
          by auto
        show "x \<in> S"
        proof (cases "card T = 0")
          case True
          then show ?thesis
            using T(4) unfolding card_0_eq[OF T(1)] by simp
        next
          case False
          then have "card T = Suc 0" using T(3) \<open>n=0\<close> by auto
          then obtain a where "T = {a}" unfolding card_Suc_eq by auto
          then show ?thesis using T(2,4) by simp
        qed
      next
        fix x assume "x\<in>S"
        then show "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
          by (rule_tac x="{x}" in exI) (use convex_hull_singleton in auto)
      qed
      then show ?thesis using assms by simp
    next
      case False
      have "{x. \<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T} =
        {(1 - u) *\<^sub>R x + u *\<^sub>R y | x y u.
          0 \<le> u \<and> u \<le> 1 \<and> x \<in> S \<and> y \<in> {x. \<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> n \<and> x \<in> convex hull T}}"
        unfolding set_eq_iff and mem_Collect_eq
      proof (rule, rule)
        fix x
        assume "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> S \<and> (\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> n \<and> v \<in> convex hull T)"
        then obtain u v c T where obt: "x = (1 - c) *\<^sub>R u + c *\<^sub>R v"
          "0 \<le> c \<and> c \<le> 1" "u \<in> S" "finite T" "T \<subseteq> S" "card T \<le> n"  "v \<in> convex hull T"
          by auto
        moreover have "(1 - c) *\<^sub>R u + c *\<^sub>R v \<in> convex hull insert u T"
          by (meson convexD_alt convex_convex_hull hull_inc hull_mono in_mono insertCI obt(2) obt(7) subset_insertI)
        ultimately show "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
          by (rule_tac x="insert u T" in exI) (auto simp: card_insert_if)
      next
        fix x
        assume "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
        then obtain T where T: "finite T" "T \<subseteq> S" "card T \<le> Suc n" "x \<in> convex hull T"
          by auto
        show "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> S \<and> (\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> n \<and> v \<in> convex hull T)"
        proof (cases "card T = Suc n")
          case False
          then have "card T \<le> n" using T(3) by auto
          then show ?thesis
            using \<open>w\<in>S\<close> and T
            by (rule_tac x=w in exI, rule_tac x=x in exI, rule_tac x=1 in exI) auto
        next
          case True
          then obtain a u where au: "T = insert a u" "a\<notin>u"
            by (metis card_le_Suc_iff order_refl)
          show ?thesis
          proof (cases "u = {}")
            case True
            then have "x = a" using T(4)[unfolded au] by auto
            show ?thesis unfolding \<open>x = a\<close>
              using T \<open>n \<noteq> 0\<close> unfolding au              
              by (rule_tac x=a in exI, rule_tac x=a in exI, rule_tac x=1 in exI) force
          next
            case False
            obtain ux vx b where obt: "ux\<ge>0" "vx\<ge>0" "ux + vx = 1"
              "b \<in> convex hull u" "x = ux *\<^sub>R a + vx *\<^sub>R b"
              using T(4)[unfolded au convex_hull_insert[OF False]]
              by auto
            have *: "1 - vx = ux" using obt(3) by auto
            show ?thesis
              using obt T(1-3) card_insert_disjoint[OF _ au(2)] unfolding au *  
              by (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=vx in exI) force
          qed
        qed
      qed
      then show ?thesis
        using compact_convex_combinations[OF assms Suc] by simp
    qed
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Extremal points of a simplex are some vertices\<close>

lemma dist_increases_online:
  fixes a b d :: "'a::real_inner"
  assumes "d \<noteq> 0"
  shows "dist a (b + d) > dist a b \<or> dist a (b - d) > dist a b"
proof (cases "inner a d - inner b d > 0")
  case True
  then have "0 < inner d d + (inner a d * 2 - inner b d * 2)"
    using assms
    by (intro add_pos_pos) auto
  then show ?thesis
    unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    by (simp add: algebra_simps inner_commute)
next
  case False
  then have "0 < inner d d + (inner b d * 2 - inner a d * 2)"
    using assms
    by (intro add_pos_nonneg) auto
  then show ?thesis
    unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    by (simp add: algebra_simps inner_commute)
qed

lemma norm_increases_online:
  fixes d :: "'a::real_inner"
  shows "d \<noteq> 0 \<Longrightarrow> norm (a + d) > norm a \<or> norm(a - d) > norm a"
  using dist_increases_online[of d a 0] unfolding dist_norm by auto

lemma simplex_furthest_lt:
  fixes S :: "'a::real_inner set"
  assumes "finite S"
  shows "\<forall>x \<in> convex hull S.  x \<notin> S \<longrightarrow> (\<exists>y \<in> convex hull S. norm (x - a) < norm(y - a))"
  using assms
proof induct
  fix x S
  assume as: "finite S" "x\<notin>S" "\<forall>x\<in>convex hull S. x \<notin> S \<longrightarrow> (\<exists>y\<in>convex hull S. norm (x - a) < norm (y - a))"
  show "\<forall>xa\<in>convex hull insert x S. xa \<notin> insert x S \<longrightarrow>
    (\<exists>y\<in>convex hull insert x S. norm (xa - a) < norm (y - a))"
  proof (intro impI ballI, cases "S = {}")
    case False
    fix y
    assume y: "y \<in> convex hull insert x S" "y \<notin> insert x S"
    obtain u v b where obt: "u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull S" "y = u *\<^sub>R x + v *\<^sub>R b"
      using y(1)[unfolded convex_hull_insert[OF False]] by auto
    show "\<exists>z\<in>convex hull insert x S. norm (y - a) < norm (z - a)"
    proof (cases "y \<in> convex hull S")
      case True
      then obtain z where "z \<in> convex hull S" "norm (y - a) < norm (z - a)"
        using as(3)[THEN bspec[where x=y]] and y(2) by auto
      then show ?thesis
        by (meson hull_mono subsetD subset_insertI)
    next
      case False
      show ?thesis
      proof (cases "u = 0 \<or> v = 0")
        case True
        with False show ?thesis
          using obt y by auto
      next
        case False
        then obtain w where w: "w>0" "w<u" "w<v"
          using field_lbound_gt_zero[of u v] and obt(1,2) by auto
        have "x \<noteq> b"
        proof
          assume "x = b"
          then have "y = b" unfolding obt(5)
            using obt(3) by (auto simp: scaleR_left_distrib[symmetric])
          then show False using obt(4) and False
            using \<open>x = b\<close> y(2) by blast
        qed
        then have *: "w *\<^sub>R (x - b) \<noteq> 0" using w(1) by auto
        show ?thesis
          using dist_increases_online[OF *, of a y]
        proof (elim disjE)
          assume "dist a y < dist a (y + w *\<^sub>R (x - b))"
          then have "norm (y - a) < norm ((u + w) *\<^sub>R x + (v - w) *\<^sub>R b - a)"
            unfolding dist_commute[of a]
            unfolding dist_norm obt(5)
            by (simp add: algebra_simps)
          moreover have "(u + w) *\<^sub>R x + (v - w) *\<^sub>R b \<in> convex hull insert x S"
            unfolding convex_hull_insert[OF \<open>S\<noteq>{}\<close>]
          proof (intro CollectI conjI exI)
            show "u + w \<ge> 0" "v - w \<ge> 0"
              using obt(1) w by auto
          qed (use obt in auto)
          ultimately show ?thesis by auto
        next
          assume "dist a y < dist a (y - w *\<^sub>R (x - b))"
          then have "norm (y - a) < norm ((u - w) *\<^sub>R x + (v + w) *\<^sub>R b - a)"
            unfolding dist_commute[of a]
            unfolding dist_norm obt(5)
            by (simp add: algebra_simps)
          moreover have "(u - w) *\<^sub>R x + (v + w) *\<^sub>R b \<in> convex hull insert x S"
            unfolding convex_hull_insert[OF \<open>S\<noteq>{}\<close>]
          proof (intro CollectI conjI exI)
            show "u - w \<ge> 0" "v + w \<ge> 0"
              using obt(1) w by auto
          qed (use obt in auto)
          ultimately show ?thesis by auto
        qed
      qed
    qed
  qed auto
qed (auto simp: assms)

lemma simplex_furthest_le:
  fixes S :: "'a::real_inner set"
  assumes "finite S"
    and "S \<noteq> {}"
  shows "\<exists>y\<in>S. \<forall>x\<in> convex hull S. norm (x - a) \<le> norm (y - a)"
proof -
  have "convex hull S \<noteq> {}"
    using hull_subset[of S convex] and assms(2) by auto
  then obtain x where x: "x \<in> convex hull S" "\<forall>y\<in>convex hull S. norm (y - a) \<le> norm (x - a)"
    using distance_attains_sup[OF finite_imp_compact_convex_hull[OF \<open>finite S\<close>], of a]
    unfolding dist_commute[of a]
    unfolding dist_norm
    by auto
  show ?thesis
  proof (cases "x \<in> S")
    case False
    then obtain y where "y \<in> convex hull S" "norm (x - a) < norm (y - a)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=x]] and x(1)
      by auto
    then show ?thesis
      using x(2)[THEN bspec[where x=y]] by auto
  next
    case True
    with x show ?thesis by auto
  qed
qed

lemma simplex_furthest_le_exists:
  fixes S :: "('a::real_inner) set"
  shows "finite S \<Longrightarrow> \<forall>x\<in>(convex hull S). \<exists>y\<in>S. norm (x - a) \<le> norm (y - a)"
  using simplex_furthest_le[of S] by (cases "S = {}") auto

lemma simplex_extremal_le:
  fixes S :: "'a::real_inner set"
  assumes "finite S"
    and "S \<noteq> {}"
  shows "\<exists>u\<in>S. \<exists>v\<in>S. \<forall>x\<in>convex hull S. \<forall>y \<in> convex hull S. norm (x - y) \<le> norm (u - v)"
proof -
  have "convex hull S \<noteq> {}"
    using hull_subset[of S convex] and assms(2) by auto
  then obtain u v where obt: "u \<in> convex hull S" "v \<in> convex hull S"
    "\<forall>x\<in>convex hull S. \<forall>y\<in>convex hull S. norm (x - y) \<le> norm (u - v)"
    using compact_sup_maxdistance[OF finite_imp_compact_convex_hull[OF assms(1)]]
    by (auto simp: dist_norm)
  then show ?thesis
  proof (cases "u\<notin>S \<or> v\<notin>S", elim disjE)
    assume "u \<notin> S"
    then obtain y where "y \<in> convex hull S" "norm (u - v) < norm (y - v)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=u]] and obt(1)
      by auto
    then show ?thesis
      using obt(3)[THEN bspec[where x=y], THEN bspec[where x=v]] and obt(2)
      by auto
  next
    assume "v \<notin> S"
    then obtain y where "y \<in> convex hull S" "norm (v - u) < norm (y - u)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=v]] and obt(2)
      by auto
    then show ?thesis
      using obt(3)[THEN bspec[where x=u], THEN bspec[where x=y]] and obt(1)
      by (auto simp: norm_minus_commute)
  qed auto
qed

lemma simplex_extremal_le_exists:
  fixes S :: "'a::real_inner set"
  shows "finite S \<Longrightarrow> x \<in> convex hull S \<Longrightarrow> y \<in> convex hull S \<Longrightarrow>
    \<exists>u\<in>S. \<exists>v\<in>S. norm (x - y) \<le> norm (u - v)"
  using convex_hull_empty simplex_extremal_le[of S]
  by(cases "S = {}") auto


subsection \<open>Closest point of a convex set is unique, with a continuous projection\<close>

definition\<^marker>\<open>tag important\<close> closest_point :: "'a::{real_inner,heine_borel} set \<Rightarrow> 'a \<Rightarrow> 'a"
  where "closest_point S a = (SOME x. x \<in> S \<and> (\<forall>y\<in>S. dist a x \<le> dist a y))"

lemma closest_point_exists:
  assumes "closed S"
    and "S \<noteq> {}"
  shows closest_point_in_set: "closest_point S a \<in> S"
    and "\<forall>y\<in>S. dist a (closest_point S a) \<le> dist a y"
  unfolding closest_point_def
  by (rule_tac someI2_ex, auto intro: distance_attains_inf[OF assms(1,2), of a])+

lemma closest_point_le: "closed S \<Longrightarrow> x \<in> S \<Longrightarrow> dist a (closest_point S a) \<le> dist a x"
  using closest_point_exists[of S] by auto

lemma closest_point_self:
  assumes "x \<in> S"
  shows "closest_point S x = x"
  unfolding closest_point_def
  by (rule some1_equality, rule ex1I[of _ x]) (use assms in auto)

lemma closest_point_refl: "closed S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> closest_point S x = x \<longleftrightarrow> x \<in> S"
  using closest_point_in_set[of S x] closest_point_self[of x S]
  by auto

lemma closer_points_lemma:
  assumes "inner y z > 0"
  shows "\<exists>u>0. \<forall>v>0. v \<le> u \<longrightarrow> norm(v *\<^sub>R z - y) < norm y"
proof -
  have z: "inner z z > 0"
    unfolding inner_gt_zero_iff using assms by auto
  have "norm (v *\<^sub>R z - y) < norm y"
    if "0 < v" and "v \<le> inner y z / inner z z" for v
    unfolding norm_lt using z assms that
    by (simp add: field_simps inner_diff inner_commute mult_strict_left_mono[OF _ \<open>0<v\<close>])
  then show ?thesis
    using assms z
    by (rule_tac x = "inner y z / inner z z" in exI) auto
qed

lemma closer_point_lemma:
  assumes "inner (y - x) (z - x) > 0"
  shows "\<exists>u>0. u \<le> 1 \<and> dist (x + u *\<^sub>R (z - x)) y < dist x y"
proof -
  obtain u where "u > 0"
    and u: "\<And>v. \<lbrakk>0<v; v \<le> u\<rbrakk> \<Longrightarrow> norm (v *\<^sub>R (z - x) - (y - x)) < norm (y - x)"
    using closer_points_lemma[OF assms] by auto
  show ?thesis
    using u[of "min u 1"] and \<open>u > 0\<close>
    by (metis diff_diff_add dist_commute dist_norm less_eq_real_def not_less u zero_less_one)
qed

lemma any_closest_point_dot:
  assumes "convex S" "closed S" "x \<in> S" "y \<in> S" "\<forall>z\<in>S. dist a x \<le> dist a z"
  shows "inner (a - x) (y - x) \<le> 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain u where u: "u>0" "u\<le>1" "dist (x + u *\<^sub>R (y - x)) a < dist x a"
    using closer_point_lemma[of a x y] by auto
  let ?z = "(1 - u) *\<^sub>R x + u *\<^sub>R y"
  have "?z \<in> S"
    using convexD_alt[OF assms(1,3,4), of u] using u by auto
  then show False
    using assms(5)[THEN bspec[where x="?z"]] and u(3)
    by (auto simp: dist_commute algebra_simps)
qed

lemma any_closest_point_unique:
  fixes x :: "'a::real_inner"
  assumes "convex S" "closed S" "x \<in> S" "y \<in> S"
    "\<forall>z\<in>S. dist a x \<le> dist a z" "\<forall>z\<in>S. dist a y \<le> dist a z"
  shows "x = y"
  using any_closest_point_dot[OF assms(1-4,5)] and any_closest_point_dot[OF assms(1-2,4,3,6)]
  unfolding norm_pths(1) and norm_le_square
  by (auto simp: algebra_simps)

lemma closest_point_unique:
  assumes "convex S" "closed S" "x \<in> S" "\<forall>z\<in>S. dist a x \<le> dist a z"
  shows "x = closest_point S a"
  using any_closest_point_unique[OF assms(1-3) _ assms(4), of "closest_point S a"]
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_dot:
  assumes "convex S" "closed S" "x \<in> S"
  shows "inner (a - closest_point S a) (x - closest_point S a) \<le> 0"
  using any_closest_point_dot[OF assms(1,2) _ assms(3)]
  by (metis assms(2) assms(3) closest_point_in_set closest_point_le empty_iff)

lemma closest_point_lt:
  assumes "convex S" "closed S" "x \<in> S" "x \<noteq> closest_point S a"
  shows "dist a (closest_point S a) < dist a x"
  using closest_point_unique[where a=a] closest_point_le[where a=a] assms by fastforce

lemma setdist_closest_point:
    "\<lbrakk>closed S; S \<noteq> {}\<rbrakk> \<Longrightarrow> setdist {a} S = dist a (closest_point S a)"
  by (metis closest_point_exists(2) closest_point_in_set emptyE insert_iff setdist_unique)

lemma closest_point_lipschitz:
  assumes "convex S"
    and "closed S" "S \<noteq> {}"
  shows "dist (closest_point S x) (closest_point S y) \<le> dist x y"
proof -
  have "inner (x - closest_point S x) (closest_point S y - closest_point S x) \<le> 0"
    and "inner (y - closest_point S y) (closest_point S x - closest_point S y) \<le> 0"
    by (simp_all add: assms closest_point_dot closest_point_in_set)
  then show ?thesis unfolding dist_norm and norm_le
    using inner_ge_zero[of "(x - closest_point S x) - (y - closest_point S y)"]
    by (simp add: inner_add inner_diff inner_commute)
qed

lemma continuous_at_closest_point:
  assumes "convex S"
    and "closed S"
    and "S \<noteq> {}"
  shows "continuous (at x) (closest_point S)"
  unfolding continuous_at_eps_delta
  using le_less_trans[OF closest_point_lipschitz[OF assms]] by auto

lemma continuous_on_closest_point:
  assumes "convex S"
    and "closed S"
    and "S \<noteq> {}"
  shows "continuous_on t (closest_point S)"
  by (metis continuous_at_imp_continuous_on continuous_at_closest_point[OF assms])

proposition closest_point_in_rel_interior:
  assumes "closed S" "S \<noteq> {}" and x: "x \<in> affine hull S"
    shows "closest_point S x \<in> rel_interior S \<longleftrightarrow> x \<in> rel_interior S"
proof (cases "x \<in> S")
  case True
  then show ?thesis
    by (simp add: closest_point_self)
next
  case False
  then have "False" if asm: "closest_point S x \<in> rel_interior S"
  proof -
    obtain e where "e > 0" and clox: "closest_point S x \<in> S"
               and e: "cball (closest_point S x) e \<inter> affine hull S \<subseteq> S"
      using asm mem_rel_interior_cball by blast
    then have clo_notx: "closest_point S x \<noteq> x"
      using \<open>x \<notin> S\<close> by auto
    define y where "y \<equiv> closest_point S x -
                        (min 1 (e / norm(closest_point S x - x))) *\<^sub>R (closest_point S x - x)"
    have "x - y = (1 - min 1 (e / norm (closest_point S x - x))) *\<^sub>R (x - closest_point S x)"
      by (simp add: y_def algebra_simps)
    then have "norm (x - y) = abs ((1 - min 1 (e / norm (closest_point S x - x)))) * norm(x - closest_point S x)"
      by simp
    also have "\<dots> < norm(x - closest_point S x)"
      using clo_notx \<open>e > 0\<close>
      by (auto simp: mult_less_cancel_right2 field_split_simps)
    finally have no_less: "norm (x - y) < norm (x - closest_point S x)" .
    have "y \<in> affine hull S"
      unfolding y_def
      by (meson affine_affine_hull clox hull_subset mem_affine_3_minus2 subsetD x)
    moreover have "dist (closest_point S x) y \<le> e"
      using \<open>e > 0\<close> by (auto simp: y_def min_mult_distrib_right)
    ultimately have "y \<in> S"
      using subsetD [OF e] by simp
    then have "dist x (closest_point S x) \<le> dist x y"
      by (simp add: closest_point_le \<open>closed S\<close>)
    with no_less show False
      by (simp add: dist_norm)
  qed
  moreover have "x \<notin> rel_interior S"
    using rel_interior_subset False by blast
  ultimately show ?thesis by blast
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Various point-to-set separating/supporting hyperplane theorems\<close>

lemma supporting_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex S"
    and "closed S"
    and "S \<noteq> {}"
    and "z \<notin> S"
  shows "\<exists>a b. \<exists>y\<in>S. inner a z < b \<and> inner a y = b \<and> (\<forall>x\<in>S. inner a x \<ge> b)"
proof -
  obtain y where "y \<in> S" and y: "\<forall>x\<in>S. dist z y \<le> dist z x"
    by (metis distance_attains_inf[OF assms(2-3)])
  show ?thesis
  proof (intro exI bexI conjI ballI)
    show "(y - z) \<bullet> z < (y - z) \<bullet> y"
      by (metis \<open>y \<in> S\<close> assms(4) diff_gt_0_iff_gt inner_commute inner_diff_left inner_gt_zero_iff right_minus_eq)
    show "(y - z) \<bullet> y \<le> (y - z) \<bullet> x" if "x \<in> S" for x
    proof (rule ccontr)
      have *: "\<And>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> dist z y \<le> dist z ((1 - u) *\<^sub>R y + u *\<^sub>R x)"
        using assms(1)[unfolded convex_alt] and y and \<open>x\<in>S\<close> and \<open>y\<in>S\<close> by auto
      assume "\<not> (y - z) \<bullet> y \<le> (y - z) \<bullet> x"
      then obtain v where "v > 0" "v \<le> 1" "dist (y + v *\<^sub>R (x - y)) z < dist y z"
        using closer_point_lemma[of z y x] by (auto simp: inner_diff)
      then show False
        using *[of v] by (auto simp: dist_commute algebra_simps)
    qed
  qed (use \<open>y \<in> S\<close> in auto)
qed

lemma separating_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex S"
    and "closed S"
    and "z \<notin> S"
  shows "\<exists>a b. inner a z < b \<and> (\<forall>x\<in>S. inner a x > b)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: gt_ex)
next
  case False
  obtain y where "y \<in> S" and y: "\<And>x. x \<in> S \<Longrightarrow> dist z y \<le> dist z x"
    by (metis distance_attains_inf[OF assms(2) False])
  show ?thesis
  proof (intro exI conjI ballI)
    show "(y - z) \<bullet> z < inner (y - z) z + (norm (y - z))\<^sup>2 / 2"
      using \<open>y\<in>S\<close> \<open>z\<notin>S\<close> by auto
  next
    fix x
    assume "x \<in> S"
    have "False" if *: "0 < inner (z - y) (x - y)"
    proof -
      obtain u where "u > 0" "u \<le> 1" "dist (y + u *\<^sub>R (x - y)) z < dist y z"
        using * closer_point_lemma by blast
      then show False using y[of "y + u *\<^sub>R (x - y)"] convexD_alt [OF \<open>convex S\<close>]
        using \<open>x\<in>S\<close> \<open>y\<in>S\<close> by (auto simp: dist_commute algebra_simps)
    qed
    moreover have "0 < (norm (y - z))\<^sup>2"
      using \<open>y\<in>S\<close> \<open>z\<notin>S\<close> by auto
    then have "0 < inner (y - z) (y - z)"
      unfolding power2_norm_eq_inner by simp
    ultimately show "(y - z) \<bullet> z + (norm (y - z))\<^sup>2 / 2 < (y - z) \<bullet> x"
      by (force simp: field_simps power2_norm_eq_inner inner_commute inner_diff)
  qed 
qed

lemma separating_hyperplane_closed_0:
  assumes "convex (S::('a::euclidean_space) set)"
    and "closed S"
    and "0 \<notin> S"
  shows "\<exists>a b. a \<noteq> 0 \<and> 0 < b \<and> (\<forall>x\<in>S. inner a x > b)"
proof (cases "S = {}")
  case True
  have "(SOME i. i\<in>Basis) \<noteq> (0::'a)"
    by (metis Basis_zero SOME_Basis)
  then show ?thesis
    using True zero_less_one by blast
next
  case False
  then show ?thesis
    using False using separating_hyperplane_closed_point[OF assms]
    by (metis all_not_in_conv inner_zero_left inner_zero_right less_eq_real_def not_le)
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Now set-to-set for closed/compact sets\<close>

lemma separating_hyperplane_closed_compact:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "closed S"
    and "convex T"
    and "compact T"
    and "T \<noteq> {}"
    and "S \<inter> T = {}"
  shows "\<exists>a b. (\<forall>x\<in>S. inner a x < b) \<and> (\<forall>x\<in>T. inner a x > b)"
proof (cases "S = {}")
  case True
  obtain b where b: "b > 0" "\<forall>x\<in>T. norm x \<le> b"
    using compact_imp_bounded[OF assms(4)] unfolding bounded_pos by auto
  obtain z :: 'a where z: "norm z = b + 1"
    using vector_choose_size[of "b + 1"] and b(1) by auto
  then have "z \<notin> T" using b(2)[THEN bspec[where x=z]] by auto
  then obtain a b where ab: "inner a z < b" "\<forall>x\<in>T. b < inner a x"
    using separating_hyperplane_closed_point[OF assms(3) compact_imp_closed[OF assms(4)], of z]
    by auto
  then show ?thesis
    using True by auto
next
  case False
  then obtain y where "y \<in> S" by auto
  obtain a b where "0 < b" and \<section>: "\<And>x. x \<in> (\<Union>x\<in> S. \<Union>y \<in> T. {x - y}) \<Longrightarrow> b < inner a x"
    using separating_hyperplane_closed_point[OF convex_differences[OF assms(1,3)], of 0]
    using closed_compact_differences assms by fastforce 
  have ab: "b + inner a y < inner a x" if "x\<in>S" "y\<in>T" for x y
    using \<section> [of "x-y"] that by (auto simp add: inner_diff_right less_diff_eq)
  define k where "k = (SUP x\<in>T. a \<bullet> x)"
  have "k + b / 2 < a \<bullet> x" if "x \<in> S" for x
  proof -
    have "k \<le> inner a x - b"
      unfolding k_def
      using \<open>T \<noteq> {}\<close> ab that by (fastforce intro: cSUP_least)
    then show ?thesis
      using \<open>0 < b\<close> by auto
  qed
  moreover
  have "- (k + b / 2) < - a \<bullet> x" if "x \<in> T" for x
  proof -
    have "inner a x - b / 2 < k"
      unfolding k_def
    proof (subst less_cSUP_iff)
      show "T \<noteq> {}" by fact
      show "bdd_above ((\<bullet>) a ` T)"
        using ab[rule_format, of y] \<open>y \<in> S\<close>
        by (intro bdd_aboveI2[where M="inner a y - b"]) (auto simp: field_simps intro: less_imp_le)
      show "\<exists>y\<in>T. a \<bullet> x - b / 2 < a \<bullet> y"
        using \<open>0 < b\<close> that by force
    qed 
    then show ?thesis
      by auto
  qed
  ultimately show ?thesis
    by (metis inner_minus_left neg_less_iff_less)
qed

lemma separating_hyperplane_compact_closed:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "compact S"
    and "S \<noteq> {}"
    and "convex T"
    and "closed T"
    and "S \<inter> T = {}"
  shows "\<exists>a b. (\<forall>x\<in>S. inner a x < b) \<and> (\<forall>x\<in>T. inner a x > b)"
proof -
  obtain a b where "(\<forall>x\<in>T. inner a x < b) \<and> (\<forall>x\<in>S. b < inner a x)"
    by (metis disjoint_iff_not_equal separating_hyperplane_closed_compact assms)
  then show ?thesis
    by (metis inner_minus_left neg_less_iff_less)
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>General case without assuming closure and getting non-strict separation\<close>

lemma separating_hyperplane_set_0:
  assumes "convex S" "(0::'a::euclidean_space) \<notin> S"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>x\<in>S. 0 \<le> inner a x)"
proof -
  let ?k = "\<lambda>c. {x::'a. 0 \<le> inner c x}"
  have *: "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}" if as: "f \<subseteq> ?k ` S" "finite f" for f
  proof -
    obtain c where c: "f = ?k ` c" "c \<subseteq> S" "finite c"
      using finite_subset_image[OF as(2,1)] by auto
    then obtain a b where ab: "a \<noteq> 0" "0 < b" "\<forall>x\<in>convex hull c. b < inner a x"
      using separating_hyperplane_closed_0[OF convex_convex_hull, of c]
      using finite_imp_compact_convex_hull[OF c(3), THEN compact_imp_closed] and assms(2)
      using subset_hull[of convex, OF assms(1), symmetric, of c]
      by force
    have "norm (a /\<^sub>R norm a) = 1"
      by (simp add: ab(1))
    moreover have "(\<forall>y\<in>c. 0 \<le> y \<bullet> (a /\<^sub>R norm a))"
      using hull_subset[of c convex] ab by (force simp: inner_commute)
    ultimately have "\<exists>x. norm x = 1 \<and> (\<forall>y\<in>c. 0 \<le> inner y x)"
      by blast
    then show "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}"
      unfolding c(1) frontier_cball sphere_def dist_norm by auto
  qed
  have "frontier (cball 0 1) \<inter> (\<Inter>(?k ` S)) \<noteq> {}"
    by (rule compact_imp_fip) (use * closed_halfspace_ge in auto)
  then obtain x where "norm x = 1" "\<forall>y\<in>S. x\<in>?k y"
    unfolding frontier_cball dist_norm sphere_def by auto
  then show ?thesis
    by (metis inner_commute mem_Collect_eq norm_eq_zero zero_neq_one)
qed

lemma separating_hyperplane_sets:
  fixes S T :: "'a::euclidean_space set"
  assumes "convex S"
    and "convex T"
    and "S \<noteq> {}"
    and "T \<noteq> {}"
    and "S \<inter> T = {}"
  shows "\<exists>a b. a \<noteq> 0 \<and> (\<forall>x\<in>S. inner a x \<le> b) \<and> (\<forall>x\<in>T. inner a x \<ge> b)"
proof -
  from separating_hyperplane_set_0[OF convex_differences[OF assms(2,1)]]
  obtain a where "a \<noteq> 0" "\<forall>x\<in>{x - y |x y. x \<in> T \<and> y \<in> S}. 0 \<le> inner a x"
    using assms(3-5) by force
  then have *: "\<And>x y. x \<in> T \<Longrightarrow> y \<in> S \<Longrightarrow> inner a y \<le> inner a x"
    by (force simp: inner_diff)
  then have bdd: "bdd_above (((\<bullet>) a)`S)"
    using \<open>T \<noteq> {}\<close> by (auto intro: bdd_aboveI2[OF *])
  show ?thesis
    using \<open>a\<noteq>0\<close>
    by (intro exI[of _ a] exI[of _ "SUP x\<in>S. a \<bullet> x"])
       (auto intro!: cSUP_upper bdd cSUP_least \<open>a \<noteq> 0\<close> \<open>S \<noteq> {}\<close> *)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>More convexity generalities\<close>

lemma convex_closure [intro,simp]:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "convex (closure S)"
  apply (rule convexI)
  unfolding closure_sequential
  apply (elim exE)
  subgoal for x y u v f g
    by (rule_tac x="\<lambda>n. u *\<^sub>R f n + v *\<^sub>R g n" in exI) (force intro: tendsto_intros dest: convexD [OF assms])
  done

lemma convex_interior [intro,simp]:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "convex (interior S)"
  unfolding convex_alt Ball_def mem_interior
proof clarify
  fix x y u
  assume u: "0 \<le> u" "u \<le> (1::real)"
  fix e d
  assume ed: "ball x e \<subseteq> S" "ball y d \<subseteq> S" "0<d" "0<e"
  show "\<exists>e>0. ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) e \<subseteq> S"
  proof (intro exI conjI subsetI)
    fix z
    assume z: "z \<in> ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) (min d e)"
    have "(1- u) *\<^sub>R (z - u *\<^sub>R (y - x)) + u *\<^sub>R (z + (1 - u) *\<^sub>R (y - x)) \<in> S"
    proof (rule_tac assms[unfolded convex_alt, rule_format])
       show "z - u *\<^sub>R (y - x) \<in> S" "z + (1 - u) *\<^sub>R (y - x) \<in> S"
         using ed z u by (auto simp add: algebra_simps dist_norm)
    qed (use u in auto)
    then show "z \<in> S"
      using u by (auto simp: algebra_simps)
  qed(use u ed in auto)
qed

lemma convex_hull_eq_empty[simp]: "convex hull S = {} \<longleftrightarrow> S = {}"
  using hull_subset[of S convex] convex_hull_empty by auto


subsection\<^marker>\<open>tag unimportant\<close> \<open>Convex set as intersection of halfspaces\<close>

lemma convex_halfspace_intersection:
  fixes S :: "('a::euclidean_space) set"
  assumes "closed S" "convex S"
  shows "S = \<Inter>{h. S \<subseteq> h \<and> (\<exists>a b. h = {x. inner a x \<le> b})}"
proof -
  { fix z
    assume "\<forall>T. S \<subseteq> T \<and> (\<exists>a b. T = {x. inner a x \<le> b}) \<longrightarrow> z \<in> T"  "z \<notin> S"
    then have \<section>: "\<And>a b. S \<subseteq> {x. inner a x \<le> b} \<Longrightarrow> z \<in> {x. inner a x \<le> b}"
      by blast
    obtain a b where "inner a z < b" "(\<forall>x\<in>S. inner a x > b)"
      using \<open>z \<notin> S\<close> assms separating_hyperplane_closed_point by blast
    then have False
      using \<section> [of "-a" "-b"] by fastforce
  }
  then show ?thesis
    by force
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Convexity of general and special intervals\<close>

lemma is_interval_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "is_interval S"
  shows "convex S"
proof (rule convexI)
  fix x y and u v :: real
  assume "x \<in> S" "y \<in> S" and uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  then have *: "u = 1 - v" "1 - v \<ge> 0" and **: "v = 1 - u" "1 - u \<ge> 0"
    by auto
  {
    fix a b
    assume "\<not> b \<le> u * a + v * b"
    then have "u * a < (1 - v) * b"
      unfolding not_le using \<open>0 \<le> v\<close>by (auto simp: field_simps)
    then have "a < b"
      using "*"(1) less_eq_real_def uv(1) by auto
    then have "a \<le> u * a + v * b"
      unfolding * using \<open>0 \<le> v\<close>
      by (auto simp: field_simps intro!:mult_right_mono)
  }
  moreover
  {
    fix a b
    assume "\<not> u * a + v * b \<le> a"
    then have "v * b > (1 - u) * a"
      unfolding not_le using \<open>0 \<le> v\<close> by (auto simp: field_simps)
    then have "a < b"
      unfolding * using \<open>0 \<le> v\<close>
      by (rule_tac mult_left_less_imp_less) (auto simp: field_simps)
    then have "u * a + v * b \<le> b"
      unfolding **
      using **(2) \<open>0 \<le> u\<close> by (auto simp: algebra_simps mult_right_mono)
  }
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> S"
    using DIM_positive[where 'a='a]
    by (intro mem_is_intervalI [OF assms \<open>x \<in> S\<close> \<open>y \<in> S\<close>]) (auto simp: inner_simps)
qed

lemma is_interval_connected:
  fixes S :: "'a::euclidean_space set"
  shows "is_interval S \<Longrightarrow> connected S"
  using is_interval_convex convex_connected by auto

lemma convex_box [simp]: "convex (cbox a b)" "convex (box a (b::'a::euclidean_space))"
  by (auto simp add: is_interval_convex)

text\<open>A non-singleton connected set is perfect (i.e. has no isolated points). \<close>
lemma connected_imp_perfect:
  fixes a :: "'a::metric_space"
  assumes "connected S" "a \<in> S" and S: "\<And>x. S \<noteq> {x}"
  shows "a islimpt S"
proof -
  have False if "a \<in> T" "open T" "\<And>y. \<lbrakk>y \<in> S; y \<in> T\<rbrakk> \<Longrightarrow> y = a" for T
  proof -
    obtain e where "e > 0" and e: "cball a e \<subseteq> T"
      using \<open>open T\<close> \<open>a \<in> T\<close> by (auto simp: open_contains_cball)
    have "openin (top_of_set S) {a}"
      unfolding openin_open using that \<open>a \<in> S\<close> by blast
    moreover have "closedin (top_of_set S) {a}"
      by (simp add: assms)
    ultimately show "False"
      using \<open>connected S\<close> connected_clopen S by blast
  qed
  then show ?thesis
    unfolding islimpt_def by blast
qed

lemma islimpt_Ioc [simp]:
  fixes a :: real
  assumes "a<b" 
  shows "x islimpt {a<..b} \<longleftrightarrow> x \<in> {a..b}"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis assms closed_atLeastAtMost closed_limpt closure_greaterThanAtMost closure_subset islimpt_subset)
next
  assume ?rhs
  then have "x \<in> closure {a<..<b}"
    using assms closure_greaterThanLessThan by blast
  then show ?lhs
    by (metis (no_types) Diff_empty Diff_insert0 interior_lessThanAtMost interior_limit_point interior_subset islimpt_in_closure islimpt_subset)
qed

lemma islimpt_Ico [simp]:
  fixes a :: real
  assumes "a<b" shows "x islimpt {a..<b} \<longleftrightarrow> x \<in> {a..b}"
  by (metis assms closure_atLeastLessThan closure_greaterThanAtMost islimpt_Ioc limpt_of_closure) 

lemma islimpt_Icc [simp]:
  fixes a :: real
  assumes "a<b" shows "x islimpt {a..b} \<longleftrightarrow> x \<in> {a..b}"
  by (metis assms closure_atLeastLessThan islimpt_Ico limpt_of_closure)

lemma connected_imp_perfect_aff_dim:
     "\<lbrakk>connected S; aff_dim S \<noteq> 0; a \<in> S\<rbrakk> \<Longrightarrow> a islimpt S"
  using aff_dim_sing connected_imp_perfect by blast

subsection\<^marker>\<open>tag unimportant\<close> \<open>On \<open>real\<close>, \<open>is_interval\<close>, \<open>convex\<close> and \<open>connected\<close> are all equivalent\<close>

lemma mem_is_interval_1_I:
  fixes a b c::real
  assumes "is_interval S"
  assumes "a \<in> S" "c \<in> S"
  assumes "a \<le> b" "b \<le> c"
  shows "b \<in> S"
  using assms is_interval_1 by blast

lemma is_interval_connected_1:
  fixes S :: "real set"
  shows "is_interval S \<longleftrightarrow> connected S"
  by (meson connected_iff_interval is_interval_1)

lemma is_interval_convex_1:
  fixes S :: "real set"
  shows "is_interval S \<longleftrightarrow> convex S"
  by (metis is_interval_convex convex_connected is_interval_connected_1)

lemma connected_compact_interval_1:
     "connected S \<and> compact S \<longleftrightarrow> (\<exists>a b. S = {a..b::real})"
  by (auto simp: is_interval_connected_1 [symmetric] is_interval_compact)

lemma connected_convex_1:
  fixes S :: "real set"
  shows "connected S \<longleftrightarrow> convex S"
  by (metis is_interval_convex convex_connected is_interval_connected_1)

lemma connected_convex_1_gen:
  fixes S :: "'a :: euclidean_space set"
  assumes "DIM('a) = 1"
  shows "connected S \<longleftrightarrow> convex S"
proof -
  obtain f:: "'a \<Rightarrow> real" where linf: "linear f" and "inj f"
    using subspace_isomorphism[OF subspace_UNIV subspace_UNIV,
        where 'a='a and 'b=real]
    unfolding Euclidean_Space.dim_UNIV
    by (auto simp: assms)
  then have "f -` (f ` S) = S"
    by (simp add: inj_vimage_image_eq)
  then show ?thesis
    by (metis connected_convex_1 convex_linear_vimage linf convex_connected connected_linear_image)
qed

lemma [simp]:
  fixes r s::real
  shows is_interval_io: "is_interval {..<r}"
    and is_interval_oi: "is_interval {r<..}"
    and is_interval_oo: "is_interval {r<..<s}"
    and is_interval_oc: "is_interval {r<..s}"
    and is_interval_co: "is_interval {r..<s}"
  by (simp_all add: is_interval_convex_1)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Another intermediate value theorem formulation\<close>

lemma ivt_increasing_component_on_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
    and "(f a)\<bullet>k \<le> y" "y \<le> (f b)\<bullet>k"
  shows "\<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
proof -
  have "f a \<in> f ` cbox a b" "f b \<in> f ` cbox a b"
    using \<open>a \<le> b\<close> by auto
  then show ?thesis
    using connected_ivt_component[of "f ` cbox a b" "f a" "f b" k y]
    by (simp add: connected_continuous_image assms)
qed

lemma ivt_increasing_component_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. continuous (at x) f \<Longrightarrow>
    f a\<bullet>k \<le> y \<Longrightarrow> y \<le> f b\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  by (rule ivt_increasing_component_on_1) (auto simp: continuous_at_imp_continuous_on)

lemma ivt_decreasing_component_on_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
    and "(f b)\<bullet>k \<le> y"
    and "y \<le> (f a)\<bullet>k"
  shows "\<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  using ivt_increasing_component_on_1[of a b "\<lambda>x. - f x" k "- y"] neg_equal_iff_equal
  using assms continuous_on_minus by force

lemma ivt_decreasing_component_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. continuous (at x) f \<Longrightarrow>
    f b\<bullet>k \<le> y \<Longrightarrow> y \<le> f a\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  by (rule ivt_decreasing_component_on_1) (auto simp: continuous_at_imp_continuous_on)


subsection\<^marker>\<open>tag unimportant\<close> \<open>A bound within an interval\<close>

lemma convex_hull_eq_real_cbox:
  fixes x y :: real assumes "x \<le> y"
  shows "convex hull {x, y} = cbox x y"
proof (rule hull_unique)
  show "{x, y} \<subseteq> cbox x y" using \<open>x \<le> y\<close> by auto
  show "convex (cbox x y)"
    by (rule convex_box)
next
  fix S assume "{x, y} \<subseteq> S" and "convex S"
  then show "cbox x y \<subseteq> S"
    unfolding is_interval_convex_1 [symmetric] is_interval_def Basis_real_def
    by - (clarify, simp (no_asm_use), fast)
qed

lemma unit_interval_convex_hull:
  "cbox (0::'a::euclidean_space) One = convex hull {x. \<forall>i\<in>Basis. (x\<bullet>i = 0) \<or> (x\<bullet>i = 1)}"
  (is "?int = convex hull ?points")
proof -
  have One[simp]: "\<And>i. i \<in> Basis \<Longrightarrow> One \<bullet> i = 1"
    by (simp add: inner_sum_left sum.If_cases inner_Basis)
  have "?int = {x. \<forall>i\<in>Basis. x \<bullet> i \<in> cbox 0 1}"
    by (auto simp: cbox_def)
  also have "\<dots> = (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` cbox 0 1)"
    by (simp only: box_eq_set_sum_Basis)
  also have "\<dots> = (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` (convex hull {0, 1}))"
    by (simp only: convex_hull_eq_real_cbox zero_le_one)
  also have "\<dots> = (\<Sum>i\<in>Basis. convex hull ((\<lambda>x. x *\<^sub>R i) ` {0, 1}))"
    by (simp add: convex_hull_linear_image)
  also have "\<dots> = convex hull (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` {0, 1})"
    by (simp only: convex_hull_set_sum)
  also have "\<dots> = convex hull {x. \<forall>i\<in>Basis. x\<bullet>i \<in> {0, 1}}"
    by (simp only: box_eq_set_sum_Basis)
  also have "convex hull {x. \<forall>i\<in>Basis. x\<bullet>i \<in> {0, 1}} = convex hull ?points"
    by simp
  finally show ?thesis .
qed

text \<open>And this is a finite set of vertices.\<close>

lemma unit_cube_convex_hull:
  obtains S :: "'a::euclidean_space set"
  where "finite S" and "cbox 0 (\<Sum>Basis) = convex hull S"
proof
  show "finite {x::'a. \<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1}"
  proof (rule finite_subset, clarify)
    show "finite ((\<lambda>S. \<Sum>i\<in>Basis. (if i \<in> S then 1 else 0) *\<^sub>R i) ` Pow Basis)"
      using finite_Basis by blast
    fix x :: 'a
    assume x: "\<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1"
    show "x \<in> (\<lambda>S. \<Sum>i\<in>Basis. (if i\<in>S then 1 else 0) *\<^sub>R i) ` Pow Basis"
      apply (rule image_eqI[where x="{i. i \<in> Basis \<and> x\<bullet>i = 1}"])
      using x
      by (subst euclidean_eq_iff, auto)
  qed
  show "cbox 0 One = convex hull {x. \<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1}"
    using unit_interval_convex_hull by blast
qed 

text \<open>Hence any cube (could do any nonempty interval).\<close>

lemma cube_convex_hull:
  assumes "d > 0"
  obtains S :: "'a::euclidean_space set" where
    "finite S" and "cbox (x - (\<Sum>i\<in>Basis. d*\<^sub>Ri)) (x + (\<Sum>i\<in>Basis. d*\<^sub>Ri)) = convex hull S"
proof -
  let ?d = "(\<Sum>i\<in>Basis. d *\<^sub>R i)::'a"
  have *: "cbox (x - ?d) (x + ?d) = (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` cbox 0 (\<Sum>Basis)"
  proof (intro set_eqI iffI)
    fix y
    assume "y \<in> cbox (x - ?d) (x + ?d)"
    then have "inverse (2 * d) *\<^sub>R (y - (x - ?d)) \<in> cbox 0 (\<Sum>Basis)"
      using assms by (simp add: mem_box inner_simps) (simp add: field_simps)
    with \<open>0 < d\<close> show "y \<in> (\<lambda>y. x - sum ((*\<^sub>R) d) Basis + (2 * d) *\<^sub>R y) ` cbox 0 One"
      by (auto intro: image_eqI[where x= "inverse (2 * d) *\<^sub>R (y - (x - ?d))"])
  next
    fix y
    assume "y \<in> (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` cbox 0 One"
    then obtain z where z: "z \<in> cbox 0 One" "y = x - ?d + (2*d) *\<^sub>R z"
      by auto
    then show "y \<in> cbox (x - ?d) (x + ?d)"
      using z assms by (auto simp: mem_box inner_simps)
  qed
  obtain S where "finite S" "cbox 0 (\<Sum>Basis::'a) = convex hull S"
    using unit_cube_convex_hull by auto
  then show ?thesis
    by (rule_tac that[of "(\<lambda>y. x - ?d + (2 * d) *\<^sub>R y)` S"]) (auto simp: convex_hull_affinity *)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Representation of any interval as a finite convex hull\<close>

lemma image_stretch_interval:
  "(\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k)) *\<^sub>R k) ` cbox a (b::'a::euclidean_space) =
  (if (cbox a b) = {} then {} else
    cbox (\<Sum>k\<in>Basis. (min (m k * (a\<bullet>k)) (m k * (b\<bullet>k))) *\<^sub>R k::'a)
     (\<Sum>k\<in>Basis. (max (m k * (a\<bullet>k)) (m k * (b\<bullet>k))) *\<^sub>R k))"
proof cases
  assume *: "cbox a b \<noteq> {}"
  show ?thesis
    unfolding box_ne_empty if_not_P[OF *]
    apply (simp add: cbox_def image_Collect set_eq_iff euclidean_eq_iff[where 'a='a] ball_conj_distrib[symmetric])
    apply (subst choice_Basis_iff[symmetric])
  proof (intro allI ball_cong refl)
    fix x i :: 'a assume "i \<in> Basis"
    with * have a_le_b: "a \<bullet> i \<le> b \<bullet> i"
      unfolding box_ne_empty by auto
    show "(\<exists>xa. x \<bullet> i = m i * xa \<and> a \<bullet> i \<le> xa \<and> xa \<le> b \<bullet> i) \<longleftrightarrow>
        min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) \<le> x \<bullet> i \<and> x \<bullet> i \<le> max (m i * (a \<bullet> i)) (m i * (b \<bullet> i))"
    proof (cases "m i = 0")
      case True
      with a_le_b show ?thesis by auto
    next
      case False
      then have *: "\<And>a b. a = m i * b \<longleftrightarrow> b = a / m i"
        by (auto simp: field_simps)
      from False have
          "min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (a \<bullet> i) else m i * (b \<bullet> i))"
          "max (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (b \<bullet> i) else m i * (a \<bullet> i))"
        using a_le_b by (auto simp: min_def max_def mult_le_cancel_left)
      with False show ?thesis using a_le_b *
        by (simp add: le_divide_eq divide_le_eq) (simp add: ac_simps)
    qed
  qed
qed simp

lemma interval_image_stretch_interval:
  "\<exists>u v. (\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k) ` cbox a (b::'a::euclidean_space) = cbox u (v::'a::euclidean_space)"
  unfolding image_stretch_interval by auto

lemma cbox_translation: "cbox (c + a) (c + b) = image (\<lambda>x. c + x) (cbox a b)"
  using image_affinity_cbox [of 1 c a b]
  using box_ne_empty [of "a+c" "b+c"]  box_ne_empty [of a b]
  by (auto simp: inner_left_distrib add.commute)

lemma cbox_image_unit_interval:
  fixes a :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
    shows "cbox a b =
           (+) a ` (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k) ` cbox 0 One"
using assms
apply (simp add: box_ne_empty image_stretch_interval cbox_translation [symmetric])
apply (simp add: min_def max_def algebra_simps sum_subtractf euclidean_representation)
done

lemma closed_interval_as_convex_hull:
  fixes a :: "'a::euclidean_space"
  obtains S where "finite S" "cbox a b = convex hull S"
proof (cases "cbox a b = {}")
  case True with convex_hull_empty that show ?thesis
    by blast
next
  case False
  obtain S::"'a set" where "finite S" and eq: "cbox 0 One = convex hull S"
    by (blast intro: unit_cube_convex_hull)
  let ?S = "((+) a ` (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k) ` S)"
  show thesis
  proof
    show "finite ?S"
      by (simp add: \<open>finite S\<close>)
    have lin: "linear (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k)"
      by (rule linear_compose_sum) (auto simp: algebra_simps linearI)
    show "cbox a b = convex hull ?S"
      using convex_hull_linear_image [OF lin] 
      by (simp add: convex_hull_translation eq cbox_image_unit_interval [OF False])
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounded convex function on open set is continuous\<close>

lemma convex_on_bounded_continuous:
  fixes S :: "('a::real_normed_vector) set"
  assumes "open S"
    and "convex_on S f"
    and "\<forall>x\<in>S. \<bar>f x\<bar> \<le> b"
  shows "continuous_on S f"
proof -
  have "\<exists>d>0. \<forall>x'. norm (x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e" if "x \<in> S" "e > 0" for x and e :: real
  proof -
    define B where "B = \<bar>b\<bar> + 1"
    then have B:  "0 < B""\<And>x. x\<in>S \<Longrightarrow> \<bar>f x\<bar> \<le> B"
      using assms(3) by auto 
    obtain k where "k > 0" and k: "cball x k \<subseteq> S"
      using \<open>x \<in> S\<close> assms(1) open_contains_cball_eq by blast
    show "\<exists>d>0. \<forall>x'. norm (x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e"
    proof (intro exI conjI allI impI)
      fix y
      assume as: "norm (y - x) < min (k / 2) (e / (2 * B) * k)"
      show "\<bar>f y - f x\<bar> < e"
      proof (cases "y = x")
        case False
        define t where "t = k / norm (y - x)"
        have "2 < t" "0<t"
          unfolding t_def using as False and \<open>k>0\<close>
          by (auto simp:field_simps)
        have "y \<in> S"
          apply (rule k[THEN subsetD])
          unfolding mem_cball dist_norm
          apply (rule order_trans[of _ "2 * norm (x - y)"])
          using as
          by (auto simp: field_simps norm_minus_commute)
        {
          define w where "w = x + t *\<^sub>R (y - x)"
          have "w \<in> S"
            using \<open>k>0\<close> by (auto simp: dist_norm t_def w_def k[THEN subsetD])
          have "(1 / t) *\<^sub>R x + - x + ((t - 1) / t) *\<^sub>R x = (1 / t - 1 + (t - 1) / t) *\<^sub>R x"
            by (auto simp: algebra_simps)
          also have "\<dots> = 0"
            using \<open>t > 0\<close> by (auto simp:field_simps)
          finally have w: "(1 / t) *\<^sub>R w + ((t - 1) / t) *\<^sub>R x = y"
            unfolding w_def using False and \<open>t > 0\<close>
            by (auto simp: algebra_simps)
          have 2: "2 * B < e * t"
            unfolding t_def using \<open>0 < e\<close> \<open>0 < k\<close> \<open>B > 0\<close> and as and False
            by (auto simp:field_simps)
          have "f y - f x \<le> (f w - f x) / t"
            using assms(2)[unfolded convex_on_def,rule_format,of w x "1/t" "(t - 1)/t", unfolded w]
            using \<open>0 < t\<close> \<open>2 < t\<close> and \<open>x \<in> S\<close> \<open>w \<in> S\<close>
            by (auto simp:field_simps)
          also have "... < e"
            using B(2)[OF \<open>w\<in>S\<close>] and B(2)[OF \<open>x\<in>S\<close>] 2 \<open>t > 0\<close> by (auto simp: field_simps)
          finally have th1: "f y - f x < e" .
        }
        moreover
        {
          define w where "w = x - t *\<^sub>R (y - x)"
          have "w \<in> S"
            using \<open>k > 0\<close> by (auto simp: dist_norm t_def w_def k[THEN subsetD])
          have "(1 / (1 + t)) *\<^sub>R x + (t / (1 + t)) *\<^sub>R x = (1 / (1 + t) + t / (1 + t)) *\<^sub>R x"
            by (auto simp: algebra_simps)
          also have "\<dots> = x"
            using \<open>t > 0\<close> by (auto simp:field_simps)
          finally have w: "(1 / (1+t)) *\<^sub>R w + (t / (1 + t)) *\<^sub>R y = x"
            unfolding w_def using False and \<open>t > 0\<close>
            by (auto simp: algebra_simps)
          have "2 * B < e * t"
            unfolding t_def
            using \<open>0 < e\<close> \<open>0 < k\<close> \<open>B > 0\<close> and as and False
            by (auto simp:field_simps)
          then have *: "(f w - f y) / t < e"
            using B(2)[OF \<open>w\<in>S\<close>] and B(2)[OF \<open>y\<in>S\<close>]
            using \<open>t > 0\<close>
            by (auto simp:field_simps)
          have "f x \<le> 1 / (1 + t) * f w + (t / (1 + t)) * f y"
            using assms(2)[unfolded convex_on_def,rule_format,of w y "1/(1+t)" "t / (1+t)",unfolded w]
            using \<open>0 < t\<close> \<open>2 < t\<close> and \<open>y \<in> S\<close> \<open>w \<in> S\<close>
            by (auto simp:field_simps)
          also have "\<dots> = (f w + t * f y) / (1 + t)"
            using \<open>t > 0\<close> by (simp add: add_divide_distrib) 
          also have "\<dots> < e + f y"
            using \<open>t > 0\<close> * \<open>e > 0\<close> by (auto simp: field_simps)
          finally have "f x - f y < e" by auto
        }
        ultimately show ?thesis by auto
      qed (use \<open>0<e\<close> in auto)
    qed (use \<open>0<e\<close> \<open>0<k\<close> \<open>0<B\<close> in \<open>auto simp: field_simps\<close>)
  qed
  then show ?thesis
    by (metis continuous_on_iff dist_norm real_norm_def)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Upper bound on a ball implies upper and lower bounds\<close>

lemma convex_bounds_lemma:
  fixes x :: "'a::real_normed_vector"
  assumes "convex_on (cball x e) f"
    and "\<forall>y \<in> cball x e. f y \<le> b" and y: "y \<in> cball x e"
  shows "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
proof (cases "0 \<le> e")
  case True
  define z where "z = 2 *\<^sub>R x - y"
  have *: "x - (2 *\<^sub>R x - y) = y - x"
    by (simp add: scaleR_2)
  have z: "z \<in> cball x e"
    using y unfolding z_def mem_cball dist_norm * by (auto simp: norm_minus_commute)
  have "(1 / 2) *\<^sub>R y + (1 / 2) *\<^sub>R z = x"
    unfolding z_def by (auto simp: algebra_simps)
  then show "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
    using assms(1)[unfolded convex_on_def,rule_format, OF y z, of "1/2" "1/2"]
    using assms(2)[rule_format,OF y] assms(2)[rule_format,OF z]
    by (auto simp:field_simps)
next
  case False
  have "dist x y < 0"
    using False y unfolding mem_cball not_le by (auto simp del: dist_not_less_zero)
  then show "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
    using zero_le_dist[of x y] by auto
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Hence a convex function on an open set is continuous\<close>

lemma real_of_nat_ge_one_iff: "1 \<le> real (n::nat) \<longleftrightarrow> 1 \<le> n"
  by auto

lemma convex_on_continuous:
  assumes "open (s::('a::euclidean_space) set)" "convex_on s f"
  shows "continuous_on s f"
  unfolding continuous_on_eq_continuous_at[OF assms(1)]
proof
  note dimge1 = DIM_positive[where 'a='a]
  fix x
  assume "x \<in> s"
  then obtain e where e: "cball x e \<subseteq> s" "e > 0"
    using assms(1) unfolding open_contains_cball by auto
  define d where "d = e / real DIM('a)"
  have "0 < d"
    unfolding d_def using \<open>e > 0\<close> dimge1 by auto
  let ?d = "(\<Sum>i\<in>Basis. d *\<^sub>R i)::'a"
  obtain c
    where c: "finite c"
    and c1: "convex hull c \<subseteq> cball x e"
    and c2: "cball x d \<subseteq> convex hull c"
  proof
    define c where "c = (\<Sum>i\<in>Basis. (\<lambda>a. a *\<^sub>R i) ` {x\<bullet>i - d, x\<bullet>i + d})"
    show "finite c"
      unfolding c_def by (simp add: finite_set_sum)
    have "\<And>i. i \<in> Basis \<Longrightarrow> convex hull {x \<bullet> i - d, x \<bullet> i + d} = cbox (x \<bullet> i - d) (x \<bullet> i + d)"
      using \<open>0 < d\<close> convex_hull_eq_real_cbox by auto
    then have 1: "convex hull c = {a. \<forall>i\<in>Basis. a \<bullet> i \<in> cbox (x \<bullet> i - d) (x \<bullet> i + d)}"
      unfolding box_eq_set_sum_Basis c_def convex_hull_set_sum 
      apply (subst convex_hull_linear_image [symmetric])
      by (force simp add: linear_iff scaleR_add_left)+
    then have 2: "convex hull c = {a. \<forall>i\<in>Basis. a \<bullet> i \<in> cball (x \<bullet> i) d}"
      by (simp add: dist_norm abs_le_iff algebra_simps)
    show "cball x d \<subseteq> convex hull c"
      unfolding 2
      by (clarsimp simp: dist_norm) (metis inner_commute inner_diff_right norm_bound_Basis_le)
    have e': "e = (\<Sum>(i::'a)\<in>Basis. d)"
      by (simp add: d_def)
    show "convex hull c \<subseteq> cball x e"
      unfolding 2
    proof clarsimp
      show "dist x y \<le> e" if "\<forall>i\<in>Basis. dist (x \<bullet> i) (y \<bullet> i) \<le> d" for y
      proof -
        have "\<And>i. i \<in> Basis \<Longrightarrow> 0 \<le> dist (x \<bullet> i) (y \<bullet> i)"
          by simp
        have "(\<Sum>i\<in>Basis. dist (x \<bullet> i) (y \<bullet> i)) \<le> e"
          using e' sum_mono that by fastforce
        then show ?thesis
          by (metis (mono_tags) euclidean_dist_l2 order_trans [OF L2_set_le_sum] zero_le_dist)
      qed
    qed
  qed
  define k where "k = Max (f ` c)"
  have "convex_on (convex hull c) f"
    using assms(2) c1 convex_on_subset e(1) by blast
  then have k: "\<forall>y\<in>convex hull c. f y \<le> k"
    using c convex_on_convex_hull_bound k_def by fastforce
  have "e \<le> e * real DIM('a)"
    using e(2) real_of_nat_ge_one_iff by auto
  then have "d \<le> e"
    by (simp add: d_def field_split_simps)
  then have dsube: "cball x d \<subseteq> cball x e"
    by (rule subset_cball)
  have conv: "convex_on (cball x d) f"
    using \<open>convex_on (convex hull c) f\<close> c2 convex_on_subset by blast
  then have "\<And>y. y\<in>cball x d \<Longrightarrow> \<bar>f y\<bar> \<le> k + 2 * \<bar>f x\<bar>"
    by (rule convex_bounds_lemma) (use c2 k in blast)
  then have "continuous_on (ball x d) f"
    by (meson Elementary_Metric_Spaces.open_ball ball_subset_cball conv convex_on_bounded_continuous 
              convex_on_subset mem_ball_imp_mem_cball)
  then show "continuous (at x) f"
    unfolding continuous_on_eq_continuous_at[OF open_ball]
    using \<open>d > 0\<close> by auto
qed

end
