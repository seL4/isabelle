(* Title:      HOL/Analysis/Starlike.thy
   Author:     L C Paulson, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
   Author:     Bogdan Grechuk, University of Edinburgh
   Author:     Armin Heller, TU Muenchen
   Author:     Johannes Hoelzl, TU Muenchen
*)
chapter \<open>Unsorted\<close>

theory Starlike
  imports
    Convex_Euclidean_Space
    Line_Segment
begin

lemma affine_hull_closed_segment [simp]:
     "affine hull (closed_segment a b) = affine hull {a,b}"
  by (simp add: segment_convex_hull)

lemma affine_hull_open_segment [simp]:
    fixes a :: "'a::euclidean_space"
    shows "affine hull (open_segment a b) = (if a = b then {} else affine hull {a,b})"
by (metis affine_hull_convex_hull affine_hull_empty closure_open_segment closure_same_affine_hull segment_convex_hull)

lemma rel_interior_closure_convex_segment:
  fixes S :: "_::euclidean_space set"
  assumes "convex S" "a \<in> rel_interior S" "b \<in> closure S"
    shows "open_segment a b \<subseteq> rel_interior S"
proof
  fix x
  have [simp]: "(1 - u) *\<^sub>R a + u *\<^sub>R b = b - (1 - u) *\<^sub>R (b - a)" for u
    by (simp add: algebra_simps)
  assume "x \<in> open_segment a b"
  then show "x \<in> rel_interior S"
    unfolding closed_segment_def open_segment_def  using assms
    by (auto intro: rel_interior_closure_convex_shrink)
qed

lemma convex_hull_insert_segments:
   "convex hull (insert a S) =
    (if S = {} then {a} else  \<Union>x \<in> convex hull S. closed_segment a x)"
  by (force simp add: convex_hull_insert_alt in_segment)

lemma Int_convex_hull_insert_rel_exterior:
  fixes z :: "'a::euclidean_space"
  assumes "convex C" "T \<subseteq> C" and z: "z \<in> rel_interior C" and dis: "disjnt S (rel_interior C)"
  shows "S \<inter> (convex hull (insert z T)) = S \<inter> (convex hull T)" (is "?lhs = ?rhs")
proof
  have "T = {} \<Longrightarrow> z \<notin> S"
    using dis z by (auto simp add: disjnt_def)
  then show "?lhs \<subseteq> ?rhs"
  proof (clarsimp simp add: convex_hull_insert_segments)
    fix x y
    assume "x \<in> S" and y: "y \<in> convex hull T" and "x \<in> closed_segment z y"
    have "y \<in> closure C"
      by (metis y \<open>convex C\<close> \<open>T \<subseteq> C\<close> closure_subset contra_subsetD convex_hull_eq hull_mono)
    moreover have "x \<notin> rel_interior C"
      by (meson \<open>x \<in> S\<close> dis disjnt_iff)
    moreover have "x \<in> open_segment z y \<union> {z, y}"
      using \<open>x \<in> closed_segment z y\<close> closed_segment_eq_open by blast
    ultimately show "x \<in> convex hull T"
      using rel_interior_closure_convex_segment [OF \<open>convex C\<close> z]
      using y z by blast
  qed
  show "?rhs \<subseteq> ?lhs"
    by (meson hull_mono inf_mono subset_insertI subset_refl)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Shrinking towards the interior of a convex set\<close>

lemma mem_interior_convex_shrink:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "c \<in> interior S"
    and "x \<in> S"
    and "0 < e"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior S"
proof -
  obtain d where "d > 0" and d: "ball c d \<subseteq> S"
    using assms(2) unfolding mem_interior by auto
  show ?thesis
    unfolding mem_interior
  proof (intro exI subsetI conjI)
    fix y
    assume "y \<in> ball (x - e *\<^sub>R (x - c)) (e*d)"
    then have as: "dist (x - e *\<^sub>R (x - c)) y < e * d"
      by simp
    have *: "y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x"
      using \<open>e > 0\<close> by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "c - ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = (1 / e) *\<^sub>R (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      using \<open>e > 0\<close>
      by (auto simp add: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
    then have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = \<bar>1/e\<bar> * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      by (simp add: dist_norm)
    also have "\<dots> = \<bar>1/e\<bar> * norm (x - e *\<^sub>R (x - c) - y)"
      by (auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d"
      using as[unfolded dist_norm] and \<open>e > 0\<close>
      by (auto simp add:pos_divide_less_eq[OF \<open>e > 0\<close>] mult.commute)
    finally have "(1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x \<in> S"
      using assms(3-5) d
      by (intro convexD_alt [OF \<open>convex S\<close>]) (auto intro: convexD_alt [OF \<open>convex S\<close>])
    with \<open>e > 0\<close> show "y \<in> S"
      by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
  qed (use \<open>e>0\<close> \<open>d>0\<close> in auto)
qed

lemma mem_interior_closure_convex_shrink:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "c \<in> interior S"
    and "x \<in> closure S"
    and "0 < e"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior S"
proof -
  obtain d where "d > 0" and d: "ball c d \<subseteq> S"
    using assms(2) unfolding mem_interior by auto
  have "\<exists>y\<in>S. norm (y - x) * (1 - e) < e * d"
  proof (cases "x \<in> S")
    case True
    then show ?thesis
      using \<open>e > 0\<close> \<open>d > 0\<close> by force
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
        using True \<open>0 < d\<close> by auto
    next
      case False
      then have "0 < e * d / (1 - e)" and *: "1 - e > 0"
        using \<open>e \<le> 1\<close> \<open>e > 0\<close> \<open>d > 0\<close> by auto
      then obtain y where "y \<in> S" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using islimpt_approachable x by blast
      then have "norm (y - x) * (1 - e) < e * d"
        by (metis "*" dist_norm mult_imp_div_pos_le not_less)
      then show ?thesis
        using \<open>y \<in> S\<close> by blast
    qed
  qed
  then obtain y where "y \<in> S" and y: "norm (y - x) * (1 - e) < e * d"
    by auto
  define z where "z = c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *: "x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)"
    unfolding z_def using \<open>e > 0\<close>
    by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have "(1 - e) * norm (x - y) / e < d"
    using y \<open>0 < e\<close> by (simp add: field_simps norm_minus_commute)
  then have "z \<in> interior (ball c d)"
    using \<open>0 < e\<close> \<open>e \<le> 1\<close> by (simp add: interior_open[OF open_ball] z_def dist_norm)
  then have "z \<in> interior S"
    using d interiorI interior_ball by blast
  then show ?thesis
    unfolding * using mem_interior_convex_shrink \<open>y \<in> S\<close> assms by blast
qed

lemma in_interior_closure_convex_segment:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and a: "a \<in> interior S" and b: "b \<in> closure S"
    shows "open_segment a b \<subseteq> interior S"
proof (clarsimp simp: in_segment)
  fix u::real
  assume u: "0 < u" "u < 1"
  have "(1 - u) *\<^sub>R a + u *\<^sub>R b = b - (1 - u) *\<^sub>R (b - a)"
    by (simp add: algebra_simps)
  also have "... \<in> interior S" using mem_interior_closure_convex_shrink [OF assms] u
    by simp
  finally show "(1 - u) *\<^sub>R a + u *\<^sub>R b \<in> interior S" .
qed

lemma convex_closure_interior:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and int: "interior S \<noteq> {}"
  shows "closure(interior S) = closure S"
proof -
  obtain a where a: "a \<in> interior S"
    using int by auto
  have "closure S \<subseteq> closure(interior S)"
  proof
    fix x
    assume x: "x \<in> closure S"
    show "x \<in> closure (interior S)"
    proof (cases "x=a")
      case True
      then show ?thesis
        using \<open>a \<in> interior S\<close> closure_subset by blast
    next
      case False
      show ?thesis
      proof (clarsimp simp add: closure_def islimpt_approachable)
        fix e::real
        assume xnotS: "x \<notin> interior S" and "0 < e"
        show "\<exists>x'\<in>interior S. x' \<noteq> x \<and> dist x' x < e"
        proof (intro bexI conjI)
          show "x - min (e/2 / norm (x - a)) 1 *\<^sub>R (x - a) \<noteq> x"
            using False \<open>0 < e\<close> by (auto simp: algebra_simps min_def)
          show "dist (x - min (e/2 / norm (x - a)) 1 *\<^sub>R (x - a)) x < e"
            using \<open>0 < e\<close> by (auto simp: dist_norm min_def)
          show "x - min (e/2 / norm (x - a)) 1 *\<^sub>R (x - a) \<in> interior S"
            using \<open>0 < e\<close> False
            by (auto simp add: min_def a intro: mem_interior_closure_convex_shrink [OF \<open>convex S\<close> a x])
        qed
      qed
    qed
  qed
  then show ?thesis
    by (simp add: closure_mono interior_subset subset_antisym)
qed

lemma closure_convex_Int_superset:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "interior S \<noteq> {}" "interior S \<subseteq> closure T"
  shows "closure(S \<inter> T) = closure S"
proof -
  have "closure S \<subseteq> closure(interior S)"
    by (simp add: convex_closure_interior assms)
  also have "... \<subseteq> closure (S \<inter> T)"
    using interior_subset [of S] assms
    by (metis (no_types, lifting) Int_assoc Int_lower2 closure_mono closure_open_Int_superset inf.orderE open_interior)
  finally show ?thesis
    by (simp add: closure_mono dual_order.antisym)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some obvious but surprisingly hard simplex lemmas\<close>

lemma simplex:
  assumes "finite S"
    and "0 \<notin> S"
  shows "convex hull (insert 0 S) = {y. \<exists>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S \<le> 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}"
proof (simp add: convex_hull_finite set_eq_iff assms, safe)
  fix x and u :: "'a \<Rightarrow> real"
  assume "0 \<le> u 0" "\<forall>x\<in>S. 0 \<le> u x" "u 0 + sum u S = 1"
  then show "\<exists>v. (\<forall>x\<in>S. 0 \<le> v x) \<and> sum v S \<le> 1 \<and> (\<Sum>x\<in>S. v x *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)"
    by force
next
  fix x and u :: "'a \<Rightarrow> real"
  assume "\<forall>x\<in>S. 0 \<le> u x" "sum u S \<le> 1"
  then show "\<exists>v. 0 \<le> v 0 \<and> (\<forall>x\<in>S. 0 \<le> v x) \<and> v 0 + sum v S = 1 \<and> (\<Sum>x\<in>S. v x *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)"
    by (rule_tac x="\<lambda>x. if x = 0 then 1 - sum u S else u x" in exI) (auto simp: sum_delta_notmem assms if_smult)
qed

lemma substd_simplex:
  assumes d: "d \<subseteq> Basis"
  shows "convex hull (insert 0 d) =
    {x. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> (\<Sum>i\<in>d. x\<bullet>i) \<le> 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)}"
  (is "convex hull (insert 0 ?p) = ?s")
proof -
  let ?D = d
  have "0 \<notin> ?p"
    using assms by (auto simp: image_def)
  from d have "finite d"
    by (blast intro: finite_subset finite_Basis)
  show ?thesis
    unfolding simplex[OF \<open>finite d\<close> \<open>0 \<notin> ?p\<close>]
  proof (intro set_eqI; safe)
    fix u :: "'a \<Rightarrow> real"
    assume as: "\<forall>x\<in>?D. 0 \<le> u x" "sum u ?D \<le> 1" 
    let ?x = "(\<Sum>x\<in>?D. u x *\<^sub>R x)"
    have ind: "\<forall>i\<in>Basis. i \<in> d \<longrightarrow> u i = ?x \<bullet> i"
      and notind: "(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> ?x \<bullet> i = 0)"
      using substdbasis_expansion_unique[OF assms] by blast+
    then have **: "sum u ?D = sum ((\<bullet>) ?x) ?D"
      using assms by (auto intro!: sum.cong)
    show "0 \<le> ?x \<bullet> i" if "i \<in> Basis" for i
      using as(1) ind notind that by fastforce
    show "sum ((\<bullet>) ?x) ?D \<le> 1"
      using "**" as(2) by linarith
    show "?x \<bullet> i = 0" if "i \<in> Basis" "i \<notin> d" for i
      using notind that by blast
  next
    fix x 
    assume "\<forall>i\<in>Basis. 0 \<le> x \<bullet> i" "sum ((\<bullet>) x) ?D \<le> 1" "(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)"
    with d show "\<exists>u. (\<forall>x\<in>?D. 0 \<le> u x) \<and> sum u ?D \<le> 1 \<and> (\<Sum>x\<in>?D. u x *\<^sub>R x) = x"
      unfolding substdbasis_expansion_unique[OF assms] 
      by (rule_tac x="inner x" in exI) auto
  qed
qed

lemma std_simplex:
  "convex hull (insert 0 Basis) =
    {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> sum (\<lambda>i. x\<bullet>i) Basis \<le> 1}"
  using substd_simplex[of Basis] by auto

lemma interior_std_simplex:
  "interior (convex hull (insert 0 Basis)) =
    {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 < x\<bullet>i) \<and> sum (\<lambda>i. x\<bullet>i) Basis < 1}"
  unfolding set_eq_iff mem_interior std_simplex
proof (intro allI iffI CollectI; clarify)
  fix x :: 'a
  fix e
  assume "e > 0" and as: "ball x e \<subseteq> {x. (\<forall>i\<in>Basis. 0 \<le> x \<bullet> i) \<and> sum ((\<bullet>) x) Basis \<le> 1}"
  show "(\<forall>i\<in>Basis. 0 < x \<bullet> i) \<and> sum ((\<bullet>) x) Basis < 1"
  proof safe
    fix i :: 'a
    assume i: "i \<in> Basis"
    then show "0 < x \<bullet> i"
      using as[THEN subsetD[where c="x - (e/2) *\<^sub>R i"]] and \<open>e > 0\<close> 
      by (force simp add: inner_simps)
  next
    have **: "dist x (x + (e/2) *\<^sub>R (SOME i. i\<in>Basis)) < e" using \<open>e > 0\<close>
      unfolding dist_norm
      by (auto intro!: mult_strict_left_mono simp: SOME_Basis)
    have "\<And>i. i \<in> Basis \<Longrightarrow> (x + (e/2) *\<^sub>R (SOME i. i\<in>Basis)) \<bullet> i =
      x\<bullet>i + (if i = (SOME i. i\<in>Basis) then e/2 else 0)"
      by (auto simp: SOME_Basis inner_Basis inner_simps)
    then have *: "sum ((\<bullet>) (x + (e/2) *\<^sub>R (SOME i. i\<in>Basis))) Basis =
      sum (\<lambda>i. x\<bullet>i + (if (SOME i. i\<in>Basis) = i then e/2 else 0)) Basis"
      by (auto simp: intro!: sum.cong)
    have "sum ((\<bullet>) x) Basis < sum ((\<bullet>) (x + (e/2) *\<^sub>R (SOME i. i\<in>Basis))) Basis"
      using \<open>e > 0\<close> DIM_positive by (auto simp: SOME_Basis sum.distrib *)
    also have "\<dots> \<le> 1"
      using ** as by force
    finally show "sum ((\<bullet>) x) Basis < 1" by auto
  qed 
next
  fix x :: 'a
  assume as: "\<forall>i\<in>Basis. 0 < x \<bullet> i" "sum ((\<bullet>) x) Basis < 1"
  obtain a :: 'b where "a \<in> UNIV" using UNIV_witness ..
  let ?d = "(1 - sum ((\<bullet>) x) Basis) / real (DIM('a))"
  show "\<exists>e>0. ball x e \<subseteq> {x. (\<forall>i\<in>Basis. 0 \<le> x \<bullet> i) \<and> sum ((\<bullet>) x) Basis \<le> 1}"
  proof (rule_tac x="min (Min (((\<bullet>) x) ` Basis)) D" for D in exI, intro conjI subsetI CollectI)
    fix y
    assume y: "y \<in> ball x (min (Min ((\<bullet>) x ` Basis)) ?d)"
    have "sum ((\<bullet>) y) Basis \<le> sum (\<lambda>i. x\<bullet>i + ?d) Basis"
    proof (rule sum_mono)
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "\<bar>y\<bullet>i - x\<bullet>i\<bar> \<le> norm (y - x)"
        by (metis Basis_le_norm i inner_commute inner_diff_right)
      also have "... < ?d"
        using y by (simp add: dist_norm norm_minus_commute)
      finally have "\<bar>y\<bullet>i - x\<bullet>i\<bar> < ?d" .
      then show "y \<bullet> i \<le> x \<bullet> i + ?d" by auto
    qed
    also have "\<dots> \<le> 1"
      unfolding sum.distrib sum_constant
      by (auto simp add: Suc_le_eq)
    finally show "sum ((\<bullet>) y) Basis \<le> 1" .
    show "(\<forall>i\<in>Basis. 0 \<le> y \<bullet> i)"
    proof safe
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "norm (x - y) < Min (((\<bullet>) x) ` Basis)"
        using y by (auto simp: dist_norm less_eq_real_def)
      also have "... \<le> x\<bullet>i"
        using i by auto
      finally have "norm (x - y) < x\<bullet>i" .
      then show "0 \<le> y\<bullet>i"
        using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format, OF i]
        by (auto simp: inner_simps)
    qed
  next
    have "Min (((\<bullet>) x) ` Basis) > 0"
      using as by simp
    moreover have "?d > 0"
      using as by (auto simp: Suc_le_eq)
    ultimately show "0 < min (Min ((\<bullet>) x ` Basis)) ((1 - sum ((\<bullet>) x) Basis) / real DIM('a))"
      by linarith
  qed 
qed

lemma interior_std_simplex_nonempty:
  obtains a :: "'a::euclidean_space" where
    "a \<in> interior(convex hull (insert 0 Basis))"
proof -
  let ?D = "Basis :: 'a set"
  let ?a = "sum (\<lambda>b::'a. inverse (2 * real DIM('a)) *\<^sub>R b) Basis"
  {
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "?a \<bullet> i = inverse (2 * real DIM('a))"
      by (rule trans[of _ "sum (\<lambda>j. if i = j then inverse (2 * real DIM('a)) else 0) ?D"])
         (simp_all add: sum.If_cases i) }
  note ** = this
  show ?thesis
  proof
    show "?a \<in> interior(convex hull (insert 0 Basis))"
      unfolding interior_std_simplex mem_Collect_eq
    proof safe
      fix i :: 'a
      assume i: "i \<in> Basis"
      show "0 < ?a \<bullet> i"
        unfolding **[OF i] by (auto simp add: Suc_le_eq)
    next
      have "sum ((\<bullet>) ?a) ?D = sum (\<lambda>i. inverse (2 * real DIM('a))) ?D"
        by (auto intro: sum.cong)
      also have "\<dots> < 1"
        unfolding sum_constant divide_inverse[symmetric]
        by (auto simp add: field_simps)
      finally show "sum ((\<bullet>) ?a) ?D < 1" by auto
    qed
  qed
qed

lemma rel_interior_substd_simplex:
  assumes D: "D \<subseteq> Basis"
  shows "rel_interior (convex hull (insert 0 D)) =
         {x::'a::euclidean_space. (\<forall>i\<in>D. 0 < x\<bullet>i) \<and> (\<Sum>i\<in>D. x\<bullet>i) < 1 \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)}"
     (is "_ = ?s")
proof -
  have "finite D"
    using D finite_Basis finite_subset by blast
  show ?thesis
  proof (cases "D = {}")
    case True
    then show ?thesis
      using rel_interior_sing using euclidean_eq_iff[of _ 0] by auto
  next
    case False
    have h0: "affine hull (convex hull (insert 0 D)) =
              {x::'a::euclidean_space. (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)}"
      using affine_hull_convex_hull affine_hull_substd_basis assms by auto
    have aux: "\<And>x::'a. \<forall>i\<in>Basis. (\<forall>i\<in>D. 0 \<le> x\<bullet>i) \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0) \<longrightarrow> 0 \<le> x\<bullet>i"
      by auto
    {
      fix x :: "'a::euclidean_space"
      assume x: "x \<in> rel_interior (convex hull (insert 0 D))"
      then obtain e where "e > 0" and
        "ball x e \<inter> {xa. (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> xa\<bullet>i = 0)} \<subseteq> convex hull (insert 0 D)"
        using mem_rel_interior_ball[of x "convex hull (insert 0 D)"] h0 by auto
      then have as: "\<And>y. \<lbrakk>dist x y < e \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> y\<bullet>i = 0)\<rbrakk> \<Longrightarrow>
                            (\<forall>i\<in>D. 0 \<le> y \<bullet> i) \<and> sum ((\<bullet>) y) D \<le> 1"
        using assms by (force simp: substd_simplex)
      have x0: "(\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)"
        using x rel_interior_subset  substd_simplex[OF assms] by auto
      have "(\<forall>i\<in>D. 0 < x \<bullet> i) \<and> sum ((\<bullet>) x) D < 1 \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)"
      proof (intro conjI ballI)
        fix i :: 'a
        assume "i \<in> D"
        then have "\<forall>j\<in>D. 0 \<le> (x - (e/2) *\<^sub>R i) \<bullet> j"
          using D \<open>e > 0\<close> x0
          by (intro as[THEN conjunct1]) (force simp: dist_norm inner_simps inner_Basis)
        then show "0 < x \<bullet> i"
          using \<open>e > 0\<close> \<open>i \<in> D\<close> D  by (force simp: inner_simps inner_Basis)
      next
        obtain a where a: "a \<in> D"
          using \<open>D \<noteq> {}\<close> by auto
        then have **: "dist x (x + (e/2) *\<^sub>R a) < e"
          using \<open>e > 0\<close> norm_Basis[of a] D by (auto simp: dist_norm)
        have "\<And>i. i \<in> Basis \<Longrightarrow> (x + (e/2) *\<^sub>R a) \<bullet> i = x\<bullet>i + (if i = a then e/2 else 0)"
          using a D by (auto simp: inner_simps inner_Basis)
        then have *: "sum ((\<bullet>) (x + (e/2) *\<^sub>R a)) D = sum (\<lambda>i. x\<bullet>i + (if a = i then e/2 else 0)) D"
          using D by (intro sum.cong) auto
        have "a \<in> Basis"
          using \<open>a \<in> D\<close> D by auto
        then have h1: "(\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> (x + (e/2) *\<^sub>R a) \<bullet> i = 0)"
          using x0 D \<open>a\<in>D\<close> by (auto simp add: inner_add_left inner_Basis)
        have "sum ((\<bullet>) x) D < sum ((\<bullet>) (x + (e/2) *\<^sub>R a)) D"
          using \<open>e > 0\<close> \<open>a \<in> D\<close> \<open>finite D\<close> by (auto simp add: * sum.distrib)
        also have "\<dots> \<le> 1"
          using ** h1 as[rule_format, of "x + (e/2) *\<^sub>R a"]
          by auto
        finally show "sum ((\<bullet>) x) D < 1" "\<And>i. i\<in>Basis \<Longrightarrow> i \<notin> D \<longrightarrow> x\<bullet>i = 0"
          using x0 by auto
      qed
    }
    moreover
    {
      fix x :: "'a::euclidean_space"
      assume as: "x \<in> ?s"
      have "\<forall>i. 0 < x\<bullet>i \<or> 0 = x\<bullet>i \<longrightarrow> 0 \<le> x\<bullet>i"
        by auto
      moreover have "\<forall>i. i \<in> D \<or> i \<notin> D" by auto
      ultimately
      have "\<forall>i. (\<forall>i\<in>D. 0 < x\<bullet>i) \<and> (\<forall>i. i \<notin> D \<longrightarrow> x\<bullet>i = 0) \<longrightarrow> 0 \<le> x\<bullet>i"
        by metis
      then have h2: "x \<in> convex hull (insert 0 D)"
        using as assms by (force simp add: substd_simplex)
      obtain a where a: "a \<in> D"
        using \<open>D \<noteq> {}\<close> by auto
      define d where "d \<equiv> (1 - sum ((\<bullet>) x) D) / real (card D)"
      have "\<exists>e>0. ball x e \<inter> {x. \<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x \<bullet> i = 0} \<subseteq> convex hull insert 0 D"
        unfolding substd_simplex[OF assms]
      proof (intro exI; safe)
        have "0 < card D" using \<open>D \<noteq> {}\<close> \<open>finite D\<close>
          by (simp add: card_gt_0_iff)
        have "Min (((\<bullet>) x) ` D) > 0"
          using as \<open>D \<noteq> {}\<close> \<open>finite D\<close> by (simp)
        moreover have "d > 0" 
          using as \<open>0 < card D\<close> by (auto simp: d_def)
        ultimately show "min (Min (((\<bullet>) x) ` D)) d > 0"
          by auto
        fix y :: 'a
        assume y2: "\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> y\<bullet>i = 0"
        assume "y \<in> ball x (min (Min ((\<bullet>) x ` D)) d)"
        then have y: "dist x y < min (Min ((\<bullet>) x ` D)) d"
          by auto
        have "sum ((\<bullet>) y) D \<le> sum (\<lambda>i. x\<bullet>i + d) D"
        proof (rule sum_mono)
          fix i
          assume "i \<in> D"
          with D have i: "i \<in> Basis"
            by auto
          have "\<bar>y\<bullet>i - x\<bullet>i\<bar> \<le> norm (y - x)"
            by (metis i inner_commute inner_diff_right norm_bound_Basis_le order_refl)
          also have "... < d"
            by (metis dist_norm min_less_iff_conj norm_minus_commute y)
          finally have "\<bar>y\<bullet>i - x\<bullet>i\<bar> < d" .
          then show "y \<bullet> i \<le> x \<bullet> i + d" by auto
        qed
        also have "\<dots> \<le> 1"
          unfolding sum.distrib sum_constant d_def using \<open>0 < card D\<close>
          by auto
        finally show "sum ((\<bullet>) y) D \<le> 1" .

        fix i :: 'a
        assume i: "i \<in> Basis"
        then show "0 \<le> y\<bullet>i"
        proof (cases "i\<in>D")
          case True
          have "norm (x - y) < x\<bullet>i"
            using y Min_gr_iff[of "(\<bullet>) x ` D" "norm (x - y)"] \<open>0 < card D\<close> \<open>i \<in> D\<close>
            by (simp add: dist_norm card_gt_0_iff)
          then show "0 \<le> y\<bullet>i"
            using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format]
            by (auto simp: inner_simps)
        qed (use y2 in auto)
      qed
      then have "x \<in> rel_interior (convex hull (insert 0 D))"
        using h0 h2 rel_interior_ball by force
    }
    ultimately have
      "\<And>x. x \<in> rel_interior (convex hull insert 0 D) \<longleftrightarrow>
        x \<in> {x. (\<forall>i\<in>D. 0 < x \<bullet> i) \<and> sum ((\<bullet>) x) D < 1 \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x \<bullet> i = 0)}"
      by blast
    then show ?thesis by (rule set_eqI)
  qed
qed

lemma rel_interior_substd_simplex_nonempty:
  assumes "D \<noteq> {}"
    and "D \<subseteq> Basis"
  obtains a :: "'a::euclidean_space"
    where "a \<in> rel_interior (convex hull (insert 0 D))"
proof -
  let ?a = "sum (\<lambda>b::'a::euclidean_space. inverse (2 * real (card D)) *\<^sub>R b) D"
  have "finite D"
    using assms finite_Basis infinite_super by blast
  then have d1: "0 < real (card D)"
    using \<open>D \<noteq> {}\<close> by auto
  {
    fix i
    assume "i \<in> D"
    have "?a \<bullet> i = sum (\<lambda>j. if i = j then inverse (2 * real (card D)) else 0) D"
      unfolding inner_sum_left
      using \<open>i \<in> D\<close> by (auto simp: inner_Basis subsetD[OF assms(2)] intro: sum.cong)
    also have "... = inverse (2 * real (card D))"
      using \<open>i \<in> D\<close> \<open>finite D\<close> by auto
    finally have "?a \<bullet> i = inverse (2 * real (card D))" .
  }
  note ** = this
  show ?thesis
  proof
    show "?a \<in> rel_interior (convex hull (insert 0 D))"
      unfolding rel_interior_substd_simplex[OF assms(2)] 
    proof safe
      fix i
      assume "i \<in> D"
      have "0 < inverse (2 * real (card D))"
        using d1 by auto
      also have "\<dots> = ?a \<bullet> i" using **[of i] \<open>i \<in> D\<close>
        by auto
      finally show "0 < ?a \<bullet> i" by auto
    next
      have "sum ((\<bullet>) ?a) D = sum (\<lambda>i. inverse (2 * real (card D))) D"
        by (rule sum.cong) (rule refl, rule **)
      also have "\<dots> < 1"
        unfolding sum_constant divide_real_def[symmetric]
        by (auto simp add: field_simps)
      finally show "sum ((\<bullet>) ?a) D < 1" by auto
    next
      fix i
      assume "i \<in> Basis" and "i \<notin> D"
      have "?a \<in> span D"
      proof (rule span_sum[of D "(\<lambda>b. b /\<^sub>R (2 * real (card D)))" D])
        {
          fix x :: "'a::euclidean_space"
          assume "x \<in> D"
          then have "x \<in> span D"
            using span_base[of _ "D"] by auto
          then have "x /\<^sub>R (2 * real (card D)) \<in> span D"
            using span_mul[of x "D" "(inverse (real (card D)) / 2)"] by auto
        }
        then show "\<And>x. x\<in>D \<Longrightarrow> x /\<^sub>R (2 * real (card D)) \<in> span D"
          by auto
      qed
      then show "?a \<bullet> i = 0 "
        using \<open>i \<notin> D\<close> unfolding span_substd_basis[OF assms(2)] using \<open>i \<in> Basis\<close> by auto
    qed
  qed
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Relative interior of convex set\<close>

lemma rel_interior_convex_nonempty_aux:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "0 \<in> S"
  shows "rel_interior S \<noteq> {}"
proof (cases "S = {0}")
  case True
  then show ?thesis using rel_interior_sing by auto
next
  case False
  obtain B where B: "independent B \<and> B \<le> S \<and> S \<le> span B \<and> card B = dim S"
    using basis_exists[of S] by metis
  then have "B \<noteq> {}"
    using B assms \<open>S \<noteq> {0}\<close> span_empty by auto
  have "insert 0 B \<le> span B"
    using subspace_span[of B] subspace_0[of "span B"]
      span_superset by auto
  then have "span (insert 0 B) \<le> span B"
    using span_span[of B] span_mono[of "insert 0 B" "span B"] by blast
  then have "convex hull insert 0 B \<le> span B"
    using convex_hull_subset_span[of "insert 0 B"] by auto
  then have "span (convex hull insert 0 B) \<le> span B"
    using span_span[of B]
      span_mono[of "convex hull insert 0 B" "span B"] by blast
  then have *: "span (convex hull insert 0 B) = span B"
    using span_mono[of B "convex hull insert 0 B"] hull_subset[of "insert 0 B"] by auto
  then have "span (convex hull insert 0 B) = span S"
    using B span_mono[of B S] span_mono[of S "span B"]
      span_span[of B] by auto
  moreover have "0 \<in> affine hull (convex hull insert 0 B)"
    using hull_subset[of "convex hull insert 0 B"] hull_subset[of "insert 0 B"] by auto
  ultimately have **: "affine hull (convex hull insert 0 B) = affine hull S"
    using affine_hull_span_0[of "convex hull insert 0 B"] affine_hull_span_0[of "S"]
      assms hull_subset[of S]
    by auto
  obtain d and f :: "'n \<Rightarrow> 'n" where
    fd: "card d = card B" "linear f" "f ` B = d"
      "f ` span B = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = (0::real)} \<and> inj_on f (span B)"
    and d: "d \<subseteq> Basis"
    using basis_to_substdbasis_subspace_isomorphism[of B,OF _ ] B by auto
  then have "bounded_linear f"
    using linear_conv_bounded_linear by auto
  have "d \<noteq> {}"
    using fd B \<open>B \<noteq> {}\<close> by auto
  have "insert 0 d = f ` (insert 0 B)"
    using fd linear_0 by auto
  then have "(convex hull (insert 0 d)) = f ` (convex hull (insert 0 B))"
    using convex_hull_linear_image[of f "(insert 0 d)"]
      convex_hull_linear_image[of f "(insert 0 B)"] \<open>linear f\<close>
    by auto
  moreover have "rel_interior (f ` (convex hull insert 0 B)) = f ` rel_interior (convex hull insert 0 B)"
  proof (rule rel_interior_injective_on_span_linear_image[OF \<open>bounded_linear f\<close>])
    show "inj_on f (span (convex hull insert 0 B))"
      using fd * by auto
  qed
  ultimately have "rel_interior (convex hull insert 0 B) \<noteq> {}"
    using rel_interior_substd_simplex_nonempty[OF \<open>d \<noteq> {}\<close> d] by fastforce
  moreover have "convex hull (insert 0 B) \<subseteq> S"
    using B assms hull_mono[of "insert 0 B" "S" "convex"] convex_hull_eq by auto
  ultimately show ?thesis
    using subset_rel_interior[of "convex hull insert 0 B" S] ** by auto
qed

lemma rel_interior_eq_empty:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_interior S = {} \<longleftrightarrow> S = {}"
proof -
  {
    assume "S \<noteq> {}"
    then obtain a where "a \<in> S" by auto
    then have "0 \<in> (+) (-a) ` S"
      using assms exI[of "(\<lambda>x. x \<in> S \<and> - a + x = 0)" a] by auto
    then have "rel_interior ((+) (-a) ` S) \<noteq> {}"
      using rel_interior_convex_nonempty_aux[of "(+) (-a) ` S"]
        convex_translation[of S "-a"] assms
      by auto
    then have "rel_interior S \<noteq> {}"
      using rel_interior_translation [of "- a"] by simp
  }
  then show ?thesis by auto
qed

lemma interior_simplex_nonempty:
  fixes S :: "'N :: euclidean_space set"
  assumes "independent S" "finite S" "card S = DIM('N)"
  obtains a where "a \<in> interior (convex hull (insert 0 S))"
proof -
  have "affine hull (insert 0 S) = UNIV"
    by (simp add: hull_inc affine_hull_span_0 dim_eq_full[symmetric]
         assms(1) assms(3) dim_eq_card_independent)
  moreover have "rel_interior (convex hull insert 0 S) \<noteq> {}"
    using rel_interior_eq_empty [of "convex hull (insert 0 S)"] by auto
  ultimately have "interior (convex hull insert 0 S) \<noteq> {}"
    by (simp add: rel_interior_interior)
  with that show ?thesis
    by auto
qed

lemma convex_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "convex (rel_interior S)"
proof -
  {
    fix x y and u :: real
    assume assm: "x \<in> rel_interior S" "y \<in> rel_interior S" "0 \<le> u" "u \<le> 1"
    then have "x \<in> S"
      using rel_interior_subset by auto
    have "x - u *\<^sub>R (x-y) \<in> rel_interior S"
    proof (cases "0 = u")
      case False
      then have "0 < u" using assm by auto
      then show ?thesis
        using assm rel_interior_convex_shrink[of S y x u] assms \<open>x \<in> S\<close> by auto
    next
      case True
      then show ?thesis using assm by auto
    qed
    then have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> rel_interior S"
      by (simp add: algebra_simps)
  }
  then show ?thesis
    unfolding convex_alt by auto
qed

lemma convex_closure_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "closure (rel_interior S) = closure S"
proof -
  have h1: "closure (rel_interior S) \<le> closure S"
    using closure_mono[of "rel_interior S" S] rel_interior_subset[of S] by auto
  show ?thesis
  proof (cases "S = {}")
    case False
    then obtain a where a: "a \<in> rel_interior S"
      using rel_interior_eq_empty assms by auto
    { fix x
      assume x: "x \<in> closure S"
      {
        assume "x = a"
        then have "x \<in> closure (rel_interior S)"
          using a unfolding closure_def by auto
      }
      moreover
      {
        assume "x \<noteq> a"
         {
           fix e :: real
           assume "e > 0"
           define e1 where "e1 = min 1 (e/norm (x - a))"
           then have e1: "e1 > 0" "e1 \<le> 1" "e1 * norm (x - a) \<le> e"
             using \<open>x \<noteq> a\<close> \<open>e > 0\<close> le_divide_eq[of e1 e "norm (x - a)"]
             by simp_all
           then have *: "x - e1 *\<^sub>R (x - a) \<in> rel_interior S"
             using rel_interior_closure_convex_shrink[of S a x e1] assms x a e1_def
             by auto
           have "\<exists>y. y \<in> rel_interior S \<and> y \<noteq> x \<and> dist y x \<le> e"
             using "*" \<open>x \<noteq> a\<close> e1 by force
        }
        then have "x islimpt rel_interior S"
          unfolding islimpt_approachable_le by auto
        then have "x \<in> closure(rel_interior S)"
          unfolding closure_def by auto
      }
      ultimately have "x \<in> closure(rel_interior S)" by auto
    }
    then show ?thesis using h1 by auto
  qed auto
qed

lemma rel_interior_same_affine_hull:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "affine hull (rel_interior S) = affine hull S"
  by (metis assms closure_same_affine_hull convex_closure_rel_interior)

lemma rel_interior_aff_dim:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "aff_dim (rel_interior S) = aff_dim S"
  by (metis aff_dim_affine_hull2 assms rel_interior_same_affine_hull)

lemma rel_interior_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_interior (rel_interior S) = rel_interior S"
proof -
  have "openin (top_of_set (affine hull (rel_interior S))) (rel_interior S)"
    using openin_rel_interior[of S] rel_interior_same_affine_hull[of S] assms by auto
  then show ?thesis
    using rel_interior_def by auto
qed

lemma rel_interior_rel_open:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_open (rel_interior S)"
  unfolding rel_open_def using rel_interior_rel_interior assms by auto

lemma convex_rel_interior_closure_aux:
  fixes x y z :: "'n::euclidean_space"
  assumes "0 < a" "0 < b" "(a + b) *\<^sub>R z = a *\<^sub>R x + b *\<^sub>R y"
  obtains e where "0 < e" "e < 1" "z = y - e *\<^sub>R (y - x)"
proof -
  define e where "e = a / (a + b)"
  have "z = (1 / (a + b)) *\<^sub>R ((a + b) *\<^sub>R z)"
    using assms  by (simp add: eq_vector_fraction_iff)
  also have "\<dots> = (1 / (a + b)) *\<^sub>R (a *\<^sub>R x + b *\<^sub>R y)"
    using assms scaleR_cancel_left[of "1/(a+b)" "(a + b) *\<^sub>R z" "a *\<^sub>R x + b *\<^sub>R y"]
    by auto
  also have "\<dots> = y - e *\<^sub>R (y-x)"
    using e_def assms
    by (simp add: divide_simps vector_fraction_eq_iff) (simp add: algebra_simps)
  finally have "z = y - e *\<^sub>R (y-x)"
    by auto
  moreover have "e > 0" "e < 1" using e_def assms by auto
  ultimately show ?thesis using that[of e] by auto
qed

lemma convex_rel_interior_closure:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_interior (closure S) = rel_interior S"
proof (cases "S = {}")
  case True
  then show ?thesis
    using assms rel_interior_eq_empty by auto
next
  case False
  have "rel_interior (closure S) \<supseteq> rel_interior S"
    using subset_rel_interior[of S "closure S"] closure_same_affine_hull closure_subset
    by auto
  moreover
  {
    fix z
    assume z: "z \<in> rel_interior (closure S)"
    obtain x where x: "x \<in> rel_interior S"
      using \<open>S \<noteq> {}\<close> assms rel_interior_eq_empty by auto
    have "z \<in> rel_interior S"
    proof (cases "x = z")
      case True
      then show ?thesis using x by auto
    next
      case False
      obtain e where e: "e > 0" "cball z e \<inter> affine hull closure S \<le> closure S"
        using z rel_interior_cball[of "closure S"] by auto
      hence *: "0 < e/norm(z-x)" using e False by auto
      define y where "y = z + (e/norm(z-x)) *\<^sub>R (z-x)"
      have yball: "y \<in> cball z e"
        using y_def dist_norm[of z y] e by auto
      have "x \<in> affine hull closure S"
        using x rel_interior_subset_closure hull_inc[of x "closure S"] by blast
      moreover have "z \<in> affine hull closure S"
        using z rel_interior_subset hull_subset[of "closure S"] by blast
      ultimately have "y \<in> affine hull closure S"
        using y_def affine_affine_hull[of "closure S"]
          mem_affine_3_minus [of "affine hull closure S" z z x "e/norm(z-x)"] by auto
      then have "y \<in> closure S" using e yball by auto
      have "(1 + (e/norm(z-x))) *\<^sub>R z = (e/norm(z-x)) *\<^sub>R x + y"
        using y_def by (simp add: algebra_simps)
      then obtain e1 where "0 < e1" "e1 < 1" "z = y - e1 *\<^sub>R (y - x)"
        using * convex_rel_interior_closure_aux[of "e / norm (z - x)" 1 z x y]
        by (auto simp add: algebra_simps)
      then show ?thesis
        using rel_interior_closure_convex_shrink assms x \<open>y \<in> closure S\<close>
        by fastforce
    qed
  }
  ultimately show ?thesis by auto
qed

lemma convex_interior_closure:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "interior (closure S) = interior S"
  using closure_aff_dim[of S] interior_rel_interior_gen[of S]
    interior_rel_interior_gen[of "closure S"]
    convex_rel_interior_closure[of S] assms
  by auto

lemma closure_eq_rel_interior_eq:
  fixes S1 S2 :: "'n::euclidean_space set"
  assumes "convex S1"
    and "convex S2"
  shows "closure S1 = closure S2 \<longleftrightarrow> rel_interior S1 = rel_interior S2"
  by (metis convex_rel_interior_closure convex_closure_rel_interior assms)

lemma closure_eq_between:
  fixes S1 S2 :: "'n::euclidean_space set"
  assumes "convex S1"
    and "convex S2"
  shows "closure S1 = closure S2 \<longleftrightarrow> rel_interior S1 \<le> S2 \<and> S2 \<subseteq> closure S1"
  (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
    by (metis assms closure_subset convex_rel_interior_closure rel_interior_subset)
next
  assume ?B
  then have "closure S1 \<subseteq> closure S2"
    by (metis assms(1) convex_closure_rel_interior closure_mono)
  moreover from \<open>?B\<close> have "closure S1 \<supseteq> closure S2"
    by (metis closed_closure closure_minimal)
  ultimately show ?A ..
qed

lemma open_inter_closure_rel_interior:
  fixes S A :: "'n::euclidean_space set"
  assumes "convex S"
    and "open A"
  shows "A \<inter> closure S = {} \<longleftrightarrow> A \<inter> rel_interior S = {}"
  by (metis assms convex_closure_rel_interior open_Int_closure_eq_empty)

lemma rel_interior_open_segment:
  fixes a :: "'a :: euclidean_space"
  shows "rel_interior(open_segment a b) = open_segment a b"
proof (cases "a = b")
  case True then show ?thesis by auto
next
  case False then
  have "open_segment a b = affine hull {a, b} \<inter> ball ((a + b) /\<^sub>R 2) (norm (b - a) / 2)"
    by (simp add: open_segment_as_ball)
  then show ?thesis
    unfolding rel_interior_eq openin_open
    by (metis Elementary_Metric_Spaces.open_ball False affine_hull_open_segment)
qed

lemma rel_interior_closed_segment:
  fixes a :: "'a :: euclidean_space"
  shows "rel_interior(closed_segment a b) =
         (if a = b then {a} else open_segment a b)"
proof (cases "a = b")
  case True then show ?thesis by auto
next
  case False then show ?thesis
    by simp
       (metis closure_open_segment convex_open_segment convex_rel_interior_closure
              rel_interior_open_segment)
qed

lemmas rel_interior_segment = rel_interior_closed_segment rel_interior_open_segment

subsection\<open>The relative frontier of a set\<close>

definition\<^marker>\<open>tag important\<close> "rel_frontier S = closure S - rel_interior S"

lemma rel_frontier_empty [simp]: "rel_frontier {} = {}"
  by (simp add: rel_frontier_def)

lemma rel_frontier_eq_empty:
    fixes S :: "'n::euclidean_space set"
    shows "rel_frontier S = {} \<longleftrightarrow> affine S"
  unfolding rel_frontier_def
  using rel_interior_subset_closure  by (auto simp add: rel_interior_eq_closure [symmetric])

lemma rel_frontier_sing [simp]:
    fixes a :: "'n::euclidean_space"
    shows "rel_frontier {a} = {}"
  by (simp add: rel_frontier_def)

lemma rel_frontier_affine_hull:
  fixes S :: "'a::euclidean_space set"
  shows "rel_frontier S \<subseteq> affine hull S"
using closure_affine_hull rel_frontier_def by fastforce

lemma rel_frontier_cball [simp]:
    fixes a :: "'n::euclidean_space"
    shows "rel_frontier(cball a r) = (if r = 0 then {} else sphere a r)"
proof (cases rule: linorder_cases [of r 0])
  case less then show ?thesis
    by (force simp: sphere_def)
next
  case equal then show ?thesis by simp
next
  case greater then show ?thesis
    by simp (metis centre_in_ball empty_iff frontier_cball frontier_def interior_cball interior_rel_interior_gen rel_frontier_def)
qed

lemma rel_frontier_translation:
  fixes a :: "'a::euclidean_space"
  shows "rel_frontier((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (rel_frontier S)"
  by (simp add: rel_frontier_def translation_diff rel_interior_translation closure_translation)

lemma rel_frontier_nonempty_interior:
  fixes S :: "'n::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> rel_frontier S = frontier S"
  by (metis frontier_def interior_rel_interior_gen rel_frontier_def)

lemma rel_frontier_frontier:
  fixes S :: "'n::euclidean_space set"
  shows "affine hull S = UNIV \<Longrightarrow> rel_frontier S = frontier S"
  by (simp add: frontier_def rel_frontier_def rel_interior_interior)

lemma closest_point_in_rel_frontier:
   "\<lbrakk>closed S; S \<noteq> {}; x \<in> affine hull S - rel_interior S\<rbrakk>
   \<Longrightarrow> closest_point S x \<in> rel_frontier S"
  by (simp add: closest_point_in_rel_interior closest_point_in_set rel_frontier_def)

lemma closed_rel_frontier [iff]:
  fixes S :: "'n::euclidean_space set"
  shows "closed (rel_frontier S)"
proof -
  have *: "closedin (top_of_set (affine hull S)) (closure S - rel_interior S)"
    by (simp add: closed_subset closedin_diff closure_affine_hull openin_rel_interior)
  show ?thesis
  proof (rule closedin_closed_trans[of "affine hull S" "rel_frontier S"])
    show "closedin (top_of_set (affine hull S)) (rel_frontier S)"
      by (simp add: "*" rel_frontier_def)
  qed simp
qed

lemma closed_rel_boundary:
  fixes S :: "'n::euclidean_space set"
  shows "closed S \<Longrightarrow> closed(S - rel_interior S)"
  by (metis closed_rel_frontier closure_closed rel_frontier_def)

lemma compact_rel_boundary:
  fixes S :: "'n::euclidean_space set"
  shows "compact S \<Longrightarrow> compact(S - rel_interior S)"
  by (metis bounded_diff closed_rel_boundary closure_eq compact_closure compact_imp_closed)

lemma bounded_rel_frontier:
  fixes S :: "'n::euclidean_space set"
  shows "bounded S \<Longrightarrow> bounded(rel_frontier S)"
by (simp add: bounded_closure bounded_diff rel_frontier_def)

lemma compact_rel_frontier_bounded:
  fixes S :: "'n::euclidean_space set"
  shows "bounded S \<Longrightarrow> compact(rel_frontier S)"
using bounded_rel_frontier closed_rel_frontier compact_eq_bounded_closed by blast

lemma compact_rel_frontier:
  fixes S :: "'n::euclidean_space set"
  shows "compact S \<Longrightarrow> compact(rel_frontier S)"
by (meson compact_eq_bounded_closed compact_rel_frontier_bounded)

lemma convex_same_rel_interior_closure:
  fixes S :: "'n::euclidean_space set"
  shows "\<lbrakk>convex S; convex T\<rbrakk>
         \<Longrightarrow> rel_interior S = rel_interior T \<longleftrightarrow> closure S = closure T"
by (simp add: closure_eq_rel_interior_eq)

lemma convex_same_rel_interior_closure_straddle:
  fixes S :: "'n::euclidean_space set"
  shows "\<lbrakk>convex S; convex T\<rbrakk>
         \<Longrightarrow> rel_interior S = rel_interior T \<longleftrightarrow>
             rel_interior S \<subseteq> T \<and> T \<subseteq> closure S"
by (simp add: closure_eq_between convex_same_rel_interior_closure)

lemma convex_rel_frontier_aff_dim:
  fixes S1 S2 :: "'n::euclidean_space set"
  assumes "convex S1"
    and "convex S2"
    and "S2 \<noteq> {}"
    and "S1 \<le> rel_frontier S2"
  shows "aff_dim S1 < aff_dim S2"
proof -
  have "S1 \<subseteq> closure S2"
    using assms unfolding rel_frontier_def by auto
  then have *: "affine hull S1 \<subseteq> affine hull S2"
    using hull_mono[of "S1" "closure S2"] closure_same_affine_hull[of S2] by blast
  then have "aff_dim S1 \<le> aff_dim S2"
    using * aff_dim_affine_hull[of S1] aff_dim_affine_hull[of S2]
      aff_dim_subset[of "affine hull S1" "affine hull S2"]
    by auto
  moreover
  {
    assume eq: "aff_dim S1 = aff_dim S2"
    then have "S1 \<noteq> {}"
      using aff_dim_empty[of S1] aff_dim_empty[of S2] \<open>S2 \<noteq> {}\<close> by auto
    have **: "affine hull S1 = affine hull S2"
      by (simp_all add: * eq \<open>S1 \<noteq> {}\<close> affine_dim_equal)
    obtain a where a: "a \<in> rel_interior S1"
      using \<open>S1 \<noteq> {}\<close> rel_interior_eq_empty assms by auto
    obtain T where T: "open T" "a \<in> T \<inter> S1" "T \<inter> affine hull S1 \<subseteq> S1"
       using mem_rel_interior[of a S1] a by auto
    then have "a \<in> T \<inter> closure S2"
      using a assms unfolding rel_frontier_def by auto
    then obtain b where b: "b \<in> T \<inter> rel_interior S2"
      using open_inter_closure_rel_interior[of S2 T] assms T by auto
    then have "b \<in> affine hull S1"
      using rel_interior_subset hull_subset[of S2] ** by auto
    then have "b \<in> S1"
      using T b by auto
    then have False
      using b assms unfolding rel_frontier_def by auto
  }
  ultimately show ?thesis
    using less_le by auto
qed

lemma convex_rel_interior_if:
  fixes S ::  "'n::euclidean_space set"
  assumes "convex S"
    and "z \<in> rel_interior S"
  shows "\<forall>x\<in>affine hull S. \<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
proof -
  obtain e1 where e1: "e1 > 0 \<and> cball z e1 \<inter> affine hull S \<subseteq> S"
    using mem_rel_interior_cball[of z S] assms by auto
  {
    fix x
    assume x: "x \<in> affine hull S"
    {
      assume "x \<noteq> z"
      define m where "m = 1 + e1/norm(x-z)"
      hence "m > 1" using e1 \<open>x \<noteq> z\<close> by auto
      {
        fix e
        assume e: "e > 1 \<and> e \<le> m"
        have "z \<in> affine hull S"
          using assms rel_interior_subset hull_subset[of S] by auto
        then have *: "(1 - e)*\<^sub>R x + e *\<^sub>R z \<in> affine hull S"
          using mem_affine[of "affine hull S" x z "(1-e)" e] affine_affine_hull[of S] x
          by auto
        have "norm (z + e *\<^sub>R x - (x + e *\<^sub>R z)) = norm ((e - 1) *\<^sub>R (x - z))"
          by (simp add: algebra_simps)
        also have "\<dots> = (e - 1) * norm (x-z)"
          using norm_scaleR e by auto
        also have "\<dots> \<le> (m - 1) * norm (x - z)"
          using e mult_right_mono[of _ _ "norm(x-z)"] by auto
        also have "\<dots> = (e1 / norm (x - z)) * norm (x - z)"
          using m_def by auto
        also have "\<dots> = e1"
          using \<open>x \<noteq> z\<close> e1 by simp
        finally have **: "norm (z + e *\<^sub>R x - (x + e *\<^sub>R z)) \<le> e1"
          by auto
        have "(1 - e)*\<^sub>R x+ e *\<^sub>R z \<in> cball z e1"
          using m_def **
          unfolding cball_def dist_norm
          by (auto simp add: algebra_simps)
        then have "(1 - e) *\<^sub>R x+ e *\<^sub>R z \<in> S"
          using e * e1 by auto
      }
      then have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S )"
        using \<open>m> 1 \<close> by auto
    }
    moreover
    {
      assume "x = z"
      define m where "m = 1 + e1"
      then have "m > 1"
        using e1 by auto
      {
        fix e
        assume e: "e > 1 \<and> e \<le> m"
        then have "(1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
          using e1 x \<open>x = z\<close> by (auto simp add: algebra_simps)
        then have "(1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
          using e by auto
      }
      then have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
        using \<open>m > 1\<close> by auto
    }
    ultimately have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S )"
      by blast
  }
  then show ?thesis by auto
qed

lemma convex_rel_interior_if2:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  assumes "z \<in> rel_interior S"
  shows "\<forall>x\<in>affine hull S. \<exists>e. e > 1 \<and> (1 - e)*\<^sub>R x + e *\<^sub>R z \<in> S"
  using convex_rel_interior_if[of S z] assms by auto

lemma convex_rel_interior_only_if:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
  assumes "\<forall>x\<in>S. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
  shows "z \<in> rel_interior S"
proof -
  obtain x where x: "x \<in> rel_interior S"
    using rel_interior_eq_empty assms by auto
  then have "x \<in> S"
    using rel_interior_subset by auto
  then obtain e where e: "e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
    using assms by auto
  define y where [abs_def]: "y = (1 - e) *\<^sub>R x + e *\<^sub>R z"
  then have "y \<in> S" using e by auto
  define e1 where "e1 = 1/e"
  then have "0 < e1 \<and> e1 < 1" using e by auto
  then have "z  =y - (1 - e1) *\<^sub>R (y - x)"
    using e1_def y_def by (auto simp add: algebra_simps)
  then show ?thesis
    using rel_interior_convex_shrink[of S x y "1-e1"] \<open>0 < e1 \<and> e1 < 1\<close> \<open>y \<in> S\<close> x assms
    by auto
qed

lemma convex_rel_interior_iff:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
  shows "z \<in> rel_interior S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
  using assms hull_subset[of S "affine"]
    convex_rel_interior_if[of S z] convex_rel_interior_only_if[of S z]
  by auto

lemma convex_rel_interior_iff2:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
  shows "z \<in> rel_interior S \<longleftrightarrow> (\<forall>x\<in>affine hull S. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
  using assms hull_subset[of S] convex_rel_interior_if2[of S z] convex_rel_interior_only_if[of S z]
  by auto

lemma convex_interior_iff:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "z \<in> interior S \<longleftrightarrow> (\<forall>x. \<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S)"
proof (cases "aff_dim S = int DIM('n)")
  case False
  { assume "z \<in> interior S"
    then have False
      using False interior_rel_interior_gen[of S] by auto }
  moreover
  { assume r: "\<forall>x. \<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S"
    { fix x
      obtain e1 where e1: "e1 > 0 \<and> z + e1 *\<^sub>R (x - z) \<in> S"
        using r by auto
      obtain e2 where e2: "e2 > 0 \<and> z + e2 *\<^sub>R (z - x) \<in> S"
        using r by auto
      define x1 where [abs_def]: "x1 = z + e1 *\<^sub>R (x - z)"
      then have x1: "x1 \<in> affine hull S"
        using e1 hull_subset[of S] by auto
      define x2 where [abs_def]: "x2 = z + e2 *\<^sub>R (z - x)"
      then have x2: "x2 \<in> affine hull S"
        using e2 hull_subset[of S] by auto
      have *: "e1/(e1+e2) + e2/(e1+e2) = 1"
        using add_divide_distrib[of e1 e2 "e1+e2"] e1 e2 by simp
      then have "z = (e2/(e1+e2)) *\<^sub>R x1 + (e1/(e1+e2)) *\<^sub>R x2"
        by (simp add: x1_def x2_def algebra_simps) (simp add: "*" pth_8)
      then have z: "z \<in> affine hull S"
        using mem_affine[of "affine hull S" x1 x2 "e2/(e1+e2)" "e1/(e1+e2)"]
          x1 x2 affine_affine_hull[of S] *
        by auto
      have "x1 - x2 = (e1 + e2) *\<^sub>R (x - z)"
        using x1_def x2_def by (auto simp add: algebra_simps)
      then have "x = z+(1/(e1+e2)) *\<^sub>R (x1-x2)"
        using e1 e2 by simp
      then have "x \<in> affine hull S"
        using mem_affine_3_minus[of "affine hull S" z x1 x2 "1/(e1+e2)"]
          x1 x2 z affine_affine_hull[of S]
        by auto
    }
    then have "affine hull S = UNIV"
      by auto
    then have "aff_dim S = int DIM('n)"
      using aff_dim_affine_hull[of S] by (simp)
    then have False
      using False by auto
  }
  ultimately show ?thesis by auto
next
  case True
  then have "S \<noteq> {}"
    using aff_dim_empty[of S] by auto
  have *: "affine hull S = UNIV"
    using True affine_hull_UNIV by auto
  {
    assume "z \<in> interior S"
    then have "z \<in> rel_interior S"
      using True interior_rel_interior_gen[of S] by auto
    then have **: "\<forall>x. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
      using convex_rel_interior_iff2[of S z] assms \<open>S \<noteq> {}\<close> * by auto
    fix x
    obtain e1 where e1: "e1 > 1" "(1 - e1) *\<^sub>R (z - x) + e1 *\<^sub>R z \<in> S"
      using **[rule_format, of "z-x"] by auto
    define e where [abs_def]: "e = e1 - 1"
    then have "(1 - e1) *\<^sub>R (z - x) + e1 *\<^sub>R z = z + e *\<^sub>R x"
      by (simp add: algebra_simps)
    then have "e > 0" "z + e *\<^sub>R x \<in> S"
      using e1 e_def by auto
    then have "\<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S"
      by auto
  }
  moreover
  {
    assume r: "\<forall>x. \<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S"
    {
      fix x
      obtain e1 where e1: "e1 > 0" "z + e1 *\<^sub>R (z - x) \<in> S"
        using r[rule_format, of "z-x"] by auto
      define e where "e = e1 + 1"
      then have "z + e1 *\<^sub>R (z - x) = (1 - e) *\<^sub>R x + e *\<^sub>R z"
        by (simp add: algebra_simps)
      then have "e > 1" "(1 - e)*\<^sub>R x + e *\<^sub>R z \<in> S"
        using e1 e_def by auto
      then have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S" by auto
    }
    then have "z \<in> rel_interior S"
      using convex_rel_interior_iff2[of S z] assms \<open>S \<noteq> {}\<close> by auto
    then have "z \<in> interior S"
      using True interior_rel_interior_gen[of S] by auto
  }
  ultimately show ?thesis by auto
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Relative interior and closure under common operations\<close>

lemma rel_interior_inter_aux: "\<Inter>{rel_interior S |S. S \<in> I} \<subseteq> \<Inter>I"
proof -
  {
    fix y
    assume "y \<in> \<Inter>{rel_interior S |S. S \<in> I}"
    then have y: "\<forall>S \<in> I. y \<in> rel_interior S"
      by auto
    {
      fix S
      assume "S \<in> I"
      then have "y \<in> S"
        using rel_interior_subset y by auto
    }
    then have "y \<in> \<Inter>I" by auto
  }
  then show ?thesis by auto
qed

lemma convex_closure_rel_interior_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "\<Inter>{closure S |S. S \<in> I} \<le> closure (\<Inter>{rel_interior S |S. S \<in> I})"
proof -
  obtain x where x: "\<forall>S\<in>I. x \<in> rel_interior S"
    using assms by auto
  {
    fix y
    assume "y \<in> \<Inter>{closure S |S. S \<in> I}"
    then have y: "\<forall>S \<in> I. y \<in> closure S"
      by auto
    {
      assume "y = x"
      then have "y \<in> closure (\<Inter>{rel_interior S |S. S \<in> I})"
        using x closure_subset[of "\<Inter>{rel_interior S |S. S \<in> I}"] by auto
    }
    moreover
    {
      assume "y \<noteq> x"
      { fix e :: real
        assume e: "e > 0"
        define e1 where "e1 = min 1 (e/norm (y - x))"
        then have e1: "e1 > 0" "e1 \<le> 1" "e1 * norm (y - x) \<le> e"
          using \<open>y \<noteq> x\<close> \<open>e > 0\<close> le_divide_eq[of e1 e "norm (y - x)"]
          by simp_all
        define z where "z = y - e1 *\<^sub>R (y - x)"
        {
          fix S
          assume "S \<in> I"
          then have "z \<in> rel_interior S"
            using rel_interior_closure_convex_shrink[of S x y e1] assms x y e1 z_def
            by auto
        }
        then have *: "z \<in> \<Inter>{rel_interior S |S. S \<in> I}"
          by auto
        have "\<exists>z. z \<in> \<Inter>{rel_interior S |S. S \<in> I} \<and> z \<noteq> y \<and> dist z y \<le> e"
          using \<open>y \<noteq> x\<close> z_def * e1 e dist_norm[of z y]
          by (rule_tac x="z" in exI) auto
      }
      then have "y islimpt \<Inter>{rel_interior S |S. S \<in> I}"
        unfolding islimpt_approachable_le by blast
      then have "y \<in> closure (\<Inter>{rel_interior S |S. S \<in> I})"
        unfolding closure_def by auto
    }
    ultimately have "y \<in> closure (\<Inter>{rel_interior S |S. S \<in> I})"
      by auto
  }
  then show ?thesis by auto
qed

lemma convex_closure_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "closure (\<Inter>I) = \<Inter>{closure S |S. S \<in> I}"
proof -
  have "\<Inter>{closure S |S. S \<in> I} \<le> closure (\<Inter>{rel_interior S |S. S \<in> I})"
    using convex_closure_rel_interior_inter assms by auto
  moreover
  have "closure (\<Inter>{rel_interior S |S. S \<in> I}) \<le> closure (\<Inter>I)"
    using rel_interior_inter_aux closure_mono[of "\<Inter>{rel_interior S |S. S \<in> I}" "\<Inter>I"]
    by auto
  ultimately show ?thesis
    using closure_Int[of I] by auto
qed

lemma convex_inter_rel_interior_same_closure:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "closure (\<Inter>{rel_interior S |S. S \<in> I}) = closure (\<Inter>I)"
proof -
  have "\<Inter>{closure S |S. S \<in> I} \<le> closure (\<Inter>{rel_interior S |S. S \<in> I})"
    using convex_closure_rel_interior_inter assms by auto
  moreover
  have "closure (\<Inter>{rel_interior S |S. S \<in> I}) \<le> closure (\<Inter>I)"
    using rel_interior_inter_aux closure_mono[of "\<Inter>{rel_interior S |S. S \<in> I}" "\<Inter>I"]
    by auto
  ultimately show ?thesis
    using closure_Int[of I] by auto
qed

lemma convex_rel_interior_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "rel_interior (\<Inter>I) \<subseteq> \<Inter>{rel_interior S |S. S \<in> I}"
proof -
  have "convex (\<Inter>I)"
    using assms convex_Inter by auto
  moreover
  have "convex (\<Inter>{rel_interior S |S. S \<in> I})"
    using assms convex_rel_interior by (force intro: convex_Inter)
  ultimately
  have "rel_interior (\<Inter>{rel_interior S |S. S \<in> I}) = rel_interior (\<Inter>I)"
    using convex_inter_rel_interior_same_closure assms
      closure_eq_rel_interior_eq[of "\<Inter>{rel_interior S |S. S \<in> I}" "\<Inter>I"]
    by blast
  then show ?thesis
    using rel_interior_subset[of "\<Inter>{rel_interior S |S. S \<in> I}"] by auto
qed

lemma convex_rel_interior_finite_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
    and "finite I"
  shows "rel_interior (\<Inter>I) = \<Inter>{rel_interior S |S. S \<in> I}"
proof -
  have "\<Inter>I \<noteq> {}"
    using assms rel_interior_inter_aux[of I] by auto
  have "convex (\<Inter>I)"
    using convex_Inter assms by auto
  show ?thesis
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Inter_empty rel_interior_UNIV by auto
  next
    case False
    {
      fix z
      assume z: "z \<in> \<Inter>{rel_interior S |S. S \<in> I}"
      {
        fix x
        assume x: "x \<in> \<Inter>I"
        {
          fix S
          assume S: "S \<in> I"
          then have "z \<in> rel_interior S" "x \<in> S"
            using z x by auto
          then have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e)*\<^sub>R x + e *\<^sub>R z \<in> S)"
            using convex_rel_interior_if[of S z] S assms hull_subset[of S] by auto
        }
        then obtain mS where
          mS: "\<forall>S\<in>I. mS S > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> mS S \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)" by metis
        define e where "e = Min (mS ` I)"
        then have "e \<in> mS ` I" using assms \<open>I \<noteq> {}\<close> by simp
        then have "e > 1" using mS by auto
        moreover have "\<forall>S\<in>I. e \<le> mS S"
          using e_def assms by auto
        ultimately have "\<exists>e > 1. (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> \<Inter>I"
          using mS by auto
      }
      then have "z \<in> rel_interior (\<Inter>I)"
        using convex_rel_interior_iff[of "\<Inter>I" z] \<open>\<Inter>I \<noteq> {}\<close> \<open>convex (\<Inter>I)\<close> by auto
    }
    then show ?thesis
      using convex_rel_interior_inter[of I] assms by auto
  qed
qed

lemma convex_closure_inter_two:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
  assumes "rel_interior S \<inter> rel_interior T \<noteq> {}"
  shows "closure (S \<inter> T) = closure S \<inter> closure T"
  using convex_closure_inter[of "{S,T}"] assms by auto

lemma convex_rel_interior_inter_two:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
    and "rel_interior S \<inter> rel_interior T \<noteq> {}"
  shows "rel_interior (S \<inter> T) = rel_interior S \<inter> rel_interior T"
  using convex_rel_interior_finite_inter[of "{S,T}"] assms by auto

lemma convex_affine_closure_Int:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "rel_interior S \<inter> T \<noteq> {}"
  shows "closure (S \<inter> T) = closure S \<inter> T"
  by (metis affine_imp_convex assms convex_closure_inter_two rel_interior_affine rel_interior_eq_closure)

lemma connected_component_1_gen:
  fixes S :: "'a :: euclidean_space set"
  assumes "DIM('a) = 1"
  shows "connected_component S a b \<longleftrightarrow> closed_segment a b \<subseteq> S"
unfolding connected_component_def
by (metis (no_types, lifting) assms subsetD subsetI convex_contains_segment convex_segment(1)
            ends_in_segment connected_convex_1_gen)

lemma connected_component_1:
  fixes S :: "real set"
  shows "connected_component S a b \<longleftrightarrow> closed_segment a b \<subseteq> S"
by (simp add: connected_component_1_gen)

lemma convex_affine_rel_interior_Int:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "rel_interior S \<inter> T \<noteq> {}"
  shows "rel_interior (S \<inter> T) = rel_interior S \<inter> T"
  by (simp add: affine_imp_convex assms convex_rel_interior_inter_two rel_interior_affine)

lemma convex_affine_rel_frontier_Int:
   fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "interior S \<inter> T \<noteq> {}"
  shows "rel_frontier(S \<inter> T) = frontier S \<inter> T"
using assms
  unfolding rel_frontier_def  frontier_def
  using convex_affine_closure_Int convex_affine_rel_interior_Int rel_interior_nonempty_interior by fastforce

lemma rel_interior_convex_Int_affine:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "affine T" "interior S \<inter> T \<noteq> {}"
  shows "rel_interior(S \<inter> T) = interior S \<inter> T"
  by (metis Int_emptyI assms convex_affine_rel_interior_Int empty_iff interior_rel_interior_gen)

lemma subset_rel_interior_convex:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
    and "S \<le> closure T"
    and "\<not> S \<subseteq> rel_frontier T"
  shows "rel_interior S \<subseteq> rel_interior T"
proof -
  have *: "S \<inter> closure T = S"
    using assms by auto
  have "\<not> rel_interior S \<subseteq> rel_frontier T"
    using closure_mono[of "rel_interior S" "rel_frontier T"] closed_rel_frontier[of T]
      closure_closed[of S] convex_closure_rel_interior[of S] closure_subset[of S] assms
    by auto
  then have "rel_interior S \<inter> rel_interior (closure T) \<noteq> {}"
    using assms rel_frontier_def[of T] rel_interior_subset convex_rel_interior_closure[of T]
    by auto
  then have "rel_interior S \<inter> rel_interior T = rel_interior (S \<inter> closure T)"
    using assms convex_closure convex_rel_interior_inter_two[of S "closure T"]
      convex_rel_interior_closure[of T]
    by auto
  also have "\<dots> = rel_interior S"
    using * by auto
  finally show ?thesis
    by auto
qed

lemma rel_interior_convex_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
  shows "f ` (rel_interior S) = rel_interior (f ` S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    using assms by auto
next
  case False
  interpret linear f by fact
  have *: "f ` (rel_interior S) \<subseteq> f ` S"
    unfolding image_mono using rel_interior_subset by auto
  have "f ` S \<subseteq> f ` (closure S)"
    unfolding image_mono using closure_subset by auto
  also have "\<dots> = f ` (closure (rel_interior S))"
    using convex_closure_rel_interior assms by auto
  also have "\<dots> \<subseteq> closure (f ` (rel_interior S))"
    using closure_linear_image_subset assms by auto
  finally have "closure (f ` S) = closure (f ` rel_interior S)"
    using closure_mono[of "f ` S" "closure (f ` rel_interior S)"] closure_closure
      closure_mono[of "f ` rel_interior S" "f ` S"] *
    by auto
  then have "rel_interior (f ` S) = rel_interior (f ` rel_interior S)"
    using assms convex_rel_interior
      linear_conv_bounded_linear[of f] convex_linear_image[of _ S]
      convex_linear_image[of _ "rel_interior S"]
      closure_eq_rel_interior_eq[of "f ` S" "f ` rel_interior S"]
    by auto
  then have "rel_interior (f ` S) \<subseteq> f ` rel_interior S"
    using rel_interior_subset by auto
  moreover
  {
    fix z
    assume "z \<in> f ` rel_interior S"
    then obtain z1 where z1: "z1 \<in> rel_interior S" "f z1 = z" by auto
    {
      fix x
      assume "x \<in> f ` S"
      then obtain x1 where x1: "x1 \<in> S" "f x1 = x" by auto
      then obtain e where e: "e > 1" "(1 - e) *\<^sub>R x1 + e *\<^sub>R z1 \<in> S"
        using convex_rel_interior_iff[of S z1] \<open>convex S\<close> x1 z1 by auto
      moreover have "f ((1 - e) *\<^sub>R x1 + e *\<^sub>R z1) = (1 - e) *\<^sub>R x + e *\<^sub>R z"
        using x1 z1 by (simp add: linear_add linear_scale \<open>linear f\<close>)
      ultimately have "(1 - e) *\<^sub>R x + e *\<^sub>R z \<in> f ` S"
        using imageI[of "(1 - e) *\<^sub>R x1 + e *\<^sub>R z1" S f] by auto
      then have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> f ` S"
        using e by auto
    }
    then have "z \<in> rel_interior (f ` S)"
      using convex_rel_interior_iff[of "f ` S" z] \<open>convex S\<close> \<open>linear f\<close>
        \<open>S \<noteq> {}\<close> convex_linear_image[of f S]  linear_conv_bounded_linear[of f]
      by auto
  }
  ultimately show ?thesis by auto
qed

lemma rel_interior_convex_linear_preimage:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
    and "f -` (rel_interior S) \<noteq> {}"
  shows "rel_interior (f -` S) = f -` (rel_interior S)"
proof -
  interpret linear f by fact
  have "S \<noteq> {}"
    using assms by auto
  have nonemp: "f -` S \<noteq> {}"
    by (metis assms(3) rel_interior_subset subset_empty vimage_mono)
  then have "S \<inter> (range f) \<noteq> {}"
    by auto
  have conv: "convex (f -` S)"
    using convex_linear_vimage assms by auto
  then have "convex (S \<inter> range f)"
    by (simp add: assms(2) convex_Int convex_linear_image linear_axioms)
  {
    fix z
    assume "z \<in> f -` (rel_interior S)"
    then have z: "f z \<in> rel_interior S"
      by auto
    {
      fix x
      assume "x \<in> f -` S"
      then have "f x \<in> S" by auto
      then obtain e where e: "e > 1" "(1 - e) *\<^sub>R f x + e *\<^sub>R f z \<in> S"
        using convex_rel_interior_iff[of S "f z"] z assms \<open>S \<noteq> {}\<close> by auto
      moreover have "(1 - e) *\<^sub>R f x + e *\<^sub>R f z = f ((1 - e) *\<^sub>R x + e *\<^sub>R z)"
        using \<open>linear f\<close> by (simp add: linear_iff)
      ultimately have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> f -` S"
        using e by auto
    }
    then have "z \<in> rel_interior (f -` S)"
      using convex_rel_interior_iff[of "f -` S" z] conv nonemp by auto
  }
  moreover
  {
    fix z
    assume z: "z \<in> rel_interior (f -` S)"
    {
      fix x
      assume "x \<in> S \<inter> range f"
      then obtain y where y: "f y = x" "y \<in> f -` S" by auto
      then obtain e where e: "e > 1" "(1 - e) *\<^sub>R y + e *\<^sub>R z \<in> f -` S"
        using convex_rel_interior_iff[of "f -` S" z] z conv by auto
      moreover have "(1 - e) *\<^sub>R x + e *\<^sub>R f z = f ((1 - e) *\<^sub>R y + e *\<^sub>R z)"
        using \<open>linear f\<close> y by (simp add: linear_iff)
      ultimately have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R f z \<in> S \<inter> range f"
        using e by auto
    }
    then have "f z \<in> rel_interior (S \<inter> range f)"
      using \<open>convex (S \<inter> (range f))\<close> \<open>S \<inter> range f \<noteq> {}\<close>
        convex_rel_interior_iff[of "S \<inter> (range f)" "f z"]
      by auto
    moreover have "affine (range f)"
      by (simp add: linear_axioms linear_subspace_image subspace_imp_affine)
    ultimately have "f z \<in> rel_interior S"
      using convex_affine_rel_interior_Int[of S "range f"] assms by auto
    then have "z \<in> f -` (rel_interior S)"
      by auto
  }
  ultimately show ?thesis by auto
qed

lemma rel_interior_Times:
  fixes S :: "'n::euclidean_space set"
    and T :: "'m::euclidean_space set"
  assumes "convex S"
    and "convex T"
  shows "rel_interior (S \<times> T) = rel_interior S \<times> rel_interior T"
proof (cases "S = {} \<or> T = {}")
  case True
  then show ?thesis 
    by auto
next
  case False
  then have "S \<noteq> {}" "T \<noteq> {}"
    by auto
  then have ri: "rel_interior S \<noteq> {}" "rel_interior T \<noteq> {}"
    using rel_interior_eq_empty assms by auto
  then have "fst -` rel_interior S \<noteq> {}"
    using fst_vimage_eq_Times[of "rel_interior S"] by auto
  then have "rel_interior ((fst :: 'n * 'm \<Rightarrow> 'n) -` S) = fst -` rel_interior S"
    using linear_fst \<open>convex S\<close> rel_interior_convex_linear_preimage[of fst S] by auto
  then have s: "rel_interior (S \<times> (UNIV :: 'm set)) = rel_interior S \<times> UNIV"
    by (simp add: fst_vimage_eq_Times)
  from ri have "snd -` rel_interior T \<noteq> {}"
    using snd_vimage_eq_Times[of "rel_interior T"] by auto
  then have "rel_interior ((snd :: 'n * 'm \<Rightarrow> 'm) -` T) = snd -` rel_interior T"
    using linear_snd \<open>convex T\<close> rel_interior_convex_linear_preimage[of snd T] by auto
  then have t: "rel_interior ((UNIV :: 'n set) \<times> T) = UNIV \<times> rel_interior T"
    by (simp add: snd_vimage_eq_Times)
  from s t have *: "rel_interior (S \<times> (UNIV :: 'm set)) \<inter> rel_interior ((UNIV :: 'n set) \<times> T) =
      rel_interior S \<times> rel_interior T" by auto
  have "S \<times> T = S \<times> (UNIV :: 'm set) \<inter> (UNIV :: 'n set) \<times> T"
    by auto
  then have "rel_interior (S \<times> T) = rel_interior ((S \<times> (UNIV :: 'm set)) \<inter> ((UNIV :: 'n set) \<times> T))"
    by auto
  also have "\<dots> = rel_interior (S \<times> (UNIV :: 'm set)) \<inter> rel_interior ((UNIV :: 'n set) \<times> T)"
    using * ri assms convex_Times
    by (subst convex_rel_interior_inter_two) auto
  finally show ?thesis using * by auto
qed

lemma rel_interior_scaleR:
  fixes S :: "'n::euclidean_space set"
  assumes "c \<noteq> 0"
  shows "((*\<^sub>R) c) ` (rel_interior S) = rel_interior (((*\<^sub>R) c) ` S)"
  using rel_interior_injective_linear_image[of "((*\<^sub>R) c)" S]
    linear_conv_bounded_linear[of "(*\<^sub>R) c"] linear_scaleR injective_scaleR[of c] assms
  by auto

lemma rel_interior_convex_scaleR:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "((*\<^sub>R) c) ` (rel_interior S) = rel_interior (((*\<^sub>R) c) ` S)"
  by (metis assms linear_scaleR rel_interior_convex_linear_image)

lemma convex_rel_open_scaleR:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "rel_open S"
  shows "convex (((*\<^sub>R) c) ` S) \<and> rel_open (((*\<^sub>R) c) ` S)"
  by (metis assms convex_scaling rel_interior_convex_scaleR rel_open_def)

lemma convex_rel_open_finite_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set) \<and> rel_open S"
    and "finite I"
  shows "convex (\<Inter>I) \<and> rel_open (\<Inter>I)"
proof (cases "\<Inter>{rel_interior S |S. S \<in> I} = {}")
  case True
  then have "\<Inter>I = {}"
    using assms unfolding rel_open_def by auto
  then show ?thesis
    unfolding rel_open_def by auto
next
  case False
  then have "rel_open (\<Inter>I)"
    using assms unfolding rel_open_def
    using convex_rel_interior_finite_inter[of I]
    by auto
  then show ?thesis
    using convex_Inter assms by auto
qed

lemma convex_rel_open_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
    and "rel_open S"
  shows "convex (f ` S) \<and> rel_open (f ` S)"
  by (metis assms convex_linear_image rel_interior_convex_linear_image rel_open_def)

lemma convex_rel_open_linear_preimage:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
    and "rel_open S"
  shows "convex (f -` S) \<and> rel_open (f -` S)"
proof (cases "f -` (rel_interior S) = {}")
  case True
  then have "f -` S = {}"
    using assms unfolding rel_open_def by auto
  then show ?thesis
    unfolding rel_open_def by auto
next
  case False
  then have "rel_open (f -` S)"
    using assms unfolding rel_open_def
    using rel_interior_convex_linear_preimage[of f S]
    by auto
  then show ?thesis
    using convex_linear_vimage assms
    by auto
qed

lemma rel_interior_projection:
  fixes S :: "('m::euclidean_space \<times> 'n::euclidean_space) set"
    and f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space set"
  assumes "convex S"
    and "f = (\<lambda>y. {z. (y, z) \<in> S})"
  shows "(y, z) \<in> rel_interior S \<longleftrightarrow> (y \<in> rel_interior {y. (f y \<noteq> {})} \<and> z \<in> rel_interior (f y))"
proof -
  {
    fix y
    assume "y \<in> {y. f y \<noteq> {}}"
    then obtain z where "(y, z) \<in> S"
      using assms by auto
    then have "\<exists>x. x \<in> S \<and> y = fst x"
      by auto
    then obtain x where "x \<in> S" "y = fst x"
      by blast
    then have "y \<in> fst ` S"
      unfolding image_def by auto
  }
  then have "fst ` S = {y. f y \<noteq> {}}"
    unfolding fst_def using assms by auto
  then have h1: "fst ` rel_interior S = rel_interior {y. f y \<noteq> {}}"
    using rel_interior_convex_linear_image[of fst S] assms linear_fst by auto
  {
    fix y
    assume "y \<in> rel_interior {y. f y \<noteq> {}}"
    then have "y \<in> fst ` rel_interior S"
      using h1 by auto
    then have *: "rel_interior S \<inter> fst -` {y} \<noteq> {}"
      by auto
    moreover have aff: "affine (fst -` {y})"
      unfolding affine_alt by (simp add: algebra_simps)
    ultimately have **: "rel_interior (S \<inter> fst -` {y}) = rel_interior S \<inter> fst -` {y}"
      using convex_affine_rel_interior_Int[of S "fst -` {y}"] assms by auto
    have conv: "convex (S \<inter> fst -` {y})"
      using convex_Int assms aff affine_imp_convex by auto
    {
      fix x
      assume "x \<in> f y"
      then have "(y, x) \<in> S \<inter> (fst -` {y})"
        using assms by auto
      moreover have "x = snd (y, x)" by auto
      ultimately have "x \<in> snd ` (S \<inter> fst -` {y})"
        by blast
    }
    then have "snd ` (S \<inter> fst -` {y}) = f y"
      using assms by auto
    then have ***: "rel_interior (f y) = snd ` rel_interior (S \<inter> fst -` {y})"
      using rel_interior_convex_linear_image[of snd "S \<inter> fst -` {y}"] linear_snd conv
      by auto
    {
      fix z
      assume "z \<in> rel_interior (f y)"
      then have "z \<in> snd ` rel_interior (S \<inter> fst -` {y})"
        using *** by auto
      moreover have "{y} = fst ` rel_interior (S \<inter> fst -` {y})"
        using * ** rel_interior_subset by auto
      ultimately have "(y, z) \<in> rel_interior (S \<inter> fst -` {y})"
        by force
      then have "(y,z) \<in> rel_interior S"
        using ** by auto
    }
    moreover
    {
      fix z
      assume "(y, z) \<in> rel_interior S"
      then have "(y, z) \<in> rel_interior (S \<inter> fst -` {y})"
        using ** by auto
      then have "z \<in> snd ` rel_interior (S \<inter> fst -` {y})"
        by (metis Range_iff snd_eq_Range)
      then have "z \<in> rel_interior (f y)"
        using *** by auto
    }
    ultimately have "\<And>z. (y, z) \<in> rel_interior S \<longleftrightarrow> z \<in> rel_interior (f y)"
      by auto
  }
  then have h2: "\<And>y z. y \<in> rel_interior {t. f t \<noteq> {}} \<Longrightarrow>
    (y, z) \<in> rel_interior S \<longleftrightarrow> z \<in> rel_interior (f y)"
    by auto
  {
    fix y z
    assume asm: "(y, z) \<in> rel_interior S"
    then have "y \<in> fst ` rel_interior S"
      by (metis Domain_iff fst_eq_Domain)
    then have "y \<in> rel_interior {t. f t \<noteq> {}}"
      using h1 by auto
    then have "y \<in> rel_interior {t. f t \<noteq> {}}" and "(z \<in> rel_interior (f y))"
      using h2 asm by auto
  }
  then show ?thesis using h2 by blast
qed

lemma rel_frontier_Times:
  fixes S :: "'n::euclidean_space set"
    and T :: "'m::euclidean_space set"
  assumes "convex S"
    and "convex T"
  shows "rel_frontier S \<times> rel_frontier T \<subseteq> rel_frontier (S \<times> T)"
    by (force simp: rel_frontier_def rel_interior_Times assms closure_Times)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Relative interior of convex cone\<close>

lemma cone_rel_interior:
  fixes S :: "'m::euclidean_space set"
  assumes "cone S"
  shows "cone ({0} \<union> rel_interior S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: cone_0)
next
  case False
  then have *: "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` S = S)"
    using cone_iff[of S] assms by auto
  then have *: "0 \<in> ({0} \<union> rel_interior S)"
    and "\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` ({0} \<union> rel_interior S) = ({0} \<union> rel_interior S)"
    by (auto simp add: rel_interior_scaleR)
  then show ?thesis
    using cone_iff[of "{0} \<union> rel_interior S"] by auto
qed

lemma rel_interior_convex_cone_aux:
  fixes S :: "'m::euclidean_space set"
  assumes "convex S"
  shows "(c, x) \<in> rel_interior (cone hull ({(1 :: real)} \<times> S)) \<longleftrightarrow>
    c > 0 \<and> x \<in> (((*\<^sub>R) c) ` (rel_interior S))"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: cone_hull_empty)
next
  case False
  then obtain s where "s \<in> S" by auto
  have conv: "convex ({(1 :: real)} \<times> S)"
    using convex_Times[of "{(1 :: real)}" S] assms convex_singleton[of "1 :: real"]
    by auto
  define f where "f y = {z. (y, z) \<in> cone hull ({1 :: real} \<times> S)}" for y
  then have *: "(c, x) \<in> rel_interior (cone hull ({(1 :: real)} \<times> S)) =
    (c \<in> rel_interior {y. f y \<noteq> {}} \<and> x \<in> rel_interior (f c))"
    using convex_cone_hull[of "{(1 :: real)} \<times> S"] conv
    by (subst rel_interior_projection) auto
  {
    fix y :: real
    assume "y \<ge> 0"
    then have "y *\<^sub>R (1,s) \<in> cone hull ({1 :: real} \<times> S)"
      using cone_hull_expl[of "{(1 :: real)} \<times> S"] \<open>s \<in> S\<close> by auto
    then have "f y \<noteq> {}"
      using f_def by auto
  }
  then have "{y. f y \<noteq> {}} = {0..}"
    using f_def cone_hull_expl[of "{1 :: real} \<times> S"] by auto
  then have **: "rel_interior {y. f y \<noteq> {}} = {0<..}"
    using rel_interior_real_semiline by auto
  {
    fix c :: real
    assume "c > 0"
    then have "f c = ((*\<^sub>R) c ` S)"
      using f_def cone_hull_expl[of "{1 :: real} \<times> S"] by auto
    then have "rel_interior (f c) = (*\<^sub>R) c ` rel_interior S"
      using rel_interior_convex_scaleR[of S c] assms by auto
  }
  then show ?thesis using * ** by auto
qed

lemma rel_interior_convex_cone:
  fixes S :: "'m::euclidean_space set"
  assumes "convex S"
  shows "rel_interior (cone hull ({1 :: real} \<times> S)) =
    {(c, c *\<^sub>R x) | c x. c > 0 \<and> x \<in> rel_interior S}"
  (is "?lhs = ?rhs")
proof -
  {
    fix z
    assume "z \<in> ?lhs"
    have *: "z = (fst z, snd z)"
      by auto
    then have "z \<in> ?rhs"
      using rel_interior_convex_cone_aux[of S "fst z" "snd z"] assms \<open>z \<in> ?lhs\<close> by fastforce
  }
  moreover
  {
    fix z
    assume "z \<in> ?rhs"
    then have "z \<in> ?lhs"
      using rel_interior_convex_cone_aux[of S "fst z" "snd z"] assms
      by auto
  }
  ultimately show ?thesis by blast
qed

lemma convex_hull_finite_union:
  assumes "finite I"
  assumes "\<forall>i\<in>I. convex (S i) \<and> (S i) \<noteq> {}"
  shows "convex hull (\<Union>(S ` I)) =
    {sum (\<lambda>i. c i *\<^sub>R s i) I | c s. (\<forall>i\<in>I. c i \<ge> 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> S i)}"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<supseteq> ?rhs"
  proof
    fix x
    assume "x \<in> ?rhs"
    then obtain c s where *: "sum (\<lambda>i. c i *\<^sub>R s i) I = x" "sum c I = 1"
      "(\<forall>i\<in>I. c i \<ge> 0) \<and> (\<forall>i\<in>I. s i \<in> S i)" by auto
    then have "\<forall>i\<in>I. s i \<in> convex hull (\<Union>(S ` I))"
      using hull_subset[of "\<Union>(S ` I)" convex] by auto
    then show "x \<in> ?lhs"
      unfolding *(1)[symmetric]
      using * assms convex_convex_hull
      by (subst convex_sum) auto
  qed
  {
    fix i
    assume "i \<in> I"
    with assms have "\<exists>p. p \<in> S i" by auto
  }
  then obtain p where p: "\<forall>i\<in>I. p i \<in> S i" by metis
  {
    fix i
    assume "i \<in> I"
    {
      fix x
      assume "x \<in> S i"
      define c where "c j = (if j = i then 1::real else 0)" for j
      then have *: "sum c I = 1"
        using \<open>finite I\<close> \<open>i \<in> I\<close> sum.delta[of I i "\<lambda>j::'a. 1::real"]
        by auto
      define s where "s j = (if j = i then x else p j)" for j
      then have "\<forall>j. c j *\<^sub>R s j = (if j = i then x else 0)"
        using c_def by (auto simp add: algebra_simps)
      then have "x = sum (\<lambda>i. c i *\<^sub>R s i) I"
        using s_def c_def \<open>finite I\<close> \<open>i \<in> I\<close> sum.delta[of I i "\<lambda>j::'a. x"]
        by auto
      moreover have "(\<forall>i\<in>I. 0 \<le> c i) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> S i)"
        using * c_def s_def p \<open>x \<in> S i\<close> by auto
      ultimately have "x \<in> ?rhs"
        by force
    }
    then have "?rhs \<supseteq> S i" by auto
  }
  then have *: "?rhs \<supseteq> \<Union>(S ` I)" by auto

  {
    fix u v :: real
    assume uv: "u \<ge> 0 \<and> v \<ge> 0 \<and> u + v = 1"
    fix x y
    assume xy: "x \<in> ?rhs \<and> y \<in> ?rhs"
    from xy obtain c s where
      xc: "x = sum (\<lambda>i. c i *\<^sub>R s i) I \<and> (\<forall>i\<in>I. c i \<ge> 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> S i)"
      by auto
    from xy obtain d t where
      yc: "y = sum (\<lambda>i. d i *\<^sub>R t i) I \<and> (\<forall>i\<in>I. d i \<ge> 0) \<and> sum d I = 1 \<and> (\<forall>i\<in>I. t i \<in> S i)"
      by auto
    define e where "e i = u * c i + v * d i" for i
    have ge0: "\<forall>i\<in>I. e i \<ge> 0"
      using e_def xc yc uv by simp
    have "sum (\<lambda>i. u * c i) I = u * sum c I"
      by (simp add: sum_distrib_left)
    moreover have "sum (\<lambda>i. v * d i) I = v * sum d I"
      by (simp add: sum_distrib_left)
    ultimately have sum1: "sum e I = 1"
      using e_def xc yc uv by (simp add: sum.distrib)
    define q where "q i = (if e i = 0 then p i else (u * c i / e i) *\<^sub>R s i + (v * d i / e i) *\<^sub>R t i)"
      for i
    {
      fix i
      assume i: "i \<in> I"
      have "q i \<in> S i"
      proof (cases "e i = 0")
        case True
        then show ?thesis using i p q_def by auto
      next
        case False
        then show ?thesis
          using mem_convex_alt[of "S i" "s i" "t i" "u * (c i)" "v * (d i)"]
            mult_nonneg_nonneg[of u "c i"] mult_nonneg_nonneg[of v "d i"]
            assms q_def e_def i False xc yc uv
          by (auto simp del: mult_nonneg_nonneg)
      qed
    }
    then have qs: "\<forall>i\<in>I. q i \<in> S i" by auto
    {
      fix i
      assume i: "i \<in> I"
      have "(u * c i) *\<^sub>R s i + (v * d i) *\<^sub>R t i = e i *\<^sub>R q i"
      proof (cases "e i = 0")
        case True
        have ge: "u * (c i) \<ge> 0 \<and> v * d i \<ge> 0"
          using xc yc uv i by simp
        moreover from ge have "u * c i \<le> 0 \<and> v * d i \<le> 0"
          using True e_def i by simp
        ultimately have "u * c i = 0 \<and> v * d i = 0" by auto
        with True show ?thesis by auto
      next
        case False
        then have "(u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i) = q i"
          using q_def by auto
        then have "e i *\<^sub>R ((u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i))
               = (e i) *\<^sub>R (q i)" by auto
        with False show ?thesis by (simp add: algebra_simps)
      qed
    }
    then have *: "\<forall>i\<in>I. (u * c i) *\<^sub>R s i + (v * d i) *\<^sub>R t i = e i *\<^sub>R q i"
      by auto
    have "u *\<^sub>R x + v *\<^sub>R y = sum (\<lambda>i. (u * c i) *\<^sub>R s i + (v * d i) *\<^sub>R t i) I"
      using xc yc by (simp add: algebra_simps scaleR_right.sum sum.distrib)
    also have "\<dots> = sum (\<lambda>i. e i *\<^sub>R q i) I"
      using * by auto
    finally have "u *\<^sub>R x + v *\<^sub>R y = sum (\<lambda>i. (e i) *\<^sub>R (q i)) I"
      by auto
    then have "u *\<^sub>R x + v *\<^sub>R y \<in> ?rhs"
      using ge0 sum1 qs by auto
  }
  then have "convex ?rhs" unfolding convex_def by auto
  then show ?thesis
    using \<open>?lhs \<supseteq> ?rhs\<close> * hull_minimal[of "\<Union>(S ` I)" ?rhs convex]
    by blast
qed

lemma convex_hull_union_two:
  fixes S T :: "'m::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
    and "convex T"
    and "T \<noteq> {}"
  shows "convex hull (S \<union> T) =
    {u *\<^sub>R s + v *\<^sub>R t | u v s t. u \<ge> 0 \<and> v \<ge> 0 \<and> u + v = 1 \<and> s \<in> S \<and> t \<in> T}"
  (is "?lhs = ?rhs")
proof
  define I :: "nat set" where "I = {1, 2}"
  define s where "s i = (if i = (1::nat) then S else T)" for i
  have "\<Union>(s ` I) = S \<union> T"
    using s_def I_def by auto
  then have "convex hull (\<Union>(s ` I)) = convex hull (S \<union> T)"
    by auto
  moreover have "convex hull \<Union>(s ` I) =
    {\<Sum> i\<in>I. c i *\<^sub>R sa i | c sa. (\<forall>i\<in>I. 0 \<le> c i) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. sa i \<in> s i)}"
      using assms s_def I_def
      by (subst convex_hull_finite_union) auto
  moreover have
    "{\<Sum>i\<in>I. c i *\<^sub>R sa i | c sa. (\<forall>i\<in>I. 0 \<le> c i) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. sa i \<in> s i)} \<le> ?rhs"
    using s_def I_def by auto
  ultimately show "?lhs \<subseteq> ?rhs" by auto
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain u v s t where *: "x = u *\<^sub>R s + v *\<^sub>R t \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> u + v = 1 \<and> s \<in> S \<and> t \<in> T"
      by auto
    then have "x \<in> convex hull {s, t}"
      using convex_hull_2[of s t] by auto
    then have "x \<in> convex hull (S \<union> T)"
      using * hull_mono[of "{s, t}" "S \<union> T"] by auto
  }
  then show "?lhs \<supseteq> ?rhs" by blast
qed

proposition ray_to_rel_frontier:
  fixes a :: "'a::real_inner"
  assumes "bounded S"
      and a: "a \<in> rel_interior S"
      and aff: "(a + l) \<in> affine hull S"
      and "l \<noteq> 0"
  obtains d where "0 < d" "(a + d *\<^sub>R l) \<in> rel_frontier S"
           "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (a + e *\<^sub>R l) \<in> rel_interior S"
proof -
  have aaff: "a \<in> affine hull S"
    by (meson a hull_subset rel_interior_subset rev_subsetD)
  let ?D = "{d. 0 < d \<and> a + d *\<^sub>R l \<notin> rel_interior S}"
  obtain B where "B > 0" and B: "S \<subseteq> ball a B"
    using bounded_subset_ballD [OF \<open>bounded S\<close>] by blast
  have "a + (B / norm l) *\<^sub>R l \<notin> ball a B"
    by (simp add: dist_norm \<open>l \<noteq> 0\<close>)
  with B have "a + (B / norm l) *\<^sub>R l \<notin> rel_interior S"
    using rel_interior_subset subsetCE by blast
  with \<open>B > 0\<close> \<open>l \<noteq> 0\<close> have nonMT: "?D \<noteq> {}"
    using divide_pos_pos zero_less_norm_iff by fastforce
  have bdd: "bdd_below ?D"
    by (metis (no_types, lifting) bdd_belowI le_less mem_Collect_eq)
  have relin_Ex: "\<And>x. x \<in> rel_interior S \<Longrightarrow>
                    \<exists>e>0. \<forall>x'\<in>affine hull S. dist x' x < e \<longrightarrow> x' \<in> rel_interior S"
    using openin_rel_interior [of S] by (simp add: openin_euclidean_subtopology_iff)
  define d where "d = Inf ?D"
  obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "\<And>\<eta>. \<lbrakk>0 \<le> \<eta>; \<eta> < \<epsilon>\<rbrakk> \<Longrightarrow> (a + \<eta> *\<^sub>R l) \<in> rel_interior S"
  proof -
    obtain e where "e>0"
            and e: "\<And>x'. x' \<in> affine hull S \<Longrightarrow> dist x' a < e \<Longrightarrow> x' \<in> rel_interior S"
      using relin_Ex a by blast
    show thesis
    proof (rule_tac \<epsilon> = "e / norm l" in that)
      show "0 < e / norm l" by (simp add: \<open>0 < e\<close> \<open>l \<noteq> 0\<close>)
    next
      show "a + \<eta> *\<^sub>R l \<in> rel_interior S" if "0 \<le> \<eta>" "\<eta> < e / norm l" for \<eta>
      proof (rule e)
        show "a + \<eta> *\<^sub>R l \<in> affine hull S"
          by (metis (no_types) add_diff_cancel_left' aff affine_affine_hull mem_affine_3_minus aaff)
        show "dist (a + \<eta> *\<^sub>R l) a < e"
          using that by (simp add: \<open>l \<noteq> 0\<close> dist_norm pos_less_divide_eq)
      qed
    qed
  qed
  have inint: "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> a + e *\<^sub>R l \<in> rel_interior S"
    unfolding d_def using cInf_lower [OF _ bdd]
    by (metis (no_types, lifting) a add.right_neutral le_less mem_Collect_eq not_less real_vector.scale_zero_left)
  have "\<epsilon> \<le> d"
    unfolding d_def
    using \<epsilon> dual_order.strict_implies_order le_less_linear 
    by (blast intro: cInf_greatest [OF nonMT])
  with \<open>0 < \<epsilon>\<close> have "0 < d" by simp
  have "a + d *\<^sub>R l \<notin> rel_interior S"
  proof
    assume adl: "a + d *\<^sub>R l \<in> rel_interior S"
    obtain e where "e > 0"
             and e: "\<And>x'. x' \<in> affine hull S \<Longrightarrow> dist x' (a + d *\<^sub>R l) < e \<Longrightarrow> x' \<in> rel_interior S"
      using relin_Ex adl by blast
    have "d + e / norm l \<le> Inf {d. 0 < d \<and> a + d *\<^sub>R l \<notin> rel_interior S}"
    proof (rule cInf_greatest [OF nonMT], clarsimp)
      fix x::real
      assume "0 < x" and nonrel: "a + x *\<^sub>R l \<notin> rel_interior S"
      show "d + e / norm l \<le> x"
      proof (cases "x < d")
        case True with inint nonrel \<open>0 < x\<close>
          show ?thesis by auto
      next
        case False
          then have dle: "x < d + e / norm l \<Longrightarrow> dist (a + x *\<^sub>R l) (a + d *\<^sub>R l) < e"
            by (simp add: field_simps \<open>l \<noteq> 0\<close>)
          have ain: "a + x *\<^sub>R l \<in> affine hull S"
            by (metis add_diff_cancel_left' aff affine_affine_hull mem_affine_3_minus aaff)
          show ?thesis
            using e [OF ain] nonrel dle by force
      qed
    qed
    then show False
      using \<open>0 < e\<close> \<open>l \<noteq> 0\<close> by (simp add: d_def [symmetric] field_simps)
  qed
  moreover have "a + d *\<^sub>R l \<in> closure S"
  proof (clarsimp simp: closure_approachable)
    fix \<eta>::real assume "0 < \<eta>"
    have 1: "a + (d - min d (\<eta> / 2 / norm l)) *\<^sub>R l \<in> S"
    proof (rule subsetD [OF rel_interior_subset inint])
      show "d - min d (\<eta> / 2 / norm l) < d"
        using \<open>l \<noteq> 0\<close> \<open>0 < d\<close> \<open>0 < \<eta>\<close> by auto
    qed auto
    have "norm l * min d (\<eta> / (norm l * 2)) \<le> norm l * (\<eta> / (norm l * 2))"
      by (metis min_def mult_left_mono norm_ge_zero order_refl)
    also have "... < \<eta>"
      using \<open>l \<noteq> 0\<close> \<open>0 < \<eta>\<close> by (simp add: field_simps)
    finally have 2: "norm l * min d (\<eta> / (norm l * 2)) < \<eta>" .
    show "\<exists>y\<in>S. dist y (a + d *\<^sub>R l) < \<eta>"
      using 1 2 \<open>0 < d\<close> \<open>0 < \<eta>\<close> 
      by (rule_tac x="a + (d - min d (\<eta> / 2 / norm l)) *\<^sub>R l" in bexI) (auto simp: algebra_simps)
  qed
  ultimately have infront: "a + d *\<^sub>R l \<in> rel_frontier S"
    by (simp add: rel_frontier_def)
  show ?thesis
    by (rule that [OF \<open>0 < d\<close> infront inint])
qed

corollary ray_to_frontier:
  fixes a :: "'a::euclidean_space"
  assumes "bounded S"
      and a: "a \<in> interior S"
      and "l \<noteq> 0"
  obtains d where "0 < d" "(a + d *\<^sub>R l) \<in> frontier S"
           "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (a + e *\<^sub>R l) \<in> interior S"
proof -
  have \<section>: "interior S = rel_interior S"
    using a rel_interior_nonempty_interior by auto
  then have "a \<in> rel_interior S"
    using a by simp
  moreover have "a + l \<in> affine hull S"
    using a affine_hull_nonempty_interior by blast
  ultimately show thesis
    by (metis \<section> \<open>bounded S\<close> \<open>l \<noteq> 0\<close> frontier_def ray_to_rel_frontier rel_frontier_def that)
qed


lemma segment_to_rel_frontier_aux:
  fixes x :: "'a::euclidean_space"
  assumes "convex S" "bounded S" and x: "x \<in> rel_interior S" and y: "y \<in> S" and xy: "x \<noteq> y"
  obtains z where "z \<in> rel_frontier S" "y \<in> closed_segment x z"
                   "open_segment x z \<subseteq> rel_interior S"
proof -
  have "x + (y - x) \<in> affine hull S"
    using hull_inc [OF y] by auto
  then obtain d where "0 < d" and df: "(x + d *\<^sub>R (y-x)) \<in> rel_frontier S"
                  and di: "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (x + e *\<^sub>R (y-x)) \<in> rel_interior S"
    by (rule ray_to_rel_frontier [OF \<open>bounded S\<close> x]) (use xy in auto)
  show ?thesis
  proof
    show "x + d *\<^sub>R (y - x) \<in> rel_frontier S"
      by (simp add: df)
  next
    have "open_segment x y \<subseteq> rel_interior S"
      using rel_interior_closure_convex_segment [OF \<open>convex S\<close> x] closure_subset y by blast
    moreover have "x + d *\<^sub>R (y - x) \<in> open_segment x y" if "d < 1"
      using xy \<open>0 < d\<close> that by (force simp: in_segment algebra_simps)
    ultimately have "1 \<le> d"
      using df rel_frontier_def by fastforce
    moreover have "x = (1 / d) *\<^sub>R x + ((d - 1) / d) *\<^sub>R x"
      by (metis \<open>0 < d\<close> add.commute add_divide_distrib diff_add_cancel divide_self_if less_irrefl scaleR_add_left scaleR_one)
    ultimately show "y \<in> closed_segment x (x + d *\<^sub>R (y - x))"
      unfolding in_segment
      by (rule_tac x="1/d" in exI) (auto simp: algebra_simps)
  next
    show "open_segment x (x + d *\<^sub>R (y - x)) \<subseteq> rel_interior S"
    proof (rule rel_interior_closure_convex_segment [OF \<open>convex S\<close> x])
      show "x + d *\<^sub>R (y - x) \<in> closure S"
        using df rel_frontier_def by auto
    qed
  qed
qed

lemma segment_to_rel_frontier:
  fixes x :: "'a::euclidean_space"
  assumes S: "convex S" "bounded S" and x: "x \<in> rel_interior S"
      and y: "y \<in> S" and xy: "\<not>(x = y \<and> S = {x})"
  obtains z where "z \<in> rel_frontier S" "y \<in> closed_segment x z"
                  "open_segment x z \<subseteq> rel_interior S"
proof (cases "x=y")
  case True
  with xy have "S \<noteq> {x}"
    by blast
  with True show ?thesis
    by (metis Set.set_insert all_not_in_conv ends_in_segment(1) insert_iff segment_to_rel_frontier_aux[OF S x] that y)
next
  case False
  then show ?thesis
    using segment_to_rel_frontier_aux [OF S x y] that by blast
qed

proposition rel_frontier_not_sing:
  fixes a :: "'a::euclidean_space"
  assumes "bounded S"
    shows "rel_frontier S \<noteq> {a}"
proof (cases "S = {}")
  case True  then show ?thesis  by simp
next
  case False
  then obtain z where "z \<in> S"
    by blast
  then show ?thesis
  proof (cases "S = {z}")
    case True then show ?thesis  by simp
  next
    case False
    then obtain w where "w \<in> S" "w \<noteq> z"
      using \<open>z \<in> S\<close> by blast
    show ?thesis
    proof
      assume "rel_frontier S = {a}"
      then consider "w \<notin> rel_frontier S" | "z \<notin> rel_frontier S"
        using \<open>w \<noteq> z\<close> by auto
      then show False
      proof cases
        case 1
        then have w: "w \<in> rel_interior S"
          using \<open>w \<in> S\<close> closure_subset rel_frontier_def by fastforce
        have "w + (w - z) \<in> affine hull S"
          by (metis \<open>w \<in> S\<close> \<open>z \<in> S\<close> affine_affine_hull hull_inc mem_affine_3_minus scaleR_one)
        then obtain e where "0 < e" "(w + e *\<^sub>R (w - z)) \<in> rel_frontier S"
          using \<open>w \<noteq> z\<close>  \<open>z \<in> S\<close> by (metis assms ray_to_rel_frontier right_minus_eq w)
        moreover obtain d where "0 < d" "(w + d *\<^sub>R (z - w)) \<in> rel_frontier S"
          using ray_to_rel_frontier [OF \<open>bounded S\<close> w, of "1 *\<^sub>R (z - w)"]  \<open>w \<noteq> z\<close>  \<open>z \<in> S\<close>
          by (metis add.commute add.right_neutral diff_add_cancel hull_inc scaleR_one)
        ultimately have "d *\<^sub>R (z - w) = e *\<^sub>R (w - z)"
          using \<open>rel_frontier S = {a}\<close> by force
        moreover have "e \<noteq> -d "
          using \<open>0 < e\<close> \<open>0 < d\<close> by force
        ultimately show False
          by (metis (no_types, lifting) \<open>w \<noteq> z\<close> eq_iff_diff_eq_0 minus_diff_eq real_vector.scale_cancel_right real_vector.scale_minus_right scaleR_left.minus)
      next
        case 2
        then have z: "z \<in> rel_interior S"
          using \<open>z \<in> S\<close> closure_subset rel_frontier_def by fastforce
        have "z + (z - w) \<in> affine hull S"
          by (metis \<open>z \<in> S\<close> \<open>w \<in> S\<close> affine_affine_hull hull_inc mem_affine_3_minus scaleR_one)
        then obtain e where "0 < e" "(z + e *\<^sub>R (z - w)) \<in> rel_frontier S"
          using \<open>w \<noteq> z\<close>  \<open>w \<in> S\<close> by (metis assms ray_to_rel_frontier right_minus_eq z)
        moreover obtain d where "0 < d" "(z + d *\<^sub>R (w - z)) \<in> rel_frontier S"
          using ray_to_rel_frontier [OF \<open>bounded S\<close> z, of "1 *\<^sub>R (w - z)"]  \<open>w \<noteq> z\<close>  \<open>w \<in> S\<close>
          by (metis add.commute add.right_neutral diff_add_cancel hull_inc scaleR_one)
        ultimately have "d *\<^sub>R (w - z) = e *\<^sub>R (z - w)"
          using \<open>rel_frontier S = {a}\<close> by force
        moreover have "e \<noteq> -d "
          using \<open>0 < e\<close> \<open>0 < d\<close> by force
        ultimately show False
          by (metis (no_types, lifting) \<open>w \<noteq> z\<close> eq_iff_diff_eq_0 minus_diff_eq real_vector.scale_cancel_right real_vector.scale_minus_right scaleR_left.minus)
      qed
    qed
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Convexity on direct sums\<close>

lemma closure_sum:
  fixes S T :: "'a::real_normed_vector set"
  shows "closure S + closure T \<subseteq> closure (S + T)"
  unfolding set_plus_image closure_Times [symmetric] split_def
  by (intro closure_bounded_linear_image_subset bounded_linear_add
    bounded_linear_fst bounded_linear_snd)

lemma rel_interior_sum:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
  shows "rel_interior (S + T) = rel_interior S + rel_interior T"
proof -
  have "rel_interior S + rel_interior T = (\<lambda>(x,y). x + y) ` (rel_interior S \<times> rel_interior T)"
    by (simp add: set_plus_image)
  also have "\<dots> = (\<lambda>(x,y). x + y) ` rel_interior (S \<times> T)"
    using rel_interior_Times assms by auto
  also have "\<dots> = rel_interior (S + T)"
    using fst_snd_linear convex_Times assms
      rel_interior_convex_linear_image[of "(\<lambda>(x,y). x + y)" "S \<times> T"]
    by (auto simp add: set_plus_image)
  finally show ?thesis ..
qed

lemma rel_interior_sum_gen:
  fixes S :: "'a \<Rightarrow> 'n::euclidean_space set"
  assumes "\<And>i. i\<in>I \<Longrightarrow> convex (S i)"
  shows "rel_interior (sum S I) = sum (\<lambda>i. rel_interior (S i)) I"
  using rel_interior_sum rel_interior_sing[of "0"] assms
  by (subst sum_set_cond_linear[of convex], auto simp add: convex_set_plus)

lemma convex_rel_open_direct_sum:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "rel_open S"
    and "convex T"
    and "rel_open T"
  shows "convex (S \<times> T) \<and> rel_open (S \<times> T)"
  by (metis assms convex_Times rel_interior_Times rel_open_def)

lemma convex_rel_open_sum:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "rel_open S"
    and "convex T"
    and "rel_open T"
  shows "convex (S + T) \<and> rel_open (S + T)"
  by (metis assms convex_set_plus rel_interior_sum rel_open_def)

lemma convex_hull_finite_union_cones:
  assumes "finite I"
    and "I \<noteq> {}"
  assumes "\<And>i. i\<in>I \<Longrightarrow> convex (S i) \<and> cone (S i) \<and> S i \<noteq> {}"
  shows "convex hull (\<Union>(S ` I)) = sum S I"
  (is "?lhs = ?rhs")
proof -
  {
    fix x
    assume "x \<in> ?lhs"
    then obtain c xs where
      x: "x = sum (\<lambda>i. c i *\<^sub>R xs i) I \<and> (\<forall>i\<in>I. c i \<ge> 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. xs i \<in> S i)"
      using convex_hull_finite_union[of I S] assms by auto
    define s where "s i = c i *\<^sub>R xs i" for i
    have "\<forall>i\<in>I. s i \<in> S i"
        using s_def x assms by (simp add: mem_cone)
    moreover have "x = sum s I" using x s_def by auto
    ultimately have "x \<in> ?rhs"
      using set_sum_alt[of I S] assms by auto
  }
  moreover
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain s where x: "x = sum s I \<and> (\<forall>i\<in>I. s i \<in> S i)"
      using set_sum_alt[of I S] assms by auto
    define xs where "xs i = of_nat(card I) *\<^sub>R s i" for i
    then have "x = sum (\<lambda>i. ((1 :: real) / of_nat(card I)) *\<^sub>R xs i) I"
      using x assms by auto
    moreover have "\<forall>i\<in>I. xs i \<in> S i"
      using x xs_def assms by (simp add: cone_def)
    moreover have "\<forall>i\<in>I. (1 :: real) / of_nat (card I) \<ge> 0"
      by auto
    moreover have "sum (\<lambda>i. (1 :: real) / of_nat (card I)) I = 1"
      using assms by auto
    ultimately have "x \<in> ?lhs"
      using assms
      apply (simp add: convex_hull_finite_union[of I S])
      by (rule_tac x = "(\<lambda>i. 1 / (card I))" in exI) auto
  }
  ultimately show ?thesis by auto
qed

lemma convex_hull_union_cones_two:
  fixes S T :: "'m::euclidean_space set"
  assumes "convex S"
    and "cone S"
    and "S \<noteq> {}"
  assumes "convex T"
    and "cone T"
    and "T \<noteq> {}"
  shows "convex hull (S \<union> T) = S + T"
proof -
  define I :: "nat set" where "I = {1, 2}"
  define A where "A i = (if i = (1::nat) then S else T)" for i
  have "\<Union>(A ` I) = S \<union> T"
    using A_def I_def by auto
  then have "convex hull (\<Union>(A ` I)) = convex hull (S \<union> T)"
    by auto
  moreover have "convex hull \<Union>(A ` I) = sum A I"
    using A_def I_def
    by (metis assms convex_hull_finite_union_cones empty_iff finite.emptyI finite.insertI insertI1)
  moreover have "sum A I = S + T"
    using A_def I_def by (force simp add: set_plus_def)
  ultimately show ?thesis by auto
qed

lemma rel_interior_convex_hull_union:
  fixes S :: "'a \<Rightarrow> 'n::euclidean_space set"
  assumes "finite I"
    and "\<forall>i\<in>I. convex (S i) \<and> S i \<noteq> {}"
  shows "rel_interior (convex hull (\<Union>(S ` I))) =
    {sum (\<lambda>i. c i *\<^sub>R s i) I | c s. (\<forall>i\<in>I. c i > 0) \<and> sum c I = 1 \<and>
      (\<forall>i\<in>I. s i \<in> rel_interior(S i))}"
  (is "?lhs = ?rhs")
proof (cases "I = {}")
  case True
  then show ?thesis
    using convex_hull_empty by auto
next
  case False
  define C0 where "C0 = convex hull (\<Union>(S ` I))"
  have "\<forall>i\<in>I. C0 \<ge> S i"
    unfolding C0_def using hull_subset[of "\<Union>(S ` I)"] by auto
  define K0 where "K0 = cone hull ({1 :: real} \<times> C0)"
  define K where "K i = cone hull ({1 :: real} \<times> S i)" for i
  have "\<forall>i\<in>I. K i \<noteq> {}"
    unfolding K_def using assms
    by (simp add: cone_hull_empty_iff[symmetric])
  have convK: "\<forall>i\<in>I. convex (K i)"
    unfolding K_def
    by (simp add: assms(2) convex_Times convex_cone_hull)
  have "K0 \<supseteq> K i" if  "i \<in> I" for i
    unfolding K0_def K_def
    by (simp add: Sigma_mono \<open>\<forall>i\<in>I. S i \<subseteq> C0\<close> hull_mono that)
  then have "K0 \<supseteq> \<Union>(K ` I)" by auto
  moreover have "convex K0"
    unfolding K0_def by (simp add: C0_def convex_Times convex_cone_hull)
  ultimately have geq: "K0 \<supseteq> convex hull (\<Union>(K ` I))"
    using hull_minimal[of _ "K0" "convex"] by blast
  have "\<forall>i\<in>I. K i \<supseteq> {1 :: real} \<times> S i"
    using K_def by (simp add: hull_subset)
  then have "\<Union>(K ` I) \<supseteq> {1 :: real} \<times> \<Union>(S ` I)"
    by auto
  then have "convex hull \<Union>(K ` I) \<supseteq> convex hull ({1 :: real} \<times> \<Union>(S ` I))"
    by (simp add: hull_mono)
  then have "convex hull \<Union>(K ` I) \<supseteq> {1 :: real} \<times> C0"
    unfolding C0_def
    using convex_hull_Times[of "{(1 :: real)}" "\<Union>(S ` I)"] convex_hull_singleton
    by auto
  moreover have "cone (convex hull (\<Union>(K ` I)))"
    by (simp add: K_def cone_Union cone_cone_hull cone_convex_hull)
  ultimately have "convex hull (\<Union>(K ` I)) \<supseteq> K0"
    unfolding K0_def
    using hull_minimal[of _ "convex hull (\<Union>(K ` I))" "cone"]
    by blast
  then have "K0 = convex hull (\<Union>(K ` I))"
    using geq by auto
  also have "\<dots> = sum K I"
    using assms False \<open>\<forall>i\<in>I. K i \<noteq> {}\<close> cone_hull_eq convK 
    by (intro convex_hull_finite_union_cones; fastforce simp: K_def)
  finally have "K0 = sum K I" by auto
  then have *: "rel_interior K0 = sum (\<lambda>i. (rel_interior (K i))) I"
    using rel_interior_sum_gen[of I K] convK by auto
  {
    fix x
    assume "x \<in> ?lhs"
    then have "(1::real, x) \<in> rel_interior K0"
      using K0_def C0_def rel_interior_convex_cone_aux[of C0 "1::real" x] convex_convex_hull
      by auto
    then obtain k where k: "(1::real, x) = sum k I \<and> (\<forall>i\<in>I. k i \<in> rel_interior (K i))"
      using \<open>finite I\<close> * set_sum_alt[of I "\<lambda>i. rel_interior (K i)"] by auto
    {
      fix i
      assume "i \<in> I"
      then have "convex (S i) \<and> k i \<in> rel_interior (cone hull {1} \<times> S i)"
        using k K_def assms by auto
      then have "\<exists>ci si. k i = (ci, ci *\<^sub>R si) \<and> 0 < ci \<and> si \<in> rel_interior (S i)"
        using rel_interior_convex_cone[of "S i"] by auto
    }
    then obtain c s where cs: "\<forall>i\<in>I. k i = (c i, c i *\<^sub>R s i) \<and> 0 < c i \<and> s i \<in> rel_interior (S i)"
      by metis
    then have "x = (\<Sum>i\<in>I. c i *\<^sub>R s i) \<and> sum c I = 1"
      using k by (simp add: sum_prod)
    then have "x \<in> ?rhs"
      using k cs by auto
  }
  moreover
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain c s where cs: "x = sum (\<lambda>i. c i *\<^sub>R s i) I \<and>
        (\<forall>i\<in>I. c i > 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> rel_interior (S i))"
      by auto
    define k where "k i = (c i, c i *\<^sub>R s i)" for i
    {
      fix i assume "i \<in> I"
      then have "k i \<in> rel_interior (K i)"
        using k_def K_def assms cs rel_interior_convex_cone[of "S i"]
        by auto
    }
    then have "(1, x) \<in> rel_interior K0"
      using * set_sum_alt[of I "(\<lambda>i. rel_interior (K i))"] assms cs
      by (simp add: k_def) (metis (mono_tags, lifting) sum_prod)
    then have "x \<in> ?lhs"
      using K0_def C0_def rel_interior_convex_cone_aux[of C0 1 x]
      by auto
  }
  ultimately show ?thesis by blast
qed


lemma convex_le_Inf_differential:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex_on I f"
    and "x \<in> interior I"
    and "y \<in> I"
  shows "f y \<ge> f x + Inf ((\<lambda>t. (f x - f t) / (x - t)) ` ({x<..} \<inter> I)) * (y - x)"
  (is "_ \<ge> _ + Inf (?F x) * (y - x)")
proof (cases rule: linorder_cases)
  assume "x < y"
  moreover
  have "open (interior I)" by auto
  from openE[OF this \<open>x \<in> interior I\<close>]
  obtain e where e: "0 < e" "ball x e \<subseteq> interior I" .
  moreover define t where "t = min (x + e / 2) ((x + y) / 2)"
  ultimately have "x < t" "t < y" "t \<in> ball x e"
    by (auto simp: dist_real_def field_simps split: split_min)
  with \<open>x \<in> interior I\<close> e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

  define K where "K = x - e / 2"
  with \<open>0 < e\<close> have "K \<in> ball x e" "K < x"
    by (auto simp: dist_real_def)
  then have "K \<in> I"
    using \<open>interior I \<subseteq> I\<close> e(2) by blast

  have "Inf (?F x) \<le> (f x - f y) / (x - y)"
  proof (intro bdd_belowI cInf_lower2)
    show "(f x - f t) / (x - t) \<in> ?F x"
      using \<open>t \<in> I\<close> \<open>x < t\<close> by auto
    show "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
      using \<open>convex_on I f\<close> \<open>x \<in> I\<close> \<open>y \<in> I\<close> \<open>x < t\<close> \<open>t < y\<close>
      by (rule convex_on_diff)
  next
    fix y
    assume "y \<in> ?F x"
    with order_trans[OF convex_on_diff[OF \<open>convex_on I f\<close> \<open>K \<in> I\<close> _ \<open>K < x\<close> _]]
    show "(f K - f x) / (K - x) \<le> y" by auto
  qed
  then show ?thesis
    using \<open>x < y\<close> by (simp add: field_simps)
next
  assume "y < x"
  moreover
  have "open (interior I)" by auto
  from openE[OF this \<open>x \<in> interior I\<close>]
  obtain e where e: "0 < e" "ball x e \<subseteq> interior I" .
  moreover define t where "t = x + e / 2"
  ultimately have "x < t" "t \<in> ball x e"
    by (auto simp: dist_real_def field_simps)
  with \<open>x \<in> interior I\<close> e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

  have "(f x - f y) / (x - y) \<le> Inf (?F x)"
  proof (rule cInf_greatest)
    have "(f x - f y) / (x - y) = (f y - f x) / (y - x)"
      using \<open>y < x\<close> by (auto simp: field_simps)
    also
    fix z
    assume "z \<in> ?F x"
    with order_trans[OF convex_on_diff[OF \<open>convex_on I f\<close> \<open>y \<in> I\<close> _ \<open>y < x\<close>]]
    have "(f y - f x) / (y - x) \<le> z"
      by auto
    finally show "(f x - f y) / (x - y) \<le> z" .
  next
    have "x + e / 2 \<in> ball x e"
      using e by (auto simp: dist_real_def)
    with e interior_subset[of I] have "x + e / 2 \<in> {x<..} \<inter> I"
      by auto
    then show "?F x \<noteq> {}"
      by blast
  qed
  then show ?thesis
    using \<open>y < x\<close> by (simp add: field_simps)
qed simp

subsection\<^marker>\<open>tag unimportant\<close>\<open>Explicit formulas for interior and relative interior of convex hull\<close>

lemma at_within_cbox_finite:
  assumes "x \<in> box a b" "x \<notin> S" "finite S"
  shows "(at x within cbox a b - S) = at x"
proof -
  have "interior (cbox a b - S) = box a b - S"
    using \<open>finite S\<close> by (simp add: interior_diff finite_imp_closed)
  then show ?thesis
    using at_within_interior assms by fastforce
qed

lemma affine_independent_convex_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S" "T \<subseteq> S"
    shows "convex hull T = affine hull T \<inter> convex hull S"
proof -
  have fin: "finite S" "finite T" using assms aff_independent_finite finite_subset by auto
  have "convex hull T \<subseteq> affine hull T"
    using convex_hull_subset_affine_hull by blast
  moreover have "convex hull T \<subseteq> convex hull S"
    using assms hull_mono by blast
  moreover have "affine hull T \<inter> convex hull S \<subseteq> convex hull T"
  proof -
    have 0: "\<And>u. sum u S = 0 \<Longrightarrow> (\<forall>v\<in>S. u v = 0) \<or> (\<Sum>v\<in>S. u v *\<^sub>R v) \<noteq> 0"
      using affine_dependent_explicit_finite assms(1) fin(1) by auto
    show ?thesis
    proof (clarsimp simp add: affine_hull_finite fin)
      fix u
      assume S: "(\<Sum>v\<in>T. u v *\<^sub>R v) \<in> convex hull S"
        and T1: "sum u T = 1"
      then obtain v where v: "\<forall>x\<in>S. 0 \<le> v x" "sum v S = 1" "(\<Sum>x\<in>S. v x *\<^sub>R x) = (\<Sum>v\<in>T. u v *\<^sub>R v)"
        by (auto simp add: convex_hull_finite fin)
      { fix x
        assume"x \<in> T"
        then have S: "S = (S - T) \<union> T" \<comment> \<open>split into separate cases\<close>
          using assms by auto
        have [simp]: "(\<Sum>x\<in>T. v x *\<^sub>R x) + (\<Sum>x\<in>S - T. v x *\<^sub>R x) = (\<Sum>x\<in>T. u x *\<^sub>R x)"
          "sum v T + sum v (S - T) = 1"
          using v fin S
          by (auto simp: sum.union_disjoint [symmetric] Un_commute)
        have "(\<Sum>x\<in>S. if x \<in> T then v x - u x else v x) = 0"
             "(\<Sum>x\<in>S. (if x \<in> T then v x - u x else v x) *\<^sub>R x) = 0"
          using v fin T1
          by (subst S, subst sum.union_disjoint, auto simp: algebra_simps sum_subtractf)+
      } note [simp] = this
      have "(\<forall>x\<in>T. 0 \<le> u x)"
        using 0 [of "\<lambda>x. if x \<in> T then v x - u x else v x"] \<open>T \<subseteq> S\<close> v(1) by fastforce
      then show "(\<Sum>v\<in>T. u v *\<^sub>R v) \<in> convex hull T"
        using 0 [of "\<lambda>x. if x \<in> T then v x - u x else v x"] \<open>T \<subseteq> S\<close> T1
        by (fastforce simp add: convex_hull_finite fin)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma affine_independent_span_eq:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S" "card S = Suc (DIM ('a))"
    shows "affine hull S = UNIV"
proof (cases "S = {}")
  case True then show ?thesis
    using assms by simp
next
  case False
    then obtain a T where T: "a \<notin> T" "S = insert a T"
      by blast
    then have fin: "finite T" using assms
      by (metis finite_insert aff_independent_finite)
    have "UNIV \<subseteq> (+) a ` span ((\<lambda>x. x - a) ` T)"
    proof (intro card_ge_dim_independent Fun.vimage_subsetD)
      show "independent ((\<lambda>x. x - a) ` T)"
        using T affine_dependent_iff_dependent assms(1) by auto
      show "dim ((+) a -` UNIV) \<le> card ((\<lambda>x. x - a) ` T)"
        using assms T fin by (auto simp: card_image inj_on_def)
    qed (use surj_plus in auto)
    then show ?thesis
      using T(2) affine_hull_insert_span_gen equalityI by fastforce
qed

lemma affine_independent_span_gt:
  fixes S :: "'a::euclidean_space set"
  assumes ind: "\<not> affine_dependent S" and dim: "DIM ('a) < card S"
    shows "affine hull S = UNIV"
proof (intro affine_independent_span_eq [OF ind] antisym)
  show "card S \<le> Suc DIM('a)"
    using aff_independent_finite affine_dependent_biggerset ind by fastforce
  show "Suc DIM('a) \<le> card S"
    using Suc_leI dim by blast
qed

lemma empty_interior_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S" and dim: "card S \<le> DIM ('a)"
    shows "interior(affine hull S) = {}"
  using assms
proof (induct S rule: finite_induct)
  case (insert x S)
  then have "dim (span ((\<lambda>y. y - x) ` S)) < DIM('a)"
    by (auto simp: Suc_le_lessD card_image_le dual_order.trans intro!: dim_le_card'[THEN le_less_trans])
  then show ?case
    by (simp add: empty_interior_lowdim affine_hull_insert_span_gen interior_translation)
qed auto

lemma empty_interior_convex_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S" and dim: "card S \<le> DIM ('a)"
    shows "interior(convex hull S) = {}"
  by (metis Diff_empty Diff_eq_empty_iff convex_hull_subset_affine_hull
            interior_mono empty_interior_affine_hull [OF assms])

lemma explicit_subset_rel_interior_convex_hull:
  fixes S :: "'a::euclidean_space set"
  shows "finite S
         \<Longrightarrow> {y. \<exists>u. (\<forall>x \<in> S. 0 < u x \<and> u x < 1) \<and> sum u S = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}
             \<subseteq> rel_interior (convex hull S)"
  by (force simp add:  rel_interior_convex_hull_union [where S="\<lambda>x. {x}" and I=S, simplified])

lemma explicit_subset_rel_interior_convex_hull_minimal:
  fixes S :: "'a::euclidean_space set"
  shows "finite S
         \<Longrightarrow> {y. \<exists>u. (\<forall>x \<in> S. 0 < u x) \<and> sum u S = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}
             \<subseteq> rel_interior (convex hull S)"
  by (force simp add:  rel_interior_convex_hull_union [where S="\<lambda>x. {x}" and I=S, simplified])

lemma rel_interior_convex_hull_explicit:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "rel_interior(convex hull S) =
         {y. \<exists>u. (\<forall>x \<in> S. 0 < u x) \<and> sum u S = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}"
         (is "?lhs = ?rhs")
proof
  show "?rhs \<le> ?lhs"
    by (simp add: aff_independent_finite explicit_subset_rel_interior_convex_hull_minimal assms)
next
  show "?lhs \<le> ?rhs"
  proof (cases "\<exists>a. S = {a}")
    case True then show "?lhs \<le> ?rhs"
      by force
  next
    case False
    have fs: "finite S"
      using assms by (simp add: aff_independent_finite)
    { fix a b and d::real
      assume ab: "a \<in> S" "b \<in> S" "a \<noteq> b"
      then have S: "S = (S - {a,b}) \<union> {a,b}" \<comment> \<open>split into separate cases\<close>
        by auto
      have "(\<Sum>x\<in>S. if x = a then - d else if x = b then d else 0) = 0"
           "(\<Sum>x\<in>S. (if x = a then - d else if x = b then d else 0) *\<^sub>R x) = d *\<^sub>R b - d *\<^sub>R a"
        using ab fs
        by (subst S, subst sum.union_disjoint, auto)+
    } note [simp] = this
    { fix y
      assume y: "y \<in> convex hull S" "y \<notin> ?rhs"
      have *: False if
        ua: "\<forall>x\<in>S. 0 \<le> u x" "sum u S = 1" "\<not> 0 < u a" "a \<in> S"
        and yT: "y = (\<Sum>x\<in>S. u x *\<^sub>R x)" "y \<in> T" "open T"
        and sb: "T \<inter> affine hull S \<subseteq> {w. \<exists>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> (\<Sum>x\<in>S. u x *\<^sub>R x) = w}"
      for u T a
      proof -
        have ua0: "u a = 0"
          using ua by auto
        obtain b where b: "b\<in>S" "a \<noteq> b"
          using ua False by auto
        obtain e where e: "0 < e" "ball (\<Sum>x\<in>S. u x *\<^sub>R x) e \<subseteq> T"
          using yT by (auto elim: openE)
        with b obtain d where d: "0 < d" "norm(d *\<^sub>R (a-b)) < e"
          by (auto intro: that [of "e / 2 / norm(a-b)"])
        have "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> affine hull S"
          using yT y by (metis affine_hull_convex_hull hull_redundant_eq)
        then have "(\<Sum>x\<in>S. u x *\<^sub>R x) - d *\<^sub>R (a - b) \<in> affine hull S"
          using ua b by (auto simp: hull_inc intro: mem_affine_3_minus2)
        then have "y - d *\<^sub>R (a - b) \<in> T \<inter> affine hull S"
          using d e yT by auto
        then obtain v where v: "\<forall>x\<in>S. 0 \<le> v x"
          "sum v S = 1"
          "(\<Sum>x\<in>S. v x *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x) - d *\<^sub>R (a - b)"
          using subsetD [OF sb] yT
          by auto
        have aff: "\<And>u. sum u S = 0 \<Longrightarrow> (\<forall>v\<in>S. u v = 0) \<or> (\<Sum>v\<in>S. u v *\<^sub>R v) \<noteq> 0"
          using assms by (simp add: affine_dependent_explicit_finite fs)
        show False
          using ua b d v aff [of "\<lambda>x. (v x - u x) - (if x = a then -d else if x = b then d else 0)"]
          by (auto simp: algebra_simps sum_subtractf sum.distrib)
      qed
      have "y \<notin> rel_interior (convex hull S)"
        using y
        apply (simp add: mem_rel_interior)
        apply (auto simp: convex_hull_finite [OF fs])
        apply (drule_tac x=u in spec)
        apply (auto intro: *)
        done
    } with rel_interior_subset show "?lhs \<le> ?rhs"
      by blast
  qed
qed

lemma interior_convex_hull_explicit_minimal:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows
   "interior(convex hull S) =
             (if card(S) \<le> DIM('a) then {}
              else {y. \<exists>u. (\<forall>x \<in> S. 0 < u x) \<and> sum u S = 1 \<and> (\<Sum>x\<in>S. u x *\<^sub>R x) = y})"  
   (is "_ = (if _ then _ else ?rhs)")
proof (clarsimp simp: aff_independent_finite empty_interior_convex_hull assms)
  assume S: "\<not> card S \<le> DIM('a)"
  have "interior (convex hull S) = rel_interior(convex hull S)"
    using assms S by (simp add: affine_independent_span_gt rel_interior_interior)
  then show "interior(convex hull S) = ?rhs"
    by (simp add: assms S rel_interior_convex_hull_explicit)
qed

lemma interior_convex_hull_explicit:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows
   "interior(convex hull S) =
             (if card(S) \<le> DIM('a) then {}
              else {y. \<exists>u. (\<forall>x \<in> S. 0 < u x \<and> u x < 1) \<and> sum u S = 1 \<and> (\<Sum>x\<in>S. u x *\<^sub>R x) = y})"
proof -
  { fix u :: "'a \<Rightarrow> real" and a
    assume "card Basis < card S" and u: "\<And>x. x\<in>S \<Longrightarrow> 0 < u x" "sum u S = 1" and a: "a \<in> S"
    then have cs: "Suc 0 < card S"
      by (metis DIM_positive less_trans_Suc)
    obtain b where b: "b \<in> S" "a \<noteq> b"
    proof (cases "S \<le> {a}")
      case True
      then show thesis
        using cs subset_singletonD by fastforce
    qed blast
    have "u a + u b \<le> sum u {a,b}"
      using a b by simp
    also have "... \<le> sum u S"
      using a b u
      by (intro Groups_Big.sum_mono2) (auto simp: less_imp_le aff_independent_finite assms)
    finally have "u a < 1"
      using \<open>b \<in> S\<close> u by fastforce
  } note [simp] = this
  show ?thesis
    using assms by (force simp add: not_le interior_convex_hull_explicit_minimal)
qed

lemma interior_closed_segment_ge2:
  fixes a :: "'a::euclidean_space"
  assumes "2 \<le> DIM('a)"
    shows  "interior(closed_segment a b) = {}"
using assms unfolding segment_convex_hull
proof -
  have "card {a, b} \<le> DIM('a)"
    using assms
    by (simp add: card_insert_if linear not_less_eq_eq numeral_2_eq_2)
  then show "interior (convex hull {a, b}) = {}"
    by (metis empty_interior_convex_hull finite.insertI finite.emptyI)
qed

lemma interior_open_segment:
  fixes a :: "'a::euclidean_space"
  shows  "interior(open_segment a b) =
                 (if 2 \<le> DIM('a) then {} else open_segment a b)"
proof (simp add: not_le, intro conjI impI)
  assume "2 \<le> DIM('a)"
  then show "interior (open_segment a b) = {}"
    using interior_closed_segment_ge2 interior_mono segment_open_subset_closed by blast
next
  assume le2: "DIM('a) < 2"
  show "interior (open_segment a b) = open_segment a b"
  proof (cases "a = b")
    case True then show ?thesis by auto
  next
    case False
    with le2 have "affine hull (open_segment a b) = UNIV"
      by (simp add: False affine_independent_span_gt)
    then show "interior (open_segment a b) = open_segment a b"
      using rel_interior_interior rel_interior_open_segment by blast
  qed
qed

lemma interior_closed_segment:
  fixes a :: "'a::euclidean_space"
  shows "interior(closed_segment a b) =
                 (if 2 \<le> DIM('a) then {} else open_segment a b)"
proof (cases "a = b")
  case True then show ?thesis by simp
next
  case False
  then have "closure (open_segment a b) = closed_segment a b"
    by simp
  then show ?thesis
    by (metis (no_types) convex_interior_closure convex_open_segment interior_open_segment)
qed

lemmas interior_segment = interior_closed_segment interior_open_segment

lemma closed_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "closed_segment a b = closed_segment c d \<longleftrightarrow> {a,b} = {c,d}"
proof
  assume abcd: "closed_segment a b = closed_segment c d"
  show "{a,b} = {c,d}"
  proof (cases "a=b \<or> c=d")
    case True with abcd show ?thesis by force
  next
    case False
    then have neq: "a \<noteq> b \<and> c \<noteq> d" by force
    have *: "closed_segment c d - {a, b} = rel_interior (closed_segment c d)"
      using neq abcd by (metis (no_types) open_segment_def rel_interior_closed_segment)
    have "b \<in> {c, d}"
    proof -
      have "insert b (closed_segment c d) = closed_segment c d"
        using abcd by blast
      then show ?thesis
        by (metis DiffD2 Diff_insert2 False * insertI1 insert_Diff_if open_segment_def rel_interior_closed_segment)
    qed
    moreover have "a \<in> {c, d}"
      by (metis Diff_iff False * abcd ends_in_segment(1) insertI1 open_segment_def rel_interior_closed_segment)
    ultimately show "{a, b} = {c, d}"
      using neq by fastforce
  qed
next
  assume "{a,b} = {c,d}"
  then show "closed_segment a b = closed_segment c d"
    by (simp add: segment_convex_hull)
qed

lemma closed_open_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "closed_segment a b \<noteq> open_segment c d"
by (metis DiffE closed_segment_neq_empty closure_closed_segment closure_open_segment ends_in_segment(1) insertI1 open_segment_def)

lemma open_closed_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b \<noteq> closed_segment c d"
using closed_open_segment_eq by blast

lemma open_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b = open_segment c d \<longleftrightarrow> a = b \<and> c = d \<or> {a,b} = {c,d}"
        (is "?lhs = ?rhs")
proof
  assume abcd: ?lhs
  show ?rhs
  proof (cases "a=b \<or> c=d")
    case True with abcd show ?thesis
      using finite_open_segment by fastforce
  next
    case False
    then have a2: "a \<noteq> b \<and> c \<noteq> d" by force
    with abcd show ?rhs
      unfolding open_segment_def
      by (metis (no_types) abcd closed_segment_eq closure_open_segment)
  qed
next
  assume ?rhs
  then show ?lhs
    by (metis Diff_cancel convex_hull_singleton insert_absorb2 open_segment_def segment_convex_hull)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Similar results for closure and (relative or absolute) frontier\<close>

lemma closure_convex_hull [simp]:
  fixes S :: "'a::euclidean_space set"
  shows "compact S ==> closure(convex hull S) = convex hull S"
  by (simp add: compact_imp_closed compact_convex_hull)

lemma rel_frontier_convex_hull_explicit:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "rel_frontier(convex hull S) =
         {y. \<exists>u. (\<forall>x \<in> S. 0 \<le> u x) \<and> (\<exists>x \<in> S. u x = 0) \<and> sum u S = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}"
proof -
  have fs: "finite S"
    using assms by (simp add: aff_independent_finite)
  have "\<And>u y v.
       \<lbrakk>y \<in> S; u y = 0; sum u S = 1; \<forall>x\<in>S. 0 < v x;
        sum v S = 1; (\<Sum>x\<in>S. v x *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)\<rbrakk>
       \<Longrightarrow> \<exists>u. sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
    apply (rule_tac x = "\<lambda>x. u x - v x" in exI)
    apply (force simp: sum_subtractf scaleR_diff_left)
    done
  then show ?thesis
    using fs assms
    apply (simp add: rel_frontier_def finite_imp_compact rel_interior_convex_hull_explicit)
    apply (auto simp: convex_hull_finite)
    apply (metis less_eq_real_def) 
    by (simp add: affine_dependent_explicit_finite)
qed

lemma frontier_convex_hull_explicit:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "frontier(convex hull S) =
         {y. \<exists>u. (\<forall>x \<in> S. 0 \<le> u x) \<and> (DIM ('a) < card S \<longrightarrow> (\<exists>x \<in> S. u x = 0)) \<and>
             sum u S = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}"
proof -
  have fs: "finite S"
    using assms by (simp add: aff_independent_finite)
  show ?thesis
  proof (cases "DIM ('a) < card S")
    case True
    with assms fs show ?thesis
      by (simp add: rel_frontier_def frontier_def rel_frontier_convex_hull_explicit [symmetric]
                    interior_convex_hull_explicit_minimal rel_interior_convex_hull_explicit)
  next
    case False
    then have "card S \<le> DIM ('a)"
      by linarith
    then show ?thesis
      using assms fs
      apply (simp add: frontier_def interior_convex_hull_explicit finite_imp_compact)
      apply (simp add: convex_hull_finite)
      done
  qed
qed

lemma rel_frontier_convex_hull_cases:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "rel_frontier(convex hull S) = \<Union>{convex hull (S - {x}) |x. x \<in> S}"
proof -
  have fs: "finite S"
    using assms by (simp add: aff_independent_finite)
  { fix u a
  have "\<forall>x\<in>S. 0 \<le> u x \<Longrightarrow> a \<in> S \<Longrightarrow> u a = 0 \<Longrightarrow> sum u S = 1 \<Longrightarrow>
            \<exists>x v. x \<in> S \<and>
                  (\<forall>x\<in>S - {x}. 0 \<le> v x) \<and>
                      sum v (S - {x}) = 1 \<and> (\<Sum>x\<in>S - {x}. v x *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)"
    apply (rule_tac x=a in exI)
    apply (rule_tac x=u in exI)
    apply (simp add: Groups_Big.sum_diff1 fs)
    done }
  moreover
  { fix a u
    have "a \<in> S \<Longrightarrow> \<forall>x\<in>S - {a}. 0 \<le> u x \<Longrightarrow> sum u (S - {a}) = 1 \<Longrightarrow>
            \<exists>v. (\<forall>x\<in>S. 0 \<le> v x) \<and>
                 (\<exists>x\<in>S. v x = 0) \<and> sum v S = 1 \<and> (\<Sum>x\<in>S. v x *\<^sub>R x) = (\<Sum>x\<in>S - {a}. u x *\<^sub>R x)"
    apply (rule_tac x="\<lambda>x. if x = a then 0 else u x" in exI)
    apply (auto simp: sum.If_cases Diff_eq if_smult fs)
    done }
  ultimately show ?thesis
    using assms
    apply (simp add: rel_frontier_convex_hull_explicit)
    apply (auto simp add: convex_hull_finite fs Union_SetCompr_eq)
    done
qed

lemma frontier_convex_hull_eq_rel_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "frontier(convex hull S) =
           (if card S \<le> DIM ('a) then convex hull S else rel_frontier(convex hull S))"
  using assms
  unfolding rel_frontier_def frontier_def
  by (simp add: affine_independent_span_gt rel_interior_interior
                finite_imp_compact empty_interior_convex_hull aff_independent_finite)

lemma frontier_convex_hull_cases:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "frontier(convex hull S) =
           (if card S \<le> DIM ('a) then convex hull S else \<Union>{convex hull (S - {x}) |x. x \<in> S})"
by (simp add: assms frontier_convex_hull_eq_rel_frontier rel_frontier_convex_hull_cases)

lemma in_frontier_convex_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S" "card S \<le> Suc (DIM ('a))" "x \<in> S"
  shows   "x \<in> frontier(convex hull S)"
proof (cases "affine_dependent S")
  case True
  with assms obtain y where "y \<in> S" and y: "y \<in> affine hull (S - {y})"
    by (auto simp: affine_dependent_def)
  moreover have "x \<in> closure (convex hull S)"
    by (meson closure_subset hull_inc subset_eq \<open>x \<in> S\<close>)
  moreover have "x \<notin> interior (convex hull S)"
    using assms
    by (metis Suc_mono affine_hull_convex_hull affine_hull_nonempty_interior \<open>y \<in> S\<close> y card.remove empty_iff empty_interior_affine_hull finite_Diff hull_redundant insert_Diff interior_UNIV not_less)
  ultimately show ?thesis
    unfolding frontier_def by blast
next
  case False
  { assume "card S = Suc (card Basis)"
    then have cs: "Suc 0 < card S"
      by (simp)
    with subset_singletonD have "\<exists>y \<in> S. y \<noteq> x"
      by (cases "S \<le> {x}") fastforce+
  } note [dest!] = this
  show ?thesis using assms
    unfolding frontier_convex_hull_cases [OF False] Union_SetCompr_eq
    by (auto simp: le_Suc_eq hull_inc)
qed

lemma not_in_interior_convex_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S" "card S \<le> Suc (DIM ('a))" "x \<in> S"
  shows   "x \<notin> interior(convex hull S)"
using in_frontier_convex_hull [OF assms]
by (metis Diff_iff frontier_def)

lemma interior_convex_hull_eq_empty:
  fixes S :: "'a::euclidean_space set"
  assumes "card S = Suc (DIM ('a))"
  shows   "interior(convex hull S) = {} \<longleftrightarrow> affine_dependent S"
proof 
  show "affine_dependent S \<Longrightarrow> interior (convex hull S) = {}"
  proof (clarsimp simp: affine_dependent_def)
    fix a b
    assume "b \<in> S" "b \<in> affine hull (S - {b})"
    then have "interior(affine hull S) = {}" using assms
      by (metis DIM_positive One_nat_def Suc_mono card.remove card.infinite empty_interior_affine_hull eq_iff hull_redundant insert_Diff not_less zero_le_one)
    then show "interior (convex hull S) = {}" 
      using affine_hull_nonempty_interior by fastforce
  qed
next
  show "interior (convex hull S) = {} \<Longrightarrow> affine_dependent S"
    by (metis affine_hull_convex_hull affine_hull_empty affine_independent_span_eq assms convex_convex_hull empty_not_UNIV rel_interior_eq_empty rel_interior_interior)
qed


subsection \<open>Coplanarity, and collinearity in terms of affine hull\<close>

definition\<^marker>\<open>tag important\<close> coplanar  where
   "coplanar S \<equiv> \<exists>u v w. S \<subseteq> affine hull {u,v,w}"

lemma collinear_affine_hull:
  "collinear S \<longleftrightarrow> (\<exists>u v. S \<subseteq> affine hull {u,v})"
proof (cases "S={}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain x where x: "x \<in> S" by auto
  { fix u
    assume *: "\<And>x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> \<exists>c. x - y = c *\<^sub>R u"
    have "\<And>y c. x - y = c *\<^sub>R u \<Longrightarrow> \<exists>a b. y = a *\<^sub>R x + b *\<^sub>R (x + u) \<and> a + b = 1"
      by (rule_tac x="1+c" in exI, rule_tac x="-c" in exI, simp add: algebra_simps)
    then have "\<exists>u v. S \<subseteq> {a *\<^sub>R u + b *\<^sub>R v |a b. a + b = 1}"
      using * [OF x] by (rule_tac x=x in exI, rule_tac x="x+u" in exI, force)
  } moreover
  { fix u v x y
    assume *: "S \<subseteq> {a *\<^sub>R u + b *\<^sub>R v |a b. a + b = 1}"
    have "\<exists>c. x - y = c *\<^sub>R (v-u)" if "x\<in>S" "y\<in>S"
    proof -
      obtain a r where "a + r = 1" "x = a *\<^sub>R u + r *\<^sub>R v"
        using "*" \<open>x \<in> S\<close> by blast
      moreover
      obtain b s where "b + s = 1" "y = b *\<^sub>R u + s *\<^sub>R v"
        using "*" \<open>y \<in> S\<close> by blast
      ultimately have "x - y = (r-s) *\<^sub>R (v-u)" 
        by (simp add: algebra_simps) (metis scaleR_left.add)
      then show ?thesis
        by blast
    qed
  } ultimately
  show ?thesis
  unfolding collinear_def affine_hull_2
    by blast
qed

lemma collinear_closed_segment [simp]: "collinear (closed_segment a b)"
  by (metis affine_hull_convex_hull collinear_affine_hull hull_subset segment_convex_hull)

lemma collinear_open_segment [simp]: "collinear (open_segment a b)"
  unfolding open_segment_def
  by (metis convex_hull_subset_affine_hull segment_convex_hull dual_order.trans
      convex_hull_subset_affine_hull Diff_subset collinear_affine_hull)

lemma collinear_between_cases:
  fixes c :: "'a::euclidean_space"
  shows "collinear {a,b,c} \<longleftrightarrow> between (b,c) a \<or> between (c,a) b \<or> between (a,b) c"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain u v where uv: "\<And>x. x \<in> {a, b, c} \<Longrightarrow> \<exists>c. x = u + c *\<^sub>R v"
    by (auto simp: collinear_alt)
  show ?rhs
    using uv [of a] uv [of b] uv [of c] by (auto simp: between_1)
next
  assume ?rhs
  then show ?lhs
    unfolding between_mem_convex_hull
    by (metis (no_types, opaque_lifting) collinear_closed_segment collinear_subset hull_redundant hull_subset insert_commute segment_convex_hull)
qed


lemma subset_continuous_image_segment_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "continuous_on (closed_segment a b) f"
  shows "closed_segment (f a) (f b) \<subseteq> image f (closed_segment a b)"
by (metis connected_segment convex_contains_segment ends_in_segment imageI
           is_interval_connected_1 is_interval_convex connected_continuous_image [OF assms])

lemma continuous_injective_image_segment_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes contf: "continuous_on (closed_segment a b) f"
      and injf: "inj_on f (closed_segment a b)"
  shows "f ` (closed_segment a b) = closed_segment (f a) (f b)"
proof
  show "closed_segment (f a) (f b) \<subseteq> f ` closed_segment a b"
    by (metis subset_continuous_image_segment_1 contf)
  show "f ` closed_segment a b \<subseteq> closed_segment (f a) (f b)"
  proof (cases "a = b")
    case True
    then show ?thesis by auto
  next
    case False
    then have fnot: "f a \<noteq> f b"
      using inj_onD injf by fastforce
    moreover
    have "f a \<notin> open_segment (f c) (f b)" if c: "c \<in> closed_segment a b" for c
    proof (clarsimp simp add: open_segment_def)
      assume fa: "f a \<in> closed_segment (f c) (f b)"
      moreover have "closed_segment (f c) (f b) \<subseteq> f ` closed_segment c b"
        by (meson closed_segment_subset contf continuous_on_subset convex_closed_segment ends_in_segment(2) subset_continuous_image_segment_1 that)
      ultimately have "f a \<in> f ` closed_segment c b"
        by blast
      then have a: "a \<in> closed_segment c b"
        by (meson ends_in_segment inj_on_image_mem_iff injf subset_closed_segment that)
      have cb: "closed_segment c b \<subseteq> closed_segment a b"
        by (simp add: closed_segment_subset that)
      show "f a = f c"
      proof (rule between_antisym)
        show "between (f c, f b) (f a)"
          by (simp add: between_mem_segment fa)
        show "between (f a, f b) (f c)"
          by (metis a cb between_antisym between_mem_segment between_triv1 subset_iff)
      qed
    qed
    moreover
    have "f b \<notin> open_segment (f a) (f c)" if c: "c \<in> closed_segment a b" for c
    proof (clarsimp simp add: open_segment_def fnot eq_commute)
      assume fb: "f b \<in> closed_segment (f a) (f c)"
      moreover have "closed_segment (f a) (f c) \<subseteq> f ` closed_segment a c"
        by (meson contf continuous_on_subset ends_in_segment(1) subset_closed_segment subset_continuous_image_segment_1 that)
      ultimately have "f b \<in> f ` closed_segment a c"
        by blast
      then have b: "b \<in> closed_segment a c"
        by (meson ends_in_segment inj_on_image_mem_iff injf subset_closed_segment that)
      have ca: "closed_segment a c \<subseteq> closed_segment a b"
        by (simp add: closed_segment_subset that)
      show "f b = f c"
      proof (rule between_antisym)
        show "between (f c, f a) (f b)"
          by (simp add: between_commute between_mem_segment fb)
        show "between (f b, f a) (f c)"
          by (metis b between_antisym between_commute between_mem_segment between_triv2 that)
      qed
    qed
    ultimately show ?thesis
      by (force simp: closed_segment_eq_real_ivl open_segment_eq_real_ivl split: if_split_asm)
  qed
qed

lemma continuous_injective_image_open_segment_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes contf: "continuous_on (closed_segment a b) f"
      and injf: "inj_on f (closed_segment a b)"
    shows "f ` (open_segment a b) = open_segment (f a) (f b)"
proof -
  have "f ` (open_segment a b) = f ` (closed_segment a b) - {f a, f b}"
    by (metis (no_types, opaque_lifting) empty_subsetI ends_in_segment image_insert image_is_empty inj_on_image_set_diff injf insert_subset open_segment_def segment_open_subset_closed)
  also have "... = open_segment (f a) (f b)"
    using continuous_injective_image_segment_1 [OF assms]
    by (simp add: open_segment_def inj_on_image_set_diff [OF injf])
  finally show ?thesis .
qed

lemma collinear_imp_coplanar:
  "collinear s ==> coplanar s"
by (metis collinear_affine_hull coplanar_def insert_absorb2)

lemma collinear_small:
  assumes "finite s" "card s \<le> 2"
    shows "collinear s"
proof -
  have "card s = 0 \<or> card s = 1 \<or> card s = 2"
    using assms by linarith
  then show ?thesis using assms
    using card_eq_SucD numeral_2_eq_2 by (force simp: card_1_singleton_iff)
qed

lemma coplanar_small:
  assumes "finite s" "card s \<le> 3"
    shows "coplanar s"
proof -
  consider "card s \<le> 2" | "card s = Suc (Suc (Suc 0))"
    using assms by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp add: \<open>finite s\<close> collinear_imp_coplanar collinear_small)
  next
    case 2
    then show ?thesis
      using hull_subset [of "{_,_,_}"]
      by (fastforce simp: coplanar_def dest!: card_eq_SucD)
  qed
qed

lemma coplanar_empty: "coplanar {}"
  by (simp add: coplanar_small)

lemma coplanar_sing: "coplanar {a}"
  by (simp add: coplanar_small)

lemma coplanar_2: "coplanar {a,b}"
  by (auto simp: card_insert_if coplanar_small)

lemma coplanar_3: "coplanar {a,b,c}"
  by (auto simp: card_insert_if coplanar_small)

lemma collinear_affine_hull_collinear: "collinear(affine hull s) \<longleftrightarrow> collinear s"
  unfolding collinear_affine_hull
  by (metis affine_affine_hull subset_hull hull_hull hull_mono)

lemma coplanar_affine_hull_coplanar: "coplanar(affine hull s) \<longleftrightarrow> coplanar s"
  unfolding coplanar_def
  by (metis affine_affine_hull subset_hull hull_hull hull_mono)

lemma coplanar_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "coplanar S" "linear f" shows "coplanar(f ` S)"
proof -
  { fix u v w
    assume "S \<subseteq> affine hull {u, v, w}"
    then have "f ` S \<subseteq> f ` (affine hull {u, v, w})"
      by (simp add: image_mono)
    then have "f ` S \<subseteq> affine hull (f ` {u, v, w})"
      by (metis assms(2) linear_conv_bounded_linear affine_hull_linear_image)
  } then
  show ?thesis
    by auto (meson assms(1) coplanar_def)
qed

lemma coplanar_translation_imp: 
  assumes "coplanar S" shows "coplanar ((\<lambda>x. a + x) ` S)"
proof -
  obtain u v w where "S \<subseteq> affine hull {u,v,w}"
    by (meson assms coplanar_def)
  then have "(+) a ` S \<subseteq> affine hull {u + a, v + a, w + a}"
    using affine_hull_translation [of a "{u,v,w}" for u v w]
    by (force simp: add.commute)
  then show ?thesis
    unfolding coplanar_def by blast
qed

lemma coplanar_translation_eq: "coplanar((\<lambda>x. a + x) ` S) \<longleftrightarrow> coplanar S"
    by (metis (no_types) coplanar_translation_imp translation_galois)

lemma coplanar_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f" shows "coplanar(f ` S) = coplanar S"
proof
  assume "coplanar S"
  then show "coplanar (f ` S)"
    using assms(1) coplanar_linear_image by blast
next
  obtain g where g: "linear g" "g \<circ> f = id"
    using linear_injective_left_inverse [OF assms]
    by blast
  assume "coplanar (f ` S)"
  then show "coplanar S"
    by (metis coplanar_linear_image g(1) g(2) id_apply image_comp image_id)
qed

lemma coplanar_subset: "\<lbrakk>coplanar t; S \<subseteq> t\<rbrakk> \<Longrightarrow> coplanar S"
  by (meson coplanar_def order_trans)

lemma affine_hull_3_imp_collinear: "c \<in> affine hull {a,b} \<Longrightarrow> collinear {a,b,c}"
  by (metis collinear_2 collinear_affine_hull_collinear hull_redundant insert_commute)

lemma collinear_3_imp_in_affine_hull:
  assumes "collinear {a,b,c}" "a \<noteq> b" shows "c \<in> affine hull {a,b}"
proof -
  obtain u x y where "b - a = y *\<^sub>R u" "c - a = x *\<^sub>R u"
    using assms unfolding collinear_def by auto
  with \<open>a \<noteq> b\<close> have "\<exists>v. c = (1 - x / y) *\<^sub>R a + v *\<^sub>R b \<and> 1 - x / y + v = 1"
    by (simp add: algebra_simps)
  then show ?thesis
    by (simp add: hull_inc mem_affine)
qed

lemma collinear_3_affine_hull:
  assumes "a \<noteq> b"
  shows "collinear {a,b,c} \<longleftrightarrow> c \<in> affine hull {a,b}"
  using affine_hull_3_imp_collinear assms collinear_3_imp_in_affine_hull by blast

lemma collinear_3_eq_affine_dependent:
  "collinear{a,b,c} \<longleftrightarrow> a = b \<or> a = c \<or> b = c \<or> affine_dependent {a,b,c}"
proof (cases "a = b \<or> a = c \<or> b = c")
  case True
  then show ?thesis
    by (auto simp: insert_commute)
next
  case False
  then have "collinear{a,b,c}" if "affine_dependent {a,b,c}"
    using that unfolding affine_dependent_def
    by (auto simp: insert_Diff_if; metis affine_hull_3_imp_collinear insert_commute)
  moreover
  have "affine_dependent {a,b,c}" if "collinear{a,b,c}"
    using False that by (auto simp: affine_dependent_def collinear_3_affine_hull insert_Diff_if)
  ultimately
  show ?thesis
    using False by blast
qed

lemma affine_dependent_imp_collinear_3:
  "affine_dependent {a,b,c} \<Longrightarrow> collinear{a,b,c}"
  by (simp add: collinear_3_eq_affine_dependent)

lemma collinear_3: "NO_MATCH 0 x \<Longrightarrow> collinear {x,y,z} \<longleftrightarrow> collinear {0, x-y, z-y}"
  by (auto simp add: collinear_def)

lemma collinear_3_expand:
   "collinear{a,b,c} \<longleftrightarrow> a = c \<or> (\<exists>u. b = u *\<^sub>R a + (1 - u) *\<^sub>R c)"
proof -
  have "collinear{a,b,c} = collinear{a,c,b}"
    by (simp add: insert_commute)
  also have "... = collinear {0, a - c, b - c}"
    by (simp add: collinear_3)
  also have "... \<longleftrightarrow> (a = c \<or> b = c \<or> (\<exists>ca. b - c = ca *\<^sub>R (a - c)))"
    by (simp add: collinear_lemma)
  also have "... \<longleftrightarrow> a = c \<or> (\<exists>u. b = u *\<^sub>R a + (1 - u) *\<^sub>R c)"
    by (cases "a = c \<or> b = c") (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma collinear_aff_dim: "collinear S \<longleftrightarrow> aff_dim S \<le> 1"
proof
  assume "collinear S"
  then obtain u and v :: "'a" where "aff_dim S \<le> aff_dim {u,v}"
    by (metis \<open>collinear S\<close> aff_dim_affine_hull aff_dim_subset collinear_affine_hull)
  then show "aff_dim S \<le> 1"
    using order_trans by fastforce
next
  assume "aff_dim S \<le> 1"
  then have le1: "aff_dim (affine hull S) \<le> 1"
    by simp
  obtain B where "B \<subseteq> S" and B: "\<not> affine_dependent B" "affine hull S = affine hull B"
    using affine_basis_exists [of S] by auto
  then have "finite B" "card B \<le> 2"
    using B le1 by (auto simp: affine_independent_iff_card)
  then have "collinear B"
    by (rule collinear_small)
  then show "collinear S"
    by (metis \<open>affine hull S = affine hull B\<close> collinear_affine_hull_collinear)
qed

lemma collinear_midpoint: "collinear{a, midpoint a b, b}"
proof -
  have \<section>: "\<lbrakk>a \<noteq> midpoint a b; b - midpoint a b \<noteq> - 1 *\<^sub>R (a - midpoint a b)\<rbrakk> \<Longrightarrow> b = midpoint a b"
    by (simp add: algebra_simps)
  show ?thesis
    by (auto simp: collinear_3 collinear_lemma intro: \<section>)
qed

lemma midpoint_collinear:
  fixes a b c :: "'a::real_normed_vector"
  assumes "a \<noteq> c"
    shows "b = midpoint a c \<longleftrightarrow> collinear{a,b,c} \<and> dist a b = dist b c"
proof -
  have *: "a - (u *\<^sub>R a + (1 - u) *\<^sub>R c) = (1 - u) *\<^sub>R (a - c)"
          "u *\<^sub>R a + (1 - u) *\<^sub>R c - c = u *\<^sub>R (a - c)"
          "\<bar>1 - u\<bar> = \<bar>u\<bar> \<longleftrightarrow> u = 1/2" for u::real
    by (auto simp: algebra_simps)
  have "b = midpoint a c \<Longrightarrow> collinear{a,b,c}"
    using collinear_midpoint by blast
  moreover have "b = midpoint a c \<longleftrightarrow> dist a b = dist b c" if "collinear{a,b,c}"
  proof -
    consider "a = c" | u where "b = u *\<^sub>R a + (1 - u) *\<^sub>R c"
      using \<open>collinear {a,b,c}\<close> unfolding collinear_3_expand by blast
    then show ?thesis
    proof cases
      case 2
      with assms have "dist a b = dist b c \<Longrightarrow> b = midpoint a c"
        by (simp add: dist_norm * midpoint_def scaleR_add_right del: divide_const_simps)
      then show ?thesis
        by (auto simp: dist_midpoint)
    qed (use assms in auto)
  qed
  ultimately show ?thesis by blast
qed

lemma between_imp_collinear:
  fixes x :: "'a :: euclidean_space"
  assumes "between (a,b) x"
    shows "collinear {a,x,b}"
proof (cases "x = a \<or> x = b \<or> a = b")
  case True with assms show ?thesis
    by (auto simp: dist_commute)
next
  case False 
  then have False if "\<And>c. b - x \<noteq> c *\<^sub>R (a - x)"
    using that [of "-(norm(b - x) / norm(x - a))"] assms
    by (simp add: between_norm vector_add_divide_simps flip: real_vector.scale_minus_right)
  then show ?thesis
    by (auto simp: collinear_3 collinear_lemma)
qed

lemma midpoint_between:
  fixes a b :: "'a::euclidean_space"
  shows "b = midpoint a c \<longleftrightarrow> between (a,c) b \<and> dist a b = dist b c"
proof (cases "a = c")
  case False
  show ?thesis
    using False between_imp_collinear between_midpoint(1) midpoint_collinear by blast
qed (auto simp: dist_commute)

lemma collinear_triples:
  assumes "a \<noteq> b"
    shows "collinear(insert a (insert b S)) \<longleftrightarrow> (\<forall>x \<in> S. collinear{a,b,x})"
          (is "?lhs = ?rhs")
proof safe
  fix x
  assume ?lhs and "x \<in> S"
  then show "collinear {a, b, x}"
    using collinear_subset by force
next
  assume ?rhs
  then have "\<forall>x \<in> S. collinear{a,x,b}"
    by (simp add: insert_commute)
  then have *: "\<exists>u. x = u *\<^sub>R a + (1 - u) *\<^sub>R b" if "x \<in> insert a (insert b S)" for x
    using that assms collinear_3_expand by fastforce+
  have "\<exists>c. x - y = c *\<^sub>R (b - a)" 
    if x: "x \<in> insert a (insert b S)" and y: "y \<in> insert a (insert b S)" for x y
  proof -
    obtain u v where "x = u *\<^sub>R a + (1 - u) *\<^sub>R b" "y = v *\<^sub>R a + (1 - v) *\<^sub>R b"
      using "*" x y by presburger
    then have "x - y = (v - u) *\<^sub>R (b - a)"
      by (simp add: scale_left_diff_distrib scale_right_diff_distrib)
    then show ?thesis ..
  qed
  then show ?lhs
    unfolding collinear_def by metis
qed

lemma collinear_4_3:
  assumes "a \<noteq> b"
    shows "collinear {a,b,c,d} \<longleftrightarrow> collinear{a,b,c} \<and> collinear{a,b,d}"
  using collinear_triples [OF assms, of "{c,d}"] by (force simp:)

lemma collinear_3_trans:
  assumes "collinear{a,b,c}" "collinear{b,c,d}" "b \<noteq> c"
    shows "collinear{a,b,d}"
proof -
  have "collinear{b,c,a,d}"
    by (metis (full_types) assms collinear_4_3 insert_commute)
  then show ?thesis
    by (simp add: collinear_subset)
qed

lemma affine_hull_2_alt:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = range (\<lambda>u. a + u *\<^sub>R (b - a))"
proof -
  have 1: "u *\<^sub>R a + v *\<^sub>R b = a + v *\<^sub>R (b - a)" if "u + v = 1" for u v
    using that
    by (simp add: algebra_simps flip: scaleR_add_left)
  have 2: "a + u *\<^sub>R (b - a) = (1 - u) *\<^sub>R a + u *\<^sub>R b" for u
    by (auto simp: algebra_simps)
  show ?thesis
    by (force simp add: affine_hull_2 dest: 1 intro!: 2)
qed

lemma interior_convex_hull_3_minimal:
  fixes a :: "'a::euclidean_space"
  assumes "\<not> collinear{a,b,c}" and 2: "DIM('a) = 2"
  shows "interior(convex hull {a,b,c}) =
         {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1 \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
        (is "?lhs = ?rhs")
proof
  have abc: "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" "\<not> affine_dependent {a, b, c}"
    using assms by (auto simp: collinear_3_eq_affine_dependent)
  with 2 show "?lhs \<subseteq> ?rhs"
    by (fastforce simp add: interior_convex_hull_explicit_minimal)
  show "?rhs \<subseteq> ?lhs"
    using abc 2
    apply (clarsimp simp add: interior_convex_hull_explicit_minimal)
    subgoal for x y z
      by (rule_tac x="\<lambda>r. (if r=a then x else if r=b then y else if r=c then z else 0)" in exI) auto
    done
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Basic lemmas about hyperplanes and halfspaces\<close>

lemma halfspace_Int_eq:
     "{x. a \<bullet> x \<le> b} \<inter> {x. b \<le> a \<bullet> x} = {x. a \<bullet> x = b}"
     "{x. b \<le> a \<bullet> x} \<inter> {x. a \<bullet> x \<le> b} = {x. a \<bullet> x = b}"
  by auto

lemma hyperplane_eq_Ex:
  assumes "a \<noteq> 0" obtains x where "a \<bullet> x = b"
  by (rule_tac x = "(b / (a \<bullet> a)) *\<^sub>R a" in that) (simp add: assms)

lemma hyperplane_eq_empty:
     "{x. a \<bullet> x = b} = {} \<longleftrightarrow> a = 0 \<and> b \<noteq> 0"
  using hyperplane_eq_Ex
  by (metis (mono_tags, lifting) empty_Collect_eq inner_zero_left)

lemma hyperplane_eq_UNIV:
   "{x. a \<bullet> x = b} = UNIV \<longleftrightarrow> a = 0 \<and> b = 0"
proof -
  have "a = 0 \<and> b = 0" if "UNIV \<subseteq> {x. a \<bullet> x = b}"
    using subsetD [OF that, where c = "((b+1) / (a \<bullet> a)) *\<^sub>R a"]
    by (simp add: field_split_simps split: if_split_asm)
  then show ?thesis by force
qed

lemma halfspace_eq_empty_lt:
   "{x. a \<bullet> x < b} = {} \<longleftrightarrow> a = 0 \<and> b \<le> 0"
proof -
  have "a = 0 \<and> b \<le> 0" if "{x. a \<bullet> x < b} \<subseteq> {}"
    using subsetD [OF that, where c = "((b-1) / (a \<bullet> a)) *\<^sub>R a"]
    by (force simp add: field_split_simps split: if_split_asm)
  then show ?thesis by force
qed

lemma halfspace_eq_empty_gt:
  "{x. a \<bullet> x > b} = {} \<longleftrightarrow> a = 0 \<and> b \<ge> 0"
  using halfspace_eq_empty_lt [of "-a" "-b"]
  by simp

lemma halfspace_eq_empty_le:
   "{x. a \<bullet> x \<le> b} = {} \<longleftrightarrow> a = 0 \<and> b < 0"
proof -
  have "a = 0 \<and> b < 0" if "{x. a \<bullet> x \<le> b} \<subseteq> {}"
    using subsetD [OF that, where c = "((b-1) / (a \<bullet> a)) *\<^sub>R a"]
    by (force simp add: field_split_simps split: if_split_asm)
  then show ?thesis by force
qed

lemma halfspace_eq_empty_ge:
  "{x. a \<bullet> x \<ge> b} = {} \<longleftrightarrow> a = 0 \<and> b > 0"
  using halfspace_eq_empty_le [of "-a" "-b"] by simp

subsection\<^marker>\<open>tag unimportant\<close>\<open>Use set distance for an easy proof of separation properties\<close>

proposition\<^marker>\<open>tag unimportant\<close> separation_closures:
  fixes S :: "'a::euclidean_space set"
  assumes "S \<inter> closure T = {}" "T \<inter> closure S = {}"
  obtains U V where "U \<inter> V = {}" "open U" "open V" "S \<subseteq> U" "T \<subseteq> V"
proof (cases "S = {} \<or> T = {}")
  case True with that show ?thesis by auto
next
  case False
  define f where "f \<equiv> \<lambda>x. setdist {x} T - setdist {x} S"
  have contf: "continuous_on UNIV f"
    unfolding f_def by (intro continuous_intros continuous_on_setdist)
  show ?thesis
  proof (rule_tac U = "{x. f x > 0}" and V = "{x. f x < 0}" in that)
    show "{x. 0 < f x} \<inter> {x. f x < 0} = {}"
      by auto
    show "open {x. 0 < f x}"
      by (simp add: open_Collect_less contf)
    show "open {x. f x < 0}"
      by (simp add: open_Collect_less contf)
    have "\<And>x. x \<in> S \<Longrightarrow> setdist {x} T \<noteq> 0" "\<And>x. x \<in> T \<Longrightarrow> setdist {x} S \<noteq> 0"
      by (meson False assms disjoint_iff setdist_eq_0_sing_1)+
    then show "S \<subseteq> {x. 0 < f x}" "T \<subseteq> {x. f x < 0}"
      using less_eq_real_def by (fastforce simp add: f_def setdist_sing_in_set)+
  qed
qed

lemma separation_normal:
  fixes S :: "'a::euclidean_space set"
  assumes "closed S" "closed T" "S \<inter> T = {}"
  obtains U V where "open U" "open V" "S \<subseteq> U" "T \<subseteq> V" "U \<inter> V = {}"
using separation_closures [of S T]
by (metis assms closure_closed disjnt_def inf_commute)

lemma separation_normal_local:
  fixes S :: "'a::euclidean_space set"
  assumes US: "closedin (top_of_set U) S"
      and UT: "closedin (top_of_set U) T"
      and "S \<inter> T = {}"
  obtains S' T' where "openin (top_of_set U) S'"
                      "openin (top_of_set U) T'"
                      "S \<subseteq> S'"  "T \<subseteq> T'"  "S' \<inter> T' = {}"
proof (cases "S = {} \<or> T = {}")
  case True with that show ?thesis
    using UT US by (blast dest: closedin_subset)
next
  case False
  define f where "f \<equiv> \<lambda>x. setdist {x} T - setdist {x} S"
  have contf: "continuous_on U f"
    unfolding f_def by (intro continuous_intros)
  show ?thesis
  proof (rule_tac S' = "(U \<inter> f -` {0<..})" and T' = "(U \<inter> f -` {..<0})" in that)
    show "(U \<inter> f -` {0<..}) \<inter> (U \<inter> f -` {..<0}) = {}"
      by auto
    show "openin (top_of_set U) (U \<inter> f -` {0<..})"
      by (rule continuous_openin_preimage [where T=UNIV]) (simp_all add: contf)
  next
    show "openin (top_of_set U) (U \<inter> f -` {..<0})"
      by (rule continuous_openin_preimage [where T=UNIV]) (simp_all add: contf)
  next
    have "S \<subseteq> U" "T \<subseteq> U"
      using closedin_imp_subset assms by blast+
    then show "S \<subseteq> U \<inter> f -` {0<..}" "T \<subseteq> U \<inter> f -` {..<0}"
      using assms False by (force simp add: f_def setdist_sing_in_set intro!: setdist_gt_0_closedin)+
  qed
qed

lemma separation_normal_compact:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "closed T" "S \<inter> T = {}"
  obtains U V where "open U" "compact(closure U)" "open V" "S \<subseteq> U" "T \<subseteq> V" "U \<inter> V = {}"
proof -
  have "closed S" "bounded S"
    using assms by (auto simp: compact_eq_bounded_closed)
  then obtain r where "r>0" and r: "S \<subseteq> ball 0 r"
    by (auto dest!: bounded_subset_ballD)
  have **: "closed (T \<union> - ball 0 r)" "S \<inter> (T \<union> - ball 0 r) = {}"
    using assms r by blast+
  then obtain U V where UV: "open U" "open V" "S \<subseteq> U" "T \<union> - ball 0 r \<subseteq> V" "U \<inter> V = {}"
    by (meson  \<open>closed S\<close> separation_normal)
  then have "compact(closure U)"
    by (meson bounded_ball bounded_subset compact_closure compl_le_swap2 disjoint_eq_subset_Compl le_sup_iff)
  with UV show thesis
    using that by auto
qed

subsection\<open>Connectedness of the intersection of a chain\<close>

proposition connected_chain:
  fixes \<F> :: "'a :: euclidean_space set set"
  assumes cc: "\<And>S. S \<in> \<F> \<Longrightarrow> compact S \<and> connected S"
      and linear: "\<And>S T. S \<in> \<F> \<and> T \<in> \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
  shows "connected(\<Inter>\<F>)"
proof (cases "\<F> = {}")
  case True then show ?thesis
    by auto
next
  case False
  then have cf: "compact(\<Inter>\<F>)"
    by (simp add: cc compact_Inter)
  have False if AB: "closed A" "closed B" "A \<inter> B = {}"
                and ABeq: "A \<union> B = \<Inter>\<F>" and "A \<noteq> {}" "B \<noteq> {}" for A B
  proof -
    obtain U V where "open U" "open V" "A \<subseteq> U" "B \<subseteq> V" "U \<inter> V = {}"
      using separation_normal [OF AB] by metis
    obtain K where "K \<in> \<F>" "compact K"
      using cc False by blast
    then obtain N where "open N" and "K \<subseteq> N"
      by blast
    let ?\<C> = "insert (U \<union> V) ((\<lambda>S. N - S) ` \<F>)"
    obtain \<D> where "\<D> \<subseteq> ?\<C>" "finite \<D>" "K \<subseteq> \<Union>\<D>"
    proof (rule compactE [OF \<open>compact K\<close>])
      show "K \<subseteq> \<Union>(insert (U \<union> V) ((-) N ` \<F>))"
        using \<open>K \<subseteq> N\<close> ABeq \<open>A \<subseteq> U\<close> \<open>B \<subseteq> V\<close> by auto
      show "\<And>B. B \<in> insert (U \<union> V) ((-) N ` \<F>) \<Longrightarrow> open B"
        by (auto simp:  \<open>open U\<close> \<open>open V\<close> open_Un \<open>open N\<close> cc compact_imp_closed open_Diff)
    qed
    then have "finite(\<D> - {U \<union> V})"
      by blast
    moreover have "\<D> - {U \<union> V} \<subseteq> (\<lambda>S. N - S) ` \<F>"
      using \<open>\<D> \<subseteq> ?\<C>\<close> by blast
    ultimately obtain \<G> where "\<G> \<subseteq> \<F>" "finite \<G>" and Deq: "\<D> - {U \<union> V} = (\<lambda>S. N-S) ` \<G>"
      using finite_subset_image by metis
    obtain J where "J \<in> \<F>" and J: "(\<Union>S\<in>\<G>. N - S) \<subseteq> N - J"
    proof (cases "\<G> = {}")
      case True
      with \<open>\<F> \<noteq> {}\<close> that show ?thesis
        by auto
    next
      case False
      have "\<And>S T. \<lbrakk>S \<in> \<G>; T \<in> \<G>\<rbrakk> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
        by (meson \<open>\<G> \<subseteq> \<F>\<close> in_mono local.linear)
      with \<open>finite \<G>\<close> \<open>\<G> \<noteq> {}\<close>
      have "\<exists>J \<in> \<G>. (\<Union>S\<in>\<G>. N - S) \<subseteq> N - J"
      proof induction
        case (insert X \<H>)
        show ?case
        proof (cases "\<H> = {}")
          case True then show ?thesis by auto
        next
          case False
          then have "\<And>S T. \<lbrakk>S \<in> \<H>; T \<in> \<H>\<rbrakk> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
            by (simp add: insert.prems)
          with insert.IH False obtain J where "J \<in> \<H>" and J: "(\<Union>Y\<in>\<H>. N - Y) \<subseteq> N - J"
            by metis
          have "N - J \<subseteq> N - X \<or> N - X \<subseteq> N - J"
            by (meson Diff_mono \<open>J \<in> \<H>\<close> insert.prems(2) insert_iff order_refl)
          then show ?thesis
          proof
            assume "N - J \<subseteq> N - X" with J show ?thesis
              by auto
          next
            assume "N - X \<subseteq> N - J"
            with J have "N - X \<union> \<Union> ((-) N ` \<H>) \<subseteq> N - J"
              by auto
            with \<open>J \<in> \<H>\<close> show ?thesis
              by blast
          qed
        qed
      qed simp
      with \<open>\<G> \<subseteq> \<F>\<close> show ?thesis by (blast intro: that)
    qed
    have "K \<subseteq> \<Union>(insert (U \<union> V) (\<D> - {U \<union> V}))"
      using \<open>K \<subseteq> \<Union>\<D>\<close> by auto
    also have "... \<subseteq> (U \<union> V) \<union> (N - J)"
      by (metis (no_types, opaque_lifting) Deq Un_subset_iff Un_upper2 J Union_insert order_trans sup_ge1)
    finally have "J \<inter> K \<subseteq> U \<union> V"
      by blast
    moreover have "connected(J \<inter> K)"
      by (metis Int_absorb1 \<open>J \<in> \<F>\<close> \<open>K \<in> \<F>\<close> cc inf.orderE local.linear)
    moreover have "U \<inter> (J \<inter> K) \<noteq> {}"
      using ABeq \<open>J \<in> \<F>\<close> \<open>K \<in> \<F>\<close> \<open>A \<noteq> {}\<close> \<open>A \<subseteq> U\<close> by blast
    moreover have "V \<inter> (J \<inter> K) \<noteq> {}"
      using ABeq \<open>J \<in> \<F>\<close> \<open>K \<in> \<F>\<close> \<open>B \<noteq> {}\<close> \<open>B \<subseteq> V\<close> by blast
    ultimately show False
        using connectedD [of "J \<inter> K" U V] \<open>open U\<close> \<open>open V\<close> \<open>U \<inter> V = {}\<close>  by auto
  qed
  with cf show ?thesis
    by (auto simp: connected_closed_set compact_imp_closed)
qed

lemma connected_chain_gen:
  fixes \<F> :: "'a :: euclidean_space set set"
  assumes X: "X \<in> \<F>" "compact X"
      and cc: "\<And>T. T \<in> \<F> \<Longrightarrow> closed T \<and> connected T"
      and linear: "\<And>S T. S \<in> \<F> \<and> T \<in> \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
  shows "connected(\<Inter>\<F>)"
proof -
  have "\<Inter>\<F> = (\<Inter>T\<in>\<F>. X \<inter> T)"
    using X by blast
  moreover have "connected (\<Inter>T\<in>\<F>. X \<inter> T)"
  proof (rule connected_chain)
    show "\<And>T. T \<in> (\<inter>) X ` \<F> \<Longrightarrow> compact T \<and> connected T"
      using cc X by auto (metis inf.absorb2 inf.orderE local.linear)
    show "\<And>S T. S \<in> (\<inter>) X ` \<F> \<and> T \<in> (\<inter>) X ` \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
      using local.linear by blast
  qed
  ultimately show ?thesis
    by metis
qed

lemma connected_nest:
  fixes S :: "'a::linorder \<Rightarrow> 'b::euclidean_space set"
  assumes S: "\<And>n. compact(S n)" "\<And>n. connected(S n)"
    and nest: "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
  shows "connected(\<Inter> (range S))"
proof (rule connected_chain)
  show "\<And>A T. A \<in> range S \<and> T \<in> range S \<Longrightarrow> A \<subseteq> T \<or> T \<subseteq> A"
  by (metis image_iff le_cases nest)
qed (use S in blast)

lemma connected_nest_gen:
  fixes S :: "'a::linorder \<Rightarrow> 'b::euclidean_space set"
  assumes S: "\<And>n. closed(S n)" "\<And>n. connected(S n)" "compact(S k)"
    and nest: "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
  shows "connected(\<Inter> (range S))"
proof (rule connected_chain_gen [of "S k"])
  show "\<And>A T. A \<in> range S \<and> T \<in> range S \<Longrightarrow> A \<subseteq> T \<or> T \<subseteq> A"
    by (metis imageE le_cases nest)
qed (use S in auto)

subsection\<open>Proper maps, including projections out of compact sets\<close>

lemma finite_indexed_bound:
  assumes A: "finite A" "\<And>x. x \<in> A \<Longrightarrow> \<exists>n::'a::linorder. P x n"
    shows "\<exists>m. \<forall>x \<in> A. \<exists>k\<le>m. P x k"
using A
proof (induction A)
  case empty then show ?case by force
next
  case (insert a A)
    then obtain m n where "\<forall>x \<in> A. \<exists>k\<le>m. P x k" "P a n"
      by force
    then show ?case
      by (metis dual_order.trans insert_iff le_cases)
qed

proposition proper_map:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b::heine_borel"
  assumes "closedin (top_of_set S) K"
      and com: "\<And>U. \<lbrakk>U \<subseteq> T; compact U\<rbrakk> \<Longrightarrow> compact (S \<inter> f -` U)"
      and "f ` S \<subseteq> T"
    shows "closedin (top_of_set T) (f ` K)"
proof -
  have "K \<subseteq> S"
    using assms closedin_imp_subset by metis
  obtain C where "closed C" and Keq: "K = S \<inter> C"
    using assms by (auto simp: closedin_closed)
  have *: "y \<in> f ` K" if "y \<in> T" and y: "y islimpt f ` K" for y
  proof -
    obtain h where "\<forall>n. (\<exists>x\<in>K. h n = f x) \<and> h n \<noteq> y" "inj h" and hlim: "(h \<longlongrightarrow> y) sequentially"
      using \<open>y \<in> T\<close> y by (force simp: limpt_sequential_inj)
    then obtain X where X: "\<And>n. X n \<in> K \<and> h n = f (X n) \<and> h n \<noteq> y"
      by metis
    then have fX: "\<And>n. f (X n) = h n"
      by metis
    define \<Psi> where "\<Psi> \<equiv> \<lambda>n. {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (n + i))))}"
    have "compact (C \<inter> (S \<inter> f -` insert y (range (\<lambda>i. f(X(n + i))))))" for n
    proof (intro closed_Int_compact [OF \<open>closed C\<close> com] compact_sequence_with_limit)
      show "insert y (range (\<lambda>i. f (X (n + i)))) \<subseteq> T"
        using X \<open>K \<subseteq> S\<close> \<open>f ` S \<subseteq> T\<close> \<open>y \<in> T\<close> by blast
      show "(\<lambda>i. f (X (n + i))) \<longlonglongrightarrow> y"
        by (simp add: fX add.commute [of n] LIMSEQ_ignore_initial_segment [OF hlim])
    qed
    then have comf: "compact (\<Psi> n)" for n
      by (simp add: Keq Int_def \<Psi>_def conj_commute)
    have ne: "\<Inter>\<F> \<noteq> {}"
             if "finite \<F>"
                and \<F>: "\<And>t. t \<in> \<F> \<Longrightarrow> (\<exists>n. t = \<Psi> n)"
             for \<F>
    proof -
      obtain m where m: "\<And>t. t \<in> \<F> \<Longrightarrow> \<exists>k\<le>m. t = \<Psi> k"
        by (rule exE [OF finite_indexed_bound [OF \<open>finite \<F>\<close> \<F>]], force+)
      have "X m \<in> \<Inter>\<F>"
        using X le_Suc_ex by (fastforce simp: \<Psi>_def dest: m)
      then show ?thesis by blast
    qed
    have "(\<Inter>n. \<Psi> n) \<noteq> {}"
    proof (rule compact_fip_Heine_Borel)
      show "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> range \<Psi>\<rbrakk> \<Longrightarrow> \<Inter> \<F>' \<noteq> {}"
        by (meson ne rangeE subset_eq)
    qed (use comf in blast)
    then obtain x where "x \<in> K" "\<And>n. (f x = y \<or> (\<exists>u. f x = h (n + u)))"
      by (force simp add: \<Psi>_def fX)
    then show ?thesis
      unfolding image_iff by (metis \<open>inj h\<close> le_add1 not_less_eq_eq rangeI range_ex1_eq)
  qed
  with assms closedin_subset show ?thesis
    by (force simp: closedin_limpt)
qed


lemma compact_continuous_image_eq:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b::heine_borel"
  assumes f: "inj_on f S"
  shows "continuous_on S f \<longleftrightarrow> (\<forall>T. compact T \<and> T \<subseteq> S \<longrightarrow> compact(f ` T))"
           (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis continuous_on_subset compact_continuous_image)
next
  assume RHS: ?rhs
  obtain g where gf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    by (metis inv_into_f_f f)
  then have *: "(S \<inter> f -` U) = g ` U" if "U \<subseteq> f ` S" for U
    using that by fastforce
  have gfim: "g ` f ` S \<subseteq> S" using gf by auto
  have **: "compact (f ` S \<inter> g -` C)" if C: "C \<subseteq> S" "compact C" for C
  proof -
    obtain h where "h C \<in> C \<and> h C \<notin> S \<or> compact (f ` C)"
      by (force simp: C RHS)
    moreover have "f ` C = (f ` S \<inter> g -` C)"
      using C gf by auto
    ultimately show ?thesis
      using C by auto
  qed
  show ?lhs
    using proper_map [OF _ _ gfim] **
    by (simp add: continuous_on_closed * closedin_imp_subset)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Trivial fact: convexity equals connectedness for collinear sets\<close>

lemma convex_connected_collinear:
  fixes S :: "'a::euclidean_space set"
  assumes "collinear S"
    shows "convex S \<longleftrightarrow> connected S"
proof
  assume "convex S"
  then show "connected S"
    using convex_connected by blast
next
  assume S: "connected S"
  show "convex S"
  proof (cases "S = {}")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain a where "a \<in> S" by auto
    have "collinear (affine hull S)"
      by (simp add: assms collinear_affine_hull_collinear)
    then obtain z where "z \<noteq> 0" "\<And>x. x \<in> affine hull S \<Longrightarrow> \<exists>c. x - a = c *\<^sub>R z"
      by (meson \<open>a \<in> S\<close> collinear hull_inc)
    then obtain f where f: "\<And>x. x \<in> affine hull S \<Longrightarrow> x - a = f x *\<^sub>R z"
      by metis
    then have inj_f: "inj_on f (affine hull S)"
      by (metis diff_add_cancel inj_onI)
    have diff: "x - y = (f x - f y) *\<^sub>R z" if x: "x \<in> affine hull S" and y: "y \<in> affine hull S" for x y
    proof -
      have "f x *\<^sub>R z = x - a"
        by (simp add: f hull_inc x)
      moreover have "f y *\<^sub>R z = y - a"
        by (simp add: f hull_inc y)
      ultimately show ?thesis
        by (simp add: scaleR_left.diff)
    qed
    have cont_f: "continuous_on (affine hull S) f"
    proof (clarsimp simp: dist_norm continuous_on_iff diff)
      show "\<And>x e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>y \<in> affine hull S. \<bar>f y - f x\<bar> * norm z < d \<longrightarrow> \<bar>f y - f x\<bar> < e"
        by (metis \<open>z \<noteq> 0\<close> mult_pos_pos mult_less_iff1 zero_less_norm_iff)
    qed
    then have conn_fS: "connected (f ` S)"
      by (meson S connected_continuous_image continuous_on_subset hull_subset)
    show ?thesis
    proof (clarsimp simp: convex_contains_segment)
      fix x y z
      assume "x \<in> S" "y \<in> S" "z \<in> closed_segment x y"
      have False if "z \<notin> S"
      proof -
        have "f ` (closed_segment x y) = closed_segment (f x) (f y)"
        proof (rule continuous_injective_image_segment_1)
          show "continuous_on (closed_segment x y) f"
            by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc continuous_on_subset [OF cont_f])
          show "inj_on f (closed_segment x y)"
            by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc inj_on_subset [OF inj_f])
        qed
        then have fz: "f z \<in> closed_segment (f x) (f y)"
          using \<open>z \<in> closed_segment x y\<close> by blast
        have "z \<in> affine hull S"
          by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>z \<in> closed_segment x y\<close> convex_affine_hull convex_contains_segment hull_inc subset_eq)
        then have fz_notin: "f z \<notin> f ` S"
          using hull_subset inj_f inj_onD that by fastforce
        moreover have "{..<f z} \<inter> f ` S \<noteq> {}" "{f z<..} \<inter> f ` S \<noteq> {}"
        proof -
          consider "f x \<le> f z \<and> f z \<le> f y" | "f y \<le> f z \<and> f z \<le> f x"
            using fz
            by (auto simp add: closed_segment_eq_real_ivl split: if_split_asm)
          then have "{..<f z} \<inter> f ` {x,y} \<noteq> {} \<and> {f z<..} \<inter> f ` {x,y} \<noteq> {}"
            by cases (use fz_notin \<open>x \<in> S\<close> \<open>y \<in> S\<close> in \<open>auto simp: image_iff\<close>)
          then show "{..<f z} \<inter> f ` S \<noteq> {}" "{f z<..} \<inter> f ` S \<noteq> {}"
            using \<open>x \<in> S\<close> \<open>y \<in> S\<close> by blast+
        qed
        ultimately show False
          using connectedD [OF conn_fS, of "{..<f z}" "{f z<..}"] by force
      qed
      then show "z \<in> S" by meson
    qed
  qed
qed

lemma compact_convex_collinear_segment_alt:
  fixes S :: "'a::euclidean_space set"
  assumes "S \<noteq> {}" "compact S" "connected S" "collinear S"
  obtains a b where "S = closed_segment a b"
proof -
  obtain \<xi> where "\<xi> \<in> S" using \<open>S \<noteq> {}\<close> by auto
  have "collinear (affine hull S)"
    by (simp add: assms collinear_affine_hull_collinear)
  then obtain z where "z \<noteq> 0" "\<And>x. x \<in> affine hull S \<Longrightarrow> \<exists>c. x - \<xi> = c *\<^sub>R z"
    by (meson \<open>\<xi> \<in> S\<close> collinear hull_inc)
  then obtain f where f: "\<And>x. x \<in> affine hull S \<Longrightarrow> x - \<xi> = f x *\<^sub>R z"
    by metis
  let ?g = "\<lambda>r. r *\<^sub>R z + \<xi>"
  have gf: "?g (f x) = x" if "x \<in> affine hull S" for x
    by (metis diff_add_cancel f that)
  then have inj_f: "inj_on f (affine hull S)"
    by (metis inj_onI)
  have diff: "x - y = (f x - f y) *\<^sub>R z" if x: "x \<in> affine hull S" and y: "y \<in> affine hull S" for x y
  proof -
    have "f x *\<^sub>R z = x - \<xi>"
      by (simp add: f hull_inc x)
    moreover have "f y *\<^sub>R z = y - \<xi>"
      by (simp add: f hull_inc y)
    ultimately show ?thesis
      by (simp add: scaleR_left.diff)
  qed
  have cont_f: "continuous_on (affine hull S) f"
  proof (clarsimp simp: dist_norm continuous_on_iff diff)
    show "\<And>x e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>y \<in> affine hull S. \<bar>f y  - f x\<bar> * norm z < d \<longrightarrow> \<bar>f y  - f x\<bar> < e"
      by (metis \<open>z \<noteq> 0\<close> mult_pos_pos mult_less_iff1 zero_less_norm_iff)
  qed
  then have "connected (f ` S)"
    by (meson \<open>connected S\<close> connected_continuous_image continuous_on_subset hull_subset)
  moreover have "compact (f ` S)"
    by (meson \<open>compact S\<close> compact_continuous_image_eq cont_f hull_subset inj_f)
  ultimately obtain x y where "f ` S = {x..y}"
    by (meson connected_compact_interval_1)
  then have fS_eq: "f ` S = closed_segment x y"
    using \<open>S \<noteq> {}\<close> closed_segment_eq_real_ivl by auto
  obtain a b where "a \<in> S" "f a = x" "b \<in> S" "f b = y"
    by (metis (full_types) ends_in_segment fS_eq imageE)
  have "f ` (closed_segment a b) = closed_segment (f a) (f b)"
  proof (rule continuous_injective_image_segment_1)
    show "continuous_on (closed_segment a b) f"
      by (meson \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc continuous_on_subset [OF cont_f])
    show "inj_on f (closed_segment a b)"
      by (meson \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc inj_on_subset [OF inj_f])
  qed
  then have "f ` (closed_segment a b) = f ` S"
    by (simp add: \<open>f a = x\<close> \<open>f b = y\<close> fS_eq)
  then have "?g ` f ` (closed_segment a b) = ?g ` f ` S"
    by simp
  moreover have "(\<lambda>x. f x *\<^sub>R z + \<xi>) ` closed_segment a b = closed_segment a b"
    unfolding image_def using \<open>a \<in> S\<close> \<open>b \<in> S\<close>
    by (safe; metis (mono_tags, lifting)  convex_affine_hull convex_contains_segment gf hull_subset subsetCE)
  ultimately have "closed_segment a b = S"
    using gf by (simp add: image_comp o_def hull_inc cong: image_cong)
  then show ?thesis
    using that by blast
qed

lemma compact_convex_collinear_segment:
  fixes S :: "'a::euclidean_space set"
  assumes "S \<noteq> {}" "compact S" "convex S" "collinear S"
  obtains a b where "S = closed_segment a b"
  using assms convex_connected_collinear compact_convex_collinear_segment_alt by blast


lemma proper_map_from_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and imf: "f ` S \<subseteq> T" and "compact S"
          "closedin (top_of_set T) K"
  shows "compact (S \<inter> f -` K)"
by (rule closedin_compact [OF \<open>compact S\<close>] continuous_closedin_preimage_gen assms)+

lemma proper_map_fst:
  assumes "compact T" "K \<subseteq> S" "compact K"
    shows "compact (S \<times> T \<inter> fst -` K)"
proof -
  have "(S \<times> T \<inter> fst -` K) = K \<times> T"
    using assms by auto
  then show ?thesis by (simp add: assms compact_Times)
qed

lemma closed_map_fst:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact T" "closedin (top_of_set (S \<times> T)) c"
   shows "closedin (top_of_set S) (fst ` c)"
proof -
  have *: "fst ` (S \<times> T) \<subseteq> S"
    by auto
  show ?thesis
    using proper_map [OF _ _ *] by (simp add: proper_map_fst assms)
qed

lemma proper_map_snd:
  assumes "compact S" "K \<subseteq> T" "compact K"
    shows "compact (S \<times> T \<inter> snd -` K)"
proof -
  have "(S \<times> T \<inter> snd -` K) = S \<times> K"
    using assms by auto
  then show ?thesis by (simp add: assms compact_Times)
qed

lemma closed_map_snd:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact S" "closedin (top_of_set (S \<times> T)) c"
   shows "closedin (top_of_set T) (snd ` c)"
proof -
  have *: "snd ` (S \<times> T) \<subseteq> T"
    by auto
  show ?thesis
    using proper_map [OF _ _ *] by (simp add: proper_map_snd assms)
qed

lemma closedin_compact_projection:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact S" and clo: "closedin (top_of_set (S \<times> T)) U"
    shows "closedin (top_of_set T) {y. \<exists>x. x \<in> S \<and> (x, y) \<in> U}"
proof -
  have "U \<subseteq> S \<times> T"
    by (metis clo closedin_imp_subset)
  then have "{y. \<exists>x. x \<in> S \<and> (x, y) \<in> U} = snd ` U"
    by force
  moreover have "closedin (top_of_set T) (snd ` U)"
    by (rule closed_map_snd [OF assms])
  ultimately show ?thesis
    by simp
qed


lemma closed_compact_projection:
  fixes S :: "'a::euclidean_space set"
    and T :: "('a * 'b::euclidean_space) set"
  assumes "compact S" and clo: "closed T"
    shows "closed {y. \<exists>x. x \<in> S \<and> (x, y) \<in> T}"
proof -
  have *: "{y. \<exists>x. x \<in> S \<and> Pair x y \<in> T} = {y. \<exists>x. x \<in> S \<and> Pair x y \<in> ((S \<times> UNIV) \<inter> T)}"
    by auto
  show ?thesis
    unfolding *
    by (intro clo closedin_closed_Int closedin_closed_trans [OF _ closed_UNIV] closedin_compact_projection [OF \<open>compact S\<close>])
qed

subsubsection\<^marker>\<open>tag unimportant\<close>\<open>Representing affine hull as a finite intersection of hyperplanes\<close>

proposition\<^marker>\<open>tag unimportant\<close> affine_hull_convex_Int_nonempty_interior:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "S \<inter> interior T \<noteq> {}"
    shows "affine hull (S \<inter> T) = affine hull S"
proof
  show "affine hull (S \<inter> T) \<subseteq> affine hull S"
    by (simp add: hull_mono)
next
  obtain a where "a \<in> S" "a \<in> T" and at: "a \<in> interior T"
    using assms interior_subset by blast
  then obtain e where "e > 0" and e: "cball a e \<subseteq> T"
    using mem_interior_cball by blast
  have *: "x \<in> (+) a ` span ((\<lambda>x. x - a) ` (S \<inter> T))" if "x \<in> S" for x
  proof (cases "x = a")
    case True with that span_0 eq_add_iff image_def mem_Collect_eq show ?thesis
      by blast
  next
    case False
    define k where "k = min (1/2) (e / norm (x-a))"
    have k: "0 < k" "k < 1"
      using \<open>e > 0\<close> False by (auto simp: k_def)
    then have xa: "(x-a) = inverse k *\<^sub>R k *\<^sub>R (x-a)"
      by simp
    have "e / norm (x - a) \<ge> k"
      using k_def by linarith
    then have "a + k *\<^sub>R (x - a) \<in> cball a e"
      using \<open>0 < k\<close> False
      by (simp add: dist_norm) (simp add: field_simps)
    then have T: "a + k *\<^sub>R (x - a) \<in> T"
      using e by blast
    have S: "a + k *\<^sub>R (x - a) \<in> S"
      using k \<open>a \<in> S\<close> convexD [OF \<open>convex S\<close> \<open>a \<in> S\<close> \<open>x \<in> S\<close>, of "1-k" k]
      by (simp add: algebra_simps)
    have "inverse k *\<^sub>R k *\<^sub>R (x-a) \<in> span ((\<lambda>x. x - a) ` (S \<inter> T))"
      by (intro span_mul [OF span_base] image_eqI [where x = "a + k *\<^sub>R (x - a)"]) (auto simp: S T)
    with xa image_iff show ?thesis  by fastforce
  qed
  have "S \<subseteq> affine hull (S \<inter> T)"
    by (force simp: * \<open>a \<in> S\<close> \<open>a \<in> T\<close> hull_inc affine_hull_span_gen [of a])
  then show "affine hull S \<subseteq> affine hull (S \<inter> T)"
    by (simp add: subset_hull)
qed

corollary affine_hull_convex_Int_open:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "open T" "S \<inter> T \<noteq> {}"
  shows "affine hull (S \<inter> T) = affine hull S"
  using affine_hull_convex_Int_nonempty_interior assms interior_eq by blast

corollary affine_hull_affine_Int_nonempty_interior:
  fixes S :: "'a::real_normed_vector set"
  assumes "affine S" "S \<inter> interior T \<noteq> {}"
  shows "affine hull (S \<inter> T) = affine hull S"
  by (simp add: affine_hull_convex_Int_nonempty_interior affine_imp_convex assms)

corollary affine_hull_affine_Int_open:
  fixes S :: "'a::real_normed_vector set"
  assumes "affine S" "open T" "S \<inter> T \<noteq> {}"
  shows "affine hull (S \<inter> T) = affine hull S"
  by (simp add: affine_hull_convex_Int_open affine_imp_convex assms)

corollary affine_hull_convex_Int_openin:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "openin (top_of_set (affine hull S)) T" "S \<inter> T \<noteq> {}"
  shows "affine hull (S \<inter> T) = affine hull S"
  using assms unfolding openin_open
  by (metis affine_hull_convex_Int_open hull_subset inf.orderE inf_assoc)

corollary affine_hull_openin:
  fixes S :: "'a::real_normed_vector set"
  assumes "openin (top_of_set (affine hull T)) S" "S \<noteq> {}"
  shows "affine hull S = affine hull T"
  using assms unfolding openin_open
  by (metis affine_affine_hull affine_hull_affine_Int_open hull_hull)

corollary affine_hull_open:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S" "S \<noteq> {}"
  shows "affine hull S = UNIV"
  by (metis affine_hull_convex_Int_nonempty_interior assms convex_UNIV hull_UNIV inf_top.left_neutral interior_open)

lemma aff_dim_convex_Int_nonempty_interior:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>convex S; S \<inter> interior T \<noteq> {}\<rbrakk> \<Longrightarrow> aff_dim(S \<inter> T) = aff_dim S"
  using aff_dim_affine_hull2 affine_hull_convex_Int_nonempty_interior by blast

lemma aff_dim_convex_Int_open:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>convex S; open T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow>  aff_dim(S \<inter> T) = aff_dim S"
  using aff_dim_convex_Int_nonempty_interior interior_eq by blast

lemma affine_hull_Diff:
  fixes S:: "'a::real_normed_vector set"
  assumes ope: "openin (top_of_set (affine hull S)) S" and "finite F" "F \<subset> S"
  shows "affine hull (S - F) = affine hull S"
proof -
  have clo: "closedin (top_of_set S) F"
    using assms finite_imp_closedin by auto
  moreover have "S - F \<noteq> {}"
    using assms by auto
  ultimately show ?thesis
    by (metis ope closedin_def topspace_euclidean_subtopology affine_hull_openin openin_trans)
qed

lemma affine_hull_halfspace_lt:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x < r} = (if a = 0 \<and> r \<le> 0 then {} else UNIV)"
using halfspace_eq_empty_lt [of a r]
by (simp add: open_halfspace_lt affine_hull_open)

lemma affine_hull_halfspace_le:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x \<le> r} = (if a = 0 \<and> r < 0 then {} else UNIV)"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  then have "affine hull closure {x. a \<bullet> x < r} = UNIV"
    using affine_hull_halfspace_lt closure_same_affine_hull by fastforce
  moreover have "{x. a \<bullet> x < r} \<subseteq> {x. a \<bullet> x \<le> r}"
    by (simp add: Collect_mono)
  ultimately show ?thesis using False antisym_conv hull_mono top_greatest
    by (metis affine_hull_halfspace_lt)
qed

lemma affine_hull_halfspace_gt:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x > r} = (if a = 0 \<and> r \<ge> 0 then {} else UNIV)"
using halfspace_eq_empty_gt [of r a]
by (simp add: open_halfspace_gt affine_hull_open)

lemma affine_hull_halfspace_ge:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x \<ge> r} = (if a = 0 \<and> r > 0 then {} else UNIV)"
using affine_hull_halfspace_le [of "-a" "-r"] by simp

lemma aff_dim_halfspace_lt:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x < r} =
        (if a = 0 \<and> r \<le> 0 then -1 else DIM('a))"
by simp (metis aff_dim_open halfspace_eq_empty_lt open_halfspace_lt)

lemma aff_dim_halfspace_le:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x \<le> r} =
        (if a = 0 \<and> r < 0 then -1 else DIM('a))"
proof -
  have "int (DIM('a)) = aff_dim (UNIV::'a set)"
    by (simp)
  then have "aff_dim (affine hull {x. a \<bullet> x \<le> r}) = DIM('a)" if "(a = 0 \<longrightarrow> r \<ge> 0)"
    using that by (simp add: affine_hull_halfspace_le not_less)
  then show ?thesis
    by (force)
qed

lemma aff_dim_halfspace_gt:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x > r} =
        (if a = 0 \<and> r \<ge> 0 then -1 else DIM('a))"
by simp (metis aff_dim_open halfspace_eq_empty_gt open_halfspace_gt)

lemma aff_dim_halfspace_ge:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x \<ge> r} =
        (if a = 0 \<and> r > 0 then -1 else DIM('a))"
using aff_dim_halfspace_le [of "-a" "-r"] by simp

proposition aff_dim_eq_hyperplane:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S = DIM('a) - 1 \<longleftrightarrow> (\<exists>a b. a \<noteq> 0 \<and> affine hull S = {x. a \<bullet> x = b})"
  (is "?lhs = ?rhs")
proof (cases "S = {}")
  case True then show ?thesis
    by (auto simp: dest: hyperplane_eq_Ex)
next
  case False
  then obtain c where "c \<in> S" by blast
  show ?thesis
  proof (cases "c = 0")
    case True 
    have "?lhs \<longleftrightarrow> (\<exists>a. a \<noteq> 0 \<and> span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = 0})"
      by (simp add: aff_dim_eq_dim [of c] \<open>c \<in> S\<close> hull_inc dim_eq_hyperplane del: One_nat_def)
    also have "... \<longleftrightarrow> ?rhs"
      using span_zero [of S] True \<open>c \<in> S\<close> affine_hull_span_0 hull_inc  
      by (fastforce simp add: affine_hull_span_gen [of c] \<open>c = 0\<close>)
    finally show ?thesis .
  next
    case False
    have xc_im: "x \<in> (+) c ` {y. a \<bullet> y = 0}" if "a \<bullet> x = a \<bullet> c" for a x
    proof -
      have "\<exists>y. a \<bullet> y = 0 \<and> c + y = x"
        by (metis that add.commute diff_add_cancel inner_commute inner_diff_left right_minus_eq)
      then show "x \<in> (+) c ` {y. a \<bullet> y = 0}"
        by blast
    qed
    have 2: "span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = 0}"
         if "(+) c ` span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = b}" for a b
    proof -
      have "b = a \<bullet> c"
        using span_0 that by fastforce
      with that have "(+) c ` span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = a \<bullet> c}"
        by simp
      then have "span ((\<lambda>x. x - c) ` S) = (\<lambda>x. x - c) ` {x. a \<bullet> x = a \<bullet> c}"
        by (metis (no_types) image_cong translation_galois uminus_add_conv_diff)
      also have "... = {x. a \<bullet> x = 0}"
        by (force simp: inner_distrib inner_diff_right
             intro: image_eqI [where x="x+c" for x])
      finally show ?thesis .
    qed
    have "?lhs = (\<exists>a. a \<noteq> 0 \<and> span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = 0})"
      by (simp add: aff_dim_eq_dim [of c] \<open>c \<in> S\<close> hull_inc dim_eq_hyperplane del: One_nat_def)
    also have "... = ?rhs"
      by (fastforce simp add: affine_hull_span_gen [of c] \<open>c \<in> S\<close> hull_inc inner_distrib intro: xc_im intro!: 2)
    finally show ?thesis .
  qed
qed

corollary aff_dim_hyperplane [simp]:
  fixes a :: "'a::euclidean_space"
  shows "a \<noteq> 0 \<Longrightarrow> aff_dim {x. a \<bullet> x = r} = DIM('a) - 1"
by (metis aff_dim_eq_hyperplane affine_hull_eq affine_hyperplane)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Some stepping theorems\<close>

lemma aff_dim_insert:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim (insert a S) = (if a \<in> affine hull S then aff_dim S else aff_dim S + 1)"
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain x s' where S: "S = insert x s'" "x \<notin> s'"
    by (meson Set.set_insert all_not_in_conv)
  show ?thesis using S
    by (force simp add: affine_hull_insert_span_gen span_zero insert_commute [of a] aff_dim_eq_dim [of x] dim_insert)
qed

lemma affine_dependent_choose:
  fixes a :: "'a :: euclidean_space"
  assumes "\<not>(affine_dependent S)"
  shows "affine_dependent(insert a S) \<longleftrightarrow> a \<notin> S \<and> a \<in> affine hull S"
        (is "?lhs = ?rhs")
proof safe
  assume "affine_dependent (insert a S)" and "a \<in> S"
  then show "False"
    using \<open>a \<in> S\<close> assms insert_absorb by fastforce
next
  assume lhs: "affine_dependent (insert a S)"
  then have "a \<notin> S"
    by (metis (no_types) assms insert_absorb)
  moreover have "finite S"
    using affine_independent_iff_card assms by blast
  moreover have "aff_dim (insert a S) \<noteq> int (card S)"
    using \<open>finite S\<close> affine_independent_iff_card \<open>a \<notin> S\<close> lhs by fastforce
  ultimately show "a \<in> affine hull S"
    by (metis aff_dim_affine_independent aff_dim_insert assms)
next
  assume "a \<notin> S" and "a \<in> affine hull S"
  show "affine_dependent (insert a S)"
    by (simp add: \<open>a \<in> affine hull S\<close> \<open>a \<notin> S\<close> affine_dependent_def)
qed

lemma affine_independent_insert:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>\<not> affine_dependent S; a \<notin> affine hull S\<rbrakk> \<Longrightarrow> \<not> affine_dependent(insert a S)"
  by (simp add: affine_dependent_choose)

lemma subspace_bounded_eq_trivial:
  fixes S :: "'a::real_normed_vector set"
  assumes "subspace S"
    shows "bounded S \<longleftrightarrow> S = {0}"
proof -
  have "False" if "bounded S" "x \<in> S" "x \<noteq> 0" for x
  proof -
    obtain B where B: "\<And>y. y \<in> S \<Longrightarrow> norm y < B" "B > 0"
      using \<open>bounded S\<close> by (force simp: bounded_pos_less)
    have "(B / norm x) *\<^sub>R x \<in> S"
      using assms subspace_mul \<open>x \<in> S\<close> by auto
    moreover have "norm ((B / norm x) *\<^sub>R x) = B"
      using that B by (simp add: algebra_simps)
    ultimately show False using B by force
  qed
  then have "bounded S \<Longrightarrow> S = {0}"
    using assms subspace_0 by fastforce
  then show ?thesis
    by blast
qed

lemma affine_bounded_eq_trivial:
  fixes S :: "'a::real_normed_vector set"
  assumes "affine S"
    shows "bounded S \<longleftrightarrow> S = {} \<or> (\<exists>a. S = {a})"
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain b where "b \<in> S" by blast
  with False assms 
  have "bounded S \<Longrightarrow> S = {b}"
    using affine_diffs_subspace [OF assms \<open>b \<in> S\<close>]
    by (metis (no_types, lifting) ab_group_add_class.ab_left_minus bounded_translation image_empty image_insert subspace_bounded_eq_trivial translation_invert)
  then show ?thesis by auto
qed

lemma affine_bounded_eq_lowdim:
  fixes S :: "'a::euclidean_space set"
  assumes "affine S"
  shows "bounded S \<longleftrightarrow> aff_dim S \<le> 0"
proof
  show "aff_dim S \<le> 0 \<Longrightarrow> bounded S"
  by (metis aff_dim_sing aff_dim_subset affine_dim_equal affine_sing all_not_in_conv assms bounded_empty bounded_insert dual_order.antisym empty_subsetI insert_subset)
qed (use affine_bounded_eq_trivial assms in fastforce)


lemma bounded_hyperplane_eq_trivial_0:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
  shows "bounded {x. a \<bullet> x = 0} \<longleftrightarrow> DIM('a) = 1"
proof
  assume "bounded {x. a \<bullet> x = 0}"
  then have "aff_dim {x. a \<bullet> x = 0} \<le> 0"
    by (simp add: affine_bounded_eq_lowdim affine_hyperplane)
  with assms show "DIM('a) = 1"
    by (simp add: le_Suc_eq)
next
  assume "DIM('a) = 1"
  then show "bounded {x. a \<bullet> x = 0}"
    by (simp add: affine_bounded_eq_lowdim affine_hyperplane assms)
qed

lemma bounded_hyperplane_eq_trivial:
  fixes a :: "'a::euclidean_space"
  shows "bounded {x. a \<bullet> x = r} \<longleftrightarrow> (if a = 0 then r \<noteq> 0 else DIM('a) = 1)"
proof (simp add: bounded_hyperplane_eq_trivial_0, clarify)
  assume "r \<noteq> 0" "a \<noteq> 0"
  have "aff_dim {x. y \<bullet> x = 0} = aff_dim {x. a \<bullet> x = r}" if "y \<noteq> 0" for y::'a
    by (metis that \<open>a \<noteq> 0\<close> aff_dim_hyperplane)
  then show "bounded {x. a \<bullet> x = r} = (DIM('a) = Suc 0)"
    by (metis One_nat_def \<open>a \<noteq> 0\<close> affine_bounded_eq_lowdim affine_hyperplane bounded_hyperplane_eq_trivial_0)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>General case without assuming closure and getting non-strict separation\<close>

proposition\<^marker>\<open>tag unimportant\<close> separating_hyperplane_closed_point_inset:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "closed S" "S \<noteq> {}" "z \<notin> S"
  obtains a b where "a \<in> S" "(a - z) \<bullet> z < b" "\<And>x. x \<in> S \<Longrightarrow> b < (a - z) \<bullet> x"
proof -
  obtain y where "y \<in> S" and y: "\<And>u. u \<in> S \<Longrightarrow> dist z y \<le> dist z u"
    using distance_attains_inf [of S z] assms by auto
  then have *: "(y - z) \<bullet> z < (y - z) \<bullet> z + (norm (y - z))\<^sup>2 / 2"
    using \<open>y \<in> S\<close> \<open>z \<notin> S\<close> by auto
  show ?thesis
  proof (rule that [OF \<open>y \<in> S\<close> *])
    fix x
    assume "x \<in> S"
    have yz: "0 < (y - z) \<bullet> (y - z)"
      using \<open>y \<in> S\<close> \<open>z \<notin> S\<close> by auto
    { assume 0: "0 < ((z - y) \<bullet> (x - y))"
      with any_closest_point_dot [OF \<open>convex S\<close> \<open>closed S\<close>]
      have False
        using y \<open>x \<in> S\<close> \<open>y \<in> S\<close> not_less by blast
    }
    then have "0 \<le> ((y - z) \<bullet> (x - y))"
      by (force simp: not_less inner_diff_left)
    with yz have "0 < 2 * ((y - z) \<bullet> (x - y)) + (y - z) \<bullet> (y - z)"
      by (simp add: algebra_simps)
    then show "(y - z) \<bullet> z + (norm (y - z))\<^sup>2 / 2 < (y - z) \<bullet> x"
      by (simp add: field_simps inner_diff_left inner_diff_right dot_square_norm [symmetric])
  qed
qed

lemma separating_hyperplane_closed_0_inset:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "closed S" "S \<noteq> {}" "0 \<notin> S"
  obtains a b where "a \<in> S" "a \<noteq> 0" "0 < b" "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x > b"
  using separating_hyperplane_closed_point_inset [OF assms] by simp (metis \<open>0 \<notin> S\<close>)


proposition\<^marker>\<open>tag unimportant\<close> separating_hyperplane_set_0_inspan:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" "0 \<notin> S"
  obtains a where "a \<in> span S" "a \<noteq> 0" "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> a \<bullet> x"
proof -
  define k where [abs_def]: "k c = {x. 0 \<le> c \<bullet> x}" for c :: 'a
  have "span S \<inter> frontier (cball 0 1) \<inter> \<Inter>f' \<noteq> {}"
          if f': "finite f'" "f' \<subseteq> k ` S" for f'
  proof -
    obtain C where "C \<subseteq> S" "finite C" and C: "f' = k ` C"
      using finite_subset_image [OF f'] by blast
    obtain a where "a \<in> S" "a \<noteq> 0"
      using \<open>S \<noteq> {}\<close> \<open>0 \<notin> S\<close> ex_in_conv by blast
    then have "norm (a /\<^sub>R (norm a)) = 1"
      by simp
    moreover have "a /\<^sub>R (norm a) \<in> span S"
      by (simp add: \<open>a \<in> S\<close> span_scale span_base)
    ultimately have ass: "a /\<^sub>R (norm a) \<in> span S \<inter> sphere 0 1"
      by simp
    show ?thesis
    proof (cases "C = {}")
      case True with C ass show ?thesis
        by auto
    next
      case False
      have "closed (convex hull C)"
        using \<open>finite C\<close> compact_eq_bounded_closed finite_imp_compact_convex_hull by auto
      moreover have "convex hull C \<noteq> {}"
        by (simp add: False)
      moreover have "0 \<notin> convex hull C"
        by (metis \<open>C \<subseteq> S\<close> \<open>convex S\<close> \<open>0 \<notin> S\<close> convex_hull_subset hull_same insert_absorb insert_subset)
      ultimately obtain a b
            where "a \<in> convex hull C" "a \<noteq> 0" "0 < b"
                  and ab: "\<And>x. x \<in> convex hull C \<Longrightarrow> a \<bullet> x > b"
        using separating_hyperplane_closed_0_inset by blast
      then have "a \<in> S"
        by (metis \<open>C \<subseteq> S\<close> assms(1) subsetCE subset_hull)
      moreover have "norm (a /\<^sub>R (norm a)) = 1"
        using \<open>a \<noteq> 0\<close> by simp
      moreover have "a /\<^sub>R (norm a) \<in> span S"
        by (simp add: \<open>a \<in> S\<close> span_scale span_base)
      ultimately have ass: "a /\<^sub>R (norm a) \<in> span S \<inter> sphere 0 1"
        by simp
      have "\<And>x. \<lbrakk>a \<noteq> 0; x \<in> C\<rbrakk> \<Longrightarrow> 0 \<le> x \<bullet> a"
        using ab \<open>0 < b\<close> by (metis hull_inc inner_commute less_eq_real_def less_trans)
      then have aa: "a /\<^sub>R (norm a) \<in> (\<Inter>c\<in>C. {x. 0 \<le> c \<bullet> x})"
        by (auto simp add: field_split_simps)
      show ?thesis
        unfolding C k_def
        using ass aa Int_iff empty_iff by force
    qed
  qed
  moreover have "\<And>T. T \<in> k ` S \<Longrightarrow> closed T"
    using closed_halfspace_ge k_def by blast
  ultimately have "(span S \<inter> frontier(cball 0 1)) \<inter> (\<Inter> (k ` S)) \<noteq> {}"
    by (metis compact_imp_fip closed_Int_compact closed_span compact_cball compact_frontier)
  then show ?thesis
    unfolding set_eq_iff k_def
    by simp (metis inner_commute norm_eq_zero that zero_neq_one)
qed


lemma separating_hyperplane_set_point_inaff:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" and zno: "z \<notin> S"
  obtains a b where "(z + a) \<in> affine hull (insert z S)"
                and "a \<noteq> 0" and "a \<bullet> z \<le> b"
                and "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b"
proof -
  from separating_hyperplane_set_0_inspan [of "image (\<lambda>x. -z + x) S"]
  have "convex ((+) (- z) ` S)"
    using \<open>convex S\<close> by simp
  moreover have "(+) (- z) ` S \<noteq> {}"
    by (simp add: \<open>S \<noteq> {}\<close>)
  moreover have "0 \<notin> (+) (- z) ` S"
    using zno by auto
  ultimately obtain a where "a \<in> span ((+) (- z) ` S)" "a \<noteq> 0"
                  and a:  "\<And>x. x \<in> ((+) (- z) ` S) \<Longrightarrow> 0 \<le> a \<bullet> x"
    using separating_hyperplane_set_0_inspan [of "image (\<lambda>x. -z + x) S"]
    by blast
  then have szx: "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> z \<le> a \<bullet> x"
    by (metis (no_types, lifting) imageI inner_minus_right inner_right_distrib minus_add neg_le_0_iff_le neg_le_iff_le real_add_le_0_iff)
  moreover
  have "z + a \<in> affine hull insert z S"
    using \<open>a \<in> span ((+) (- z) ` S)\<close> affine_hull_insert_span_gen by blast
  ultimately show ?thesis
    using \<open>a \<noteq> 0\<close> szx that by auto
qed

proposition\<^marker>\<open>tag unimportant\<close> supporting_hyperplane_rel_boundary:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> S" and xno: "x \<notin> rel_interior S"
  obtains a where "a \<noteq> 0"
              and "\<And>y. y \<in> S \<Longrightarrow> a \<bullet> x \<le> a \<bullet> y"
              and "\<And>y. y \<in> rel_interior S \<Longrightarrow> a \<bullet> x < a \<bullet> y"
proof -
  obtain a b where aff: "(x + a) \<in> affine hull (insert x (rel_interior S))"
                  and "a \<noteq> 0" and "a \<bullet> x \<le> b"
                  and ageb: "\<And>u. u \<in> (rel_interior S) \<Longrightarrow> a \<bullet> u \<ge> b"
    using separating_hyperplane_set_point_inaff [of "rel_interior S" x] assms
    by (auto simp: rel_interior_eq_empty convex_rel_interior)
  have le_ay: "a \<bullet> x \<le> a \<bullet> y" if "y \<in> S" for y
  proof -
    have con: "continuous_on (closure (rel_interior S)) ((\<bullet>) a)"
      by (rule continuous_intros continuous_on_subset | blast)+
    have y: "y \<in> closure (rel_interior S)"
      using \<open>convex S\<close> closure_def convex_closure_rel_interior \<open>y \<in> S\<close>
      by fastforce
    show ?thesis
      using continuous_ge_on_closure [OF con y] ageb \<open>a \<bullet> x \<le> b\<close>
      by fastforce
  qed
  have 3: "a \<bullet> x < a \<bullet> y" if "y \<in> rel_interior S" for y
  proof -
    obtain e where "0 < e" "y \<in> S" and e: "cball y e \<inter> affine hull S \<subseteq> S"
      using \<open>y \<in> rel_interior S\<close> by (force simp: rel_interior_cball)
    define y' where "y' = y - (e / norm a) *\<^sub>R ((x + a) - x)"
    have "y' \<in> cball y e"
      unfolding y'_def using \<open>0 < e\<close> by force
    moreover have "y' \<in> affine hull S"
      unfolding y'_def
      by (metis \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>convex S\<close> aff affine_affine_hull hull_redundant
                rel_interior_same_affine_hull hull_inc mem_affine_3_minus2)
    ultimately have "y' \<in> S"
      using e by auto
    have "a \<bullet> x \<le> a \<bullet> y"
      using le_ay \<open>a \<noteq> 0\<close> \<open>y \<in> S\<close> by blast
    moreover have "a \<bullet> x \<noteq> a \<bullet> y"
      using le_ay [OF \<open>y' \<in> S\<close>] \<open>a \<noteq> 0\<close> \<open>0 < e\<close> not_le
      by (fastforce simp add: y'_def inner_diff dot_square_norm power2_eq_square)
    ultimately show ?thesis by force
  qed
  show ?thesis
    by (rule that [OF \<open>a \<noteq> 0\<close> le_ay 3])
qed

lemma supporting_hyperplane_relative_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> closure S" "x \<notin> rel_interior S"
  obtains a where "a \<noteq> 0"
              and "\<And>y. y \<in> closure S \<Longrightarrow> a \<bullet> x \<le> a \<bullet> y"
              and "\<And>y. y \<in> rel_interior S \<Longrightarrow> a \<bullet> x < a \<bullet> y"
using supporting_hyperplane_rel_boundary [of "closure S" x]
by (metis assms convex_closure convex_rel_interior_closure)


subsection\<^marker>\<open>tag unimportant\<close>\<open> Some results on decomposing convex hulls: intersections, simplicial subdivision\<close>

lemma
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent(S \<union> T)"
    shows convex_hull_Int_subset: "convex hull S \<inter> convex hull T \<subseteq> convex hull (S \<inter> T)" (is ?C)
      and affine_hull_Int_subset: "affine hull S \<inter> affine hull T \<subseteq> affine hull (S \<inter> T)" (is ?A)
proof -
  have [simp]: "finite S" "finite T"
    using aff_independent_finite assms by blast+
    have "sum u (S \<inter> T) = 1 \<and>
          (\<Sum>v\<in>S \<inter> T. u v *\<^sub>R v) = (\<Sum>v\<in>S. u v *\<^sub>R v)"
      if [simp]:  "sum u S = 1"
                 "sum v T = 1"
         and eq: "(\<Sum>x\<in>T. v x *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)" for u v
    proof -
      define f where "f x = (if x \<in> S then u x else 0) - (if x \<in> T then v x else 0)" for x
      have "sum f (S \<union> T) = 0"
        by (simp add: f_def sum_Un sum_subtractf flip: sum.inter_restrict)
      moreover have "(\<Sum>x\<in>(S \<union> T). f x *\<^sub>R x) = 0"
        by (simp add: eq f_def sum_Un scaleR_left_diff_distrib sum_subtractf if_smult flip: sum.inter_restrict cong: if_cong)
      ultimately have "\<And>v. v \<in> S \<union> T \<Longrightarrow> f v = 0"
        using aff_independent_finite assms unfolding affine_dependent_explicit
        by blast
      then have u [simp]: "\<And>x. x \<in> S \<Longrightarrow> u x = (if x \<in> T then v x else 0)"
        by (simp add: f_def) presburger
      have "sum u (S \<inter> T) = sum u S"
        by (simp add: sum.inter_restrict)
      then have "sum u (S \<inter> T) = 1"
        using that by linarith
      moreover have "(\<Sum>v\<in>S \<inter> T. u v *\<^sub>R v) = (\<Sum>v\<in>S. u v *\<^sub>R v)"
      by (auto simp: if_smult sum.inter_restrict intro: sum.cong)
    ultimately show ?thesis
      by force
    qed
    then show ?A ?C
      by (auto simp: convex_hull_finite affine_hull_finite)
qed


proposition\<^marker>\<open>tag unimportant\<close> affine_hull_Int:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent(S \<union> T)"
    shows "affine hull (S \<inter> T) = affine hull S \<inter> affine hull T"
  by (simp add: affine_hull_Int_subset assms hull_mono subset_antisym)

proposition\<^marker>\<open>tag unimportant\<close> convex_hull_Int:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent(S \<union> T)"
    shows "convex hull (S \<inter> T) = convex hull S \<inter> convex hull T"
  by (simp add: convex_hull_Int_subset assms hull_mono subset_antisym)

proposition\<^marker>\<open>tag unimportant\<close>
  fixes S :: "'a::euclidean_space set set"
  assumes "\<not> affine_dependent (\<Union>S)"
    shows affine_hull_Inter: "affine hull (\<Inter>S) = (\<Inter>T\<in>S. affine hull T)" (is "?A")
      and convex_hull_Inter: "convex hull (\<Inter>S) = (\<Inter>T\<in>S. convex hull T)" (is "?C")
proof -
  have "finite S"
    using aff_independent_finite assms finite_UnionD by blast
  then have "?A \<and> ?C" using assms
  proof (induction S rule: finite_induct)
    case empty then show ?case by auto
  next
    case (insert T F)
    then show ?case
    proof (cases "F={}")
      case True then show ?thesis by simp
    next
      case False
      with "insert.prems" have [simp]: "\<not> affine_dependent (T \<union> \<Inter>F)"
        by (auto intro: affine_dependent_subset)
      have [simp]: "\<not> affine_dependent (\<Union>F)"
        using affine_independent_subset insert.prems by fastforce
      show ?thesis
        by (simp add: affine_hull_Int convex_hull_Int insert.IH)
    qed
  qed
  then show "?A" "?C"
    by auto
qed

proposition\<^marker>\<open>tag unimportant\<close> in_convex_hull_exchange_unique:
  fixes S :: "'a::euclidean_space set"
  assumes naff: "\<not> affine_dependent S" and a: "a \<in> convex hull S"
      and S: "T \<subseteq> S" "T' \<subseteq> S"
      and x:  "x \<in> convex hull (insert a T)"
      and x': "x \<in> convex hull (insert a T')"
    shows "x \<in> convex hull (insert a (T \<inter> T'))"
proof (cases "a \<in> S")
  case True
  then have "\<not> affine_dependent (insert a T \<union> insert a T')"
    using affine_dependent_subset assms by auto
  then have "x \<in> convex hull (insert a T \<inter> insert a T')"
    by (metis IntI convex_hull_Int x x')
  then show ?thesis
    by simp
next
  case False
  then have anot: "a \<notin> T" "a \<notin> T'"
    using assms by auto
  have [simp]: "finite S"
    by (simp add: aff_independent_finite assms)
  then obtain b where b0: "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> b s"
                  and b1: "sum b S = 1" and aeq: "a = (\<Sum>s\<in>S. b s *\<^sub>R s)"
    using a by (auto simp: convex_hull_finite)
  have fin [simp]: "finite T" "finite T'"
    using assms infinite_super \<open>finite S\<close> by blast+
  then obtain c c' where c0: "\<And>t. t \<in> insert a T \<Longrightarrow> 0 \<le> c t"
                     and c1: "sum c (insert a T) = 1"
                     and xeq: "x = (\<Sum>t \<in> insert a T. c t *\<^sub>R t)"
                     and c'0: "\<And>t. t \<in> insert a T' \<Longrightarrow> 0 \<le> c' t"
                     and c'1: "sum c' (insert a T') = 1"
                     and x'eq: "x = (\<Sum>t \<in> insert a T'. c' t *\<^sub>R t)"
    using x x' by (auto simp: convex_hull_finite)
  with fin anot
  have sumTT': "sum c T = 1 - c a" "sum c' T' = 1 - c' a"
   and wsumT: "(\<Sum>t \<in> T. c t *\<^sub>R t) = x - c a *\<^sub>R a"
    by simp_all
  have wsumT': "(\<Sum>t \<in> T'. c' t *\<^sub>R t) = x - c' a *\<^sub>R a"
    using x'eq fin anot by simp
  define cc  where "cc \<equiv> \<lambda>x. if x \<in> T then c x else 0"
  define cc' where "cc' \<equiv> \<lambda>x. if x \<in> T' then c' x else 0"
  define dd  where "dd \<equiv> \<lambda>x. cc x - cc' x + (c a - c' a) * b x"
  have sumSS': "sum cc S = 1 - c a" "sum cc' S = 1 - c' a"
    unfolding cc_def cc'_def  using S
    by (simp_all add: Int_absorb1 Int_absorb2 sum_subtractf sum.inter_restrict [symmetric] sumTT')
  have wsumSS: "(\<Sum>t \<in> S. cc t *\<^sub>R t) = x - c a *\<^sub>R a" "(\<Sum>t \<in> S. cc' t *\<^sub>R t) = x - c' a *\<^sub>R a"
    unfolding cc_def cc'_def  using S
    by (simp_all add: Int_absorb1 Int_absorb2 if_smult sum.inter_restrict [symmetric] wsumT wsumT' cong: if_cong)
  have sum_dd0: "sum dd S = 0"
    unfolding dd_def  using S
    by (simp add: sumSS' comm_monoid_add_class.sum.distrib sum_subtractf
                  algebra_simps sum_distrib_right [symmetric] b1)
  have "(\<Sum>v\<in>S. (b v * x) *\<^sub>R v) = x *\<^sub>R (\<Sum>v\<in>S. b v *\<^sub>R v)" for x
    by (simp add: pth_5 real_vector.scale_sum_right mult.commute)
  then have *: "(\<Sum>v\<in>S. (b v * x) *\<^sub>R v) = x *\<^sub>R a" for x
    using aeq by blast
  have "(\<Sum>v \<in> S. dd v *\<^sub>R v) = 0"
    unfolding dd_def using S
    by (simp add: * wsumSS sum.distrib sum_subtractf algebra_simps)
  then have dd0: "dd v = 0" if "v \<in> S" for v
    using naff [unfolded affine_dependent_explicit not_ex, rule_format, of S dd]
    using that sum_dd0 by force
  consider "c' a \<le> c a" | "c a \<le> c' a" by linarith
  then show ?thesis
  proof cases
    case 1
    then have "sum cc S \<le> sum cc' S"
      by (simp add: sumSS')
    then have le: "cc x \<le> cc' x" if "x \<in> S" for x
      using dd0 [OF that] 1 b0 mult_left_mono that
      by (fastforce simp add: dd_def algebra_simps)
    have cc0: "cc x = 0" if "x \<in> S" "x \<notin> T \<inter> T'" for x
      using le [OF \<open>x \<in> S\<close>] that c0
      by (force simp: cc_def cc'_def split: if_split_asm)
    show ?thesis
    proof (simp add: convex_hull_finite, intro exI conjI)
      show "\<forall>x\<in>T \<inter> T'. 0 \<le> (cc(a := c a)) x"
        by (simp add: c0 cc_def)
      show "0 \<le> (cc(a := c a)) a"
        by (simp add: c0)
      have "sum (cc(a := c a)) (insert a (T \<inter> T')) = c a + sum (cc(a := c a)) (T \<inter> T')"
        by (simp add: anot)
      also have "... = c a + sum (cc(a := c a)) S"
        using \<open>T \<subseteq> S\<close> False cc0 cc_def \<open>a \<notin> S\<close> by (fastforce intro!: sum.mono_neutral_left split: if_split_asm)
      also have "... = c a + (1 - c a)"
        by (metis \<open>a \<notin> S\<close> fun_upd_other sum.cong sumSS'(1))
      finally show "sum (cc(a := c a)) (insert a (T \<inter> T')) = 1"
        by simp
      have "(\<Sum>x\<in>insert a (T \<inter> T'). (cc(a := c a)) x *\<^sub>R x) = c a *\<^sub>R a + (\<Sum>x \<in> T \<inter> T'. (cc(a := c a)) x *\<^sub>R x)"
        by (simp add: anot)
      also have "... = c a *\<^sub>R a + (\<Sum>x \<in> S. (cc(a := c a)) x *\<^sub>R x)"
        using \<open>T \<subseteq> S\<close> False cc0 by (fastforce intro!: sum.mono_neutral_left split: if_split_asm)
      also have "... = c a *\<^sub>R a + x - c a *\<^sub>R a"
        by (simp add: wsumSS \<open>a \<notin> S\<close> if_smult sum_delta_notmem)
      finally show "(\<Sum>x\<in>insert a (T \<inter> T'). (cc(a := c a)) x *\<^sub>R x) = x"
        by simp
    qed
  next
    case 2
    then have "sum cc' S \<le> sum cc S"
      by (simp add: sumSS')
    then have le: "cc' x \<le> cc x" if "x \<in> S" for x
      using dd0 [OF that] 2 b0 mult_left_mono that
      by (fastforce simp add: dd_def algebra_simps)
    have cc0: "cc' x = 0" if "x \<in> S" "x \<notin> T \<inter> T'" for x
      using le [OF \<open>x \<in> S\<close>] that c'0
      by (force simp: cc_def cc'_def split: if_split_asm)
    show ?thesis
    proof (simp add: convex_hull_finite, intro exI conjI)
      show "\<forall>x\<in>T \<inter> T'. 0 \<le> (cc'(a := c' a)) x"
        by (simp add: c'0 cc'_def)
      show "0 \<le> (cc'(a := c' a)) a"
        by (simp add: c'0)
      have "sum (cc'(a := c' a)) (insert a (T \<inter> T')) = c' a + sum (cc'(a := c' a)) (T \<inter> T')"
        by (simp add: anot)
      also have "... = c' a + sum (cc'(a := c' a)) S"
        using \<open>T \<subseteq> S\<close> False cc0 by (fastforce intro!: sum.mono_neutral_left split: if_split_asm)
      also have "... = c' a + (1 - c' a)"
        by (metis \<open>a \<notin> S\<close> fun_upd_other sum.cong sumSS')
      finally show "sum (cc'(a := c' a)) (insert a (T \<inter> T')) = 1"
        by simp
      have "(\<Sum>x\<in>insert a (T \<inter> T'). (cc'(a := c' a)) x *\<^sub>R x) = c' a *\<^sub>R a + (\<Sum>x \<in> T \<inter> T'. (cc'(a := c' a)) x *\<^sub>R x)"
        by (simp add: anot)
      also have "... = c' a *\<^sub>R a + (\<Sum>x \<in> S. (cc'(a := c' a)) x *\<^sub>R x)"
        using \<open>T \<subseteq> S\<close> False cc0 by (fastforce intro!: sum.mono_neutral_left split: if_split_asm)
      also have "... = c a *\<^sub>R a + x - c a *\<^sub>R a"
        by (simp add: wsumSS \<open>a \<notin> S\<close> if_smult sum_delta_notmem)
      finally show "(\<Sum>x\<in>insert a (T \<inter> T'). (cc'(a := c' a)) x *\<^sub>R x) = x"
        by simp
    qed
  qed
qed

corollary\<^marker>\<open>tag unimportant\<close> convex_hull_exchange_Int:
  fixes a  :: "'a::euclidean_space"
  assumes "\<not> affine_dependent S" "a \<in> convex hull S" "T \<subseteq> S" "T' \<subseteq> S"
  shows "(convex hull (insert a T)) \<inter> (convex hull (insert a T')) =
         convex hull (insert a (T \<inter> T'))" (is "?lhs = ?rhs")
proof (rule subset_antisym)
  show "?lhs \<subseteq> ?rhs"
    using in_convex_hull_exchange_unique assms by blast
  show "?rhs \<subseteq> ?lhs"
    by (metis hull_mono inf_le1 inf_le2 insert_inter_insert le_inf_iff)
qed

lemma Int_closed_segment:
  fixes b :: "'a::euclidean_space"
  assumes "b \<in> closed_segment a c \<or> \<not> collinear{a,b,c}"
    shows "closed_segment a b \<inter> closed_segment b c = {b}"
proof (cases "c = a")
  case True
  then show ?thesis
    using assms collinear_3_eq_affine_dependent by fastforce
next
  case False
  from assms show ?thesis
  proof
    assume "b \<in> closed_segment a c"
    moreover have "\<not> affine_dependent {a, c}"
      by (simp)
    ultimately show ?thesis
      using False convex_hull_exchange_Int [of "{a,c}" b "{a}" "{c}"]
      by (simp add: segment_convex_hull insert_commute)
  next
    assume ncoll: "\<not> collinear {a, b, c}"
    have False if "closed_segment a b \<inter> closed_segment b c \<noteq> {b}"
    proof -
      have "b \<in> closed_segment a b" and "b \<in> closed_segment b c"
        by auto
      with that obtain d where "b \<noteq> d" "d \<in> closed_segment a b" "d \<in> closed_segment b c"
        by force
      then have d: "collinear {a, d, b}"  "collinear {b, d, c}"
        by (auto simp:  between_mem_segment between_imp_collinear)
      have "collinear {a, b, c}"
        by (metis (full_types) \<open>b \<noteq> d\<close> collinear_3_trans d insert_commute)
      with ncoll show False ..
    qed
    then show ?thesis
      by blast
  qed
qed

lemma affine_hull_finite_intersection_hyperplanes:
  fixes S :: "'a::euclidean_space set"
  obtains \<F> where
     "finite \<F>"
     "of_nat (card \<F>) + aff_dim S = DIM('a)"
     "affine hull S = \<Inter>\<F>"
     "\<And>h. h \<in> \<F> \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x = b}"
proof -
  obtain b where "b \<subseteq> S"
             and indb: "\<not> affine_dependent b"
             and eq: "affine hull S = affine hull b"
    using affine_basis_exists by blast
  obtain c where indc: "\<not> affine_dependent c" and "b \<subseteq> c"
             and affc: "affine hull c = UNIV"
    by (metis extend_to_affine_basis affine_UNIV hull_same indb subset_UNIV)
  then have "finite c"
    by (simp add: aff_independent_finite)
  then have fbc: "finite b" "card b \<le> card c"
    using \<open>b \<subseteq> c\<close> infinite_super by (auto simp: card_mono)
  have imeq: "(\<lambda>x. affine hull x) ` ((\<lambda>a. c - {a}) ` (c - b)) = ((\<lambda>a. affine hull (c - {a})) ` (c - b))"
    by blast
  have card_cb: "(card (c - b)) + aff_dim S = DIM('a)"
  proof -
    have aff: "aff_dim (UNIV::'a set) = aff_dim c"
      by (metis aff_dim_affine_hull affc)
    have "aff_dim b = aff_dim S"
      by (metis (no_types) aff_dim_affine_hull eq)
    then have "int (card b) = 1 + aff_dim S"
      by (simp add: aff_dim_affine_independent indb)
    then show ?thesis
      using fbc aff
      by (simp add: \<open>\<not> affine_dependent c\<close> \<open>b \<subseteq> c\<close> aff_dim_affine_independent card_Diff_subset of_nat_diff)
  qed
  show ?thesis
  proof (cases "c = b")
    case True show ?thesis
    proof
      show "int (card {}) + aff_dim S = int DIM('a)"
        using True card_cb by auto
      show "affine hull S = \<Inter> {}"
        using True affc eq by blast
    qed auto
  next
    case False
    have ind: "\<not> affine_dependent (\<Union>a\<in>c - b. c - {a})"
      by (rule affine_independent_subset [OF indc]) auto
    have *: "1 + aff_dim (c - {t}) = int (DIM('a))" if t: "t \<in> c" for t
    proof -
      have "insert t c = c"
        using t by blast
      then show ?thesis
        by (metis (full_types) add.commute aff_dim_affine_hull aff_dim_insert aff_dim_UNIV affc affine_dependent_def indc insert_Diff_single t)
    qed
    let ?\<F> = "(\<lambda>x. affine hull x) ` ((\<lambda>a. c - {a}) ` (c - b))"
    show ?thesis
    proof
      have "card ((\<lambda>a. affine hull (c - {a})) ` (c - b)) = card (c - b)"
      proof (rule card_image)
        show "inj_on (\<lambda>a. affine hull (c - {a})) (c - b)"
          unfolding inj_on_def
          by (metis Diff_eq_empty_iff Diff_iff indc affine_dependent_def hull_subset insert_iff)
      qed
      then show "int (card ?\<F>) + aff_dim S = int DIM('a)"
        by (simp add: imeq card_cb)
      show "affine hull S = \<Inter> ?\<F>"
        by (metis Diff_eq_empty_iff INT_simps(4) UN_singleton order_refl \<open>b \<subseteq> c\<close> False eq double_diff affine_hull_Inter [OF ind])
      have "\<And>a. \<lbrakk>a \<in> c; a \<notin> b\<rbrakk> \<Longrightarrow> aff_dim (c - {a}) = int (DIM('a) - Suc 0)"
        by (metis "*" DIM_ge_Suc0 One_nat_def add_diff_cancel_left' int_ops(2) of_nat_diff)
      then show "\<And>h. h \<in> ?\<F> \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x = b}"
        by (auto simp only: One_nat_def aff_dim_eq_hyperplane [symmetric])
      qed (use \<open>finite c\<close> in auto)
  qed
qed

lemma affine_hyperplane_sums_eq_UNIV_0:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S"
     and "0 \<in> S" and "w \<in> S"
     and "a \<bullet> w \<noteq> 0"
   shows "{x + y| x y. x \<in> S \<and> a \<bullet> y = 0} = UNIV"
proof -
  have "subspace S"
    by (simp add: assms subspace_affine)
  have span1: "span {y. a \<bullet> y = 0} \<subseteq> span {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    using \<open>0 \<in> S\<close> add.left_neutral by (intro span_mono) force
  have "w \<notin> span {y. a \<bullet> y = 0}"
    using \<open>a \<bullet> w \<noteq> 0\<close> span_induct subspace_hyperplane by auto
  moreover have "w \<in> span {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    using \<open>w \<in> S\<close>
    by (metis (mono_tags, lifting) inner_zero_right mem_Collect_eq pth_d span_base)
  ultimately have span2: "span {y. a \<bullet> y = 0} \<noteq> span {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    by blast
  have "a \<noteq> 0" using assms inner_zero_left by blast
  then have "DIM('a) - 1 = dim {y. a \<bullet> y = 0}"
    by (simp add: dim_hyperplane)
  also have "... < dim {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    using span1 span2 by (blast intro: dim_psubset)
  finally have "DIM('a) - 1 < dim {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}" .
  then have DD: "dim {x + y |x y. x \<in> S \<and> a \<bullet> y = 0} = DIM('a)"
    using antisym dim_subset_UNIV lowdim_subset_hyperplane not_le by fastforce
  have subs: "subspace {x + y| x y. x \<in> S \<and> a \<bullet> y = 0}"
    using subspace_sums [OF \<open>subspace S\<close> subspace_hyperplane] by simp
  moreover have "span {x + y| x y. x \<in> S \<and> a \<bullet> y = 0} = UNIV"
    using DD dim_eq_full by blast
  ultimately show ?thesis
    by (simp add: subs) (metis (lifting) span_eq_iff subs)
qed

proposition\<^marker>\<open>tag unimportant\<close> affine_hyperplane_sums_eq_UNIV:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S"
      and "S \<inter> {v. a \<bullet> v = b} \<noteq> {}"
      and "S - {v. a \<bullet> v = b} \<noteq> {}"
    shows "{x + y| x y. x \<in> S \<and> a \<bullet> y = b} = UNIV"
proof (cases "a = 0")
  case True with assms show ?thesis
    by (auto simp: if_splits)
next
  case False
  obtain c where "c \<in> S" and c: "a \<bullet> c = b"
    using assms by force
  with affine_diffs_subspace [OF \<open>affine S\<close>]
  have "subspace ((+) (- c) ` S)" by blast
  then have aff: "affine ((+) (- c) ` S)"
    by (simp add: subspace_imp_affine)
  have 0: "0 \<in> (+) (- c) ` S"
    by (simp add: \<open>c \<in> S\<close>)
  obtain d where "d \<in> S" and "a \<bullet> d \<noteq> b" and dc: "d-c \<in> (+) (- c) ` S"
    using assms by auto
  then have adc: "a \<bullet> (d - c) \<noteq> 0"
    by (simp add: c inner_diff_right)
  define U where "U \<equiv> {x + y |x y. x \<in> (+) (- c) ` S \<and> a \<bullet> y = 0}"
  have "u + v \<in> (+) (c+c) ` U"
    if "u \<in> S" "b = a \<bullet> v" for u v
  proof
    show "u + v = c + c + (u + v - c - c)"
      by (simp add: algebra_simps)
    have "\<exists>x y. u + v - c - c = x + y \<and> (\<exists>xa\<in>S. x = xa - c) \<and> a \<bullet> y = 0"
    proof (intro exI conjI)
      show "u + v - c - c = (u-c) + (v-c)" "a \<bullet> (v - c) = 0"
        by (simp_all add: algebra_simps c that)
    qed (use that in auto)
    then show "u + v - c - c \<in> U"
      by (auto simp: U_def image_def)
  qed
  moreover have "\<lbrakk>a \<bullet> v = 0; u \<in> S\<rbrakk>
       \<Longrightarrow> \<exists>x ya. v + (u + c) = x + ya \<and> x \<in> S \<and> a \<bullet> ya = b" for v u
    by (metis add.left_commute c inner_right_distrib pth_d)
  ultimately have "{x + y |x y. x \<in> S \<and> a \<bullet> y = b} = (+) (c+c) ` U"
    by (fastforce simp: algebra_simps U_def)
  also have "... = range ((+) (c + c))"
    by (simp only: U_def affine_hyperplane_sums_eq_UNIV_0 [OF aff 0 dc adc])
  also have "... = UNIV"
    by simp
  finally show ?thesis .
qed

lemma aff_dim_sums_Int_0:
  assumes "affine S"
      and "affine T"
      and "0 \<in> S" "0 \<in> T"
    shows "aff_dim {x + y| x y. x \<in> S \<and> y \<in> T} = (aff_dim S + aff_dim T) - aff_dim(S \<inter> T)"
proof -
  have "0 \<in> {x + y |x y. x \<in> S \<and> y \<in> T}"
    using assms by force
  then have 0: "0 \<in> affine hull {x + y |x y. x \<in> S \<and> y \<in> T}"
    by (metis (lifting) hull_inc)
  have sub: "subspace S"  "subspace T"
    using assms by (auto simp: subspace_affine)
  show ?thesis
    using dim_sums_Int [OF sub] by (simp add: aff_dim_zero assms 0 hull_inc)
qed

proposition aff_dim_sums_Int:
  assumes "affine S"
      and "affine T"
      and "S \<inter> T \<noteq> {}"
    shows "aff_dim {x + y| x y. x \<in> S \<and> y \<in> T} = (aff_dim S + aff_dim T) - aff_dim(S \<inter> T)"
proof -
  obtain a where a: "a \<in> S" "a \<in> T" using assms by force
  have aff: "affine ((+) (-a) ` S)"  "affine ((+) (-a) ` T)"
    using affine_translation [symmetric, of "- a"] assms by (simp_all cong: image_cong_simp)
  have zero: "0 \<in> ((+) (-a) ` S)"  "0 \<in> ((+) (-a) ` T)"
    using a assms by auto
  have "{x + y |x y. x \<in> (+) (- a) ` S \<and> y \<in> (+) (- a) ` T} =
      (+) (- 2 *\<^sub>R a) ` {x + y| x y. x \<in> S \<and> y \<in> T}"
    by (force simp: algebra_simps scaleR_2)
  moreover have "(+) (- a) ` S \<inter> (+) (- a) ` T = (+) (- a) ` (S \<inter> T)"
    by auto
  ultimately show ?thesis
    using aff_dim_sums_Int_0 [OF aff zero] aff_dim_translation_eq
    by (metis (lifting))
qed

lemma aff_dim_affine_Int_hyperplane:
  fixes a :: "'a::euclidean_space"
  assumes "affine S"
    shows "aff_dim(S \<inter> {x. a \<bullet> x = b}) =
             (if S \<inter> {v. a \<bullet> v = b} = {} then - 1
              else if S \<subseteq> {v. a \<bullet> v = b} then aff_dim S
              else aff_dim S - 1)"
proof (cases "a = 0")
  case True with assms show ?thesis
    by auto
next
  case False
  then have "aff_dim (S \<inter> {x. a \<bullet> x = b}) = aff_dim S - 1"
            if "x \<in> S" "a \<bullet> x \<noteq> b" and non: "S \<inter> {v. a \<bullet> v = b} \<noteq> {}" for x
  proof -
    have [simp]: "{x + y| x y. x \<in> S \<and> a \<bullet> y = b} = UNIV"
      using affine_hyperplane_sums_eq_UNIV [OF assms non] that  by blast
    show ?thesis
      using aff_dim_sums_Int [OF assms affine_hyperplane non]
      by (simp add: of_nat_diff False)
  qed
  then show ?thesis
    by (metis (mono_tags, lifting) inf.orderE aff_dim_empty_eq mem_Collect_eq subsetI)
qed

lemma aff_dim_lt_full:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S < DIM('a) \<longleftrightarrow> (affine hull S \<noteq> UNIV)"
by (metis (no_types) aff_dim_affine_hull aff_dim_le_DIM aff_dim_UNIV affine_hull_UNIV less_le)

lemma aff_dim_openin:
  fixes S :: "'a::euclidean_space set"
  assumes ope: "openin (top_of_set T) S" and "affine T" "S \<noteq> {}"
  shows "aff_dim S = aff_dim T"
proof -
  show ?thesis
  proof (rule order_antisym)
    show "aff_dim S \<le> aff_dim T"
      by (blast intro: aff_dim_subset [OF openin_imp_subset] ope)
  next
    obtain a where "a \<in> S"
      using \<open>S \<noteq> {}\<close> by blast
    have "S \<subseteq> T"
      using ope openin_imp_subset by auto
    then have "a \<in> T"
      using \<open>a \<in> S\<close> by auto
    then have subT': "subspace ((\<lambda>x. - a + x) ` T)"
      using affine_diffs_subspace \<open>affine T\<close> by auto
    then obtain B where Bsub: "B \<subseteq> ((\<lambda>x. - a + x) ` T)" and po: "pairwise orthogonal B"
                    and eq1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1" and "independent B"
                    and cardB: "card B = dim ((\<lambda>x. - a + x) ` T)"
                    and spanB: "span B = ((\<lambda>x. - a + x) ` T)"
      by (rule orthonormal_basis_subspace) auto
    obtain e where "0 < e" and e: "cball a e \<inter> T \<subseteq> S"
      by (meson \<open>a \<in> S\<close> openin_contains_cball ope)
    have "aff_dim T = aff_dim ((\<lambda>x. - a + x) ` T)"
      by (metis aff_dim_translation_eq)
    also have "... = dim ((\<lambda>x. - a + x) ` T)"
      using aff_dim_subspace subT' by blast
    also have "... = card B"
      by (simp add: cardB)
    also have "... = card ((\<lambda>x. e *\<^sub>R x) ` B)"
      using \<open>0 < e\<close>  by (force simp: inj_on_def card_image)
    also have "... \<le> dim ((\<lambda>x. - a + x) ` S)"
    proof (simp, rule independent_card_le_dim)
      have e': "cball 0 e \<inter> (\<lambda>x. x - a) ` T \<subseteq> (\<lambda>x. x - a) ` S"
        using e by (auto simp: dist_norm norm_minus_commute subset_eq)
      have "(\<lambda>x. e *\<^sub>R x) ` B \<subseteq> cball 0 e \<inter> (\<lambda>x. x - a) ` T"
        using Bsub \<open>0 < e\<close> eq1 subT' \<open>a \<in> T\<close> by (auto simp: subspace_def)
      then show "(\<lambda>x. e *\<^sub>R x) ` B \<subseteq> (\<lambda>x. x - a) ` S"
        using e' by blast
      have "inj_on ((*\<^sub>R) e) (span B)"
        using \<open>0 < e\<close> inj_on_def by fastforce
      then show "independent ((\<lambda>x. e *\<^sub>R x) ` B)"
        using linear_scale_self \<open>independent B\<close> linear_dependent_inj_imageD by blast
    qed
    also have "... = aff_dim S"
      using \<open>a \<in> S\<close> aff_dim_eq_dim hull_inc by (force cong: image_cong_simp)
    finally show "aff_dim T \<le> aff_dim S" .
  qed
qed

lemma dim_openin:
  fixes S :: "'a::euclidean_space set"
  assumes ope: "openin (top_of_set T) S" and "subspace T" "S \<noteq> {}"
  shows "dim S = dim T"
proof (rule order_antisym)
  show "dim S \<le> dim T"
    by (metis ope dim_subset openin_subset topspace_euclidean_subtopology)
next
  have "dim T = aff_dim S"
    using aff_dim_openin
    by (metis aff_dim_subspace \<open>subspace T\<close> \<open>S \<noteq> {}\<close> ope subspace_affine)
  also have "... \<le> dim S"
    by (metis aff_dim_subset aff_dim_subspace dim_span span_superset
        subspace_span)
  finally show "dim T \<le> dim S" by simp
qed

subsection\<open>Lower-dimensional affine subsets are nowhere dense\<close>

proposition dense_complement_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes dim_less: "dim T < dim S" and "subspace S" shows "closure(S - T) = S"
proof -
  have "closure(S - U) = S" if "dim U < dim S" "U \<subseteq> S" for U
  proof -
    have "span U \<subset> span S"
      by (metis neq_iff psubsetI span_eq_dim span_mono that)
    then obtain a where "a \<noteq> 0" "a \<in> span S" and a: "\<And>y. y \<in> span U \<Longrightarrow> orthogonal a y"
      using orthogonal_to_subspace_exists_gen by metis
    show ?thesis
    proof
      have "closed S"
        by (simp add: \<open>subspace S\<close> closed_subspace)
      then show "closure (S - U) \<subseteq> S"
        by (simp add: closure_minimal)
      show "S \<subseteq> closure (S - U)"
      proof (clarsimp simp: closure_approachable)
        fix x and e::real
        assume "x \<in> S" "0 < e"
        show "\<exists>y\<in>S - U. dist y x < e"
        proof (cases "x \<in> U")
          case True
          let ?y = "x + (e/2 / norm a) *\<^sub>R a"
          show ?thesis
          proof
            show "dist ?y x < e"
              using \<open>0 < e\<close> by (simp add: dist_norm)
          next
            have "?y \<in> S"
              by (metis \<open>a \<in> span S\<close> \<open>x \<in> S\<close> assms(2) span_eq_iff subspace_add subspace_scale)
            moreover have "?y \<notin> U"
            proof -
              have "e/2 / norm a \<noteq> 0"
                using \<open>0 < e\<close> \<open>a \<noteq> 0\<close> by auto
              then show ?thesis
                by (metis True \<open>a \<noteq> 0\<close> a orthogonal_scaleR orthogonal_self real_vector.scale_eq_0_iff span_add_eq span_base)
            qed
            ultimately show "?y \<in> S - U" by blast
          qed
        next
          case False
          with \<open>0 < e\<close> \<open>x \<in> S\<close> show ?thesis by force
        qed
      qed
    qed
  qed
  moreover have "S - S \<inter> T = S-T"
    by blast
  moreover have "dim (S \<inter> T) < dim S"
    by (metis dim_less dim_subset inf.cobounded2 inf.orderE inf.strict_boundedE not_le)
  ultimately show ?thesis
    by force
qed

corollary\<^marker>\<open>tag unimportant\<close> dense_complement_affine:
  fixes S :: "'a :: euclidean_space set"
  assumes less: "aff_dim T < aff_dim S" and "affine S" shows "closure(S - T) = S"
proof (cases "S \<inter> T = {}")
  case True
  then show ?thesis
    by (metis Diff_triv affine_hull_eq \<open>affine S\<close> closure_same_affine_hull closure_subset hull_subset subset_antisym)
next
  case False
  then obtain z where z: "z \<in> S \<inter> T" by blast
  then have "subspace ((+) (- z) ` S)"
    by (meson IntD1 affine_diffs_subspace \<open>affine S\<close>)
  moreover have "int (dim ((+) (- z) ` T)) < int (dim ((+) (- z) ` S))"
thm aff_dim_eq_dim
    using z less by (simp add: aff_dim_eq_dim_subtract [of z] hull_inc cong: image_cong_simp)
  ultimately have "closure(((+) (- z) ` S) - ((+) (- z) ` T)) = ((+) (- z) ` S)"
    by (simp add: dense_complement_subspace)
  then show ?thesis
    by (metis closure_translation translation_diff translation_invert)
qed

corollary\<^marker>\<open>tag unimportant\<close> dense_complement_openin_affine_hull:
  fixes S :: "'a :: euclidean_space set"
  assumes less: "aff_dim T < aff_dim S"
      and ope: "openin (top_of_set (affine hull S)) S"
    shows "closure(S - T) = closure S"
proof -
  have "affine hull S - T \<subseteq> affine hull S"
    by blast
  then have "closure (S \<inter> closure (affine hull S - T)) = closure (S \<inter> (affine hull S - T))"
    by (rule closure_openin_Int_closure [OF ope])
  then show ?thesis
    by (metis Int_Diff aff_dim_affine_hull affine_affine_hull dense_complement_affine hull_subset inf.orderE less)
qed

corollary\<^marker>\<open>tag unimportant\<close> dense_complement_convex:
  fixes S :: "'a :: euclidean_space set"
  assumes "aff_dim T < aff_dim S" "convex S"
    shows "closure(S - T) = closure S"
proof
  show "closure (S - T) \<subseteq> closure S"
    by (simp add: closure_mono)
  have "closure (rel_interior S - T) = closure (rel_interior S)"
    by (simp add: assms dense_complement_openin_affine_hull openin_rel_interior rel_interior_aff_dim rel_interior_same_affine_hull)
  then show "closure S \<subseteq> closure (S - T)"
    by (metis Diff_mono \<open>convex S\<close> closure_mono convex_closure_rel_interior order_refl rel_interior_subset)
qed

corollary\<^marker>\<open>tag unimportant\<close> dense_complement_convex_closed:
  fixes S :: "'a :: euclidean_space set"
  assumes "aff_dim T < aff_dim S" "convex S" "closed S"
    shows "closure(S - T) = S"
  by (simp add: assms dense_complement_convex)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Parallel slices, etc\<close>

text\<open> If we take a slice out of a set, we can do it perpendicularly,
  with the normal vector to the slice parallel to the affine hull.\<close>

proposition\<^marker>\<open>tag unimportant\<close> affine_parallel_slice:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S"
      and "S \<inter> {x. a \<bullet> x \<le> b} \<noteq> {}"
      and "\<not> (S \<subseteq> {x. a \<bullet> x \<le> b})"
  obtains a' b' where "a' \<noteq> 0"
                   "S \<inter> {x. a' \<bullet> x \<le> b'} = S \<inter> {x. a \<bullet> x \<le> b}"
                   "S \<inter> {x. a' \<bullet> x = b'} = S \<inter> {x. a \<bullet> x = b}"
                   "\<And>w. w \<in> S \<Longrightarrow> (w + a') \<in> S"
proof (cases "S \<inter> {x. a \<bullet> x = b} = {}")
  case True
  then obtain u v where "u \<in> S" "v \<in> S" "a \<bullet> u \<le> b" "a \<bullet> v > b"
    using assms by (auto simp: not_le)
  define \<eta> where "\<eta> = u + ((b - a \<bullet> u) / (a \<bullet> v - a \<bullet> u)) *\<^sub>R (v - u)"
  have "\<eta> \<in> S"
    by (simp add: \<eta>_def \<open>u \<in> S\<close> \<open>v \<in> S\<close> \<open>affine S\<close> mem_affine_3_minus)
  moreover have "a \<bullet> \<eta> = b"
    using \<open>a \<bullet> u \<le> b\<close> \<open>b < a \<bullet> v\<close>
    by (simp add: \<eta>_def algebra_simps) (simp add: field_simps)
  ultimately have False
    using True by force
  then show ?thesis ..
next
  case False
  then obtain z where "z \<in> S" and z: "a \<bullet> z = b"
    using assms by auto
  with affine_diffs_subspace [OF \<open>affine S\<close>]
  have sub: "subspace ((+) (- z) ` S)" by blast
  then have aff: "affine ((+) (- z) ` S)" and span: "span ((+) (- z) ` S) = ((+) (- z) ` S)"
    by (auto simp: subspace_imp_affine)
  obtain a' a'' where a': "a' \<in> span ((+) (- z) ` S)" and a: "a = a' + a''"
                  and "\<And>w. w \<in> span ((+) (- z) ` S) \<Longrightarrow> orthogonal a'' w"
    using orthogonal_subspace_decomp_exists [of "(+) (- z) ` S" "a"] by metis
  then have "\<And>w. w \<in> S \<Longrightarrow> a'' \<bullet> (w-z) = 0"
    by (simp add: span_base orthogonal_def)
  then have a'': "\<And>w. w \<in> S \<Longrightarrow> a'' \<bullet> w = (a - a') \<bullet> z"
    by (simp add: a inner_diff_right)
  then have ba'': "\<And>w. w \<in> S \<Longrightarrow> a'' \<bullet> w = b - a' \<bullet> z"
    by (simp add: inner_diff_left z)
  show ?thesis
  proof (cases "a' = 0")
    case True
    with a assms True a'' diff_zero less_irrefl show ?thesis
      by auto
  next
    case False
    show ?thesis
    proof
      show "S \<inter> {x. a' \<bullet> x \<le> a' \<bullet> z} = S \<inter> {x. a \<bullet> x \<le> b}"
        "S \<inter> {x. a' \<bullet> x = a' \<bullet> z} = S \<inter> {x. a \<bullet> x = b}"
        by (auto simp: a ba'' inner_left_distrib)
      have "\<And>w. w \<in> (+) (- z) ` S \<Longrightarrow> (w + a') \<in> (+) (- z) ` S"
        by (metis subspace_add a' span_eq_iff sub)
      then show "\<And>w. w \<in> S \<Longrightarrow> (w + a') \<in> S"
        by fastforce
    qed (use False in auto)
  qed
qed

lemma diffs_affine_hull_span:
  assumes "a \<in> S"
    shows "(\<lambda>x. x - a) ` (affine hull S) = span ((\<lambda>x. x - a) ` S)"
proof -
  have *: "((\<lambda>x. x - a) ` (S - {a})) = ((\<lambda>x. x - a) ` S) - {0}"
    by (auto simp: algebra_simps)
  show ?thesis
    by (auto simp add: algebra_simps affine_hull_span2 [OF assms] *)
qed

lemma aff_dim_dim_affine_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S" "a \<in> S"
    shows "aff_dim S = dim ((\<lambda>x. x - a) ` S)"
proof -
  obtain B where aff: "affine hull B = affine hull S"
             and ind: "\<not> affine_dependent B"
             and card: "of_nat (card B) = aff_dim S + 1"
    using aff_dim_basis_exists by blast
  then have "B \<noteq> {}" using assms
    by (metis affine_hull_eq_empty ex_in_conv)
  then obtain c where "c \<in> B" by auto
  then have "c \<in> S"
    by (metis aff affine_hull_eq \<open>affine S\<close> hull_inc)
  have xy: "x - c = y - a \<longleftrightarrow> y = x + 1 *\<^sub>R (a - c)" for x y c and a::'a
    by (auto simp: algebra_simps)
  have *: "(\<lambda>x. x - c) ` S = (\<lambda>x. x - a) ` S"
    using assms \<open>c \<in> S\<close>
    by (auto simp: image_iff xy; metis mem_affine_3_minus pth_1)
  have affS: "affine hull S = S"
    by (simp add: \<open>affine S\<close>)
  have "aff_dim S = of_nat (card B) - 1"
    using card by simp
  also have "... = dim ((\<lambda>x. x - c) ` B)"
    using affine_independent_card_dim_diffs [OF ind \<open>c \<in> B\<close>]
    by (simp add: affine_independent_card_dim_diffs [OF ind \<open>c \<in> B\<close>])
  also have "... = dim ((\<lambda>x. x - c) ` (affine hull B))"
    by (simp add: diffs_affine_hull_span \<open>c \<in> B\<close>)
  also have "... = dim ((\<lambda>x. x - a) ` S)"
    by (simp add: affS aff *)
  finally show ?thesis .
qed

lemma aff_dim_linear_image_le:
  assumes "linear f"
    shows "aff_dim(f ` S) \<le> aff_dim S"
proof -
  have "aff_dim (f ` T) \<le> aff_dim T" if "affine T" for T
  proof (cases "T = {}")
    case True then show ?thesis by (simp add: aff_dim_geq)
  next
    case False
    then obtain a where "a \<in> T" by auto
    have 1: "((\<lambda>x. x - f a) ` f ` T) = {x - f a |x. x \<in> f ` T}"
      by auto
    have 2: "{x - f a| x. x \<in> f ` T} = f ` ((\<lambda>x. x - a) ` T)"
      by (force simp: linear_diff [OF assms])
    have "aff_dim (f ` T) = int (dim {x - f a |x. x \<in> f ` T})"
      by (simp add: \<open>a \<in> T\<close> hull_inc aff_dim_eq_dim [of "f a"] 1 cong: image_cong_simp)
    also have "... = int (dim (f ` ((\<lambda>x. x - a) ` T)))"
      by (force simp: linear_diff [OF assms] 2)
    also have "... \<le> int (dim ((\<lambda>x. x - a) ` T))"
      by (simp add: dim_image_le [OF assms])
    also have "... \<le> aff_dim T"
      by (simp add: aff_dim_dim_affine_diffs [symmetric] \<open>a \<in> T\<close> \<open>affine T\<close>)
    finally show ?thesis .
  qed
  then
  have "aff_dim (f ` (affine hull S)) \<le> aff_dim (affine hull S)"
    using affine_affine_hull [of S] by blast
  then show ?thesis
    using affine_hull_linear_image assms linear_conv_bounded_linear by fastforce
qed

lemma aff_dim_injective_linear_image [simp]:
  assumes "linear f" "inj f"
    shows "aff_dim (f ` S) = aff_dim S"
proof (rule antisym)
  show "aff_dim (f ` S) \<le> aff_dim S"
    by (simp add: aff_dim_linear_image_le assms(1))
next
  obtain g where "linear g" "g \<circ> f = id"
    using assms(1) assms(2) linear_injective_left_inverse by blast
  then have "aff_dim S \<le> aff_dim(g ` f ` S)"
    by (simp add: image_comp)
  also have "... \<le> aff_dim (f ` S)"
    by (simp add: \<open>linear g\<close> aff_dim_linear_image_le)
  finally show "aff_dim S \<le> aff_dim (f ` S)" .
qed


lemma choose_affine_subset:
  assumes "affine S" "-1 \<le> d" and dle: "d \<le> aff_dim S"
  obtains T where "affine T" "T \<subseteq> S" "aff_dim T = d"
proof (cases "d = -1 \<or> S={}")
  case True with assms show ?thesis
    by (metis aff_dim_empty affine_empty bot.extremum that eq_iff)
next
  case False
  with assms obtain a where "a \<in> S" "0 \<le> d" by auto
  with assms have ss: "subspace ((+) (- a) ` S)"
    by (simp add: affine_diffs_subspace_subtract cong: image_cong_simp)
  have "nat d \<le> dim ((+) (- a) ` S)"
    by (metis aff_dim_subspace aff_dim_translation_eq dle nat_int nat_mono ss)
  then obtain T where "subspace T" and Tsb: "T \<subseteq> span ((+) (- a) ` S)"
                  and Tdim: "dim T = nat d"
    using choose_subspace_of_subspace [of "nat d" "(+) (- a) ` S"] by blast
  then have "affine T"
    using subspace_affine by blast
  then have "affine ((+) a ` T)"
    by (metis affine_hull_eq affine_hull_translation)
  moreover have "(+) a ` T \<subseteq> S"
  proof -
    have "T \<subseteq> (+) (- a) ` S"
      by (metis (no_types) span_eq_iff Tsb ss)
    then show "(+) a ` T \<subseteq> S"
      using add_ac by auto
  qed
  moreover have "aff_dim ((+) a ` T) = d"
    by (simp add: aff_dim_subspace Tdim \<open>0 \<le> d\<close> \<open>subspace T\<close> aff_dim_translation_eq)
  ultimately show ?thesis
    by (rule that)
qed

subsection\<open>Paracompactness\<close>

proposition paracompact:
  fixes S :: "'a :: {metric_space,second_countable_topology} set"
  assumes "S \<subseteq> \<Union>\<C>" and opC: "\<And>T. T \<in> \<C> \<Longrightarrow> open T"
  obtains \<C>' where "S \<subseteq> \<Union> \<C>'"
               and "\<And>U. U \<in> \<C>' \<Longrightarrow> open U \<and> (\<exists>T. T \<in> \<C> \<and> U \<subseteq> T)"
               and "\<And>x. x \<in> S
                       \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U. U \<in> \<C>' \<and> (U \<inter> V \<noteq> {})}"
proof (cases "S = {}")
  case True with that show ?thesis by blast
next
  case False
  have "\<exists>T U. x \<in> U \<and> open U \<and> closure U \<subseteq> T \<and> T \<in> \<C>" if "x \<in> S" for x
  proof -
    obtain T where "x \<in> T" "T \<in> \<C>" "open T"
      using assms \<open>x \<in> S\<close> by blast
    then obtain e where "e > 0" "cball x e \<subseteq> T"
      by (force simp: open_contains_cball)
    then show ?thesis
      by (meson open_ball \<open>T \<in> \<C>\<close> ball_subset_cball centre_in_ball closed_cball closure_minimal dual_order.trans)
  qed
  then obtain F G where Gin: "x \<in> G x" and oG: "open (G x)"
    and clos: "closure (G x) \<subseteq> F x" and Fin: "F x \<in> \<C>"
  if "x \<in> S" for x
    by metis
  then obtain \<F> where "\<F> \<subseteq> G ` S" "countable \<F>" "\<Union>\<F> = \<Union>(G ` S)"
    using Lindelof [of "G ` S"] by (metis image_iff)
  then obtain K where K: "K \<subseteq> S" "countable K" and eq: "\<Union>(G ` K) = \<Union>(G ` S)"
    by (metis countable_subset_image)
  with False Gin have "K \<noteq> {}" by force
  then obtain a :: "nat \<Rightarrow> 'a" where "range a = K"
    by (metis range_from_nat_into \<open>countable K\<close>)
  then have odif: "\<And>n. open (F (a n) - \<Union>{closure (G (a m)) |m. m < n})"
    using \<open>K \<subseteq> S\<close> Fin opC by (fastforce simp add:)
  let ?C = "range (\<lambda>n. F(a n) - \<Union>{closure(G(a m)) |m. m < n})"
  have enum_S: "\<exists>n. x \<in> F(a n) \<and> x \<in> G(a n)" if "x \<in> S" for x
  proof -
    have "\<exists>y \<in> K. x \<in> G y" using eq that Gin by fastforce
    then show ?thesis
      using clos K \<open>range a = K\<close> closure_subset by blast
  qed
  show ?thesis
  proof
    show "S \<subseteq> Union ?C"
    proof
      fix x assume "x \<in> S"
      define n where "n \<equiv> LEAST n. x \<in> F(a n)"
      have n: "x \<in> F(a n)"
        using enum_S [OF \<open>x \<in> S\<close>] by (force simp: n_def intro: LeastI)
      have notn: "x \<notin> F(a m)" if "m < n" for m
        using that not_less_Least by (force simp: n_def)
      then have "x \<notin> \<Union>{closure (G (a m)) |m. m < n}"
        using n \<open>K \<subseteq> S\<close> \<open>range a = K\<close> clos notn by fastforce
      with n show "x \<in> Union ?C"
        by blast
    qed
    show "\<And>U. U \<in> ?C \<Longrightarrow> open U \<and> (\<exists>T. T \<in> \<C> \<and> U \<subseteq> T)"
      using Fin \<open>K \<subseteq> S\<close> \<open>range a = K\<close> by (auto simp: odif)
    show "\<exists>V. open V \<and> x \<in> V \<and> finite {U. U \<in> ?C \<and> (U \<inter> V \<noteq> {})}" if "x \<in> S" for x
    proof -
      obtain n where n: "x \<in> F(a n)" "x \<in> G(a n)"
        using \<open>x \<in> S\<close> enum_S by auto
      have "{U \<in> ?C. U \<inter> G (a n) \<noteq> {}} \<subseteq> (\<lambda>n. F(a n) - \<Union>{closure(G(a m)) |m. m < n}) ` atMost n"
      proof clarsimp
        fix k  assume "(F (a k) - \<Union>{closure (G (a m)) |m. m < k}) \<inter> G (a n) \<noteq> {}"
        then have "k \<le> n"
          by auto (metis closure_subset not_le subsetCE)
        then show "F (a k) - \<Union>{closure (G (a m)) |m. m < k}
                 \<in> (\<lambda>n. F (a n) - \<Union>{closure (G (a m)) |m. m < n}) ` {..n}"
          by force
      qed
      moreover have "finite ((\<lambda>n. F(a n) - \<Union>{closure(G(a m)) |m. m < n}) ` atMost n)"
        by force
      ultimately have *: "finite {U \<in> ?C. U \<inter> G (a n) \<noteq> {}}"
        using finite_subset by blast
      have "a n \<in> S"
        using \<open>K \<subseteq> S\<close> \<open>range a = K\<close> by blast
      then show ?thesis
        by (blast intro: oG n *)
    qed
  qed
qed

corollary paracompact_closedin:
  fixes S :: "'a :: {metric_space,second_countable_topology} set"
  assumes cin: "closedin (top_of_set U) S"
      and oin: "\<And>T. T \<in> \<C> \<Longrightarrow> openin (top_of_set U) T"
      and "S \<subseteq> \<Union>\<C>"
  obtains \<C>' where "S \<subseteq> \<Union> \<C>'"
               and "\<And>V. V \<in> \<C>' \<Longrightarrow> openin (top_of_set U) V \<and> (\<exists>T. T \<in> \<C> \<and> V \<subseteq> T)"
               and "\<And>x. x \<in> U
                       \<Longrightarrow> \<exists>V. openin (top_of_set U) V \<and> x \<in> V \<and>
                               finite {X. X \<in> \<C>' \<and> (X \<inter> V \<noteq> {})}"
proof -
  have "\<exists>Z. open Z \<and> (T = U \<inter> Z)" if "T \<in> \<C>" for T
    using oin [OF that] by (auto simp: openin_open)
  then obtain F where opF: "open (F T)" and intF: "U \<inter> F T = T" if "T \<in> \<C>" for T
    by metis
  obtain K where K: "closed K" "U \<inter> K = S"
    using cin by (auto simp: closedin_closed)
  have 1: "U \<subseteq> \<Union>(insert (- K) (F ` \<C>))"
    by clarsimp (metis Int_iff Union_iff \<open>U \<inter> K = S\<close> \<open>S \<subseteq> \<Union>\<C>\<close> subsetD intF)
  have 2: "\<And>T. T \<in> insert (- K) (F ` \<C>) \<Longrightarrow> open T"
    using \<open>closed K\<close> by (auto simp: opF)
  obtain \<D> where "U \<subseteq> \<Union>\<D>"
             and D1: "\<And>U. U \<in> \<D> \<Longrightarrow> open U \<and> (\<exists>T. T \<in> insert (- K) (F ` \<C>) \<and> U \<subseteq> T)"
             and D2: "\<And>x. x \<in> U \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<D>. U \<inter> V \<noteq> {}}"
    by (blast intro: paracompact [OF 1 2])
  let ?C = "{U \<inter> V |V. V \<in> \<D> \<and> (V \<inter> K \<noteq> {})}"
  show ?thesis
  proof (rule_tac \<C>' = "{U \<inter> V |V. V \<in> \<D> \<and> (V \<inter> K \<noteq> {})}" in that)
    show "S \<subseteq> \<Union>?C"
      using \<open>U \<inter> K = S\<close> \<open>U \<subseteq> \<Union>\<D>\<close> K by (blast dest!: subsetD)
    show "\<And>V. V \<in> ?C \<Longrightarrow> openin (top_of_set U) V \<and> (\<exists>T. T \<in> \<C> \<and> V \<subseteq> T)"
      using D1 intF by fastforce
    have *: "{X. (\<exists>V. X = U \<inter> V \<and> V \<in> \<D> \<and> V \<inter> K \<noteq> {}) \<and> X \<inter> (U \<inter> V) \<noteq> {}} \<subseteq>
             (\<lambda>x. U \<inter> x) ` {U \<in> \<D>. U \<inter> V \<noteq> {}}" for V
      by blast
    show "\<exists>V. openin (top_of_set U) V \<and> x \<in> V \<and> finite {X \<in> ?C. X \<inter> V \<noteq> {}}"
      if "x \<in> U" for x
    proof -
      from D2 [OF that] obtain V where "open V" "x \<in> V" "finite {U \<in> \<D>. U \<inter> V \<noteq> {}}"
        by auto
      with * show ?thesis
        by (rule_tac x="U \<inter> V" in exI) (auto intro: that finite_subset [OF *])
    qed
  qed
qed

corollary\<^marker>\<open>tag unimportant\<close> paracompact_closed:
  fixes S :: "'a :: {metric_space,second_countable_topology} set"
  assumes "closed S"
      and opC: "\<And>T. T \<in> \<C> \<Longrightarrow> open T"
      and "S \<subseteq> \<Union>\<C>"
  obtains \<C>' where "S \<subseteq> \<Union>\<C>'"
               and "\<And>U. U \<in> \<C>' \<Longrightarrow> open U \<and> (\<exists>T. T \<in> \<C> \<and> U \<subseteq> T)"
               and "\<And>x. \<exists>V. open V \<and> x \<in> V \<and>
                               finite {U. U \<in> \<C>' \<and> (U \<inter> V \<noteq> {})}"
  by (rule paracompact_closedin [of UNIV S \<C>]) (auto simp: assms)

  
subsection\<^marker>\<open>tag unimportant\<close>\<open>Closed-graph characterization of continuity\<close>

lemma continuous_closed_graph_gen:
  fixes T :: "'b::real_normed_vector set"
  assumes contf: "continuous_on S f" and fim: "f ` S \<subseteq> T"
    shows "closedin (top_of_set (S \<times> T)) ((\<lambda>x. Pair x (f x)) ` S)"
proof -
  have eq: "((\<lambda>x. Pair x (f x)) ` S) = (S \<times> T \<inter> (\<lambda>z. (f \<circ> fst)z - snd z) -` {0})"
    using fim by auto
  show ?thesis
    unfolding eq
    by (intro continuous_intros continuous_closedin_preimage continuous_on_subset [OF contf]) auto
qed

lemma continuous_closed_graph_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact T" and fim: "f ` S \<subseteq> T"
  shows "continuous_on S f \<longleftrightarrow>
         closedin (top_of_set (S \<times> T)) ((\<lambda>x. Pair x (f x)) ` S)"
         (is "?lhs = ?rhs")
proof -
  have "?lhs" if ?rhs
  proof (clarsimp simp add: continuous_on_closed_gen [OF fim])
    fix U
    assume U: "closedin (top_of_set T) U"
    have eq: "(S \<inter> f -` U) = fst ` (((\<lambda>x. Pair x (f x)) ` S) \<inter> (S \<times> U))"
      by (force simp: image_iff)
    show "closedin (top_of_set S) (S \<inter> f -` U)"
      by (simp add: U closedin_Int closedin_Times closed_map_fst [OF \<open>compact T\<close>] that eq)
  qed
  with continuous_closed_graph_gen assms show ?thesis by blast
qed

lemma continuous_closed_graph:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  assumes "closed S" and contf: "continuous_on S f"
  shows "closed ((\<lambda>x. Pair x (f x)) ` S)"
proof (rule closedin_closed_trans)
  show "closedin (top_of_set (S \<times> UNIV)) ((\<lambda>x. (x, f x)) ` S)"
    by (rule continuous_closed_graph_gen [OF contf subset_UNIV])
qed (simp add: \<open>closed S\<close> closed_Times)

lemma continuous_from_closed_graph:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact T" and fim: "f ` S \<subseteq> T" and clo: "closed ((\<lambda>x. Pair x (f x)) ` S)"
  shows "continuous_on S f"
    using fim clo
    by (auto intro: closed_subset simp: continuous_closed_graph_eq [OF \<open>compact T\<close> fim])

lemma continuous_on_Un_local_open:
  assumes opS: "openin (top_of_set (S \<union> T)) S"
      and opT: "openin (top_of_set (S \<union> T)) T"
      and contf: "continuous_on S f" and contg: "continuous_on T f"
    shows "continuous_on (S \<union> T) f"
  using pasting_lemma [of "{S,T}" "top_of_set (S \<union> T)" id euclidean "\<lambda>i. f" f] contf contg opS opT
  by (simp add: subtopology_subtopology) (metis inf.absorb2 openin_imp_subset)  

lemma continuous_on_cases_local_open:
  assumes opS: "openin (top_of_set (S \<union> T)) S"
      and opT: "openin (top_of_set (S \<union> T)) T"
      and contf: "continuous_on S f" and contg: "continuous_on T g"
      and fg: "\<And>x. x \<in> S \<and> \<not>P x \<or> x \<in> T \<and> P x \<Longrightarrow> f x = g x"
    shows "continuous_on (S \<union> T) (\<lambda>x. if P x then f x else g x)"
proof -
  have "\<And>x. x \<in> S \<Longrightarrow> (if P x then f x else g x) = f x"  "\<And>x. x \<in> T \<Longrightarrow> (if P x then f x else g x) = g x"
    by (simp_all add: fg)
  then have "continuous_on S (\<lambda>x. if P x then f x else g x)" "continuous_on T (\<lambda>x. if P x then f x else g x)"
    by (simp_all add: contf contg cong: continuous_on_cong)
  then show ?thesis
    by (rule continuous_on_Un_local_open [OF opS opT])
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>The union of two collinear segments is another segment\<close>

proposition\<^marker>\<open>tag unimportant\<close> in_convex_hull_exchange:
  fixes a :: "'a::euclidean_space"
  assumes a: "a \<in> convex hull S" and xS: "x \<in> convex hull S"
  obtains b where "b \<in> S" "x \<in> convex hull (insert a (S - {b}))"
proof (cases "a \<in> S")
  case True
  with xS insert_Diff that  show ?thesis by fastforce
next
  case False
  show ?thesis
  proof (cases "finite S \<and> card S \<le> Suc (DIM('a))")
    case True
    then obtain u where u0: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> u i" and u1: "sum u S = 1"
                    and ua: "(\<Sum>i\<in>S. u i *\<^sub>R i) = a"
        using a by (auto simp: convex_hull_finite)
    obtain v where v0: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> v i" and v1: "sum v S = 1"
               and vx: "(\<Sum>i\<in>S. v i *\<^sub>R i) = x"
      using True xS by (auto simp: convex_hull_finite)
    show ?thesis
    proof (cases "\<exists>b. b \<in> S \<and> v b = 0")
      case True
      then obtain b where b: "b \<in> S" "v b = 0"
        by blast
      show ?thesis
      proof
        have fin: "finite (insert a (S - {b}))"
          using sum.infinite v1 by fastforce
        show "x \<in> convex hull insert a (S - {b})"
          unfolding convex_hull_finite [OF fin] mem_Collect_eq
        proof (intro conjI exI ballI)
          have "(\<Sum>x \<in> insert a (S - {b}). if x = a then 0 else v x) =
                (\<Sum>x \<in> S - {b}. if x = a then 0 else v x)"
            using fin by (force intro: sum.mono_neutral_right)
          also have "... = (\<Sum>x \<in> S - {b}. v x)"
            using b False by (auto intro!: sum.cong split: if_split_asm)
          also have "... = (\<Sum>x\<in>S. v x)"
            by (metis \<open>v b = 0\<close> diff_zero sum.infinite sum_diff1 u1 zero_neq_one)
          finally show "(\<Sum>x\<in>insert a (S - {b}). if x = a then 0 else v x) = 1"
            by (simp add: v1)
          show "\<And>x. x \<in> insert a (S - {b}) \<Longrightarrow> 0 \<le> (if x = a then 0 else v x)"
            by (auto simp: v0)
          have "(\<Sum>x \<in> insert a (S - {b}). (if x = a then 0 else v x) *\<^sub>R x) =
                (\<Sum>x \<in> S - {b}. (if x = a then 0 else v x) *\<^sub>R x)"
            using fin by (force intro: sum.mono_neutral_right)
          also have "... = (\<Sum>x \<in> S - {b}. v x *\<^sub>R x)"
            using b False by (auto intro!: sum.cong split: if_split_asm)
          also have "... = (\<Sum>x\<in>S. v x *\<^sub>R x)"
            by (metis (no_types, lifting) b(2) diff_zero fin finite.emptyI finite_Diff2 finite_insert scale_eq_0_iff sum_diff1)
          finally show "(\<Sum>x\<in>insert a (S - {b}). (if x = a then 0 else v x) *\<^sub>R x) = x"
            by (simp add: vx)
        qed
      qed (rule \<open>b \<in> S\<close>)
    next
      case False
      have le_Max: "u i / v i \<le> Max ((\<lambda>i. u i / v i) ` S)" if "i \<in> S" for i
        by (simp add: True that)
      have "Max ((\<lambda>i. u i / v i) ` S) \<in> (\<lambda>i. u i / v i) ` S"
        using True v1 by (auto intro: Max_in)
      then obtain b where "b \<in> S" and beq: "Max ((\<lambda>b. u b / v b) ` S) = u b / v b"
        by blast
      then have "0 \<noteq> u b / v b"
        using le_Max beq divide_le_0_iff le_numeral_extra(2) sum_nonpos u1
        by (metis False eq_iff v0)
      then have  "0 < u b" "0 < v b"
        using False \<open>b \<in> S\<close> u0 v0 by force+
      have fin: "finite (insert a (S - {b}))"
        using sum.infinite v1 by fastforce
      show ?thesis
      proof
        show "x \<in> convex hull insert a (S - {b})"
          unfolding convex_hull_finite [OF fin] mem_Collect_eq
        proof (intro conjI exI ballI)
          have "(\<Sum>x \<in> insert a (S - {b}). if x=a then v b / u b else v x - (v b / u b) * u x) =
                v b / u b + (\<Sum>x \<in> S - {b}. v x - (v b / u b) * u x)"
            using \<open>a \<notin> S\<close> \<open>b \<in> S\<close> True  
            by (auto intro!: sum.cong split: if_split_asm)
          also have "... = v b / u b + (\<Sum>x \<in> S - {b}. v x) - (v b / u b) * (\<Sum>x \<in> S - {b}. u x)"
            by (simp add: Groups_Big.sum_subtractf sum_distrib_left)
          also have "... = (\<Sum>x\<in>S. v x)"
            using \<open>0 < u b\<close> True  by (simp add: Groups_Big.sum_diff1 u1 field_simps)
          finally show "sum (\<lambda>x. if x=a then v b / u b else v x - (v b / u b) * u x) (insert a (S - {b})) = 1"
            by (simp add: v1)
          show "0 \<le> (if i = a then v b / u b else v i - v b / u b * u i)"
            if "i \<in> insert a (S - {b})" for i
            using \<open>0 < u b\<close> \<open>0 < v b\<close> v0 [of i] le_Max [of i] beq that False
            by (auto simp: field_simps split: if_split_asm)
          have "(\<Sum>x\<in>insert a (S - {b}). (if x=a then v b / u b else v x - v b / u b * u x) *\<^sub>R x) =
                (v b / u b) *\<^sub>R a + (\<Sum>x\<in>S - {b}. (v x - v b / u b * u x) *\<^sub>R x)"
            using \<open>a \<notin> S\<close> \<open>b \<in> S\<close> True  by (auto intro!: sum.cong split: if_split_asm)
          also have "... = (v b / u b) *\<^sub>R a + (\<Sum>x \<in> S - {b}. v x *\<^sub>R x) - (v b / u b) *\<^sub>R (\<Sum>x \<in> S - {b}. u x *\<^sub>R x)"
            by (simp add: Groups_Big.sum_subtractf scaleR_left_diff_distrib sum_distrib_left scale_sum_right)
          also have "... = (\<Sum>x\<in>S. v x *\<^sub>R x)"
            using \<open>0 < u b\<close> True  by (simp add: ua vx Groups_Big.sum_diff1 algebra_simps)
          finally
          show "(\<Sum>x\<in>insert a (S - {b}). (if x=a then v b / u b else v x - v b / u b * u x) *\<^sub>R x) = x"
            by (simp add: vx)
        qed
      qed (rule \<open>b \<in> S\<close>)
    qed
  next
    case False
    obtain T where "finite T" "T \<subseteq> S" and caT: "card T \<le> Suc (DIM('a))" and xT: "x \<in> convex hull T"
      using xS by (auto simp: caratheodory [of S])
    with False obtain b where b: "b \<in> S" "b \<notin> T"
      by (metis antisym subsetI)
    show ?thesis
    proof
      show "x \<in> convex hull insert a (S - {b})"
        using  \<open>T \<subseteq> S\<close> b by (blast intro: subsetD [OF hull_mono xT])
    qed (rule \<open>b \<in> S\<close>)
  qed
qed

lemma convex_hull_exchange_Union:
  fixes a :: "'a::euclidean_space"
  assumes "a \<in> convex hull S"
  shows "convex hull S = (\<Union>b \<in> S. convex hull (insert a (S - {b})))" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (blast intro: in_convex_hull_exchange [OF assms])
  show "?rhs \<subseteq> ?lhs"
  proof clarify
    fix x b
    assume"b \<in> S" "x \<in> convex hull insert a (S - {b})"
    then show "x \<in> convex hull S" if "b \<in> S"
      by (metis (no_types) that assms order_refl hull_mono hull_redundant insert_Diff_single insert_subset subsetCE)
  qed
qed

lemma Un_closed_segment:
  fixes a :: "'a::euclidean_space"
  assumes "b \<in> closed_segment a c"
    shows "closed_segment a b \<union> closed_segment b c = closed_segment a c"
proof (cases "c = a")
  case True
  with assms show ?thesis by simp
next
  case False
  with assms have "convex hull {a, b} \<union> convex hull {b, c} = (\<Union>ba\<in>{a, c}. convex hull insert b ({a, c} - {ba}))"
    by (auto simp: insert_Diff_if insert_commute)
  then show ?thesis
    using convex_hull_exchange_Union
    by (metis assms segment_convex_hull)
qed

lemma Un_open_segment:
  fixes a :: "'a::euclidean_space"
  assumes "b \<in> open_segment a c"
  shows "open_segment a b \<union> {b} \<union> open_segment b c = open_segment a c" (is "?lhs = ?rhs")
proof -
  have b: "b \<in> closed_segment a c"
    by (simp add: assms open_closed_segment)
  have *: "?rhs \<subseteq> insert b (open_segment a b \<union> open_segment b c)"
          if "{b,c,a} \<union> open_segment a b \<union> open_segment b c = {c,a} \<union> ?rhs"
  proof -
    have "insert a (insert c (insert b (open_segment a b \<union> open_segment b c))) = insert a (insert c (?rhs))"
      using that by (simp add: insert_commute)
    then show ?thesis
      by (metis (no_types) Diff_cancel Diff_eq_empty_iff Diff_insert2 open_segment_def)
  qed
  show ?thesis
  proof
    show "?lhs \<subseteq> ?rhs"
      by (simp add: assms b subset_open_segment)
    show "?rhs \<subseteq> ?lhs"
      using Un_closed_segment [OF b] *
      by (simp add: closed_segment_eq_open insert_commute)
  qed
qed

subsection\<open>Covering an open set by a countable chain of compact sets\<close>
  
proposition open_Union_compact_subsets:
  fixes S :: "'a::euclidean_space set"
  assumes "open S"
  obtains C where "\<And>n. compact(C n)" "\<And>n. C n \<subseteq> S"
                  "\<And>n. C n \<subseteq> interior(C(Suc n))"
                  "\<Union>(range C) = S"
                  "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. K \<subseteq> (C n)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (rule_tac C = "\<lambda>n. {}" in that) auto
next
  case False
  then obtain a where "a \<in> S"
    by auto
  let ?C = "\<lambda>n. cball a (real n) - (\<Union>x \<in> -S. \<Union>e \<in> ball 0 (1 / real(Suc n)). {x + e})"
  have "\<exists>N. \<forall>n\<ge>N. K \<subseteq> (f n)"
        if "\<And>n. compact(f n)" and sub_int: "\<And>n. f n \<subseteq> interior (f(Suc n))"
            and eq: "\<Union>(range f) = S" and "compact K" "K \<subseteq> S" for f K
  proof -
    have *: "\<forall>n. f n \<subseteq> (\<Union>n. interior (f n))"
      by (meson Sup_upper2 UNIV_I \<open>\<And>n. f n \<subseteq> interior (f (Suc n))\<close> image_iff)
    have mono: "\<And>m n. m \<le> n \<Longrightarrow>f m \<subseteq> f n"
      by (meson dual_order.trans interior_subset lift_Suc_mono_le sub_int)
    obtain I where "finite I" and I: "K \<subseteq> (\<Union>i\<in>I. interior (f i))"
    proof (rule compactE_image [OF \<open>compact K\<close>])
      show "K \<subseteq> (\<Union>n. interior (f n))"
        using \<open>K \<subseteq> S\<close> \<open>\<Union>(f ` UNIV) = S\<close> * by blast
    qed auto
    { fix n
      assume n: "Max I \<le> n"
      have "(\<Union>i\<in>I. interior (f i)) \<subseteq> f n"
        by (rule UN_least) (meson dual_order.trans interior_subset mono I Max_ge [OF \<open>finite I\<close>] n)
      then have "K \<subseteq> f n"
        using I by auto
    }
    then show ?thesis
      by blast
  qed
  moreover have "\<exists>f. (\<forall>n. compact(f n)) \<and> (\<forall>n. (f n) \<subseteq> S) \<and> (\<forall>n. (f n) \<subseteq> interior(f(Suc n))) \<and>
                     ((\<Union>(range f) = S))"
  proof (intro exI conjI allI)
    show "\<And>n. compact (?C n)"
      by (auto simp: compact_diff open_sums)
    show "\<And>n. ?C n \<subseteq> S"
      by auto
    show "?C n \<subseteq> interior (?C (Suc n))" for n
    proof (simp add: interior_diff, rule Diff_mono)
      show "cball a (real n) \<subseteq> ball a (1 + real n)"
        by (simp add: cball_subset_ball_iff)
      have cl: "closed (\<Union>x\<in>- S. \<Union>e\<in>cball 0 (1 / (2 + real n)). {x + e})"
        using assms by (auto intro: closed_compact_sums)
      have "closure (\<Union>x\<in>- S. \<Union>y\<in>ball 0 (1 / (2 + real n)). {x + y})
            \<subseteq> (\<Union>x \<in> -S. \<Union>e \<in> cball 0 (1 / (2 + real n)). {x + e})"
        by (intro closure_minimal UN_mono ball_subset_cball order_refl cl)
      also have "... \<subseteq> (\<Union>x \<in> -S. \<Union>y\<in>ball 0 (1 / (1 + real n)). {x + y})"
        by (simp add: cball_subset_ball_iff field_split_simps UN_mono)
      finally show "closure (\<Union>x\<in>- S. \<Union>y\<in>ball 0 (1 / (2 + real n)). {x + y})
                    \<subseteq> (\<Union>x \<in> -S. \<Union>y\<in>ball 0 (1 / (1 + real n)). {x + y})" .
    qed
    have "S \<subseteq> \<Union> (range ?C)"
    proof
      fix x
      assume x: "x \<in> S"
      then obtain e where "e > 0" and e: "ball x e \<subseteq> S"
        using assms open_contains_ball by blast
      then obtain N1 where "N1 > 0" and N1: "real N1 > 1/e"
        using reals_Archimedean2
        by (metis divide_less_0_iff less_eq_real_def neq0_conv not_le of_nat_0 of_nat_1 of_nat_less_0_iff)
      obtain N2 where N2: "norm(x - a) \<le> real N2"
        by (meson real_arch_simple)
      have N12: "inverse((N1 + N2) + 1) \<le> inverse(N1)"
        using \<open>N1 > 0\<close> by (auto simp: field_split_simps)
      have "x \<noteq> y + z" if "y \<notin> S" "norm z < 1 / (1 + (real N1 + real N2))" for y z
      proof -
        have "e * real N1 < e * (1 + (real N1 + real N2))"
          by (simp add: \<open>0 < e\<close>)
        then have "1 / (1 + (real N1 + real N2)) < e"
          using N1 \<open>e > 0\<close>
          by (metis divide_less_eq less_trans mult.commute of_nat_add of_nat_less_0_iff of_nat_Suc)
        then have "x - z \<in> ball x e"
          using that by simp
        then have "x - z \<in> S"
          using e by blast
        with that show ?thesis
          by auto
      qed
      with N2 show "x \<in> \<Union> (range ?C)"
        by (rule_tac a = "N1+N2" in UN_I) (auto simp: dist_norm norm_minus_commute)
    qed
    then show "\<Union> (range ?C) = S" by auto
  qed
  ultimately show ?thesis
    using that by metis
qed


subsection\<open>Orthogonal complement\<close>

definition\<^marker>\<open>tag important\<close> orthogonal_comp ("_\<^sup>\<bottom>" [80] 80)
  where "orthogonal_comp W \<equiv> {x. \<forall>y \<in> W. orthogonal y x}"

proposition subspace_orthogonal_comp: "subspace (W\<^sup>\<bottom>)"
  unfolding subspace_def orthogonal_comp_def orthogonal_def
  by (auto simp: inner_right_distrib)

lemma orthogonal_comp_anti_mono:
  assumes "A \<subseteq> B"
  shows "B\<^sup>\<bottom> \<subseteq> A\<^sup>\<bottom>"
proof
  fix x assume x: "x \<in> B\<^sup>\<bottom>"
  show "x \<in> orthogonal_comp A" using x unfolding orthogonal_comp_def
    by (simp add: orthogonal_def, metis assms in_mono)
qed

lemma orthogonal_comp_null [simp]: "{0}\<^sup>\<bottom> = UNIV"
  by (auto simp: orthogonal_comp_def orthogonal_def)

lemma orthogonal_comp_UNIV [simp]: "UNIV\<^sup>\<bottom> = {0}"
  unfolding orthogonal_comp_def orthogonal_def
  by auto (use inner_eq_zero_iff in blast)

lemma orthogonal_comp_subset: "U \<subseteq> U\<^sup>\<bottom>\<^sup>\<bottom>"
  by (auto simp: orthogonal_comp_def orthogonal_def inner_commute)

lemma subspace_sum_minimal:
  assumes "S \<subseteq> U" "T \<subseteq> U" "subspace U"
  shows "S + T \<subseteq> U"
proof
  fix x
  assume "x \<in> S + T"
  then obtain xs xt where "xs \<in> S" "xt \<in> T" "x = xs+xt"
    by (meson set_plus_elim)
  then show "x \<in> U"
    by (meson assms subsetCE subspace_add)
qed

proposition subspace_sum_orthogonal_comp:
  fixes U :: "'a :: euclidean_space set"
  assumes "subspace U"
  shows "U + U\<^sup>\<bottom> = UNIV"
proof -
  obtain B where "B \<subseteq> U"
    and ortho: "pairwise orthogonal B" "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
    and "independent B" "card B = dim U" "span B = U"
    using orthonormal_basis_subspace [OF assms] by metis
  then have "finite B"
    by (simp add: indep_card_eq_dim_span)
  have *: "\<forall>x\<in>B. \<forall>y\<in>B. x \<bullet> y = (if x=y then 1 else 0)"
    using ortho norm_eq_1 by (auto simp: orthogonal_def pairwise_def)
  { fix v
    let ?u = "\<Sum>b\<in>B. (v \<bullet> b) *\<^sub>R b"
    have "v = ?u + (v - ?u)"
      by simp
    moreover have "?u \<in> U"
      by (metis (no_types, lifting) \<open>span B = U\<close> assms subspace_sum span_base span_mul)
    moreover have "(v - ?u) \<in> U\<^sup>\<bottom>"
    proof (clarsimp simp: orthogonal_comp_def orthogonal_def)
      fix y
      assume "y \<in> U"
      with \<open>span B = U\<close> span_finite [OF \<open>finite B\<close>]
      obtain u where u: "y = (\<Sum>b\<in>B. u b *\<^sub>R b)"
        by auto
      have "b \<bullet> (v - ?u) = 0" if "b \<in> B" for b
        using that \<open>finite B\<close>
        by (simp add: * algebra_simps inner_sum_right if_distrib [of "(*)v" for v] inner_commute cong: if_cong)
      then show "y \<bullet> (v - ?u) = 0"
        by (simp add: u inner_sum_left)
    qed
    ultimately have "v \<in> U + U\<^sup>\<bottom>"
      using set_plus_intro by fastforce
  } then show ?thesis
    by auto
qed

lemma orthogonal_Int_0:
  assumes "subspace U"
  shows "U \<inter> U\<^sup>\<bottom> = {0}"
  using orthogonal_comp_def orthogonal_self
  by (force simp: assms subspace_0 subspace_orthogonal_comp)

lemma orthogonal_comp_self:
  fixes U :: "'a :: euclidean_space set"
  assumes "subspace U"
  shows "U\<^sup>\<bottom>\<^sup>\<bottom> = U"
proof
  have ssU': "subspace (U\<^sup>\<bottom>)"
    by (simp add: subspace_orthogonal_comp)
  have "u \<in> U" if "u \<in> U\<^sup>\<bottom>\<^sup>\<bottom>" for u
  proof -
    obtain v w where "u = v+w" "v \<in> U" "w \<in> U\<^sup>\<bottom>"
      using subspace_sum_orthogonal_comp [OF assms] set_plus_elim by blast
    then have "u-v \<in> U\<^sup>\<bottom>"
      by simp
    moreover have "v \<in> U\<^sup>\<bottom>\<^sup>\<bottom>"
      using \<open>v \<in> U\<close> orthogonal_comp_subset by blast
    then have "u-v \<in> U\<^sup>\<bottom>\<^sup>\<bottom>"
      by (simp add: subspace_diff subspace_orthogonal_comp that)
    ultimately have "u-v = 0"
      using orthogonal_Int_0 ssU' by blast
    with \<open>v \<in> U\<close> show ?thesis
      by auto
  qed
  then show "U\<^sup>\<bottom>\<^sup>\<bottom> \<subseteq> U"
    by auto
qed (use orthogonal_comp_subset in auto)

lemma ker_orthogonal_comp_adjoint:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
  shows "f -` {0} = (range (adjoint f))\<^sup>\<bottom>"
proof -
  have "\<And>x. \<lbrakk>\<forall>y. y \<bullet> f x = 0\<rbrakk> \<Longrightarrow> f x = 0"
    using assms inner_commute all_zero_iff by metis
  then show ?thesis
    using assms 
    by (auto simp: orthogonal_comp_def orthogonal_def adjoint_works inner_commute)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>A non-injective linear function maps into a hyperplane.\<close>

lemma linear_surj_adj_imp_inj:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f" "surj (adjoint f)"
  shows "inj f"
proof -
  have "\<exists>x. y = adjoint f x" for y
    using assms by (simp add: surjD)
  then show "inj f"
    using assms unfolding inj_on_def image_def
    by (metis (no_types) adjoint_works euclidean_eqI)
qed

\<comment> \<open>\<^url>\<open>https://mathonline.wikidot.com/injectivity-and-surjectivity-of-the-adjoint-of-a-linear-map\<close>\<close>
lemma surj_adjoint_iff_inj [simp]:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
  shows  "surj (adjoint f) \<longleftrightarrow> inj f"
proof
  assume "surj (adjoint f)"
  then show "inj f"
    by (simp add: assms linear_surj_adj_imp_inj)
next
  assume "inj f"
  have "f -` {0} = {0}"
    using assms \<open>inj f\<close> linear_0 linear_injective_0 by fastforce
  moreover have "f -` {0} = range (adjoint f)\<^sup>\<bottom>"
    by (intro ker_orthogonal_comp_adjoint assms)
  ultimately have "range (adjoint f)\<^sup>\<bottom>\<^sup>\<bottom> = UNIV"
    by (metis orthogonal_comp_null)
  then show "surj (adjoint f)"
    using adjoint_linear \<open>linear f\<close>
    by (subst (asm) orthogonal_comp_self)
      (simp add: adjoint_linear linear_subspace_image)
qed

lemma inj_adjoint_iff_surj [simp]:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
  shows  "inj (adjoint f) \<longleftrightarrow> surj f"
proof
  assume "inj (adjoint f)"
  have "(adjoint f) -` {0} = {0}"
    by (metis \<open>inj (adjoint f)\<close> adjoint_linear assms surj_adjoint_iff_inj ker_orthogonal_comp_adjoint orthogonal_comp_UNIV)
  then have "(range(f))\<^sup>\<bottom> = {0}"
    by (metis (no_types, opaque_lifting) adjoint_adjoint adjoint_linear assms ker_orthogonal_comp_adjoint set_zero)
  then show "surj f"
    by (metis \<open>inj (adjoint f)\<close> adjoint_adjoint adjoint_linear assms surj_adjoint_iff_inj)
next
  assume "surj f"
  then have "range f = (adjoint f -` {0})\<^sup>\<bottom>"
    by (simp add: adjoint_adjoint adjoint_linear assms ker_orthogonal_comp_adjoint)
  then have "{0} = adjoint f -` {0}"
    using \<open>surj f\<close> adjoint_adjoint adjoint_linear assms ker_orthogonal_comp_adjoint by force
  then show "inj (adjoint f)"
    by (simp add: \<open>surj f\<close> adjoint_adjoint adjoint_linear assms linear_surj_adj_imp_inj)
qed

lemma linear_singular_into_hyperplane:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "linear f"
  shows "\<not> inj f \<longleftrightarrow> (\<exists>a. a \<noteq> 0 \<and> (\<forall>x. a \<bullet> f x = 0))" (is "_ = ?rhs")
proof
  assume "\<not>inj f"
  then show ?rhs
    using all_zero_iff
    by (metis (no_types, opaque_lifting) adjoint_clauses(2) adjoint_linear assms
        linear_injective_0 linear_injective_imp_surjective linear_surj_adj_imp_inj)
next
  assume ?rhs
  then show "\<not>inj f"
    by (metis assms linear_injective_isomorphism all_zero_iff)
qed

lemma linear_singular_image_hyperplane:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "linear f" "\<not>inj f"
  obtains a where "a \<noteq> 0" "\<And>S. f ` S \<subseteq> {x. a \<bullet> x = 0}"
  using assms by (fastforce simp add: linear_singular_into_hyperplane)

end
