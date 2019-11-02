(* Title:      HOL/Analysis/Starlike.thy
   Author:     L C Paulson, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
   Author:     Bogdan Grechuk, University of Edinburgh
   Author:     Armin Heller, TU Muenchen
   Author:     Johannes Hoelzl, TU Muenchen
*)
chapter \<open>Unsorted\<close>

theory Starlike
imports Convex_Euclidean_Space Abstract_Limits
begin

section \<open>Line Segments\<close>

subsection \<open>Midpoint\<close>

definition\<^marker>\<open>tag important\<close> midpoint :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a"
  where "midpoint a b = (inverse (2::real)) *\<^sub>R (a + b)"

lemma midpoint_idem [simp]: "midpoint x x = x"
  unfolding midpoint_def  by simp

lemma midpoint_sym: "midpoint a b = midpoint b a"
  unfolding midpoint_def by (auto simp add: scaleR_right_distrib)

lemma midpoint_eq_iff: "midpoint a b = c \<longleftrightarrow> a + b = c + c"
proof -
  have "midpoint a b = c \<longleftrightarrow> scaleR 2 (midpoint a b) = scaleR 2 c"
    by simp
  then show ?thesis
    unfolding midpoint_def scaleR_2 [symmetric] by simp
qed

lemma
  fixes a::real
  assumes "a \<le> b" shows ge_midpoint_1: "a \<le> midpoint a b"
                    and le_midpoint_1: "midpoint a b \<le> b"
  by (simp_all add: midpoint_def assms)

lemma dist_midpoint:
  fixes a b :: "'a::real_normed_vector" shows
  "dist a (midpoint a b) = (dist a b) / 2" (is ?t1)
  "dist b (midpoint a b) = (dist a b) / 2" (is ?t2)
  "dist (midpoint a b) a = (dist a b) / 2" (is ?t3)
  "dist (midpoint a b) b = (dist a b) / 2" (is ?t4)
proof -
  have *: "\<And>x y::'a. 2 *\<^sub>R x = - y \<Longrightarrow> norm x = (norm y) / 2"
    unfolding equation_minus_iff by auto
  have **: "\<And>x y::'a. 2 *\<^sub>R x =   y \<Longrightarrow> norm x = (norm y) / 2"
    by auto
  note scaleR_right_distrib [simp]
  show ?t1
    unfolding midpoint_def dist_norm
    apply (rule **)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
  show ?t2
    unfolding midpoint_def dist_norm
    apply (rule *)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
  show ?t3
    unfolding midpoint_def dist_norm
    apply (rule *)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
  show ?t4
    unfolding midpoint_def dist_norm
    apply (rule **)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
qed

lemma midpoint_eq_endpoint [simp]:
  "midpoint a b = a \<longleftrightarrow> a = b"
  "midpoint a b = b \<longleftrightarrow> a = b"
  unfolding midpoint_eq_iff by auto

lemma midpoint_plus_self [simp]: "midpoint a b + midpoint a b = a + b"
  using midpoint_eq_iff by metis

lemma midpoint_linear_image:
   "linear f \<Longrightarrow> midpoint(f a)(f b) = f(midpoint a b)"
by (simp add: linear_iff midpoint_def)


subsection \<open>Line segments\<close>

definition\<^marker>\<open>tag important\<close> closed_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "closed_segment a b = {(1 - u) *\<^sub>R a + u *\<^sub>R b | u::real. 0 \<le> u \<and> u \<le> 1}"

definition\<^marker>\<open>tag important\<close> open_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_segment a b \<equiv> closed_segment a b - {a,b}"

lemmas segment = open_segment_def closed_segment_def

lemma in_segment:
    "x \<in> closed_segment a b \<longleftrightarrow> (\<exists>u. 0 \<le> u \<and> u \<le> 1 \<and> x = (1 - u) *\<^sub>R a + u *\<^sub>R b)"
    "x \<in> open_segment a b \<longleftrightarrow> a \<noteq> b \<and> (\<exists>u. 0 < u \<and> u < 1 \<and> x = (1 - u) *\<^sub>R a + u *\<^sub>R b)"
  using less_eq_real_def by (auto simp: segment algebra_simps)

lemma closed_segment_linear_image:
  "closed_segment (f a) (f b) = f ` (closed_segment a b)" if "linear f"
proof -
  interpret linear f by fact
  show ?thesis
    by (force simp add: in_segment add scale)
qed

lemma open_segment_linear_image:
    "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> open_segment (f a) (f b) = f ` (open_segment a b)"
  by (force simp: open_segment_def closed_segment_linear_image inj_on_def)

lemma closed_segment_translation:
    "closed_segment (c + a) (c + b) = image (\<lambda>x. c + x) (closed_segment a b)"
apply safe
apply (rule_tac x="x-c" in image_eqI)
apply (auto simp: in_segment algebra_simps)
done

lemma open_segment_translation:
    "open_segment (c + a) (c + b) = image (\<lambda>x. c + x) (open_segment a b)"
by (simp add: open_segment_def closed_segment_translation translation_diff)

lemma closed_segment_of_real:
    "closed_segment (of_real x) (of_real y) = of_real ` closed_segment x y"
  apply (auto simp: image_iff in_segment scaleR_conv_of_real)
    apply (rule_tac x="(1-u)*x + u*y" in bexI)
  apply (auto simp: in_segment)
  done

lemma open_segment_of_real:
    "open_segment (of_real x) (of_real y) = of_real ` open_segment x y"
  apply (auto simp: image_iff in_segment scaleR_conv_of_real)
    apply (rule_tac x="(1-u)*x + u*y" in bexI)
  apply (auto simp: in_segment)
  done

lemma closed_segment_Reals:
    "\<lbrakk>x \<in> Reals; y \<in> Reals\<rbrakk> \<Longrightarrow> closed_segment x y = of_real ` closed_segment (Re x) (Re y)"
  by (metis closed_segment_of_real of_real_Re)

lemma open_segment_Reals:
    "\<lbrakk>x \<in> Reals; y \<in> Reals\<rbrakk> \<Longrightarrow> open_segment x y = of_real ` open_segment (Re x) (Re y)"
  by (metis open_segment_of_real of_real_Re)

lemma open_segment_PairD:
    "(x, x') \<in> open_segment (a, a') (b, b')
     \<Longrightarrow> (x \<in> open_segment a b \<or> a = b) \<and> (x' \<in> open_segment a' b' \<or> a' = b')"
  by (auto simp: in_segment)

lemma closed_segment_PairD:
  "(x, x') \<in> closed_segment (a, a') (b, b') \<Longrightarrow> x \<in> closed_segment a b \<and> x' \<in> closed_segment a' b'"
  by (auto simp: closed_segment_def)

lemma closed_segment_translation_eq [simp]:
    "d + x \<in> closed_segment (d + a) (d + b) \<longleftrightarrow> x \<in> closed_segment a b"
proof -
  have *: "\<And>d x a b. x \<in> closed_segment a b \<Longrightarrow> d + x \<in> closed_segment (d + a) (d + b)"
    apply (simp add: closed_segment_def)
    apply (erule ex_forward)
    apply (simp add: algebra_simps)
    done
  show ?thesis
  using * [where d = "-d"] *
  by (fastforce simp add:)
qed

lemma open_segment_translation_eq [simp]:
    "d + x \<in> open_segment (d + a) (d + b) \<longleftrightarrow> x \<in> open_segment a b"
  by (simp add: open_segment_def)

lemma of_real_closed_segment [simp]:
  "of_real x \<in> closed_segment (of_real a) (of_real b) \<longleftrightarrow> x \<in> closed_segment a b"
  apply (auto simp: in_segment scaleR_conv_of_real elim!: ex_forward)
  using of_real_eq_iff by fastforce

lemma of_real_open_segment [simp]:
  "of_real x \<in> open_segment (of_real a) (of_real b) \<longleftrightarrow> x \<in> open_segment a b"
  apply (auto simp: in_segment scaleR_conv_of_real elim!: ex_forward del: exE)
  using of_real_eq_iff by fastforce

lemma convex_contains_segment:
  "convex S \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. closed_segment a b \<subseteq> S)"
  unfolding convex_alt closed_segment_def by auto

lemma closed_segment_in_Reals:
   "\<lbrakk>x \<in> closed_segment a b; a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> x \<in> Reals"
  by (meson subsetD convex_Reals convex_contains_segment)

lemma open_segment_in_Reals:
   "\<lbrakk>x \<in> open_segment a b; a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> x \<in> Reals"
  by (metis Diff_iff closed_segment_in_Reals open_segment_def)

lemma closed_segment_subset: "\<lbrakk>x \<in> S; y \<in> S; convex S\<rbrakk> \<Longrightarrow> closed_segment x y \<subseteq> S"
  by (simp add: convex_contains_segment)

lemma closed_segment_subset_convex_hull:
    "\<lbrakk>x \<in> convex hull S; y \<in> convex hull S\<rbrakk> \<Longrightarrow> closed_segment x y \<subseteq> convex hull S"
  using convex_contains_segment by blast

lemma segment_convex_hull:
  "closed_segment a b = convex hull {a,b}"
proof -
  have *: "\<And>x. {x} \<noteq> {}" by auto
  show ?thesis
    unfolding segment convex_hull_insert[OF *] convex_hull_singleton
    by (safe; rule_tac x="1 - u" in exI; force)
qed

lemma open_closed_segment: "u \<in> open_segment w z \<Longrightarrow> u \<in> closed_segment w z"
  by (auto simp add: closed_segment_def open_segment_def)

lemma segment_open_subset_closed:
   "open_segment a b \<subseteq> closed_segment a b"
  by (auto simp: closed_segment_def open_segment_def)

lemma bounded_closed_segment:
    fixes a :: "'a::euclidean_space" shows "bounded (closed_segment a b)"
  by (simp add: segment_convex_hull compact_convex_hull compact_imp_bounded)

lemma bounded_open_segment:
    fixes a :: "'a::euclidean_space" shows "bounded (open_segment a b)"
  by (rule bounded_subset [OF bounded_closed_segment segment_open_subset_closed])

lemmas bounded_segment = bounded_closed_segment open_closed_segment

lemma ends_in_segment [iff]: "a \<in> closed_segment a b" "b \<in> closed_segment a b"
  unfolding segment_convex_hull
  by (auto intro!: hull_subset[unfolded subset_eq, rule_format])

lemma eventually_closed_segment:
  fixes x0::"'a::real_normed_vector"
  assumes "open X0" "x0 \<in> X0"
  shows "\<forall>\<^sub>F x in at x0 within U. closed_segment x0 x \<subseteq> X0"
proof -
  from openE[OF assms]
  obtain e where e: "0 < e" "ball x0 e \<subseteq> X0" .
  then have "\<forall>\<^sub>F x in at x0 within U. x \<in> ball x0 e"
    by (auto simp: dist_commute eventually_at)
  then show ?thesis
  proof eventually_elim
    case (elim x)
    have "x0 \<in> ball x0 e" using \<open>e > 0\<close> by simp
    from convex_ball[unfolded convex_contains_segment, rule_format, OF this elim]
    have "closed_segment x0 x \<subseteq> ball x0 e" .
    also note \<open>\<dots> \<subseteq> X0\<close>
    finally show ?case .
  qed
qed

lemma segment_furthest_le:
  fixes a b x y :: "'a::euclidean_space"
  assumes "x \<in> closed_segment a b"
  shows "norm (y - x) \<le> norm (y - a) \<or>  norm (y - x) \<le> norm (y - b)"
proof -
  obtain z where "z \<in> {a, b}" "norm (x - y) \<le> norm (z - y)"
    using simplex_furthest_le[of "{a, b}" y]
    using assms[unfolded segment_convex_hull]
    by auto
  then show ?thesis
    by (auto simp add:norm_minus_commute)
qed

lemma closed_segment_commute: "closed_segment a b = closed_segment b a"
proof -
  have "{a, b} = {b, a}" by auto
  thus ?thesis
    by (simp add: segment_convex_hull)
qed

lemma segment_bound1:
  assumes "x \<in> closed_segment a b"
  shows "norm (x - a) \<le> norm (b - a)"
proof -
  obtain u where "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
    using assms by (auto simp add: closed_segment_def)
  then show "norm (x - a) \<le> norm (b - a)"
    apply clarify
    apply (auto simp: algebra_simps)
    apply (simp add: scaleR_diff_right [symmetric] mult_left_le_one_le)
    done
qed

lemma segment_bound:
  assumes "x \<in> closed_segment a b"
  shows "norm (x - a) \<le> norm (b - a)" "norm (x - b) \<le> norm (b - a)"
apply (simp add: assms segment_bound1)
by (metis assms closed_segment_commute dist_commute dist_norm segment_bound1)

lemma open_segment_commute: "open_segment a b = open_segment b a"
proof -
  have "{a, b} = {b, a}" by auto
  thus ?thesis
    by (simp add: closed_segment_commute open_segment_def)
qed

lemma closed_segment_idem [simp]: "closed_segment a a = {a}"
  unfolding segment by (auto simp add: algebra_simps)

lemma open_segment_idem [simp]: "open_segment a a = {}"
  by (simp add: open_segment_def)

lemma closed_segment_eq_open: "closed_segment a b = open_segment a b \<union> {a,b}"
  using open_segment_def by auto

lemma convex_contains_open_segment:
  "convex s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. open_segment a b \<subseteq> s)"
  by (simp add: convex_contains_segment closed_segment_eq_open)

lemma closed_segment_eq_real_ivl:
  fixes a b::real
  shows "closed_segment a b = (if a \<le> b then {a .. b} else {b .. a})"
proof -
  have "b \<le> a \<Longrightarrow> closed_segment b a = {b .. a}"
    and "a \<le> b \<Longrightarrow> closed_segment a b = {a .. b}"
    by (auto simp: convex_hull_eq_real_cbox segment_convex_hull)
  thus ?thesis
    by (auto simp: closed_segment_commute)
qed

lemma open_segment_eq_real_ivl:
  fixes a b::real
  shows "open_segment a b = (if a \<le> b then {a<..<b} else {b<..<a})"
by (auto simp: closed_segment_eq_real_ivl open_segment_def split: if_split_asm)

lemma closed_segment_real_eq:
  fixes u::real shows "closed_segment u v = (\<lambda>x. (v - u) * x + u) ` {0..1}"
  by (simp add: add.commute [of u] image_affinity_atLeastAtMost [where c=u] closed_segment_eq_real_ivl)

lemma dist_in_closed_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> closed_segment a b"
    shows "dist x a \<le> dist a b \<and> dist x b \<le> dist a b"
proof (intro conjI)
  obtain u where u: "0 \<le> u" "u \<le> 1" and x: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
    using assms by (force simp: in_segment algebra_simps)
  have "dist x a = u * dist a b"
    apply (simp add: dist_norm algebra_simps x)
    by (metis \<open>0 \<le> u\<close> abs_of_nonneg norm_minus_commute norm_scaleR real_vector.scale_right_diff_distrib)
  also have "...  \<le> dist a b"
    by (simp add: mult_left_le_one_le u)
  finally show "dist x a \<le> dist a b" .
  have "dist x b = norm ((1-u) *\<^sub>R a - (1-u) *\<^sub>R b)"
    by (simp add: dist_norm algebra_simps x)
  also have "... = (1-u) * dist a b"
  proof -
    have "norm ((1 - 1 * u) *\<^sub>R (a - b)) = (1 - 1 * u) * norm (a - b)"
      using \<open>u \<le> 1\<close> by force
    then show ?thesis
      by (simp add: dist_norm real_vector.scale_right_diff_distrib)
  qed
  also have "... \<le> dist a b"
    by (simp add: mult_left_le_one_le u)
  finally show "dist x b \<le> dist a b" .
qed

lemma dist_in_open_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> open_segment a b"
    shows "dist x a < dist a b \<and> dist x b < dist a b"
proof (intro conjI)
  obtain u where u: "0 < u" "u < 1" and x: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
    using assms by (force simp: in_segment algebra_simps)
  have "dist x a = u * dist a b"
    apply (simp add: dist_norm algebra_simps x)
    by (metis abs_of_nonneg less_eq_real_def norm_minus_commute norm_scaleR real_vector.scale_right_diff_distrib \<open>0 < u\<close>)
  also have *: "...  < dist a b"
    by (metis (no_types) assms dist_eq_0_iff dist_not_less_zero in_segment(2) linorder_neqE_linordered_idom mult.left_neutral real_mult_less_iff1 \<open>u < 1\<close>)
  finally show "dist x a < dist a b" .
  have ab_ne0: "dist a b \<noteq> 0"
    using * by fastforce
  have "dist x b = norm ((1-u) *\<^sub>R a - (1-u) *\<^sub>R b)"
    by (simp add: dist_norm algebra_simps x)
  also have "... = (1-u) * dist a b"
  proof -
    have "norm ((1 - 1 * u) *\<^sub>R (a - b)) = (1 - 1 * u) * norm (a - b)"
      using \<open>u < 1\<close> by force
    then show ?thesis
      by (simp add: dist_norm real_vector.scale_right_diff_distrib)
  qed
  also have "... < dist a b"
    using ab_ne0 \<open>0 < u\<close> by simp
  finally show "dist x b < dist a b" .
qed

lemma dist_decreases_open_segment_0:
  fixes x :: "'a :: euclidean_space"
  assumes "x \<in> open_segment 0 b"
    shows "dist c x < dist c 0 \<or> dist c x < dist c b"
proof (rule ccontr, clarsimp simp: not_less)
  obtain u where u: "0 \<noteq> b" "0 < u" "u < 1" and x: "x = u *\<^sub>R b"
    using assms by (auto simp: in_segment)
  have xb: "x \<bullet> b < b \<bullet> b"
    using u x by auto
  assume "norm c \<le> dist c x"
  then have "c \<bullet> c \<le> (c - x) \<bullet> (c - x)"
    by (simp add: dist_norm norm_le)
  moreover have "0 < x \<bullet> b"
    using u x by auto
  ultimately have less: "c \<bullet> b < x \<bullet> b"
    by (simp add: x algebra_simps inner_commute u)
  assume "dist c b \<le> dist c x"
  then have "(c - b) \<bullet> (c - b) \<le> (c - x) \<bullet> (c - x)"
    by (simp add: dist_norm norm_le)
  then have "(b \<bullet> b) * (1 - u*u) \<le> 2 * (b \<bullet> c) * (1-u)"
    by (simp add: x algebra_simps inner_commute)
  then have "(1+u) * (b \<bullet> b) * (1-u) \<le> 2 * (b \<bullet> c) * (1-u)"
    by (simp add: algebra_simps)
  then have "(1+u) * (b \<bullet> b) \<le> 2 * (b \<bullet> c)"
    using \<open>u < 1\<close> by auto
  with xb have "c \<bullet> b \<ge> x \<bullet> b"
    by (auto simp: x algebra_simps inner_commute)
  with less show False by auto
qed

proposition dist_decreases_open_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> open_segment a b"
    shows "dist c x < dist c a \<or> dist c x < dist c b"
proof -
  have *: "x - a \<in> open_segment 0 (b - a)" using assms
    by (metis diff_self open_segment_translation_eq uminus_add_conv_diff)
  show ?thesis
    using dist_decreases_open_segment_0 [OF *, of "c-a"] assms
    by (simp add: dist_norm)
qed

corollary open_segment_furthest_le:
  fixes a b x y :: "'a::euclidean_space"
  assumes "x \<in> open_segment a b"
  shows "norm (y - x) < norm (y - a) \<or>  norm (y - x) < norm (y - b)"
  by (metis assms dist_decreases_open_segment dist_norm)

corollary dist_decreases_closed_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> closed_segment a b"
    shows "dist c x \<le> dist c a \<or> dist c x \<le> dist c b"
apply (cases "x \<in> open_segment a b")
 using dist_decreases_open_segment less_eq_real_def apply blast
by (metis DiffI assms empty_iff insertE open_segment_def order_refl)

lemma convex_intermediate_ball:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>ball a r \<subseteq> T; T \<subseteq> cball a r\<rbrakk> \<Longrightarrow> convex T"
apply (simp add: convex_contains_open_segment, clarify)
by (metis (no_types, hide_lams) less_le_trans mem_ball mem_cball subsetCE dist_decreases_open_segment)

lemma csegment_midpoint_subset: "closed_segment (midpoint a b) b \<subseteq> closed_segment a b"
  apply (clarsimp simp: midpoint_def in_segment)
  apply (rule_tac x="(1 + u) / 2" in exI)
  apply (auto simp: algebra_simps add_divide_distrib diff_divide_distrib)
  by (metis field_sum_of_halves scaleR_left.add)

lemma notin_segment_midpoint:
  fixes a :: "'a :: euclidean_space"
  shows "a \<noteq> b \<Longrightarrow> a \<notin> closed_segment (midpoint a b) b"
by (auto simp: dist_midpoint dest!: dist_in_closed_segment)

lemma segment_to_closest_point:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>closed S; S \<noteq> {}\<rbrakk> \<Longrightarrow> open_segment a (closest_point S a) \<inter> S = {}"
  apply (subst disjoint_iff_not_equal)
  apply (clarify dest!: dist_in_open_segment)
  by (metis closest_point_le dist_commute le_less_trans less_irrefl)

lemma segment_to_point_exists:
  fixes S :: "'a :: euclidean_space set"
    assumes "closed S" "S \<noteq> {}"
    obtains b where "b \<in> S" "open_segment a b \<inter> S = {}"
  by (metis assms segment_to_closest_point closest_point_exists that)

subsubsection\<open>More lemmas, especially for working with the underlying formula\<close>

lemma segment_eq_compose:
  fixes a :: "'a :: real_vector"
  shows "(\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) = (\<lambda>x. a + x) o (\<lambda>u. u *\<^sub>R (b - a))"
    by (simp add: o_def algebra_simps)

lemma segment_degen_1:
  fixes a :: "'a :: real_vector"
  shows "(1 - u) *\<^sub>R a + u *\<^sub>R b = b \<longleftrightarrow> a=b \<or> u=1"
proof -
  { assume "(1 - u) *\<^sub>R a + u *\<^sub>R b = b"
    then have "(1 - u) *\<^sub>R a = (1 - u) *\<^sub>R b"
      by (simp add: algebra_simps)
    then have "a=b \<or> u=1"
      by simp
  } then show ?thesis
      by (auto simp: algebra_simps)
qed

lemma segment_degen_0:
    fixes a :: "'a :: real_vector"
    shows "(1 - u) *\<^sub>R a + u *\<^sub>R b = a \<longleftrightarrow> a=b \<or> u=0"
  using segment_degen_1 [of "1-u" b a]
  by (auto simp: algebra_simps)

lemma add_scaleR_degen:
  fixes a b ::"'a::real_vector"
  assumes  "(u *\<^sub>R b + v *\<^sub>R a) = (u *\<^sub>R a + v *\<^sub>R b)"  "u \<noteq> v"
  shows "a=b"
  by (metis (no_types, hide_lams) add.commute add_diff_eq diff_add_cancel real_vector.scale_cancel_left real_vector.scale_left_diff_distrib assms)
  
lemma closed_segment_image_interval:
     "closed_segment a b = (\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) ` {0..1}"
  by (auto simp: set_eq_iff image_iff closed_segment_def)

lemma open_segment_image_interval:
     "open_segment a b = (if a=b then {} else (\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) ` {0<..<1})"
  by (auto simp:  open_segment_def closed_segment_def segment_degen_0 segment_degen_1)

lemmas segment_image_interval = closed_segment_image_interval open_segment_image_interval

lemma open_segment_bound1:
  assumes "x \<in> open_segment a b"
  shows "norm (x - a) < norm (b - a)"
proof -
  obtain u where "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 < u" "u < 1" "a \<noteq> b"
    using assms by (auto simp add: open_segment_image_interval split: if_split_asm)
  then show "norm (x - a) < norm (b - a)"
    apply clarify
    apply (auto simp: algebra_simps)
    apply (simp add: scaleR_diff_right [symmetric])
    done
qed

lemma compact_segment [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "compact (closed_segment a b)"
  by (auto simp: segment_image_interval intro!: compact_continuous_image continuous_intros)

lemma closed_segment [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "closed (closed_segment a b)"
  by (simp add: compact_imp_closed)

lemma closure_closed_segment [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "closure(closed_segment a b) = closed_segment a b"
  by simp

lemma open_segment_bound:
  assumes "x \<in> open_segment a b"
  shows "norm (x - a) < norm (b - a)" "norm (x - b) < norm (b - a)"
apply (simp add: assms open_segment_bound1)
by (metis assms norm_minus_commute open_segment_bound1 open_segment_commute)

lemma closure_open_segment [simp]:
  "closure (open_segment a b) = (if a = b then {} else closed_segment a b)"
    for a :: "'a::euclidean_space"
proof (cases "a = b")
  case True
  then show ?thesis
    by simp
next
  case False
  have "closure ((\<lambda>u. u *\<^sub>R (b - a)) ` {0<..<1}) = (\<lambda>u. u *\<^sub>R (b - a)) ` closure {0<..<1}"
    apply (rule closure_injective_linear_image [symmetric])
     apply (use False in \<open>auto intro!: injI\<close>)
    done
  then have "closure
     ((\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) ` {0<..<1}) =
    (\<lambda>x. (1 - x) *\<^sub>R a + x *\<^sub>R b) ` closure {0<..<1}"
    using closure_translation [of a "((\<lambda>x. x *\<^sub>R b - x *\<^sub>R a) ` {0<..<1})"]
    by (simp add: segment_eq_compose field_simps scaleR_diff_left scaleR_diff_right image_image)
  then show ?thesis
    by (simp add: segment_image_interval closure_greaterThanLessThan [symmetric] del: closure_greaterThanLessThan)
qed

lemma closed_open_segment_iff [simp]:
    fixes a :: "'a::euclidean_space"  shows "closed(open_segment a b) \<longleftrightarrow> a = b"
  by (metis open_segment_def DiffE closure_eq closure_open_segment ends_in_segment(1) insert_iff segment_image_interval(2))

lemma compact_open_segment_iff [simp]:
    fixes a :: "'a::euclidean_space"  shows "compact(open_segment a b) \<longleftrightarrow> a = b"
  by (simp add: bounded_open_segment compact_eq_bounded_closed)

lemma convex_closed_segment [iff]: "convex (closed_segment a b)"
  unfolding segment_convex_hull by(rule convex_convex_hull)

lemma convex_open_segment [iff]: "convex (open_segment a b)"
proof -
  have "convex ((\<lambda>u. u *\<^sub>R (b - a)) ` {0<..<1})"
    by (rule convex_linear_image) auto
  then have "convex ((+) a ` (\<lambda>u. u *\<^sub>R (b - a)) ` {0<..<1})"
    by (rule convex_translation)
  then show ?thesis
    by (simp add: image_image open_segment_image_interval segment_eq_compose field_simps scaleR_diff_left scaleR_diff_right)
qed

lemmas convex_segment = convex_closed_segment convex_open_segment

lemma connected_segment [iff]:
  fixes x :: "'a :: real_normed_vector"
  shows "connected (closed_segment x y)"
  by (simp add: convex_connected)

lemma is_interval_closed_segment_1[intro, simp]: "is_interval (closed_segment a b)" for a b::real
  by (auto simp: is_interval_convex_1)

lemma IVT'_closed_segment_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "y \<in> closed_segment (f a) (f b)"
  assumes "continuous_on (closed_segment a b) f"
  shows "\<exists>x \<in> closed_segment a b. f x = y"
  using IVT'[of f a y b]
    IVT'[of "-f" a "-y" b]
    IVT'[of f b y a]
    IVT'[of "-f" b "-y" a] assms
  by (cases "a \<le> b"; cases "f b \<ge> f a") (auto simp: closed_segment_eq_real_ivl continuous_on_minus)


subsection\<open>Starlike sets\<close>

definition\<^marker>\<open>tag important\<close> "starlike S \<longleftrightarrow> (\<exists>a\<in>S. \<forall>x\<in>S. closed_segment a x \<subseteq> S)"

lemma starlike_UNIV [simp]: "starlike UNIV"
  by (simp add: starlike_def)

lemma convex_imp_starlike:
  "convex S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> starlike S"
  unfolding convex_contains_segment starlike_def by auto


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

subsection\<^marker>\<open>tag unimportant\<close>\<open>More results about segments\<close>

lemma dist_half_times2:
  fixes a :: "'a :: real_normed_vector"
  shows "dist ((1 / 2) *\<^sub>R (a + b)) x * 2 = dist (a+b) (2 *\<^sub>R x)"
proof -
  have "norm ((1 / 2) *\<^sub>R (a + b) - x) * 2 = norm (2 *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x))"
    by simp
  also have "... = norm ((a + b) - 2 *\<^sub>R x)"
    by (simp add: real_vector.scale_right_diff_distrib)
  finally show ?thesis
    by (simp only: dist_norm)
qed

lemma closed_segment_as_ball:
    "closed_segment a b = affine hull {a,b} \<inter> cball(inverse 2 *\<^sub>R (a + b))(norm(b - a) / 2)"
proof (cases "b = a")
  case True then show ?thesis by (auto simp: hull_inc)
next
  case False
  then have *: "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 \<le> norm (b - a)) =
                 (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1)" for x
  proof -
    have "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 \<le> norm (b - a)) =
          ((\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 \<le> norm (b - a))"
      unfolding eq_diff_eq [symmetric] by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          norm ((a+b) - (2 *\<^sub>R x)) \<le> norm (b - a))"
      by (simp add: dist_half_times2) (simp add: dist_norm)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
            norm ((a+b) - (2 *\<^sub>R ((1 - u) *\<^sub>R a + u *\<^sub>R b))) \<le> norm (b - a))"
      by auto
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                norm ((1 - u * 2) *\<^sub>R (b - a)) \<le> norm (b - a))"
      by (simp add: algebra_simps scaleR_2)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          \<bar>1 - u * 2\<bar> * norm (b - a) \<le> norm (b - a))"
      by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> \<bar>1 - u * 2\<bar> \<le> 1)"
      by (simp add: mult_le_cancel_right2 False)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1)"
      by auto
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: affine_hull_2 Set.set_eq_iff closed_segment_def *)
qed

lemma open_segment_as_ball:
    "open_segment a b =
     affine hull {a,b} \<inter> ball(inverse 2 *\<^sub>R (a + b))(norm(b - a) / 2)"
proof (cases "b = a")
  case True then show ?thesis by (auto simp: hull_inc)
next
  case False
  then have *: "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 < norm (b - a)) =
                 (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 < u \<and> u < 1)" for x
  proof -
    have "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 < norm (b - a)) =
          ((\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 < norm (b - a))"
      unfolding eq_diff_eq [symmetric] by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          norm ((a+b) - (2 *\<^sub>R x)) < norm (b - a))"
      by (simp add: dist_half_times2) (simp add: dist_norm)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
            norm ((a+b) - (2 *\<^sub>R ((1 - u) *\<^sub>R a + u *\<^sub>R b))) < norm (b - a))"
      by auto
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                norm ((1 - u * 2) *\<^sub>R (b - a)) < norm (b - a))"
      by (simp add: algebra_simps scaleR_2)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          \<bar>1 - u * 2\<bar> * norm (b - a) < norm (b - a))"
      by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> \<bar>1 - u * 2\<bar> < 1)"
      by (simp add: mult_le_cancel_right2 False)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 < u \<and> u < 1)"
      by auto
    finally show ?thesis .
  qed
  show ?thesis
    using False by (force simp: affine_hull_2 Set.set_eq_iff open_segment_image_interval *)
qed

lemmas segment_as_ball = closed_segment_as_ball open_segment_as_ball

lemma closed_segment_neq_empty [simp]: "closed_segment a b \<noteq> {}"
  by auto

lemma open_segment_eq_empty [simp]: "open_segment a b = {} \<longleftrightarrow> a = b"
proof -
  { assume a1: "open_segment a b = {}"
    have "{} \<noteq> {0::real<..<1}"
      by simp
    then have "a = b"
      using a1 open_segment_image_interval by fastforce
  } then show ?thesis by auto
qed

lemma open_segment_eq_empty' [simp]: "{} = open_segment a b \<longleftrightarrow> a = b"
  using open_segment_eq_empty by blast

lemmas segment_eq_empty = closed_segment_neq_empty open_segment_eq_empty

lemma inj_segment:
  fixes a :: "'a :: real_vector"
  assumes "a \<noteq> b"
    shows "inj_on (\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) I"
proof
  fix x y
  assume "(1 - x) *\<^sub>R a + x *\<^sub>R b = (1 - y) *\<^sub>R a + y *\<^sub>R b"
  then have "x *\<^sub>R (b - a) = y *\<^sub>R (b - a)"
    by (simp add: algebra_simps)
  with assms show "x = y"
    by (simp add: real_vector.scale_right_imp_eq)
qed

lemma finite_closed_segment [simp]: "finite(closed_segment a b) \<longleftrightarrow> a = b"
  apply auto
  apply (rule ccontr)
  apply (simp add: segment_image_interval)
  using infinite_Icc [OF zero_less_one] finite_imageD [OF _ inj_segment] apply blast
  done

lemma finite_open_segment [simp]: "finite(open_segment a b) \<longleftrightarrow> a = b"
  by (auto simp: open_segment_def)

lemmas finite_segment = finite_closed_segment finite_open_segment

lemma closed_segment_eq_sing: "closed_segment a b = {c} \<longleftrightarrow> a = c \<and> b = c"
  by auto

lemma open_segment_eq_sing: "open_segment a b \<noteq> {c}"
  by (metis finite_insert finite_open_segment insert_not_empty open_segment_image_interval)

lemmas segment_eq_sing = closed_segment_eq_sing open_segment_eq_sing

lemma subset_closed_segment:
    "closed_segment a b \<subseteq> closed_segment c d \<longleftrightarrow>
     a \<in> closed_segment c d \<and> b \<in> closed_segment c d"
  by auto (meson contra_subsetD convex_closed_segment convex_contains_segment)

lemma subset_co_segment:
    "closed_segment a b \<subseteq> open_segment c d \<longleftrightarrow>
     a \<in> open_segment c d \<and> b \<in> open_segment c d"
using closed_segment_subset by blast

lemma subset_open_segment:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b \<subseteq> open_segment c d \<longleftrightarrow>
         a = b \<or> a \<in> closed_segment c d \<and> b \<in> closed_segment c d"
        (is "?lhs = ?rhs")
proof (cases "a = b")
  case True then show ?thesis by simp
next
  case False show ?thesis
  proof
    assume rhs: ?rhs
    with \<open>a \<noteq> b\<close> have "c \<noteq> d"
      using closed_segment_idem singleton_iff by auto
    have "\<exists>uc. (1 - u) *\<^sub>R ((1 - ua) *\<^sub>R c + ua *\<^sub>R d) + u *\<^sub>R ((1 - ub) *\<^sub>R c + ub *\<^sub>R d) =
               (1 - uc) *\<^sub>R c + uc *\<^sub>R d \<and> 0 < uc \<and> uc < 1"
        if neq: "(1 - ua) *\<^sub>R c + ua *\<^sub>R d \<noteq> (1 - ub) *\<^sub>R c + ub *\<^sub>R d" "c \<noteq> d"
           and "a = (1 - ua) *\<^sub>R c + ua *\<^sub>R d" "b = (1 - ub) *\<^sub>R c + ub *\<^sub>R d"
           and u: "0 < u" "u < 1" and uab: "0 \<le> ua" "ua \<le> 1" "0 \<le> ub" "ub \<le> 1"
        for u ua ub
    proof -
      have "ua \<noteq> ub"
        using neq by auto
      moreover have "(u - 1) * ua \<le> 0" using u uab
        by (simp add: mult_nonpos_nonneg)
      ultimately have lt: "(u - 1) * ua < u * ub" using u uab
        by (metis antisym_conv diff_ge_0_iff_ge le_less_trans mult_eq_0_iff mult_le_0_iff not_less)
      have "p * ua + q * ub < p+q" if p: "0 < p" and  q: "0 < q" for p q
      proof -
        have "\<not> p \<le> 0" "\<not> q \<le> 0"
          using p q not_less by blast+
        then show ?thesis
          by (metis \<open>ua \<noteq> ub\<close> add_less_cancel_left add_less_cancel_right add_mono_thms_linordered_field(5)
                    less_eq_real_def mult_cancel_left1 mult_less_cancel_left2 uab(2) uab(4))
      qed
      then have "(1 - u) * ua + u * ub < 1" using u \<open>ua \<noteq> ub\<close>
        by (metis diff_add_cancel diff_gt_0_iff_gt)
      with lt show ?thesis
        by (rule_tac x="ua + u*(ub-ua)" in exI) (simp add: algebra_simps)
    qed
    with rhs \<open>a \<noteq> b\<close> \<open>c \<noteq> d\<close> show ?lhs
      unfolding open_segment_image_interval closed_segment_def
      by (fastforce simp add:)
  next
    assume lhs: ?lhs
    with \<open>a \<noteq> b\<close> have "c \<noteq> d"
      by (meson finite_open_segment rev_finite_subset)
    have "closure (open_segment a b) \<subseteq> closure (open_segment c d)"
      using lhs closure_mono by blast
    then have "closed_segment a b \<subseteq> closed_segment c d"
      by (simp add: \<open>a \<noteq> b\<close> \<open>c \<noteq> d\<close>)
    then show ?rhs
      by (force simp: \<open>a \<noteq> b\<close>)
  qed
qed

lemma subset_oc_segment:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b \<subseteq> closed_segment c d \<longleftrightarrow>
         a = b \<or> a \<in> closed_segment c d \<and> b \<in> closed_segment c d"
apply (simp add: subset_open_segment [symmetric])
apply (rule iffI)
 apply (metis closure_closed_segment closure_mono closure_open_segment subset_closed_segment subset_open_segment)
apply (meson dual_order.trans segment_open_subset_closed)
done

lemmas subset_segment = subset_closed_segment subset_co_segment subset_oc_segment subset_open_segment


subsection\<open>Betweenness\<close>

definition\<^marker>\<open>tag important\<close> "between = (\<lambda>(a,b) x. x \<in> closed_segment a b)"

lemma betweenI:
  assumes "0 \<le> u" "u \<le> 1" "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
  shows "between (a, b) x"
using assms unfolding between_def closed_segment_def by auto

lemma betweenE:
  assumes "between (a, b) x"
  obtains u where "0 \<le> u" "u \<le> 1" "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
using assms unfolding between_def closed_segment_def by auto

lemma between_implies_scaled_diff:
  assumes "between (S, T) X" "between (S, T) Y" "S \<noteq> Y"
  obtains c where "(X - Y) = c *\<^sub>R (S - Y)"
proof -
  from \<open>between (S, T) X\<close> obtain u\<^sub>X where X: "X = u\<^sub>X *\<^sub>R S + (1 - u\<^sub>X) *\<^sub>R T"
    by (metis add.commute betweenE eq_diff_eq)
  from \<open>between (S, T) Y\<close> obtain u\<^sub>Y where Y: "Y = u\<^sub>Y *\<^sub>R S + (1 - u\<^sub>Y) *\<^sub>R T"
    by (metis add.commute betweenE eq_diff_eq)
  have "X - Y = (u\<^sub>X - u\<^sub>Y) *\<^sub>R (S - T)"
  proof -
    from X Y have "X - Y =  u\<^sub>X *\<^sub>R S - u\<^sub>Y *\<^sub>R S + ((1 - u\<^sub>X) *\<^sub>R T - (1 - u\<^sub>Y) *\<^sub>R T)" by simp
    also have "\<dots> = (u\<^sub>X - u\<^sub>Y) *\<^sub>R S - (u\<^sub>X - u\<^sub>Y) *\<^sub>R T" by (simp add: scaleR_left.diff)
    finally show ?thesis by (simp add: real_vector.scale_right_diff_distrib)
  qed
  moreover from Y have "S - Y = (1 - u\<^sub>Y) *\<^sub>R (S - T)"
    by (simp add: real_vector.scale_left_diff_distrib real_vector.scale_right_diff_distrib)
  moreover note \<open>S \<noteq> Y\<close>
  ultimately have "(X - Y) = ((u\<^sub>X - u\<^sub>Y) / (1 - u\<^sub>Y)) *\<^sub>R (S - Y)" by auto
  from this that show thesis by blast
qed

lemma between_mem_segment: "between (a,b) x \<longleftrightarrow> x \<in> closed_segment a b"
  unfolding between_def by auto

lemma between: "between (a, b) (x::'a::euclidean_space) \<longleftrightarrow> dist a b = (dist a x) + (dist x b)"
proof (cases "a = b")
  case True
  then show ?thesis
    by (auto simp add: between_def dist_commute)
next
  case False
  then have Fal: "norm (a - b) \<noteq> 0" and Fal2: "norm (a - b) > 0"
    by auto
  have *: "\<And>u. a - ((1 - u) *\<^sub>R a + u *\<^sub>R b) = u *\<^sub>R (a - b)"
    by (auto simp add: algebra_simps)
  have "norm (a - x) *\<^sub>R (x - b) = norm (x - b) *\<^sub>R (a - x)" if "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1" for u
  proof -
    have *: "a - x = u *\<^sub>R (a - b)" "x - b = (1 - u) *\<^sub>R (a - b)"
      unfolding that(1) by (auto simp add:algebra_simps)
    show "norm (a - x) *\<^sub>R (x - b) = norm (x - b) *\<^sub>R (a - x)"
      unfolding norm_minus_commute[of x a] * using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
      by simp
  qed
  moreover have "\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1" if "dist a b = dist a x + dist x b" 
  proof -
    let ?\<beta> = "norm (a - x) / norm (a - b)"
    show "\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1"
    proof (intro exI conjI)
      show "?\<beta> \<le> 1"
        using Fal2 unfolding that[unfolded dist_norm] norm_ge_zero by auto
      show "x = (1 - ?\<beta>) *\<^sub>R a + (?\<beta>) *\<^sub>R b"
      proof (subst euclidean_eq_iff; intro ballI)
        fix i :: 'a
        assume i: "i \<in> Basis"
        have "((1 - ?\<beta>) *\<^sub>R a + (?\<beta>) *\<^sub>R b) \<bullet> i 
              = ((norm (a - b) - norm (a - x)) * (a \<bullet> i) + norm (a - x) * (b \<bullet> i)) / norm (a - b)"
          using Fal by (auto simp add: field_simps inner_simps)
        also have "\<dots> = x\<bullet>i"
          apply (rule divide_eq_imp[OF Fal])
          unfolding that[unfolded dist_norm]
          using that[unfolded dist_triangle_eq] i
          apply (subst (asm) euclidean_eq_iff)
           apply (auto simp add: field_simps inner_simps)
          done
        finally show "x \<bullet> i = ((1 - ?\<beta>) *\<^sub>R a + (?\<beta>) *\<^sub>R b) \<bullet> i"
          by auto
      qed
    qed (use Fal2 in auto)
  qed
  ultimately show ?thesis
    by (force simp add: between_def closed_segment_def dist_triangle_eq)
qed

lemma between_midpoint:
  fixes a :: "'a::euclidean_space"
  shows "between (a,b) (midpoint a b)" (is ?t1)
    and "between (b,a) (midpoint a b)" (is ?t2)
proof -
  have *: "\<And>x y z. x = (1/2::real) *\<^sub>R z \<Longrightarrow> y = (1/2) *\<^sub>R z \<Longrightarrow> norm z = norm x + norm y"
    by auto
  show ?t1 ?t2
    unfolding between midpoint_def dist_norm
    by (auto simp add: field_simps inner_simps euclidean_eq_iff[where 'a='a] intro!: *)
qed

lemma between_mem_convex_hull:
  "between (a,b) x \<longleftrightarrow> x \<in> convex hull {a,b}"
  unfolding between_mem_segment segment_convex_hull ..

lemma between_triv_iff [simp]: "between (a,a) b \<longleftrightarrow> a=b"
  by (auto simp: between_def)

lemma between_triv1 [simp]: "between (a,b) a"
  by (auto simp: between_def)

lemma between_triv2 [simp]: "between (a,b) b"
  by (auto simp: between_def)

lemma between_commute:
   "between (a,b) = between (b,a)"
by (auto simp: between_def closed_segment_commute)

lemma between_antisym:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>between (b,c) a; between (a,c) b\<rbrakk> \<Longrightarrow> a = b"
by (auto simp: between dist_commute)

lemma between_trans:
    fixes a :: "'a :: euclidean_space"
    shows "\<lbrakk>between (b,c) a; between (a,c) d\<rbrakk> \<Longrightarrow> between (b,c) d"
  using dist_triangle2 [of b c d] dist_triangle3 [of b d a]
  by (auto simp: between dist_commute)

lemma between_norm:
    fixes a :: "'a :: euclidean_space"
    shows "between (a,b) x \<longleftrightarrow> norm(x - a) *\<^sub>R (b - x) = norm(b - x) *\<^sub>R (x - a)"
  by (auto simp: between dist_triangle_eq norm_minus_commute algebra_simps)

lemma between_swap:
  fixes A B X Y :: "'a::euclidean_space"
  assumes "between (A, B) X"
  assumes "between (A, B) Y"
  shows "between (X, B) Y \<longleftrightarrow> between (A, Y) X"
using assms by (auto simp add: between)

lemma between_translation [simp]: "between (a + y,a + z) (a + x) \<longleftrightarrow> between (y,z) x"
  by (auto simp: between_def)

lemma between_trans_2:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>between (b,c) a; between (a,b) d\<rbrakk> \<Longrightarrow> between (c,d) a"
  by (metis between_commute between_swap between_trans)

lemma between_scaleR_lift [simp]:
  fixes v :: "'a::euclidean_space"
  shows "between (a *\<^sub>R v, b *\<^sub>R v) (c *\<^sub>R v) \<longleftrightarrow> v = 0 \<or> between (a, b) c"
  by (simp add: between dist_norm scaleR_left_diff_distrib [symmetric] distrib_right [symmetric])

lemma between_1:
  fixes x::real
  shows "between (a,b) x \<longleftrightarrow> (a \<le> x \<and> x \<le> b) \<or> (b \<le> x \<and> x \<le> a)"
  by (auto simp: between_mem_segment closed_segment_eq_real_ivl)


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
    have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = \<bar>1/e\<bar> * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm
      unfolding norm_scaleR[symmetric]
      apply (rule arg_cong[where f=norm])
      using \<open>e > 0\<close>
      by (auto simp add: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
    also have "\<dots> = \<bar>1/e\<bar> * norm (x - e *\<^sub>R (x - c) - y)"
      by (auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d"
      using as[unfolded dist_norm] and \<open>e > 0\<close>
      by (auto simp add:pos_divide_less_eq[OF \<open>e > 0\<close>] mult.commute)
    finally show "y \<in> S"
      apply (subst *)
      apply (rule assms(1)[unfolded convex_alt,rule_format])
      apply (rule d[unfolded subset_eq,rule_format])
      unfolding mem_ball
      using assms(3-5)
      apply auto
      done
  qed (insert \<open>e>0\<close> \<open>d>0\<close>, auto)
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
      using \<open>e > 0\<close> \<open>d > 0\<close>
      apply (rule_tac bexI[where x=x])
      apply (auto)
      done
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
        apply (rule_tac x=y in bexI)
        unfolding True
        using \<open>d > 0\<close>
        apply auto
        done
    next
      case False
      then have "0 < e * d / (1 - e)" and *: "1 - e > 0"
        using \<open>e \<le> 1\<close> \<open>e > 0\<close> \<open>d > 0\<close> by auto
      then obtain y where "y \<in> S" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      then show ?thesis
        apply (rule_tac x=y in bexI)
        unfolding dist_norm
        using pos_less_divide_eq[OF *]
        apply auto
        done
    qed
  qed
  then obtain y where "y \<in> S" and y: "norm (y - x) * (1 - e) < e * d"
    by auto
  define z where "z = c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *: "x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)"
    unfolding z_def using \<open>e > 0\<close>
    by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have "z \<in> interior S"
    apply (rule interior_mono[OF d,unfolded subset_eq,rule_format])
    unfolding interior_open[OF open_ball] mem_ball z_def dist_norm using y and assms(4,5)
    by simp (simp add: field_simps norm_minus_commute)
  then show ?thesis
    unfolding *
    using mem_interior_convex_shrink \<open>y \<in> S\<close> assms by blast
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

lemma closure_open_Int_superset:
  assumes "open S" "S \<subseteq> closure T"
  shows "closure(S \<inter> T) = closure S"
proof -
  have "closure S \<subseteq> closure(S \<inter> T)"
    by (metis assms closed_closure closure_minimal inf.orderE open_Int_closure_subset)
  then show ?thesis
    by (simp add: closure_mono dual_order.antisym)
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
            apply (clarsimp simp add: min_def a)
            apply (rule mem_interior_closure_convex_shrink [OF \<open>convex S\<close> a x])
            using \<open>0 < e\<close> False apply (auto simp: field_split_simps)
            done
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
      using as[THEN subsetD[where c="x - (e / 2) *\<^sub>R i"]] and \<open>e > 0\<close> 
      by (force simp add: inner_simps)
  next
    have **: "dist x (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis)) < e" using \<open>e > 0\<close>
      unfolding dist_norm
      by (auto intro!: mult_strict_left_mono simp: SOME_Basis)
    have "\<And>i. i \<in> Basis \<Longrightarrow> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis)) \<bullet> i =
      x\<bullet>i + (if i = (SOME i. i\<in>Basis) then e/2 else 0)"
      by (auto simp: SOME_Basis inner_Basis inner_simps)
    then have *: "sum ((\<bullet>) (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis))) Basis =
      sum (\<lambda>i. x\<bullet>i + (if (SOME i. i\<in>Basis) = i then e/2 else 0)) Basis"
      by (auto simp: intro!: sum.cong)
    have "sum ((\<bullet>) x) Basis < sum ((\<bullet>) (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis))) Basis"
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
    apply (rule that[of ?a])
    unfolding interior_std_simplex mem_Collect_eq
  proof safe
    fix i :: 'a
    assume i: "i \<in> Basis"
    show "0 < ?a \<bullet> i"
      unfolding **[OF i] by (auto simp add: Suc_le_eq DIM_positive)
  next
    have "sum ((\<bullet>) ?a) ?D = sum (\<lambda>i. inverse (2 * real DIM('a))) ?D"
      apply (rule sum.cong)
      apply rule
      apply auto
      done
    also have "\<dots> < 1"
      unfolding sum_constant divide_inverse[symmetric]
      by (auto simp add: field_simps)
    finally show "sum ((\<bullet>) ?a) ?D < 1" by auto
  qed
qed

lemma rel_interior_substd_simplex:
  assumes D: "D \<subseteq> Basis"
  shows "rel_interior (convex hull (insert 0 D)) =
    {x::'a::euclidean_space. (\<forall>i\<in>D. 0 < x\<bullet>i) \<and> (\<Sum>i\<in>D. x\<bullet>i) < 1 \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)}"
  (is "rel_interior (convex hull (insert 0 ?p)) = ?s")
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
    have h0: "affine hull (convex hull (insert 0 ?p)) =
      {x::'a::euclidean_space. (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)}"
      using affine_hull_convex_hull affine_hull_substd_basis assms by auto
    have aux: "\<And>x::'a. \<forall>i\<in>Basis. (\<forall>i\<in>D. 0 \<le> x\<bullet>i) \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0) \<longrightarrow> 0 \<le> x\<bullet>i"
      by auto
    {
      fix x :: "'a::euclidean_space"
      assume x: "x \<in> rel_interior (convex hull (insert 0 ?p))"
      then obtain e where "e > 0" and
        "ball x e \<inter> {xa. (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> xa\<bullet>i = 0)} \<subseteq> convex hull (insert 0 ?p)"
        using mem_rel_interior_ball[of x "convex hull (insert 0 ?p)"] h0 by auto
      then have as [rule_format]: "\<And>y. dist x y < e \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> y\<bullet>i = 0) \<longrightarrow>
        (\<forall>i\<in>D. 0 \<le> y \<bullet> i) \<and> sum ((\<bullet>) y) D \<le> 1"
        unfolding ball_def unfolding substd_simplex[OF assms] using assms by auto
      have x0: "(\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)"
        using x rel_interior_subset  substd_simplex[OF assms] by auto
      have "(\<forall>i\<in>D. 0 < x \<bullet> i) \<and> sum ((\<bullet>) x) D < 1 \<and> (\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> x\<bullet>i = 0)"
      proof (intro conjI ballI)
        fix i :: 'a
        assume "i \<in> D"
        then have "\<forall>j\<in>D. 0 \<le> (x - (e / 2) *\<^sub>R i) \<bullet> j"
          apply -
          apply (rule as[THEN conjunct1])
          using D \<open>e > 0\<close> x0
          apply (auto simp: dist_norm inner_simps inner_Basis)
          done
        then show "0 < x \<bullet> i"
          using \<open>e > 0\<close> \<open>i \<in> D\<close> D  by (force simp: inner_simps inner_Basis)
      next
        obtain a where a: "a \<in> D"
          using \<open>D \<noteq> {}\<close> by auto
        then have **: "dist x (x + (e / 2) *\<^sub>R a) < e"
          using \<open>e > 0\<close> norm_Basis[of a] D
          unfolding dist_norm
          by auto
        have "\<And>i. i \<in> Basis \<Longrightarrow> (x + (e / 2) *\<^sub>R a) \<bullet> i = x\<bullet>i + (if i = a then e/2 else 0)"
          using a D by (auto simp: inner_simps inner_Basis)
        then have *: "sum ((\<bullet>) (x + (e / 2) *\<^sub>R a)) D =
          sum (\<lambda>i. x\<bullet>i + (if a = i then e/2 else 0)) D"
          using D by (intro sum.cong) auto
        have "a \<in> Basis"
          using \<open>a \<in> D\<close> D by auto
        then have h1: "(\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> (x + (e / 2) *\<^sub>R a) \<bullet> i = 0)"
          using x0 D \<open>a\<in>D\<close> by (auto simp add: inner_add_left inner_Basis)
        have "sum ((\<bullet>) x) D < sum ((\<bullet>) (x + (e / 2) *\<^sub>R a)) D"
          using \<open>e > 0\<close> \<open>a \<in> D\<close> \<open>finite D\<close> by (auto simp add: * sum.distrib)
        also have "\<dots> \<le> 1"
          using ** h1 as[rule_format, of "x + (e / 2) *\<^sub>R a"]
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
      then have h2: "x \<in> convex hull (insert 0 ?p)"
        using as assms
        unfolding substd_simplex[OF assms] by fastforce
      obtain a where a: "a \<in> D"
        using \<open>D \<noteq> {}\<close> by auto
      let ?d = "(1 - sum ((\<bullet>) x) D) / real (card D)"
      have "0 < card D" using \<open>D \<noteq> {}\<close> \<open>finite D\<close>
        by (simp add: card_gt_0_iff)
      have "Min (((\<bullet>) x) ` D) > 0"
        using as \<open>D \<noteq> {}\<close> \<open>finite D\<close> by (simp add: Min_gr_iff)
      moreover have "?d > 0" using as using \<open>0 < card D\<close> by auto
      ultimately have h3: "min (Min (((\<bullet>) x) ` D)) ?d > 0"
        by auto

      have "x \<in> rel_interior (convex hull (insert 0 ?p))"
        unfolding rel_interior_ball mem_Collect_eq h0
        apply (rule,rule h2)
        unfolding substd_simplex[OF assms]
        apply (rule_tac x="min (Min (((\<bullet>) x) ` D)) ?d" in exI)
        apply (rule, rule h3)
        apply safe
        unfolding mem_ball
      proof -
        fix y :: 'a
        assume y: "dist x y < min (Min ((\<bullet>) x ` D)) ?d"
        assume y2: "\<forall>i\<in>Basis. i \<notin> D \<longrightarrow> y\<bullet>i = 0"
        have "sum ((\<bullet>) y) D \<le> sum (\<lambda>i. x\<bullet>i + ?d) D"
        proof (rule sum_mono)
          fix i
          assume "i \<in> D"
          with D have i: "i \<in> Basis"
            by auto
          have "\<bar>y\<bullet>i - x\<bullet>i\<bar> \<le> norm (y - x)"
            by (metis i inner_commute inner_diff_right norm_bound_Basis_le order_refl)
          also have "... < ?d"
            by (metis dist_norm min_less_iff_conj norm_minus_commute y)
          finally have "\<bar>y\<bullet>i - x\<bullet>i\<bar> < ?d" .
          then show "y \<bullet> i \<le> x \<bullet> i + ?d" by auto
        qed
        also have "\<dots> \<le> 1"
          unfolding sum.distrib sum_constant  using \<open>0 < card D\<close>
          by auto
        finally show "sum ((\<bullet>) y) D \<le> 1" .

        fix i :: 'a
        assume i: "i \<in> Basis"
        then show "0 \<le> y\<bullet>i"
        proof (cases "i\<in>D")
          case True
          have "norm (x - y) < x\<bullet>i"
            using y[unfolded min_less_iff_conj dist_norm, THEN conjunct1]
            using Min_gr_iff[of "(\<bullet>) x ` D" "norm (x - y)"] \<open>0 < card D\<close> \<open>i \<in> D\<close>
            by (simp add: card_gt_0_iff)
          then show "0 \<le> y\<bullet>i"
            using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format]
            by (auto simp: inner_simps)
        qed (insert y2, auto)
      qed
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
  let ?D = D
  let ?a = "sum (\<lambda>b::'a::euclidean_space. inverse (2 * real (card D)) *\<^sub>R b) ?D"
  have "finite D"
    apply (rule finite_subset)
    using assms(2)
    apply auto
    done
  then have d1: "0 < real (card D)"
    using \<open>D \<noteq> {}\<close> by auto
  {
    fix i
    assume "i \<in> D"
    have "?a \<bullet> i = inverse (2 * real (card D))"
      apply (rule trans[of _ "sum (\<lambda>j. if i = j then inverse (2 * real (card D)) else 0) ?D"])
      unfolding inner_sum_left
      apply (rule sum.cong)
      using \<open>i \<in> D\<close> \<open>finite D\<close> sum.delta'[of D i "(\<lambda>k. inverse (2 * real (card D)))"]
        d1 assms(2)
      by (auto simp: inner_Basis rev_subsetD[OF _ assms(2)])
  }
  note ** = this
  show ?thesis
    apply (rule that[of ?a])
    unfolding rel_interior_substd_simplex[OF assms(2)] mem_Collect_eq
  proof safe
    fix i
    assume "i \<in> D"
    have "0 < inverse (2 * real (card D))"
      using d1 by auto
    also have "\<dots> = ?a \<bullet> i" using **[of i] \<open>i \<in> D\<close>
      by auto
    finally show "0 < ?a \<bullet> i" by auto
  next
    have "sum ((\<bullet>) ?a) ?D = sum (\<lambda>i. inverse (2 * real (card D))) ?D"
      by (rule sum.cong) (rule refl, rule **)
    also have "\<dots> < 1"
      unfolding sum_constant divide_real_def[symmetric]
      by (auto simp add: field_simps)
    finally show "sum ((\<bullet>) ?a) ?D < 1" by auto
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
  moreover have "rel_interior (f ` (convex hull insert 0 B)) =
    f ` rel_interior (convex hull insert 0 B)"
    apply (rule  rel_interior_injective_on_span_linear_image[of f "(convex hull insert 0 B)"])
    using \<open>bounded_linear f\<close> fd *
    apply auto
    done
  ultimately have "rel_interior (convex hull insert 0 B) \<noteq> {}"
    using rel_interior_substd_simplex_nonempty[OF \<open>d \<noteq> {}\<close> d]
    apply auto
    apply blast
    done
  moreover have "convex hull (insert 0 B) \<subseteq> S"
    using B assms hull_mono[of "insert 0 B" "S" "convex"] convex_hull_eq
    by auto
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
  then show ?thesis
    using rel_interior_empty by auto
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
              apply (rule_tac x="x - e1 *\<^sub>R (x - a)" in exI)
              using * e1 dist_norm[of "x - e1 *\<^sub>R (x - a)" x] \<open>x \<noteq> a\<close>
              apply simp
              done
        }
        then have "x islimpt rel_interior S"
          unfolding islimpt_approachable_le by auto
        then have "x \<in> closure(rel_interior S)"
          unfolding closure_def by auto
      }
      ultimately have "x \<in> closure(rel_interior S)" by auto
    }
    then show ?thesis using h1 by auto
  next
    case True
    then have "rel_interior S = {}"
      using rel_interior_empty by auto
    then have "closure (rel_interior S) = {}"
      using closure_empty by auto
    with True show ?thesis by auto
  qed
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
  obtains e where "0 < e" "e \<le> 1" "z = y - e *\<^sub>R (y - x)"
proof -
  define e where "e = a / (a + b)"
  have "z = (1 / (a + b)) *\<^sub>R ((a + b) *\<^sub>R z)"
    using assms  by (simp add: eq_vector_fraction_iff)
  also have "\<dots> = (1 / (a + b)) *\<^sub>R (a *\<^sub>R x + b *\<^sub>R y)"
    using assms scaleR_cancel_left[of "1/(a+b)" "(a + b) *\<^sub>R z" "a *\<^sub>R x + b *\<^sub>R y"]
    by auto
  also have "\<dots> = y - e *\<^sub>R (y-x)"
    using e_def
    apply (simp add: algebra_simps)
    using scaleR_left_distrib[of "a/(a+b)" "b/(a+b)" y] assms add_divide_distrib[of a b "a+b"]
    apply auto
    done
  finally have "z = y - e *\<^sub>R (y-x)"
    by auto
  moreover have "e > 0" using e_def assms by auto
  moreover have "e \<le> 1" using e_def assms by auto
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
        using mem_cball y_def dist_norm[of z y] e by auto
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
      then obtain e1 where "0 < e1" "e1 \<le> 1" "z = y - e1 *\<^sub>R (y - x)"
        using * convex_rel_interior_closure_aux[of "e / norm (z - x)" 1 z x y]
        by (auto simp add: algebra_simps)
      then show ?thesis
        using rel_interior_closure_convex_shrink assms x \<open>y \<in> closure S\<close>
        by auto
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
  case False then show ?thesis
    apply (simp add: rel_interior_eq openin_open)
    apply (rule_tac x="ball (inverse 2 *\<^sub>R (a + b)) (norm(b - a) / 2)" in exI)
    apply (simp add: open_segment_as_ball)
    done
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

lemma starlike_convex_tweak_boundary_points:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" and ST: "rel_interior S \<subseteq> T" and TS: "T \<subseteq> closure S"
  shows "starlike T"
proof -
  have "rel_interior S \<noteq> {}"
    by (simp add: assms rel_interior_eq_empty)
  then obtain a where a: "a \<in> rel_interior S"  by blast
  with ST have "a \<in> T"  by blast
  have *: "\<And>x. x \<in> T \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    apply (rule rel_interior_closure_convex_segment [OF \<open>convex S\<close> a])
    using assms by blast
  show ?thesis
    unfolding starlike_def
    apply (rule bexI [OF _ \<open>a \<in> T\<close>])
    apply (simp add: closed_segment_eq_open)
    apply (intro conjI ballI a \<open>a \<in> T\<close> rel_interior_closure_convex_segment [OF \<open>convex S\<close> a])
    apply (simp add: order_trans [OF * ST])
    done
qed

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
    apply simp
    by (metis centre_in_ball empty_iff frontier_cball frontier_def interior_cball interior_rel_interior_gen rel_frontier_def)
qed

lemma rel_frontier_translation:
  fixes a :: "'a::euclidean_space"
  shows "rel_frontier((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (rel_frontier S)"
by (simp add: rel_frontier_def translation_diff rel_interior_translation closure_translation)

lemma closed_affine_hull [iff]:
  fixes S :: "'n::euclidean_space set"
  shows "closed (affine hull S)"
  by (metis affine_affine_hull affine_closed)

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
    apply (rule closedin_closed_trans[of "affine hull S" "rel_frontier S"])
    unfolding rel_frontier_def
    using * closed_affine_hull
    apply auto
    done
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
       apply (rule affine_dim_equal)
       using * affine_affine_hull
       apply auto
       using \<open>S1 \<noteq> {}\<close> hull_subset[of S1]
       apply auto
       using eq aff_dim_affine_hull[of S1] aff_dim_affine_hull[of S2]
       apply auto
       done
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
        using x1_def x2_def
        apply (auto simp add: algebra_simps)
        using scaleR_left_distrib[of "e1/(e1+e2)" "e2/(e1+e2)" z]
        apply auto
        done
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
      using aff_dim_affine_hull[of S] by (simp add: aff_dim_UNIV)
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

lemma closure_Int: "closure (\<Inter>I) \<le> \<Inter>{closure S |S. S \<in> I}"
proof -
  {
    fix y
    assume "y \<in> \<Inter>I"
    then have y: "\<forall>S \<in> I. y \<in> S" by auto
    {
      fix S
      assume "S \<in> I"
      then have "y \<in> closure S"
        using closure_subset y by auto
    }
    then have "y \<in> \<Inter>{closure S |S. S \<in> I}"
      by auto
  }
  then have "\<Inter>I \<subseteq> \<Inter>{closure S |S. S \<in> I}"
    by auto
  moreover have "closed (\<Inter>{closure S |S. S \<in> I})"
    unfolding closed_Inter closed_closure by auto
  ultimately show ?thesis using closure_hull[of "\<Inter>I"]
    hull_minimal[of "\<Inter>I" "\<Inter>{closure S |S. S \<in> I}" "closed"] by auto
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
          apply (rule_tac x="z" in exI)
          using \<open>y \<noteq> x\<close> z_def * e1 e dist_norm[of z y]
          apply simp
          done
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
    apply (rule convex_Inter)
    using assms convex_rel_interior
    apply auto
    done
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
proof -
  have "affine hull T = T"
    using assms by auto
  then have "rel_interior T = T"
    using rel_interior_affine_hull[of T] by metis
  moreover have "closure T = T"
    using assms affine_closed[of T] by auto
  ultimately show ?thesis
    using convex_closure_inter_two[of S T] assms affine_imp_convex by auto
qed

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
proof -
  have "affine hull T = T"
    using assms by auto
  then have "rel_interior T = T"
    using rel_interior_affine_hull[of T] by metis
  moreover have "closure T = T"
    using assms affine_closed[of T] by auto
  ultimately show ?thesis
    using convex_rel_interior_inter_two[of S T] assms affine_imp_convex by auto
qed

lemma convex_affine_rel_frontier_Int:
   fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "interior S \<inter> T \<noteq> {}"
  shows "rel_frontier(S \<inter> T) = frontier S \<inter> T"
using assms
apply (simp add: rel_frontier_def convex_affine_closure_Int frontier_def)
by (metis Diff_Int_distrib2 Int_emptyI convex_affine_closure_Int convex_affine_rel_interior_Int empty_iff interior_rel_interior_gen)

lemma rel_interior_convex_Int_affine:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "affine T" "interior S \<inter> T \<noteq> {}"
    shows "rel_interior(S \<inter> T) = interior S \<inter> T"
proof -
  obtain a where aS: "a \<in> interior S" and aT:"a \<in> T"
    using assms by force
  have "rel_interior S = interior S"
    by (metis (no_types) aS affine_hull_nonempty_interior equals0D rel_interior_interior)
  then show ?thesis
    by (metis (no_types) affine_imp_convex assms convex_rel_interior_inter_two hull_same rel_interior_affine_hull)
qed

lemma closure_convex_Int_affine:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "affine T" "rel_interior S \<inter> T \<noteq> {}"
  shows "closure(S \<inter> T) = closure S \<inter> T"
proof
  have "closure (S \<inter> T) \<subseteq> closure T"
    by (simp add: closure_mono)
  also have "... \<subseteq> T"
    by (simp add: affine_closed assms)
  finally show "closure(S \<inter> T) \<subseteq> closure S \<inter> T"
    by (simp add: closure_mono)
next
  obtain a where "a \<in> rel_interior S" "a \<in> T"
    using assms by auto
  then have ssT: "subspace ((\<lambda>x. (-a)+x) ` T)" and "a \<in> S"
    using affine_diffs_subspace rel_interior_subset assms by blast+
  show "closure S \<inter> T \<subseteq> closure (S \<inter> T)"
  proof
    fix x  assume "x \<in> closure S \<inter> T"
    show "x \<in> closure (S \<inter> T)"
    proof (cases "x = a")
      case True
      then show ?thesis
        using \<open>a \<in> S\<close> \<open>a \<in> T\<close> closure_subset by fastforce
    next
      case False
      then have "x \<in> closure(open_segment a x)"
        by auto
      then show ?thesis
        using \<open>x \<in> closure S \<inter> T\<close> assms convex_affine_closure_Int by blast
    qed
  qed
qed

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
    using assms rel_interior_empty rel_interior_eq_empty by auto
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
    using assms rel_interior_empty by auto
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
proof -
  { assume "S = {}"
    then have ?thesis
      by auto
  }
  moreover
  { assume "T = {}"
    then have ?thesis
       by auto
  }
  moreover
  {
    assume "S \<noteq> {}" "T \<noteq> {}"
    then have ri: "rel_interior S \<noteq> {}" "rel_interior T \<noteq> {}"
      using rel_interior_eq_empty assms by auto
    then have "fst -` rel_interior S \<noteq> {}"
      using fst_vimage_eq_Times[of "rel_interior S"] by auto
    then have "rel_interior ((fst :: 'n * 'm \<Rightarrow> 'n) -` S) = fst -` rel_interior S"
      using fst_linear \<open>convex S\<close> rel_interior_convex_linear_preimage[of fst S] by auto
    then have s: "rel_interior (S \<times> (UNIV :: 'm set)) = rel_interior S \<times> UNIV"
      by (simp add: fst_vimage_eq_Times)
    from ri have "snd -` rel_interior T \<noteq> {}"
      using snd_vimage_eq_Times[of "rel_interior T"] by auto
    then have "rel_interior ((snd :: 'n * 'm \<Rightarrow> 'm) -` T) = snd -` rel_interior T"
      using snd_linear \<open>convex T\<close> rel_interior_convex_linear_preimage[of snd T] by auto
    then have t: "rel_interior ((UNIV :: 'n set) \<times> T) = UNIV \<times> rel_interior T"
      by (simp add: snd_vimage_eq_Times)
    from s t have *: "rel_interior (S \<times> (UNIV :: 'm set)) \<inter> rel_interior ((UNIV :: 'n set) \<times> T) =
      rel_interior S \<times> rel_interior T" by auto
    have "S \<times> T = S \<times> (UNIV :: 'm set) \<inter> (UNIV :: 'n set) \<times> T"
      by auto
    then have "rel_interior (S \<times> T) = rel_interior ((S \<times> (UNIV :: 'm set)) \<inter> ((UNIV :: 'n set) \<times> T))"
      by auto
    also have "\<dots> = rel_interior (S \<times> (UNIV :: 'm set)) \<inter> rel_interior ((UNIV :: 'n set) \<times> T)"
       apply (subst convex_rel_interior_inter_two[of "S \<times> (UNIV :: 'm set)" "(UNIV :: 'n set) \<times> T"])
       using * ri assms convex_Times
       apply auto
       done
    finally have ?thesis using * by auto
  }
  ultimately show ?thesis by blast
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
    unfolding rel_open_def using rel_interior_empty by auto
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
    unfolding rel_open_def using rel_interior_empty by auto
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
      apply (rule_tac x="(y, z)" in exI)
      apply auto
      done
    then obtain x where "x \<in> S" "y = fst x"
      by blast
    then have "y \<in> fst ` S"
      unfolding image_def by auto
  }
  then have "fst ` S = {y. f y \<noteq> {}}"
    unfolding fst_def using assms by auto
  then have h1: "fst ` rel_interior S = rel_interior {y. f y \<noteq> {}}"
    using rel_interior_convex_linear_image[of fst S] assms fst_linear by auto
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
      using rel_interior_convex_linear_image[of snd "S \<inter> fst -` {y}"] snd_linear conv
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
    by (simp add: rel_interior_empty cone_0)
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
    by (simp add: rel_interior_empty cone_hull_empty)
next
  case False
  then obtain s where "s \<in> S" by auto
  have conv: "convex ({(1 :: real)} \<times> S)"
    using convex_Times[of "{(1 :: real)}" S] assms convex_singleton[of "1 :: real"]
    by auto
  define f where "f y = {z. (y, z) \<in> cone hull ({1 :: real} \<times> S)}" for y
  then have *: "(c, x) \<in> rel_interior (cone hull ({(1 :: real)} \<times> S)) =
    (c \<in> rel_interior {y. f y \<noteq> {}} \<and> x \<in> rel_interior (f c))"
    apply (subst rel_interior_projection[of "cone hull ({(1 :: real)} \<times> S)" f c x])
    using convex_cone_hull[of "{(1 :: real)} \<times> S"] conv
    apply auto
    done
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
      apply (subst convex_sum[of I "convex hull \<Union>(S ` I)" c s])
      using * assms convex_convex_hull
      apply auto
      done
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
      then have "x \<in> ?rhs"
        apply auto
        apply (rule_tac x = c in exI)
        apply (rule_tac x = s in exI)
        using * c_def s_def p \<open>x \<in> S i\<close>
        apply auto
        done
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
      apply (subst convex_hull_finite_union[of I s])
      using assms s_def I_def
      apply auto
      done
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
    apply (rule cInf_greatest [OF nonMT])
    using \<epsilon> dual_order.strict_implies_order le_less_linear by blast
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
      apply (rule subsetD [OF rel_interior_subset inint])
      using \<open>l \<noteq> 0\<close> \<open>0 < d\<close> \<open>0 < \<eta>\<close> by auto
    have "norm l * min d (\<eta> / (norm l * 2)) \<le> norm l * (\<eta> / (norm l * 2))"
      by (metis min_def mult_left_mono norm_ge_zero order_refl)
    also have "... < \<eta>"
      using \<open>l \<noteq> 0\<close> \<open>0 < \<eta>\<close> by (simp add: field_simps)
    finally have 2: "norm l * min d (\<eta> / (norm l * 2)) < \<eta>" .
    show "\<exists>y\<in>S. dist y (a + d *\<^sub>R l) < \<eta>"
      apply (rule_tac x="a + (d - min d (\<eta> / 2 / norm l)) *\<^sub>R l" in bexI)
      using 1 2 \<open>0 < d\<close> \<open>0 < \<eta>\<close> apply (auto simp: algebra_simps)
      done
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
  have "interior S = rel_interior S"
    using a rel_interior_nonempty_interior by auto
  then have "a \<in> rel_interior S"
    using a by simp
  then show ?thesis
    apply (rule ray_to_rel_frontier [OF \<open>bounded S\<close> _ _ \<open>l \<noteq> 0\<close>])
     using a affine_hull_nonempty_interior apply blast
    by (simp add: \<open>interior S = rel_interior S\<close> frontier_def rel_frontier_def that)
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
      using xy
      apply (auto simp: in_segment)
      apply (rule_tac x="d" in exI)
      using \<open>0 < d\<close> that apply (auto simp: algebra_simps)
      done
    ultimately have "1 \<le> d"
      using df rel_frontier_def by fastforce
    moreover have "x = (1 / d) *\<^sub>R x + ((d - 1) / d) *\<^sub>R x"
      by (metis \<open>0 < d\<close> add.commute add_divide_distrib diff_add_cancel divide_self_if less_irrefl scaleR_add_left scaleR_one)
    ultimately show "y \<in> closed_segment x (x + d *\<^sub>R (y - x))"
      apply (auto simp: in_segment)
      apply (rule_tac x="1/d" in exI)
      apply (auto simp: algebra_simps)
      done
  next
    show "open_segment x (x + d *\<^sub>R (y - x)) \<subseteq> rel_interior S"
      apply (rule rel_interior_closure_convex_segment [OF \<open>convex S\<close> x])
      using df rel_frontier_def by auto
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
  assumes "\<forall>i\<in>I. convex (S i)"
  shows "rel_interior (sum S I) = sum (\<lambda>i. rel_interior (S i)) I"
  apply (subst sum_set_cond_linear[of convex])
  using rel_interior_sum rel_interior_sing[of "0"] assms
  apply (auto simp add: convex_set_plus)
  done

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
  assumes "\<forall>i\<in>I. convex (S i) \<and> cone (S i) \<and> S i \<noteq> {}"
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
    {
      fix i
      assume "i \<in> I"
      then have "s i \<in> S i"
        using s_def x assms mem_cone[of "S i" "xs i" "c i"] by auto
    }
    then have "\<forall>i\<in>I. s i \<in> S i" by auto
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
      apply (subst convex_hull_finite_union[of I S])
      using assms
      apply blast
      using assms
      apply blast
      apply rule
      apply (rule_tac x = "(\<lambda>i. (1 :: real) / of_nat (card I))" in exI)
      apply auto
      done
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
    apply (subst convex_hull_finite_union_cones[of I A])
    using assms A_def I_def
    apply auto
    done
  moreover have "sum A I = S + T"
    using A_def I_def
    unfolding set_plus_def
    apply auto
    unfolding set_plus_def
    apply auto
    done
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
    using convex_hull_empty rel_interior_empty by auto
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
  {
    fix i
    assume "i \<in> I"
    then have "convex (K i)"
      unfolding K_def
      apply (subst convex_cone_hull)
      apply (subst convex_Times)
      using assms
      apply auto
      done
  }
  then have convK: "\<forall>i\<in>I. convex (K i)"
    by auto
  {
    fix i
    assume "i \<in> I"
    then have "K0 \<supseteq> K i"
      unfolding K0_def K_def
      apply (subst hull_mono)
      using \<open>\<forall>i\<in>I. C0 \<ge> S i\<close>
      apply auto
      done
  }
  then have "K0 \<supseteq> \<Union>(K ` I)" by auto
  moreover have "convex K0"
    unfolding K0_def
    apply (subst convex_cone_hull)
    apply (subst convex_Times)
    unfolding C0_def
    using convex_convex_hull
    apply auto
    done
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
    apply (subst cone_convex_hull)
    using cone_Union[of "K ` I"]
    apply auto
    unfolding K_def
    using cone_cone_hull
    apply auto
    done
  ultimately have "convex hull (\<Union>(K ` I)) \<supseteq> K0"
    unfolding K0_def
    using hull_minimal[of _ "convex hull (\<Union>(K ` I))" "cone"]
    by blast
  then have "K0 = convex hull (\<Union>(K ` I))"
    using geq by auto
  also have "\<dots> = sum K I"
    apply (subst convex_hull_finite_union_cones[of I K])
    using assms
    apply blast
    using False
    apply blast
    unfolding K_def
    apply rule
    apply (subst convex_cone_hull)
    apply (subst convex_Times)
    using assms cone_cone_hull \<open>\<forall>i\<in>I. K i \<noteq> {}\<close> K_def
    apply auto
    done
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
    then obtain c s where
      cs: "\<forall>i\<in>I. k i = (c i, c i *\<^sub>R s i) \<and> 0 < c i \<and> s i \<in> rel_interior (S i)"
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
    then have "(1::real, x) \<in> rel_interior K0"
      using K0_def * set_sum_alt[of I "(\<lambda>i. rel_interior (K i))"] assms k_def cs
      apply auto
      apply (rule_tac x = k in exI)
      apply (simp add: sum_prod)
      done
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

  have "open (interior I)" by auto
  from openE[OF this \<open>x \<in> interior I\<close>]
  obtain e where "0 < e" "ball x e \<subseteq> interior I" .
  moreover define K where "K = x - e / 2"
  with \<open>0 < e\<close> have "K \<in> ball x e" "K < x"
    by (auto simp: dist_real_def)
  ultimately have "K \<in> I" "K < x" "x \<in> I"
    using interior_subset[of I] \<open>x \<in> interior I\<close> by auto

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
    have "open (interior I)" by auto
    from openE[OF this \<open>x \<in> interior I\<close>]
    obtain e where e: "0 < e" "ball x e \<subseteq> interior I" .
    then have "x + e / 2 \<in> ball x e"
      by (auto simp: dist_real_def)
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
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s" "t \<subseteq> s"
    shows "convex hull t = affine hull t \<inter> convex hull s"
proof -
  have fin: "finite s" "finite t" using assms aff_independent_finite finite_subset by auto
    { fix u v x
      assume uv: "sum u t = 1" "\<forall>x\<in>s. 0 \<le> v x" "sum v s = 1"
                 "(\<Sum>x\<in>s. v x *\<^sub>R x) = (\<Sum>v\<in>t. u v *\<^sub>R v)" "x \<in> t"
      then have s: "s = (s - t) \<union> t" \<comment> \<open>split into separate cases\<close>
        using assms by auto
      have [simp]: "(\<Sum>x\<in>t. v x *\<^sub>R x) + (\<Sum>x\<in>s - t. v x *\<^sub>R x) = (\<Sum>x\<in>t. u x *\<^sub>R x)"
                   "sum v t + sum v (s - t) = 1"
        using uv fin s
        by (auto simp: sum.union_disjoint [symmetric] Un_commute)
      have "(\<Sum>x\<in>s. if x \<in> t then v x - u x else v x) = 0"
           "(\<Sum>x\<in>s. (if x \<in> t then v x - u x else v x) *\<^sub>R x) = 0"
        using uv fin
        by (subst s, subst sum.union_disjoint, auto simp: algebra_simps sum_subtractf)+
    } note [simp] = this
  have "convex hull t \<subseteq> affine hull t"
    using convex_hull_subset_affine_hull by blast
  moreover have "convex hull t \<subseteq> convex hull s"
    using assms hull_mono by blast
  moreover have "affine hull t \<inter> convex hull s \<subseteq> convex hull t"
    using assms
    apply (simp add: convex_hull_finite affine_hull_finite fin affine_dependent_explicit)
    apply (drule_tac x=s in spec)
    apply (auto simp: fin)
    apply (rule_tac x=u in exI)
    apply (rename_tac v)
    apply (drule_tac x="\<lambda>x. if x \<in> t then v x - u x else v x" in spec)
    apply (force)+
    done
  ultimately show ?thesis
    by blast
qed

lemma affine_independent_span_eq:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s" "card s = Suc (DIM ('a))"
    shows "affine hull s = UNIV"
proof (cases "s = {}")
  case True then show ?thesis
    using assms by simp
next
  case False
    then obtain a t where t: "a \<notin> t" "s = insert a t"
      by blast
    then have fin: "finite t" using assms
      by (metis finite_insert aff_independent_finite)
    show ?thesis
    using assms t fin
      apply (simp add: affine_dependent_iff_dependent affine_hull_insert_span_gen)
      apply (rule subset_antisym)
      apply force
      apply (rule Fun.vimage_subsetD)
      apply (metis add.commute diff_add_cancel surj_def)
      apply (rule card_ge_dim_independent)
      apply (auto simp: card_image inj_on_def dim_subset_UNIV)
      done
qed

lemma affine_independent_span_gt:
  fixes s :: "'a::euclidean_space set"
  assumes ind: "\<not> affine_dependent s" and dim: "DIM ('a) < card s"
    shows "affine hull s = UNIV"
  apply (rule affine_independent_span_eq [OF ind])
  apply (rule antisym)
  using assms
  apply auto
  apply (metis add_2_eq_Suc' not_less_eq_eq affine_dependent_biggerset aff_independent_finite)
  done

lemma empty_interior_affine_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" and dim: "card s \<le> DIM ('a)"
    shows "interior(affine hull s) = {}"
  using assms
  apply (induct s rule: finite_induct)
  apply (simp_all add:  affine_dependent_iff_dependent affine_hull_insert_span_gen interior_translation)
  apply (rule empty_interior_lowdim)
  by (auto simp: Suc_le_lessD card_image_le dual_order.trans intro!: dim_le_card'[THEN le_less_trans])

lemma empty_interior_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" and dim: "card s \<le> DIM ('a)"
    shows "interior(convex hull s) = {}"
  by (metis Diff_empty Diff_eq_empty_iff convex_hull_subset_affine_hull
            interior_mono empty_interior_affine_hull [OF assms])

lemma explicit_subset_rel_interior_convex_hull:
  fixes s :: "'a::euclidean_space set"
  shows "finite s
         \<Longrightarrow> {y. \<exists>u. (\<forall>x \<in> s. 0 < u x \<and> u x < 1) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}
             \<subseteq> rel_interior (convex hull s)"
  by (force simp add:  rel_interior_convex_hull_union [where S="\<lambda>x. {x}" and I=s, simplified])

lemma explicit_subset_rel_interior_convex_hull_minimal:
  fixes s :: "'a::euclidean_space set"
  shows "finite s
         \<Longrightarrow> {y. \<exists>u. (\<forall>x \<in> s. 0 < u x) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}
             \<subseteq> rel_interior (convex hull s)"
  by (force simp add:  rel_interior_convex_hull_union [where S="\<lambda>x. {x}" and I=s, simplified])

lemma rel_interior_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows "rel_interior(convex hull s) =
         {y. \<exists>u. (\<forall>x \<in> s. 0 < u x) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
         (is "?lhs = ?rhs")
proof
  show "?rhs \<le> ?lhs"
    by (simp add: aff_independent_finite explicit_subset_rel_interior_convex_hull_minimal assms)
next
  show "?lhs \<le> ?rhs"
  proof (cases "\<exists>a. s = {a}")
    case True then show "?lhs \<le> ?rhs"
      by force
  next
    case False
    have fs: "finite s"
      using assms by (simp add: aff_independent_finite)
    { fix a b and d::real
      assume ab: "a \<in> s" "b \<in> s" "a \<noteq> b"
      then have s: "s = (s - {a,b}) \<union> {a,b}" \<comment> \<open>split into separate cases\<close>
        by auto
      have "(\<Sum>x\<in>s. if x = a then - d else if x = b then d else 0) = 0"
           "(\<Sum>x\<in>s. (if x = a then - d else if x = b then d else 0) *\<^sub>R x) = d *\<^sub>R b - d *\<^sub>R a"
        using ab fs
        by (subst s, subst sum.union_disjoint, auto)+
    } note [simp] = this
    { fix y
      assume y: "y \<in> convex hull s" "y \<notin> ?rhs"
      { fix u T a
        assume ua: "\<forall>x\<in>s. 0 \<le> u x" "sum u s = 1" "\<not> 0 < u a" "a \<in> s"
           and yT: "y = (\<Sum>x\<in>s. u x *\<^sub>R x)" "y \<in> T" "open T"
           and sb: "T \<inter> affine hull s \<subseteq> {w. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = w}"
        have ua0: "u a = 0"
          using ua by auto
        obtain b where b: "b\<in>s" "a \<noteq> b"
          using ua False by auto
        obtain e where e: "0 < e" "ball (\<Sum>x\<in>s. u x *\<^sub>R x) e \<subseteq> T"
          using yT by (auto elim: openE)
        with b obtain d where d: "0 < d" "norm(d *\<^sub>R (a-b)) < e"
          by (auto intro: that [of "e / 2 / norm(a-b)"])
        have "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> affine hull s"
          using yT y by (metis affine_hull_convex_hull hull_redundant_eq)
        then have "(\<Sum>x\<in>s. u x *\<^sub>R x) - d *\<^sub>R (a - b) \<in> affine hull s"
          using ua b by (auto simp: hull_inc intro: mem_affine_3_minus2)
        then have "y - d *\<^sub>R (a - b) \<in> T \<inter> affine hull s"
          using d e yT by auto
        then obtain v where "\<forall>x\<in>s. 0 \<le> v x"
                            "sum v s = 1"
                            "(\<Sum>x\<in>s. v x *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x) - d *\<^sub>R (a - b)"
          using subsetD [OF sb] yT
          by auto
        then have False
          using assms
          apply (simp add: affine_dependent_explicit_finite fs)
          apply (drule_tac x="\<lambda>x. (v x - u x) - (if x = a then -d else if x = b then d else 0)" in spec)
          using ua b d
          apply (auto simp: algebra_simps sum_subtractf sum.distrib)
          done
      } note * = this
      have "y \<notin> rel_interior (convex hull s)"
        using y
        apply (simp add: mem_rel_interior affine_hull_convex_hull)
        apply (auto simp: convex_hull_finite [OF fs])
        apply (drule_tac x=u in spec)
        apply (auto intro: *)
        done
    } with rel_interior_subset show "?lhs \<le> ?rhs"
      by blast
  qed
qed

lemma interior_convex_hull_explicit_minimal:
  fixes s :: "'a::euclidean_space set"
  shows
   "\<not> affine_dependent s
        ==> interior(convex hull s) =
             (if card(s) \<le> DIM('a) then {}
              else {y. \<exists>u. (\<forall>x \<in> s. 0 < u x) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = y})"
  apply (simp add: aff_independent_finite empty_interior_convex_hull, clarify)
  apply (rule trans [of _ "rel_interior(convex hull s)"])
  apply (simp add: affine_independent_span_gt rel_interior_interior)
  by (simp add: rel_interior_convex_hull_explicit)

lemma interior_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows
   "interior(convex hull s) =
             (if card(s) \<le> DIM('a) then {}
              else {y. \<exists>u. (\<forall>x \<in> s. 0 < u x \<and> u x < 1) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = y})"
proof -
  { fix u :: "'a \<Rightarrow> real" and a
    assume "card Basis < card s" and u: "\<And>x. x\<in>s \<Longrightarrow> 0 < u x" "sum u s = 1" and a: "a \<in> s"
    then have cs: "Suc 0 < card s"
      by (metis DIM_positive less_trans_Suc)
    obtain b where b: "b \<in> s" "a \<noteq> b"
    proof (cases "s \<le> {a}")
      case True
      then show thesis
        using cs subset_singletonD by fastforce
    next
      case False
      then show thesis
      by (blast intro: that)
    qed
    have "u a + u b \<le> sum u {a,b}"
      using a b by simp
    also have "... \<le> sum u s"
      apply (rule Groups_Big.sum_mono2)
      using a b u
      apply (auto simp: less_imp_le aff_independent_finite assms)
      done
    finally have "u a < 1"
      using \<open>b \<in> s\<close> u by fastforce
  } note [simp] = this
  show ?thesis
    using assms
    apply (auto simp: interior_convex_hull_explicit_minimal)
    apply (rule_tac x=u in exI)
    apply (auto simp: not_le)
    done
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
    apply (simp add: segment_convex_hull open_segment_def)
    apply (metis Diff_subset interior_mono segment_convex_hull subset_empty interior_closed_segment_ge2)
    done
next
  assume le2: "DIM('a) < 2"
  show "interior (open_segment a b) = open_segment a b"
  proof (cases "a = b")
    case True then show ?thesis by auto
  next
    case False
    with le2 have "affine hull (open_segment a b) = UNIV"
      apply simp
      apply (rule affine_independent_span_gt)
      apply (simp_all add: affine_dependent_def insert_Diff_if)
      done
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
  fixes s :: "'a::euclidean_space set"
  shows "compact s ==> closure(convex hull s) = convex hull s"
  by (simp add: compact_imp_closed compact_convex_hull)

lemma rel_frontier_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows "rel_frontier(convex hull s) =
         {y. \<exists>u. (\<forall>x \<in> s. 0 \<le> u x) \<and> (\<exists>x \<in> s. u x = 0) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
proof -
  have fs: "finite s"
    using assms by (simp add: aff_independent_finite)
  show ?thesis
    apply (simp add: rel_frontier_def finite_imp_compact rel_interior_convex_hull_explicit assms fs)
    apply (auto simp: convex_hull_finite fs)
    apply (drule_tac x=u in spec)
    apply (rule_tac x=u in exI)
    apply force
    apply (rename_tac v)
    apply (rule notE [OF assms])
    apply (simp add: affine_dependent_explicit)
    apply (rule_tac x=s in exI)
    apply (auto simp: fs)
    apply (rule_tac x = "\<lambda>x. u x - v x" in exI)
    apply (force simp: sum_subtractf scaleR_diff_left)
    done
qed

lemma frontier_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows "frontier(convex hull s) =
         {y. \<exists>u. (\<forall>x \<in> s. 0 \<le> u x) \<and> (DIM ('a) < card s \<longrightarrow> (\<exists>x \<in> s. u x = 0)) \<and>
             sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
proof -
  have fs: "finite s"
    using assms by (simp add: aff_independent_finite)
  show ?thesis
  proof (cases "DIM ('a) < card s")
    case True
    with assms fs show ?thesis
      by (simp add: rel_frontier_def frontier_def rel_frontier_convex_hull_explicit [symmetric]
                    interior_convex_hull_explicit_minimal rel_interior_convex_hull_explicit)
  next
    case False
    then have "card s \<le> DIM ('a)"
      by linarith
    then show ?thesis
      using assms fs
      apply (simp add: frontier_def interior_convex_hull_explicit finite_imp_compact)
      apply (simp add: convex_hull_finite)
      done
  qed
qed

lemma rel_frontier_convex_hull_cases:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows "rel_frontier(convex hull s) = \<Union>{convex hull (s - {x}) |x. x \<in> s}"
proof -
  have fs: "finite s"
    using assms by (simp add: aff_independent_finite)
  { fix u a
  have "\<forall>x\<in>s. 0 \<le> u x \<Longrightarrow> a \<in> s \<Longrightarrow> u a = 0 \<Longrightarrow> sum u s = 1 \<Longrightarrow>
            \<exists>x v. x \<in> s \<and>
                  (\<forall>x\<in>s - {x}. 0 \<le> v x) \<and>
                      sum v (s - {x}) = 1 \<and> (\<Sum>x\<in>s - {x}. v x *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)"
    apply (rule_tac x=a in exI)
    apply (rule_tac x=u in exI)
    apply (simp add: Groups_Big.sum_diff1 fs)
    done }
  moreover
  { fix a u
    have "a \<in> s \<Longrightarrow> \<forall>x\<in>s - {a}. 0 \<le> u x \<Longrightarrow> sum u (s - {a}) = 1 \<Longrightarrow>
            \<exists>v. (\<forall>x\<in>s. 0 \<le> v x) \<and>
                 (\<exists>x\<in>s. v x = 0) \<and> sum v s = 1 \<and> (\<Sum>x\<in>s. v x *\<^sub>R x) = (\<Sum>x\<in>s - {a}. u x *\<^sub>R x)"
    apply (rule_tac x="\<lambda>x. if x = a then 0 else u x" in exI)
    apply (auto simp: sum.If_cases Diff_eq if_smult fs)
    done }
  ultimately show ?thesis
    using assms
    apply (simp add: rel_frontier_convex_hull_explicit)
    apply (simp add: convex_hull_finite fs Union_SetCompr_eq, auto)
    done
qed

lemma frontier_convex_hull_eq_rel_frontier:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows "frontier(convex hull s) =
           (if card s \<le> DIM ('a) then convex hull s else rel_frontier(convex hull s))"
  using assms
  unfolding rel_frontier_def frontier_def
  by (simp add: affine_independent_span_gt rel_interior_interior
                finite_imp_compact empty_interior_convex_hull aff_independent_finite)

lemma frontier_convex_hull_cases:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent s"
  shows "frontier(convex hull s) =
           (if card s \<le> DIM ('a) then convex hull s else \<Union>{convex hull (s - {x}) |x. x \<in> s})"
by (simp add: assms frontier_convex_hull_eq_rel_frontier rel_frontier_convex_hull_cases)

lemma in_frontier_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" "card s \<le> Suc (DIM ('a))" "x \<in> s"
  shows   "x \<in> frontier(convex hull s)"
proof (cases "affine_dependent s")
  case True
  with assms show ?thesis
    apply (auto simp: affine_dependent_def frontier_def finite_imp_compact hull_inc)
    by (metis card.insert_remove convex_hull_subset_affine_hull empty_interior_affine_hull finite_Diff hull_redundant insert_Diff insert_Diff_single insert_not_empty interior_mono not_less_eq_eq subset_empty)
next
  case False
  { assume "card s = Suc (card Basis)"
    then have cs: "Suc 0 < card s"
      by (simp add: DIM_positive)
    with subset_singletonD have "\<exists>y \<in> s. y \<noteq> x"
      by (cases "s \<le> {x}") fastforce+
  } note [dest!] = this
  show ?thesis using assms
    unfolding frontier_convex_hull_cases [OF False] Union_SetCompr_eq
    by (auto simp: le_Suc_eq hull_inc)
qed

lemma not_in_interior_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" "card s \<le> Suc (DIM ('a))" "x \<in> s"
  shows   "x \<notin> interior(convex hull s)"
using in_frontier_convex_hull [OF assms]
by (metis Diff_iff frontier_def)

lemma interior_convex_hull_eq_empty:
  fixes s :: "'a::euclidean_space set"
  assumes "card s = Suc (DIM ('a))"
  shows   "interior(convex hull s) = {} \<longleftrightarrow> affine_dependent s"
proof -
  { fix a b
    assume ab: "a \<in> interior (convex hull s)" "b \<in> s" "b \<in> affine hull (s - {b})"
    then have "interior(affine hull s) = {}" using assms
      by (metis DIM_positive One_nat_def Suc_mono card.remove card_infinite empty_interior_affine_hull eq_iff hull_redundant insert_Diff not_less zero_le_one)
    then have False using ab
      by (metis convex_hull_subset_affine_hull equals0D interior_mono subset_eq)
  } then
  show ?thesis
    using assms
    apply auto
    apply (metis UNIV_I affine_hull_convex_hull affine_hull_empty affine_independent_span_eq convex_convex_hull empty_iff rel_interior_interior rel_interior_same_affine_hull)
    apply (auto simp: affine_dependent_def)
    done
qed


subsection \<open>Coplanarity, and collinearity in terms of affine hull\<close>

definition\<^marker>\<open>tag important\<close> coplanar  where
   "coplanar s \<equiv> \<exists>u v w. s \<subseteq> affine hull {u,v,w}"

lemma collinear_affine_hull:
  "collinear s \<longleftrightarrow> (\<exists>u v. s \<subseteq> affine hull {u,v})"
proof (cases "s={}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain x where x: "x \<in> s" by auto
  { fix u
    assume *: "\<And>x y. \<lbrakk>x\<in>s; y\<in>s\<rbrakk> \<Longrightarrow> \<exists>c. x - y = c *\<^sub>R u"
    have "\<exists>u v. s \<subseteq> {a *\<^sub>R u + b *\<^sub>R v |a b. a + b = 1}"
      apply (rule_tac x=x in exI)
      apply (rule_tac x="x+u" in exI, clarify)
      apply (erule exE [OF * [OF x]])
      apply (rename_tac c)
      apply (rule_tac x="1+c" in exI)
      apply (rule_tac x="-c" in exI)
      apply (simp add: algebra_simps)
      done
  } moreover
  { fix u v x y
    assume *: "s \<subseteq> {a *\<^sub>R u + b *\<^sub>R v |a b. a + b = 1}"
    have "x\<in>s \<Longrightarrow> y\<in>s \<Longrightarrow> \<exists>c. x - y = c *\<^sub>R (v-u)"
      apply (drule subsetD [OF *])+
      apply simp
      apply clarify
      apply (rename_tac r1 r2)
      apply (rule_tac x="r1-r2" in exI)
      apply (simp add: algebra_simps)
      apply (metis scaleR_left.add)
      done
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
    by (metis (no_types, hide_lams) collinear_closed_segment collinear_subset hull_redundant hull_subset insert_commute segment_convex_hull)
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
        by (meson ends_in_segment inj_on_image_mem_iff_alt injf subset_closed_segment that)
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
        by (meson ends_in_segment inj_on_image_mem_iff_alt injf subset_closed_segment that)
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
    by (metis (no_types, hide_lams) empty_subsetI ends_in_segment image_insert image_is_empty inj_on_image_set_diff injf insert_subset open_segment_def segment_open_subset_closed)
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
    using card_eq_SucD
    by auto (metis collinear_2 numeral_2_eq_2)
qed

lemma coplanar_small:
  assumes "finite s" "card s \<le> 3"
    shows "coplanar s"
proof -
  have "card s \<le> 2 \<or> card s = Suc (Suc (Suc 0))"
    using assms by linarith
  then show ?thesis using assms
    apply safe
    apply (simp add: collinear_small collinear_imp_coplanar)
    apply (safe dest!: card_eq_SucD)
    apply (auto simp: coplanar_def)
    apply (metis hull_subset insert_subset)
    done
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
  assumes "coplanar s" "linear f" shows "coplanar(f ` s)"
proof -
  { fix u v w
    assume "s \<subseteq> affine hull {u, v, w}"
    then have "f ` s \<subseteq> f ` (affine hull {u, v, w})"
      by (simp add: image_mono)
    then have "f ` s \<subseteq> affine hull (f ` {u, v, w})"
      by (metis assms(2) linear_conv_bounded_linear affine_hull_linear_image)
  } then
  show ?thesis
    by auto (meson assms(1) coplanar_def)
qed

lemma coplanar_translation_imp: "coplanar s \<Longrightarrow> coplanar ((\<lambda>x. a + x) ` s)"
  unfolding coplanar_def
  apply clarify
  apply (rule_tac x="u+a" in exI)
  apply (rule_tac x="v+a" in exI)
  apply (rule_tac x="w+a" in exI)
  using affine_hull_translation [of a "{u,v,w}" for u v w]
  apply (force simp: add.commute)
  done

lemma coplanar_translation_eq: "coplanar((\<lambda>x. a + x) ` s) \<longleftrightarrow> coplanar s"
    by (metis (no_types) coplanar_translation_imp translation_galois)

lemma coplanar_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f" shows "coplanar(f ` s) = coplanar s"
proof
  assume "coplanar s"
  then show "coplanar (f ` s)"
    unfolding coplanar_def
    using affine_hull_linear_image [of f "{u,v,w}" for u v w]  assms
    by (meson coplanar_def coplanar_linear_image)
next
  obtain g where g: "linear g" "g \<circ> f = id"
    using linear_injective_left_inverse [OF assms]
    by blast
  assume "coplanar (f ` s)"
  then obtain u v w where "f ` s \<subseteq> affine hull {u, v, w}"
    by (auto simp: coplanar_def)
  then have "g ` f ` s \<subseteq> g ` (affine hull {u, v, w})"
    by blast
  then have "s \<subseteq> g ` (affine hull {u, v, w})"
    using g by (simp add: Fun.image_comp)
  then show "coplanar s"
    unfolding coplanar_def
    using affine_hull_linear_image [of g "{u,v,w}" for u v w]  \<open>linear g\<close> linear_conv_bounded_linear
    by fastforce
qed
(*The HOL Light proof is simply
    MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COPLANAR_LINEAR_IMAGE));;
*)

lemma coplanar_subset: "\<lbrakk>coplanar t; s \<subseteq> t\<rbrakk> \<Longrightarrow> coplanar s"
  by (meson coplanar_def order_trans)

lemma affine_hull_3_imp_collinear: "c \<in> affine hull {a,b} \<Longrightarrow> collinear {a,b,c}"
  by (metis collinear_2 collinear_affine_hull_collinear hull_redundant insert_commute)

lemma collinear_3_imp_in_affine_hull: "\<lbrakk>collinear {a,b,c}; a \<noteq> b\<rbrakk> \<Longrightarrow> c \<in> affine hull {a,b}"
  unfolding collinear_def
  apply clarify
  apply (frule_tac x=b in bspec, blast, drule_tac x=a in bspec, blast, erule exE)
  apply (drule_tac x=c in bspec, blast, drule_tac x=a in bspec, blast, erule exE)
  apply (rename_tac y x)
  apply (simp add: affine_hull_2)
  apply (rule_tac x="1 - x/y" in exI)
  apply (simp add: algebra_simps)
  done

lemma collinear_3_affine_hull:
  assumes "a \<noteq> b"
    shows "collinear {a,b,c} \<longleftrightarrow> c \<in> affine hull {a,b}"
using affine_hull_3_imp_collinear assms collinear_3_imp_in_affine_hull by blast

lemma collinear_3_eq_affine_dependent:
  "collinear{a,b,c} \<longleftrightarrow> a = b \<or> a = c \<or> b = c \<or> affine_dependent {a,b,c}"
apply (case_tac "a=b", simp)
apply (case_tac "a=c")
apply (simp add: insert_commute)
apply (case_tac "b=c")
apply (simp add: insert_commute)
apply (auto simp: affine_dependent_def collinear_3_affine_hull insert_Diff_if)
apply (metis collinear_3_affine_hull insert_commute)+
done

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

lemma collinear_midpoint: "collinear{a,midpoint a b,b}"
  apply (auto simp: collinear_3 collinear_lemma)
  apply (drule_tac x="-1" in spec)
  apply (simp add: algebra_simps)
  done

lemma midpoint_collinear:
  fixes a b c :: "'a::real_normed_vector"
  assumes "a \<noteq> c"
    shows "b = midpoint a c \<longleftrightarrow> collinear{a,b,c} \<and> dist a b = dist b c"
proof -
  have *: "a - (u *\<^sub>R a + (1 - u) *\<^sub>R c) = (1 - u) *\<^sub>R (a - c)"
          "u *\<^sub>R a + (1 - u) *\<^sub>R c - c = u *\<^sub>R (a - c)"
          "\<bar>1 - u\<bar> = \<bar>u\<bar> \<longleftrightarrow> u = 1/2" for u::real
    by (auto simp: algebra_simps)
  have "b = midpoint a c \<Longrightarrow> collinear{a,b,c} "
    using collinear_midpoint by blast
  moreover have "collinear{a,b,c} \<Longrightarrow> b = midpoint a c \<longleftrightarrow> dist a b = dist b c"
    apply (auto simp: collinear_3_expand assms dist_midpoint)
    apply (simp add: dist_norm * assms midpoint_def del: divide_const_simps)
    apply (simp add: algebra_simps)
    done
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
  case False with assms show ?thesis
    apply (auto simp: collinear_3 collinear_lemma between_norm)
    apply (drule_tac x="-(norm(b - x) / norm(x - a))" in spec)
    apply (simp add: vector_add_divide_simps eq_vector_fraction_iff real_vector.scale_minus_right [symmetric])
    done
qed

lemma midpoint_between:
  fixes a b :: "'a::euclidean_space"
  shows "b = midpoint a c \<longleftrightarrow> between (a,c) b \<and> dist a b = dist b c"
proof (cases "a = c")
  case True then show ?thesis
    by (auto simp: dist_commute)
next
  case False
  show ?thesis
    apply (rule iffI)
    apply (simp add: between_midpoint(1) dist_midpoint)
    using False between_imp_collinear midpoint_collinear by blast
qed

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
  then have *: "\<exists>u. x = u *\<^sub>R a + (1 - u) *\<^sub>R b" if "x \<in> (insert a (insert b S))" for x
    using that assms collinear_3_expand by fastforce+
  show ?lhs
    unfolding collinear_def
    apply (rule_tac x="b-a" in exI)
    apply (clarify dest!: *)
    by (metis (no_types, hide_lams) add.commute diff_add_cancel diff_diff_eq2 real_vector.scale_right_diff_distrib scaleR_left.diff)
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

lemma affine_hull_eq_empty [simp]: "affine hull S = {} \<longleftrightarrow> S = {}"
  using affine_hull_nonempty by blast

lemma affine_hull_2_alt:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = range (\<lambda>u. a + u *\<^sub>R (b - a))"
apply (simp add: affine_hull_2, safe)
apply (rule_tac x=v in image_eqI)
apply (simp add: algebra_simps)
apply (metis scaleR_add_left scaleR_one, simp)
apply (rule_tac x="1-u" in exI)
apply (simp add: algebra_simps)
done

lemma interior_convex_hull_3_minimal:
  fixes a :: "'a::euclidean_space"
  shows "\<lbrakk>\<not> collinear{a,b,c}; DIM('a) = 2\<rbrakk>
         \<Longrightarrow> interior(convex hull {a,b,c}) =
                {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1 \<and>
                            x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
apply (simp add: collinear_3_eq_affine_dependent interior_convex_hull_explicit_minimal, safe)
apply (rule_tac x="u a" in exI, simp)
apply (rule_tac x="u b" in exI, simp)
apply (rule_tac x="u c" in exI, simp)
apply (rename_tac uu x y z)
apply (rule_tac x="\<lambda>r. (if r=a then x else if r=b then y else if r=c then z else 0)" in exI)
apply simp
done


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
  using hyperplane_eq_Ex apply auto[1]
  using inner_zero_right by blast

lemma hyperplane_eq_UNIV:
   "{x. a \<bullet> x = b} = UNIV \<longleftrightarrow> a = 0 \<and> b = 0"
proof -
  have "UNIV \<subseteq> {x. a \<bullet> x = b} \<Longrightarrow> a = 0 \<and> b = 0"
    apply (drule_tac c = "((b+1) / (a \<bullet> a)) *\<^sub>R a" in subsetD)
    apply simp_all
    by (metis add_cancel_right_right zero_neq_one)
  then show ?thesis by force
qed

lemma halfspace_eq_empty_lt:
   "{x. a \<bullet> x < b} = {} \<longleftrightarrow> a = 0 \<and> b \<le> 0"
proof -
  have "{x. a \<bullet> x < b} \<subseteq> {} \<Longrightarrow> a = 0 \<and> b \<le> 0"
    apply (rule ccontr)
    apply (drule_tac c = "((b-1) / (a \<bullet> a)) *\<^sub>R a" in subsetD)
    apply force+
    done
  then show ?thesis by force
qed

lemma halfspace_eq_empty_gt:
   "{x. a \<bullet> x > b} = {} \<longleftrightarrow> a = 0 \<and> b \<ge> 0"
using halfspace_eq_empty_lt [of "-a" "-b"]
by simp

lemma halfspace_eq_empty_le:
   "{x. a \<bullet> x \<le> b} = {} \<longleftrightarrow> a = 0 \<and> b < 0"
proof -
  have "{x. a \<bullet> x \<le> b} \<subseteq> {} \<Longrightarrow> a = 0 \<and> b < 0"
    apply (rule ccontr)
    apply (drule_tac c = "((b-1) / (a \<bullet> a)) *\<^sub>R a" in subsetD)
    apply force+
    done
  then show ?thesis by force
qed

lemma halfspace_eq_empty_ge:
   "{x. a \<bullet> x \<ge> b} = {} \<longleftrightarrow> a = 0 \<and> b > 0"
using halfspace_eq_empty_le [of "-a" "-b"]
by simp

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
      by (simp add: open_Collect_less contf continuous_on_const)
    show "open {x. f x < 0}"
      by (simp add: open_Collect_less contf continuous_on_const)
    show "S \<subseteq> {x. 0 < f x}"
      apply (clarsimp simp add: f_def setdist_sing_in_set)
      using assms
      by (metis False IntI empty_iff le_less setdist_eq_0_sing_2 setdist_pos_le setdist_sym)
    show "T \<subseteq> {x. f x < 0}"
      apply (clarsimp simp add: f_def setdist_sing_in_set)
      using assms
      by (metis False IntI empty_iff le_less setdist_eq_0_sing_2 setdist_pos_le setdist_sym)
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
  then show ?thesis
    apply (rule separation_normal [OF \<open>closed S\<close>])
    apply (rule_tac U=U and V=V in that)
    by auto (meson bounded_ball bounded_subset compl_le_swap2 disjoint_eq_subset_Compl)
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
      by (metis (no_types, hide_lams) Deq Un_subset_iff Un_upper2 J Union_insert order_trans sup_ge1)
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
  apply (rule connected_chain)
  using S apply blast
  by (metis image_iff le_cases nest)

lemma connected_nest_gen:
  fixes S :: "'a::linorder \<Rightarrow> 'b::euclidean_space set"
  assumes S: "\<And>n. closed(S n)" "\<And>n. connected(S n)" "compact(S k)"
    and nest: "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
  shows "connected(\<Inter> (range S))"
  apply (rule connected_chain_gen [of "S k"])
  using S apply auto
  by (meson le_cases nest subsetCE)

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
      apply (rule_tac x="max m n" in exI, safe)
      using max.cobounded2 apply blast
      by (meson le_max_iff_disj)
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
    have "compact (C \<inter> (S \<inter> f -` insert y (range (\<lambda>i. f(X(n + i))))))" for n
      apply (rule closed_Int_compact [OF \<open>closed C\<close>])
      apply (rule com)
       using X \<open>K \<subseteq> S\<close> \<open>f ` S \<subseteq> T\<close> \<open>y \<in> T\<close> apply blast
      apply (rule compact_sequence_with_limit)
      apply (simp add: fX add.commute [of n] LIMSEQ_ignore_initial_segment [OF hlim])
      done
    then have comf: "compact {a \<in> K. f a \<in> insert y (range (\<lambda>i. f(X(n + i))))}" for n
      by (simp add: Keq Int_def conj_commute)
    have ne: "\<Inter>\<F> \<noteq> {}"
             if "finite \<F>"
                and \<F>: "\<And>t. t \<in> \<F> \<Longrightarrow>
                           (\<exists>n. t = {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (n + i))))})"
             for \<F>
    proof -
      obtain m where m: "\<And>t. t \<in> \<F> \<Longrightarrow> \<exists>k\<le>m. t = {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (k + i))))}"
        apply (rule exE)
        apply (rule finite_indexed_bound [OF \<open>finite \<F>\<close> \<F>], assumption, force)
        done
      have "X m \<in> \<Inter>\<F>"
        using X le_Suc_ex by (fastforce dest: m)
      then show ?thesis by blast
    qed
    have "\<Inter>{{a. a \<in> K \<and> f a \<in> insert y (range (\<lambda>i. f(X(n + i))))} |n. n \<in> UNIV}
               \<noteq> {}"
      apply (rule compact_fip_Heine_Borel)
       using comf apply force
      using ne  apply (simp add: subset_iff del: insert_iff)
      done
    then have "\<exists>x. x \<in> (\<Inter>n. {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (n + i))))})"
      by blast
    then show ?thesis
      apply (simp add: image_iff fX)
      by (metis \<open>inj h\<close> le_add1 not_less_eq_eq rangeI range_ex1_eq)
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
      apply (clarsimp simp: dist_norm continuous_on_iff diff)
      by (metis \<open>z \<noteq> 0\<close> mult.commute mult_less_cancel_left_pos norm_minus_commute real_norm_def zero_less_mult_iff zero_less_norm_iff)
    then have conn_fS: "connected (f ` S)"
      by (meson S connected_continuous_image continuous_on_subset hull_subset)
    show ?thesis
    proof (clarsimp simp: convex_contains_segment)
      fix x y z
      assume "x \<in> S" "y \<in> S" "z \<in> closed_segment x y"
      have False if "z \<notin> S"
      proof -
        have "f ` (closed_segment x y) = closed_segment (f x) (f y)"
          apply (rule continuous_injective_image_segment_1)
          apply (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc continuous_on_subset [OF cont_f])
          by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc inj_on_subset [OF inj_f])
        then have fz: "f z \<in> closed_segment (f x) (f y)"
          using \<open>z \<in> closed_segment x y\<close> by blast
        have "z \<in> affine hull S"
          by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>z \<in> closed_segment x y\<close> convex_affine_hull convex_contains_segment hull_inc subset_eq)
        then have fz_notin: "f z \<notin> f ` S"
          using hull_subset inj_f inj_onD that by fastforce
        moreover have "{..<f z} \<inter> f ` S \<noteq> {}" "{f z<..} \<inter> f ` S \<noteq> {}"
        proof -
          have "{..<f z} \<inter> f ` {x,y} \<noteq> {}"  "{f z<..} \<inter> f ` {x,y} \<noteq> {}"
            using fz fz_notin \<open>x \<in> S\<close> \<open>y \<in> S\<close>
             apply (auto simp: closed_segment_eq_real_ivl split: if_split_asm)
             apply (metis image_eqI less_eq_real_def)+
            done
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
    apply (clarsimp simp: dist_norm continuous_on_iff diff)
    by (metis \<open>z \<noteq> 0\<close> mult.commute mult_less_cancel_left_pos norm_minus_commute real_norm_def zero_less_mult_iff zero_less_norm_iff)
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
    apply (rule continuous_injective_image_segment_1)
     apply (meson \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc continuous_on_subset [OF cont_f])
    by (meson \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc inj_on_subset [OF inj_f])
  then have "f ` (closed_segment a b) = f ` S"
    by (simp add: \<open>f a = x\<close> \<open>f b = y\<close> fS_eq)
  then have "?g ` f ` (closed_segment a b) = ?g ` f ` S"
    by simp
  moreover have "(\<lambda>x. f x *\<^sub>R z + \<xi>) ` closed_segment a b = closed_segment a b"
    apply safe
     apply (metis (mono_tags, hide_lams) \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment gf hull_inc subsetCE)
    by (metis (mono_tags, lifting) \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment gf hull_subset image_iff subsetCE)
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
  have *: "{y. \<exists>x. x \<in> S \<and> Pair x y \<in> T} =
        {y. \<exists>x. x \<in> S \<and> Pair x y \<in> ((S \<times> UNIV) \<inter> T)}"
    by auto
  show ?thesis
    apply (subst *)
    apply (rule closedin_closed_trans [OF _ closed_UNIV])
    apply (rule closedin_compact_projection [OF \<open>compact S\<close>])
    by (simp add: clo closedin_closed_Int)
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
      apply (rule span_mul)
      apply (rule span_base)
      apply (rule image_eqI [where x = "a + k *\<^sub>R (x - a)"])
      apply (auto simp: S T)
      done
    with xa image_iff show ?thesis  by fastforce
  qed
  show "affine hull S \<subseteq> affine hull (S \<inter> T)"
    apply (simp add: subset_hull)
    apply (simp add: \<open>a \<in> S\<close> \<open>a \<in> T\<close> hull_inc affine_hull_span_gen [of a])
    apply (force simp: *)
    done
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
    by (simp add: aff_dim_UNIV)
  then have "aff_dim (affine hull {x. a \<bullet> x \<le> r}) = DIM('a)" if "(a = 0 \<longrightarrow> r \<ge> 0)"
    using that by (simp add: affine_hull_halfspace_le not_less)
  then show ?thesis
    by (force simp: aff_dim_affine_hull)
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
proof (cases "S = {}")
  case True then show ?thesis
    by (auto simp: dest: hyperplane_eq_Ex)
next
  case False
  then obtain c where "c \<in> S" by blast
  show ?thesis
  proof (cases "c = 0")
    case True show ?thesis
      using span_zero [of S]
        apply (simp add: aff_dim_eq_dim [of c] affine_hull_span_gen [of c] \<open>c \<in> S\<close> hull_inc dim_eq_hyperplane
          del: One_nat_def)
        apply (auto simp add: \<open>c = 0\<close>)
        done
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
    show ?thesis
      apply (simp add: aff_dim_eq_dim [of c] affine_hull_span_gen [of c] \<open>c \<in> S\<close> hull_inc dim_eq_hyperplane
                  del: One_nat_def cong: image_cong_simp, safe)
      apply (fastforce simp add: inner_distrib intro: xc_im)
      apply (force simp: intro!: 2)
      done
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
    apply (simp add: hull_redundant cong: aff_dim_affine_hull2)
    apply (simp add: affine_hull_insert_span_gen hull_inc)
    by (force simp add: span_zero insert_commute [of a] hull_inc aff_dim_eq_dim [of x] dim_insert
      cong: image_cong_simp)
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
  with False assms show ?thesis
    apply safe
    using affine_diffs_subspace [OF assms \<open>b \<in> S\<close>]
    apply (metis (no_types, lifting) subspace_bounded_eq_trivial ab_left_minus bounded_translation
                image_empty image_insert translation_invert)
    apply force
    done
qed

lemma affine_bounded_eq_lowdim:
  fixes S :: "'a::euclidean_space set"
  assumes "affine S"
    shows "bounded S \<longleftrightarrow> aff_dim S \<le> 0"
apply safe
using affine_bounded_eq_trivial assms apply fastforce
by (metis aff_dim_sing aff_dim_subset affine_dim_equal affine_sing all_not_in_conv assms bounded_empty bounded_insert dual_order.antisym empty_subsetI insert_subset)


lemma bounded_hyperplane_eq_trivial_0:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
  shows "bounded {x. a \<bullet> x = 0} \<longleftrightarrow> DIM('a) = 1"
proof
  assume "bounded {x. a \<bullet> x = 0}"
  then have "aff_dim {x. a \<bullet> x = 0} \<le> 0"
    by (simp add: affine_bounded_eq_lowdim affine_hyperplane)
  with assms show "DIM('a) = 1"
    by (simp add: le_Suc_eq aff_dim_hyperplane)
next
  assume "DIM('a) = 1"
  then show "bounded {x. a \<bullet> x = 0}"
    by (simp add: aff_dim_hyperplane affine_bounded_eq_lowdim affine_hyperplane assms)
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
using separating_hyperplane_closed_point_inset [OF assms]
by simp (metis \<open>0 \<notin> S\<close>)


proposition\<^marker>\<open>tag unimportant\<close> separating_hyperplane_set_0_inspan:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" "0 \<notin> S"
  obtains a where "a \<in> span S" "a \<noteq> 0" "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> a \<bullet> x"
proof -
  define k where [abs_def]: "k c = {x. 0 \<le> c \<bullet> x}" for c :: 'a
  have *: "span S \<inter> frontier (cball 0 1) \<inter> \<Inter>f' \<noteq> {}"
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
      have aa: "a /\<^sub>R (norm a) \<in> (\<Inter>c\<in>C. {x. 0 \<le> c \<bullet> x})"
        apply (clarsimp simp add: field_split_simps)
        using ab \<open>0 < b\<close>
        by (metis hull_inc inner_commute less_eq_real_def less_trans)
      show ?thesis
        apply (simp add: C k_def)
        using ass aa Int_iff empty_iff by blast
    qed
  qed
  have "(span S \<inter> frontier(cball 0 1)) \<inter> (\<Inter> (k ` S)) \<noteq> {}"
    apply (rule compact_imp_fip)
    apply (blast intro: compact_cball)
    using closed_halfspace_ge k_def apply blast
    apply (metis *)
    done
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
  show ?thesis
    apply (rule_tac a=a and b = "a  \<bullet> z" in that, simp_all)
    using \<open>a \<in> span ((+) (- z) ` S)\<close> affine_hull_insert_span_gen apply blast
    apply (simp_all add: \<open>a \<noteq> 0\<close> szx)
    done
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
      using le_ay [OF \<open>y' \<in> S\<close>] \<open>a \<noteq> 0\<close>
      apply (simp add: y'_def inner_diff dot_square_norm power2_eq_square)
      by (metis \<open>0 < e\<close> add_le_same_cancel1 inner_commute inner_real_def inner_zero_left le_diff_eq norm_le_zero_iff real_mult_le_cancel_iff2)
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
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent(s \<union> t)"
    shows convex_hull_Int_subset: "convex hull s \<inter> convex hull t \<subseteq> convex hull (s \<inter> t)" (is ?C)
      and affine_hull_Int_subset: "affine hull s \<inter> affine hull t \<subseteq> affine hull (s \<inter> t)" (is ?A)
proof -
  have [simp]: "finite s" "finite t"
    using aff_independent_finite assms by blast+
    have "sum u (s \<inter> t) = 1 \<and>
          (\<Sum>v\<in>s \<inter> t. u v *\<^sub>R v) = (\<Sum>v\<in>s. u v *\<^sub>R v)"
      if [simp]:  "sum u s = 1"
                 "sum v t = 1"
         and eq: "(\<Sum>x\<in>t. v x *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)" for u v
    proof -
    define f where "f x = (if x \<in> s then u x else 0) - (if x \<in> t then v x else 0)" for x
    have "sum f (s \<union> t) = 0"
      apply (simp add: f_def sum_Un sum_subtractf)
      apply (simp add: sum.inter_restrict [symmetric] Int_commute)
      done
    moreover have "(\<Sum>x\<in>(s \<union> t). f x *\<^sub>R x) = 0"
      apply (simp add: f_def sum_Un scaleR_left_diff_distrib sum_subtractf)
      apply (simp add: if_smult sum.inter_restrict [symmetric] Int_commute eq
          cong del: if_weak_cong)
      done
    ultimately have "\<And>v. v \<in> s \<union> t \<Longrightarrow> f v = 0"
      using aff_independent_finite assms unfolding affine_dependent_explicit
      by blast
    then have u [simp]: "\<And>x. x \<in> s \<Longrightarrow> u x = (if x \<in> t then v x else 0)"
      by (simp add: f_def) presburger
    have "sum u (s \<inter> t) = sum u s"
      by (simp add: sum.inter_restrict)
    then have "sum u (s \<inter> t) = 1"
      using that by linarith
    moreover have "(\<Sum>v\<in>s \<inter> t. u v *\<^sub>R v) = (\<Sum>v\<in>s. u v *\<^sub>R v)"
      by (auto simp: if_smult sum.inter_restrict intro: sum.cong)
    ultimately show ?thesis
      by force
    qed
    then show ?A ?C
      by (auto simp: convex_hull_finite affine_hull_finite)
qed


proposition\<^marker>\<open>tag unimportant\<close> affine_hull_Int:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent(s \<union> t)"
    shows "affine hull (s \<inter> t) = affine hull s \<inter> affine hull t"
apply (rule subset_antisym)
apply (simp add: hull_mono)
by (simp add: affine_hull_Int_subset assms)

proposition\<^marker>\<open>tag unimportant\<close> convex_hull_Int:
  fixes s :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent(s \<union> t)"
    shows "convex hull (s \<inter> t) = convex hull s \<inter> convex hull t"
apply (rule subset_antisym)
apply (simp add: hull_mono)
by (simp add: convex_hull_Int_subset assms)

proposition\<^marker>\<open>tag unimportant\<close>
  fixes s :: "'a::euclidean_space set set"
  assumes "\<not> affine_dependent (\<Union>s)"
    shows affine_hull_Inter: "affine hull (\<Inter>s) = (\<Inter>t\<in>s. affine hull t)" (is "?A")
      and convex_hull_Inter: "convex hull (\<Inter>s) = (\<Inter>t\<in>s. convex hull t)" (is "?C")
proof -
  have "finite s"
    using aff_independent_finite assms finite_UnionD by blast
  then have "?A \<and> ?C" using assms
  proof (induction s rule: finite_induct)
    case empty then show ?case by auto
  next
    case (insert t F)
    then show ?case
    proof (cases "F={}")
      case True then show ?thesis by simp
    next
      case False
      with "insert.prems" have [simp]: "\<not> affine_dependent (t \<union> \<Inter>F)"
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
    using naff that \<open>finite S\<close> sum_dd0 unfolding affine_dependent_explicit
    apply (simp only: not_ex)
    apply (drule_tac x=S in spec)
    apply (drule_tac x=dd in spec, simp)
    done
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
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
      also have "... = c a + (1 - c a)"
        by (metis \<open>a \<notin> S\<close> fun_upd_other sum.cong sumSS')
      finally show "sum (cc(a := c a)) (insert a (T \<inter> T')) = 1"
        by simp
      have "(\<Sum>x\<in>insert a (T \<inter> T'). (cc(a := c a)) x *\<^sub>R x) = c a *\<^sub>R a + (\<Sum>x \<in> T \<inter> T'. (cc(a := c a)) x *\<^sub>R x)"
        by (simp add: anot)
      also have "... = c a *\<^sub>R a + (\<Sum>x \<in> S. (cc(a := c a)) x *\<^sub>R x)"
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
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
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
      also have "... = c' a + (1 - c' a)"
        by (metis \<open>a \<notin> S\<close> fun_upd_other sum.cong sumSS')
      finally show "sum (cc'(a := c' a)) (insert a (T \<inter> T')) = 1"
        by simp
      have "(\<Sum>x\<in>insert a (T \<inter> T'). (cc'(a := c' a)) x *\<^sub>R x) = c' a *\<^sub>R a + (\<Sum>x \<in> T \<inter> T'. (cc'(a := c' a)) x *\<^sub>R x)"
        by (simp add: anot)
      also have "... = c' a *\<^sub>R a + (\<Sum>x \<in> S. (cc'(a := c' a)) x *\<^sub>R x)"
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
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
         convex hull (insert a (T \<inter> T'))"
apply (rule subset_antisym)
  using in_convex_hull_exchange_unique assms apply blast
  by (metis hull_mono inf_le1 inf_le2 insert_inter_insert le_inf_iff)

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
      by (simp add: affine_independent_2)
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
        apply (rule collinear_3_trans [OF _ _ \<open>b \<noteq> d\<close>])
        using d  by (auto simp: insert_commute)
      with ncoll show False ..
    qed
    then show ?thesis
      by blast
  qed
qed

lemma affine_hull_finite_intersection_hyperplanes:
  fixes s :: "'a::euclidean_space set"
  obtains f where
     "finite f"
     "of_nat (card f) + aff_dim s = DIM('a)"
     "affine hull s = \<Inter>f"
     "\<And>h. h \<in> f \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x = b}"
proof -
  obtain b where "b \<subseteq> s"
             and indb: "\<not> affine_dependent b"
             and eq: "affine hull s = affine hull b"
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
  have card1: "card ((\<lambda>a. affine hull (c - {a})) ` (c - b)) = card (c - b)"
    apply (rule card_image [OF inj_onI])
    by (metis Diff_eq_empty_iff Diff_iff indc affine_dependent_def hull_subset insert_iff)
  have card2: "(card (c - b)) + aff_dim s = DIM('a)"
  proof -
    have aff: "aff_dim (UNIV::'a set) = aff_dim c"
      by (metis aff_dim_affine_hull affc)
    have "aff_dim b = aff_dim s"
      by (metis (no_types) aff_dim_affine_hull eq)
    then have "int (card b) = 1 + aff_dim s"
      by (simp add: aff_dim_affine_independent indb)
    then show ?thesis
      using fbc aff
      by (simp add: \<open>\<not> affine_dependent c\<close> \<open>b \<subseteq> c\<close> aff_dim_affine_independent aff_dim_UNIV card_Diff_subset of_nat_diff)
  qed
  show ?thesis
  proof (cases "c = b")
    case True show ?thesis
      apply (rule_tac f="{}" in that)
      using True affc
      apply (simp_all add: eq [symmetric])
      by (metis aff_dim_UNIV aff_dim_affine_hull)
  next
    case False
    have ind: "\<not> affine_dependent (\<Union>a\<in>c - b. c - {a})"
      by (rule affine_independent_subset [OF indc]) auto
    have affeq: "affine hull s = (\<Inter>x\<in>(\<lambda>a. c - {a}) ` (c - b). affine hull x)"
      using \<open>b \<subseteq> c\<close> False
      apply (subst affine_hull_Inter [OF ind, symmetric])
      apply (simp add: eq double_diff)
      done
    have *: "1 + aff_dim (c - {t}) = int (DIM('a))"
            if t: "t \<in> c" for t
    proof -
      have "insert t c = c"
        using t by blast
      then show ?thesis
        by (metis (full_types) add.commute aff_dim_affine_hull aff_dim_insert aff_dim_UNIV affc affine_dependent_def indc insert_Diff_single t)
    qed
    show ?thesis
      apply (rule_tac f = "(\<lambda>x. affine hull x) ` ((\<lambda>a. c - {a}) ` (c - b))" in that)
         using \<open>finite c\<close> apply blast
        apply (simp add: imeq card1 card2)
      apply (simp add: affeq, clarify)
      apply (metis DIM_positive One_nat_def Suc_leI add_diff_cancel_left' of_nat_1 aff_dim_eq_hyperplane of_nat_diff *)
      done
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
    apply (rule span_mono)
    using \<open>0 \<in> S\<close> add.left_neutral by force
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
  finally have DIM_lt: "DIM('a) - 1 < dim {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}" .
  have subs: "subspace {x + y| x y. x \<in> S \<and> a \<bullet> y = 0}"
    using subspace_sums [OF \<open>subspace S\<close> subspace_hyperplane] by simp
  moreover have "span {x + y| x y. x \<in> S \<and> a \<bullet> y = 0} = UNIV"
    apply (rule dim_eq_full [THEN iffD1])
    apply (rule antisym [OF dim_subset_UNIV])
    using DIM_lt apply simp
    done
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
  let ?U = "(+) (c+c) ` {x + y |x y. x \<in> (+) (- c) ` S \<and> a \<bullet> y = 0}"
  have "u + v \<in> (+) (c + c) ` {x + v |x v. x \<in> (+) (- c) ` S \<and> a \<bullet> v = 0}"
              if "u \<in> S" "b = a \<bullet> v" for u v
    apply (rule_tac x="u+v-c-c" in image_eqI)
    apply (simp_all add: algebra_simps)
    apply (rule_tac x="u-c" in exI)
    apply (rule_tac x="v-c" in exI)
    apply (simp add: algebra_simps that c)
    done
  moreover have "\<lbrakk>a \<bullet> v = 0; u \<in> S\<rbrakk>
       \<Longrightarrow> \<exists>x ya. v + (u + c) = x + ya \<and> x \<in> S \<and> a \<bullet> ya = b" for v u
    by (metis add.left_commute c inner_right_distrib pth_d)
  ultimately have "{x + y |x y. x \<in> S \<and> a \<bullet> y = b} = ?U"
    by (fastforce simp: algebra_simps)
  also have "... = range ((+) (c + c))"
    by (simp only: affine_hyperplane_sums_eq_UNIV_0 [OF aff 0 dc adc])
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
      show "independent ((\<lambda>x. e *\<^sub>R x) ` B)"
        using linear_scale_self \<open>independent B\<close>
        apply (rule linear_independent_injective_image)
        using \<open>0 < e\<close> inj_on_def by fastforce
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
    apply (rule dense_complement_openin_affine_hull)
    apply (simp add: assms rel_interior_aff_dim)
    using \<open>convex S\<close> rel_interior_rel_open rel_open by blast
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
  have "\<And>w. w \<in> (+) (- z) ` S \<Longrightarrow> (w + a') \<in> (+) (- z) ` S"
    by (metis subspace_add a' span_eq_iff sub)
  then have Sclo: "\<And>w. w \<in> S \<Longrightarrow> (w + a') \<in> S"
    by fastforce
  show ?thesis
  proof (cases "a' = 0")
    case True
    with a assms True a'' diff_zero less_irrefl show ?thesis
      by auto
  next
    case False
    show ?thesis
      apply (rule_tac a' = "a'" and b' = "a' \<bullet> z" in that)
      apply (auto simp: a ba'' inner_left_distrib False Sclo)
      done
  qed
qed

lemma diffs_affine_hull_span:
  assumes "a \<in> S"
    shows "{x - a |x. x \<in> affine hull S} = span {x - a |x. x \<in> S}"
proof -
  have *: "((\<lambda>x. x - a) ` (S - {a})) = {x. x + a \<in> S} - {0}"
    by (auto simp: algebra_simps)
  show ?thesis
    apply (simp add: affine_hull_span2 [OF assms] *)
    apply (auto simp: algebra_simps)
    done
qed

lemma aff_dim_dim_affine_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S" "a \<in> S"
    shows "aff_dim S = dim {x - a |x. x \<in> S}"
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
  have *: "{x - c |x. x \<in> S} = {x - a |x. x \<in> S}"
    apply safe
    apply (simp_all only: xy)
    using mem_affine_3_minus [OF \<open>affine S\<close>] \<open>a \<in> S\<close> \<open>c \<in> S\<close> apply blast+
    done
  have affS: "affine hull S = S"
    by (simp add: \<open>affine S\<close>)
  have "aff_dim S = of_nat (card B) - 1"
    using card by simp
  also have "... = dim {x - c |x. x \<in> B}"
    by (simp add: affine_independent_card_dim_diffs [OF ind \<open>c \<in> B\<close>])
  also have "... = dim {x - c | x. x \<in> affine hull B}"
     by (simp add: diffs_affine_hull_span \<open>c \<in> B\<close> dim_span)
  also have "... = dim {x - a |x. x \<in> S}"
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
    have 2: "{x - f a| x. x \<in> f ` T} = f ` {x - a| x. x \<in> T}"
      by (force simp: linear_diff [OF assms])
    have "aff_dim (f ` T) = int (dim {x - f a |x. x \<in> f ` T})"
      by (simp add: \<open>a \<in> T\<close> hull_inc aff_dim_eq_dim [of "f a"] 1 cong: image_cong_simp)
    also have "... = int (dim (f ` {x - a| x. x \<in> T}))"
      by (force simp: linear_diff [OF assms] 2)
    also have "... \<le> int (dim {x - a| x. x \<in> T})"
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
      apply (rule_tac x = T in exI)
      apply (rule_tac x = "ball x e" in exI)
      using  \<open>T \<in> \<C>\<close>
      apply (simp add: closure_minimal)
      using closed_cball closure_minimal by blast
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
  have 1: "S \<subseteq> Union ?C"
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
  have 3: "\<exists>V. open V \<and> x \<in> V \<and> finite {U. U \<in> ?C \<and> (U \<inter> V \<noteq> {})}" if "x \<in> S" for x
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
    show ?thesis
      apply (rule_tac x="G (a n)" in exI)
      apply (intro conjI oG n *)
      using \<open>K \<subseteq> S\<close> \<open>range a = K\<close> apply blast
      done
  qed
  show ?thesis
    apply (rule that [OF 1 _ 3])
    using Fin \<open>K \<subseteq> S\<close> \<open>range a = K\<close>  apply (auto simp: odif)
    done
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
      using D2 [OF that]
      apply clarify
      apply (rule_tac x="U \<inter> V" in exI)
      apply (auto intro: that finite_subset [OF *])
      done
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
  have eq: "((\<lambda>x. Pair x (f x)) ` S) =(S \<times> T \<inter> (\<lambda>z. (f \<circ> fst)z - snd z) -` {0})"
    using fim by auto
  show ?thesis
    apply (subst eq)
    apply (intro continuous_intros continuous_closedin_preimage continuous_on_subset [OF contf])
    by auto
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
  apply (rule closedin_closed_trans)
   apply (rule continuous_closed_graph_gen [OF contf subset_UNIV])
  by (simp add: \<open>closed S\<close> closed_Times)

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

lemma continuous_map_cases_le:
  assumes contp: "continuous_map X euclideanreal p"
    and contq: "continuous_map X euclideanreal q"
    and contf: "continuous_map (subtopology X {x. x \<in> topspace X \<and> p x \<le> q x}) Y f"
    and contg: "continuous_map (subtopology X {x. x \<in> topspace X \<and> q x \<le> p x}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x = q x\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x \<le> q x then f x else g x)"
proof -
  have "continuous_map X Y (\<lambda>x. if q x - p x \<in> {0..} then f x else g x)"
  proof (rule continuous_map_cases_function)
    show "continuous_map X euclideanreal (\<lambda>x. q x - p x)"
      by (intro contp contq continuous_intros)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of {0..}}) Y f"
      by (simp add: contf)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of (topspace euclideanreal - {0..})}) Y g"
      by (simp add: contg flip: Compl_eq_Diff_UNIV)
  qed (auto simp: fg)
  then show ?thesis
    by simp
qed

lemma continuous_map_cases_lt:
  assumes contp: "continuous_map X euclideanreal p"
    and contq: "continuous_map X euclideanreal q"
    and contf: "continuous_map (subtopology X {x. x \<in> topspace X \<and> p x \<le> q x}) Y f"
    and contg: "continuous_map (subtopology X {x. x \<in> topspace X \<and> q x \<le> p x}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x = q x\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x < q x then f x else g x)"
proof -
  have "continuous_map X Y (\<lambda>x. if q x - p x \<in> {0<..} then f x else g x)"
  proof (rule continuous_map_cases_function)
    show "continuous_map X euclideanreal (\<lambda>x. q x - p x)"
      by (intro contp contq continuous_intros)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of {0<..}}) Y f"
      by (simp add: contf)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of (topspace euclideanreal - {0<..})}) Y g"
      by (simp add: contg flip: Compl_eq_Diff_UNIV)
  qed (auto simp: fg)
  then show ?thesis
    by simp
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
            apply (rule sum.mono_neutral_right)
            using fin by auto
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
            apply (rule sum.mono_neutral_right)
            using fin by auto
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
            using \<open>a \<notin> S\<close> \<open>b \<in> S\<close> True  apply simp
            apply (rule sum.cong, auto)
            done
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
            using \<open>a \<notin> S\<close> \<open>b \<in> S\<close> True  apply simp
            apply (rule sum.cong, auto)
            done
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
  shows "open_segment a b \<union> {b} \<union> open_segment b c = open_segment a c"
proof -
  have b: "b \<in> closed_segment a c"
    by (simp add: assms open_closed_segment)
  have *: "open_segment a c \<subseteq> insert b (open_segment a b \<union> open_segment b c)"
          if "{b,c,a} \<union> open_segment a b \<union> open_segment b c = {c,a} \<union> open_segment a c"
  proof -
    have "insert a (insert c (insert b (open_segment a b \<union> open_segment b c))) = insert a (insert c (open_segment a c))"
      using that by (simp add: insert_commute)
    then show ?thesis
      by (metis (no_types) Diff_cancel Diff_eq_empty_iff Diff_insert2 open_segment_def)
  qed
  show ?thesis
    using Un_closed_segment [OF b]
    apply (simp add: closed_segment_eq_open)
      apply (rule equalityI)
    using assms
     apply (simp add: b subset_open_segment)
      using * by (simp add: insert_commute)
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
        apply (intro UN_mono order_refl)
        apply (simp add: cball_subset_ball_iff field_split_simps)
        done
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
  shows "f -` {0} =  (range (adjoint f))\<^sup>\<bottom>"
  apply (auto simp: orthogonal_comp_def orthogonal_def)
  apply (simp add: adjoint_works assms(1) inner_commute)
  by (metis adjoint_works all_zero_iff assms(1) inner_commute)

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
    by (metis (no_types, hide_lams) adjoint_adjoint adjoint_linear assms ker_orthogonal_comp_adjoint set_zero)
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
    by (metis (no_types, hide_lams) adjoint_clauses(2) adjoint_linear assms
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
