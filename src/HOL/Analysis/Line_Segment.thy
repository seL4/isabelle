(* Title:      HOL/Analysis/Line_Segment.thy
   Author:     L C Paulson, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
   Author:     Bogdan Grechuk, University of Edinburgh
   Author:     Armin Heller, TU Muenchen
   Author:     Johannes Hoelzl, TU Muenchen
*)

section \<open>Line Segment\<close>

theory Line_Segment
imports
  Convex
  Topology_Euclidean_Space
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Topological Properties of Convex Sets, Metric Spaces and Functions\<close>

lemma convex_supp_sum:
  assumes "convex S" and 1: "supp_sum u I = 1"
      and "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> u i \<and> (u i = 0 \<or> f i \<in> S)"
    shows "supp_sum (\<lambda>i. u i *\<^sub>R f i) I \<in> S"
proof -
  have fin: "finite {i \<in> I. u i \<noteq> 0}"
    using 1 sum.infinite by (force simp: supp_sum_def support_on_def)
  then have "supp_sum (\<lambda>i. u i *\<^sub>R f i) I = sum (\<lambda>i. u i *\<^sub>R f i) {i \<in> I. u i \<noteq> 0}"
    by (force intro: sum.mono_neutral_left simp: supp_sum_def support_on_def)
  also have "... \<in> S"
    using 1 assms by (force simp: supp_sum_def support_on_def intro: convex_sum [OF fin \<open>convex S\<close>])
  finally show ?thesis .
qed

lemma sphere_eq_empty [simp]:
  fixes a :: "'a::{real_normed_vector, perfect_space}"
  shows "sphere a r = {} \<longleftrightarrow> r < 0"
by (auto simp: sphere_def dist_norm) (metis dist_norm le_less_linear vector_choose_dist)

lemma cone_closure:
  fixes S :: "'a::real_normed_vector set"
  assumes "cone S"
  shows "cone (closure S)"
proof (cases "S = {}")
  case True
  then show ?thesis by auto
next
  case False
  then have "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` S = S)"
    using cone_iff[of S] assms by auto
  then have "0 \<in> closure S \<and> (\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` closure S = closure S)"
    using closure_subset by (auto simp: closure_scaleR)
  then show ?thesis
    using False cone_iff[of "closure S"] by auto
qed


corollary component_complement_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "connected S" "C \<in> components (-S)"
  shows "connected(-C)"
  using component_diff_connected [of S UNIV] assms
  by (auto simp: Compl_eq_Diff_UNIV)

proposition clopen:
  fixes S :: "'a :: real_normed_vector set"
  shows "closed S \<and> open S \<longleftrightarrow> S = {} \<or> S = UNIV"
  by (force intro!: connected_UNIV [unfolded connected_clopen, rule_format])

corollary compact_open:
  fixes S :: "'a :: euclidean_space set"
  shows "compact S \<and> open S \<longleftrightarrow> S = {}"
  by (auto simp: compact_eq_bounded_closed clopen)

corollary finite_imp_not_open:
  fixes S :: "'a::{real_normed_vector, perfect_space} set"
  shows "\<lbrakk>finite S; open S\<rbrakk> \<Longrightarrow> S={}"
  using clopen [of S] finite_imp_closed not_bounded_UNIV by blast

corollary empty_interior_finite:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "finite S \<Longrightarrow> interior S = {}"
  by (metis interior_subset finite_subset open_interior [of S] finite_imp_not_open)

text \<open>Balls, being convex, are connected.\<close>

lemma convex_local_global_minimum:
  fixes s :: "'a::real_normed_vector set"
  assumes "e > 0"
    and "convex_on s f"
    and "ball x e \<subseteq> s"
    and "\<forall>y\<in>ball x e. f x \<le> f y"
  shows "\<forall>y\<in>s. f x \<le> f y"
proof (rule ccontr)
  have "x \<in> s" using assms(1,3) by auto
  assume "\<not> ?thesis"
  then obtain y where "y\<in>s" and y: "f x > f y" by auto
  then have xy: "0 < dist x y"  by auto
  then obtain u where "0 < u" "u \<le> 1" and u: "u < e / dist x y"
    using field_lbound_gt_zero[of 1 "e / dist x y"] xy \<open>e>0\<close> by auto
  then have "f ((1-u) *\<^sub>R x + u *\<^sub>R y) \<le> (1-u) * f x + u * f y"
    using \<open>x\<in>s\<close> \<open>y\<in>s\<close>
    using assms(2)[unfolded convex_on_def,
      THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x="1-u"]]
    by auto
  moreover
  have *: "x - ((1 - u) *\<^sub>R x + u *\<^sub>R y) = u *\<^sub>R (x - y)"
    by (simp add: algebra_simps)
  have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> ball x e"
    unfolding mem_ball dist_norm
    unfolding * and norm_scaleR and abs_of_pos[OF \<open>0<u\<close>]
    unfolding dist_norm[symmetric]
    using u
    unfolding pos_less_divide_eq[OF xy]
    by auto
  then have "f x \<le> f ((1 - u) *\<^sub>R x + u *\<^sub>R y)"
    using assms(4) by auto
  ultimately show False
    using mult_strict_left_mono[OF y \<open>u>0\<close>]
    unfolding left_diff_distrib
    by auto
qed

lemma convex_ball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "convex (ball x e)"
proof (auto simp: convex_def)
  fix y z
  assume yz: "dist x y < e" "dist x z < e"
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z"
    using uv yz
    using convex_on_dist [of "ball x e" x, unfolded convex_on_def,
      THEN bspec[where x=y], THEN bspec[where x=z]]
    by auto
  then show "dist x (u *\<^sub>R y + v *\<^sub>R z) < e"
    using convex_bound_lt[OF yz uv] by auto
qed

lemma convex_cball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "convex (cball x e)"
proof -
  {
    fix y z
    assume yz: "dist x y \<le> e" "dist x z \<le> e"
    fix u v :: real
    assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
    have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z"
      using uv yz
      using convex_on_dist [of "cball x e" x, unfolded convex_on_def,
        THEN bspec[where x=y], THEN bspec[where x=z]]
      by auto
    then have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> e"
      using convex_bound_le[OF yz uv] by auto
  }
  then show ?thesis by (auto simp: convex_def Ball_def)
qed

lemma connected_ball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "connected (ball x e)"
  using convex_connected convex_ball by auto

lemma connected_cball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "connected (cball x e)"
  using convex_connected convex_cball by auto

lemma bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  assumes "bounded s"
  shows "bounded (convex hull s)"
proof -
  from assms obtain B where B: "\<forall>x\<in>s. norm x \<le> B"
    unfolding bounded_iff by auto
  show ?thesis
    by (simp add: bounded_subset[OF bounded_cball, of _ 0 B] B subsetI subset_hull)
qed

lemma finite_imp_bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  shows "finite s \<Longrightarrow> bounded (convex hull s)"
  using bounded_convex_hull finite_imp_bounded
  by auto


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


subsection \<open>Open and closed segments\<close>

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
  fixes a :: "'a::real_normed_vector" shows "bounded (closed_segment a b)"
  by (rule boundedI[where B="max (norm a) (norm b)"])
    (auto simp: closed_segment_def max_def convex_bound_le intro!: norm_triangle_le)

lemma bounded_open_segment:
    fixes a :: "'a::real_normed_vector" shows "bounded (open_segment a b)"
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
by (metis assms closed_segment_commute dist_commute dist_norm segment_bound1)+

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

lemma closed_segment_eq_real_ivl1:
  fixes a b::real
  assumes "a \<le> b"
  shows "closed_segment a b = {a .. b}"
proof safe
  fix x
  assume "x \<in> closed_segment a b"
  then obtain u where u: "0 \<le> u" "u \<le> 1" and x_def: "x = (1 - u) * a + u * b"
    by (auto simp: closed_segment_def)
  have "u * a \<le> u * b" "(1 - u) * a \<le> (1 - u) * b"
    by (auto intro!: mult_left_mono u assms)
  then show "x \<in> {a .. b}"
    unfolding x_def by (auto simp: algebra_simps)
next
  show "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<in> closed_segment a b"
    by (force simp: closed_segment_def divide_simps algebra_simps
              intro: exI[where x="(x - a) / (b - a)" for x])
qed 

lemma closed_segment_eq_real_ivl:
  fixes a b::real
  shows "closed_segment a b = (if a \<le> b then {a .. b} else {b .. a})"
  using closed_segment_eq_real_ivl1[of a b] closed_segment_eq_real_ivl1[of b a]
  by (auto simp: closed_segment_commute)

lemma open_segment_eq_real_ivl:
  fixes a b::real
  shows "open_segment a b = (if a \<le> b then {a<..<b} else {b<..<a})"
by (auto simp: closed_segment_eq_real_ivl open_segment_def split: if_split_asm)

lemma closed_segment_real_eq:
  fixes u::real shows "closed_segment u v = (\<lambda>x. (v - u) * x + u) ` {0..1}"
  by (simp add: add.commute [of u] image_affinity_atLeastAtMost [where c=u] closed_segment_eq_real_ivl)

lemma closed_segment_same_Re:
  assumes "Re a = Re b"
  shows   "closed_segment a b = {z. Re z = Re a \<and> Im z \<in> closed_segment (Im a) (Im b)}"
proof safe
  fix z assume "z \<in> closed_segment a b"
  then obtain u where u: "u \<in> {0..1}" "z = a + of_real u * (b - a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from assms show "Re z = Re a" by (auto simp: u)
  from u(1) show "Im z \<in> closed_segment (Im a) (Im b)"
    by (force simp: u closed_segment_def algebra_simps)
next
  fix z assume [simp]: "Re z = Re a" and "Im z \<in> closed_segment (Im a) (Im b)"
  then obtain u where u: "u \<in> {0..1}" "Im z = Im a + of_real u * (Im b - Im a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from u(1) show "z \<in> closed_segment a b" using assms
    by (force simp: u closed_segment_def algebra_simps scaleR_conv_of_real complex_eq_iff)
qed

lemma closed_segment_same_Im:
  assumes "Im a = Im b"
  shows   "closed_segment a b = {z. Im z = Im a \<and> Re z \<in> closed_segment (Re a) (Re b)}"
proof safe
  fix z assume "z \<in> closed_segment a b"
  then obtain u where u: "u \<in> {0..1}" "z = a + of_real u * (b - a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from assms show "Im z = Im a" by (auto simp: u)
  from u(1) show "Re z \<in> closed_segment (Re a) (Re b)"
    by (force simp: u closed_segment_def algebra_simps)
next
  fix z assume [simp]: "Im z = Im a" and "Re z \<in> closed_segment (Re a) (Re b)"
  then obtain u where u: "u \<in> {0..1}" "Re z = Re a + of_real u * (Re b - Re a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from u(1) show "z \<in> closed_segment a b" using assms
    by (force simp: u closed_segment_def algebra_simps scaleR_conv_of_real complex_eq_iff)
qed

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
    using assms mult_less_cancel_right2 u(2) by fastforce
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

corollary segment_furthest_le:
  fixes a b x y :: "'a::euclidean_space"
  assumes "x \<in> closed_segment a b"
  shows "norm (y - x) \<le> norm (y - a) \<or>  norm (y - x) \<le> norm (y - b)"
  by (metis assms dist_decreases_closed_segment dist_norm)

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

lemma connected_segment [iff]:
  fixes x :: "'a :: real_normed_vector"
  shows "connected (closed_segment x y)"
  by (simp add: convex_connected)

lemma is_interval_closed_segment_1[intro, simp]: "is_interval (closed_segment a b)" for a b::real
  unfolding closed_segment_eq_real_ivl
  by (auto simp: is_interval_def)

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

subsection \<open>Betweenness\<close>

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

end