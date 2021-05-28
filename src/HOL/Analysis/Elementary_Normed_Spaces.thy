(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary Normed Vector Spaces\<close>

theory Elementary_Normed_Spaces
  imports
  "HOL-Library.FuncSet"
  Elementary_Metric_Spaces Cartesian_Space
  Connected
begin
subsection \<open>Orthogonal Transformation of Balls\<close>

subsection\<^marker>\<open>tag unimportant\<close> \<open>Various Lemmas Combining Imports\<close>

lemma open_sums:
  fixes T :: "('b::real_normed_vector) set"
  assumes "open S \<or> open T"
  shows "open (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  using assms
proof
  assume S: "open S"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with S obtain e where "e > 0" and e: "\<And>x'. dist x' x < e \<Longrightarrow> x' \<in> S"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>y \<in> T\<close> diff_add_cancel dist_add_cancel2)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>x \<in> S\<close> by blast
  qed
next
  assume T: "open T"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with T obtain e where "e > 0" and e: "\<And>x'. dist x' y < e \<Longrightarrow> x' \<in> T"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>x \<in> S\<close> add_diff_cancel_left' add_diff_eq diff_diff_add dist_norm)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>y \<in> T\<close> by blast
  qed
qed

lemma image_orthogonal_transformation_ball:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "orthogonal_transformation f"
  shows "f ` ball x r = ball (f x) r"
proof (intro equalityI subsetI)
  fix y assume "y \<in> f ` ball x r"
  with assms show "y \<in> ball (f x) r"
    by (auto simp: orthogonal_transformation_isometry)
next
  fix y assume y: "y \<in> ball (f x) r"
  then obtain z where z: "y = f z"
    using assms orthogonal_transformation_surj by blast
  with y assms show "y \<in> f ` ball x r"
    by (auto simp: orthogonal_transformation_isometry)
qed

lemma image_orthogonal_transformation_cball:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "orthogonal_transformation f"
  shows "f ` cball x r = cball (f x) r"
proof (intro equalityI subsetI)
  fix y assume "y \<in> f ` cball x r"
  with assms show "y \<in> cball (f x) r"
    by (auto simp: orthogonal_transformation_isometry)
next
  fix y assume y: "y \<in> cball (f x) r"
  then obtain z where z: "y = f z"
    using assms orthogonal_transformation_surj by blast
  with y assms show "y \<in> f ` cball x r"
    by (auto simp: orthogonal_transformation_isometry)
qed


subsection \<open>Support\<close>

definition (in monoid_add) support_on :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b set"
  where "support_on S f = {x\<in>S. f x \<noteq> 0}"

lemma in_support_on: "x \<in> support_on S f \<longleftrightarrow> x \<in> S \<and> f x \<noteq> 0"
  by (simp add: support_on_def)

lemma support_on_simps[simp]:
  "support_on {} f = {}"
  "support_on (insert x S) f =
    (if f x = 0 then support_on S f else insert x (support_on S f))"
  "support_on (S \<union> T) f = support_on S f \<union> support_on T f"
  "support_on (S \<inter> T) f = support_on S f \<inter> support_on T f"
  "support_on (S - T) f = support_on S f - support_on T f"
  "support_on (f ` S) g = f ` (support_on S (g \<circ> f))"
  unfolding support_on_def by auto

lemma support_on_cong:
  "(\<And>x. x \<in> S \<Longrightarrow> f x = 0 \<longleftrightarrow> g x = 0) \<Longrightarrow> support_on S f = support_on S g"
  by (auto simp: support_on_def)

lemma support_on_if: "a \<noteq> 0 \<Longrightarrow> support_on A (\<lambda>x. if P x then a else 0) = {x\<in>A. P x}"
  by (auto simp: support_on_def)

lemma support_on_if_subset: "support_on A (\<lambda>x. if P x then a else 0) \<subseteq> {x \<in> A. P x}"
  by (auto simp: support_on_def)

lemma finite_support[intro]: "finite S \<Longrightarrow> finite (support_on S f)"
  unfolding support_on_def by auto

(* TODO: is supp_sum really needed? TODO: Generalize to Finite_Set.fold *)
definition (in comm_monoid_add) supp_sum :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  where "supp_sum f S = (\<Sum>x\<in>support_on S f. f x)"

lemma supp_sum_empty[simp]: "supp_sum f {} = 0"
  unfolding supp_sum_def by auto

lemma supp_sum_insert[simp]:
  "finite (support_on S f) \<Longrightarrow>
    supp_sum f (insert x S) = (if x \<in> S then supp_sum f S else f x + supp_sum f S)"
  by (simp add: supp_sum_def in_support_on insert_absorb)

lemma supp_sum_divide_distrib: "supp_sum f A / (r::'a::field) = supp_sum (\<lambda>n. f n / r) A"
  by (cases "r = 0")
     (auto simp: supp_sum_def sum_divide_distrib intro!: sum.cong support_on_cong)


subsection \<open>Intervals\<close>

lemma image_affinity_interval:
  fixes c :: "'a::ordered_real_vector"
  shows "((\<lambda>x. m *\<^sub>R x + c) ` {a..b}) = 
           (if {a..b}={} then {}
            else if 0 \<le> m then {m *\<^sub>R a + c .. m  *\<^sub>R b + c}
            else {m *\<^sub>R b + c .. m *\<^sub>R a + c})"
         (is "?lhs = ?rhs")
proof (cases "m=0")
  case True
  then show ?thesis
    by force
next
  case False
  show ?thesis
  proof
    show "?lhs \<subseteq> ?rhs"
      by (auto simp: scaleR_left_mono scaleR_left_mono_neg)
    show "?rhs \<subseteq> ?lhs"
    proof (clarsimp, intro conjI impI subsetI)
      show "\<lbrakk>0 \<le> m; a \<le> b; x \<in> {m *\<^sub>R a + c..m *\<^sub>R b + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        using False
        by (rule_tac x="inverse m *\<^sub>R (x-c)" in image_eqI)
           (auto simp: pos_le_divideR_eq pos_divideR_le_eq le_diff_eq diff_le_eq)
      show "\<lbrakk>\<not> 0 \<le> m; a \<le> b;  x \<in> {m *\<^sub>R b + c..m *\<^sub>R a + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        by (rule_tac x="inverse m *\<^sub>R (x-c)" in image_eqI)
           (auto simp add: neg_le_divideR_eq neg_divideR_le_eq le_diff_eq diff_le_eq)
    qed
  qed
qed

subsection \<open>Limit Points\<close>

lemma islimpt_ball:
  fixes x y :: "'a::{real_normed_vector,perfect_space}"
  shows "y islimpt ball x e \<longleftrightarrow> 0 < e \<and> y \<in> cball x e"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof
    {
      assume "e \<le> 0"
      then have *: "ball x e = {}"
        using ball_eq_empty[of x e] by auto
      have False using \<open>?lhs\<close>
        unfolding * using islimpt_EMPTY[of y] by auto
    }
    then show "e > 0" by (metis not_less)
    show "y \<in> cball x e"
      using closed_cball[of x e] islimpt_subset[of y "ball x e" "cball x e"]
        ball_subset_cball[of x e] \<open>?lhs\<close>
      unfolding closed_limpt by auto
  qed
  show ?lhs if ?rhs
  proof -
    from that have "e > 0" by auto
    {
      fix d :: real
      assume "d > 0"
      have "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
      proof (cases "d \<le> dist x y")
        case True
        then show ?thesis
        proof (cases "x = y")
          case True
          then have False
            using \<open>d \<le> dist x y\<close> \<open>d>0\<close> by auto
          then show ?thesis
            by auto
        next
          case False
          have "dist x (y - (d / (2 * dist y x)) *\<^sub>R (y - x)) =
            norm (x - y + (d / (2 * norm (y - x))) *\<^sub>R (y - x))"
            unfolding mem_cball mem_ball dist_norm diff_diff_eq2 diff_add_eq[symmetric]
            by auto
          also have "\<dots> = \<bar>- 1 + d / (2 * norm (x - y))\<bar> * norm (x - y)"
            using scaleR_left_distrib[of "- 1" "d / (2 * norm (y - x))", symmetric, of "y - x"]
            unfolding scaleR_minus_left scaleR_one
            by (auto simp: norm_minus_commute)
          also have "\<dots> = \<bar>- norm (x - y) + d / 2\<bar>"
            unfolding abs_mult_pos[of "norm (x - y)", OF norm_ge_zero[of "x - y"]]
            unfolding distrib_right using \<open>x\<noteq>y\<close>  by auto
          also have "\<dots> \<le> e - d/2" using \<open>d \<le> dist x y\<close> and \<open>d>0\<close> and \<open>?rhs\<close>
            by (auto simp: dist_norm)
          finally have "y - (d / (2 * dist y x)) *\<^sub>R (y - x) \<in> ball x e" using \<open>d>0\<close>
            by auto
          moreover
          have "(d / (2*dist y x)) *\<^sub>R (y - x) \<noteq> 0"
            using \<open>x\<noteq>y\<close>[unfolded dist_nz] \<open>d>0\<close> unfolding scaleR_eq_0_iff
            by (auto simp: dist_commute)
          moreover
          have "dist (y - (d / (2 * dist y x)) *\<^sub>R (y - x)) y < d"
            using \<open>0 < d\<close> by (fastforce simp: dist_norm)
          ultimately show ?thesis
            by (rule_tac x = "y - (d / (2*dist y x)) *\<^sub>R (y - x)" in bexI) auto
        qed
      next
        case False
        then have "d > dist x y" by auto
        show "\<exists>x' \<in> ball x e. x' \<noteq> y \<and> dist x' y < d"
        proof (cases "x = y")
          case True
          obtain z where z: "z \<noteq> y" "dist z y < min e d"
            using perfect_choose_dist[of "min e d" y]
            using \<open>d > 0\<close> \<open>e>0\<close> by auto
          show ?thesis
            by (metis True z dist_commute mem_ball min_less_iff_conj)
        next
          case False
          then show ?thesis
            using \<open>d>0\<close> \<open>d > dist x y\<close> \<open>?rhs\<close> by force
        qed
      qed
    }
    then show ?thesis
      unfolding mem_cball islimpt_approachable mem_ball by auto
  qed
qed

lemma closure_ball_lemma:
  fixes x y :: "'a::real_normed_vector"
  assumes "x \<noteq> y"
  shows "y islimpt ball x (dist x y)"
proof (rule islimptI)
  fix T
  assume "y \<in> T" "open T"
  then obtain r where "0 < r" "\<forall>z. dist z y < r \<longrightarrow> z \<in> T"
    unfolding open_dist by fast
  \<comment>\<open>choose point between @{term x} and @{term y}, within distance @{term r} of @{term y}.\<close>
  define k where "k = min 1 (r / (2 * dist x y))"
  define z where "z = y + scaleR k (x - y)"
  have z_def2: "z = x + scaleR (1 - k) (y - x)"
    unfolding z_def by (simp add: algebra_simps)
  have "dist z y < r"
    unfolding z_def k_def using \<open>0 < r\<close>
    by (simp add: dist_norm min_def)
  then have "z \<in> T"
    using \<open>\<forall>z. dist z y < r \<longrightarrow> z \<in> T\<close> by simp
  have "dist x z < dist x y"
    using \<open>0 < r\<close> assms by (simp add: z_def2 k_def dist_norm norm_minus_commute) 
  then have "z \<in> ball x (dist x y)"
    by simp
  have "z \<noteq> y"
    unfolding z_def k_def using \<open>x \<noteq> y\<close> \<open>0 < r\<close>
    by (simp add: min_def)
  show "\<exists>z\<in>ball x (dist x y). z \<in> T \<and> z \<noteq> y"
    using \<open>z \<in> ball x (dist x y)\<close> \<open>z \<in> T\<close> \<open>z \<noteq> y\<close>
    by fast
qed


subsection \<open>Balls and Spheres in Normed Spaces\<close>

lemma mem_ball_0 [simp]: "x \<in> ball 0 e \<longleftrightarrow> norm x < e"
  for x :: "'a::real_normed_vector"
  by simp

lemma mem_cball_0 [simp]: "x \<in> cball 0 e \<longleftrightarrow> norm x \<le> e"
  for x :: "'a::real_normed_vector"
  by simp

lemma closure_ball [simp]:
  fixes x :: "'a::real_normed_vector"
  assumes "0 < e"
  shows "closure (ball x e) = cball x e"
proof
  show "closure (ball x e) \<subseteq> cball x e"
    using closed_cball closure_minimal by blast
  have "\<And>y. dist x y < e \<or> dist x y = e \<Longrightarrow> y \<in> closure (ball x e)"
    by (metis Un_iff assms closure_ball_lemma closure_def dist_eq_0_iff mem_Collect_eq mem_ball)
  then show "cball x e \<subseteq> closure (ball x e)"
    by force
qed

lemma mem_sphere_0 [simp]: "x \<in> sphere 0 e \<longleftrightarrow> norm x = e"
  for x :: "'a::real_normed_vector"
  by simp

(* In a trivial vector space, this fails for e = 0. *)
lemma interior_cball [simp]:
  fixes x :: "'a::{real_normed_vector, perfect_space}"
  shows "interior (cball x e) = ball x e"
proof (cases "e \<ge> 0")
  case False note cs = this
  from cs have null: "ball x e = {}"
    using ball_empty[of e x] by auto
  moreover
  have "cball x e = {}"
  proof (rule equals0I)
    fix y
    assume "y \<in> cball x e"
    then show False
      by (metis ball_eq_empty null cs dist_eq_0_iff dist_le_zero_iff empty_subsetI mem_cball
          subset_antisym subset_ball)
  qed
  then have "interior (cball x e) = {}"
    using interior_empty by auto
  ultimately show ?thesis by blast
next
  case True note cs = this
  have "ball x e \<subseteq> cball x e"
    using ball_subset_cball by auto
  moreover
  {
    fix S y
    assume as: "S \<subseteq> cball x e" "open S" "y\<in>S"
    then obtain d where "d>0" and d: "\<forall>x'. dist x' y < d \<longrightarrow> x' \<in> S"
      unfolding open_dist by blast
    then obtain xa where xa_y: "xa \<noteq> y" and xa: "dist xa y < d"
      using perfect_choose_dist [of d] by auto
    have "xa \<in> S"
      using d[THEN spec[where x = xa]]
      using xa by (auto simp: dist_commute)
    then have xa_cball: "xa \<in> cball x e"
      using as(1) by auto
    then have "y \<in> ball x e"
    proof (cases "x = y")
      case True
      then have "e > 0" using cs order.order_iff_strict xa_cball xa_y by fastforce
      then show "y \<in> ball x e"
        using \<open>x = y \<close> by simp
    next
      case False
      have "dist (y + (d / 2 / dist y x) *\<^sub>R (y - x)) y < d"
        unfolding dist_norm
        using \<open>d>0\<close> norm_ge_zero[of "y - x"] \<open>x \<noteq> y\<close> by auto
      then have *: "y + (d / 2 / dist y x) *\<^sub>R (y - x) \<in> cball x e"
        using d as(1)[unfolded subset_eq] by blast
      have "y - x \<noteq> 0" using \<open>x \<noteq> y\<close> by auto
      hence **:"d / (2 * norm (y - x)) > 0"
        unfolding zero_less_norm_iff[symmetric] using \<open>d>0\<close> by auto
      have "dist (y + (d / 2 / dist y x) *\<^sub>R (y - x)) x =
        norm (y + (d / (2 * norm (y - x))) *\<^sub>R y - (d / (2 * norm (y - x))) *\<^sub>R x - x)"
        by (auto simp: dist_norm algebra_simps)
      also have "\<dots> = norm ((1 + d / (2 * norm (y - x))) *\<^sub>R (y - x))"
        by (auto simp: algebra_simps)
      also have "\<dots> = \<bar>1 + d / (2 * norm (y - x))\<bar> * norm (y - x)"
        using ** by auto
      also have "\<dots> = (dist y x) + d/2"
        using ** by (auto simp: distrib_right dist_norm)
      finally have "e \<ge> dist x y +d/2"
        using *[unfolded mem_cball] by (auto simp: dist_commute)
      then show "y \<in> ball x e"
        unfolding mem_ball using \<open>d>0\<close> by auto
    qed
  }
  then have "\<forall>S \<subseteq> cball x e. open S \<longrightarrow> S \<subseteq> ball x e"
    by auto
  ultimately show ?thesis
    using interior_unique[of "ball x e" "cball x e"]
    using open_ball[of x e]
    by auto
qed

lemma frontier_ball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "0 < e \<Longrightarrow> frontier (ball a e) = sphere a e"
  by (force simp: frontier_def)

lemma frontier_cball [simp]:
  fixes a :: "'a::{real_normed_vector, perfect_space}"
  shows "frontier (cball a e) = sphere a e"
  by (force simp: frontier_def)

corollary compact_sphere [simp]:
  fixes a :: "'a::{real_normed_vector,perfect_space,heine_borel}"
  shows "compact (sphere a r)"
using compact_frontier [of "cball a r"] by simp

corollary bounded_sphere [simp]:
  fixes a :: "'a::{real_normed_vector,perfect_space,heine_borel}"
  shows "bounded (sphere a r)"
by (simp add: compact_imp_bounded)

corollary closed_sphere  [simp]:
  fixes a :: "'a::{real_normed_vector,perfect_space,heine_borel}"
  shows "closed (sphere a r)"
by (simp add: compact_imp_closed)

lemma image_add_ball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "(+) b ` ball a r = ball (a+b) r"
proof -
  { fix x :: 'a
    assume "dist (a + b) x < r"
    moreover
    have "b + (x - b) = x"
      by simp
    ultimately have "x \<in> (+) b ` ball a r"
      by (metis add.commute dist_add_cancel image_eqI mem_ball) }
  then show ?thesis
    by (auto simp: add.commute)
qed

lemma image_add_cball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "(+) b ` cball a r = cball (a+b) r"
proof -
  have "\<And>x. dist (a + b) x \<le> r \<Longrightarrow> \<exists>y\<in>cball a r. x = b + y"
    by (metis (no_types) add.commute diff_add_cancel dist_add_cancel2 mem_cball)
  then show ?thesis
    by (force simp: add.commute)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Various Lemmas on Normed Algebras\<close>


lemma closed_of_nat_image: "closed (of_nat ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_nat)

lemma closed_of_int_image: "closed (of_int ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_int)

lemma closed_Nats [simp]: "closed (\<nat> :: 'a :: real_normed_algebra_1 set)"
  unfolding Nats_def by (rule closed_of_nat_image)

lemma closed_Ints [simp]: "closed (\<int> :: 'a :: real_normed_algebra_1 set)"
  unfolding Ints_def by (rule closed_of_int_image)

lemma closed_subset_Ints:
  fixes A :: "'a :: real_normed_algebra_1 set"
  assumes "A \<subseteq> \<int>"
  shows   "closed A"
proof (intro discrete_imp_closed[OF zero_less_one] ballI impI, goal_cases)
  case (1 x y)
  with assms have "x \<in> \<int>" and "y \<in> \<int>" by auto
  with \<open>dist y x < 1\<close> show "y = x"
    by (auto elim!: Ints_cases simp: dist_of_int)
qed

subsection \<open>Filters\<close>

definition indirection :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'a filter"  (infixr "indirection" 70)
  where "a indirection v = at a within {b. \<exists>c\<ge>0. b - a = scaleR c v}"


subsection \<open>Trivial Limits\<close>

lemma trivial_limit_at_infinity:
  "\<not> trivial_limit (at_infinity :: ('a::{real_normed_vector,perfect_space}) filter)"
proof -
  obtain x::'a where "x \<noteq> 0"
    by (meson perfect_choose_dist zero_less_one)
  then have "b \<le> norm ((b / norm x) *\<^sub>R x)" for b
    by simp
  then show ?thesis
    unfolding trivial_limit_def eventually_at_infinity
    by blast
qed

lemma at_within_ball_bot_iff:
  fixes x y :: "'a::{real_normed_vector,perfect_space}"
  shows "at x within ball y r = bot \<longleftrightarrow> (r=0 \<or> x \<notin> cball y r)"
  unfolding trivial_limit_within
  by (metis (no_types) cball_empty equals0D islimpt_ball less_linear) 


subsection \<open>Limits\<close>

proposition Lim_at_infinity: "(f \<longlongrightarrow> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x. norm x \<ge> b \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_infinity)

corollary Lim_at_infinityI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>B. \<forall>x. norm x \<ge> B \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) at_infinity"
proof -
  have "\<And>e. e > 0 \<Longrightarrow> \<exists>B. \<forall>x. norm x \<ge> B \<longrightarrow> dist (f x) l < e"
    by (meson assms dense le_less_trans)
  then show ?thesis
    using Lim_at_infinity by blast
qed

lemma Lim_transform_within_set_eq:
  fixes a :: "'a::metric_space" and l :: "'b::metric_space"
  shows "eventually (\<lambda>x. x \<in> S \<longleftrightarrow> x \<in> T) (at a)
         \<Longrightarrow> ((f \<longlongrightarrow> l) (at a within S) \<longleftrightarrow> (f \<longlongrightarrow> l) (at a within T))"
  by (force intro: Lim_transform_within_set elim: eventually_mono)

lemma Lim_null:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f \<longlongrightarrow> l) net \<longleftrightarrow> ((\<lambda>x. f(x) - l) \<longlongrightarrow> 0) net"
  by (simp add: Lim dist_norm)

lemma Lim_null_comparison:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "eventually (\<lambda>x. norm (f x) \<le> g x) net" "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(2)
proof (rule metric_tendsto_imp_tendsto)
  show "eventually (\<lambda>x. dist (f x) 0 \<le> dist (g x) 0) net"
    using assms(1) by (rule eventually_mono) (simp add: dist_norm)
qed

lemma Lim_transform_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
    and g :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) net"
    and "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(1) tendsto_norm_zero [OF assms(2)]
  by (rule Lim_null_comparison)

lemma lim_null_mult_right_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "eventually (\<lambda>x. norm(g x) \<le> B) F"
    shows "((\<lambda>z. f z * g z) \<longlongrightarrow> 0) F"
proof -
  have "((\<lambda>x. norm (f x) * norm (g x)) \<longlongrightarrow> 0) F"
  proof (rule Lim_null_comparison)
    show "\<forall>\<^sub>F x in F. norm (norm (f x) * norm (g x)) \<le> norm (f x) * B"
      by (simp add: eventually_mono [OF g] mult_left_mono)
    show "((\<lambda>x. norm (f x) * B) \<longlongrightarrow> 0) F"
      by (simp add: f tendsto_mult_left_zero tendsto_norm_zero)
  qed
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_mult_left_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes g: "eventually (\<lambda>x. norm(g x) \<le> B) F" and f: "(f \<longlongrightarrow> 0) F"
    shows "((\<lambda>z. g z * f z) \<longlongrightarrow> 0) F"
proof -
  have "((\<lambda>x. norm (g x) * norm (f x)) \<longlongrightarrow> 0) F"
  proof (rule Lim_null_comparison)
    show "\<forall>\<^sub>F x in F. norm (norm (g x) * norm (f x)) \<le> B * norm (f x)"
      by (simp add: eventually_mono [OF g] mult_right_mono)
    show "((\<lambda>x. B * norm (f x)) \<longlongrightarrow> 0) F"
      by (simp add: f tendsto_mult_right_zero tendsto_norm_zero)
  qed
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_scaleR_bounded:
  assumes f: "(f \<longlongrightarrow> 0) net" and gB: "eventually (\<lambda>a. f a = 0 \<or> norm(g a) \<le> B) net"
    shows "((\<lambda>n. f n *\<^sub>R g n) \<longlongrightarrow> 0) net"
proof
  fix \<epsilon>::real
  assume "0 < \<epsilon>"
  then have B: "0 < \<epsilon> / (abs B + 1)" by simp
  have *: "\<bar>f x\<bar> * norm (g x) < \<epsilon>" if f: "\<bar>f x\<bar> * (\<bar>B\<bar> + 1) < \<epsilon>" and g: "norm (g x) \<le> B" for x
  proof -
    have "\<bar>f x\<bar> * norm (g x) \<le> \<bar>f x\<bar> * B"
      by (simp add: mult_left_mono g)
    also have "\<dots> \<le> \<bar>f x\<bar> * (\<bar>B\<bar> + 1)"
      by (simp add: mult_left_mono)
    also have "\<dots> < \<epsilon>"
      by (rule f)
    finally show ?thesis .
  qed
  have "\<And>x. \<lbrakk>\<bar>f x\<bar> < \<epsilon> / (\<bar>B\<bar> + 1); norm (g x) \<le> B\<rbrakk> \<Longrightarrow> \<bar>f x\<bar> * norm (g x) < \<epsilon>"
    by (simp add: "*" pos_less_divide_eq)
  then show "\<forall>\<^sub>F x in net. dist (f x *\<^sub>R g x) 0 < \<epsilon>"
    using \<open>0 < \<epsilon>\<close> by (auto intro: eventually_mono [OF eventually_conj [OF tendstoD [OF f B] gB]])
qed

lemma Lim_norm_ubound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not>(trivial_limit net)" "(f \<longlongrightarrow> l) net" "eventually (\<lambda>x. norm(f x) \<le> e) net"
  shows "norm(l) \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)

lemma Lim_norm_lbound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not> trivial_limit net"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. e \<le> norm (f x)) net"
  shows "e \<le> norm l"
  using assms by (fast intro: tendsto_le tendsto_intros)

text\<open>Limit under bilinear function\<close>

lemma Lim_bilinear:
  assumes "(f \<longlongrightarrow> l) net"
    and "(g \<longlongrightarrow> m) net"
    and "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) \<longlongrightarrow> (h l m)) net"
  using \<open>bounded_bilinear h\<close> \<open>(f \<longlongrightarrow> l) net\<close> \<open>(g \<longlongrightarrow> m) net\<close>
  by (rule bounded_bilinear.tendsto)

lemma Lim_at_zero:
  fixes a :: "'a::real_normed_vector"
    and l :: "'b::topological_space"
  shows "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow> ((\<lambda>x. f(a + x)) \<longlongrightarrow> l) (at 0)"
  using LIM_offset_zero LIM_offset_zero_cancel ..


subsection\<^marker>\<open>tag unimportant\<close> \<open>Limit Point of Filter\<close>

lemma netlimit_at_vector:
  fixes a :: "'a::real_normed_vector"
  shows "netlimit (at a) = a"
proof (cases "\<exists>x. x \<noteq> a")
  case True then obtain x where x: "x \<noteq> a" ..
  have "\<And>d. 0 < d \<Longrightarrow> \<exists>x. x \<noteq> a \<and> norm (x - a) < d"
    by (rule_tac x="a + scaleR (d / 2) (sgn (x - a))" in exI) (simp add: norm_sgn sgn_zero_iff x)
  then have "\<not> trivial_limit (at a)"
    by (auto simp: trivial_limit_def eventually_at dist_norm)
  then show ?thesis
    by (rule Lim_ident_at [of a UNIV])
qed simp

subsection \<open>Boundedness\<close>

lemma continuous_on_closure_norm_le:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous_on (closure s) f"
    and "\<forall>y \<in> s. norm(f y) \<le> b"
    and "x \<in> (closure s)"
  shows "norm (f x) \<le> b"
proof -
  have *: "f ` s \<subseteq> cball 0 b"
    using assms(2)[unfolded mem_cball_0[symmetric]] by auto
  show ?thesis
    by (meson "*" assms(1) assms(3) closed_cball image_closure_subset image_subset_iff mem_cball_0)
qed

lemma bounded_pos: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x \<le> b)"
  unfolding bounded_iff 
  by (meson less_imp_le not_le order_trans zero_less_one)

lemma bounded_pos_less: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x < b)"
  by (metis bounded_pos le_less_trans less_imp_le linordered_field_no_ub)

lemma Bseq_eq_bounded:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "Bseq f \<longleftrightarrow> bounded (range f)"
  unfolding Bseq_def bounded_pos by auto

lemma bounded_linear_image:
  assumes "bounded S"
    and "bounded_linear f"
  shows "bounded (f ` S)"
proof -
  from assms(1) obtain b where "b > 0" and b: "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  from assms(2) obtain B where B: "B > 0" "\<forall>x. norm (f x) \<le> B * norm x"
    using bounded_linear.pos_bounded by (auto simp: ac_simps)
  show ?thesis
    unfolding bounded_pos
  proof (intro exI, safe)
    show "norm (f x) \<le> B * b" if "x \<in> S" for x
      by (meson B b less_imp_le mult_left_mono order_trans that)
  qed (use \<open>b > 0\<close> \<open>B > 0\<close> in auto)
qed

lemma bounded_scaling:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. c *\<^sub>R x) ` S)"
  by (simp add: bounded_linear_image bounded_linear_scaleR_right)

lemma bounded_scaleR_comp:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  shows "bounded ((\<lambda>x. r *\<^sub>R f x) ` S)"
  using bounded_scaling[of "f ` S" r] assms
  by (auto simp: image_image)

lemma bounded_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S"
  shows "bounded ((\<lambda>x. a + x) ` S)"
proof -
  from assms obtain b where b: "b > 0" "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  {
    fix x
    assume "x \<in> S"
    then have "norm (a + x) \<le> b + norm a"
      using norm_triangle_ineq[of a x] b by auto
  }
  then show ?thesis
    unfolding bounded_pos
    using norm_ge_zero[of a] b(1) and add_strict_increasing[of b 0 "norm a"]
    by (auto intro!: exI[of _ "b + norm a"])
qed

lemma bounded_translation_minus:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. x - a) ` S)"
using bounded_translation [of S "-a"] by simp

lemma bounded_uminus [simp]:
  fixes X :: "'a::real_normed_vector set"
  shows "bounded (uminus ` X) \<longleftrightarrow> bounded X"
by (auto simp: bounded_def dist_norm; rule_tac x="-x" in exI; force simp: add.commute norm_minus_commute)

lemma uminus_bounded_comp [simp]:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "bounded ((\<lambda>x. - f x) ` S) \<longleftrightarrow> bounded (f ` S)"
  using bounded_uminus[of "f ` S"]
  by (auto simp: image_image)

lemma bounded_plus_comp:
  fixes f g::"'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  assumes "bounded (g ` S)"
  shows "bounded ((\<lambda>x. f x + g x) ` S)"
proof -
  {
    fix B C
    assume "\<And>x. x\<in>S \<Longrightarrow> norm (f x) \<le> B" "\<And>x. x\<in>S \<Longrightarrow> norm (g x) \<le> C"
    then have "\<And>x. x \<in> S \<Longrightarrow> norm (f x + g x) \<le> B + C"
      by (auto intro!: norm_triangle_le add_mono)
  } then show ?thesis
    using assms by (fastforce simp: bounded_iff)
qed

lemma bounded_plus:
  fixes S ::"'a::real_normed_vector set"
  assumes "bounded S" "bounded T"
  shows "bounded ((\<lambda>(x,y). x + y) ` (S \<times> T))"
  using bounded_plus_comp [of fst "S \<times> T" snd] assms
  by (auto simp: split_def split: if_split_asm)

lemma bounded_minus_comp:
  "bounded (f ` S) \<Longrightarrow> bounded (g ` S) \<Longrightarrow> bounded ((\<lambda>x. f x - g x) ` S)"
  for f g::"'a \<Rightarrow> 'b::real_normed_vector"
  using bounded_plus_comp[of "f" S "\<lambda>x. - g x"]
  by auto

lemma bounded_minus:
  fixes S ::"'a::real_normed_vector set"
  assumes "bounded S" "bounded T"
  shows "bounded ((\<lambda>(x,y). x - y) ` (S \<times> T))"
  using bounded_minus_comp [of fst "S \<times> T" snd] assms
  by (auto simp: split_def split: if_split_asm)

lemma bounded_sums:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S" and "bounded T"
  shows "bounded (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  using assms by (simp add: bounded_iff) (meson norm_triangle_mono)

lemma bounded_differences:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S" and "bounded T"
  shows "bounded (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
  using assms by (simp add: bounded_iff) (meson add_mono norm_triangle_le_diff)

lemma not_bounded_UNIV[simp]:
  "\<not> bounded (UNIV :: 'a::{real_normed_vector, perfect_space} set)"
proof (auto simp: bounded_pos not_le)
  obtain x :: 'a where "x \<noteq> 0"
    using perfect_choose_dist [OF zero_less_one] by fast
  fix b :: real
  assume b: "b >0"
  have b1: "b +1 \<ge> 0"
    using b by simp
  with \<open>x \<noteq> 0\<close> have "b < norm (scaleR (b + 1) (sgn x))"
    by (simp add: norm_sgn)
  then show "\<exists>x::'a. b < norm x" ..
qed

corollary cobounded_imp_unbounded:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded (- S) \<Longrightarrow> \<not> bounded S"
  using bounded_Un [of S "-S"]  by (simp)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relations among convergence and absolute convergence for power series\<close>

lemma summable_imp_bounded:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable f \<Longrightarrow> bounded (range f)"
by (frule summable_LIMSEQ_zero) (simp add: convergent_imp_bounded)

lemma summable_imp_sums_bounded:
   "summable f \<Longrightarrow> bounded (range (\<lambda>n. sum f {..<n}))"
by (auto simp: summable_def sums_def dest: convergent_imp_bounded)

lemma power_series_conv_imp_absconv_weak:
  fixes a:: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}" and w :: 'a
  assumes sum: "summable (\<lambda>n. a n * z ^ n)" and no: "norm w < norm z"
    shows "summable (\<lambda>n. of_real(norm(a n)) * w ^ n)"
proof -
  obtain M where M: "\<And>x. norm (a x * z ^ x) \<le> M"
    using summable_imp_bounded [OF sum] by (force simp: bounded_iff)
  show ?thesis
  proof (rule series_comparison_complex)
    have "\<And>n. norm (a n) * norm z ^ n \<le> M"
      by (metis (no_types) M norm_mult norm_power)
    then show "summable (\<lambda>n. complex_of_real (norm (a n) * norm w ^ n))"
      using Abel_lemma no norm_ge_zero summable_of_real by blast
  qed (auto simp: norm_mult norm_power)
qed


subsection \<open>Normed spaces with the Heine-Borel property\<close>

lemma not_compact_UNIV[simp]:
  fixes s :: "'a::{real_normed_vector,perfect_space,heine_borel} set"
  shows "\<not> compact (UNIV::'a set)"
    by (simp add: compact_eq_bounded_closed)

lemma not_compact_space_euclideanreal [simp]: "\<not> compact_space euclideanreal"
  by (simp add: compact_space_def)

text\<open>Representing sets as the union of a chain of compact sets.\<close>
lemma closed_Union_compact_subsets:
  fixes S :: "'a::{heine_borel,real_normed_vector} set"
  assumes "closed S"
  obtains F where "\<And>n. compact(F n)" "\<And>n. F n \<subseteq> S" "\<And>n. F n \<subseteq> F(Suc n)"
                  "(\<Union>n. F n) = S" "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n \<ge> N. K \<subseteq> F n"
proof
  show "compact (S \<inter> cball 0 (of_nat n))" for n
    using assms compact_eq_bounded_closed by auto
next
  show "(\<Union>n. S \<inter> cball 0 (real n)) = S"
    by (auto simp: real_arch_simple)
next
  fix K :: "'a set"
  assume "compact K" "K \<subseteq> S"
  then obtain N where "K \<subseteq> cball 0 N"
    by (meson bounded_pos mem_cball_0 compact_imp_bounded subsetI)
  then show "\<exists>N. \<forall>n\<ge>N. K \<subseteq> S \<inter> cball 0 (real n)"
    by (metis of_nat_le_iff Int_subset_iff \<open>K \<subseteq> S\<close> real_arch_simple subset_cball subset_trans)
qed auto

subsection \<open>Intersecting chains of compact sets and the Baire property\<close>

proposition bounded_closed_chain:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "B \<in> \<F>" "bounded B" and \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> closed S" and "{} \<notin> \<F>"
      and chain: "\<And>S T. S \<in> \<F> \<and> T \<in> \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    shows "\<Inter>\<F> \<noteq> {}"
proof -
  have "B \<inter> \<Inter>\<F> \<noteq> {}"
  proof (rule compact_imp_fip)
    show "compact B" "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      by (simp_all add: assms compact_eq_bounded_closed)
    show "\<lbrakk>finite \<G>; \<G> \<subseteq> \<F>\<rbrakk> \<Longrightarrow> B \<inter> \<Inter>\<G> \<noteq> {}" for \<G>
    proof (induction \<G> rule: finite_induct)
      case empty
      with assms show ?case by force
    next
      case (insert U \<G>)
      then have "U \<in> \<F>" and ne: "B \<inter> \<Inter>\<G> \<noteq> {}" by auto
      then consider "B \<subseteq> U" | "U \<subseteq> B"
          using \<open>B \<in> \<F>\<close> chain by blast
        then show ?case
        proof cases
          case 1
          then show ?thesis
            using Int_left_commute ne by auto
        next
          case 2
          have "U \<noteq> {}"
            using \<open>U \<in> \<F>\<close> \<open>{} \<notin> \<F>\<close> by blast
          moreover
          have False if "\<And>x. x \<in> U \<Longrightarrow> \<exists>Y\<in>\<G>. x \<notin> Y"
          proof -
            have "\<And>x. x \<in> U \<Longrightarrow> \<exists>Y\<in>\<G>. Y \<subseteq> U"
              by (metis chain contra_subsetD insert.prems insert_subset that)
            then obtain Y where "Y \<in> \<G>" "Y \<subseteq> U"
              by (metis all_not_in_conv \<open>U \<noteq> {}\<close>)
            moreover obtain x where "x \<in> \<Inter>\<G>"
              by (metis Int_emptyI ne)
            ultimately show ?thesis
              by (metis Inf_lower subset_eq that)
          qed
          with 2 show ?thesis
            by blast
        qed
      qed
  qed
  then show ?thesis by blast
qed

corollary compact_chain:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> compact S" "{} \<notin> \<F>"
          "\<And>S T. S \<in> \<F> \<and> T \<in> \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    shows "\<Inter> \<F> \<noteq> {}"
proof (cases "\<F> = {}")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis
    by (metis False all_not_in_conv assms compact_imp_bounded compact_imp_closed bounded_closed_chain)
qed

lemma compact_nest:
  fixes F :: "'a::linorder \<Rightarrow> 'b::heine_borel set"
  assumes F: "\<And>n. compact(F n)" "\<And>n. F n \<noteq> {}" and mono: "\<And>m n. m \<le> n \<Longrightarrow> F n \<subseteq> F m"
  shows "\<Inter>(range F) \<noteq> {}"
proof -
  have *: "\<And>S T. S \<in> range F \<and> T \<in> range F \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    by (metis mono image_iff le_cases)
  show ?thesis
    using F by (intro compact_chain [OF _ _ *]; blast dest: *)
qed

text\<open>The Baire property of dense sets\<close>
theorem Baire:
  fixes S::"'a::{real_normed_vector,heine_borel} set"
  assumes "closed S" "countable \<G>"
      and ope: "\<And>T. T \<in> \<G> \<Longrightarrow> openin (top_of_set S) T \<and> S \<subseteq> closure T"
 shows "S \<subseteq> closure(\<Inter>\<G>)"
proof (cases "\<G> = {}")
  case True
  then show ?thesis
    using closure_subset by auto
next
  let ?g = "from_nat_into \<G>"
  case False
  then have gin: "?g n \<in> \<G>" for n
    by (simp add: from_nat_into)
  show ?thesis
  proof (clarsimp simp: closure_approachable)
    fix x and e::real
    assume "x \<in> S" "0 < e"
    obtain TF where opeF: "\<And>n. openin (top_of_set S) (TF n)"
               and ne: "\<And>n. TF n \<noteq> {}"
               and subg: "\<And>n. S \<inter> closure(TF n) \<subseteq> ?g n"
               and subball: "\<And>n. closure(TF n) \<subseteq> ball x e"
               and decr: "\<And>n. TF(Suc n) \<subseteq> TF n"
    proof -
      have *: "\<exists>Y. (openin (top_of_set S) Y \<and> Y \<noteq> {} \<and>
                   S \<inter> closure Y \<subseteq> ?g n \<and> closure Y \<subseteq> ball x e) \<and> Y \<subseteq> U"
        if opeU: "openin (top_of_set S) U" and "U \<noteq> {}" and cloU: "closure U \<subseteq> ball x e" for U n
      proof -
        obtain T where T: "open T" "U = T \<inter> S"
          using \<open>openin (top_of_set S) U\<close> by (auto simp: openin_subtopology)
        with \<open>U \<noteq> {}\<close> have "T \<inter> closure (?g n) \<noteq> {}"
          using gin ope by fastforce
        then have "T \<inter> ?g n \<noteq> {}"
          using \<open>open T\<close> open_Int_closure_eq_empty by blast
        then obtain y where "y \<in> U" "y \<in> ?g n"
          using T ope [of "?g n", OF gin] by (blast dest:  openin_imp_subset)
        moreover have "openin (top_of_set S) (U \<inter> ?g n)"
          using gin ope opeU by blast
        ultimately obtain d where U: "U \<inter> ?g n \<subseteq> S" and "d > 0" and d: "ball y d \<inter> S \<subseteq> U \<inter> ?g n"
          by (force simp: openin_contains_ball)
        show ?thesis
        proof (intro exI conjI)
          show "openin (top_of_set S) (S \<inter> ball y (d/2))"
            by (simp add: openin_open_Int)
          show "S \<inter> ball y (d/2) \<noteq> {}"
            using \<open>0 < d\<close> \<open>y \<in> U\<close> opeU openin_imp_subset by fastforce
          have "S \<inter> closure (S \<inter> ball y (d/2)) \<subseteq> S \<inter> closure (ball y (d/2))"
            using closure_mono by blast
          also have "... \<subseteq> ?g n"
            using \<open>d > 0\<close> d by force
          finally show "S \<inter> closure (S \<inter> ball y (d/2)) \<subseteq> ?g n" .
          have "closure (S \<inter> ball y (d/2)) \<subseteq> S \<inter> ball y d"
          proof -
            have "closure (ball y (d/2)) \<subseteq> ball y d"
              using \<open>d > 0\<close> by auto
            then have "closure (S \<inter> ball y (d/2)) \<subseteq> ball y d"
              by (meson closure_mono inf.cobounded2 subset_trans)
            then show ?thesis
              by (simp add: \<open>closed S\<close> closure_minimal)
          qed
          also have "...  \<subseteq> ball x e"
            using cloU closure_subset d by blast
          finally show "closure (S \<inter> ball y (d/2)) \<subseteq> ball x e" .
          show "S \<inter> ball y (d/2) \<subseteq> U"
            using ball_divide_subset_numeral d by blast
        qed
      qed
      let ?\<Phi> = "\<lambda>n X. openin (top_of_set S) X \<and> X \<noteq> {} \<and>
                      S \<inter> closure X \<subseteq> ?g n \<and> closure X \<subseteq> ball x e"
      have "closure (S \<inter> ball x (e/2)) \<subseteq> closure(ball x (e/2))"
        by (simp add: closure_mono)
      also have "...  \<subseteq> ball x e"
        using \<open>e > 0\<close> by auto
      finally have "closure (S \<inter> ball x (e/2)) \<subseteq> ball x e" .
      moreover have"openin (top_of_set S) (S \<inter> ball x (e/2))" "S \<inter> ball x (e/2) \<noteq> {}"
        using \<open>0 < e\<close> \<open>x \<in> S\<close> by auto
      ultimately obtain Y where Y: "?\<Phi> 0 Y \<and> Y \<subseteq> S \<inter> ball x (e/2)"
            using * [of "S \<inter> ball x (e/2)" 0] by metis
      show thesis
      proof (rule exE [OF dependent_nat_choice])
        show "\<exists>x. ?\<Phi> 0 x"
          using Y by auto
        show "\<exists>Y. ?\<Phi> (Suc n) Y \<and> Y \<subseteq> X" if "?\<Phi> n X" for X n
          using that by (blast intro: *)
      qed (use that in metis)
    qed
    have "(\<Inter>n. S \<inter> closure (TF n)) \<noteq> {}"
    proof (rule compact_nest)
      show "\<And>n. compact (S \<inter> closure (TF n))"
        by (metis closed_closure subball bounded_subset_ballI compact_eq_bounded_closed closed_Int_compact [OF \<open>closed S\<close>])
      show "\<And>n. S \<inter> closure (TF n) \<noteq> {}"
        by (metis Int_absorb1 opeF \<open>closed S\<close> closure_eq_empty closure_minimal ne openin_imp_subset)
      show "\<And>m n. m \<le> n \<Longrightarrow> S \<inter> closure (TF n) \<subseteq> S \<inter> closure (TF m)"
        by (meson closure_mono decr dual_order.refl inf_mono lift_Suc_antimono_le)
    qed
    moreover have "(\<Inter>n. S \<inter> closure (TF n)) \<subseteq> {y \<in> \<Inter>\<G>. dist y x < e}"
    proof (clarsimp, intro conjI)
      fix y
      assume "y \<in> S" and y: "\<forall>n. y \<in> closure (TF n)"
      then show "\<forall>T\<in>\<G>. y \<in> T"
        by (metis Int_iff from_nat_into_surj [OF \<open>countable \<G>\<close>] subsetD subg)
      show "dist y x < e"
        by (metis y dist_commute mem_ball subball subsetCE)
    qed
    ultimately show "\<exists>y \<in> \<Inter>\<G>. dist y x < e"
      by auto
  qed
qed


subsection \<open>Continuity\<close>

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Structural rules for uniform continuity\<close>

lemma (in bounded_linear) uniformly_continuous_on[continuous_intros]:
  fixes g :: "_::metric_space \<Rightarrow> _"
  assumes "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f (g x))"
  using assms unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff diff[symmetric]
  by (auto intro: tendsto_zero)

lemma uniformly_continuous_on_dist[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. dist (f x) (g x))"
proof -
  {
    fix a b c d :: 'b
    have "\<bar>dist a b - dist c d\<bar> \<le> dist a c + dist b d"
      using dist_triangle2 [of a b c] dist_triangle2 [of b c d]
      using dist_triangle3 [of c d a] dist_triangle [of a d b]
      by arith
  } note le = this
  {
    fix x y
    assume f: "(\<lambda>n. dist (f (x n)) (f (y n))) \<longlonglongrightarrow> 0"
    assume g: "(\<lambda>n. dist (g (x n)) (g (y n))) \<longlonglongrightarrow> 0"
    have "(\<lambda>n. \<bar>dist (f (x n)) (g (x n)) - dist (f (y n)) (g (y n))\<bar>) \<longlonglongrightarrow> 0"
      by (rule Lim_transform_bound [OF _ tendsto_add_zero [OF f g]],
        simp add: le)
  }
  then show ?thesis
    using assms unfolding uniformly_continuous_on_sequentially
    unfolding dist_real_def by simp
qed

lemma uniformly_continuous_on_cmul_right [continuous_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. f x * c)"
  using bounded_linear.uniformly_continuous_on[OF bounded_linear_mult_left] .

lemma uniformly_continuous_on_cmul_left[continuous_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "uniformly_continuous_on s f"
    shows "uniformly_continuous_on s (\<lambda>x. c * f x)"
by (metis assms bounded_linear.uniformly_continuous_on bounded_linear_mult_right)

lemma uniformly_continuous_on_norm[continuous_intros]:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. norm (f x))"
  unfolding norm_conv_dist using assms
  by (intro uniformly_continuous_on_dist uniformly_continuous_on_const)

lemma uniformly_continuous_on_cmul[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. c *\<^sub>R f(x))"
  using bounded_linear_scaleR_right assms
  by (rule bounded_linear.uniformly_continuous_on)

lemma dist_minus:
  fixes x y :: "'a::real_normed_vector"
  shows "dist (- x) (- y) = dist x y"
  unfolding dist_norm minus_diff_minus norm_minus_cancel ..

lemma uniformly_continuous_on_minus[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. - f x)"
  unfolding uniformly_continuous_on_def dist_minus .

lemma uniformly_continuous_on_add[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x + g x)"
  using assms
  unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff add_diff_add
  by (auto intro: tendsto_add_zero)

lemma uniformly_continuous_on_diff[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x - g x)"
  using assms uniformly_continuous_on_add [of s f "- g"]
    by (simp add: fun_Compl_def uniformly_continuous_on_minus)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetic Preserves Topological Properties\<close>

lemma open_scaling[intro]:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
    and "open s"
  shows "open((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  {
    fix x
    assume "x \<in> s"
    then obtain e where "e>0"
      and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> s" using assms(2)[unfolded open_dist, THEN bspec[where x=x]]
      by auto
    have "e * \<bar>c\<bar> > 0"
      using assms(1)[unfolded zero_less_abs_iff[symmetric]] \<open>e>0\<close> by auto
    moreover
    {
      fix y
      assume "dist y (c *\<^sub>R x) < e * \<bar>c\<bar>"
      then have "norm (c *\<^sub>R ((1 / c) *\<^sub>R y - x)) < e * norm c"
        by (simp add: \<open>c \<noteq> 0\<close> dist_norm scale_right_diff_distrib)
      then have "norm ((1 / c) *\<^sub>R y - x) < e"
        by (simp add: \<open>c \<noteq> 0\<close>)
      then have "y \<in> (*\<^sub>R) c ` s"
        using rev_image_eqI[of "(1 / c) *\<^sub>R y" s y "(*\<^sub>R) c"]
        by (simp add: \<open>c \<noteq> 0\<close> dist_norm e)
    }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' (c *\<^sub>R x) < e \<longrightarrow> x' \<in> (*\<^sub>R) c ` s"
      by (rule_tac x="e * \<bar>c\<bar>" in exI, auto)
  }
  then show ?thesis unfolding open_dist by auto
qed

lemma minus_image_eq_vimage:
  fixes A :: "'a::ab_group_add set"
  shows "(\<lambda>x. - x) ` A = (\<lambda>x. - x) -` A"
  by (auto intro!: image_eqI [where f="\<lambda>x. - x"])

lemma open_negations:
  fixes S :: "'a::real_normed_vector set"
  shows "open S \<Longrightarrow> open ((\<lambda>x. - x) ` S)"
  using open_scaling [of "- 1" S] by simp

lemma open_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open((\<lambda>x. a + x) ` S)"
proof -
  {
    fix x
    have "continuous (at x) (\<lambda>x. x - a)"
      by (intro continuous_diff continuous_ident continuous_const)
  }
  moreover have "{x. x - a \<in> S} = (+) a ` S"
    by force
  ultimately show ?thesis
    by (metis assms continuous_open_vimage vimage_def)
qed

lemma open_translation_subtract:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open ((\<lambda>x. x - a) ` S)" 
  using assms open_translation [of S "- a"] by (simp cong: image_cong_simp)

lemma open_neg_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open((\<lambda>x. a - x) ` S)"
  using open_translation[OF open_negations[OF assms], of a]
  by (auto simp: image_image)

lemma open_affinity:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"  "c \<noteq> 0"
  shows "open ((\<lambda>x. a + c *\<^sub>R x) ` S)"
proof -
  have *: "(\<lambda>x. a + c *\<^sub>R x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. c *\<^sub>R x)"
    unfolding o_def ..
  have "(+) a ` (*\<^sub>R) c ` S = ((+) a \<circ> (*\<^sub>R) c) ` S"
    by auto
  then show ?thesis
    using assms open_translation[of "(*\<^sub>R) c ` S" a]
    unfolding *
    by auto
qed

lemma interior_translation:
  "interior ((+) a ` S) = (+) a ` (interior S)" for S :: "'a::real_normed_vector set"
proof (rule set_eqI, rule)
  fix x
  assume "x \<in> interior ((+) a ` S)"
  then obtain e where "e > 0" and e: "ball x e \<subseteq> (+) a ` S"
    unfolding mem_interior by auto
  then have "ball (x - a) e \<subseteq> S"
    unfolding subset_eq Ball_def mem_ball dist_norm
    by (auto simp: diff_diff_eq)
  then show "x \<in> (+) a ` interior S"
    unfolding image_iff
    by (metis \<open>0 < e\<close> add.commute diff_add_cancel mem_interior)
next
  fix x
  assume "x \<in> (+) a ` interior S"
  then obtain y e where "e > 0" and e: "ball y e \<subseteq> S" and y: "x = a + y"
    unfolding image_iff Bex_def mem_interior by auto
  {
    fix z
    have *: "a + y - z = y + a - z" by auto
    assume "z \<in> ball x e"
    then have "z - a \<in> S"
      using e[unfolded subset_eq, THEN bspec[where x="z - a"]]
      unfolding mem_ball dist_norm y group_add_class.diff_diff_eq2 *
      by auto
    then have "z \<in> (+) a ` S"
      unfolding image_iff by (auto intro!: bexI[where x="z - a"])
  }
  then have "ball x e \<subseteq> (+) a ` S"
    unfolding subset_eq by auto
  then show "x \<in> interior ((+) a ` S)"
    unfolding mem_interior using \<open>e > 0\<close> by auto
qed

lemma interior_translation_subtract:
  "interior ((\<lambda>x. x - a) ` S) = (\<lambda>x. x - a) ` interior S" for S :: "'a::real_normed_vector set"
  using interior_translation [of "- a"] by (simp cong: image_cong_simp)


lemma compact_scaling:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  let ?f = "\<lambda>x. scaleR c x"
  have *: "bounded_linear ?f" by (rule bounded_linear_scaleR_right)
  show ?thesis
    using compact_continuous_image[of s ?f] continuous_at_imp_continuous_on[of s ?f]
    using linear_continuous_at[OF *] assms
    by auto
qed

lemma compact_negations:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. - x) ` s)"
  using compact_scaling [OF assms, of "- 1"] by auto

lemma compact_sums:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"
    and "compact t"
  shows "compact {x + y | x y. x \<in> s \<and> y \<in> t}"
proof -
  have *: "{x + y | x y. x \<in> s \<and> y \<in> t} = (\<lambda>z. fst z + snd z) ` (s \<times> t)"
    by (fastforce simp: image_iff)
  have "continuous_on (s \<times> t) (\<lambda>z. fst z + snd z)"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  then show ?thesis
    unfolding * using compact_continuous_image compact_Times [OF assms] by auto
qed

lemma compact_differences:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"
    and "compact t"
  shows "compact {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x - y | x y. x\<in>s \<and> y \<in> t} = {x + y | x y. x \<in> s \<and> y \<in> (uminus ` t)}"
    using diff_conv_add_uminus by force
  then show ?thesis
    using compact_sums[OF assms(1) compact_negations[OF assms(2)]] by auto
qed

lemma compact_sums':
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S" and "compact T"
  shows "compact (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  have "(\<Union>x\<in>S. \<Union>y\<in>T. {x + y}) = {x + y |x y. x \<in> S \<and> y \<in> T}"
    by blast
  then show ?thesis
    using compact_sums [OF assms] by simp
qed

lemma compact_differences':
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S" and "compact T"
  shows "compact (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in>S. \<Union>y\<in>T. {x - y}) = {x - y |x y. x \<in> S \<and> y \<in> T}"
    by blast
  then show ?thesis
    using compact_differences [OF assms] by simp
qed

lemma compact_translation:
  "compact ((+) a ` s)" if "compact s" for s :: "'a::real_normed_vector set"
proof -
  have "{x + y |x y. x \<in> s \<and> y \<in> {a}} = (\<lambda>x. a + x) ` s"
    by auto
  then show ?thesis
    using compact_sums [OF that compact_sing [of a]] by auto
qed

lemma compact_translation_subtract:
  "compact ((\<lambda>x. x - a) ` s)" if "compact s" for s :: "'a::real_normed_vector set"
  using that compact_translation [of s "- a"] by (simp cong: image_cong_simp)

lemma compact_affinity:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have "(+) a ` (*\<^sub>R) c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s"
    by auto
  then show ?thesis
    using compact_translation[OF compact_scaling[OF assms], of a c] by auto
qed

lemma closed_scaling:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closed ((\<lambda>x. c *\<^sub>R x) ` S)"
proof (cases "c = 0")
  case True then show ?thesis
    by (auto simp: image_constant_conv)
next
  case False
  from assms have "closed ((\<lambda>x. inverse c *\<^sub>R x) -` S)"
    by (simp add: continuous_closed_vimage)
  also have "(\<lambda>x. inverse c *\<^sub>R x) -` S = (\<lambda>x. c *\<^sub>R x) ` S"
    using \<open>c \<noteq> 0\<close> by (auto elim: image_eqI [rotated])
  finally show ?thesis .
qed

lemma closed_negations:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closed ((\<lambda>x. -x) ` S)"
  using closed_scaling[OF assms, of "- 1"] by simp

lemma compact_closed_sums:
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S" and "closed T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  let ?S = "{x + y |x y. x \<in> S \<and> y \<in> T}"
  {
    fix x l
    assume as: "\<forall>n. x n \<in> ?S"  "(x \<longlongrightarrow> l) sequentially"
    from as(1) obtain f where f: "\<forall>n. x n = fst (f n) + snd (f n)"  "\<forall>n. fst (f n) \<in> S"  "\<forall>n. snd (f n) \<in> T"
      using choice[of "\<lambda>n y. x n = (fst y) + (snd y) \<and> fst y \<in> S \<and> snd y \<in> T"] by auto
    obtain l' r where "l'\<in>S" and r: "strict_mono r" and lr: "(((\<lambda>n. fst (f n)) \<circ> r) \<longlongrightarrow> l') sequentially"
      using assms(1)[unfolded compact_def, THEN spec[where x="\<lambda> n. fst (f n)"]] using f(2) by auto
    have "((\<lambda>n. snd (f (r n))) \<longlongrightarrow> l - l') sequentially"
      using tendsto_diff[OF LIMSEQ_subseq_LIMSEQ[OF as(2) r] lr] and f(1)
      unfolding o_def
      by auto
    then have "l - l' \<in> T"
      using assms(2)[unfolded closed_sequential_limits,
        THEN spec[where x="\<lambda> n. snd (f (r n))"],
        THEN spec[where x="l - l'"]]
      using f(3)
      by auto
    then have "l \<in> ?S"
      using \<open>l' \<in> S\<close> by force
  }
  moreover have "?S = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by force
  ultimately show ?thesis
    unfolding closed_sequential_limits
    by (metis (no_types, lifting))
qed

lemma closed_compact_sums:
  fixes S T :: "'a::real_normed_vector set"
  assumes "closed S" "compact T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  have "(\<Union>x\<in> T. \<Union>y \<in> S. {x + y}) = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by auto
  then show ?thesis
    using compact_closed_sums[OF assms(2,1)] by simp
qed

lemma compact_closed_differences:
  fixes S T :: "'a::real_normed_vector set"
  assumes "compact S" "closed T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> uminus ` T. {x + y}) = (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
    by force
  then show ?thesis
    by (metis assms closed_negations compact_closed_sums)
qed

lemma closed_compact_differences:
  fixes S T :: "'a::real_normed_vector set"
  assumes "closed S" "compact T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> uminus ` T. {x + y}) = {x - y |x y. x \<in> S \<and> y \<in> T}"
    by auto
 then show ?thesis
  using closed_compact_sums[OF assms(1) compact_negations[OF assms(2)]] by simp
qed

lemma closed_translation:
  "closed ((+) a ` S)" if "closed S" for a :: "'a::real_normed_vector"
proof -
  have "(\<Union>x\<in> {a}. \<Union>y \<in> S. {x + y}) = ((+) a ` S)" by auto
  then show ?thesis
    using compact_closed_sums [OF compact_sing [of a] that] by auto
qed

lemma closed_translation_subtract:
  "closed ((\<lambda>x. x - a) ` S)" if "closed S" for a :: "'a::real_normed_vector"
  using that closed_translation [of S "- a"] by (simp cong: image_cong_simp)

lemma closure_translation:
  "closure ((+) a ` s) = (+) a ` closure s" for a :: "'a::real_normed_vector"
proof -
  have *: "(+) a ` (- s) = - (+) a ` s"
    by (auto intro!: image_eqI [where x = "x - a" for x])
  show ?thesis
    using interior_translation [of a "- s", symmetric]
    by (simp add: closure_interior translation_Compl *)
qed

lemma closure_translation_subtract:
  "closure ((\<lambda>x. x - a) ` s) = (\<lambda>x. x - a) ` closure s" for a :: "'a::real_normed_vector"
  using closure_translation [of "- a" s] by (simp cong: image_cong_simp)

lemma frontier_translation:
  "frontier ((+) a ` s) = (+) a ` frontier s" for a :: "'a::real_normed_vector"
  by (auto simp add: frontier_def translation_diff interior_translation closure_translation)

lemma frontier_translation_subtract:
  "frontier ((+) a ` s) = (+) a ` frontier s" for a :: "'a::real_normed_vector"
  by (auto simp add: frontier_def translation_diff interior_translation closure_translation)

lemma sphere_translation:
  "sphere (a + c) r = (+) a ` sphere c r" for a :: "'n::real_normed_vector"
  by (auto simp: dist_norm algebra_simps intro!: image_eqI [where x = "x - a" for x])

lemma sphere_translation_subtract:
  "sphere (c - a) r = (\<lambda>x. x - a) ` sphere c r" for a :: "'n::real_normed_vector"
  using sphere_translation [of "- a" c] by (simp cong: image_cong_simp)

lemma cball_translation:
  "cball (a + c) r = (+) a ` cball c r" for a :: "'n::real_normed_vector"
  by (auto simp: dist_norm algebra_simps intro!: image_eqI [where x = "x - a" for x])

lemma cball_translation_subtract:
  "cball (c - a) r = (\<lambda>x. x - a) ` cball c r" for a :: "'n::real_normed_vector"
  using cball_translation [of "- a" c] by (simp cong: image_cong_simp)

lemma ball_translation:
  "ball (a + c) r = (+) a ` ball c r" for a :: "'n::real_normed_vector"
  by (auto simp: dist_norm algebra_simps intro!: image_eqI [where x = "x - a" for x])

lemma ball_translation_subtract:
  "ball (c - a) r = (\<lambda>x. x - a) ` ball c r" for a :: "'n::real_normed_vector"
  using ball_translation [of "- a" c] by (simp cong: image_cong_simp)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Homeomorphisms\<close>

lemma homeomorphic_scaling:
  fixes S :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
  shows "S homeomorphic ((\<lambda>x. c *\<^sub>R x) ` S)"
  unfolding homeomorphic_minimal
  apply (rule_tac x="\<lambda>x. c *\<^sub>R x" in exI)
  apply (rule_tac x="\<lambda>x. (1 / c) *\<^sub>R x" in exI)
  using assms by (auto simp: continuous_intros)

lemma homeomorphic_translation:
  fixes S :: "'a::real_normed_vector set"
  shows "S homeomorphic ((\<lambda>x. a + x) ` S)"
  unfolding homeomorphic_minimal
  apply (rule_tac x="\<lambda>x. a + x" in exI)
  apply (rule_tac x="\<lambda>x. -a + x" in exI)
  by (auto simp: continuous_intros)

lemma homeomorphic_affinity:
  fixes S :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
  shows "S homeomorphic ((\<lambda>x. a + c *\<^sub>R x) ` S)"
proof -
  have *: "(+) a ` (*\<^sub>R) c ` S = (\<lambda>x. a + c *\<^sub>R x) ` S" by auto
  show ?thesis
    by (metis "*" assms homeomorphic_scaling homeomorphic_trans homeomorphic_translation)
qed

lemma homeomorphic_balls:
  fixes a b ::"'a::real_normed_vector"
  assumes "0 < d"  "0 < e"
  shows "(ball a d) homeomorphic  (ball b e)" (is ?th)
    and "(cball a d) homeomorphic (cball b e)" (is ?cth)
proof -
  show ?th unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    by (auto intro!: continuous_intros simp: dist_commute dist_norm pos_divide_less_eq)
  show ?cth unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    by (auto intro!: continuous_intros simp: dist_commute dist_norm pos_divide_le_eq)
qed

lemma homeomorphic_spheres:
  fixes a b ::"'a::real_normed_vector"
  assumes "0 < d"  "0 < e"
  shows "(sphere a d) homeomorphic (sphere b e)"
unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    by (auto intro!: continuous_intros simp: dist_commute dist_norm pos_divide_less_eq)

lemma homeomorphic_ball01_UNIV:
  "ball (0::'a::real_normed_vector) 1 homeomorphic (UNIV:: 'a set)"
  (is "?B homeomorphic ?U")
proof
  have "x \<in> (\<lambda>z. z /\<^sub>R (1 - norm z)) ` ball 0 1" for x::'a
    apply (rule_tac x="x /\<^sub>R (1 + norm x)" in image_eqI)
     apply (auto simp: field_split_simps)
    using norm_ge_zero [of x] apply linarith+
    done
  then show "(\<lambda>z::'a. z /\<^sub>R (1 - norm z)) ` ?B = ?U"
    by blast
  have "x \<in> range (\<lambda>z. (1 / (1 + norm z)) *\<^sub>R z)" if "norm x < 1" for x::'a
    using that
    by (rule_tac x="x /\<^sub>R (1 - norm x)" in image_eqI) (auto simp: field_split_simps)
  then show "(\<lambda>z::'a. z /\<^sub>R (1 + norm z)) ` ?U = ?B"
    by (force simp: field_split_simps dest: add_less_zeroD)
  show "continuous_on (ball 0 1) (\<lambda>z. z /\<^sub>R (1 - norm z))"
    by (rule continuous_intros | force)+
  have 0: "\<And>z. 1 + norm z \<noteq> 0"
    by (metis (no_types) le_add_same_cancel1 norm_ge_zero not_one_le_zero)
  then show "continuous_on UNIV (\<lambda>z. z /\<^sub>R (1 + norm z))"
    by (auto intro!: continuous_intros)
  show "\<And>x. x \<in> ball 0 1 \<Longrightarrow>
         x /\<^sub>R (1 - norm x) /\<^sub>R (1 + norm (x /\<^sub>R (1 - norm x))) = x"
    by (auto simp: field_split_simps)
  show "\<And>y. y /\<^sub>R (1 + norm y) /\<^sub>R (1 - norm (y /\<^sub>R (1 + norm y))) = y"
    using 0 by (auto simp: field_split_simps)
qed

proposition homeomorphic_ball_UNIV:
  fixes a ::"'a::real_normed_vector"
  assumes "0 < r" shows "ball a r homeomorphic (UNIV:: 'a set)"
  using assms homeomorphic_ball01_UNIV homeomorphic_balls(1) homeomorphic_trans zero_less_one by blast


subsection\<^marker>\<open>tag unimportant\<close> \<open>Discrete\<close>

lemma finite_implies_discrete:
  fixes S :: "'a::topological_space set"
  assumes "finite (f ` S)"
  shows "(\<forall>x \<in> S. \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x))"
proof -
  have "\<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)" if "x \<in> S" for x
  proof (cases "f ` S - {f x} = {}")
    case True
    with zero_less_numeral show ?thesis
      by (fastforce simp add: Set.image_subset_iff cong: conj_cong)
  next
    case False
    then obtain z where "z \<in> S" "f z \<noteq> f x"
      by blast
    moreover have finn: "finite {norm (z - f x) |z. z \<in> f ` S - {f x}}"
      using assms by simp
    ultimately have *: "0 < Inf{norm(z - f x) | z. z \<in> f ` S - {f x}}"
      by (force intro: finite_imp_less_Inf)
    show ?thesis
      by (force intro!: * cInf_le_finite [OF finn])
  qed
  with assms show ?thesis
    by blast
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Completeness of "Isometry" (up to constant bounds)\<close>

lemma cauchy_isometric:\<comment> \<open>TODO: rename lemma to \<open>Cauchy_isometric\<close>\<close>
  assumes e: "e > 0"
    and s: "subspace s"
    and f: "bounded_linear f"
    and normf: "\<forall>x\<in>s. norm (f x) \<ge> e * norm x"
    and xs: "\<forall>n. x n \<in> s"
    and cf: "Cauchy (f \<circ> x)"
  shows "Cauchy x"
proof -
  interpret f: bounded_linear f by fact
  have "\<exists>N. \<forall>n\<ge>N. norm (x n - x N) < d" if "d > 0" for d :: real
  proof -
    from that obtain N where N: "\<forall>n\<ge>N. norm (f (x n) - f (x N)) < e * d"
      using cf[unfolded Cauchy_def o_def dist_norm, THEN spec[where x="e*d"]] e
      by auto
    have "norm (x n - x N) < d" if "n \<ge> N" for n
    proof -
      have "e * norm (x n - x N) \<le> norm (f (x n - x N))"
        using subspace_diff[OF s, of "x n" "x N"]
        using xs[THEN spec[where x=N]] and xs[THEN spec[where x=n]]
        using normf[THEN bspec[where x="x n - x N"]]
        by auto
      also have "norm (f (x n - x N)) < e * d"
        using \<open>N \<le> n\<close> N unfolding f.diff[symmetric] by auto
      finally show ?thesis
        using \<open>e>0\<close> by simp
    qed
    then show ?thesis by auto
  qed
  then show ?thesis
    by (simp add: Cauchy_altdef2 dist_norm)
qed

lemma complete_isometric_image:
  assumes "0 < e"
    and s: "subspace s"
    and f: "bounded_linear f"
    and normf: "\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)"
    and cs: "complete s"
  shows "complete (f ` s)"
proof -
  have "\<exists>l\<in>f ` s. (g \<longlongrightarrow> l) sequentially"
    if as:"\<forall>n::nat. g n \<in> f ` s" and cfg:"Cauchy g" for g
  proof -
    from that obtain x where "\<forall>n. x n \<in> s \<and> g n = f (x n)"
      using choice[of "\<lambda> n xa. xa \<in> s \<and> g n = f xa"] by auto
    then have x: "\<forall>n. x n \<in> s" "\<forall>n. g n = f (x n)" by auto
    then have "f \<circ> x = g" by (simp add: fun_eq_iff)
    then obtain l where "l\<in>s" and l:"(x \<longlongrightarrow> l) sequentially"
      using cs[unfolded complete_def, THEN spec[where x=x]]
      using cauchy_isometric[OF \<open>0 < e\<close> s f normf] and cfg and x(1)
      by auto
    then show ?thesis
      using linear_continuous_at[OF f, unfolded continuous_at_sequentially, THEN spec[where x=x], of l]
      by (auto simp: \<open>f \<circ> x = g\<close>)
  qed
  then show ?thesis
    unfolding complete_def by auto
qed

subsection \<open>Connected Normed Spaces\<close>

lemma compact_components:
  fixes s :: "'a::heine_borel set"
  shows "\<lbrakk>compact s; c \<in> components s\<rbrakk> \<Longrightarrow> compact c"
by (meson bounded_subset closed_components in_components_subset compact_eq_bounded_closed)

lemma discrete_subset_disconnected:
  fixes S :: "'a::topological_space set"
  fixes t :: "'b::real_normed_vector set"
  assumes conf: "continuous_on S f"
      and no: "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
   shows "f ` S \<subseteq> {y. connected_component_set (f ` S) y = {y}}"
proof -
  { fix x assume x: "x \<in> S"
    then obtain e where "e>0" and ele: "\<And>y. \<lbrakk>y \<in> S; f y \<noteq> f x\<rbrakk> \<Longrightarrow> e \<le> norm (f y - f x)"
      using conf no [OF x] by auto
    then have e2: "0 \<le> e/2"
      by simp
    define F where "F \<equiv> connected_component_set (f ` S) (f x)"
    have False if "y \<in> S" and ccs: "f y \<in> F" and not: "f y \<noteq> f x" for y 
    proof -
      define C where "C \<equiv> cball (f x) (e/2)"
      define D where "D \<equiv> - ball (f x) e"
      have disj: "C \<inter> D = {}"
        unfolding C_def D_def using \<open>0 < e\<close> by fastforce
      moreover have FCD: "F \<subseteq> C \<union> D"
      proof -
        have "t \<in> C \<or> t \<in> D" if "t \<in> F" for t
        proof -
          obtain y where "y \<in> S" "t = f y"
            using F_def \<open>t \<in> F\<close> connected_component_in by blast
          then show ?thesis
            by (metis C_def ComplI D_def centre_in_cball dist_norm e2 ele mem_ball norm_minus_commute not_le)
        qed
        then show ?thesis
          by auto
      qed
      ultimately have "C \<inter> F = {} \<or> D \<inter> F = {}"
        using connected_closed [of "F"] \<open>e>0\<close> not
        unfolding C_def D_def
        by (metis Elementary_Metric_Spaces.open_ball F_def closed_cball connected_connected_component inf_bot_left open_closed)
      moreover have "C \<inter> F \<noteq> {}"
        unfolding disjoint_iff
        by (metis FCD ComplD image_eqI mem_Collect_eq subsetD x  D_def F_def Un_iff \<open>0 < e\<close> centre_in_ball connected_component_refl_eq)
      moreover have "D \<inter> F \<noteq> {}"
        unfolding disjoint_iff
        by (metis ComplI D_def ccs dist_norm ele mem_ball norm_minus_commute not not_le that(1))
      ultimately show ?thesis by metis
    qed
    moreover have "connected_component_set (f ` S) (f x) \<subseteq> f ` S"
      by (auto simp: connected_component_in)
    ultimately have "connected_component_set (f ` S) (f x) = {f x}"
      by (auto simp: x F_def)
  }
  with assms show ?thesis
    by blast
qed

lemma continuous_disconnected_range_constant_eq:
      "(connected S \<longleftrightarrow>
           (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
            \<forall>t. continuous_on S f \<and> f ` S \<subseteq> t \<and> (\<forall>y \<in> t. connected_component_set t y = {y})
            \<longrightarrow> f constant_on S))" (is ?thesis1)
  and continuous_discrete_range_constant_eq:
      "(connected S \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on S f \<and>
          (\<forall>x \<in> S. \<exists>e. 0 < e \<and> (\<forall>y. y \<in> S \<and> (f y \<noteq> f x) \<longrightarrow> e \<le> norm(f y - f x)))
          \<longrightarrow> f constant_on S))" (is ?thesis2)
  and continuous_finite_range_constant_eq:
      "(connected S \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on S f \<and> finite (f ` S)
          \<longrightarrow> f constant_on S))" (is ?thesis3)
proof -
  have *: "\<And>s t u v. \<lbrakk>s \<Longrightarrow> t; t \<Longrightarrow> u; u \<Longrightarrow> v; v \<Longrightarrow> s\<rbrakk>
    \<Longrightarrow> (s \<longleftrightarrow> t) \<and> (s \<longleftrightarrow> u) \<and> (s \<longleftrightarrow> v)"
    by blast
  have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
    apply (rule *)
    using continuous_disconnected_range_constant apply metis
    apply clarify
    apply (frule discrete_subset_disconnected; blast)
    apply (blast dest: finite_implies_discrete)
    apply (blast intro!: finite_range_constant_imp_connected)
    done
  then show ?thesis1 ?thesis2 ?thesis3
    by blast+
qed

lemma continuous_discrete_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes S: "connected S"
      and "continuous_on S f"
      and "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
    shows "f constant_on S"
  using continuous_discrete_range_constant_eq [THEN iffD1, OF S] assms by blast

lemma continuous_finite_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes "connected S"
      and "continuous_on S f"
      and "finite (f ` S)"
    shows "f constant_on S"
  using assms continuous_finite_range_constant_eq  by blast

end
