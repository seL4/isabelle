(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary Normed Vector Spaces\<close>

theory Elementary_Normed_Spaces
  imports
  "HOL-Library.FuncSet"
  Elementary_Metric_Spaces
begin

subsection%unimportant \<open>Various Lemmas Combining Imports\<close>

lemma countable_PiE:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> countable (F i)) \<Longrightarrow> countable (Pi\<^sub>E I F)"
  by (induct I arbitrary: F rule: finite_induct) (auto simp: PiE_insert_eq)


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


subsection \<open>Support\<close>

definition (in monoid_add) support_on :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b set"
  where "support_on s f = {x\<in>s. f x \<noteq> 0}"

lemma in_support_on: "x \<in> support_on s f \<longleftrightarrow> x \<in> s \<and> f x \<noteq> 0"
  by (simp add: support_on_def)

lemma support_on_simps[simp]:
  "support_on {} f = {}"
  "support_on (insert x s) f =
    (if f x = 0 then support_on s f else insert x (support_on s f))"
  "support_on (s \<union> t) f = support_on s f \<union> support_on t f"
  "support_on (s \<inter> t) f = support_on s f \<inter> support_on t f"
  "support_on (s - t) f = support_on s f - support_on t f"
  "support_on (f ` s) g = f ` (support_on s (g \<circ> f))"
  unfolding support_on_def by auto

lemma support_on_cong:
  "(\<And>x. x \<in> s \<Longrightarrow> f x = 0 \<longleftrightarrow> g x = 0) \<Longrightarrow> support_on s f = support_on s g"
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
        apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI)
        using False apply (auto simp: le_diff_eq pos_le_divideRI)
        using diff_le_eq pos_le_divideR_eq by force
      show "\<lbrakk>\<not> 0 \<le> m; a \<le> b;  x \<in> {m *\<^sub>R b + c..m *\<^sub>R a + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI)
        apply (auto simp: diff_le_eq neg_le_divideR_eq)
        using diff_eq_diff_less_eq linordered_field_class.sign_simps(11) minus_diff_eq not_less scaleR_le_cancel_left_neg by fastforce
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
        then show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
        proof (cases "x = y")
          case True
          then have False
            using \<open>d \<le> dist x y\<close> \<open>d>0\<close> by auto
          then show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
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
            unfolding dist_norm
            apply simp
            unfolding norm_minus_cancel
            using \<open>d > 0\<close> \<open>x\<noteq>y\<close>[unfolded dist_nz] dist_commute[of x y]
            unfolding dist_norm
            apply auto
            done
          ultimately show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            apply (rule_tac x = "y - (d / (2*dist y x)) *\<^sub>R (y - x)" in bexI)
            apply auto
            done
        qed
      next
        case False
        then have "d > dist x y" by auto
        show "\<exists>x' \<in> ball x e. x' \<noteq> y \<and> dist x' y < d"
        proof (cases "x = y")
          case True
          obtain z where **: "z \<noteq> y" "dist z y < min e d"
            using perfect_choose_dist[of "min e d" y]
            using \<open>d > 0\<close> \<open>e>0\<close> by auto
          show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            unfolding \<open>x = y\<close>
            using \<open>z \<noteq> y\<close> **
            apply (rule_tac x=z in bexI)
            apply (auto simp: dist_commute)
            done
        next
          case False
          then show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            using \<open>d>0\<close> \<open>d > dist x y\<close> \<open>?rhs\<close>
            apply (rule_tac x=x in bexI, auto)
            done
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
  (* choose point between x and y, within distance r of y. *)
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
    unfolding z_def2 dist_norm
    apply (simp add: norm_minus_commute)
    apply (simp only: dist_norm [symmetric])
    apply (subgoal_tac "\<bar>1 - k\<bar> * dist x y < 1 * dist x y", simp)
    apply (rule mult_strict_right_mono)
    apply (simp add: k_def \<open>0 < r\<close> \<open>x \<noteq> y\<close>)
    apply (simp add: \<open>x \<noteq> y\<close>)
    done
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
  by (simp add: dist_norm)

lemma mem_cball_0 [simp]: "x \<in> cball 0 e \<longleftrightarrow> norm x \<le> e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma closure_ball [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "0 < e \<Longrightarrow> closure (ball x e) = cball x e"
  apply (rule equalityI)
  apply (rule closure_minimal)
  apply (rule ball_subset_cball)
  apply (rule closed_cball)
  apply (rule subsetI, rename_tac y)
  apply (simp add: le_less [where 'a=real])
  apply (erule disjE)
  apply (rule subsetD [OF closure_subset], simp)
  apply (simp add: closure_def, clarify)
  apply (rule closure_ball_lemma)
  apply simp
  done

lemma mem_sphere_0 [simp]: "x \<in> sphere 0 e \<longleftrightarrow> norm x = e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

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
apply (intro equalityI subsetI)
apply (force simp: dist_norm)
apply (rule_tac x="x-b" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma image_add_cball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "(+) b ` cball a r = cball (a+b) r"
apply (intro equalityI subsetI)
apply (force simp: dist_norm)
apply (rule_tac x="x-b" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done


subsection%unimportant \<open>Various Lemmas on Normed Algebras\<close>


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
  unfolding trivial_limit_def eventually_at_infinity
  apply clarsimp
  apply (subgoal_tac "\<exists>x::'a. x \<noteq> 0", clarify)
   apply (rule_tac x="scaleR (b / norm x) x" in exI, simp)
  apply (cut_tac islimpt_UNIV [of "0::'a", unfolded islimpt_def])
  apply (drule_tac x=UNIV in spec, simp)
  done

lemma at_within_ball_bot_iff:
  fixes x y :: "'a::{real_normed_vector,perfect_space}"
  shows "at x within ball y r = bot \<longleftrightarrow> (r=0 \<or> x \<notin> cball y r)"
  unfolding trivial_limit_within 
  apply (auto simp add:trivial_limit_within islimpt_ball )
  by (metis le_less_trans less_eq_real_def zero_le_dist)


subsection \<open>Limits\<close>

proposition Lim_at_infinity: "(f \<longlongrightarrow> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x. norm x \<ge> b \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_infinity)

corollary Lim_at_infinityI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>B. \<forall>x. norm x \<ge> B \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) at_infinity"
  apply (simp add: Lim_at_infinity, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

lemma Lim_transform_within_set_eq:
  fixes a l :: "'a::real_normed_vector"
  shows "eventually (\<lambda>x. x \<in> s \<longleftrightarrow> x \<in> t) (at a)
         \<Longrightarrow> ((f \<longlongrightarrow> l) (at a within s) \<longleftrightarrow> (f \<longlongrightarrow> l) (at a within t))"
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
  have *: "((\<lambda>x. norm (f x) * B) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_left_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (f x) * norm (g x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_left_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_mult_left_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes g: "eventually (\<lambda>x. norm(g x) \<le> B) F" and f: "(f \<longlongrightarrow> 0) F"
    shows "((\<lambda>z. g z * f z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. B * norm (f x)) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_right_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (g x) * norm (f x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_right_mono)
    done
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
  show "\<forall>\<^sub>F x in net. dist (f x *\<^sub>R g x) 0 < \<epsilon>"
    apply (rule eventually_mono [OF eventually_conj [OF tendstoD [OF f B] gB] ])
    apply (auto simp: \<open>0 < \<epsilon>\<close> divide_simps * split: if_split_asm)
    done
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


subsection%unimportant \<open>Limit Point of Filter\<close>

lemma netlimit_at_vector:
  fixes a :: "'a::real_normed_vector"
  shows "netlimit (at a) = a"
proof (cases "\<exists>x. x \<noteq> a")
  case True then obtain x where x: "x \<noteq> a" ..
  have "\<not> trivial_limit (at a)"
    unfolding trivial_limit_def eventually_at dist_norm
    apply clarsimp
    apply (rule_tac x="a + scaleR (d / 2) (sgn (x - a))" in exI)
    apply (simp add: norm_sgn sgn_zero_iff x)
    done
  then show ?thesis
    by (rule netlimit_within [of a UNIV])
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
  apply (simp add: bounded_iff)
  apply (subgoal_tac "\<And>x (y::real). 0 < 1 + \<bar>y\<bar> \<and> (x \<le> y \<longrightarrow> x \<le> 1 + \<bar>y\<bar>)")
  apply metis
  apply arith
  done

lemma bounded_pos_less: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x < b)"
  apply (simp add: bounded_pos)
  apply (safe; rule_tac x="b+1" in exI; force)
  done

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
  apply (rule bounded_linear_image, assumption)
  apply (rule bounded_linear_scaleR_right)
  done

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
  using bounded_Un [of S "-S"]  by (simp add: sup_compl_top)

subsection%unimportant\<open>Relations among convergence and absolute convergence for power series\<close>

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
  then have *: "summable (\<lambda>n. norm (a n) * norm w ^ n)"
    by (rule_tac M=M in Abel_lemma) (auto simp: norm_mult norm_power intro: no)
  show ?thesis
    apply (rule series_comparison_complex [of "(\<lambda>n. of_real(norm(a n) * norm w ^ n))"])
    apply (simp only: summable_complex_of_real *)
    apply (auto simp: norm_mult norm_power)
    done
qed


subsection \<open>Normed spaces with the Heine-Borel property\<close>

lemma not_compact_UNIV[simp]:
  fixes s :: "'a::{real_normed_vector,perfect_space,heine_borel} set"
  shows "\<not> compact (UNIV::'a set)"
    by (simp add: compact_eq_bounded_closed)

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
  shows "\<Inter>range F \<noteq> {}"
proof -
  have *: "\<And>S T. S \<in> range F \<and> T \<in> range F \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    by (metis mono image_iff le_cases)
  show ?thesis
    apply (rule compact_chain [OF _ _ *])
    using F apply (blast intro: dest: *)+
    done
qed

text\<open>The Baire property of dense sets\<close>
theorem Baire:
  fixes S::"'a::{real_normed_vector,heine_borel} set"
  assumes "closed S" "countable \<G>"
      and ope: "\<And>T. T \<in> \<G> \<Longrightarrow> openin (subtopology euclidean S) T \<and> S \<subseteq> closure T"
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
    obtain TF where opeF: "\<And>n. openin (subtopology euclidean S) (TF n)"
               and ne: "\<And>n. TF n \<noteq> {}"
               and subg: "\<And>n. S \<inter> closure(TF n) \<subseteq> ?g n"
               and subball: "\<And>n. closure(TF n) \<subseteq> ball x e"
               and decr: "\<And>n. TF(Suc n) \<subseteq> TF n"
    proof -
      have *: "\<exists>Y. (openin (subtopology euclidean S) Y \<and> Y \<noteq> {} \<and>
                   S \<inter> closure Y \<subseteq> ?g n \<and> closure Y \<subseteq> ball x e) \<and> Y \<subseteq> U"
        if opeU: "openin (subtopology euclidean S) U" and "U \<noteq> {}" and cloU: "closure U \<subseteq> ball x e" for U n
      proof -
        obtain T where T: "open T" "U = T \<inter> S"
          using \<open>openin (subtopology euclidean S) U\<close> by (auto simp: openin_subtopology)
        with \<open>U \<noteq> {}\<close> have "T \<inter> closure (?g n) \<noteq> {}"
          using gin ope by fastforce
        then have "T \<inter> ?g n \<noteq> {}"
          using \<open>open T\<close> open_Int_closure_eq_empty by blast
        then obtain y where "y \<in> U" "y \<in> ?g n"
          using T ope [of "?g n", OF gin] by (blast dest:  openin_imp_subset)
        moreover have "openin (subtopology euclidean S) (U \<inter> ?g n)"
          using gin ope opeU by blast
        ultimately obtain d where U: "U \<inter> ?g n \<subseteq> S" and "d > 0" and d: "ball y d \<inter> S \<subseteq> U \<inter> ?g n"
          by (force simp: openin_contains_ball)
        show ?thesis
        proof (intro exI conjI)
          show "openin (subtopology euclidean S) (S \<inter> ball y (d/2))"
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
      let ?\<Phi> = "\<lambda>n X. openin (subtopology euclidean S) X \<and> X \<noteq> {} \<and>
                      S \<inter> closure X \<subseteq> ?g n \<and> closure X \<subseteq> ball x e"
      have "closure (S \<inter> ball x (e / 2)) \<subseteq> closure(ball x (e/2))"
        by (simp add: closure_mono)
      also have "...  \<subseteq> ball x e"
        using \<open>e > 0\<close> by auto
      finally have "closure (S \<inter> ball x (e / 2)) \<subseteq> ball x e" .
      moreover have"openin (subtopology euclidean S) (S \<inter> ball x (e / 2))" "S \<inter> ball x (e / 2) \<noteq> {}"
        using \<open>0 < e\<close> \<open>x \<in> S\<close> by auto
      ultimately obtain Y where Y: "?\<Phi> 0 Y \<and> Y \<subseteq> S \<inter> ball x (e / 2)"
            using * [of "S \<inter> ball x (e/2)" 0] by metis
      show thesis
      proof (rule exE [OF dependent_nat_choice [of ?\<Phi> "\<lambda>n X Y. Y \<subseteq> X"]])
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
        by (metis Int_iff from_nat_into_surj [OF \<open>countable \<G>\<close>] set_mp subg)
      show "dist y x < e"
        by (metis y dist_commute mem_ball subball subsetCE)
    qed
    ultimately show "\<exists>y \<in> \<Inter>\<G>. dist y x < e"
      by auto
  qed
qed


subsection \<open>Continuity\<close>

subsubsection%unimportant \<open>Structural rules for uniform continuity\<close>

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


subsection%unimportant \<open>Topological properties of linear functions\<close>

lemma linear_lim_0:
  assumes "bounded_linear f"
  shows "(f \<longlongrightarrow> 0) (at (0))"
proof -
  interpret f: bounded_linear f by fact
  have "(f \<longlongrightarrow> f 0) (at 0)"
    using tendsto_ident_at by (rule f.tendsto)
  then show ?thesis unfolding f.zero .
qed

lemma linear_continuous_at:
  assumes "bounded_linear f"
  shows "continuous (at a) f"
  unfolding continuous_at using assms
  apply (rule bounded_linear.tendsto)
  apply (rule tendsto_ident_at)
  done

lemma linear_continuous_within:
  "bounded_linear f \<Longrightarrow> continuous (at x within s) f"
  using continuous_at_imp_continuous_within[of x f s] using linear_continuous_at[of f] by auto

lemma linear_continuous_on:
  "bounded_linear f \<Longrightarrow> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

end