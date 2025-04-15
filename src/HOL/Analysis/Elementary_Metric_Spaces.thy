(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
    Author:     Ata Keskin, TU Muenchen
*)

chapter \<open>Elementary Metric Spaces\<close>

theory Elementary_Metric_Spaces
  imports
    Abstract_Topology_2
    Metric_Arith
begin

section \<open>Open and closed balls\<close>

definition\<^marker>\<open>tag important\<close> ball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "ball x e = {y. dist x y < e}"

definition\<^marker>\<open>tag important\<close> cball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "cball x e = {y. dist x y \<le> e}"

definition\<^marker>\<open>tag important\<close> sphere :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "sphere x e = {y. dist x y = e}"

lemma mem_ball [simp, metric_unfold]: "y \<in> ball x e \<longleftrightarrow> dist x y < e"
  by (simp add: ball_def)

lemma mem_cball [simp, metric_unfold]: "y \<in> cball x e \<longleftrightarrow> dist x y \<le> e"
  by (simp add: cball_def)

lemma mem_sphere [simp]: "y \<in> sphere x e \<longleftrightarrow> dist x y = e"
  by (simp add: sphere_def)

lemma ball_trivial [simp]: "ball x 0 = {}"
  by auto

lemma cball_trivial [simp]: "cball x 0 = {x}"
  by auto

lemma sphere_trivial [simp]: "sphere x 0 = {x}"
  by auto

lemma disjoint_ballI: "dist x y \<ge> r+s \<Longrightarrow> ball x r \<inter> ball y s = {}"
  using dist_triangle_less_add not_le by fastforce

lemma disjoint_cballI: "dist x y > r + s \<Longrightarrow> cball x r \<inter> cball y s = {}"
  by (metis add_mono disjoint_iff_not_equal dist_triangle2 dual_order.trans leD mem_cball)

lemma sphere_empty [simp]: "r < 0 \<Longrightarrow> sphere a r = {}"
  for a :: "'a::metric_space"
  by auto

lemma centre_in_ball [simp]: "x \<in> ball x e \<longleftrightarrow> 0 < e"
  by simp

lemma centre_in_cball [simp]: "x \<in> cball x e \<longleftrightarrow> 0 \<le> e"
  by simp

lemma ball_subset_cball [simp, intro]: "ball x e \<subseteq> cball x e"
  by (simp add: subset_eq)

lemma mem_ball_imp_mem_cball: "x \<in> ball y e \<Longrightarrow> x \<in> cball y e"
  by auto

lemma sphere_cball [simp,intro]: "sphere z r \<subseteq> cball z r"
  by force

lemma cball_diff_sphere: "cball a r - sphere a r = ball a r"
  by auto

lemma subset_ball[intro]: "d \<le> e \<Longrightarrow> ball x d \<subseteq> ball x e"
  by auto

lemma subset_cball[intro]: "d \<le> e \<Longrightarrow> cball x d \<subseteq> cball x e"
  by auto

lemma mem_ball_leI: "x \<in> ball y e \<Longrightarrow> e \<le> f \<Longrightarrow> x \<in> ball y f"
  by auto

lemma mem_cball_leI: "x \<in> cball y e \<Longrightarrow> e \<le> f \<Longrightarrow> x \<in> cball y f"
  by auto

lemma cball_trans: "y \<in> cball z b \<Longrightarrow> x \<in> cball y a \<Longrightarrow> x \<in> cball z (b + a)"
  by metric

lemma ball_max_Un: "ball a (max r s) = ball a r \<union> ball a s"
  by auto

lemma ball_min_Int: "ball a (min r s) = ball a r \<inter> ball a s"
  by auto

lemma cball_max_Un: "cball a (max r s) = cball a r \<union> cball a s"
  by auto

lemma cball_min_Int: "cball a (min r s) = cball a r \<inter> cball a s"
  by auto

lemma cball_diff_eq_sphere: "cball a r - ball a r =  sphere a r"
  by auto

lemma open_ball [intro, simp]: "open (ball x e)"
proof -
  have "open (dist x -` {..<e})"
    by (intro open_vimage open_lessThan continuous_intros)
  also have "dist x -` {..<e} = ball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_ball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. ball x e \<subseteq> S)"
  by (simp add: open_dist subset_eq Ball_def dist_commute)

lemma openI [intro?]: "(\<And>x. x\<in>S \<Longrightarrow> \<exists>e>0. ball x e \<subseteq> S) \<Longrightarrow> open S"
  by (auto simp: open_contains_ball)

lemma openE[elim?]:
  assumes "open S" "x\<in>S"
  obtains e where "e>0" "ball x e \<subseteq> S"
  using assms unfolding open_contains_ball by auto

lemma open_contains_ball_eq: "open S \<Longrightarrow> x\<in>S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  by (metis open_contains_ball subset_eq centre_in_ball)

lemma ball_eq_empty[simp]: "ball x e = {} \<longleftrightarrow> e \<le> 0"
  unfolding mem_ball set_eq_iff
  by (simp add: not_less) metric

lemma ball_empty: "e \<le> 0 \<Longrightarrow> ball x e = {}" 
  by simp

lemma closed_cball [iff]: "closed (cball x e)"
proof -
  have "closed (dist x -` {..e})"
    by (intro closed_vimage closed_atMost continuous_intros)
  also have "dist x -` {..e} = cball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_cball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0.  cball x e \<subseteq> S)"
proof -
  {
    fix x and e::real
    assume "x\<in>S" "e>0" "ball x e \<subseteq> S"
    then have "\<exists>d>0. cball x d \<subseteq> S"
      unfolding subset_eq by (intro exI [where x="e/2"], auto)
  }
  then show ?thesis
    unfolding open_contains_ball by force
qed

lemma open_contains_cball_eq: "open S \<Longrightarrow> (\<forall>x. x \<in> S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S))"
  by (metis open_contains_cball subset_eq order_less_imp_le centre_in_cball)

lemma eventually_nhds_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>x. x \<in> ball z d) (nhds z)"
  by (rule eventually_nhds_in_open) simp_all

lemma eventually_at_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>t. t \<in> ball z d \<and> t \<in> A) (at z within A)"
  unfolding eventually_at by (intro exI[of _ d]) (simp_all add: dist_commute)

lemma eventually_at_ball': "d > 0 \<Longrightarrow> eventually (\<lambda>t. t \<in> ball z d \<and> t \<noteq> z \<and> t \<in> A) (at z within A)"
  unfolding eventually_at by (intro exI[of _ d]) (simp_all add: dist_commute)

lemma at_within_ball: "e > 0 \<Longrightarrow> dist x y < e \<Longrightarrow> at y within ball x e = at y"
  by (subst at_within_open) auto

lemma atLeastAtMost_eq_cball:
  fixes a b::real
  shows "{a .. b} = cball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps)

lemma cball_eq_atLeastAtMost:
  fixes a b::real
  shows "cball a b = {a - b .. a + b}"
  by (auto simp: dist_real_def)

lemma greaterThanLessThan_eq_ball:
  fixes a b::real
  shows "{a <..< b} = ball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps)

lemma ball_eq_greaterThanLessThan:
  fixes a b::real
  shows "ball a b = {a - b <..< a + b}"
  by (auto simp: dist_real_def)

lemma interior_ball [simp]: "interior (ball x e) = ball x e"
  by (simp add: interior_open)

lemma cball_eq_empty [simp]: "cball x e = {} \<longleftrightarrow> e < 0"
  by (smt (verit, best) Diff_empty ball_eq_empty cball_diff_sphere centre_in_ball centre_in_cball sphere_empty)

lemma cball_empty [simp]: "e < 0 \<Longrightarrow> cball x e = {}"
  by simp

lemma cball_sing:
  fixes x :: "'a::metric_space"
  shows "e = 0 \<Longrightarrow> cball x e = {x}"
  by simp

lemma ball_divide_subset: "d \<ge> 1 \<Longrightarrow> ball x (e/d) \<subseteq> ball x e"
  by (metis ball_eq_empty div_by_1 frac_le linear subset_ball zero_less_one)

lemma ball_divide_subset_numeral: "ball x (e / numeral w) \<subseteq> ball x e"
  using ball_divide_subset one_le_numeral by blast

lemma cball_divide_subset: "d \<ge> 1 \<Longrightarrow> cball x (e/d) \<subseteq> cball x e"
  by (smt (verit, best) cball_empty div_by_1 frac_le subset_cball zero_le_divide_iff)

lemma cball_divide_subset_numeral: "cball x (e / numeral w) \<subseteq> cball x e"
  using cball_divide_subset one_le_numeral by blast

lemma cball_scale:
  assumes "a \<noteq> 0"
  shows   "(\<lambda>x. a *\<^sub>R x) ` cball c r = cball (a *\<^sub>R c :: 'a :: real_normed_vector) (\<bar>a\<bar> * r)"
proof -
  have *: "(\<lambda>x. a *\<^sub>R x) ` cball c r \<subseteq> cball (a *\<^sub>R c) (\<bar>a\<bar> * r)" for a r and c :: 'a
    by (auto simp: dist_norm simp flip: scaleR_right_diff_distrib intro!: mult_left_mono)
  have "cball (a *\<^sub>R c) (\<bar>a\<bar> * r) = (\<lambda>x. a *\<^sub>R x) ` (\<lambda>x. inverse a *\<^sub>R x) ` cball (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    unfolding image_image using assms by simp
  also have "\<dots> \<subseteq> (\<lambda>x. a *\<^sub>R x) ` cball (inverse a *\<^sub>R (a *\<^sub>R c)) (\<bar>inverse a\<bar> * (\<bar>a\<bar> * r))"
    using "*" by blast
  also have "\<dots> = (\<lambda>x. a *\<^sub>R x) ` cball c r"
    using assms by (simp add: algebra_simps)
  finally have "cball (a *\<^sub>R c) (\<bar>a\<bar> * r) \<subseteq> (\<lambda>x. a *\<^sub>R x) ` cball c r" .
  moreover from assms have "(\<lambda>x. a *\<^sub>R x) ` cball c r \<subseteq> cball (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    using "*" by blast
  ultimately show ?thesis by blast
qed

lemma ball_scale:
  assumes "a \<noteq> 0"
  shows   "(\<lambda>x. a *\<^sub>R x) ` ball c r = ball (a *\<^sub>R c :: 'a :: real_normed_vector) (\<bar>a\<bar> * r)"
proof -
  have *: "(\<lambda>x. a *\<^sub>R x) ` ball c r \<subseteq> ball (a *\<^sub>R c) (\<bar>a\<bar> * r)" if "a \<noteq> 0" for a r and c :: 'a
    using that by (auto simp: dist_norm simp flip: scaleR_right_diff_distrib)
  have "ball (a *\<^sub>R c) (\<bar>a\<bar> * r) = (\<lambda>x. a *\<^sub>R x) ` (\<lambda>x. inverse a *\<^sub>R x) ` ball (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    unfolding image_image using assms by simp
  also have "\<dots> \<subseteq> (\<lambda>x. a *\<^sub>R x) ` ball (inverse a *\<^sub>R (a *\<^sub>R c)) (\<bar>inverse a\<bar> * (\<bar>a\<bar> * r))"
    using assms by (intro image_mono *) auto
  also have "\<dots> = (\<lambda>x. a *\<^sub>R x) ` ball c r"
    using assms by (simp add: algebra_simps)
  finally have "ball (a *\<^sub>R c) (\<bar>a\<bar> * r) \<subseteq> (\<lambda>x. a *\<^sub>R x) ` ball c r" .
  moreover from assms have "(\<lambda>x. a *\<^sub>R x) ` ball c r \<subseteq> ball (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    by (intro *) auto
  ultimately show ?thesis by blast
qed

lemma sphere_scale:
  assumes "a \<noteq> 0"
  shows   "(\<lambda>x. a *\<^sub>R x) ` sphere c r = sphere (a *\<^sub>R c :: 'a :: real_normed_vector) (\<bar>a\<bar> * r)"
proof -
  have *: "(\<lambda>x. a *\<^sub>R x) ` sphere c r \<subseteq> sphere (a *\<^sub>R c) (\<bar>a\<bar> * r)" for a r and c :: 'a
    by (metis (no_types, opaque_lifting) scaleR_right_diff_distrib dist_norm image_subsetI mem_sphere norm_scaleR)
  have "sphere (a *\<^sub>R c) (\<bar>a\<bar> * r) = (\<lambda>x. a *\<^sub>R x) ` (\<lambda>x. inverse a *\<^sub>R x) ` sphere (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    unfolding image_image using assms by simp
  also have "\<dots> \<subseteq> (\<lambda>x. a *\<^sub>R x) ` sphere (inverse a *\<^sub>R (a *\<^sub>R c)) (\<bar>inverse a\<bar> * (\<bar>a\<bar> * r))"
    using "*" by blast
  also have "\<dots> = (\<lambda>x. a *\<^sub>R x) ` sphere c r"
    using assms by (simp add: algebra_simps)
  finally have "sphere (a *\<^sub>R c) (\<bar>a\<bar> * r) \<subseteq> (\<lambda>x. a *\<^sub>R x) ` sphere c r" .
  moreover have "(\<lambda>x. a *\<^sub>R x) ` sphere c r \<subseteq> sphere (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    using "*" by blast
  ultimately show ?thesis by blast
qed

text \<open>As above, but scaled by a complex number\<close>
lemma sphere_cscale:
  assumes "a \<noteq> 0"
  shows   "(\<lambda>x. a * x) ` sphere c r = sphere (a * c :: complex) (cmod a * r)"
proof -
  have *: "(\<lambda>x. a * x) ` sphere c r \<subseteq> sphere (a * c) (cmod a * r)" for a r c
    using dist_mult_left by fastforce
  have "sphere (a * c) (cmod a * r) = (\<lambda>x. a * x) ` (\<lambda>x. inverse a * x) ` sphere (a * c) (cmod a * r)"
    by (simp add: image_image inverse_eq_divide)
  also have "\<dots> \<subseteq> (\<lambda>x. a * x) ` sphere (inverse a * (a * c)) (cmod (inverse a) * (cmod a * r))"
    using "*" by blast
  also have "\<dots> = (\<lambda>x. a * x) ` sphere c r"
    using assms by (simp add: field_simps flip: norm_mult)
  finally have "sphere (a * c) (cmod a * r) \<subseteq> (\<lambda>x. a * x) ` sphere c r" .
  moreover have "(\<lambda>x. a * x) ` sphere c r \<subseteq> sphere (a * c) (cmod a * r)"
    using "*" by blast
  ultimately show ?thesis by blast
qed

lemma frequently_atE:
  fixes x :: "'a :: metric_space"
  assumes "frequently P (at x within s)"
  shows   "\<exists>f. filterlim f (at x within s) sequentially \<and> (\<forall>n. P (f n))"
proof -
  have "\<exists>y. y \<in> s \<inter> (ball x (1 / real (Suc n)) - {x}) \<and> P y" for n
  proof -
    have "\<exists>z\<in>s. z \<noteq> x \<and> dist z x < (1 / real (Suc n)) \<and> P z"
      by (metis assms divide_pos_pos frequently_at of_nat_0_less_iff zero_less_Suc zero_less_one)
    then show ?thesis
      by (auto simp: dist_commute conj_commute)
  qed
  then obtain f where f: "\<And>n. f n \<in> s \<inter> (ball x (1 / real (Suc n)) - {x}) \<and> P (f n)"
    by metis
  have "filterlim f (nhds x) sequentially"
    unfolding tendsto_iff
  proof clarify
    fix e :: real
    assume e: "e > 0"
    then obtain n where n: "Suc n > 1 / e"
      by (meson le_nat_floor lessI not_le)
    have "dist (f k) x < e" if "k \<ge> n" for k
    proof -
      have "dist (f k) x < 1 / real (Suc k)"
        using f[of k] by (auto simp: dist_commute)
      also have "\<dots> \<le> 1 / real (Suc n)"
        using that by (intro divide_left_mono) auto
      also have "\<dots> < e"
        using n e by (simp add: field_simps)
      finally show ?thesis .
    qed
    thus "\<forall>\<^sub>F k in sequentially. dist (f k) x < e"
      unfolding eventually_at_top_linorder by blast
  qed
  moreover have "f n \<noteq> x" for n
    using f[of n] by auto
  ultimately have "filterlim f (at x within s) sequentially"
    using f by (auto simp: filterlim_at)
  with f show ?thesis
    by blast
qed

section \<open>Limit Points\<close>

lemma islimpt_approachable:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e)"
  unfolding islimpt_iff_eventually eventually_at by fast

lemma islimpt_approachable_le: "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> S. x' \<noteq> x \<and> dist x' x \<le> e)"
  for x :: "'a::metric_space"
  unfolding islimpt_approachable
  using approachable_lt_le2 [where f="\<lambda>y. dist y x" and P="\<lambda>y. y \<notin> S \<or> y = x" and Q="\<lambda>x. True"]
  by auto

lemma limpt_of_limpts: "x islimpt {y. y islimpt S} \<Longrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  by (metis islimpt_def islimpt_eq_acc_point mem_Collect_eq)

lemma closed_limpts:  "closed {x::'a::metric_space. x islimpt S}"
  using closed_limpt limpt_of_limpts by blast

lemma limpt_of_closure: "x islimpt closure S \<longleftrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  by (auto simp: closure_def islimpt_Un dest: limpt_of_limpts)

lemma islimpt_eq_infinite_ball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> ball x e))"
  unfolding islimpt_eq_acc_point
  by (metis open_ball Int_commute Int_mono finite_subset open_contains_ball_eq subset_eq)

lemma islimpt_eq_infinite_cball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> cball x e))"
  unfolding islimpt_eq_infinite_ball
  by (metis open_ball ball_subset_cball centre_in_ball finite_Int inf.absorb_iff2 inf_assoc open_contains_cball_eq)


section \<open>Perfect Metric Spaces\<close>

lemma perfect_choose_dist: "0 < r \<Longrightarrow> \<exists>a. a \<noteq> x \<and> dist a x < r"
  for x :: "'a::{perfect_space,metric_space}"
  using islimpt_UNIV [of x] by (simp add: islimpt_approachable)


lemma pointed_ball_nonempty:
  assumes "r > 0"
  shows   "ball x r - {x :: 'a :: {perfect_space, metric_space}} \<noteq> {}"
  using perfect_choose_dist[of r x] assms by (auto simp: ball_def dist_commute)

lemma cball_eq_sing:
  fixes x :: "'a::{metric_space,perfect_space}"
  shows "cball x e = {x} \<longleftrightarrow> e = 0"
  by (metis cball_trivial centre_in_cball finite.emptyI finite.insertI finite_Int
      islimpt_UNIV islimpt_eq_infinite_cball less_eq_real_def) 


section \<open>Finite and discrete\<close>

lemma finite_ball_include:
  fixes a :: "'a::metric_space"
  assumes "finite S" 
  shows "\<exists>e>0. S \<subseteq> ball a e"
  using assms
proof induction
  case (insert x S)
  then obtain e0 where "e0>0" and e0:"S \<subseteq> ball a e0" by auto
  define e where "e = max e0 (2 * dist a x)"
  have "e>0" unfolding e_def using \<open>e0>0\<close> by auto
  moreover have "insert x S \<subseteq> ball a e"
    using e0 \<open>e>0\<close> unfolding e_def by auto
  ultimately show ?case by auto
qed (auto intro: zero_less_one)

lemma finite_set_avoid:
  fixes a :: "'a::metric_space"
  assumes "finite S"
  shows "\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<longrightarrow> d \<le> dist a x"
  using assms
proof induction
  case (insert x S)
  then obtain d where "d > 0" and d: "\<forall>x\<in>S. x \<noteq> a \<longrightarrow> d \<le> dist a x"
    by blast
  then show ?case
    by (metis dist_nz dual_order.strict_implies_order insertE leI order.strict_trans2)
qed (auto intro: zero_less_one)

lemma discrete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes e: "0 < e"
    and d: "\<forall>x \<in> S. \<forall>y \<in> S. dist y x < e \<longrightarrow> y = x"
  shows "closed S"
proof -
  have False if C: "\<And>e. e>0 \<Longrightarrow> \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e" for x
  proof -
    obtain y where y: "y \<in> S" "y \<noteq> x" "dist y x < e/2"
      by (meson C e half_gt_zero)
    then have mp: "min (e/2) (dist x y) > 0"
      by (simp add: dist_commute)
    from d y C[OF mp] show ?thesis
      by metric
  qed
  then show ?thesis
    by (metis islimpt_approachable closed_limpt [where 'a='a])
qed

lemma discrete_imp_not_islimpt:
  assumes e: "0 < e"
    and d: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist y x < e \<Longrightarrow> y = x"
  shows "\<not> x islimpt S"
  by (metis closed_limpt d discrete_imp_closed e islimpt_approachable)
  

section \<open>Interior\<close>

lemma mem_interior: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  using open_contains_ball_eq [where S="interior S"]
  by (simp add: open_subset_interior)

lemma mem_interior_cball: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S)"
  by (meson ball_subset_cball interior_subset mem_interior open_contains_cball open_interior
      subset_trans)

lemma ball_iff_cball: "(\<exists>r>0. ball x r \<subseteq> U) \<longleftrightarrow> (\<exists>r>0. cball x r \<subseteq> U)"
  by (meson mem_interior mem_interior_cball)


section \<open>Frontier\<close>

lemma frontier_straddle:
  fixes a :: "'a::metric_space"
  shows "a \<in> frontier S \<longleftrightarrow> (\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e))"
  unfolding frontier_def closure_interior
  by (auto simp: mem_interior subset_eq ball_def)


section \<open>Limits\<close>

proposition Lim: "(f \<longlongrightarrow> l) net \<longleftrightarrow> trivial_limit net \<or> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"
  by (auto simp: tendsto_iff trivial_limit_eq)

text \<open>Show that they yield usual definitions in the various cases.\<close>

proposition Lim_within_le: "(f \<longlongrightarrow> l)(at a within S) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a \<le> d \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_le)

proposition Lim_within: "(f \<longlongrightarrow> l) (at a within S) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x \<in> S. 0 < dist x a \<and> dist x a  < d \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

corollary Lim_withinI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x \<in> S. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) (at a within S)"
  unfolding Lim_within by (smt (verit, ccfv_SIG) assms zero_less_dist_iff)

proposition Lim_at: "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

lemma Lim_transform_within_set:
  fixes a :: "'a::metric_space" and l :: "'b::metric_space"
  shows "\<lbrakk>(f \<longlongrightarrow> l) (at a within S); eventually (\<lambda>x. x \<in> S \<longleftrightarrow> x \<in> T) (at a)\<rbrakk>
         \<Longrightarrow> (f \<longlongrightarrow> l) (at a within T)"
  by (simp add: eventually_at Lim_within) (smt (verit, best))

text \<open>Another limit point characterization.\<close>

lemma limpt_sequential_inj:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow>
         (\<exists>f. (\<forall>n::nat. f n \<in> S - {x}) \<and> inj f \<and> (f \<longlongrightarrow> x) sequentially)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e"
    by (force simp: islimpt_approachable)
  then obtain y where y: "\<And>e. e>0 \<Longrightarrow> y e \<in> S \<and> y e \<noteq> x \<and> dist (y e) x < e"
    by metis
  define f where "f \<equiv> rec_nat (y 1) (\<lambda>n fn. y (min (inverse(2 ^ (Suc n))) (dist fn x)))"
  have [simp]: "f 0 = y 1"
            and fSuc: "f(Suc n) = y (min (inverse(2 ^ (Suc n))) (dist (f n) x))" for n
    by (simp_all add: f_def)
  have f: "f n \<in> S \<and> (f n \<noteq> x) \<and> dist (f n) x < inverse(2 ^ n)" for n
  proof (induction n)
    case 0 show ?case
      by (simp add: y)
  next
    case (Suc n) then show ?case
      by (smt (verit, best) fSuc dist_pos_lt inverse_positive_iff_positive y zero_less_power)
  qed
  show ?rhs
  proof (intro exI conjI allI)
    show "\<And>n. f n \<in> S - {x}"
      using f by blast
    have "dist (f n) x < dist (f m) x" if "m < n" for m n
    using that
    proof (induction n)
      case 0 then show ?case by simp
    next
      case (Suc n)
      then consider "m < n" | "m = n" using less_Suc_eq by blast
      then show ?case
        by (smt (verit, ccfv_threshold) Suc.IH dist_nz f fSuc y)
    qed
    then show "inj f"
      by (metis less_irrefl linorder_injI)
    have "\<And>e n. \<lbrakk>0 < e; nat \<lceil>1 / e::real\<rceil> \<le> n\<rbrakk> \<Longrightarrow> inverse (2 ^ n) < e"
      by (simp add: divide_simps order_le_less_trans)
    then show "f \<longlonglongrightarrow> x"
      by (metis dual_order.strict_trans f lim_sequentially)
  qed
next
  assume ?rhs
  then show ?lhs
    by (fastforce simp: islimpt_approachable lim_sequentially)
qed

lemma Lim_dist_ubound:
  assumes "\<not>(trivial_limit net)"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. dist a (f x) \<le> e) net"
  shows "dist a l \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)


section \<open>Continuity\<close>

text\<open>Derive the epsilon-delta forms, which we often use as "definitions"\<close>

proposition continuous_within_eps_delta:
  "continuous (at x within s) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'\<in> s.  dist x' x < d --> dist (f x') (f x) < e)"
  unfolding continuous_within and Lim_within  by fastforce

corollary continuous_at_eps_delta:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e > 0. \<exists>d > 0. \<forall>x'. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  using continuous_within_eps_delta [of x UNIV f] by simp

lemma continuous_at_right_real_increasing:
  fixes f :: "real \<Rightarrow> real"
  assumes nondecF: "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "continuous (at_right a) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f (a + d) - f a < e)"
  apply (simp add: greaterThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong)
  by (smt (verit, best) nondecF)

lemma continuous_at_left_real_increasing:
  assumes nondecF: "\<And> x y. x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
  shows "(continuous (at_left (a :: real)) f) \<longleftrightarrow> (\<forall>e > 0. \<exists>delta > 0. f a - f (a - delta) < e)"
  apply (simp add: lessThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong)
  by (smt (verit) nondecF)

text\<open>Versions in terms of open balls.\<close>

lemma continuous_within_ball:
  "continuous (at x within S) f \<longleftrightarrow>
    (\<forall>e > 0. \<exists>d > 0. f ` (ball x d \<inter> S) \<subseteq> ball (f x) e)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix e :: real
    assume "e > 0"
    then obtain d where "d>0" and d: "\<forall>y\<in>S. 0 < dist y x \<and> dist y x < d \<longrightarrow> dist (f y) (f x) < e"
      using \<open>?lhs\<close>[unfolded continuous_within Lim_within] by auto
    { fix y
      assume "y \<in> f ` (ball x d \<inter> S)" then have "y \<in> ball (f x) e"
        using d \<open>e > 0\<close> by (auto simp: dist_commute)
    }
    then have "\<exists>d>0. f ` (ball x d \<inter> S) \<subseteq> ball (f x) e"
      using \<open>d > 0\<close> by blast
  }
  then show ?rhs by auto
next
  assume ?rhs
  then show ?lhs
    apply (simp add: continuous_within Lim_within ball_def subset_eq)
    by (metis (mono_tags, lifting) Int_iff dist_commute mem_Collect_eq)
qed

lemma continuous_at_ball:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f ` (ball x d) \<subseteq> ball (f x) e)"
  apply (simp add: continuous_at Lim_at subset_eq Ball_def Bex_def image_iff)
  by (smt (verit, ccfv_threshold) dist_commute dist_self)


text\<open>Define setwise continuity in terms of limits within the set.\<close>

lemma continuous_on_iff:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  unfolding continuous_on_def Lim_within
  by (metis dist_pos_lt dist_self)

lemma continuous_within_E:
  assumes "continuous (at x within S) f" "e>0"
  obtains d where "d>0"  "\<And>x'. \<lbrakk>x'\<in> S; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms unfolding continuous_within_eps_delta
  by (metis dense order_le_less_trans)

lemma continuous_onI [intro?]:
  assumes "\<And>x e. \<lbrakk>e > 0; x \<in> S\<rbrakk> \<Longrightarrow> \<exists>d>0. \<forall>x'\<in>S. dist x' x < d \<longrightarrow> dist (f x') (f x) \<le> e"
  shows "continuous_on S f"
apply (simp add: continuous_on_iff, clarify)
apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
done

text\<open>Some simple consequential lemmas.\<close>

lemma continuous_onE:
    assumes "continuous_on s f" "x\<in>s" "e>0"
    obtains d where "d>0"  "\<And>x'. \<lbrakk>x' \<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms
  unfolding continuous_on_iff by (metis dense order_le_less_trans)

text\<open>The usual transformation theorems.\<close>

lemma continuous_transform_within:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at x within s) f"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x' \<in> s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "continuous (at x within s) g"
  using assms
  unfolding continuous_within by (force intro: Lim_transform_within)


section \<open>Closure and Limit Characterization\<close>

lemma closure_approachable:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e)"
  using dist_self by (force simp: closure_def islimpt_approachable)

lemma closure_approachable_le:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x \<le> e)"
  unfolding closure_approachable
  using dense by force

lemma closure_approachableD:
  assumes "x \<in> closure S" "e>0"
  shows "\<exists>y\<in>S. dist x y < e"
  using assms unfolding closure_approachable by (auto simp: dist_commute)

lemma closed_approachable:
  fixes S :: "'a::metric_space set"
  shows "closed S \<Longrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e) \<longleftrightarrow> x \<in> S"
  by (metis closure_closed closure_approachable)

lemma closure_contains_Inf:
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_below S"
  shows "Inf S \<in> closure S"
proof -
  have *: "\<forall>x\<in>S. Inf S \<le> x"
    using cInf_lower[of _ S] assms by metis
  { fix e :: real
    assume "e > 0"
    then have "Inf S < Inf S + e" by simp
    with assms obtain x where "x \<in> S" "x < Inf S + e"
      using cInf_lessD by blast
    with * have "\<exists>x\<in>S. dist x (Inf S) < e"
      using dist_real_def by force
  }
  then show ?thesis unfolding closure_approachable by auto
qed

lemma closure_contains_Sup:
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "Sup S \<in> closure S"
proof -
  have *: "\<forall>x\<in>S. x \<le> Sup S"
    using cSup_upper[of _ S] assms by metis
  {
    fix e :: real
    assume "e > 0"
    then have "Sup S - e < Sup S" by simp
    with assms obtain x where "x \<in> S" "Sup S - e < x"
      using less_cSupE by blast
    with * have "\<exists>x\<in>S. dist x (Sup S) < e"
      using dist_real_def by force
  }
  then show ?thesis unfolding closure_approachable by auto
qed

lemma not_trivial_limit_within_ball:
  "\<not> trivial_limit (at x within S) \<longleftrightarrow> (\<forall>e>0. S \<inter> ball x e - {x} \<noteq> {})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    { fix e :: real
      assume "e > 0"
      then obtain y where "y \<in> S - {x}" and "dist y x < e"
        using \<open>?lhs\<close> not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"]
        by auto
      then have "y \<in> S \<inter> ball x e - {x}"
        unfolding ball_def by (simp add: dist_commute)
      then have "S \<inter> ball x e - {x} \<noteq> {}" by blast
    }
    then show ?thesis by auto
  qed
  show ?lhs if ?rhs
  proof -
    { fix e :: real
      assume "e > 0"
      then obtain y where "y \<in> S \<inter> ball x e - {x}"
        using \<open>?rhs\<close> by blast
      then have "y \<in> S - {x}" and "dist y x < e"
        unfolding ball_def by (simp_all add: dist_commute)
      then have "\<exists>y \<in> S - {x}. dist y x < e"
        by auto
    }
    then show ?thesis
      using not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"]
      by auto
  qed
qed


section \<open>Boundedness\<close>

  (* FIXME: This has to be unified with BSEQ!! *)
definition\<^marker>\<open>tag important\<close> (in metric_space) bounded :: "'a set \<Rightarrow> bool"
  where "bounded S \<longleftrightarrow> (\<exists>x e. \<forall>y\<in>S. dist x y \<le> e)"

lemma bounded_subset_cball: "bounded S \<longleftrightarrow> (\<exists>e x. S \<subseteq> cball x e \<and> 0 \<le> e)"
  unfolding bounded_def subset_eq  by auto (meson order_trans zero_le_dist)

lemma bounded_any_center: "bounded S \<longleftrightarrow> (\<exists>e. \<forall>y\<in>S. dist a y \<le> e)"
  unfolding bounded_def
  by auto (metis add.commute add_le_cancel_right dist_commute dist_triangle_le)

lemma bounded_iff: "bounded S \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. norm x \<le> a)"
  unfolding bounded_any_center [where a=0]
  by (simp add: dist_norm)

lemma bdd_above_norm: "bdd_above (norm ` X) \<longleftrightarrow> bounded X"
  by (simp add: bounded_iff bdd_above_def)

lemma bounded_norm_comp: "bounded ((\<lambda>x. norm (f x)) ` S) = bounded (f ` S)"
  by (simp add: bounded_iff)

lemma boundedI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
  shows "bounded S"
  using assms bounded_iff by blast

lemma bounded_empty [simp]: "bounded {}"
  by (simp add: bounded_def)

lemma bounded_subset: "bounded T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> bounded S"
  by (metis bounded_def subset_eq)

lemma bounded_interior[intro]: "bounded S \<Longrightarrow> bounded(interior S)"
  by (metis bounded_subset interior_subset)

lemma bounded_closure[intro]:
  assumes "bounded S"
  shows "bounded (closure S)"
proof -
  from assms obtain x and a where a: "\<forall>y\<in>S. dist x y \<le> a"
    unfolding bounded_def by auto
  { fix y
    assume "y \<in> closure S"
    then obtain f where f: "\<forall>n. f n \<in> S"  "(f \<longlongrightarrow> y) sequentially"
      unfolding closure_sequential by auto
    have "\<forall>n. f n \<in> S \<longrightarrow> dist x (f n) \<le> a" using a by simp
    then have "eventually (\<lambda>n. dist x (f n) \<le> a) sequentially"
      by (simp add: f(1))
    then have "dist x y \<le> a"
      using Lim_dist_ubound f(2) trivial_limit_sequentially by blast
  }
  then show ?thesis
    unfolding bounded_def by auto
qed

lemma bounded_closure_image: "bounded (f ` closure S) \<Longrightarrow> bounded (f ` S)"
  by (simp add: bounded_subset closure_subset image_mono)

lemma bounded_cball[simp,intro]: "bounded (cball x e)"
  unfolding bounded_def  using mem_cball by blast

lemma bounded_ball[simp,intro]: "bounded (ball x e)"
  by (metis ball_subset_cball bounded_cball bounded_subset)

lemma bounded_Un[simp]: "bounded (S \<union> T) \<longleftrightarrow> bounded S \<and> bounded T"
  by (auto simp: bounded_def) (metis Un_iff bounded_any_center le_max_iff_disj)

lemma bounded_Union[intro]: "finite F \<Longrightarrow> \<forall>S\<in>F. bounded S \<Longrightarrow> bounded (\<Union>F)"
  by (induct rule: finite_induct[of F]) auto

lemma bounded_UN [intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. bounded (B x) \<Longrightarrow> bounded (\<Union>x\<in>A. B x)"
  by auto

lemma bounded_insert [simp]: "bounded (insert x S) \<longleftrightarrow> bounded S"
proof -
  have "\<forall>y\<in>{x}. dist x y \<le> 0"
    by simp
  then have "bounded {x}"
    unfolding bounded_def by fast
  then show ?thesis
    by (metis insert_is_Un bounded_Un)
qed

lemma bounded_subset_ballI: "S \<subseteq> ball x r \<Longrightarrow> bounded S"
  by (meson bounded_ball bounded_subset)

lemma bounded_subset_ballD:
  assumes "bounded S" shows "\<exists>r. 0 < r \<and> S \<subseteq> ball x r"
proof -
  obtain e::real and y where "S \<subseteq> cball y e" "0 \<le> e"
    using assms by (auto simp: bounded_subset_cball)
  then show ?thesis
    by (intro exI[where x="dist x y + e + 1"]) metric
qed

lemma finite_imp_bounded [intro]: "finite S \<Longrightarrow> bounded S"
  by (induct set: finite) simp_all

lemma bounded_Int[intro]: "bounded S \<or> bounded T \<Longrightarrow> bounded (S \<inter> T)"
  by (metis Int_lower1 Int_lower2 bounded_subset)

lemma bounded_diff[intro]: "bounded S \<Longrightarrow> bounded (S - T)"
  by (metis Diff_subset bounded_subset)

lemma bounded_dist_comp:
  assumes "bounded (f ` S)" "bounded (g ` S)"
  shows "bounded ((\<lambda>x. dist (f x) (g x)) ` S)"
proof -
  from assms obtain M1 M2 where *: "dist (f x) undefined \<le> M1" "dist undefined (g x) \<le> M2" if "x \<in> S" for x
    by (auto simp: bounded_any_center[of _ undefined] dist_commute)
  have "dist (f x) (g x) \<le> M1 + M2" if "x \<in> S" for x
    using *[OF that]
    by metric
  then show ?thesis
    by (auto intro!: boundedI)
qed

lemma bounded_Times:
  assumes "bounded s" "bounded t"
  shows "bounded (s \<times> t)"
proof -
  obtain x y a b where "\<forall>z\<in>s. dist x z \<le> a" "\<forall>z\<in>t. dist y z \<le> b"
    using assms [unfolded bounded_def] by auto
  then have "\<forall>z\<in>s \<times> t. dist (x, y) z \<le> sqrt (a\<^sup>2 + b\<^sup>2)"
    by (auto simp: dist_Pair_Pair real_sqrt_le_mono add_mono power_mono)
  then show ?thesis unfolding bounded_any_center [where a="(x, y)"] by auto
qed


section \<open>Compactness\<close>

lemma compact_imp_bounded:
  assumes "compact U"
  shows "bounded U"
proof -
  have "compact U" "\<forall>x\<in>U. open (ball x 1)" "U \<subseteq> (\<Union>x\<in>U. ball x 1)"
    using assms by auto
  then obtain D where D: "D \<subseteq> U" "finite D" "U \<subseteq> (\<Union>x\<in>D. ball x 1)"
    by (metis compactE_image)
  from \<open>finite D\<close> have "bounded (\<Union>x\<in>D. ball x 1)"
    by (simp add: bounded_UN)
  then show "bounded U" using \<open>U \<subseteq> (\<Union>x\<in>D. ball x 1)\<close>
    by (rule bounded_subset)
qed

lemma continuous_on_compact_bound:
  assumes "compact A" "continuous_on A f"
  obtains B where "B \<ge> 0" "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> B"
proof -
  have "compact (f ` A)" by (metis assms compact_continuous_image)
  then obtain B where "\<forall>x\<in>A. norm (f x) \<le> B"
    by (auto dest!: compact_imp_bounded simp: bounded_iff)
  hence "max B 0 \<ge> 0" and "\<forall>x\<in>A. norm (f x) \<le> max B 0" by auto
  thus ?thesis using that by blast
qed

lemma closure_Int_ball_not_empty:
  assumes "S \<subseteq> closure T" "x \<in> S" "r > 0"
  shows "T \<inter> ball x r \<noteq> {}"
  using assms centre_in_ball closure_iff_nhds_not_empty by blast

lemma compact_sup_maxdistance:
  fixes S :: "'a::metric_space set"
  assumes "compact S"
    and "S \<noteq> {}"
  shows "\<exists>x\<in>S. \<exists>y\<in>S. \<forall>u\<in>S. \<forall>v\<in>S. dist u v \<le> dist x y"
proof -
  have "compact (S \<times> S)"
    using \<open>compact S\<close> by (intro compact_Times)
  moreover have "S \<times> S \<noteq> {}"
    using \<open>S \<noteq> {}\<close> by auto
  moreover have "continuous_on (S \<times> S) (\<lambda>x. dist (fst x) (snd x))"
    by (intro continuous_at_imp_continuous_on ballI continuous_intros)
  ultimately show ?thesis
    using continuous_attains_sup[of "S \<times> S" "\<lambda>x. dist (fst x) (snd x)"] by auto
qed

text \<open>
  If \<open>A\<close> is a compact subset of an open set \<open>B\<close> in a metric space, then there exists an \<open>\<epsilon> > 0\<close>
  such that the Minkowski sum of \<open>A\<close> with an open ball of radius \<open>\<epsilon>\<close> is also a subset of \<open>B\<close>.
\<close>
lemma compact_subset_open_imp_ball_epsilon_subset:
  assumes "compact A" "open B" "A \<subseteq> B"
  obtains e where "e > 0"  "(\<Union>x\<in>A. ball x e) \<subseteq> B"
proof -
  have "\<forall>x\<in>A. \<exists>e. e > 0 \<and> ball x e \<subseteq> B"
    using assms unfolding open_contains_ball by blast
  then obtain e where e: "\<And>x. x \<in> A \<Longrightarrow> e x > 0" "\<And>x. x \<in> A \<Longrightarrow> ball x (e x) \<subseteq> B"
    by metis
  define C where "C = e ` A"
  obtain X where X: "X \<subseteq> A" "finite X" "A \<subseteq> (\<Union>c\<in>X. ball c (e c / 2))"
    using assms(1)
  proof (rule compactE_image)
    show "open (ball x (e x / 2))" if "x \<in> A" for x
      by simp
    show "A \<subseteq> (\<Union>c\<in>A. ball c (e c / 2))"
      using e by auto
  qed auto

  define e' where "e' = Min (insert 1 ((\<lambda>x. e x / 2) ` X))"
  have "e' > 0"
    unfolding e'_def using e X by (subst Min_gr_iff) auto
  have e': "e' \<le> e x / 2" if "x \<in> X" for x
    using that X unfolding e'_def by (intro Min.coboundedI) auto

  show ?thesis
  proof 
    show "e' > 0"
      by fact
  next
    show "(\<Union>x\<in>A. ball x e') \<subseteq> B"
    proof clarify
      fix x y assume xy: "x \<in> A" "y \<in> ball x e'"
      from xy(1) X obtain z where z: "z \<in> X" "x \<in> ball z (e z / 2)"
        by auto
      have "dist y z \<le> dist x y + dist z x"
        by (metis dist_commute dist_triangle)
      also have "dist z x < e z / 2"
        using xy z by auto
      also have "dist x y < e'"
        using xy by auto
      also have "\<dots> \<le> e z / 2"
        using z by (intro e') auto
      finally have "y \<in> ball z (e z)"
        by (simp add: dist_commute)
      also have "\<dots> \<subseteq> B"
        using z X by (intro e) auto
      finally show "y \<in> B" .
    qed
  qed
qed

lemma compact_subset_open_imp_cball_epsilon_subset:
  assumes "compact A" "open B" "A \<subseteq> B"
  obtains e where "e > 0"  "(\<Union>x\<in>A. cball x e) \<subseteq> B"
proof -
  obtain e where "e > 0" and e: "(\<Union>x\<in>A. ball x e) \<subseteq> B"
    using compact_subset_open_imp_ball_epsilon_subset [OF assms] by blast
  then have "(\<Union>x\<in>A. cball x (e / 2)) \<subseteq> (\<Union>x\<in>A. ball x e)"
    by auto
  with \<open>0 < e\<close> that show ?thesis
    by (metis e half_gt_zero_iff order_trans)
qed

subsubsection\<open>Totally bounded\<close>

proposition seq_compact_imp_totally_bounded:
  assumes "seq_compact S"
  shows "\<forall>e>0. \<exists>k. finite k \<and> k \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>k. ball x e)"
proof -
  { fix e::real assume "e > 0" assume *: "\<And>k. finite k \<Longrightarrow> k \<subseteq> S \<Longrightarrow> \<not> S \<subseteq> (\<Union>x\<in>k. ball x e)"
    let ?Q = "\<lambda>x n r. r \<in> S \<and> (\<forall>m < (n::nat). \<not> (dist (x m) r < e))"
    have "\<exists>x. \<forall>n::nat. ?Q x n (x n)"
    proof (rule dependent_wellorder_choice)
      fix n x assume "\<And>y. y < n \<Longrightarrow> ?Q x y (x y)"
      then have "\<not> S \<subseteq> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        using *[of "x ` {0 ..< n}"] by (auto simp: subset_eq)
      then obtain z where z:"z\<in>S" "z \<notin> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        unfolding subset_eq by auto
      show "\<exists>r. ?Q x n r"
        using z by auto
    qed simp
    then obtain x where "\<forall>n::nat. x n \<in> S" and x:"\<And>n m. m < n \<Longrightarrow> \<not> (dist (x m) (x n) < e)"
      by blast
    then obtain l r where "l \<in> S" and r:"strict_mono  r" and "((x \<circ> r) \<longlongrightarrow> l) sequentially"
      using assms by (metis seq_compact_def)
    then have "Cauchy (x \<circ> r)"
      using LIMSEQ_imp_Cauchy by auto
    then obtain N::nat where "\<And>m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> dist ((x \<circ> r) m) ((x \<circ> r) n) < e"
      unfolding Cauchy_def using \<open>e > 0\<close> by blast
    then have False
      using x[of "r N" "r (N+1)"] r by (auto simp: strict_mono_def) }
  then show ?thesis
    by metis
qed

subsubsection\<open>Heine-Borel theorem\<close>

proposition seq_compact_imp_Heine_Borel:
  fixes S :: "'a :: metric_space set"
  assumes "seq_compact S"
  shows "compact S"
proof -
  from seq_compact_imp_totally_bounded[OF \<open>seq_compact S\<close>]
  obtain f where f: "\<forall>e>0. finite (f e) \<and> f e \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>f e. ball x e)"
    unfolding choice_iff' ..
  define K where "K = (\<lambda>(x, r). ball x r) ` ((\<Union>e \<in> \<rat> \<inter> {0 <..}. f e) \<times> \<rat>)"
  have "countably_compact S"
    using \<open>seq_compact S\<close> by (rule seq_compact_imp_countably_compact)
  then show "compact S"
  proof (rule countably_compact_imp_compact)
    show "countable K"
      unfolding K_def using f
      by (auto intro: countable_finite countable_subset countable_rat
               intro!: countable_image countable_SIGMA countable_UN)
    show "\<forall>b\<in>K. open b" by (auto simp: K_def)
  next
    fix T x
    assume T: "open T" "x \<in> T" and x: "x \<in> S"
    from openE[OF T] obtain e where "0 < e" "ball x e \<subseteq> T"
      by auto
    then have "0 < e/2" "ball x (e/2) \<subseteq> T"
      by auto
    from Rats_dense_in_real[OF \<open>0 < e/2\<close>] obtain r where "r \<in> \<rat>" "0 < r" "r < e/2"
      by auto
    from f[rule_format, of r] \<open>0 < r\<close> \<open>x \<in> S\<close> obtain k where "k \<in> f r" "x \<in> ball k r"
      by auto
    from \<open>r \<in> \<rat>\<close> \<open>0 < r\<close> \<open>k \<in> f r\<close> have "ball k r \<in> K"
      by (auto simp: K_def)
    then show "\<exists>b\<in>K. x \<in> b \<and> b \<inter> S \<subseteq> T"
    proof (rule bexI[rotated], safe)
      fix y
      assume "y \<in> ball k r"
      with \<open>r < e/2\<close> \<open>x \<in> ball k r\<close> have "dist x y < e"
        by (intro dist_triangle_half_r [of k _ e]) (auto simp: dist_commute)
      with \<open>ball x e \<subseteq> T\<close> show "y \<in> T"
        by auto
    next
      show "x \<in> ball k r" by fact
    qed
  qed
qed

proposition compact_eq_seq_compact_metric:
  "compact (S :: 'a::metric_space set) \<longleftrightarrow> seq_compact S"
  using compact_imp_seq_compact seq_compact_imp_Heine_Borel by blast

proposition compact_def: \<comment> \<open>this is the definition of compactness in HOL Light\<close>
  "compact (S :: 'a::metric_space set) \<longleftrightarrow>
   (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l))"
  unfolding compact_eq_seq_compact_metric seq_compact_def by auto

subsubsection \<open>Complete the chain of compactness variants\<close>

proposition compact_eq_Bolzano_Weierstrass:
  fixes S :: "'a::metric_space set"
  shows "compact S \<longleftrightarrow> (\<forall>T. infinite T \<and> T \<subseteq> S \<longrightarrow> (\<exists>x \<in> S. x islimpt T))"
  by (meson Bolzano_Weierstrass_imp_seq_compact Heine_Borel_imp_Bolzano_Weierstrass seq_compact_imp_Heine_Borel)

proposition Bolzano_Weierstrass_imp_bounded:
  "(\<And>T. \<lbrakk>infinite T; T \<subseteq> S\<rbrakk> \<Longrightarrow> (\<exists>x \<in> S. x islimpt T)) \<Longrightarrow> bounded S"
  using compact_imp_bounded unfolding compact_eq_Bolzano_Weierstrass by metis


section \<open>Banach fixed point theorem\<close>
  
theorem Banach_fix:
  assumes s: "complete s" "s \<noteq> {}"
    and c: "0 \<le> c" "c < 1"
    and f: "f ` s \<subseteq> s"
    and lipschitz: "\<forall>x\<in>s. \<forall>y\<in>s. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x\<in>s. f x = x"
proof -
  from c have "1 - c > 0" by simp

  from s(2) obtain z0 where z0: "z0 \<in> s" by blast
  define z where "z n = (f ^^ n) z0" for n
  with f z0 have z_in_s: "z n \<in> s" for n :: nat
    by (induct n) auto
  define d where "d = dist (z 0) (z 1)"

  have fzn: "f (z n) = z (Suc n)" for n
    by (simp add: z_def)
  have cf_z: "dist (z n) (z (Suc n)) \<le> (c ^ n) * d" for n :: nat
  proof (induct n)
    case 0
    then show ?case
      by (simp add: d_def)
  next
    case (Suc m)
    with \<open>0 \<le> c\<close> have "c * dist (z m) (z (Suc m)) \<le> c ^ Suc m * d"
      using mult_left_mono[of "dist (z m) (z (Suc m))" "c ^ m * d" c] by simp
    then show ?case
      using lipschitz[THEN bspec[where x="z m"], OF z_in_s, THEN bspec[where x="z (Suc m)"], OF z_in_s]
      by (simp add: fzn mult_le_cancel_left)
  qed

  have cf_z2: "(1 - c) * dist (z m) (z (m + n)) \<le> (c ^ m) * d * (1 - c ^ n)" for n m :: nat
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc k)
    from c have "(1 - c) * dist (z m) (z (m + Suc k)) \<le>
        (1 - c) * (dist (z m) (z (m + k)) + dist (z (m + k)) (z (Suc (m + k))))"
      by (simp add: dist_triangle)
    also from c cf_z[of "m + k"] have "\<dots> \<le> (1 - c) * (dist (z m) (z (m + k)) + c ^ (m + k) * d)"
      by simp
    also from Suc have "\<dots> \<le> c ^ m * d * (1 - c ^ k) + (1 - c) * c ^ (m + k) * d"
      by (simp add: field_simps)
    also have "\<dots> = (c ^ m) * (d * (1 - c ^ k) + (1 - c) * c ^ k * d)"
      by (simp add: power_add field_simps)
    also from c have "\<dots> \<le> (c ^ m) * d * (1 - c ^ Suc k)"
      by (simp add: field_simps)
    finally show ?case by simp
  qed

  have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (z m) (z n) < e" if "e > 0" for e
  proof (cases "d = 0")
    case True
    from \<open>1 - c > 0\<close> have "(1 - c) * x \<le> 0 \<longleftrightarrow> x \<le> 0" for x
      by (simp add: mult_le_0_iff)
    with c cf_z2[of 0] True have "z n = z0" for n
      by (simp add: z_def)
    with \<open>e > 0\<close> show ?thesis by simp
  next
    case False
    with zero_le_dist[of "z 0" "z 1"] have "d > 0"
      by (metis d_def less_le)
    with \<open>1 - c > 0\<close> \<open>e > 0\<close> have "0 < e * (1 - c) / d"
      by simp
    with c obtain N where N: "c ^ N < e * (1 - c) / d"
      using real_arch_pow_inv[of "e * (1 - c) / d" c] by auto
    have *: "dist (z m) (z n) < e" if "m > n" and as: "m \<ge> N" "n \<ge> N" for m n :: nat
    proof -
      from c \<open>n \<ge> N\<close> have *: "c ^ n \<le> c ^ N"
        using power_decreasing[OF \<open>n\<ge>N\<close>, of c] by simp
      from c \<open>m > n\<close> have "1 - c ^ (m - n) > 0"
        using power_strict_mono[of c 1 "m - n"] by simp
      with \<open>d > 0\<close> \<open>0 < 1 - c\<close> have **: "d * (1 - c ^ (m - n)) / (1 - c) > 0"
        by simp
      from cf_z2[of n "m - n"] \<open>m > n\<close>
      have "dist (z m) (z n) \<le> c ^ n * d * (1 - c ^ (m - n)) / (1 - c)"
        by (simp add: pos_le_divide_eq[OF \<open>1 - c > 0\<close>] mult.commute dist_commute)
      also have "\<dots> \<le> c ^ N * d * (1 - c ^ (m - n)) / (1 - c)"
        using mult_right_mono[OF * order_less_imp_le[OF **]]
        by (simp add: mult.assoc)
      also have "\<dots> < (e * (1 - c) / d) * d * (1 - c ^ (m - n)) / (1 - c)"
        using mult_strict_right_mono[OF N **] by (auto simp: mult.assoc)
      also from c \<open>1 - c ^ (m - n) > 0\<close> \<open>e > 0\<close> have "\<dots> \<le> e"
        using mult_right_le_one_le[of e "1 - c ^ (m - n)"] by auto
      finally show ?thesis by simp
    qed
    have "dist (z n) (z m) < e" if "N \<le> m" "N \<le> n" for m n :: nat
      using  *[of n m] *[of m n]
      using \<open>0 < e\<close> dist_commute_lessI that by fastforce
    then show ?thesis by auto
  qed
  then have "Cauchy z"
    by (metis metric_CauchyI)
  then obtain x where "x\<in>s" and x:"(z \<longlongrightarrow> x) sequentially"
    using s(1)[unfolded compact_def complete_def, THEN spec[where x=z]] and z_in_s by auto

  define e where "e = dist (f x) x"
  have "e = 0"
  proof (rule ccontr)
    assume "e \<noteq> 0"
    then have "e > 0"
      unfolding e_def using zero_le_dist[of "f x" x]
      by (metis dist_eq_0_iff dist_nz e_def)
    then obtain N where N:"\<forall>n\<ge>N. dist (z n) x < e/2"
      using x[unfolded lim_sequentially, THEN spec[where x="e/2"]] by auto
    then have N':"dist (z N) x < e/2" by auto
    have *: "c * dist (z N) x \<le> dist (z N) x"
      unfolding mult_le_cancel_right2
      using zero_le_dist[of "z N" x] and c
      by (metis dist_eq_0_iff dist_nz order_less_asym less_le)
    have "dist (f (z N)) (f x) \<le> c * dist (z N) x"
      using lipschitz[THEN bspec[where x="z N"], THEN bspec[where x=x]]
      using z_in_s[of N] \<open>x\<in>s\<close> c
      by auto
    also have "\<dots> < e/2"
      using N' and c using * by auto
    finally show False
      unfolding fzn
      using N[THEN spec[where x="Suc N"]] and dist_triangle_half_r[of "z (Suc N)" "f x" e x]
      unfolding e_def
      by auto
  qed
  then have "f x = x" by (auto simp: e_def)
  moreover have "y = x" if "f y = y" "y \<in> s" for y
  proof -
    from \<open>x \<in> s\<close> \<open>f x = x\<close> that have "dist x y \<le> c * dist x y"
      using lipschitz by fastforce
    with c and zero_le_dist[of x y] have "dist x y = 0"
      by (simp add: mult_le_cancel_right1)
    then show ?thesis by simp
  qed
  ultimately show ?thesis
    using \<open>x\<in>s\<close> by blast
qed


section \<open>Edelstein fixed point theorem\<close>

theorem Edelstein_fix:
  fixes S :: "'a::metric_space set"
  assumes S: "compact S" "S \<noteq> {}"
    and gs: "(g ` S) \<subseteq> S"
    and dist: "\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> dist (g x) (g y) < dist x y"
  shows "\<exists>!x\<in>S. g x = x"
proof -
  let ?D = "(\<lambda>x. (x, x)) ` S"
  have D: "compact ?D" "?D \<noteq> {}"
    by (rule compact_continuous_image)
       (auto intro!: S continuous_Pair continuous_ident simp: continuous_on_eq_continuous_within)

  have "\<And>x y e. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> 0 < e \<Longrightarrow> dist y x < e \<Longrightarrow> dist (g y) (g x) < e"
    using dist by fastforce
  then have "continuous_on S g"
    by (auto simp: continuous_on_iff)
  then have cont: "continuous_on ?D (\<lambda>x. dist ((g \<circ> fst) x) (snd x))"
    unfolding continuous_on_eq_continuous_within
    by (intro continuous_dist ballI continuous_within_compose)
       (auto intro!: continuous_fst continuous_snd continuous_ident simp: image_image)

  obtain a where "a \<in> S" and le: "\<And>x. x \<in> S \<Longrightarrow> dist (g a) a \<le> dist (g x) x"
    using continuous_attains_inf[OF D cont] by auto

  have "g a = a"
    by (metis \<open>a \<in> S\<close> dist gs image_subset_iff le order.strict_iff_not)
  moreover have "\<And>x. x \<in> S \<Longrightarrow> g x = x \<Longrightarrow> x = a"
    using dist[THEN bspec[where x=a]] \<open>g a = a\<close> and \<open>a\<in>S\<close> by auto
  ultimately show "\<exists>!x\<in>S. g x = x"
    using \<open>a \<in> S\<close> by blast
qed

section \<open>The diameter of a set\<close>

definition\<^marker>\<open>tag important\<close> diameter :: "'a::metric_space set \<Rightarrow> real" where
  "diameter S = (if S = {} then 0 else SUP (x,y)\<in>S\<times>S. dist x y)"

lemma diameter_empty [simp]: "diameter{} = 0"
  by (auto simp: diameter_def)

lemma diameter_singleton [simp]: "diameter{x} = 0"
  by (auto simp: diameter_def)

lemma diameter_le:
  assumes "S \<noteq> {} \<or> 0 \<le> d"
    and no: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> norm(x - y) \<le> d"
  shows "diameter S \<le> d"
  using assms
  by (auto simp: dist_norm diameter_def intro: cSUP_least)

lemma diameter_bounded_bound:
  fixes S :: "'a :: metric_space set"
  assumes S: "bounded S" "x \<in> S" "y \<in> S"
  shows "dist x y \<le> diameter S"
proof -
  from S obtain z d where z: "\<And>x. x \<in> S \<Longrightarrow> dist z x \<le> d"
    unfolding bounded_def by auto
  have "bdd_above (case_prod dist ` (S\<times>S))"
  proof (intro bdd_aboveI, safe)
    fix a b
    assume "a \<in> S" "b \<in> S"
    with z[of a] z[of b] dist_triangle[of a b z]
    show "dist a b \<le> 2 * d"
      by (simp add: dist_commute)
  qed
  moreover have "(x,y) \<in> S\<times>S" using S by auto
  ultimately have "dist x y \<le> (SUP (x,y)\<in>S\<times>S. dist x y)"
    by (rule cSUP_upper2) simp
  with \<open>x \<in> S\<close> show ?thesis
    by (auto simp: diameter_def)
qed

lemma diameter_lower_bounded:
  fixes S :: "'a :: metric_space set"
  assumes S: "bounded S"
    and d: "0 < d" "d < diameter S"
  shows "\<exists>x\<in>S. \<exists>y\<in>S. d < dist x y"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  moreover have "S \<noteq> {}"
    using d by (auto simp: diameter_def)
  ultimately have "diameter S \<le> d"
    by (auto simp: not_less diameter_def intro!: cSUP_least)
  with \<open>d < diameter S\<close> show False by auto
qed

lemma diameter_bounded:
  assumes "bounded S"
  shows "\<forall>x\<in>S. \<forall>y\<in>S. dist x y \<le> diameter S"
    and "\<forall>d>0. d < diameter S \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>S. dist x y > d)"
  using diameter_bounded_bound[of S] diameter_lower_bounded[of S] assms
  by auto

lemma bounded_two_points: "bounded S \<longleftrightarrow> (\<exists>e. \<forall>x\<in>S. \<forall>y\<in>S. dist x y \<le> e)"
  by (meson bounded_def diameter_bounded(1))

lemma diameter_compact_attained:
  assumes "compact S"
    and "S \<noteq> {}"
  shows "\<exists>x\<in>S. \<exists>y\<in>S. dist x y = diameter S"
proof -
  have b: "bounded S" using assms(1)
    by (rule compact_imp_bounded)
  then obtain x y where xys: "x\<in>S" "y\<in>S"
    and xy: "\<forall>u\<in>S. \<forall>v\<in>S. dist u v \<le> dist x y"
    using compact_sup_maxdistance[OF assms] by auto
  then have "diameter S \<le> dist x y"
    unfolding diameter_def by (force intro!: cSUP_least)
  then show ?thesis
    by (metis b diameter_bounded_bound order_antisym xys)
qed

lemma diameter_ge_0:
  assumes "bounded S"  shows "0 \<le> diameter S"
  by (metis all_not_in_conv assms diameter_bounded_bound diameter_empty dist_self order_refl)

lemma diameter_subset:
  assumes "S \<subseteq> T" "bounded T"
  shows "diameter S \<le> diameter T"
proof (cases "S = {} \<or> T = {}")
  case True
  with assms show ?thesis
    by (force simp: diameter_ge_0)
next
  case False
  then have "bdd_above ((\<lambda>x. case x of (x, xa) \<Rightarrow> dist x xa) ` (T \<times> T))"
    using \<open>bounded T\<close> diameter_bounded_bound by (force simp: bdd_above_def)
  with False \<open>S \<subseteq> T\<close> show ?thesis
    apply (simp add: diameter_def)
    apply (rule cSUP_subset_mono, auto)
    done
qed

lemma diameter_closure:
  assumes "bounded S"
  shows "diameter(closure S) = diameter S"
proof (rule order_antisym)
  have "False" if d_less_d: "diameter S < diameter (closure S)"
  proof -
    define d where "d = diameter(closure S) - diameter(S)"
    have "d > 0"
      using that by (simp add: d_def)
    then have dle: "diameter(closure(S)) - d / 2 < diameter(closure(S))"
      by simp
    have dd: "diameter (closure S) - d / 2 = (diameter(closure(S)) + diameter(S)) / 2"
      by (simp add: d_def field_split_simps)
     have bocl: "bounded (closure S)"
      using assms by blast
    moreover have "0 \<le> diameter S"
      using assms diameter_ge_0 by blast
    ultimately obtain x y where "x \<in> closure S" "y \<in> closure S" and xy: "diameter(closure(S)) - d / 2 < dist x y"
      by (smt (verit) dle d_less_d d_def dd diameter_lower_bounded)
    then obtain x' y' where x'y': "x' \<in> S" "dist x' x < d/4" "y' \<in> S" "dist y' y < d/4"
      by (metis \<open>0 < d\<close> zero_less_divide_iff zero_less_numeral closure_approachable)
    then have "dist x' y' \<le> diameter S"
      using assms diameter_bounded_bound by blast
    with x'y' have "dist x y \<le> d / 4 + diameter S + d / 4"
      by (meson add_mono dist_triangle dist_triangle3 less_eq_real_def order_trans)
    then show ?thesis
      using xy d_def by linarith
  qed
  then show "diameter (closure S) \<le> diameter S"
    by fastforce
  next
    show "diameter S \<le> diameter (closure S)"
      by (simp add: assms bounded_closure closure_subset diameter_subset)
qed

proposition Lebesgue_number_lemma:
  assumes "compact S" "\<C> \<noteq> {}" "S \<subseteq> \<Union>\<C>" and ope: "\<And>B. B \<in> \<C> \<Longrightarrow> open B"
  obtains \<delta> where "0 < \<delta>" "\<And>T. \<lbrakk>T \<subseteq> S; diameter T < \<delta>\<rbrakk> \<Longrightarrow> \<exists>B \<in> \<C>. T \<subseteq> B"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (metis \<open>\<C> \<noteq> {}\<close> zero_less_one empty_subsetI equals0I subset_trans that)
next
  case False
  { fix x assume "x \<in> S"
    then obtain C where C: "x \<in> C" "C \<in> \<C>"
      using \<open>S \<subseteq> \<Union>\<C>\<close> by blast
    then obtain r where r: "r>0" "ball x (2*r) \<subseteq> C"
      by (metis field_sum_of_halves half_gt_zero mult.commute mult_2_right ope open_contains_ball)
    then have "\<exists>r C. r > 0 \<and> ball x (2*r) \<subseteq> C \<and> C \<in> \<C>"
      using C by blast
  }
  then obtain r where r: "\<And>x. x \<in> S \<Longrightarrow> r x > 0 \<and> (\<exists>C \<in> \<C>. ball x (2*r x) \<subseteq> C)"
    by metis
  then have "S \<subseteq> (\<Union>x \<in> S. ball x (r x))"
    by auto
  then obtain \<T> where "finite \<T>" "S \<subseteq> \<Union>\<T>" and \<T>: "\<T> \<subseteq> (\<lambda>x. ball x (r x)) ` S"
    by (rule compactE [OF \<open>compact S\<close>]) auto
  then obtain S0 where "S0 \<subseteq> S" "finite S0" and S0: "\<T> = (\<lambda>x. ball x (r x)) ` S0"
    by (meson finite_subset_image)
  then have "S0 \<noteq> {}"
    using False \<open>S \<subseteq> \<Union>\<T>\<close> by auto
  define \<delta> where "\<delta> = Inf (r ` S0)"
  have "\<delta> > 0"
    using \<open>finite S0\<close> \<open>S0 \<subseteq> S\<close> \<open>S0 \<noteq> {}\<close> r by (auto simp: \<delta>_def finite_less_Inf_iff)
  show ?thesis
  proof
    show "0 < \<delta>"
      by (simp add: \<open>0 < \<delta>\<close>)
    show "\<exists>B \<in> \<C>. T \<subseteq> B" if "T \<subseteq> S" and dia: "diameter T < \<delta>" for T
    proof (cases "T = {}")
      case True
      then show ?thesis
        using \<open>\<C> \<noteq> {}\<close> by blast
    next
      case False
      then obtain y where "y \<in> T" by blast
      then have "y \<in> S"
        using \<open>T \<subseteq> S\<close> by auto
      then obtain x where "x \<in> S0" and x: "y \<in> ball x (r x)"
        using \<open>S \<subseteq> \<Union>\<T>\<close> S0 that by blast
      have "ball y \<delta> \<subseteq> ball y (r x)"
        by (metis \<delta>_def \<open>S0 \<noteq> {}\<close> \<open>finite S0\<close> \<open>x \<in> S0\<close> empty_is_image finite_imageI finite_less_Inf_iff imageI less_irrefl not_le subset_ball)
      also have "... \<subseteq> ball x (2*r x)"
        using x by metric
      finally obtain C where "C \<in> \<C>" "ball y \<delta> \<subseteq> C"
        by (meson r \<open>S0 \<subseteq> S\<close> \<open>x \<in> S0\<close> dual_order.trans subsetCE)
      have "bounded T"
        using \<open>compact S\<close> bounded_subset compact_imp_bounded \<open>T \<subseteq> S\<close> by blast
      then have "T \<subseteq> ball y \<delta>"
        using \<open>y \<in> T\<close> dia diameter_bounded_bound by fastforce
      then show ?thesis
        by (meson \<open>C \<in> \<C>\<close> \<open>ball y \<delta> \<subseteq> C\<close> subset_eq)
    qed
  qed
qed


section \<open>Metric spaces with the Heine-Borel property\<close>

text \<open>
  A metric space (or topological vector space) is said to have the
  Heine-Borel property if every closed and bounded subset is compact.
\<close>

class heine_borel = metric_space +
  assumes bounded_imp_convergent_subsequence:
    "bounded (range f) \<Longrightarrow> \<exists>l r. strict_mono (r::nat\<Rightarrow>nat) \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"

proposition bounded_closed_imp_seq_compact:
  fixes S::"'a::heine_borel set"
  assumes "bounded S"
    and "closed S"
  shows "seq_compact S"
  unfolding seq_compact_def
proof (intro strip)
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> S"
  with \<open>bounded S\<close> have "bounded (range f)"
    by (auto intro: bounded_subset)
  obtain l r where r: "strict_mono (r :: nat \<Rightarrow> nat)" and l: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using bounded_imp_convergent_subsequence [OF \<open>bounded (range f)\<close>] by auto
  from f have fr: "\<forall>n. (f \<circ> r) n \<in> S"
    by simp
  show "\<exists>l\<in>S. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    using assms(2) closed_sequentially fr l r by blast
qed

lemma compact_eq_bounded_closed:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<longleftrightarrow> bounded S \<and> closed S"
  using bounded_closed_imp_seq_compact compact_eq_seq_compact_metric compact_imp_bounded compact_imp_closed 
  by auto

lemma bounded_infinite_imp_islimpt:
  fixes S :: "'a::heine_borel set"
  assumes "T \<subseteq> S" "bounded S" "infinite T"
  obtains x where "x islimpt S" 
  by (meson assms closed_limpt compact_eq_Bolzano_Weierstrass compact_eq_bounded_closed islimpt_subset) 

lemma compact_Inter:
  fixes \<F> :: "'a :: heine_borel set set"
  assumes com: "\<And>S. S \<in> \<F> \<Longrightarrow> compact S" and "\<F> \<noteq> {}"
  shows "compact(\<Inter> \<F>)"
  using assms
  by (meson Inf_lower all_not_in_conv bounded_subset closed_Inter compact_eq_bounded_closed)

lemma compact_closure [simp]:
  fixes S :: "'a::heine_borel set"
  shows "compact(closure S) \<longleftrightarrow> bounded S"
by (meson bounded_closure bounded_subset closed_closure closure_subset compact_eq_bounded_closed)

instance\<^marker>\<open>tag important\<close> real :: heine_borel
proof
  fix f :: "nat \<Rightarrow> real"
  assume f: "bounded (range f)"
  obtain r :: "nat \<Rightarrow> nat" where r: "strict_mono r" "monoseq (f \<circ> r)"
    unfolding comp_def by (metis seq_monosub)
  then have "Bseq (f \<circ> r)"
    unfolding Bseq_eq_bounded by (metis f BseqI' bounded_iff comp_apply rangeI)
  with r show "\<exists>l r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    using Bseq_monoseq_convergent[of "f \<circ> r"] by (auto simp: convergent_def)
qed

lemma compact_lemma_general:
  fixes f :: "nat \<Rightarrow> 'a"
  fixes proj::"'a \<Rightarrow> 'b \<Rightarrow> 'c::heine_borel" (infixl \<open>proj\<close> 60)
  fixes unproj:: "('b \<Rightarrow> 'c) \<Rightarrow> 'a"
  assumes finite_basis: "finite basis"
  assumes bounded_proj: "\<And>k. k \<in> basis \<Longrightarrow> bounded ((\<lambda>x. x proj k) ` range f)"
  assumes proj_unproj: "\<And>e k. k \<in> basis \<Longrightarrow> (unproj e) proj k = e k"
  assumes unproj_proj: "\<And>x. unproj (\<lambda>k. x proj k) = x"
  shows "\<forall>d\<subseteq>basis. \<exists>l::'a. \<exists> r::nat\<Rightarrow>nat.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) proj i) (l proj i) < e) sequentially)"
proof safe
  fix d :: "'b set"
  assume d: "d \<subseteq> basis"
  with finite_basis have "finite d"
    by (blast intro: finite_subset)
  from this d show "\<exists>l::'a. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and>
    (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) proj i) (l proj i) < e) sequentially)"
  proof (induct d)
    case empty
    then show ?case
      unfolding strict_mono_def by auto
  next
    case (insert k d)
    have k[intro]: "k \<in> basis"
      using insert by auto
    have s': "bounded ((\<lambda>x. x proj k) ` range f)"
      using k
      by (rule bounded_proj)
    obtain l1::"'a" and r1 where r1: "strict_mono r1"
      and lr1: "\<forall>e > 0. \<forall>\<^sub>F n in sequentially. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e"
      using insert by auto
    have f': "\<forall>n. f (r1 n) proj k \<in> (\<lambda>x. x proj k) ` range f"
      by simp
    have "bounded (range (\<lambda>i. f (r1 i) proj k))"
      by (metis (lifting) bounded_subset f' image_subsetI s')
    then obtain l2 r2 where r2: "strict_mono r2" and lr2: "(\<lambda>i. f (r1 (r2 i)) proj k) \<longlonglongrightarrow> l2"
      using bounded_imp_convergent_subsequence[of "\<lambda>i. f (r1 i) proj k"]
      by (auto simp: o_def)
    define r where "r = r1 \<circ> r2"
    have r: "strict_mono r"
      using r1 and r2 unfolding r_def o_def strict_mono_def by auto
    moreover
    define l where "l = unproj (\<lambda>i. if i = k then l2 else l1 proj i)"
    { fix e::real
      assume "e > 0"
      from lr1 \<open>e > 0\<close> have N1: "\<forall>\<^sub>F n in sequentially. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e"
        by blast
      from lr2 \<open>e > 0\<close> have N2: "\<forall>\<^sub>F n in sequentially. dist (f (r1 (r2 n)) proj k) l2 < e"
        by (rule tendstoD)
      from r2 N1 have N1': "\<forall>\<^sub>F n in sequentially. \<forall>i\<in>d. dist (f (r1 (r2 n)) proj i) (l1 proj i) < e"
        by (rule eventually_subseq)
      have "\<forall>\<^sub>F n in sequentially. \<forall>i\<in>insert k d. dist (f (r n) proj i) (l proj i) < e"
        using N1' N2
        by eventually_elim (use insert.prems in \<open>auto simp: l_def r_def o_def proj_unproj\<close>)
    }
    ultimately show ?case by auto
  qed
qed

lemma bounded_fst: "bounded s \<Longrightarrow> bounded (fst ` s)"
  unfolding bounded_def
  by (metis (erased, opaque_lifting) dist_fst_le image_iff order_trans)

lemma bounded_snd: "bounded s \<Longrightarrow> bounded (snd ` s)"
  unfolding bounded_def
  by (metis (no_types, opaque_lifting) dist_snd_le image_iff order.trans)

instance\<^marker>\<open>tag important\<close> prod :: (heine_borel, heine_borel) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a \<times> 'b"
  assume f: "bounded (range f)"
  then have "bounded (fst ` range f)"
    by (rule bounded_fst)
  then have s1: "bounded (range (fst \<circ> f))"
    by (simp add: image_comp)
  obtain l1 r1 where r1: "strict_mono r1" and l1: "(\<lambda>n. fst (f (r1 n))) \<longlonglongrightarrow> l1"
    using bounded_imp_convergent_subsequence [OF s1] unfolding o_def by fast
  from f have s2: "bounded (range (snd \<circ> f \<circ> r1))"
    by (auto simp: image_comp intro: bounded_snd bounded_subset)
  obtain l2 r2 where r2: "strict_mono r2" and l2: "(\<lambda>n. snd (f (r1 (r2 n)))) \<longlonglongrightarrow> l2"
    using bounded_imp_convergent_subsequence [OF s2]
    unfolding o_def by fast
  have l1': "((\<lambda>n. fst (f (r1 (r2 n)))) \<longlongrightarrow> l1) sequentially"
    using LIMSEQ_subseq_LIMSEQ [OF l1 r2] unfolding o_def .
  have l: "((f \<circ> (r1 \<circ> r2)) \<longlongrightarrow> (l1, l2)) sequentially"
    using tendsto_Pair [OF l1' l2] unfolding o_def by simp
  have r: "strict_mono (r1 \<circ> r2)"
    using r1 r2 unfolding strict_mono_def by simp
  show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using l r by fast
qed


section \<open>Completeness\<close>

proposition (in metric_space) completeI:
  assumes "\<And>f. \<forall>n. f n \<in> s \<Longrightarrow> Cauchy f \<Longrightarrow> \<exists>l\<in>s. f \<longlonglongrightarrow> l"
  shows "complete s"
  using assms unfolding complete_def by fast

proposition (in metric_space) completeE:
  assumes "complete s" and "\<forall>n. f n \<in> s" and "Cauchy f"
  obtains l where "l \<in> s" and "f \<longlonglongrightarrow> l"
  using assms unfolding complete_def by fast

(* TODO: generalize to uniform spaces *)
lemma compact_imp_complete:
  fixes S :: "'a::metric_space set"
  assumes "compact S"
  shows "complete S"
  unfolding complete_def
proof clarify
  fix f
  assume as: "(\<forall>n::nat. f n \<in> S)" "Cauchy f"
  from as(1) obtain l r where lr: "l\<in>S" "strict_mono r" "(f \<circ> r) \<longlonglongrightarrow> l"
    using assms unfolding compact_def by blast

  note lr' = seq_suble [OF lr(2)]
  {
    fix e :: real
    assume "e > 0"
    from as(2) obtain N where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (f m) (f n) < e/2"
      unfolding Cauchy_def using \<open>e > 0\<close> by (meson half_gt_zero)
    then obtain M where M:"\<forall>n\<ge>M. dist ((f \<circ> r) n) l < e/2"
      by (metis dist_self lim_sequentially lr(3))
    {
      fix n :: nat
      assume n: "n \<ge> max N M"
      have "dist ((f \<circ> r) n) l < e/2"
        using n M by auto
      moreover have "r n \<ge> N"
        using lr'[of n] n by auto
      then have "dist (f n) ((f \<circ> r) n) < e/2"
        using N and n by auto
      ultimately have "dist (f n) l < e" using n M
        by metric
    }
    then have "\<exists>N. \<forall>n\<ge>N. dist (f n) l < e" by blast
  }
  then show "\<exists>l\<in>S. (f \<longlongrightarrow> l) sequentially" using \<open>l\<in>S\<close>
    unfolding lim_sequentially by auto
qed

proposition compact_eq_totally_bounded:
  "compact S \<longleftrightarrow> complete S \<and> (\<forall>e>0. \<exists>k. finite k \<and> S \<subseteq> (\<Union>x\<in>k. ball x e))"
    (is "_ \<longleftrightarrow> ?rhs")
proof
  assume assms: "?rhs"
  then obtain k where k: "\<And>e. 0 < e \<Longrightarrow> finite (k e)" "\<And>e. 0 < e \<Longrightarrow> S \<subseteq> (\<Union>x\<in>k e. ball x e)"
    by (auto simp: choice_iff')

  show "compact S"
  proof cases
    assume "S = {}"
    then show "compact S" by (simp add: compact_def)
  next
    assume "S \<noteq> {}"
    show ?thesis
      unfolding compact_def
    proof safe
      fix f :: "nat \<Rightarrow> 'a"
      assume f: "\<forall>n. f n \<in> S"

      define e where "e n = 1 / (2 * Suc n)" for n
      then have [simp]: "\<And>n. 0 < e n" by auto
      define B where "B n U = (SOME b. infinite {n. f n \<in> b} \<and> (\<exists>x. b \<subseteq> ball x (e n) \<inter> U))" for n U
      {
        fix n U
        assume "infinite {n. f n \<in> U}"
        then have "\<exists>b\<in>k (e n). infinite {i\<in>{n. f n \<in> U}. f i \<in> ball b (e n)}"
          using k f by (intro pigeonhole_infinite_rel) (auto simp: subset_eq)
        then obtain a where
          "a \<in> k (e n)"
          "infinite {i \<in> {n. f n \<in> U}. f i \<in> ball a (e n)}" ..
        then have "\<exists>b. infinite {i. f i \<in> b} \<and> (\<exists>x. b \<subseteq> ball x (e n) \<inter> U)"
          by (intro exI[of _ "ball a (e n) \<inter> U"] exI[of _ a]) (auto simp: ac_simps)
        from someI_ex[OF this]
        have "infinite {i. f i \<in> B n U}" "\<exists>x. B n U \<subseteq> ball x (e n) \<inter> U"
          unfolding B_def by auto
      }
      note B = this

      define F where "F = rec_nat (B 0 UNIV) B"
      {
        fix n
        have "infinite {i. f i \<in> F n}"
          by (induct n) (auto simp: F_def B)
      }
      then have F: "\<And>n. \<exists>x. F (Suc n) \<subseteq> ball x (e n) \<inter> F n"
        using B by (simp add: F_def)
      then have F_dec: "\<And>m n. m \<le> n \<Longrightarrow> F n \<subseteq> F m"
        using decseq_SucI[of F] by (auto simp: decseq_def)

      obtain sel where sel: "\<And>k i. i < sel k i" "\<And>k i. f (sel k i) \<in> F k"
      proof (atomize_elim, unfold all_conj_distrib[symmetric], intro choice allI)
        fix k i
        have "infinite ({n. f n \<in> F k} - {.. i})"
          using \<open>infinite {n. f n \<in> F k}\<close> by auto
        from infinite_imp_nonempty[OF this]
        show "\<exists>x>i. f x \<in> F k"
          by (simp add: set_eq_iff not_le conj_commute)
      qed

      define t where "t = rec_nat (sel 0 0) (\<lambda>n i. sel (Suc n) i)"
      have "strict_mono t"
        unfolding strict_mono_Suc_iff by (simp add: t_def sel)
      moreover have "\<forall>i. (f \<circ> t) i \<in> S"
        using f by auto
      moreover
      have t: "(f \<circ> t) n \<in> F n" for n
        by (cases n) (simp_all add: t_def sel)

      have "Cauchy (f \<circ> t)"
      proof (safe intro!: metric_CauchyI exI elim!: nat_approx_posE)
        fix r :: real and N n m
        assume "1 / Suc N < r" "Suc N \<le> n" "Suc N \<le> m"
        then have "(f \<circ> t) n \<in> F (Suc N)" "(f \<circ> t) m \<in> F (Suc N)" "2 * e N < r"
          using F_dec t by (auto simp: e_def field_simps)
        with F[of N] obtain x where "dist x ((f \<circ> t) n) < e N" "dist x ((f \<circ> t) m) < e N"
          by (auto simp: subset_eq)
        with \<open>2 * e N < r\<close> show "dist ((f \<circ> t) m) ((f \<circ> t) n) < r"
          by metric
      qed

      ultimately show "\<exists>l\<in>S. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
        using assms unfolding complete_def by blast
    qed
  qed
qed (metis compact_imp_complete compact_imp_seq_compact seq_compact_imp_totally_bounded)

lemma cauchy_imp_bounded:
  assumes "Cauchy S"
  shows "bounded (range S)"
proof -
  from assms obtain N :: nat where "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (S m) (S n) < 1"
    by (meson Cauchy_def zero_less_one)
  then have N:"\<forall>n. N \<le> n \<longrightarrow> dist (S N) (S n) < 1" by auto
  moreover
  have "bounded (S ` {0..N})"
    using finite_imp_bounded[of "S ` {1..N}"] by auto
  then obtain a where a:"\<forall>x\<in>S ` {0..N}. dist (S N) x \<le> a"
    unfolding bounded_any_center [where a="S N"] by auto
  ultimately show "?thesis"
    unfolding bounded_any_center [where a="S N"]
    apply (intro exI [where x="max a 1"])
    apply (force simp: le_max_iff_disj less_le_not_le)
    done
qed

instance heine_borel < complete_space
proof
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then show "convergent f"
    unfolding convergent_def
    using Cauchy_converges_subseq cauchy_imp_bounded bounded_imp_convergent_subsequence by blast
qed

lemma complete_UNIV: "complete (UNIV :: ('a::complete_space) set)"
  by (meson Cauchy_convergent UNIV_I completeI convergent_def)

lemma complete_imp_closed:
  fixes S :: "'a::metric_space set"
  shows "complete S \<Longrightarrow> closed S"
  by (metis LIMSEQ_imp_Cauchy LIMSEQ_unique closed_sequential_limits completeE)

lemma complete_Int_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S" and "closed t"
  shows "complete (S \<inter> t)"
  by (metis Int_iff assms closed_sequentially completeE completeI)

lemma complete_closed_subset:
  fixes S :: "'a::metric_space set"
  assumes "closed S" and "S \<subseteq> t" and "complete t"
  shows "complete S"
  using assms complete_Int_closed [of t S] by (simp add: Int_absorb1)

lemma complete_eq_closed:
  fixes S :: "('a::complete_space) set"
  shows "complete S \<longleftrightarrow> closed S"
proof
  assume "closed S" then show "complete S"
    using subset_UNIV complete_UNIV by (rule complete_closed_subset)
next
  assume "complete S" then show "closed S"
    by (rule complete_imp_closed)
qed

lemma convergent_eq_Cauchy:
  fixes S :: "nat \<Rightarrow> 'a::complete_space"
  shows "(\<exists>l. (S \<longlongrightarrow> l) sequentially) \<longleftrightarrow> Cauchy S"
  unfolding Cauchy_convergent_iff convergent_def ..

lemma convergent_imp_bounded:
  fixes S :: "nat \<Rightarrow> 'a::metric_space"
  shows "(S \<longlongrightarrow> l) sequentially \<Longrightarrow> bounded (range S)"
  by (intro cauchy_imp_bounded LIMSEQ_imp_Cauchy)

lemma frontier_subset_compact:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<Longrightarrow> frontier S \<subseteq> S"
  using frontier_subset_closed compact_eq_bounded_closed
  by blast

lemma banach_fix_type:
  fixes f::"'a::complete_space\<Rightarrow>'a"
  assumes c:"0 \<le> c" "c < 1"
      and lipschitz:"\<forall>x. \<forall>y. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x. (f x = x)"
  using assms Banach_fix[OF complete_UNIV UNIV_not_empty c subset_UNIV, of f]
  by auto

section \<open>Cauchy continuity\<close>

definition Cauchy_continuous_on where
  "Cauchy_continuous_on \<equiv> \<lambda>S f. \<forall>\<sigma>. Cauchy \<sigma> \<longrightarrow> range \<sigma> \<subseteq> S \<longrightarrow> Cauchy (f \<circ> \<sigma>)"

lemma continuous_closed_imp_Cauchy_continuous:
  fixes S :: "('a::complete_space) set"
  shows "\<lbrakk>continuous_on S f; closed S\<rbrakk> \<Longrightarrow> Cauchy_continuous_on S f"
  unfolding Cauchy_continuous_on_def
  by (metis LIMSEQ_imp_Cauchy completeE complete_eq_closed continuous_on_sequentially range_subsetD)

lemma uniformly_continuous_imp_Cauchy_continuous:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  shows "uniformly_continuous_on S f \<Longrightarrow> Cauchy_continuous_on S f"
  by (simp add: uniformly_continuous_on_def Cauchy_continuous_on_def Cauchy_def image_subset_iff) metis

lemma Cauchy_continuous_on_imp_continuous:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "Cauchy_continuous_on S f"
  shows "continuous_on S f"
proof -
  have False if x: "\<forall>n. \<exists>x'\<in>S. dist x' x < inverse(Suc n) \<and> \<not> dist (f x') (f x) < \<epsilon>" "\<epsilon>>0" "x \<in> S" for x and \<epsilon>::real
  proof -
    obtain \<rho> where \<rho>: "\<forall>n. \<rho> n \<in> S" and dx: "\<forall>n. dist (\<rho> n) x < inverse(Suc n)" and dfx: "\<forall>n. \<not> dist (f (\<rho> n)) (f x) < \<epsilon>"
      using x by metis
    define \<sigma> where "\<sigma> \<equiv> \<lambda>n. if even n then \<rho> n else x"
    with \<rho> \<open>x \<in> S\<close> have "range \<sigma> \<subseteq> S"
      by auto
    have "\<sigma> \<longlonglongrightarrow> x"
      unfolding tendsto_iff
    proof (intro strip)
      fix e :: real
      assume "e>0"
      then obtain N where "inverse (Suc N) < e"
        using reals_Archimedean by blast
      then have "\<forall>n. N \<le> n \<longrightarrow> dist (\<rho> n) x < e"
        by (smt (verit, ccfv_SIG) dx inverse_Suc inverse_less_iff_less inverse_positive_iff_positive of_nat_Suc of_nat_mono)
      with \<open>e>0\<close> show "\<forall>\<^sub>F n in sequentially. dist (\<sigma> n) x < e"
        by (auto simp add: eventually_sequentially \<sigma>_def)
    qed
    then have "Cauchy \<sigma>"
      by (intro LIMSEQ_imp_Cauchy)
    then have Cf: "Cauchy (f \<circ> \<sigma>)"
      by (meson Cauchy_continuous_on_def \<open>range \<sigma> \<subseteq> S\<close> assms)
    have "(f \<circ> \<sigma>) \<longlonglongrightarrow> f x"
      unfolding tendsto_iff 
    proof (intro strip)
      fix e :: real
      assume "e>0"
      then obtain N where N: "\<forall>m\<ge>N. \<forall>n\<ge>N. dist ((f \<circ> \<sigma>) m) ((f \<circ> \<sigma>) n) < e"
        using Cf unfolding Cauchy_def by presburger
      moreover have "(f \<circ> \<sigma>) (Suc(N+N)) = f x"
        by (simp add: \<sigma>_def)
      ultimately have "\<forall>n\<ge>N. dist ((f \<circ> \<sigma>) n) (f x) < e"
        by (metis add_Suc le_add2)
      then show "\<forall>\<^sub>F n in sequentially. dist ((f \<circ> \<sigma>) n) (f x) < e"
        using eventually_sequentially by blast
    qed
    moreover have "\<And>n. \<not> dist (f (\<sigma> (2*n))) (f x) < \<epsilon>"
      using dfx by (simp add: \<sigma>_def)
    ultimately show False
      using \<open>\<epsilon>>0\<close> by (fastforce simp: mult_2 nat_le_iff_add tendsto_iff eventually_sequentially)
  qed
  then show ?thesis
    unfolding continuous_on_iff by (meson inverse_Suc)
qed


section\<^marker>\<open>tag unimportant\<close>\<open> Finite intersection property\<close>

text\<open>Also developed in HOL's toplogical spaces theory, but the Heine-Borel type class isn't available there.\<close>

lemma closed_imp_fip:
  fixes S :: "'a::heine_borel set"
  assumes "closed S"
      and T: "T \<in> \<F>" "bounded T"
      and clof: "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      and "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F>' \<noteq> {}"
    shows "S \<inter> \<Inter>\<F> \<noteq> {}"
proof -
  have "compact (S \<inter> T)"
    using \<open>closed S\<close> clof compact_eq_bounded_closed T by blast
  then have "(S \<inter> T) \<inter> \<Inter>\<F> \<noteq> {}"
    by (smt (verit, best) Inf_insert Int_assoc assms compact_imp_fip finite_insert insert_subset)
  then show ?thesis by blast
qed

lemma closed_imp_fip_compact:
  fixes S :: "'a::heine_borel set"
  shows
   "\<lbrakk>closed S; \<And>T. T \<in> \<F> \<Longrightarrow> compact T;
     \<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F>' \<noteq> {}\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}"
  by (metis closed_imp_fip compact_eq_bounded_closed equals0I finite.emptyI order.refl)

lemma closed_fip_Heine_Borel:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "T \<in> \<F>" "bounded T"
      and "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      and "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> \<Inter>\<F>' \<noteq> {}"
    shows "\<Inter>\<F> \<noteq> {}"
  using closed_imp_fip [OF closed_UNIV] assms by auto

lemma compact_fip_Heine_Borel:
  fixes \<F> :: "'a::heine_borel set set"
  assumes clof: "\<And>T. T \<in> \<F> \<Longrightarrow> compact T"
      and none: "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> \<Inter>\<F>' \<noteq> {}"
    shows "\<Inter>\<F> \<noteq> {}"
  by (metis InterI clof closed_fip_Heine_Borel compact_eq_bounded_closed equals0D none)

lemma compact_sequence_with_limit:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel"
  shows "f \<longlonglongrightarrow> l \<Longrightarrow> compact (insert l (range f))"
  by (simp add: closed_limpt compact_eq_bounded_closed convergent_imp_bounded islimpt_insert sequence_unique_limpt)


section \<open>Properties of Balls and Spheres\<close>

lemma compact_cball[simp]:
  fixes x :: "'a::heine_borel"
  shows "compact (cball x e)"
  using compact_eq_bounded_closed bounded_cball closed_cball by blast

lemma compact_frontier_bounded[intro]:
  fixes S :: "'a::heine_borel set"
  shows "bounded S \<Longrightarrow> compact (frontier S)"
  unfolding frontier_def
  using compact_eq_bounded_closed by blast

lemma compact_frontier[intro]:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<Longrightarrow> compact (frontier S)"
  using compact_eq_bounded_closed compact_frontier_bounded by blast

lemma no_limpt_imp_countable:
  assumes "\<And>z. \<not>z islimpt (X :: 'a :: {real_normed_vector, heine_borel} set)"
  shows   "countable X"
proof -
  have "countable (\<Union>n. cball 0 (real n) \<inter> X)"
  proof (intro countable_UN[OF _ countable_finite])
    fix n :: nat
    show "finite (cball 0 (real n) \<inter> X)"
      using assms by (intro finite_not_islimpt_in_compact) auto
  qed auto
  also have "(\<Union>n. cball 0 (real n)) = (UNIV :: 'a set)"
    by (force simp: real_arch_simple)
  hence "(\<Union>n. cball 0 (real n) \<inter> X) = X"
    by blast
  finally show "countable X" .
qed


section \<open>Distance from a Set\<close>

lemma distance_attains_sup:
  assumes "compact S" "S \<noteq> {}"
  shows "\<exists>x\<in>S. \<forall>y\<in>S. dist a y \<le> dist a x"
proof (rule continuous_attains_sup [OF assms])
  show "continuous_on S (dist a)"
    unfolding continuous_on
    using Lim_at_imp_Lim_at_within continuous_at_dist isCont_def by blast
qed

text \<open>For \emph{minimal} distance, we only need closure, not compactness.\<close>

lemma distance_attains_inf:
  fixes a :: "'a::heine_borel"
  assumes "closed S" and "S \<noteq> {}"
  obtains x where "x\<in>S" "\<And>y. y \<in> S \<Longrightarrow> dist a x \<le> dist a y"
proof -
  from assms obtain b where "b \<in> S" by auto
  let ?B = "S \<inter> cball a (dist b a)"
  have "?B \<noteq> {}" using \<open>b \<in> S\<close>
    by (auto simp: dist_commute)
  moreover have "continuous_on ?B (dist a)"
    by (auto intro!: continuous_at_imp_continuous_on continuous_dist continuous_ident continuous_const)
  moreover have "compact ?B"
    by (intro closed_Int_compact \<open>closed S\<close> compact_cball)
  ultimately obtain x where "x \<in> ?B" "\<forall>y\<in>?B. dist a x \<le> dist a y"
    by (metis continuous_attains_inf)
  with that show ?thesis by fastforce
qed


section \<open>Infimum Distance\<close>

definition\<^marker>\<open>tag important\<close> "infdist x A = (if A = {} then 0 else INF a\<in>A. dist x a)"

lemma bdd_below_image_dist[intro, simp]: "bdd_below (dist x ` A)"
  by (auto intro!: zero_le_dist)

lemma infdist_notempty: "A \<noteq> {} \<Longrightarrow> infdist x A = (INF a\<in>A. dist x a)"
  by (simp add: infdist_def)

lemma infdist_nonneg: "0 \<le> infdist x A"
  by (auto simp: infdist_def intro: cINF_greatest)

lemma infdist_le: "a \<in> A \<Longrightarrow> infdist x A \<le> dist x a"
  by (auto intro: cINF_lower simp add: infdist_def)

lemma infdist_le2: "a \<in> A \<Longrightarrow> dist x a \<le> d \<Longrightarrow> infdist x A \<le> d"
  by (auto intro!: cINF_lower2 simp add: infdist_def)

lemma infdist_zero[simp]: "a \<in> A \<Longrightarrow> infdist a A = 0"
  by (auto intro!: antisym infdist_nonneg infdist_le2)

lemma infdist_Un_min:
  assumes "A \<noteq> {}" "B \<noteq> {}"
  shows "infdist x (A \<union> B) = min (infdist x A) (infdist x B)"
using assms by (simp add: infdist_def cINF_union inf_real_def)

lemma infdist_triangle: "infdist x A \<le> infdist y A + dist x y"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: infdist_def)
next
  case False
  then obtain a where "a \<in> A" by auto
  have "infdist x A \<le> Inf {dist x y + dist y a |a. a \<in> A}"
  proof (rule cInf_greatest)
    from \<open>A \<noteq> {}\<close> show "{dist x y + dist y a |a. a \<in> A} \<noteq> {}"
      by simp
    fix d
    assume "d \<in> {dist x y + dist y a |a. a \<in> A}"
    then obtain a where d: "d = dist x y + dist y a" "a \<in> A"
      by auto
    show "infdist x A \<le> d"
      using infdist_notempty[OF \<open>A \<noteq> {}\<close>]
      by (metis d dist_commute dist_triangle3 infdist_le2)
  qed
  also have "\<dots> = dist x y + infdist y A"
  proof (rule cInf_eq, safe)
    fix a
    assume "a \<in> A"
    then show "dist x y + infdist y A \<le> dist x y + dist y a"
      by (auto intro: infdist_le)
  next
    fix i
    assume inf: "\<And>d. d \<in> {dist x y + dist y a |a. a \<in> A} \<Longrightarrow> i \<le> d"
    then have "i - dist x y \<le> infdist y A"
      unfolding infdist_notempty[OF \<open>A \<noteq> {}\<close>] using \<open>a \<in> A\<close>
      by (intro cINF_greatest) (auto simp: field_simps)
    then show "i \<le> dist x y + infdist y A"
      by simp
  qed
  finally show ?thesis by simp
qed

lemma infdist_triangle_abs: "\<bar>infdist x A - infdist y A\<bar> \<le> dist x y"
  by (metis abs_diff_le_iff diff_le_eq dist_commute infdist_triangle)

lemma in_closure_iff_infdist_zero:
  assumes "A \<noteq> {}"
  shows "x \<in> closure A \<longleftrightarrow> infdist x A = 0"
proof
  assume "x \<in> closure A"
  show "infdist x A = 0"
  proof (rule ccontr)
    assume "infdist x A \<noteq> 0"
    with infdist_nonneg[of x A] have "infdist x A > 0"
      by auto
    then have "ball x (infdist x A) \<inter> closure A = {}"
      by (meson \<open>x \<in> closure A\<close> closure_approachableD infdist_le linorder_not_le)
    then have "x \<notin> closure A"
      by (metis \<open>0 < infdist x A\<close> centre_in_ball disjoint_iff_not_equal)
    then show False using \<open>x \<in> closure A\<close> by simp
  qed
next
  assume x: "infdist x A = 0"
  then obtain a where "a \<in> A"
    by atomize_elim (metis all_not_in_conv assms)
  have False if "e > 0" "\<not> (\<exists>y\<in>A. dist y x < e)" for e
  proof -
    have "infdist x A \<ge> e" using \<open>a \<in> A\<close>
      unfolding infdist_def using that
      by (force simp: dist_commute intro: cINF_greatest)
    with x \<open>e > 0\<close> show False by auto
  qed
  then show "x \<in> closure A"
    using closure_approachable by blast
qed

lemma in_closed_iff_infdist_zero:
  assumes "closed A" "A \<noteq> {}"
  shows "x \<in> A \<longleftrightarrow> infdist x A = 0"
  by (metis assms closure_closed in_closure_iff_infdist_zero)

lemma infdist_pos_not_in_closed:
  assumes "closed S" "S \<noteq> {}" "x \<notin> S"
  shows "infdist x S > 0"
  by (meson assms dual_order.order_iff_strict in_closed_iff_infdist_zero infdist_nonneg)

lemma
  infdist_attains_inf:
  fixes X::"'a::heine_borel set"
  assumes "closed X"
  assumes "X \<noteq> {}"
  obtains x where "x \<in> X" "infdist y X = dist y x"
proof -
  have "bdd_below (dist y ` X)"
    by auto
  from distance_attains_inf[OF assms, of y]
  obtain x where "x \<in> X" "\<And>z. z \<in> X \<Longrightarrow> dist y x \<le> dist y z" by auto
  then have "infdist y X = dist y x"
    by (metis antisym assms(2) cINF_greatest infdist_def infdist_le)
  with \<open>x \<in> X\<close> show ?thesis ..
qed


text \<open>Every metric space is a T4 space:\<close>

instance metric_space \<subseteq> t4_space
proof
  fix S T::"'a set" assume H: "closed S" "closed T" "S \<inter> T = {}"
  consider "S = {}" | "T = {}" | "S \<noteq> {} \<and> T \<noteq> {}" by auto
  then show "\<exists>U V. open U \<and> open V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> U \<inter> V = {}"
  proof (cases)
    case 1 then show ?thesis by blast
  next
    case 2 then show ?thesis by blast
  next
    case 3
    define U where "U = (\<Union>x\<in>S. ball x ((infdist x T)/2))"
    have A: "open U" unfolding U_def by auto
    have "infdist x T > 0" if "x \<in> S" for x
      using H that 3 by (auto intro!: infdist_pos_not_in_closed)
    then have B: "S \<subseteq> U" unfolding U_def by auto
    define V where "V = (\<Union>x\<in>T. ball x ((infdist x S)/2))"
    have C: "open V" unfolding V_def by auto
    have "infdist x S > 0" if "x \<in> T" for x
      using H that 3 by (auto intro!: infdist_pos_not_in_closed)
    then have D: "T \<subseteq> V" unfolding V_def by auto

    have "(ball x ((infdist x T)/2)) \<inter> (ball y ((infdist y S)/2)) = {}" if "x \<in> S" "y \<in> T" for x y
    proof auto
      fix z assume H: "dist x z * 2 < infdist x T" "dist y z * 2 < infdist y S"
      have "2 * dist x y \<le> 2 * dist x z + 2 * dist y z"
        by metric
      also have "... < infdist x T + infdist y S"
        using H by auto
      finally have "dist x y < infdist x T \<or> dist x y < infdist y S"
        by auto
      then show False
        using infdist_le[OF \<open>x \<in> S\<close>, of y] infdist_le[OF \<open>y \<in> T\<close>, of x] by (auto simp add: dist_commute)
    qed
    then have E: "U \<inter> V = {}"
      unfolding U_def V_def by auto
    show ?thesis
      using A B C D E by blast
  qed
qed

lemma tendsto_infdist [tendsto_intros]:
  assumes f: "(f \<longlongrightarrow> l) F"
  shows "((\<lambda>x. infdist (f x) A) \<longlongrightarrow> infdist l A) F"
proof (rule tendstoI)
  fix e ::real
  assume "e > 0"
  from tendstoD[OF f this]
  show "eventually (\<lambda>x. dist (infdist (f x) A) (infdist l A) < e) F"
  proof (eventually_elim)
    fix x
    from infdist_triangle[of l A "f x"] infdist_triangle[of "f x" A l]
    have "dist (infdist (f x) A) (infdist l A) \<le> dist (f x) l"
      by (simp add: dist_commute dist_real_def)
    also assume "dist (f x) l < e"
    finally show "dist (infdist (f x) A) (infdist l A) < e" .
  qed
qed

lemma continuous_infdist[continuous_intros]:
  assumes "continuous F f"
  shows "continuous F (\<lambda>x. infdist (f x) A)"
  using assms unfolding continuous_def by (rule tendsto_infdist)

lemma continuous_on_infdist [continuous_intros]:
  assumes "continuous_on S f"
  shows "continuous_on S (\<lambda>x. infdist (f x) A)"
using assms unfolding continuous_on by (auto intro: tendsto_infdist)

lemma compact_infdist_le:
  fixes A::"'a::heine_borel set"
  assumes "A \<noteq> {}"
  assumes "compact A"
  assumes "e > 0"
  shows "compact {x. infdist x A \<le> e}"
proof -
  from continuous_closed_vimage[of "{0..e}" "\<lambda>x. infdist x A"]
    continuous_infdist[OF continuous_ident, of _ UNIV A]
  have "closed {x. infdist x A \<le> e}" by (auto simp: vimage_def infdist_nonneg)
  moreover
  from assms obtain x0 b where b: "\<And>x. x \<in> A \<Longrightarrow> dist x0 x \<le> b" "closed A"
    by (auto simp: compact_eq_bounded_closed bounded_def)
  {
    fix y
    assume "infdist y A \<le> e"
    moreover
    from infdist_attains_inf[OF \<open>closed A\<close> \<open>A \<noteq> {}\<close>, of y]
    obtain z where "z \<in> A" "infdist y A = dist y z" by blast
    ultimately
    have "dist x0 y \<le> b + e" using b by metric
  } then
  have "bounded {x. infdist x A \<le> e}"
    by (auto simp: bounded_any_center[where a=x0] intro!: exI[where x="b + e"])
  ultimately show "compact {x. infdist x A \<le> e}"
    by (simp add: compact_eq_bounded_closed)
qed


section \<open>Separation between Points and Sets\<close>

proposition separate_point_closed:
  fixes S :: "'a::heine_borel set"
  assumes "closed S" and "a \<notin> S"
  shows "\<exists>d>0. \<forall>x\<in>S. d \<le> dist a x"
  by (metis assms distance_attains_inf empty_iff gt_ex zero_less_dist_iff)

proposition separate_compact_closed:
  fixes S T :: "'a::heine_borel set"
  assumes "compact S"
    and T: "closed T" "S \<inter> T = {}"
  shows "\<exists>d>0. \<forall>x\<in>S. \<forall>y\<in>T. d \<le> dist x y"
proof cases
  assume "S \<noteq> {} \<and> T \<noteq> {}"
  then have "S \<noteq> {}" "T \<noteq> {}" by auto
  let ?inf = "\<lambda>x. infdist x T"
  have "continuous_on S ?inf"
    by (auto intro!: continuous_at_imp_continuous_on continuous_infdist continuous_ident)
  then obtain x where x: "x \<in> S" "\<forall>y\<in>S. ?inf x \<le> ?inf y"
    using continuous_attains_inf[OF \<open>compact S\<close> \<open>S \<noteq> {}\<close>] by auto
  then have "0 < ?inf x"
    using T \<open>T \<noteq> {}\<close> in_closed_iff_infdist_zero by (auto simp: less_le infdist_nonneg)
  moreover have "\<forall>x'\<in>S. \<forall>y\<in>T. ?inf x \<le> dist x' y"
    using x by (auto intro: order_trans infdist_le)
  ultimately show ?thesis by auto
qed (auto intro!: exI[of _ 1])

proposition separate_closed_compact:
  fixes S T :: "'a::heine_borel set"
  assumes S: "closed S"
    and T: "compact T"
    and dis: "S \<inter> T = {}"
  shows "\<exists>d>0. \<forall>x\<in>S. \<forall>y\<in>T. d \<le> dist x y"
  by (metis separate_compact_closed[OF T S] dis dist_commute inf_commute)

proposition compact_in_open_separated:
  fixes A::"'a::heine_borel set"
  assumes A: "A \<noteq> {}" "compact A"
  assumes "open B"
  assumes "A \<subseteq> B"
  obtains e where "e > 0" "{x. infdist x A \<le> e} \<subseteq> B"
proof atomize_elim
  have "closed (- B)" "compact A" "- B \<inter> A = {}"
    using assms by (auto simp: open_Diff compact_eq_bounded_closed)
  from separate_closed_compact[OF this]
  obtain d'::real where d': "d'>0" "\<And>x y. x \<notin> B \<Longrightarrow> y \<in> A \<Longrightarrow> d' \<le> dist x y"
    by auto
  define d where "d = d' / 2"
  hence "d>0" "d < d'" using d' by auto
  with d' have d: "\<And>x y. x \<notin> B \<Longrightarrow> y \<in> A \<Longrightarrow> d < dist x y"
    by force
  show "\<exists>e>0. {x. infdist x A \<le> e} \<subseteq> B"
  proof (rule ccontr)
    assume "\<nexists>e. 0 < e \<and> {x. infdist x A \<le> e} \<subseteq> B"
    with \<open>d > 0\<close> obtain x where x: "infdist x A \<le> d" "x \<notin> B"
      by auto
    then show False
      by (metis A compact_eq_bounded_closed infdist_attains_inf x d linorder_not_less)
  qed
qed


section \<open>Uniform Continuity\<close>

lemma uniformly_continuous_onE:
  assumes "uniformly_continuous_on s f" "0 < e"
  obtains d where "d>0" "\<And>x x'. \<lbrakk>x\<in>s; x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms
  by (auto simp: uniformly_continuous_on_def)

lemma uniformly_continuous_on_sequentially:
  "uniformly_continuous_on s f \<longleftrightarrow> (\<forall>x y. (\<forall>n. x n \<in> s) \<and> (\<forall>n. y n \<in> s) \<and>
    (\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0 \<longrightarrow> (\<lambda>n. dist (f(x n)) (f(y n))) \<longlonglongrightarrow> 0)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix x y
    assume x: "\<forall>n. x n \<in> s"
      and y: "\<forall>n. y n \<in> s"
      and xy: "((\<lambda>n. dist (x n) (y n)) \<longlongrightarrow> 0) sequentially"
    {
      fix e :: real
      assume "e > 0"
      then obtain d where "d > 0" and d: "\<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
        by (metis \<open>?lhs\<close> uniformly_continuous_onE)
      obtain N where N: "\<forall>n\<ge>N. dist (x n) (y n) < d"
        using xy[unfolded lim_sequentially dist_norm] and \<open>d>0\<close> by auto
      then have "\<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
        using d x y by blast
    }
    then have "((\<lambda>n. dist (f(x n)) (f(y n))) \<longlongrightarrow> 0) sequentially"
      unfolding lim_sequentially and dist_real_def by auto
  }
  then show ?rhs by auto
next
  assume ?rhs
  {
    assume "\<not> ?lhs"
    then obtain e where "e > 0" "\<forall>d>0. \<exists>x\<in>s. \<exists>x'\<in>s. dist x' x < d \<and> \<not> dist (f x') (f x) < e"
      unfolding uniformly_continuous_on_def by auto
    then obtain fa where fa:
      "\<forall>x. 0 < x \<longrightarrow> fst (fa x) \<in> s \<and> snd (fa x) \<in> s \<and> dist (fst (fa x)) (snd (fa x)) < x \<and> \<not> dist (f (fst (fa x))) (f (snd (fa x))) < e"
      using choice[of "\<lambda>d x. d>0 \<longrightarrow> fst x \<in> s \<and> snd x \<in> s \<and> dist (snd x) (fst x) < d \<and> \<not> dist (f (snd x)) (f (fst x)) < e"]
      by (auto simp: Bex_def dist_commute)
    define x where "x n = fst (fa (inverse (real n + 1)))" for n
    define y where "y n = snd (fa (inverse (real n + 1)))" for n
    have xyn: "\<forall>n. x n \<in> s \<and> y n \<in> s"
      and xy0: "\<forall>n. dist (x n) (y n) < inverse (real n + 1)"
      and fxy:"\<forall>n. \<not> dist (f (x n)) (f (y n)) < e"
      unfolding x_def and y_def using fa
      by auto
    {
      fix e :: real
      assume "e > 0"
      then obtain N :: nat where "N \<noteq> 0" and N: "0 < inverse (real N) \<and> inverse (real N) < e"
        unfolding real_arch_inverse[of e] by auto
      with xy0 have "\<exists>N. \<forall>n\<ge>N. dist (x n) (y n) < e"
        by (metis order.strict_trans inverse_positive_iff_positive less_imp_inverse_less
            nat_le_real_less)
    }
    then have "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
      using \<open>?rhs\<close>[THEN spec[where x=x], THEN spec[where x=y]] and xyn
      unfolding lim_sequentially dist_real_def by auto
    then have False using fxy and \<open>e>0\<close> by auto
  }
  then show ?lhs
    unfolding uniformly_continuous_on_def by blast
qed


section \<open>Continuity on a Compact Domain Implies Uniform Continuity\<close>

text\<open>From the proof of the Heine-Borel theorem: Lemma 2 in section 3.7, page 69 of
J. C. Burkill and H. Burkill. A Second Course in Mathematical Analysis (CUP, 2002)\<close>

lemma Heine_Borel_lemma:
  assumes "compact S" and Ssub: "S \<subseteq> \<Union>\<G>" and opn: "\<And>G. G \<in> \<G> \<Longrightarrow> open G"
  obtains e where "0 < e" "\<And>x. x \<in> S \<Longrightarrow> \<exists>G \<in> \<G>. ball x e \<subseteq> G"
proof -
  have False if neg: "\<And>e. 0 < e \<Longrightarrow> \<exists>x \<in> S. \<forall>G \<in> \<G>. \<not> ball x e \<subseteq> G"
  proof -
    have "\<exists>x \<in> S. \<forall>G \<in> \<G>. \<not> ball x (1 / Suc n) \<subseteq> G" for n
      using neg by simp
    then obtain f where "\<And>n. f n \<in> S" and fG: "\<And>G n. G \<in> \<G> \<Longrightarrow> \<not> ball (f n) (1 / Suc n) \<subseteq> G"
      by metis
    then obtain l r where "l \<in> S" "strict_mono r" and to_l: "(f \<circ> r) \<longlonglongrightarrow> l"
      using \<open>compact S\<close> compact_def that by metis
    then obtain G where "l \<in> G" "G \<in> \<G>"
      using Ssub by auto
    then obtain e where "0 < e" and e: "\<And>z. dist z l < e \<Longrightarrow> z \<in> G"
      using opn open_dist by blast
    obtain N1 where N1: "\<And>n. n \<ge> N1 \<Longrightarrow> dist (f (r n)) l < e/2"
      by (metis \<open>0 < e\<close> half_gt_zero lim_sequentially o_apply to_l)
    obtain N2 where N2: "of_nat N2 > 2/e"
      using reals_Archimedean2 by blast
    obtain x where "x \<in> ball (f (r (max N1 N2))) (1 / real (Suc (r (max N1 N2))))" and "x \<notin> G"
      using fG [OF \<open>G \<in> \<G>\<close>, of "r (max N1 N2)"] by blast
    then have "dist (f (r (max N1 N2))) x < 1 / real (Suc (r (max N1 N2)))"
      by simp
    also have "... \<le> 1 / real (Suc (max N1 N2))"
      by (meson Suc_le_mono \<open>strict_mono r\<close> inverse_of_nat_le nat.discI seq_suble)
    also have "... \<le> 1 / real (Suc N2)"
      by (simp add: field_simps)
    also have "... < e/2"
      using N2 \<open>0 < e\<close> by (simp add: field_simps)
    finally have "dist (f (r (max N1 N2))) x < e/2" .
    moreover have "dist (f (r (max N1 N2))) l < e/2"
      using N1 max.cobounded1 by blast
    ultimately have "dist x l < e"
      by metric
    then show ?thesis
      using e \<open>x \<notin> G\<close> by blast
  qed
  then show ?thesis
    by (meson that)
qed

lemma compact_uniformly_equicontinuous:
  assumes "compact S"
      and cont: "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk>
                        \<Longrightarrow> \<exists>d. 0 < d \<and>
                                (\<forall>f \<in> \<F>. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
      and "0 < e"
  obtains d where "0 < d"
                  "\<And>f x x'. \<lbrakk>f \<in> \<F>; x \<in> S; x' \<in> S; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
proof -
  obtain d where d_pos: "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk> \<Longrightarrow> 0 < d x e"
     and d_dist : "\<And>x x' e f. \<lbrakk>dist x' x < d x e; x \<in> S; x' \<in> S; 0 < e; f \<in> \<F>\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
    using cont by metis
  let ?\<G> = "((\<lambda>x. ball x (d x (e/2))) ` S)"
  have Ssub: "S \<subseteq> \<Union> ?\<G>"
    using \<open>0 < e\<close> d_pos by auto
  then obtain k where "0 < k" and k: "\<And>x. x \<in> S \<Longrightarrow> \<exists>G \<in> ?\<G>. ball x k \<subseteq> G"
    by (rule Heine_Borel_lemma [OF \<open>compact S\<close>]) auto
  moreover have "dist (f v) (f u) < e" if "f \<in> \<F>" "u \<in> S" "v \<in> S" "dist v u < k" for f u v
  proof -
    obtain G where "G \<in> ?\<G>" "u \<in> G" "v \<in> G"
      using k that
      by (metis \<open>dist v u < k\<close> \<open>u \<in> S\<close> \<open>0 < k\<close> centre_in_ball subsetD dist_commute mem_ball)
    then obtain w where w: "dist w u < d w (e/2)" "dist w v < d w (e/2)" "w \<in> S"
      by auto
    with that d_dist have "dist (f w) (f v) < e/2"
      by (metis \<open>0 < e\<close> dist_commute half_gt_zero)
    moreover
    have "dist (f w) (f u) < e/2"
      using that d_dist w by (metis \<open>0 < e\<close> dist_commute divide_pos_pos zero_less_numeral)
    ultimately show ?thesis
      using dist_triangle_half_r by blast
  qed
  ultimately show ?thesis using that by blast
qed

corollary compact_uniformly_continuous:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: metric_space"
  assumes f: "continuous_on S f" and S: "compact S"
  shows "uniformly_continuous_on S f"
  using f
    unfolding continuous_on_iff uniformly_continuous_on_def
    by (force intro: compact_uniformly_equicontinuous [OF S, of "{f}"])


section\<^marker>\<open>tag unimportant\<close>\<open> Theorems relating continuity and uniform continuity to closures\<close>

lemma continuous_on_closure:
   "continuous_on (closure S) f \<longleftrightarrow>
    (\<forall>x e. x \<in> closure S \<and> 0 < e
           \<longrightarrow> (\<exists>d. 0 < d \<and> (\<forall>y. y \<in> S \<and> dist y x < d \<longrightarrow> dist (f y) (f x) < e)))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    unfolding continuous_on_iff  by (metis Un_iff closure_def)
next
  assume R [rule_format]: ?rhs
  show ?lhs
  proof
    fix x and e::real
    assume "0 < e" and x: "x \<in> closure S"
    obtain \<delta>::real where "\<delta> > 0"
                   and \<delta>: "\<And>y. \<lbrakk>y \<in> S; dist y x < \<delta>\<rbrakk> \<Longrightarrow> dist (f y) (f x) < e/2"
      using R [of x "e/2"] \<open>0 < e\<close> x by auto
    have "dist (f y) (f x) \<le> e" if y: "y \<in> closure S" and dyx: "dist y x < \<delta>/2" for y
    proof -
      obtain \<delta>'::real where "\<delta>' > 0"
                      and \<delta>': "\<And>z. \<lbrakk>z \<in> S; dist z y < \<delta>'\<rbrakk> \<Longrightarrow> dist (f z) (f y) < e/2"
        using R [of y "e/2"] \<open>0 < e\<close> y by auto
      obtain z where "z \<in> S" and z: "dist z y < min \<delta>' \<delta> / 2"
        using closure_approachable y
        by (metis \<open>0 < \<delta>'\<close> \<open>0 < \<delta>\<close> divide_pos_pos min_less_iff_conj zero_less_numeral)
      have "dist (f z) (f y) < e/2"
        using \<delta>' [OF \<open>z \<in> S\<close>] z \<open>0 < \<delta>'\<close> by metric
      moreover have "dist (f z) (f x) < e/2"
        using \<delta>[OF \<open>z \<in> S\<close>] z dyx by metric
      ultimately show ?thesis
        by metric
    qed
    then show "\<exists>d>0. \<forall>x'\<in>closure S. dist x' x < d \<longrightarrow> dist (f x') (f x) \<le> e"
      by (rule_tac x="\<delta>/2" in exI) (simp add: \<open>\<delta> > 0\<close>)
  qed
qed

lemma continuous_on_closure_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b :: metric_space"
  shows
   "continuous_on (closure S) f \<longleftrightarrow>
    (\<forall>x a. a \<in> closure S \<and> (\<forall>n. x n \<in> S) \<and> x \<longlonglongrightarrow> a \<longrightarrow> (f \<circ> x) \<longlonglongrightarrow> f a)"
   (is "?lhs = ?rhs")
proof -
  have "continuous_on (closure S) f \<longleftrightarrow>
           (\<forall>x \<in> closure S. continuous (at x within S) f)"
    by (force simp: continuous_on_closure continuous_within_eps_delta)
  also have "... = ?rhs"
    by (force simp: continuous_within_sequentially)
  finally show ?thesis .
qed

lemma uniformly_continuous_on_closure:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes ucont: "uniformly_continuous_on S f"
      and cont: "continuous_on (closure S) f"
    shows "uniformly_continuous_on (closure S) f"
unfolding uniformly_continuous_on_def
proof (intro allI impI)
  fix e::real
  assume "0 < e"
  then obtain d::real
    where "d>0"
      and d: "\<And>x x'. \<lbrakk>x\<in>S; x'\<in>S; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e/3"
    using ucont [unfolded uniformly_continuous_on_def, rule_format, of "e/3"] by auto
  show "\<exists>d>0. \<forall>x\<in>closure S. \<forall>x'\<in>closure S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
  proof (rule exI [where x="d/3"], clarsimp simp: \<open>d > 0\<close>)
    fix x y
    assume x: "x \<in> closure S" and y: "y \<in> closure S" and dyx: "dist y x * 3 < d"
    obtain d1::real where "d1 > 0"
           and d1: "\<And>w. \<lbrakk>w \<in> closure S; dist w x < d1\<rbrakk> \<Longrightarrow> dist (f w) (f x) < e/3"
      using cont [unfolded continuous_on_iff, rule_format, of "x" "e/3"] \<open>0 < e\<close> x by auto
     obtain x' where "x' \<in> S" and x': "dist x' x < min d1 (d / 3)"
        using closure_approachable [of x S]
        by (metis \<open>0 < d1\<close> \<open>0 < d\<close> divide_pos_pos min_less_iff_conj x zero_less_numeral)
    obtain d2::real where "d2 > 0"
           and d2: "\<forall>w \<in> closure S. dist w y < d2 \<longrightarrow> dist (f w) (f y) < e/3"
      using cont [unfolded continuous_on_iff, rule_format, of "y" "e/3"] \<open>0 < e\<close> y by auto
    obtain y' where "y' \<in> S" and y': "dist y' y < min d2 (d / 3)"
      using closure_approachable [of y S]
      by (metis \<open>0 < d2\<close> \<open>0 < d\<close> divide_pos_pos min_less_iff_conj y zero_less_numeral)
    have "dist x' x < d/3" using x' by auto
    then have "dist x' y' < d"
      using dyx y' by metric
    then have "dist (f x') (f y') < e/3"
      by (rule d [OF \<open>y' \<in> S\<close> \<open>x' \<in> S\<close>])
    moreover have "dist (f x') (f x) < e/3" using \<open>x' \<in> S\<close> closure_subset x' d1
      by (simp add: closure_def)
    moreover have "dist (f y') (f y) < e/3" using \<open>y' \<in> S\<close> closure_subset y' d2
      by (simp add: closure_def)
    ultimately show "dist (f y) (f x) < e" by metric
  qed
qed

lemma uniformly_continuous_on_extension_at_closure:
  fixes f::"'a::metric_space \<Rightarrow> 'b::complete_space"
  assumes uc: "uniformly_continuous_on X f"
  assumes "x \<in> closure X"
  obtains l where "(f \<longlongrightarrow> l) (at x within X)"
proof -
  from assms obtain xs where xs: "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X"
    by (auto simp: closure_sequential)

  from uniformly_continuous_on_Cauchy[OF uc LIMSEQ_imp_Cauchy, OF xs]
  obtain l where l: "(\<lambda>n. f (xs n)) \<longlonglongrightarrow> l"
    by atomize_elim (simp only: convergent_eq_Cauchy)

  have "(f \<longlongrightarrow> l) (at x within X)"
  proof (clarify intro!: Lim_within_LIMSEQ)
    fix xs'
    assume "\<forall>n. xs' n \<noteq> x \<and> xs' n \<in> X"
      and xs': "xs' \<longlonglongrightarrow> x"
    then have "xs' n \<noteq> x" "xs' n \<in> X" for n by auto

    from uniformly_continuous_on_Cauchy[OF uc LIMSEQ_imp_Cauchy, OF \<open>xs' \<longlonglongrightarrow> x\<close> \<open>xs' _ \<in> X\<close>]
    obtain l' where l': "(\<lambda>n. f (xs' n)) \<longlonglongrightarrow> l'"
      by atomize_elim (simp only: convergent_eq_Cauchy)

    show "(\<lambda>n. f (xs' n)) \<longlonglongrightarrow> l"
    proof (rule tendstoI)
      fix e::real assume "e > 0"
      define e' where "e' \<equiv> e/2"
      have "e' > 0" using \<open>e > 0\<close> by (simp add: e'_def)

      have "\<forall>\<^sub>F n in sequentially. dist (f (xs n)) l < e'"
        by (simp add: \<open>0 < e'\<close> l tendstoD)
      moreover
      from uc[unfolded uniformly_continuous_on_def, rule_format, OF \<open>e' > 0\<close>]
      obtain d where d: "d > 0" "\<And>x x'. x \<in> X \<Longrightarrow> x' \<in> X \<Longrightarrow> dist x x' < d \<Longrightarrow> dist (f x) (f x') < e'"
        by auto
      have "\<forall>\<^sub>F n in sequentially. dist (xs n) (xs' n) < d"
        by (auto intro!: \<open>0 < d\<close> order_tendstoD tendsto_eq_intros xs xs')
      ultimately
      show "\<forall>\<^sub>F n in sequentially. dist (f (xs' n)) l < e"
      proof eventually_elim
        case (elim n)
        have "dist (f (xs' n)) l \<le> dist (f (xs n)) (f (xs' n)) + dist (f (xs n)) l"
          by metric
        also have "dist (f (xs n)) (f (xs' n)) < e'"
          by (auto intro!: d xs \<open>xs' _ \<in> _\<close> elim)
        also note \<open>dist (f (xs n)) l < e'\<close>
        also have "e' + e' = e" by (simp add: e'_def)
        finally show ?case by simp
      qed
    qed
  qed
  thus ?thesis ..
qed

lemma uniformly_continuous_on_extension_on_closure:
  fixes f::"'a::metric_space \<Rightarrow> 'b::complete_space"
  assumes uc: "uniformly_continuous_on X f"
  obtains g where "uniformly_continuous_on (closure X) g" "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
    "\<And>Y h x. X \<subseteq> Y \<Longrightarrow> Y \<subseteq> closure X \<Longrightarrow> continuous_on Y h \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f x = h x) \<Longrightarrow> x \<in> Y \<Longrightarrow> h x = g x"
proof -
  from uc have cont_f: "continuous_on X f"
    by (simp add: uniformly_continuous_imp_continuous)
  obtain y where y: "(f \<longlongrightarrow> y x) (at x within X)" if "x \<in> closure X" for x
    using uniformly_continuous_on_extension_at_closure[OF assms] by meson
  let ?g = "\<lambda>x. if x \<in> X then f x else y x"

  have "uniformly_continuous_on (closure X) ?g"
    unfolding uniformly_continuous_on_def
  proof safe
    fix e::real assume "e > 0"
    define e' where "e' \<equiv> e / 3"
    have "e' > 0" using \<open>e > 0\<close> by (simp add: e'_def)
    from uc[unfolded uniformly_continuous_on_def, rule_format, OF \<open>0 < e'\<close>]
    obtain d where "d > 0" and d: "\<And>x x'. x \<in> X \<Longrightarrow> x' \<in> X \<Longrightarrow> dist x' x < d \<Longrightarrow> dist (f x') (f x) < e'"
      by auto
    define d' where "d' = d / 3"
    have "d' > 0" using \<open>d > 0\<close> by (simp add: d'_def)
    show "\<exists>d>0. \<forall>x\<in>closure X. \<forall>x'\<in>closure X. dist x' x < d \<longrightarrow> dist (?g x') (?g x) < e"
    proof (safe intro!: exI[where x=d'] \<open>d' > 0\<close>)
      fix x x' assume x: "x \<in> closure X" and x': "x' \<in> closure X" and dist: "dist x' x < d'"
      then obtain xs xs' where xs: "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X"
        and xs': "xs' \<longlonglongrightarrow> x'" "\<And>n. xs' n \<in> X"
        by (auto simp: closure_sequential)
      have "\<forall>\<^sub>F n in sequentially. dist (xs' n) x' < d'"
        and "\<forall>\<^sub>F n in sequentially. dist (xs n) x < d'"
        by (auto intro!: \<open>0 < d'\<close> order_tendstoD tendsto_eq_intros xs xs')
      moreover
      have "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> y x" if "x \<in> closure X" "x \<notin> X" "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X" for xs x
        using that not_eventuallyD
        by (force intro!: filterlim_compose[OF y[OF \<open>x \<in> closure X\<close>]] simp: filterlim_at)
      then have "(\<lambda>x. f (xs' x)) \<longlonglongrightarrow> ?g x'" "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> ?g x"
        using x x'
        by (auto intro!: continuous_on_tendsto_compose[OF cont_f] simp: xs' xs)
      then have "\<forall>\<^sub>F n in sequentially. dist (f (xs' n)) (?g x') < e'"
        "\<forall>\<^sub>F n in sequentially. dist (f (xs n)) (?g x) < e'"
        by (auto intro!: \<open>0 < e'\<close> order_tendstoD tendsto_eq_intros)
      ultimately
      have "\<forall>\<^sub>F n in sequentially. dist (?g x') (?g x) < e"
      proof eventually_elim
        case (elim n)
        have "dist (?g x') (?g x) \<le>
          dist (f (xs' n)) (?g x') + dist (f (xs' n)) (f (xs n)) + dist (f (xs n)) (?g x)"
          by (metis add.commute add_le_cancel_left dist_commute dist_triangle dist_triangle_le)
        also
        from \<open>dist (xs' n) x' < d'\<close> \<open>dist x' x < d'\<close> \<open>dist (xs n) x < d'\<close>
        have "dist (xs' n) (xs n) < d" unfolding d'_def by metric
        with \<open>xs _ \<in> X\<close> \<open>xs' _ \<in> X\<close> have "dist (f (xs' n)) (f (xs n)) < e'"
          by (rule d)
        also note \<open>dist (f (xs' n)) (?g x') < e'\<close>
        also note \<open>dist (f (xs n)) (?g x) < e'\<close>
        finally show ?case by (simp add: e'_def)
      qed
      then show "dist (?g x') (?g x) < e" by simp
    qed
  qed
  moreover have "f x = ?g x" if "x \<in> X" for x using that by simp
  moreover
  {
    fix Y h x
    assume Y: "x \<in> Y" "X \<subseteq> Y" "Y \<subseteq> closure X" and cont_h: "continuous_on Y h"
      and extension: "(\<And>x. x \<in> X \<Longrightarrow> f x = h x)"
    {
      assume "x \<notin> X"
      have "x \<in> closure X" using Y by auto
      then obtain xs where xs: "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X"
        by (auto simp: closure_sequential)
      from continuous_on_tendsto_compose[OF cont_h xs(1)] xs(2) Y
      have hx: "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> h x"
        by (auto simp: subsetD extension)
      then have "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> y x"
        using \<open>x \<notin> X\<close> not_eventuallyD xs(2)
        by (force intro!: filterlim_compose[OF y[OF \<open>x \<in> closure X\<close>]] simp: filterlim_at xs)
      with hx have "h x = y x" by (rule LIMSEQ_unique)
    } then
    have "h x = ?g x"
      using extension by auto
  }
  ultimately show ?thesis ..
qed

lemma bounded_uniformly_continuous_image:
  fixes f :: "'a :: heine_borel \<Rightarrow> 'b :: heine_borel"
  assumes "uniformly_continuous_on S f" "bounded S"
  shows "bounded(f ` S)"
  by (metis (no_types) assms bounded_closure_image compact_closure compact_continuous_image compact_eq_bounded_closed image_cong uniformly_continuous_imp_continuous uniformly_continuous_on_extension_on_closure)


section \<open>With Abstract Topology (TODO: move and remove dependency?)\<close>

lemma openin_contains_ball:
    "openin (top_of_set T) S \<longleftrightarrow>
     S \<subseteq> T \<and> (\<forall>x \<in> S. \<exists>e. 0 < e \<and> ball x e \<inter> T \<subseteq> S)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis IntD2 Int_commute Int_lower1 Int_mono inf.idem openE openin_open)
next
  assume ?rhs
  then show ?lhs
    by (smt (verit) open_ball Int_commute Int_iff centre_in_ball in_mono openin_open_Int openin_subopen)
qed

lemma openin_contains_cball:
   "openin (top_of_set T) S \<longleftrightarrow>
        S \<subseteq> T \<and> (\<forall>x \<in> S. \<exists>e. 0 < e \<and> cball x e \<inter> T \<subseteq> S)"
  by (fastforce simp: openin_contains_ball intro: exI [where x="_/2"])



section \<open>Closed Nest\<close>

text \<open>Bounded closed nest property (proof does not use Heine-Borel)\<close>

lemma bounded_closed_nest:
  fixes S :: "nat \<Rightarrow> ('a::heine_borel) set"
  assumes "\<And>n. closed (S n)"
      and "\<And>n. S n \<noteq> {}"
      and "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
      and "bounded (S 0)"
  obtains a where "\<And>n. a \<in> S n"
proof -
  from assms(2) obtain x where x: "\<forall>n. x n \<in> S n"
    using choice[of "\<lambda>n x. x \<in> S n"] by auto
  from assms(4,1) have "seq_compact (S 0)"
    by (simp add: bounded_closed_imp_seq_compact)
  then obtain l r where lr: "l \<in> S 0" "strict_mono r" "(x \<circ> r) \<longlonglongrightarrow> l"
    using x and assms(3) unfolding seq_compact_def by blast
  have "\<forall>n. l \<in> S n"
  proof
    fix n :: nat
    have "closed (S n)"
      using assms(1) by simp
    moreover have "\<forall>i. (x \<circ> r) i \<in> S i"
      using x and assms(3) and lr(2) [THEN seq_suble] by auto
    then have "\<forall>i. (x \<circ> r) (i + n) \<in> S n"
      using assms(3) by (fast intro!: le_add2)
    moreover have "(\<lambda>i. (x \<circ> r) (i + n)) \<longlonglongrightarrow> l"
      using lr(3) by (rule LIMSEQ_ignore_initial_segment)
    ultimately show "l \<in> S n"
      by (metis closed_sequentially)
  qed
  then show ?thesis 
    using that by blast
qed

text \<open>Decreasing case does not even need compactness, just completeness.\<close>

lemma decreasing_closed_nest:
  fixes S :: "nat \<Rightarrow> ('a::complete_space) set"
  assumes "\<And>n. closed (S n)"
          "\<And>n. S n \<noteq> {}"
          "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
          "\<And>e. e>0 \<Longrightarrow> \<exists>n. \<forall>x\<in>S n. \<forall>y\<in>S n. dist x y < e"
  obtains a where "\<And>n. a \<in> S n"
proof -
  obtain t where t: "\<forall>n. t n \<in> S n"
    by (meson assms(2) equals0I)
  have "Cauchy t"
  proof (intro metric_CauchyI)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    then obtain N where N: "\<forall>x\<in>S N. \<forall>y\<in>S N. dist x y < \<epsilon>"
      using assms(4) by blast
    {
      fix m n :: nat
      assume "N \<le> m \<and> N \<le> n"
      then have "t m \<in> S N" "t n \<in> S N"
        using assms(3) t unfolding  subset_eq t by blast+
      then have "dist (t m) (t n) < \<epsilon>"
        using N by auto
    }
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (t m) (t n) < \<epsilon>"
      by auto
  qed
  then obtain l where l:"(t \<longlongrightarrow> l) sequentially"
    using complete_UNIV unfolding complete_def by auto
  show thesis
  proof
    fix n :: nat
    { fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then obtain N :: nat where N: "\<forall>n\<ge>N. dist (t n) l < \<epsilon>"
        using l[unfolded lim_sequentially] by auto
      have "t (max n N) \<in> S n"
        by (meson assms(3) contra_subsetD max.cobounded1 t)
      then have "\<exists>y\<in>S n. dist y l < \<epsilon>"
        using N max.cobounded2 by blast
    }
    then show "l \<in> S n"
      using closed_approachable[of "S n" l] assms(1) by auto
  qed
qed

text \<open>Strengthen it to the intersection actually being a singleton.\<close>

lemma decreasing_closed_nest_sing:
  fixes S :: "nat \<Rightarrow> 'a::complete_space set"
  assumes "\<And>n. closed(S n)"
          "\<And>n. S n \<noteq> {}"
          "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
   and \<section>: "\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<exists>n. \<forall>x \<in> (S n). \<forall> y\<in>(S n). dist x y < \<epsilon>"
  shows "\<exists>a. \<Inter>(range S) = {a}"
proof -
  obtain a where a: "\<forall>n. a \<in> S n"
    using decreasing_closed_nest[of S] using assms by auto
  { fix b
    assume b: "b \<in> \<Inter>(range S)"
    then have "dist a b = 0"
      by (meson InterE a \<section> linorder_neq_iff linorder_not_less range_eqI zero_le_dist)
  }
  with a have "\<Inter>(range S) = {a}"
    unfolding image_def by auto
  then show ?thesis ..
qed

section\<^marker>\<open>tag unimportant\<close> \<open>Making a continuous function avoid some value in a neighbourhood\<close>

lemma continuous_within_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous (at x within S) f"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> S. dist x y < e --> f y \<noteq> a"
proof -
  obtain U where "open U" and "f x \<in> U" and "a \<notin> U"
    using t1_space [OF \<open>f x \<noteq> a\<close>] by fast
  have "(f \<longlongrightarrow> f x) (at x within S)"
    using assms(1) by (simp add: continuous_within)
  then have "eventually (\<lambda>y. f y \<in> U) (at x within S)"
    using \<open>open U\<close> and \<open>f x \<in> U\<close>
    unfolding tendsto_def by fast
  then have "eventually (\<lambda>y. f y \<noteq> a) (at x within S)"
    using \<open>a \<notin> U\<close> by (fast elim: eventually_mono)
  then show ?thesis
    using \<open>f x \<noteq> a\<close> by (auto simp: dist_commute eventually_at)
qed

lemma continuous_at_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous (at x) f"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
  using assms continuous_within_avoid[of x UNIV f a] by simp

lemma continuous_on_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous_on S f"
    and "x \<in> S"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> S. dist x y < e \<longrightarrow> f y \<noteq> a"
  using continuous_within_avoid[of x S f a] assms
  by (meson continuous_on_eq_continuous_within)

lemma continuous_on_open_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous_on S f"
    and "open S"
    and "x \<in> S"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
  using continuous_at_avoid[of x f a]  assms
  by (meson continuous_on_eq_continuous_at)

section \<open>Consequences for Real Numbers\<close>

lemma closed_contains_Inf:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> closed S \<Longrightarrow> Inf S \<in> S"
  by (metis closure_contains_Inf closure_closed)

lemma closed_subset_contains_Inf:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<in> C"
  by (metis closure_contains_Inf closure_minimal subset_eq)

lemma closed_contains_Sup:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> closed S \<Longrightarrow> Sup S \<in> S"
  by (subst closure_closed[symmetric], assumption, rule closure_contains_Sup)

lemma closed_subset_contains_Sup:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> Sup A \<in> C"
  by (metis closure_contains_Sup closure_minimal subset_eq)

lemma atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real
  shows "A \<noteq> {} \<Longrightarrow> a \<le> b \<Longrightarrow> A \<subseteq> {a..b} \<Longrightarrow> Inf A \<in> {a..b}"
  by (rule closed_subset_contains_Inf)
     (auto intro: closed_real_atLeastAtMost intro!: bdd_belowI[of A a])

lemma bounded_real: "bounded (S::real set) \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. \<bar>x\<bar> \<le> a)"
  by (simp add: bounded_iff)

lemma bounded_imp_bdd_above: "bounded S \<Longrightarrow> bdd_above (S :: real set)"
  by (meson abs_le_D1 bdd_above.unfold bounded_real)

lemma bounded_imp_bdd_below: "bounded S \<Longrightarrow> bdd_below (S :: real set)"
  by (metis add.commute abs_le_D1 bdd_below.unfold bounded_def diff_le_eq dist_real_def)

lemma bounded_norm_le_SUP_norm:
  "bounded (range f) \<Longrightarrow> norm (f x) \<le> (SUP x. norm (f x))"
  by (auto intro!: cSUP_upper bounded_imp_bdd_above simp: bounded_norm_comp)

lemma bounded_has_Sup:
  fixes S :: "real set"
  assumes "bounded S"
    and "S \<noteq> {}"
  shows "\<forall>x\<in>S. x \<le> Sup S"
    and "\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> Sup S \<le> b"
proof
  show "\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> Sup S \<le> b"
    using assms by (metis cSup_least)
qed (metis cSup_upper assms(1) bounded_imp_bdd_above)

lemma Sup_insert:
  fixes S :: "real set"
  shows "bounded S \<Longrightarrow> Sup (insert x S) = (if S = {} then x else max x (Sup S))"
  by (auto simp: bounded_imp_bdd_above sup_max cSup_insert_If)

lemma bounded_has_Inf:
  fixes S :: "real set"
  assumes "bounded S"
    and "S \<noteq> {}"
  shows "\<forall>x\<in>S. x \<ge> Inf S"
    and "\<forall>b. (\<forall>x\<in>S. x \<ge> b) \<longrightarrow> Inf S \<ge> b"
proof
  show "\<forall>b. (\<forall>x\<in>S. x \<ge> b) \<longrightarrow> Inf S \<ge> b"
    using assms by (metis cInf_greatest)
qed (metis cInf_lower assms(1) bounded_imp_bdd_below)

lemma Inf_insert:
  fixes S :: "real set"
  shows "bounded S \<Longrightarrow> Inf (insert x S) = (if S = {} then x else min x (Inf S))"
  by (auto simp: bounded_imp_bdd_below inf_min cInf_insert_If)

lemma open_real:
  fixes s :: "real set"
  shows "open s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>e>0. \<forall>x'. \<bar>x' - x\<bar> < e --> x' \<in> s)"
  unfolding open_dist dist_norm by simp

lemma islimpt_approachable_real:
  fixes s :: "real set"
  shows "x islimpt s \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> s. x' \<noteq> x \<and> \<bar>x' - x\<bar> < e)"
  unfolding islimpt_approachable dist_norm by simp

lemma closed_real:
  fixes s :: "real set"
  shows "closed s \<longleftrightarrow> (\<forall>x. (\<forall>e>0.  \<exists>x' \<in> s. x' \<noteq> x \<and> \<bar>x' - x\<bar> < e) \<longrightarrow> x \<in> s)"
  unfolding closed_limpt islimpt_approachable dist_norm by simp

lemma continuous_at_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'. norm(x' - x) < d --> \<bar>f x' - f x\<bar> < e)"
  by (metis (mono_tags, opaque_lifting) LIM_eq continuous_within norm_eq_zero real_norm_def right_minus_eq)

lemma continuous_on_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous_on s f \<longleftrightarrow>
    (\<forall>x \<in> s. \<forall>e>0. \<exists>d>0. (\<forall>x' \<in> s. norm(x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e))"
  unfolding continuous_on_iff dist_norm by simp

lemma continuous_on_closed_Collect_le:
  fixes f g :: "'a::topological_space \<Rightarrow> real"
  assumes f: "continuous_on s f" and g: "continuous_on s g" and s: "closed s"
  shows "closed {x \<in> s. f x \<le> g x}"
proof -
  have "closed ((\<lambda>x. g x - f x) -` {0..} \<inter> s)"
    using closed_real_atLeast continuous_on_diff [OF g f]
    by (simp add: continuous_on_closed_vimage [OF s])
  also have "((\<lambda>x. g x - f x) -` {0..} \<inter> s) = {x\<in>s. f x \<le> g x}"
    by auto
  finally show ?thesis .
qed

lemma continuous_le_on_closure:
  fixes a::real
  assumes f: "continuous_on (closure s) f"
      and x: "x \<in> closure(s)"
      and xlo: "\<And>x. x \<in> s ==> f(x) \<le> a"
    shows "f(x) \<le> a"
  using image_closure_subset [OF f, where T=" {x. x \<le> a}" ] assms
    continuous_on_closed_Collect_le[of "UNIV" "\<lambda>x. x" "\<lambda>x. a"]
  by auto

lemma continuous_ge_on_closure:
  fixes a::real
  assumes f: "continuous_on (closure s) f"
      and x: "x \<in> closure(s)"
      and xlo: "\<And>x. x \<in> s ==> f(x) \<ge> a"
    shows "f(x) \<ge> a"
  using image_closure_subset [OF f, where T=" {x. a \<le> x}"] assms
    continuous_on_closed_Collect_le[of "UNIV" "\<lambda>x. a" "\<lambda>x. x"]
  by auto


section\<open>The infimum of the distance between two sets\<close>

definition\<^marker>\<open>tag important\<close> setdist :: "'a::metric_space set \<Rightarrow> 'a set \<Rightarrow> real" where
  "setdist s t \<equiv>
       (if s = {} \<or> t = {} then 0
        else Inf {dist x y| x y. x \<in> s \<and> y \<in> t})"

lemma setdist_empty1 [simp]: "setdist {} t = 0"
  by (simp add: setdist_def)

lemma setdist_empty2 [simp]: "setdist t {} = 0"
  by (simp add: setdist_def)

lemma setdist_pos_le [simp]: "0 \<le> setdist s t"
  by (auto simp: setdist_def ex_in_conv [symmetric] intro: cInf_greatest)

lemma le_setdistI:
  assumes "s \<noteq> {}" "t \<noteq> {}" "\<And>x y. \<lbrakk>x \<in> s; y \<in> t\<rbrakk> \<Longrightarrow> d \<le> dist x y"
    shows "d \<le> setdist s t"
  using assms
  by (auto simp: setdist_def Set.ex_in_conv [symmetric] intro: cInf_greatest)

lemma setdist_le_dist: "\<lbrakk>x \<in> s; y \<in> t\<rbrakk> \<Longrightarrow> setdist s t \<le> dist x y"
  unfolding setdist_def
  by (auto intro!: bdd_belowI [where m=0] cInf_lower)

lemma le_setdist_iff:
        "d \<le> setdist S T \<longleftrightarrow>
        (\<forall>x \<in> S. \<forall>y \<in> T. d \<le> dist x y) \<and> (S = {} \<or> T = {} \<longrightarrow> d \<le> 0)"
  by (smt (verit) le_setdistI setdist_def setdist_le_dist)

lemma setdist_ltE:
  assumes "setdist S T < b" "S \<noteq> {}" "T \<noteq> {}"
  obtains x y where "x \<in> S" "y \<in> T" "dist x y < b"
  using assms
  by (auto simp: not_le [symmetric] le_setdist_iff)

lemma setdist_refl: "setdist S S = 0"
  by (metis dist_eq_0_iff ex_in_conv order_antisym setdist_def setdist_le_dist setdist_pos_le)

lemma setdist_sym: "setdist S T = setdist T S"
  by (force simp: setdist_def dist_commute intro!: arg_cong [where f=Inf])

lemma setdist_triangle: "setdist S T \<le> setdist S {a} + setdist {a} T"
proof (cases "S = {} \<or> T = {}")
  case True then show ?thesis
    using setdist_pos_le by fastforce
next
  case False
  then have "\<And>x. x \<in> S \<Longrightarrow> setdist S T - dist x a \<le> setdist {a} T"
    by (smt (verit, best) dist_self dist_triangle3 empty_not_insert le_setdist_iff setdist_le_dist singleton_iff)
  then have "setdist S T - setdist {a} T \<le> setdist S {a}"
    using False by (fastforce intro: le_setdistI)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma setdist_singletons [simp]: "setdist {x} {y} = dist x y"
  by (simp add: setdist_def)

lemma setdist_Lipschitz: "\<bar>setdist {x} S - setdist {y} S\<bar> \<le> dist x y"
  unfolding setdist_singletons [symmetric]
  by (metis abs_diff_le_iff diff_le_eq setdist_triangle setdist_sym)

lemma continuous_at_setdist [continuous_intros]: "continuous (at x) (\<lambda>y. (setdist {y} S))"
  by (force simp: continuous_at_eps_delta dist_real_def intro: le_less_trans [OF setdist_Lipschitz])

lemma continuous_on_setdist [continuous_intros]: "continuous_on T (\<lambda>y. (setdist {y} S))"
  by (metis continuous_at_setdist continuous_at_imp_continuous_on)

lemma uniformly_continuous_on_setdist: "uniformly_continuous_on T (\<lambda>y. (setdist {y} S))"
  by (force simp: uniformly_continuous_on_def dist_real_def intro: le_less_trans [OF setdist_Lipschitz])

lemma setdist_subset_right: "\<lbrakk>T \<noteq> {}; T \<subseteq> u\<rbrakk> \<Longrightarrow> setdist S u \<le> setdist S T"
  by (smt (verit, best) in_mono le_setdist_iff)

lemma setdist_subset_left: "\<lbrakk>S \<noteq> {}; S \<subseteq> T\<rbrakk> \<Longrightarrow> setdist T u \<le> setdist S u"
  by (metis setdist_subset_right setdist_sym)

lemma setdist_closure_1 [simp]: "setdist (closure S) T = setdist S T"
proof (cases "S = {} \<or> T = {}")
  case True then show ?thesis by force
next
  case False
  { fix y
    assume "y \<in> T"
    have "continuous_on (closure S) (\<lambda>a. dist a y)"
      by (auto simp: continuous_intros dist_norm)
    then have *: "\<And>x. x \<in> closure S \<Longrightarrow> setdist S T \<le> dist x y"
      by (fast intro: setdist_le_dist \<open>y \<in> T\<close> continuous_ge_on_closure)
  } then
  show ?thesis
    by (metis False antisym closure_eq_empty closure_subset le_setdist_iff setdist_subset_left)
qed

lemma setdist_closure_2 [simp]: "setdist T (closure S) = setdist T S"
  by (metis setdist_closure_1 setdist_sym)

lemma setdist_eq_0I: "\<lbrakk>x \<in> S; x \<in> T\<rbrakk> \<Longrightarrow> setdist S T = 0"
  by (metis antisym dist_self setdist_le_dist setdist_pos_le)

lemma setdist_unique:
  "\<lbrakk>a \<in> S; b \<in> T; \<And>x y. x \<in> S \<and> y \<in> T ==> dist a b \<le> dist x y\<rbrakk>
   \<Longrightarrow> setdist S T = dist a b"
  by (force simp: setdist_le_dist le_setdist_iff intro: antisym)

lemma setdist_le_sing: "x \<in> S ==> setdist S T \<le> setdist {x} T"
  using setdist_subset_left by auto

lemma infdist_eq_setdist: "infdist x A = setdist {x} A"
  by (simp add: infdist_def setdist_def Setcompr_eq_image)

lemma setdist_eq_infdist: "setdist A B = (if A = {} then 0 else INF a\<in>A. infdist a B)"
proof -
  have "Inf {dist x y |x y. x \<in> A \<and> y \<in> B} = (INF x\<in>A. Inf (dist x ` B))"
    if "b \<in> B" "a \<in> A" for a b
  proof (rule order_antisym)
    have "Inf {dist x y |x y. x \<in> A \<and> y \<in> B} \<le> Inf (dist x ` B)"
      if  "b \<in> B" "a \<in> A" "x \<in> A" for x 
    proof -
      have "\<And>b'. b' \<in> B \<Longrightarrow> Inf {dist x y |x y. x \<in> A \<and> y \<in> B} \<le> dist x b'"
        by (metis (mono_tags, lifting) ex_in_conv setdist_def setdist_le_dist that(3))
      then show ?thesis
        by (smt (verit) cINF_greatest ex_in_conv \<open>b \<in> B\<close>)
    qed
    then show "Inf {dist x y |x y. x \<in> A \<and> y \<in> B} \<le> (INF x\<in>A. Inf (dist x ` B))"
      by (metis (mono_tags, lifting) cINF_greatest emptyE that)
  next
    have *: "\<And>x y. \<lbrakk>b \<in> B; a \<in> A; x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> \<exists>a\<in>A. Inf (dist a ` B) \<le> dist x y"
      by (meson bdd_below_image_dist cINF_lower)
    show "(INF x\<in>A. Inf (dist x ` B)) \<le> Inf {dist x y |x y. x \<in> A \<and> y \<in> B}"
    proof (rule conditionally_complete_lattice_class.cInf_mono)
      show "bdd_below ((\<lambda>x. Inf (dist x ` B)) ` A)"
        by (metis (no_types, lifting) bdd_belowI2 ex_in_conv infdist_def infdist_nonneg that(1))
    qed (use that in \<open>auto simp: *\<close>)
  qed
  then show ?thesis
    by (auto simp: setdist_def infdist_def)
qed

lemma infdist_mono:
  assumes "A \<subseteq> B" "A \<noteq> {}"
  shows "infdist x B \<le> infdist x A"
  by (simp add: assms infdist_eq_setdist setdist_subset_right)

lemma infdist_singleton [simp]: "infdist x {y} = dist x y"
  by (simp add: infdist_eq_setdist)

proposition setdist_attains_inf:
  assumes "compact B" "B \<noteq> {}"
  obtains y where "y \<in> B" "setdist A B = infdist y A"
proof (cases "A = {}")
  case True
  then show thesis
    by (metis assms diameter_compact_attained infdist_def setdist_def that)
next
  case False
  obtain y where "y \<in> B" and min: "\<And>y'. y' \<in> B \<Longrightarrow> infdist y A \<le> infdist y' A"
    by (metis continuous_attains_inf [OF assms continuous_on_infdist] continuous_on_id)
  show thesis
  proof
    have "setdist A B = (INF y\<in>B. infdist y A)"
      by (metis \<open>B \<noteq> {}\<close> setdist_eq_infdist setdist_sym)
    also have "\<dots> = infdist y A"
    proof (rule order_antisym)
      show "(INF y\<in>B. infdist y A) \<le> infdist y A"
        by (meson \<open>y \<in> B\<close> bdd_belowI2 cInf_lower image_eqI infdist_nonneg)
    next
      show "infdist y A \<le> (INF y\<in>B. infdist y A)"
        by (simp add: \<open>B \<noteq> {}\<close> cINF_greatest min)
    qed
    finally show "setdist A B = infdist y A" .
  qed (fact \<open>y \<in> B\<close>)
qed


section \<open>Diameter Lemma\<close>

text \<open>taken from the AFP entry Martingales, by Ata Keskin, TU München\<close>

lemma diameter_comp_strict_mono:
  fixes s :: "nat \<Rightarrow> 'a :: metric_space"
  assumes "strict_mono r" "bounded {s i |i. r n \<le> i}"
  shows "diameter {s (r i) | i. n \<le> i} \<le> diameter {s i | i. r n \<le> i}"
proof (rule diameter_subset)
  show "{s (r i) | i. n \<le> i} \<subseteq> {s i | i. r n \<le> i}" using assms(1) monotoneD strict_mono_mono by fastforce
qed (intro assms(2))

lemma diameter_bounded_bound':
  fixes S :: "'a :: metric_space set"
  assumes S: "bdd_above (case_prod dist ` (S\<times>S))" and "x \<in> S" "y \<in> S"
  shows "dist x y \<le> diameter S"
proof -
  have "(x,y) \<in> S\<times>S" using assms by auto
  then have "dist x y \<le> (SUP (x,y)\<in>S\<times>S. dist x y)"
    by (metis S cSUP_upper case_prod_conv)
  with \<open>x \<in> S\<close> show ?thesis by (auto simp: diameter_def)
qed

lemma bounded_imp_dist_bounded:
  assumes "bounded (range s)"
  shows "bounded ((\<lambda>(i, j). dist (s i) (s j)) ` ({n..} \<times> {n..}))"
  using bounded_dist_comp[OF bounded_fst bounded_snd, OF bounded_Times(1,1)[OF assms(1,1)]] by (rule bounded_subset, force) 

text \<open>A sequence is Cauchy, if and only if it is bounded and its diameter tends to zero. The diameter is well-defined only if the sequence is bounded.\<close>
lemma cauchy_iff_diameter_tends_to_zero_and_bounded:
  fixes s :: "nat \<Rightarrow> 'a :: metric_space"
  shows "Cauchy s \<longleftrightarrow> ((\<lambda>n. diameter {s i | i. i \<ge> n}) \<longlonglongrightarrow> 0 \<and> bounded (range s))"
proof -
  have "{s i |i. N \<le> i} \<noteq> {}" for N by blast
  hence diameter_SUP: "diameter {s i |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i) (s j))" for N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  show ?thesis 
  proof (intro iffI)
    assume asm: "Cauchy s"
    have "\<exists>N. \<forall>n\<ge>N. norm (diameter {s i |i. n \<le> i}) < e" if e_pos: "e > 0" for e
    proof -
      obtain N where dist_less: "dist (s n) (s m) < (1/2) * e" if "n \<ge> N" "m \<ge> N" for n m using asm e_pos by (metis Cauchy_def mult_pos_pos zero_less_divide_iff zero_less_numeral zero_less_one)
      {
        fix r assume "r \<ge> N"
        hence "dist (s n) (s m) < (1/2) * e" if "n \<ge> r" "m \<ge> r" for n m using dist_less that by simp
        hence "(SUP (i, j) \<in> {r..} \<times> {r..}. dist (s i) (s j)) \<le> (1/2) * e" by (intro cSup_least) fastforce+
        also have "... < e" using e_pos by simp
        finally have "diameter {s i |i. r \<le> i} < e" using diameter_SUP by presburger
      }
      moreover have "diameter {s i |i. r \<le> i} \<ge> 0" for r unfolding diameter_SUP using bounded_imp_dist_bounded[OF cauchy_imp_bounded, THEN bounded_imp_bdd_above, OF asm] by (intro cSup_upper2, auto)
      ultimately show ?thesis by auto
    qed                 
    thus "(\<lambda>n. diameter {s i |i. n \<le> i}) \<longlonglongrightarrow> 0 \<and> bounded (range s)" using cauchy_imp_bounded[OF asm] by (simp add: LIMSEQ_iff)
  next
    assume asm: "(\<lambda>n. diameter {s i |i. n \<le> i}) \<longlonglongrightarrow> 0 \<and> bounded (range s)"
    have "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (s n) (s m) < e" if e_pos: "e > 0" for e
    proof -
      obtain N where diam_less: "diameter {s i |i. r \<le> i} < e" if "r \<ge> N" for r using LIMSEQ_D asm(1) e_pos by fastforce
      {
        fix n m assume "n \<ge> N" "m \<ge> N"
        hence "dist (s n) (s m) < e" using cSUP_lessD[OF bounded_imp_dist_bounded[THEN bounded_imp_bdd_above], OF _ diam_less[unfolded diameter_SUP]] asm by auto
      }
      thus ?thesis by blast
    qed
    then show "Cauchy s" by (simp add: Cauchy_def)
  qed            
qed
  
end
