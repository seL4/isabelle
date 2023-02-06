section \<open>Some Uncountable Sets\<close>

theory Uncountable_Sets
  imports Path_Connected Continuum_Not_Denumerable  
begin

lemma uncountable_closed_segment:
  fixes a :: "'a::real_normed_vector"
  assumes "a \<noteq> b" shows "uncountable (closed_segment a b)"
unfolding path_image_linepath [symmetric] path_image_def
  using inj_on_linepath [OF assms] uncountable_closed_interval [of 0 1]
        countable_image_inj_on by auto

lemma uncountable_open_segment:
  fixes a :: "'a::real_normed_vector"
  assumes "a \<noteq> b" shows "uncountable (open_segment a b)"
  by (simp add: assms open_segment_def uncountable_closed_segment uncountable_minus_countable)

lemma uncountable_convex:
  fixes a :: "'a::real_normed_vector"
  assumes "convex S" "a \<in> S" "b \<in> S" "a \<noteq> b"
    shows "uncountable S"
proof -
  have "uncountable (closed_segment a b)"
    by (simp add: uncountable_closed_segment assms)
  then show ?thesis
    by (meson assms convex_contains_segment countable_subset)
qed

lemma uncountable_ball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0"
    shows "uncountable (ball a r)"
proof -
  have "uncountable (open_segment a (a + r *\<^sub>R (SOME i. i \<in> Basis)))"
    by (metis Basis_zero SOME_Basis add_cancel_right_right assms less_le scale_eq_0_iff uncountable_open_segment)
  moreover have "open_segment a (a + r *\<^sub>R (SOME i. i \<in> Basis)) \<subseteq> ball a r"
    using assms by (auto simp: in_segment algebra_simps dist_norm SOME_Basis)
  ultimately show ?thesis
    by (metis countable_subset)
qed

lemma ball_minus_countable_nonempty:
  assumes "countable (A :: 'a :: euclidean_space set)" "r > 0"
  shows   "ball z r - A \<noteq> {}"
proof
  assume *: "ball z r - A = {}"
  have "uncountable (ball z r - A)"
    by (intro uncountable_minus_countable assms uncountable_ball)
  thus False by (subst (asm) *) auto
qed

lemma uncountable_cball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0"
  shows "uncountable (cball a r)"
  using assms countable_subset uncountable_ball by auto

lemma pairwise_disjnt_countable:
  fixes \<N> :: "nat set set"
  assumes "pairwise disjnt \<N>"
    shows "countable \<N>"
  by (simp add: assms countable_disjoint_open_subsets open_discrete)

lemma pairwise_disjnt_countable_Union:
    assumes "countable (\<Union>\<N>)" and pwd: "pairwise disjnt \<N>"
    shows "countable \<N>"
proof -
  obtain f :: "_ \<Rightarrow> nat" where f: "inj_on f (\<Union>\<N>)"
    using assms by blast
  then have "pairwise disjnt (\<Union> X \<in> \<N>. {f ` X})"
    using assms by (force simp: pairwise_def disjnt_inj_on_iff [OF f])
  then have "countable (\<Union> X \<in> \<N>. {f ` X})"
    using pairwise_disjnt_countable by blast
  then show ?thesis
    by (meson pwd countable_image_inj_on disjoint_image f inj_on_image pairwise_disjnt_countable)
qed

lemma connected_uncountable:
  fixes S :: "'a::metric_space set"
  assumes "connected S" "a \<in> S" "b \<in> S" "a \<noteq> b" shows "uncountable S"
proof -
  have "continuous_on S (dist a)"
    by (intro continuous_intros)
  then have "connected (dist a ` S)"
    by (metis connected_continuous_image \<open>connected S\<close>)
  then have "closed_segment 0 (dist a b) \<subseteq> (dist a ` S)"
    by (simp add: assms closed_segment_subset is_interval_connected_1 is_interval_convex)
  then have "uncountable (dist a ` S)"
    by (metis \<open>a \<noteq> b\<close> countable_subset dist_eq_0_iff uncountable_closed_segment)
  then show ?thesis
    by blast
qed

lemma path_connected_uncountable:
  fixes S :: "'a::metric_space set"
  assumes "path_connected S" "a \<in> S" "b \<in> S" "a \<noteq> b" shows "uncountable S"
  using path_connected_imp_connected assms connected_uncountable by metis

lemma simple_path_image_uncountable: 
  fixes g :: "real \<Rightarrow> 'a::metric_space"
  assumes "simple_path g"
  shows "uncountable (path_image g)"
proof -
  have "g 0 \<in> path_image g" "g (1/2) \<in> path_image g"
    by (simp_all add: path_defs)
  moreover have "g 0 \<noteq> g (1/2)"
    using assms by (fastforce simp add: simple_path_def loop_free_def)
  ultimately have "\<forall>a. \<not> path_image g \<subseteq> {a}"
    by blast
  then show ?thesis
    using assms connected_simple_path_image connected_uncountable by blast
qed

lemma arc_image_uncountable:
  fixes g :: "real \<Rightarrow> 'a::metric_space"
  assumes "arc g"
  shows "uncountable (path_image g)"
  by (simp add: arc_imp_simple_path assms simple_path_image_uncountable)

end
