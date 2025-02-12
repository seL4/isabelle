theory Isolated
  imports "Elementary_Metric_Spaces" "Sparse_In"

begin

subsection \<open>Isolate and discrete\<close>

definition (in topological_space) isolated_in:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infixr \<open>isolated'_in\<close> 60)
  where "x isolated_in S \<longleftrightarrow> (x\<in>S \<and> (\<exists>T. open T \<and> T \<inter> S = {x}))"

definition (in topological_space) discrete:: "'a set \<Rightarrow> bool"
  where "discrete S \<longleftrightarrow> (\<forall>x\<in>S. x isolated_in S)"

definition (in metric_space) uniform_discrete :: "'a set \<Rightarrow> bool" where
  "uniform_discrete S \<longleftrightarrow> (\<exists>e>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < e \<longrightarrow> x = y)"

lemma discreteI: "(\<And>x. x \<in> X \<Longrightarrow> x isolated_in X ) \<Longrightarrow> discrete X"
  unfolding discrete_def by auto

lemma discreteD: "discrete X \<Longrightarrow> x \<in> X \<Longrightarrow> x isolated_in X "
  unfolding discrete_def by auto
 
lemma uniformI1:
  assumes "e>0" "\<And>x y. \<lbrakk>x\<in>S;y\<in>S;dist x y<e\<rbrakk> \<Longrightarrow> x =y "
  shows "uniform_discrete S"
unfolding uniform_discrete_def using assms by auto

lemma uniformI2:
  assumes "e>0" "\<And>x y. \<lbrakk>x\<in>S;y\<in>S;x\<noteq>y\<rbrakk> \<Longrightarrow> dist x y\<ge>e "
  shows "uniform_discrete S"
unfolding uniform_discrete_def using assms not_less by blast

lemma isolated_in_islimpt_iff:"(x isolated_in S) \<longleftrightarrow> (\<not> (x islimpt S) \<and> x\<in>S)"
  unfolding isolated_in_def islimpt_def by auto

lemma isolated_in_dist_Ex_iff:
  fixes x::"'a::metric_space"
  shows "x isolated_in S \<longleftrightarrow> (x\<in>S \<and> (\<exists>e>0. \<forall>y\<in>S. dist x y < e \<longrightarrow> y=x))"
unfolding isolated_in_islimpt_iff islimpt_approachable by (metis dist_commute)

lemma discrete_empty[simp]: "discrete {}"
  unfolding discrete_def by auto

lemma uniform_discrete_empty[simp]: "uniform_discrete {}"
  unfolding uniform_discrete_def by (simp add: gt_ex)

lemma isolated_in_insert:
  fixes x :: "'a::t1_space"
  shows "x isolated_in (insert a S) \<longleftrightarrow> x isolated_in S \<or> (x=a \<and> \<not> (x islimpt S))"
by (meson insert_iff islimpt_insert isolated_in_islimpt_iff)

lemma isolated_inI:
  assumes "x\<in>S" "open T" "T \<inter> S = {x}"
  shows   "x isolated_in S"
  using assms unfolding isolated_in_def by auto

lemma isolated_inE:
  assumes "x isolated_in S"
  obtains T where "x \<in> S" "open T" "T \<inter> S = {x}"
  using assms that unfolding isolated_in_def by force

lemma isolated_inE_dist:
  assumes "x isolated_in S"
  obtains d where "d > 0" "\<And>y. y \<in> S \<Longrightarrow> dist x y < d \<Longrightarrow> y = x"
  by (meson assms isolated_in_dist_Ex_iff)

lemma isolated_in_altdef: 
  "x isolated_in S \<longleftrightarrow> (x\<in>S \<and> eventually (\<lambda>y. y \<notin> S) (at x))"
proof 
  assume "x isolated_in S"
  from isolated_inE[OF this] 
  obtain T where "x \<in> S" and T:"open T" "T \<inter> S = {x}"
    by metis
  have "\<forall>\<^sub>F y in nhds x. y \<in> T"
    apply (rule eventually_nhds_in_open)
    using T by auto
  then have  "eventually (\<lambda>y. y \<in> T - {x}) (at x)"
    unfolding eventually_at_filter by eventually_elim auto
  then have "eventually (\<lambda>y. y \<notin> S) (at x)"
    by eventually_elim (use T in auto)
  then show " x \<in> S \<and> (\<forall>\<^sub>F y in at x. y \<notin> S)" using \<open>x \<in> S\<close> by auto
next
  assume "x \<in> S \<and> (\<forall>\<^sub>F y in at x. y \<notin> S)" 
  then have "\<forall>\<^sub>F y in at x. y \<notin> S" "x\<in>S" by auto
  from this(1) have "eventually (\<lambda>y. y \<notin> S \<or> y = x) (nhds x)"
    unfolding eventually_at_filter by eventually_elim auto
  then obtain T where T:"open T" "x \<in> T" "(\<forall>y\<in>T. y \<notin> S \<or> y = x)" 
    unfolding eventually_nhds by auto
  with \<open>x \<in> S\<close> have "T \<inter> S = {x}"  
    by fastforce
  with \<open>x\<in>S\<close> \<open>open T\<close>
  show "x isolated_in S"
    unfolding isolated_in_def by auto
qed

lemma discrete_altdef:
  "discrete S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>\<^sub>F y in at x. y \<notin> S)"
  unfolding discrete_def isolated_in_altdef by auto

(*
TODO.
Other than

  uniform_discrete S \<longrightarrow> discrete S
  uniform_discrete S \<longrightarrow> closed S

, we should be able to prove

  discrete S \<and> closed S \<longrightarrow> uniform_discrete S

but the proof (based on Tietze Extension Theorem) seems not very trivial to me. Informal proofs can be found in

http://topology.auburn.edu/tp/reprints/v30/tp30120.pdf
http://msp.org/pjm/1959/9-2/pjm-v9-n2-p19-s.pdf
*)

lemma uniform_discrete_imp_closed:
  "uniform_discrete S \<Longrightarrow> closed S"
  by (meson discrete_imp_closed uniform_discrete_def)

lemma uniform_discrete_imp_discrete:
  "uniform_discrete S \<Longrightarrow> discrete S"
  by (metis discrete_def isolated_in_dist_Ex_iff uniform_discrete_def)

lemma isolated_in_subset:"x isolated_in S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> x\<in>T \<Longrightarrow> x isolated_in T"
  unfolding isolated_in_def by fastforce

lemma discrete_subset[elim]: "discrete S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> discrete T"
  unfolding discrete_def using islimpt_subset isolated_in_islimpt_iff by blast

lemma uniform_discrete_subset[elim]: "uniform_discrete S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> uniform_discrete T"
  by (meson subsetD uniform_discrete_def)

lemma continuous_on_discrete: "discrete S \<Longrightarrow> continuous_on S f"
  unfolding continuous_on_topological by (metis discrete_def islimptI isolated_in_islimpt_iff)

lemma uniform_discrete_insert: "uniform_discrete (insert a S) \<longleftrightarrow> uniform_discrete S"
proof
  assume asm:"uniform_discrete S"
  let ?thesis = "uniform_discrete (insert a S)"
  have ?thesis when "a\<in>S" using that asm by (simp add: insert_absorb)
  moreover have ?thesis when "S={}" using that asm by (simp add: uniform_discrete_def)
  moreover have ?thesis when "a\<notin>S" "S\<noteq>{}"
  proof -
    obtain e1 where "e1>0" and e1_dist:"\<forall>x\<in>S. \<forall>y\<in>S. dist y x < e1 \<longrightarrow> y = x"
      using asm unfolding uniform_discrete_def by auto
    define e2 where "e2 \<equiv> min (setdist {a} S) e1"
    have "closed S" using asm uniform_discrete_imp_closed by auto
    then have "e2>0"
      by (smt (verit) \<open>0 < e1\<close> e2_def infdist_eq_setdist infdist_pos_not_in_closed that)
    moreover have "x = y" if "x\<in>insert a S" "y\<in>insert a S" "dist x y < e2" for x y
    proof (cases "x=a \<or> y=a")
      case True then show ?thesis
        by (smt (verit, best) dist_commute e2_def infdist_eq_setdist infdist_le insertE that)
    next
      case False then show ?thesis
        using e1_dist e2_def that by force
    qed
    ultimately show ?thesis unfolding uniform_discrete_def by meson
  qed
  ultimately show ?thesis by auto
qed (simp add: subset_insertI uniform_discrete_subset)

lemma discrete_compact_finite_iff:
  fixes S :: "'a::t1_space set"
  shows "discrete S \<and> compact S \<longleftrightarrow> finite S"
proof
  assume "finite S"
  then have "compact S" using finite_imp_compact by auto
  moreover have "discrete S"
    unfolding discrete_def using isolated_in_islimpt_iff islimpt_finite[OF \<open>finite S\<close>] by auto
  ultimately show "discrete S \<and> compact S" by auto
next
  assume "discrete S \<and> compact S"
  then show "finite S"
    by (meson discrete_def Heine_Borel_imp_Bolzano_Weierstrass isolated_in_islimpt_iff order_refl)
qed

lemma uniform_discrete_finite_iff:
  fixes S :: "'a::heine_borel set"
  shows "uniform_discrete S \<and> bounded S \<longleftrightarrow> finite S"
proof
  assume "uniform_discrete S \<and> bounded S"
  then have "discrete S" "compact S"
    using uniform_discrete_imp_discrete uniform_discrete_imp_closed compact_eq_bounded_closed
    by auto
  then show "finite S" using discrete_compact_finite_iff by auto
next
  assume asm:"finite S"
  let ?thesis = "uniform_discrete S \<and> bounded S"
  have ?thesis when "S={}" using that by auto
  moreover have ?thesis when "S\<noteq>{}"
  proof -
    have "\<forall>x. \<exists>d>0. \<forall>y\<in>S. y \<noteq> x \<longrightarrow> d \<le> dist x y"
      using finite_set_avoid[OF \<open>finite S\<close>] by auto
    then obtain f where f_pos:"f x>0"
        and f_dist: "\<forall>y\<in>S. y \<noteq> x \<longrightarrow> f x \<le> dist x y"
        if "x\<in>S" for x
      by metis
    define f_min where "f_min \<equiv> Min (f ` S)"
    have "f_min > 0"
      unfolding f_min_def
      by (simp add: asm f_pos that)
    moreover have "\<forall>x\<in>S. \<forall>y\<in>S. f_min > dist x y \<longrightarrow> x=y"
      using f_dist unfolding f_min_def
      by (metis Min_le asm finite_imageI imageI le_less_trans linorder_not_less)
    ultimately have "uniform_discrete S"
      unfolding uniform_discrete_def by auto
    moreover have "bounded S" using \<open>finite S\<close> by auto
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed

lemma uniform_discrete_image_scale:
  assumes "uniform_discrete S" and dist:"\<forall>x\<in>S. \<forall>y\<in>S. dist x y = c * dist (f x) (f y)"
  shows "uniform_discrete (f ` S)"
proof -
  have ?thesis when "S={}" using that by auto
  moreover have ?thesis when "S\<noteq>{}" "c\<le>0"
  proof -
    obtain x1 where "x1\<in>S" using \<open>S\<noteq>{}\<close> by auto
    have ?thesis when "S-{x1} = {}"
      using \<open>x1 \<in> S\<close> subset_antisym that uniform_discrete_insert by fastforce
    moreover have ?thesis when "S-{x1} \<noteq> {}"
    proof -
      obtain x2 where "x2\<in>S-{x1}" using \<open>S-{x1} \<noteq> {}\<close> by auto
      then have "x2\<in>S" "x1\<noteq>x2" by auto
      then have "dist x1 x2 > 0" by auto
      moreover have "dist x1 x2 = c * dist (f x1) (f x2)"
        by (simp add: \<open>x1 \<in> S\<close> \<open>x2 \<in> S\<close> dist)
      moreover have "dist (f x2) (f x2) \<ge> 0" by auto
      ultimately have False using \<open>c\<le>0\<close> by (simp add: zero_less_mult_iff)
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  moreover have ?thesis when "S\<noteq>{}" "c>0"
  proof -
    obtain e1 where "e1>0" and e1_dist:"\<forall>x\<in>S. \<forall>y\<in>S. dist y x < e1 \<longrightarrow> y = x"
      using \<open>uniform_discrete S\<close> unfolding uniform_discrete_def by auto
    define e where "e \<equiv> e1/c"
    have "x1 = x2" when "x1 \<in> f ` S" "x2 \<in> f ` S" and d: "dist x1 x2 < e" for x1 x2
      by (smt (verit) \<open>0 < c\<close> d dist divide_right_mono e1_dist e_def imageE nonzero_mult_div_cancel_left that)
    moreover have "e>0" using \<open>e1>0\<close> \<open>c>0\<close> unfolding e_def by auto
    ultimately show ?thesis unfolding uniform_discrete_def by meson
  qed
  ultimately show ?thesis by fastforce
qed

definition sparse :: "real \<Rightarrow> 'a :: metric_space set \<Rightarrow> bool"
  where "sparse \<epsilon> X \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X-{x}. dist x y > \<epsilon>)"

lemma sparse_empty [simp, intro]: "sparse \<epsilon> {}"
  by (auto simp: sparse_def)

lemma sparseI [intro?]:
  "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<noteq> y \<Longrightarrow> dist x y > \<epsilon>) \<Longrightarrow> sparse \<epsilon> X"
  unfolding sparse_def by auto

lemma sparseD:
  "sparse \<epsilon> X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<noteq> y \<Longrightarrow> dist x y > \<epsilon>"
  unfolding sparse_def by auto

lemma sparseD':
  "sparse \<epsilon> X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist x y \<le> \<epsilon> \<Longrightarrow> x = y"
  unfolding sparse_def by force

lemma sparse_singleton [simp, intro]: "sparse \<epsilon> {x}"
  by (auto simp: sparse_def)

definition setdist_gt where "setdist_gt \<epsilon> X Y \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>Y. dist x y > \<epsilon>)"

lemma setdist_gt_empty [simp]: "setdist_gt \<epsilon> {} Y" "setdist_gt \<epsilon> X {}"
  by (auto simp: setdist_gt_def)

lemma setdist_gtI: "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> dist x y > \<epsilon>) \<Longrightarrow> setdist_gt \<epsilon> X Y"
  unfolding setdist_gt_def by auto

lemma setdist_gtD: "setdist_gt \<epsilon> X Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> dist x y > \<epsilon>"
  unfolding setdist_gt_def by auto 

lemma setdist_gt_setdist: "\<epsilon> < setdist A B \<Longrightarrow> setdist_gt \<epsilon> A B"
  unfolding setdist_gt_def using setdist_le_dist by fastforce

lemma setdist_gt_mono: "setdist_gt \<epsilon>' A B \<Longrightarrow> \<epsilon> \<le> \<epsilon>' \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> setdist_gt \<epsilon> A' B'"
  by (force simp: setdist_gt_def)
  
lemma setdist_gt_Un_left: "setdist_gt \<epsilon> (A \<union> B) C \<longleftrightarrow> setdist_gt \<epsilon> A C \<and> setdist_gt \<epsilon> B C"
  by (auto simp: setdist_gt_def)

lemma setdist_gt_Un_right: "setdist_gt \<epsilon> C (A \<union> B) \<longleftrightarrow> setdist_gt \<epsilon> C A \<and> setdist_gt \<epsilon> C B"
  by (auto simp: setdist_gt_def)
  
lemma compact_closed_imp_eventually_setdist_gt_at_right_0:
  assumes "compact A" "closed B" "A \<inter> B = {}"
  shows   "eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> A B) (at_right 0)"
proof (cases "A = {} \<or> B = {}")
  case False
  hence "setdist A B > 0"
    by (metis IntI assms empty_iff in_closed_iff_infdist_zero order_less_le setdist_attains_inf setdist_pos_le setdist_sym)
  hence "eventually (\<lambda>\<epsilon>. \<epsilon> < setdist A B) (at_right 0)"
    using eventually_at_right_field by blast
  thus ?thesis
    by eventually_elim (auto intro: setdist_gt_setdist)
qed auto 

lemma setdist_gt_symI: "setdist_gt \<epsilon> A B \<Longrightarrow> setdist_gt \<epsilon> B A"
  by (force simp: setdist_gt_def dist_commute)

lemma setdist_gt_sym: "setdist_gt \<epsilon> A B \<longleftrightarrow> setdist_gt \<epsilon> B A"
  by (force simp: setdist_gt_def dist_commute)

lemma eventually_setdist_gt_at_right_0_mult_iff:
  assumes "c > 0"
  shows   "eventually (\<lambda>\<epsilon>. setdist_gt (c * \<epsilon>) A B) (at_right 0) \<longleftrightarrow>
             eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> A B) (at_right 0)"
proof -
  have "eventually (\<lambda>\<epsilon>. setdist_gt (c * \<epsilon>) A B) (at_right 0) \<longleftrightarrow>
        eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> A B) (filtermap ((*) c) (at_right 0))"
    by (simp add: eventually_filtermap)
  also have "filtermap ((*) c) (at_right 0) = at_right 0"
    by (subst filtermap_times_pos_at_right) (use assms in auto)
  finally show ?thesis .
qed

lemma uniform_discrete_imp_sparse:
  assumes "uniform_discrete X"
  shows   "X sparse_in A"
  using assms unfolding uniform_discrete_def sparse_in_ball_def
  by (auto simp: discrete_imp_not_islimpt)

end
