theory Isolated
  imports "HOL-Analysis.Elementary_Metric_Spaces"

begin

subsection \<open>Isolate and discrete\<close>

definition (in topological_space) isolated_in:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infixr "isolated'_in" 60)
  where "x isolated_in S \<longleftrightarrow> (x\<in>S \<and> (\<exists>T. open T \<and> T \<inter> S = {x}))"

definition (in topological_space) discrete:: "'a set \<Rightarrow> bool"
  where "discrete S \<longleftrightarrow> (\<forall>x\<in>S. x isolated_in S)"

definition (in metric_space) uniform_discrete :: "'a set \<Rightarrow> bool" where
  "uniform_discrete S \<longleftrightarrow> (\<exists>e>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < e \<longrightarrow> x = y)"

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

end
