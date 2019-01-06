(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary Metric Spaces\<close>

theory Elementary_Metric_Spaces
  imports
    Elementary_Topology
    Abstract_Topology
begin

(* FIXME: move elsewhere *)

lemma approachable_lt_le: "(\<exists>(d::real) > 0. \<forall>x. f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI)
  apply auto
  done

lemma approachable_lt_le2:  \<comment> \<open>like the above, but pushes aside an extra formula\<close>
    "(\<exists>(d::real) > 0. \<forall>x. Q x \<longrightarrow> f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> Q x \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI, auto)
  done

lemma triangle_lemma:
  fixes x y z :: real
  assumes x: "0 \<le> x"
    and y: "0 \<le> y"
    and z: "0 \<le> z"
    and xy: "x\<^sup>2 \<le> y\<^sup>2 + z\<^sup>2"
  shows "x \<le> y + z"
proof -
  have "y\<^sup>2 + z\<^sup>2 \<le> y\<^sup>2 + 2 * y * z + z\<^sup>2"
    using z y by simp
  with xy have th: "x\<^sup>2 \<le> (y + z)\<^sup>2"
    by (simp add: power2_eq_square field_simps)
  from y z have yz: "y + z \<ge> 0"
    by arith
  from power2_le_imp_le[OF th yz] show ?thesis .
qed


subsection \<open>Combination of Elementary and Abstract Topology\<close>

lemma closedin_limpt:
  "closedin (subtopology euclidean T) S \<longleftrightarrow> S \<subseteq> T \<and> (\<forall>x. x islimpt S \<and> x \<in> T \<longrightarrow> x \<in> S)"
  apply (simp add: closedin_closed, safe)
   apply (simp add: closed_limpt islimpt_subset)
  apply (rule_tac x="closure S" in exI, simp)
  apply (force simp: closure_def)
  done

lemma closedin_closed_eq: "closed S \<Longrightarrow> closedin (subtopology euclidean S) T \<longleftrightarrow> closed T \<and> T \<subseteq> S"
  by (meson closedin_limpt closed_subset closedin_closed_trans)

lemma connected_closed_set:
   "closed S
    \<Longrightarrow> connected S \<longleftrightarrow> (\<nexists>A B. closed A \<and> closed B \<and> A \<noteq> {} \<and> B \<noteq> {} \<and> A \<union> B = S \<and> A \<inter> B = {})"
  unfolding connected_closedin_eq closedin_closed_eq connected_closedin_eq by blast

text \<open>If a connnected set is written as the union of two nonempty closed sets, then these sets
have to intersect.\<close>

lemma connected_as_closed_union:
  assumes "connected C" "C = A \<union> B" "closed A" "closed B" "A \<noteq> {}" "B \<noteq> {}"
  shows "A \<inter> B \<noteq> {}"
by (metis assms closed_Un connected_closed_set)

lemma closedin_subset_trans:
  "closedin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    closedin (subtopology euclidean T) S"
  by (meson closedin_limpt subset_iff)

lemma openin_subset_trans:
  "openin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    openin (subtopology euclidean T) S"
  by (auto simp: openin_open)

lemma openin_Times:
  "openin (subtopology euclidean S) S' \<Longrightarrow> openin (subtopology euclidean T) T' \<Longrightarrow>
    openin (subtopology euclidean (S \<times> T)) (S' \<times> T')"
  unfolding openin_open using open_Times by blast


subsubsection \<open>Closure\<close>

lemma closure_openin_Int_closure:
  assumes ope: "openin (subtopology euclidean U) S" and "T \<subseteq> U"
  shows "closure(S \<inter> closure T) = closure(S \<inter> T)"
proof
  obtain V where "open V" and S: "S = U \<inter> V"
    using ope using openin_open by metis
  show "closure (S \<inter> closure T) \<subseteq> closure (S \<inter> T)"
    proof (clarsimp simp: S)
      fix x
      assume  "x \<in> closure (U \<inter> V \<inter> closure T)"
      then have "V \<inter> closure T \<subseteq> A \<Longrightarrow> x \<in> closure A" for A
          by (metis closure_mono subsetD inf.coboundedI2 inf_assoc)
      then have "x \<in> closure (T \<inter> V)"
         by (metis \<open>open V\<close> closure_closure inf_commute open_Int_closure_subset)
      then show "x \<in> closure (U \<inter> V \<inter> T)"
        by (metis \<open>T \<subseteq> U\<close> inf.absorb_iff2 inf_assoc inf_commute)
    qed
next
  show "closure (S \<inter> T) \<subseteq> closure (S \<inter> closure T)"
    by (meson Int_mono closure_mono closure_subset order_refl)
qed

corollary infinite_openin:
  fixes S :: "'a :: t1_space set"
  shows "\<lbrakk>openin (subtopology euclidean U) S; x \<in> S; x islimpt U\<rbrakk> \<Longrightarrow> infinite S"
  by (clarsimp simp add: openin_open islimpt_eq_acc_point inf_commute)

subsubsection \<open>Frontier\<close>

lemma connected_Int_frontier:
     "\<lbrakk>connected s; s \<inter> t \<noteq> {}; s - t \<noteq> {}\<rbrakk> \<Longrightarrow> (s \<inter> frontier t \<noteq> {})"
  apply (simp add: frontier_interiors connected_openin, safe)
  apply (drule_tac x="s \<inter> interior t" in spec, safe)
   apply (drule_tac [2] x="s \<inter> interior (-t)" in spec)
   apply (auto simp: disjoint_eq_subset_Compl dest: interior_subset [THEN subsetD])
  done

subsubsection \<open>Compactness\<close>

lemma openin_delete:
  fixes a :: "'a :: t1_space"
  shows "openin (subtopology euclidean u) s
         \<Longrightarrow> openin (subtopology euclidean u) (s - {a})"
by (metis Int_Diff open_delete openin_open)

lemma compact_eq_openin_cover:
  "compact S \<longleftrightarrow>
    (\<forall>C. (\<forall>c\<in>C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"
proof safe
  fix C
  assume "compact S" and "\<forall>c\<in>C. openin (subtopology euclidean S) c" and "S \<subseteq> \<Union>C"
  then have "\<forall>c\<in>{T. open T \<and> S \<inter> T \<in> C}. open c" and "S \<subseteq> \<Union>{T. open T \<and> S \<inter> T \<in> C}"
    unfolding openin_open by force+
  with \<open>compact S\<close> obtain D where "D \<subseteq> {T. open T \<and> S \<inter> T \<in> C}" and "finite D" and "S \<subseteq> \<Union>D"
    by (meson compactE)
  then have "image (\<lambda>T. S \<inter> T) D \<subseteq> C \<and> finite (image (\<lambda>T. S \<inter> T) D) \<and> S \<subseteq> \<Union>(image (\<lambda>T. S \<inter> T) D)"
    by auto
  then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
next
  assume 1: "\<forall>C. (\<forall>c\<in>C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
        (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D)"
  show "compact S"
  proof (rule compactI)
    fix C
    let ?C = "image (\<lambda>T. S \<inter> T) C"
    assume "\<forall>t\<in>C. open t" and "S \<subseteq> \<Union>C"
    then have "(\<forall>c\<in>?C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>?C"
      unfolding openin_open by auto
    with 1 obtain D where "D \<subseteq> ?C" and "finite D" and "S \<subseteq> \<Union>D"
      by metis
    let ?D = "inv_into C (\<lambda>T. S \<inter> T) ` D"
    have "?D \<subseteq> C \<and> finite ?D \<and> S \<subseteq> \<Union>?D"
    proof (intro conjI)
      from \<open>D \<subseteq> ?C\<close> show "?D \<subseteq> C"
        by (fast intro: inv_into_into)
      from \<open>finite D\<close> show "finite ?D"
        by (rule finite_imageI)
      from \<open>S \<subseteq> \<Union>D\<close> show "S \<subseteq> \<Union>?D"
        apply (rule subset_trans, clarsimp)
        apply (frule subsetD [OF \<open>D \<subseteq> ?C\<close>, THEN f_inv_into_f])
        apply (erule rev_bexI, fast)
        done
    qed
    then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
  qed
qed


subsubsection \<open>Continuity\<close>

lemma interior_image_subset:
  assumes "inj f" "\<And>x. continuous (at x) f"
  shows "interior (f ` S) \<subseteq> f ` (interior S)"
proof
  fix x assume "x \<in> interior (f ` S)"
  then obtain T where as: "open T" "x \<in> T" "T \<subseteq> f ` S" ..
  then have "x \<in> f ` S" by auto
  then obtain y where y: "y \<in> S" "x = f y" by auto
  have "open (f -` T)"
    using assms \<open>open T\<close> by (simp add: continuous_at_imp_continuous_on open_vimage)
  moreover have "y \<in> vimage f T"
    using \<open>x = f y\<close> \<open>x \<in> T\<close> by simp
  moreover have "vimage f T \<subseteq> S"
    using \<open>T \<subseteq> image f S\<close> \<open>inj f\<close> unfolding inj_on_def subset_eq by auto
  ultimately have "y \<in> interior S" ..
  with \<open>x = f y\<close> show "x \<in> f ` interior S" ..
qed

subsubsection%unimportant \<open>Equality of continuous functions on closure and related results\<close>

lemma continuous_closedin_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on S f \<Longrightarrow> closedin (subtopology euclidean S) {x \<in> S. f x = a}"
  using continuous_closedin_preimage[of S f "{a}"] by (simp add: vimage_def Collect_conj_eq)

lemma continuous_closed_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on S f \<Longrightarrow> closed S \<Longrightarrow> closed {x \<in> S. f x = a}"
  using continuous_closed_preimage[of S f "{a}"] by (simp add: vimage_def Collect_conj_eq)

lemma continuous_constant_on_closure:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes "continuous_on (closure S) f"
      and "\<And>x. x \<in> S \<Longrightarrow> f x = a"
      and "x \<in> closure S"
  shows "f x = a"
    using continuous_closed_preimage_constant[of "closure S" f a]
      assms closure_minimal[of S "{x \<in> closure S. f x = a}"] closure_subset
    unfolding subset_eq
    by auto

lemma image_closure_subset:
  assumes contf: "continuous_on (closure S) f"
    and "closed T"
    and "(f ` S) \<subseteq> T"
  shows "f ` (closure S) \<subseteq> T"
proof -
  have "S \<subseteq> {x \<in> closure S. f x \<in> T}"
    using assms(3) closure_subset by auto
  moreover have "closed (closure S \<inter> f -` T)"
    using continuous_closed_preimage[OF contf] \<open>closed T\<close> by auto
  ultimately have "closure S = (closure S \<inter> f -` T)"
    using closure_minimal[of S "(closure S \<inter> f -` T)"] by auto
  then show ?thesis by auto
qed

subsubsection%unimportant \<open>A function constant on a set\<close>

definition constant_on  (infixl "(constant'_on)" 50)
  where "f constant_on A \<equiv> \<exists>y. \<forall>x\<in>A. f x = y"

lemma constant_on_subset: "\<lbrakk>f constant_on A; B \<subseteq> A\<rbrakk> \<Longrightarrow> f constant_on B"
  unfolding constant_on_def by blast

lemma injective_not_constant:
  fixes S :: "'a::{perfect_space} set"
  shows "\<lbrakk>open S; inj_on f S; f constant_on S\<rbrakk> \<Longrightarrow> S = {}"
unfolding constant_on_def
by (metis equals0I inj_on_contraD islimpt_UNIV islimpt_def)

lemma constant_on_closureI:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes cof: "f constant_on S" and contf: "continuous_on (closure S) f"
    shows "f constant_on (closure S)"
using continuous_constant_on_closure [OF contf] cof unfolding constant_on_def
by metis


subsection \<open>Open and closed balls\<close>

definition%important ball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "ball x e = {y. dist x y < e}"

definition%important cball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "cball x e = {y. dist x y \<le> e}"

definition%important sphere :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "sphere x e = {y. dist x y = e}"

lemma mem_ball [simp]: "y \<in> ball x e \<longleftrightarrow> dist x y < e"
  by (simp add: ball_def)

lemma mem_cball [simp]: "y \<in> cball x e \<longleftrightarrow> dist x y \<le> e"
  by (simp add: cball_def)

lemma mem_sphere [simp]: "y \<in> sphere x e \<longleftrightarrow> dist x y = e"
  by (simp add: sphere_def)

lemma ball_trivial [simp]: "ball x 0 = {}"
  by (simp add: ball_def)

lemma cball_trivial [simp]: "cball x 0 = {x}"
  by (simp add: cball_def)

lemma sphere_trivial [simp]: "sphere x 0 = {x}"
  by (simp add: sphere_def)

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
  by (auto simp: mem_ball mem_cball)

lemma sphere_cball [simp,intro]: "sphere z r \<subseteq> cball z r"
  by force

lemma cball_diff_sphere: "cball a r - sphere a r = ball a r"
  by auto

lemma subset_ball[intro]: "d \<le> e \<Longrightarrow> ball x d \<subseteq> ball x e"
  by (simp add: subset_eq)

lemma subset_cball[intro]: "d \<le> e \<Longrightarrow> cball x d \<subseteq> cball x e"
  by (simp add: subset_eq)

lemma mem_ball_leI: "x \<in> ball y e \<Longrightarrow> e \<le> f \<Longrightarrow> x \<in> ball y f"
  by (auto simp: mem_ball mem_cball)

lemma mem_cball_leI: "x \<in> cball y e \<Longrightarrow> e \<le> f \<Longrightarrow> x \<in> cball y f"
  by (auto simp: mem_ball mem_cball)

lemma cball_trans: "y \<in> cball z b \<Longrightarrow> x \<in> cball y a \<Longrightarrow> x \<in> cball z (b + a)"
  unfolding mem_cball
proof -
  have "dist z x \<le> dist z y + dist y x"
    by (rule dist_triangle)
  also assume "dist z y \<le> b"
  also assume "dist y x \<le> a"
  finally show "dist z x \<le> b + a" by arith
qed

lemma ball_max_Un: "ball a (max r s) = ball a r \<union> ball a s"
  by (simp add: set_eq_iff) arith

lemma ball_min_Int: "ball a (min r s) = ball a r \<inter> ball a s"
  by (simp add: set_eq_iff)

lemma cball_max_Un: "cball a (max r s) = cball a r \<union> cball a s"
  by (simp add: set_eq_iff) arith

lemma cball_min_Int: "cball a (min r s) = cball a r \<inter> cball a s"
  by (simp add: set_eq_iff)

lemma cball_diff_eq_sphere: "cball a r - ball a r =  sphere a r"
  by (auto simp: cball_def ball_def dist_commute)

lemma open_ball [intro, simp]: "open (ball x e)"
proof -
  have "open (dist x -` {..<e})"
    by (intro open_vimage open_lessThan continuous_intros)
  also have "dist x -` {..<e} = ball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_ball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. ball x e \<subseteq> S)"
  by (simp add: open_dist subset_eq mem_ball Ball_def dist_commute)

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
  apply (simp add: not_less)
  apply (metis zero_le_dist order_trans dist_self)
  done

lemma ball_empty: "e \<le> 0 \<Longrightarrow> ball x e = {}" by simp

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
    then have "\<exists>d>0. cball x d \<subseteq> S" unfolding subset_eq by (rule_tac x="e/2" in exI, auto)
  }
  moreover
  {
    fix x and e::real
    assume "x\<in>S" "e>0" "cball x e \<subseteq> S"
    then have "\<exists>d>0. ball x d \<subseteq> S"
      unfolding subset_eq
      apply (rule_tac x="e/2" in exI, auto)
      done
  }
  ultimately show ?thesis
    unfolding open_contains_ball by auto
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
  by (auto simp: dist_real_def field_simps mem_cball)

lemma greaterThanLessThan_eq_ball:
  fixes a b::real
  shows "{a <..< b} = ball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps mem_ball)

lemma interior_ball [simp]: "interior (ball x e) = ball x e"
  by (simp add: interior_open)

lemma cball_eq_empty [simp]: "cball x e = {} \<longleftrightarrow> e < 0"
  apply (simp add: set_eq_iff not_le)
  apply (metis zero_le_dist dist_self order_less_le_trans)
  done

lemma cball_empty [simp]: "e < 0 \<Longrightarrow> cball x e = {}"
  by simp

lemma cball_sing:
  fixes x :: "'a::metric_space"
  shows "e = 0 \<Longrightarrow> cball x e = {x}"
  by (auto simp: set_eq_iff)

lemma ball_divide_subset: "d \<ge> 1 \<Longrightarrow> ball x (e/d) \<subseteq> ball x e"
  apply (cases "e \<le> 0")
  apply (simp add: ball_empty divide_simps)
  apply (rule subset_ball)
  apply (simp add: divide_simps)
  done

lemma ball_divide_subset_numeral: "ball x (e / numeral w) \<subseteq> ball x e"
  using ball_divide_subset one_le_numeral by blast

lemma cball_divide_subset: "d \<ge> 1 \<Longrightarrow> cball x (e/d) \<subseteq> cball x e"
  apply (cases "e < 0")
  apply (simp add: divide_simps)
  apply (rule subset_cball)
  apply (metis div_by_1 frac_le not_le order_refl zero_less_one)
  done

lemma cball_divide_subset_numeral: "cball x (e / numeral w) \<subseteq> cball x e"
  using cball_divide_subset one_le_numeral by blast


subsection \<open>Limit Points\<close>

lemma islimpt_approachable:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e)"
  unfolding islimpt_iff_eventually eventually_at by fast

lemma islimpt_approachable_le: "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> S. x' \<noteq> x \<and> dist x' x \<le> e)"
  for x :: "'a::metric_space"
  unfolding islimpt_approachable
  using approachable_lt_le [where f="\<lambda>y. dist y x" and P="\<lambda>y. y \<notin> S \<or> y = x",
    THEN arg_cong [where f=Not]]
  by (simp add: Bex_def conj_commute conj_left_commute)

lemma limpt_of_limpts: "x islimpt {y. y islimpt S} \<Longrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  apply (clarsimp simp add: islimpt_approachable)
  apply (drule_tac x="e/2" in spec)
  apply (auto simp: simp del: less_divide_eq_numeral1)
  apply (drule_tac x="dist x' x" in spec)
  apply (auto simp: zero_less_dist_iff simp del: less_divide_eq_numeral1)
  apply (erule rev_bexI)
  apply (metis dist_commute dist_triangle_half_r less_trans less_irrefl)
  done

lemma closed_limpts:  "closed {x::'a::metric_space. x islimpt S}"
  using closed_limpt limpt_of_limpts by blast

lemma limpt_of_closure: "x islimpt closure S \<longleftrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  by (auto simp: closure_def islimpt_Un dest: limpt_of_limpts)

lemma islimpt_eq_infinite_ball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> ball x e))"
  apply (simp add: islimpt_eq_acc_point, safe)
   apply (metis Int_commute open_ball centre_in_ball)
  by (metis open_contains_ball Int_mono finite_subset inf_commute subset_refl)

lemma islimpt_eq_infinite_cball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> cball x e))"
  apply (simp add: islimpt_eq_infinite_ball, safe)
   apply (meson Int_mono ball_subset_cball finite_subset order_refl)
  by (metis open_ball centre_in_ball finite_Int inf.absorb_iff2 inf_assoc open_contains_cball_eq)


subsection \<open>Perfect Metric Spaces\<close>

lemma perfect_choose_dist: "0 < r \<Longrightarrow> \<exists>a. a \<noteq> x \<and> dist a x < r"
  for x :: "'a::{perfect_space,metric_space}"
  using islimpt_UNIV [of x] by (simp add: islimpt_approachable)

lemma cball_eq_sing:
  fixes x :: "'a::{metric_space,perfect_space}"
  shows "cball x e = {x} \<longleftrightarrow> e = 0"
proof (rule linorder_cases)
  assume e: "0 < e"
  obtain a where "a \<noteq> x" "dist a x < e"
    using perfect_choose_dist [OF e] by auto
  then have "a \<noteq> x" "dist x a \<le> e"
    by (auto simp: dist_commute)
  with e show ?thesis by (auto simp: set_eq_iff)
qed auto


subsection \<open>?\<close>

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
  show ?case
  proof (cases "x = a")
    case True
    with \<open>d > 0 \<close>d show ?thesis by auto
  next
    case False
    let ?d = "min d (dist a x)"
    from False \<open>d > 0\<close> have dp: "?d > 0"
      by auto
    from d have d': "\<forall>x\<in>S. x \<noteq> a \<longrightarrow> ?d \<le> dist a x"
      by auto
    with dp False show ?thesis
      by (metis insert_iff le_less min_less_iff_conj not_less)
  qed
qed (auto intro: zero_less_one)

lemma discrete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes e: "0 < e"
    and d: "\<forall>x \<in> S. \<forall>y \<in> S. dist y x < e \<longrightarrow> y = x"
  shows "closed S"
proof -
  have False if C: "\<And>e. e>0 \<Longrightarrow> \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e" for x
  proof -
    from e have e2: "e/2 > 0" by arith
    from C[rule_format, OF e2] obtain y where y: "y \<in> S" "y \<noteq> x" "dist y x < e/2"
      by blast
    let ?m = "min (e/2) (dist x y) "
    from e2 y(2) have mp: "?m > 0"
      by simp
    from C[OF mp] obtain z where z: "z \<in> S" "z \<noteq> x" "dist z x < ?m"
      by blast
    from z y have "dist z y < e"
      by (intro dist_triangle_lt [where z=x]) simp
    from d[rule_format, OF y(1) z(1) this] y z show ?thesis
      by (auto simp: dist_commute)
  qed
  then show ?thesis
    by (metis islimpt_approachable closed_limpt [where 'a='a])
qed


subsection \<open>Interior\<close>

lemma mem_interior: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  using open_contains_ball_eq [where S="interior S"]
  by (simp add: open_subset_interior)

lemma mem_interior_cball: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S)"
  by (meson ball_subset_cball interior_subset mem_interior open_contains_cball open_interior
      subset_trans)


subsection \<open>Frontier\<close>

lemma frontier_straddle:
  fixes a :: "'a::metric_space"
  shows "a \<in> frontier S \<longleftrightarrow> (\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e))"
  unfolding frontier_def closure_interior
  by (auto simp: mem_interior subset_eq ball_def)


subsection \<open>Limits\<close>

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
  apply (simp add: Lim_within, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

proposition Lim_at: "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

lemma Lim_transform_within_set:
  fixes a :: "'a::metric_space" and l :: "'b::metric_space"
  shows "\<lbrakk>(f \<longlongrightarrow> l) (at a within S); eventually (\<lambda>x. x \<in> S \<longleftrightarrow> x \<in> T) (at a)\<rbrakk>
         \<Longrightarrow> (f \<longlongrightarrow> l) (at a within T)"
apply (clarsimp simp: eventually_at Lim_within)
apply (drule_tac x=e in spec, clarify)
apply (rename_tac k)
apply (rule_tac x="min d k" in exI, simp)
done

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
               "f(Suc n) = y (min (inverse(2 ^ (Suc n))) (dist (f n) x))" for n
    by (simp_all add: f_def)
  have f: "f n \<in> S \<and> (f n \<noteq> x) \<and> dist (f n) x < inverse(2 ^ n)" for n
  proof (induction n)
    case 0 show ?case
      by (simp add: y)
  next
    case (Suc n) then show ?case
      apply (auto simp: y)
      by (metis half_gt_zero_iff inverse_positive_iff_positive less_divide_eq_numeral1(1) min_less_iff_conj y zero_less_dist_iff zero_less_numeral zero_less_power)
  qed
  show ?rhs
  proof (rule_tac x=f in exI, intro conjI allI)
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
      proof cases
        assume "m < n"
        have "dist (f(Suc n)) x = dist (y (min (inverse(2 ^ (Suc n))) (dist (f n) x))) x"
          by simp
        also have "\<dots> < dist (f n) x"
          by (metis dist_pos_lt f min.strict_order_iff min_less_iff_conj y)
        also have "\<dots> < dist (f m) x"
          using Suc.IH \<open>m < n\<close> by blast
        finally show ?thesis .
      next
        assume "m = n" then show ?case
          by simp (metis dist_pos_lt f half_gt_zero_iff inverse_positive_iff_positive min_less_iff_conj y zero_less_numeral zero_less_power)
      qed
    qed
    then show "inj f"
      by (metis less_irrefl linorder_injI)
    show "f \<longlonglongrightarrow> x"
      apply (rule tendstoI)
      apply (rule_tac c="nat (ceiling(1/e))" in eventually_sequentiallyI)
      apply (rule less_trans [OF f [THEN conjunct2, THEN conjunct2]])
      apply (simp add: field_simps)
      by (meson le_less_trans mult_less_cancel_left not_le of_nat_less_two_power)
  qed
next
  assume ?rhs
  then show ?lhs
    by (fastforce simp add: islimpt_approachable lim_sequentially)
qed

lemma Lim_dist_ubound:
  assumes "\<not>(trivial_limit net)"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. dist a (f x) \<le> e) net"
  shows "dist a l \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)


subsection \<open>Closure and Limit Characterization\<close>

lemma closure_approachable:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e)"
  apply (auto simp: closure_def islimpt_approachable)
  apply (metis dist_self)
  done

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
  {
    fix e :: real
    assume "e > 0"
    then have "Inf S < Inf S + e" by simp
    with assms obtain x where "x \<in> S" "x < Inf S + e"
      by (subst (asm) cInf_less_iff) auto
    with * have "\<exists>x\<in>S. dist x (Inf S) < e"
      by (intro bexI[of _ x]) (auto simp: dist_real_def)
  }
  then show ?thesis unfolding closure_approachable by auto
qed

lemma not_trivial_limit_within_ball:
  "\<not> trivial_limit (at x within S) \<longleftrightarrow> (\<forall>e>0. S \<inter> ball x e - {x} \<noteq> {})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    {
      fix e :: real
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
    {
      fix e :: real
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

subsection \<open>Boundedness\<close>

  (* FIXME: This has to be unified with BSEQ!! *)
definition%important (in metric_space) bounded :: "'a set \<Rightarrow> bool"
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
  {
    fix y
    assume "y \<in> closure S"
    then obtain f where f: "\<forall>n. f n \<in> S"  "(f \<longlongrightarrow> y) sequentially"
      unfolding closure_sequential by auto
    have "\<forall>n. f n \<in> S \<longrightarrow> dist x (f n) \<le> a" using a by simp
    then have "eventually (\<lambda>n. dist x (f n) \<le> a) sequentially"
      by (simp add: f(1))
    have "dist x y \<le> a"
      apply (rule Lim_dist_ubound [of sequentially f])
      apply (rule trivial_limit_sequentially)
      apply (rule f(2))
      apply fact
      done
  }
  then show ?thesis
    unfolding bounded_def by auto
qed

lemma bounded_closure_image: "bounded (f ` closure S) \<Longrightarrow> bounded (f ` S)"
  by (simp add: bounded_subset closure_subset image_mono)

lemma bounded_cball[simp,intro]: "bounded (cball x e)"
  apply (simp add: bounded_def)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=e in exI, auto)
  done

lemma bounded_ball[simp,intro]: "bounded (ball x e)"
  by (metis ball_subset_cball bounded_cball bounded_subset)

lemma bounded_Un[simp]: "bounded (S \<union> T) \<longleftrightarrow> bounded S \<and> bounded T"
  by (auto simp: bounded_def) (metis Un_iff bounded_any_center le_max_iff_disj)

lemma bounded_Union[intro]: "finite F \<Longrightarrow> \<forall>S\<in>F. bounded S \<Longrightarrow> bounded (\<Union>F)"
  by (induct rule: finite_induct[of F]) auto

lemma bounded_UN [intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. bounded (B x) \<Longrightarrow> bounded (\<Union>x\<in>A. B x)"
  by (induct set: finite) auto

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
  obtain e::real and y where "S \<subseteq> cball y e"  "0 \<le> e"
    using assms by (auto simp: bounded_subset_cball)
  then show ?thesis
    apply (rule_tac x="dist x y + e + 1" in exI)
    apply (simp add: add.commute add_pos_nonneg)
    apply (erule subset_trans)
    apply (clarsimp simp add: cball_def)
    by (metis add_le_cancel_right add_strict_increasing dist_commute dist_triangle_le zero_less_one)
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
    by (rule order_trans[OF dist_triangle add_mono])
  then show ?thesis
    by (auto intro!: boundedI)
qed


subsection \<open>Consequences for Real Numbers\<close>

lemma closed_contains_Inf:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> closed S \<Longrightarrow> Inf S \<in> S"
  by (metis closure_contains_Inf closure_closed)

lemma closed_subset_contains_Inf:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<in> C"
  by (metis closure_contains_Inf closure_minimal subset_eq)

lemma atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real
  shows "A \<noteq> {} \<Longrightarrow> a \<le> b \<Longrightarrow> A \<subseteq> {a..b} \<Longrightarrow> Inf A \<in> {a..b}"
  by (rule closed_subset_contains_Inf)
     (auto intro: closed_real_atLeastAtMost intro!: bdd_belowI[of A a])

lemma bounded_real: "bounded (S::real set) \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. \<bar>x\<bar> \<le> a)"
  by (simp add: bounded_iff)

lemma bounded_imp_bdd_above: "bounded S \<Longrightarrow> bdd_above (S :: real set)"
  by (auto simp: bounded_def bdd_above_def dist_real_def)
     (metis abs_le_D1 abs_minus_commute diff_le_eq)

lemma bounded_imp_bdd_below: "bounded S \<Longrightarrow> bdd_below (S :: real set)"
  by (auto simp: bounded_def bdd_below_def dist_real_def)
     (metis abs_le_D1 add.commute diff_le_eq)

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


subsection \<open>Compactness\<close>

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

lemma closure_Int_ball_not_empty:
  assumes "S \<subseteq> closure T" "x \<in> S" "r > 0"
  shows "T \<inter> ball x r \<noteq> {}"
  using assms centre_in_ball closure_iff_nhds_not_empty by blast

subsubsection\<open>Totally bounded\<close>

lemma cauchy_def: "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m n. m \<ge> N \<and> n \<ge> N \<longrightarrow> dist (s m) (s n) < e)"
  unfolding Cauchy_def by metis

proposition seq_compact_imp_totally_bounded:
  assumes "seq_compact s"
  shows "\<forall>e>0. \<exists>k. finite k \<and> k \<subseteq> s \<and> s \<subseteq> (\<Union>x\<in>k. ball x e)"
proof -
  { fix e::real assume "e > 0" assume *: "\<And>k. finite k \<Longrightarrow> k \<subseteq> s \<Longrightarrow> \<not> s \<subseteq> (\<Union>x\<in>k. ball x e)"
    let ?Q = "\<lambda>x n r. r \<in> s \<and> (\<forall>m < (n::nat). \<not> (dist (x m) r < e))"
    have "\<exists>x. \<forall>n::nat. ?Q x n (x n)"
    proof (rule dependent_wellorder_choice)
      fix n x assume "\<And>y. y < n \<Longrightarrow> ?Q x y (x y)"
      then have "\<not> s \<subseteq> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        using *[of "x ` {0 ..< n}"] by (auto simp: subset_eq)
      then obtain z where z:"z\<in>s" "z \<notin> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        unfolding subset_eq by auto
      show "\<exists>r. ?Q x n r"
        using z by auto
    qed simp
    then obtain x where "\<forall>n::nat. x n \<in> s" and x:"\<And>n m. m < n \<Longrightarrow> \<not> (dist (x m) (x n) < e)"
      by blast
    then obtain l r where "l \<in> s" and r:"strict_mono  r" and "((x \<circ> r) \<longlongrightarrow> l) sequentially"
      using assms by (metis seq_compact_def)
    from this(3) have "Cauchy (x \<circ> r)"
      using LIMSEQ_imp_Cauchy by auto
    then obtain N::nat where "\<And>m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> dist ((x \<circ> r) m) ((x \<circ> r) n) < e"
      unfolding cauchy_def using \<open>e > 0\<close> by blast
    then have False
      using x[of "r N" "r (N+1)"] r by (auto simp: strict_mono_def) }
  then show ?thesis
    by metis
qed

subsubsection\<open>Heine-Borel theorem\<close>

proposition seq_compact_imp_Heine_Borel:
  fixes s :: "'a :: metric_space set"
  assumes "seq_compact s"
  shows "compact s"
proof -
  from seq_compact_imp_totally_bounded[OF \<open>seq_compact s\<close>]
  obtain f where f: "\<forall>e>0. finite (f e) \<and> f e \<subseteq> s \<and> s \<subseteq> (\<Union>x\<in>f e. ball x e)"
    unfolding choice_iff' ..
  define K where "K = (\<lambda>(x, r). ball x r) ` ((\<Union>e \<in> \<rat> \<inter> {0 <..}. f e) \<times> \<rat>)"
  have "countably_compact s"
    using \<open>seq_compact s\<close> by (rule seq_compact_imp_countably_compact)
  then show "compact s"
  proof (rule countably_compact_imp_compact)
    show "countable K"
      unfolding K_def using f
      by (auto intro: countable_finite countable_subset countable_rat
               intro!: countable_image countable_SIGMA countable_UN)
    show "\<forall>b\<in>K. open b" by (auto simp: K_def)
  next
    fix T x
    assume T: "open T" "x \<in> T" and x: "x \<in> s"
    from openE[OF T] obtain e where "0 < e" "ball x e \<subseteq> T"
      by auto
    then have "0 < e / 2" "ball x (e / 2) \<subseteq> T"
      by auto
    from Rats_dense_in_real[OF \<open>0 < e / 2\<close>] obtain r where "r \<in> \<rat>" "0 < r" "r < e / 2"
      by auto
    from f[rule_format, of r] \<open>0 < r\<close> \<open>x \<in> s\<close> obtain k where "k \<in> f r" "x \<in> ball k r"
      by auto
    from \<open>r \<in> \<rat>\<close> \<open>0 < r\<close> \<open>k \<in> f r\<close> have "ball k r \<in> K"
      by (auto simp: K_def)
    then show "\<exists>b\<in>K. x \<in> b \<and> b \<inter> s \<subseteq> T"
    proof (rule bexI[rotated], safe)
      fix y
      assume "y \<in> ball k r"
      with \<open>r < e / 2\<close> \<open>x \<in> ball k r\<close> have "dist x y < e"
        by (intro dist_triangle_half_r [of k _ e]) (auto simp: dist_commute)
      with \<open>ball x e \<subseteq> T\<close> show "y \<in> T"
        by auto
    next
      show "x \<in> ball k r" by fact
    qed
  qed
qed

proposition compact_eq_seq_compact_metric:
  "compact (s :: 'a::metric_space set) \<longleftrightarrow> seq_compact s"
  using compact_imp_seq_compact seq_compact_imp_Heine_Borel by blast

proposition compact_def: \<comment> \<open>this is the definition of compactness in HOL Light\<close>
  "compact (S :: 'a::metric_space set) \<longleftrightarrow>
   (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l))"
  unfolding compact_eq_seq_compact_metric seq_compact_def by auto

subsubsection \<open>Complete the chain of compactness variants\<close>

proposition compact_eq_Bolzano_Weierstrass:
  fixes s :: "'a::metric_space set"
  shows "compact s \<longleftrightarrow> (\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using Heine_Borel_imp_Bolzano_Weierstrass[of s] by auto
next
  assume ?rhs
  then show ?lhs
    unfolding compact_eq_seq_compact_metric by (rule Bolzano_Weierstrass_imp_seq_compact)
qed

proposition Bolzano_Weierstrass_imp_bounded:
  "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t) \<Longrightarrow> bounded s"
  using compact_imp_bounded unfolding compact_eq_Bolzano_Weierstrass .


subsection \<open>Metric spaces with the Heine-Borel property\<close>

text \<open>
  A metric space (or topological vector space) is said to have the
  Heine-Borel property if every closed and bounded subset is compact.
\<close>

class heine_borel = metric_space +
  assumes bounded_imp_convergent_subsequence:
    "bounded (range f) \<Longrightarrow> \<exists>l r. strict_mono (r::nat\<Rightarrow>nat) \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"

proposition bounded_closed_imp_seq_compact:
  fixes s::"'a::heine_borel set"
  assumes "bounded s"
    and "closed s"
  shows "seq_compact s"
proof (unfold seq_compact_def, clarify)
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> s"
  with \<open>bounded s\<close> have "bounded (range f)"
    by (auto intro: bounded_subset)
  obtain l r where r: "strict_mono (r :: nat \<Rightarrow> nat)" and l: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using bounded_imp_convergent_subsequence [OF \<open>bounded (range f)\<close>] by auto
  from f have fr: "\<forall>n. (f \<circ> r) n \<in> s"
    by simp
  have "l \<in> s" using \<open>closed s\<close> fr l
    by (rule closed_sequentially)
  show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using \<open>l \<in> s\<close> r l by blast
qed

lemma compact_eq_bounded_closed:
  fixes s :: "'a::heine_borel set"
  shows "compact s \<longleftrightarrow> bounded s \<and> closed s"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using compact_imp_closed compact_imp_bounded
    by blast
next
  assume ?rhs
  then show ?lhs
    using bounded_closed_imp_seq_compact[of s]
    unfolding compact_eq_seq_compact_metric
    by auto
qed

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

instance%important real :: heine_borel
proof%unimportant
  fix f :: "nat \<Rightarrow> real"
  assume f: "bounded (range f)"
  obtain r :: "nat \<Rightarrow> nat" where r: "strict_mono r" "monoseq (f \<circ> r)"
    unfolding comp_def by (metis seq_monosub)
  then have "Bseq (f \<circ> r)"
    unfolding Bseq_eq_bounded using f
    by (metis BseqI' bounded_iff comp_apply rangeI)
  with r show "\<exists>l r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    using Bseq_monoseq_convergent[of "f \<circ> r"] by (auto simp: convergent_def)
qed

lemma compact_lemma_general:
  fixes f :: "nat \<Rightarrow> 'a"
  fixes proj::"'a \<Rightarrow> 'b \<Rightarrow> 'c::heine_borel" (infixl "proj" 60)
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
      and lr1: "\<forall>e > 0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e) sequentially"
      using insert(3) using insert(4) by auto
    have f': "\<forall>n. f (r1 n) proj k \<in> (\<lambda>x. x proj k) ` range f"
      by simp
    have "bounded (range (\<lambda>i. f (r1 i) proj k))"
      by (metis (lifting) bounded_subset f' image_subsetI s')
    then obtain l2 r2 where r2:"strict_mono r2" and lr2:"((\<lambda>i. f (r1 (r2 i)) proj k) \<longlongrightarrow> l2) sequentially"
      using bounded_imp_convergent_subsequence[of "\<lambda>i. f (r1 i) proj k"]
      by (auto simp: o_def)
    define r where "r = r1 \<circ> r2"
    have r:"strict_mono r"
      using r1 and r2 unfolding r_def o_def strict_mono_def by auto
    moreover
    define l where "l = unproj (\<lambda>i. if i = k then l2 else l1 proj i)"
    {
      fix e::real
      assume "e > 0"
      from lr1 \<open>e > 0\<close> have N1: "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e) sequentially"
        by blast
      from lr2 \<open>e > 0\<close> have N2:"eventually (\<lambda>n. dist (f (r1 (r2 n)) proj k) l2 < e) sequentially"
        by (rule tendstoD)
      from r2 N1 have N1': "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 (r2 n)) proj i) (l1 proj i) < e) sequentially"
        by (rule eventually_subseq)
      have "eventually (\<lambda>n. \<forall>i\<in>(insert k d). dist (f (r n) proj i) (l proj i) < e) sequentially"
        using N1' N2
        by eventually_elim (insert insert.prems, auto simp: l_def r_def o_def proj_unproj)
    }
    ultimately show ?case by auto
  qed
qed

lemma bounded_fst: "bounded s \<Longrightarrow> bounded (fst ` s)"
  unfolding bounded_def
  by (metis (erased, hide_lams) dist_fst_le image_iff order_trans)

lemma bounded_snd: "bounded s \<Longrightarrow> bounded (snd ` s)"
  unfolding bounded_def
  by (metis (no_types, hide_lams) dist_snd_le image_iff order.trans)

instance%important prod :: (heine_borel, heine_borel) heine_borel
proof%unimportant
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
  obtain l2 r2 where r2: "strict_mono r2" and l2: "((\<lambda>n. snd (f (r1 (r2 n)))) \<longlongrightarrow> l2) sequentially"
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


subsubsection \<open>Completeness\<close>

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
  fixes s :: "'a::metric_space set"
  assumes "compact s"
  shows "complete s"
proof -
  {
    fix f
    assume as: "(\<forall>n::nat. f n \<in> s)" "Cauchy f"
    from as(1) obtain l r where lr: "l\<in>s" "strict_mono r" "(f \<circ> r) \<longlonglongrightarrow> l"
      using assms unfolding compact_def by blast

    note lr' = seq_suble [OF lr(2)]
    {
      fix e :: real
      assume "e > 0"
      from as(2) obtain N where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (f m) (f n) < e/2"
        unfolding cauchy_def
        using \<open>e > 0\<close>
        apply (erule_tac x="e/2" in allE, auto)
        done
      from lr(3)[unfolded lim_sequentially, THEN spec[where x="e/2"]]
      obtain M where M:"\<forall>n\<ge>M. dist ((f \<circ> r) n) l < e/2"
        using \<open>e > 0\<close> by auto
      {
        fix n :: nat
        assume n: "n \<ge> max N M"
        have "dist ((f \<circ> r) n) l < e/2"
          using n M by auto
        moreover have "r n \<ge> N"
          using lr'[of n] n by auto
        then have "dist (f n) ((f \<circ> r) n) < e / 2"
          using N and n by auto
        ultimately have "dist (f n) l < e"
          using dist_triangle_half_r[of "f (r n)" "f n" e l]
          by (auto simp: dist_commute)
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (f n) l < e" by blast
    }
    then have "\<exists>l\<in>s. (f \<longlongrightarrow> l) sequentially" using \<open>l\<in>s\<close>
      unfolding lim_sequentially by auto
  }
  then show ?thesis unfolding complete_def by auto
qed

proposition compact_eq_totally_bounded:
  "compact s \<longleftrightarrow> complete s \<and> (\<forall>e>0. \<exists>k. finite k \<and> s \<subseteq> (\<Union>x\<in>k. ball x e))"
    (is "_ \<longleftrightarrow> ?rhs")
proof
  assume assms: "?rhs"
  then obtain k where k: "\<And>e. 0 < e \<Longrightarrow> finite (k e)" "\<And>e. 0 < e \<Longrightarrow> s \<subseteq> (\<Union>x\<in>k e. ball x e)"
    by (auto simp: choice_iff')

  show "compact s"
  proof cases
    assume "s = {}"
    then show "compact s" by (simp add: compact_def)
  next
    assume "s \<noteq> {}"
    show ?thesis
      unfolding compact_def
    proof safe
      fix f :: "nat \<Rightarrow> 'a"
      assume f: "\<forall>n. f n \<in> s"

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
      moreover have "\<forall>i. (f \<circ> t) i \<in> s"
        using f by auto
      moreover
      {
        fix n
        have "(f \<circ> t) n \<in> F n"
          by (cases n) (simp_all add: t_def sel)
      }
      note t = this

      have "Cauchy (f \<circ> t)"
      proof (safe intro!: metric_CauchyI exI elim!: nat_approx_posE)
        fix r :: real and N n m
        assume "1 / Suc N < r" "Suc N \<le> n" "Suc N \<le> m"
        then have "(f \<circ> t) n \<in> F (Suc N)" "(f \<circ> t) m \<in> F (Suc N)" "2 * e N < r"
          using F_dec t by (auto simp: e_def field_simps of_nat_Suc)
        with F[of N] obtain x where "dist x ((f \<circ> t) n) < e N" "dist x ((f \<circ> t) m) < e N"
          by (auto simp: subset_eq)
        with dist_triangle[of "(f \<circ> t) m" "(f \<circ> t) n" x] \<open>2 * e N < r\<close>
        show "dist ((f \<circ> t) m) ((f \<circ> t) n) < r"
          by (simp add: dist_commute)
      qed

      ultimately show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
        using assms unfolding complete_def by blast
    qed
  qed
qed (metis compact_imp_complete compact_imp_seq_compact seq_compact_imp_totally_bounded)

lemma cauchy_imp_bounded:
  assumes "Cauchy s"
  shows "bounded (range s)"
proof -
  from assms obtain N :: nat where "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < 1"
    unfolding cauchy_def by force
  then have N:"\<forall>n. N \<le> n \<longrightarrow> dist (s N) (s n) < 1" by auto
  moreover
  have "bounded (s ` {0..N})"
    using finite_imp_bounded[of "s ` {1..N}"] by auto
  then obtain a where a:"\<forall>x\<in>s ` {0..N}. dist (s N) x \<le> a"
    unfolding bounded_any_center [where a="s N"] by auto
  ultimately show "?thesis"
    unfolding bounded_any_center [where a="s N"]
    apply (rule_tac x="max a 1" in exI, auto)
    apply (erule_tac x=y in allE)
    apply (erule_tac x=y in ballE, auto)
    done
qed

instance heine_borel < complete_space
proof
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then have "bounded (range f)"
    by (rule cauchy_imp_bounded)
  then have "compact (closure (range f))"
    unfolding compact_eq_bounded_closed by auto
  then have "complete (closure (range f))"
    by (rule compact_imp_complete)
  moreover have "\<forall>n. f n \<in> closure (range f)"
    using closure_subset [of "range f"] by auto
  ultimately have "\<exists>l\<in>closure (range f). (f \<longlongrightarrow> l) sequentially"
    using \<open>Cauchy f\<close> unfolding complete_def by auto
  then show "convergent f"
    unfolding convergent_def by auto
qed

lemma complete_UNIV: "complete (UNIV :: ('a::complete_space) set)"
proof (rule completeI)
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then have "convergent f" by (rule Cauchy_convergent)
  then show "\<exists>l\<in>UNIV. f \<longlonglongrightarrow> l" unfolding convergent_def by simp
qed

lemma complete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S"
  shows "closed S"
proof (unfold closed_sequential_limits, clarify)
  fix f x assume "\<forall>n. f n \<in> S" and "f \<longlonglongrightarrow> x"
  from \<open>f \<longlonglongrightarrow> x\<close> have "Cauchy f"
    by (rule LIMSEQ_imp_Cauchy)
  with \<open>complete S\<close> and \<open>\<forall>n. f n \<in> S\<close> obtain l where "l \<in> S" and "f \<longlonglongrightarrow> l"
    by (rule completeE)
  from \<open>f \<longlonglongrightarrow> x\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "x = l"
    by (rule LIMSEQ_unique)
  with \<open>l \<in> S\<close> show "x \<in> S"
    by simp
qed

lemma complete_Int_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S" and "closed t"
  shows "complete (S \<inter> t)"
proof (rule completeI)
  fix f assume "\<forall>n. f n \<in> S \<inter> t" and "Cauchy f"
  then have "\<forall>n. f n \<in> S" and "\<forall>n. f n \<in> t"
    by simp_all
  from \<open>complete S\<close> obtain l where "l \<in> S" and "f \<longlonglongrightarrow> l"
    using \<open>\<forall>n. f n \<in> S\<close> and \<open>Cauchy f\<close> by (rule completeE)
  from \<open>closed t\<close> and \<open>\<forall>n. f n \<in> t\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "l \<in> t"
    by (rule closed_sequentially)
  with \<open>l \<in> S\<close> and \<open>f \<longlonglongrightarrow> l\<close> show "\<exists>l\<in>S \<inter> t. f \<longlonglongrightarrow> l"
    by fast
qed

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


subsubsection \<open>Properties of Balls and Spheres\<close>

lemma compact_cball[simp]:
  fixes x :: "'a::heine_borel"
  shows "compact (cball x e)"
  using compact_eq_bounded_closed bounded_cball closed_cball
  by blast

lemma compact_frontier_bounded[intro]:
  fixes S :: "'a::heine_borel set"
  shows "bounded S \<Longrightarrow> compact (frontier S)"
  unfolding frontier_def
  using compact_eq_bounded_closed
  by blast

lemma compact_frontier[intro]:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<Longrightarrow> compact (frontier S)"
  using compact_eq_bounded_closed compact_frontier_bounded
  by blast


subsubsection \<open>Distance from a Set\<close>

lemma distance_attains_sup:
  assumes "compact s" "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<forall>y\<in>s. dist a y \<le> dist a x"
proof (rule continuous_attains_sup [OF assms])
  {
    fix x
    assume "x\<in>s"
    have "(dist a \<longlongrightarrow> dist a x) (at x within s)"
      by (intro tendsto_dist tendsto_const tendsto_ident_at)
  }
  then show "continuous_on s (dist a)"
    unfolding continuous_on ..
qed

text \<open>For \emph{minimal} distance, we only need closure, not compactness.\<close>

lemma distance_attains_inf:
  fixes a :: "'a::heine_borel"
  assumes "closed s" and "s \<noteq> {}"
  obtains x where "x\<in>s" "\<And>y. y \<in> s \<Longrightarrow> dist a x \<le> dist a y"
proof -
  from assms obtain b where "b \<in> s" by auto
  let ?B = "s \<inter> cball a (dist b a)"
  have "?B \<noteq> {}" using \<open>b \<in> s\<close>
    by (auto simp: dist_commute)
  moreover have "continuous_on ?B (dist a)"
    by (auto intro!: continuous_at_imp_continuous_on continuous_dist continuous_ident continuous_const)
  moreover have "compact ?B"
    by (intro closed_Int_compact \<open>closed s\<close> compact_cball)
  ultimately obtain x where "x \<in> ?B" "\<forall>y\<in>?B. dist a x \<le> dist a y"
    by (metis continuous_attains_inf)
  with that show ?thesis by fastforce
qed

subsection \<open>Infimum Distance\<close>

definition%important "infdist x A = (if A = {} then 0 else INF a\<in>A. dist x a)"

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
      unfolding infdist_notempty[OF \<open>A \<noteq> {}\<close>]
    proof (rule cINF_lower2)
      show "a \<in> A" by fact
      show "dist x a \<le> d"
        unfolding d by (rule dist_triangle)
    qed simp
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
      apply auto
      apply (metis \<open>x \<in> closure A\<close> closure_approachable dist_commute infdist_le not_less)
      done
    then have "x \<notin> closure A"
      by (metis \<open>0 < infdist x A\<close> centre_in_ball disjoint_iff_not_equal)
    then show False using \<open>x \<in> closure A\<close> by simp
  qed
next
  assume x: "infdist x A = 0"
  then obtain a where "a \<in> A"
    by atomize_elim (metis all_not_in_conv assms)
  show "x \<in> closure A"
    unfolding closure_approachable
    apply safe
  proof (rule ccontr)
    fix e :: real
    assume "e > 0"
    assume "\<not> (\<exists>y\<in>A. dist y x < e)"
    then have "infdist x A \<ge> e" using \<open>a \<in> A\<close>
      unfolding infdist_def
      by (force simp: dist_commute intro: cINF_greatest)
    with x \<open>e > 0\<close> show False by auto
  qed
qed

lemma in_closed_iff_infdist_zero:
  assumes "closed A" "A \<noteq> {}"
  shows "x \<in> A \<longleftrightarrow> infdist x A = 0"
proof -
  have "x \<in> closure A \<longleftrightarrow> infdist x A = 0"
    by (rule in_closure_iff_infdist_zero) fact
  with assms show ?thesis by simp
qed

lemma infdist_pos_not_in_closed:
  assumes "closed S" "S \<noteq> {}" "x \<notin> S"
  shows "infdist x S > 0"
using in_closed_iff_infdist_zero[OF assms(1) assms(2), of x] assms(3) infdist_nonneg le_less by fastforce

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
  obtain x where INF: "x \<in> X" "\<And>z. z \<in> X \<Longrightarrow> dist y x \<le> dist y z" by auto
  have "infdist y X = dist y x"
    by (auto simp: infdist_def assms
      intro!: antisym cINF_lower[OF _ \<open>x \<in> X\<close>] cINF_greatest[OF assms(2) INF(2)])
  with \<open>x \<in> X\<close> show ?thesis ..
qed


text \<open>Every metric space is a T4 space:\<close>

instance metric_space \<subseteq> t4_space
proof
  fix S T::"'a set" assume H: "closed S" "closed T" "S \<inter> T = {}"
  consider "S = {}" | "T = {}" | "S \<noteq> {} \<and> T \<noteq> {}" by auto
  then show "\<exists>U V. open U \<and> open V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> U \<inter> V = {}"
  proof (cases)
    case 1
    show ?thesis
      apply (rule exI[of _ "{}"], rule exI[of _ UNIV]) using 1 by auto
  next
    case 2
    show ?thesis
      apply (rule exI[of _ UNIV], rule exI[of _ "{}"]) using 2 by auto
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
    proof (auto)
      fix z assume H: "dist x z * 2 < infdist x T" "dist y z * 2 < infdist y S"
      have "2 * dist x y \<le> 2 * dist x z + 2 * dist y z"
        using dist_triangle[of x y z] by (auto simp add: dist_commute)
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
      apply (rule exI[of _ U], rule exI[of _ V]) using A B C D E by auto
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
    assume le: "infdist y A \<le> e"
    from infdist_attains_inf[OF \<open>closed A\<close> \<open>A \<noteq> {}\<close>, of y]
    obtain z where z: "z \<in> A" "infdist y A = dist y z" by blast
    have "dist x0 y \<le> dist y z + dist x0 z"
      by (metis dist_commute dist_triangle)
    also have "dist y z \<le> e" using le z by simp
    also have "dist x0 z \<le> b" using b z by simp
    finally have "dist x0 y \<le> b + e" by arith
  } then
  have "bounded {x. infdist x A \<le> e}"
    by (auto simp: bounded_any_center[where a=x0] intro!: exI[where x="b + e"])
  ultimately show "compact {x. infdist x A \<le> e}"
    by (simp add: compact_eq_bounded_closed)
qed


subsection \<open>Continuity\<close>

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
  apply (intro all_cong ex_cong, safe)
  apply (erule_tac x="a + d" in allE, simp)
  apply (simp add: nondecF field_simps)
  apply (drule nondecF, simp)
  done

lemma continuous_at_left_real_increasing:
  assumes nondecF: "\<And> x y. x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
  shows "(continuous (at_left (a :: real)) f) = (\<forall>e > 0. \<exists>delta > 0. f a - f (a - delta) < e)"
  apply (simp add: lessThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong, safe)
  apply (erule_tac x="a - d" in allE, simp)
  apply (simp add: nondecF field_simps)
  apply (cut_tac x="a - d" and y=x in nondecF, simp_all)
  done

text\<open>Versions in terms of open balls.\<close>

lemma continuous_within_ball:
  "continuous (at x within s) f \<longleftrightarrow>
    (\<forall>e > 0. \<exists>d > 0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix e :: real
    assume "e > 0"
    then obtain d where d: "d>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e"
      using \<open>?lhs\<close>[unfolded continuous_within Lim_within] by auto
    {
      fix y
      assume "y \<in> f ` (ball x d \<inter> s)"
      then have "y \<in> ball (f x) e"
        using d(2)
        apply (auto simp: dist_commute)
        apply (erule_tac x=xa in ballE, auto)
        using \<open>e > 0\<close>
        apply auto
        done
    }
    then have "\<exists>d>0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e"
      using \<open>d > 0\<close>
      unfolding subset_eq ball_def by (auto simp: dist_commute)
  }
  then show ?rhs by auto
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_within Lim_within ball_def subset_eq
    apply (auto simp: dist_commute)
    apply (erule_tac x=e in allE, auto)
    done
qed

lemma continuous_at_ball:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f ` (ball x d) \<subseteq> ball (f x) e)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto
    apply (erule_tac x=e in allE, auto)
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x=xa in allE)
    apply (auto simp: dist_commute)
    done
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto
    apply (erule_tac x=e in allE, auto)
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x="f xa" in allE)
    apply (auto simp: dist_commute)
    done
qed

text\<open>Define setwise continuity in terms of limits within the set.\<close>

lemma continuous_on_iff:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  unfolding continuous_on_def Lim_within
  by (metis dist_pos_lt dist_self)

lemma continuous_within_E:
  assumes "continuous (at x within s) f" "e>0"
  obtains d where "d>0"  "\<And>x'. \<lbrakk>x'\<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms apply (simp add: continuous_within_eps_delta)
  apply (drule spec [of _ e], clarify)
  apply (rule_tac d="d/2" in that, auto)
  done

lemma continuous_onI [intro?]:
  assumes "\<And>x e. \<lbrakk>e > 0; x \<in> s\<rbrakk> \<Longrightarrow> \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) \<le> e"
  shows "continuous_on s f"
apply (simp add: continuous_on_iff, clarify)
apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
done

text\<open>Some simple consequential lemmas.\<close>

lemma continuous_onE:
    assumes "continuous_on s f" "x\<in>s" "e>0"
    obtains d where "d>0"  "\<And>x'. \<lbrakk>x' \<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms
  apply (simp add: continuous_on_iff)
  apply (elim ballE allE)
  apply (auto intro: that [where d="d/2" for d])
  done

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
        using \<open>?lhs\<close>[unfolded uniformly_continuous_on_def, THEN spec[where x=e]] by auto
      obtain N where N: "\<forall>n\<ge>N. dist (x n) (y n) < d"
        using xy[unfolded lim_sequentially dist_norm] and \<open>d>0\<close> by auto
      {
        fix n
        assume "n\<ge>N"
        then have "dist (f (x n)) (f (y n)) < e"
          using N[THEN spec[where x=n]]
          using d[THEN bspec[where x="x n"], THEN bspec[where x="y n"]]
          using x and y
          by (simp add: dist_commute)
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
        by auto
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
      unfolding Bex_def
      by (auto simp: dist_commute)
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
      {
        fix n :: nat
        assume "n \<ge> N"
        then have "inverse (real n + 1) < inverse (real N)"
          using of_nat_0_le_iff and \<open>N\<noteq>0\<close> by auto
        also have "\<dots> < e" using N by auto
        finally have "inverse (real n + 1) < e" by auto
        then have "dist (x n) (y n) < e"
          using xy0[THEN spec[where x=n]] by auto
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (x n) (y n) < e" by auto
    }
    then have "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
      using \<open>?rhs\<close>[THEN spec[where x=x], THEN spec[where x=y]] and xyn
      unfolding lim_sequentially dist_real_def by auto
    then have False using fxy and \<open>e>0\<close> by auto
  }
  then show ?lhs
    unfolding uniformly_continuous_on_def by blast
qed

lemma continuous_closed_imp_Cauchy_continuous:
  fixes S :: "('a::complete_space) set"
  shows "\<lbrakk>continuous_on S f; closed S; Cauchy \<sigma>; \<And>n. (\<sigma> n) \<in> S\<rbrakk> \<Longrightarrow> Cauchy(f \<circ> \<sigma>)"
  apply (simp add: complete_eq_closed [symmetric] continuous_on_sequentially)
  by (meson LIMSEQ_imp_Cauchy complete_def)

text\<open>The usual transformation theorems.\<close>

lemma continuous_transform_within:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at x within s) f"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x' \<in> s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "continuous (at x within s) g"
  using assms
  unfolding continuous_within
  by (force intro: Lim_transform_within)

subsubsection%unimportant \<open>Structural rules for uniform continuity\<close>

lemma (in bounded_linear) uniformly_continuous_on[continuous_intros]:
  fixes g :: "_::metric_space \<Rightarrow> _"
  assumes "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f (g x))"
  using assms unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff diff[symmetric]
  by (auto intro: tendsto_zero)

subsection%unimportant\<open> Theorems relating continuity and uniform continuity to closures\<close>

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
        apply (rule \<delta>' [OF \<open>z \<in> S\<close>])
        using z \<open>0 < \<delta>'\<close> by linarith
      moreover have "dist (f z) (f x) < e/2"
        apply (rule \<delta> [OF \<open>z \<in> S\<close>])
        using z \<open>0 < \<delta>\<close>  dist_commute[of y z] dist_triangle_half_r [of y] dyx by auto
      ultimately show ?thesis
        by (metis dist_commute dist_triangle_half_l less_imp_le)
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
     moreover have "dist x y < d/3"
       by (metis dist_commute dyx less_divide_eq_numeral1(1))
     moreover have "dist y y' < d/3"
       by (metis (no_types) dist_commute min_less_iff_conj y')
     ultimately have "dist x' y' < d/3 + d/3 + d/3"
       by (meson dist_commute_lessI dist_triangle_lt add_strict_mono)
     then have "dist x' y' < d" by simp
     then have "dist (f x') (f y') < e/3"
       by (rule d [OF \<open>y' \<in> S\<close> \<open>x' \<in> S\<close>])
     moreover have "dist (f x') (f x) < e/3" using \<open>x' \<in> S\<close> closure_subset x' d1
       by (simp add: closure_def)
     moreover have "dist (f y') (f y) < e/3" using \<open>y' \<in> S\<close> closure_subset y' d2
       by (simp add: closure_def)
     ultimately have "dist (f y) (f x) < e/3 + e/3 + e/3"
       by (meson dist_commute_lessI dist_triangle_lt add_strict_mono)
    then show "dist (f y) (f x) < e" by simp
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
  proof (safe intro!: Lim_within_LIMSEQ)
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
      define e' where "e' \<equiv> e / 2"
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
          by (metis dist_triangle dist_commute)
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
    apply atomize_elim
    apply (rule choice)
    using uniformly_continuous_on_extension_at_closure[OF assms]
    by metis
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
        {
          have "dist (xs' n) (xs n) \<le> dist (xs' n) x' + dist x' x + dist (xs n) x"
            by (metis add.commute add_le_cancel_left  dist_triangle dist_triangle_le)
          also note \<open>dist (xs' n) x' < d'\<close>
          also note \<open>dist x' x < d'\<close>
          also note \<open>dist (xs n) x < d'\<close>
          finally have "dist (xs' n) (xs n) < d" by (simp add: d'_def)
        }
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
        by (auto simp: set_mp extension)
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
  by (metis (no_types, lifting) assms bounded_closure_image compact_closure compact_continuous_image compact_eq_bounded_closed image_cong uniformly_continuous_imp_continuous uniformly_continuous_on_extension_on_closure)


subsection \<open>With Abstract Topology (TODO: move and remove dependency?)\<close>

lemma openin_contains_ball:
    "openin (subtopology euclidean t) s \<longleftrightarrow>
     s \<subseteq> t \<and> (\<forall>x \<in> s. \<exists>e. 0 < e \<and> ball x e \<inter> t \<subseteq> s)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: openin_open)
    apply (metis Int_commute Int_mono inf.cobounded2 open_contains_ball order_refl subsetCE)
    done
next
  assume ?rhs
  then show ?lhs
    apply (simp add: openin_euclidean_subtopology_iff)
    by (metis (no_types) Int_iff dist_commute inf.absorb_iff2 mem_ball)
qed

lemma openin_contains_cball:
   "openin (subtopology euclidean t) s \<longleftrightarrow>
        s \<subseteq> t \<and>
        (\<forall>x \<in> s. \<exists>e. 0 < e \<and> cball x e \<inter> t \<subseteq> s)"
apply (simp add: openin_contains_ball)
apply (rule iffI)
apply (auto dest!: bspec)
apply (rule_tac x="e/2" in exI, force+)
  done

subsection \<open>With abstract Topology\<close>

lemma Times_in_interior_subtopology:
  fixes U :: "('a::metric_space \<times> 'b::metric_space) set"
  assumes "(x, y) \<in> U" "openin (subtopology euclidean (S \<times> T)) U"
  obtains V W where "openin (subtopology euclidean S) V" "x \<in> V"
                    "openin (subtopology euclidean T) W" "y \<in> W" "(V \<times> W) \<subseteq> U"
proof -
  from assms obtain e where "e > 0" and "U \<subseteq> S \<times> T"
    and e: "\<And>x' y'. \<lbrakk>x'\<in>S; y'\<in>T; dist (x', y') (x, y) < e\<rbrakk> \<Longrightarrow> (x', y') \<in> U"
    by (force simp: openin_euclidean_subtopology_iff)
  with assms have "x \<in> S" "y \<in> T"
    by auto
  show ?thesis
  proof
    show "openin (subtopology euclidean S) (ball x (e/2) \<inter> S)"
      by (simp add: Int_commute openin_open_Int)
    show "x \<in> ball x (e / 2) \<inter> S"
      by (simp add: \<open>0 < e\<close> \<open>x \<in> S\<close>)
    show "openin (subtopology euclidean T) (ball y (e/2) \<inter> T)"
      by (simp add: Int_commute openin_open_Int)
    show "y \<in> ball y (e / 2) \<inter> T"
      by (simp add: \<open>0 < e\<close> \<open>y \<in> T\<close>)
    show "(ball x (e / 2) \<inter> S) \<times> (ball y (e / 2) \<inter> T) \<subseteq> U"
      by clarify (simp add: e dist_Pair_Pair \<open>0 < e\<close> dist_commute sqrt_sum_squares_half_less)
  qed
qed

lemma openin_Times_eq:
  fixes S :: "'a::metric_space set" and T :: "'b::metric_space set"
  shows
    "openin (subtopology euclidean (S \<times> T)) (S' \<times> T') \<longleftrightarrow>
      S' = {} \<or> T' = {} \<or> openin (subtopology euclidean S) S' \<and> openin (subtopology euclidean T) T'"
    (is "?lhs = ?rhs")
proof (cases "S' = {} \<or> T' = {}")
  case True
  then show ?thesis by auto
next
  case False
  then obtain x y where "x \<in> S'" "y \<in> T'"
    by blast
  show ?thesis
  proof
    assume ?lhs
    have "openin (subtopology euclidean S) S'"
      apply (subst openin_subopen, clarify)
      apply (rule Times_in_interior_subtopology [OF _ \<open>?lhs\<close>])
      using \<open>y \<in> T'\<close>
       apply auto
      done
    moreover have "openin (subtopology euclidean T) T'"
      apply (subst openin_subopen, clarify)
      apply (rule Times_in_interior_subtopology [OF _ \<open>?lhs\<close>])
      using \<open>x \<in> S'\<close>
       apply auto
      done
    ultimately show ?rhs
      by simp
  next
    assume ?rhs
    with False show ?lhs
      by (simp add: openin_Times)
  qed
qed

lemma closedin_Times:
  "closedin (subtopology euclidean S) S' \<Longrightarrow> closedin (subtopology euclidean T) T' \<Longrightarrow>
    closedin (subtopology euclidean (S \<times> T)) (S' \<times> T')"
  unfolding closedin_closed using closed_Times by blast

lemma Lim_transform_within_openin:
  fixes a :: "'a::metric_space"
  assumes f: "(f \<longlongrightarrow> l) (at a within T)"
    and "openin (subtopology euclidean T) S" "a \<in> S"
    and eq: "\<And>x. \<lbrakk>x \<in> S; x \<noteq> a\<rbrakk> \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) (at a within T)"
proof -
  obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball a \<epsilon> \<inter> T \<subseteq> S"
    using assms by (force simp: openin_contains_ball)
  then have "a \<in> ball a \<epsilon>"
    by simp
  show ?thesis
    by (rule Lim_transform_within [OF f \<open>0 < \<epsilon>\<close> eq]) (use \<epsilon> in \<open>auto simp: dist_commute subset_iff\<close>)
qed

lemma closure_Int_ballI:
  fixes S :: "'a :: metric_space set"
  assumes "\<And>U. \<lbrakk>openin (subtopology euclidean S) U; U \<noteq> {}\<rbrakk> \<Longrightarrow> T \<inter> U \<noteq> {}"
 shows "S \<subseteq> closure T"
proof (clarsimp simp: closure_approachable dist_commute)
  fix x and e::real
  assume "x \<in> S" "0 < e"
  with assms [of "S \<inter> ball x e"] show "\<exists>y\<in>T. dist x y < e"
    by force
qed

lemma continuous_on_open_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. openin (subtopology euclidean T) U
                  \<longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` U))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (clarsimp simp: openin_euclidean_subtopology_iff continuous_on_iff)
    by (metis assms image_subset_iff)
next
  have ope: "openin (subtopology euclidean T) (ball y e \<inter> T)" for y e
    by (simp add: Int_commute openin_open_Int)
  assume R [rule_format]: ?rhs
  show ?lhs
  proof (clarsimp simp add: continuous_on_iff)
    fix x and e::real
    assume "x \<in> S" and "0 < e"
    then have x: "x \<in> S \<inter> (f -` ball (f x) e \<inter> f -` T)"
      using assms by auto
    show "\<exists>d>0. \<forall>x'\<in>S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
      using R [of "ball (f x) e \<inter> T"] x
      by (fastforce simp add: ope openin_euclidean_subtopology_iff [of S] dist_commute)
  qed
qed

lemma continuous_openin_preimage:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  shows
   "\<lbrakk>continuous_on S f; f ` S \<subseteq> T; openin (subtopology euclidean T) U\<rbrakk>
        \<Longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` U)"
by (simp add: continuous_on_open_gen)

lemma continuous_on_closed_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. closedin (subtopology euclidean T) U
                  \<longrightarrow> closedin (subtopology euclidean S) (S \<inter> f -` U))"
     (is "?lhs = ?rhs")
proof -
  have *: "U \<subseteq> T \<Longrightarrow> S \<inter> f -` (T - U) = S - (S \<inter> f -` U)" for U
    using assms by blast
  show ?thesis
  proof
    assume L: ?lhs
    show ?rhs
    proof clarify
      fix U
      assume "closedin (subtopology euclidean T) U"
      then show "closedin (subtopology euclidean S) (S \<inter> f -` U)"
        using L unfolding continuous_on_open_gen [OF assms]
        by (metis * closedin_def inf_le1 topspace_euclidean_subtopology)
    qed
  next
    assume R [rule_format]: ?rhs
    show ?lhs
      unfolding continuous_on_open_gen [OF assms]
      by (metis * R inf_le1 openin_closedin_eq topspace_euclidean_subtopology)
  qed
qed

lemma continuous_closedin_preimage_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on S f" "f ` S \<subseteq> T" "closedin (subtopology euclidean T) U"
    shows "closedin (subtopology euclidean S) (S \<inter> f -` U)"
using assms continuous_on_closed_gen by blast

lemma continuous_transform_within_openin:
  fixes a :: "'a::metric_space"
  assumes "continuous (at a within T) f"
    and "openin (subtopology euclidean T) S" "a \<in> S"
    and eq: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "continuous (at a within T) g"
  using assms by (simp add: Lim_transform_within_openin continuous_within)


subsection \<open>Closed Nest\<close>

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
      by (rule closed_sequentially)
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
  have "\<forall>n. \<exists>x. x \<in> S n"
    using assms(2) by auto
  then have "\<exists>t. \<forall>n. t n \<in> S n"
    using choice[of "\<lambda>n x. x \<in> S n"] by auto
  then obtain t where t: "\<forall>n. t n \<in> S n" by auto
  {
    fix e :: real
    assume "e > 0"
    then obtain N where N: "\<forall>x\<in>S N. \<forall>y\<in>S N. dist x y < e"
      using assms(4) by blast
    {
      fix m n :: nat
      assume "N \<le> m \<and> N \<le> n"
      then have "t m \<in> S N" "t n \<in> S N"
        using assms(3) t unfolding  subset_eq t by blast+
      then have "dist (t m) (t n) < e"
        using N by auto
    }
    then have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (t m) (t n) < e"
      by auto
  }
  then have "Cauchy t"
    unfolding cauchy_def by auto
  then obtain l where l:"(t \<longlongrightarrow> l) sequentially"
    using complete_UNIV unfolding complete_def by auto
  { fix n :: nat
    { fix e :: real
      assume "e > 0"
      then obtain N :: nat where N: "\<forall>n\<ge>N. dist (t n) l < e"
        using l[unfolded lim_sequentially] by auto
      have "t (max n N) \<in> S n"
        by (meson assms(3) contra_subsetD max.cobounded1 t)
      then have "\<exists>y\<in>S n. dist y l < e"
        using N max.cobounded2 by blast
    }
    then have "l \<in> S n"
      using closed_approachable[of "S n" l] assms(1) by auto
  }
  then show ?thesis
    using that by blast
qed

text \<open>Strengthen it to the intersection actually being a singleton.\<close>

lemma decreasing_closed_nest_sing:
  fixes S :: "nat \<Rightarrow> 'a::complete_space set"
  assumes "\<And>n. closed(S n)"
          "\<And>n. S n \<noteq> {}"
          "\<And>m n. m \<le> n \<Longrightarrow> S n \<subseteq> S m"
          "\<And>e. e>0 \<Longrightarrow> \<exists>n. \<forall>x \<in> (S n). \<forall> y\<in>(S n). dist x y < e"
  shows "\<exists>a. \<Inter>(range S) = {a}"
proof -
  obtain a where a: "\<forall>n. a \<in> S n"
    using decreasing_closed_nest[of S] using assms by auto
  { fix b
    assume b: "b \<in> \<Inter>(range S)"
    { fix e :: real
      assume "e > 0"
      then have "dist a b < e"
        using assms(4) and b and a by blast
    }
    then have "dist a b = 0"
      by (metis dist_eq_0_iff dist_nz less_le)
  }
  with a have "\<Inter>(range S) = {a}"
    unfolding image_def by auto
  then show ?thesis ..
qed

subsection%unimportant \<open>Making a continuous function avoid some value in a neighbourhood\<close>

lemma continuous_within_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous (at x within s) f"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> s. dist x y < e --> f y \<noteq> a"
proof -
  obtain U where "open U" and "f x \<in> U" and "a \<notin> U"
    using t1_space [OF \<open>f x \<noteq> a\<close>] by fast
  have "(f \<longlongrightarrow> f x) (at x within s)"
    using assms(1) by (simp add: continuous_within)
  then have "eventually (\<lambda>y. f y \<in> U) (at x within s)"
    using \<open>open U\<close> and \<open>f x \<in> U\<close>
    unfolding tendsto_def by fast
  then have "eventually (\<lambda>y. f y \<noteq> a) (at x within s)"
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
  assumes "continuous_on s f"
    and "x \<in> s"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> s. dist x y < e \<longrightarrow> f y \<noteq> a"
  using assms(1)[unfolded continuous_on_eq_continuous_within, THEN bspec[where x=x],
    OF assms(2)] continuous_within_avoid[of x s f a]
  using assms(3)
  by auto

lemma continuous_on_open_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous_on s f"
    and "open s"
    and "x \<in> s"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
  using assms(1)[unfolded continuous_on_eq_continuous_at[OF assms(2)], THEN bspec[where x=x], OF assms(3)]
  using continuous_at_avoid[of x f a] assms(4)
  by auto


end