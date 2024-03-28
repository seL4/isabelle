(*
  Material originally from HOL Light, ported by Larry Paulson, moved here by Manuel Eberl
*)
section\<^marker>\<open>tag unimportant\<close> \<open>Smooth paths\<close>
theory Smooth_Paths
  imports Retracts
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Homeomorphisms of arc images\<close>

lemma path_connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "path_connected(- path_image \<gamma>)"
proof -
  have "path_image \<gamma> homeomorphic {0..1::real}"
    by (simp add: assms homeomorphic_arc_image_interval)
  then show ?thesis
    by (intro path_connected_complement_homeomorphic_convex_compact) (auto simp: assms)
qed

lemma connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "connected(- path_image \<gamma>)"
  by (simp add: assms path_connected_arc_complement path_connected_imp_connected)

lemma inside_arc_empty:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>"
    shows "inside(path_image \<gamma>) = {}"
proof (cases "DIM('a) = 1")
  case True
  then show ?thesis
    using assms connected_arc_image connected_convex_1_gen inside_convex by blast
next
  case False
  then have "connected (- path_image \<gamma>)"
      by (metis DIM_ge_Suc0 One_nat_def Suc_1 antisym assms connected_arc_complement not_less_eq_eq)
    then
  show ?thesis
    by (simp add: assms bounded_arc_image inside_bounded_complement_connected_empty)
qed

lemma inside_simple_curve_imp_closed:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
    shows "\<lbrakk>simple_path \<gamma>; x \<in> inside(path_image \<gamma>)\<rbrakk> \<Longrightarrow> pathfinish \<gamma> = pathstart \<gamma>"
  using arc_simple_path  inside_arc_empty by blast


subsection \<open>Piecewise differentiability of paths\<close>

lemma continuous_on_joinpaths_D1:
  assumes "continuous_on {0..1} (g1 +++ g2)"
  shows "continuous_on {0..1} g1"
proof (rule continuous_on_eq)
  have "continuous_on {0..1/2} (g1 +++ g2)"
    using assms continuous_on_subset split_01 by auto
  then show "continuous_on {0..1} (g1 +++ g2 \<circ> (*) (inverse 2))"
    by (intro continuous_intros) force
qed (auto simp: joinpaths_def)

lemma continuous_on_joinpaths_D2:
    "\<lbrakk>continuous_on {0..1} (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> continuous_on {0..1} g2"
  using path_def path_join by blast

lemma piecewise_differentiable_D1:
  assumes "(g1 +++ g2) piecewise_differentiable_on {0..1}"
  shows "g1 piecewise_differentiable_on {0..1}"
proof -
  obtain S where cont: "continuous_on {0..1} g1" and "finite S"
    and S: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> g1 +++ g2 differentiable at x within {0..1}"
    using assms unfolding piecewise_differentiable_on_def
    by (blast dest!: continuous_on_joinpaths_D1)
  show ?thesis
    unfolding piecewise_differentiable_on_def
  proof (intro exI conjI ballI cont)
    show "finite (insert 1 (((*)2) ` S))"
      by (simp add: \<open>finite S\<close>)
    show "g1 differentiable at x within {0..1}" if "x \<in> {0..1} - insert 1 ((*) 2 ` S)" for x
    proof (rule_tac d="dist (x/2) (1/2)" in differentiable_transform_within)
      have "g1 +++ g2 differentiable at (x / 2) within {0..1/2}"
        by (rule differentiable_subset [OF S [of "x/2"]] | use that in force)+
      then show "g1 +++ g2 \<circ> (*) (inverse 2) differentiable at x within {0..1}"
        using image_affinity_atLeastAtMost_div [of 2 0 "0::real" 1]
        by (auto intro: differentiable_chain_within)
    qed (use that in \<open>auto simp: joinpaths_def\<close>)
  qed
qed

lemma piecewise_differentiable_D2:
  assumes "(g1 +++ g2) piecewise_differentiable_on {0..1}" and eq: "pathfinish g1 = pathstart g2"
  shows "g2 piecewise_differentiable_on {0..1}"
proof -
  have [simp]: "g1 1 = g2 0"
    using eq by (simp add: pathfinish_def pathstart_def)
  obtain S where cont: "continuous_on {0..1} g2" and "finite S"
    and S: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> g1 +++ g2 differentiable at x within {0..1}"
    using assms unfolding piecewise_differentiable_on_def
    by (blast dest!: continuous_on_joinpaths_D2)
  show ?thesis
    unfolding piecewise_differentiable_on_def
  proof (intro exI conjI ballI cont)
    show "finite (insert 0 ((\<lambda>x. 2*x-1)`S))"
      by (simp add: \<open>finite S\<close>)
    show "g2 differentiable at x within {0..1}" if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1)`S)" for x
    proof (rule_tac d="dist ((x+1)/2) (1/2)" in differentiable_transform_within)
      have x2: "(x + 1) / 2 \<notin> S"
        using that
        apply (clarsimp simp: image_iff)
        by (metis add.commute add_diff_cancel_left' mult_2 field_sum_of_halves)
      have "g1 +++ g2 \<circ> (\<lambda>x. (x+1) / 2) differentiable at x within {0..1}"
        by (rule differentiable_chain_within differentiable_subset [OF S [of "(x+1)/2"]] | use x2 that in force)+
      then show "g1 +++ g2 \<circ> (\<lambda>x. (x+1) / 2) differentiable at x within {0..1}"
        by (auto intro: differentiable_chain_within)
      show "(g1 +++ g2 \<circ> (\<lambda>x. (x + 1) / 2)) x' = g2 x'" if "x' \<in> {0..1}" "dist x' x < dist ((x + 1) / 2) (1/2)" for x'
      proof -
        have [simp]: "(2*x'+2)/2 = x'+1"
          by (simp add: field_split_simps)
        show ?thesis
          using that by (auto simp: joinpaths_def)
      qed
    qed (use that in \<open>auto simp: joinpaths_def\<close>)
  qed
qed

lemma piecewise_C1_differentiable_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}"
    shows "g1 piecewise_C1_differentiable_on {0..1}"
proof -
  obtain S where "finite S"
             and co12: "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
             and g12D: "\<forall>x\<in>{0..1} - S. g1 +++ g2 differentiable at x"
    using assms  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have g1D: "g1 differentiable at x" if "x \<in> {0..1} - insert 1 ((*) 2 ` S)" for x
  proof (rule differentiable_transform_within)
    show "g1 +++ g2 \<circ> (*) (inverse 2) differentiable at x"
      using that g12D
      unfolding joinpaths_def
      by (intro differentiable_chain_at derivative_intros | force)+
    show "\<And>x'. \<lbrakk>dist x' x < dist (x/2) (1/2)\<rbrakk>
          \<Longrightarrow> (g1 +++ g2 \<circ> (*) (inverse 2)) x' = g1 x'"
      using that by (auto simp: dist_real_def joinpaths_def)
  qed (use that in \<open>auto simp: dist_real_def\<close>)
  have [simp]: "vector_derivative (g1 \<circ> (*) 2) (at (x/2)) = 2 *\<^sub>R vector_derivative g1 (at x)"
               if "x \<in> {0..1} - insert 1 ((*) 2 ` S)" for x
    apply (subst vector_derivative_chain_at)
    using that
    apply (rule derivative_eq_intros g1D | simp)+
    done
  have "continuous_on ({0..1/2} - insert (1/2) S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
    using co12 by (rule continuous_on_subset) force
  then have coDhalf: "continuous_on ({0..1/2} - insert (1/2) S) (\<lambda>x. vector_derivative (g1 \<circ> (*)2) (at x))"
  proof (rule continuous_on_eq [OF _ vector_derivative_at])
    show "(g1 +++ g2 has_vector_derivative vector_derivative (g1 \<circ> (*) 2) (at x)) (at x)"
      if "x \<in> {0..1/2} - insert (1/2) S" for x
    proof (rule has_vector_derivative_transform_within)
      show "(g1 \<circ> (*) 2 has_vector_derivative vector_derivative (g1 \<circ> (*) 2) (at x)) (at x)"
        using that
        by (force intro: g1D differentiable_chain_at simp: vector_derivative_works [symmetric])
      show "\<And>x'. \<lbrakk>dist x' x < dist x (1/2)\<rbrakk> \<Longrightarrow> (g1 \<circ> (*) 2) x' = (g1 +++ g2) x'"
        using that by (auto simp: dist_norm joinpaths_def)
    qed (use that in \<open>auto simp: dist_norm\<close>)
  qed
  have "continuous_on ({0..1} - insert 1 ((*) 2 ` S))
                      ((\<lambda>x. 1/2 * vector_derivative (g1 \<circ> (*)2) (at x)) \<circ> (*)(1/2))"
    using coDhalf
    apply (intro continuous_intros)
    by (simp add: scaleR_conv_of_real image_set_diff image_image)
  then have con_g1: "continuous_on ({0..1} - insert 1 ((*) 2 ` S)) (\<lambda>x. vector_derivative g1 (at x))"
    by (rule continuous_on_eq) (simp add: scaleR_conv_of_real)
  have "continuous_on {0..1} g1"
    using continuous_on_joinpaths_D1 assms piecewise_C1_differentiable_on_def by blast
  with \<open>finite S\<close> show ?thesis
    apply (clarsimp simp add: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    apply (rule_tac x="insert 1 (((*)2)`S)" in exI)
    apply (simp add: g1D con_g1)
  done
qed

lemma piecewise_C1_differentiable_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}" "pathfinish g1 = pathstart g2"
    shows "g2 piecewise_C1_differentiable_on {0..1}"
proof -
  obtain S where "finite S"
             and co12: "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
             and g12D: "\<forall>x\<in>{0..1} - S. g1 +++ g2 differentiable at x"
    using assms  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have g2D: "g2 differentiable at x" if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S)" for x
  proof (rule differentiable_transform_within)
    show "g1 +++ g2 \<circ> (\<lambda>x. (x + 1) / 2) differentiable at x"
      using g12D that
      unfolding joinpaths_def
      apply (drule_tac x= "(x+1) / 2" in bspec, force simp: field_split_simps)
      apply (rule differentiable_chain_at derivative_intros | force)+
      done
    show "\<And>x'. dist x' x < dist ((x + 1) / 2) (1/2) \<Longrightarrow> (g1 +++ g2 \<circ> (\<lambda>x. (x + 1) / 2)) x' = g2 x'"
      using that by (auto simp: dist_real_def joinpaths_def field_simps)
    qed (use that in \<open>auto simp: dist_norm\<close>)
  have [simp]: "vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at ((x+1)/2)) = 2 *\<^sub>R vector_derivative g2 (at x)"
               if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S)" for x
    using that  by (auto simp: vector_derivative_chain_at field_split_simps g2D)
  have "continuous_on ({1/2..1} - insert (1/2) S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
    using co12 by (rule continuous_on_subset) force
  then have coDhalf: "continuous_on ({1/2..1} - insert (1/2) S) (\<lambda>x. vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at x))"
  proof (rule continuous_on_eq [OF _ vector_derivative_at])
    show "(g1 +++ g2 has_vector_derivative vector_derivative (g2 \<circ> (\<lambda>x. 2 * x - 1)) (at x))
          (at x)"
      if "x \<in> {1 / 2..1} - insert (1 / 2) S" for x
    proof (rule_tac f="g2 \<circ> (\<lambda>x. 2*x-1)" and d="dist (3/4) ((x+1)/2)" in has_vector_derivative_transform_within)
      show "(g2 \<circ> (\<lambda>x. 2 * x - 1) has_vector_derivative vector_derivative (g2 \<circ> (\<lambda>x. 2 * x - 1)) (at x))
            (at x)"
        using that by (force intro: g2D differentiable_chain_at simp: vector_derivative_works [symmetric])
      show "\<And>x'. \<lbrakk>dist x' x < dist (3 / 4) ((x + 1) / 2)\<rbrakk> \<Longrightarrow> (g2 \<circ> (\<lambda>x. 2 * x - 1)) x' = (g1 +++ g2) x'"
        using that by (auto simp: dist_norm joinpaths_def add_divide_distrib)
    qed (use that in \<open>auto simp: dist_norm\<close>)
  qed
  have [simp]: "((\<lambda>x. (x+1) / 2) ` ({0..1} - insert 0 ((\<lambda>x. 2 * x - 1) ` S))) = ({1/2..1} - insert (1/2) S)"
    apply (simp add: image_set_diff inj_on_def image_image)
    apply (auto simp: image_affinity_atLeastAtMost_div add_divide_distrib)
    done
  have "continuous_on ({0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S))
                      ((\<lambda>x. 1/2 * vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at x)) \<circ> (\<lambda>x. (x+1)/2))"
    by (rule continuous_intros | simp add:  coDhalf)+
  then have con_g2: "continuous_on ({0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S)) (\<lambda>x. vector_derivative g2 (at x))"
    by (rule continuous_on_eq) (simp add: scaleR_conv_of_real)
  have "continuous_on {0..1} g2"
    using continuous_on_joinpaths_D2 assms piecewise_C1_differentiable_on_def by blast
  with \<open>finite S\<close> show ?thesis
    by (meson C1_differentiable_on_eq con_g2 finite_imageI finite_insert g2D piecewise_C1_differentiable_on_def)
qed


subsection \<open>Valid paths, and their start and finish\<close>

definition\<^marker>\<open>tag important\<close> valid_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "valid_path f \<equiv> f piecewise_C1_differentiable_on {0..1::real}"

definition closed_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "closed_path g \<equiv> g 0 = g 1"

text\<open>In particular, all results for paths apply\<close>

lemma valid_path_imp_path: "valid_path g \<Longrightarrow> path g"
  by (simp add: path_def piecewise_C1_differentiable_on_def valid_path_def)

lemma connected_valid_path_image: "valid_path g \<Longrightarrow> connected(path_image g)"
  by (metis connected_path_image valid_path_imp_path)

lemma compact_valid_path_image: "valid_path g \<Longrightarrow> compact(path_image g)"
  by (metis compact_path_image valid_path_imp_path)

lemma bounded_valid_path_image: "valid_path g \<Longrightarrow> bounded(path_image g)"
  by (metis bounded_path_image valid_path_imp_path)

lemma closed_valid_path_image: "valid_path g \<Longrightarrow> closed(path_image g)"
  by (metis closed_path_image valid_path_imp_path)

lemma valid_path_translation_eq: "valid_path ((+)d \<circ> p) \<longleftrightarrow> valid_path p"
  by (simp add: valid_path_def piecewise_C1_differentiable_on_translation_eq)
 
lemma valid_path_compose:
  assumes "valid_path g"
      and der: "\<And>x. x \<in> path_image g \<Longrightarrow> f field_differentiable (at x)"
      and con: "continuous_on (path_image g) (deriv f)"
    shows "valid_path (f \<circ> g)"
proof -
  obtain S where "finite S" and g_diff: "g C1_differentiable_on {0..1} - S"
    using \<open>valid_path g\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto
  have "f \<circ> g differentiable at t" when "t\<in>{0..1} - S" for t
    proof (rule differentiable_chain_at)
      show "g differentiable at t" using \<open>valid_path g\<close>
        by (meson C1_differentiable_on_eq \<open>g C1_differentiable_on {0..1} - S\<close> that)
    next
      have "g t\<in>path_image g" using that DiffD1 image_eqI path_image_def by metis
      then show "f differentiable at (g t)"
        using der[THEN field_differentiable_imp_differentiable] by auto
    qed
  moreover have "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative (f \<circ> g) (at x))"
    proof (rule continuous_on_eq [where f = "\<lambda>x. vector_derivative g (at x) * deriv f (g x)"],
        rule continuous_intros)
      show "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative g (at x))"
        using g_diff C1_differentiable_on_eq by auto
    next
      have "continuous_on {0..1} (\<lambda>x. deriv f (g x))"
        using continuous_on_compose[OF _ con[unfolded path_image_def],unfolded comp_def]
          \<open>valid_path g\<close> piecewise_C1_differentiable_on_def valid_path_def
        by blast
      then show "continuous_on ({0..1} - S) (\<lambda>x. deriv f (g x))"
        using continuous_on_subset by blast
    next
      show "vector_derivative g (at t) * deriv f (g t) = vector_derivative (f \<circ> g) (at t)"
          when "t \<in> {0..1} - S" for t
        by (metis C1_differentiable_on_eq DiffD1 der g_diff imageI path_image_def that 
                  vector_derivative_chain_at_general)
    qed
  ultimately have "f \<circ> g C1_differentiable_on {0..1} - S"
    using C1_differentiable_on_eq by blast
  moreover have "path (f \<circ> g)"
    using der
    by (simp add: path_continuous_image[OF valid_path_imp_path[OF \<open>valid_path g\<close>]] continuous_at_imp_continuous_on field_differentiable_imp_continuous_at)
  ultimately show ?thesis unfolding valid_path_def piecewise_C1_differentiable_on_def path_def
    using \<open>finite S\<close> by auto
qed
  
lemma valid_path_uminus_comp[simp]:
  fixes g::"real \<Rightarrow> 'a ::real_normed_field"
  shows "valid_path (uminus \<circ> g) \<longleftrightarrow> valid_path g"
proof 
  show "valid_path g \<Longrightarrow> valid_path (uminus \<circ> g)" for g::"real \<Rightarrow> 'a"
    by (auto intro!: valid_path_compose derivative_intros)  
  then show "valid_path g" when "valid_path (uminus \<circ> g)"
    by (metis fun.map_comp group_add_class.minus_comp_minus id_comp that)
qed

lemma valid_path_offset[simp]:
  shows "valid_path (\<lambda>t. g t - z) \<longleftrightarrow> valid_path g"  
proof 
  show *: "valid_path (g::real\<Rightarrow>'a) \<Longrightarrow> valid_path (\<lambda>t. g t - z)" for g z
    unfolding valid_path_def
    by (fastforce intro:derivative_intros C1_differentiable_imp_piecewise piecewise_C1_differentiable_diff)
  show "valid_path (\<lambda>t. g t - z) \<Longrightarrow> valid_path g"
    using *[of "\<lambda>t. g t - z" "-z",simplified] .
qed

lemma valid_path_imp_reverse:
  assumes "valid_path g"
    shows "valid_path(reversepath g)"
proof -
  obtain S where "finite S" and S: "g C1_differentiable_on ({0..1} - S)"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  then have "finite ((-) 1 ` S)"
    by auto
  moreover have "(reversepath g C1_differentiable_on ({0..1} - (-) 1 ` S))"
    unfolding reversepath_def
    apply (rule C1_differentiable_compose [of "\<lambda>x::real. 1-x" _ g, unfolded o_def])
    using S
    by (force simp: finite_vimageI inj_on_def C1_differentiable_on_eq elim!: continuous_on_subset)+
  ultimately show ?thesis using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def path_def [symmetric])
qed

lemma valid_path_reversepath [simp]: "valid_path(reversepath g) \<longleftrightarrow> valid_path g"
  using valid_path_imp_reverse by force

lemma valid_path_join:
  assumes "valid_path g1" "valid_path g2" "pathfinish g1 = pathstart g2"
    shows "valid_path(g1 +++ g2)"
proof -
  have "g1 1 = g2 0"
    using assms by (auto simp: pathfinish_def pathstart_def)
  moreover have "(g1 \<circ> (\<lambda>x. 2*x)) piecewise_C1_differentiable_on {0..1/2}"
    apply (rule piecewise_C1_differentiable_compose)
    using assms
    apply (auto simp: valid_path_def piecewise_C1_differentiable_on_def continuous_on_joinpaths)
    apply (force intro: finite_vimageI [where h = "(*)2"] inj_onI)
    done
  moreover have "(g2 \<circ> (\<lambda>x. 2*x-1)) piecewise_C1_differentiable_on {1/2..1}"
    apply (rule piecewise_C1_differentiable_compose)
    using assms unfolding valid_path_def piecewise_C1_differentiable_on_def
    by (auto intro!: continuous_intros finite_vimageI [where h = "(\<lambda>x. 2*x - 1)"] inj_onI
             simp: image_affinity_atLeastAtMost_diff continuous_on_joinpaths)
  ultimately show ?thesis
    unfolding valid_path_def continuous_on_joinpaths joinpaths_def
    by (intro piecewise_C1_differentiable_cases) (auto simp: o_def)
qed

lemma valid_path_join_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "valid_path (g1 +++ g2) \<Longrightarrow> valid_path g1"
  unfolding valid_path_def
  by (rule piecewise_C1_differentiable_D1)

lemma valid_path_join_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>valid_path (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> valid_path g2"
  unfolding valid_path_def
  by (rule piecewise_C1_differentiable_D2)

lemma valid_path_join_eq [simp]:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "pathfinish g1 = pathstart g2 \<Longrightarrow> (valid_path(g1 +++ g2) \<longleftrightarrow> valid_path g1 \<and> valid_path g2)"
  using valid_path_join_D1 valid_path_join_D2 valid_path_join by blast

lemma valid_path_shiftpath [intro]:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "valid_path(shiftpath a g)"
  using assms
  unfolding valid_path_def shiftpath_alt_def
  apply (intro piecewise_C1_differentiable_cases)
      apply (simp_all add: add.commute)
    apply (rule piecewise_C1_differentiable_affine [of g 1 a, simplified o_def scaleR_one])
    apply (force simp: pathfinish_def pathstart_def elim: piecewise_C1_differentiable_on_subset)
   apply (rule piecewise_C1_differentiable_affine [of g 1 "a-1", simplified o_def scaleR_one algebra_simps])
   apply (auto simp: pathfinish_def pathstart_def elim: piecewise_C1_differentiable_on_subset)
  done

lemma vector_derivative_linepath_within:
    "x \<in> {0..1} \<Longrightarrow> vector_derivative (linepath a b) (at x within {0..1}) = b - a"
  by (simp add: has_vector_derivative_linepath_within vector_derivative_at_within_ivl)

lemma vector_derivative_linepath_at [simp]: "vector_derivative (linepath a b) (at x) = b - a"
  by (simp add: has_vector_derivative_linepath_within vector_derivative_at)

lemma valid_path_linepath [iff]: "valid_path (linepath a b)"
  using C1_differentiable_on_eq piecewise_C1_differentiable_on_def valid_path_def by fastforce

lemma valid_path_subpath:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "valid_path(subpath u v g)"
proof (cases "v=u")
  case True
  then show ?thesis
    unfolding valid_path_def subpath_def
    by (force intro: C1_differentiable_on_const C1_differentiable_imp_piecewise)
next
  case False
  let ?f = "\<lambda>x. ((v-u) * x + u)"
  have "(g \<circ> ?f) piecewise_C1_differentiable_on {0..1}"
  proof (rule piecewise_C1_differentiable_compose)
    show "?f piecewise_C1_differentiable_on {0..1}"
      by (simp add: C1_differentiable_imp_piecewise)
    have "g piecewise_C1_differentiable_on (if u \<le> v then {u..v} else {v..u})"
      using assms piecewise_C1_differentiable_on_subset valid_path_def by force
    then show "g piecewise_C1_differentiable_on ?f ` {0..1}"
      by (simp add: image_affinity_atLeastAtMost split: if_split_asm)
    show "\<And>x. finite ({0..1} \<inter> ?f -` {x})"
      using False
      by (simp add: Int_commute [of "{0..1}"] inj_on_def crossproduct_eq finite_vimage_IntI)
  qed
  then show ?thesis
    by (auto simp: o_def valid_path_def subpath_def)
qed

lemma valid_path_rectpath [simp, intro]: "valid_path (rectpath a b)"
  by (simp add: Let_def rectpath_def)

lemma linear_image_valid_path:
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes  "valid_path p" "linear f"
  shows    "valid_path (f \<circ> p)"
  unfolding valid_path_def piecewise_C1_differentiable_on_def
proof (intro conjI)
  from assms have "path p"
    by (simp add: valid_path_imp_path)
  thus "continuous_on {0..1} (f \<circ> p)"
    unfolding o_def path_def by (intro linear_continuous_on_compose[OF _ assms(2)])
  from assms(1) obtain S where S: "finite S" "p C1_differentiable_on {0..1} - S"
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  from S(2) obtain p' :: "real \<Rightarrow> 'a"
    where p': "\<And>x. x \<in> {0..1} - S \<Longrightarrow> (p has_vector_derivative p' x) (at x)"
              "continuous_on ({0..1} - S) p'"
    by (fastforce simp: C1_differentiable_on_def)

  have "(f \<circ> p has_vector_derivative f (p' x)) (at x)" if "x \<in> {0..1} - S" for x
    by (rule vector_derivative_diff_chain_within [OF p'(1)[OF that]]
             linear_imp_has_derivative assms)+
  moreover have "continuous_on ({0..1} - S) (\<lambda>x. f (p' x))"
    by (rule linear_continuous_on_compose [OF p'(2) assms(2)])
  ultimately have "f \<circ> p C1_differentiable_on {0..1} - S"
    unfolding C1_differentiable_on_def by (intro exI[of _ "\<lambda>x. f (p' x)"]) fast
  thus "\<exists>S. finite S \<and> f \<circ> p C1_differentiable_on {0..1} - S"
    using \<open>finite S\<close> by blast
qed

lemma valid_path_times:
  fixes \<gamma>::"real \<Rightarrow> 'a ::real_normed_field"
  assumes "c\<noteq>0"
  shows "valid_path ((*) c \<circ> \<gamma>) = valid_path \<gamma>"
proof 
  assume "valid_path ((*) c \<circ> \<gamma>)"
  then have "valid_path ((*) (1/c) \<circ> ((*) c \<circ> \<gamma>))"
    by (simp add: valid_path_compose)
  then show "valid_path \<gamma>" 
    unfolding comp_def using \<open>c\<noteq>0\<close> by auto
next
  assume "valid_path \<gamma>"
  then show "valid_path ((*) c \<circ> \<gamma>)"
    by (simp add: valid_path_compose)
qed

lemma path_compose_cnj_iff [simp]: "path (cnj \<circ> p) \<longleftrightarrow> path p"
proof -
  have "path (cnj \<circ> p)" if "path p" for p
    by (intro path_continuous_image continuous_intros that)
  from this[of p] and this[of "cnj \<circ> p"] show ?thesis
    by (auto simp: o_def)
qed

lemma valid_path_cnj:
  fixes g::"real \<Rightarrow> complex"
    shows "valid_path (cnj \<circ> g) = valid_path g"
proof
  show valid:"valid_path (cnj \<circ> g)" if "valid_path g" for g
  proof -
    obtain S where "finite S" and g_diff: "g C1_differentiable_on {0..1} - S"
      using \<open>valid_path g\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto
  
    have g_diff':"g differentiable at t" when "t\<in>{0..1} - S" for t
      by (meson C1_differentiable_on_eq \<open>g C1_differentiable_on {0..1} - S\<close> that)
    then have "(cnj \<circ> g) differentiable at t" when "t\<in>{0..1} - S" for t
      using bounded_linear_cnj bounded_linear_imp_differentiable differentiable_chain_at that by blast
    moreover have "continuous_on ({0..1} - S)
        (\<lambda>x. vector_derivative (cnj \<circ> g) (at x))"
    proof -
      have "continuous_on ({0..1} - S)
          (\<lambda>x. vector_derivative (cnj \<circ> g) (at x))
        = continuous_on ({0..1} - S)
          (\<lambda>x. cnj (vector_derivative g (at x)))"
        apply (rule continuous_on_cong[OF refl])
        unfolding comp_def using g_diff'
        using has_vector_derivative_cnj vector_derivative_at vector_derivative_works by blast
      also have "\<dots>"
        apply (intro continuous_intros)
        using C1_differentiable_on_eq g_diff by blast
      finally show ?thesis .
    qed
    ultimately have "cnj \<circ> g C1_differentiable_on {0..1} - S"
      using C1_differentiable_on_eq by blast
    moreover have "path (cnj \<circ> g)"
      apply (rule path_continuous_image[OF valid_path_imp_path[OF \<open>valid_path g\<close>]])
      by (intro continuous_intros)
    ultimately show ?thesis unfolding valid_path_def piecewise_C1_differentiable_on_def path_def
      using \<open>finite S\<close> by auto
  qed
  from this[of "cnj o g"]
  show "valid_path (cnj \<circ> g) \<Longrightarrow> valid_path g"
    unfolding comp_def by simp
qed

end
