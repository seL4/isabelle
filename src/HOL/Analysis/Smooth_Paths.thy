(*
  Material originally from HOL Light, ported by Larry Paulson, moved here by Manuel Eberl
*)
section\<^marker>\<open>tag unimportant\<close> \<open>Smooth paths\<close>
theory Smooth_Paths
  imports
  Retracts
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Homeomorphisms of arc images\<close>

lemma path_connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "path_connected(- path_image \<gamma>)"
proof -
  have "path_image \<gamma> homeomorphic {0..1::real}"
    by (simp add: assms homeomorphic_arc_image_interval)
  then
  show ?thesis
    apply (rule path_connected_complement_homeomorphic_convex_compact)
      apply (auto simp: assms)
    done
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
  show ?thesis
  proof (rule inside_bounded_complement_connected_empty)
    show "connected (- path_image \<gamma>)"
      apply (rule connected_arc_complement [OF assms])
      using False
      by (metis DIM_ge_Suc0 One_nat_def Suc_1 not_less_eq_eq order_class.order.antisym)
    show "bounded (path_image \<gamma>)"
      by (simp add: assms bounded_arc_image)
  qed
qed

lemma inside_simple_curve_imp_closed:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
    shows "\<lbrakk>simple_path \<gamma>; x \<in> inside(path_image \<gamma>)\<rbrakk> \<Longrightarrow> pathfinish \<gamma> = pathstart \<gamma>"
  using arc_simple_path  inside_arc_empty by blast


subsection \<open>Piecewise differentiability of paths\<close>

lemma continuous_on_joinpaths_D1:
    "continuous_on {0..1} (g1 +++ g2) \<Longrightarrow> continuous_on {0..1} g1"
  apply (rule continuous_on_eq [of _ "(g1 +++ g2) \<circ> ((*)(inverse 2))"])
  apply (rule continuous_intros | simp)+
  apply (auto elim!: continuous_on_subset simp: joinpaths_def)
  done

lemma continuous_on_joinpaths_D2:
    "\<lbrakk>continuous_on {0..1} (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> continuous_on {0..1} g2"
  apply (rule continuous_on_eq [of _ "(g1 +++ g2) \<circ> (\<lambda>x. inverse 2*x + 1/2)"])
  apply (rule continuous_intros | simp)+
  apply (auto elim!: continuous_on_subset simp add: joinpaths_def pathfinish_def pathstart_def Ball_def)
  done

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
      apply (simp only: joinpaths_def)
      by (rule differentiable_chain_at derivative_intros | force)+
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
    apply (rule continuous_intros)+
    using coDhalf
    apply (simp add: scaleR_conv_of_real image_set_diff image_image)
    done
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
      apply (simp only: joinpaths_def)
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
    apply (clarsimp simp add: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    apply (rule_tac x="insert 0 ((\<lambda>x. 2 * x - 1) ` S)" in exI)
    apply (simp add: g2D con_g2)
  done
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
        proof (rule vector_derivative_chain_at_general[symmetric])
          show "g differentiable at t" by (meson C1_differentiable_on_eq g_diff that)
        next
          have "g t\<in>path_image g" using that DiffD1 image_eqI path_image_def by metis
          then show "f field_differentiable at (g t)" using der by auto
        qed
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
    apply (simp only: valid_path_def continuous_on_joinpaths joinpaths_def)
    apply (rule piecewise_C1_differentiable_cases)
    apply (auto simp: o_def)
    done
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
  apply (auto simp: valid_path_def shiftpath_alt_def)
  apply (rule piecewise_C1_differentiable_cases)
  apply (auto simp: algebra_simps)
  apply (rule piecewise_C1_differentiable_affine [of g 1 a, simplified o_def scaleR_one])
  apply (auto simp: pathfinish_def pathstart_def elim: piecewise_C1_differentiable_on_subset)
  apply (rule piecewise_C1_differentiable_affine [of g 1 "a-1", simplified o_def scaleR_one algebra_simps])
  apply (auto simp: pathfinish_def pathstart_def elim: piecewise_C1_differentiable_on_subset)
  done

lemma vector_derivative_linepath_within:
    "x \<in> {0..1} \<Longrightarrow> vector_derivative (linepath a b) (at x within {0..1}) = b - a"
  apply (rule vector_derivative_within_cbox [of 0 "1::real", simplified])
  apply (auto simp: has_vector_derivative_linepath_within)
  done

lemma vector_derivative_linepath_at [simp]: "vector_derivative (linepath a b) (at x) = b - a"
  by (simp add: has_vector_derivative_linepath_within vector_derivative_at)

lemma valid_path_linepath [iff]: "valid_path (linepath a b)"
  apply (simp add: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq continuous_on_linepath)
  apply (rule_tac x="{}" in exI)
  apply (simp add: differentiable_on_def differentiable_def)
  using has_vector_derivative_def has_vector_derivative_linepath_within
  apply (fastforce simp add: continuous_on_eq_continuous_within)
  done

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
  have "(g \<circ> (\<lambda>x. ((v-u) * x + u))) piecewise_C1_differentiable_on {0..1}"
    apply (rule piecewise_C1_differentiable_compose)
    apply (simp add: C1_differentiable_imp_piecewise)
     apply (simp add: image_affinity_atLeastAtMost)
    using assms False
    apply (auto simp: algebra_simps valid_path_def piecewise_C1_differentiable_on_subset)
    apply (subst Int_commute)
    apply (auto simp: inj_on_def algebra_simps crossproduct_eq finite_vimage_IntI)
    done
  then show ?thesis
    by (auto simp: o_def valid_path_def subpath_def)
qed

lemma valid_path_rectpath [simp, intro]: "valid_path (rectpath a b)"
  by (simp add: Let_def rectpath_def)

end
