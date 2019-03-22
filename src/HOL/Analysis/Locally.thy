section \<open>Neigbourhood bases and Locally path-connected spaces\<close>

theory Locally
  imports
    Path_Connected Function_Topology
begin

subsection\<open>Neigbourhood bases (useful for "local" properties of various kinds)\<close>

definition neighbourhood_base_at where
 "neighbourhood_base_at x P X \<equiv>
        \<forall>W. openin X W \<and> x \<in> W
            \<longrightarrow> (\<exists>U V. openin X U \<and> P V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W)"

definition neighbourhood_base_of where
 "neighbourhood_base_of P X \<equiv>
        \<forall>x \<in> topspace X. neighbourhood_base_at x P X"

lemma neighbourhood_base_of:
   "neighbourhood_base_of P X \<longleftrightarrow>
        (\<forall>W x. openin X W \<and> x \<in> W
          \<longrightarrow> (\<exists>U V. openin X U \<and> P V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W))"
  unfolding neighbourhood_base_at_def neighbourhood_base_of_def
  using openin_subset by blast

lemma neighbourhood_base_at_mono:
   "\<lbrakk>neighbourhood_base_at x P X; \<And>S. \<lbrakk>P S; x \<in> S\<rbrakk> \<Longrightarrow> Q S\<rbrakk> \<Longrightarrow> neighbourhood_base_at x Q X"
  unfolding neighbourhood_base_at_def
  by (meson subset_eq)

lemma neighbourhood_base_of_mono:
   "\<lbrakk>neighbourhood_base_of P X; \<And>S. P S \<Longrightarrow> Q S\<rbrakk> \<Longrightarrow> neighbourhood_base_of Q X"
  unfolding neighbourhood_base_of_def
  using neighbourhood_base_at_mono by force

lemma open_neighbourhood_base_at:
   "(\<And>S. \<lbrakk>P S; x \<in> S\<rbrakk> \<Longrightarrow> openin X S)
        \<Longrightarrow> neighbourhood_base_at x P X \<longleftrightarrow> (\<forall>W. openin X W \<and> x \<in> W \<longrightarrow> (\<exists>U. P U \<and> x \<in> U \<and> U \<subseteq> W))"
  unfolding neighbourhood_base_at_def
  by (meson subsetD)

lemma open_neighbourhood_base_of:
  "(\<forall>S. P S \<longrightarrow> openin X S)
        \<Longrightarrow> neighbourhood_base_of P X \<longleftrightarrow> (\<forall>W x. openin X W \<and> x \<in> W \<longrightarrow> (\<exists>U. P U \<and> x \<in> U \<and> U \<subseteq> W))"
  apply (simp add: neighbourhood_base_of, safe, blast)
  by meson

lemma neighbourhood_base_of_open_subset:
   "\<lbrakk>neighbourhood_base_of P X; openin X S\<rbrakk>
        \<Longrightarrow> neighbourhood_base_of P (subtopology X S)"
  apply (clarsimp simp add: neighbourhood_base_of openin_subtopology_alt image_def)
  apply (rename_tac x V)
  apply (drule_tac x="S \<inter> V" in spec)
  apply (simp add: Int_ac)
  by (metis IntI le_infI1 openin_Int)

lemma neighbourhood_base_of_topology_base:
   "openin X = arbitrary union_of (\<lambda>W. W \<in> \<B>)
        \<Longrightarrow> neighbourhood_base_of P X \<longleftrightarrow>
             (\<forall>W x. W \<in> \<B> \<and> x \<in> W  \<longrightarrow> (\<exists>U V. openin X U \<and> P V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W))"
  apply (auto simp: openin_topology_base_unique neighbourhood_base_of)
  by (meson subset_trans)

lemma neighbourhood_base_at_unlocalized:
  assumes "\<And>S T. \<lbrakk>P S; openin X T; x \<in> T; T \<subseteq> S\<rbrakk> \<Longrightarrow> P T"
  shows "neighbourhood_base_at x P X
     \<longleftrightarrow> (x \<in> topspace X \<longrightarrow> (\<exists>U V. openin X U \<and> P V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> topspace X))"
         (is "?lhs = ?rhs")
proof
  assume R: ?rhs show ?lhs
    unfolding neighbourhood_base_at_def
  proof clarify
    fix W
    assume "openin X W" "x \<in> W"
    then have "x \<in> topspace X"
      using openin_subset by blast
    with R obtain U V where "openin X U" "P V" "x \<in> U" "U \<subseteq> V" "V \<subseteq> topspace X"
      by blast
    then show "\<exists>U V. openin X U \<and> P V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
      by (metis IntI \<open>openin X W\<close> \<open>x \<in> W\<close> assms inf_le1 inf_le2 openin_Int)
  qed
qed (simp add: neighbourhood_base_at_def)

lemma neighbourhood_base_at_with_subset:
   "\<lbrakk>openin X U; x \<in> U\<rbrakk>
        \<Longrightarrow> (neighbourhood_base_at x P X \<longleftrightarrow> neighbourhood_base_at x (\<lambda>T. T \<subseteq> U \<and> P T) X)"
  apply (simp add: neighbourhood_base_at_def)
  apply (metis IntI Int_subset_iff openin_Int)
  done

lemma neighbourhood_base_of_with_subset:
   "neighbourhood_base_of P X \<longleftrightarrow> neighbourhood_base_of (\<lambda>t. t \<subseteq> topspace X \<and> P t) X"
  using neighbourhood_base_at_with_subset
  by (fastforce simp add: neighbourhood_base_of_def)

subsection\<open>Locally path-connected spaces\<close>

definition weakly_locally_path_connected_at
  where "weakly_locally_path_connected_at x X \<equiv> neighbourhood_base_at x (path_connectedin X) X"

definition locally_path_connected_at
  where "locally_path_connected_at x X \<equiv>
    neighbourhood_base_at x (\<lambda>U. openin X U \<and> path_connectedin X U) X"

definition locally_path_connected_space
  where "locally_path_connected_space X \<equiv> neighbourhood_base_of (path_connectedin X) X"

lemma locally_path_connected_space_alt:
  "locally_path_connected_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>U. openin X U \<and> path_connectedin X U) X"
  (is "?P = ?Q")
  and locally_path_connected_space_eq_open_path_component_of:
  "locally_path_connected_space X \<longleftrightarrow>
        (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> openin X (Collect (path_component_of (subtopology X U) x)))"
  (is "?P = ?R")
proof -
  have ?P if ?Q
    using locally_path_connected_space_def neighbourhood_base_of_mono that by auto
  moreover have ?R if P: ?P
  proof -
    show ?thesis
    proof clarify
      fix U y
      assume "openin X U" "y \<in> U"
      have "\<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> Collect (path_component_of (subtopology X U) y)"
        if "path_component_of (subtopology X U) y x" for x

      proof -
        have "x \<in> U"
          using path_component_of_equiv that topspace_subtopology by fastforce
        then have "\<exists>Ua. openin X Ua \<and> (\<exists>V. path_connectedin X V \<and> x \<in> Ua \<and> Ua \<subseteq> V \<and> V \<subseteq> U)"
      using P
      by (simp add: \<open>openin X U\<close> locally_path_connected_space_def neighbourhood_base_of)
        then show ?thesis
          by (metis dual_order.trans path_component_of_equiv path_component_of_maximal path_connectedin_subtopology subset_iff that)
      qed
      then show "openin X (Collect (path_component_of (subtopology X U) y))"
        using openin_subopen by force
    qed
  qed
  moreover have ?Q if ?R
    using that
    apply (simp add: open_neighbourhood_base_of)
    by (metis mem_Collect_eq openin_subset path_component_of_refl path_connectedin_path_component_of path_connectedin_subtopology that topspace_subtopology_subset)
  ultimately show "?P = ?Q" "?P = ?R"
    by blast+
qed

lemma locally_path_connected_space:
   "locally_path_connected_space X
   \<longleftrightarrow> (\<forall>V x. openin X V \<and> x \<in> V \<longrightarrow> (\<exists>U. openin X U \<and> path_connectedin X U \<and> x \<in> U \<and> U \<subseteq> V))"
  by (simp add: locally_path_connected_space_alt open_neighbourhood_base_of)

lemma locally_path_connected_space_open_path_components:
   "locally_path_connected_space X \<longleftrightarrow>
        (\<forall>U c. openin X U \<and> c \<in> path_components_of(subtopology X U) \<longrightarrow> openin X c)"
  apply (auto simp: locally_path_connected_space_eq_open_path_component_of path_components_of_def topspace_subtopology)
  by (metis imageI inf.absorb_iff2 openin_closedin_eq)

lemma openin_path_component_of_locally_path_connected_space:
   "locally_path_connected_space X \<Longrightarrow> openin X (Collect (path_component_of X x))"
  apply (auto simp: locally_path_connected_space_eq_open_path_component_of)
  by (metis openin_empty openin_topspace path_component_of_eq_empty subtopology_topspace)

lemma openin_path_components_of_locally_path_connected_space:
   "\<lbrakk>locally_path_connected_space X; c \<in> path_components_of X\<rbrakk> \<Longrightarrow> openin X c"
  apply (auto simp: locally_path_connected_space_eq_open_path_component_of)
  by (metis (no_types, lifting) imageE openin_topspace path_components_of_def subtopology_topspace)

lemma closedin_path_components_of_locally_path_connected_space:
   "\<lbrakk>locally_path_connected_space X; c \<in> path_components_of X\<rbrakk> \<Longrightarrow> closedin X c"
  by (simp add: closedin_def complement_path_components_of_Union openin_path_components_of_locally_path_connected_space openin_clauses(3) path_components_of_subset)

lemma closedin_path_component_of_locally_path_connected_space:
  assumes "locally_path_connected_space X"
  shows "closedin X (Collect (path_component_of X x))"
proof (cases "x \<in> topspace X")
  case True
  then show ?thesis
    by (simp add: assms closedin_path_components_of_locally_path_connected_space path_component_in_path_components_of)
next
  case False
  then show ?thesis
    by (metis closedin_empty path_component_of_eq_empty)
qed

lemma weakly_locally_path_connected_at:
   "weakly_locally_path_connected_at x X \<longleftrightarrow>
    (\<forall>V. openin X V \<and> x \<in> V
          \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> U \<subseteq> V \<and>
                  (\<forall>y \<in> U. \<exists>C. path_connectedin X C \<and> C \<subseteq> V \<and> x \<in> C \<and> y \<in> C)))"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    apply (simp add: weakly_locally_path_connected_at_def neighbourhood_base_at_def)
    by (meson order_trans subsetD)
next
  have *: "\<exists>V. path_connectedin X V \<and> U \<subseteq> V \<and> V \<subseteq> W"
    if "(\<forall>y\<in>U. \<exists>C. path_connectedin X C \<and> C \<subseteq> W \<and> x \<in> C \<and> y \<in> C)"
    for W U
  proof (intro exI conjI)
    let ?V = "(Collect (path_component_of (subtopology X W) x))"
      show "path_connectedin X (Collect (path_component_of (subtopology X W) x))"
        by (meson path_connectedin_path_component_of path_connectedin_subtopology)
      show "U \<subseteq> ?V"
        by (auto simp: path_component_of path_connectedin_subtopology that)
      show "?V \<subseteq> W"
        by (meson path_connectedin_path_component_of path_connectedin_subtopology)
    qed
  assume ?rhs
  then show ?lhs
    unfolding weakly_locally_path_connected_at_def neighbourhood_base_at_def by (metis "*")
qed

lemma locally_path_connected_space_im_kleinen:
   "locally_path_connected_space X \<longleftrightarrow>
      (\<forall>V x. openin X V \<and> x \<in> V
             \<longrightarrow> (\<exists>U. openin X U \<and>
                    x \<in> U \<and> U \<subseteq> V \<and>
                    (\<forall>y \<in> U. \<exists>c. path_connectedin X c \<and>
                                c \<subseteq> V \<and> x \<in> c \<and> y \<in> c)))"
  apply (simp add: locally_path_connected_space_def neighbourhood_base_of_def)
  apply (simp add: weakly_locally_path_connected_at flip: weakly_locally_path_connected_at_def)
  using openin_subset apply force
  done

lemma locally_path_connected_space_open_subset:
   "\<lbrakk>locally_path_connected_space X; openin X s\<rbrakk>
        \<Longrightarrow> locally_path_connected_space (subtopology X s)"
  apply (simp add: locally_path_connected_space_def neighbourhood_base_of openin_open_subtopology path_connectedin_subtopology)
  by (meson order_trans)

lemma locally_path_connected_space_quotient_map_image:
  assumes f: "quotient_map X Y f" and X: "locally_path_connected_space X"
  shows "locally_path_connected_space Y"
  unfolding locally_path_connected_space_open_path_components
proof clarify
  fix V C
  assume V: "openin Y V" and c: "C \<in> path_components_of (subtopology Y V)"
  then have sub: "C \<subseteq> topspace Y"
    using path_connectedin_path_components_of path_connectedin_subset_topspace path_connectedin_subtopology by blast
  have "openin X {x \<in> topspace X. f x \<in> C}"
  proof (subst openin_subopen, clarify)
    fix x
    assume x: "x \<in> topspace X" and "f x \<in> C"
    let ?T = "Collect (path_component_of (subtopology X {z \<in> topspace X. f z \<in> V}) x)"
    show "\<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> {x \<in> topspace X. f x \<in> C}"
    proof (intro exI conjI)
      have "\<exists>U. openin X U \<and> ?T \<in> path_components_of (subtopology X U)"
      proof (intro exI conjI)
        show "openin X ({z \<in> topspace X. f z \<in> V})"
          using V f openin_subset quotient_map_def by fastforce
        show "Collect (path_component_of (subtopology X {z \<in> topspace X. f z \<in> V}) x)
        \<in> path_components_of (subtopology X {z \<in> topspace X. f z \<in> V})"
          by (metis (no_types, lifting) Int_iff \<open>f x \<in> C\<close> c mem_Collect_eq path_component_in_path_components_of path_components_of_subset topspace_subtopology topspace_subtopology_subset x)
      qed
      with X show "openin X ?T"
        using locally_path_connected_space_open_path_components by blast
      show x: "x \<in> ?T"
        using V \<open>f x \<in> C\<close> c openin_subset path_component_of_equiv path_components_of_subset topspace_subtopology topspace_subtopology_subset x
        by fastforce
      have "f ` ?T \<subseteq> C"
      proof (rule path_components_of_maximal)
        show "C \<in> path_components_of (subtopology Y V)"
          by (simp add: c)
        show "path_connectedin (subtopology Y V) (f ` ?T)"
        proof -
          have "quotient_map (subtopology X {a \<in> topspace X. f a \<in> V}) (subtopology Y V) f"
            by (simp add: V f quotient_map_restriction)
          then show ?thesis
            by (meson path_connectedin_continuous_map_image path_connectedin_path_component_of quotient_imp_continuous_map)
        qed
        show "\<not> disjnt C (f ` ?T)"
          by (metis (no_types, lifting) \<open>f x \<in> C\<close> x disjnt_iff image_eqI)
      qed
      then show "?T \<subseteq> {x \<in> topspace X. f x \<in> C}"
        by (force simp: path_component_of_equiv topspace_subtopology)
    qed
  qed
  then show "openin Y C"
    using f sub by (simp add: quotient_map_def)
qed

lemma homeomorphic_locally_path_connected_space:
  assumes "X homeomorphic_space Y"
  shows "locally_path_connected_space X \<longleftrightarrow> locally_path_connected_space Y"
proof -
  obtain f g where "homeomorphic_maps X Y f g"
    using assms homeomorphic_space_def by fastforce
  then show ?thesis
    by (metis (no_types) homeomorphic_map_def homeomorphic_maps_map locally_path_connected_space_quotient_map_image)
qed

lemma locally_path_connected_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; locally_path_connected_space X\<rbrakk>
        \<Longrightarrow> locally_path_connected_space Y"
  using Abstract_Topology.retraction_imp_quotient_map locally_path_connected_space_quotient_map_image by blast

lemma locally_path_connected_space_euclideanreal: "locally_path_connected_space euclideanreal"
  unfolding locally_path_connected_space_def neighbourhood_base_of
  proof clarsimp
  fix W and x :: "real"
  assume "open W" "x \<in> W"
  then obtain e where "e > 0" and e: "\<And>x'. \<bar>x' - x\<bar> < e \<longrightarrow> x' \<in> W"
    by (auto simp: open_real)
  then show "\<exists>U. open U \<and> (\<exists>V. path_connected V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W)"
    by (force intro!: convex_imp_path_connected exI [where x = "{x-e<..<x+e}"])
qed

lemma locally_path_connected_space_discrete_topology:
   "locally_path_connected_space (discrete_topology U)"
  using locally_path_connected_space_open_path_components by fastforce

lemma path_component_eq_connected_component_of:
  assumes "locally_path_connected_space X"
  shows "(path_component_of_set X x = connected_component_of_set X x)"
proof (cases "x \<in> topspace X")
  case True
  then show ?thesis
    using connectedin_connected_component_of [of X x]
    apply (clarsimp simp add: connectedin_def connected_space_clopen_in topspace_subtopology_subset cong: conj_cong)
    apply (drule_tac x="path_component_of_set X x" in spec)
    by (metis assms closedin_closed_subtopology closedin_connected_component_of closedin_path_component_of_locally_path_connected_space inf.absorb_iff2 inf.orderE openin_path_component_of_locally_path_connected_space openin_subtopology path_component_of_eq_empty path_component_subset_connected_component_of)
next
  case False
  then show ?thesis
    using connected_component_of_eq_empty path_component_of_eq_empty by fastforce
qed

lemma path_components_eq_connected_components_of:
   "locally_path_connected_space X \<Longrightarrow> (path_components_of X = connected_components_of X)"
  by (simp add: path_components_of_def connected_components_of_def image_def path_component_eq_connected_component_of)

lemma path_connected_eq_connected_space:
   "locally_path_connected_space X
         \<Longrightarrow> path_connected_space X \<longleftrightarrow> connected_space X"
  by (metis connected_components_of_subset_sing path_components_eq_connected_components_of path_components_of_subset_singleton)

lemma locally_path_connected_space_product_topology:
   "locally_path_connected_space(product_topology X I) \<longleftrightarrow>
        topspace(product_topology X I) = {} \<or>
        finite {i. i \<in> I \<and> ~path_connected_space(X i)} \<and>
        (\<forall>i \<in> I. locally_path_connected_space(X i))"
    (is "?lhs \<longleftrightarrow> ?empty \<or> ?rhs")
proof (cases ?empty)
  case True
  then show ?thesis
    by (simp add: locally_path_connected_space_def neighbourhood_base_of openin_closedin_eq)
next
  case False
  then obtain z where z: "z \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
    by auto
  have ?rhs if L: ?lhs
  proof -
    obtain U C where U: "openin (product_topology X I) U"
      and V: "path_connectedin (product_topology X I) C"
      and "z \<in> U" "U \<subseteq> C" and Csub: "C \<subseteq> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
      using L apply (clarsimp simp add: locally_path_connected_space_def neighbourhood_base_of)
      by (metis openin_topspace topspace_product_topology z)
    then obtain V where finV: "finite {i \<in> I. V i \<noteq> topspace (X i)}"
      and XV: "\<And>i. i\<in>I \<Longrightarrow> openin (X i) (V i)" and "z \<in> Pi\<^sub>E I V" and subU: "Pi\<^sub>E I V \<subseteq> U"
      by (force simp: openin_product_topology_alt)
    show ?thesis
    proof (intro conjI ballI)
      have "path_connected_space (X i)" if "i \<in> I" "V i = topspace (X i)" for i
      proof -
        have pc: "path_connectedin (X i) ((\<lambda>x. x i) ` C)"
          apply (rule path_connectedin_continuous_map_image [OF _ V])
          by (simp add: continuous_map_product_projection \<open>i \<in> I\<close>)
        moreover have "((\<lambda>x. x i) ` C) = topspace (X i)"
        proof
          show "(\<lambda>x. x i) ` C \<subseteq> topspace (X i)"
            by (simp add: pc path_connectedin_subset_topspace)
          have "V i \<subseteq> (\<lambda>x. x i) ` (\<Pi>\<^sub>E i\<in>I. V i)"
            by (metis \<open>z \<in> Pi\<^sub>E I V\<close> empty_iff image_projection_PiE order_refl that(1))
          also have "\<dots> \<subseteq> (\<lambda>x. x i) ` U"
            using subU by blast
          finally show "topspace (X i) \<subseteq> (\<lambda>x. x i) ` C"
            using \<open>U \<subseteq> C\<close> that by blast
        qed
        ultimately show ?thesis
          by (simp add: path_connectedin_topspace)
      qed
      then have "{i \<in> I. \<not> path_connected_space (X i)} \<subseteq> {i \<in> I. V i \<noteq> topspace (X i)}"
        by blast
      with finV show "finite {i \<in> I. \<not> path_connected_space (X i)}"
        using finite_subset by blast
    next
      show "locally_path_connected_space (X i)" if "i \<in> I" for i
        apply (rule locally_path_connected_space_quotient_map_image [OF _ L, where f = "\<lambda>x. x i"])
        by (metis False Abstract_Topology.retraction_imp_quotient_map retraction_map_product_projection that)
    qed
  qed
  moreover have ?lhs if R: ?rhs
  proof (clarsimp simp add: locally_path_connected_space_def neighbourhood_base_of)
    fix F z
    assume "openin (product_topology X I) F" and "z \<in> F"
    then obtain W where finW: "finite {i \<in> I. W i \<noteq> topspace (X i)}"
            and opeW: "\<And>i. i \<in> I \<Longrightarrow> openin (X i) (W i)" and "z \<in> Pi\<^sub>E I W" "Pi\<^sub>E I W \<subseteq> F"
      by (auto simp: openin_product_topology_alt)
    have "\<forall>i \<in> I. \<exists>U C. openin (X i) U \<and> path_connectedin (X i) C \<and> z i \<in> U \<and> U \<subseteq> C \<and> C \<subseteq> W i \<and>
                        (W i = topspace (X i) \<and>
                         path_connected_space (X i) \<longrightarrow> U = topspace (X i) \<and> C = topspace (X i))"
          (is "\<forall>i \<in> I. ?\<Phi> i")
    proof
      fix i assume "i \<in> I"
      have "locally_path_connected_space (X i)"
        by (simp add: R \<open>i \<in> I\<close>)
      moreover have "openin (X i) (W i) " "z i \<in> W i"
        using \<open>z \<in> Pi\<^sub>E I W\<close> opeW \<open>i \<in> I\<close> by auto
      ultimately obtain U C where UC: "openin (X i) U" "path_connectedin (X i) C" "z i \<in> U" "U \<subseteq> C" "C \<subseteq> W i"
        using \<open>i \<in> I\<close> by (force simp: locally_path_connected_space_def neighbourhood_base_of)
      show "?\<Phi> i"
      proof (cases "W i = topspace (X i) \<and> path_connected_space(X i)")
        case True
        then show ?thesis
          using \<open>z i \<in> W i\<close> path_connectedin_topspace by blast
      next
        case False
        then show ?thesis
          by (meson UC)
      qed
    qed
    then obtain U C where
      *: "\<And>i. i \<in> I \<Longrightarrow> openin (X i) (U i) \<and> path_connectedin (X i) (C i) \<and> z i \<in> (U i) \<and> (U i) \<subseteq> (C i) \<and> (C i) \<subseteq> W i \<and>
                        (W i = topspace (X i) \<and> path_connected_space (X i)
                         \<longrightarrow> (U i) = topspace (X i) \<and> (C i) = topspace (X i))"
      by metis
    let ?A = "{i \<in> I. \<not> path_connected_space (X i)} \<union> {i \<in> I. W i \<noteq> topspace (X i)}"
    have "{i \<in> I. U i \<noteq> topspace (X i)} \<subseteq> ?A"
      by (clarsimp simp add: "*")
    moreover have "finite ?A"
      by (simp add: that finW)
    ultimately have "finite {i \<in> I. U i \<noteq> topspace (X i)}"
      using finite_subset by auto
    then have "openin (product_topology X I) (Pi\<^sub>E I U)"
      using * by (simp add: openin_PiE_gen)
    then show "\<exists>U. openin (product_topology X I) U \<and>
            (\<exists>V. path_connectedin (product_topology X I) V \<and> z \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> F)"
      apply (rule_tac x="PiE I U" in exI, simp)
      apply (rule_tac x="PiE I C" in exI)
      using \<open>z \<in> Pi\<^sub>E I W\<close> \<open>Pi\<^sub>E I W \<subseteq> F\<close> *
      apply (simp add: path_connectedin_PiE subset_PiE PiE_iff PiE_mono dual_order.trans)
      done
  qed
  ultimately show ?thesis
    using False by blast
qed

end
