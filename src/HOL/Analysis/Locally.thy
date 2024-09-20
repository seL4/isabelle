section \<open>Neighbourhood bases and Locally path-connected spaces\<close>

theory Locally
  imports
    Path_Connected Function_Topology Sum_Topology
begin

subsection\<open>Neighbourhood Bases\<close>

text \<open>Useful for "local" properties of various kinds\<close>

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
  by (smt (verit) neighbourhood_base_of subsetD)

lemma neighbourhood_base_of_open_subset:
   "\<lbrakk>neighbourhood_base_of P X; openin X S\<rbrakk>
        \<Longrightarrow> neighbourhood_base_of P (subtopology X S)"
  by (smt (verit, ccfv_SIG) neighbourhood_base_of openin_open_subtopology subset_trans)

lemma neighbourhood_base_of_topology_base:
   "openin X = arbitrary union_of (\<lambda>W. W \<in> \<B>)
        \<Longrightarrow> neighbourhood_base_of P X \<longleftrightarrow>
             (\<forall>W x. W \<in> \<B> \<and> x \<in> W  \<longrightarrow> (\<exists>U V. openin X U \<and> P V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W))"
  by (smt (verit, del_insts) neighbourhood_base_of openin_topology_base_unique subset_trans)

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
  unfolding neighbourhood_base_at_def by (metis IntI Int_subset_iff openin_Int)

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
    by (smt (verit) mem_Collect_eq open_neighbourhood_base_of openin_subset path_component_of_refl 
        path_connectedin_path_component_of path_connectedin_subtopology that topspace_subtopology_subset)
  ultimately show "?P = ?Q" "?P = ?R"
    by blast+
qed

lemma locally_path_connected_space:
   "locally_path_connected_space X
   \<longleftrightarrow> (\<forall>V x. openin X V \<and> x \<in> V \<longrightarrow> (\<exists>U. openin X U \<and> path_connectedin X U \<and> x \<in> U \<and> U \<subseteq> V))"
  by (simp add: locally_path_connected_space_alt open_neighbourhood_base_of)

lemma locally_path_connected_space_open_path_components:
   "locally_path_connected_space X \<longleftrightarrow>
        (\<forall>U C. openin X U \<and> C \<in> path_components_of(subtopology X U) \<longrightarrow> openin X C)"
  apply (simp add: locally_path_connected_space_eq_open_path_component_of path_components_of_def)
  by (smt (verit, ccfv_threshold) Int_iff image_iff openin_subset subset_iff)

lemma openin_path_component_of_locally_path_connected_space:
   "locally_path_connected_space X \<Longrightarrow> openin X (Collect (path_component_of X x))"
  using locally_path_connected_space_eq_open_path_component_of openin_subopen path_component_of_eq_empty 
  by fastforce

lemma openin_path_components_of_locally_path_connected_space:
   "\<lbrakk>locally_path_connected_space X; C \<in> path_components_of X\<rbrakk> \<Longrightarrow> openin X C"
  using locally_path_connected_space_open_path_components by force

lemma closedin_path_components_of_locally_path_connected_space:
   "\<lbrakk>locally_path_connected_space X; C \<in> path_components_of X\<rbrakk> \<Longrightarrow> closedin X C"
  unfolding closedin_def
  by (metis Diff_iff complement_path_components_of_Union openin_clauses(3) openin_closedin_eq 
      openin_path_components_of_locally_path_connected_space)

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
    by (smt (verit) neighbourhood_base_at_def subset_iff weakly_locally_path_connected_at_def)
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
                    (\<forall>y \<in> U. \<exists>C. path_connectedin X C \<and>
                                C \<subseteq> V \<and> x \<in> C \<and> y \<in> C)))"
         (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis locally_path_connected_space)
  assume ?rhs
  then show ?lhs
    unfolding locally_path_connected_space_def neighbourhood_base_of
    by (metis neighbourhood_base_at_def weakly_locally_path_connected_at weakly_locally_path_connected_at_def)
qed

lemma locally_path_connected_space_open_subset:
   "\<lbrakk>locally_path_connected_space X; openin X S\<rbrakk>
        \<Longrightarrow> locally_path_connected_space (subtopology X S)"
  by (smt (verit, best) locally_path_connected_space openin_open_subtopology path_connectedin_subtopology subset_trans)

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
      have *: "\<exists>U. openin X U \<and> ?T \<in> path_components_of (subtopology X U)"
      proof (intro exI conjI)
        show "openin X ({z \<in> topspace X. f z \<in> V})"
          using V f openin_subset quotient_map_def by fastforce
        have "x \<in> topspace (subtopology X {z \<in> topspace X. f z \<in> V})"
          using \<open>f x \<in> C\<close> c path_components_of_subset x by force
        then show "Collect (path_component_of (subtopology X {z \<in> topspace X. f z \<in> V}) x)
            \<in> path_components_of (subtopology X {z \<in> topspace X. f z \<in> V})"
          by (meson path_component_in_path_components_of)
      qed
      with X show "openin X ?T"
        using locally_path_connected_space_open_path_components by blast
      show x: "x \<in> ?T"
        using * nonempty_path_components_of path_component_of_eq path_component_of_eq_empty by fastforce
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
        by (force simp: path_component_of_equiv)
    qed
  qed
  then show "openin Y C"
    using f sub by (simp add: quotient_map_def)
qed

lemma homeomorphic_locally_path_connected_space:
  assumes "X homeomorphic_space Y"
  shows "locally_path_connected_space X \<longleftrightarrow> locally_path_connected_space Y"
  using assms
    unfolding homeomorphic_space_def homeomorphic_map_def homeomorphic_maps_map
    by (metis locally_path_connected_space_quotient_map_image)

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
  shows "path_component_of_set X x = connected_component_of_set X x"
proof (cases "x \<in> topspace X")
  case True
  have "path_component_of_set X x \<subseteq> connected_component_of_set X x"
    by (simp add: path_component_subset_connected_component_of)
  moreover have "closedin X (path_component_of_set X x)"
    by (simp add: assms closedin_path_component_of_locally_path_connected_space)
  moreover have "openin X (path_component_of_set X x)"
    by (simp add: assms openin_path_component_of_locally_path_connected_space)
  moreover have "path_component_of_set X x \<noteq> {}"
    by (meson True path_component_of_eq_empty)
  ultimately show ?thesis
    using connectedin_connected_component_of [of X x] unfolding connectedin_def
    by (metis closedin_subset_topspace connected_space_clopen_in  
        subset_openin_subtopology topspace_subtopology_subset)
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
        (product_topology X I) = trivial_topology \<or>
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
    using discrete_topology_unique_derived_set by (fastforce iff: null_topspace_iff_trivial)
  have ?rhs if L: ?lhs
  proof -
    obtain U C where U: "openin (product_topology X I) U"
      and V: "path_connectedin (product_topology X I) C"
      and "z \<in> U" "U \<subseteq> C" and Csub: "C \<subseteq> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
      by (metis L locally_path_connected_space openin_topspace topspace_product_topology z)
    then obtain V where finV: "finite {i \<in> I. V i \<noteq> topspace (X i)}"
      and XV: "\<And>i. i\<in>I \<Longrightarrow> openin (X i) (V i)" and "z \<in> Pi\<^sub>E I V" and subU: "Pi\<^sub>E I V \<subseteq> U"
      by (force simp: openin_product_topology_alt)
    show ?thesis
    proof (intro conjI ballI)
      have "path_connected_space (X i)" if "i \<in> I" "V i = topspace (X i)" for i
      proof -
        have pc: "path_connectedin (X i) ((\<lambda>x. x i) ` C)"
          by (metis V continuous_map_product_projection path_connectedin_continuous_map_image that(1))
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
        by (meson False L locally_path_connected_space_quotient_map_image quotient_map_product_projection that)
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
      moreover have *:"openin (X i) (W i) " "z i \<in> W i"
        using \<open>z \<in> Pi\<^sub>E I W\<close> opeW \<open>i \<in> I\<close> by auto
      ultimately obtain U C where UC: "openin (X i) U" "path_connectedin (X i) C" "z i \<in> U" "U \<subseteq> C" "C \<subseteq> W i"
        using \<open>i \<in> I\<close> by (force simp: locally_path_connected_space_def neighbourhood_base_of)
      show "?\<Phi> i"
        by (metis UC * openin_subset path_connectedin_topspace)
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
    with * have "openin (product_topology X I) (Pi\<^sub>E I U)"
      by (simp add: openin_PiE_gen)
    then show "\<exists>U. openin (product_topology X I) U \<and>
              (\<exists>V. path_connectedin (product_topology X I) V \<and> z \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> F)"
      by (metis (no_types, opaque_lifting) subsetI \<open>z \<in> Pi\<^sub>E I W\<close> \<open>Pi\<^sub>E I W \<subseteq> F\<close> * path_connectedin_PiE 
          PiE_iff PiE_mono order.trans)
  qed
  ultimately show ?thesis
    using False by blast
qed

lemma locally_path_connected_is_realinterval:
  assumes "is_interval S"
  shows "locally_path_connected_space(subtopology euclideanreal S)"
  unfolding locally_path_connected_space_def
proof (clarsimp simp add: neighbourhood_base_of openin_subtopology_alt)
  fix a U
  assume "a \<in> S" and "a \<in> U" and "open U"
  then obtain r where "r > 0" and r: "ball a r \<subseteq> U"
    by (metis open_contains_ball_eq)
  show "\<exists>W. open W \<and> (\<exists>V. path_connectedin (top_of_set S) V \<and> a \<in> W \<and> S \<inter> W \<subseteq> V \<and> V \<subseteq> S \<and> V \<subseteq> U)"
  proof (intro exI conjI)
    show "path_connectedin (top_of_set S) (S \<inter> ball a r)"
      by (simp add: assms is_interval_Int is_interval_ball_real is_interval_path_connected path_connectedin_subtopology)
    show "a \<in> ball a r"
      by (simp add: \<open>0 < r\<close>)
  qed (use \<open>0 < r\<close> r in auto)
qed

lemma locally_path_connected_real_interval:
 "locally_path_connected_space (subtopology euclideanreal{a..b})"
  "locally_path_connected_space (subtopology euclideanreal{a<..<b})"
  using locally_path_connected_is_realinterval
  by (auto simp add: is_interval_1)

lemma locally_path_connected_space_prod_topology:
   "locally_path_connected_space (prod_topology X Y) \<longleftrightarrow>
      (prod_topology X Y) = trivial_topology \<or>
      locally_path_connected_space X \<and> locally_path_connected_space Y" (is "?lhs=?rhs")
proof (cases "(prod_topology X Y) = trivial_topology")
  case True
  then show ?thesis
    using locally_path_connected_space_discrete_topology by force
next
  case False
  then have ne: "X \<noteq> trivial_topology" "Y \<noteq> trivial_topology"
    by simp_all
  show ?thesis
  proof
    assume ?lhs then show ?rhs
      by (meson locally_path_connected_space_quotient_map_image ne(1) ne(2) quotient_map_fst quotient_map_snd)
  next
    assume ?rhs
    with False have X: "locally_path_connected_space X" and Y: "locally_path_connected_space Y"
      by auto
    show ?lhs
      unfolding locally_path_connected_space_def neighbourhood_base_of
    proof clarify
      fix UV x y
      assume UV: "openin (prod_topology X Y) UV" and "(x,y) \<in> UV"
      obtain A B where W12: "openin X A \<and> openin Y B \<and> x \<in> A \<and> y \<in> B \<and> A \<times> B \<subseteq> UV"
        using X Y by (metis UV \<open>(x,y) \<in> UV\<close> openin_prod_topology_alt)
      then obtain C D K L
        where "openin X C" "path_connectedin X K" "x \<in> C" "C \<subseteq> K" "K \<subseteq> A"
          "openin Y D" "path_connectedin Y L" "y \<in> D" "D \<subseteq> L" "L \<subseteq> B"
        by (metis X Y locally_path_connected_space)
      with W12 \<open>openin X C\<close> \<open>openin Y D\<close>
      show "\<exists>U V. openin (prod_topology X Y) U \<and> path_connectedin (prod_topology X Y) V \<and> (x, y) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> UV"
        apply (rule_tac x="C \<times> D" in exI)
        apply (rule_tac x="K \<times> L" in exI)
        apply (fastforce simp: openin_prod_Times_iff path_connectedin_Times)
        done
    qed
  qed
qed

lemma locally_path_connected_space_sum_topology:
   "locally_path_connected_space(sum_topology X I) \<longleftrightarrow>
    (\<forall>i \<in> I. locally_path_connected_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (smt (verit) homeomorphic_locally_path_connected_space locally_path_connected_space_open_subset topological_property_of_sum_component)
next
  assume R: ?rhs
  show ?lhs
  proof (clarsimp simp add: locally_path_connected_space_def neighbourhood_base_of forall_openin_sum_topology imp_conjL)
    fix W i x
    assume ope: "\<forall>i\<in>I. openin (X i) (W i)" 
      and "i \<in> I" and "x \<in> W i"
    then obtain U V where U: "openin (X i) U" and V: "path_connectedin (X i) V" 
           and "x \<in> U" "U \<subseteq> V" "V \<subseteq> W i"
      by (metis R \<open>i \<in> I\<close> \<open>x \<in> W i\<close> locally_path_connected_space)
    show "\<exists>U. openin (sum_topology X I) U \<and> (\<exists>V. path_connectedin (sum_topology X I) V \<and> (i, x) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> Sigma I W)"
    proof (intro exI conjI)
      show "openin (sum_topology X I) (Pair i ` U)"
        by (meson U \<open>i \<in> I\<close> open_map_component_injection open_map_def)
      show "path_connectedin (sum_topology X I) (Pair i ` V)"
        by (meson V \<open>i \<in> I\<close> continuous_map_component_injection path_connectedin_continuous_map_image)
      show "Pair i ` V \<subseteq> Sigma I W"
        using \<open>V \<subseteq> W i\<close> \<open>i \<in> I\<close> by force
    qed (use \<open>x \<in> U\<close> \<open>U \<subseteq> V\<close> in auto)
  qed
qed


subsection\<open>Locally connected spaces\<close>

definition weakly_locally_connected_at 
  where "weakly_locally_connected_at x X \<equiv> neighbourhood_base_at x (connectedin X) X"

definition locally_connected_at 
  where "locally_connected_at x X \<equiv>
           neighbourhood_base_at x (\<lambda>U. openin X U \<and> connectedin X U ) X"

definition locally_connected_space 
  where "locally_connected_space X \<equiv> neighbourhood_base_of (connectedin X) X"


lemma locally_connected_A: "(\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> openin X (connected_component_of_set (subtopology X U) x))
       \<Longrightarrow> neighbourhood_base_of (\<lambda>U. openin X U \<and> connectedin X U) X"
  unfolding neighbourhood_base_of
  by (metis (full_types) connected_component_of_refl connectedin_connected_component_of connectedin_subtopology mem_Collect_eq openin_subset topspace_subtopology_subset)

lemma locally_connected_B: "locally_connected_space X \<Longrightarrow> 
          (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> openin X (connected_component_of_set (subtopology X U) x))"
  unfolding locally_connected_space_def neighbourhood_base_of
  apply (erule all_forward)
  apply clarify
  apply (subst openin_subopen)
  by (smt (verit, ccfv_threshold) Ball_Collect connected_component_of_def connected_component_of_equiv connectedin_subtopology in_mono mem_Collect_eq)

lemma locally_connected_C: "neighbourhood_base_of (\<lambda>U. openin X U \<and> connectedin X U) X \<Longrightarrow> locally_connected_space X"
  using locally_connected_space_def neighbourhood_base_of_mono by auto


lemma locally_connected_space_alt: 
  "locally_connected_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>U. openin X U \<and> connectedin X U) X"
  using locally_connected_A locally_connected_B locally_connected_C by blast

lemma locally_connected_space_eq_open_connected_component_of:
  "locally_connected_space X \<longleftrightarrow>
        (\<forall>U x. openin X U \<and> x \<in> U
              \<longrightarrow> openin X (connected_component_of_set (subtopology X U) x))"
  by (meson locally_connected_A locally_connected_B locally_connected_C)

lemma locally_connected_space:
   "locally_connected_space X \<longleftrightarrow>
     (\<forall>V x. openin X V \<and> x \<in> V \<longrightarrow> (\<exists>U. openin X U \<and> connectedin X U \<and> x \<in> U \<and> U \<subseteq> V))"
  by (simp add: locally_connected_space_alt open_neighbourhood_base_of)

lemma locally_path_connected_imp_locally_connected_space:
   "locally_path_connected_space X \<Longrightarrow> locally_connected_space X"
  by (simp add: locally_connected_space_def locally_path_connected_space_def neighbourhood_base_of_mono path_connectedin_imp_connectedin)

lemma locally_connected_space_open_connected_components:
  "locally_connected_space X \<longleftrightarrow>
   (\<forall>U C. openin X U \<and> C \<in> connected_components_of(subtopology X U) \<longrightarrow> openin X C)"
  unfolding connected_components_of_def locally_connected_space_eq_open_connected_component_of
  by (smt (verit, best) image_iff openin_subset topspace_subtopology_subset)

lemma openin_connected_component_of_locally_connected_space:
   "locally_connected_space X \<Longrightarrow> openin X (connected_component_of_set X x)"
  by (metis connected_component_of_eq_empty locally_connected_B openin_empty openin_topspace subtopology_topspace)

lemma openin_connected_components_of_locally_connected_space:
   "\<lbrakk>locally_connected_space X; C \<in> connected_components_of X\<rbrakk> \<Longrightarrow> openin X C"
  by (metis locally_connected_space_open_connected_components openin_topspace subtopology_topspace)

lemma weakly_locally_connected_at:
   "weakly_locally_connected_at x X \<longleftrightarrow>
    (\<forall>V. openin X V \<and> x \<in> V
       \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> U \<subseteq> V \<and>
                (\<forall>y \<in> U. \<exists>C. connectedin X C \<and> C \<subseteq> V \<and> x \<in> C \<and> y \<in> C)))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    unfolding neighbourhood_base_at_def weakly_locally_connected_at_def
    by (meson subsetD subset_trans)
next
  assume R: ?rhs
  show ?lhs
    unfolding neighbourhood_base_at_def weakly_locally_connected_at_def
  proof clarify
    fix V
    assume "openin X V" and "x \<in> V"
    then obtain U where "openin X U" "x \<in> U" "U \<subseteq> V" 
                  and U: "\<forall>y\<in>U. \<exists>C. connectedin X C \<and> C \<subseteq> V \<and> x \<in> C \<and> y \<in> C"
      using R by force
    show "\<exists>A B. openin X A \<and> connectedin X B \<and> x \<in> A \<and> A \<subseteq> B \<and> B \<subseteq> V"
    proof (intro conjI exI)
      show "connectedin X (connected_component_of_set (subtopology X V) x)"
        by (meson connectedin_connected_component_of connectedin_subtopology)
      show "U \<subseteq> connected_component_of_set (subtopology X V) x"
        using connected_component_of_maximal U
        by (simp add: connected_component_of_def connectedin_subtopology subsetI)
      show "connected_component_of_set (subtopology X V) x \<subseteq> V"
        using connected_component_of_subset_topspace by fastforce
    qed (auto simp: \<open>x \<in> U\<close> \<open>openin X U\<close>)
  qed
qed

lemma locally_connected_space_iff_weak:
  "locally_connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. weakly_locally_connected_at x X)"
  by (simp add: locally_connected_space_def neighbourhood_base_of_def weakly_locally_connected_at_def)

lemma locally_connected_space_im_kleinen:
   "locally_connected_space X \<longleftrightarrow>
    (\<forall>V x. openin X V \<and> x \<in> V
          \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> U \<subseteq> V \<and>
                    (\<forall>y \<in> U. \<exists>C. connectedin X C \<and> C \<subseteq> V \<and> x \<in> C \<and> y \<in> C)))"
  unfolding locally_connected_space_iff_weak weakly_locally_connected_at
  using openin_subset subsetD by fastforce

lemma locally_connected_space_open_subset:
   "\<lbrakk>locally_connected_space X; openin X S\<rbrakk> \<Longrightarrow> locally_connected_space (subtopology X S)"
  unfolding locally_connected_space_def neighbourhood_base_of
  by (smt (verit) connectedin_subtopology openin_open_subtopology subset_trans)

lemma locally_connected_space_quotient_map_image:
  assumes X: "locally_connected_space X" and f: "quotient_map X Y f"
  shows "locally_connected_space Y"
  unfolding locally_connected_space_open_connected_components
proof clarify
  fix V C
  assume "openin Y V" and C: "C \<in> connected_components_of (subtopology Y V)"
  then have "C \<subseteq> topspace Y"
    using connected_components_of_subset by force
  have ope1: "openin X {a \<in> topspace X. f a \<in> V}"
    using \<open>openin Y V\<close> f openin_continuous_map_preimage quotient_imp_continuous_map by blast
  define Vf where "Vf \<equiv> {z \<in> topspace X. f z \<in> V}"
  have "openin X {x \<in> topspace X. f x \<in> C}"
  proof (clarsimp simp: openin_subopen [where S = "{x \<in> topspace X. f x \<in> C}"])
    fix x
    assume "x \<in> topspace X" and "f x \<in> C"
    show "\<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> {x \<in> topspace X. f x \<in> C}"
    proof (intro exI conjI)
      show "openin X (connected_component_of_set (subtopology X Vf) x)"
        by (metis Vf_def X connected_component_of_eq_empty locally_connected_B ope1 openin_empty
                  openin_subset topspace_subtopology_subset)
      show x_in_conn: "x \<in> connected_component_of_set (subtopology X Vf) x"
        using C Vf_def \<open>f x \<in> C\<close> \<open>x \<in> topspace X\<close> connected_component_of_refl connected_components_of_subset by fastforce
      have "connected_component_of_set (subtopology X Vf) x \<subseteq> topspace X \<inter> Vf"
        using connected_component_of_subset_topspace by fastforce
      moreover
      have "f ` connected_component_of_set (subtopology X Vf) x \<subseteq> C"
      proof (rule connected_components_of_maximal [where X = "subtopology Y V"])
        show "C \<in> connected_components_of (subtopology Y V)"
          by (simp add: C)
        have \<section>: "quotient_map (subtopology X Vf) (subtopology Y V) f"
          by (simp add: Vf_def \<open>openin Y V\<close> f quotient_map_restriction)
        then show "connectedin (subtopology Y V) (f ` connected_component_of_set (subtopology X Vf) x)"
          by (metis connectedin_connected_component_of connectedin_continuous_map_image quotient_imp_continuous_map)
        show "\<not> disjnt C (f ` connected_component_of_set (subtopology X Vf) x)"
          using \<open>f x \<in> C\<close> x_in_conn by (auto simp: disjnt_iff)
      qed
      ultimately
      show "connected_component_of_set (subtopology X Vf) x \<subseteq> {x \<in> topspace X. f x \<in> C}"
        by blast
    qed
  qed
  then show "openin Y C"
    using \<open>C \<subseteq> topspace Y\<close> f quotient_map_def by fastforce
qed


lemma locally_connected_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; locally_connected_space X\<rbrakk>
        \<Longrightarrow> locally_connected_space Y"
  using locally_connected_space_quotient_map_image retraction_imp_quotient_map by blast

lemma homeomorphic_locally_connected_space:
   "X homeomorphic_space Y \<Longrightarrow> locally_connected_space X \<longleftrightarrow> locally_connected_space Y"
  by (meson homeomorphic_map_def homeomorphic_space homeomorphic_space_sym locally_connected_space_quotient_map_image)

lemma locally_connected_space_euclideanreal: "locally_connected_space euclideanreal"
  by (simp add: locally_path_connected_imp_locally_connected_space locally_path_connected_space_euclideanreal)

lemma locally_connected_is_realinterval:
   "is_interval S \<Longrightarrow> locally_connected_space(subtopology euclideanreal S)"
  by (simp add: locally_path_connected_imp_locally_connected_space locally_path_connected_is_realinterval)

lemma locally_connected_real_interval:
    "locally_connected_space (subtopology euclideanreal{a..b})"
    "locally_connected_space (subtopology euclideanreal{a<..<b})"
  using connected_Icc is_interval_connected_1 locally_connected_is_realinterval by auto

lemma locally_connected_space_discrete_topology:
   "locally_connected_space (discrete_topology U)"
  by (simp add: locally_path_connected_imp_locally_connected_space locally_path_connected_space_discrete_topology)

lemma locally_path_connected_imp_locally_connected_at:
   "locally_path_connected_at x X \<Longrightarrow> locally_connected_at x X"
  by (simp add: locally_connected_at_def locally_path_connected_at_def neighbourhood_base_at_mono path_connectedin_imp_connectedin)

lemma weakly_locally_path_connected_imp_weakly_locally_connected_at:
   "weakly_locally_path_connected_at x X \<Longrightarrow> weakly_locally_connected_at x X"
  by (metis path_connectedin_imp_connectedin weakly_locally_connected_at weakly_locally_path_connected_at)


lemma interior_of_locally_connected_subspace_component:
  assumes X: "locally_connected_space X"
    and C: "C \<in> connected_components_of (subtopology X S)"
  shows "X interior_of C = C \<inter> X interior_of S"
proof -
  obtain Csub: "C \<subseteq> topspace X" "C \<subseteq> S"
    by (meson C connectedin_connected_components_of connectedin_subset_topspace connectedin_subtopology)
  show ?thesis
  proof
    show "X interior_of C \<subseteq> C \<inter> X interior_of S"
      by (simp add: Csub interior_of_mono interior_of_subset)
    have eq: "X interior_of S = \<Union> (connected_components_of (subtopology X (X interior_of S)))"
      by (metis Union_connected_components_of interior_of_subset_topspace topspace_subtopology_subset)
    moreover have "C \<inter> D \<subseteq> X interior_of C"
      if "D \<in> connected_components_of (subtopology X (X interior_of S))" for D
    proof (cases "C \<inter> D = {}")
      case False
      have "D \<subseteq> X interior_of C"
      proof (rule interior_of_maximal)
        have "connectedin (subtopology X S) D"
          by (meson connectedin_connected_components_of connectedin_subtopology interior_of_subset subset_trans that)
        then show "D \<subseteq> C"
          by (meson C False connected_components_of_maximal disjnt_def)
        show "openin X D"
          using X locally_connected_space_open_connected_components openin_interior_of that by blast
      qed
      then show ?thesis 
        by blast
    qed auto
    ultimately show "C \<inter> X interior_of S \<subseteq> X interior_of C"
      by blast
  qed
qed


lemma frontier_of_locally_connected_subspace_component:
  assumes X: "locally_connected_space X" and "closedin X S" 
    and C: "C \<in> connected_components_of (subtopology X S)"
  shows "X frontier_of C = C \<inter> X frontier_of S"
proof -
  obtain Csub: "C \<subseteq> topspace X" "C \<subseteq> S"
    by (meson C connectedin_connected_components_of connectedin_subset_topspace connectedin_subtopology)
  then have "X closure_of C - X interior_of C = C \<inter> X closure_of S - C \<inter> X interior_of S"
    using assms
    apply (simp add: closure_of_closedin flip: interior_of_locally_connected_subspace_component)
    by (metis closedin_connected_components_of closedin_trans_full closure_of_eq inf.orderE)
  then show ?thesis
    by (simp add: Diff_Int_distrib frontier_of_def)
qed

(*Similar proof to locally_connected_space_prod_topology*)
lemma locally_connected_space_prod_topology:
   "locally_connected_space (prod_topology X Y) \<longleftrightarrow>
      (prod_topology X Y) = trivial_topology \<or>
      locally_connected_space X \<and> locally_connected_space Y" (is "?lhs=?rhs")
proof (cases "(prod_topology X Y) = trivial_topology")
  case True
  then show ?thesis
    using locally_connected_space_iff_weak by force
next
  case False
  then have ne: "X \<noteq> trivial_topology" "Y \<noteq> trivial_topology"
    by simp_all
  show ?thesis
  proof
    assume ?lhs then show ?rhs
      by (metis locally_connected_space_quotient_map_image ne quotient_map_fst quotient_map_snd)
  next
    assume ?rhs
    with False have X: "locally_connected_space X" and Y: "locally_connected_space Y"
      by auto
    show ?lhs
      unfolding locally_connected_space_def neighbourhood_base_of
    proof clarify
      fix UV x y
      assume UV: "openin (prod_topology X Y) UV" and "(x,y) \<in> UV"

     obtain A B where W12: "openin X A \<and> openin Y B \<and> x \<in> A \<and> y \<in> B \<and> A \<times> B \<subseteq> UV"
        using X Y by (metis UV \<open>(x,y) \<in> UV\<close> openin_prod_topology_alt)
      then obtain C D K L
        where "openin X C" "connectedin X K" "x \<in> C" "C \<subseteq> K" "K \<subseteq> A"
          "openin Y D" "connectedin Y L" "y \<in> D" "D \<subseteq> L" "L \<subseteq> B"
        by (metis X Y locally_connected_space)
      with W12 \<open>openin X C\<close> \<open>openin Y D\<close>
      show "\<exists>U V. openin (prod_topology X Y) U \<and> connectedin (prod_topology X Y) V \<and> (x, y) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> UV"
        apply (rule_tac x="C \<times> D" in exI)
        apply (rule_tac x="K \<times> L" in exI)
        apply (auto simp: openin_prod_Times_iff connectedin_Times)
        done
    qed
  qed
qed

(*Same proof as locally_path_connected_space_product_topology*)
lemma locally_connected_space_product_topology:
   "locally_connected_space(product_topology X I) \<longleftrightarrow>
        (product_topology X I) = trivial_topology \<or>
        finite {i. i \<in> I \<and> ~connected_space(X i)} \<and>
        (\<forall>i \<in> I. locally_connected_space(X i))"
    (is "?lhs \<longleftrightarrow> ?empty \<or> ?rhs")
proof (cases ?empty)
  case True
  then show ?thesis
    by (simp add: locally_connected_space_def neighbourhood_base_of openin_closedin_eq)
next
  case False
  then obtain z where z: "z \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
    using discrete_topology_unique_derived_set by (fastforce iff: null_topspace_iff_trivial)
  have ?rhs if L: ?lhs
  proof -
    obtain U C where U: "openin (product_topology X I) U"
      and V: "connectedin (product_topology X I) C"
      and "z \<in> U" "U \<subseteq> C" and Csub: "C \<subseteq> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
      using L apply (clarsimp simp add: locally_connected_space_def neighbourhood_base_of)
      by (metis openin_topspace topspace_product_topology z)
    then obtain V where finV: "finite {i \<in> I. V i \<noteq> topspace (X i)}"
      and XV: "\<And>i. i\<in>I \<Longrightarrow> openin (X i) (V i)" and "z \<in> Pi\<^sub>E I V" and subU: "Pi\<^sub>E I V \<subseteq> U"
      by (force simp: openin_product_topology_alt)
    show ?thesis
    proof (intro conjI ballI)
      have "connected_space (X i)" if "i \<in> I" "V i = topspace (X i)" for i
      proof -
        have pc: "connectedin (X i) ((\<lambda>x. x i) ` C)"
          by (metis V connectedin_continuous_map_image continuous_map_product_projection that(1))
        moreover have "((\<lambda>x. x i) ` C) = topspace (X i)"
        proof
          show "(\<lambda>x. x i) ` C \<subseteq> topspace (X i)"
            by (simp add: pc connectedin_subset_topspace)
          have "V i \<subseteq> (\<lambda>x. x i) ` (\<Pi>\<^sub>E i\<in>I. V i)"
            by (metis \<open>z \<in> Pi\<^sub>E I V\<close> empty_iff image_projection_PiE order_refl that(1))
          also have "\<dots> \<subseteq> (\<lambda>x. x i) ` U"
            using subU by blast
          finally show "topspace (X i) \<subseteq> (\<lambda>x. x i) ` C"
            using \<open>U \<subseteq> C\<close> that by blast
        qed
        ultimately show ?thesis
          by (simp add: connectedin_topspace)
      qed
      then have "{i \<in> I. \<not> connected_space (X i)} \<subseteq> {i \<in> I. V i \<noteq> topspace (X i)}"
        by blast
      with finV show "finite {i \<in> I. \<not> connected_space (X i)}"
        using finite_subset by blast
    next
      show "locally_connected_space (X i)" if "i \<in> I" for i
        by (meson False L locally_connected_space_quotient_map_image quotient_map_product_projection that)
    qed
  qed
  moreover have ?lhs if R: ?rhs
  proof (clarsimp simp add: locally_connected_space_def neighbourhood_base_of)
    fix F z
    assume "openin (product_topology X I) F" and "z \<in> F"
    then obtain W where finW: "finite {i \<in> I. W i \<noteq> topspace (X i)}"
            and opeW: "\<And>i. i \<in> I \<Longrightarrow> openin (X i) (W i)" and "z \<in> Pi\<^sub>E I W" "Pi\<^sub>E I W \<subseteq> F"
      by (auto simp: openin_product_topology_alt)
    have "\<forall>i \<in> I. \<exists>U C. openin (X i) U \<and> connectedin (X i) C \<and> z i \<in> U \<and> U \<subseteq> C \<and> C \<subseteq> W i \<and>
                        (W i = topspace (X i) \<and>
                         connected_space (X i) \<longrightarrow> U = topspace (X i) \<and> C = topspace (X i))"
          (is "\<forall>i \<in> I. ?\<Phi> i")
    proof
      fix i assume "i \<in> I"
      have "locally_connected_space (X i)"
        by (simp add: R \<open>i \<in> I\<close>)
      moreover have *: "openin (X i) (W i)" "z i \<in> W i"
        using \<open>z \<in> Pi\<^sub>E I W\<close> opeW \<open>i \<in> I\<close> by auto
      ultimately obtain U C where "openin (X i) U" "connectedin (X i) C" "z i \<in> U" "U \<subseteq> C" "C \<subseteq> W i"
        using \<open>i \<in> I\<close> by (force simp: locally_connected_space_def neighbourhood_base_of)
      then show "?\<Phi> i"
        by (metis * connectedin_topspace openin_subset)
    qed
    then obtain U C where
      *: "\<And>i. i \<in> I \<Longrightarrow> openin (X i) (U i) \<and> connectedin (X i) (C i) \<and> z i \<in> (U i) \<and> (U i) \<subseteq> (C i) \<and> (C i) \<subseteq> W i \<and>
                        (W i = topspace (X i) \<and> connected_space (X i)
                         \<longrightarrow> (U i) = topspace (X i) \<and> (C i) = topspace (X i))"
      by metis
    let ?A = "{i \<in> I. \<not> connected_space (X i)} \<union> {i \<in> I. W i \<noteq> topspace (X i)}"
    have "{i \<in> I. U i \<noteq> topspace (X i)} \<subseteq> ?A"
      by (clarsimp simp add: "*")
    moreover have "finite ?A"
      by (simp add: that finW)
    ultimately have "finite {i \<in> I. U i \<noteq> topspace (X i)}"
      using finite_subset by auto
    then have "openin (product_topology X I) (Pi\<^sub>E I U)"
      using * by (simp add: openin_PiE_gen)
    then show "\<exists>U. openin (product_topology X I) U \<and>
            (\<exists>V. connectedin (product_topology X I) V \<and> z \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> F)"
      using \<open>z \<in> Pi\<^sub>E I W\<close> \<open>Pi\<^sub>E I W \<subseteq> F\<close> *
      by (metis (no_types, opaque_lifting) PiE_iff PiE_mono connectedin_PiE subset_iff)
  qed
  ultimately show ?thesis
    using False by blast
qed

lemma locally_connected_space_sum_topology:
   "locally_connected_space(sum_topology X I) \<longleftrightarrow>
    (\<forall>i \<in> I. locally_connected_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (smt (verit) homeomorphic_locally_connected_space locally_connected_space_open_subset topological_property_of_sum_component)
next
  assume R: ?rhs
  show ?lhs
  proof (clarsimp simp add: locally_connected_space_def neighbourhood_base_of forall_openin_sum_topology imp_conjL)
    fix W i x
    assume ope: "\<forall>i\<in>I. openin (X i) (W i)" 
      and "i \<in> I" and "x \<in> W i"
    then obtain U V where U: "openin (X i) U" and V: "connectedin (X i) V" 
           and "x \<in> U" "U \<subseteq> V" "V \<subseteq> W i"
      by (metis R \<open>i \<in> I\<close> \<open>x \<in> W i\<close> locally_connected_space)
    show "\<exists>U. openin (sum_topology X I) U \<and> (\<exists>V. connectedin (sum_topology X I) V \<and> (i,x) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> Sigma I W)"
    proof (intro exI conjI)
      show "openin (sum_topology X I) (Pair i ` U)"
        by (meson U \<open>i \<in> I\<close> open_map_component_injection open_map_def)
      show "connectedin (sum_topology X I) (Pair i ` V)"
        by (meson V \<open>i \<in> I\<close> continuous_map_component_injection connectedin_continuous_map_image)
      show "Pair i ` V \<subseteq> Sigma I W"
        using \<open>V \<subseteq> W i\<close> \<open>i \<in> I\<close> by force
    qed (use \<open>x \<in> U\<close> \<open>U \<subseteq> V\<close> in auto)
  qed
qed

subsection \<open>Dimension of a topological space\<close>

text\<open>Basic definition of the small inductive dimension relation. Works in any topological space.\<close>

inductive dimension_le :: "['a topology, int] \<Rightarrow> bool" (infix \<open>dim'_le\<close> 50) 
  where "\<lbrakk>-1 \<le> n;
        \<And>V a. \<lbrakk>openin X V; a \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> (subtopology X (X frontier_of U)) dim_le (n-1)\<rbrakk>
              \<Longrightarrow> X dim_le (n::int)"

lemma dimension_le_neighbourhood_base:
   "X dim_le n \<longleftrightarrow>
   -1 \<le> n \<and> neighbourhood_base_of (\<lambda>U. openin X U \<and> (subtopology X (X frontier_of U)) dim_le (n-1)) X"
  by (smt (verit, best) dimension_le.simps open_neighbourhood_base_of)

lemma dimension_le_bound: "X dim_le n \<Longrightarrow>-1 \<le> n"
  using dimension_le.simps by blast
  
lemma dimension_le_mono [rule_format]:
  assumes "X dim_le m"
  shows "m \<le> n \<longrightarrow> X dim_le n"
  using assms
proof (induction arbitrary: n rule: dimension_le.induct)
qed (smt (verit) dimension_le.simps)

inductive_simps dim_le_minus2 [simp]: "X dim_le -2"

lemma dimension_le_eq_empty [simp]:
   "X dim_le -1 \<longleftrightarrow> X = trivial_topology"
proof
  show "X dim_le (-1) \<Longrightarrow> X = trivial_topology"
    by (force intro: dimension_le.cases)
next
  show "X = trivial_topology \<Longrightarrow> X dim_le (-1)"
    using dimension_le.simps openin_subset by fastforce
qed

lemma dimension_le_0_neighbourhood_base_of_clopen:
  "X dim_le 0 \<longleftrightarrow> neighbourhood_base_of (\<lambda>U. closedin X U \<and> openin X U) X"
proof -
  have "(subtopology X (X frontier_of U) dim_le -1) = closedin X U" 
      if "openin X U" for U
    using that clopenin_eq_frontier_of openin_subset 
    by (fastforce simp add: subtopology_trivial_iff frontier_of_subset_topspace Int_absorb1)
  then show ?thesis
    by (smt (verit, del_insts) dimension_le.simps open_neighbourhood_base_of)
qed

lemma dimension_le_subtopology:
  "X dim_le n \<Longrightarrow> subtopology X S dim_le n"
proof (induction arbitrary: S rule: dimension_le.induct)
  case (1 n X)
  show ?case 
  proof (intro dimension_le.intros)
    show "- 1 \<le> n"
      by (simp add: "1.hyps")
    fix U' a
    assume U': "openin (subtopology X S) U'" and "a \<in> U'"
    then obtain U where U: "openin X U" "U' = U \<inter> S"
      by (meson openin_subtopology)
    then obtain V where "a \<in> V" "V \<subseteq> U" "openin X V" 
      and subV: "subtopology X (X frontier_of V) dim_le n-1" 
      and dimV: "\<And>T. subtopology X (X frontier_of V \<inter> T) dim_le n-1"
      by (metis "1.IH" Int_iff \<open>a \<in> U'\<close> subtopology_subtopology)
    show "\<exists>W. a \<in> W \<and> W \<subseteq> U' \<and> openin (subtopology X S) W \<and> subtopology (subtopology X S) (subtopology X S frontier_of W) dim_le n-1"
    proof (intro exI conjI)
      show "a \<in> S \<inter> V" "S \<inter> V \<subseteq> U'"
        using \<open>U' = U \<inter> S\<close> \<open>a \<in> U'\<close> \<open>a \<in> V\<close> \<open>V \<subseteq> U\<close> by blast+
      show "openin (subtopology X S) (S \<inter> V)"
        by (simp add: \<open>openin X V\<close> openin_subtopology_Int2)
      have "S \<inter> subtopology X S frontier_of V \<subseteq> X frontier_of V"
        by (simp add: frontier_of_subtopology_subset)
      then show "subtopology (subtopology X S) (subtopology X S frontier_of (S \<inter> V)) dim_le n-1"
        by (metis dimV frontier_of_restrict inf.absorb_iff2 inf_left_idem subtopology_subtopology topspace_subtopology)
    qed
  qed
qed

lemma dimension_le_subtopologies:
   "\<lbrakk>subtopology X T dim_le n; S \<subseteq> T\<rbrakk> \<Longrightarrow> (subtopology X S) dim_le n"
  by (metis dimension_le_subtopology inf.absorb_iff2 subtopology_subtopology)

lemma dimension_le_eq_subtopology:
   "(subtopology X S) dim_le n \<longleftrightarrow>
    -1 \<le> n \<and>
    (\<forall>V a. openin X V \<and> a \<in> V \<and> a \<in> S
           \<longrightarrow> (\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and>
                    subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le (n-1)))"
proof -
  have *: "(\<exists>T. a \<in> T \<and> T \<inter> S \<subseteq> V \<inter> S \<and> openin X T \<and> subtopology X (S \<inter> (subtopology X S frontier_of (T \<inter> S))) dim_le n-1)
       \<longleftrightarrow> (\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le n-1)"
    if "a \<in> V" "a \<in> S" "openin X V" for a V
  proof -
    have "\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le n-1"
      if "a \<in> T" and sub: "T \<inter> S \<subseteq> V \<inter> S" and "openin X T"
        and dim: "subtopology X (S \<inter> subtopology X S frontier_of (T \<inter> S)) dim_le n-1"
      for T 
    proof (intro exI conjI)
      show "openin X (T \<inter> V)"
        using \<open>openin X V\<close> \<open>openin X T\<close> by blast
      show "subtopology X (subtopology X S frontier_of (S \<inter> (T \<inter> V))) dim_le n-1"
        by (metis dim frontier_of_subset_subtopology inf.boundedE inf_absorb2 inf_assoc inf_commute sub)
    qed (use \<open>a \<in> V\<close> \<open>a \<in> T\<close> in auto)
    moreover have "\<exists>T. a \<in> T \<and> T \<inter> S \<subseteq> V \<inter> S \<and> openin X T \<and> subtopology X (S \<inter> subtopology X S frontier_of (T \<inter> S)) dim_le n-1"
      if "a \<in> U" and "U \<subseteq> V" and "openin X U"
        and dim: "subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le n-1"
      for U
      by (metis that frontier_of_subset_subtopology inf_absorb2 inf_commute inf_le1 le_inf_iff)
    ultimately show ?thesis
      by safe
  qed
  show ?thesis
    apply (simp add: dimension_le.simps [of _ n] subtopology_subtopology openin_subtopology flip: *)
    by (safe; metis Int_iff inf_le2 le_inf_iff)
qed


lemma homeomorphic_space_dimension_le_aux:
  assumes "X homeomorphic_space Y" "X dim_le of_nat n - 1"
  shows "Y dim_le of_nat n - 1"
  using assms
proof (induction n arbitrary: X Y)
  case 0
  then show ?case
    by (simp add: dimension_le_eq_empty homeomorphic_empty_space)
next
  case (Suc n)
  then have X_dim_n: "X dim_le n"
    by simp
  show ?case 
  proof (clarsimp simp add: dimension_le.simps [of Y n])
    fix V b
    assume "openin Y V" and "b \<in> V"
    obtain f g where fg: "homeomorphic_maps X Y f g"
      using \<open>X homeomorphic_space Y\<close> homeomorphic_space_def by blast
    then have "openin X (g ` V)"
      using \<open>openin Y V\<close> homeomorphic_map_openness_eq homeomorphic_maps_map by blast
    then obtain U where "g b \<in> U" "openin X U" and gim: "U \<subseteq> g ` V" and sub: "subtopology X (X frontier_of U) dim_le int n - int 1"
      using X_dim_n unfolding dimension_le.simps [of X n] by (metis \<open>b \<in> V\<close> imageI of_nat_eq_1_iff)
    show "\<exists>U. b \<in> U \<and> U \<subseteq> V \<and> openin Y U \<and> subtopology Y (Y frontier_of U) dim_le int n - 1"
    proof (intro conjI exI)
      show "b \<in> f ` U"
        by (metis (no_types, lifting) \<open>b \<in> V\<close> \<open>g b \<in> U\<close> \<open>openin Y V\<close> fg homeomorphic_maps_map image_iff openin_subset subsetD)
      show "f ` U \<subseteq> V"
        by (smt (verit, ccfv_threshold) \<open>openin Y V\<close> fg gim homeomorphic_maps_map image_iff openin_subset subset_iff)
      show "openin Y (f ` U)"
        using \<open>openin X U\<close> fg homeomorphic_map_openness_eq homeomorphic_maps_map by blast
      show "subtopology Y (Y frontier_of f ` U) dim_le int n-1"
      proof (rule Suc.IH)
        have "homeomorphic_maps (subtopology X (X frontier_of U)) (subtopology Y (Y frontier_of f ` U)) f g"
          using \<open>openin X U\<close> fg
          by (metis frontier_of_subset_topspace homeomorphic_map_frontier_of homeomorphic_maps_map homeomorphic_maps_subtopologies openin_subset topspace_subtopology topspace_subtopology_subset)
        then show "subtopology X (X frontier_of U) homeomorphic_space subtopology Y (Y frontier_of f ` U)"
          using homeomorphic_space_def by blast
        show "subtopology X (X frontier_of U) dim_le int n-1"
          using sub by fastforce
      qed
    qed
  qed
qed

lemma homeomorphic_space_dimension_le:
  assumes "X homeomorphic_space Y"
  shows "X dim_le n \<longleftrightarrow> Y dim_le n"
proof (cases "n \<ge> -1")
  case True
  then show ?thesis
    using homeomorphic_space_dimension_le_aux [of _ _ "nat(n+1)"] 
    by (smt (verit) assms homeomorphic_space_sym nat_eq_iff)
next
  case False
  then show ?thesis
    by (metis dimension_le_bound)
qed

lemma dimension_le_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; X dim_le n\<rbrakk> \<Longrightarrow> Y dim_le n"
  by (meson dimension_le_subtopology homeomorphic_space_dimension_le retraction_map_def retraction_maps_section_image2)

lemma dimension_le_discrete_topology [simp]: "(discrete_topology U) dim_le 0"
  using dimension_le.simps dimension_le_eq_empty by fastforce

end
