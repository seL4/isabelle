(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light] *)

section \<open>Various Forms of Topological Spaces\<close>

theory Abstract_Topological_Spaces
  imports Lindelof_Spaces Locally Abstract_Euclidean_Space Sum_Topology FSigma
begin


subsection\<open>Connected topological spaces\<close>

lemma connected_space_eq_frontier_eq_empty:
   "connected_space X \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<and> X frontier_of S = {} \<longrightarrow> S = {} \<or> S = topspace X)"
  by (meson clopenin_eq_frontier_of connected_space_clopen_in)

lemma connected_space_frontier_eq_empty:
   "connected_space X \<and> S \<subseteq> topspace X
        \<Longrightarrow> (X frontier_of S = {} \<longleftrightarrow> S = {} \<or> S = topspace X)"
  by (meson connected_space_eq_frontier_eq_empty frontier_of_empty frontier_of_topspace)

lemma connectedin_eq_subset_separated_union:
   "connectedin X C \<longleftrightarrow>
        C \<subseteq> topspace X \<and> (\<forall>S T. separatedin X S T \<and> C \<subseteq> S \<union> T \<longrightarrow> C \<subseteq> S \<or> C \<subseteq> T)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
  using connectedin_subset_topspace connectedin_subset_separated_union by blast
next
  assume ?rhs
  then show ?lhs
  by (metis closure_of_subset connectedin_separation dual_order.eq_iff inf.orderE separatedin_def sup.boundedE)
qed


lemma connectedin_clopen_cases:
   "\<lbrakk>connectedin X C; closedin X T; openin X T\<rbrakk> \<Longrightarrow> C \<subseteq> T \<or> disjnt C T"
  by (metis Diff_eq_empty_iff Int_empty_right clopenin_eq_frontier_of connectedin_Int_frontier_of disjnt_def)

lemma connected_space_retraction_map_image:
   "\<lbrakk>retraction_map X X' r; connected_space X\<rbrakk> \<Longrightarrow> connected_space X'"
  using connected_space_quotient_map_image retraction_imp_quotient_map by blast

lemma connectedin_imp_perfect_gen:
  assumes X: "t1_space X" and S: "connectedin X S" and nontriv: "\<nexists>a. S = {a}"
  shows "S \<subseteq> X derived_set_of S"
unfolding derived_set_of_def
proof (intro subsetI CollectI conjI strip)
  show XS: "x \<in> topspace X" if "x \<in> S" for x
    using that S connectedin by fastforce 
  show "\<exists>y. y \<noteq> x \<and> y \<in> S \<and> y \<in> T"
    if "x \<in> S" and "x \<in> T \<and> openin X T" for x T
  proof -
    have opeXx: "openin X (topspace X - {x})"
      by (meson X openin_topspace t1_space_openin_delete_alt)
    moreover
    have "S \<subseteq> T \<union> (topspace X - {x})"
      using XS that(2) by auto
    moreover have "(topspace X - {x}) \<inter> S \<noteq> {}"
      by (metis Diff_triv S connectedin double_diff empty_subsetI inf_commute insert_subsetI nontriv that(1))
    ultimately show ?thesis
      using that connectedinD [OF S, of T "topspace X - {x}"]
      by blast
  qed
qed

lemma connectedin_imp_perfect:
  "\<lbrakk>Hausdorff_space X; connectedin X S; \<nexists>a. S = {a}\<rbrakk> \<Longrightarrow> S \<subseteq> X derived_set_of S"
  by (simp add: Hausdorff_imp_t1_space connectedin_imp_perfect_gen)



subsection\<open>The notion of "separated between" (complement of "connected between)"\<close>

definition separated_between 
  where "separated_between X S T \<equiv>
        \<exists>U V. openin X U \<and> openin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> S \<subseteq> U \<and> T \<subseteq> V"

lemma separated_between_alt:
   "separated_between X S T \<longleftrightarrow>
        (\<exists>U V. closedin X U \<and> closedin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> S \<subseteq> U \<and> T \<subseteq> V)"
  unfolding separated_between_def
  by (metis separatedin_open_sets separation_closedin_Un_gen subtopology_topspace 
            separatedin_closed_sets separation_openin_Un_gen)

lemma separated_between:
   "separated_between X S T \<longleftrightarrow>
        (\<exists>U. closedin X U \<and> openin X U \<and> S \<subseteq> U \<and> T \<subseteq> topspace X - U)"
  unfolding separated_between_def closedin_def disjnt_def
  by (smt (verit, del_insts) Diff_cancel Diff_disjoint Diff_partition Un_Diff Un_Diff_Int openin_subset)

lemma separated_between_mono:
   "\<lbrakk>separated_between X S T; S' \<subseteq> S; T' \<subseteq> T\<rbrakk> \<Longrightarrow> separated_between X S' T'"
  by (meson order.trans separated_between)

lemma separated_between_refl:
   "separated_between X S S \<longleftrightarrow> S = {}"
  unfolding separated_between_def
  by (metis Un_empty_right disjnt_def disjnt_empty2 disjnt_subset2 disjnt_sym le_iff_inf openin_empty openin_topspace)

lemma separated_between_sym:
   "separated_between X S T \<longleftrightarrow> separated_between X T S"
  by (metis disjnt_sym separated_between_alt sup_commute)

lemma separated_between_imp_subset:
   "separated_between X S T \<Longrightarrow> S \<subseteq> topspace X \<and> T \<subseteq> topspace X"
  by (metis le_supI1 le_supI2 separated_between_def)

lemma separated_between_empty: 
  "(separated_between X {} S \<longleftrightarrow> S \<subseteq> topspace X) \<and> (separated_between X S {} \<longleftrightarrow> S \<subseteq> topspace X)"
  by (metis Diff_empty bot.extremum closedin_empty openin_empty separated_between separated_between_imp_subset separated_between_sym)


lemma separated_between_Un: 
  "separated_between X S (T \<union> U) \<longleftrightarrow> separated_between X S T \<and> separated_between X S U"
  by (auto simp: separated_between)

lemma separated_between_Un': 
  "separated_between X (S \<union> T) U \<longleftrightarrow> separated_between X S U \<and> separated_between X T U"
  by (simp add: separated_between_Un separated_between_sym)

lemma separated_between_imp_disjoint:
   "separated_between X S T \<Longrightarrow> disjnt S T"
  by (meson disjnt_iff separated_between_def subsetD)

lemma separated_between_imp_separatedin:
   "separated_between X S T \<Longrightarrow> separatedin X S T"
  by (meson separated_between_def separatedin_mono separatedin_open_sets)

lemma separated_between_full:
  assumes "S \<union> T = topspace X"
  shows "separated_between X S T \<longleftrightarrow> disjnt S T \<and> closedin X S \<and> openin X S \<and> closedin X T \<and> openin X T"
proof -
  have "separated_between X S T \<longrightarrow> separatedin X S T"
    by (simp add: separated_between_imp_separatedin)
  then show ?thesis
    unfolding separated_between_def
    by (metis assms separation_closedin_Un_gen separation_openin_Un_gen subset_refl subtopology_topspace)
qed

lemma separated_between_eq_separatedin:
   "S \<union> T = topspace X \<Longrightarrow> (separated_between X S T \<longleftrightarrow> separatedin X S T)"
  by (simp add: separated_between_full separatedin_full)

lemma separated_between_pointwise_left:
  assumes "compactin X S"
  shows "separated_between X S T \<longleftrightarrow>
         (S = {} \<longrightarrow> T \<subseteq> topspace X) \<and> (\<forall>x \<in> S. separated_between X {x} T)"  (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    using separated_between_imp_subset separated_between_mono by fastforce
next
  assume R: ?rhs
  then have "T \<subseteq> topspace X"
    by (meson equals0I separated_between_imp_subset)
  show ?lhs
  proof -
    obtain U where U: "\<forall>x \<in> S. openin X (U x)"
      "\<forall>x \<in> S. \<exists>V. openin X V \<and> U x \<union> V = topspace X \<and> disjnt (U x) V \<and> {x} \<subseteq> U x \<and> T \<subseteq> V"
      using R unfolding separated_between_def by metis
    then have "S \<subseteq> \<Union>(U ` S)"
      by blast
    then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>i\<in>K. U i)"
      using assms U unfolding compactin_def by (smt (verit) finite_subset_image imageE)
    show ?thesis
      unfolding separated_between
    proof (intro conjI exI)
      have "\<And>x. x \<in> K \<Longrightarrow> closedin X (U x)"
        by (smt (verit) \<open>K \<subseteq> S\<close> Diff_cancel U(2) Un_Diff Un_Diff_Int disjnt_def openin_closedin_eq subsetD)
      then show "closedin X (\<Union> (U ` K))"
        by (metis (mono_tags, lifting) \<open>finite K\<close> closedin_Union finite_imageI image_iff)
      show "openin X (\<Union> (U ` K))"
        using U(1) \<open>K \<subseteq> S\<close> by blast
      show "S \<subseteq> \<Union> (U ` K)"
        by (simp add: K)
      have "\<And>x i. \<lbrakk>x \<in> T; i \<in> K; x \<in> U i\<rbrakk> \<Longrightarrow> False"
        by (meson U(2) \<open>K \<subseteq> S\<close> disjnt_iff subsetD)
      then show "T \<subseteq> topspace X - \<Union> (U ` K)"
        using \<open>T \<subseteq> topspace X\<close> by auto
    qed
  qed
qed

lemma separated_between_pointwise_right:
   "compactin X T
        \<Longrightarrow> separated_between X S T \<longleftrightarrow> (T = {} \<longrightarrow> S \<subseteq> topspace X) \<and> (\<forall>y \<in> T. separated_between X S {y})"
  by (meson separated_between_pointwise_left separated_between_sym)

lemma separated_between_closure_of:
  "S \<subseteq> topspace X \<Longrightarrow> separated_between X (X closure_of S) T \<longleftrightarrow> separated_between X S T"
  by (meson closure_of_minimal_eq separated_between_alt)


lemma separated_between_closure_of':
 "T \<subseteq> topspace X \<Longrightarrow> separated_between X S (X closure_of T) \<longleftrightarrow> separated_between X S T"
  by (meson separated_between_closure_of separated_between_sym)

lemma separated_between_closure_of_eq:
 "separated_between X S T \<longleftrightarrow> S \<subseteq> topspace X \<and> separated_between X (X closure_of S) T"
  by (metis separated_between_closure_of separated_between_imp_subset)

lemma separated_between_closure_of_eq':
 "separated_between X S T \<longleftrightarrow> T \<subseteq> topspace X \<and> separated_between X S (X closure_of T)"
  by (metis separated_between_closure_of' separated_between_imp_subset)

lemma separated_between_frontier_of_eq':
  "separated_between X S T \<longleftrightarrow>
   T \<subseteq> topspace X \<and> disjnt S T \<and> separated_between X S (X frontier_of T)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis interior_of_union_frontier_of separated_between_Un separated_between_closure_of_eq' 
        separated_between_imp_disjoint)
next
  assume R: ?rhs
  then obtain U where U: "closedin X U" "openin X U" "S \<subseteq> U" "X closure_of T - X interior_of T \<subseteq> topspace X - U"
    by (metis frontier_of_def separated_between)
  show ?lhs
  proof (rule separated_between_mono [of _ S "X closure_of T"])
    have "separated_between X S T"
      unfolding separated_between
    proof (intro conjI exI)
      show "S \<subseteq> U - T" "T \<subseteq> topspace X - (U - T)"
        using R U(3) by (force simp: disjnt_iff)+
      have "T \<subseteq> X closure_of T"
        by (simp add: R closure_of_subset)
      then have *: "U - T = U - X interior_of T"
        using U(4) interior_of_subset by fastforce
      then show "closedin X (U - T)"
        by (simp add: U(1) closedin_diff)
      have "U \<inter> X frontier_of T = {}"
        using U(4) frontier_of_def by fastforce
      then show "openin X (U - T)"
        by (metis * Diff_Un U(2) Un_Diff_Int Un_Int_eq(1) closedin_closure_of interior_of_union_frontier_of openin_diff sup_bot_right)
    qed
    then show "separated_between X S (X closure_of T)"
      by (simp add: R separated_between_closure_of')
  qed (auto simp: R closure_of_subset)
qed

lemma separated_between_frontier_of_eq:
  "separated_between X S T \<longleftrightarrow> S \<subseteq> topspace X \<and> disjnt S T \<and> separated_between X (X frontier_of S) T"
  by (metis disjnt_sym separated_between_frontier_of_eq' separated_between_sym)

lemma separated_between_frontier_of:
  "\<lbrakk>S \<subseteq> topspace X; disjnt S T\<rbrakk>
   \<Longrightarrow> (separated_between X (X frontier_of S) T \<longleftrightarrow> separated_between X S T)"
  using separated_between_frontier_of_eq by blast

lemma separated_between_frontier_of':
 "\<lbrakk>T \<subseteq> topspace X; disjnt S T\<rbrakk>
   \<Longrightarrow> (separated_between X S (X frontier_of T) \<longleftrightarrow> separated_between X S T)"
  using separated_between_frontier_of_eq' by auto

lemma connected_space_separated_between:
  "connected_space X \<longleftrightarrow> (\<forall>S T. separated_between X S T \<longrightarrow> S = {} \<or> T = {})" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis Diff_cancel connected_space_clopen_in separated_between subset_empty)
next
  assume ?rhs then show ?lhs
    by (meson connected_space_eq_not_separated separated_between_eq_separatedin)
qed

lemma connected_space_imp_separated_between_trivial:
   "connected_space X
        \<Longrightarrow> (separated_between X S T \<longleftrightarrow> S = {} \<and> T \<subseteq> topspace X \<or> S \<subseteq> topspace X \<and> T = {})"
  by (metis connected_space_separated_between separated_between_empty)


subsection\<open>Connected components\<close>

lemma connected_component_of_subtopology_eq:
   "connected_component_of (subtopology X U) a = connected_component_of X a \<longleftrightarrow>
    connected_component_of_set X a \<subseteq> U"
  by (force simp: connected_component_of_set connectedin_subtopology connected_component_of_def fun_eq_iff subset_iff)

lemma connected_components_of_subtopology:
  assumes "C \<in> connected_components_of X" "C \<subseteq> U"
  shows "C \<in> connected_components_of (subtopology X U)"
proof -
  obtain a where a: "connected_component_of_set X a \<subseteq> U" and "a \<in> topspace X"
             and Ceq: "C = connected_component_of_set X a"
    using assms by (force simp: connected_components_of_def)
  then have "a \<in> U"
    by (simp add: connected_component_of_refl in_mono)
  then have "connected_component_of_set X a = connected_component_of_set (subtopology X U) a"
    by (metis a connected_component_of_subtopology_eq)
  then show ?thesis
    by (simp add: Ceq \<open>a \<in> U\<close> \<open>a \<in> topspace X\<close> connected_component_in_connected_components_of)
qed

lemma open_in_finite_connected_components:
  assumes "finite(connected_components_of X)" "C \<in> connected_components_of X"
  shows "openin X C"
proof -
  have "closedin X (topspace X - C)"
    by (metis DiffD1 assms closedin_Union closedin_connected_components_of complement_connected_components_of_Union finite_Diff)
  then show ?thesis
    by (simp add: assms connected_components_of_subset openin_closedin)
qed
thm connected_component_of_eq_overlap

lemma connected_components_of_disjoint:
  assumes "C \<in> connected_components_of X" "C' \<in> connected_components_of X"
    shows "(disjnt C C' \<longleftrightarrow> (C \<noteq> C'))"
  using assms nonempty_connected_components_of pairwiseD pairwise_disjoint_connected_components_of by fastforce

lemma connected_components_of_overlap:
   "\<lbrakk>C \<in> connected_components_of X; C' \<in> connected_components_of X\<rbrakk> \<Longrightarrow> C \<inter> C' \<noteq> {} \<longleftrightarrow> C = C'"
  by (meson connected_components_of_disjoint disjnt_def)

lemma pairwise_separated_connected_components_of:
   "pairwise (separatedin X) (connected_components_of X)"
  by (simp add: closedin_connected_components_of connected_components_of_disjoint pairwiseI separatedin_closed_sets)

lemma finite_connected_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(connected_components_of X)"
  by (simp add: Union_connected_components_of finite_UnionD)

lemma connected_component_of_unique:
   "\<lbrakk>x \<in> C; connectedin X C; \<And>C'. x \<in> C' \<and> connectedin X C' \<Longrightarrow> C' \<subseteq> C\<rbrakk>
        \<Longrightarrow> connected_component_of_set X x = C"
  by (meson connected_component_of_maximal connectedin_connected_component_of subsetD subset_antisym)

lemma closedin_connected_component_of_subtopology:
   "\<lbrakk>C \<in> connected_components_of (subtopology X s); X closure_of C \<subseteq> s\<rbrakk> \<Longrightarrow> closedin X C"
  by (metis closedin_Int_closure_of closedin_connected_components_of closure_of_eq inf.absorb_iff2)

lemma connected_component_of_discrete_topology:
   "connected_component_of_set (discrete_topology U) x = (if x \<in> U then {x} else {})"
  by (simp add: locally_path_connected_space_discrete_topology flip: path_component_eq_connected_component_of)

lemma connected_components_of_discrete_topology:
   "connected_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
  by (simp add: connected_component_of_discrete_topology connected_components_of_def)

lemma connected_component_of_continuous_image:
   "\<lbrakk>continuous_map X Y f; connected_component_of X x y\<rbrakk>
        \<Longrightarrow> connected_component_of Y (f x) (f y)"
  by (meson connected_component_of_def connectedin_continuous_map_image image_eqI)

lemma homeomorphic_map_connected_component_of:
  assumes "homeomorphic_map X Y f" and x: "x \<in> topspace X"
  shows "connected_component_of_set Y (f x) = f ` (connected_component_of_set X x)"
proof -
  obtain g where g: "continuous_map X Y f"
    "continuous_map Y X g " "\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x" 
    "\<And>y. y \<in> topspace Y \<Longrightarrow> f (g y) = y"
    using assms(1) homeomorphic_map_maps homeomorphic_maps_def by fastforce
  show ?thesis
    using connected_component_in_topspace [of Y] x g
          connected_component_of_continuous_image [of X Y f]
          connected_component_of_continuous_image [of Y X g]
    by force
qed

lemma homeomorphic_map_connected_components_of:
  assumes "homeomorphic_map X Y f"
  shows "connected_components_of Y = (image f) ` (connected_components_of X)"
proof -
  have "topspace Y = f ` topspace X"
    by (metis assms homeomorphic_imp_surjective_map)
  with homeomorphic_map_connected_component_of [OF assms] show ?thesis
    by (auto simp: connected_components_of_def image_iff)
qed

lemma connected_component_of_pair:
   "connected_component_of_set (prod_topology X Y) (x,y) =
        connected_component_of_set X x \<times> connected_component_of_set Y y"
proof (cases "x \<in> topspace X \<and> y \<in> topspace Y")
  case True
  show ?thesis
  proof (rule connected_component_of_unique)
    show "(x, y) \<in> connected_component_of_set X x \<times> connected_component_of_set Y y"
      using True by (simp add: connected_component_of_refl)
    show "connectedin (prod_topology X Y) (connected_component_of_set X x \<times> connected_component_of_set Y y)"
      by (metis connectedin_Times connectedin_connected_component_of)
    show "C \<subseteq> connected_component_of_set X x \<times> connected_component_of_set Y y"
      if "(x, y) \<in> C \<and> connectedin (prod_topology X Y) C" for C 
      using that unfolding connected_component_of_def
      apply clarsimp
      by (metis (no_types) connectedin_continuous_map_image continuous_map_fst continuous_map_snd fst_conv imageI snd_conv)
  qed
next
  case False then show ?thesis
    by (metis Sigma_empty1 Sigma_empty2 connected_component_of_eq_empty mem_Sigma_iff topspace_prod_topology)
qed

lemma connected_components_of_prod_topology:
  "connected_components_of (prod_topology X Y) =
    {C \<times> D |C D. C \<in> connected_components_of X \<and> D \<in> connected_components_of Y}" (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (clarsimp simp: connected_components_of_def)
    by (metis (no_types) connected_component_of_pair imageI)
next
  show "?rhs \<subseteq> ?lhs"
    using connected_component_of_pair
    by (fastforce simp: connected_components_of_def)
qed


lemma connected_component_of_product_topology:
   "connected_component_of_set (product_topology X I) x =
    (if x \<in> extensional I then PiE I (\<lambda>i. connected_component_of_set (X i) (x i)) else {})"
    (is "?lhs = If _ ?R _")    
proof (cases "x \<in> topspace(product_topology X I)")
  case True
  have "?lhs = (\<Pi>\<^sub>E i\<in>I. connected_component_of_set (X i) (x i))"
    if xX: "\<And>i. i\<in>I \<Longrightarrow> x i \<in> topspace (X i)" and ext: "x \<in> extensional I"
  proof (rule connected_component_of_unique)
    show "x \<in> ?R"
      by (simp add: PiE_iff connected_component_of_refl local.ext xX)
    show "connectedin (product_topology X I) ?R"
      by (simp add: connectedin_PiE connectedin_connected_component_of)
    show "C \<subseteq> ?R"
      if "x \<in> C \<and> connectedin (product_topology X I) C" for C 
    proof -
      have "C \<subseteq> extensional I"
        using PiE_def connectedin_subset_topspace that by fastforce
      have "\<And>y. y \<in> C \<Longrightarrow> y \<in> (\<Pi> i\<in>I. connected_component_of_set (X i) (x i))"
        apply (simp add: connected_component_of_def Pi_def)
        by (metis connectedin_continuous_map_image continuous_map_product_projection imageI that)
      then show ?thesis
        using PiE_def \<open>C \<subseteq> extensional I\<close> by fastforce
    qed
  qed
  with True show ?thesis
    by (simp add: PiE_iff)
next
  case False
  then show ?thesis
    by (smt (verit, best) PiE_eq_empty_iff PiE_iff connected_component_of_eq_empty topspace_product_topology)
qed


lemma connected_components_of_product_topology:
   "connected_components_of (product_topology X I) =
    {PiE I B |B. \<forall>i \<in> I. B i \<in> connected_components_of(X i)}"  (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (auto simp: connected_components_of_def connected_component_of_product_topology PiE_iff)
  show "?rhs \<subseteq> ?lhs"
  proof
    fix F
    assume "F \<in> ?rhs"
    then obtain B where Feq: "F = Pi\<^sub>E I B" and
      "\<forall>i\<in>I. \<exists>x\<in>topspace (X i). B i = connected_component_of_set (X i) x"
      by (force simp: connected_components_of_def connected_component_of_product_topology image_iff)
    then obtain f where
      f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> topspace (X i) \<and> B i = connected_component_of_set (X i) (f i)"
      by metis
    then have "(\<lambda>i\<in>I. f i) \<in> ((\<Pi>\<^sub>E i\<in>I. topspace (X i)) \<inter> extensional I)"
      by simp
    with f show "F \<in> ?lhs"
      unfolding Feq connected_components_of_def connected_component_of_product_topology image_iff
      by (smt (verit, del_insts) PiE_cong restrict_PiE_iff restrict_apply' restrict_extensional topspace_product_topology)
  qed
qed


subsection \<open>Monotone maps (in the general topological sense)\<close>


definition monotone_map 
  where "monotone_map X Y f ==
        f ` (topspace X) \<subseteq> topspace Y \<and>
        (\<forall>y \<in> topspace Y. connectedin X {x \<in> topspace X. f x = y})"

lemma monotone_map:
  "monotone_map X Y f \<longleftrightarrow>
   f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>y. connectedin X {x \<in> topspace X. f x = y})"
  apply (simp add: monotone_map_def)
  by (metis (mono_tags, lifting) connectedin_empty [of X] Collect_empty_eq image_subset_iff) 


lemma monotone_map_in_subtopology:
   "monotone_map X (subtopology Y S) f \<longleftrightarrow> monotone_map X Y f \<and> f ` (topspace X) \<subseteq> S"
  by (smt (verit, del_insts) le_inf_iff monotone_map topspace_subtopology)

lemma monotone_map_from_subtopology:
  assumes "monotone_map X Y f" 
    "\<And>x y. \<lbrakk>x \<in> topspace X; y \<in> topspace X; x \<in> S; f x = f y\<rbrakk> \<Longrightarrow> y \<in> S"
  shows "monotone_map (subtopology X S) Y f"
proof -
  have "\<And>y. y \<in> topspace Y \<Longrightarrow> connectedin X {x \<in> topspace X. x \<in> S \<and> f x = y}"
    by (smt (verit) Collect_cong assms connectedin_empty empty_def monotone_map_def)
  then show ?thesis
    using assms by (auto simp: monotone_map_def connectedin_subtopology)
qed

lemma monotone_map_restriction:
  "monotone_map X Y f \<and> {x \<in> topspace X. f x \<in> v} = u
        \<Longrightarrow> monotone_map (subtopology X u) (subtopology Y v) f"
  by (smt (verit, best) IntI Int_Collect image_subset_iff mem_Collect_eq monotone_map monotone_map_from_subtopology topspace_subtopology)

lemma injective_imp_monotone_map:
  assumes "f ` topspace X \<subseteq> topspace Y"  "inj_on f (topspace X)"
  shows "monotone_map X Y f"
  unfolding monotone_map_def
proof (intro conjI assms strip)
  fix y
  assume "y \<in> topspace Y"
  then have "{x \<in> topspace X. f x = y} = {} \<or> (\<exists>a \<in> topspace X. {x \<in> topspace X. f x = y} = {a})"
    using assms(2) unfolding inj_on_def by blast
  then show "connectedin X {x \<in> topspace X. f x = y}"
    by (metis (no_types, lifting) connectedin_empty connectedin_sing)
qed

lemma embedding_imp_monotone_map:
   "embedding_map X Y f \<Longrightarrow> monotone_map X Y f"
  by (metis (no_types) embedding_map_def homeomorphic_eq_everything_map inf.absorb_iff2 injective_imp_monotone_map topspace_subtopology)

lemma section_imp_monotone_map:
   "section_map X Y f \<Longrightarrow> monotone_map X Y f"
  by (simp add: embedding_imp_monotone_map section_imp_embedding_map)

lemma homeomorphic_imp_monotone_map:
   "homeomorphic_map X Y f \<Longrightarrow> monotone_map X Y f"
  by (meson section_and_retraction_eq_homeomorphic_map section_imp_monotone_map)

proposition connected_space_monotone_quotient_map_preimage:
  assumes f: "monotone_map X Y f" "quotient_map X Y f" and "connected_space Y"
  shows "connected_space X"
proof (rule ccontr)
  assume "\<not> connected_space X"
  then obtain U V where "openin X U" "openin X V" "U \<inter> V = {}"
    "U \<noteq> {}" "V \<noteq> {}" and topUV: "topspace X \<subseteq> U \<union> V"
    by (auto simp: connected_space_def)
  then have UVsub: "U \<subseteq> topspace X" "V \<subseteq> topspace X"
    by (auto simp: openin_subset)
  have "\<not> connected_space Y"
    unfolding connected_space_def not_not
  proof (intro exI conjI)
    show "topspace Y \<subseteq> f`U \<union> f`V"
      by (metis f(2) image_Un quotient_imp_surjective_map subset_Un_eq topUV)
    show "f`U \<noteq> {}"
      by (simp add: \<open>U \<noteq> {}\<close>)
    show "(f`V) \<noteq> {}"
      by (simp add: \<open>V \<noteq> {}\<close>)
    have *: "y \<notin> f ` V" if "y \<in> f ` U" for y
    proof -
      have \<section>: "connectedin X {x \<in> topspace X. f x = y}"
        using f(1) monotone_map by fastforce
      show ?thesis
        using connectedinD [OF \<section> \<open>openin X U\<close> \<open>openin X V\<close>] UVsub topUV \<open>U \<inter> V = {}\<close> that
        by (force simp: disjoint_iff)
    qed
    then show "f`U \<inter> f`V = {}"
      by blast
    show "openin Y (f`U)"
      using f \<open>openin X U\<close> topUV * unfolding quotient_map_saturated_open by force
    show "openin Y (f`V)"
      using f \<open>openin X V\<close> topUV * unfolding quotient_map_saturated_open by force
  qed
  then show False
    by (simp add: assms)
qed

lemma connectedin_monotone_quotient_map_preimage:
  assumes "monotone_map X Y f" "quotient_map X Y f" "connectedin Y C" "openin Y C \<or> closedin Y C"
  shows "connectedin X {x \<in> topspace X. f x \<in> C}"
proof -
  have "connected_space (subtopology X {x \<in> topspace X. f x \<in> C})"
  proof -
    have "connected_space (subtopology Y C)"
      using \<open>connectedin Y C\<close> connectedin_def by blast
    moreover have "quotient_map (subtopology X {a \<in> topspace X. f a \<in> C}) (subtopology Y C) f"
      by (simp add: assms quotient_map_restriction)
    ultimately show ?thesis
      using \<open>monotone_map X Y f\<close> connected_space_monotone_quotient_map_preimage monotone_map_restriction by blast
  qed
  then show ?thesis
    by (simp add: connectedin_def)
qed

lemma monotone_open_map:
  assumes "continuous_map X Y f" "open_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "monotone_map X Y f \<longleftrightarrow> (\<forall>C. connectedin Y C \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> C})"
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding connectedin_def
  proof (intro strip conjI)
    fix C
    assume C: "C \<subseteq> topspace Y \<and> connected_space (subtopology Y C)"
    show "connected_space (subtopology X {x \<in> topspace X. f x \<in> C})"
    proof (rule connected_space_monotone_quotient_map_preimage)
      show "monotone_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
        by (simp add: L monotone_map_restriction)
      show "quotient_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
      proof (rule continuous_open_imp_quotient_map)
        show "continuous_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
          using assms continuous_map_from_subtopology continuous_map_in_subtopology by fastforce
      qed (use open_map_restriction assms in fastforce)+
    qed (simp add: C)
  qed auto
next
  assume ?rhs 
  then have "\<forall>y. connectedin Y {y} \<longrightarrow> connectedin X {x \<in> topspace X. f x = y}"
    by (smt (verit) Collect_cong singletonD singletonI)
  then show ?lhs
    by (simp add: fim monotone_map_def)
qed

lemma monotone_closed_map:
  assumes "continuous_map X Y f" "closed_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "monotone_map X Y f \<longleftrightarrow> (\<forall>C. connectedin Y C \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> C})" 
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding connectedin_def
  proof (intro strip conjI)
    fix C
    assume C: "C \<subseteq> topspace Y \<and> connected_space (subtopology Y C)"
    show "connected_space (subtopology X {x \<in> topspace X. f x \<in> C})"
    proof (rule connected_space_monotone_quotient_map_preimage)
      show "monotone_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
        by (simp add: L monotone_map_restriction)
      show "quotient_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
      proof (rule continuous_closed_imp_quotient_map)
        show "continuous_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
          using assms continuous_map_from_subtopology continuous_map_in_subtopology by fastforce
      qed (use closed_map_restriction assms in fastforce)+
    qed (simp add: C)
  qed auto
next
  assume ?rhs 
  then have "\<forall>y. connectedin Y {y} \<longrightarrow> connectedin X {x \<in> topspace X. f x = y}"
    by (smt (verit) Collect_cong singletonD singletonI)
  then show ?lhs
    by (simp add: fim monotone_map_def)
qed

subsection\<open>Other countability properties\<close>

definition second_countable
  where "second_countable X \<equiv>
         \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and>
             (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U))"

definition first_countable
  where "first_countable X \<equiv>
        \<forall>x \<in> topspace X.
         \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and>
             (\<forall>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U))"

definition separable_space
  where "separable_space X \<equiv>
        \<exists>C. countable C \<and> C \<subseteq> topspace X \<and> X closure_of C = topspace X"

lemma second_countable:
   "second_countable X \<longleftrightarrow>
        (\<exists>\<B>. countable \<B> \<and> openin X = arbitrary union_of (\<lambda>x. x \<in> \<B>))"
  by (smt (verit) openin_topology_base_unique second_countable_def)

lemma second_countable_subtopology:
  assumes "second_countable X"
  shows "second_countable (subtopology X S)"
proof -
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  show ?thesis
    unfolding second_countable_def
  proof (intro exI conjI)
    show "\<forall>V\<in>((\<inter>)S) ` \<B>. openin (subtopology X S) V"
      using openin_subtopology_Int2 \<B> by blast
    show "\<forall>U x. openin (subtopology X S) U \<and> x \<in> U \<longrightarrow> (\<exists>V\<in>((\<inter>)S) ` \<B>. x \<in> V \<and> V \<subseteq> U)"
      using \<B> unfolding openin_subtopology
      by (smt (verit, del_insts) IntI image_iff inf_commute inf_le1 subset_iff)
  qed (use \<B> in auto)
qed


lemma second_countable_discrete_topology:
   "second_countable(discrete_topology U) \<longleftrightarrow> countable U" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> V \<subseteq> U"
    "\<And>W x. W \<subseteq> U \<and> x \<in> W \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> W)"
    by (auto simp: second_countable_def)
  then have "{x} \<in> \<B>" if "x \<in> U" for x
    by (metis empty_subsetI insertCI insert_subset subset_antisym that)
  then show ?rhs
    by (smt (verit) countable_subset image_subsetI \<open>countable \<B>\<close> countable_image_inj_on [OF _ inj_singleton])
next
  assume ?rhs 
  then show ?lhs
    unfolding second_countable_def
    by (rule_tac x="(\<lambda>x. {x}) ` U" in exI) auto
qed

lemma second_countable_open_map_image:
  assumes "continuous_map X Y f" "open_map X Y f" 
   and fim: "f ` (topspace X) = topspace Y" and "second_countable X"
 shows "second_countable Y"
proof -
  have openXYf: "\<And>U. openin X U \<longrightarrow> openin Y (f ` U)"
    using assms by (auto simp: open_map_def)
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  show ?thesis
    unfolding second_countable_def
  proof (intro exI conjI strip)
    fix V y
    assume V: "openin Y V \<and> y \<in> V"
    then obtain x where "x \<in> topspace X" and x: "f x = y"
      by (metis fim image_iff openin_subset subsetD)

    then obtain W where "W\<in>\<B>" "x \<in> W" "W \<subseteq> {x \<in> topspace X. f x \<in> V}"
      using * [of "{x \<in> topspace X. f x \<in> V}" x] V assms openin_continuous_map_preimage 
      by force
    then show "\<exists>W \<in> (image f) ` \<B>. y \<in> W \<and> W \<subseteq> V"
      using x by auto
  qed (use \<B> openXYf in auto)
qed

lemma homeomorphic_space_second_countability:
   "X homeomorphic_space Y \<Longrightarrow> (second_countable X \<longleftrightarrow> second_countable Y)"
  by (meson homeomorphic_eq_everything_map homeomorphic_space homeomorphic_space_sym second_countable_open_map_image)

lemma second_countable_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; second_countable X\<rbrakk> \<Longrightarrow> second_countable Y"
  using hereditary_imp_retractive_property homeomorphic_space_second_countability second_countable_subtopology by blast

lemma second_countable_imp_first_countable:
   "second_countable X \<Longrightarrow> first_countable X"
  by (metis first_countable_def second_countable_def)

lemma first_countable_subtopology:
  assumes "first_countable X"
  shows "first_countable (subtopology X S)"
  unfolding first_countable_def
proof
  fix x
  assume "x \<in> topspace (subtopology X S)"
  then obtain \<B> where "countable \<B>" and \<B>: "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    "\<And>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms first_countable_def by force
  show "\<exists>\<B>. countable \<B> \<and> (\<forall>V\<in>\<B>. openin (subtopology X S) V) \<and> (\<forall>U. openin (subtopology X S) U \<and> x \<in> U \<longrightarrow> (\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> U))"
  proof (intro exI conjI strip)
    show "countable (((\<inter>)S) ` \<B>)"
      using \<open>countable \<B>\<close> by blast
    show "openin (subtopology X S) V" if "V \<in> ((\<inter>)S) ` \<B>" for V
      using \<B> openin_subtopology_Int2 that by fastforce
    show "\<exists>V\<in>((\<inter>)S) ` \<B>. x \<in> V \<and> V \<subseteq> U"
      if "openin (subtopology X S) U \<and> x \<in> U" for U 
      using that \<B>(2) by (clarsimp simp: openin_subtopology) (meson le_infI2)
  qed
qed

lemma first_countable_discrete_topology:
   "first_countable (discrete_topology U)"
  unfolding first_countable_def topspace_discrete_topology openin_discrete_topology
proof
  fix x assume "x \<in> U"
  show "\<exists>\<B>. countable \<B> \<and> (\<forall>V\<in>\<B>. V \<subseteq> U) \<and> (\<forall>Ua. Ua \<subseteq> U \<and> x \<in> Ua \<longrightarrow> (\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> Ua))"
    using \<open>x \<in> U\<close> by (rule_tac x="{{x}}" in exI) auto
qed

lemma first_countable_open_map_image:
  assumes "continuous_map X Y f" "open_map X Y f" 
   and fim: "f ` (topspace X) = topspace Y" and "first_countable X"
 shows "first_countable Y"
  unfolding first_countable_def
proof
  fix y
  assume "y \<in> topspace Y"
  have openXYf: "\<And>U. openin X U \<longrightarrow> openin Y (f ` U)"
    using assms by (auto simp: open_map_def)
  then obtain x where x: "x \<in> topspace X" "f x = y"
    by (metis \<open>y \<in> topspace Y\<close> fim imageE)
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms x first_countable_def by force
  show "\<exists>\<B>. countable \<B> \<and>
              (\<forall>V\<in>\<B>. openin Y V) \<and> (\<forall>U. openin Y U \<and> y \<in> U \<longrightarrow> (\<exists>V\<in>\<B>. y \<in> V \<and> V \<subseteq> U))"
  proof (intro exI conjI strip)
    fix V assume "openin Y V \<and> y \<in> V"
    then have "\<exists>W\<in>\<B>. x \<in> W \<and> W \<subseteq> {x \<in> topspace X. f x \<in> V}"
      using * [of "{x \<in> topspace X. f x \<in> V}"] assms openin_continuous_map_preimage x 
      by fastforce
    then show "\<exists>V' \<in> (image f) ` \<B>. y \<in> V' \<and> V' \<subseteq> V"
      using image_mono x by auto 
  qed (use \<B> openXYf in force)+
qed

lemma homeomorphic_space_first_countability:
  "X homeomorphic_space Y \<Longrightarrow> first_countable X \<longleftrightarrow> first_countable Y"
  by (meson first_countable_open_map_image homeomorphic_eq_everything_map homeomorphic_space homeomorphic_space_sym)

lemma first_countable_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; first_countable X\<rbrakk> \<Longrightarrow> first_countable Y"
  using first_countable_subtopology hereditary_imp_retractive_property homeomorphic_space_first_countability by blast

lemma separable_space_open_subset:
  assumes "separable_space X" "openin X S"
  shows "separable_space (subtopology X S)"
proof -
  obtain C where C: "countable C" "C \<subseteq> topspace X" "X closure_of C = topspace X"
    by (meson assms separable_space_def)
  then have "\<And>x T. \<lbrakk>x \<in> topspace X; x \<in> T; openin (subtopology X S) T\<rbrakk>
           \<Longrightarrow> \<exists>y. y \<in> S \<and> y \<in> C \<and> y \<in> T"
    by (smt (verit) \<open>openin X S\<close> in_closure_of openin_open_subtopology subsetD)
  with C \<open>openin X S\<close> show ?thesis
    unfolding separable_space_def
    by (rule_tac x="S \<inter> C" in exI) (force simp: in_closure_of)
qed

lemma separable_space_continuous_map_image:
  assumes "separable_space X" "continuous_map X Y f" 
    and fim: "f ` (topspace X) = topspace Y"
  shows "separable_space Y"
proof -
  have cont: "\<And>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S"
    by (simp add: assms continuous_map_image_closure_subset)
  obtain C where C: "countable C" "C \<subseteq> topspace X" "X closure_of C = topspace X"
    by (meson assms separable_space_def)
  then show ?thesis
    unfolding separable_space_def
    by (metis cont fim closure_of_subset_topspace countable_image image_mono subset_antisym)
qed

lemma separable_space_quotient_map_image:
  "\<lbrakk>quotient_map X Y q; separable_space X\<rbrakk> \<Longrightarrow> separable_space Y"
  by (meson quotient_imp_continuous_map quotient_imp_surjective_map separable_space_continuous_map_image)

lemma separable_space_retraction_map_image:
  "\<lbrakk>retraction_map X Y r; separable_space X\<rbrakk> \<Longrightarrow> separable_space Y"
  using retraction_imp_quotient_map separable_space_quotient_map_image by blast

lemma homeomorphic_separable_space:
  "X homeomorphic_space Y \<Longrightarrow> (separable_space X \<longleftrightarrow> separable_space Y)"
  by (meson homeomorphic_eq_everything_map homeomorphic_maps_map homeomorphic_space_def separable_space_continuous_map_image)

lemma separable_space_discrete_topology:
   "separable_space(discrete_topology U) \<longleftrightarrow> countable U"
  by (metis countable_Int2 discrete_topology_closure_of dual_order.refl inf.orderE separable_space_def topspace_discrete_topology)

lemma second_countable_imp_separable_space:
  assumes "second_countable X"
  shows "separable_space X"
proof -
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  obtain c where c: "\<And>V. \<lbrakk>V \<in> \<B>; V \<noteq> {}\<rbrakk> \<Longrightarrow> c V \<in> V"
    by (metis all_not_in_conv)
  then have **: "\<And>x. x \<in> topspace X \<Longrightarrow> x \<in> X closure_of c ` (\<B> - {{}})"
    using * by (force simp: closure_of_def)
  show ?thesis
    unfolding separable_space_def
  proof (intro exI conjI)
    show "countable (c ` (\<B>-{{}}))"
      using \<B>(1) by blast
    show "(c ` (\<B>-{{}})) \<subseteq> topspace X"
      using \<B>(2) c openin_subset by fastforce
    show "X closure_of (c ` (\<B>-{{}})) = topspace X"
      by (meson ** closure_of_subset_topspace subsetI subset_antisym)
  qed
qed

lemma second_countable_imp_Lindelof_space:
  assumes "second_countable X"
  shows "Lindelof_space X"
unfolding Lindelof_space_def
proof clarify
  fix \<U>
  assume "\<forall>U \<in> \<U>. openin X U" and UU: "\<Union>\<U> = topspace X"
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  define \<B>' where "\<B>' = {B \<in> \<B>. \<exists>U. U \<in> \<U> \<and> B \<subseteq> U}"
  have \<B>': "countable \<B>'" "\<Union>\<B>' = \<Union>\<U>"
    using \<B> using "*" \<open>\<forall>U\<in>\<U>. openin X U\<close> by (fastforce simp: \<B>'_def)+
  have "\<And>b. \<exists>U. b \<in> \<B>' \<longrightarrow> U \<in> \<U> \<and> b \<subseteq> U" 
    by (simp add: \<B>'_def)
  then obtain G where G: "\<And>b. b \<in> \<B>' \<longrightarrow> G b \<in> \<U> \<and> b \<subseteq> G b" 
    by metis
  with \<B>' UU show "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> \<Union>\<V> = topspace X"
    by (rule_tac x="G ` \<B>'" in exI) fastforce
qed

subsection \<open>Neigbourhood bases EXTRAS\<close>

text \<open>Neigbourhood bases: useful for "local" properties of various kinds\<close>

lemma openin_topology_neighbourhood_base_unique:
   "openin X = arbitrary union_of P \<longleftrightarrow>
        (\<forall>u. P u \<longrightarrow> openin X u) \<and> neighbourhood_base_of P X"
  by (smt (verit, best) open_neighbourhood_base_of openin_topology_base_unique)

lemma neighbourhood_base_at_topology_base:
   "        openin X = arbitrary union_of b
        \<Longrightarrow> (neighbourhood_base_at x P X \<longleftrightarrow>
             (\<forall>w. b w \<and> x \<in> w \<longrightarrow> (\<exists>u v. openin X u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w)))"
  apply (simp add: neighbourhood_base_at_def)
  by (smt (verit, del_insts) openin_topology_base_unique subset_trans)

lemma neighbourhood_base_of_unlocalized:
  assumes "\<And>S t. P S \<and> openin X t \<and> (t \<noteq> {}) \<and> t \<subseteq> S \<Longrightarrow> P t"
  shows "neighbourhood_base_of P X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>u v. openin X u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> topspace X)"
  apply (simp add: neighbourhood_base_of_def)
  by (smt (verit, ccfv_SIG) assms empty_iff neighbourhood_base_at_unlocalized)

lemma neighbourhood_base_at_discrete_topology:
   "neighbourhood_base_at x P (discrete_topology u) \<longleftrightarrow> x \<in> u \<Longrightarrow> P {x}"
  apply (simp add: neighbourhood_base_at_def)
  by (smt (verit) empty_iff empty_subsetI insert_subset singletonI subsetD subset_singletonD)

lemma neighbourhood_base_of_discrete_topology:
   "neighbourhood_base_of P (discrete_topology u) \<longleftrightarrow> (\<forall>x \<in> u. P {x})"
  apply (simp add: neighbourhood_base_of_def)
  using neighbourhood_base_at_discrete_topology[of _ P u]
  by (metis empty_subsetI insert_subset neighbourhood_base_at_def openin_discrete_topology singletonI)

lemma second_countable_neighbourhood_base_alt:
  "second_countable X \<longleftrightarrow> 
  (\<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and> neighbourhood_base_of (\<lambda>A. A\<in>\<B>) X)"
  by (metis (full_types) openin_topology_neighbourhood_base_unique second_countable)

lemma first_countable_neighbourhood_base_alt:
   "first_countable X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X)"
  unfolding first_countable_def
  apply (intro ball_cong refl ex_cong conj_cong)
  by (metis (mono_tags, lifting) open_neighbourhood_base_at)

lemma second_countable_neighbourhood_base:
   "second_countable X \<longleftrightarrow>
        (\<exists>\<B>. countable \<B> \<and> neighbourhood_base_of (\<lambda>V. V \<in> \<B>) X)" (is "?lhs=?rhs")
proof
  assume ?lhs 
  then show ?rhs
    using second_countable_neighbourhood_base_alt by blast
next
  assume ?rhs 
  then obtain \<B> where "countable \<B>"
    and \<B>: "\<And>W x. openin X W \<and> x \<in> W \<longrightarrow> (\<exists>U. openin X U \<and> (\<exists>V. V \<in> \<B> \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W))"
    by (metis neighbourhood_base_of)
  then show ?lhs
    unfolding second_countable_neighbourhood_base_alt neighbourhood_base_of
    apply (rule_tac x="(\<lambda>u. X interior_of u) ` \<B>" in exI)
    by (smt (verit, best) interior_of_eq interior_of_mono countable_image image_iff openin_interior_of)
qed

lemma first_countable_neighbourhood_base:
   "first_countable X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<exists>\<B>. countable \<B> \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X)" (is "?lhs=?rhs")
proof
  assume ?lhs 
  then show ?rhs
    by (metis first_countable_neighbourhood_base_alt)
next
  assume R: ?rhs 
  show ?lhs
    unfolding first_countable_neighbourhood_base_alt
  proof
    fix x
    assume "x \<in> topspace X"
    with R obtain \<B> where "countable \<B>" and \<B>: "neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X"
      by blast
    then
    show "\<exists>\<B>. countable \<B> \<and> Ball \<B> (openin X) \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X"
      unfolding neighbourhood_base_at_def
      apply (rule_tac x="(\<lambda>u. X interior_of u) ` \<B>" in exI)
      by (smt (verit, best) countable_image image_iff interior_of_eq interior_of_mono openin_interior_of)
  qed
qed


subsection\<open>$T_0$ spaces and the Kolmogorov quotient\<close>

definition t0_space where
  "t0_space X \<equiv>
     \<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<noteq> y \<longrightarrow> (\<exists>U. openin X U \<and> (x \<notin> U \<longleftrightarrow> y \<in> U))"

lemma t0_space_expansive:
   "\<lbrakk>topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk> \<Longrightarrow> t0_space X \<Longrightarrow> t0_space Y"
  by (metis t0_space_def)

lemma t1_imp_t0_space: "t1_space X \<Longrightarrow> t0_space X"
  by (metis t0_space_def t1_space_def)

lemma t1_eq_symmetric_t0_space_alt:
   "t1_space X \<longleftrightarrow>
      t0_space X \<and>
      (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<in> X closure_of {y} \<longleftrightarrow> y \<in> X closure_of {x})"
  apply (simp add: t0_space_def t1_space_def closure_of_def)
  by (smt (verit, best) openin_topspace)

lemma t1_eq_symmetric_t0_space:
  "t1_space X \<longleftrightarrow> t0_space X \<and> (\<forall>x y. x \<in> X closure_of {y} \<longleftrightarrow> y \<in> X closure_of {x})"
  by (auto simp: t1_eq_symmetric_t0_space_alt in_closure_of)

lemma Hausdorff_imp_t0_space:
   "Hausdorff_space X \<Longrightarrow> t0_space X"
  by (simp add: Hausdorff_imp_t1_space t1_imp_t0_space)

lemma t0_space:
   "t0_space X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<noteq> y \<longrightarrow> (\<exists>C. closedin X C \<and> (x \<notin> C \<longleftrightarrow> y \<in> C)))"
  unfolding t0_space_def by (metis Diff_iff closedin_def openin_closedin_eq)

lemma homeomorphic_t0_space:
  assumes "X homeomorphic_space Y"
  shows "t0_space X \<longleftrightarrow> t0_space Y"
proof -
  obtain f where f: "homeomorphic_map X Y f" and F: "inj_on f (topspace X)" and "topspace Y = f ` topspace X"
    by (metis assms homeomorphic_imp_injective_map homeomorphic_imp_surjective_map homeomorphic_space)
  with inj_on_image_mem_iff [OF F] 
  show ?thesis
    apply (simp add: t0_space_def homeomorphic_eq_everything_map continuous_map_def open_map_def inj_on_def)
    by (smt (verit)  mem_Collect_eq openin_subset)
qed

lemma t0_space_closure_of_sing:
   "t0_space X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. X closure_of {x} = X closure_of {y} \<longrightarrow> x = y)"
  by (simp add: t0_space_def closure_of_def set_eq_iff) (smt (verit))

lemma t0_space_discrete_topology: "t0_space (discrete_topology S)"
  by (simp add: Hausdorff_imp_t0_space)

lemma t0_space_subtopology: "t0_space X \<Longrightarrow> t0_space (subtopology X U)"
  by (simp add: t0_space_def openin_subtopology) (metis Int_iff)

lemma t0_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; t0_space X\<rbrakk> \<Longrightarrow> t0_space Y"
  using hereditary_imp_retractive_property homeomorphic_t0_space t0_space_subtopology by blast

lemma t0_space_prod_topologyI: "\<lbrakk>t0_space X; t0_space Y\<rbrakk> \<Longrightarrow> t0_space (prod_topology X Y)"
  by (simp add: t0_space_closure_of_sing closure_of_Times closure_of_eq_empty_gen times_eq_iff flip: sing_Times_sing insert_Times_insert)


lemma t0_space_prod_topology_iff:
   "t0_space (prod_topology X Y) \<longleftrightarrow> prod_topology X Y = trivial_topology \<or> t0_space X \<and> t0_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis prod_topology_trivial_iff retraction_map_fst retraction_map_snd t0_space_retraction_map_image)
qed (metis t0_space_discrete_topology t0_space_prod_topologyI)

proposition t0_space_product_topology:
   "t0_space (product_topology X I) \<longleftrightarrow> product_topology X I = trivial_topology \<or> (\<forall>i \<in> I. t0_space (X i))" 
    (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson retraction_map_product_projection t0_space_retraction_map_image)
next
  assume R: ?rhs 
  show ?lhs
  proof (cases "product_topology X I = trivial_topology")
    case True
    then show ?thesis
      by (simp add: t0_space_def)
  next
    case False
    show ?thesis
      unfolding t0_space
    proof (intro strip)
      fix x y
      assume x: "x \<in> topspace (product_topology X I)"
        and y: "y \<in> topspace (product_topology X I)"
        and "x \<noteq> y"
      then obtain i where "i \<in> I" "x i \<noteq> y i"
        by (metis PiE_ext topspace_product_topology)
      then have "t0_space (X i)"
        using False R by blast
      then obtain U where "closedin (X i) U" "(x i \<notin> U \<longleftrightarrow> y i \<in> U)"
        by (metis t0_space PiE_mem \<open>i \<in> I\<close> \<open>x i \<noteq> y i\<close> topspace_product_topology x y)
      with \<open>i \<in> I\<close> x y show "\<exists>U. closedin (product_topology X I) U \<and> (x \<notin> U) = (y \<in> U)"
        by (rule_tac x="PiE I (\<lambda>j. if j = i then U else topspace(X j))" in exI)
          (simp add: closedin_product_topology PiE_iff)
    qed
  qed
qed


subsection \<open>Kolmogorov quotients\<close>

definition Kolmogorov_quotient 
  where "Kolmogorov_quotient X \<equiv> \<lambda>x. @y. \<forall>U. openin X U \<longrightarrow> (y \<in> U \<longleftrightarrow> x \<in> U)"

lemma Kolmogorov_quotient_in_open:
   "openin X U \<Longrightarrow> (Kolmogorov_quotient X x \<in> U \<longleftrightarrow> x \<in> U)"
  by (smt (verit, ccfv_SIG) Kolmogorov_quotient_def someI_ex)

lemma Kolmogorov_quotient_in_topspace:
   "Kolmogorov_quotient X x \<in> topspace X \<longleftrightarrow> x \<in> topspace X"
  by (simp add: Kolmogorov_quotient_in_open)

lemma Kolmogorov_quotient_in_closed:
  "closedin X C \<Longrightarrow> (Kolmogorov_quotient X x \<in> C \<longleftrightarrow> x \<in> C)"
  unfolding closedin_def
  by (meson DiffD2 DiffI Kolmogorov_quotient_in_open Kolmogorov_quotient_in_topspace in_mono)
 
lemma continuous_map_Kolmogorov_quotient:
   "continuous_map X X (Kolmogorov_quotient X)"
  using Kolmogorov_quotient_in_open openin_subopen openin_subset 
    by (fastforce simp: continuous_map_def Kolmogorov_quotient_in_topspace)

lemma open_map_Kolmogorov_quotient_explicit:
   "openin X U \<Longrightarrow> Kolmogorov_quotient X ` U = Kolmogorov_quotient X ` topspace X \<inter> U"
  using Kolmogorov_quotient_in_open openin_subset by fastforce


lemma open_map_Kolmogorov_quotient_gen:
   "open_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
proof (clarsimp simp: open_map_def openin_subtopology_alt image_iff)
  fix U
  assume "openin X U"
  then have "Kolmogorov_quotient X ` (S \<inter> U) = Kolmogorov_quotient X ` S \<inter> U"
    using Kolmogorov_quotient_in_open [of X U] by auto
  then show "\<exists>V. openin X V \<and> Kolmogorov_quotient X ` (S \<inter> U) = Kolmogorov_quotient X ` S \<inter> V"
    using \<open>openin X U\<close> by blast
qed

lemma open_map_Kolmogorov_quotient:
   "open_map X (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
  by (metis open_map_Kolmogorov_quotient_gen subtopology_topspace)

lemma closed_map_Kolmogorov_quotient_explicit:
   "closedin X U \<Longrightarrow> Kolmogorov_quotient X ` U = Kolmogorov_quotient X ` topspace X \<inter> U"
  using closedin_subset by (fastforce simp: Kolmogorov_quotient_in_closed)

lemma closed_map_Kolmogorov_quotient_gen:
   "closed_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S))
     (Kolmogorov_quotient X)"
  using Kolmogorov_quotient_in_closed by (force simp: closed_map_def closedin_subtopology_alt image_iff)

lemma closed_map_Kolmogorov_quotient:
   "closed_map X (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
  by (metis closed_map_Kolmogorov_quotient_gen subtopology_topspace)

lemma quotient_map_Kolmogorov_quotient_gen:
  "quotient_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
proof (intro continuous_open_imp_quotient_map)
  show "continuous_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
    by (simp add: continuous_map_Kolmogorov_quotient continuous_map_from_subtopology continuous_map_in_subtopology image_mono)
  show "open_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
    using open_map_Kolmogorov_quotient_gen by blast
  show "Kolmogorov_quotient X ` topspace (subtopology X S) = topspace (subtopology X (Kolmogorov_quotient X ` S))"
    by (force simp: Kolmogorov_quotient_in_open)
qed

lemma quotient_map_Kolmogorov_quotient:
   "quotient_map X (subtopology X (Kolmogorov_quotient X ` topspace X)) (Kolmogorov_quotient X)"
  by (metis quotient_map_Kolmogorov_quotient_gen subtopology_topspace)

lemma Kolmogorov_quotient_eq:
   "Kolmogorov_quotient X x = Kolmogorov_quotient X y \<longleftrightarrow>
    (\<forall>U. openin X U \<longrightarrow> (x \<in> U \<longleftrightarrow> y \<in> U))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis Kolmogorov_quotient_in_open)
next
  assume ?rhs then show ?lhs
    by (simp add: Kolmogorov_quotient_def)
qed

lemma Kolmogorov_quotient_eq_alt:
   "Kolmogorov_quotient X x = Kolmogorov_quotient X y \<longleftrightarrow>
    (\<forall>U. closedin X U \<longrightarrow> (x \<in> U \<longleftrightarrow> y \<in> U))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis Kolmogorov_quotient_in_closed)
next
  assume ?rhs then show ?lhs
    by (smt (verit) Diff_iff Kolmogorov_quotient_eq closedin_topspace in_mono openin_closedin_eq)
qed

lemma Kolmogorov_quotient_continuous_map:
  assumes "continuous_map X Y f" "t0_space Y" and x: "x \<in> topspace X"
  shows "f (Kolmogorov_quotient X x) = f x"
  using assms unfolding continuous_map_def t0_space_def
  by (smt (verit, ccfv_threshold) Kolmogorov_quotient_in_open Kolmogorov_quotient_in_topspace PiE mem_Collect_eq)

lemma t0_space_Kolmogorov_quotient:
  "t0_space (subtopology X (Kolmogorov_quotient X ` topspace X))"
  apply (clarsimp simp: t0_space_def )
  by (smt (verit, best) Kolmogorov_quotient_eq imageE image_eqI open_map_Kolmogorov_quotient open_map_def)

lemma Kolmogorov_quotient_id:
   "t0_space X \<Longrightarrow> x \<in> topspace X \<Longrightarrow> Kolmogorov_quotient X x = x"
  by (metis Kolmogorov_quotient_in_open Kolmogorov_quotient_in_topspace t0_space_def)

lemma Kolmogorov_quotient_idemp:
   "Kolmogorov_quotient X (Kolmogorov_quotient X x) = Kolmogorov_quotient X x"
  by (simp add: Kolmogorov_quotient_eq Kolmogorov_quotient_in_open)

lemma retraction_maps_Kolmogorov_quotient:
   "retraction_maps X
     (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X) id"
  unfolding retraction_maps_def continuous_map_in_subtopology
  using Kolmogorov_quotient_idemp continuous_map_Kolmogorov_quotient by force

lemma retraction_map_Kolmogorov_quotient:
   "retraction_map X
     (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
  using retraction_map_def retraction_maps_Kolmogorov_quotient by blast

lemma retract_of_space_Kolmogorov_quotient_image:
   "Kolmogorov_quotient X ` topspace X retract_of_space X"
proof -
  have "continuous_map X X (Kolmogorov_quotient X)"
    by (simp add: continuous_map_Kolmogorov_quotient)
  then have "Kolmogorov_quotient X ` topspace X \<subseteq> topspace X"
    by (simp add: continuous_map_image_subset_topspace)
  then show ?thesis
    by (meson retract_of_space_retraction_maps retraction_maps_Kolmogorov_quotient)
qed

lemma Kolmogorov_quotient_lift_exists:
  assumes "S \<subseteq> topspace X" "t0_space Y" and f: "continuous_map (subtopology X S) Y f"
  obtains g where "continuous_map (subtopology X (Kolmogorov_quotient X ` S)) Y g"
              "\<And>x. x \<in> S \<Longrightarrow> g(Kolmogorov_quotient X x) = f x"
proof -
  have "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; Kolmogorov_quotient X x = Kolmogorov_quotient X y\<rbrakk> \<Longrightarrow> f x = f y"
    using assms
    apply (simp add: Kolmogorov_quotient_eq t0_space_def continuous_map_def Int_absorb1 openin_subtopology)
    by (smt (verit, del_insts) Int_iff mem_Collect_eq Pi_iff)
  then obtain g where g: "continuous_map (subtopology X (Kolmogorov_quotient X ` S)) Y g"
    "g ` (topspace X \<inter> Kolmogorov_quotient X ` S) = f ` S"
    "\<And>x. x \<in> S \<Longrightarrow> g (Kolmogorov_quotient X x) = f x"
    using quotient_map_lift_exists [OF quotient_map_Kolmogorov_quotient_gen [of X S] f]
    by (metis assms(1) topspace_subtopology topspace_subtopology_subset) 
  show ?thesis
    proof qed (use g in auto)
qed

subsection\<open>Closed diagonals and graphs\<close>

lemma Hausdorff_space_closedin_diagonal:
  "Hausdorff_space X \<longleftrightarrow> closedin (prod_topology X X) ((\<lambda>x. (x,x)) ` topspace X)"
proof -
  have \<section>: "((\<lambda>x. (x, x)) ` topspace X) \<subseteq> topspace X \<times> topspace X"
    by auto
  show ?thesis
    apply (simp add: closedin_def openin_prod_topology_alt Hausdorff_space_def disjnt_iff \<section>)
    apply (intro all_cong1 imp_cong ex_cong1 conj_cong refl)
    by (force dest!: openin_subset)+
qed

lemma closed_map_diag_eq:
   "closed_map X (prod_topology X X) (\<lambda>x. (x,x)) \<longleftrightarrow> Hausdorff_space X"
proof -
  have "section_map X (prod_topology X X) (\<lambda>x. (x, x))"
    unfolding section_map_def retraction_maps_def
    by (smt (verit) continuous_map_fst continuous_map_of_fst continuous_map_on_empty continuous_map_pairwise fst_conv fst_diag_fst snd_diag_fst)
  then have "embedding_map X (prod_topology X X) (\<lambda>x. (x, x))"
    by (rule section_imp_embedding_map)
  then show ?thesis
    using Hausdorff_space_closedin_diagonal embedding_imp_closed_map_eq by blast
qed

lemma proper_map_diag_eq [simp]:
   "proper_map X (prod_topology X X) (\<lambda>x. (x,x)) \<longleftrightarrow> Hausdorff_space X"
  by (simp add: closed_map_diag_eq inj_on_convol_ident injective_imp_proper_eq_closed_map)
  
lemma closedin_continuous_maps_eq:
  assumes "Hausdorff_space Y" and f: "continuous_map X Y f" and g: "continuous_map X Y g"
  shows "closedin X {x \<in> topspace X. f x = g x}"
proof -
  have \<section>:"{x \<in> topspace X. f x = g x} = {x \<in> topspace X. (f x,g x) \<in> ((\<lambda>y.(y,y)) ` topspace Y)}"
    using f continuous_map_image_subset_topspace by fastforce
  show ?thesis
    unfolding \<section>
  proof (intro closedin_continuous_map_preimage)
    show "continuous_map X (prod_topology Y Y) (\<lambda>x. (f x, g x))"
      by (simp add: continuous_map_pairedI f g)
    show "closedin (prod_topology Y Y) ((\<lambda>y. (y, y)) ` topspace Y)"
      using Hausdorff_space_closedin_diagonal assms by blast
  qed
qed

lemma forall_in_closure_of:
  assumes "x \<in> X closure_of S" "\<And>x. x \<in> S \<Longrightarrow> P x"
    and "closedin X {x \<in> topspace X. P x}"
  shows "P x"
  by (smt (verit, ccfv_threshold) Diff_iff assms closedin_def in_closure_of mem_Collect_eq)

lemma forall_in_closure_of_eq:
  assumes x: "x \<in> X closure_of S"
    and Y: "Hausdorff_space Y" 
    and f: "continuous_map X Y f" and g: "continuous_map X Y g"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "f x = g x"
proof -
  have "closedin X {x \<in> topspace X. f x = g x}"
    using Y closedin_continuous_maps_eq f g by blast
  then show ?thesis
    using forall_in_closure_of [OF x fg]
    by fastforce
qed
    
lemma retract_of_space_imp_closedin:
  assumes "Hausdorff_space X" and S: "S retract_of_space X"
  shows "closedin X S"
proof -
  obtain r where r: "continuous_map X (subtopology X S) r" "\<forall>x\<in>S. r x = x"
    using assms by (meson retract_of_space_def)
  then have \<section>: "S = {x \<in> topspace X. r x = x}"
    using S retract_of_space_imp_subset by (force simp: continuous_map_def Pi_iff)
  show ?thesis
    unfolding \<section> 
    using r continuous_map_into_fulltopology assms
    by (force intro: closedin_continuous_maps_eq)
qed

lemma homeomorphic_maps_graph:
   "homeomorphic_maps X (subtopology (prod_topology X Y) ((\<lambda>x. (x, f x)) ` (topspace X)))
         (\<lambda>x. (x, f x)) fst  \<longleftrightarrow>  continuous_map X Y f" 
   (is "?lhs=?rhs")
proof
  assume ?lhs
  then 
  have h: "homeomorphic_map X (subtopology (prod_topology X Y) ((\<lambda>x. (x, f x)) ` topspace X)) (\<lambda>x. (x, f x))"
    by (auto simp: homeomorphic_maps_map)
  have "f = snd \<circ> (\<lambda>x. (x, f x))"
    by force
  then show ?rhs
    by (metis (no_types, lifting) h continuous_map_in_subtopology continuous_map_snd_of homeomorphic_eq_everything_map)
next
  assume ?rhs
  then show ?lhs
    unfolding homeomorphic_maps_def
    by (smt (verit, del_insts) continuous_map_eq continuous_map_subtopology_fst embedding_map_def 
        embedding_map_graph homeomorphic_eq_everything_map image_cong image_iff prod.sel(1))
qed


subsection \<open> KC spaces, those where all compact sets are closed.\<close>

definition kc_space 
  where "kc_space X \<equiv> \<forall>S. compactin X S \<longrightarrow> closedin X S"

lemma kc_space_euclidean: "kc_space (euclidean :: 'a::metric_space topology)"
  by (simp add: compact_imp_closed kc_space_def)
  
lemma kc_space_expansive:
   "\<lbrakk>kc_space X; topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk>
      \<Longrightarrow> kc_space Y"
  by (meson compactin_contractive kc_space_def topology_finer_closedin)

lemma compactin_imp_closedin_gen:
   "\<lbrakk>kc_space X; compactin X S\<rbrakk> \<Longrightarrow> closedin X S"
  using kc_space_def by blast

lemma Hausdorff_imp_kc_space: "Hausdorff_space X \<Longrightarrow> kc_space X"
  by (simp add: compactin_imp_closedin kc_space_def)

lemma kc_imp_t1_space: "kc_space X \<Longrightarrow> t1_space X"
  by (simp add: finite_imp_compactin kc_space_def t1_space_closedin_finite)

lemma kc_space_subtopology:
   "kc_space X \<Longrightarrow> kc_space(subtopology X S)"
  by (metis closedin_Int_closure_of closure_of_eq compactin_subtopology inf.absorb2 kc_space_def)

lemma kc_space_discrete_topology:
   "kc_space(discrete_topology U)"
  using Hausdorff_space_discrete_topology compactin_imp_closedin kc_space_def by blast

lemma kc_space_continuous_injective_map_preimage:
  assumes "kc_space Y" "continuous_map X Y f" and injf: "inj_on f (topspace X)"
  shows "kc_space X"
  unfolding kc_space_def
proof (intro strip)
  fix S
  assume S: "compactin X S"
  have "S = {x \<in> topspace X. f x \<in> f ` S}"
    using S compactin_subset_topspace inj_onD [OF injf] by blast
  with assms S show "closedin X S"
    by (metis (no_types, lifting) Collect_cong closedin_continuous_map_preimage compactin_imp_closedin_gen image_compactin)
qed

lemma kc_space_retraction_map_image:
  assumes "retraction_map X Y r" "kc_space X"
  shows "kc_space Y"
proof -
  obtain s where s: "continuous_map X Y r" "continuous_map Y X s" "\<And>x. x \<in> topspace Y \<Longrightarrow> r (s x) = x"
    using assms by (force simp: retraction_map_def retraction_maps_def)
  then have inj: "inj_on s (topspace Y)"
    by (metis inj_on_def)
  show ?thesis
    unfolding kc_space_def
  proof (intro strip)
    fix S
    assume S: "compactin Y S"
    have "S = {x \<in> topspace Y. s x \<in> s ` S}"
      using S compactin_subset_topspace inj_onD [OF inj] by blast
    with assms S show "closedin Y S"
      by (meson compactin_imp_closedin_gen inj kc_space_continuous_injective_map_preimage s(2))
  qed
qed

lemma homeomorphic_kc_space:
   "X homeomorphic_space Y \<Longrightarrow> kc_space X \<longleftrightarrow> kc_space Y"
  by (meson homeomorphic_eq_everything_map homeomorphic_space homeomorphic_space_sym kc_space_continuous_injective_map_preimage)

lemma compact_kc_eq_maximal_compact_space:
  assumes "compact_space X"
  shows "kc_space X \<longleftrightarrow>
         (\<forall>Y. topspace Y = topspace X \<and> (\<forall>S. openin X S \<longrightarrow> openin Y S) \<and> compact_space Y \<longrightarrow> Y = X)" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis closedin_compact_space compactin_contractive kc_space_def topology_eq topology_finer_closedin)    
next
  assume R: ?rhs
  show ?lhs
    unfolding kc_space_def
  proof (intro strip)
    fix S
    assume S: "compactin X S"
    define Y where 
      "Y \<equiv> topology (arbitrary union_of (finite intersection_of (\<lambda>A. A = topspace X - S \<or> openin X A)
                           relative_to (topspace X)))"
    have "topspace Y = topspace X"
      by (auto simp: Y_def)
    have "openin X T \<longrightarrow> openin Y T" for T
      by (simp add: Y_def arbitrary_union_of_inc finite_intersection_of_inc openin_subbase openin_subset relative_to_subset_inc)
    have "compact_space Y"
    proof (rule Alexander_subbase_alt)
      show "\<exists>\<F>'. finite \<F>' \<and> \<F>' \<subseteq> \<C> \<and> topspace X \<subseteq> \<Union> \<F>'" 
        if \<C>: "\<C> \<subseteq> insert (topspace X - S) (Collect (openin X))" and sub: "topspace X \<subseteq> \<Union>\<C>" for \<C>
      proof -
        consider "\<C> \<subseteq> Collect (openin X)" | \<V> where "\<C> = insert (topspace X - S) \<V>" "\<V> \<subseteq> Collect (openin X)"
          using \<C> by (metis insert_Diff subset_insert_iff)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis
            by (metis assms compact_space_alt mem_Collect_eq subsetD that(2))
        next
          case 2
          then have "S \<subseteq> \<Union>\<V>"
            using S sub compactin_subset_topspace by blast
          with 2 obtain \<F> where "finite \<F> \<and> \<F> \<subseteq> \<V> \<and> S \<subseteq> \<Union>\<F>"
            using S unfolding compactin_def by (metis Ball_Collect)
          with 2 show ?thesis
            by (rule_tac x="insert (topspace X - S) \<F>" in exI) blast
        qed
      qed
    qed (auto simp: Y_def)
    have "Y = X"
      using R \<open>\<And>S. openin X S \<longrightarrow> openin Y S\<close> \<open>compact_space Y\<close> \<open>topspace Y = topspace X\<close> by blast
    moreover have "openin Y (topspace X - S)"
      by (simp add: Y_def arbitrary_union_of_inc finite_intersection_of_inc openin_subbase relative_to_subset_inc)
    ultimately show "closedin X S"
      unfolding closedin_def using S compactin_subset_topspace by blast
  qed
qed

lemma continuous_imp_closed_map_gen:
   "\<lbrakk>compact_space X; kc_space Y; continuous_map X Y f\<rbrakk> \<Longrightarrow> closed_map X Y f"
  by (meson closed_map_def closedin_compact_space compactin_imp_closedin_gen image_compactin)

lemma kc_space_compact_subtopologies:
  "kc_space X \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> kc_space(subtopology X K))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: kc_space_def closedin_closed_subtopology compactin_subtopology)
next
  assume R: ?rhs
  show ?lhs
    unfolding kc_space_def
  proof (intro strip)
    fix K
    assume K: "compactin X K"
    then have "K \<subseteq> topspace X"
      by (simp add: compactin_subset_topspace)
    moreover have "X closure_of K \<subseteq> K"
    proof
      fix x
      assume x: "x \<in> X closure_of K"
      have "kc_space (subtopology X K)"
        by (simp add: R \<open>compactin X K\<close>)
      have "compactin X (insert x K)"
        by (metis K x compactin_Un compactin_sing in_closure_of insert_is_Un)
      then show "x \<in> K"
        by (metis R x K Int_insert_left_if1 closedin_Int_closure_of compact_imp_compactin_subtopology 
            insertCI kc_space_def subset_insertI)
    qed
    ultimately show "closedin X K"
      using closure_of_subset_eq by blast
  qed
qed

lemma kc_space_compact_prod_topology:
  assumes "compact_space X"
  shows "kc_space(prod_topology X X) \<longleftrightarrow> Hausdorff_space X" (is "?lhs=?rhs")
proof
  assume L: ?lhs
  show ?rhs
    unfolding closed_map_diag_eq [symmetric]
  proof (intro continuous_imp_closed_map_gen)
    show "continuous_map X (prod_topology X X) (\<lambda>x. (x, x))"
      by (intro continuous_intros)
  qed (use L assms in auto)
next
  assume ?rhs then show ?lhs
    by (simp add: Hausdorff_imp_kc_space Hausdorff_space_prod_topology)
qed

lemma kc_space_prod_topology:
   "kc_space(prod_topology X X) \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> Hausdorff_space(subtopology X K))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis compactin_subspace kc_space_compact_prod_topology kc_space_subtopology subtopology_Times)
next
  assume R: ?rhs  
  have "kc_space (subtopology (prod_topology X X) L)" if "compactin (prod_topology X X) L" for L 
  proof -
    define K where "K \<equiv> fst ` L \<union> snd ` L"
    have "L \<subseteq> K \<times> K"
      by (force simp: K_def)
    have "compactin X K"
      by (metis K_def compactin_Un continuous_map_fst continuous_map_snd image_compactin that)
    then have "Hausdorff_space (subtopology X K)"
      by (simp add: R)
    then have "kc_space (prod_topology (subtopology X K) (subtopology X K))"
      by (simp add: \<open>compactin X K\<close> compact_space_subtopology kc_space_compact_prod_topology)
    then have "kc_space (subtopology (prod_topology (subtopology X K) (subtopology X K)) L)"
      using kc_space_subtopology by blast
    then show ?thesis
      using \<open>L \<subseteq> K \<times> K\<close> subtopology_Times subtopology_subtopology
      by (metis (no_types, lifting) Sigma_cong inf.absorb_iff2)
  qed
  then show ?lhs
    using kc_space_compact_subtopologies by blast
qed

lemma kc_space_prod_topology_alt:
   "kc_space(prod_topology X X) \<longleftrightarrow>
        kc_space X \<and>
        (\<forall>K. compactin X K \<longrightarrow> Hausdorff_space(subtopology X K))"
  using Hausdorff_imp_kc_space kc_space_compact_subtopologies kc_space_prod_topology by blast

proposition kc_space_prod_topology_left:
  assumes X: "kc_space X" and Y: "Hausdorff_space Y"
  shows "kc_space (prod_topology X Y)"
  unfolding kc_space_def
proof (intro strip)
  fix K
  assume K: "compactin (prod_topology X Y) K"
  then have "K \<subseteq> topspace X \<times> topspace Y"
    using compactin_subset_topspace topspace_prod_topology by blast
  moreover have "\<exists>T. openin (prod_topology X Y) T \<and> (a,b) \<in> T \<and> T \<subseteq> (topspace X \<times> topspace Y) - K"
    if ab: "(a,b) \<in> (topspace X \<times> topspace Y) - K" for a b
  proof - 
    have "compactin Y {b}"
      using that by force
    moreover 
    have "compactin Y {y \<in> topspace Y. (a,y) \<in> K}"
    proof -
      have "compactin (prod_topology X Y) (K \<inter> {a} \<times> topspace Y)"
        using that compact_Int_closedin [OF K]
        by (simp add: X closedin_prod_Times_iff compactin_imp_closedin_gen)
      moreover have "subtopology (prod_topology X Y) (K \<inter> {a} \<times> topspace Y)  homeomorphic_space 
                     subtopology Y {y \<in> topspace Y. (a, y) \<in> K}"
        unfolding homeomorphic_space_def homeomorphic_maps_def
        using that
        apply (rule_tac x="snd" in exI)
        apply (rule_tac x="Pair a" in exI)
        by (force simp: continuous_map_in_subtopology continuous_map_from_subtopology continuous_map_subtopology_snd continuous_map_paired)
      ultimately show ?thesis
        by (simp add: compactin_subspace homeomorphic_compact_space) 
    qed
    moreover have "disjnt {b} {y \<in> topspace Y. (a,y) \<in> K}"
      using ab by force
    ultimately obtain V U where VU: "openin Y V" "openin Y U" "{b} \<subseteq> V" "{y \<in> topspace Y. (a,y) \<in> K} \<subseteq> U" "disjnt V U"
      using Hausdorff_space_compact_separation [OF Y] by blast
    define V' where "V' \<equiv> topspace Y - U"
    have W: "closedin Y V'" "{y \<in> topspace Y. (a,y) \<in> K} \<subseteq> topspace Y - V'" "disjnt V (topspace Y - V')"
      using VU by (auto simp: V'_def disjnt_iff)
    with VU obtain "V \<subseteq> topspace Y" "V' \<subseteq> topspace Y"
      by (meson closedin_subset openin_closedin_eq)
    then obtain "b \<in> V" "disjnt {y \<in> topspace Y. (a,y) \<in> K} V'" "V \<subseteq> V'"
      using VU unfolding disjnt_iff V'_def by force
    define C where "C \<equiv> image fst (K \<inter> {z \<in> topspace(prod_topology X Y). snd z \<in> V'})"
    have "closedin (prod_topology X Y) {z \<in> topspace (prod_topology X Y). snd z \<in> V'}"
        using closedin_continuous_map_preimage \<open>closedin Y V'\<close> continuous_map_snd by blast
    then have "compactin X C"
      unfolding C_def by (meson K compact_Int_closedin continuous_map_fst image_compactin)
    then have "closedin X C"
      using assms by (auto simp: kc_space_def)
    show ?thesis
    proof (intro exI conjI)
      show "openin (prod_topology X Y) ((topspace X - C) \<times> V)"
        by (simp add: VU \<open>closedin X C\<close> openin_diff openin_prod_Times_iff)
      have "a \<notin> C"
        using VU by (auto simp: C_def V'_def)
      then show "(a, b) \<in> (topspace X - C) \<times> V"
        using \<open>a \<notin> C\<close> \<open>b \<in> V\<close> that by blast
      show "(topspace X - C) \<times> V \<subseteq> topspace X \<times> topspace Y - K"
        using \<open>V \<subseteq> V'\<close> \<open>V \<subseteq> topspace Y\<close> 
        apply (simp add: C_def )
        by (smt (verit, ccfv_threshold) DiffE DiffI IntI SigmaE SigmaI image_eqI mem_Collect_eq prod.sel(1) snd_conv subset_iff)
    qed
  qed
  ultimately show "closedin (prod_topology X Y) K"
    by (metis surj_pair closedin_def openin_subopen topspace_prod_topology)
qed

lemma kc_space_prod_topology_right:
   "\<lbrakk>Hausdorff_space X; kc_space Y\<rbrakk> \<Longrightarrow> kc_space (prod_topology X Y)"
  using kc_space_prod_topology_left homeomorphic_kc_space homeomorphic_space_prod_topology_swap by blast

subsection \<open>Technical results about proper maps, perfect maps, etc\<close>

lemma compact_imp_proper_map_gen:
  assumes Y: "\<And>S. \<lbrakk>S \<subseteq> topspace Y; \<And>K. compactin Y K \<Longrightarrow> compactin Y (S \<inter> K)\<rbrakk>
               \<Longrightarrow> closedin Y S"
    and fim: "f ` (topspace X) \<subseteq> topspace Y"
    and f: "continuous_map X Y f \<or> kc_space X"
    and YX: "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
  shows "proper_map X Y f"
  unfolding proper_map_alt closed_map_def
proof (intro conjI strip)
  fix C
  assume C: "closedin X C"
  show "closedin Y (f ` C)"
  proof (intro Y)
    show "f ` C \<subseteq> topspace Y"
      using C closedin_subset fim by blast
    fix K
    assume K: "compactin Y K"
    define A where "A \<equiv> {x \<in> topspace X. f x \<in> K}"
    have eq: "f ` C \<inter> K = f ` ({x \<in> topspace X. f x \<in> K} \<inter> C)"
      using C closedin_subset by auto
    show "compactin Y (f ` C \<inter> K)"
      unfolding eq
    proof (rule image_compactin)
      show "compactin (subtopology X A) ({x \<in> topspace X. f x \<in> K} \<inter> C)"
      proof (rule closedin_compact_space)
        show "compact_space (subtopology X A)"
          by (simp add: A_def K YX compact_space_subtopology)
        show "closedin (subtopology X A) ({x \<in> topspace X. f x \<in> K} \<inter> C)"
          using A_def C closedin_subtopology by blast
      qed
      have "continuous_map (subtopology X A) (subtopology Y K) f" if "kc_space X"
        unfolding continuous_map_closedin
      proof (intro conjI strip)
        show "f \<in> topspace (subtopology X A) \<rightarrow> topspace (subtopology Y K)"
          using A_def K compactin_subset_topspace by fastforce
      next
        fix C
        assume C: "closedin (subtopology Y K) C"
        show "closedin (subtopology X A) {x \<in> topspace (subtopology X A). f x \<in> C}"
        proof (rule compactin_imp_closedin_gen)
          show "kc_space (subtopology X A)"
            by (simp add: kc_space_subtopology that)
          have [simp]: "{x \<in> topspace X. f x \<in> K \<and> f x \<in> C} = {x \<in> topspace X. f x \<in> C}"
            using C closedin_imp_subset by auto
          have "compactin (subtopology Y K) C"
            by (simp add: C K closedin_compact_space compact_space_subtopology)
          then have "compactin X {x \<in> topspace X. x \<in> A \<and> f x \<in> C}"
            by (auto simp: A_def compactin_subtopology dest: YX)
          then show "compactin (subtopology X A) {x \<in> topspace (subtopology X A). f x \<in> C}"
            by (auto simp add: compactin_subtopology)
        qed
      qed
      with f show "continuous_map (subtopology X A) Y f"
        using continuous_map_from_subtopology continuous_map_in_subtopology by blast
    qed
  qed
qed (simp add: YX)

lemma tube_lemma_left:
  assumes W: "openin (prod_topology X Y) W" and C: "compactin X C" 
    and y: "y \<in> topspace Y" and subW: "C \<times> {y} \<subseteq> W"
  shows "\<exists>U V. openin X U \<and> openin Y V \<and> C \<subseteq> U \<and> y \<in> V \<and> U \<times> V \<subseteq> W"
proof (cases "C = {}")
  case True
  with y show ?thesis by auto
next
  case False
  have "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> W" 
    if "x \<in> C" for x
    using W openin_prod_topology_alt subW subsetD that by fastforce
  then obtain U V where UV: "\<And>x. x \<in> C \<Longrightarrow> openin X (U x) \<and> openin Y (V x) \<and> x \<in> U x \<and> y \<in> V x \<and> U x \<times> V x \<subseteq> W" 
    by metis
  then obtain D where D: "finite D" "D \<subseteq> C" "C \<subseteq> \<Union> (U ` D)"
    using compactinD [OF C, of "U`C"]
    by (smt (verit) UN_I finite_subset_image imageE subsetI)
  show ?thesis
  proof (intro exI conjI)
    show "openin X (\<Union> (U ` D))" "openin Y (\<Inter> (V ` D))"
      using D False UV by blast+
    show "y \<in> \<Inter> (V ` D)" "C \<subseteq> \<Union> (U ` D)" "\<Union>(U ` D) \<times> \<Inter>(V ` D) \<subseteq> W"
      using D UV by force+
  qed
qed

lemma Wallace_theorem_prod_topology:
  assumes "compactin X K" "compactin Y L" 
    and W: "openin (prod_topology X Y) W" and subW: "K \<times> L \<subseteq> W"
  obtains U V where "openin X U" "openin Y V" "K \<subseteq> U" "L \<subseteq> V" "U \<times> V \<subseteq> W"
proof -
  have "\<And>y. y \<in> L \<Longrightarrow> \<exists>U V. openin X U \<and> openin Y V \<and> K \<subseteq> U \<and> y \<in> V \<and> U \<times> V \<subseteq> W"
  proof (intro tube_lemma_left assms)
    fix y assume "y \<in> L"
    show "y \<in> topspace Y"
      using assms \<open>y \<in> L\<close> compactin_subset_topspace by blast 
    show "K \<times> {y} \<subseteq> W"
      using \<open>y \<in> L\<close> subW by force
  qed
  then obtain U V where UV: 
         "\<And>y. y \<in> L \<Longrightarrow> openin X (U y) \<and> openin Y (V y) \<and> K \<subseteq> U y \<and> y \<in> V y \<and> U y \<times> V y \<subseteq> W"
    by metis
  then obtain M where "finite M" "M \<subseteq> L" and M: "L \<subseteq> \<Union> (V ` M)"
    using \<open>compactin Y L\<close> unfolding compactin_def
    by (smt (verit) UN_iff finite_subset_image imageE subset_iff)
  show thesis
  proof (cases "M={}")
    case True
    with M have "L={}"
      by blast
    then show ?thesis
      using \<open>compactin X K\<close> compactin_subset_topspace that by fastforce
  next
    case False
    show ?thesis
    proof
      show "openin X (\<Inter>(U`M))"
        using False UV \<open>M \<subseteq> L\<close> \<open>finite M\<close> by blast
      show "openin Y (\<Union>(V`M))"
        using UV \<open>M \<subseteq> L\<close> by blast
      show "K \<subseteq> \<Inter>(U`M)"
        by (meson INF_greatest UV \<open>M \<subseteq> L\<close> subsetD)
      show "L \<subseteq> \<Union>(V`M)"
        by (simp add: M)
      show "\<Inter>(U`M) \<times> \<Union>(V`M) \<subseteq> W"
        using UV \<open>M \<subseteq> L\<close> by fastforce
    qed   
  qed
qed

lemma proper_map_prod:
   "proper_map (prod_topology X Y) (prod_topology X' Y') (\<lambda>(x,y). (f x, g y)) \<longleftrightarrow>
    (prod_topology X Y) = trivial_topology \<or> proper_map X X' f \<and> proper_map Y Y' g"
   (is "?lhs \<longleftrightarrow> _ \<or> ?rhs")
proof (cases "(prod_topology X Y) = trivial_topology")
  case True then show ?thesis by auto
next
  case False
  then have ne: "topspace X \<noteq> {}" "topspace Y \<noteq> {}"
    by auto
  define h where "h \<equiv> \<lambda>(x,y). (f x, g y)"
  have "proper_map X X' f" "proper_map Y Y' g" if ?lhs
  proof -
    have cm: "closed_map X X' f" "closed_map Y Y' g"
      using that False closed_map_prod proper_imp_closed_map by blast+
    show "proper_map X X' f"
    proof (clarsimp simp add: proper_map_def cm)
      fix y
      assume y: "y \<in> topspace X'"
      obtain z where z: "z \<in> topspace Y"
        using ne by blast
      then have eq: "{x \<in> topspace X. f x = y} =
                     fst ` {u \<in> topspace X \<times> topspace Y. h u = (y,g z)}"
        by (force simp: h_def)
      show "compactin X {x \<in> topspace X. f x = y}"
        unfolding eq
      proof (intro image_compactin)
        have "g z \<in> topspace Y'"
          by (meson closed_map_def closedin_subset closedin_topspace cm image_subset_iff z)
        with y show "compactin (prod_topology X Y) {u \<in> topspace X \<times> topspace Y. (h u) = (y, g z)}"
          using that by (simp add: h_def proper_map_def)
        show "continuous_map (prod_topology X Y) X fst"
          by (simp add: continuous_map_fst)
      qed
    qed
    show "proper_map Y Y' g"
    proof (clarsimp simp add: proper_map_def cm)
      fix y
      assume y: "y \<in> topspace Y'"
      obtain z where z: "z \<in> topspace X"
        using ne by blast
      then have eq: "{x \<in> topspace Y. g x = y} =
                     snd ` {u \<in> topspace X \<times> topspace Y. h u = (f z,y)}"
        by (force simp: h_def)
      show "compactin Y {x \<in> topspace Y. g x = y}"
        unfolding eq
      proof (intro image_compactin)
        have "f z \<in> topspace X'"
          by (meson closed_map_def closedin_subset closedin_topspace cm image_subset_iff z)
        with y show "compactin (prod_topology X Y) {u \<in> topspace X \<times> topspace Y. (h u) = (f z, y)}"
          using that by (simp add: proper_map_def h_def)
        show "continuous_map (prod_topology X Y) Y snd"
          by (simp add: continuous_map_snd)
      qed
    qed
  qed
  moreover
  { assume R: ?rhs
    then have fgim: "f \<in> topspace X \<rightarrow> topspace X'" "g \<in> topspace Y \<rightarrow> topspace Y'" 
          and cm: "closed_map X X' f" "closed_map Y Y' g"
      by (auto simp: proper_map_def closed_map_imp_subset_topspace)
    have "closed_map (prod_topology X Y) (prod_topology X' Y') h"
      unfolding closed_map_fibre_neighbourhood imp_conjL
    proof (intro conjI strip)
      show "h \<in> topspace (prod_topology X Y) \<rightarrow> topspace (prod_topology X' Y')"
        unfolding h_def using fgim by auto
      fix W w
      assume W: "openin (prod_topology X Y) W"
        and w: "w \<in> topspace (prod_topology X' Y')"
        and subW: "{x \<in> topspace (prod_topology X Y). h x = w} \<subseteq> W"
      then obtain x' y' where weq: "w = (x',y')" "x' \<in> topspace X'" "y' \<in> topspace Y'"
        by auto
      have eq: "{u \<in> topspace X \<times> topspace Y. h u = (x',y')} = {x \<in> topspace X. f x = x'} \<times> {y \<in> topspace Y. g y = y'}"
        by (auto simp: h_def)
      obtain U V where "openin X U" "openin Y V" "U \<times> V \<subseteq> W"
        and U: "{x \<in> topspace X. f x = x'} \<subseteq> U" 
        and V: "{x \<in> topspace Y. g x = y'} \<subseteq> V" 
      proof (rule Wallace_theorem_prod_topology)
        show "compactin X {x \<in> topspace X. f x = x'}" "compactin Y {x \<in> topspace Y. g x = y'}"
          using R weq unfolding proper_map_def closed_map_fibre_neighbourhood by fastforce+
        show "{x \<in> topspace X. f x = x'} \<times> {x \<in> topspace Y. g x = y'} \<subseteq> W"
          using weq subW by (auto simp: h_def)
      qed (use W in auto)
      obtain U' where "openin X' U'" "x' \<in> U'" and U': "{x \<in> topspace X. f x \<in> U'} \<subseteq> U"
        using cm U \<open>openin X U\<close> weq unfolding closed_map_fibre_neighbourhood by meson
      obtain V' where "openin Y' V'" "y' \<in> V'" and V': "{x \<in> topspace Y. g x \<in> V'} \<subseteq> V"
        using cm V \<open>openin Y V\<close> weq unfolding closed_map_fibre_neighbourhood by meson
      show "\<exists>V. openin (prod_topology X' Y') V \<and> w \<in> V \<and> {x \<in> topspace (prod_topology X Y). h x \<in> V} \<subseteq> W"
      proof (intro conjI exI)
        show "openin (prod_topology X' Y') (U' \<times> V')"
          by (simp add: \<open>openin X' U'\<close> \<open>openin Y' V'\<close> openin_prod_Times_iff)
        show "w \<in> U' \<times> V'"
          using \<open>x' \<in> U'\<close> \<open>y' \<in> V'\<close> weq by blast
        show "{x \<in> topspace (prod_topology X Y). h x \<in> U' \<times> V'} \<subseteq> W"
          using \<open>U \<times> V \<subseteq> W\<close> U' V' h_def by auto
      qed
    qed
    moreover
    have "compactin (prod_topology X Y) {u \<in> topspace X \<times> topspace Y. h u = (w, z)}"
      if "w \<in> topspace X'" and "z \<in> topspace Y'" for w z
    proof -
      have eq: "{u \<in> topspace X \<times> topspace Y. h u = (w,z)} =
                {u \<in> topspace X. f u = w} \<times> {y. y \<in> topspace Y \<and> g y = z}"
        by (auto simp: h_def)
      show ?thesis
        using R that by (simp add: eq compactin_Times proper_map_def)
    qed
    ultimately have ?lhs
      by (auto simp: h_def proper_map_def) 
  }
  ultimately show ?thesis using False by metis
qed

lemma proper_map_paired:
  assumes "Hausdorff_space X \<and> proper_map X Y f \<and> proper_map X Z g \<or>
        Hausdorff_space Y \<and> continuous_map X Y f \<and> proper_map X Z g \<or>
        Hausdorff_space Z \<and> proper_map X Y f \<and> continuous_map X Z g"
  shows "proper_map X (prod_topology Y Z) (\<lambda>x. (f x,g x))"
  using assms
proof (elim disjE conjE)
  assume \<section>: "Hausdorff_space X" "proper_map X Y f" "proper_map X Z g"
  have eq: "(\<lambda>x. (f x, g x)) = (\<lambda>(x, y). (f x, g y)) \<circ> (\<lambda>x. (x, x))"
    by auto
  show "proper_map X (prod_topology Y Z) (\<lambda>x. (f x, g x))"
    unfolding eq
  proof (rule proper_map_compose)
    show "proper_map X (prod_topology X X) (\<lambda>x. (x,x))"
      by (simp add: \<section>)
    show "proper_map (prod_topology X X) (prod_topology Y Z) (\<lambda>(x,y). (f x, g y))"
      by (simp add: \<section> proper_map_prod)
  qed
next
  assume \<section>: "Hausdorff_space Y" "continuous_map X Y f" "proper_map X Z g"
  have eq: "(\<lambda>x. (f x, g x)) = (\<lambda>(x,y). (x,g y)) \<circ> (\<lambda>x. (f x,x))"
    by auto
  show "proper_map X (prod_topology Y Z) (\<lambda>x. (f x, g x))"
    unfolding eq
  proof (rule proper_map_compose)
    show "proper_map X (prod_topology Y X) (\<lambda>x. (f x,x))"
      by (simp add: \<section> proper_map_paired_continuous_map_left)
    show "proper_map (prod_topology Y X) (prod_topology Y Z) (\<lambda>(x,y). (x,g y))"
      by (simp add: \<section> proper_map_prod proper_map_id [unfolded id_def])
  qed
next
  assume \<section>: "Hausdorff_space Z" "proper_map X Y f" "continuous_map X Z g"
  have eq: "(\<lambda>x. (f x, g x)) = (\<lambda>(x,y). (f x,y)) \<circ> (\<lambda>x. (x,g x))"
    by auto
  show "proper_map X (prod_topology Y Z) (\<lambda>x. (f x, g x))"
    unfolding eq
  proof (rule proper_map_compose)
    show "proper_map X (prod_topology X Z) (\<lambda>x. (x, g x))"
      using \<section> proper_map_paired_continuous_map_right by auto
    show "proper_map (prod_topology X Z) (prod_topology Y Z) (\<lambda>(x,y). (f x,y))"
      by (simp add: \<section> proper_map_prod proper_map_id [unfolded id_def])
  qed
qed

lemma proper_map_pairwise:
  assumes
    "Hausdorff_space X \<and> proper_map X Y (fst \<circ> f) \<and> proper_map X Z (snd \<circ> f) \<or>
     Hausdorff_space Y \<and> continuous_map X Y (fst \<circ> f) \<and> proper_map X Z (snd \<circ> f) \<or>
     Hausdorff_space Z \<and> proper_map X Y (fst \<circ> f) \<and> continuous_map X Z (snd \<circ> f)"
  shows "proper_map X (prod_topology Y Z) f"
  using proper_map_paired [OF assms] by (simp add: o_def)

lemma proper_map_from_composition_right:
  assumes "Hausdorff_space Y" "proper_map X Z (g \<circ> f)" and contf: "continuous_map X Y f"
    and contg: "continuous_map Y Z g"
  shows "proper_map X Y f"
proof -
  define YZ where "YZ \<equiv> subtopology (prod_topology Y Z) ((\<lambda>x. (x, g x)) ` topspace Y)"
  have "proper_map X Y (fst \<circ> (\<lambda>x. (f x, (g \<circ> f) x)))"
  proof (rule proper_map_compose)
    have [simp]: "x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y" for x
      using contf continuous_map_preimage_topspace by auto
    show "proper_map X YZ (\<lambda>x. (f x, (g \<circ> f) x))"
      unfolding YZ_def
      using assms
      by (force intro!: proper_map_into_subtopology proper_map_paired simp: o_def image_iff)+
    show "proper_map YZ Y fst"
      using contg 
      by (simp flip: homeomorphic_maps_graph add: YZ_def homeomorphic_maps_map homeomorphic_imp_proper_map)
  qed
  moreover have "fst \<circ> (\<lambda>x. (f x, (g \<circ> f) x)) = f"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma perfect_map_from_composition_right:
   "\<lbrakk>Hausdorff_space Y; perfect_map X Z (g \<circ> f);
     continuous_map X Y f; continuous_map Y Z g; f ` topspace X = topspace Y\<rbrakk>
    \<Longrightarrow> perfect_map X Y f"
  by (meson perfect_map_def proper_map_from_composition_right)

lemma perfect_map_from_composition_right_inj:
   "\<lbrakk>perfect_map X Z (g \<circ> f); f ` topspace X = topspace Y;
     continuous_map X Y f; continuous_map Y Z g; inj_on g (topspace Y)\<rbrakk>
    \<Longrightarrow> perfect_map X Y f"
  by (meson continuous_map_openin_preimage_eq perfect_map_def proper_map_from_composition_right_inj)


subsection \<open>Regular spaces\<close>

text \<open>Regular spaces are *not* a priori assumed to be Hausdorff or $T_1$\<close>

definition regular_space 
  where "regular_space X \<equiv>
        \<forall>C a. closedin X C \<and> a \<in> topspace X - C
                \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V)"

lemma homeomorphic_regular_space_aux:
  assumes hom: "X homeomorphic_space Y" and X: "regular_space X"
  shows "regular_space Y"
proof -
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms X homeomorphic_maps_map homeomorphic_space_def by fastforce
  show ?thesis
    unfolding regular_space_def
  proof clarify
    fix C a
    assume Y: "closedin Y C" "a \<in> topspace Y" and "a \<notin> C"
    then obtain "closedin X (g ` C)" "g a \<in> topspace X" "g a \<notin> g ` C"
      using \<open>closedin Y C\<close> hmg homeomorphic_map_closedness_eq
      by (smt (verit, ccfv_SIG) fg homeomorphic_imp_surjective_map image_iff in_mono) 
    then obtain S T where ST: "openin X S" "openin X T" "g a \<in> S" "g`C \<subseteq> T" "disjnt S T"
      using X unfolding regular_space_def by (metis DiffI)
    then have "openin Y (f`S)" "openin Y (f`T)"
      by (meson hmf homeomorphic_map_openness_eq)+
    moreover have "a \<in> f`S \<and> C \<subseteq> f`T"
      using ST by (smt (verit, best) Y closedin_subset fg image_eqI subset_iff)   
    moreover have "disjnt (f`S) (f`T)"
      using ST by (smt (verit, ccfv_SIG) disjnt_iff fg image_iff openin_subset subsetD)
    ultimately show "\<exists>U V. openin Y U \<and> openin Y V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
      by metis
  qed
qed

lemma homeomorphic_regular_space:
   "X homeomorphic_space Y
        \<Longrightarrow> (regular_space X \<longleftrightarrow> regular_space Y)"
  by (meson homeomorphic_regular_space_aux homeomorphic_space_sym)

lemma regular_space:
   "regular_space X \<longleftrightarrow>
        (\<forall>C a. closedin X C \<and> a \<in> topspace X - C
              \<longrightarrow> (\<exists>U. openin X U \<and> a \<in> U \<and> disjnt C (X closure_of U)))"
  unfolding regular_space_def
proof (intro all_cong1 imp_cong refl ex_cong1)
  fix C a U
  assume C: "closedin X C \<and> a \<in> topspace X - C"
  show "(\<exists>V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V)  
    \<longleftrightarrow> (openin X U \<and> a \<in> U \<and> disjnt C (X closure_of U))" (is "?lhs=?rhs")
  proof
    assume ?lhs
    then show ?rhs
      by (smt (verit, best) disjnt_iff in_closure_of subsetD)
  next
    assume R: ?rhs
    then have "disjnt U (topspace X - X closure_of U)"
      by (meson DiffD2 closure_of_subset disjnt_iff openin_subset subsetD)
    moreover have "C \<subseteq> topspace X - X closure_of U"
      by (meson C DiffI R closedin_subset disjnt_iff subset_eq)
    ultimately show ?lhs
      using R by (rule_tac x="topspace X - X closure_of U" in exI) auto
    qed
qed

lemma neighbourhood_base_of_closedin:
  "neighbourhood_base_of (closedin X) X \<longleftrightarrow> regular_space X" (is "?lhs=?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<forall>W x. openin X W \<and> x \<in> W \<longrightarrow>
                  (\<exists>U. openin X U \<and> (\<exists>V. closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W)))"
    by (simp add: neighbourhood_base_of)
  also have "\<dots> \<longleftrightarrow> (\<forall>W x. closedin X W \<and> x \<in> topspace X - W \<longrightarrow>
                     (\<exists>U. openin X U \<and> (\<exists>V. closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> topspace X - W)))"
    by (smt (verit) Diff_Diff_Int closedin_def inf.absorb_iff2 openin_closedin_eq)
  also have "\<dots> \<longleftrightarrow> ?rhs"
  proof -
    have \<section>: "(\<exists>V. closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> topspace X - W) 
         \<longleftrightarrow> (\<exists>V. openin X V \<and> x \<in> U \<and> W \<subseteq> V \<and> disjnt U V)" (is "?lhs=?rhs")
      if "openin X U"  "closedin X W" "x \<in> topspace X" "x \<notin> W" for W U x
    proof
      assume ?lhs with \<open>closedin X W\<close> show ?rhs
        unfolding closedin_def by (smt (verit) Diff_mono disjnt_Diff1 double_diff subset_eq)
    next
      assume ?rhs with \<open>openin X U\<close> show ?lhs
        unfolding openin_closedin_eq disjnt_def
        by (smt (verit) Diff_Diff_Int Diff_disjoint Diff_eq_empty_iff Int_Diff inf.orderE)
    qed
    show ?thesis
      unfolding regular_space_def
      by (intro all_cong1 ex_cong1 imp_cong refl) (metis \<section> DiffE)
  qed
  finally show ?thesis .
qed

lemma regular_space_discrete_topology [simp]:
   "regular_space (discrete_topology S)"
  using neighbourhood_base_of_closedin neighbourhood_base_of_discrete_topology by fastforce

lemma regular_space_subtopology:
 "regular_space X \<Longrightarrow> regular_space (subtopology X S)"
  unfolding regular_space_def openin_subtopology_alt closedin_subtopology_alt disjnt_iff
  by clarsimp (smt (verit, best) inf.orderE inf_le1 le_inf_iff)


lemma regular_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; regular_space X\<rbrakk> \<Longrightarrow> regular_space Y"
  using hereditary_imp_retractive_property homeomorphic_regular_space regular_space_subtopology by blast

lemma regular_t0_imp_Hausdorff_space:
   "\<lbrakk>regular_space X; t0_space X\<rbrakk> \<Longrightarrow> Hausdorff_space X"
  apply (clarsimp simp: regular_space_def t0_space Hausdorff_space_def)
  by (metis disjnt_sym subsetD)

lemma regular_t0_eq_Hausdorff_space:
   "regular_space X \<Longrightarrow> (t0_space X \<longleftrightarrow> Hausdorff_space X)"
  using Hausdorff_imp_t0_space regular_t0_imp_Hausdorff_space by blast

lemma regular_t1_imp_Hausdorff_space:
   "\<lbrakk>regular_space X; t1_space X\<rbrakk> \<Longrightarrow> Hausdorff_space X"
  by (simp add: regular_t0_imp_Hausdorff_space t1_imp_t0_space)

lemma regular_t1_eq_Hausdorff_space:
   "regular_space X \<Longrightarrow> t1_space X \<longleftrightarrow> Hausdorff_space X"
  using regular_t0_imp_Hausdorff_space t1_imp_t0_space t1_or_Hausdorff_space by blast

lemma compact_Hausdorff_imp_regular_space:
  assumes "compact_space X" "Hausdorff_space X"
  shows "regular_space X"
  unfolding regular_space_def
proof clarify
  fix S a
  assume "closedin X S" and "a \<in> topspace X" and "a \<notin> S"
  then show "\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> S \<subseteq> V \<and> disjnt U V"
    using assms unfolding Hausdorff_space_compact_sets
    by (metis closedin_compact_space compactin_sing disjnt_empty1 insert_subset disjnt_insert1)
qed

lemma neighbourhood_base_of_closed_Hausdorff_space:
   "regular_space X \<and> Hausdorff_space X \<longleftrightarrow>
    neighbourhood_base_of (\<lambda>C. closedin X C \<and> Hausdorff_space(subtopology X C)) X" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: Hausdorff_space_subtopology neighbourhood_base_of_closedin)
next
  assume ?rhs then show ?lhs
  by (metis (mono_tags, lifting) Hausdorff_space_closed_neighbourhood neighbourhood_base_of neighbourhood_base_of_closedin openin_topspace)
qed

lemma locally_compact_imp_kc_eq_Hausdorff_space:
   "neighbourhood_base_of (compactin X) X \<Longrightarrow> kc_space X \<longleftrightarrow> Hausdorff_space X"
  by (metis Hausdorff_imp_kc_space kc_imp_t1_space kc_space_def neighbourhood_base_of_closedin neighbourhood_base_of_mono regular_t1_imp_Hausdorff_space)

lemma regular_space_compact_closed_separation:
  assumes X: "regular_space X"
      and S: "compactin X S"
      and T: "closedin X T"
      and "disjnt S T"
    shows "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
proof (cases "S={}")
  case True
  then show ?thesis
    by (meson T closedin_def disjnt_empty1 empty_subsetI openin_empty openin_topspace)
next
  case False
  then have "\<exists>U V. x \<in> S \<longrightarrow> openin X U \<and> openin X V \<and> x \<in> U \<and> T \<subseteq> V \<and> disjnt U V" for x
    using assms unfolding regular_space_def
    by (smt (verit) Diff_iff compactin_subset_topspace disjnt_iff subsetD)
  then obtain U V where UV: "\<And>x. x \<in> S \<Longrightarrow> openin X (U x) \<and> openin X (V x) \<and> x \<in> (U x) \<and> T \<subseteq> (V x) \<and> disjnt (U x) (V x)" 
    by metis
  then obtain \<F> where "finite \<F>" "\<F> \<subseteq> U ` S" "S \<subseteq> \<Union> \<F>"
    using S unfolding compactin_def by (smt (verit) UN_iff image_iff subsetI)
  then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> \<Union>(U ` K)"
    by (metis finite_subset_image)
  show ?thesis 
  proof (intro exI conjI)
    show "openin X (\<Union>(U ` K))"
      using \<open>K \<subseteq> S\<close> UV by blast
    show "openin X (\<Inter>(V ` K))"
      using False K UV \<open>K \<subseteq> S\<close> \<open>finite K\<close> by blast
    show "S \<subseteq> \<Union>(U ` K)"
      by (simp add: K)
    show "T \<subseteq> \<Inter>(V ` K)"
      using UV \<open>K \<subseteq> S\<close> by blast
    show "disjnt (\<Union>(U ` K)) (\<Inter>(V ` K))"
      by (smt (verit) Inter_iff UN_E UV \<open>K \<subseteq> S\<close> disjnt_iff image_eqI subset_iff)
  qed
qed

lemma regular_space_compact_closed_sets:
   "regular_space X \<longleftrightarrow>
        (\<forall>S T. compactin X S \<and> closedin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    using regular_space_compact_closed_separation by fastforce
next
  assume R: ?rhs
  show ?lhs
    unfolding regular_space
  proof clarify
    fix S x
    assume "closedin X S" and "x \<in> topspace X" and "x \<notin> S"
    then obtain U V where "openin X U \<and> openin X V \<and> {x} \<subseteq> U \<and> S \<subseteq> V \<and> disjnt U V"
      by (metis R compactin_sing disjnt_empty1 disjnt_insert1)
    then show "\<exists>U. openin X U \<and> x \<in> U \<and> disjnt S (X closure_of U)"
      by (smt (verit, best) disjnt_iff in_closure_of insert_subset subsetD)
  qed
qed


lemma regular_space_prod_topology:
   "regular_space (prod_topology X Y) \<longleftrightarrow>
        X = trivial_topology \<or> Y = trivial_topology \<or> regular_space X \<and> regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis regular_space_retraction_map_image retraction_map_fst retraction_map_snd)
next
  assume R: ?rhs  
  show ?lhs
  proof (cases "X = trivial_topology \<or> Y = trivial_topology")
    case True then show ?thesis by auto
  next
    case False
    then have "regular_space X" "regular_space Y"
      using R by auto
    show ?thesis
      unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of
    proof clarify
      fix W x y
      assume W: "openin (prod_topology X Y) W" and "(x,y) \<in> W"
      then obtain U V where U: "openin X U" "x \<in> U" and V: "openin Y V" "y \<in> V" 
        and "U \<times> V \<subseteq> W"
        by (metis openin_prod_topology_alt)
      obtain D1 C1 where 1: "openin X D1" "closedin X C1" "x \<in> D1" "D1 \<subseteq> C1" "C1 \<subseteq> U"
        by (metis \<open>regular_space X\<close> U neighbourhood_base_of neighbourhood_base_of_closedin)
      obtain D2 C2 where 2: "openin Y D2" "closedin Y C2" "y \<in> D2" "D2 \<subseteq> C2" "C2 \<subseteq> V"
        by (metis \<open>regular_space Y\<close> V neighbourhood_base_of neighbourhood_base_of_closedin)
      show "\<exists>U V. openin (prod_topology X Y) U \<and> closedin (prod_topology X Y) V \<and>
                  (x,y) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
      proof (intro conjI exI)
        show "openin (prod_topology X Y) (D1 \<times> D2)"
          by (simp add: 1 2 openin_prod_Times_iff)
        show "closedin (prod_topology X Y) (C1 \<times> C2)"
          by (simp add: 1 2 closedin_prod_Times_iff)
      qed (use 1 2 \<open>U \<times> V \<subseteq> W\<close> in auto)
    qed
  qed
qed

lemma regular_space_product_topology:
   "regular_space (product_topology X I) \<longleftrightarrow>
    (product_topology X I) = trivial_topology \<or> (\<forall>i \<in> I. regular_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson regular_space_retraction_map_image retraction_map_product_projection)
next
  assume R: ?rhs  
  show ?lhs
  proof (cases "product_topology X I = trivial_topology")
    case True
    then show ?thesis
      by auto
  next
    case False
    then obtain x where x: "x \<in> topspace (product_topology X I)"
      by (meson ex_in_conv null_topspace_iff_trivial)
    define \<F> where "\<F> \<equiv> {Pi\<^sub>E I U |U. finite {i \<in> I. U i \<noteq> topspace (X i)}
                        \<and> (\<forall>i\<in>I. openin (X i) (U i))}"
    have oo: "openin (product_topology X I) = arbitrary union_of (\<lambda>W. W \<in> \<F>)"
      by (simp add: \<F>_def openin_product_topology product_topology_base_alt)
    have "\<exists>U V. openin (product_topology X I) U \<and> closedin (product_topology X I) V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> Pi\<^sub>E I W"
      if fin: "finite {i \<in> I. W i \<noteq> topspace (X i)}" 
        and opeW: "\<And>k. k \<in> I \<Longrightarrow> openin (X k) (W k)" and x: "x \<in> PiE I W" for W x
    proof -
      have "\<And>i. i \<in> I \<Longrightarrow> \<exists>U V. openin (X i) U \<and> closedin (X i) V \<and> x i \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W i"
        by (metis False PiE_iff R neighbourhood_base_of neighbourhood_base_of_closedin opeW x)
      then obtain U C where UC: 
        "\<And>i. i \<in> I \<Longrightarrow> openin (X i) (U i) \<and> closedin (X i) (C i) \<and> x i \<in> U i \<and> U i \<subseteq> C i \<and> C i \<subseteq> W i"
        by metis
      define PI where "PI \<equiv> \<lambda>V. PiE I (\<lambda>i. if W i = topspace(X i) then topspace(X i) else V i)"
      show ?thesis
      proof (intro conjI exI)
        have "\<forall>i\<in>I. W i \<noteq> topspace (X i) \<longrightarrow> openin (X i) (U i)"
          using UC by force
        with fin show "openin (product_topology X I) (PI U)"
          by (simp add: Collect_mono_iff PI_def openin_PiE_gen rev_finite_subset)
        show "closedin (product_topology X I) (PI C)"
          by (simp add: UC closedin_product_topology PI_def)
        show "x \<in> PI U"
          using UC x by (fastforce simp: PI_def)
        show "PI U \<subseteq> PI C"
          by (smt (verit) UC Orderings.order_eq_iff PiE_mono PI_def)
        show "PI C \<subseteq> Pi\<^sub>E I W"
          by (simp add: UC PI_def subset_PiE)
      qed
    qed
    then have "neighbourhood_base_of (closedin (product_topology X I)) (product_topology X I)"
      unfolding neighbourhood_base_of_topology_base [OF oo] by (force simp: \<F>_def)
    then show ?thesis
      by (simp add: neighbourhood_base_of_closedin)
  qed
qed

lemma closed_map_paired_gen_aux:
  assumes "regular_space Y" and f: "closed_map Z X f" and g: "closed_map Z Y g"
    and clo: "\<And>y. y \<in> topspace X \<Longrightarrow> closedin Z {x \<in> topspace Z. f x = y}"
    and contg: "continuous_map Z Y g"
  shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
  unfolding closed_map_def
proof (intro strip)
  fix C assume "closedin Z C"
  then have "C \<subseteq> topspace Z"
    by (simp add: closedin_subset)
  have "f \<in> topspace Z \<rightarrow> topspace X" "g \<in> topspace Z \<rightarrow> topspace Y"
    by (simp_all add: assms closed_map_imp_subset_topspace)
  show "closedin (prod_topology X Y) ((\<lambda>x. (f x, g x)) ` C)"
    unfolding closedin_def topspace_prod_topology
  proof (intro conjI)
    have "closedin Y (g ` C)"
      using \<open>closedin Z C\<close> assms(3) closed_map_def by blast
    with assms show "(\<lambda>x. (f x, g x)) ` C \<subseteq> topspace X \<times> topspace Y"
      by (smt (verit) SigmaI \<open>closedin Z C\<close> closed_map_def closedin_subset image_subset_iff)
    have *: "\<exists>T. openin (prod_topology X Y) T \<and> (y1,y2) \<in> T \<and> T \<subseteq> topspace X \<times> topspace Y - (\<lambda>x. (f x, g x)) ` C"
      if "(y1,y2) \<notin> (\<lambda>x. (f x, g x)) ` C" and y1: "y1 \<in> topspace X" and y2: "y2 \<in> topspace Y"
      for y1 y2
    proof -
      define A where "A \<equiv> topspace Z - (C \<inter> {x \<in> topspace Z. f x = y1})"
      have A: "openin Z A" "{x \<in> topspace Z. g x = y2} \<subseteq> A"
        using that \<open>closedin Z C\<close> clo that(2) by (auto simp: A_def)
      obtain V0 where "openin Y V0 \<and> y2 \<in> V0" and UA: "{x \<in> topspace Z. g x \<in> V0} \<subseteq> A"
        using g A y2 unfolding closed_map_fibre_neighbourhood by blast
      then obtain V V' where VV: "openin Y V \<and> closedin Y V' \<and> y2 \<in> V \<and> V \<subseteq> V'" and "V' \<subseteq> V0"
        by (metis (no_types, lifting) \<open>regular_space Y\<close> neighbourhood_base_of neighbourhood_base_of_closedin)
      with UA have subA: "{x \<in> topspace Z. g x \<in> V'} \<subseteq> A"
        by blast
      show ?thesis
      proof -
        define B where "B \<equiv> topspace Z - (C \<inter> {x \<in> topspace Z. g x \<in> V'})"
        have "openin Z B"
          using VV \<open>closedin Z C\<close> contg by (fastforce simp: B_def continuous_map_closedin)
        have "{x \<in> topspace Z. f x = y1} \<subseteq> B"
          using A_def subA by (auto simp: A_def B_def)
        then obtain U where "openin X U" "y1 \<in> U" and subB: "{x \<in> topspace Z. f x \<in> U} \<subseteq> B"
          using \<open>openin Z B\<close> y1 f unfolding closed_map_fibre_neighbourhood by meson
        show ?thesis
        proof (intro conjI exI)
          show "openin (prod_topology X Y) (U \<times> V)"
            by (metis VV \<open>openin X U\<close> openin_prod_Times_iff)
          show "(y1, y2) \<in> U \<times> V"
            by (simp add: VV \<open>y1 \<in> U\<close>)
          show "U \<times> V \<subseteq> topspace X \<times> topspace Y - (\<lambda>x. (f x, g x)) ` C"
            using VV \<open>C \<subseteq> topspace Z\<close> \<open>openin X U\<close> subB
            by (force simp: image_iff B_def subset_iff dest: openin_subset)
        qed
      qed
    qed
    then show "openin (prod_topology X Y) (topspace X \<times> topspace Y - (\<lambda>x. (f x, g x)) ` C)"
      by (smt (verit, ccfv_threshold) Diff_iff SigmaE openin_subopen)
  qed
qed


lemma closed_map_paired_gen:
  assumes f: "closed_map Z X f" and g: "closed_map Z Y g"
  and D: "(regular_space X \<and> continuous_map Z X f \<and> (\<forall>z \<in> topspace Y. closedin Z {x \<in> topspace Z. g x = z})
         \<or> regular_space Y \<and> continuous_map Z Y g \<and> (\<forall>y \<in> topspace X. closedin Z {x \<in> topspace Z. f x = y}))"
         (is "?RSX \<or> ?RSY")
       shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
  using D
proof
  assume RSX: ?RSX
  have eq: "(\<lambda>x. (f x, g x)) = (\<lambda>(x,y). (y,x)) \<circ> (\<lambda>x. (g x, f x))"
    by auto
  show ?thesis
    unfolding eq
  proof (rule closed_map_compose)
    show "closed_map Z (prod_topology Y X) (\<lambda>x. (g x, f x))"
      using RSX closed_map_paired_gen_aux f g by fastforce
    show "closed_map (prod_topology Y X) (prod_topology X Y) (\<lambda>(x, y). (y, x))"
      using homeomorphic_imp_closed_map homeomorphic_map_swap by blast
  qed
qed (blast intro: assms closed_map_paired_gen_aux)

lemma closed_map_paired:
  assumes "closed_map Z X f" and contf: "continuous_map Z X f"
          "closed_map Z Y g" and contg: "continuous_map Z Y g"
  and D: "t1_space X \<and> regular_space Y \<or> regular_space X \<and> t1_space Y"
  shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
proof (rule closed_map_paired_gen)
  show "regular_space X \<and> continuous_map Z X f \<and> (\<forall>z\<in>topspace Y. closedin Z {x \<in> topspace Z. g x = z}) \<or> regular_space Y \<and> continuous_map Z Y g \<and> (\<forall>y\<in>topspace X. closedin Z {x \<in> topspace Z. f x = y})"
    using D contf contg
    by (smt (verit, del_insts) Collect_cong closedin_continuous_map_preimage t1_space_closedin_singleton singleton_iff)
qed (use assms in auto)

lemma closed_map_pairwise:
  assumes  "closed_map Z X (fst \<circ> f)" "continuous_map Z X (fst \<circ> f)"
    "closed_map Z Y (snd \<circ> f)" "continuous_map Z Y (snd \<circ> f)"
    "t1_space X \<and> regular_space Y \<or> regular_space X \<and> t1_space Y"
  shows "closed_map Z (prod_topology X Y) f"
proof -
  have "closed_map Z (prod_topology X Y) (\<lambda>a. ((fst \<circ> f) a, (snd \<circ> f) a))"
    using assms closed_map_paired by blast
  then show ?thesis
    by auto
qed

lemma continuous_imp_proper_map:
   "\<lbrakk>compact_space X; kc_space Y; continuous_map X Y f\<rbrakk> \<Longrightarrow> proper_map X Y f"
  by (simp add: continuous_closed_imp_proper_map continuous_imp_closed_map_gen kc_imp_t1_space)


lemma tube_lemma_right:
  assumes W: "openin (prod_topology X Y) W" and C: "compactin Y C" 
    and x: "x \<in> topspace X" and subW: "{x} \<times> C \<subseteq> W"
  shows "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> C \<subseteq> V \<and> U \<times> V \<subseteq> W"
proof (cases "C = {}")
  case True
  with x show ?thesis by auto
next
  case False
  have "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> W" 
    if "y \<in> C" for y
    using W openin_prod_topology_alt subW subsetD that by fastforce
  then obtain U V where UV: "\<And>y. y \<in> C \<Longrightarrow> openin X (U y) \<and> openin Y (V y) \<and> x \<in> U y \<and> y \<in> V y \<and> U y \<times> V y \<subseteq> W" 
    by metis
  then obtain D where D: "finite D" "D \<subseteq> C" "C \<subseteq> \<Union> (V ` D)"
    using compactinD [OF C, of "V`C"]
    by (smt (verit) UN_I finite_subset_image imageE subsetI)
  show ?thesis
  proof (intro exI conjI)
    show "openin X (\<Inter> (U ` D))" "openin Y (\<Union> (V ` D))"
      using D False UV by blast+
    show "x \<in> \<Inter> (U ` D)" "C \<subseteq> \<Union> (V ` D)" "\<Inter> (U ` D) \<times> \<Union> (V ` D) \<subseteq> W"
      using D UV by force+
  qed
qed


lemma closed_map_fst:
  assumes "compact_space Y"
  shows "closed_map (prod_topology X Y) X fst"
proof -
  have *: "{x \<in> topspace X \<times> topspace Y. fst x \<in> U} = U \<times> topspace Y"
    if "U \<subseteq> topspace X" for U
    using that by force
  have **: "\<And>U y. \<lbrakk>openin (prod_topology X Y) U; y \<in> topspace X;
            {x \<in> topspace X \<times> topspace Y. fst x = y} \<subseteq> U\<rbrakk>
           \<Longrightarrow> \<exists>V. openin X V \<and> y \<in> V \<and> V \<times> topspace Y \<subseteq> U"
    using tube_lemma_right[of X Y _ "topspace Y"] assms by (fastforce simp: compact_space_def)
  show ?thesis
    unfolding closed_map_fibre_neighbourhood
    by (force simp: * openin_subset cong: conj_cong intro: **)
qed

lemma closed_map_snd:
  assumes "compact_space X"
  shows "closed_map (prod_topology X Y) Y snd"
proof -
  have "snd = fst o prod.swap"
    by force
  moreover have "closed_map (prod_topology X Y) Y (fst o prod.swap)"
  proof (rule closed_map_compose)
    show "closed_map (prod_topology X Y) (prod_topology Y X) prod.swap"
      by (metis (no_types, lifting) homeomorphic_imp_closed_map homeomorphic_map_eq homeomorphic_map_swap prod.swap_def split_beta)
    show "closed_map (prod_topology Y X) Y fst"
      by (simp add: closed_map_fst assms)
  qed
  ultimately show ?thesis
    by metis
qed

lemma closed_map_paired_closed_map_right:
   "\<lbrakk>closed_map X Y f; regular_space X;
     \<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}\<rbrakk>
    \<Longrightarrow> closed_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
  by (rule closed_map_paired_gen [OF closed_map_id, unfolded id_def]) auto

lemma closed_map_paired_closed_map_left:
  assumes "closed_map X Y f"  "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "closed_map X (prod_topology Y X) (\<lambda>x. (f x, x))"
proof -
  have eq: "(\<lambda>x. (f x, x)) = (\<lambda>(x,y). (y,x)) \<circ> (\<lambda>x. (x, f x))"
    by auto
  show ?thesis
    unfolding eq
  proof (rule closed_map_compose)
    show "closed_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
      by (simp add: assms closed_map_paired_closed_map_right)
    show "closed_map (prod_topology X Y) (prod_topology Y X) (\<lambda>(x, y). (y, x))"
      using homeomorphic_imp_closed_map homeomorphic_map_swap by blast
  qed
qed

lemma closed_map_imp_closed_graph:
  assumes "closed_map X Y f" "regular_space X"
          "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "closedin (prod_topology X Y) ((\<lambda>x. (x, f x)) ` topspace X)"
  using assms closed_map_def closed_map_paired_closed_map_right by blast

lemma proper_map_paired_closed_map_right:
  assumes "closed_map X Y f" "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "proper_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
  by (simp add: assms closed_injective_imp_proper_map inj_on_def closed_map_paired_closed_map_right)

lemma proper_map_paired_closed_map_left:
  assumes "closed_map X Y f" "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "proper_map X (prod_topology Y X) (\<lambda>x. (f x, x))"
  by (simp add: assms closed_injective_imp_proper_map inj_on_def closed_map_paired_closed_map_left)

proposition regular_space_continuous_proper_map_image:
  assumes "regular_space X" and contf: "continuous_map X Y f" and pmapf: "proper_map X Y f"
    and fim: "f ` (topspace X) = topspace Y"
  shows "regular_space Y"
  unfolding regular_space_def
proof clarify
  fix C y
  assume "closedin Y C" and "y \<in> topspace Y" and "y \<notin> C"
  have "closed_map X Y f" "(\<forall>y \<in> topspace Y. compactin X {x \<in> topspace X. f x = y})"
    using pmapf proper_map_def by force+
  moreover have "closedin X {z \<in> topspace X. f z \<in> C}"
    using \<open>closedin Y C\<close> contf continuous_map_closedin by fastforce
  moreover have "disjnt {z \<in> topspace X. f z = y} {z \<in> topspace X. f z \<in> C}"
    using \<open>y \<notin> C\<close> disjnt_iff by blast
  ultimately
  obtain U V where UV: "openin X U" "openin X V" "{z \<in> topspace X. f z = y} \<subseteq> U" "{z \<in> topspace X. f z \<in> C} \<subseteq> V"
                  and dUV: "disjnt U V"
    using \<open>y \<in> topspace Y\<close> \<open>regular_space X\<close> unfolding regular_space_compact_closed_sets
    by meson

  have *: "\<And>U T. openin X U \<and> T \<subseteq> topspace Y \<and> {x \<in> topspace X. f x \<in> T} \<subseteq> U \<longrightarrow>
         (\<exists>V. openin Y V \<and> T \<subseteq> V \<and> {x \<in> topspace X. f x \<in> V} \<subseteq> U)"
   using \<open>closed_map X Y f\<close> unfolding closed_map_preimage_neighbourhood by blast
  obtain V1 where V1: "openin Y V1 \<and> y \<in> V1" and sub1: "{x \<in> topspace X. f x \<in> V1} \<subseteq> U"
    using * [of U "{y}"] UV \<open>y \<in> topspace Y\<close> by auto
  moreover
  obtain V2 where "openin Y V2 \<and> C \<subseteq> V2" and sub2: "{x \<in> topspace X. f x \<in> V2} \<subseteq> V"
    by (smt (verit, ccfv_SIG) * UV \<open>closedin Y C\<close> closedin_subset mem_Collect_eq subset_iff)
  moreover have "disjnt V1 V2"
  proof -
    have "\<And>x. \<lbrakk>\<forall>x. x \<in> U \<longrightarrow> x \<notin> V; x \<in> V1; x \<in> V2\<rbrakk> \<Longrightarrow> False"
      by (smt (verit) V1 fim image_iff mem_Collect_eq openin_subset sub1 sub2 subsetD)
    with dUV show ?thesis by (auto simp: disjnt_iff)
  qed
  ultimately show "\<exists>U V. openin Y U \<and> openin Y V \<and> y \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
    by meson
qed

lemma regular_space_perfect_map_image:
   "\<lbrakk>regular_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> regular_space Y"
  by (meson perfect_map_def regular_space_continuous_proper_map_image)

proposition regular_space_perfect_map_image_eq:
  assumes "Hausdorff_space X" and perf: "perfect_map X Y f"
  shows "regular_space X \<longleftrightarrow> regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    using perf regular_space_perfect_map_image by blast
next
  assume R: ?rhs  
  have "continuous_map X Y f" "proper_map X Y f" and fim: "f ` (topspace X) = topspace Y"
    using perf by (auto simp: perfect_map_def)
  then have "closed_map X Y f" and preYf: "(\<forall>y \<in> topspace Y. compactin X {x \<in> topspace X. f x = y})"
    by (simp_all add: proper_map_def)
  show ?lhs
    unfolding regular_space_def
  proof clarify
    fix C x
    assume "closedin X C" and "x \<in> topspace X" and "x \<notin> C"
    obtain U1 U2 where "openin X U1" "openin X U2" "{x} \<subseteq> U1" and "disjnt U1 U2"
      and subV: "C \<inter> {z \<in> topspace X. f z = f x} \<subseteq> U2"
    proof (rule Hausdorff_space_compact_separation [of X "{x}" "C \<inter> {z \<in> topspace X. f z = f x}", OF \<open>Hausdorff_space X\<close>])
      show "compactin X {x}"
        by (simp add: \<open>x \<in> topspace X\<close>)
      show "compactin X (C \<inter> {z \<in> topspace X. f z = f x})"
        using \<open>closedin X C\<close> fim \<open>x \<in> topspace X\<close> closed_Int_compactin preYf by fastforce
      show "disjnt {x} (C \<inter> {z \<in> topspace X. f z = f x})"
        using \<open>x \<notin> C\<close> by force
    qed
    have "closedin Y (f ` (C - U2))"
      using \<open>closed_map X Y f\<close> \<open>closedin X C\<close> \<open>openin X U2\<close> closed_map_def by blast
    moreover
    have "f x \<in> topspace Y - f ` (C - U2)"
      using \<open>closedin X C\<close> \<open>continuous_map X Y f\<close> \<open>x \<in> topspace X\<close> closedin_subset continuous_map_def subV 
      by (fastforce simp: Pi_iff)
    ultimately
    obtain V1 V2 where VV: "openin Y V1" "openin Y V2" "f x \<in> V1" 
                and subV2: "f ` (C - U2) \<subseteq> V2" and "disjnt V1 V2"
      by (meson R regular_space_def)
    show "\<exists>U U'. openin X U \<and> openin X U' \<and> x \<in> U \<and> C \<subseteq> U' \<and> disjnt U U'"
    proof (intro exI conjI)
      show "openin X (U1 \<inter> {x \<in> topspace X. f x \<in> V1})"
        using VV(1) \<open>continuous_map X Y f\<close> \<open>openin X U1\<close> continuous_map by fastforce
      show "openin X (U2 \<union> {x \<in> topspace X. f x \<in> V2})"
        using VV(2) \<open>continuous_map X Y f\<close> \<open>openin X U2\<close> continuous_map by fastforce
      show "x \<in> U1 \<inter> {x \<in> topspace X. f x \<in> V1}"
        using VV(3) \<open>x \<in> topspace X\<close> \<open>{x} \<subseteq> U1\<close> by auto
      show "C \<subseteq> U2 \<union> {x \<in> topspace X. f x \<in> V2}"
        using \<open>closedin X C\<close> closedin_subset subV2 by auto
      show "disjnt (U1 \<inter> {x \<in> topspace X. f x \<in> V1}) (U2 \<union> {x \<in> topspace X. f x \<in> V2})"
        using \<open>disjnt U1 U2\<close> \<open>disjnt V1 V2\<close> by (auto simp: disjnt_iff)
    qed
  qed
qed


subsection\<open>Locally compact spaces\<close>

definition locally_compact_space 
  where "locally_compact_space X \<equiv>
    \<forall>x \<in> topspace X. \<exists>U K. openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"

lemma homeomorphic_locally_compact_spaceD:
  assumes X: "locally_compact_space X" and "X homeomorphic_space Y"
  shows "locally_compact_space Y"
proof -
  obtain f where hmf: "homeomorphic_map X Y f"
    using assms homeomorphic_space by blast
  then have eq: "topspace Y = f ` (topspace X)"
    by (simp add: homeomorphic_imp_surjective_map)
  have "\<exists>V K. openin Y V \<and> compactin Y K \<and> f x \<in> V \<and> V \<subseteq> K"
    if "x \<in> topspace X" "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K" for x U K
    using that 
    by (meson hmf homeomorphic_map_compactness_eq homeomorphic_map_openness_eq image_mono image_eqI)
  with X show ?thesis
    by (smt (verit) eq image_iff locally_compact_space_def)
qed

lemma homeomorphic_locally_compact_space:
  assumes "X homeomorphic_space Y"
  shows "locally_compact_space X \<longleftrightarrow> locally_compact_space Y"
  by (meson assms homeomorphic_locally_compact_spaceD homeomorphic_space_sym)

lemma locally_compact_space_retraction_map_image:
  assumes "retraction_map X Y r" and X: "locally_compact_space X"
  shows "locally_compact_space Y"
proof -
  obtain s where s: "retraction_maps X Y r s"
    using assms retraction_map_def by blast
  obtain T where "T retract_of_space X" and Teq: "T = s ` topspace Y"
    using retraction_maps_section_image1 s by blast
  then obtain r where r: "continuous_map X (subtopology X T) r" "\<forall>x\<in>T. r x = x"
    by (meson retract_of_space_def)
  have "locally_compact_space (subtopology X T)"
    unfolding locally_compact_space_def openin_subtopology_alt
  proof clarsimp
    fix x
    assume "x \<in> topspace X" "x \<in> T"
    obtain U K where UK: "openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"
      by (meson X \<open>x \<in> topspace X\<close> locally_compact_space_def)
    then have "compactin (subtopology X T) (r ` K) \<and> T \<inter> U \<subseteq> r ` K"
      by (smt (verit) IntD1 image_compactin image_iff inf_le2 r subset_iff)
    then show "\<exists>U. openin X U \<and> (\<exists>K. compactin (subtopology X T) K \<and> x \<in> U \<and> T \<inter> U \<subseteq> K)"
      using UK by auto
  qed
  with Teq show ?thesis
    using homeomorphic_locally_compact_space retraction_maps_section_image2 s by blast
qed

lemma compact_imp_locally_compact_space:
   "compact_space X \<Longrightarrow> locally_compact_space X"
  using compact_space_def locally_compact_space_def by blast

lemma neighbourhood_base_imp_locally_compact_space:
   "neighbourhood_base_of (compactin X) X \<Longrightarrow> locally_compact_space X"
  by (metis locally_compact_space_def neighbourhood_base_of openin_topspace)

lemma locally_compact_imp_neighbourhood_base:
  assumes loc: "locally_compact_space X" and reg: "regular_space X"
  shows "neighbourhood_base_of (compactin X) X"
  unfolding neighbourhood_base_of
proof clarify
  fix W x
  assume "openin X W" and "x \<in> W"
  then obtain U K where "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K"
    by (metis loc locally_compact_space_def openin_subset subsetD)
  moreover have "openin X (U \<inter> W) \<and> x \<in> U \<inter> W"
    using \<open>openin X W\<close> \<open>x \<in> W\<close> \<open>openin X U\<close> \<open>x \<in> U\<close> by blast
  then have "\<exists>u' v. openin X u' \<and> closedin X v \<and> x \<in> u' \<and> u' \<subseteq> v \<and> v \<subseteq> U \<and> v \<subseteq> W"
    using reg
    by (metis le_infE neighbourhood_base_of neighbourhood_base_of_closedin)
  then show "\<exists>U V. openin X U \<and> compactin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
    by (meson \<open>U \<subseteq> K\<close> \<open>compactin X K\<close> closed_compactin subset_trans)
qed

lemma Hausdorff_regular: "\<lbrakk>Hausdorff_space X; neighbourhood_base_of (compactin X) X\<rbrakk> \<Longrightarrow> regular_space X"
  by (metis compactin_imp_closedin neighbourhood_base_of_closedin neighbourhood_base_of_mono)

lemma locally_compact_Hausdorff_imp_regular_space: 
  assumes loc: "locally_compact_space X" and "Hausdorff_space X"
  shows "regular_space X"
  unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of
proof clarify
  fix W x
  assume "openin X W" and "x \<in> W"
  then have "x \<in> topspace X"
    using openin_subset by blast 
  then obtain U K where "openin X U" "compactin X K" and UK: "x \<in> U" "U \<subseteq> K"
    by (meson loc locally_compact_space_def)
  with \<open>Hausdorff_space X\<close> have "regular_space (subtopology X K)"
    using Hausdorff_space_subtopology compact_Hausdorff_imp_regular_space compact_space_subtopology by blast
  then have "\<exists>U' V'. openin (subtopology X K) U' \<and> closedin (subtopology X K) V' \<and> x \<in> U' \<and> U' \<subseteq> V' \<and> V' \<subseteq> K \<inter> W"
    unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of
    by (meson IntI \<open>U \<subseteq> K\<close> \<open>openin X W\<close> \<open>x \<in> U\<close> \<open>x \<in> W\<close> openin_subtopology_Int2 subsetD)
  then obtain V C where "openin X V" "closedin X C" and VC: "x \<in> K \<inter> V" "K \<inter> V \<subseteq> K \<inter> C" "K \<inter> C \<subseteq> K \<inter> W"
    by (metis Int_commute closedin_subtopology openin_subtopology)
  show "\<exists>U V. openin X U \<and> closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
  proof (intro conjI exI)
    show "openin X (U \<inter> V)"
      using \<open>openin X U\<close> \<open>openin X V\<close> by blast
    show "closedin X (K \<inter> C)"
      using \<open>closedin X C\<close> \<open>compactin X K\<close> compactin_imp_closedin \<open>Hausdorff_space X\<close> by blast
  qed (use UK VC in auto)
qed

lemma locally_compact_space_neighbourhood_base:
  "Hausdorff_space X \<or> regular_space X
        \<Longrightarrow> locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (compactin X) X"
  by (metis locally_compact_imp_neighbourhood_base locally_compact_Hausdorff_imp_regular_space 
            neighbourhood_base_imp_locally_compact_space)

lemma locally_compact_Hausdorff_or_regular:
   "locally_compact_space X \<and> (Hausdorff_space X \<or> regular_space X) \<longleftrightarrow> locally_compact_space X \<and> regular_space X"
  using locally_compact_Hausdorff_imp_regular_space by blast

lemma locally_compact_space_compact_closedin:
  assumes  "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>U K. openin X U \<and> compactin X K \<and> closedin X K \<and> x \<in> U \<and> U \<subseteq> K)"
  using locally_compact_Hausdorff_or_regular unfolding locally_compact_space_def
  by (metis assms closed_compactin inf.absorb_iff2 le_infE neighbourhood_base_of neighbourhood_base_of_closedin)

lemma locally_compact_space_compact_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>U. openin X U \<and> compactin X (X closure_of U) \<and> x \<in> U)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis assms closed_compactin closedin_closure_of closure_of_eq closure_of_mono locally_compact_space_compact_closedin)
next
  assume ?rhs then show ?lhs
    by (meson closure_of_subset locally_compact_space_def openin_subset)
qed

lemma locally_compact_space_neighbourhood_base_closedin:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  with L have "neighbourhood_base_of (compactin X) X"
   by (simp add: locally_compact_imp_neighbourhood_base)
  with \<open>regular_space X\<close> show ?rhs
    by (smt (verit, ccfv_threshold) closed_compactin neighbourhood_base_of subset_trans neighbourhood_base_of_closedin)
next
  assume ?rhs then show ?lhs
    using neighbourhood_base_imp_locally_compact_space neighbourhood_base_of_mono by blast
qed

lemma locally_compact_space_neighbourhood_base_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>T. compactin X (X closure_of T)) X" 
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  with L have "neighbourhood_base_of (\<lambda>A. compactin X A \<and> closedin X A) X"
    using locally_compact_space_neighbourhood_base_closedin by blast
  then show ?rhs
    by (simp add: closure_of_closedin neighbourhood_base_of_mono)
next
  assume ?rhs then show ?lhs
    unfolding locally_compact_space_def neighbourhood_base_of
    by (meson closure_of_subset openin_topspace subset_trans)
qed

lemma locally_compact_space_neighbourhood_base_open_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> 
             neighbourhood_base_of (\<lambda>U. openin X U \<and> compactin X (X closure_of U)) X"
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  then have "neighbourhood_base_of (\<lambda>T. compactin X (X closure_of T)) X"
    using L locally_compact_space_neighbourhood_base_closure_of by auto
  with L show ?rhs
    unfolding neighbourhood_base_of
    by (meson closed_compactin closure_of_closure_of closure_of_eq closure_of_mono subset_trans)
next
  assume ?rhs then show ?lhs
    unfolding locally_compact_space_def neighbourhood_base_of
    by (meson closure_of_subset openin_topspace subset_trans)
qed

lemma locally_compact_space_compact_closed_compact:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>K. compactin X K
              \<longrightarrow> (\<exists>U L. openin X U \<and> compactin X L \<and> closedin X L \<and> K \<subseteq> U \<and> U \<subseteq> L))"
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then obtain U L where UL: "\<forall>x \<in> topspace X. openin X (U x) \<and> compactin X (L x) \<and> closedin X (L x) \<and> x \<in> U x \<and> U x \<subseteq> L x"
    unfolding locally_compact_space_compact_closedin [OF assms]
    by metis
  show ?rhs
  proof clarify
    fix K
    assume "compactin X K"
    then have "K \<subseteq> topspace X"
      by (simp add: compactin_subset_topspace)
    then have *: "(\<forall>U\<in>U ` K. openin X U) \<and> K \<subseteq> \<Union> (U ` K)"
      using UL by blast
    with \<open>compactin X K\<close> obtain KF where KF: "finite KF" "KF \<subseteq> K" "K \<subseteq> \<Union>(U ` KF)"
      by (metis compactinD finite_subset_image)
    show "\<exists>U L. openin X U \<and> compactin X L \<and> closedin X L \<and> K \<subseteq> U \<and> U \<subseteq> L"
    proof (intro conjI exI)
      show "openin X (\<Union> (U ` KF))"
        using "*" \<open>KF \<subseteq> K\<close> by fastforce
      show "compactin X (\<Union> (L ` KF))"
        by (smt (verit) UL \<open>K \<subseteq> topspace X\<close> KF compactin_Union finite_imageI imageE subset_iff)
      show "closedin X (\<Union> (L ` KF))"
        by (smt (verit) UL \<open>K \<subseteq> topspace X\<close> KF closedin_Union finite_imageI imageE subsetD)
    qed (use UL \<open>K \<subseteq> topspace X\<close> KF in auto)
  qed
next
  assume ?rhs then show ?lhs
    by (metis compactin_sing insert_subset locally_compact_space_def)
qed

lemma locally_compact_regular_space_neighbourhood_base:
   "locally_compact_space X \<and> regular_space X \<longleftrightarrow>
        neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X"
  using locally_compact_space_neighbourhood_base_closedin neighbourhood_base_of_closedin neighbourhood_base_of_mono by blast

lemma locally_compact_kc_space:
   "neighbourhood_base_of (compactin X) X \<and> kc_space X \<longleftrightarrow>
        locally_compact_space X \<and> Hausdorff_space X"
  using Hausdorff_imp_kc_space locally_compact_imp_kc_eq_Hausdorff_space locally_compact_space_neighbourhood_base by blast

lemma locally_compact_kc_space_alt:
   "neighbourhood_base_of (compactin X) X \<and> kc_space X \<longleftrightarrow>
        locally_compact_space X \<and> Hausdorff_space X \<and> regular_space X"
  using Hausdorff_regular locally_compact_kc_space by blast

lemma locally_compact_kc_imp_regular_space:
   "\<lbrakk>neighbourhood_base_of (compactin X) X; kc_space X\<rbrakk> \<Longrightarrow> regular_space X"
  using Hausdorff_regular locally_compact_imp_kc_eq_Hausdorff_space by blast

lemma kc_locally_compact_space:
   "kc_space X
    \<Longrightarrow> neighbourhood_base_of (compactin X) X \<longleftrightarrow> locally_compact_space X \<and> Hausdorff_space X \<and> regular_space X"
  using Hausdorff_regular locally_compact_kc_space by blast

lemma locally_compact_space_closed_subset:
  assumes loc: "locally_compact_space X" and "closedin X S"
  shows "locally_compact_space (subtopology X S)"
proof (clarsimp simp: locally_compact_space_def)
  fix x assume x: "x \<in> topspace X" "x \<in> S"
  then obtain U K where UK: "openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"
    by (meson loc locally_compact_space_def)
  show "\<exists>U. openin (subtopology X S) U \<and> 
            (\<exists>K. compactin (subtopology X S) K \<and> x \<in> U \<and> U \<subseteq> K)"
  proof (intro conjI exI)
    show "openin (subtopology X S) (S \<inter> U)"
      by (simp add: UK openin_subtopology_Int2)
    show "compactin (subtopology X S) (S \<inter> K)"
      by (simp add: UK assms(2) closed_Int_compactin compactin_subtopology)
  qed (use UK x in auto)
qed

lemma locally_compact_space_open_subset:
  assumes X: "Hausdorff_space X \<or> regular_space X" and loc: "locally_compact_space X" and "openin X S"
  shows "locally_compact_space (subtopology X S)"
proof (clarsimp simp: locally_compact_space_def)
  fix x assume x: "x \<in> topspace X" "x \<in> S"
  then obtain U K where UK: "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K"
    by (meson loc locally_compact_space_def)
  moreover have reg: "regular_space X"
    using X loc locally_compact_Hausdorff_imp_regular_space by blast
  moreover have "openin X (U \<inter> S)"
    by (simp add: UK \<open>openin X S\<close> openin_Int)
  ultimately obtain V C 
      where VC: "openin X V" "closedin X C" "x \<in> V" "V \<subseteq> C" "C \<subseteq> U" "C \<subseteq> S"
    by (metis \<open>x \<in> S\<close> IntI le_inf_iff neighbourhood_base_of neighbourhood_base_of_closedin)
  show "\<exists>U. openin (subtopology X S) U \<and> 
            (\<exists>K. compactin (subtopology X S) K \<and> x \<in> U \<and> U \<subseteq> K)"
  proof (intro conjI exI)
    show "openin (subtopology X S) V"
      using VC by (meson \<open>openin X S\<close> openin_open_subtopology order_trans)
    show "compactin (subtopology X S) (C \<inter> K)"
      using UK VC closed_Int_compactin compactin_subtopology by fastforce
  qed (use UK VC x in auto)
qed

lemma locally_compact_space_discrete_topology:
   "locally_compact_space (discrete_topology U)"
  by (simp add: neighbourhood_base_imp_locally_compact_space neighbourhood_base_of_discrete_topology)

lemma locally_compact_space_continuous_open_map_image:
  "\<lbrakk>continuous_map X X' f; open_map X X' f;
    f ` topspace X = topspace X'; locally_compact_space X\<rbrakk> \<Longrightarrow> locally_compact_space X'"
unfolding locally_compact_space_def open_map_def
  by (smt (verit, ccfv_SIG) image_compactin image_iff image_mono)

lemma locally_compact_subspace_openin_closure_of:
  assumes "Hausdorff_space X" and S: "S \<subseteq> topspace X" 
    and loc: "locally_compact_space (subtopology X S)"
  shows "openin (subtopology X (X closure_of S)) S"
  unfolding openin_subopen [where S=S]
proof clarify
  fix a assume "a \<in> S"
  then obtain T K where *: "openin X T" "compactin X K" "K \<subseteq> S" "a \<in> S" "a \<in> T" "S \<inter> T \<subseteq> K"
    using loc unfolding locally_compact_space_def
  by (metis IntE S compactin_subtopology inf_commute openin_subtopology topspace_subtopology_subset)
  have "T \<inter> X closure_of S \<subseteq> X closure_of (T \<inter> S)"
    by (simp add: "*"(1) openin_Int_closure_of_subset)
  also have "... \<subseteq> S"
    using * \<open>Hausdorff_space X\<close> by (metis closure_of_minimal compactin_imp_closedin order.trans inf_commute)
  finally have "T \<inter> X closure_of S \<subseteq> T \<inter> S" by simp 
  then have "openin (subtopology X (X closure_of S)) (T \<inter> S)"
    unfolding openin_subtopology using \<open>openin X T\<close> S closure_of_subset by fastforce
  with * show "\<exists>T. openin (subtopology X (X closure_of S)) T \<and> a \<in> T \<and> T \<subseteq> S"
    by blast
qed

lemma locally_compact_subspace_closed_Int_openin:
   "\<lbrakk>Hausdorff_space X \<and> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)\<rbrakk>
        \<Longrightarrow> \<exists>C U. closedin X C \<and> openin X U \<and> C \<inter> U = S"
  by (metis closedin_closure_of inf_commute locally_compact_subspace_openin_closure_of openin_subtopology)

lemma locally_compact_subspace_open_in_closure_of_eq:
  assumes "Hausdorff_space X" and loc: "locally_compact_space X"
  shows "openin (subtopology X (X closure_of S)) S \<longleftrightarrow> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then obtain "S \<subseteq> topspace X" "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space openin_subset by fastforce 
  then have "locally_compact_space (subtopology (subtopology X (X closure_of S)) S)"
    by (simp add: L loc locally_compact_space_closed_subset locally_compact_space_open_subset regular_space_subtopology)
  then show ?rhs
    by (metis L inf.orderE inf_commute le_inf_iff openin_subset subtopology_subtopology topspace_subtopology)
next
  assume ?rhs then show ?lhs
    using  assms locally_compact_subspace_openin_closure_of by blast
qed

lemma locally_compact_subspace_closed_Int_openin_eq:
  assumes "Hausdorff_space X" and loc: "locally_compact_space X"
  shows "(\<exists>C U. closedin X C \<and> openin X U \<and> C \<inter> U = S) \<longleftrightarrow> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then obtain C U where "closedin X C" "openin X U" and Seq: "S = C \<inter> U"
    by blast
  then have "C \<subseteq> topspace X"
    by (simp add: closedin_subset)
  have "locally_compact_space (subtopology (subtopology X C) (topspace (subtopology X C) \<inter> U))"
  proof (rule locally_compact_space_open_subset)
    show "locally_compact_space (subtopology X C)"
      by (simp add: \<open>closedin X C\<close> loc locally_compact_space_closed_subset)
    show "openin (subtopology X C) (topspace (subtopology X C) \<inter> U)"
      by (simp add: \<open>openin X U\<close> Int_left_commute inf_commute openin_Int openin_subtopology_Int2)
  qed (simp add: Hausdorff_space_subtopology \<open>Hausdorff_space X\<close>)
  then show ?rhs
    by (metis Seq \<open>C \<subseteq> topspace X\<close> inf.coboundedI1 subtopology_subtopology subtopology_topspace)
next
  assume ?rhs then show ?lhs
    using assms locally_compact_subspace_closed_Int_openin by blast
qed

lemma dense_locally_compact_openin_Hausdorff_space:
   "\<lbrakk>Hausdorff_space X; S \<subseteq> topspace X; X closure_of S = topspace X;
     locally_compact_space (subtopology X S)\<rbrakk> \<Longrightarrow> openin X S"
  by (metis locally_compact_subspace_openin_closure_of subtopology_topspace)

lemma locally_compact_space_prod_topology:
  "locally_compact_space (prod_topology X Y) \<longleftrightarrow>
        (prod_topology X Y) = trivial_topology \<or>
        locally_compact_space X \<and> locally_compact_space Y" (is "?lhs=?rhs")
proof (cases "(prod_topology X Y) = trivial_topology")
  case True
  then show ?thesis
    using locally_compact_space_discrete_topology by force
next
  case False
  then obtain w z where wz: "w \<in> topspace X" "z \<in> topspace Y"
    by fastforce
  show ?thesis 
  proof
    assume L: ?lhs then show ?rhs
      by (metis locally_compact_space_retraction_map_image prod_topology_trivial_iff retraction_map_fst retraction_map_snd)
  next
    assume R: ?rhs 
    show ?lhs
      unfolding locally_compact_space_def
    proof clarsimp
      fix x y
      assume "x \<in> topspace X" and "y \<in> topspace Y"
      obtain U C where "openin X U" "compactin X C" "x \<in> U" "U \<subseteq> C"
        by (meson False R \<open>x \<in> topspace X\<close> locally_compact_space_def)
      obtain V D where "openin Y V" "compactin Y D" "y \<in> V" "V \<subseteq> D"
        by (meson False R \<open>y \<in> topspace Y\<close> locally_compact_space_def)
      show "\<exists>U. openin (prod_topology X Y) U \<and> (\<exists>K. compactin (prod_topology X Y) K \<and> (x, y) \<in> U \<and> U \<subseteq> K)"
      proof (intro exI conjI)
        show "openin (prod_topology X Y) (U \<times> V)"
          by (simp add: \<open>openin X U\<close> \<open>openin Y V\<close> openin_prod_Times_iff)
        show "compactin (prod_topology X Y) (C \<times> D)"
          by (simp add: \<open>compactin X C\<close> \<open>compactin Y D\<close> compactin_Times)
        show "(x, y) \<in> U \<times> V"
          by (simp add: \<open>x \<in> U\<close> \<open>y \<in> V\<close>)
        show "U \<times> V \<subseteq> C \<times> D"
          by (simp add: Sigma_mono \<open>U \<subseteq> C\<close> \<open>V \<subseteq> D\<close>)
      qed
    qed
  qed
qed

lemma locally_compact_space_product_topology:
   "locally_compact_space(product_topology X I) \<longleftrightarrow>
        product_topology X I = trivial_topology \<or>
        finite {i \<in> I. \<not> compact_space(X i)} \<and> (\<forall>i \<in> I. locally_compact_space(X i))" (is "?lhs=?rhs")
proof (cases "(product_topology X I) = trivial_topology")
  case True
  then show ?thesis
    by (simp add: locally_compact_space_def)
next
  case False
  show ?thesis 
  proof
    assume L: ?lhs
    obtain z where z: "z \<in> topspace (product_topology X I)"
      using False
      by (meson ex_in_conv null_topspace_iff_trivial)
    with L z obtain U C where "openin (product_topology X I) U" "compactin (product_topology X I) C" "z \<in> U" "U \<subseteq> C"
      by (meson locally_compact_space_def)
    then obtain V where finV: "finite {i \<in> I. V i \<noteq> topspace (X i)}" and "\<forall>i \<in> I. openin (X i) (V i)" 
                    and "z \<in> PiE I V" "PiE I V \<subseteq> U"
      by (auto simp: openin_product_topology_alt)
    have "compact_space (X i)" if "i \<in> I" "V i = topspace (X i)" for i
    proof -
      have "compactin (X i) ((\<lambda>x. x i) ` C)"
        using \<open>compactin (product_topology X I) C\<close> image_compactin
        by (metis continuous_map_product_projection \<open>i \<in> I\<close>)
      moreover have "V i \<subseteq> (\<lambda>x. x i) ` C"
      proof -
        have "V i \<subseteq> (\<lambda>x. x i) ` Pi\<^sub>E I V"
          by (metis \<open>z \<in> Pi\<^sub>E I V\<close> empty_iff image_projection_PiE order_refl \<open>i \<in> I\<close>)
        also have "\<dots> \<subseteq> (\<lambda>x. x i) ` C"
          using \<open>U \<subseteq> C\<close> \<open>Pi\<^sub>E I V \<subseteq> U\<close> by blast
        finally show ?thesis .
      qed
      ultimately show ?thesis
        by (metis closed_compactin closedin_topspace compact_space_def that(2))
    qed
    with finV have "finite {i \<in> I. \<not> compact_space (X i)}"
      by (metis (mono_tags, lifting) mem_Collect_eq finite_subset subsetI)
    moreover have "locally_compact_space (X i)" if "i \<in> I" for i
      by (meson False L locally_compact_space_retraction_map_image retraction_map_product_projection that)
    ultimately show ?rhs by metis
  next
    assume R: ?rhs 
    show ?lhs
      unfolding locally_compact_space_def
    proof clarsimp
      fix z
      assume z: "z \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
      have "\<exists>U C. openin (X i) U \<and> compactin (X i) C \<and> z i \<in> U \<and> U \<subseteq> C \<and>
                    (compact_space(X i) \<longrightarrow> U = topspace(X i) \<and> C = topspace(X i))" 
        if "i \<in> I" for i
        using that R z unfolding locally_compact_space_def compact_space_def
        by (metis (no_types, lifting) False PiE_mem openin_topspace set_eq_subset)
      then obtain U C where UC: "\<And>i. i \<in> I \<Longrightarrow> 
             openin (X i) (U i) \<and> compactin (X i) (C i) \<and> z i \<in> U i \<and> U i \<subseteq> C i \<and>
                    (compact_space(X i) \<longrightarrow> U i = topspace(X i) \<and> C i = topspace(X i))"
        by metis
      show "\<exists>U. openin (product_topology X I) U \<and> (\<exists>K. compactin (product_topology X I) K \<and> z \<in> U \<and> U \<subseteq> K)"
      proof (intro exI conjI)
        show "openin (product_topology X I) (Pi\<^sub>E I U)"
        by (smt (verit) Collect_cong False R UC compactin_subspace openin_PiE_gen subset_antisym subtopology_topspace)
        show "compactin (product_topology X I) (Pi\<^sub>E I C)"
          by (simp add: UC compactin_PiE)
      qed (use UC z in blast)+
    qed
  qed
qed

lemma locally_compact_space_sum_topology:
   "locally_compact_space (sum_topology X I) \<longleftrightarrow> (\<forall>i \<in> I. locally_compact_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis closed_map_component_injection embedding_map_imp_homeomorphic_space embedding_map_component_injection
        embedding_imp_closed_map_eq homeomorphic_locally_compact_space locally_compact_space_closed_subset)
next
  assume R: ?rhs
  show ?lhs
    unfolding locally_compact_space_def
  proof clarsimp
    fix i y
    assume "i \<in> I" and y: "y \<in> topspace (X i)"
    then obtain U K where UK: "openin (X i) U" "compactin (X i) K" "y \<in> U" "U \<subseteq> K"
      using R by (fastforce simp: locally_compact_space_def)
    then show "\<exists>U. openin (sum_topology X I) U \<and> (\<exists>K. compactin (sum_topology X I) K \<and> (i, y) \<in> U \<and> U \<subseteq> K)"
      by (metis \<open>i \<in> I\<close> continuous_map_component_injection image_compactin image_mono 
          imageI open_map_component_injection open_map_def)
  qed
qed

lemma locally_compact_space_euclidean:
  "locally_compact_space (euclidean::'a::heine_borel topology)" 
  unfolding locally_compact_space_def
proof (intro strip)
  fix x::'a
  assume "x \<in> topspace euclidean"
  have "ball x 1 \<subseteq> cball x 1"
    by auto
  then show "\<exists>U K. openin euclidean U \<and> compactin euclidean K \<and> x \<in> U \<and> U \<subseteq> K"
    by (metis Elementary_Metric_Spaces.open_ball centre_in_ball compact_cball compactin_euclidean_iff open_openin zero_less_one)
qed

lemma locally_compact_Euclidean_space:
  "locally_compact_space(Euclidean_space n)"
  using homeomorphic_locally_compact_space [OF homeomorphic_Euclidean_space_product_topology] 
  using locally_compact_space_product_topology locally_compact_space_euclidean by fastforce

proposition quotient_map_prod_right:
  assumes loc: "locally_compact_space Z" 
    and reg: "Hausdorff_space Z \<or> regular_space Z" 
    and f: "quotient_map X Y f"
  shows "quotient_map (prod_topology Z X) (prod_topology Z Y) (\<lambda>(x,y). (x,f y))"
proof -
  define h where "h \<equiv> (\<lambda>(x::'a,y). (x,f y))"
  have "continuous_map (prod_topology Z X) Y (f o snd)"
    by (simp add: continuous_map_of_snd f quotient_imp_continuous_map)
  then have cmh: "continuous_map (prod_topology Z X) (prod_topology Z Y) h"
    by (simp add: h_def continuous_map_paired split_def continuous_map_fst o_def)
  have fim: "f ` topspace X = topspace Y"
    by (simp add: f quotient_imp_surjective_map)
  moreover
  have "openin (prod_topology Z X) {u \<in> topspace Z \<times> topspace X. h u \<in> W}
   \<longleftrightarrow> openin (prod_topology Z Y) W"   (is "?lhs=?rhs")
    if W: "W \<subseteq> topspace Z \<times> topspace Y" for W
  proof
    define S where "S \<equiv> {u \<in> topspace Z \<times> topspace X. h u \<in> W}"
    assume ?lhs 
    then have L: "openin (prod_topology Z X) S"
      using S_def by blast
    have "\<exists>T. openin (prod_topology Z Y) T \<and> (x0, z0) \<in> T \<and> T \<subseteq> W"
      if \<section>: "(x0,z0) \<in> W" for x0 z0 
    proof -
      have x0: "x0 \<in> topspace Z"
        using W that by blast
      obtain y0 where y0: "y0 \<in> topspace X" "f y0 = z0"
        by (metis W fim imageE insert_absorb insert_subset mem_Sigma_iff \<section>)
      then have "(x0, y0) \<in> S"
        by (simp add: S_def h_def that x0)
      have "continuous_map Z (prod_topology Z X) (\<lambda>x. (x, y0))"
        by (simp add: continuous_map_paired y0)
      with openin_continuous_map_preimage [OF _ L] 
      have ope_ZS: "openin Z {x \<in> topspace Z. (x,y0) \<in> S}"
        by blast
      obtain U U' where "openin Z U" "compactin Z U'" "closedin Z U'" 
        "x0 \<in> U"  "U \<subseteq> U'" "U' \<subseteq> {x \<in> topspace Z. (x,y0) \<in> S}"
        using loc ope_ZS x0 \<open>(x0, y0) \<in> S\<close>
        by (force simp: locally_compact_space_neighbourhood_base_closedin [OF reg] 
            neighbourhood_base_of)
      then have D: "U' \<times> {y0} \<subseteq> S"
        by (auto simp: )
      define V where "V \<equiv> {z \<in> topspace Y. U' \<times> {y \<in> topspace X. f y = z} \<subseteq> S}"
      have "z0 \<in> V"
        using D y0 Int_Collect fim by (fastforce simp: h_def V_def S_def)
      have "openin X {x \<in> topspace X. f x \<in> V} \<Longrightarrow> openin Y V"
        using f unfolding V_def quotient_map_def subset_iff
        by (smt (verit, del_insts) Collect_cong mem_Collect_eq)
      moreover have "openin X {x \<in> topspace X. f x \<in> V}"
      proof -
        let ?Z = "subtopology Z U'"
        have *: "{x \<in> topspace X. f x \<in> V} = topspace X - snd ` (U' \<times> topspace X - S)"
          by (force simp: V_def S_def h_def simp flip: fim)
        have "compact_space ?Z"
          using \<open>compactin Z U'\<close> compactin_subspace by auto
        moreover have "closedin (prod_topology ?Z X) (U' \<times> topspace X - S)"
          by (simp add: L \<open>closedin Z U'\<close> closedin_closed_subtopology closedin_diff closedin_prod_Times_iff 
              prod_topology_subtopology(1))
        ultimately show ?thesis
          using "*" closed_map_snd closed_map_def by fastforce
      qed
      ultimately have "openin Y V"
        by metis
      show ?thesis
      proof (intro conjI exI)
        show "openin (prod_topology Z Y) (U \<times> V)"
          by (simp add: openin_prod_Times_iff \<open>openin Z U\<close> \<open>openin Y V\<close>)
        show "(x0, z0) \<in> U \<times> V"
          by (simp add: \<open>x0 \<in> U\<close> \<open>z0 \<in> V\<close>)
        show "U \<times> V \<subseteq> W"
          using \<open>U \<subseteq> U'\<close> by (force simp: V_def S_def h_def simp flip: fim)
      qed
    qed
    with openin_subopen show ?rhs by force
  next
    assume ?rhs then show ?lhs
      using openin_continuous_map_preimage cmh by fastforce
  qed
  ultimately show ?thesis
    by (fastforce simp: image_iff quotient_map_def h_def)
qed

lemma quotient_map_prod_left:
  assumes loc: "locally_compact_space Z" 
    and reg: "Hausdorff_space Z \<or> regular_space Z" 
    and f: "quotient_map X Y f"
  shows "quotient_map (prod_topology X Z) (prod_topology Y Z) (\<lambda>(x,y). (f x,y))"
proof -
  have "(\<lambda>(x,y). (f x,y)) = prod.swap \<circ> (\<lambda>(x,y). (x,f y)) \<circ> prod.swap"
    by force
  then
  show ?thesis
    apply (rule ssubst)
  proof (intro quotient_map_compose)
    show "quotient_map (prod_topology X Z) (prod_topology Z X) prod.swap"
      "quotient_map (prod_topology Z Y) (prod_topology Y Z) prod.swap"
      using homeomorphic_map_def homeomorphic_map_swap quotient_map_eq by fastforce+
    show "quotient_map (prod_topology Z X) (prod_topology Z Y) (\<lambda>(x, y). (x, f y))"
      by (simp add: f loc quotient_map_prod_right reg)
  qed
qed

lemma locally_compact_space_perfect_map_preimage:
  assumes "locally_compact_space X'" and f: "perfect_map X X' f"
  shows "locally_compact_space X"
  unfolding locally_compact_space_def
proof (intro strip)
  fix x
  assume x: "x \<in> topspace X"
  then obtain U K where "openin X' U" "compactin X' K" "f x \<in> U" "U \<subseteq> K"
    using assms unfolding locally_compact_space_def perfect_map_def
    by (metis (no_types, lifting) continuous_map_closedin Pi_iff)
  show "\<exists>U K. openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"
  proof (intro exI conjI)
    have "continuous_map X X' f"
      using f perfect_map_def by blast
    then show "openin X {x \<in> topspace X. f x \<in> U}"
      by (simp add: \<open>openin X' U\<close> continuous_map)
    show "compactin X {x \<in> topspace X. f x \<in> K}"
      using \<open>compactin X' K\<close> f perfect_imp_proper_map proper_map_alt by blast
  qed (use x \<open>f x \<in> U\<close> \<open>U \<subseteq> K\<close> in auto)
qed


subsection\<open>Special characterizations of classes of functions into and out of R\<close>

lemma monotone_map_into_euclideanreal_alt:
  assumes "continuous_map X euclideanreal f" 
  shows "(\<forall>k. is_interval k \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> k}) \<longleftrightarrow>
         connected_space X \<and> monotone_map X euclideanreal f"  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof
    show "connected_space X"
      using L connected_space_subconnected by blast
    have "connectedin X {x \<in> topspace X. f x \<in> {y}}" for y
      by (metis L is_interval_1 nle_le singletonD)
    then show "monotone_map X euclideanreal f"
      by (simp add: monotone_map)
  qed
next
  assume R: ?rhs 
  then
  have *: False 
      if "a < b" "closedin X U" "closedin X V" "U \<noteq> {}" "V \<noteq> {}" "disjnt U V"
         and UV: "{x \<in> topspace X. f x \<in> {a..b}} = U \<union> V" 
         and dis: "disjnt U {x \<in> topspace X. f x = b}" "disjnt V {x \<in> topspace X. f x = a}" 
       for a b U V
  proof -
    define E1 where "E1 \<equiv> U \<union> {x \<in> topspace X. f x \<in> {c. c \<le> a}}"
    define E2 where "E2 \<equiv> V \<union> {x \<in> topspace X. f x \<in> {c. b \<le> c}}"
    have "closedin X {x \<in> topspace X. f x \<le> a}" "closedin X {x \<in> topspace X. b \<le> f x}"
      using assms continuous_map_upper_lower_semicontinuous_le by blast+
    then have "closedin X E1" "closedin X E2"
      unfolding E1_def E2_def using that by auto
    moreover
    have "E1 \<inter> E2 = {}"
      unfolding E1_def E2_def using \<open>a<b\<close> \<open>disjnt U V\<close> dis UV
      by (simp add: disjnt_def set_eq_iff) (smt (verit))
    have "topspace X \<subseteq> E1 \<union> E2"
      unfolding E1_def E2_def using UV by fastforce
    have "E1 = {} \<or> E2 = {}"
      using R connected_space_closedin
      using \<open>E1 \<inter> E2 = {}\<close> \<open>closedin X E1\<close> \<open>closedin X E2\<close> \<open>topspace X \<subseteq> E1 \<union> E2\<close> by blast
    then show False
      using E1_def E2_def \<open>U \<noteq> {}\<close> \<open>V \<noteq> {}\<close> by fastforce
  qed
  show ?lhs
  proof (intro strip)
    fix K :: "real set"
    assume "is_interval K"
    have False
      if "a \<in> K" "b \<in> K" and clo: "closedin X U" "closedin X V" 
         and UV: "{x. x \<in> topspace X \<and> f x \<in> K} \<subseteq> U \<union> V"
                 "U \<inter> V \<inter> {x. x \<in> topspace X \<and> f x \<in> K} = {}" 
         and nondis: "\<not> disjnt U {x. x \<in> topspace X \<and> f x = a}"
                     "\<not> disjnt V {x. x \<in> topspace X \<and> f x = b}" 
     for a b U V
    proof -
      have closedin_topspace: "closedin X {x \<in> topspace X. f x \<in> {y..z}}" for y z
        using closed_real_atLeastAtMost[unfolded closed_closedin]
          \<open>continuous_map X euclideanreal f\<close>[unfolded continuous_map_closedin]
        by blast

      have "\<forall>y. connectedin X {x. x \<in> topspace X \<and> f x = y}"
        using R monotone_map by fastforce
      then have **: False if "p \<in> U \<and> q \<in> V \<and> f p = f q \<and> f q \<in> K" for p q
        unfolding connectedin_closedin
        using \<open>a \<in> K\<close> \<open>b \<in> K\<close> UV clo that 
        by (smt (verit, ccfv_threshold) closedin_subset disjoint_iff mem_Collect_eq subset_iff)
      consider "a < b" | "a = b" | "b < a"
        by linarith
      then show ?thesis
      proof cases
        case 1
        define W where "W \<equiv> {x \<in> topspace X. f x \<in> {a..b}}"
        have "closedin X W"
          unfolding W_def
          using closedin_topspace .
        show ?thesis
        proof (rule * [OF 1 , of "U \<inter> W" "V \<inter> W"])
          show "closedin X (U \<inter> W)" "closedin X (V \<inter> W)"
            using \<open>closedin X W\<close> clo by auto
          show "U \<inter> W \<noteq> {}" "V \<inter> W \<noteq> {}"
            using nondis 1 by (auto simp: disjnt_iff W_def)
          show "disjnt (U \<inter> W) (V \<inter> W)"
            using \<open>is_interval K\<close> unfolding is_interval_1 disjnt_iff W_def
            by (metis (mono_tags, lifting) \<open>a \<in> K\<close> \<open>b \<in> K\<close> ** Int_Collect atLeastAtMost_iff)
          have "\<And>x. \<lbrakk>x \<in> topspace X; a \<le> f x; f x \<le> b\<rbrakk> \<Longrightarrow> x \<in> U \<or> x \<in> V"
            using \<open>a \<in> K\<close> \<open>b \<in> K\<close> \<open>is_interval K\<close> UV unfolding is_interval_1 disjnt_iff
            by blast
          then show "{x \<in> topspace X. f x \<in> {a..b}} = U \<inter> W \<union> V \<inter> W"
            by (auto simp: W_def)
          show "disjnt (U \<inter> W) {x \<in> topspace X. f x = b}" "disjnt (V \<inter> W) {x \<in> topspace X. f x = a}"
            using ** \<open>a \<in> K\<close> \<open>b \<in> K\<close> nondis by (force simp: disjnt_iff)+
        qed
      next
        case 2
        then show ?thesis
          using ** nondis \<open>b \<in> K\<close> by (force simp add: disjnt_iff)
      next
        case 3
        define W where "W \<equiv> {x \<in> topspace X. f x \<in> {b..a}}"
        have "closedin X W"
          unfolding W_def
          using closedin_topspace .
        show ?thesis
        proof (rule * [OF 3, of "V \<inter> W" "U \<inter> W"])
          show "closedin X (U \<inter> W)" "closedin X (V \<inter> W)"
            using \<open>closedin X W\<close> clo by auto
          show "U \<inter> W \<noteq> {}" "V \<inter> W \<noteq> {}"
            using nondis 3 by (auto simp: disjnt_iff W_def)
          show "disjnt (V \<inter> W) (U \<inter> W)"
            using \<open>is_interval K\<close> unfolding is_interval_1 disjnt_iff W_def
            by (metis (mono_tags, lifting) \<open>a \<in> K\<close> \<open>b \<in> K\<close> ** Int_Collect atLeastAtMost_iff)
          have "\<And>x. \<lbrakk>x \<in> topspace X; b \<le> f x; f x \<le> a\<rbrakk> \<Longrightarrow> x \<in> U \<or> x \<in> V"
            using \<open>a \<in> K\<close> \<open>b \<in> K\<close> \<open>is_interval K\<close> UV unfolding is_interval_1 disjnt_iff
            by blast
          then show "{x \<in> topspace X. f x \<in> {b..a}} = V \<inter> W \<union> U \<inter> W"
            by (auto simp: W_def)
          show "disjnt (V \<inter> W) {x \<in> topspace X. f x = a}" "disjnt (U \<inter> W) {x \<in> topspace X. f x = b}"
            using ** \<open>a \<in> K\<close> \<open>b \<in> K\<close> nondis by (force simp: disjnt_iff)+
        qed      
      qed
    qed
    then show "connectedin X {x \<in> topspace X. f x \<in> K}"
      unfolding connectedin_closedin disjnt_iff by blast
  qed
qed

lemma monotone_map_into_euclideanreal:
   "\<lbrakk>connected_space X; continuous_map X euclideanreal f\<rbrakk>
    \<Longrightarrow> monotone_map X euclideanreal f \<longleftrightarrow>
        (\<forall>k. is_interval k \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> k})"
  by (simp add: monotone_map_into_euclideanreal_alt)

lemma monotone_map_euclideanreal_alt:
   "(\<forall>I::real set. is_interval I \<longrightarrow> is_interval {x::real. x \<in> S \<and> f x \<in> I}) \<longleftrightarrow>
    is_interval S \<and> (mono_on S f \<or> antimono_on S f)" (is "?lhs=?rhs")
proof
  assume L [rule_format]: ?lhs 
  show ?rhs
  proof
    show "is_interval S"
      using L is_interval_1 by auto
    have False if "a \<in> S" "b \<in> S" "c \<in> S" "a<b" "b<c" and d: "f a < f b \<and> f c < f b \<or> f a > f b \<and> f c > f b" for a b c
      using d
    proof
      assume "f a < f b \<and> f c < f b"
      then show False
        using L [of "{y.  y < f b}"] unfolding is_interval_1
        by (smt (verit, best) mem_Collect_eq that)
    next
      assume "f b < f a \<and> f b < f c"
      then show False
        using L [of "{y.  y > f b}"] unfolding is_interval_1
        by (smt (verit, best) mem_Collect_eq that)
    qed
    then show "mono_on S f \<or> monotone_on S (\<le>) (\<ge>) f"
      unfolding monotone_on_def by (smt (verit))
  qed
next
  assume ?rhs then show ?lhs
    unfolding is_interval_1 monotone_on_def by simp meson
qed


lemma monotone_map_euclideanreal:
  fixes S :: "real set"
  shows
   "\<lbrakk>is_interval S; continuous_on S f\<rbrakk> \<Longrightarrow> 
    monotone_map (top_of_set S) euclideanreal f \<longleftrightarrow> (mono_on S f \<or> monotone_on S (\<le>) (\<ge>) f)"
  using monotone_map_euclideanreal_alt 
  by (simp add: monotone_map_into_euclideanreal connectedin_subtopology is_interval_connected_1)

lemma injective_eq_monotone_map:
  fixes f :: "real \<Rightarrow> real"
  assumes "is_interval S" "continuous_on S f"
  shows "inj_on f S \<longleftrightarrow> strict_mono_on S f \<or> strict_antimono_on S f"
  by (metis assms injective_imp_monotone_map monotone_map_euclideanreal strict_antimono_iff_antimono 
        strict_mono_iff_mono top_greatest topspace_euclidean topspace_euclidean_subtopology)


subsection\<open>Normal spaces\<close>

definition normal_space 
  where "normal_space X \<equiv>
        \<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T 
              \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V)"

lemma normal_space_retraction_map_image:
  assumes r: "retraction_map X Y r" and X: "normal_space X"
  shows "normal_space Y"
  unfolding normal_space_def
proof clarify
  fix S T
  assume "closedin Y S" and "closedin Y T" and "disjnt S T"
  obtain r' where r': "retraction_maps X Y r r'"
    using r retraction_map_def by blast
  have "closedin X {x \<in> topspace X. r x \<in> S}" "closedin X {x \<in> topspace X. r x \<in> T}"
    using closedin_continuous_map_preimage \<open>closedin Y S\<close> \<open>closedin Y T\<close> r'
    by (auto simp: retraction_maps_def)
  moreover
  have "disjnt {x \<in> topspace X. r x \<in> S} {x \<in> topspace X. r x \<in> T}"
    using \<open>disjnt S T\<close> by (auto simp: disjnt_def)
  ultimately
  obtain U V where UV: "openin X U \<and> openin X V \<and> {x \<in> topspace X. r x \<in> S} \<subseteq> U \<and> {x \<in> topspace X. r x \<in> T} \<subseteq> V" "disjnt U V"
    by (meson X normal_space_def)
  show "\<exists>U V. openin Y U \<and> openin Y V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  proof (intro exI conjI)
    show "openin Y {x \<in> topspace Y. r' x \<in> U}" "openin Y {x \<in> topspace Y. r' x \<in> V}"
      using openin_continuous_map_preimage UV r'
      by (auto simp: retraction_maps_def)
    show "S \<subseteq> {x \<in> topspace Y. r' x \<in> U}" "T \<subseteq> {x \<in> topspace Y. r' x \<in> V}"
      using openin_continuous_map_preimage UV r' \<open>closedin Y S\<close> \<open>closedin Y T\<close> 
      by (auto simp add: closedin_def continuous_map_closedin retraction_maps_def subset_iff Pi_iff)
    show "disjnt {x \<in> topspace Y. r' x \<in> U} {x \<in> topspace Y. r' x \<in> V}"
      using \<open>disjnt U V\<close> by (auto simp: disjnt_def)
  qed
qed

lemma homeomorphic_normal_space:
   "X homeomorphic_space Y \<Longrightarrow> normal_space X \<longleftrightarrow> normal_space Y"
  unfolding homeomorphic_space_def
  by (meson homeomorphic_imp_retraction_maps homeomorphic_maps_sym normal_space_retraction_map_image retraction_map_def)

lemma normal_space:
  "normal_space X \<longleftrightarrow>
    (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
          \<longrightarrow> (\<exists>U. openin X U \<and> S \<subseteq> U \<and> disjnt T (X closure_of U)))"
proof -
  have "(\<exists>V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V) \<longleftrightarrow> openin X U \<and> S \<subseteq> U \<and> disjnt T (X closure_of U)"
    (is "?lhs=?rhs")
    if "closedin X S" "closedin X T" "disjnt S T" for S T U
  proof
    show "?lhs \<Longrightarrow> ?rhs"
      by (smt (verit, best) disjnt_iff in_closure_of subsetD)
    assume R: ?rhs
    then have "(U \<union> S) \<inter> (topspace X - X closure_of U) = {}"
      by (metis Diff_eq_empty_iff Int_Diff Int_Un_eq(4) closure_of_subset inf.orderE openin_subset)
    moreover have "T \<subseteq> topspace X - X closure_of U"
      by (meson DiffI R closedin_subset disjnt_iff subsetD subsetI that(2))
    ultimately show ?lhs
      by (metis R closedin_closure_of closedin_def disjnt_def sup.orderE)
  qed
  then show ?thesis
    unfolding normal_space_def by meson
qed

lemma normal_space_alt:
   "normal_space X \<longleftrightarrow>
    (\<forall>S U. closedin X S \<and> openin X U \<and> S \<subseteq> U \<longrightarrow> (\<exists>V. openin X V \<and> S \<subseteq> V \<and> X closure_of V \<subseteq> U))"
proof -
  have "\<exists>V. openin X V \<and> S \<subseteq> V \<and> X closure_of V \<subseteq> U"
    if "\<And>T. closedin X T \<longrightarrow> disjnt S T \<longrightarrow> (\<exists>U. openin X U \<and> S \<subseteq> U \<and> disjnt T (X closure_of U))"
       "closedin X S" "openin X U" "S \<subseteq> U"
    for S U
    using that 
    by (smt (verit) Diff_eq_empty_iff Int_Diff closure_of_subset_topspace disjnt_def inf.orderE inf_commute openin_closedin_eq)
  moreover have "\<exists>U. openin X U \<and> S \<subseteq> U \<and> disjnt T (X closure_of U)"
    if "\<And>U. openin X U \<and> S \<subseteq> U \<longrightarrow> (\<exists>V. openin X V \<and> S \<subseteq> V \<and> X closure_of V \<subseteq> U)"
      and "closedin X S" "closedin X T" "disjnt S T"
    for S T
    using that   
    by (smt (verit) Diff_Diff_Int Diff_eq_empty_iff Int_Diff closedin_def disjnt_def inf.absorb_iff2 inf.orderE)
  ultimately show ?thesis
    by (fastforce simp: normal_space)
qed

lemma normal_space_closures:
   "normal_space X \<longleftrightarrow>
    (\<forall>S T. S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and>
              disjnt (X closure_of S) (X closure_of T)
              \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))" 
   (is "?lhs=?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (meson closedin_closure_of closure_of_subset normal_space_def order.trans)
  show "?rhs \<Longrightarrow> ?lhs"
    by (metis closedin_subset closure_of_eq normal_space_def)
qed

lemma normal_space_disjoint_closures:
   "normal_space X \<longleftrightarrow>
    (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
          \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and>
                    disjnt (X closure_of U) (X closure_of V)))"
   (is "?lhs=?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis closedin_closure_of normal_space)
  show "?rhs \<Longrightarrow> ?lhs"
    by (smt (verit) closure_of_subset disjnt_iff normal_space openin_subset subset_eq)
qed

lemma normal_space_dual:
   "normal_space X \<longleftrightarrow>
    (\<forall>U V. openin X U \<longrightarrow> openin X V \<and> U \<union> V = topspace X
          \<longrightarrow> (\<exists>S T. closedin X S \<and> closedin X T \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> S \<union> T = topspace X))"
   (is "_ = ?rhs")
proof -
  have "normal_space X \<longleftrightarrow>
        (\<forall>U V. closedin X U \<longrightarrow> closedin X V \<longrightarrow> disjnt U V \<longrightarrow>
              (\<exists>S T. \<not> (openin X S \<and> openin X T \<longrightarrow>
                         \<not> (U \<subseteq> S \<and> V \<subseteq> T \<and> disjnt S T))))"
    unfolding normal_space_def by meson
  also have "... \<longleftrightarrow> (\<forall>U V. openin X U \<longrightarrow> openin X V \<and> disjnt (topspace X - U) (topspace X - V) \<longrightarrow>
              (\<exists>S T. \<not> (openin X S \<and> openin X T \<longrightarrow>
                         \<not> (topspace X - U \<subseteq> S \<and> topspace X - V \<subseteq> T \<and> disjnt S T))))"
    by (auto simp: all_closedin)
  also have "... \<longleftrightarrow> ?rhs"
  proof -
    have *: "disjnt (topspace X - U) (topspace X - V) \<longleftrightarrow> U \<union> V = topspace X"
      if "U \<subseteq> topspace X" "V \<subseteq> topspace X" for U V
      using that by (auto simp: disjnt_iff)
    show ?thesis
      using ex_closedin *
      apply (simp add: ex_closedin * [OF openin_subset openin_subset] cong: conj_cong)
      apply (intro all_cong1 ex_cong1 imp_cong refl)
      by (smt (verit, best) "*" Diff_Diff_Int Diff_subset Diff_subset_conv inf.orderE inf_commute openin_subset sup_commute)
  qed
  finally show ?thesis .
qed


lemma normal_t1_imp_Hausdorff_space:
  assumes "normal_space X" "t1_space X"
  shows "Hausdorff_space X"
  unfolding Hausdorff_space_def
proof clarify
  fix x y
  assume xy: "x \<in> topspace X" "y \<in> topspace X" "x \<noteq> y"
  then have "disjnt {x} {y}"
    by (auto simp: disjnt_iff)
  then show "\<exists>U V. openin X U \<and> openin X V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
    using assms xy closedin_t1_singleton normal_space_def
    by (metis singletonI subsetD)
qed

lemma normal_t1_eq_Hausdorff_space:
   "normal_space X \<Longrightarrow> t1_space X \<longleftrightarrow> Hausdorff_space X"
  using normal_t1_imp_Hausdorff_space t1_or_Hausdorff_space by blast

lemma normal_t1_imp_regular_space:
   "\<lbrakk>normal_space X; t1_space X\<rbrakk> \<Longrightarrow> regular_space X"
  by (metis compactin_imp_closedin normal_space_def normal_t1_eq_Hausdorff_space regular_space_compact_closed_sets)

lemma compact_Hausdorff_or_regular_imp_normal_space:
   "\<lbrakk>compact_space X; Hausdorff_space X \<or> regular_space X\<rbrakk>
        \<Longrightarrow> normal_space X"
  by (metis Hausdorff_space_compact_sets closedin_compact_space normal_space_def regular_space_compact_closed_sets)

lemma normal_space_discrete_topology:
   "normal_space(discrete_topology U)"
  by (metis discrete_topology_closure_of inf_le2 normal_space_alt)

lemma normal_space_fsigmas:
  "normal_space X \<longleftrightarrow>
    (\<forall>S T. fsigma_in X S \<and> fsigma_in X T \<and> separatedin X S T
           \<longrightarrow> (\<exists>U B. openin X U \<and> openin X B \<and> S \<subseteq> U \<and> T \<subseteq> B \<and> disjnt U B))" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix S T
    assume "fsigma_in X S" 
    then obtain C where C: "\<And>n. closedin X (C n)" "\<And>n. C n \<subseteq> C (Suc n)" "\<Union> (range C) = S"
      by (meson fsigma_in_ascending)
    assume "fsigma_in X T" 
    then obtain D where D: "\<And>n. closedin X (D n)" "\<And>n. D n \<subseteq> D (Suc n)" "\<Union> (range D) = T"
      by (meson fsigma_in_ascending)
    assume "separatedin X S T"
    have "\<And>n. disjnt (D n) (X closure_of S)"
      by (metis D(3) \<open>separatedin X S T\<close> disjnt_Union1 disjnt_def rangeI separatedin_def)
    then have "\<And>n. \<exists>V V'. openin X V \<and> openin X V' \<and> D n \<subseteq> V \<and> X closure_of S \<subseteq> V' \<and> disjnt V V'"
      by (metis D(1) L closedin_closure_of normal_space_def)
    then obtain V V' where V: "\<And>n. openin X (V n)" and "\<And>n. openin X (V' n)" "\<And>n. disjnt (V n) (V' n)"
          and DV:  "\<And>n. D n \<subseteq> V n" 
          and subV': "\<And>n. X closure_of S \<subseteq> V' n"
      by metis
    then have VV: "V' n \<inter> X closure_of V n = {}" for n
      using openin_Int_closure_of_eq_empty [of X "V' n" "V n"] by (simp add: Int_commute disjnt_def)
    have "\<And>n. disjnt (C n) (X closure_of T)"
      by (metis C(3) \<open>separatedin X S T\<close> disjnt_Union1 disjnt_def rangeI separatedin_def)
    then have "\<And>n. \<exists>U U'. openin X U \<and> openin X U' \<and> C n \<subseteq> U \<and> X closure_of T \<subseteq> U' \<and> disjnt U U'"
      by (metis C(1) L closedin_closure_of normal_space_def)
    then obtain U U' where U: "\<And>n. openin X (U n)" and "\<And>n. openin X (U' n)" "\<And>n. disjnt (U n) (U' n)"
          and CU:  "\<And>n. C n \<subseteq> U n" 
          and subU': "\<And>n. X closure_of T \<subseteq> U' n"
      by metis
    then have UU: "U' n \<inter> X closure_of U n = {}" for n
      using openin_Int_closure_of_eq_empty [of X "U' n" "U n"] by (simp add: Int_commute disjnt_def)
    show "\<exists>U B. openin X U \<and> openin X B \<and> S \<subseteq> U \<and> T \<subseteq> B \<and> disjnt U B"
    proof (intro conjI exI)
      have "\<And>S n. closedin X (\<Union>m\<le>n. X closure_of V m)"
        by (force intro: closedin_Union)
      then show "openin X (\<Union>n. U n - (\<Union>m\<le>n. X closure_of V m))"
        using U by blast
      have "\<And>S n. closedin X (\<Union>m\<le>n. X closure_of U m)"
        by (force intro: closedin_Union)
      then show "openin X (\<Union>n. V n - (\<Union>m\<le>n. X closure_of U m))"
        using V by blast
      have "S \<subseteq> topspace X"
        by (simp add: \<open>fsigma_in X S\<close> fsigma_in_subset)
      then show "S \<subseteq> (\<Union>n. U n - (\<Union>m\<le>n. X closure_of V m))"
        apply (clarsimp simp: Ball_def)
        by (metis VV C(3) CU IntI UN_E closure_of_subset empty_iff subV' subsetD)
      have "T \<subseteq> topspace X"
        by (simp add: \<open>fsigma_in X T\<close> fsigma_in_subset)
      then show "T \<subseteq> (\<Union>n. V n - (\<Union>m\<le>n. X closure_of U m))"
        apply (clarsimp simp: Ball_def)
        by (metis UU D(3) DV IntI UN_E closure_of_subset empty_iff subU' subsetD)
      have "\<And>x m n. \<lbrakk>x \<in> U n; x \<in> V m; \<forall>k\<le>m. x \<notin> X closure_of U k\<rbrakk> \<Longrightarrow> \<exists>k\<le>n. x \<in> X closure_of V k"
        by (meson U V closure_of_subset nat_le_linear openin_subset subsetD)
      then show "disjnt (\<Union>n. U n - (\<Union>m\<le>n. X closure_of V m)) (\<Union>n. V n - (\<Union>m\<le>n. X closure_of U m))"
        by (force simp: disjnt_iff)
    qed
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: closed_imp_fsigma_in normal_space_def separatedin_closed_sets)
qed

lemma normal_space_fsigma_subtopology:
  assumes "normal_space X" "fsigma_in X S"
  shows "normal_space (subtopology X S)"
  unfolding normal_space_fsigmas
proof clarify
  fix T U
  assume "fsigma_in (subtopology X S) T"
      and "fsigma_in (subtopology X S) U"
      and TU: "separatedin (subtopology X S) T U"
  then obtain A B where "openin X A \<and> openin X B \<and> T \<subseteq> A \<and> U \<subseteq> B \<and> disjnt A B"
    by (metis assms fsigma_in_fsigma_subtopology normal_space_fsigmas separatedin_subtopology)
  then
  show "\<exists>A B. openin (subtopology X S) A \<and> openin (subtopology X S) B \<and> T \<subseteq> A \<and>
   U \<subseteq> B \<and> disjnt A B"
    using TU
    by (force simp add: separatedin_subtopology openin_subtopology_alt disjnt_iff)
qed

lemma normal_space_closed_subtopology:
  assumes "normal_space X" "closedin X S"
  shows "normal_space (subtopology X S)"
  by (simp add: assms closed_imp_fsigma_in normal_space_fsigma_subtopology)

lemma normal_space_continuous_closed_map_image:
  assumes "normal_space X" and contf: "continuous_map X Y f" 
    and clof: "closed_map X Y f"  and fim: "f ` topspace X = topspace Y"
shows "normal_space Y"
  unfolding normal_space_def
proof clarify
  fix S T
  assume "closedin Y S" and "closedin Y T" and "disjnt S T"
  have "closedin X {x \<in> topspace X. f x \<in> S}" "closedin X {x \<in> topspace X. f x \<in> T}"
    using \<open>closedin Y S\<close> \<open>closedin Y T\<close> closedin_continuous_map_preimage contf by auto
  moreover
  have "disjnt {x \<in> topspace X. f x \<in> S} {x \<in> topspace X. f x \<in> T}"
    using \<open>disjnt S T\<close> by (auto simp: disjnt_iff)
  ultimately
  obtain U V where "closedin X U" "closedin X V" 
    and subXU: "{x \<in> topspace X. f x \<in> S} \<subseteq> topspace X - U" 
    and subXV: "{x \<in> topspace X. f x \<in> T} \<subseteq> topspace X - V" 
    and dis: "disjnt (topspace X - U) (topspace X -V)"
    using \<open>normal_space X\<close> by (force simp add: normal_space_def ex_openin)
  have "closedin Y (f ` U)" "closedin Y (f ` V)"
    using \<open>closedin X U\<close> \<open>closedin X V\<close> clof closed_map_def by blast+
  moreover have "S \<subseteq> topspace Y - f ` U"
    using \<open>closedin Y S\<close> \<open>closedin X U\<close> subXU by (force dest: closedin_subset)
  moreover have "T \<subseteq> topspace Y - f ` V"
    using \<open>closedin Y T\<close> \<open>closedin X V\<close> subXV by (force dest: closedin_subset)
  moreover have "disjnt (topspace Y - f ` U) (topspace Y - f ` V)"
    using fim dis by (force simp add: disjnt_iff)
  ultimately show "\<exists>U V. openin Y U \<and> openin Y V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
    by (force simp add: ex_openin)
qed


subsection \<open>Hereditary topological properties\<close>

definition hereditarily 
  where "hereditarily P X \<equiv>
        \<forall>S. S \<subseteq> topspace X \<longrightarrow> P(subtopology X S)"

lemma hereditarily:
   "hereditarily P X \<longleftrightarrow> (\<forall>S. P(subtopology X S))"
  by (metis Int_lower1 hereditarily_def subtopology_restrict)

lemma hereditarily_mono:
   "\<lbrakk>hereditarily P X; \<And>x. P x \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> hereditarily Q X"
  by (simp add: hereditarily)

lemma hereditarily_inc:
   "hereditarily P X \<Longrightarrow> P X"
  by (metis hereditarily subtopology_topspace)

lemma hereditarily_subtopology:
   "hereditarily P X \<Longrightarrow> hereditarily P (subtopology X S)"
  by (simp add: hereditarily subtopology_subtopology)

lemma hereditarily_normal_space_continuous_closed_map_image:
  assumes X: "hereditarily normal_space X" and contf: "continuous_map X Y f" 
    and clof: "closed_map X Y f"  and fim: "f ` (topspace X) = topspace Y" 
  shows "hereditarily normal_space Y"
  unfolding hereditarily_def
proof (intro strip)
  fix T
  assume "T \<subseteq> topspace Y"
  then have nx: "normal_space (subtopology X {x \<in> topspace X. f x \<in> T})"
    by (meson X hereditarily)
  moreover have "continuous_map (subtopology X {x \<in> topspace X. f x \<in> T}) (subtopology Y T) f"
    by (simp add: contf continuous_map_from_subtopology continuous_map_in_subtopology image_subset_iff)
  moreover have "closed_map (subtopology X {x \<in> topspace X. f x \<in> T}) (subtopology Y T) f"
    by (simp add: clof closed_map_restriction)
  ultimately show "normal_space (subtopology Y T)"
    using fim normal_space_continuous_closed_map_image by fastforce
qed

lemma homeomorphic_hereditarily_normal_space:
   "X homeomorphic_space Y
      \<Longrightarrow> (hereditarily normal_space X \<longleftrightarrow> hereditarily normal_space Y)"
  by (meson hereditarily_normal_space_continuous_closed_map_image homeomorphic_eq_everything_map 
      homeomorphic_space homeomorphic_space_sym)

lemma hereditarily_normal_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; hereditarily normal_space X\<rbrakk> \<Longrightarrow> hereditarily normal_space Y"
  by (smt (verit) hereditarily_subtopology hereditary_imp_retractive_property homeomorphic_hereditarily_normal_space)

subsection\<open>Limits in a topological space\<close>

lemma limitin_const_iff:
  assumes "t1_space X" "\<not> trivial_limit F"
  shows "limitin X (\<lambda>k. a) l F \<longleftrightarrow> l \<in> topspace X \<and> a = l"  (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    using assms unfolding limitin_def t1_space_def by (metis eventually_const openin_topspace)
next
  assume ?rhs then show ?lhs
    using assms by (auto simp: limitin_def t1_space_def)
qed

lemma compactin_sequence_with_limit:
  assumes lim: "limitin X \<sigma> l sequentially" and "S \<subseteq> range \<sigma>" and SX: "S \<subseteq> topspace X"
  shows "compactin X (insert l S)"
unfolding compactin_def
proof (intro conjI strip)
  show "insert l S \<subseteq> topspace X"
    by (meson SX insert_subset lim limitin_topspace)
  fix \<U>
  assume \<section>: "Ball \<U> (openin X) \<and> insert l S \<subseteq> \<Union> \<U>"
  have "\<exists>V. finite V \<and> V \<subseteq> \<U> \<and> (\<exists>t \<in> V. l \<in> t) \<and> S \<subseteq> \<Union> V"
    if *: "\<forall>x \<in> S. \<exists>T \<in> \<U>. x \<in> T" and "T \<in> \<U>" "l \<in> T" for T
  proof -
    obtain V where V: "\<And>x. x \<in> S \<Longrightarrow> V x \<in> \<U> \<and> x \<in> V x"
      using * by metis
    obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> \<sigma> n \<in> T"
      by (meson "\<section>" \<open>T \<in> \<U>\<close> \<open>l \<in> T\<close> lim limitin_sequentially)
    show ?thesis
    proof (intro conjI exI)
      have "x \<in> T"
        if "x \<in> S" and "\<forall>A. (\<forall>x \<in> S. (\<forall>n\<le>N. x \<noteq> \<sigma> n) \<or> A \<noteq> V x) \<or> x \<notin> A" for x 
        by (metis (no_types) N V that assms(2) imageE nle_le subsetD)
      then show "S \<subseteq> \<Union> (insert T (V ` (S \<inter> \<sigma> ` {0..N})))"
        by force
    qed (use V that in auto)
  qed
  then show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> insert l S \<subseteq> \<Union> \<F>"
    by (smt (verit, best) Union_iff \<section> insert_subset subsetD)
qed

lemma limitin_Hausdorff_unique:
  assumes "limitin X f l1 F" "limitin X f l2 F" "\<not> trivial_limit F" "Hausdorff_space X"
  shows "l1 = l2"
proof (rule ccontr)
  assume "l1 \<noteq> l2"
  with assms obtain U V where "openin X U" "openin X V" "l1 \<in> U" "l2 \<in> V" "disjnt U V"
    by (metis Hausdorff_space_def limitin_topspace)
  then have "eventually (\<lambda>x. f x \<in> U) F" "eventually (\<lambda>x. f x \<in> V) F"
    using assms by (fastforce simp: limitin_def)+
  then have "\<exists>x. f x \<in> U \<and> f x \<in> V"
    using assms eventually_elim2 filter_eq_iff by fastforce
  with assms \<open>disjnt U V\<close> show False
    by (meson disjnt_iff)
qed

lemma limitin_kc_unique:
  assumes "kc_space X" and lim1: "limitin X f l1 sequentially" and lim2: "limitin X f l2 sequentially"
  shows "l1 = l2"
proof (rule ccontr)
  assume "l1 \<noteq> l2"
  define A where "A \<equiv> insert l1 (range f - {l2})"
  have "l1 \<in> topspace X"
    using lim1 limitin_def by fastforce
  moreover have "compactin X (insert l1 (topspace X \<inter> (range f - {l2})))"
    by (meson Diff_subset compactin_sequence_with_limit inf_le1 inf_le2 lim1 subset_trans)
  ultimately have "compactin X (topspace X \<inter> A)"
    by (simp add: A_def)
  then have OXA: "openin X (topspace X - A)"
    by (metis Diff_Diff_Int Diff_subset \<open>kc_space X\<close> kc_space_def openin_closedin_eq)
  have "l2 \<in> topspace X - A"
    using \<open>l1 \<noteq> l2\<close> A_def lim2 limitin_topspace by fastforce
  then have "\<forall>\<^sub>F x in sequentially. f x = l2"
    using limitinD [OF lim2 OXA] by (auto simp: A_def eventually_conj_iff)
  then show False
    using limitin_transform_eventually [OF _ lim1] 
          limitin_const_iff [OF kc_imp_t1_space trivial_limit_sequentially]
    using \<open>l1 \<noteq> l2\<close> \<open>kc_space X\<close> by fastforce
qed

lemma limitin_closedin:
  assumes lim: "limitin X f l F" 
    and "closedin X S" and ev: "eventually (\<lambda>x. f x \<in> S) F" "\<not> trivial_limit F"
  shows "l \<in> S"
proof (rule ccontr)
  assume "l \<notin> S"
  have "\<forall>\<^sub>F x in F. f x \<in> topspace X - S"
    by (metis Diff_iff \<open>l \<notin> S\<close> \<open>closedin X S\<close> closedin_def lim limitin_def)
  with ev eventually_elim2 trivial_limit_def show False
    by force
qed

subsection\<open>Quasi-components\<close>

definition quasi_component_of :: "'a topology \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
  "quasi_component_of X x y \<equiv>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        (\<forall>T. closedin X T \<and> openin X T \<longrightarrow> (x \<in> T \<longleftrightarrow> y \<in> T))"

abbreviation "quasi_component_of_set S x \<equiv> Collect (quasi_component_of S x)"

definition quasi_components_of :: "'a topology \<Rightarrow> ('a set) set"
  where
  "quasi_components_of X = quasi_component_of_set X ` topspace X"

lemma quasi_component_in_topspace:
   "quasi_component_of X x y \<Longrightarrow> x \<in> topspace X \<and> y \<in> topspace X"
  by (simp add: quasi_component_of_def)

lemma quasi_component_of_refl [simp]:
   "quasi_component_of X x x \<longleftrightarrow> x \<in> topspace X"
  by (simp add: quasi_component_of_def)

lemma quasi_component_of_sym:
   "quasi_component_of X x y \<longleftrightarrow> quasi_component_of X y x"
  by (meson quasi_component_of_def)

lemma quasi_component_of_trans:
   "\<lbrakk>quasi_component_of X x y; quasi_component_of X y z\<rbrakk> \<Longrightarrow> quasi_component_of X x z"
  by (simp add: quasi_component_of_def)

lemma quasi_component_of_subset_topspace:
   "quasi_component_of_set X x \<subseteq> topspace X"
  using quasi_component_of_def by fastforce

lemma quasi_component_of_eq_empty:
   "quasi_component_of_set X x = {} \<longleftrightarrow> (x \<notin> topspace X)"
  using quasi_component_of_def by fastforce

lemma quasi_component_of:
   "quasi_component_of X x y \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> (\<forall>T. x \<in> T \<and> closedin X T \<and> openin X T \<longrightarrow> y \<in> T)"
  unfolding quasi_component_of_def by (metis Diff_iff closedin_def openin_closedin_eq) 

lemma quasi_component_of_alt:
  "quasi_component_of X x y \<longleftrightarrow>
      x \<in> topspace X \<and> y \<in> topspace X \<and>
      \<not> (\<exists>U V. openin X U \<and> openin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> x \<in> U \<and> y \<in> V)" 
  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding quasi_component_of_def
    by (metis disjnt_iff separatedin_full separatedin_open_sets)
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding quasi_component_of_def
    by (metis Diff_disjoint Diff_iff Un_Diff_cancel closedin_def disjnt_def inf_commute sup.orderE sup_commute)
qed

lemma quasi_components_lepoll_topspace: "quasi_components_of X \<lesssim> topspace X"
  by (simp add: image_lepoll quasi_components_of_def)

lemma quasi_component_of_separated:
   "quasi_component_of X x y \<longleftrightarrow>
     x \<in> topspace X \<and> y \<in> topspace X \<and>
     \<not> (\<exists>U V. separatedin X U V \<and> U \<union> V = topspace X \<and> x \<in> U \<and> y \<in> V)"
  by (meson quasi_component_of_alt separatedin_full separatedin_open_sets)

lemma quasi_component_of_subtopology:
  "quasi_component_of (subtopology X s) x y \<Longrightarrow> quasi_component_of X x y"
  unfolding quasi_component_of_def
  by (simp add: closedin_subtopology) (metis Int_iff inf_commute openin_subtopology_Int2)

lemma quasi_component_of_mono:
   "quasi_component_of (subtopology X S) x y \<and> S \<subseteq> T
        \<Longrightarrow> quasi_component_of (subtopology X T) x y"
  by (metis inf.absorb_iff2 quasi_component_of_subtopology subtopology_subtopology)

lemma quasi_component_of_equiv:
   "quasi_component_of X x y \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> quasi_component_of X x = quasi_component_of X y"
  using quasi_component_of_def by fastforce

lemma quasi_component_of_disjoint [simp]:
   "disjnt (quasi_component_of_set X x) (quasi_component_of_set X y) \<longleftrightarrow> \<not> (quasi_component_of X x y)"
  by (metis disjnt_iff quasi_component_of_equiv mem_Collect_eq)

lemma quasi_component_of_eq:
   "quasi_component_of X x = quasi_component_of X y \<longleftrightarrow>
    (x \<notin> topspace X \<and> y \<notin> topspace X) 
  \<or> x \<in> topspace X \<and> y \<in> topspace X \<and> quasi_component_of X x y"
  by (metis Collect_empty_eq_bot quasi_component_of_eq_empty quasi_component_of_equiv)

lemma topspace_imp_quasi_components_of:
  assumes "x \<in> topspace X"
  obtains C where "C \<in> quasi_components_of X" "x \<in> C"
  by (metis assms imageI mem_Collect_eq quasi_component_of_refl quasi_components_of_def)

lemma Union_quasi_components_of: "\<Union> (quasi_components_of X) = topspace X"
  by (auto simp: quasi_components_of_def quasi_component_of_def)

lemma pairwise_disjoint_quasi_components_of:
   "pairwise disjnt (quasi_components_of X)"
  by (auto simp: quasi_components_of_def quasi_component_of_def disjoint_def)

lemma complement_quasi_components_of_Union:
  assumes "C \<in> quasi_components_of X"
  shows "topspace X - C = \<Union> (quasi_components_of X - {C})"  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using Union_quasi_components_of by fastforce
  show "?rhs \<subseteq> ?lhs"
    using assms
    using quasi_component_of_equiv by (fastforce simp add: quasi_components_of_def image_iff subset_iff)
qed

lemma nonempty_quasi_components_of:
   "C \<in> quasi_components_of X \<Longrightarrow> C \<noteq> {}"
  by (metis imageE quasi_component_of_eq_empty quasi_components_of_def)

lemma quasi_components_of_subset:
   "C \<in> quasi_components_of X \<Longrightarrow> C \<subseteq> topspace X"
  using Union_quasi_components_of by force

lemma quasi_component_in_quasi_components_of:
   "quasi_component_of_set X a \<in> quasi_components_of X \<longleftrightarrow> a \<in> topspace X"
  by (metis (no_types, lifting) image_iff quasi_component_of_eq_empty quasi_components_of_def)

lemma quasi_components_of_eq_empty [simp]:
   "quasi_components_of X = {} \<longleftrightarrow> X = trivial_topology"
  by (simp add: quasi_components_of_def)

lemma quasi_components_of_empty_space [simp]:
   "quasi_components_of trivial_topology = {}"
  by simp

lemma quasi_component_of_set:
   "quasi_component_of_set X x =
        (if x \<in> topspace X
        then \<Inter> {t. closedin X t \<and> openin X t \<and> x \<in> t}
        else {})"
  by (auto simp: quasi_component_of)

lemma closedin_quasi_component_of: "closedin X (quasi_component_of_set X x)"
  by (auto simp: quasi_component_of_set)

lemma closedin_quasi_components_of:
   "C \<in> quasi_components_of X \<Longrightarrow> closedin X C"
  by (auto simp: quasi_components_of_def closedin_quasi_component_of)

lemma openin_finite_quasi_components:
  "\<lbrakk>finite(quasi_components_of X); C \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> openin X C"
  apply (simp add:openin_closedin_eq quasi_components_of_subset complement_quasi_components_of_Union)
  by (meson DiffD1 closedin_Union closedin_quasi_components_of finite_Diff)

lemma quasi_component_of_eq_overlap:
   "quasi_component_of X x = quasi_component_of X y \<longleftrightarrow>
      (x \<notin> topspace X \<and> y \<notin> topspace X) \<or>
      \<not> (quasi_component_of_set X x \<inter> quasi_component_of_set X y = {})"
  using quasi_component_of_equiv by fastforce

lemma quasi_component_of_nonoverlap:
   "quasi_component_of_set X x \<inter> quasi_component_of_set X y = {} \<longleftrightarrow>
     (x \<notin> topspace X) \<or> (y \<notin> topspace X) \<or>
     \<not> (quasi_component_of X x = quasi_component_of X y)"
  by (metis inf.idem quasi_component_of_eq_empty quasi_component_of_eq_overlap)

lemma quasi_component_of_overlap:
   "\<not> (quasi_component_of_set X x \<inter> quasi_component_of_set X y = {}) \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> quasi_component_of X x = quasi_component_of X y"
  by (meson quasi_component_of_nonoverlap)

lemma quasi_components_of_disjoint:
   "\<lbrakk>C \<in> quasi_components_of X; D \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> disjnt C D \<longleftrightarrow> C \<noteq> D"
  by (metis disjnt_self_iff_empty nonempty_quasi_components_of pairwiseD pairwise_disjoint_quasi_components_of)

lemma quasi_components_of_overlap:
   "\<lbrakk>C \<in> quasi_components_of X; D \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> \<not> (C \<inter> D = {}) \<longleftrightarrow> C = D"
  by (metis disjnt_def quasi_components_of_disjoint)

lemma pairwise_separated_quasi_components_of:
   "pairwise (separatedin X) (quasi_components_of X)"
  by (metis closedin_quasi_components_of pairwise_def pairwise_disjoint_quasi_components_of separatedin_closed_sets)

lemma finite_quasi_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(quasi_components_of X)"
  by (simp add: Union_quasi_components_of finite_UnionD)

lemma connected_imp_quasi_component_of:
  assumes "connected_component_of X x y"
  shows "quasi_component_of X x y"
proof -
  have "x \<in> topspace X" "y \<in> topspace X"
    by (meson assms connected_component_of_equiv)+
  with assms show ?thesis
    apply (clarsimp simp add: quasi_component_of connected_component_of_def)
    by (meson connectedin_clopen_cases disjnt_iff subsetD)
qed

lemma connected_component_subset_quasi_component_of:
   "connected_component_of_set X x \<subseteq> quasi_component_of_set X x"
  using connected_imp_quasi_component_of by force

lemma quasi_component_as_connected_component_Union:
   "quasi_component_of_set X x =
    \<Union> (connected_component_of_set X ` quasi_component_of_set X x)" 
    (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using connected_component_of_refl quasi_component_of by fastforce
  show "?rhs \<subseteq> ?lhs"
    apply (rule SUP_least)
    by (simp add: connected_component_subset_quasi_component_of quasi_component_of_equiv)
qed

lemma quasi_components_as_connected_components_Union:
  assumes "C \<in> quasi_components_of X"
  obtains \<T> where "\<T> \<subseteq> connected_components_of X" "\<Union>\<T> = C"
proof -
  obtain x where "x \<in> topspace X" and Ceq: "C = quasi_component_of_set X x"
    by (metis assms imageE quasi_components_of_def)
  define \<T> where "\<T> \<equiv> connected_component_of_set X ` quasi_component_of_set X x"
  show thesis
  proof
    show "\<T> \<subseteq> connected_components_of X"
      by (simp add: \<T>_def connected_components_of_def image_mono quasi_component_of_subset_topspace)
    show "\<Union>\<T> = C"
      by (metis \<T>_def Ceq quasi_component_as_connected_component_Union)
  qed
qed

lemma path_imp_quasi_component_of:
   "path_component_of X x y \<Longrightarrow> quasi_component_of X x y"
  by (simp add: connected_imp_quasi_component_of path_imp_connected_component_of)

lemma path_component_subset_quasi_component_of:
   "path_component_of_set X x \<subseteq> quasi_component_of_set X x"
  by (simp add: Collect_mono path_imp_quasi_component_of)

lemma connected_space_iff_quasi_component:
   "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. quasi_component_of X x y)"
  unfolding connected_space_clopen_in closedin_def quasi_component_of
  by blast

lemma connected_space_imp_quasi_component_of:
   " \<lbrakk>connected_space X; a \<in> topspace X; b \<in> topspace X\<rbrakk> \<Longrightarrow> quasi_component_of X a b"
  by (simp add: connected_space_iff_quasi_component)

lemma connected_space_quasi_component_set:
   "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. quasi_component_of_set X x = topspace X)"
  by (metis Ball_Collect connected_space_iff_quasi_component quasi_component_of_subset_topspace subset_antisym)

lemma connected_space_iff_quasi_components_eq:
  "connected_space X \<longleftrightarrow>
    (\<forall>C \<in> quasi_components_of X. \<forall>D \<in> quasi_components_of X. C = D)"
  apply (simp add: quasi_components_of_def)
  by (metis connected_space_iff_quasi_component mem_Collect_eq quasi_component_of_equiv)

lemma quasi_components_of_subset_sing:
   "quasi_components_of X \<subseteq> {S} \<longleftrightarrow> connected_space X \<and> (X = trivial_topology \<or> topspace X = S)"
proof (cases "quasi_components_of X = {}")
  case True
  then show ?thesis
    by (simp add: subset_singleton_iff)
next
  case False
  then show ?thesis
    apply (simp add: connected_space_iff_quasi_components_eq subset_iff Ball_def)
    by (metis False Union_quasi_components_of ccpo_Sup_singleton insert_iff is_singletonE is_singletonI')
qed

lemma connected_space_iff_quasi_components_subset_sing:
   "connected_space X \<longleftrightarrow> (\<exists>a. quasi_components_of X \<subseteq> {a})"
  by (simp add: quasi_components_of_subset_sing)

lemma quasi_components_of_eq_singleton:
   "quasi_components_of X = {S} \<longleftrightarrow>
        connected_space X \<and> \<not> (X = trivial_topology) \<and> S = topspace X"
  by (metis empty_not_insert quasi_components_of_eq_empty quasi_components_of_subset_sing subset_singleton_iff)

lemma quasi_components_of_connected_space:
   "connected_space X
        \<Longrightarrow> quasi_components_of X = (if X = trivial_topology then {} else {topspace X})"
  by (simp add: quasi_components_of_eq_singleton)

lemma separated_between_singletons:
   "separated_between X {x} {y} \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> \<not> (quasi_component_of X x y)"
proof (cases "x \<in> topspace X \<and> y \<in> topspace X")
  case True
  then show ?thesis
    by (auto simp add: separated_between_def quasi_component_of_alt)
qed (use separated_between_imp_subset in blast)

lemma quasi_component_nonseparated:
   "quasi_component_of X x y \<longleftrightarrow> x \<in> topspace X \<and> y \<in> topspace X \<and> \<not> (separated_between X {x} {y})"
  by (metis quasi_component_of_equiv separated_between_singletons)

lemma separated_between_quasi_component_pointwise_left:
  assumes "C \<in> quasi_components_of X"
  shows "separated_between X C S \<longleftrightarrow> (\<exists>x \<in> C. separated_between X {x} S)"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using assms quasi_components_of_disjoint separated_between_mono by fastforce
next
  assume ?rhs
  then obtain y where "separated_between X {y} S" and "y \<in> C"
    by metis
  with assms show ?lhs
    by (force simp add: separated_between quasi_components_of_def quasi_component_of_def)
qed

lemma separated_between_quasi_component_pointwise_right:
   "C \<in> quasi_components_of X \<Longrightarrow> separated_between X S C \<longleftrightarrow> (\<exists>x \<in> C. separated_between X S {x})"
  by (simp add: separated_between_quasi_component_pointwise_left separated_between_sym)

lemma separated_between_quasi_component_point:
  assumes "C \<in> quasi_components_of X"
  shows "separated_between X C {x} \<longleftrightarrow> x \<in> topspace X - C" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (meson DiffI disjnt_insert2 insert_subset separated_between_imp_disjoint separated_between_imp_subset)
next
  assume ?rhs
  with assms show ?lhs
    unfolding quasi_components_of_def image_iff Diff_iff separated_between_quasi_component_pointwise_left [OF assms]
    by (metis mem_Collect_eq quasi_component_of_refl separated_between_singletons)
qed

lemma separated_between_point_quasi_component:
   "C \<in> quasi_components_of X \<Longrightarrow> separated_between X {x} C \<longleftrightarrow> x \<in> topspace X - C"
  by (simp add: separated_between_quasi_component_point separated_between_sym)

lemma separated_between_quasi_component_compact:
   "\<lbrakk>C \<in> quasi_components_of X; compactin X K\<rbrakk> \<Longrightarrow> (separated_between X C K \<longleftrightarrow> disjnt C K)"
  unfolding disjnt_iff
  using compactin_subset_topspace quasi_components_of_subset separated_between_pointwise_right separated_between_quasi_component_point by fastforce

lemma separated_between_compact_quasi_component:
   "\<lbrakk>compactin X K; C \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> separated_between X K C \<longleftrightarrow> disjnt K C"
  using disjnt_sym separated_between_quasi_component_compact separated_between_sym by blast

lemma separated_between_quasi_components:
  assumes C: "C \<in> quasi_components_of X" and D: "D \<in> quasi_components_of X"
  shows "separated_between X C D \<longleftrightarrow> disjnt C D"   (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (simp add: separated_between_imp_disjoint)
next
  assume ?rhs
  obtain x y where x: "C = quasi_component_of_set X x" and "x \<in> C"
               and y: "D = quasi_component_of_set X y" and "y \<in> D"
    using assms by (auto simp: quasi_components_of_def)
  then have "separated_between X {x} {y}"
    using \<open>disjnt C D\<close> separated_between_singletons by fastforce
  with \<open>x \<in> C\<close> \<open>y \<in> D\<close> show ?lhs
    by (auto simp: assms separated_between_quasi_component_pointwise_left separated_between_quasi_component_pointwise_right)
qed

lemma quasi_eq_connected_component_of_eq:
   "quasi_component_of X x = connected_component_of X x \<longleftrightarrow>
    connectedin X (quasi_component_of_set X x)"  (is "?lhs = ?rhs")
proof (cases "x \<in> topspace X")
  case True
  show ?thesis
  proof
    show "?lhs \<Longrightarrow> ?rhs"
      by (simp add: connectedin_connected_component_of)
  next
    assume ?rhs
    then have "\<And>y. quasi_component_of X x y = connected_component_of X x y"
      by (metis connected_component_of_def connected_imp_quasi_component_of mem_Collect_eq quasi_component_of_equiv)
    then show ?lhs
      by force
  qed
next
  case False
  then show ?thesis
    by (metis Collect_empty_eq_bot connected_component_of_eq_empty connectedin_empty quasi_component_of_eq_empty)
qed

lemma connected_quasi_component_of:
  assumes "C \<in> quasi_components_of X"
  shows "C \<in> connected_components_of X \<longleftrightarrow> connectedin X C"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using assms
    by (simp add: connectedin_connected_components_of)
next
  assume ?rhs
  with assms show ?lhs
    unfolding quasi_components_of_def connected_components_of_def image_iff
    by (metis quasi_eq_connected_component_of_eq)
qed

lemma quasi_component_of_clopen_cases:
   "\<lbrakk>C \<in> quasi_components_of X; closedin X T; openin X T\<rbrakk> \<Longrightarrow> C \<subseteq> T \<or> disjnt C T"
  by (smt (verit) disjnt_iff image_iff mem_Collect_eq quasi_component_of_def quasi_components_of_def subset_iff)

lemma quasi_components_of_set:
  assumes "C \<in> quasi_components_of X"
  shows "\<Inter> {T. closedin X T \<and> openin X T \<and> C \<subseteq> T} = C"  (is "?lhs = ?rhs")
proof
  have "x \<in> C" if "x \<in> \<Inter> {T. closedin X T \<and> openin X T \<and> C \<subseteq> T}" for x
  proof (rule ccontr)
    assume "x \<notin> C"
    have "x \<in> topspace X"
      using assms quasi_components_of_subset that by force
    then have "separated_between X C {x}"
      by (simp add: \<open>x \<notin> C\<close> assms separated_between_quasi_component_point)
    with that show False
      by (auto simp: separated_between)
  qed
  then show "?lhs \<subseteq> ?rhs"
    by auto
qed blast

lemma open_quasi_eq_connected_components_of:
  assumes "openin X C"
  shows "C \<in> quasi_components_of X \<longleftrightarrow> C \<in> connected_components_of X"  (is "?lhs = ?rhs")
proof (cases "closedin X C")
  case True
  show ?thesis
  proof
    assume L: ?lhs
    have "T = {} \<or> T = topspace X \<inter> C"
      if "openin (subtopology X C) T" "closedin (subtopology X C) T" for T
    proof -
      have "C \<subseteq> T \<or> disjnt C T"
        by (meson L True assms closedin_trans_full openin_trans_full quasi_component_of_clopen_cases that)
      with that show ?thesis
        by (metis Int_absorb2 True closedin_imp_subset closure_of_subset_eq disjnt_def inf_absorb2)
    qed
    with L assms show "?rhs"
      by (simp add: connected_quasi_component_of connected_space_clopen_in connectedin_def openin_subset)
  next
    assume ?rhs
    then obtain x where "x \<in> topspace X" and x: "C = connected_component_of_set X x"
      by (metis connected_components_of_def imageE)
    have "C = quasi_component_of_set X x"
      using True assms connected_component_of_refl connected_imp_quasi_component_of quasi_component_of_def x by fastforce
    then show ?lhs
      using \<open>x \<in> topspace X\<close> quasi_components_of_def by fastforce
  qed
next
  case False
  then show ?thesis
    using closedin_connected_components_of closedin_quasi_components_of by blast
qed

lemma quasi_component_of_continuous_image:
  assumes f:  "continuous_map X Y f" and qc: "quasi_component_of X x y"
  shows "quasi_component_of Y (f x) (f y)"
  unfolding quasi_component_of_def
proof (intro strip conjI)
  show "f x \<in> topspace Y" "f y \<in> topspace Y"
    using assms by (simp_all add: continuous_map_def quasi_component_of_def Pi_iff)
  fix T
  assume "closedin Y T \<and> openin Y T"
  with assms show "(f x \<in> T) = (f y \<in> T)"
    by (smt (verit) continuous_map_closedin continuous_map_def mem_Collect_eq quasi_component_of_def)
qed

lemma quasi_component_of_discrete_topology:
   "quasi_component_of_set (discrete_topology U) x = (if x \<in> U then {x} else {})"
proof -
  have "quasi_component_of_set (discrete_topology U) y = {y}" if "y \<in> U" for y
    using that
    apply (simp add: set_eq_iff quasi_component_of_def)
    by (metis Set.set_insert insertE subset_insertI)
  then show ?thesis
    by (simp add: quasi_component_of)
qed

lemma quasi_components_of_discrete_topology:
   "quasi_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
  by (auto simp add: quasi_components_of_def quasi_component_of_discrete_topology)

lemma homeomorphic_map_quasi_component_of:
  assumes hmf: "homeomorphic_map X Y f" and "x \<in> topspace X"
  shows "quasi_component_of_set Y (f x) = f ` (quasi_component_of_set X x)"
proof -
  obtain g where hmg: "homeomorphic_map Y X g"
    and contf: "continuous_map X Y f" and contg: "continuous_map Y X g"
    and fg: "(\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    by (smt (verit, best) hmf homeomorphic_map_maps homeomorphic_maps_def)
  show ?thesis
  proof
    show "quasi_component_of_set Y (f x) \<subseteq> f ` quasi_component_of_set X x"
      using quasi_component_of_continuous_image [OF contg]
         \<open>x \<in> topspace X\<close> fg image_iff quasi_component_of_subset_topspace by fastforce
    show "f ` quasi_component_of_set X x \<subseteq> quasi_component_of_set Y (f x)"
      using quasi_component_of_continuous_image [OF contf] by blast
  qed
qed


lemma homeomorphic_map_quasi_components_of:
  assumes "homeomorphic_map X Y f"
  shows "quasi_components_of Y = image (image f) (quasi_components_of X)"
  using assms
proof -
  have "\<exists>x\<in>topspace X. quasi_component_of_set Y y = f ` quasi_component_of_set X x"
    if "y \<in> topspace Y" for y 
    by (metis that assms homeomorphic_imp_surjective_map homeomorphic_map_quasi_component_of image_iff)
  moreover have "\<exists>x\<in>topspace Y. f ` quasi_component_of_set X u = quasi_component_of_set Y x"
    if  "u \<in> topspace X" for u
    by (metis that assms homeomorphic_imp_surjective_map homeomorphic_map_quasi_component_of imageI)
  ultimately show ?thesis
    by (auto simp: quasi_components_of_def image_iff)
qed

lemma openin_quasi_component_of_locally_connected_space:
  assumes "locally_connected_space X"
  shows "openin X (quasi_component_of_set X x)"
proof -
  have *: "openin X (connected_component_of_set X x)"
    by (simp add: assms openin_connected_component_of_locally_connected_space)
  moreover have "connected_component_of_set X x = quasi_component_of_set X x"
    using * closedin_connected_component_of connected_component_of_refl connected_imp_quasi_component_of
            quasi_component_of_def by fastforce
  ultimately show ?thesis
    by simp
qed

lemma openin_quasi_components_of_locally_connected_space:
   "locally_connected_space X \<and> c \<in> quasi_components_of X
        \<Longrightarrow> openin X c"
  by (smt (verit, best) image_iff openin_quasi_component_of_locally_connected_space quasi_components_of_def)

lemma quasi_eq_connected_components_of_alt:
  "quasi_components_of X = connected_components_of X \<longleftrightarrow> (\<forall>C \<in> quasi_components_of X. connectedin X C)"
  (is "?lhs = ?rhs")
proof
  assume R: ?rhs
  moreover have "connected_components_of X \<subseteq> quasi_components_of X"
    using R unfolding quasi_components_of_def connected_components_of_def
    by (force simp flip: quasi_eq_connected_component_of_eq)
  ultimately show ?lhs
    using connected_quasi_component_of by blast
qed (use connected_quasi_component_of in blast)
  
lemma connected_subset_quasi_components_of_pointwise:
   "connected_components_of X \<subseteq> quasi_components_of X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. quasi_component_of X x = connected_component_of X x)"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have "connectedin X (quasi_component_of_set X x)" if "x \<in> topspace X" for x
  proof -
    have "\<exists>y\<in>topspace X. connected_component_of_set X x = quasi_component_of_set X y"
      using L that by (force simp: quasi_components_of_def connected_components_of_def image_subset_iff)
    then show ?thesis
      by (metis connected_component_of_equiv connectedin_connected_component_of mem_Collect_eq quasi_component_of_eq)
  qed
  then show ?rhs
    by (simp add: quasi_eq_connected_component_of_eq)
qed (simp add: connected_components_of_def quasi_components_of_def)

lemma quasi_subset_connected_components_of_pointwise:
   "quasi_components_of X \<subseteq> connected_components_of X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. quasi_component_of X x = connected_component_of X x)"
  by (simp add: connected_quasi_component_of image_subset_iff quasi_components_of_def quasi_eq_connected_component_of_eq)

lemma quasi_eq_connected_components_of_pointwise:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. quasi_component_of X x = connected_component_of X x)"
  using connected_subset_quasi_components_of_pointwise quasi_subset_connected_components_of_pointwise by fastforce

lemma quasi_eq_connected_components_of_pointwise_alt:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
    (\<forall>x. quasi_component_of X x = connected_component_of X x)"
  unfolding quasi_eq_connected_components_of_pointwise
  by (metis connectedin_empty quasi_component_of_eq_empty quasi_eq_connected_component_of_eq)

lemma quasi_eq_connected_components_of_inclusion:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
        connected_components_of X \<subseteq> quasi_components_of X \<or>
        quasi_components_of X \<subseteq> connected_components_of X"
  by (simp add: connected_subset_quasi_components_of_pointwise dual_order.eq_iff quasi_subset_connected_components_of_pointwise)


lemma quasi_eq_connected_components_of:
  "finite(connected_components_of X) \<or>
      finite(quasi_components_of X) \<or>
      locally_connected_space X \<or>
      compact_space X \<and> (Hausdorff_space X \<or> regular_space X \<or> normal_space X)
      \<Longrightarrow> quasi_components_of X = connected_components_of X"
proof (elim disjE)
  show "quasi_components_of X = connected_components_of X"
    if "finite (connected_components_of X)"
    unfolding quasi_eq_connected_components_of_inclusion
    using that open_in_finite_connected_components open_quasi_eq_connected_components_of by blast
  show "quasi_components_of X = connected_components_of X"
    if "finite (quasi_components_of X)"
    unfolding quasi_eq_connected_components_of_inclusion
    using that open_quasi_eq_connected_components_of openin_finite_quasi_components by blast 
  show "quasi_components_of X = connected_components_of X"
    if "locally_connected_space X"
    unfolding quasi_eq_connected_components_of_inclusion
    using that open_quasi_eq_connected_components_of openin_quasi_components_of_locally_connected_space by auto 
  show "quasi_components_of X = connected_components_of X"
    if "compact_space X \<and> (Hausdorff_space X \<or> regular_space X \<or> normal_space X)"
  proof -
    show ?thesis
      unfolding quasi_eq_connected_components_of_alt
    proof (intro strip)
      fix C
      assume C: "C \<in> quasi_components_of X"
      then have cloC: "closedin X C"
        by (simp add: closedin_quasi_components_of)
      have "normal_space X"
        using that compact_Hausdorff_or_regular_imp_normal_space by blast
      show "connectedin X C"
      proof (clarsimp simp add: connectedin_def connected_space_closedin_eq closedin_closed_subtopology cloC closedin_subset [OF cloC])
        fix S T
        assume "S \<subseteq> C" and "closedin X S" and "S \<inter> T = {}" and SUT: "S \<union> T = topspace X \<inter> C"
          and T: "T \<subseteq> C" "T \<noteq> {}" and "closedin X T" 
        with \<open>normal_space X\<close> obtain U V where UV: "openin X U" "openin X V" "S \<subseteq> U" "T \<subseteq> V" "disjnt U V"
          by (meson disjnt_def normal_space_def)
        moreover have "compactin X (topspace X - (U \<union> V))"
          using UV that by (intro closedin_compact_space closedin_diff openin_Un) auto
        ultimately have "separated_between X C (topspace X - (U \<union> V)) \<longleftrightarrow> disjnt C (topspace X - (U \<union> V))"
          by (simp add: \<open>C \<in> quasi_components_of X\<close> separated_between_quasi_component_compact)
        moreover have "disjnt C (topspace X - (U \<union> V))"
          using UV SUT disjnt_def by fastforce
        ultimately have "separated_between X C (topspace X - (U \<union> V))"
          by simp
        then obtain A B where "openin X A" "openin X B" "A \<union> B = topspace X" "disjnt A B" "C \<subseteq> A" 
                        and subB: "topspace X - (U \<union> V) \<subseteq> B"
          by (meson separated_between_def)
        have "B \<union> U = topspace X - (A \<inter> V)"
        proof
          show "B \<union> U \<subseteq> topspace X - A \<inter> V"
            using \<open>openin X U\<close> \<open>disjnt U V\<close> \<open>disjnt A B\<close> \<open>openin X B\<close> disjnt_iff openin_closedin_eq by fastforce
          show "topspace X - A \<inter> V \<subseteq> B \<union> U"
            using \<open>A \<union> B = topspace X\<close> subB by fastforce
        qed
        then have "closedin X (B \<union> U)"
          using \<open>openin X V\<close> \<open>openin X A\<close> by auto
        then have "C \<subseteq> B \<union> U \<or> disjnt C (B \<union> U)"
          using quasi_component_of_clopen_cases [OF C] \<open>openin X U\<close> \<open>openin X B\<close> by blast
        with UV show "S = {}"
          by (metis UnE \<open>C \<subseteq> A\<close> \<open>S \<subseteq> C\<close> T \<open>disjnt A B\<close> all_not_in_conv disjnt_Un2 disjnt_iff subset_eq)
      qed
    qed
  qed
qed


lemma quasi_eq_connected_component_of:
   "finite(connected_components_of X) \<or>
      finite(quasi_components_of X) \<or>
      locally_connected_space X \<or>
      compact_space X \<and> (Hausdorff_space X \<or> regular_space X \<or> normal_space X)
      \<Longrightarrow> quasi_component_of X x = connected_component_of X x"
  by (metis quasi_eq_connected_components_of quasi_eq_connected_components_of_pointwise_alt)


subsection\<open>Additional quasicomponent and continuum properties like Boundary Bumping\<close>

lemma cut_wire_fence_theorem_gen:
  assumes "compact_space X" and X: "Hausdorff_space X \<or> regular_space X \<or> normal_space X"
    and S: "compactin X S" and T: "closedin X T"
    and dis: "\<And>C. connectedin X C \<Longrightarrow> disjnt C S \<or> disjnt C T"
  shows "separated_between X S T"
  proof -
  have "x \<in> topspace X" if "x \<in> S" and "T = {}" for x
    using that S compactin_subset_topspace by auto
  moreover have "separated_between X {x} {y}" if "x \<in> S" and "y \<in> T" for x y
  proof (cases "x \<in> topspace X \<and> y \<in> topspace X")
    case True
    then have "\<not> connected_component_of X x y"
      by (meson dis connected_component_of_def disjnt_iff that)
    with True X \<open>compact_space X\<close> show ?thesis
      by (metis quasi_component_nonseparated quasi_eq_connected_component_of)
  next
    case False
    then show ?thesis
      using S T compactin_subset_topspace closedin_subset that by blast
  qed
  ultimately show ?thesis
    using assms
    by (simp add: separated_between_pointwise_left separated_between_pointwise_right 
              closedin_compact_space closedin_subset)
qed

lemma cut_wire_fence_theorem:
   "\<lbrakk>compact_space X; Hausdorff_space X; closedin X S; closedin X T;
     \<And>C. connectedin X C \<Longrightarrow> disjnt C S \<or> disjnt C T\<rbrakk>
        \<Longrightarrow> separated_between X S T"
  by (simp add: closedin_compact_space cut_wire_fence_theorem_gen)

lemma separated_between_from_closed_subtopology:
  assumes XC: "separated_between (subtopology X C) S (X frontier_of C)" 
    and ST: "separated_between (subtopology X C) S T"
  shows "separated_between X S T"
proof -
  obtain U where clo: "closedin (subtopology X C) U" and ope: "openin (subtopology X C) U" 
             and "S \<subseteq> U" and sub: "X frontier_of C \<union> T \<subseteq> topspace (subtopology X C) - U"
    by (meson assms separated_between separated_between_Un)
  then have "X frontier_of C \<union> T \<subseteq> topspace X \<inter> C - U"
    by auto
  have "closedin X (topspace X \<inter> C)"
    by (metis XC frontier_of_restrict frontier_of_subset_eq inf_le1 separated_between_imp_subset topspace_subtopology)
  then have "closedin X U"
    by (metis clo closedin_closed_subtopology subtopology_restrict)
  moreover have "openin (subtopology X C) U \<longleftrightarrow> openin X U \<and> U \<subseteq> C"
    using disjnt_iff sub by (force intro!: openin_subset_topspace_eq)
  with ope have "openin X U"
    by blast
  moreover have "T \<subseteq> topspace X - U"
    using ope openin_closedin_eq sub by auto
  ultimately show ?thesis
    using \<open>S \<subseteq> U\<close> separated_between by blast
qed

lemma separated_between_from_closed_subtopology_frontier:
   "separated_between (subtopology X T) S (X frontier_of T)
        \<Longrightarrow> separated_between X S (X frontier_of T)"
  using separated_between_from_closed_subtopology by blast

lemma separated_between_from_frontier_of_closed_subtopology:
  assumes "separated_between (subtopology X T) S (X frontier_of T)"
  shows "separated_between X S (topspace X - T)"
proof -
  have "disjnt S (topspace X - T)"
    using assms disjnt_iff separated_between_imp_subset by fastforce
  then show ?thesis
    by (metis Diff_subset assms frontier_of_complement separated_between_from_closed_subtopology separated_between_frontier_of_eq')
qed

lemma separated_between_compact_connected_component:
  assumes "locally_compact_space X" "Hausdorff_space X" 
    and C: "C \<in> connected_components_of X" 
    and "compactin X C" "closedin X T" "disjnt C T"
  shows "separated_between X C T"
proof -
  have Csub: "C \<subseteq> topspace X"
    by (simp add: assms(4) compactin_subset_topspace)
  have "Hausdorff_space (subtopology X (topspace X - T))"
    using Hausdorff_space_subtopology assms(2) by blast
  moreover have "compactin (subtopology X (topspace X - T)) C"
    using assms Csub by (metis Diff_Int_distrib Diff_empty compact_imp_compactin_subtopology disjnt_def le_iff_inf)
  moreover have "locally_compact_space (subtopology X (topspace X - T))"
    by (meson assms closedin_def locally_compact_Hausdorff_imp_regular_space locally_compact_space_open_subset)
  ultimately
  obtain N L where "openin X N" "compactin X L" "closedin X L" "C \<subseteq> N" "N \<subseteq> L" 
    and Lsub: "L \<subseteq> topspace X - T"
    using \<open>Hausdorff_space X\<close> \<open>closedin X T\<close>
    apply (simp add: locally_compact_space_compact_closed_compact compactin_subtopology)
    by (meson closedin_def compactin_imp_closedin  openin_trans_full)
  then have disC: "disjnt C (topspace X - L)"
    by (meson DiffD2 disjnt_iff subset_iff)
  have "separated_between (subtopology X L) C (X frontier_of L)"
  proof (rule cut_wire_fence_theorem)
    show "compact_space (subtopology X L)"
      by (simp add: \<open>compactin X L\<close> compact_space_subtopology)
    show "Hausdorff_space (subtopology X L)"
      by (simp add: Hausdorff_space_subtopology \<open>Hausdorff_space X\<close>)
    show "closedin (subtopology X L) C"
      by (meson \<open>C \<subseteq> N\<close> \<open>N \<subseteq> L\<close> \<open>Hausdorff_space X\<close> \<open>compactin X C\<close> closedin_subset_topspace compactin_imp_closedin subset_trans)
    show "closedin (subtopology X L) (X frontier_of L)"
      by (simp add: \<open>closedin X L\<close> closedin_frontier_of closedin_subset_topspace frontier_of_subset_closedin)
    show "disjnt D C \<or> disjnt D (X frontier_of L)"
      if "connectedin (subtopology X L) D" for D 
    proof (rule ccontr)
      assume "\<not> (disjnt D C \<or> disjnt D (X frontier_of L))"
      moreover have "connectedin X D"
        using connectedin_subtopology that by blast
      ultimately show False
        using that connected_components_of_maximal [of C X D] C
        apply (simp add: disjnt_iff)
        by (metis Diff_eq_empty_iff \<open>C \<subseteq> N\<close> \<open>N \<subseteq> L\<close> \<open>openin X N\<close> disjoint_iff frontier_of_openin_straddle_Int(2) subsetD)
    qed
  qed
  then have "separated_between X (X frontier_of C) (topspace X - L)"
    using separated_between_from_frontier_of_closed_subtopology separated_between_frontier_of_eq by blast
  with \<open>closedin X T\<close>  
    separated_between_frontier_of [OF Csub disC] 
  show ?thesis
    unfolding separated_between by (smt (verit) Diff_iff Lsub closedin_subset subset_iff)
qed

lemma wilder_locally_compact_component_thm:
  assumes "locally_compact_space X" "Hausdorff_space X" 
    and "C \<in> connected_components_of X" "compactin X C" "openin X W" "C \<subseteq> W"
  obtains U V where "openin X U" "openin X V" "disjnt U V" "U \<union> V = topspace X" "C \<subseteq> U" "U \<subseteq> W"
proof -
  have "closedin X (topspace X - W)"
    using \<open>openin X W\<close> by blast
  moreover have "disjnt C (topspace X - W)"
    using \<open>C \<subseteq> W\<close> disjnt_def by fastforce
  ultimately have "separated_between X C (topspace X - W)"
    using separated_between_compact_connected_component assms by blast
  then show thesis
    by (smt (verit, del_insts) DiffI disjnt_iff openin_subset separated_between_def subset_iff that)
qed

lemma compact_quasi_eq_connected_components_of:
  assumes "locally_compact_space X" "Hausdorff_space X" "compactin X C"
  shows "C \<in> quasi_components_of X \<longleftrightarrow> C \<in> connected_components_of X"
proof -
  have "compactin X (connected_component_of_set X x)" 
    if "x \<in> topspace X" "compactin X (quasi_component_of_set X x)" for x
  proof (rule closed_compactin)
    show "compactin X (quasi_component_of_set X x)"
      by (simp add: that)
    show "connected_component_of_set X x \<subseteq> quasi_component_of_set X x"
      by (simp add: connected_component_subset_quasi_component_of)
    show "closedin X (connected_component_of_set X x)"
      by (simp add: closedin_connected_component_of)
  qed
  moreover have "connected_component_of X x = quasi_component_of X x"
    if \<section>: "x \<in> topspace X" "compactin X (connected_component_of_set X x)" for x
  proof -
    have "\<And>y. connected_component_of X x y \<Longrightarrow> quasi_component_of X x y"
      by (simp add: connected_imp_quasi_component_of)
    moreover have False if non: "\<not> connected_component_of X x y" and quasi: "quasi_component_of X x y" for y
    proof -
      have "y \<in> topspace X"
        by (meson quasi_component_of_equiv that)
      then have "closedin X {y}"
        by (simp add: \<open>Hausdorff_space X\<close> compactin_imp_closedin)
      moreover have "disjnt (connected_component_of_set X x) {y}"
        by (simp add: non)
      moreover have "\<not> separated_between X (connected_component_of_set X x) {y}"
        using \<section> quasi separated_between_pointwise_left 
        by (fastforce simp: quasi_component_nonseparated connected_component_of_refl)
      ultimately show False
        using assms by (metis \<section> connected_component_in_connected_components_of separated_between_compact_connected_component)
    qed
    ultimately show ?thesis
      by blast
  qed
  ultimately show ?thesis
    using \<open>compactin X C\<close> unfolding connected_components_of_def image_iff quasi_components_of_def by metis
qed


lemma boundary_bumping_theorem_closed_gen:
  assumes "connected_space X" "locally_compact_space X" "Hausdorff_space X" "closedin X S" 
    "S \<noteq> topspace X" and C: "compactin X C" "C \<in> connected_components_of (subtopology X S)"
  shows "C \<inter> X frontier_of S \<noteq> {}"
proof 
  assume \<section>: "C \<inter> X frontier_of S = {}"
  consider "C \<noteq> {}" "X frontier_of S \<subseteq> topspace X" | "C \<subseteq> topspace X" "S = {}"
    using C by (metis frontier_of_subset_topspace nonempty_connected_components_of)
  then show False
  proof cases
    case 1
    have "separated_between (subtopology X S) C (X frontier_of S)"
    proof (rule separated_between_compact_connected_component)
      show "compactin (subtopology X S) C"
        using C compact_imp_compactin_subtopology connected_components_of_subset by fastforce
      show "closedin (subtopology X S) (X frontier_of S)"
        by (simp add: \<open>closedin X S\<close> closedin_frontier_of closedin_subset_topspace frontier_of_subset_closedin)
      show "disjnt C (X frontier_of S)"
        using \<section> by (simp add: disjnt_def)
    qed (use assms Hausdorff_space_subtopology locally_compact_space_closed_subset in auto)
    then have "separated_between X C (X frontier_of S)"
      using separated_between_from_closed_subtopology by auto
    then have "X frontier_of S = {}"
      using \<open>C \<noteq> {}\<close> \<open>connected_space X\<close> connected_space_separated_between by blast
    moreover have "C \<subseteq> S"
      using C connected_components_of_subset by fastforce
    ultimately show False
      using 1 assms by (metis closedin_subset connected_space_eq_frontier_eq_empty subset_empty)
  next
    case 2
    then show False
      using C connected_components_of_eq_empty by fastforce
  qed
qed

lemma boundary_bumping_theorem_closed:
  assumes "connected_space X" "compact_space X" "Hausdorff_space X" "closedin X S" 
          "S \<noteq> topspace X" "C \<in> connected_components_of(subtopology X S)"
  shows "C \<inter> X frontier_of S \<noteq> {}"
  by (meson assms boundary_bumping_theorem_closed_gen closedin_compact_space closedin_connected_components_of
            closedin_trans_full compact_imp_locally_compact_space)


lemma intermediate_continuum_exists:
  assumes "connected_space X" "locally_compact_space X" "Hausdorff_space X" 
    and C: "compactin X C" "connectedin X C" "C \<noteq> {}" "C \<noteq> topspace X"
    and U: "openin X U" "C \<subseteq> U"
  obtains D where "compactin X D" "connectedin X D" "C \<subset> D" "D \<subset> U"
proof -
  have "C \<subseteq> topspace X"
    by (simp add: C compactin_subset_topspace)
  with C obtain a where a: "a \<in> topspace X" "a \<notin> C"
    by blast
  moreover have "compactin (subtopology X (U - {a})) C"
    by (simp add: C U a compact_imp_compactin_subtopology subset_Diff_insert)
  moreover have "Hausdorff_space (subtopology X (U - {a}))"
    using Hausdorff_space_subtopology assms(3) by blast
  moreover
  have "locally_compact_space (subtopology X (U - {a}))"
    by (rule locally_compact_space_open_subset)
       (auto simp: locally_compact_Hausdorff_imp_regular_space open_in_Hausdorff_delete assms)
  ultimately obtain V K where V: "openin X V" "a \<notin> V" "V \<subseteq> U" and K: "compactin X K" "a \<notin> K" "K \<subseteq> U" 
    and cloK: "closedin (subtopology X (U - {a})) K" and "C \<subseteq> V" "V \<subseteq> K"
    using locally_compact_space_compact_closed_compact [of "subtopology X (U - {a})"] assms
    by (smt (verit, del_insts) Diff_empty compactin_subtopology open_in_Hausdorff_delete openin_open_subtopology subset_Diff_insert)
  then obtain D where D: "D \<in> connected_components_of (subtopology X K)" and "C \<subseteq> D"
    using C
    by (metis compactin_subset_topspace connected_component_in_connected_components_of        
              connected_component_of_maximal connectedin_subtopology subset_empty subset_eq topspace_subtopology_subset)
  show thesis
  proof
    have cloD: "closedin (subtopology X K) D"
      by (simp add: D closedin_connected_components_of)
    then have XKD: "compactin (subtopology X K) D"
      by (simp add: K closedin_compact_space compact_space_subtopology)
    then show "compactin X D"
      by (simp add: compactin_subtopology)
    show "connectedin X D"
      using D connectedin_connected_components_of connectedin_subtopology by blast
    have "K \<noteq> topspace X"
      using K a by blast
    moreover have "V \<subseteq> X interior_of K"
      by (simp add: \<open>openin X V\<close> \<open>V \<subseteq> K\<close> interior_of_maximal)
    ultimately have "C \<noteq> D"
      using boundary_bumping_theorem_closed_gen [of X K C] D \<open>C \<subseteq> V\<close> 
      by (auto simp add: assms K compactin_imp_closedin frontier_of_def)
    then show "C \<subset> D"
      using \<open>C \<subseteq> D\<close> by blast
    have "D \<subseteq> U"
      using K(3) \<open>closedin (subtopology X K) D\<close> closedin_imp_subset by blast
    moreover have "D \<noteq> U"
      using K XKD \<open>C \<subset> D\<close> assms
      by (metis \<open>K \<noteq> topspace X\<close> cloD closedin_imp_subset compactin_imp_closedin connected_space_clopen_in
                inf_bot_left inf_le2 subset_antisym)
    ultimately
    show "D \<subset> U" by blast
  qed
qed

lemma boundary_bumping_theorem_gen:
  assumes X: "connected_space X" "locally_compact_space X" "Hausdorff_space X" 
   and "S \<subset> topspace X" and C: "C \<in> connected_components_of(subtopology X S)" 
   and compC: "compactin X (X closure_of C)"
 shows "X frontier_of C \<inter> X frontier_of S \<noteq> {}"
proof -
  have Csub: "C \<subseteq> topspace X" "C \<subseteq> S" and "connectedin X C"
    using C connectedin_connected_components_of connectedin_subset_topspace connectedin_subtopology
    by fastforce+
  have "C \<noteq> {}"
    using C nonempty_connected_components_of by blast
  obtain "X interior_of C \<subseteq> X interior_of S" "X closure_of C \<subseteq> X closure_of S"
    by (simp add: Csub closure_of_mono interior_of_mono)
  moreover have False if "X closure_of C \<subseteq> X interior_of S"
  proof -
    have "X closure_of C = C"
      by (meson C closedin_connected_component_of_subtopology closure_of_eq interior_of_subset order_trans that)
    with that have "C \<subseteq> X interior_of S"
      by simp
    then obtain D where  "compactin X D" and "connectedin X D" and "C \<subset> D" and "D \<subset> X interior_of S"
      using intermediate_continuum_exists assms  \<open>X closure_of C = C\<close> compC Csub
      by (metis \<open>C \<noteq> {}\<close> \<open>connectedin X C\<close> openin_interior_of psubsetE)
    then have "D \<subseteq> C"
      by (metis C \<open>C \<noteq> {}\<close> connected_components_of_maximal connectedin_subtopology disjnt_def inf.orderE interior_of_subset order_trans psubsetE)
    then show False
      using \<open>C \<subset> D\<close> by blast
  qed
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) DiffI disjoint_iff_not_equal frontier_of_def subset_eq)
qed

lemma boundary_bumping_theorem:
   "\<lbrakk>connected_space X; compact_space X; Hausdorff_space X; S \<subset> topspace X; 
     C \<in> connected_components_of(subtopology X S)\<rbrakk>
    \<Longrightarrow> X frontier_of C \<inter> X frontier_of S \<noteq> {}"
  by (simp add: boundary_bumping_theorem_gen closedin_compact_space compact_imp_locally_compact_space)

subsection \<open>Compactly generated spaces (k-spaces)\<close>

text \<open>These don't have to be Hausdorff\<close>

definition k_space where
  "k_space X \<equiv>
    \<forall>S. S \<subseteq> topspace X \<longrightarrow> 
        (closedin X S \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> S)))"

lemma k_space:
   "k_space X \<longleftrightarrow>
    (\<forall>S. S \<subseteq> topspace X \<and>
         (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> S)) \<longrightarrow> closedin X S)"
  by (metis closedin_subtopology inf_commute k_space_def)

lemma k_space_open:
   "k_space X \<longleftrightarrow>
    (\<forall>S. S \<subseteq> topspace X \<and>
         (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S)) \<longrightarrow> openin X S)"
proof -
  have "openin X S"
    if "k_space X" "S \<subseteq> topspace X"
      and "\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S)" for S
    using that unfolding k_space openin_closedin_eq
    by (metis Diff_Int_distrib2 Diff_subset inf_commute topspace_subtopology)
  moreover have "k_space X"
    if "\<forall>S. S \<subseteq> topspace X \<and> (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S)) \<longrightarrow> openin X S"
    unfolding k_space openin_closedin_eq
    by (simp add: Diff_Int_distrib closedin_def inf_commute that)
  ultimately show ?thesis
    by blast
qed

lemma k_space_alt:
   "k_space X \<longleftrightarrow>
    (\<forall>S. S \<subseteq> topspace X
        \<longrightarrow> (openin X S \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S))))"
  by (meson k_space_open openin_subtopology_Int2)

lemma k_space_quotient_map_image:
  assumes q: "quotient_map X Y q" and X: "k_space X"
  shows "k_space Y"
  unfolding k_space
proof clarify
  fix S
  assume "S \<subseteq> topspace Y" and S: "\<forall>K. compactin Y K \<longrightarrow> closedin (subtopology Y K) (K \<inter> S)"
  then have iff: "closedin X {x \<in> topspace X. q x \<in> S} \<longleftrightarrow> closedin Y S"
    using q quotient_map_closedin by fastforce
  have "closedin (subtopology X K) (K \<inter> {x \<in> topspace X. q x \<in> S})" if "compactin X K" for K
  proof -
    have "{x \<in> topspace X. q x \<in> q ` K} \<inter> K = K"
      using compactin_subset_topspace that by blast
    then have *: "subtopology X K = subtopology (subtopology X {x \<in> topspace X. q x \<in> q ` K}) K"
      by (simp add: subtopology_subtopology)
    have **: "K \<inter> {x \<in> topspace X. q x \<in> S} =
              K \<inter> {x \<in> topspace (subtopology X {x \<in> topspace X. q x \<in> q ` K}). q x \<in> q ` K \<inter> S}"
      by auto
    have "K \<subseteq> topspace X"
      by (simp add: compactin_subset_topspace that)
    show ?thesis
      unfolding * **
    proof (intro closedin_continuous_map_preimage closedin_subtopology_Int_closed)
      show "continuous_map (subtopology X {x \<in> topspace X. q x \<in> q ` K}) (subtopology Y (q ` K)) q"
        by (auto simp add: continuous_map_in_subtopology continuous_map_from_subtopology q quotient_imp_continuous_map)
      show "closedin (subtopology Y (q ` K)) (q ` K \<inter> S)"
        by (meson S image_compactin q quotient_imp_continuous_map that)
    qed
  qed
  then have "closedin X {x \<in> topspace X. q x \<in> S}"
    by (metis (no_types, lifting) X k_space mem_Collect_eq subsetI)
  with iff show "closedin Y S" by simp
qed

lemma k_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; k_space X\<rbrakk> \<Longrightarrow> k_space Y"
  using k_space_quotient_map_image retraction_imp_quotient_map by blast

lemma homeomorphic_k_space:
   "X homeomorphic_space Y \<Longrightarrow> k_space X \<longleftrightarrow> k_space Y"
  by (meson homeomorphic_map_def homeomorphic_space homeomorphic_space_sym k_space_quotient_map_image)

lemma k_space_perfect_map_image:
   "\<lbrakk>k_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> k_space Y"
  using k_space_quotient_map_image perfect_imp_quotient_map by blast

lemma locally_compact_imp_k_space:
  assumes "locally_compact_space X"
  shows "k_space X"
  unfolding k_space
proof clarify
  fix S
  assume "S \<subseteq> topspace X" and S: "\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> S)"
  have False if non: "\<not> (X closure_of S \<subseteq> S)"
  proof -
    obtain x where "x \<in> X closure_of S" "x \<notin> S"
      using non by blast
    then have "x \<in> topspace X"
      by (simp add: in_closure_of)
    then obtain K U where "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K"
      by (meson assms locally_compact_space_def)
    then show False
      using \<open>x \<in> X closure_of S\<close>  openin_Int_closure_of_eq [OF \<open>openin X U\<close>]
      by (smt (verit, ccfv_threshold) Int_iff S \<open>x \<notin> S\<close> closedin_Int_closure_of inf.orderE inf_assoc)
  qed
  then show "closedin X S"
    using S \<open>S \<subseteq> topspace X\<close> closure_of_subset_eq by blast
qed

lemma compact_imp_k_space:
   "compact_space X \<Longrightarrow> k_space X"
  by (simp add: compact_imp_locally_compact_space locally_compact_imp_k_space)

lemma k_space_discrete_topology: "k_space(discrete_topology U)"
  by (simp add: k_space_open)

lemma k_space_closed_subtopology:
  assumes "k_space X" "closedin X C"
  shows "k_space (subtopology X C)"
unfolding k_space compactin_subtopology
proof clarsimp
  fix S
  assume Ssub: "S \<subseteq> topspace X" "S \<subseteq> C"
      and S: "\<forall>K. compactin X K \<and> K \<subseteq> C \<longrightarrow> closedin (subtopology (subtopology X C) K) (K \<inter> S)"
  have "closedin (subtopology X K) (K \<inter> S)" if "compactin X K" for K
  proof -
    have "closedin (subtopology (subtopology X C) (K \<inter> C)) ((K \<inter> C) \<inter> S)"
      by (simp add: S \<open>closedin X C\<close> compact_Int_closedin that)
    then show ?thesis
      using \<open>closedin X C\<close> Ssub by (auto simp add: closedin_subtopology)
  qed
  then show "closedin (subtopology X C) S"
    by (metis Ssub \<open>k_space X\<close> closedin_subset_topspace k_space_def)
qed

lemma k_space_subtopology:
  assumes 1: "\<And>T. \<lbrakk>T \<subseteq> topspace X; T \<subseteq> S;
                   \<And>K. compactin X K \<Longrightarrow> closedin (subtopology X (K \<inter> S)) (K \<inter> T)\<rbrakk> \<Longrightarrow> closedin (subtopology X S) T"
  assumes 2: "\<And>K. compactin X K \<Longrightarrow> k_space(subtopology X (K \<inter> S))"
  shows "k_space (subtopology X S)"
  unfolding k_space
proof (intro conjI strip)
  fix U
  assume \<section>: "U \<subseteq> topspace (subtopology X S) \<and> (\<forall>K. compactin (subtopology X S) K \<longrightarrow> closedin (subtopology (subtopology X S) K) (K \<inter> U))"
  have "closedin (subtopology X (K \<inter> S)) (K \<inter> U)" if "compactin X K" for K
  proof -
    have "K \<inter> U \<subseteq> topspace (subtopology X (K \<inter> S))"
      using "\<section>" by auto
    moreover
    have "\<And>K'. compactin (subtopology X (K \<inter> S)) K' \<Longrightarrow> closedin (subtopology (subtopology X (K \<inter> S)) K') (K' \<inter> K \<inter> U)"
      by (metis "\<section>" compactin_subtopology inf.orderE inf_commute subtopology_subtopology)
    ultimately show ?thesis
      by (metis (no_types, opaque_lifting) "2" inf.assoc k_space_def that)
  qed
  then show "closedin (subtopology X S) U"
    using "1" \<section> by auto
qed

lemma k_space_subtopology_open:
  assumes 1: "\<And>T. \<lbrakk>T \<subseteq> topspace X; T \<subseteq> S;
                    \<And>K. compactin X K \<Longrightarrow> openin (subtopology X (K \<inter> S)) (K \<inter> T)\<rbrakk> \<Longrightarrow> openin (subtopology X S) T"
  assumes 2: "\<And>K. compactin X K \<Longrightarrow> k_space(subtopology X (K \<inter> S))"
  shows "k_space (subtopology X S)"
  unfolding k_space_open
proof (intro conjI strip)
  fix U
  assume \<section>: "U \<subseteq> topspace (subtopology X S) \<and> (\<forall>K. compactin (subtopology X S) K \<longrightarrow> openin (subtopology (subtopology X S) K) (K \<inter> U))"
  have "openin (subtopology X (K \<inter> S)) (K \<inter> U)" if "compactin X K" for K
  proof -
    have "K \<inter> U \<subseteq> topspace (subtopology X (K \<inter> S))"
      using "\<section>" by auto
    moreover
    have "\<And>K'. compactin (subtopology X (K \<inter> S)) K' \<Longrightarrow> openin (subtopology (subtopology X (K \<inter> S)) K') (K' \<inter> K \<inter> U)"
      by (metis "\<section>" compactin_subtopology inf.orderE inf_commute subtopology_subtopology)
    ultimately show ?thesis
      by (metis (no_types, opaque_lifting) "2" inf.assoc k_space_open that)
  qed
  then show "openin (subtopology X S) U"
    using "1" \<section> by auto
qed


lemma k_space_open_subtopology_aux:
  assumes "kc_space X" "compact_space X" "openin X V"
  shows "k_space (subtopology X V)"
proof (clarsimp simp: k_space subtopology_subtopology compactin_subtopology Int_absorb1)
  fix S
  assume "S \<subseteq> topspace X"
    and "S \<subseteq> V"
    and S: "\<forall>K. compactin X K \<and> K \<subseteq> V \<longrightarrow> closedin (subtopology X K) (K \<inter> S)"
  then have "V \<subseteq> topspace X"
    using assms openin_subset by blast
  have "S = V \<inter> ((topspace X - V) \<union> S)"
    using \<open>S \<subseteq> V\<close> by auto
  moreover have "closedin (subtopology X V) (V \<inter> ((topspace X - V) \<union> S))"
  proof (intro closedin_subtopology_Int_closed compactin_imp_closedin_gen \<open>kc_space X\<close>)
    show "compactin X (topspace X - V \<union> S)"
      unfolding compactin_def
    proof (intro conjI strip)
      show "topspace X - V \<union> S \<subseteq> topspace X"
        by (simp add: \<open>S \<subseteq> topspace X\<close>)
      fix \<U>
      assume \<U>: "Ball \<U> (openin X) \<and> topspace X - V \<union> S \<subseteq> \<Union>\<U>"
      moreover
      have "compactin X (topspace X - V)"
        using assms closedin_compact_space by blast
      ultimately obtain \<G> where "finite \<G>" "\<G> \<subseteq> \<U>" and \<G>: "topspace X - V \<subseteq> \<Union>\<G>"
        unfolding compactin_def using \<open>V \<subseteq> topspace X\<close> by (metis le_sup_iff)
      then have "topspace X - \<Union>\<G> \<subseteq> V"
        by blast
      then have "closedin (subtopology X (topspace X - \<Union>\<G>)) ((topspace X - \<Union>\<G>) \<inter> S)"
        by (meson S \<U> \<open>\<G> \<subseteq> \<U>\<close> \<open>compact_space X\<close> closedin_compact_space openin_Union openin_closedin_eq subset_iff)
      then have "compactin X ((topspace X - \<Union>\<G>) \<inter> S)"
        by (meson \<U> \<open>\<G> \<subseteq> \<U>\<close>\<open>compact_space X\<close> closedin_compact_space closedin_trans_full openin_Union openin_closedin_eq subset_iff)
      then obtain \<H> where "finite \<H>" "\<H> \<subseteq> \<U>" "(topspace X - \<Union>\<G>) \<inter> S \<subseteq> \<Union>\<H>"
        unfolding compactin_def by (smt (verit, best) \<U> inf_le2 subset_trans sup.boundedE)
      with \<G> have "topspace X - V \<union> S \<subseteq> \<Union>(\<G> \<union> \<H>)"
        using \<open>S \<subseteq> topspace X\<close> by auto
      then show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> topspace X - V \<union> S \<subseteq> \<Union>\<F>"
        by (metis \<open>\<G> \<subseteq> \<U>\<close> \<open>\<H> \<subseteq> \<U>\<close> \<open>finite \<G>\<close> \<open>finite \<H>\<close> finite_Un le_sup_iff)
    qed
  qed
  ultimately show "closedin (subtopology X V) S"
    by metis
qed


lemma k_space_open_subtopology:
  assumes X: "kc_space X \<or> Hausdorff_space X \<or> regular_space X" and "k_space X" "openin X S"
  shows "k_space(subtopology X S)"
proof (rule k_space_subtopology_open)
  fix T
  assume "T \<subseteq> topspace X"
    and "T \<subseteq> S"
    and T: "\<And>K. compactin X K \<Longrightarrow> openin (subtopology X (K \<inter> S)) (K \<inter> T)"
  have "openin (subtopology X K) (K \<inter> T)" if "compactin X K" for K
    by (smt (verit, ccfv_threshold) T assms(3) inf_assoc inf_commute openin_Int openin_subtopology that)
  then show "openin (subtopology X S) T"
    by (metis \<open>T \<subseteq> S\<close> \<open>T \<subseteq> topspace X\<close> assms(2) k_space_alt subset_openin_subtopology)
next
  fix K
  assume "compactin X K"
  then have KS: "openin (subtopology X K) (K \<inter> S)"
    by (simp add: \<open>openin X S\<close> openin_subtopology_Int2)
  have XK: "compact_space (subtopology X K)"
    by (simp add: \<open>compactin X K\<close> compact_space_subtopology)
  show "k_space (subtopology X (K \<inter> S))"
    using X
  proof (rule disjE)
    assume "kc_space X"
    then show "k_space (subtopology X (K \<inter> S))"
      using k_space_open_subtopology_aux [of "subtopology X K" "K \<inter> S"]
      by (simp add: KS XK kc_space_subtopology subtopology_subtopology)
  next
    assume "Hausdorff_space X \<or> regular_space X"
    then have "locally_compact_space (subtopology (subtopology X K) (K \<inter> S))"
      using locally_compact_space_open_subset Hausdorff_space_subtopology KS XK 
        compact_imp_locally_compact_space regular_space_subtopology by blast
    then show "k_space (subtopology X (K \<inter> S))"
      by (simp add: locally_compact_imp_k_space subtopology_subtopology)
  qed
qed

lemma k_kc_space_subtopology:
   "\<lbrakk>k_space X; kc_space X; openin X S \<or> closedin X S\<rbrakk> \<Longrightarrow> k_space(subtopology X S) \<and> kc_space(subtopology X S)"
  by (metis k_space_closed_subtopology k_space_open_subtopology kc_space_subtopology)


lemma k_space_as_quotient_explicit:
  "k_space X \<longleftrightarrow> quotient_map (sum_topology (subtopology X) {K. compactin X K}) X snd"
proof -
  have [simp]: "{x \<in> topspace X. x \<in> K \<and> x \<in> U} = K \<inter> U" if "U \<subseteq> topspace X" for K U
    using that by blast
  show "?thesis"
    apply (simp add: quotient_map_def openin_sum_topology snd_image_Sigma k_space_alt)
    by (smt (verit, del_insts) Union_iff compactin_sing inf.orderE mem_Collect_eq singletonI subsetI)
qed

lemma k_space_as_quotient:
  fixes X :: "'a topology"
  shows "k_space X \<longleftrightarrow> (\<exists>q. \<exists>Y:: ('a set * 'a) topology. locally_compact_space Y \<and> quotient_map Y X q)" 
         (is "?lhs=?rhs")
proof
  show "k_space X" if ?rhs
    using that k_space_quotient_map_image locally_compact_imp_k_space by blast 
next
  assume "k_space X"
  show ?rhs
  proof (intro exI conjI)
    show "locally_compact_space (sum_topology (subtopology X) {K. compactin X K})"
      by (simp add: compact_imp_locally_compact_space compact_space_subtopology locally_compact_space_sum_topology)
    show "quotient_map (sum_topology (subtopology X) {K. compactin X K}) X snd"
      using \<open>k_space X\<close> k_space_as_quotient_explicit by blast
  qed
qed

lemma k_space_prod_topology_left:
  assumes X: "locally_compact_space X" "Hausdorff_space X \<or> regular_space X" and "k_space Y"
  shows "k_space (prod_topology X Y)"
proof -
  obtain q and Z :: "('b set * 'b) topology" where "locally_compact_space Z" and q: "quotient_map Z Y q"
    using \<open>k_space Y\<close> k_space_as_quotient by blast
  then show ?thesis
    using quotient_map_prod_right [OF X q] X k_space_quotient_map_image locally_compact_imp_k_space 
          locally_compact_space_prod_topology by blast
qed

lemma k_space_prod_topology_right:
  assumes "k_space X" and Y: "locally_compact_space Y" "Hausdorff_space Y \<or> regular_space Y"
  shows "k_space (prod_topology X Y)"
  using assms homeomorphic_k_space homeomorphic_space_prod_topology_swap k_space_prod_topology_left by blast


lemma continuous_map_from_k_space:
  assumes "k_space X" and f: "\<And>K. compactin X K \<Longrightarrow> continuous_map(subtopology X K) Y f"
  shows "continuous_map X Y f"
proof -
  have "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y"
    by (metis compactin_absolute compactin_sing f image_compactin image_empty image_insert)
  moreover have "closedin X {x \<in> topspace X. f x \<in> C}" if "closedin Y C" for C
  proof -
    have "{x \<in> topspace X. f x \<in> C} \<subseteq> topspace X"
      by fastforce
    moreover 
    have eq: "K \<inter> {x \<in> topspace X. f x \<in> C} = {x. x \<in> topspace(subtopology X K) \<and> f x \<in> (f ` K \<inter> C)}" for K
      by auto
    have "closedin (subtopology X K) (K \<inter> {x \<in> topspace X. f x \<in> C})" if "compactin X K" for K
      unfolding eq
    proof (rule closedin_continuous_map_preimage)
      show "continuous_map (subtopology X K) (subtopology Y (f`K)) f"
        by (simp add: continuous_map_in_subtopology f image_mono that)
      show "closedin (subtopology Y (f`K)) (f ` K \<inter> C)"
        using \<open>closedin Y C\<close> closedin_subtopology by blast
    qed
    ultimately show ?thesis
      using \<open>k_space X\<close> k_space by blast
  qed
  ultimately show ?thesis
    by (simp add: continuous_map_closedin)
qed

lemma closed_map_into_k_space:
  assumes "k_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y"
    and f: "\<And>K. compactin Y K
                \<Longrightarrow> closed_map(subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f"
  shows "closed_map X Y f"
  unfolding closed_map_def
proof (intro strip)
  fix C
  assume "closedin X C"
  have "closedin (subtopology Y K) (K \<inter> f ` C)"
    if "compactin Y K" for K
  proof -
    have eq: "K \<inter> f ` C = f ` ({x \<in> topspace X. f x \<in> K} \<inter> C)"
      using \<open>closedin X C\<close> closedin_subset by auto
    show ?thesis
      unfolding eq
      by (metis (no_types, lifting) \<open>closedin X C\<close> closed_map_def closedin_subtopology f inf_commute that)
  qed
  then show "closedin Y (f ` C)"
    using \<open>k_space Y\<close> unfolding k_space
    by (meson \<open>closedin X C\<close> closedin_subset order.trans fim funcset_image subset_image_iff)
qed


text \<open>Essentially the same proof\<close>
lemma open_map_into_k_space:
  assumes "k_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y"
    and f: "\<And>K. compactin Y K
                 \<Longrightarrow> open_map (subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f"
  shows "open_map X Y f"
  unfolding open_map_def
proof (intro strip)
  fix C
  assume "openin X C"
  have "openin (subtopology Y K) (K \<inter> f ` C)"
    if "compactin Y K" for K
  proof -
    have eq: "K \<inter> f ` C = f ` ({x \<in> topspace X. f x \<in> K} \<inter> C)"
      using \<open>openin X C\<close> openin_subset by auto
    show ?thesis
      unfolding eq
      by (metis (no_types, lifting) \<open>openin X C\<close> open_map_def openin_subtopology f inf_commute that)
  qed
  then show "openin Y (f ` C)"
    using \<open>k_space Y\<close> unfolding k_space_open
    by (meson \<open>openin X C\<close> openin_subset order.trans fim funcset_image subset_image_iff)
qed

lemma quotient_map_into_k_space:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "k_space Y" and cmf: "continuous_map X Y f" 
    and fim: "f ` (topspace X) = topspace Y"
    and f: "\<And>k. compactin Y k
                 \<Longrightarrow> quotient_map (subtopology X {x \<in> topspace X. f x \<in> k})
                                  (subtopology Y k) f"
  shows "quotient_map X Y f"
proof -
  have "closedin Y C"
    if "C \<subseteq> topspace Y" and K: "closedin X {x \<in> topspace X. f x \<in> C}" for C
  proof -
    have "closedin (subtopology Y K) (K \<inter> C)" if "compactin Y K" for K
    proof -
      define Kf where "Kf \<equiv> {x \<in> topspace X. f x \<in> K}"
      have *: "K \<inter> C \<subseteq> topspace Y \<and> K \<inter> C \<subseteq> K"
        using \<open>C \<subseteq> topspace Y\<close> by blast
      then have eq: "closedin (subtopology X Kf) (Kf \<inter> {x \<in> topspace X. f x \<in> C}) =
                 closedin (subtopology Y K) (K \<inter> C)"
        using f [OF that] * unfolding quotient_map_closedin Kf_def
        by (smt (verit, ccfv_SIG) Collect_cong Int_def compactin_subset_topspace mem_Collect_eq that topspace_subtopology topspace_subtopology_subset)
      have dd: "{x \<in> topspace X \<inter> Kf. f x \<in> K \<inter> C} = Kf \<inter> {x \<in> topspace X. f x \<in> C}"
        by (auto simp add: Kf_def)
      have "closedin (subtopology X Kf) {x \<in> topspace X. x \<in> Kf \<and> f x \<in> K \<and> f x \<in> C}"
        using K closedin_subtopology by (fastforce simp add: Kf_def)
      with K closedin_subtopology_Int_closed eq show ?thesis
        by blast
    qed
    then show ?thesis 
      using \<open>k_space Y\<close> that unfolding k_space by blast
  qed
  moreover have "closedin X {x \<in> topspace X. f x \<in> K}"
    if "K \<subseteq> topspace Y" "closedin Y K" for K
    using that cmf continuous_map_closedin by fastforce
  ultimately show ?thesis
    unfolding quotient_map_closedin using fim by blast
qed

lemma quotient_map_into_k_space_eq:
  assumes "k_space Y" "kc_space Y"
  shows "quotient_map X Y f \<longleftrightarrow>
         continuous_map X Y f \<and> f ` (topspace X) = topspace Y \<and>
         (\<forall>K. compactin Y K
              \<longrightarrow> quotient_map (subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f)"
  using assms
  by (auto simp: kc_space_def intro: quotient_map_into_k_space quotient_map_restriction
       dest: quotient_imp_continuous_map quotient_imp_surjective_map)

lemma open_map_into_k_space_eq:
  assumes "k_space Y"
  shows "open_map X Y f \<longleftrightarrow>
         f \<in> (topspace X) \<rightarrow> topspace Y \<and>
         (\<forall>k. compactin Y k
              \<longrightarrow> open_map (subtopology X {x \<in> topspace X. f x \<in> k}) (subtopology Y k) f)"
  using assms open_map_imp_subset_topspace open_map_into_k_space open_map_restriction by fastforce

lemma closed_map_into_k_space_eq:
  assumes "k_space Y"
  shows "closed_map X Y f \<longleftrightarrow>
         f \<in> (topspace X) \<rightarrow> topspace Y \<and>
         (\<forall>k. compactin Y k
              \<longrightarrow> closed_map (subtopology X {x \<in> topspace X. f x \<in> k}) (subtopology Y k) f)"
       (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (simp add: closed_map_imp_subset_topspace closed_map_restriction)
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: assms closed_map_into_k_space)
qed

lemma proper_map_into_k_space:
  assumes "k_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y"
    and f: "\<And>K. compactin Y K
                 \<Longrightarrow> proper_map (subtopology X {x \<in> topspace X. f x \<in> K})
                                (subtopology Y K) f"
  shows "proper_map X Y f"
proof -
  have "closed_map X Y f"
    by (meson assms closed_map_into_k_space fim proper_map_def)
  with f topspace_subtopology_subset show ?thesis
    apply (simp add: proper_map_alt)
    by (smt (verit, best) Collect_cong compactin_absolute)
qed

lemma proper_map_into_k_space_eq:
  assumes "k_space Y"
  shows "proper_map X Y f \<longleftrightarrow>
         f \<in> (topspace X) \<rightarrow> topspace Y \<and>
         (\<forall>K. compactin Y K
              \<longrightarrow> proper_map (subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f)"
         (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (simp add: proper_map_imp_subset_topspace proper_map_restriction)
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: assms funcset_image proper_map_into_k_space)
qed

lemma compact_imp_proper_map:
  assumes "k_space Y" "kc_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y" 
    and f: "continuous_map X Y f \<or> kc_space X" 
    and comp: "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
  shows "proper_map X Y f"
proof (rule compact_imp_proper_map_gen)
  fix S
  assume "S \<subseteq> topspace Y"
      and "\<And>K. compactin Y K \<Longrightarrow> compactin Y (S \<inter> K)"
  with assms show "closedin Y S"
    by (simp add: closedin_subset_topspace inf_commute k_space kc_space_def)
qed (use assms in auto)

lemma proper_eq_compact_map:
  assumes "k_space Y" "kc_space Y" 
    and f: "continuous_map X Y f \<or> kc_space X" 
  shows  "proper_map X Y f \<longleftrightarrow>
             f \<in> (topspace X) \<rightarrow> topspace Y \<and>
             (\<forall>K. compactin Y K \<longrightarrow> compactin X {x \<in> topspace X. f x \<in> K})"
         (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using \<open>k_space Y\<close> compactin_proper_map_preimage proper_map_into_k_space_eq by blast
qed (use assms compact_imp_proper_map in auto)

lemma compact_imp_perfect_map:
  assumes "k_space Y" "kc_space Y" and "f ` (topspace X) = topspace Y" 
    and "continuous_map X Y f" 
    and "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
  shows "perfect_map X Y f"
  by (simp add: assms compact_imp_proper_map perfect_map_def flip: image_subset_iff_funcset)

end

