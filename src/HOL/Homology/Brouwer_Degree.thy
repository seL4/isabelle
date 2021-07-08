section\<open>Homology, III: Brouwer Degree\<close>

theory Brouwer_Degree
  imports Homology_Groups "HOL-Algebra.Multiplicative_Group"

begin

subsection\<open>Reduced Homology\<close>

definition reduced_homology_group :: "int \<Rightarrow> 'a topology \<Rightarrow> 'a chain set monoid"
  where "reduced_homology_group p X \<equiv>
           subgroup_generated (homology_group p X)
             (kernel (homology_group p X) (homology_group p (discrete_topology {()}))
                     (hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ())))"

lemma one_reduced_homology_group: "\<one>\<^bsub>reduced_homology_group p X\<^esub> = \<one>\<^bsub>homology_group p X\<^esub>"
    by (simp add: reduced_homology_group_def)

lemma group_reduced_homology_group [simp]: "group (reduced_homology_group p X)"
    by (simp add: reduced_homology_group_def group.group_subgroup_generated)

lemma carrier_reduced_homology_group:
   "carrier (reduced_homology_group p X) =
    kernel (homology_group p X) (homology_group p (discrete_topology {()}))
           (hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ()))"
    (is "_ = kernel ?G ?H ?h")
proof -
  interpret subgroup "kernel ?G ?H ?h" ?G
  by (simp add: hom_induced_empty_hom group_hom_axioms_def group_hom_def group_hom.subgroup_kernel)
  show ?thesis
    unfolding reduced_homology_group_def
    using carrier_subgroup_generated_subgroup by blast
qed

lemma carrier_reduced_homology_group_subset:
   "carrier (reduced_homology_group p X) \<subseteq> carrier (homology_group p X)"
  by (simp add: group.carrier_subgroup_generated_subset reduced_homology_group_def)

lemma un_reduced_homology_group:
  assumes "p \<noteq> 0"
  shows "reduced_homology_group p X = homology_group p X"
proof -
  have "(kernel (homology_group p X) (homology_group p (discrete_topology {()}))
              (hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ())))
      = carrier (homology_group p X)"
  proof (rule group_hom.kernel_to_trivial_group)
    show "group_hom (homology_group p X) (homology_group p (discrete_topology {()}))
         (hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ()))"
      by (auto simp: hom_induced_empty_hom group_hom_def group_hom_axioms_def)
    show "trivial_group (homology_group p (discrete_topology {()}))"
      by (simp add: homology_dimension_axiom [OF _ assms])
  qed
  then show ?thesis
    by (simp add: reduced_homology_group_def group.subgroup_generated_group_carrier)
qed

lemma trivial_reduced_homology_group:
   "p < 0 \<Longrightarrow> trivial_group(reduced_homology_group p X)"
  by (simp add: trivial_homology_group un_reduced_homology_group)

lemma hom_induced_reduced_hom:
   "(hom_induced p X {} Y {} f) \<in> hom (reduced_homology_group p X) (reduced_homology_group p Y)"
proof (cases "continuous_map X Y f")
  case True
  have eq: "continuous_map X Y f
         \<Longrightarrow> hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ())
           = (hom_induced p Y {} (discrete_topology {()}) {} (\<lambda>x. ()) \<circ> hom_induced p X {} Y {} f)"
    by (simp flip: hom_induced_compose_empty)
  interpret subgroup "kernel (homology_group p X)
                       (homology_group p (discrete_topology {()}))
                         (hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ()))"
                     "homology_group p X"
    by (meson group_hom.subgroup_kernel group_hom_axioms_def group_hom_def group_relative_homology_group hom_induced)
  have sb: "hom_induced p X {} Y {} f ` carrier (homology_group p X) \<subseteq> carrier (homology_group p Y)"
    using hom_induced_carrier by blast
    show ?thesis
    using True
    unfolding reduced_homology_group_def
    apply (simp add: hom_into_subgroup_eq group_hom.subgroup_kernel hom_induced_empty_hom group.hom_from_subgroup_generated group_hom_def group_hom_axioms_def)
    unfolding kernel_def using eq sb by auto
next
  case False
  then have "hom_induced p X {} Y {} f = (\<lambda>c. one(reduced_homology_group p Y))"
    by (force simp: hom_induced_default reduced_homology_group_def)
  then show ?thesis
    by (simp add: trivial_hom)
qed


lemma hom_induced_reduced:
   "c \<in> carrier(reduced_homology_group p X)
        \<Longrightarrow> hom_induced p X {} Y {} f c \<in> carrier(reduced_homology_group p Y)"
  by (meson hom_in_carrier hom_induced_reduced_hom)

lemma hom_boundary_reduced_hom:
   "hom_boundary p X S
  \<in> hom (relative_homology_group p X S) (reduced_homology_group (p-1) (subtopology X S))"
proof -
  have *: "continuous_map X (discrete_topology {()}) (\<lambda>x. ())" "(\<lambda>x. ()) ` S \<subseteq> {()}"
    by auto
  interpret group_hom "relative_homology_group p (discrete_topology {()}) {()}"
                      "homology_group (p-1) (discrete_topology {()})"
                      "hom_boundary p (discrete_topology {()}) {()}"
    apply (clarsimp simp: group_hom_def group_hom_axioms_def)
    by (metis UNIV_unit hom_boundary_hom subtopology_UNIV)
  have "hom_boundary p X S `
        carrier (relative_homology_group p X S)
        \<subseteq> kernel (homology_group (p - 1) (subtopology X S))
            (homology_group (p - 1) (discrete_topology {()}))
            (hom_induced (p - 1) (subtopology X S) {}
              (discrete_topology {()}) {} (\<lambda>x. ()))"
  proof (clarsimp simp add: kernel_def hom_boundary_carrier)
    fix c
    assume c: "c \<in> carrier (relative_homology_group p X S)"
    have triv: "trivial_group (relative_homology_group p (discrete_topology {()}) {()})"
      by (metis topspace_discrete_topology trivial_relative_homology_group_topspace)
    have "hom_boundary p (discrete_topology {()}) {()}
         (hom_induced p X S (discrete_topology {()}) {()} (\<lambda>x. ()) c)
       = \<one>\<^bsub>homology_group (p - 1) (discrete_topology {()})\<^esub>"
      by (metis hom_induced_carrier local.hom_one singletonD triv trivial_group_def)
    then show "hom_induced (p - 1) (subtopology X S) {} (discrete_topology {()}) {} (\<lambda>x. ()) (hom_boundary p X S c) =
        \<one>\<^bsub>homology_group (p - 1) (discrete_topology {()})\<^esub>"
      using naturality_hom_induced [OF *, of p, symmetric] by (simp add: o_def fun_eq_iff)
  qed
  then show ?thesis
    by (simp add: reduced_homology_group_def hom_boundary_hom hom_into_subgroup)
qed


lemma homotopy_equivalence_reduced_homology_group_isomorphisms:
  assumes contf: "continuous_map X Y f" and contg: "continuous_map Y X g"
    and gf: "homotopic_with (\<lambda>h. True) X X (g \<circ> f) id"
    and fg: "homotopic_with (\<lambda>k. True) Y Y (f \<circ> g) id"
  shows "group_isomorphisms (reduced_homology_group p X) (reduced_homology_group p Y)
                               (hom_induced p X {} Y {} f) (hom_induced p Y {} X {} g)"
proof (simp add: hom_induced_reduced_hom group_isomorphisms_def, intro conjI ballI)
  fix a
  assume "a \<in> carrier (reduced_homology_group p X)"
  then have "(hom_induced p Y {} X {} g \<circ> hom_induced p X {} Y {} f) a = a"
    apply (simp add: contf contg flip: hom_induced_compose)
    using carrier_reduced_homology_group_subset gf hom_induced_id homology_homotopy_empty by fastforce
  then show "hom_induced p Y {} X {} g (hom_induced p X {} Y {} f a) = a"
    by simp
next
  fix b
  assume "b \<in> carrier (reduced_homology_group p Y)"
  then have "(hom_induced p X {} Y {} f \<circ> hom_induced p Y {} X {} g) b = b"
    apply (simp add: contf contg flip: hom_induced_compose)
    using carrier_reduced_homology_group_subset fg hom_induced_id homology_homotopy_empty by fastforce
  then show "hom_induced p X {} Y {} f (hom_induced p Y {} X {} g b) = b"
    by (simp add: carrier_reduced_homology_group)
qed

lemma homotopy_equivalence_reduced_homology_group_isomorphism:
  assumes "continuous_map X Y f" "continuous_map Y X g"
      and "homotopic_with (\<lambda>h. True) X X (g \<circ> f) id" "homotopic_with (\<lambda>k. True) Y Y (f \<circ> g) id"
  shows "(hom_induced p X {} Y {} f)
          \<in> iso (reduced_homology_group p X) (reduced_homology_group p Y)"
proof (rule group_isomorphisms_imp_iso)
  show "group_isomorphisms (reduced_homology_group p X) (reduced_homology_group p Y)
         (hom_induced p X {} Y {} f) (hom_induced p Y {} X {} g)"
    by (simp add: assms homotopy_equivalence_reduced_homology_group_isomorphisms)
qed

lemma homotopy_equivalent_space_imp_isomorphic_reduced_homology_groups:
   "X homotopy_equivalent_space Y
        \<Longrightarrow> reduced_homology_group p X \<cong> reduced_homology_group p Y"
  unfolding homotopy_equivalent_space_def
  using homotopy_equivalence_reduced_homology_group_isomorphism is_isoI by blast

lemma homeomorphic_space_imp_isomorphic_reduced_homology_groups:
   "X homeomorphic_space Y \<Longrightarrow> reduced_homology_group p X \<cong> reduced_homology_group p Y"
  by (simp add: homeomorphic_imp_homotopy_equivalent_space homotopy_equivalent_space_imp_isomorphic_reduced_homology_groups)

lemma trivial_reduced_homology_group_empty:
   "topspace X = {} \<Longrightarrow> trivial_group(reduced_homology_group p X)"
  by (metis carrier_reduced_homology_group_subset group.trivial_group_alt group_reduced_homology_group trivial_group_def trivial_homology_group_empty)

lemma homology_dimension_reduced:
  assumes "topspace X = {a}"
  shows "trivial_group (reduced_homology_group p X)"
proof -
  have iso: "(hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ()))
           \<in> iso (homology_group p X) (homology_group p (discrete_topology {()}))"
    apply (rule homeomorphic_map_homology_iso)
    apply (force simp: homeomorphic_map_maps homeomorphic_maps_def assms)
    done
  show ?thesis
    unfolding reduced_homology_group_def
    by (rule group.trivial_group_subgroup_generated) (use iso in \<open>auto simp: iso_kernel_image\<close>)
qed


lemma trivial_reduced_homology_group_contractible_space:
   "contractible_space X \<Longrightarrow> trivial_group (reduced_homology_group p X)"
  apply (simp add: contractible_eq_homotopy_equivalent_singleton_subtopology)
  apply (auto simp: trivial_reduced_homology_group_empty)
  using isomorphic_group_triviality
  by (metis (full_types) group_reduced_homology_group homology_dimension_reduced homotopy_equivalent_space_imp_isomorphic_reduced_homology_groups path_connectedin_def path_connectedin_singleton topspace_subtopology_subset)


lemma image_reduced_homology_group:
  assumes "topspace X \<inter> S \<noteq> {}"
  shows "hom_induced p X {} X S id ` carrier (reduced_homology_group p X)
       = hom_induced p X {} X S id ` carrier (homology_group p X)"
    (is "?h ` carrier ?G = ?h ` carrier ?H")
proof -
  obtain a where a: "a \<in> topspace X" and "a \<in> S"
    using assms by blast
  have [simp]: "A \<inter> {x \<in> A. P x} = {x \<in> A. P x}" for A P
    by blast
  interpret comm_group "homology_group p X"
    by (rule abelian_relative_homology_group)
  have *: "\<exists>x'. ?h y = ?h x' \<and>
             x' \<in> carrier ?H \<and>
             hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ()) x'
           = \<one>\<^bsub>homology_group p (discrete_topology {()})\<^esub>"
    if "y \<in> carrier ?H" for y
  proof -
    let ?f = "hom_induced p (discrete_topology {()}) {} X {} (\<lambda>x. a)"
    let ?g = "hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ())"
    have bcarr: "?f (?g y) \<in> carrier ?H"
      by (simp add: hom_induced_carrier)
    interpret gh1:
      group_hom "relative_homology_group p X S" "relative_homology_group p (discrete_topology {()}) {()}"
                "hom_induced p X S (discrete_topology {()}) {()} (\<lambda>x. ())"
      by (meson group_hom_axioms_def group_hom_def hom_induced_hom group_relative_homology_group)
    interpret gh2:
      group_hom "relative_homology_group p (discrete_topology {()}) {()}" "relative_homology_group p X S"
                "hom_induced p (discrete_topology {()}) {()} X S (\<lambda>x. a)"
      by (meson group_hom_axioms_def group_hom_def hom_induced_hom group_relative_homology_group)
    interpret gh3:
      group_hom "homology_group p X" "relative_homology_group p X S" "?h"
      by (meson group_hom_axioms_def group_hom_def hom_induced_hom group_relative_homology_group)
    interpret gh4:
      group_hom "homology_group p X" "homology_group p (discrete_topology {()})"
                "?g"
      by (meson group_hom_axioms_def group_hom_def hom_induced_hom group_relative_homology_group)
    interpret gh5:
      group_hom "homology_group p (discrete_topology {()})" "homology_group p X"
                "?f"
      by (meson group_hom_axioms_def group_hom_def hom_induced_hom group_relative_homology_group)
    interpret gh6:
      group_hom "homology_group p (discrete_topology {()})" "relative_homology_group p (discrete_topology {()}) {()}"
                "hom_induced p (discrete_topology {()}) {} (discrete_topology {()}) {()} id"
      by (meson group_hom_axioms_def group_hom_def hom_induced_hom group_relative_homology_group)
    show ?thesis
    proof (intro exI conjI)
      have "(?h \<circ> ?f \<circ> ?g) y
          = (hom_induced p (discrete_topology {()}) {()} X S (\<lambda>x. a) \<circ>
             hom_induced p (discrete_topology {()}) {} (discrete_topology {()}) {()} id \<circ> ?g) y"
        by (simp add: a \<open>a \<in> S\<close> flip: hom_induced_compose)
      also have "\<dots> = \<one>\<^bsub>relative_homology_group p X S\<^esub>"
        using trivial_relative_homology_group_topspace [of p "discrete_topology {()}"]
        apply simp
        by (metis (full_types) empty_iff gh1.H.one_closed gh1.H.trivial_group gh2.hom_one hom_induced_carrier insert_iff)
      finally have "?h (?f (?g y)) = \<one>\<^bsub>relative_homology_group p X S\<^esub>"
        by simp
      then show "?h y = ?h (y \<otimes>\<^bsub>?H\<^esub> inv\<^bsub>?H\<^esub> ?f (?g y))"
        by (simp add: that hom_induced_carrier)
      show "(y \<otimes>\<^bsub>?H\<^esub> inv\<^bsub>?H\<^esub> ?f (?g y)) \<in> carrier (homology_group p X)"
        by (simp add: hom_induced_carrier that)
      have *: "(?g \<circ> hom_induced p X {} X {} (\<lambda>x. a)) y = hom_induced p X {} (discrete_topology {()}) {} (\<lambda>a. ()) y"
        by (simp add: a \<open>a \<in> S\<close> flip: hom_induced_compose)
      have "?g (y \<otimes>\<^bsub>?H\<^esub> inv\<^bsub>?H\<^esub> (?f \<circ> ?g) y)
          = \<one>\<^bsub>homology_group p (discrete_topology {()})\<^esub>"
        by (simp add: a \<open>a \<in> S\<close> that hom_induced_carrier flip: hom_induced_compose * [unfolded o_def])
      then show "?g (y \<otimes>\<^bsub>?H\<^esub> inv\<^bsub>?H\<^esub> ?f (?g y))
          = \<one>\<^bsub>homology_group p (discrete_topology {()})\<^esub>"
        by simp
    qed
  qed
  show ?thesis
    apply (auto simp: reduced_homology_group_def carrier_subgroup_generated kernel_def image_iff)
     apply (metis (no_types, lifting) generate_in_carrier mem_Collect_eq subsetI)
    apply (force simp: dest: * intro: generate.incl)
    done
qed


lemma homology_exactness_reduced_1:
  assumes "topspace X \<inter> S \<noteq> {}"
  shows  "exact_seq([reduced_homology_group(p - 1) (subtopology X S),
                     relative_homology_group p X S,
                     reduced_homology_group p X],
                    [hom_boundary p X S, hom_induced p X {} X S id])"
    (is "exact_seq ([?G1,?G2,?G3], [?h1,?h2])")
proof -
  have *: "?h2 ` carrier (homology_group p X)
         = kernel ?G2 (homology_group (p - 1) (subtopology X S)) ?h1"
    using homology_exactness_axiom_1 [of p X S] by simp
  have gh: "group_hom ?G3 ?G2 ?h2"
    by (simp add: reduced_homology_group_def group_hom_def group_hom_axioms_def
      group.group_subgroup_generated group.hom_from_subgroup_generated hom_induced_hom)
  show ?thesis
    apply (simp add: hom_boundary_reduced_hom gh * image_reduced_homology_group [OF assms])
    apply (simp add: kernel_def one_reduced_homology_group)
    done
qed


lemma homology_exactness_reduced_2:
   "exact_seq([reduced_homology_group(p - 1) X,
                 reduced_homology_group(p - 1) (subtopology X S),
                 relative_homology_group p X S],
                [hom_induced (p - 1) (subtopology X S) {} X {} id, hom_boundary p X S])"
    (is "exact_seq ([?G1,?G2,?G3], [?h1,?h2])")
  using homology_exactness_axiom_2 [of p X S]
  apply (simp add: group_hom_axioms_def group_hom_def hom_boundary_reduced_hom hom_induced_reduced_hom)
  apply (simp add: reduced_homology_group_def group_hom.subgroup_kernel group_hom_axioms_def group_hom_def hom_induced_hom)
  using hom_boundary_reduced_hom [of p X S]
  apply (auto simp: image_def set_eq_iff)
  by (metis carrier_reduced_homology_group hom_in_carrier set_eq_iff)


lemma homology_exactness_reduced_3:
   "exact_seq([relative_homology_group p X S,
               reduced_homology_group p X,
               reduced_homology_group p (subtopology X S)],
              [hom_induced p X {} X S id, hom_induced p (subtopology X S) {} X {} id])"
    (is "exact_seq ([?G1,?G2,?G3], [?h1,?h2])")
proof -
  have "kernel ?G2 ?G1 ?h1 =
      ?h2 ` carrier ?G3"
  proof -
    obtain U where U:
      "(hom_induced p (subtopology X S) {} X {} id) ` carrier ?G3 \<subseteq> U"
      "(hom_induced p (subtopology X S) {} X {} id) ` carrier ?G3
       \<subseteq> (hom_induced p (subtopology X S) {} X {} id) ` carrier (homology_group p (subtopology X S))"
      "U \<inter> kernel (homology_group p X) ?G1 (hom_induced p X {} X S id)
     = kernel ?G2 ?G1 (hom_induced p X {} X S id)"
      "U \<inter> (hom_induced p (subtopology X S) {} X {} id) ` carrier (homology_group p (subtopology X S))
    \<subseteq> (hom_induced p (subtopology X S) {} X {} id) ` carrier ?G3"
    proof
      show "?h2 ` carrier ?G3 \<subseteq> carrier ?G2"
        by (simp add: hom_induced_reduced image_subset_iff)
      show "?h2 ` carrier ?G3 \<subseteq> ?h2 ` carrier (homology_group p (subtopology X S))"
        by (meson carrier_reduced_homology_group_subset image_mono)
      have "subgroup (kernel (homology_group p X) (homology_group p (discrete_topology {()}))
                             (hom_induced p X {} (discrete_topology {()}) {} (\<lambda>x. ())))
                     (homology_group p X)"
        by (simp add: group.normal_invE(1) group_hom.normal_kernel group_hom_axioms_def group_hom_def hom_induced_empty_hom)
      then show "carrier ?G2 \<inter> kernel (homology_group p X) ?G1 ?h1 = kernel ?G2 ?G1 ?h1"
        unfolding carrier_reduced_homology_group
        by (auto simp: reduced_homology_group_def)
    show "carrier ?G2 \<inter> ?h2 ` carrier (homology_group p (subtopology X S))
       \<subseteq> ?h2 ` carrier ?G3"
      by (force simp: carrier_reduced_homology_group kernel_def hom_induced_compose')
  qed
  with homology_exactness_axiom_3 [of p X S] show ?thesis
    by (fastforce simp add:)
qed
  then show ?thesis
    apply (simp add: group_hom_axioms_def group_hom_def hom_boundary_reduced_hom hom_induced_reduced_hom)
    apply (simp add: group.hom_from_subgroup_generated hom_induced_hom reduced_homology_group_def)
    done
qed


subsection\<open>More homology properties of deformations, retracts, contractible spaces\<close>

lemma iso_relative_homology_of_contractible:
   "\<lbrakk>contractible_space X; topspace X \<inter> S \<noteq> {}\<rbrakk>
  \<Longrightarrow> hom_boundary p X S
      \<in> iso (relative_homology_group p X S) (reduced_homology_group(p - 1) (subtopology X S))"
  using very_short_exact_sequence
    [of "reduced_homology_group (p - 1) X"
        "reduced_homology_group (p - 1) (subtopology X S)"
        "relative_homology_group p X S"
        "reduced_homology_group p X"
        "hom_induced (p - 1) (subtopology X S) {} X {} id"
        "hom_boundary p X S"
        "hom_induced p X {} X S id"]
  by (meson exact_seq_cons_iff homology_exactness_reduced_1 homology_exactness_reduced_2 trivial_reduced_homology_group_contractible_space)

lemma isomorphic_group_relative_homology_of_contractible:
   "\<lbrakk>contractible_space X; topspace X \<inter> S \<noteq> {}\<rbrakk>
        \<Longrightarrow> relative_homology_group p X S \<cong>
            reduced_homology_group(p - 1) (subtopology X S)"
  by (meson iso_relative_homology_of_contractible is_isoI)

lemma isomorphic_group_reduced_homology_of_contractible:
   "\<lbrakk>contractible_space X; topspace X \<inter> S \<noteq> {}\<rbrakk>
        \<Longrightarrow> reduced_homology_group p (subtopology X S) \<cong> relative_homology_group(p + 1) X S"
  by (metis add.commute add_diff_cancel_left' group.iso_sym group_relative_homology_group isomorphic_group_relative_homology_of_contractible)

lemma iso_reduced_homology_by_contractible:
   "\<lbrakk>contractible_space(subtopology X S); topspace X \<inter> S \<noteq> {}\<rbrakk>
      \<Longrightarrow> (hom_induced p X {} X S id) \<in> iso (reduced_homology_group p X) (relative_homology_group p X S)"
  using very_short_exact_sequence
    [of "reduced_homology_group (p - 1) (subtopology X S)"
        "relative_homology_group p X S"
        "reduced_homology_group p X"
        "reduced_homology_group p (subtopology X S)"
        "hom_boundary p X S"
        "hom_induced p X {} X S id"
        "hom_induced p (subtopology X S) {} X {} id"]
  by (meson exact_seq_cons_iff homology_exactness_reduced_1 homology_exactness_reduced_3 trivial_reduced_homology_group_contractible_space)

lemma isomorphic_reduced_homology_by_contractible:
   "\<lbrakk>contractible_space(subtopology X S); topspace X \<inter> S \<noteq> {}\<rbrakk>
      \<Longrightarrow> reduced_homology_group p X \<cong> relative_homology_group p X S"
  using is_isoI iso_reduced_homology_by_contractible by blast

lemma isomorphic_relative_homology_by_contractible:
   "\<lbrakk>contractible_space(subtopology X S); topspace X \<inter> S \<noteq> {}\<rbrakk>
      \<Longrightarrow> relative_homology_group p X S \<cong> reduced_homology_group p X"
  using group.iso_sym group_reduced_homology_group isomorphic_reduced_homology_by_contractible by blast

lemma isomorphic_reduced_homology_by_singleton:
   "a \<in> topspace X \<Longrightarrow> reduced_homology_group p X \<cong> relative_homology_group p X ({a})"
  by (simp add: contractible_space_subtopology_singleton isomorphic_reduced_homology_by_contractible)

lemma isomorphic_relative_homology_by_singleton:
   "a \<in> topspace X \<Longrightarrow> relative_homology_group p X ({a}) \<cong> reduced_homology_group p X"
  by (simp add: group.iso_sym isomorphic_reduced_homology_by_singleton)

lemma reduced_homology_group_pair:
  assumes "t1_space X" and a: "a \<in> topspace X" and b: "b \<in> topspace X" and "a \<noteq> b"
  shows "reduced_homology_group p (subtopology X {a,b}) \<cong> homology_group p (subtopology X {a})"
        (is  "?lhs \<cong> ?rhs")
proof -
  have "?lhs \<cong> relative_homology_group p (subtopology X {a,b}) {b}"
    by (simp add: b isomorphic_reduced_homology_by_singleton topspace_subtopology)
  also have "\<dots> \<cong> ?rhs"
  proof -
    have sub: "subtopology X {a, b} closure_of {b} \<subseteq> subtopology X {a, b} interior_of {b}"
      by (simp add: assms t1_space_subtopology closure_of_singleton subtopology_eq_discrete_topology_finite discrete_topology_closure_of)
    show ?thesis
      using homology_excision_axiom [OF sub, of "{a,b}" p]
      by (simp add: assms(4) group.iso_sym is_isoI subtopology_subtopology)
  qed
  finally show ?thesis .
qed


lemma deformation_retraction_relative_homology_group_isomorphisms:
   "\<lbrakk>retraction_maps X Y r s; r ` U \<subseteq> V; s ` V \<subseteq> U; homotopic_with (\<lambda>h. h ` U \<subseteq> U) X X (s \<circ> r) id\<rbrakk>
    \<Longrightarrow> group_isomorphisms (relative_homology_group p X U) (relative_homology_group p Y V)
             (hom_induced p X U Y V r) (hom_induced p Y V X U s)"
  apply (simp add: retraction_maps_def)
  apply (rule homotopy_equivalence_relative_homology_group_isomorphisms)
       apply (auto simp: image_subset_iff continuous_map_compose homotopic_with_equal)
  done


lemma deformation_retract_relative_homology_group_isomorphisms:
   "\<lbrakk>retraction_maps X Y r id; V \<subseteq> U; r ` U \<subseteq> V; homotopic_with (\<lambda>h. h ` U \<subseteq> U) X X r id\<rbrakk>
        \<Longrightarrow> group_isomorphisms (relative_homology_group p X U) (relative_homology_group p Y V)
             (hom_induced p X U Y V r) (hom_induced p Y V X U id)"
  by (simp add: deformation_retraction_relative_homology_group_isomorphisms)

lemma deformation_retract_relative_homology_group_isomorphism:
   "\<lbrakk>retraction_maps X Y r id; V \<subseteq> U; r ` U \<subseteq> V; homotopic_with (\<lambda>h. h ` U \<subseteq> U) X X r id\<rbrakk>
    \<Longrightarrow> (hom_induced p X U Y V r) \<in> iso (relative_homology_group p X U) (relative_homology_group p Y V)"
  by (metis deformation_retract_relative_homology_group_isomorphisms group_isomorphisms_imp_iso)

lemma deformation_retract_relative_homology_group_isomorphism_id:
   "\<lbrakk>retraction_maps X Y r id; V \<subseteq> U; r ` U \<subseteq> V; homotopic_with (\<lambda>h. h ` U \<subseteq> U) X X r id\<rbrakk>
    \<Longrightarrow> (hom_induced p Y V X U id) \<in> iso (relative_homology_group p Y V) (relative_homology_group p X U)"
  by (metis deformation_retract_relative_homology_group_isomorphisms group_isomorphisms_imp_iso group_isomorphisms_sym)

lemma deformation_retraction_imp_isomorphic_relative_homology_groups:
   "\<lbrakk>retraction_maps X Y r s; r ` U \<subseteq> V; s ` V \<subseteq> U; homotopic_with (\<lambda>h. h ` U \<subseteq> U) X X (s \<circ> r) id\<rbrakk>
    \<Longrightarrow> relative_homology_group p X U \<cong> relative_homology_group p Y V"
  by (blast intro: is_isoI group_isomorphisms_imp_iso deformation_retraction_relative_homology_group_isomorphisms)

lemma deformation_retraction_imp_isomorphic_homology_groups:
   "\<lbrakk>retraction_maps X Y r s; homotopic_with (\<lambda>h. True) X X (s \<circ> r) id\<rbrakk>
        \<Longrightarrow> homology_group p X \<cong> homology_group p Y"
  by (simp add: deformation_retraction_imp_homotopy_equivalent_space homotopy_equivalent_space_imp_isomorphic_homology_groups)

lemma deformation_retract_imp_isomorphic_relative_homology_groups:
   "\<lbrakk>retraction_maps X X' r id; V \<subseteq> U; r ` U \<subseteq> V; homotopic_with (\<lambda>h. h ` U \<subseteq> U) X X r id\<rbrakk>
        \<Longrightarrow> relative_homology_group p X U \<cong> relative_homology_group p X' V"
  by (simp add: deformation_retraction_imp_isomorphic_relative_homology_groups)

lemma deformation_retract_imp_isomorphic_homology_groups:
   "\<lbrakk>retraction_maps X X' r id; homotopic_with (\<lambda>h. True) X X r id\<rbrakk>
        \<Longrightarrow> homology_group p X \<cong> homology_group p X'"
  by (simp add: deformation_retraction_imp_isomorphic_homology_groups)


lemma epi_hom_induced_inclusion:
  assumes "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
  shows "(hom_induced p (subtopology X S) {} X {} id)
   \<in> epi (homology_group p (subtopology X S)) (homology_group p X)"
proof (rule epi_right_invertible)
  show "hom_induced p (subtopology X S) {} X {} id
        \<in> hom (homology_group p (subtopology X S)) (homology_group p X)"
    by (simp add: hom_induced_empty_hom)
  show "hom_induced p X {} (subtopology X S) {} f
      \<in> carrier (homology_group p X) \<rightarrow> carrier (homology_group p (subtopology X S))"
    by (simp add: hom_induced_carrier)
  fix x
  assume "x \<in> carrier (homology_group p X)"
  then show "hom_induced p (subtopology X S) {} X {} id (hom_induced p X {} (subtopology X S) {} f x) = x"
    by (metis  assms continuous_map_id_subt continuous_map_in_subtopology hom_induced_compose' hom_induced_id homology_homotopy_empty homotopic_with_imp_continuous_maps image_empty order_refl)
qed


lemma trivial_homomorphism_hom_induced_relativization:
  assumes "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
  shows "trivial_homomorphism (homology_group p X) (relative_homology_group p X S)
              (hom_induced p X {} X S id)"
proof -
  have "(hom_induced p (subtopology X S) {} X {} id)
      \<in> epi (homology_group p (subtopology X S)) (homology_group p X)"
    by (metis assms epi_hom_induced_inclusion)
  then show ?thesis
    using homology_exactness_axiom_3 [of p X S] homology_exactness_axiom_1 [of p X S]
    by (simp add: epi_def group.trivial_homomorphism_image group_hom.trivial_hom_iff)
qed


lemma mon_hom_boundary_inclusion:
  assumes "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
  shows "(hom_boundary p X S) \<in> mon
             (relative_homology_group p X S) (homology_group (p - 1) (subtopology X S))"
proof -
  have "(hom_induced p (subtopology X S) {} X {} id)
      \<in> epi (homology_group p (subtopology X S)) (homology_group p X)"
    by (metis assms epi_hom_induced_inclusion)
  then show ?thesis
    using homology_exactness_axiom_3 [of p X S] homology_exactness_axiom_1 [of p X S]
    apply (simp add: mon_def epi_def hom_boundary_hom)
    by (metis (no_types, opaque_lifting) group_hom.trivial_hom_iff group_hom.trivial_ker_imp_inj group_hom_axioms_def group_hom_def group_relative_homology_group hom_boundary_hom)
qed

lemma short_exact_sequence_hom_induced_relativization:
  assumes "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
  shows "short_exact_sequence (homology_group (p-1) X) (homology_group (p-1) (subtopology X S)) (relative_homology_group p X S)
                   (hom_induced (p-1) (subtopology X S) {} X {} id) (hom_boundary p X S)"
  unfolding short_exact_sequence_iff
  by (intro conjI homology_exactness_axiom_2 epi_hom_induced_inclusion [OF assms] mon_hom_boundary_inclusion [OF assms])


lemma group_isomorphisms_homology_group_prod_deformation:
  fixes p::int
  assumes "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
  obtains H K where
    "subgroup H (homology_group p (subtopology X S))"
    "subgroup K (homology_group p (subtopology X S))"
    "(\<lambda>(x, y). x \<otimes>\<^bsub>homology_group p (subtopology X S)\<^esub> y)
             \<in> Group.iso (subgroup_generated (homology_group p (subtopology X S)) H \<times>\<times>
                          subgroup_generated (homology_group p (subtopology X S)) K)
                         (homology_group p (subtopology X S))"
    "hom_boundary (p + 1) X S
     \<in> Group.iso (relative_homology_group (p + 1) X S)
         (subgroup_generated (homology_group p (subtopology X S)) H)"
    "hom_induced p (subtopology X S) {} X {} id
     \<in> Group.iso
         (subgroup_generated (homology_group p (subtopology X S)) K)
         (homology_group p X)"
proof -
  let ?rhs = "relative_homology_group (p + 1) X S"
  let ?pXS = "homology_group p (subtopology X S)"
  let ?pX = "homology_group p X"
  let ?hb = "hom_boundary (p + 1) X S"
  let ?hi = "hom_induced p (subtopology X S) {} X {} id"
  have x: "short_exact_sequence (?pX) ?pXS ?rhs ?hi ?hb"
    using short_exact_sequence_hom_induced_relativization [OF assms, of "p + 1"] by simp
  have contf: "continuous_map X (subtopology X S) f"
    by (meson assms continuous_map_in_subtopology homotopic_with_imp_continuous_maps)
  obtain H K where HK: "H \<lhd> ?pXS" "subgroup K ?pXS" "H \<inter> K \<subseteq> {one ?pXS}" "set_mult ?pXS H K = carrier ?pXS"
    and iso: "?hb \<in> iso ?rhs (subgroup_generated ?pXS H)" "?hi \<in> iso (subgroup_generated ?pXS K) ?pX"
    apply (rule splitting_lemma_right [OF x, where g' = "hom_induced p X {} (subtopology X S) {} f"])
      apply (simp add: hom_induced_empty_hom)
     apply (simp add: contf hom_induced_compose')
     apply (metis (full_types) assms(1) hom_induced_id homology_homotopy_empty)
    apply blast
    done
  show ?thesis
  proof
    show "subgroup H ?pXS"
      using HK(1) normal_imp_subgroup by blast
    then show "(\<lambda>(x, y). x \<otimes>\<^bsub>?pXS\<^esub> y)
        \<in> Group.iso (subgroup_generated (?pXS) H \<times>\<times> subgroup_generated (?pXS) K) (?pXS)"
      by (meson HK abelian_relative_homology_group group_disjoint_sum.iso_group_mul group_disjoint_sum_def group_relative_homology_group)
    show "subgroup K ?pXS"
      by (rule HK)
    show "hom_boundary (p + 1) X S \<in> Group.iso ?rhs (subgroup_generated (?pXS) H)"
      using iso int_ops(4) by presburger
    show "hom_induced p (subtopology X S) {} X {} id \<in> Group.iso (subgroup_generated (?pXS) K) (?pX)"
      by (simp add: iso(2))
  qed
qed

lemma iso_homology_group_prod_deformation:
  assumes "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
  shows "homology_group p (subtopology X S)
      \<cong> DirProd (homology_group p X) (relative_homology_group(p + 1) X S)"
    (is "?G \<cong> DirProd ?H ?R")
proof -
  obtain H K where HK:
    "(\<lambda>(x, y). x \<otimes>\<^bsub>?G\<^esub> y)
     \<in> Group.iso (subgroup_generated (?G) H \<times>\<times> subgroup_generated (?G) K) (?G)"
    "hom_boundary (p + 1) X S \<in> Group.iso (?R) (subgroup_generated (?G) H)"
    "hom_induced p (subtopology X S) {} X {} id \<in> Group.iso (subgroup_generated (?G) K) (?H)"
    by (blast intro: group_isomorphisms_homology_group_prod_deformation [OF assms])
  have "?G \<cong> DirProd (subgroup_generated (?G) H) (subgroup_generated (?G) K)"
    by (meson DirProd_group HK(1) group.group_subgroup_generated group.iso_sym group_relative_homology_group is_isoI)
  also have "\<dots> \<cong> DirProd ?R ?H"
    by (meson HK group.DirProd_iso_trans group.group_subgroup_generated group.iso_sym group_relative_homology_group is_isoI)
  also have "\<dots>  \<cong> DirProd ?H ?R"
    by (simp add: DirProd_commute_iso)
  finally show ?thesis .
qed



lemma iso_homology_contractible_space_subtopology1:
  assumes "contractible_space X" "S \<subseteq> topspace X" "S \<noteq> {}"
  shows  "homology_group  0 (subtopology X S) \<cong> DirProd integer_group (relative_homology_group(1) X S)"
proof -
  obtain f where  "homotopic_with (\<lambda>x. True) X X id f" and "f ` (topspace X) \<subseteq> S"
    using assms contractible_space_alt by fastforce
  then have "homology_group 0 (subtopology X S) \<cong> homology_group 0 X \<times>\<times> relative_homology_group 1 X S"
    using iso_homology_group_prod_deformation [of X _ S 0] by auto
  also have "\<dots> \<cong> integer_group \<times>\<times> relative_homology_group 1 X S"
    using assms contractible_imp_path_connected_space group.DirProd_iso_trans group_relative_homology_group iso_refl isomorphic_integer_zeroth_homology_group by blast
  finally show ?thesis .
qed

lemma iso_homology_contractible_space_subtopology2:
  "\<lbrakk>contractible_space X; S \<subseteq> topspace X; p \<noteq> 0; S \<noteq> {}\<rbrakk>
    \<Longrightarrow> homology_group p (subtopology X S) \<cong> relative_homology_group (p + 1) X S"
  by (metis (no_types, opaque_lifting) add.commute isomorphic_group_reduced_homology_of_contractible topspace_subtopology topspace_subtopology_subset un_reduced_homology_group)

lemma trivial_relative_homology_group_contractible_spaces:
   "\<lbrakk>contractible_space X; contractible_space(subtopology X S); topspace X \<inter> S \<noteq> {}\<rbrakk>
        \<Longrightarrow> trivial_group(relative_homology_group p X S)"
  using group_reduced_homology_group group_relative_homology_group isomorphic_group_triviality isomorphic_relative_homology_by_contractible trivial_reduced_homology_group_contractible_space by blast

lemma trivial_relative_homology_group_alt:
  assumes contf: "continuous_map X (subtopology X S) f" and hom: "homotopic_with (\<lambda>k. k ` S \<subseteq> S) X X f id"
  shows "trivial_group (relative_homology_group p X S)"
proof (rule trivial_relative_homology_group_gen [OF contf])
  show "homotopic_with (\<lambda>h. True) (subtopology X S) (subtopology X S) f id"
    using hom unfolding homotopic_with_def
    apply (rule ex_forward)
    apply (auto simp: prod_topology_subtopology continuous_map_in_subtopology continuous_map_from_subtopology image_subset_iff topspace_subtopology)
    done
  show "homotopic_with (\<lambda>k. True) X X f id"
    using assms by (force simp: homotopic_with_def)
qed


lemma iso_hom_induced_relativization_contractible:
  assumes "contractible_space(subtopology X S)" "contractible_space(subtopology X T)" "T \<subseteq> S" "topspace X \<inter> T \<noteq> {}"
  shows "(hom_induced p X T X S id) \<in> iso (relative_homology_group p X T) (relative_homology_group p X S)"
proof (rule very_short_exact_sequence)
  show "exact_seq
         ([relative_homology_group(p - 1) (subtopology X S) T, relative_homology_group p X S, relative_homology_group p X T, relative_homology_group p (subtopology X S) T],
          [hom_relboundary p X S T, hom_induced p X T X S id, hom_induced p (subtopology X S) T X T id])"
    using homology_exactness_triple_1 [OF \<open>T \<subseteq> S\<close>] homology_exactness_triple_3 [OF \<open>T \<subseteq> S\<close>]
    by fastforce
  show "trivial_group (relative_homology_group p (subtopology X S) T)" "trivial_group (relative_homology_group(p - 1) (subtopology X S) T)"
    using assms
    by (force simp: inf.absorb_iff2 subtopology_subtopology topspace_subtopology intro!: trivial_relative_homology_group_contractible_spaces)+
qed

corollary isomorphic_relative_homology_groups_relativization_contractible:
  assumes "contractible_space(subtopology X S)" "contractible_space(subtopology X T)" "T \<subseteq> S" "topspace X \<inter> T \<noteq> {}"
  shows "relative_homology_group p X T \<cong> relative_homology_group p X S"
  by (rule is_isoI) (rule iso_hom_induced_relativization_contractible [OF assms])

lemma iso_hom_induced_inclusion_contractible:
  assumes "contractible_space X" "contractible_space(subtopology X S)" "T \<subseteq> S" "topspace X \<inter> S \<noteq> {}"
  shows "(hom_induced p (subtopology X S) T X T id)
         \<in> iso (relative_homology_group p (subtopology X S) T) (relative_homology_group p X T)"
proof (rule very_short_exact_sequence)
  show "exact_seq
         ([relative_homology_group p X S, relative_homology_group p X T,
           relative_homology_group p (subtopology X S) T, relative_homology_group (p+1) X S],
          [hom_induced p X T X S id, hom_induced p (subtopology X S) T X T id, hom_relboundary (p+1) X S T])"
    using homology_exactness_triple_2 [OF \<open>T \<subseteq> S\<close>] homology_exactness_triple_3 [OF \<open>T \<subseteq> S\<close>]
    by (metis add_diff_cancel_left' diff_add_cancel exact_seq_cons_iff)
  show "trivial_group (relative_homology_group (p+1) X S)" "trivial_group (relative_homology_group p X S)"
    using assms
    by (auto simp: subtopology_subtopology topspace_subtopology intro!: trivial_relative_homology_group_contractible_spaces)
qed

corollary isomorphic_relative_homology_groups_inclusion_contractible:
  assumes "contractible_space X" "contractible_space(subtopology X S)" "T \<subseteq> S" "topspace X \<inter> S \<noteq> {}"
  shows "relative_homology_group p (subtopology X S) T \<cong> relative_homology_group p X T"
  by (rule is_isoI) (rule iso_hom_induced_inclusion_contractible [OF assms])

lemma iso_hom_relboundary_contractible:
  assumes "contractible_space X" "contractible_space(subtopology X T)" "T \<subseteq> S" "topspace X \<inter> T \<noteq> {}"
  shows "hom_relboundary p X S T
         \<in> iso (relative_homology_group p X S) (relative_homology_group (p - 1) (subtopology X S) T)"
proof (rule very_short_exact_sequence)
  show "exact_seq
         ([relative_homology_group (p - 1) X T, relative_homology_group (p - 1) (subtopology X S) T, relative_homology_group p X S, relative_homology_group p X T],
          [hom_induced (p - 1) (subtopology X S) T X T id, hom_relboundary p X S T, hom_induced p X T X S id])"
    using homology_exactness_triple_1 [OF \<open>T \<subseteq> S\<close>] homology_exactness_triple_2 [OF \<open>T \<subseteq> S\<close>] by simp
  show "trivial_group (relative_homology_group p X T)" "trivial_group (relative_homology_group (p - 1) X T)"
    using assms
    by (auto simp: subtopology_subtopology topspace_subtopology intro!: trivial_relative_homology_group_contractible_spaces)
qed

corollary isomorphic_relative_homology_groups_relboundary_contractible:
  assumes "contractible_space X" "contractible_space(subtopology X T)" "T \<subseteq> S" "topspace X \<inter> T \<noteq> {}"
  shows "relative_homology_group p X S \<cong> relative_homology_group (p - 1) (subtopology X S) T"
  by (rule is_isoI) (rule iso_hom_relboundary_contractible [OF assms])

lemma isomorphic_relative_contractible_space_imp_homology_groups:
  assumes "contractible_space X" "contractible_space Y" "S \<subseteq> topspace X" "T \<subseteq> topspace Y"
     and ST: "S = {} \<longleftrightarrow> T = {}"
     and iso: "\<And>p. relative_homology_group p X S \<cong> relative_homology_group p Y T"
  shows "homology_group p (subtopology X S) \<cong> homology_group p (subtopology Y T)"
proof (cases "T = {}")
  case True
  have "homology_group p (subtopology X {}) \<cong> homology_group p (subtopology Y {})"
    by (simp add: homeomorphic_empty_space_eq homeomorphic_space_imp_isomorphic_homology_groups)
  then show ?thesis
    using ST True by blast
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    have "homology_group p (subtopology X S) \<cong> integer_group \<times>\<times> relative_homology_group 1 X S"
      using assms True \<open>T \<noteq> {}\<close>
      by (simp add: iso_homology_contractible_space_subtopology1)
    also have "\<dots>  \<cong> integer_group \<times>\<times> relative_homology_group 1 Y T"
      by (simp add: assms group.DirProd_iso_trans iso_refl)
    also have "\<dots> \<cong> homology_group p (subtopology Y T)"
      by (simp add: True \<open>T \<noteq> {}\<close> assms group.iso_sym iso_homology_contractible_space_subtopology1)
    finally show ?thesis .
  next
    case False
    have "homology_group p (subtopology X S) \<cong> relative_homology_group (p+1) X S"
      using assms False \<open>T \<noteq> {}\<close>
      by (simp add: iso_homology_contractible_space_subtopology2)
    also have "\<dots>  \<cong> relative_homology_group (p+1) Y T"
      by (simp add: assms)
    also have "\<dots> \<cong> homology_group p (subtopology Y T)"
      by (simp add: False \<open>T \<noteq> {}\<close> assms group.iso_sym iso_homology_contractible_space_subtopology2)
    finally show ?thesis .
  qed
qed


subsection\<open>Homology groups of spheres\<close>

lemma iso_reduced_homology_group_lower_hemisphere:
  assumes "k \<le> n"
  shows "hom_induced p (nsphere n) {} (nsphere n) {x. x k \<le> 0} id
      \<in> iso (reduced_homology_group p (nsphere n)) (relative_homology_group p (nsphere n) {x. x k \<le> 0})"
proof (rule iso_reduced_homology_by_contractible)
  show "contractible_space (subtopology (nsphere n) {x. x k \<le> 0})"
    by (simp add: assms contractible_space_lower_hemisphere)
  have "(\<lambda>i. if i = k then -1 else 0) \<in> topspace (nsphere n) \<inter> {x. x k \<le> 0}"
    using assms by (simp add: nsphere if_distrib [of "\<lambda>x. x ^ 2"] cong: if_cong)
  then show "topspace (nsphere n) \<inter> {x. x k \<le> 0} \<noteq> {}"
    by blast
qed


lemma topspace_nsphere_1:
  assumes "x \<in> topspace (nsphere n)" shows "(x k)\<^sup>2 \<le> 1"
proof (cases "k \<le> n")
  case True
  have "(\<Sum>i \<in> {..n} - {k}. (x i)\<^sup>2) = (\<Sum>i\<le>n. (x i)\<^sup>2) - (x k)\<^sup>2"
    using \<open>k \<le> n\<close> by (simp add: sum_diff)
  then show ?thesis
    using assms
    apply (simp add: nsphere)
    by (metis diff_ge_0_iff_ge sum_nonneg zero_le_power2)
next
  case False
  then show ?thesis
    using assms by (simp add: nsphere)
qed

lemma topspace_nsphere_1_eq_0:
  fixes x :: "nat \<Rightarrow> real"
  assumes x: "x \<in> topspace (nsphere n)" and xk: "(x k)\<^sup>2 = 1" and "i \<noteq> k"
  shows "x i = 0"
proof (cases "i \<le> n")
  case True
  have "k \<le> n"
    using x
    by (simp add: nsphere) (metis not_less xk zero_neq_one zero_power2)
  have "(\<Sum>i \<in> {..n} - {k}. (x i)\<^sup>2) = (\<Sum>i\<le>n. (x i)\<^sup>2) - (x k)\<^sup>2"
    using \<open>k \<le> n\<close> by (simp add: sum_diff)
  also have "\<dots> = 0"
    using assms by (simp add: nsphere)
  finally have "\<forall>i\<in>{..n} - {k}. (x i)\<^sup>2 = 0"
    by (simp add: sum_nonneg_eq_0_iff)
  then show ?thesis
    using True \<open>i \<noteq> k\<close> by auto
next
  case False
  with x show ?thesis
    by (simp add: nsphere)
qed


proposition iso_relative_homology_group_upper_hemisphere:
   "(hom_induced p (subtopology (nsphere n) {x. x k \<ge> 0}) {x. x k = 0} (nsphere n) {x. x k \<le> 0} id)
  \<in> iso (relative_homology_group p (subtopology (nsphere n) {x. x k \<ge> 0}) {x. x k = 0})
        (relative_homology_group p (nsphere n) {x. x k \<le> 0})" (is "?h \<in> iso ?G ?H")
proof -
  have "topspace (nsphere n) \<inter> {x. x k < - 1 / 2} \<subseteq> {x \<in> topspace (nsphere n). x k \<in> {y. y \<le> - 1 / 2}}"
    by force
  moreover have "closedin (nsphere n) {x \<in> topspace (nsphere n). x k \<in> {y. y \<le> - 1 / 2}}"
    apply (rule closedin_continuous_map_preimage [OF continuous_map_nsphere_projection])
    using closed_Collect_le [of id "\<lambda>x::real. -1/2"] apply simp
    done
  ultimately have "nsphere n closure_of {x. x k < -1/2} \<subseteq> {x \<in> topspace (nsphere n). x k \<in> {y. y \<le> -1/2}}"
    by (metis (no_types, lifting) closure_of_eq closure_of_mono closure_of_restrict)
  also have "\<dots> \<subseteq> {x \<in> topspace (nsphere n). x k \<in> {y. y < 0}}"
    by force
  also have "\<dots> \<subseteq> nsphere n interior_of {x. x k \<le> 0}"
  proof (rule interior_of_maximal)
    show "{x \<in> topspace (nsphere n). x k \<in> {y. y < 0}} \<subseteq> {x. x k \<le> 0}"
      by force
    show "openin (nsphere n) {x \<in> topspace (nsphere n). x k \<in> {y. y < 0}}"
      apply (rule openin_continuous_map_preimage [OF continuous_map_nsphere_projection])
      using open_Collect_less [of id "\<lambda>x::real. 0"] apply simp
      done
  qed
  finally have nn: "nsphere n closure_of {x. x k < -1/2} \<subseteq> nsphere n interior_of {x. x k \<le> 0}" .
  have [simp]: "{x::nat\<Rightarrow>real. x k \<le> 0} - {x. x k < - (1/2)} = {x. -1/2 \<le> x k \<and> x k \<le> 0}"
               "UNIV - {x::nat\<Rightarrow>real. x k < a} = {x. a \<le> x k}" for a
    by auto
  let ?T01 = "top_of_set {0..1::real}"
  let ?X12 = "subtopology (nsphere n) {x. -1/2 \<le> x k}"
  have 1: "hom_induced p ?X12 {x. -1/2 \<le> x k \<and> x k \<le> 0} (nsphere n) {x. x k \<le> 0} id
         \<in> iso (relative_homology_group p ?X12 {x. -1/2 \<le> x k \<and> x k \<le> 0})
               ?H"
    using homology_excision_axiom [OF nn subset_UNIV, of p] by simp
  define h where "h \<equiv> \<lambda>(T,x). let y = max (x k) (-T) in
                               (\<lambda>i. if i = k then y else sqrt(1 - y ^ 2) / sqrt(1 - x k ^ 2) * x i)"
  have h: "h(T,x) = x" if "0 \<le> T" "T \<le> 1" "(\<Sum>i\<le>n. (x i)\<^sup>2) = 1" and 0: "\<forall>i>n. x i = 0" "-T \<le> x k" for T x
    using that by (force simp: nsphere h_def Let_def max_def intro!: topspace_nsphere_1_eq_0)
  have "continuous_map (prod_topology ?T01 ?X12) euclideanreal (\<lambda>x. h x i)" for i
  proof -
    show ?thesis
    proof (rule continuous_map_eq)
      show "continuous_map (prod_topology ?T01 ?X12)
         euclideanreal (\<lambda>(T, x). if 0 \<le> x k then x i else h (T, x) i)"
        unfolding case_prod_unfold
      proof (rule continuous_map_cases_le)
        show "continuous_map (prod_topology ?T01 ?X12) euclideanreal (\<lambda>x. snd x k)"
          apply (subst continuous_map_of_snd [unfolded o_def])
          by (simp add: continuous_map_from_subtopology continuous_map_nsphere_projection)
      next
        show "continuous_map (subtopology (prod_topology ?T01 ?X12) {p \<in> topspace (prod_topology ?T01 ?X12). 0 \<le> snd p k})
         euclideanreal (\<lambda>x. snd x i)"
          apply (rule continuous_map_from_subtopology)
          apply (subst continuous_map_of_snd [unfolded o_def])
          by (simp add: continuous_map_from_subtopology continuous_map_nsphere_projection)
      next
        note fst = continuous_map_into_fulltopology [OF continuous_map_subtopology_fst]
        have snd: "continuous_map (subtopology (prod_topology ?T01 (subtopology (nsphere n) T)) S) euclideanreal (\<lambda>x. snd x k)" for k S T
          apply (simp add: nsphere)
          apply (rule continuous_map_from_subtopology)
          apply (subst continuous_map_of_snd [unfolded o_def])
          using continuous_map_from_subtopology continuous_map_nsphere_projection nsphere by fastforce
        show "continuous_map (subtopology (prod_topology ?T01 ?X12) {p \<in> topspace (prod_topology ?T01 ?X12). snd p k \<le> 0})
         euclideanreal (\<lambda>x. h (fst x, snd x) i)"
          apply (simp add: h_def case_prod_unfold Let_def)
          apply (intro conjI impI fst snd continuous_intros)
          apply (auto simp: nsphere power2_eq_1_iff)
          done
      qed (auto simp: nsphere h)
    qed (auto simp: nsphere h)
  qed
  moreover
  have "h ` ({0..1} \<times> (topspace (nsphere n) \<inter> {x. - (1/2) \<le> x k}))
     \<subseteq> {x. (\<Sum>i\<le>n. (x i)\<^sup>2) = 1 \<and> (\<forall>i>n. x i = 0)}"
  proof -
    have "(\<Sum>i\<le>n. (h (T,x) i)\<^sup>2) = 1"
      if x: "x \<in> topspace (nsphere n)" and xk: "- (1/2) \<le> x k" and T: "0 \<le> T" "T \<le> 1" for T x
    proof (cases "-T \<le> x k ")
      case True
      then show ?thesis
        using that by (auto simp: nsphere h)
    next
      case False
      with x \<open>0 \<le> T\<close> have "k \<le> n"
        apply (simp add: nsphere)
        by (metis neg_le_0_iff_le not_le)
      have "1 - (x k)\<^sup>2 \<ge> 0"
        using topspace_nsphere_1 x by auto
      with False T \<open>k \<le> n\<close>
      have "(\<Sum>i\<le>n. (h (T,x) i)\<^sup>2) = T\<^sup>2 + (1 - T\<^sup>2) * (\<Sum>i\<in>{..n} - {k}. (x i)\<^sup>2 / (1 - (x k)\<^sup>2))"
        unfolding h_def Let_def max_def
        by (simp add: not_le square_le_1 power_mult_distrib power_divide if_distrib [of "\<lambda>x. x ^ 2"]
              sum.delta_remove sum_distrib_left)
      also have "\<dots> = 1"
        using x False xk \<open>0 \<le> T\<close>
        by (simp add: nsphere sum_diff not_le \<open>k \<le> n\<close> power2_eq_1_iff flip: sum_divide_distrib)
      finally show ?thesis .
    qed
    moreover
    have "h (T,x) i = 0"
      if "x \<in> topspace (nsphere n)" "- (1/2) \<le> x k" and "n < i" "0 \<le> T" "T \<le> 1"
      for T x i
    proof (cases "-T \<le> x k ")
      case False
      then show ?thesis
        using that by (auto simp: nsphere h_def Let_def not_le max_def)
    qed (use that in \<open>auto simp: nsphere h\<close>)
    ultimately show ?thesis
      by auto
  qed
  ultimately
  have cmh: "continuous_map (prod_topology ?T01 ?X12) (nsphere n) h"
    by (subst (2) nsphere) (simp add: continuous_map_in_subtopology continuous_map_componentwise_UNIV)
  have "hom_induced p (subtopology (nsphere n) {x. 0 \<le> x k})
             (topspace (subtopology (nsphere n) {x. 0 \<le> x k}) \<inter> {x. x k = 0}) ?X12
             (topspace ?X12 \<inter> {x. - 1/2 \<le> x k \<and> x k \<le> 0}) id
            \<in> iso (relative_homology_group p (subtopology (nsphere n) {x. 0 \<le> x k})
                       (topspace (subtopology (nsphere n) {x. 0 \<le> x k}) \<inter> {x. x k = 0}))
                (relative_homology_group p ?X12 (topspace ?X12 \<inter> {x. - 1/2 \<le> x k \<and> x k \<le> 0}))"
  proof (rule deformation_retract_relative_homology_group_isomorphism_id)
    show "retraction_maps ?X12 (subtopology (nsphere n) {x. 0 \<le> x k}) (h \<circ> (\<lambda>x. (0,x))) id"
      unfolding retraction_maps_def
    proof (intro conjI ballI)
      show "continuous_map ?X12 (subtopology (nsphere n) {x. 0 \<le> x k}) (h \<circ> Pair 0)"
        apply (simp add: continuous_map_in_subtopology)
        apply (intro conjI continuous_map_compose [OF _ cmh] continuous_intros)
          apply (auto simp: h_def Let_def)
        done
      show "continuous_map (subtopology (nsphere n) {x. 0 \<le> x k}) ?X12 id"
        by (simp add: continuous_map_in_subtopology) (auto simp: nsphere)
    qed (simp add: nsphere h)
  next
    have h0: "\<And>xa. \<lbrakk>xa \<in> topspace (nsphere n); - (1/2) \<le> xa k; xa k \<le> 0\<rbrakk> \<Longrightarrow> h (0, xa) k = 0"
      by (simp add: h_def Let_def)
    show "(h \<circ> (\<lambda>x. (0,x))) ` (topspace ?X12 \<inter> {x. - 1 / 2 \<le> x k \<and> x k \<le> 0})
        \<subseteq> topspace (subtopology (nsphere n) {x. 0 \<le> x k}) \<inter> {x. x k = 0}"
      apply (auto simp: h0)
      apply (rule subsetD [OF continuous_map_image_subset_topspace [OF cmh]])
      apply (force simp: nsphere)
      done
    have hin: "\<And>t x. \<lbrakk>x \<in> topspace (nsphere n); - (1/2) \<le> x k; 0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> h (t,x) \<in> topspace (nsphere n)"
      apply (rule subsetD [OF continuous_map_image_subset_topspace [OF cmh]])
      apply (force simp: nsphere)
      done
    have h1: "\<And>x. \<lbrakk>x \<in> topspace (nsphere n); - (1/2) \<le> x k\<rbrakk> \<Longrightarrow> h (1, x) = x"
      by (simp add: h nsphere)
    have "continuous_map (prod_topology ?T01 ?X12) (nsphere n) h"
      using cmh by force
    then show "homotopic_with
                 (\<lambda>h. h ` (topspace ?X12 \<inter> {x. - 1 / 2 \<le> x k \<and> x k \<le> 0}) \<subseteq> topspace ?X12 \<inter> {x. - 1 / 2 \<le> x k \<and> x k \<le> 0})
                 ?X12 ?X12 (h \<circ> (\<lambda>x. (0,x))) id"
      apply (subst homotopic_with, force)
      apply (rule_tac x=h in exI)
      apply (auto simp: hin h1 continuous_map_in_subtopology)
         apply (auto simp: h_def Let_def max_def)
      done
  qed auto
  then have 2: "hom_induced p (subtopology (nsphere n) {x. 0 \<le> x k}) {x. x k = 0}
             ?X12 {x. - 1/2 \<le> x k \<and> x k \<le> 0} id
            \<in> Group.iso
                (relative_homology_group p (subtopology (nsphere n) {x. 0 \<le> x k}) {x. x k = 0})
                (relative_homology_group p ?X12 {x. - 1/2 \<le> x k \<and> x k \<le> 0})"
    by (metis hom_induced_restrict relative_homology_group_restrict topspace_subtopology)
  show ?thesis
    using iso_set_trans [OF 2 1]
    by (simp add: subset_iff continuous_map_in_subtopology flip: hom_induced_compose)
qed


corollary iso_upper_hemisphere_reduced_homology_group:
   "(hom_boundary (1 + p) (subtopology (nsphere (Suc n)) {x. x(Suc n) \<ge> 0}) {x. x(Suc n) = 0})
  \<in> iso (relative_homology_group (1 + p) (subtopology (nsphere (Suc n)) {x. x(Suc n) \<ge> 0}) {x. x(Suc n) = 0})
        (reduced_homology_group p (nsphere n))"
proof -
  have "{x. 0 \<le> x (Suc n)} \<inter> {x. x (Suc n) = 0} = {x. x (Suc n) = (0::real)}"
    by auto
  then have n: "nsphere n = subtopology (subtopology (nsphere (Suc n)) {x. x(Suc n) \<ge> 0}) {x. x(Suc n) = 0}"
    by (simp add: subtopology_nsphere_equator subtopology_subtopology)
  have ne: "(\<lambda>i. if i = n then 1 else 0) \<in> topspace (subtopology (nsphere (Suc n)) {x. 0 \<le> x (Suc n)}) \<inter> {x. x (Suc n) = 0}"
    by (simp add: nsphere if_distrib [of "\<lambda>x. x ^ 2"] cong: if_cong)
  show ?thesis
    unfolding n
    apply (rule iso_relative_homology_of_contractible [where p = "1 + p", simplified])
    using contractible_space_upper_hemisphere ne apply blast+
    done
qed

corollary iso_reduced_homology_group_upper_hemisphere:
  assumes "k \<le> n"
  shows "hom_induced p (nsphere n) {} (nsphere n) {x. x k \<ge> 0} id
      \<in> iso (reduced_homology_group p (nsphere n)) (relative_homology_group p (nsphere n) {x. x k \<ge> 0})"
proof (rule iso_reduced_homology_by_contractible [OF contractible_space_upper_hemisphere [OF assms]])
  have "(\<lambda>i. if i = k then 1 else 0) \<in> topspace (nsphere n) \<inter> {x. 0 \<le> x k}"
    using assms by (simp add: nsphere if_distrib [of "\<lambda>x. x ^ 2"] cong: if_cong)
  then show "topspace (nsphere n) \<inter> {x. 0 \<le> x k} \<noteq> {}"
    by blast
qed


lemma iso_relative_homology_group_lower_hemisphere:
  "hom_induced p (subtopology (nsphere n) {x. x k \<le> 0}) {x. x k = 0} (nsphere n) {x. x k \<ge> 0} id
  \<in> iso (relative_homology_group p (subtopology (nsphere n) {x. x k \<le> 0}) {x. x k = 0})
        (relative_homology_group p (nsphere n) {x. x k \<ge> 0})" (is "?k \<in> iso ?G ?H")
proof -
  define r where "r \<equiv> \<lambda>x i. if i = k then -x i else (x i::real)"
  then have [simp]: "r \<circ> r = id"
    by force
  have cmr: "continuous_map (subtopology (nsphere n) S) (nsphere n) r" for S
    using continuous_map_nsphere_reflection [of n k]
    by (simp add: continuous_map_from_subtopology r_def)
  let ?f = "hom_induced p (subtopology (nsphere n) {x. x k \<le> 0}) {x. x k = 0}
                          (subtopology (nsphere n) {x. x k \<ge> 0}) {x. x k = 0} r"
  let ?g = "hom_induced p (subtopology (nsphere n) {x. x k \<ge> 0}) {x. x k = 0} (nsphere n) {x. x k \<le> 0} id"
  let ?h = "hom_induced p (nsphere n) {x. x k \<le> 0} (nsphere n) {x. x k \<ge> 0} r"
  obtain f h where
        f: "f \<in> iso ?G (relative_homology_group p (subtopology (nsphere n) {x. x k \<ge> 0}) {x. x k = 0})"
    and h: "h \<in> iso (relative_homology_group p (nsphere n) {x. x k \<le> 0}) ?H"
    and eq: "h \<circ> ?g \<circ> f = ?k"
  proof
    have hmr: "homeomorphic_map (nsphere n) (nsphere n) r"
      unfolding homeomorphic_map_maps
      by (metis \<open>r \<circ> r = id\<close> cmr homeomorphic_maps_involution pointfree_idE subtopology_topspace)
    then have hmrs: "homeomorphic_map (subtopology (nsphere n) {x. x k \<le> 0}) (subtopology (nsphere n) {x. x k \<ge> 0}) r"
      by (simp add: homeomorphic_map_subtopologies_alt r_def)
    have rimeq: "r ` (topspace (subtopology (nsphere n) {x. x k \<le> 0}) \<inter> {x. x k = 0})
               = topspace (subtopology (nsphere n) {x. 0 \<le> x k}) \<inter> {x. x k = 0}"
      using continuous_map_eq_topcontinuous_at continuous_map_nsphere_reflection topcontinuous_at_atin
      by (fastforce simp: r_def)
    show "?f \<in> iso ?G (relative_homology_group p (subtopology (nsphere n) {x. x k \<ge> 0}) {x. x k = 0})"
      using homeomorphic_map_relative_homology_iso [OF hmrs Int_lower1 rimeq]
      by (metis hom_induced_restrict relative_homology_group_restrict)
    have rimeq: "r ` (topspace (nsphere n) \<inter> {x. x k \<le> 0}) = topspace (nsphere n) \<inter> {x. 0 \<le> x k}"
      by (metis hmrs homeomorphic_imp_surjective_map topspace_subtopology)
    show "?h \<in> Group.iso (relative_homology_group p (nsphere n) {x. x k \<le> 0}) ?H"
      using homeomorphic_map_relative_homology_iso [OF hmr Int_lower1 rimeq] by simp
    have [simp]: "\<And>x. x k = 0 \<Longrightarrow> r x k = 0"
      by (auto simp: r_def)
    have "?h \<circ> ?g \<circ> ?f
        = hom_induced p (subtopology (nsphere n) {x. 0 \<le> x k}) {x. x k = 0} (nsphere n) {x. 0 \<le> x k} r \<circ>
          hom_induced p (subtopology (nsphere n) {x. x k \<le> 0}) {x. x k = 0} (subtopology (nsphere n) {x. 0 \<le> x k}) {x. x k = 0} r"
      apply (subst hom_induced_compose [symmetric])
      using continuous_map_nsphere_reflection apply (force simp: r_def)+
      done
    also have "\<dots> = ?k"
      apply (subst hom_induced_compose [symmetric])
          apply (simp_all add: image_subset_iff cmr)
      using hmrs homeomorphic_imp_continuous_map apply blast
      done
    finally show "?h \<circ> ?g \<circ> ?f = ?k" .
  qed
  with iso_relative_homology_group_upper_hemisphere [of p n k]
  have "h \<circ> hom_induced p (subtopology (nsphere n) {f. 0 \<le> f k}) {f. f k = 0} (nsphere n) {f. f k \<le> 0} id \<circ> f
  \<in> Group.iso ?G (relative_homology_group p (nsphere n) {f. 0 \<le> f k})"
    using f h iso_set_trans by blast
  then show ?thesis
    by (simp add: eq)
qed


lemma iso_lower_hemisphere_reduced_homology_group:
   "hom_boundary (1 + p) (subtopology (nsphere (Suc n)) {x. x(Suc n) \<le> 0}) {x. x(Suc n) = 0}
  \<in> iso (relative_homology_group (1 + p) (subtopology (nsphere (Suc n)) {x. x(Suc n) \<le> 0})
                        {x. x(Suc n) = 0})
        (reduced_homology_group p (nsphere n))"
proof -
  have "{x. (\<Sum>i\<le>n. (x i)\<^sup>2) = 1 \<and> (\<forall>i>n. x i = 0)} =
       ({x. (\<Sum>i\<le>n. (x i)\<^sup>2) + (x (Suc n))\<^sup>2 = 1 \<and> (\<forall>i>Suc n. x i = 0)} \<inter> {x. x (Suc n) \<le> 0} \<inter>
        {x. x (Suc n) = (0::real)})"
    by (force simp: dest: Suc_lessI)
  then have n: "nsphere n = subtopology (subtopology (nsphere (Suc n)) {x. x(Suc n) \<le> 0}) {x. x(Suc n) = 0}"
    by (simp add: nsphere subtopology_subtopology)
  have ne: "(\<lambda>i. if i = n then 1 else 0) \<in> topspace (subtopology (nsphere (Suc n)) {x. x (Suc n) \<le> 0}) \<inter> {x. x (Suc n) = 0}"
    by (simp add: nsphere if_distrib [of "\<lambda>x. x ^ 2"] cong: if_cong)
  show ?thesis
    unfolding n
    apply (rule iso_relative_homology_of_contractible [where p = "1 + p", simplified])
    using contractible_space_lower_hemisphere ne apply blast+
    done
qed

lemma isomorphism_sym:
  "\<lbrakk>f \<in> iso G1 G2; \<And>x. x \<in> carrier G1 \<Longrightarrow> r'(f x) = f(r x);
     \<And>x. x \<in> carrier G1 \<Longrightarrow> r x \<in> carrier G1; group G1; group G2\<rbrakk>
      \<Longrightarrow> \<exists>f \<in> iso G2 G1. \<forall>x \<in> carrier G2. r(f x) = f(r' x)"
  apply (clarsimp simp add: group.iso_iff_group_isomorphisms Bex_def)
  by (metis (full_types) group_isomorphisms_def group_isomorphisms_sym hom_in_carrier)

lemma isomorphism_trans:
  "\<lbrakk>\<exists>f \<in> iso G1 G2. \<forall>x \<in> carrier G1. r2(f x) = f(r1 x); \<exists>f \<in> iso G2 G3. \<forall>x \<in> carrier G2. r3(f x) = f(r2 x)\<rbrakk>
   \<Longrightarrow> \<exists>f \<in> iso G1 G3. \<forall>x \<in> carrier G1. r3(f x) = f(r1 x)"
  apply clarify
  apply (rename_tac g f)
  apply (rule_tac x="f \<circ> g" in bexI)
  apply (metis iso_iff comp_apply hom_in_carrier)
  using iso_set_trans by blast

lemma reduced_homology_group_nsphere_step:
   "\<exists>f \<in> iso(reduced_homology_group p (nsphere n))
            (reduced_homology_group (1 + p) (nsphere (Suc n))).
        \<forall>c \<in> carrier(reduced_homology_group p (nsphere n)).
             hom_induced (1 + p) (nsphere(Suc n)) {} (nsphere(Suc n)) {}
                         (\<lambda>x i. if i = 0 then -x i else x i) (f c)
           = f (hom_induced p (nsphere n) {} (nsphere n) {} (\<lambda>x i. if i = 0 then -x i else x i) c)"
proof -
  define r where "r \<equiv> \<lambda>x::nat\<Rightarrow>real. \<lambda>i. if i = 0 then -x i else x i"
  have cmr: "continuous_map (nsphere n) (nsphere n) r" for n
    unfolding r_def by (rule continuous_map_nsphere_reflection)
  have rsub: "r ` {x. 0 \<le> x (Suc n)} \<subseteq> {x. 0 \<le> x (Suc n)}" "r ` {x. x (Suc n) \<le> 0} \<subseteq> {x. x (Suc n) \<le> 0}" "r ` {x. x (Suc n) = 0} \<subseteq> {x. x (Suc n) = 0}"
    by (force simp: r_def)+
  let ?sub = "subtopology (nsphere (Suc n)) {x. x (Suc n) \<ge> 0}"
  let ?G2 = "relative_homology_group (1 + p) ?sub {x. x (Suc n) = 0}"
  let ?r2 = "hom_induced (1 + p) ?sub {x. x (Suc n) = 0} ?sub {x. x (Suc n) = 0} r"
  let ?j = "\<lambda>p n. hom_induced p (nsphere n) {} (nsphere n) {} r"
  show ?thesis
    unfolding r_def [symmetric]
  proof (rule isomorphism_trans)
    let ?f = "hom_boundary (1 + p) ?sub {x. x (Suc n) = 0}"
    show "\<exists>f\<in>Group.iso (reduced_homology_group p (nsphere n)) ?G2.
           \<forall>c\<in>carrier (reduced_homology_group p (nsphere n)). ?r2 (f c) = f (?j p n c)"
    proof (rule isomorphism_sym)
      show "?f \<in> Group.iso ?G2 (reduced_homology_group p (nsphere n))"
        using iso_upper_hemisphere_reduced_homology_group
        by (metis add.commute)
    next
      fix c
      assume "c \<in> carrier ?G2"
      have cmrs: "continuous_map ?sub ?sub r"
        by (metis (mono_tags, lifting) IntE cmr continuous_map_from_subtopology continuous_map_in_subtopology image_subset_iff rsub(1) topspace_subtopology)
      have "hom_induced p (nsphere n) {} (nsphere n) {} r \<circ> hom_boundary (1 + p) ?sub {x. x (Suc n) = 0}
          = hom_boundary (1 + p) ?sub {x. x (Suc n) = 0} \<circ>
            hom_induced (1 + p) ?sub {x. x (Suc n) = 0} ?sub {x. x (Suc n) = 0} r"
        using naturality_hom_induced [OF cmrs rsub(3), symmetric, of "1+p", simplified]
        by (simp add: subtopology_subtopology subtopology_nsphere_equator flip: Collect_conj_eq cong: rev_conj_cong)
      then show "?j p n (?f c) = ?f (hom_induced (1 + p) ?sub {x. x (Suc n) = 0} ?sub {x. x (Suc n) = 0} r c)"
        by (metis comp_def)
    next
      fix c
      assume "c \<in> carrier ?G2"
      show "hom_induced (1 + p) ?sub {x. x (Suc n) = 0} ?sub {x. x (Suc n) = 0} r c \<in> carrier ?G2"
        using hom_induced_carrier by blast
    qed auto
  next
    let ?H2 = "relative_homology_group (1 + p) (nsphere (Suc n)) {x. x (Suc n) \<le> 0}"
    let ?s2 = "hom_induced (1 + p) (nsphere (Suc n)) {x. x (Suc n) \<le> 0} (nsphere (Suc n)) {x. x (Suc n) \<le> 0} r"
    show "\<exists>f\<in>Group.iso ?G2 (reduced_homology_group (1 + p) (nsphere (Suc n))). \<forall>c\<in>carrier ?G2. ?j (1 + p) (Suc n) (f c)
            = f (?r2 c)"
    proof (rule isomorphism_trans)
      show "\<exists>f\<in>Group.iso ?G2 ?H2.
                 \<forall>c\<in>carrier ?G2.
                    ?s2 (f c) = f (hom_induced (1 + p) ?sub {x. x (Suc n) = 0} ?sub {x. x (Suc n) = 0} r c)"
      proof (intro ballI bexI)
        fix c
        assume "c \<in> carrier (relative_homology_group (1 + p) ?sub {x. x (Suc n) = 0})"
        show "?s2 (hom_induced (1 + p) ?sub {x. x (Suc n) = 0} (nsphere (Suc n)) {x. x (Suc n) \<le> 0} id c)
            = hom_induced (1 + p) ?sub {x. x (Suc n) = 0} (nsphere (Suc n)) {x. x (Suc n) \<le> 0} id (?r2 c)"
          apply (simp add: rsub hom_induced_compose' Collect_mono_iff cmr)
          apply (subst hom_induced_compose')
              apply (simp_all add: continuous_map_in_subtopology continuous_map_from_subtopology [OF cmr] rsub)
           apply (auto simp: r_def)
          done
      qed (simp add: iso_relative_homology_group_upper_hemisphere)
    next
      let ?h = "hom_induced (1 + p) (nsphere(Suc n)) {} (nsphere (Suc n)) {x. x(Suc n) \<le> 0} id"
      show "\<exists>f\<in>Group.iso ?H2 (reduced_homology_group (1 + p) (nsphere (Suc n))).
               \<forall>c\<in>carrier ?H2. ?j (1 + p) (Suc n) (f c) = f (?s2 c)"
      proof (rule isomorphism_sym)
        show "?h \<in> Group.iso (reduced_homology_group (1 + p) (nsphere (Suc n)))
               (relative_homology_group (1 + p) (nsphere (Suc n)) {x. x (Suc n) \<le> 0})"
          using iso_reduced_homology_group_lower_hemisphere by blast
      next
        fix c
        assume "c \<in> carrier (reduced_homology_group (1 + p) (nsphere (Suc n)))"
        show "?s2 (?h c) = ?h (?j (1 + p) (Suc n)  c)"
          by (simp add: hom_induced_compose' cmr rsub)
      next
        fix c
        assume "c \<in> carrier (reduced_homology_group (1 + p) (nsphere (Suc n)))"
        then show "hom_induced (1 + p) (nsphere (Suc n)) {} (nsphere (Suc n)) {} r c
        \<in> carrier (reduced_homology_group (1 + p) (nsphere (Suc n)))"
          by (simp add: hom_induced_reduced)
      qed auto
    qed
  qed
qed


lemma reduced_homology_group_nsphere_aux:
  "if p = int n then reduced_homology_group n (nsphere n) \<cong> integer_group
                     else trivial_group(reduced_homology_group p (nsphere n))"
proof (induction n arbitrary: p)
  case 0
  let ?a = "\<lambda>i::nat. if i = 0 then 1 else (0::real)"
  let ?b = "\<lambda>i::nat. if i = 0 then -1 else (0::real)"
  have st: "subtopology (powertop_real UNIV) {?a, ?b} = nsphere 0"
  proof -
    have "{?a, ?b} = {x. (x 0)\<^sup>2 = 1 \<and> (\<forall>i>0. x i = 0)}"
      using power2_eq_iff by fastforce
    then show ?thesis
      by (simp add: nsphere)
  qed
  have *: "reduced_homology_group p (subtopology (powertop_real UNIV) {?a, ?b}) \<cong>
        homology_group p (subtopology (powertop_real UNIV) {?a})"
    apply (rule reduced_homology_group_pair)
      apply (simp_all add: fun_eq_iff)
    apply (simp add: open_fun_def separation_t1 t1_space_def)
    done
  have "reduced_homology_group 0 (nsphere 0) \<cong> integer_group" if "p=0"
  proof -
    have "reduced_homology_group 0 (nsphere 0) \<cong> homology_group 0 (top_of_set {?a})" if "p=0"
      by (metis * euclidean_product_topology st that)
    also have "\<dots> \<cong> integer_group"
      by (simp add: homology_coefficients)
    finally show ?thesis
      using that by blast
  qed
  moreover have "trivial_group (reduced_homology_group p (nsphere 0))" if "p\<noteq>0"
    using * that homology_dimension_axiom [of "subtopology (powertop_real UNIV) {?a}" ?a p]
    using isomorphic_group_triviality st by force
  ultimately show ?case
    by auto
next
  case (Suc n)
  have eq: "reduced_homology_group (int n) (nsphere n) \<cong> integer_group" if "p-1 = n"
    by (simp add: Suc.IH)
  have neq: "trivial_group (reduced_homology_group (p-1) (nsphere n))" if "p-1 \<noteq> n"
    by (simp add: Suc.IH that)
  have iso: "reduced_homology_group p (nsphere (Suc n)) \<cong> reduced_homology_group (p-1) (nsphere n)"
    using reduced_homology_group_nsphere_step [of "p-1" n]  group.iso_sym [OF _ is_isoI] group_reduced_homology_group
    by fastforce
  then show ?case
    using eq iso_trans iso isomorphic_group_triviality neq
    by (metis (no_types, opaque_lifting) add.commute add_left_cancel diff_add_cancel group_reduced_homology_group of_nat_Suc)
qed


lemma reduced_homology_group_nsphere:
  "reduced_homology_group n (nsphere n) \<cong> integer_group"
  "p \<noteq> n \<Longrightarrow> trivial_group(reduced_homology_group p (nsphere n))"
  using reduced_homology_group_nsphere_aux by auto

lemma cyclic_reduced_homology_group_nsphere:
   "cyclic_group(reduced_homology_group p (nsphere n))"
  by (metis reduced_homology_group_nsphere trivial_imp_cyclic_group cyclic_integer_group
      group_integer_group group_reduced_homology_group isomorphic_group_cyclicity)

lemma trivial_reduced_homology_group_nsphere:
   "trivial_group(reduced_homology_group p (nsphere n)) \<longleftrightarrow> (p \<noteq> n)"
  using group_integer_group isomorphic_group_triviality nontrivial_integer_group reduced_homology_group_nsphere(1) reduced_homology_group_nsphere(2) trivial_group_def by blast

lemma non_contractible_space_nsphere: "\<not> (contractible_space(nsphere n))"
  proof (clarsimp simp add: contractible_eq_homotopy_equivalent_singleton_subtopology)
  fix a :: "nat \<Rightarrow> real"
  assume a: "a \<in> topspace (nsphere n)"
    and he: "nsphere n homotopy_equivalent_space subtopology (nsphere n) {a}"
  have "trivial_group (reduced_homology_group (int n) (subtopology (nsphere n) {a}))"
    by (simp add: a homology_dimension_reduced [where a=a])
  then show "False"
    using isomorphic_group_triviality [OF homotopy_equivalent_space_imp_isomorphic_reduced_homology_groups [OF he, of n]]
    by (simp add: trivial_reduced_homology_group_nsphere)
qed


subsection\<open>Brouwer degree of a Map\<close>

definition Brouwer_degree2 :: "nat \<Rightarrow> ((nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> int"
  where
 "Brouwer_degree2 p f \<equiv>
    @d::int. \<forall>x \<in> carrier(reduced_homology_group p (nsphere p)).
                hom_induced p (nsphere p) {} (nsphere p) {} f x = pow (reduced_homology_group p (nsphere p)) x d"

lemma Brouwer_degree2_eq:
   "(\<And>x. x \<in> topspace(nsphere p) \<Longrightarrow> f x = g x) \<Longrightarrow> Brouwer_degree2 p f = Brouwer_degree2 p g"
  unfolding Brouwer_degree2_def Ball_def
  apply (intro Eps_cong all_cong)
  by (metis (mono_tags, lifting) hom_induced_eq)

lemma Brouwer_degree2:
  assumes "x \<in> carrier(reduced_homology_group p (nsphere p))"
  shows "hom_induced p (nsphere p) {} (nsphere p) {} f x
       = pow (reduced_homology_group p (nsphere p)) x (Brouwer_degree2 p f)"
       (is "?h x = pow ?G x _")
proof (cases "continuous_map(nsphere p) (nsphere p) f")
  case True
  interpret group ?G
    by simp
  interpret group_hom ?G ?G ?h
    using hom_induced_reduced_hom group_hom_axioms_def group_hom_def is_group by blast
  obtain a where a: "a \<in> carrier ?G"
    and aeq: "subgroup_generated ?G {a} = ?G"
    using cyclic_reduced_homology_group_nsphere [of p p] by (auto simp: cyclic_group_def)
  then have carra: "carrier (subgroup_generated ?G {a}) = range (\<lambda>n::int. pow ?G a n)"
    using carrier_subgroup_generated_by_singleton by blast
  moreover have "?h a \<in> carrier (subgroup_generated ?G {a})"
    by (simp add: a aeq hom_induced_reduced)
  ultimately obtain d::int where d: "?h a = pow ?G a d"
    by auto
  have *: "hom_induced (int p) (nsphere p) {} (nsphere p) {} f x = x [^]\<^bsub>?G\<^esub> d"
    if x: "x \<in> carrier ?G" for x
  proof -
    obtain n::int where xeq: "x = pow ?G a n"
      using carra x aeq by moura
    show ?thesis
      by (simp add: xeq a d hom_int_pow int_pow_pow mult.commute)
  qed
  show ?thesis
    unfolding Brouwer_degree2_def
    apply (rule someI2 [where a=d])
    using assms * apply blast+
    done
next
  case False
  show ?thesis
    unfolding Brouwer_degree2_def
    by (rule someI2 [where a=0]) (simp_all add: hom_induced_default False one_reduced_homology_group assms)
qed



lemma Brouwer_degree2_iff:
  assumes f: "continuous_map (nsphere p) (nsphere p) f"
    and x: "x \<in> carrier(reduced_homology_group p (nsphere p))"
  shows "(hom_induced (int p) (nsphere p) {} (nsphere p) {} f x =
         x [^]\<^bsub>reduced_homology_group (int p) (nsphere p)\<^esub> d)
    \<longleftrightarrow> (x = \<one>\<^bsub>reduced_homology_group (int p) (nsphere p)\<^esub> \<or> Brouwer_degree2 p f = d)"
    (is  "(?h x = x [^]\<^bsub>?G\<^esub> d) \<longleftrightarrow> _")
proof -
  interpret group "?G"
    by simp
  obtain a where a: "a \<in> carrier ?G"
    and aeq: "subgroup_generated ?G {a} = ?G"
    using cyclic_reduced_homology_group_nsphere [of p p] by (auto simp: cyclic_group_def)
  then obtain i::int where i: "x = (a [^]\<^bsub>?G\<^esub> i)"
    using carrier_subgroup_generated_by_singleton x by fastforce
  then have "a [^]\<^bsub>?G\<^esub> i \<in> carrier ?G"
    using x by blast
  have [simp]: "ord a = 0"
    by (simp add: a aeq iso_finite [OF reduced_homology_group_nsphere(1)] flip: infinite_cyclic_subgroup_order)
  show ?thesis
    by (auto simp: Brouwer_degree2 int_pow_eq_id x i a int_pow_pow int_pow_eq)
qed


lemma Brouwer_degree2_unique:
  assumes f: "continuous_map (nsphere p) (nsphere p) f"
    and hi: "\<And>x. x \<in> carrier(reduced_homology_group p (nsphere p))
               \<Longrightarrow> hom_induced p (nsphere p) {} (nsphere p) {} f x = pow (reduced_homology_group p (nsphere p)) x d"
          (is "\<And>x. x \<in> carrier ?G \<Longrightarrow> ?h x = _")
  shows "Brouwer_degree2 p f = d"
proof -
  obtain a where a: "a \<in> carrier ?G"
    and aeq: "subgroup_generated ?G {a} = ?G"
    using cyclic_reduced_homology_group_nsphere [of p p] by (auto simp: cyclic_group_def)
  show ?thesis
    using hi [OF a]
    apply (simp add: Brouwer_degree2 a)
    by (metis Brouwer_degree2_iff a aeq f group.trivial_group_subgroup_generated group_reduced_homology_group subsetI trivial_reduced_homology_group_nsphere)
qed

lemma Brouwer_degree2_unique_generator:
  assumes f: "continuous_map (nsphere p) (nsphere p) f"
    and eq: "subgroup_generated (reduced_homology_group p (nsphere p)) {a}
           = reduced_homology_group p (nsphere p)"
    and hi: "hom_induced p (nsphere p) {} (nsphere p) {} f a = pow (reduced_homology_group p (nsphere p)) a d"
          (is "?h a = pow ?G a _")
  shows "Brouwer_degree2 p f = d"
proof (cases "a \<in> carrier ?G")
  case True
  then show ?thesis
    by (metis Brouwer_degree2_iff hi eq f group.trivial_group_subgroup_generated group_reduced_homology_group
              subset_singleton_iff trivial_reduced_homology_group_nsphere)
next
  case False
  then show ?thesis
    using trivial_reduced_homology_group_nsphere [of p p]
    by (metis group.trivial_group_subgroup_generated_eq disjoint_insert(1) eq group_reduced_homology_group inf_bot_right subset_singleton_iff)
qed

lemma Brouwer_degree2_homotopic:
  assumes "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) f g"
  shows "Brouwer_degree2 p f = Brouwer_degree2 p g"
proof -
  have "continuous_map (nsphere p) (nsphere p) f"
    using homotopic_with_imp_continuous_maps [OF assms] by auto
  show ?thesis
    using Brouwer_degree2_def assms homology_homotopy_empty by fastforce
qed

lemma Brouwer_degree2_id [simp]: "Brouwer_degree2 p id = 1"
proof (rule Brouwer_degree2_unique)
  fix x
  assume x: "x \<in> carrier (reduced_homology_group (int p) (nsphere p))"
  then have "x \<in> carrier (homology_group (int p) (nsphere p))"
    using carrier_reduced_homology_group_subset by blast
  then show "hom_induced (int p) (nsphere p) {} (nsphere p) {} id x =
        x [^]\<^bsub>reduced_homology_group (int p) (nsphere p)\<^esub> (1::int)"
    by (simp add: hom_induced_id group.int_pow_1 x)
qed auto

lemma Brouwer_degree2_compose:
  assumes f: "continuous_map (nsphere p) (nsphere p) f" and g: "continuous_map (nsphere p) (nsphere p) g"
  shows "Brouwer_degree2 p (g \<circ> f) = Brouwer_degree2 p g * Brouwer_degree2 p f"
proof (rule Brouwer_degree2_unique)
  show "continuous_map (nsphere p) (nsphere p) (g \<circ> f)"
    by (meson continuous_map_compose f g)
next
  fix x
  assume x: "x \<in> carrier (reduced_homology_group (int p) (nsphere p))"
  have "hom_induced (int p) (nsphere p) {} (nsphere p) {} (g \<circ> f) =
             hom_induced (int p) (nsphere p) {} (nsphere p) {} g \<circ>
             hom_induced (int p) (nsphere p) {} (nsphere p) {} f"
    by (blast intro: hom_induced_compose [OF f _ g])
  with x show "hom_induced (int p) (nsphere p) {} (nsphere p) {} (g \<circ> f) x =
        x [^]\<^bsub>reduced_homology_group (int p) (nsphere p)\<^esub> (Brouwer_degree2 p g * Brouwer_degree2 p f)"
    by (simp add: mult.commute hom_induced_reduced flip: Brouwer_degree2 group.int_pow_pow)
qed

lemma Brouwer_degree2_homotopy_equivalence:
  assumes f: "continuous_map (nsphere p) (nsphere p) f" and g: "continuous_map (nsphere p) (nsphere p) g"
    and hom: "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) (f \<circ> g) id"
  obtains "\<bar>Brouwer_degree2 p f\<bar> = 1" "\<bar>Brouwer_degree2 p g\<bar> = 1" "Brouwer_degree2 p g = Brouwer_degree2 p f"
  using Brouwer_degree2_homotopic [OF hom] Brouwer_degree2_compose f g zmult_eq_1_iff by auto

lemma Brouwer_degree2_homeomorphic_maps:
  assumes "homeomorphic_maps (nsphere p) (nsphere p) f g"
  obtains "\<bar>Brouwer_degree2 p f\<bar> = 1" "\<bar>Brouwer_degree2 p g\<bar> = 1" "Brouwer_degree2 p g = Brouwer_degree2 p f"
  using assms
  by (auto simp: homeomorphic_maps_def homotopic_with_equal continuous_map_compose intro: Brouwer_degree2_homotopy_equivalence)


lemma Brouwer_degree2_retraction_map:
  assumes "retraction_map (nsphere p) (nsphere p) f"
  shows "\<bar>Brouwer_degree2 p f\<bar> = 1"
proof -
  obtain g where g: "retraction_maps (nsphere p) (nsphere p) f g"
    using assms by (auto simp: retraction_map_def)
  show ?thesis
  proof (rule Brouwer_degree2_homotopy_equivalence)
    show "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) (f \<circ> g) id"
      using g apply (auto simp: retraction_maps_def)
      by (simp add: homotopic_with_equal continuous_map_compose)
    show "continuous_map (nsphere p) (nsphere p) f" "continuous_map (nsphere p) (nsphere p) g"
      using g retraction_maps_def by blast+
  qed
qed

lemma Brouwer_degree2_section_map:
  assumes "section_map (nsphere p) (nsphere p) f"
  shows "\<bar>Brouwer_degree2 p f\<bar> = 1"
proof -
  obtain g where g: "retraction_maps (nsphere p) (nsphere p) g f"
    using assms by (auto simp: section_map_def)
  show ?thesis
  proof (rule Brouwer_degree2_homotopy_equivalence)
    show "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) (g \<circ> f) id"
      using g apply (auto simp: retraction_maps_def)
      by (simp add: homotopic_with_equal continuous_map_compose)
    show "continuous_map (nsphere p) (nsphere p) g" "continuous_map (nsphere p) (nsphere p) f"
      using g retraction_maps_def by blast+
  qed
qed

lemma Brouwer_degree2_homeomorphic_map:
   "homeomorphic_map (nsphere p) (nsphere p) f \<Longrightarrow> \<bar>Brouwer_degree2 p f\<bar> = 1"
  using Brouwer_degree2_retraction_map section_and_retraction_eq_homeomorphic_map by blast


lemma Brouwer_degree2_nullhomotopic:
  assumes "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) f (\<lambda>x. a)"
  shows "Brouwer_degree2 p f = 0"
proof -
  have contf: "continuous_map (nsphere p) (nsphere p) f"
   and contc: "continuous_map (nsphere p) (nsphere p) (\<lambda>x. a)"
    using homotopic_with_imp_continuous_maps [OF assms] by metis+
  have "Brouwer_degree2 p f = Brouwer_degree2 p (\<lambda>x. a)"
    using Brouwer_degree2_homotopic [OF assms] .
  moreover
  let ?G = "reduced_homology_group (int p) (nsphere p)"
  interpret group ?G
    by simp
  have "Brouwer_degree2 p (\<lambda>x. a) = 0"
  proof (rule Brouwer_degree2_unique [OF contc])
    fix c
    assume c: "c \<in> carrier ?G"
    have "continuous_map (nsphere p) (subtopology (nsphere p) {a}) (\<lambda>f. a)"
      using contc continuous_map_in_subtopology by blast
    then have he: "hom_induced p (nsphere p) {} (nsphere p) {} (\<lambda>x. a)
                 = hom_induced p (subtopology (nsphere p) {a}) {} (nsphere p) {} id \<circ>
                   hom_induced p (nsphere p) {} (subtopology (nsphere p) {a}) {} (\<lambda>x. a)"
      by (metis continuous_map_id_subt hom_induced_compose id_comp image_empty order_refl)
    have 1: "hom_induced p (nsphere p) {} (subtopology (nsphere p) {a}) {} (\<lambda>x. a) c =
             \<one>\<^bsub>reduced_homology_group (int p) (subtopology (nsphere p) {a})\<^esub>"
      using c trivial_reduced_homology_group_contractible_space [of "subtopology (nsphere p) {a}" p]
      by (simp add: hom_induced_reduced contractible_space_subtopology_singleton trivial_group_subset group.trivial_group_subset subset_iff)
    show "hom_induced (int p) (nsphere p) {} (nsphere p) {} (\<lambda>x. a) c =
        c [^]\<^bsub>?G\<^esub> (0::int)"
      apply (simp add: he 1)
      using hom_induced_reduced_hom group_hom.hom_one group_hom_axioms_def group_hom_def group_reduced_homology_group by blast
  qed
  ultimately show ?thesis
    by metis
qed


lemma Brouwer_degree2_const: "Brouwer_degree2 p (\<lambda>x. a) = 0"
proof (cases "continuous_map(nsphere p) (nsphere p) (\<lambda>x. a)")
  case True
  then show ?thesis
    by (auto intro: Brouwer_degree2_nullhomotopic [where a=a])
next
  case False
  let ?G = "reduced_homology_group (int p) (nsphere p)"
  let ?H = "homology_group (int p) (nsphere p)"
  interpret group ?G
    by simp
  have eq1: "\<one>\<^bsub>?H\<^esub> = \<one>\<^bsub>?G\<^esub>"
    by (simp add: one_reduced_homology_group)
  have *: "\<forall>x\<in>carrier ?G. hom_induced (int p) (nsphere p) {} (nsphere p) {} (\<lambda>x. a) x = \<one>\<^bsub>?H\<^esub>"
    by (metis False hom_induced_default one_relative_homology_group)
  obtain c where c: "c \<in> carrier ?G" and ceq: "subgroup_generated ?G {c} = ?G"
    using cyclic_reduced_homology_group_nsphere [of p p] by (force simp: cyclic_group_def)
  have [simp]: "ord c = 0"
    by (simp add: c ceq iso_finite [OF reduced_homology_group_nsphere(1)] flip: infinite_cyclic_subgroup_order)
  show ?thesis
    unfolding Brouwer_degree2_def
  proof (rule some_equality)
    fix d :: "int"
    assume "\<forall>x\<in>carrier ?G. hom_induced (int p) (nsphere p) {} (nsphere p) {} (\<lambda>x. a) x = x [^]\<^bsub>?G\<^esub> d"
    then have "c [^]\<^bsub>?G\<^esub> d = \<one>\<^bsub>?H\<^esub>"
      using "*" c by blast
    then have "int (ord c) dvd d"
      using c eq1 int_pow_eq_id by auto
    then show "d = 0"
      by (simp add: * del: one_relative_homology_group)
  qed (use "*" eq1 in force)
qed


corollary Brouwer_degree2_nonsurjective:
   "\<lbrakk>continuous_map(nsphere p) (nsphere p) f; f ` topspace (nsphere p) \<noteq> topspace (nsphere p)\<rbrakk>
    \<Longrightarrow> Brouwer_degree2 p f = 0"
  by (meson Brouwer_degree2_nullhomotopic nullhomotopic_nonsurjective_sphere_map)


proposition Brouwer_degree2_reflection:
  "Brouwer_degree2 p (\<lambda>x i. if i = 0 then -x i else x i) = -1" (is "Brouwer_degree2 _ ?r = -1")
proof (induction p)
  case 0
  let ?G = "homology_group 0 (nsphere 0)"
  let ?D = "homology_group 0 (discrete_topology {()})"
  interpret group ?G
    by simp
  define r where "r \<equiv> \<lambda>x::nat\<Rightarrow>real. \<lambda>i. if i = 0 then -x i else x i"
  then have [simp]: "r \<circ> r = id"
    by force
  have cmr: "continuous_map (nsphere 0) (nsphere 0) r"
    by (simp add: r_def continuous_map_nsphere_reflection)
  have *: "hom_induced 0 (nsphere 0) {} (nsphere 0) {} r c = inv\<^bsub>?G\<^esub> c"
    if "c \<in> carrier(reduced_homology_group 0 (nsphere 0))" for c
  proof -
    have c: "c \<in> carrier ?G"
      and ceq: "hom_induced 0 (nsphere 0) {} (discrete_topology {()}) {} (\<lambda>x. ()) c = \<one>\<^bsub>?D\<^esub>"
      using that by (auto simp: carrier_reduced_homology_group kernel_def)
    define pp::"nat\<Rightarrow>real" where "pp \<equiv> \<lambda>i. if i = 0 then 1 else 0"
    define nn::"nat\<Rightarrow>real" where "nn \<equiv> \<lambda>i. if i = 0 then -1 else 0"
    have topn0: "topspace(nsphere 0) = {pp,nn}"
      by (auto simp: nsphere pp_def nn_def fun_eq_iff power2_eq_1_iff split: if_split_asm)
    have "t1_space (nsphere 0)"
      unfolding nsphere
      apply (rule t1_space_subtopology)
      by (metis (full_types) open_fun_def t1_space t1_space_def)
    then have dtn0: "discrete_topology {pp,nn} = nsphere 0"
      using finite_t1_space_imp_discrete_topology [OF topn0] by auto
    have "pp \<noteq> nn"
      by (auto simp: pp_def nn_def fun_eq_iff)
    have [simp]: "r pp = nn" "r nn = pp"
      by (auto simp: r_def pp_def nn_def fun_eq_iff)
    have iso: "(\<lambda>(a,b). hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} id a
                  \<otimes>\<^bsub>?G\<^esub> hom_induced 0 (subtopology (nsphere 0) {nn}) {} (nsphere 0) {} id b)
            \<in> iso (homology_group 0 (subtopology (nsphere 0) {pp}) \<times>\<times> homology_group 0 (subtopology (nsphere 0) {nn}))
                  ?G" (is "?f \<in> iso (?P \<times>\<times> ?N) ?G")
      apply (rule homology_additivity_explicit)
      using dtn0 \<open>pp \<noteq> nn\<close> by (auto simp: discrete_topology_unique)
    then have fim: "?f ` carrier(?P \<times>\<times> ?N) = carrier ?G"
      by (simp add: iso_def bij_betw_def)
    obtain d d' where d: "d \<in> carrier ?P" and d': "d' \<in> carrier ?N" and eqc: "?f(d,d') = c"
      using c by (force simp flip: fim)
    let ?h = "\<lambda>xx. hom_induced 0 (subtopology (nsphere 0) {xx}) {} (discrete_topology {()}) {} (\<lambda>x. ())"
    have "retraction_map (subtopology (nsphere 0) {pp}) (subtopology (nsphere 0) {nn}) r"
      apply (simp add: retraction_map_def retraction_maps_def continuous_map_in_subtopology continuous_map_from_subtopology cmr image_subset_iff)
      apply (rule_tac x=r in exI)
      apply (force simp: retraction_map_def retraction_maps_def continuous_map_in_subtopology continuous_map_from_subtopology cmr)
      done
    then have "carrier ?N = (hom_induced 0 (subtopology (nsphere 0) {pp}) {} (subtopology (nsphere 0) {nn}) {} r) ` carrier ?P"
      by (rule surj_hom_induced_retraction_map)
    then obtain e where e: "e \<in> carrier ?P" and eqd': "hom_induced 0 (subtopology (nsphere 0) {pp}) {} (subtopology (nsphere 0) {nn}) {} r e = d'"
      using d' by auto
    have "section_map (subtopology (nsphere 0) {pp}) (discrete_topology {()}) (\<lambda>x. ())"
      by (force simp: section_map_def retraction_maps_def topn0)
    then have "?h pp \<in> mon ?P ?D"
      by (rule mon_hom_induced_section_map)
    then have one: "x = one ?P"
      if "?h pp x = \<one>\<^bsub>?D\<^esub>" "x \<in> carrier ?P" for x
      using that by (simp add: mon_iff_hom_one)
    interpret hpd: group_hom ?P ?D "?h pp"
      using hom_induced_empty_hom by (simp add: hom_induced_empty_hom group_hom_axioms_def group_hom_def)
    interpret hgd: group_hom ?G ?D "hom_induced 0 (nsphere 0) {} (discrete_topology {()}) {} (\<lambda>x. ())"
      using hom_induced_empty_hom by (simp add: hom_induced_empty_hom group_hom_axioms_def group_hom_def)
    interpret hpg: group_hom ?P ?G "hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} r"
      using hom_induced_empty_hom by (simp add: hom_induced_empty_hom group_hom_axioms_def group_hom_def)
    interpret hgg: group_hom ?G ?G "hom_induced 0 (nsphere 0) {} (nsphere 0) {} r"
      using hom_induced_empty_hom by (simp add: hom_induced_empty_hom group_hom_axioms_def group_hom_def)
    have "?h pp d =
          (hom_induced 0 (nsphere 0) {} (discrete_topology {()}) {} (\<lambda>x. ())
           \<circ> hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} id) d"
      by (simp flip: hom_induced_compose_empty)
    moreover
    have "?h pp = ?h nn \<circ> hom_induced 0 (subtopology (nsphere 0) {pp}) {} (subtopology (nsphere 0) {nn}) {} r"
      by (simp add: cmr continuous_map_from_subtopology continuous_map_in_subtopology image_subset_iff flip: hom_induced_compose_empty)
    then have "?h pp e =
               (hom_induced 0 (nsphere 0) {} (discrete_topology {()}) {} (\<lambda>x. ())
                \<circ> hom_induced 0 (subtopology (nsphere 0) {nn}) {} (nsphere 0) {} id) d'"
      by (simp flip: hom_induced_compose_empty eqd')
    ultimately have "?h pp (d \<otimes>\<^bsub>?P\<^esub> e) = hom_induced 0 (nsphere 0) {} (discrete_topology {()}) {} (\<lambda>x. ()) (?f(d,d'))"
      by (simp add: d e hom_induced_carrier)
    then have "?h pp (d \<otimes>\<^bsub>?P\<^esub> e) = \<one>\<^bsub>?D\<^esub>"
      using ceq eqc by simp
    then have inv_p: "inv\<^bsub>?P\<^esub> d = e"
      by (metis (no_types, lifting) Group.group_def d e group.inv_equality group.r_inv group_relative_homology_group one monoid.m_closed)
    have cmr_pn: "continuous_map (subtopology (nsphere 0) {pp}) (subtopology (nsphere 0) {nn}) r"
      by (simp add: cmr continuous_map_from_subtopology continuous_map_in_subtopology image_subset_iff)
    then have "hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} (id \<circ> r) =
               hom_induced 0 (subtopology (nsphere 0) {nn}) {} (nsphere 0) {} id \<circ>
               hom_induced 0 (subtopology (nsphere 0) {pp}) {} (subtopology (nsphere 0) {nn}) {} r"
      using hom_induced_compose_empty continuous_map_id_subt by blast
    then have "inv\<^bsub>?G\<^esub> hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} r d =
                  hom_induced 0 (subtopology (nsphere 0) {nn}) {} (nsphere 0) {} id d'"
      apply (simp add: flip: inv_p eqd')
      using d hpg.hom_inv by auto
    then have c: "c = (hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} id d)
                       \<otimes>\<^bsub>?G\<^esub> inv\<^bsub>?G\<^esub> (hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} r d)"
      by (simp flip: eqc)
    have "hom_induced 0 (nsphere 0) {} (nsphere 0) {} r \<circ>
          hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} id =
          hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} r"
      by (metis cmr comp_id continuous_map_id_subt hom_induced_compose_empty)
    moreover
    have "hom_induced 0 (nsphere 0) {} (nsphere 0) {} r \<circ>
          hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} r =
          hom_induced 0 (subtopology (nsphere 0) {pp}) {} (nsphere 0) {} id"
      by (metis \<open>r \<circ> r = id\<close> cmr continuous_map_from_subtopology hom_induced_compose_empty)
    ultimately show ?thesis
      by (metis inv_p c comp_def d e hgg.hom_inv hgg.hom_mult hom_induced_carrier hpd.G.inv_inv hpg.hom_inv inv_mult_group)
  qed
  show ?case
    unfolding r_def [symmetric]
    using Brouwer_degree2_unique [OF cmr]
    by (auto simp: * group.int_pow_neg group.int_pow_1 reduced_homology_group_def intro!: Brouwer_degree2_unique [OF cmr])
next
  case (Suc p)
  let ?G = "reduced_homology_group (int p) (nsphere p)"
  let ?G1 = "reduced_homology_group (1 + int p) (nsphere (Suc p))"
  obtain f g where fg: "group_isomorphisms ?G ?G1 f g"
    and *: "\<forall>c\<in>carrier ?G.
           hom_induced (1 + int p) (nsphere (Suc p)) {} (nsphere (Suc p)) {} ?r (f c) =
           f (hom_induced p (nsphere p) {} (nsphere p) {} ?r c)"
    using reduced_homology_group_nsphere_step
    by (meson group.iso_iff_group_isomorphisms group_reduced_homology_group)
  then have eq: "carrier ?G1 = f ` carrier ?G"
    by (fastforce simp add: iso_iff dest: group_isomorphisms_imp_iso)
  interpret group_hom ?G ?G1 f
    by (meson fg group_hom_axioms_def group_hom_def group_isomorphisms_def group_reduced_homology_group)
  have homf: "f \<in> hom ?G ?G1"
    using fg group_isomorphisms_def by blast
  have "hom_induced (1 + int p) (nsphere (Suc p)) {} (nsphere (Suc p)) {} ?r (f y) = f y [^]\<^bsub>?G1\<^esub> (-1::int)"
    if "y \<in> carrier ?G" for y
    by (simp add: that * Brouwer_degree2 Suc hom_int_pow)
  then show ?case
    by (fastforce simp: eq intro: Brouwer_degree2_unique [OF continuous_map_nsphere_reflection])
qed

end
