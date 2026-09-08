theory Group_Iso_Classes
  imports Group_Theory
begin

section \<open>Isomorphism classes of set-based groups\<close>

text \<open>
  \<open>New_Algebra\<close> represents a group by its carrier, composition, and unit rather
  than by a record.  This theory gives that triple a type-level wrapper before
  quotienting by group isomorphism.  The wrapper is important: the raw triple
  type also contains non-groups, whereas isomorphism is an equivalence only on
  the valid group triples.
\<close>

typedef 'a group_structure =
  "{T :: 'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a.
      Group (fst T) (fst (snd T)) (snd (snd T))}"
  morphisms dest_group_structure group_structure
  using trivial_Group by auto

declare dest_group_structure_inverse [simp]

lemma group_structure_group [iff]:
  "Group (fst (dest_group_structure S))
      (fst (snd (dest_group_structure S))) (snd (snd (dest_group_structure S)))"
  using dest_group_structure[of S] by blast

lemma isomorphic_as_groups_refl:
  assumes "Group G composition unit"
  shows "(G, composition, unit) \<cong>\<^sub>G (G, composition, unit)"
proof -
  interpret G: Group G composition unit by fact
  show ?thesis
    unfolding isomorphic_as_groups_def
    unfolding Let_def split_beta
    apply (rule_tac x = "restrict id G" in exI)
    by (unfold_locales; simp add: PiE_def extensional_def restrict_def
      bij_betw_def inj_on_def G.associative)
qed

text \<open>
  The native isomorphism lemmas are stated for explicit triples.  These
  variants lift them to an arbitrary value of the product type used by the
  quotient representation.
\<close>

lemma isomorphic_as_groups_refl_triple:
  fixes T :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes "Group (fst T) (fst (snd T)) (snd (snd T))"
  shows "T \<cong>\<^sub>G T"
  using assms isomorphic_as_groups_refl by fastforce

lemma isomorphic_as_groups_symmetric_triples:
  fixes T U :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes "T \<cong>\<^sub>G U"
  shows "U \<cong>\<^sub>G T"
  using assms by (metis isomorphic_as_groups_symmetric split_pairs)

lemma isomorphic_as_groups_transitive_triples:
  fixes T U V :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes "T \<cong>\<^sub>G U" "U \<cong>\<^sub>G V"
  shows "T \<cong>\<^sub>G V"
  using assms by (metis isomorphic_as_groups_transitive surjective_pairing)

definition group_iso_rel :: "'a group_structure \<Rightarrow> 'a group_structure \<Rightarrow> bool"
  where "group_iso_rel G H \<equiv> dest_group_structure G \<cong>\<^sub>G dest_group_structure H"

text \<open>
  Isomorphism is an equivalence relation on the wrapped group structures, so
  the quotient below records exactly the invariant needed by Jordan--Hölder.
  The warning "No map function defined" is apparently irrelevant.
\<close>

quotient_type 'a group_iso_class = "'a group_structure" / group_iso_rel
  morphisms Rep_group_iso Abs_group_iso
proof (rule equivpI)
  show "reflp group_iso_rel"
    by (simp add: group_iso_rel_def isomorphic_as_groups_refl_triple reflpI)
  show "symp group_iso_rel"
    by (simp add: group_iso_rel_def isomorphic_as_groups_symmetric_triples symp_on_def)
  show "transp group_iso_rel"
    unfolding transp_def group_iso_rel_def by (metis isomorphic_as_groups_transitive_triples)
qed

definition group_iso_class_of :: "'a group_structure \<Rightarrow> 'a group_iso_class"
  where "group_iso_class_of G \<equiv> Abs_group_iso G"

lemma group_iso_class_of_eq_iff:
  "group_iso_class_of G = group_iso_class_of H \<longleftrightarrow> group_iso_rel G H"
  unfolding group_iso_class_of_def
  using group_iso_class.abs_eq_iff[of G H] by simp

lemma group_iso_class_of_eq_iff_isomorphic:
  "group_iso_class_of G = group_iso_class_of H \<longleftrightarrow>
    dest_group_structure G \<cong>\<^sub>G dest_group_structure H"
  unfolding group_iso_class_of_eq_iff group_iso_rel_def
  by simp

text \<open>
  The public constructor @{const group_structure} packages a valid carrier,
  operation, and unit.  This bridge lets clients compare the resulting
  isomorphism classes directly at the level of their original group triples.
\<close>
lemma group_iso_class_of_group_structure_eq_iff:
  fixes T U :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes "Group (fst T) (fst (snd T)) (snd (snd T))"
          "Group (fst U) (fst (snd U)) (snd (snd U))"
  shows "group_iso_class_of (group_structure T) = group_iso_class_of (group_structure U) 
         \<longleftrightarrow> T \<cong>\<^sub>G U"
  by (simp add: assms group_iso_class_of_eq_iff_isomorphic group_structure_inverse)

subsection \<open>The trivial isomorphism class\<close>

text \<open>
  A distinguished class for the one-element group lets later developments
  discard repetition factors without choosing a representative from each
  quotient.  The use of @{const undefined} is harmless: every one-element
  group is isomorphic to this canonical representative.
\<close>
definition trivial_group_structure :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  where "trivial_group_structure \<equiv> ({undefined}, (\<lambda>_ _. undefined), undefined)"

lemma trivial_group_structure_group [iff]:
  "Group (fst (trivial_group_structure ::
      'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a))
    (fst (snd trivial_group_structure)) (snd (snd trivial_group_structure))"
  by (simp add: trivial_group_structure_def trivial_Group)

definition trivial_group_iso_class :: "'a group_iso_class"
  where
    "trivial_group_iso_class \<equiv> group_iso_class_of (group_structure trivial_group_structure)"

lemma group_iso_class_eq_trivial_iff:
  assumes G: "Group G composition unit"
  shows "group_iso_class_of (group_structure (G, composition, unit)) = trivial_group_iso_class 
     \<longleftrightarrow> G = {unit}"
proof -
  let ?triv = "(trivial_group_structure :: 'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a)"
  interpret G: Group G composition unit by fact
  have "group_iso_class_of (group_structure (G, composition, unit)) = trivial_group_iso_class \<longleftrightarrow>
       (G, composition, unit) \<cong>\<^sub>G ?triv"
    by (simp add: assms group_iso_class_of_group_structure_eq_iff trivial_group_iso_class_def)
  also have "... \<longleftrightarrow> G = {unit}"
  proof
    assume "(G, composition, unit) \<cong>\<^sub>G ?triv"
    then obtain \<eta> where
      \<eta>: "group_isomorphism \<eta> G composition unit
        {undefined :: 'a} (\<lambda>_ _. undefined) undefined"
      by (auto simp add: isomorphic_as_groups_def trivial_group_structure_def)
    interpret \<eta>: group_isomorphism \<eta> G composition unit
      "{undefined :: 'a}" "\<lambda>_ _. undefined" undefined by fact
    show "G = {unit}"
      using \<eta>.injective_iff_kernel_unit \<eta>.map_closed by blast
  next
    assume trivial: "G = {unit}"
    have iso:
      "group_isomorphism (\<lambda>_. undefined) G composition unit
        {undefined :: 'a} (\<lambda>_ _. undefined) undefined"
      using G.Group_axioms trivial_Group trivial trivial_Monoid_invertible
      by unfold_locales (auto simp: PiE_def extensional_def)
    show "(G, composition, unit) \<cong>\<^sub>G ?triv"
      unfolding isomorphic_as_groups_def trivial_group_structure_def
      using iso by auto
  qed
  finally show ?thesis .
qed

end
