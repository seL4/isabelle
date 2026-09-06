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
proof
  show "({undefined}, (\<lambda>x y. undefined), undefined) \<in>
      {T :: 'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a.
        Group (fst T) (fst (snd T)) (snd (snd T))}"
    by (simp add: trivial_Group)
qed

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
    apply (simp only: Let_def split_beta)
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
proof -
  obtain G composition unit where T: "T = (G, composition, unit)"
    by (cases T) simp
  have "Group G composition unit"
    using assms T by simp
  then show ?thesis
    unfolding T
    by (rule isomorphic_as_groups_refl)
qed

lemma isomorphic_as_groups_symmetric_triples:
  fixes T U :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes "T \<cong>\<^sub>G U"
  shows "U \<cong>\<^sub>G T"
proof -
  have canonical_iso:
      "(fst T, fst (snd T), snd (snd T)) \<cong>\<^sub>G
        (fst U, fst (snd U), snd (snd U))"
    using assms by (simp add: surjective_pairing)
  have "(fst U, fst (snd U), snd (snd U)) \<cong>\<^sub>G
      (fst T, fst (snd T), snd (snd T))"
    by (rule isomorphic_as_groups_symmetric[OF canonical_iso])
  then show ?thesis
    by (simp add: surjective_pairing)
qed

lemma isomorphic_as_groups_transitive_triples:
  fixes T U V :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes "T \<cong>\<^sub>G U" "U \<cong>\<^sub>G V"
  shows "T \<cong>\<^sub>G V"
proof -
  have first:
      "(fst T, fst (snd T), snd (snd T)) \<cong>\<^sub>G
        (fst U, fst (snd U), snd (snd U))"
    using assms(1) by (simp add: surjective_pairing)
  have second:
      "(fst U, fst (snd U), snd (snd U)) \<cong>\<^sub>G
        (fst V, fst (snd V), snd (snd V))"
    using assms(2) by (simp add: surjective_pairing)
  have "(fst T, fst (snd T), snd (snd T)) \<cong>\<^sub>G
      (fst V, fst (snd V), snd (snd V))"
    by (rule isomorphic_as_groups_transitive[OF first second])
  then show ?thesis
    by (simp add: surjective_pairing)
qed

definition group_iso_rel :: "'a group_structure \<Rightarrow> 'a group_structure \<Rightarrow> bool"
  where
    "group_iso_rel G H \<longleftrightarrow>
      dest_group_structure G \<cong>\<^sub>G dest_group_structure H"

text \<open>
  Isomorphism is an equivalence relation on the wrapped group structures, so
  the quotient below records exactly the invariant needed by Jordan--Hölder.
\<close>

quotient_type 'a group_iso_class = "'a group_structure" / group_iso_rel
  morphisms Rep_group_iso Abs_group_iso
proof (rule equivpI)
  show "reflp group_iso_rel"
  proof (rule reflpI)
    fix G
    show "group_iso_rel G G"
      unfolding group_iso_rel_def
      by (rule isomorphic_as_groups_refl_triple[OF group_structure_group])
  qed
next
  show "symp group_iso_rel"
  proof (rule sympI)
    fix G H
    assume "group_iso_rel G H"
    then show "group_iso_rel H G"
      unfolding group_iso_rel_def
      by (rule isomorphic_as_groups_symmetric_triples)
  qed
next
  show "transp group_iso_rel"
  proof (rule transpI)
    fix G H I
    assume "group_iso_rel G H" "group_iso_rel H I"
    then show "group_iso_rel G I"
      unfolding group_iso_rel_def
      by (rule isomorphic_as_groups_transitive_triples)
  qed
qed

definition group_iso_class_of :: "'a group_structure \<Rightarrow> 'a group_iso_class"
  where
    "group_iso_class_of G = Abs_group_iso G"

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
  assumes T_group:
      "Group (fst T) (fst (snd T)) (snd (snd T))"
    and U_group:
      "Group (fst U) (fst (snd U)) (snd (snd U))"
  shows "group_iso_class_of (group_structure T) =
      group_iso_class_of (group_structure U) \<longleftrightarrow> T \<cong>\<^sub>G U"
proof -
  have T_mem:
      "T \<in> {S. Group (fst S) (fst (snd S)) (snd (snd S))}"
    using T_group by simp
  have U_mem:
      "U \<in> {S. Group (fst S) (fst (snd S)) (snd (snd S))}"
    using U_group by simp
  have T_dest: "dest_group_structure (group_structure T) = T"
    using T_mem by (simp add: dest_group_structure_inverse group_structure_inverse)
  have U_dest: "dest_group_structure (group_structure U) = U"
    using U_mem by (simp add: dest_group_structure_inverse group_structure_inverse)
  show ?thesis
    using group_iso_class_of_eq_iff_isomorphic[
      of "group_structure T" "group_structure U"] T_dest U_dest
    by simp
qed

subsection \<open>The trivial isomorphism class\<close>

text \<open>
  A distinguished class for the one-element group lets later developments
  discard repetition factors without choosing a representative from each
  quotient.  The use of @{const undefined} is harmless: every one-element
  group is isomorphic to this canonical representative.
\<close>
definition trivial_group_structure ::
    "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  where
    "trivial_group_structure =
      ({undefined}, (\<lambda>_ _. undefined), undefined)"

lemma trivial_group_structure_group [iff]:
  "Group (fst (trivial_group_structure ::
      'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a))
    (fst (snd trivial_group_structure)) (snd (snd trivial_group_structure))"
  by (simp add: trivial_group_structure_def trivial_Group)

definition trivial_group_iso_class :: "'a group_iso_class"
  where
    "trivial_group_iso_class =
      group_iso_class_of (group_structure trivial_group_structure)"

lemma group_iso_class_eq_trivial_iff:
  assumes G: "Group G composition unit"
  shows "group_iso_class_of (group_structure (G, composition, unit)) =
      trivial_group_iso_class \<longleftrightarrow> G = {unit}"
proof -
  interpret G: Group G composition unit by fact
  have class_iff:
      "group_iso_class_of (group_structure (G, composition, unit)) =
          trivial_group_iso_class \<longleftrightarrow>
        (G, composition, unit) \<cong>\<^sub>G
          (trivial_group_structure ::
            'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a)"
    unfolding trivial_group_iso_class_def
    by (subst group_iso_class_of_group_structure_eq_iff;
        simp add: G.Group_axioms)
  also have "... \<longleftrightarrow> G = {unit}"
  proof
    assume iso:
      "(G, composition, unit) \<cong>\<^sub>G
        (trivial_group_structure ::
          'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a)"
    have exists_iso:
      "\<exists>f. group_isomorphism f G composition unit
        {undefined :: 'a} (\<lambda>(_::'a) (_::'a). undefined) undefined"
      using iso
      by (simp add: isomorphic_as_groups_def trivial_group_structure_def)
    then obtain \<eta> where
      \<eta>: "group_isomorphism \<eta> G composition unit
        {undefined :: 'a} (\<lambda>(_::'a) (_::'a). undefined) undefined"
      by blast
    interpret \<eta>: group_isomorphism \<eta> G composition unit
      "{undefined :: 'a}" "\<lambda>(_::'a) (_::'a). undefined" undefined by fact
    show "G = {unit}"
    proof (rule equalityI)
      show "G \<subseteq> {unit}"
      proof
        fix x
        assume x: "x \<in> G"
        have \<eta>x: "\<eta> x = undefined"
          by (rule singletonD[OF \<eta>.map_closed[OF x]])
        have \<eta>unit: "\<eta> unit = undefined"
          by (rule \<eta>.commutes_with_unit)
        have "x = unit"
        proof (rule inj_onD[OF \<eta>.injective])
          show "\<eta> x = \<eta> unit"
            by (rule trans[OF \<eta>x \<eta>unit[symmetric]])
          show "x \<in> G" by fact
          show "unit \<in> G" by (rule G.unit_closed)
        qed
        then show "x \<in> {unit}" by simp
      qed
      show "{unit} \<subseteq> G" using G.unit_closed by simp
    qed
  next
    assume trivial: "G = {unit}"
    have iso:
      "group_isomorphism (\<lambda>_. undefined) G composition unit
        {undefined :: 'a} (\<lambda>(_::'a) (_::'a). undefined) undefined"
      using G.Group_axioms trivial_Group trivial trivial_Monoid_invertible
      by unfold_locales (auto simp: PiE_def extensional_def)
    show "(G, composition, unit) \<cong>\<^sub>G
      (trivial_group_structure ::
        'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a)"
      unfolding isomorphic_as_groups_def trivial_group_structure_def
      using iso by auto
  qed
  finally show ?thesis .
qed

end
