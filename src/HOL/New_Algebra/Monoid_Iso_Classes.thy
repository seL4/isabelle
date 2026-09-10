theory Monoid_Iso_Classes
  imports Group_Theory
begin

section \<open>Isomorphism classes of set-based monoids\<close>

text \<open>
  \<open>New_Algebra\<close> represents a monoid by its carrier, composition, and unit rather than by a record,
  and \<^typ>\<open>'a monoid\<close> is the type-level wrapper for a valid such triple.  Quotienting it by
  isomorphism gives isomorphism classes.

  Classes are formed once, at the level of monoids, rather than separately for each stronger
  structure.  Nothing is lost for groups: \<open>Monoid_isomorphism.target_Group\<close> makes being a group a
  property of the isomorphism class, and \<open>isomorphic_as_monoids_iff_groups\<close> shows the two notions
  of isomorphism agree on groups.  Where group-ness is needed it is imposed as a constraint, as in
  \<open>monoid_iso_class_of_monoid_eq_iff_groups\<close> and \<open>monoid_iso_class_eq_trivial_iff\<close> below.
\<close>

definition monoid_iso_rel :: "'a monoid \<Rightarrow> 'a monoid \<Rightarrow> bool"
  where
    "monoid_iso_rel m n \<longleftrightarrow>
      (mcarrier m, mmult m, munit m) \<cong>\<^sub>M (mcarrier n, mmult n, munit n)"

text \<open>
  Isomorphism is an equivalence relation on the wrapped monoids, so the quotient below records
  exactly the invariant needed by Jordan--H\"older.
\<close>

quotient_type 'a monoid_iso_class = "'a monoid" / monoid_iso_rel
  morphisms Rep_monoid_iso Abs_monoid_iso
proof (rule equivpI)
  show "reflp monoid_iso_rel"
    by (rule reflpI)
      (simp add: monoid_iso_rel_def isomorphic_as_monoids_refl [OF monoid_is_Monoid])
  show "symp monoid_iso_rel"
    by (rule sympI) (simp add: monoid_iso_rel_def isomorphic_as_monoids_symmetric)
  show "transp monoid_iso_rel"
    by (rule transpI)
      (metis monoid_iso_rel_def isomorphic_as_monoids_transitive)
qed

definition monoid_iso_class_of :: "'a monoid \<Rightarrow> 'a monoid_iso_class"
  where "monoid_iso_class_of m = Abs_monoid_iso m"

lemma monoid_iso_class_of_eq_iff:
  "monoid_iso_class_of m = monoid_iso_class_of n \<longleftrightarrow> monoid_iso_rel m n"
  unfolding monoid_iso_class_of_def
  using monoid_iso_class.abs_eq_iff [of m n] by simp

lemma monoid_iso_class_of_eq_iff_isomorphic:
  "monoid_iso_class_of m = monoid_iso_class_of n \<longleftrightarrow>
    (mcarrier m, mmult m, munit m) \<cong>\<^sub>M (mcarrier n, mmult n, munit n)"
  unfolding monoid_iso_class_of_eq_iff monoid_iso_rel_def by simp

text \<open>
  The bridge clients use: comparing classes of monoids built from explicit triples is comparing
  the triples up to isomorphism.
\<close>
lemma monoid_iso_class_of_monoid_eq_iff:
  fixes T U :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes T: "Monoid (fst T) (fst (snd T)) (snd (snd T))"
    and U: "Monoid (fst U) (fst (snd U)) (snd (snd U))"
  shows "monoid_iso_class_of (monoid T) = monoid_iso_class_of (monoid U) \<longleftrightarrow> T \<cong>\<^sub>M U"
proof -
  obtain M composition unit where T_eq: "T = (M, composition, unit)" by (cases T) simp
  obtain M' composition' unit' where U_eq: "U = (M', composition', unit')" by (cases U) simp
  interpret T: Monoid M composition unit using T by (simp add: T_eq)
  interpret U: Monoid M' composition' unit' using U by (simp add: U_eq)
  show ?thesis
    unfolding monoid_iso_class_of_eq_iff_isomorphic T_eq U_eq by simp
qed

text \<open>
  For groups the same statement holds with group isomorphism, because the two notions agree there.
  This is the form the Jordan--H\"older development needs.
\<close>
lemma monoid_iso_class_of_monoid_eq_iff_groups:
  fixes T U :: "'a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a"
  assumes T: "Group (fst T) (fst (snd T)) (snd (snd T))"
    and U: "Group (fst U) (fst (snd U)) (snd (snd U))"
  shows "monoid_iso_class_of (monoid T) = monoid_iso_class_of (monoid U) \<longleftrightarrow> T \<cong>\<^sub>G U"
proof -
  obtain M composition unit where T_eq: "T = (M, composition, unit)" by (cases T) simp
  obtain M' composition' unit' where U_eq: "U = (M', composition', unit')" by (cases U) simp
  have T_group: "Group M composition unit" using T by (simp add: T_eq)
  have U_group: "Group M' composition' unit'" using U by (simp add: U_eq)
  have "monoid_iso_class_of (monoid T) = monoid_iso_class_of (monoid U) \<longleftrightarrow> T \<cong>\<^sub>M U"
    by (rule monoid_iso_class_of_monoid_eq_iff)
      (use T U Group.axioms(1) in \<open>simp_all add: T_eq U_eq\<close>)
  also have "T \<cong>\<^sub>M U \<longleftrightarrow> T \<cong>\<^sub>G U"
    unfolding T_eq U_eq by (rule isomorphic_as_monoids_iff_groups [OF T_group U_group])
  finally show ?thesis .
qed


subsection \<open>The trivial isomorphism class\<close>

text \<open>
  A distinguished class for the one-element monoid lets later developments discard repetition
  factors without choosing a representative from each quotient.  @{const trivial_monoid} is the
  canonical representative; every one-element group is isomorphic to it.
\<close>

definition trivial_monoid_iso_class :: "'a monoid_iso_class"
  where "trivial_monoid_iso_class = monoid_iso_class_of trivial_monoid"

lemma monoid_iso_class_eq_trivial_iff:
  assumes G: "Group G composition unit"
  shows "monoid_iso_class_of (monoid (G, composition, unit)) = trivial_monoid_iso_class
     \<longleftrightarrow> G = {unit}"
proof -
  interpret G: Group G composition unit by fact
  have trivial_group:
      "Group (fst ({undefined :: 'a}, (\<lambda>x y. undefined), undefined))
        (fst (snd ({undefined :: 'a}, (\<lambda>x y. undefined), undefined)))
        (snd (snd ({undefined :: 'a}, (\<lambda>x y. undefined), undefined)))"
    by (simp add: trivial_Group)
  have class_iff:
      "monoid_iso_class_of (monoid (G, composition, unit)) = trivial_monoid_iso_class \<longleftrightarrow>
        (G, composition, unit) \<cong>\<^sub>G
          ({undefined :: 'a}, (\<lambda>x y. undefined), undefined)"
    unfolding trivial_monoid_iso_class_def trivial_monoid_def
    by (rule monoid_iso_class_of_monoid_eq_iff_groups)
      (simp_all add: G.Group_axioms trivial_Group)
  also have "... \<longleftrightarrow> G = {unit}"
  proof
    assume iso: "(G, composition, unit) \<cong>\<^sub>G
      ({undefined :: 'a}, (\<lambda>x y. undefined), undefined)"
    then obtain \<eta> where
      \<eta>: "group_isomorphism \<eta> G composition unit
        {undefined :: 'a} (\<lambda>(_::'a) (_::'a). undefined) undefined"
      by (simp add: isomorphic_as_groups_def) blast
    interpret \<eta>: group_isomorphism \<eta> G composition unit
      "{undefined :: 'a}" "\<lambda>(_::'a) (_::'a). undefined" undefined by fact
    show "G = {unit}"
    proof (rule equalityI)
      show "G \<subseteq> {unit}"
      proof
        fix x
        assume x: "x \<in> G"
        have \<eta>x: "\<eta> x = undefined"
          by (rule singletonD [OF \<eta>.map_closed [OF x]])
        have \<eta>unit: "\<eta> unit = undefined"
          by (rule \<eta>.commutes_with_unit)
        have "x = unit"
        proof (rule inj_onD [OF \<eta>.injective])
          show "\<eta> x = \<eta> unit"
            by (rule trans [OF \<eta>x \<eta>unit [symmetric]])
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
      ({undefined :: 'a}, (\<lambda>x y. undefined), undefined)"
      unfolding isomorphic_as_groups_def using iso by auto
  qed
  finally show ?thesis .
qed

end
