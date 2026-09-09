section \<open>Finite relative normal chains\<close>

theory Normal_Chain
  imports Normal_Series Group_Iso_Classes "HOL-Library.Multiset"
begin

subsection \<open>Normal factors\<close>

text \<open>
  A refinement of one step in a normal series starts at an intermediate
  subgroup rather than at the trivial subgroup.  The following locale records
  exactly the structure shared by such relative chains: finitely many
  subgroups of one ambient group, with each term normal in its successor.
\<close>

definition normal_factor ::
    "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      ('a set set \<times> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) \<times> 'a set)"
  where
    "normal_factor K H composition unit \<equiv>
      (normal_subgroup.Factor_Group K H composition unit,
       Monoid_congruence.quotient_composition H composition
         (normal_subgroup.Congruence K H composition unit),
       Equivalence.Class H
         (normal_subgroup.Congruence K H composition unit) unit)"

definition normal_factor_class ::
    "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set group_iso_class"
  where
    "normal_factor_class K H composition unit \<equiv>
      group_iso_class_of (group_structure (normal_factor K H composition unit))"

text \<open>
  A normal factor is a group whenever its denominator is normal in its
  numerator.  Equality of factor classes can therefore be discharged by an
  ordinary group isomorphism between the corresponding quotient triples.
\<close>
lemma normal_factor_group:
  assumes "normal_subgroup K H composition unit"
  shows "Group (fst (normal_factor K H composition unit))
      (fst (snd (normal_factor K H composition unit)))
      (snd (snd (normal_factor K H composition unit)))"
proof -
  interpret N: normal_subgroup K H composition unit by fact
  show ?thesis
    unfolding normal_factor_def using N.quotient.Group_axioms by simp
qed

lemma normal_factor_class_eq_iff:
  assumes KH: "normal_subgroup K H composition unit"
    and LM: "normal_subgroup L M composition unit"
  shows "normal_factor_class K H composition unit =
      normal_factor_class L M composition unit \<longleftrightarrow>
      normal_factor K H composition unit \<cong>\<^sub>G normal_factor L M composition unit"
  unfolding normal_factor_class_def
  by (rule group_iso_class_of_group_structure_eq_iff[OF
        normal_factor_group[OF KH] normal_factor_group[OF LM]])

text \<open>
  A normal factor is trivial precisely when its denominator and numerator
  coincide.  The quotient-level argument is proved once in
  \<open>Factor_Group_eq_singleton_iff\<close>; the carrier lemma below exposes it
  through the packaged factor triple, independently of the representative
  chosen for the trivial isomorphism class.
\<close>
lemma normal_factor_carrier_eq_singleton_iff:
  assumes N: "normal_subgroup K H composition unit"
  shows "fst (normal_factor K H composition unit) =
      {snd (snd (normal_factor K H composition unit))} \<longleftrightarrow> K = H"
  by (simp add: assms normal_factor_def normal_subgroup.Factor_Group_eq_singleton_iff)

lemma normal_factor_class_eq_trivial_iff:
  assumes N: "normal_subgroup K H composition unit"
  shows "normal_factor_class K H composition unit = trivial_group_iso_class \<longleftrightarrow> K = H"
  unfolding normal_factor_class_def
  using assms normal_factor_group[OF N]
  by (metis group_iso_class_eq_trivial_iff normal_factor_carrier_eq_singleton_iff prod.exhaust_sel)

locale normal_chain =
  G: Group G "(\<cdot>)" \<one>
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  fixes C :: "nat \<Rightarrow> 'a set" and n :: nat
  assumes term_subgroup:
      "\<And>i. i \<le> n \<Longrightarrow> Subgroup (C i) G (\<cdot>) \<one>"
    and normal_step:
      "\<And>i. i < n \<Longrightarrow> normal_subgroup (C i) (C (Suc i)) (\<cdot>) \<one>"
begin

lemma step_subset:
  assumes "i < n"
  shows "C i \<subseteq> C (Suc i)"
proof -
  interpret step: normal_subgroup "C i" "C (Suc i)" "(\<cdot>)" \<one>
    by (rule normal_step[OF assms])
  show ?thesis by (rule step.subset)
qed

lemma chain_mono:
  fixes i j :: nat
  assumes ij: "i \<le> j" and jn: "j \<le> n"
  shows "C i \<subseteq> C j"
  using ij
proof (induction rule: inc_induct)
  case (step k)
  then show ?case
    using jn order_less_le_trans step_subset by blast
qed auto

definition chain_factor_class :: "nat \<Rightarrow> 'a set group_iso_class"
  where "chain_factor_class i \<equiv> normal_factor_class (C i) (C (Suc i)) (\<cdot>) \<one>"

lemma prefix_normal_chain:
  assumes "k \<le> n"
  shows "normal_chain G (\<cdot>) \<one> C k"
proof intro_locales
  show "normal_chain_axioms G (\<cdot>) \<one> C k"
    by (simp add: assms le_trans normal_chain_axioms_def normal_step order_less_le_trans
        term_subgroup)
qed

end

sublocale normal_series \<subseteq> chain: normal_chain G "(\<cdot>)" \<one> H n
proof intro_locales
  show "normal_chain_axioms G (\<cdot>) \<one> H n"
    by (simp add: normal_chain_axioms_def normal_step term_subgroup)
qed


subsection \<open>Isomorphism classes of normal-series factors\<close>

text \<open>
  We turn the valid factors of
  an arbitrary normal series into isomorphism classes and then into a multiset.
  When used with a composition series, these are the corresponding
  composition-factor classes.
\<close>

context normal_series
begin

definition series_factor_class :: "nat \<Rightarrow> 'a set group_iso_class"
  where "series_factor_class i \<equiv> group_iso_class_of (group_structure (series_factor i))"

text \<open>The class sequence is ordered by increasing factor index.\<close>

definition series_factor_classes :: "'a set group_iso_class list"
  where "series_factor_classes \<equiv> List.map series_factor_class [0..<n]"

definition series_factor_multiset :: "'a set group_iso_class multiset"
  where "series_factor_multiset \<equiv> mset series_factor_classes"

lemma length_series_factor_classes:
  "length series_factor_classes = n"
  unfolding series_factor_classes_def by simp

lemma series_factor_classes_prefix:
  assumes k: "k \<le> n"
  shows "take k series_factor_classes = List.map series_factor_class [0..<k]"
  using k unfolding series_factor_classes_def by (simp add: take_map)

lemma series_factor_classes_nth:
  assumes i: "i < n"
  shows "series_factor_classes ! i = series_factor_class i"
  using i unfolding series_factor_classes_def by simp

lemma size_series_factor_multiset:
  "size series_factor_multiset = n"
  unfolding series_factor_multiset_def using length_series_factor_classes by simp

lemma series_factor_class_eq_iff:
  assumes i: "i < n" and j: "j < n"
  shows "series_factor_class i = series_factor_class j \<longleftrightarrow>
    series_factor i \<cong>\<^sub>G series_factor j"
  by (simp add: group_iso_class_of_group_structure_eq_iff i j series_factor_class_def
      series_factor_group)

lemma series_factor_eq_normal_factor:
  "series_factor i = normal_factor (H i) (H (Suc i)) (\<cdot>) \<one>"
  unfolding series_factor_def normal_factor_def by rule

lemma series_factor_class_eq_normal_factor_class:
  "series_factor_class i =
    normal_factor_class (H i) (H (Suc i)) (\<cdot>) \<one>"
  unfolding series_factor_class_def normal_factor_class_def
  by (simp add: series_factor_eq_normal_factor)

end

end
