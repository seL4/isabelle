theory Composition_Factor_Classes
  imports Normal_Series Group_Iso_Classes "HOL-Library.Multiset"
begin

section \<open>Isomorphism classes of normal-series factors\<close>

text \<open>
  The factor API stores quotient groups as the same carrier--operation--unit
  triples used throughout \<open>New_Algebra\<close>.  This theory turns the valid factors of
  an arbitrary normal series into isomorphism classes and then into a multiset.
  When used with a composition series, these are the corresponding
  composition-factor classes.  The multiset is the invariant needed for a
  native Jordan--Hölder theorem; no uniqueness theorem is assumed here.
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

end

end
