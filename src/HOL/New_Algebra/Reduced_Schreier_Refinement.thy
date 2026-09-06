theory Reduced_Schreier_Refinement
  imports Schreier_Refinement
begin

section \<open>Reduced Schreier refinements\<close>

text \<open>
  A finite normal chain may repeat a term.  Its corresponding quotient is the
  one-element group and contributes no genuine factor.  The operation below
  removes precisely the canonical trivial isomorphism class while retaining
  multiplicity and forgetting order.
\<close>
definition nontrivial_factor_multiset ::
    "'a group_iso_class list \<Rightarrow> 'a group_iso_class multiset"
  where
    "nontrivial_factor_multiset factors =
      filter_mset (\<lambda>C. C \<noteq> trivial_group_iso_class) (mset factors)"

lemma nontrivial_factor_multiset_cong:
  assumes "mset factors = mset factors'"
  shows "nontrivial_factor_multiset factors =
    nontrivial_factor_multiset factors'"
  using assms unfolding nontrivial_factor_multiset_def by simp

lemma nontrivial_factor_multiset_append [simp]:
  "nontrivial_factor_multiset (factors @ factors') =
    nontrivial_factor_multiset factors + nontrivial_factor_multiset factors'"
  unfolding nontrivial_factor_multiset_def by simp

lemma nontrivial_factor_multiset_Nil [simp]:
  "nontrivial_factor_multiset [] = {#}"
  unfolding nontrivial_factor_multiset_def by simp

lemma nontrivial_factor_multiset_singleton [simp]:
  "nontrivial_factor_multiset [C] =
    (if C = trivial_group_iso_class then {#} else {#C#})"
  unfolding nontrivial_factor_multiset_def by simp

lemma nontrivial_factor_multiset_concat_map_upt:
  "nontrivial_factor_multiset (concat (List.map f [0..<m])) =
    (\<Sum>i<m. nontrivial_factor_multiset (f i))"
  by (induction m) (simp_all add: sum.lessThan_Suc)

context normal_series_pair
begin

text \<open>
  The trivial-class test has a concrete chain interpretation: it detects
  exactly an adjacent repetition.  These equivalences are the bridge used by
  the later Jordan--Hölder argument when a refinement row lies inside a simple
  factor.
\<close>
lemma left_refinement_factor_class_eq_trivial_iff:
  assumes i: "i < m" and j: "j < n"
  shows "left_refinement_factor_class i j = trivial_group_iso_class
    \<longleftrightarrow>
    left_refinement_term i j = left_refinement_term i (Suc j)"
  unfolding left_refinement_factor_class_def
  by (rule normal_factor_class_eq_trivial_iff[
        OF left_refinement_step[OF i j]])

lemma right_refinement_factor_class_eq_trivial_iff:
  assumes i: "i < m" and j: "j < n"
  shows "right_refinement_factor_class j i = trivial_group_iso_class
    \<longleftrightarrow>
    right_refinement_term j i = right_refinement_term j (Suc i)"
  unfolding right_refinement_factor_class_def
  by (rule normal_factor_class_eq_trivial_iff[
        OF right_refinement_step[OF i j]])

definition left_reduced_refinement_factor_multiset ::
    "'a set group_iso_class multiset"
  where
    "left_reduced_refinement_factor_multiset =
      nontrivial_factor_multiset left_refinement_factor_classes"

definition right_reduced_refinement_factor_multiset ::
    "'a set group_iso_class multiset"
  where
    "right_reduced_refinement_factor_multiset =
      nontrivial_factor_multiset right_refinement_factor_classes"

text \<open>
  Removing repetition factors from equivalent Schreier refinements preserves
  equality.  Unlike @{thm schreier_refinement}, this form is ready to compare
  directly with the factor multiset of a composition series.
\<close>
theorem reduced_schreier_refinement:
  "left_reduced_refinement_factor_multiset =
    right_reduced_refinement_factor_multiset"
  unfolding left_reduced_refinement_factor_multiset_def
    right_reduced_refinement_factor_multiset_def
  by (rule nontrivial_factor_multiset_cong[OF schreier_refinement])

end

end
