theory Schreier_Sanity
  imports Schreier_Refinement
begin

section \<open>Cross-checking the Schreier refinement indices\<close>

text \<open>
  These checks specialise one side of the Schreier construction to the
  canonical one-step series.  Both flattened refinement matrices must then be
  exactly the factor sequence of the other series, not merely a permutation of
  it.  This pins down the row bounds, endpoint orientation, factor packaging,
  and row-major flattening independently of the final multiset argument.
\<close>

context normal_series
begin

interpretation one_step: normal_series_pair
    G "(\<cdot>)" \<one> "one_step_normal_series_term G \<one>" 1 H n
proof (rule normal_series_pair.intro)
  show "normal_series G (\<cdot>) \<one> (one_step_normal_series_term G \<one>) 1"
    by (rule G.one_step_normal_series)
  show "normal_series G (\<cdot>) \<one> H n"
    by (rule normal_series_axioms)
qed

theorem one_step_schreier_factor_classes:
  "one_step.left_refinement_factor_classes = series_factor_classes \<and>
    one_step.right_refinement_factor_classes = series_factor_classes"
proof -
  have right_factor:
      "one_step.right_refinement_factor_class j 0 = series_factor_class j"
    if j: "j < n" for j
  proof -
    have start: "one_step.right_refinement_term j 0 = H j"
      by (rule one_step.right_refinement_start[OF j])
    have finish: "one_step.right_refinement_term j 1 = H (Suc j)"
      by (rule one_step.right_refinement_end[OF j])
    show ?thesis
      unfolding one_step.right_refinement_factor_class_def
      using start finish series_factor_class_eq_normal_factor_class
      by simp
  qed
  have left_factor:
      "one_step.left_refinement_factor_class 0 j = series_factor_class j"
    if j: "j < n" for j
  proof -
    have transpose:
        "one_step.left_refinement_factor_class 0 j =
          one_step.right_refinement_factor_class j 0"
      by (rule one_step.refinement_factor_class_eq) (use j in simp_all)
    show ?thesis using transpose right_factor[OF j] by simp
  qed
  show ?thesis
  proof
    show "one_step.left_refinement_factor_classes = series_factor_classes"
      unfolding one_step.left_refinement_factor_classes_def series_factor_classes_def
      by (simp add: left_factor)
    show "one_step.right_refinement_factor_classes = series_factor_classes"
      unfolding one_step.right_refinement_factor_classes_def series_factor_classes_def
      by (simp add: right_factor)
  qed
qed

end

end
