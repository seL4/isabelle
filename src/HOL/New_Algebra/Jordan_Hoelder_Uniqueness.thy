theory Jordan_Hoelder_Uniqueness
  imports Simple_Factor_Chain
begin

section \<open>The Jordan--Hölder theorem\<close>

text \<open>
  Two composition series of the same set-based group form a normal-series
  pair, while simplicity of their factors supplies the additional rigidity
  needed to collapse each Schreier refinement row.  Keeping these assumptions
  in one locale makes the final comparison symmetric and explicit.
\<close>
locale composition_series_pair =
  normal_series_pair G "(\<cdot>)" \<one> A m B n +
  A_comp: composition_series G "(\<cdot>)" \<one> A m +
  B_comp: composition_series G "(\<cdot>)" \<one> B n
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and A :: "nat \<Rightarrow> 'a set" and m
    and B :: "nat \<Rightarrow> 'a set" and n
begin

text \<open>
  Each refinement row spans one simple composition factor.  The generic
  simple-factor chain theorem therefore leaves exactly that factor after
  deleting repetitions.
\<close>
lemma left_refinement_row_reduction:
  assumes i: "i < m"
  shows "nontrivial_factor_multiset (List.map (left_refinement_factor_class i) [0..<n]) =
         {#A.series_factor_class i#}"
proof -
  have "reduced_normal_chain_factor_multiset (left_refinement_term i) n (\<cdot>) \<one> =
        {#normal_factor_class (A i) (A (Suc i)) (\<cdot>) \<one>#}"
    using A_comp.factor_simple_step i left_refinement_end left_refinement_row left_refinement_start
    by (metis simple_factor_chain_reduction)
  then show ?thesis
    unfolding reduced_normal_chain_factor_multiset_def
      normal_chain_factor_classes_def left_refinement_factor_class_def
      A.series_factor_class_eq_normal_factor_class
    by simp
qed

lemma right_refinement_row_reduction:
  assumes j: "j < n"
  shows "nontrivial_factor_multiset (List.map (right_refinement_factor_class j) [0..<m]) =
         {#B.series_factor_class j#}"
proof -
  have "reduced_normal_chain_factor_multiset (right_refinement_term j) m (\<cdot>) \<one> =
        {#normal_factor_class (B j) (B (Suc j)) (\<cdot>) \<one>#}"
    using B_comp.factor_simple_step j right_refinement_end right_refinement_row right_refinement_start
    by (metis simple_factor_chain_reduction)
  then show ?thesis
    unfolding reduced_normal_chain_factor_multiset_def
      normal_chain_factor_classes_def right_refinement_factor_class_def
      B.series_factor_class_eq_normal_factor_class
    by simp
qed

lemma left_reduced_refinement_eq_series_factor_multiset:
  "left_reduced_refinement_factor_multiset = A.series_factor_multiset"
proof -
  have "left_reduced_refinement_factor_multiset =
      (\<Sum>i<m. nontrivial_factor_multiset (List.map (left_refinement_factor_class i) [0..<n]))"
    by (simp add: left_reduced_refinement_factor_multiset_def left_refinement_factor_classes_def
        nontrivial_factor_multiset_concat_map_upt)
  also have "... = (\<Sum>i<m. {#A.series_factor_class i#})"
    using left_refinement_row_reduction by auto
  also have "... = A.series_factor_multiset"
    using A.series_factor_classes_def A.series_factor_multiset_def by (metis mset_map_upt)
  finally show ?thesis .
qed

lemma right_reduced_refinement_eq_series_factor_multiset:
  "right_reduced_refinement_factor_multiset = B.series_factor_multiset"
proof -
  have "right_reduced_refinement_factor_multiset =
      (\<Sum>j<n. nontrivial_factor_multiset (List.map (right_refinement_factor_class j) [0..<m]))"
    by (simp add: nontrivial_factor_multiset_concat_map_upt right_reduced_refinement_factor_multiset_def
        right_refinement_factor_classes_def)
  also have "... = (\<Sum>j<n. {#B.series_factor_class j#})"
    using right_refinement_row_reduction by auto
  also have "... = B.series_factor_multiset"
    using B.series_factor_classes_def B.series_factor_multiset_def by (metis mset_map_upt)
  finally show ?thesis .
qed

text \<open>
  The factor-class multiset of a composition series is independent of the
  series.  Equality is obtained by identifying each original series with its
  reduced Schreier refinement and applying the reduced refinement theorem.
\<close>
theorem jordan_hoelder:
  "A.series_factor_multiset = B.series_factor_multiset"
  using left_reduced_refinement_eq_series_factor_multiset reduced_schreier_refinement
    right_reduced_refinement_eq_series_factor_multiset by presburger

corollary jordan_hoelder_length: "m = n"
  using A.size_series_factor_multiset B.size_series_factor_multiset jordan_hoelder by argo

end

end
