theory Series_Refinement
  imports Normal_Chain Zassenhaus_Lemma
begin

section \<open>Refining pairs of finite normal series\<close>

text \<open>
  The Zassenhaus lemma compares one refinement cell determined by a step from
  each of two normal series.  We name the two families of subgroup products
  independently of a particular cell.  Fixing one index produces a row of
  intermediate subgroups refining the corresponding step of the other series.
\<close>

locale normal_series_pair =
  A: normal_series G "(\<cdot>)" \<one> A m +
  B: normal_series G "(\<cdot>)" \<one> B n
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and A :: "nat \<Rightarrow> 'a set" and m
    and B :: "nat \<Rightarrow> 'a set" and n
begin

definition left_refinement_term :: "nat \<Rightarrow> nat \<Rightarrow> 'a set"
  where
    "left_refinement_term i j =
      (case_prod (\<cdot>)) ` ((A (Suc i) \<inter> B j) \<times> A i)"

definition right_refinement_term :: "nat \<Rightarrow> nat \<Rightarrow> 'a set"
  where
    "right_refinement_term j i =
      (case_prod (\<cdot>)) ` ((B (Suc j) \<inter> A i) \<times> B j)"

end

locale series_refinement_cell =
  normal_series_pair G "(\<cdot>)" \<one> A m B n
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and A :: "nat \<Rightarrow> 'a set" and m
    and B :: "nat \<Rightarrow> 'a set" and n
    and i j +
  assumes i_lt: "i < m" and j_lt: "j < n"
begin

lemma ambient_group:
  "Group G (\<cdot>) \<one>"
  by (rule A.G.Group_axioms)

lemma A_step_top_subgroup:
  "subgroup_of_group (A (Suc i)) G (\<cdot>) \<one>"
  by (rule subgroup_of_groupI[OF A.term_subgroup ambient_group])
    (use i_lt in simp)

lemma B_step_top_subgroup:
  "subgroup_of_group (B (Suc j)) G (\<cdot>) \<one>"
  by (rule subgroup_of_groupI[OF B.term_subgroup ambient_group])
    (use j_lt in simp)

interpretation cell: zassenhaus
    G "A (Suc i)" "B (Suc j)" "A i" "B j" "(\<cdot>)" \<one>
  by (rule zassenhaus.intro[OF ambient_group A_step_top_subgroup
        B_step_top_subgroup A.normal_step[OF i_lt] B.normal_step[OF j_lt]])

lemma left_refinement_bottom_eq:
  "left_refinement_term i j = cell.left_bottom"
  unfolding left_refinement_term_def cell.left_bottom_def by rule

lemma left_refinement_top_eq:
  "left_refinement_term i (Suc j) = cell.left_top"
  unfolding left_refinement_term_def cell.left_top_def by rule

lemma right_refinement_bottom_eq:
  "right_refinement_term j i = cell.right_bottom"
  unfolding right_refinement_term_def cell.right_bottom_def by rule

lemma right_refinement_top_eq:
  "right_refinement_term j (Suc i) = cell.right_top"
  unfolding right_refinement_term_def cell.right_top_def
  by (simp only: Int_commute)

lemma left_refinement_normal:
  "normal_subgroup (left_refinement_term i j)
      (left_refinement_term i (Suc j)) (\<cdot>) \<one>"
  unfolding left_refinement_bottom_eq left_refinement_top_eq
  by (rule cell.left_bottom_normal)

lemma right_refinement_normal:
  "normal_subgroup (right_refinement_term j i)
      (right_refinement_term j (Suc i)) (\<cdot>) \<one>"
  unfolding right_refinement_bottom_eq right_refinement_top_eq
  by (rule cell.right_bottom_normal)

text \<open>
  Opposite sides of every refinement cell have the same native quotient-group
  isomorphism class.  This is the factor-level form of Zassenhaus needed by a
  later Schreier refinement theorem; the statement contains no HOL-Algebra
  records and no representatives of quotient isomorphisms.
\<close>
theorem refinement_cell_factor_class_eq:
  "normal_factor_class (left_refinement_term i j)
      (left_refinement_term i (Suc j)) (\<cdot>) \<one> =
    normal_factor_class (right_refinement_term j i)
      (right_refinement_term j (Suc i)) (\<cdot>) \<one>"
proof (rule normal_factor_class_eq_iff[
      OF left_refinement_normal right_refinement_normal, THEN iffD2])
  show "normal_factor (left_refinement_term i j)
      (left_refinement_term i (Suc j)) (\<cdot>) \<one> \<cong>\<^sub>G
    normal_factor (right_refinement_term j i)
      (right_refinement_term j (Suc i)) (\<cdot>) \<one>"
    unfolding normal_factor_def left_refinement_bottom_eq left_refinement_top_eq
      right_refinement_bottom_eq right_refinement_top_eq
    by (rule cell.butterfly_lemma)
qed

end

end
