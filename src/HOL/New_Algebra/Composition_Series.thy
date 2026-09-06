theory Composition_Series
  imports Normal_Series Simple_Group
begin

section \<open>Composition series\<close>

text \<open>
  A simple factor group is the quotient associated with a normal subgroup whose
  factor group is simple.  Naming this local construction keeps the quotient
  operations attached to the existing @{locale normal_subgroup} interpretation.
\<close>

locale simple_factor_group =
  N: normal_subgroup K H "(\<cdot>)" \<one> +
  Q: Simple_Group N.Factor_Group N.quotient_composition "N.Class \<one>"
  for K and H and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

lemma factor_group_is_simple:
  "Simple_Group N.Factor_Group N.quotient_composition (N.Class \<one>)"
  by (rule Q.Simple_Group_axioms)

lemma factor_group_nontrivial:
  "N.Factor_Group \<noteq> {N.Class \<one>}"
  by (rule Q.nontrivial)

lemma proper:
  "K \<noteq> H"
  using N.Factor_Group_eq_singleton_iff Q.nontrivial by blast

end

text \<open>
  A composition series is a finite normal series whose successive factor groups
  are simple.  The indexed representation is inherited from @{locale normal_series}.
\<close>

locale composition_series = normal_series +
  assumes factor_simple:
    "\<And>i. i < n \<Longrightarrow>
      simple_factor_group (H i) (H (Suc i)) (\<cdot>) \<one>"
begin

lemma factor_simple_step:
  assumes i: "i < n"
  shows "simple_factor_group (H i) (H (Suc i)) (\<cdot>) \<one>"
  by (rule factor_simple[OF i])

lemma series_factor_simple:
  assumes i: "i < n"
  shows "Simple_Group (fst (series_factor i))
      (fst (snd (series_factor i))) (snd (snd (series_factor i)))"
proof -
  interpret step: simple_factor_group "H i" "H (Suc i)" "(\<cdot>)" \<one>
    by (rule factor_simple[OF i])
  show ?thesis
    unfolding series_factor_def
    using step.factor_group_is_simple by simp
qed

lemma series_factors_nth_simple:
  assumes i: "i < n"
  shows "Simple_Group (fst (series_factors ! i))
      (fst (snd (series_factors ! i))) (snd (snd (series_factors ! i)))"
  using series_factors_nth[OF i] series_factor_simple[OF i] by simp

lemma composition_step_strict:
  assumes i: "i < n"
  shows "H i \<noteq> H (Suc i)"
proof -
  interpret step: simple_factor_group "H i" "H (Suc i)" "(\<cdot>)" \<one>
    by (rule factor_simple[OF i])
  show ?thesis by (rule step.proper)
qed

text \<open>Every prefix of a composition series is again a composition series.\<close>

lemma prefix_composition_series:
  assumes k: "k \<le> n"
  shows "composition_series (H k) (\<cdot>) \<one> H k"
proof -
  show ?thesis
  proof (intro composition_series.intro)
    show "normal_series (H k) (\<cdot>) \<one> H k"
      by (rule prefix_normal_series[OF k])
  next
    show "composition_series_axioms (\<cdot>) \<one> H k"
    proof (intro composition_series_axioms.intro)
      show "\<And>i. i < k \<Longrightarrow>
          simple_factor_group (H i) (H (Suc i)) (\<cdot>) \<one>"
      proof -
        fix i
        assume i: "i < k"
        have i_n: "i < n" by (rule less_le_trans[OF i k])
        show "simple_factor_group (H i) (H (Suc i)) (\<cdot>) \<one>"
          by (rule factor_simple[OF i_n])
      qed
    qed
  qed
qed

text \<open>A composition series has positive length exactly when its group is nontrivial.\<close>

lemma zero_length_iff_trivial:
  "n = 0 \<longleftrightarrow> G = {\<one>}"
proof
  show "n = 0 \<Longrightarrow> G = {\<one>}"
    by (rule zero_length_implies_trivial)
next
  assume G_trivial: "G = {\<one>}"
  show "n = 0"
  proof (rule ccontr)
    assume n_nonzero: "n \<noteq> 0"
    have zero_lt_n: "0 < n" by (cases n) (simp_all add: n_nonzero)
    have one_le_n: "Suc 0 \<le> n" by (rule Suc_leI[OF zero_lt_n])
    have H1_subgroup: "Subgroup (H (Suc 0)) G (\<cdot>) \<one>"
      by (rule term_subgroup[OF one_le_n])
    interpret H1: Subgroup "H (Suc 0)" G "(\<cdot>)" \<one> by fact
    have H1_subset_singleton: "H (Suc 0) \<subseteq> {\<one>}"
      using H1.subset G_trivial by simp
    have singleton_subset_H1: "{\<one>} \<subseteq> H (Suc 0)"
      using H1.sub_unit_closed by simp
    have H1_trivial: "H (Suc 0) = {\<one>}"
      by (rule subset_antisym[OF H1_subset_singleton singleton_subset_H1])
    have H0_H1: "H 0 = H (Suc 0)"
      using bottom H1_trivial by simp
    have H0_H1_neq: "H 0 \<noteq> H (Suc 0)"
      by (rule composition_step_strict[OF zero_lt_n])
    show False using H0_H1 H0_H1_neq by blast
  qed
qed

end

end
