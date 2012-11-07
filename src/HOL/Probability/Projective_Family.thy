theory Projective_Family
imports Finite_Product_Measure Probability_Measure
begin

definition
  PiP :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i set \<Rightarrow> ('i \<Rightarrow> 'a) measure) \<Rightarrow> ('i \<Rightarrow> 'a) measure" where
  "PiP I M P = extend_measure (\<Pi>\<^isub>E i\<in>I. space (M i))
    {(J, X). (J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}
    (\<lambda>(J, X). prod_emb I M J (\<Pi>\<^isub>E j\<in>J. X j))
    (\<lambda>(J, X). emeasure (P J) (Pi\<^isub>E J X))"

lemma space_PiP[simp]: "space (PiP I M P) = space (PiM I M)"
  by (auto simp add: PiP_def space_PiM prod_emb_def intro!: space_extend_measure)

lemma sets_PiP[simp]: "sets (PiP I M P) = sets (PiM I M)"
  by (auto simp add: PiP_def sets_PiM prod_algebra_def prod_emb_def intro!: sets_extend_measure)

lemma measurable_PiP1[simp]: "measurable (PiP I M P) M' = measurable (\<Pi>\<^isub>M i\<in>I. M i) M'"
  unfolding measurable_def by auto

lemma measurable_PiP2[simp]: "measurable M' (PiP I M P) = measurable M' (\<Pi>\<^isub>M i\<in>I. M i)"
  unfolding measurable_def by auto

locale projective_family =
  fixes I::"'i set" and P::"'i set \<Rightarrow> ('i \<Rightarrow> 'a) measure" and M::"('i \<Rightarrow> 'a measure)"
  assumes projective: "\<And>J H X. J \<noteq> {} \<Longrightarrow> J \<subseteq> H \<Longrightarrow> H \<subseteq> I \<Longrightarrow> finite H \<Longrightarrow> X \<in> sets (PiM J M) \<Longrightarrow>
     (P H) (prod_emb H M J X) = (P J) X"
  assumes prob_space: "\<And>J. finite J \<Longrightarrow> prob_space (P J)"
  assumes proj_space: "\<And>J. finite J \<Longrightarrow> space (P J) = space (PiM J M)"
  assumes proj_sets: "\<And>J. finite J \<Longrightarrow> sets (P J) = sets (PiM J M)"
  assumes proj_finite_measure: "\<And>J. finite J \<Longrightarrow> emeasure (P J) (space (PiM J M)) \<noteq> \<infinity>"
  assumes measure_space: "\<And>i. prob_space (M i)"
begin

lemma emeasure_PiP:
  assumes "finite J"
  assumes "J \<subseteq> I"
  assumes A: "\<And>i. i\<in>J \<Longrightarrow> A i \<in> sets (M i)"
  shows "emeasure (PiP J M P) (Pi\<^isub>E J A) = emeasure (P J) (Pi\<^isub>E J A)"
proof -
  have "Pi\<^isub>E J (restrict A J) \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))"
  proof safe
    fix x j assume "x \<in> Pi J (restrict A J)" "j \<in> J"
    hence "x j \<in> restrict A J j" by (auto simp: Pi_def)
    also have "\<dots> \<subseteq> space (M j)" using sets_into_space A `j \<in> J` by auto
    finally show "x j \<in> space (M j)" .
  qed
  hence "emeasure (PiP J M P) (Pi\<^isub>E J A) =
    emeasure (PiP J M P) (prod_emb J M J (Pi\<^isub>E J A))"
    using assms(1-3) sets_into_space by (auto simp add: prod_emb_id Pi_def)
  also have "\<dots> = emeasure (P J) (Pi\<^isub>E J A)"
  proof (rule emeasure_extend_measure_Pair[OF PiP_def])
    show "positive (sets (PiP J M P)) (P J)" unfolding positive_def by auto
    show "countably_additive (sets (PiP J M P)) (P J)" unfolding countably_additive_def
      by (auto simp: suminf_emeasure proj_sets[OF `finite J`])
    show "(J \<noteq> {} \<or> J = {}) \<and> finite J \<and> J \<subseteq> J \<and> A \<in> (\<Pi> j\<in>J. sets (M j))"
      using assms by auto
    fix K and X::"'i \<Rightarrow> 'a set"
    show "prod_emb J M K (Pi\<^isub>E K X) \<in> Pow (\<Pi>\<^isub>E i\<in>J. space (M i))"
      by (auto simp: prod_emb_def)
    assume JX: "(K \<noteq> {} \<or> J = {}) \<and> finite K \<and> K \<subseteq> J \<and> X \<in> (\<Pi> j\<in>K. sets (M j))"
    thus "emeasure (P J) (prod_emb J M K (Pi\<^isub>E K X)) = emeasure (P K) (Pi\<^isub>E K X)"
      using assms
      apply (cases "J = {}")
      apply (simp add: prod_emb_id)
      apply (fastforce simp add: intro!: projective sets_PiM_I_finite)
      done
  qed
  finally show ?thesis .
qed

lemma PiP_finite:
  assumes "finite J"
  assumes "J \<subseteq> I"
  shows "PiP J M P = P J" (is "?P = _")
proof (rule measure_eqI_generator_eq)
  let ?J = "{Pi\<^isub>E J E | E. \<forall>i\<in>J. E i \<in> sets (M i)}"
  let ?F = "\<lambda>i. \<Pi>\<^isub>E k\<in>J. space (M k)"
  let ?\<Omega> = "(\<Pi>\<^isub>E k\<in>J. space (M k))"
  show "Int_stable ?J"
    by (rule Int_stable_PiE)
  interpret finite_measure "P J" using proj_finite_measure `finite J`
    by (intro finite_measureI) (simp add: proj_space)
  show "emeasure ?P (?F _) \<noteq> \<infinity>" using assms `finite J` by (auto simp: emeasure_PiP)
  show "?J \<subseteq> Pow ?\<Omega>" by (auto simp: Pi_iff dest: sets_into_space)
  show "sets (PiP J M P) = sigma_sets ?\<Omega> ?J" "sets (P J) = sigma_sets ?\<Omega> ?J"
    using `finite J` proj_sets by (simp_all add: sets_PiM prod_algebra_eq_finite Pi_iff)
  fix X assume "X \<in> ?J"
  then obtain E where X: "X = Pi\<^isub>E J E" and E: "\<forall>i\<in>J. E i \<in> sets (M i)" by auto
  with `finite J` have "X \<in> sets (PiP J M P)" by simp
  have emb_self: "prod_emb J M J (Pi\<^isub>E J E) = Pi\<^isub>E J E"
    using E sets_into_space
    by (auto intro!: prod_emb_PiE_same_index)
  show "emeasure (PiP J M P) X = emeasure (P J) X"
    unfolding X using E
    by (intro emeasure_PiP assms) simp
qed (insert `finite J`, auto intro!: prod_algebraI_finite)

lemma emeasure_fun_emb[simp]:
  assumes L: "J \<noteq> {}" "J \<subseteq> L" "finite L" "L \<subseteq> I" and X: "X \<in> sets (PiM J M)"
  shows "emeasure (PiP L M P) (prod_emb L M J X) = emeasure (PiP J M P) X"
  using assms
  by (subst PiP_finite) (auto simp: PiP_finite finite_subset projective)

end

sublocale projective_family \<subseteq> M: prob_space "M i" for i
  by (rule measure_space)

end
