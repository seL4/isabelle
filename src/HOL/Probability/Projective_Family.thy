(*  Title:      HOL/Probability/Projective_Family.thy
    Author:     Fabian Immler, TU München
    Author:     Johannes Hölzl, TU München
*)

header {*Projective Family*}

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
  interpret prob_space "P J" using prob_space `finite J` by simp
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

lemma prod_emb_injective:
  assumes "J \<noteq> {}" "J \<subseteq> L" "finite J" and sets: "X \<in> sets (Pi\<^isub>M J M)" "Y \<in> sets (Pi\<^isub>M J M)"
  assumes "prod_emb L M J X = prod_emb L M J Y"
  shows "X = Y"
proof (rule injective_vimage_restrict)
  show "X \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))" "Y \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))"
    using sets[THEN sets_into_space] by (auto simp: space_PiM)
  have "\<forall>i\<in>L. \<exists>x. x \<in> space (M i)"
  proof
    fix i assume "i \<in> L"
    interpret prob_space "P {i}" using prob_space by simp
    from not_empty show "\<exists>x. x \<in> space (M i)" by (auto simp add: proj_space space_PiM)
  qed
  from bchoice[OF this]
  show "(\<Pi>\<^isub>E i\<in>L. space (M i)) \<noteq> {}" by auto
  show "(\<lambda>x. restrict x J) -` X \<inter> (\<Pi>\<^isub>E i\<in>L. space (M i)) = (\<lambda>x. restrict x J) -` Y \<inter> (\<Pi>\<^isub>E i\<in>L. space (M i))"
    using `prod_emb L M J X = prod_emb L M J Y` by (simp add: prod_emb_def)
qed fact

abbreviation
  "emb L K X \<equiv> prod_emb L M K X"

definition generator :: "('i \<Rightarrow> 'a) set set" where
  "generator = (\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` sets (Pi\<^isub>M J M))"

lemma generatorI':
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> emb I J X \<in> generator"
  unfolding generator_def by auto

lemma algebra_generator:
  assumes "I \<noteq> {}" shows "algebra (\<Pi>\<^isub>E i\<in>I. space (M i)) generator" (is "algebra ?\<Omega> ?G")
  unfolding algebra_def algebra_axioms_def ring_of_sets_iff
proof (intro conjI ballI)
  let ?G = generator
  show "?G \<subseteq> Pow ?\<Omega>"
    by (auto simp: generator_def prod_emb_def)
  from `I \<noteq> {}` obtain i where "i \<in> I" by auto
  then show "{} \<in> ?G"
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="\<lambda>i. {}"]
             simp: sigma_sets.Empty generator_def prod_emb_def)
  from `i \<in> I` show "?\<Omega> \<in> ?G"
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="Pi\<^isub>E {i} (\<lambda>i. space (M i))"]
             simp: generator_def prod_emb_def)
  fix A assume "A \<in> ?G"
  then obtain JA XA where XA: "JA \<noteq> {}" "finite JA" "JA \<subseteq> I" "XA \<in> sets (Pi\<^isub>M JA M)" and A: "A = emb I JA XA"
    by (auto simp: generator_def)
  fix B assume "B \<in> ?G"
  then obtain JB XB where XB: "JB \<noteq> {}" "finite JB" "JB \<subseteq> I" "XB \<in> sets (Pi\<^isub>M JB M)" and B: "B = emb I JB XB"
    by (auto simp: generator_def)
  let ?RA = "emb (JA \<union> JB) JA XA"
  let ?RB = "emb (JA \<union> JB) JB XB"
  have *: "A - B = emb I (JA \<union> JB) (?RA - ?RB)" "A \<union> B = emb I (JA \<union> JB) (?RA \<union> ?RB)"
    using XA A XB B by auto
  show "A - B \<in> ?G" "A \<union> B \<in> ?G"
    unfolding * using XA XB by (safe intro!: generatorI') auto
qed

lemma sets_PiM_generator:
  "sets (PiM I M) = sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) generator"
proof cases
  assume "I = {}" then show ?thesis
    unfolding generator_def
    by (auto simp: sets_PiM_empty sigma_sets_empty_eq cong: conj_cong)
next
  assume "I \<noteq> {}"
  show ?thesis
  proof
    show "sets (Pi\<^isub>M I M) \<subseteq> sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) generator"
      unfolding sets_PiM
    proof (safe intro!: sigma_sets_subseteq)
      fix A assume "A \<in> prod_algebra I M" with `I \<noteq> {}` show "A \<in> generator"
        by (auto intro!: generatorI' sets_PiM_I_finite elim!: prod_algebraE)
    qed
  qed (auto simp: generator_def space_PiM[symmetric] intro!: sigma_sets_subset)
qed

lemma generatorI:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> A = emb I J X \<Longrightarrow> A \<in> generator"
  unfolding generator_def by auto

definition
  "\<mu>G A =
    (THE x. \<forall>J. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> J \<subseteq> I \<longrightarrow> (\<forall>X\<in>sets (Pi\<^isub>M J M). A = emb I J X \<longrightarrow> x = emeasure (PiP J M P) X))"

lemma \<mu>G_spec:
  assumes J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^isub>M J M)"
  shows "\<mu>G A = emeasure (PiP J M P) X"
  unfolding \<mu>G_def
proof (intro the_equality allI impI ballI)
  fix K Y assume K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "A = emb I K Y" "Y \<in> sets (Pi\<^isub>M K M)"
  have "emeasure (PiP K M P) Y = emeasure (PiP (K \<union> J) M P) (emb (K \<union> J) K Y)"
    using K J by simp
  also have "emb (K \<union> J) K Y = emb (K \<union> J) J X"
    using K J by (simp add: prod_emb_injective[of "K \<union> J" I])
  also have "emeasure (PiP (K \<union> J) M P) (emb (K \<union> J) J X) = emeasure (PiP J M P) X"
    using K J by simp
  finally show "emeasure (PiP J M P) X = emeasure (PiP K M P) Y" ..
qed (insert J, force)

lemma \<mu>G_eq:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> \<mu>G (emb I J X) = emeasure (PiP J M P) X"
  by (intro \<mu>G_spec) auto

lemma generator_Ex:
  assumes *: "A \<in> generator"
  shows "\<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^isub>M J M) \<and> A = emb I J X \<and> \<mu>G A = emeasure (PiP J M P) X"
proof -
  from * obtain J X where J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^isub>M J M)"
    unfolding generator_def by auto
  with \<mu>G_spec[OF this] show ?thesis by auto
qed

lemma generatorE:
  assumes A: "A \<in> generator"
  obtains J X where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)" "emb I J X = A" "\<mu>G A = emeasure (PiP J M P) X"
proof -
  from generator_Ex[OF A] obtain X J where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)" "emb I J X = A"
    "\<mu>G A = emeasure (PiP J M P) X" by auto
  then show thesis by (intro that) auto
qed

lemma merge_sets:
  "J \<inter> K = {} \<Longrightarrow> A \<in> sets (Pi\<^isub>M (J \<union> K) M) \<Longrightarrow> x \<in> space (Pi\<^isub>M J M) \<Longrightarrow> (\<lambda>y. merge J K (x,y)) -` A \<inter> space (Pi\<^isub>M K M) \<in> sets (Pi\<^isub>M K M)"
  by simp

lemma merge_emb:
  assumes "K \<subseteq> I" "J \<subseteq> I" and y: "y \<in> space (Pi\<^isub>M J M)"
  shows "((\<lambda>x. merge J (I - J) (y, x)) -` emb I K X \<inter> space (Pi\<^isub>M I M)) =
    emb I (K - J) ((\<lambda>x. merge J (K - J) (y, x)) -` emb (J \<union> K) K X \<inter> space (Pi\<^isub>M (K - J) M))"
proof -
  have [simp]: "\<And>x J K L. merge J K (y, restrict x L) = merge J (K \<inter> L) (y, x)"
    by (auto simp: restrict_def merge_def)
  have [simp]: "\<And>x J K L. restrict (merge J K (y, x)) L = merge (J \<inter> L) (K \<inter> L) (y, x)"
    by (auto simp: restrict_def merge_def)
  have [simp]: "(I - J) \<inter> K = K - J" using `K \<subseteq> I` `J \<subseteq> I` by auto
  have [simp]: "(K - J) \<inter> (K \<union> J) = K - J" by auto
  have [simp]: "(K - J) \<inter> K = K - J" by auto
  from y `K \<subseteq> I` `J \<subseteq> I` show ?thesis
    by (simp split: split_merge add: prod_emb_def Pi_iff extensional_merge_sub set_eq_iff space_PiM)
       auto
qed

lemma positive_\<mu>G:
  assumes "I \<noteq> {}"
  shows "positive generator \<mu>G"
proof -
  interpret G!: algebra "\<Pi>\<^isub>E i\<in>I. space (M i)" generator by (rule algebra_generator) fact
  show ?thesis
  proof (intro positive_def[THEN iffD2] conjI ballI)
    from generatorE[OF G.empty_sets] guess J X . note this[simp]
    have "X = {}"
      by (rule prod_emb_injective[of J I]) simp_all
    then show "\<mu>G {} = 0" by simp
  next
    fix A assume "A \<in> generator"
    from generatorE[OF this] guess J X . note this[simp]
    show "0 \<le> \<mu>G A" by (simp add: emeasure_nonneg)
  qed
qed

lemma additive_\<mu>G:
  assumes "I \<noteq> {}"
  shows "additive generator \<mu>G"
proof -
  interpret G!: algebra "\<Pi>\<^isub>E i\<in>I. space (M i)" generator by (rule algebra_generator) fact
  show ?thesis
  proof (intro additive_def[THEN iffD2] ballI impI)
    fix A assume "A \<in> generator" with generatorE guess J X . note J = this
    fix B assume "B \<in> generator" with generatorE guess K Y . note K = this
    assume "A \<inter> B = {}"
    have JK: "J \<union> K \<noteq> {}" "J \<union> K \<subseteq> I" "finite (J \<union> K)"
      using J K by auto
    have JK_disj: "emb (J \<union> K) J X \<inter> emb (J \<union> K) K Y = {}"
      apply (rule prod_emb_injective[of "J \<union> K" I])
      apply (insert `A \<inter> B = {}` JK J K)
      apply (simp_all add: Int prod_emb_Int)
      done
    have AB: "A = emb I (J \<union> K) (emb (J \<union> K) J X)" "B = emb I (J \<union> K) (emb (J \<union> K) K Y)"
      using J K by simp_all
    then have "\<mu>G (A \<union> B) = \<mu>G (emb I (J \<union> K) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y))"
      by simp
    also have "\<dots> = emeasure (PiP (J \<union> K) M P) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y)"
      using JK J(1, 4) K(1, 4) by (simp add: \<mu>G_eq Un del: prod_emb_Un)
    also have "\<dots> = \<mu>G A + \<mu>G B"
      using J K JK_disj by (simp add: plus_emeasure[symmetric])
    finally show "\<mu>G (A \<union> B) = \<mu>G A + \<mu>G B" .
  qed
qed

end

end
