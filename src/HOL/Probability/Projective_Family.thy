(*  Title:      HOL/Probability/Projective_Family.thy
    Author:     Fabian Immler, TU München
    Author:     Johannes Hölzl, TU München
*)

section {*Projective Family*}

theory Projective_Family
imports Finite_Product_Measure Probability_Measure
begin

lemma (in product_prob_space) distr_restrict:
  assumes "J \<noteq> {}" "J \<subseteq> K" "finite K"
  shows "(\<Pi>\<^sub>M i\<in>J. M i) = distr (\<Pi>\<^sub>M i\<in>K. M i) (\<Pi>\<^sub>M i\<in>J. M i) (\<lambda>f. restrict f J)" (is "?P = ?D")
proof (rule measure_eqI_generator_eq)
  have "finite J" using `J \<subseteq> K` `finite K` by (auto simp add: finite_subset)
  interpret J: finite_product_prob_space M J proof qed fact
  interpret K: finite_product_prob_space M K proof qed fact

  let ?J = "{Pi\<^sub>E J E | E. \<forall>i\<in>J. E i \<in> sets (M i)}"
  let ?F = "\<lambda>i. \<Pi>\<^sub>E k\<in>J. space (M k)"
  let ?\<Omega> = "(\<Pi>\<^sub>E k\<in>J. space (M k))"
  show "Int_stable ?J"
    by (rule Int_stable_PiE)
  show "range ?F \<subseteq> ?J" "(\<Union>i. ?F i) = ?\<Omega>"
    using `finite J` by (auto intro!: prod_algebraI_finite)
  { fix i show "emeasure ?P (?F i) \<noteq> \<infinity>" by simp }
  show "?J \<subseteq> Pow ?\<Omega>" by (auto simp: Pi_iff dest: sets.sets_into_space)
  show "sets (\<Pi>\<^sub>M i\<in>J. M i) = sigma_sets ?\<Omega> ?J" "sets ?D = sigma_sets ?\<Omega> ?J"
    using `finite J` by (simp_all add: sets_PiM prod_algebra_eq_finite Pi_iff)

  fix X assume "X \<in> ?J"
  then obtain E where [simp]: "X = Pi\<^sub>E J E" and E: "\<forall>i\<in>J. E i \<in> sets (M i)" by auto
  with `finite J` have X: "X \<in> sets (Pi\<^sub>M J M)"
    by simp

  have "emeasure ?P X = (\<Prod> i\<in>J. emeasure (M i) (E i))"
    using E by (simp add: J.measure_times)
  also have "\<dots> = (\<Prod> i\<in>J. emeasure (M i) (if i \<in> J then E i else space (M i)))"
    by simp
  also have "\<dots> = (\<Prod> i\<in>K. emeasure (M i) (if i \<in> J then E i else space (M i)))"
    using `finite K` `J \<subseteq> K`
    by (intro setprod.mono_neutral_left) (auto simp: M.emeasure_space_1)
  also have "\<dots> = emeasure (Pi\<^sub>M K M) (\<Pi>\<^sub>E i\<in>K. if i \<in> J then E i else space (M i))"
    using E by (simp add: K.measure_times)
  also have "(\<Pi>\<^sub>E i\<in>K. if i \<in> J then E i else space (M i)) = (\<lambda>f. restrict f J) -` Pi\<^sub>E J E \<inter> (\<Pi>\<^sub>E i\<in>K. space (M i))"
    using `J \<subseteq> K` sets.sets_into_space E by (force simp: Pi_iff PiE_def split: split_if_asm)
  finally show "emeasure (Pi\<^sub>M J M) X = emeasure ?D X"
    using X `J \<subseteq> K` apply (subst emeasure_distr)
    by (auto intro!: measurable_restrict_subset simp: space_PiM)
qed

lemma (in product_prob_space) emeasure_prod_emb[simp]:
  assumes L: "J \<noteq> {}" "J \<subseteq> L" "finite L" and X: "X \<in> sets (Pi\<^sub>M J M)"
  shows "emeasure (Pi\<^sub>M L M) (prod_emb L M J X) = emeasure (Pi\<^sub>M J M) X"
  by (subst distr_restrict[OF L])
     (simp add: prod_emb_def space_PiM emeasure_distr measurable_restrict_subset L X)

definition
  limP :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i set \<Rightarrow> ('i \<Rightarrow> 'a) measure) \<Rightarrow> ('i \<Rightarrow> 'a) measure" where
  "limP I M P = extend_measure (\<Pi>\<^sub>E i\<in>I. space (M i))
    {(J, X). (J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}
    (\<lambda>(J, X). prod_emb I M J (\<Pi>\<^sub>E j\<in>J. X j))
    (\<lambda>(J, X). emeasure (P J) (Pi\<^sub>E J X))"

abbreviation "lim\<^sub>P \<equiv> limP"

lemma space_limP[simp]: "space (limP I M P) = space (PiM I M)"
  by (auto simp add: limP_def space_PiM prod_emb_def intro!: space_extend_measure)

lemma sets_limP[simp]: "sets (limP I M P) = sets (PiM I M)"
  by (auto simp add: limP_def sets_PiM prod_algebra_def prod_emb_def intro!: sets_extend_measure)

lemma measurable_limP1[simp]: "measurable (limP I M P) M' = measurable (\<Pi>\<^sub>M i\<in>I. M i) M'"
  unfolding measurable_def by auto

lemma measurable_limP2[simp]: "measurable M' (limP I M P) = measurable M' (\<Pi>\<^sub>M i\<in>I. M i)"
  unfolding measurable_def by auto

locale projective_family =
  fixes I::"'i set" and P::"'i set \<Rightarrow> ('i \<Rightarrow> 'a) measure" and M::"('i \<Rightarrow> 'a measure)"
  assumes projective: "\<And>J H X. J \<noteq> {} \<Longrightarrow> J \<subseteq> H \<Longrightarrow> H \<subseteq> I \<Longrightarrow> finite H \<Longrightarrow> X \<in> sets (PiM J M) \<Longrightarrow>
     (P H) (prod_emb H M J X) = (P J) X"
  assumes proj_prob_space: "\<And>J. finite J \<Longrightarrow> prob_space (P J)"
  assumes proj_space: "\<And>J. finite J \<Longrightarrow> space (P J) = space (PiM J M)"
  assumes proj_sets: "\<And>J. finite J \<Longrightarrow> sets (P J) = sets (PiM J M)"
begin

lemma emeasure_limP:
  assumes "finite J"
  assumes "J \<subseteq> I"
  assumes A: "\<And>i. i\<in>J \<Longrightarrow> A i \<in> sets (M i)"
  shows "emeasure (limP J M P) (Pi\<^sub>E J A) = emeasure (P J) (Pi\<^sub>E J A)"
proof -
  have "Pi\<^sub>E J (restrict A J) \<subseteq> (\<Pi>\<^sub>E i\<in>J. space (M i))"
    using sets.sets_into_space[OF A] by (auto simp: PiE_iff) blast
  hence "emeasure (limP J M P) (Pi\<^sub>E J A) =
    emeasure (limP J M P) (prod_emb J M J (Pi\<^sub>E J A))"
    using assms(1-3) sets.sets_into_space by (auto simp add: prod_emb_id PiE_def Pi_def)
  also have "\<dots> = emeasure (P J) (Pi\<^sub>E J A)"
  proof (rule emeasure_extend_measure_Pair[OF limP_def])
    show "positive (sets (limP J M P)) (P J)" unfolding positive_def by auto
    show "countably_additive (sets (limP J M P)) (P J)" unfolding countably_additive_def
      by (auto simp: suminf_emeasure proj_sets[OF `finite J`])
    show "(J \<noteq> {} \<or> J = {}) \<and> finite J \<and> J \<subseteq> J \<and> A \<in> (\<Pi> j\<in>J. sets (M j))"
      using assms by auto
    fix K and X::"'i \<Rightarrow> 'a set"
    show "prod_emb J M K (Pi\<^sub>E K X) \<in> Pow (\<Pi>\<^sub>E i\<in>J. space (M i))"
      by (auto simp: prod_emb_def)
    assume JX: "(K \<noteq> {} \<or> J = {}) \<and> finite K \<and> K \<subseteq> J \<and> X \<in> (\<Pi> j\<in>K. sets (M j))"
    thus "emeasure (P J) (prod_emb J M K (Pi\<^sub>E K X)) = emeasure (P K) (Pi\<^sub>E K X)"
      using assms
      apply (cases "J = {}")
      apply (simp add: prod_emb_id)
      apply (fastforce simp add: intro!: projective sets_PiM_I_finite)
      done
  qed
  finally show ?thesis .
qed

lemma limP_finite[simp]:
  assumes "finite J"
  assumes "J \<subseteq> I"
  shows "limP J M P = P J" (is "?P = _")
proof (rule measure_eqI_generator_eq)
  let ?J = "{Pi\<^sub>E J E | E. \<forall>i\<in>J. E i \<in> sets (M i)}"
  let ?\<Omega> = "(\<Pi>\<^sub>E k\<in>J. space (M k))"
  interpret prob_space "P J" using proj_prob_space `finite J` by simp
  show "emeasure ?P (\<Pi>\<^sub>E k\<in>J. space (M k)) \<noteq> \<infinity>" using assms `finite J` by (auto simp: emeasure_limP)
  show "sets (limP J M P) = sigma_sets ?\<Omega> ?J" "sets (P J) = sigma_sets ?\<Omega> ?J"
    using `finite J` proj_sets by (simp_all add: sets_PiM prod_algebra_eq_finite Pi_iff)
  fix X assume "X \<in> ?J"
  then obtain E where X: "X = Pi\<^sub>E J E" and E: "\<forall>i\<in>J. E i \<in> sets (M i)" by auto
  with `finite J` have "X \<in> sets (limP J M P)" by simp
  have emb_self: "prod_emb J M J (Pi\<^sub>E J E) = Pi\<^sub>E J E"
    using E sets.sets_into_space
    by (auto intro!: prod_emb_PiE_same_index)
  show "emeasure (limP J M P) X = emeasure (P J) X"
    unfolding X using E
    by (intro emeasure_limP assms) simp
qed (auto simp: Pi_iff dest: sets.sets_into_space intro: Int_stable_PiE)

lemma emeasure_fun_emb[simp]:
  assumes L: "J \<noteq> {}" "J \<subseteq> L" "finite L" "L \<subseteq> I" and X: "X \<in> sets (PiM J M)"
  shows "emeasure (limP L M P) (prod_emb L M J X) = emeasure (limP J M P) X"
  using assms
  by (subst limP_finite) (auto simp: limP_finite finite_subset projective)

abbreviation
  "emb L K X \<equiv> prod_emb L M K X"

lemma prod_emb_injective:
  assumes "J \<subseteq> L" and sets: "X \<in> sets (Pi\<^sub>M J M)" "Y \<in> sets (Pi\<^sub>M J M)"
  assumes "emb L J X = emb L J Y"
  shows "X = Y"
proof (rule injective_vimage_restrict)
  show "X \<subseteq> (\<Pi>\<^sub>E i\<in>J. space (M i))" "Y \<subseteq> (\<Pi>\<^sub>E i\<in>J. space (M i))"
    using sets[THEN sets.sets_into_space] by (auto simp: space_PiM)
  have "\<forall>i\<in>L. \<exists>x. x \<in> space (M i)"
  proof
    fix i assume "i \<in> L"
    interpret prob_space "P {i}" using proj_prob_space by simp
    from not_empty show "\<exists>x. x \<in> space (M i)" by (auto simp add: proj_space space_PiM)
  qed
  from bchoice[OF this]
  show "(\<Pi>\<^sub>E i\<in>L. space (M i)) \<noteq> {}" by (auto simp: PiE_def)
  show "(\<lambda>x. restrict x J) -` X \<inter> (\<Pi>\<^sub>E i\<in>L. space (M i)) = (\<lambda>x. restrict x J) -` Y \<inter> (\<Pi>\<^sub>E i\<in>L. space (M i))"
    using `prod_emb L M J X = prod_emb L M J Y` by (simp add: prod_emb_def)
qed fact

definition generator :: "('i \<Rightarrow> 'a) set set" where
  "generator = (\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` sets (Pi\<^sub>M J M))"

lemma generatorI':
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^sub>M J M) \<Longrightarrow> emb I J X \<in> generator"
  unfolding generator_def by auto

lemma algebra_generator:
  assumes "I \<noteq> {}" shows "algebra (\<Pi>\<^sub>E i\<in>I. space (M i)) generator" (is "algebra ?\<Omega> ?G")
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
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="Pi\<^sub>E {i} (\<lambda>i. space (M i))"]
             simp: generator_def prod_emb_def)
  fix A assume "A \<in> ?G"
  then obtain JA XA where XA: "JA \<noteq> {}" "finite JA" "JA \<subseteq> I" "XA \<in> sets (Pi\<^sub>M JA M)" and A: "A = emb I JA XA"
    by (auto simp: generator_def)
  fix B assume "B \<in> ?G"
  then obtain JB XB where XB: "JB \<noteq> {}" "finite JB" "JB \<subseteq> I" "XB \<in> sets (Pi\<^sub>M JB M)" and B: "B = emb I JB XB"
    by (auto simp: generator_def)
  let ?RA = "emb (JA \<union> JB) JA XA"
  let ?RB = "emb (JA \<union> JB) JB XB"
  have *: "A - B = emb I (JA \<union> JB) (?RA - ?RB)" "A \<union> B = emb I (JA \<union> JB) (?RA \<union> ?RB)"
    using XA A XB B by auto
  show "A - B \<in> ?G" "A \<union> B \<in> ?G"
    unfolding * using XA XB by (safe intro!: generatorI') auto
qed

lemma sets_PiM_generator:
  "sets (PiM I M) = sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) generator"
proof cases
  assume "I = {}" then show ?thesis
    unfolding generator_def
    by (auto simp: sets_PiM_empty sigma_sets_empty_eq cong: conj_cong)
next
  assume "I \<noteq> {}"
  show ?thesis
  proof
    show "sets (Pi\<^sub>M I M) \<subseteq> sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) generator"
      unfolding sets_PiM
    proof (safe intro!: sigma_sets_subseteq)
      fix A assume "A \<in> prod_algebra I M" with `I \<noteq> {}` show "A \<in> generator"
        by (auto intro!: generatorI' sets_PiM_I_finite elim!: prod_algebraE)
    qed
  qed (auto simp: generator_def space_PiM[symmetric] intro!: sets.sigma_sets_subset)
qed

lemma generatorI:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^sub>M J M) \<Longrightarrow> A = emb I J X \<Longrightarrow> A \<in> generator"
  unfolding generator_def by auto

definition mu_G ("\<mu>G") where
  "\<mu>G A =
    (THE x. \<forall>J. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> J \<subseteq> I \<longrightarrow> (\<forall>X\<in>sets (Pi\<^sub>M J M). A = emb I J X \<longrightarrow> x = emeasure (limP J M P) X))"

lemma mu_G_spec:
  assumes J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^sub>M J M)"
  shows "\<mu>G A = emeasure (limP J M P) X"
  unfolding mu_G_def
proof (intro the_equality allI impI ballI)
  fix K Y assume K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "A = emb I K Y" "Y \<in> sets (Pi\<^sub>M K M)"
  have "emeasure (limP K M P) Y = emeasure (limP (K \<union> J) M P) (emb (K \<union> J) K Y)"
    using K J by (simp del: limP_finite)
  also have "emb (K \<union> J) K Y = emb (K \<union> J) J X"
    using K J by (simp add: prod_emb_injective[of "K \<union> J" I])
  also have "emeasure (limP (K \<union> J) M P) (emb (K \<union> J) J X) = emeasure (limP J M P) X"
    using K J by (simp del: limP_finite)
  finally show "emeasure (limP J M P) X = emeasure (limP K M P) Y" ..
qed (insert J, force)

lemma mu_G_eq:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^sub>M J M) \<Longrightarrow> \<mu>G (emb I J X) = emeasure (limP J M P) X"
  by (intro mu_G_spec) auto

lemma generator_Ex:
  assumes *: "A \<in> generator"
  shows "\<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^sub>M J M) \<and> A = emb I J X \<and> \<mu>G A = emeasure (limP J M P) X"
proof -
  from * obtain J X where J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^sub>M J M)"
    unfolding generator_def by auto
  with mu_G_spec[OF this] show ?thesis by (auto simp del: limP_finite)
qed

lemma generatorE:
  assumes A: "A \<in> generator"
  obtains J X where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^sub>M J M)" "emb I J X = A" "\<mu>G A = emeasure (limP J M P) X"
  using generator_Ex[OF A] by atomize_elim auto

lemma merge_sets:
  "J \<inter> K = {} \<Longrightarrow> A \<in> sets (Pi\<^sub>M (J \<union> K) M) \<Longrightarrow> x \<in> space (Pi\<^sub>M J M) \<Longrightarrow> (\<lambda>y. merge J K (x,y)) -` A \<inter> space (Pi\<^sub>M K M) \<in> sets (Pi\<^sub>M K M)"
  by simp

lemma merge_emb:
  assumes "K \<subseteq> I" "J \<subseteq> I" and y: "y \<in> space (Pi\<^sub>M J M)"
  shows "((\<lambda>x. merge J (I - J) (y, x)) -` emb I K X \<inter> space (Pi\<^sub>M I M)) =
    emb I (K - J) ((\<lambda>x. merge J (K - J) (y, x)) -` emb (J \<union> K) K X \<inter> space (Pi\<^sub>M (K - J) M))"
proof -
  have [simp]: "\<And>x J K L. merge J K (y, restrict x L) = merge J (K \<inter> L) (y, x)"
    by (auto simp: restrict_def merge_def)
  have [simp]: "\<And>x J K L. restrict (merge J K (y, x)) L = merge (J \<inter> L) (K \<inter> L) (y, x)"
    by (auto simp: restrict_def merge_def)
  have [simp]: "(I - J) \<inter> K = K - J" using `K \<subseteq> I` `J \<subseteq> I` by auto
  have [simp]: "(K - J) \<inter> (K \<union> J) = K - J" by auto
  have [simp]: "(K - J) \<inter> K = K - J" by auto
  from y `K \<subseteq> I` `J \<subseteq> I` show ?thesis
    by (simp split: split_merge add: prod_emb_def Pi_iff PiE_def extensional_merge_sub set_eq_iff space_PiM)
       auto
qed

lemma positive_mu_G:
  assumes "I \<noteq> {}"
  shows "positive generator \<mu>G"
proof -
  interpret G!: algebra "\<Pi>\<^sub>E i\<in>I. space (M i)" generator by (rule algebra_generator) fact
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

lemma additive_mu_G:
  assumes "I \<noteq> {}"
  shows "additive generator \<mu>G"
proof -
  interpret G!: algebra "\<Pi>\<^sub>E i\<in>I. space (M i)" generator by (rule algebra_generator) fact
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
      apply (simp_all add: sets.Int prod_emb_Int)
      done
    have AB: "A = emb I (J \<union> K) (emb (J \<union> K) J X)" "B = emb I (J \<union> K) (emb (J \<union> K) K Y)"
      using J K by simp_all
    then have "\<mu>G (A \<union> B) = \<mu>G (emb I (J \<union> K) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y))"
      by simp
    also have "\<dots> = emeasure (limP (J \<union> K) M P) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y)"
      using JK J(1, 4) K(1, 4) by (simp add: mu_G_eq sets.Un del: prod_emb_Un)
    also have "\<dots> = \<mu>G A + \<mu>G B"
      using J K JK_disj by (simp add: plus_emeasure[symmetric] del: limP_finite)
    finally show "\<mu>G (A \<union> B) = \<mu>G A + \<mu>G B" .
  qed
qed

end

sublocale product_prob_space \<subseteq> projective_family I "\<lambda>J. PiM J M" M
proof (simp add: projective_family_def, safe)
  fix J::"'i set" assume [simp]: "finite J"
  interpret f: finite_product_prob_space M J proof qed fact
  show "prob_space (Pi\<^sub>M J M)"
  proof
    show "emeasure (Pi\<^sub>M J M) (space (Pi\<^sub>M J M)) = 1"
      by (simp add: space_PiM emeasure_PiM emeasure_space_1)
  qed
qed

end
