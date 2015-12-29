(*  Title:      HOL/Probability/Infinite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

section \<open>Infinite Product Measure\<close>

theory Infinite_Product_Measure
  imports Probability_Measure Caratheodory Projective_Family
begin

lemma (in product_prob_space) distr_PiM_restrict_finite:
  assumes "finite J" "J \<subseteq> I"
  shows "distr (PiM I M) (PiM J M) (\<lambda>x. restrict x J) = PiM J M"
proof (rule PiM_eqI)
  fix X assume X: "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  { fix J X assume J: "J \<noteq> {} \<or> I = {}" "finite J" "J \<subseteq> I" and X: "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
    have "emeasure (PiM I M) (emb I J (PiE J X)) = (\<Prod>i\<in>J. M i (X i))"
    proof (subst emeasure_extend_measure_Pair[OF PiM_def, where \<mu>'=lim], goal_cases)
      case 1 then show ?case
        by (simp add: M.emeasure_space_1 emeasure_PiM Pi_iff sets_PiM_I_finite emeasure_lim_emb)
    next
      case (2 J X)
      then have "emb I J (Pi\<^sub>E J X) \<in> sets (PiM I M)"
        by (intro measurable_prod_emb sets_PiM_I_finite) auto
      from this[THEN sets.sets_into_space] show ?case
        by (simp add: space_PiM)
    qed (insert assms J X, simp_all del: sets_lim
      add: M.emeasure_space_1 sets_lim[symmetric] emeasure_countably_additive emeasure_positive) }
  note * = this

  have "emeasure (PiM I M) (emb I J (PiE J X)) = (\<Prod>i\<in>J. M i (X i))"
  proof cases
    assume "\<not> (J \<noteq> {} \<or> I = {})"
    then obtain i where "J = {}" "i \<in> I" by auto
    moreover then have "emb I {} {\<lambda>x. undefined} = emb I {i} (\<Pi>\<^sub>E i\<in>{i}. space (M i))"
      by (auto simp: space_PiM prod_emb_def)
    ultimately show ?thesis
      by (simp add: * M.emeasure_space_1)
  qed (simp add: *[OF _ assms X])
  with assms show "emeasure (distr (Pi\<^sub>M I M) (Pi\<^sub>M J M) (\<lambda>x. restrict x J)) (Pi\<^sub>E J X) = (\<Prod>i\<in>J. emeasure (M i) (X i))"
    by (subst emeasure_distr_restrict[OF _ refl]) (auto intro!: sets_PiM_I_finite X)
qed (insert assms, auto)

lemma (in product_prob_space) emeasure_PiM_emb':
  "J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> X \<in> sets (PiM J M) \<Longrightarrow> emeasure (Pi\<^sub>M I M) (emb I J X) = PiM J M X"
  by (subst distr_PiM_restrict_finite[symmetric, of J])
     (auto intro!: emeasure_distr_restrict[symmetric])

lemma (in product_prob_space) emeasure_PiM_emb:
  "J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)) \<Longrightarrow> 
    emeasure (Pi\<^sub>M I M) (emb I J (Pi\<^sub>E J X)) = (\<Prod> i\<in>J. emeasure (M i) (X i))"
  by (subst emeasure_PiM_emb') (auto intro!: emeasure_PiM)

sublocale product_prob_space \<subseteq> P?: prob_space "Pi\<^sub>M I M"
proof
  have *: "emb I {} {\<lambda>x. undefined} = space (PiM I M)"
    by (auto simp: prod_emb_def space_PiM)
  show "emeasure (Pi\<^sub>M I M) (space (Pi\<^sub>M I M)) = 1"
    using emeasure_PiM_emb[of "{}" "\<lambda>_. {}"] by (simp add: *)
qed

lemma (in product_prob_space) emeasure_PiM_Collect:
  assumes X: "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) {x\<in>space (Pi\<^sub>M I M). \<forall>i\<in>J. x i \<in> X i} = (\<Prod> i\<in>J. emeasure (M i) (X i))"
proof -
  have "{x\<in>space (Pi\<^sub>M I M). \<forall>i\<in>J. x i \<in> X i} = emb I J (Pi\<^sub>E J X)"
    unfolding prod_emb_def using assms by (auto simp: space_PiM Pi_iff)
  with emeasure_PiM_emb[OF assms] show ?thesis by simp
qed

lemma (in product_prob_space) emeasure_PiM_Collect_single:
  assumes X: "i \<in> I" "A \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) {x\<in>space (Pi\<^sub>M I M). x i \<in> A} = emeasure (M i) A"
  using emeasure_PiM_Collect[of "{i}" "\<lambda>i. A"] assms
  by simp

lemma (in product_prob_space) measure_PiM_emb:
  assumes "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "measure (PiM I M) (emb I J (Pi\<^sub>E J X)) = (\<Prod> i\<in>J. measure (M i) (X i))"
  using emeasure_PiM_emb[OF assms]
  unfolding emeasure_eq_measure M.emeasure_eq_measure by (simp add: setprod_ereal)

lemma sets_Collect_single':
  "i \<in> I \<Longrightarrow> {x\<in>space (M i). P x} \<in> sets (M i) \<Longrightarrow> {x\<in>space (PiM I M). P (x i)} \<in> sets (PiM I M)"
  using sets_Collect_single[of i I "{x\<in>space (M i). P x}" M]
  by (simp add: space_PiM PiE_iff cong: conj_cong)

lemma (in finite_product_prob_space) finite_measure_PiM_emb:
  "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> measure (PiM I M) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. measure (M i) (A i))"
  using measure_PiM_emb[of I A] finite_index prod_emb_PiE_same_index[OF sets.sets_into_space, of I A M]
  by auto

lemma (in product_prob_space) PiM_component:
  assumes "i \<in> I"
  shows "distr (PiM I M) (M i) (\<lambda>\<omega>. \<omega> i) = M i"
proof (rule measure_eqI[symmetric])
  fix A assume "A \<in> sets (M i)"
  moreover have "((\<lambda>\<omega>. \<omega> i) -` A \<inter> space (PiM I M)) = {x\<in>space (PiM I M). x i \<in> A}"
    by auto
  ultimately show "emeasure (M i) A = emeasure (distr (PiM I M) (M i) (\<lambda>\<omega>. \<omega> i)) A"
    by (auto simp: \<open>i\<in>I\<close> emeasure_distr measurable_component_singleton emeasure_PiM_Collect_single)
qed simp

lemma (in product_prob_space) PiM_eq:
  assumes M': "sets M' = sets (PiM I M)"
  assumes eq: "\<And>J F. finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>j. j \<in> J \<Longrightarrow> F j \<in> sets (M j)) \<Longrightarrow>
    emeasure M' (prod_emb I M J (\<Pi>\<^sub>E j\<in>J. F j)) = (\<Prod>j\<in>J. emeasure (M j) (F j))"
  shows "M' = (PiM I M)"
proof (rule measure_eqI_PiM_infinite[symmetric, OF refl M'])
  show "finite_measure (Pi\<^sub>M I M)"
    by standard (simp add: P.emeasure_space_1)
qed (simp add: eq emeasure_PiM_emb)

lemma (in product_prob_space) AE_component: "i \<in> I \<Longrightarrow> AE x in M i. P x \<Longrightarrow> AE x in PiM I M. P (x i)"
  apply (rule AE_distrD[of "\<lambda>\<omega>. \<omega> i" "PiM I M" "M i" P])
  apply simp
  apply (subst PiM_component)
  apply simp_all
  done

subsection \<open>Sequence space\<close>

definition comb_seq :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "comb_seq i \<omega> \<omega>' j = (if j < i then \<omega> j else \<omega>' (j - i))"

lemma split_comb_seq: "P (comb_seq i \<omega> \<omega>' j) \<longleftrightarrow> (j < i \<longrightarrow> P (\<omega> j)) \<and> (\<forall>k. j = i + k \<longrightarrow> P (\<omega>' k))"
  by (auto simp: comb_seq_def not_less)

lemma split_comb_seq_asm: "P (comb_seq i \<omega> \<omega>' j) \<longleftrightarrow> \<not> ((j < i \<and> \<not> P (\<omega> j)) \<or> (\<exists>k. j = i + k \<and> \<not> P (\<omega>' k)))"
  by (auto simp: comb_seq_def)

lemma measurable_comb_seq:
  "(\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<in> measurable ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)) (\<Pi>\<^sub>M i\<in>UNIV. M)"
proof (rule measurable_PiM_single)
  show "(\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<in> space ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)) \<rightarrow> (UNIV \<rightarrow>\<^sub>E space M)"
    by (auto simp: space_pair_measure space_PiM PiE_iff split: split_comb_seq)
  fix j :: nat and A assume A: "A \<in> sets M"
  then have *: "{\<omega> \<in> space ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)). case_prod (comb_seq i) \<omega> j \<in> A} =
    (if j < i then {\<omega> \<in> space (\<Pi>\<^sub>M i\<in>UNIV. M). \<omega> j \<in> A} \<times> space (\<Pi>\<^sub>M i\<in>UNIV. M)
              else space (\<Pi>\<^sub>M i\<in>UNIV. M) \<times> {\<omega> \<in> space (\<Pi>\<^sub>M i\<in>UNIV. M). \<omega> (j - i) \<in> A})"
    by (auto simp: space_PiM space_pair_measure comb_seq_def dest: sets.sets_into_space)
  show "{\<omega> \<in> space ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)). case_prod (comb_seq i) \<omega> j \<in> A} \<in> sets ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M))"
    unfolding * by (auto simp: A intro!: sets_Collect_single)
qed

lemma measurable_comb_seq'[measurable (raw)]:
  assumes f: "f \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)" and g: "g \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)"
  shows "(\<lambda>x. comb_seq i (f x) (g x)) \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)"
  using measurable_compose[OF measurable_Pair[OF f g] measurable_comb_seq] by simp

lemma comb_seq_0: "comb_seq 0 \<omega> \<omega>' = \<omega>'"
  by (auto simp add: comb_seq_def)

lemma comb_seq_Suc: "comb_seq (Suc n) \<omega> \<omega>' = comb_seq n \<omega> (case_nat (\<omega> n) \<omega>')"
  by (auto simp add: comb_seq_def not_less less_Suc_eq le_imp_diff_is_add intro!: ext split: nat.split)

lemma comb_seq_Suc_0[simp]: "comb_seq (Suc 0) \<omega> = case_nat (\<omega> 0)"
  by (intro ext) (simp add: comb_seq_Suc comb_seq_0)

lemma comb_seq_less: "i < n \<Longrightarrow> comb_seq n \<omega> \<omega>' i = \<omega> i"
  by (auto split: split_comb_seq)

lemma comb_seq_add: "comb_seq n \<omega> \<omega>' (i + n) = \<omega>' i"
  by (auto split: nat.split split_comb_seq)

lemma case_nat_comb_seq: "case_nat s' (comb_seq n \<omega> \<omega>') (i + n) = case_nat (case_nat s' \<omega> n) \<omega>' i"
  by (auto split: nat.split split_comb_seq)

lemma case_nat_comb_seq':
  "case_nat s (comb_seq i \<omega> \<omega>') = comb_seq (Suc i) (case_nat s \<omega>) \<omega>'"
  by (auto split: split_comb_seq nat.split)

locale sequence_space = product_prob_space "\<lambda>i. M" "UNIV :: nat set" for M
begin

abbreviation "S \<equiv> \<Pi>\<^sub>M i\<in>UNIV::nat set. M"

lemma infprod_in_sets[intro]:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets M"
  shows "Pi UNIV E \<in> sets S"
proof -
  have "Pi UNIV E = (\<Inter>i. emb UNIV {..i} (\<Pi>\<^sub>E j\<in>{..i}. E j))"
    using E E[THEN sets.sets_into_space]
    by (auto simp: prod_emb_def Pi_iff extensional_def) blast
  with E show ?thesis by auto
qed

lemma measure_PiM_countable:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets M"
  shows "(\<lambda>n. \<Prod>i\<le>n. measure M (E i)) \<longlonglongrightarrow> measure S (Pi UNIV E)"
proof -
  let ?E = "\<lambda>n. emb UNIV {..n} (Pi\<^sub>E {.. n} E)"
  have "\<And>n. (\<Prod>i\<le>n. measure M (E i)) = measure S (?E n)"
    using E by (simp add: measure_PiM_emb)
  moreover have "Pi UNIV E = (\<Inter>n. ?E n)"
    using E E[THEN sets.sets_into_space]
    by (auto simp: prod_emb_def extensional_def Pi_iff) blast
  moreover have "range ?E \<subseteq> sets S"
    using E by auto
  moreover have "decseq ?E"
    by (auto simp: prod_emb_def Pi_iff decseq_def)
  ultimately show ?thesis
    by (simp add: finite_Lim_measure_decseq)
qed

lemma nat_eq_diff_eq: 
  fixes a b c :: nat
  shows "c \<le> b \<Longrightarrow> a = b - c \<longleftrightarrow> a + c = b"
  by auto

lemma PiM_comb_seq:
  "distr (S \<Otimes>\<^sub>M S) S (\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (\<Pi>\<^sub>E j\<in>J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets.sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (S \<Otimes>\<^sub>M S) =
    (prod_emb ?I ?M (J \<inter> {..<i}) (PIE j:J \<inter> {..<i}. E j)) \<times>
    (prod_emb ?I ?M ((op + i) -` J) (PIE j:(op + i) -` J. E (i + j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM prod_emb_def all_conj_distrib PiE_iff
               split: split_comb_seq split_comb_seq_asm)
  then have "emeasure ?D ?X = emeasure (S \<Otimes>\<^sub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr[OF measurable_comb_seq])
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure S ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times)  (auto intro!: sets_PiM_I finite_vimageI simp: inj_on_def)
  also have "emeasure S ?F = (\<Prod>j\<in>(op + i) -` J. emeasure M (E (i + j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI inj_on_def)
  also have "\<dots> = (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j))"
    by (rule setprod.reindex_cong [of "\<lambda>x. x - i"])
       (auto simp: image_iff Bex_def not_less nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure S ?E = (\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j))"
    using J by (intro emeasure_PiM_emb) simp_all
  also have "(\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j)) * (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (subst mult.commute) (auto simp: J setprod.subset_diff[symmetric])
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

lemma PiM_iter:
  "distr (M \<Otimes>\<^sub>M S) S (\<lambda>(s, \<omega>). case_nat s \<omega>) = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (PIE j:J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets.sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (M \<Otimes>\<^sub>M S) = (if 0 \<in> J then E 0 else space M) \<times>
    (prod_emb ?I ?M (Suc -` J) (PIE j:Suc -` J. E (Suc j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM PiE_iff prod_emb_def all_conj_distrib
      split: nat.split nat.split_asm)
  then have "emeasure ?D ?X = emeasure (M \<Otimes>\<^sub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr)
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure M ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times) (auto intro!: sets_PiM_I finite_vimageI)
  also have "emeasure S ?F = (\<Prod>j\<in>Suc -` J. emeasure M (E (Suc j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI)
  also have "\<dots> = (\<Prod>j\<in>J - {0}. emeasure M (E j))"
    by (rule setprod.reindex_cong [of "\<lambda>x. x - 1"])
       (auto simp: image_iff Bex_def not_less nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure M ?E * (\<Prod>j\<in>J - {0}. emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (auto simp: M.emeasure_space_1 setprod.remove J)
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

end

end