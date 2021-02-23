(*  Title:      HOL/Probability/Infinite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

section \<open>Infinite Product Measure\<close>

theory Infinite_Product_Measure
  imports Probability_Measure Projective_Family
begin

lemma (in product_prob_space) distr_PiM_restrict_finite:
  assumes "finite J" "J \<subseteq> I"
  shows "distr (PiM I M) (PiM J M) (\<lambda>x. restrict x J) = PiM J M"
proof (rule PiM_eqI)
  fix X assume X: "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  { fix J X assume J: "J \<noteq> {} \<or> I = {}" "finite J" "J \<subseteq> I" and X: "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
    have "emeasure (PiM I M) (emb I J (Pi\<^sub>E J X)) = (\<Prod>i\<in>J. M i (X i))"
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

  have "emeasure (PiM I M) (emb I J (Pi\<^sub>E J X)) = (\<Prod>i\<in>J. M i (X i))"
  proof (cases "J \<noteq> {} \<or> I = {}")
    case False
    then obtain i where i: "J = {}" "i \<in> I" by auto
    then have "emb I {} {\<lambda>x. undefined} = emb I {i} (\<Pi>\<^sub>E i\<in>{i}. space (M i))"
      by (auto simp: space_PiM prod_emb_def)
    with i show ?thesis
      by (simp add: * M.emeasure_space_1)
  next
    case True
    then show ?thesis
      by (simp add: *[OF _ assms X])
  qed
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

lemma prob_space_PiM:
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)" shows "prob_space (PiM I M)"
proof -
  let ?M = "\<lambda>i. if i \<in> I then M i else count_space {undefined}"
  interpret M': prob_space "?M i" for i
    using M by (cases "i \<in> I") (auto intro!: prob_spaceI)
  interpret product_prob_space ?M I
    by unfold_locales
  have "prob_space (\<Pi>\<^sub>M i\<in>I. ?M i)"
    by unfold_locales
  also have "(\<Pi>\<^sub>M i\<in>I. ?M i) = (\<Pi>\<^sub>M i\<in>I. M i)"
    by (intro PiM_cong) auto
  finally show ?thesis .
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
  unfolding emeasure_eq_measure M.emeasure_eq_measure
  by (simp add: prod_ennreal measure_nonneg prod_nonneg)

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

lemma emeasure_PiM_emb:
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes J: "J \<subseteq> I" "finite J" and A: "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) (prod_emb I M J (Pi\<^sub>E J A)) = (\<Prod>i\<in>J. emeasure (M i) (A i))"
proof -
  let ?M = "\<lambda>i. if i \<in> I then M i else count_space {undefined}"
  interpret M': prob_space "?M i" for i
    using M by (cases "i \<in> I") (auto intro!: prob_spaceI)
  interpret P: product_prob_space ?M I
    by unfold_locales
  have "emeasure (Pi\<^sub>M I M) (prod_emb I M J (Pi\<^sub>E J A)) = emeasure (Pi\<^sub>M I ?M) (P.emb I J (Pi\<^sub>E J A))"
    by (auto simp: prod_emb_def PiE_iff intro!: arg_cong2[where f=emeasure] PiM_cong)
  also have "\<dots> = (\<Prod>i\<in>J. emeasure (M i) (A i))"
    using J A by (subst P.emeasure_PiM_emb[OF J]) (auto intro!: prod.cong)
  finally show ?thesis .
qed

lemma distr_pair_PiM_eq_PiM:
  fixes i' :: "'i" and I :: "'i set" and M :: "'i \<Rightarrow> 'a measure"
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)" "prob_space (M i')"
  shows "distr (M i' \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>I. M i)) (\<Pi>\<^sub>M i\<in>insert i' I. M i) (\<lambda>(x, X). X(i' := x)) =
    (\<Pi>\<^sub>M i\<in>insert i' I. M i)" (is "?L = _")
proof (rule measure_eqI_PiM_infinite[symmetric, OF refl])
  interpret M': prob_space "M i'" by fact
  interpret I: prob_space "(\<Pi>\<^sub>M i\<in>I. M i)"
    using M by (intro prob_space_PiM) auto
  interpret I': prob_space "(\<Pi>\<^sub>M i\<in>insert i' I. M i)"
    using M by (intro prob_space_PiM) auto
  show "finite_measure (\<Pi>\<^sub>M i\<in>insert i' I. M i)"
    by unfold_locales
  fix J A assume J: "finite J" "J \<subseteq> insert i' I" and A: "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets (M i)"
  let ?X = "prod_emb (insert i' I) M J (Pi\<^sub>E J A)"
  have "Pi\<^sub>M (insert i' I) M ?X = (\<Prod>i\<in>J. M i (A i))"
    using M J A by (intro emeasure_PiM_emb) auto
  also have "\<dots> = M i' (if i' \<in> J then (A i') else space (M i')) * (\<Prod>i\<in>J-{i'}. M i (A i))"
    using prod.insert_remove[of J "\<lambda>i. M i (A i)" i'] J M'.emeasure_space_1
    by (cases "i' \<in> J") (auto simp: insert_absorb)
  also have "(\<Prod>i\<in>J-{i'}. M i (A i)) = Pi\<^sub>M I M (prod_emb I M (J - {i'}) (Pi\<^sub>E (J - {i'}) A))"
    using M J A by (intro emeasure_PiM_emb[symmetric]) auto
  also have "M i' (if i' \<in> J then (A i') else space (M i')) * \<dots> =
    (M i' \<Otimes>\<^sub>M Pi\<^sub>M I M) ((if i' \<in> J then (A i') else space (M i')) \<times> prod_emb I M (J - {i'}) (Pi\<^sub>E (J - {i'}) A))"
    using J A by (intro I.emeasure_pair_measure_Times[symmetric] sets_PiM_I) auto
  also have "((if i' \<in> J then (A i') else space (M i')) \<times> prod_emb I M (J - {i'}) (Pi\<^sub>E (J - {i'}) A)) =
    (\<lambda>(x, X). X(i' := x)) -` ?X \<inter> space (M i' \<Otimes>\<^sub>M Pi\<^sub>M I M)"
    using A[of i', THEN sets.sets_into_space] unfolding set_eq_iff
    by (simp add: prod_emb_def space_pair_measure space_PiM PiE_fun_upd ac_simps cong: conj_cong)
       (auto simp add: Pi_iff Ball_def all_conj_distrib)
  finally show "Pi\<^sub>M (insert i' I) M ?X = ?L ?X"
    using J A by (simp add: emeasure_distr)
qed simp

lemma distr_PiM_reindex:
  assumes M: "\<And>i. i \<in> K \<Longrightarrow> prob_space (M i)"
  assumes f: "inj_on f I" "f \<in> I \<rightarrow> K"
  shows "distr (Pi\<^sub>M K M) (\<Pi>\<^sub>M i\<in>I. M (f i)) (\<lambda>\<omega>. \<lambda>n\<in>I. \<omega> (f n)) = (\<Pi>\<^sub>M i\<in>I. M (f i))"
    (is "distr ?K ?I ?t = ?I")
proof (rule measure_eqI_PiM_infinite[symmetric, OF refl])
  interpret prob_space ?I
    using f M by (intro prob_space_PiM) auto
  show "finite_measure ?I"
    by unfold_locales
  fix A J assume J: "finite J" "J \<subseteq> I" and A: "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets (M (f i))"
  have [simp]: "i \<in> J \<Longrightarrow> the_inv_into I f (f i) = i" for i
    using J f by (intro the_inv_into_f_f) auto
  have "?I (prod_emb I (\<lambda>i. M (f i)) J (Pi\<^sub>E J A)) = (\<Prod>j\<in>J. M (f j) (A j))"
    using f J A by (intro emeasure_PiM_emb M) auto
  also have "\<dots> = (\<Prod>j\<in>f`J. M j (A (the_inv_into I f j)))"
    using f J by (subst prod.reindex) (auto intro!: prod.cong intro: inj_on_subset simp: the_inv_into_f_f)
  also have "\<dots> = ?K (prod_emb K M (f`J) (\<Pi>\<^sub>E j\<in>f`J. A (the_inv_into I f j)))"
    using f J A by (intro emeasure_PiM_emb[symmetric] M) (auto simp: the_inv_into_f_f)
  also have "prod_emb K M (f`J) (\<Pi>\<^sub>E j\<in>f`J. A (the_inv_into I f j)) = ?t -` prod_emb I (\<lambda>i. M (f i)) J (Pi\<^sub>E J A) \<inter> space ?K"
    using f J A by (auto simp: prod_emb_def space_PiM Pi_iff PiE_iff Int_absorb1)
  also have "?K \<dots> = distr ?K ?I ?t (prod_emb I (\<lambda>i. M (f i)) J (Pi\<^sub>E J A))"
    using f J A by (intro emeasure_distr[symmetric] sets_PiM_I) (auto simp: Pi_iff)
  finally show "?I (prod_emb I (\<lambda>i. M (f i)) J (Pi\<^sub>E J A)) = distr ?K ?I ?t (prod_emb I (\<lambda>i. M (f i)) J (Pi\<^sub>E J A))" .
qed simp

lemma distr_PiM_component:
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "i \<in> I"
  shows "distr (Pi\<^sub>M I M) (M i) (\<lambda>\<omega>. \<omega> i) = M i"
proof -
  have *: "(\<lambda>\<omega>. \<omega> i) -` A \<inter> space (Pi\<^sub>M I M) = prod_emb I M {i} (\<Pi>\<^sub>E i'\<in>{i}. A)" for A
    by (auto simp: prod_emb_def space_PiM)
  show ?thesis
    apply (intro measure_eqI)
    apply (auto simp add: emeasure_distr \<open>i\<in>I\<close> * emeasure_PiM_emb M)
    apply (subst emeasure_PiM_emb)
    apply (simp_all add: M \<open>i\<in>I\<close>)
    done
qed

lemma AE_PiM_component:
  "(\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)) \<Longrightarrow> i \<in> I \<Longrightarrow> AE x in M i. P x \<Longrightarrow> AE x in PiM I M. P (x i)"
  using AE_distrD[of "\<lambda>x. x i" "PiM I M" "M i"]
  by (subst (asm) distr_PiM_component[of I _ i]) (auto intro: AE_distrD[of "\<lambda>x. x i" _ _ P])

lemma decseq_emb_PiE:
  "incseq J \<Longrightarrow> decseq (\<lambda>i. prod_emb I M (J i) (\<Pi>\<^sub>E j\<in>J i. X j))"
  by (fastforce simp: decseq_def prod_emb_def incseq_def Pi_iff)

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
    by (auto simp: prod_emb_def Pi_iff extensional_def)
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
    by (auto simp: prod_emb_def extensional_def Pi_iff)
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
    (prod_emb ?I ?M (J \<inter> {..<i}) (\<Pi>\<^sub>E j\<in>J \<inter> {..<i}. E j)) \<times>
    (prod_emb ?I ?M (((+) i) -` J) (\<Pi>\<^sub>E j\<in>((+) i) -` J. E (i + j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM prod_emb_def all_conj_distrib PiE_iff
               split: split_comb_seq split_comb_seq_asm)
  then have "emeasure ?D ?X = emeasure (S \<Otimes>\<^sub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr[OF measurable_comb_seq])
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure S ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times)  (auto intro!: sets_PiM_I finite_vimageI simp: inj_on_def)
  also have "emeasure S ?F = (\<Prod>j\<in>((+) i) -` J. emeasure M (E (i + j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI inj_on_def)
  also have "\<dots> = (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j))"
    by (rule prod.reindex_cong [of "\<lambda>x. x - i"])
      (auto simp: image_iff ac_simps nat_eq_diff_eq cong: conj_cong intro!: inj_onI)
  also have "emeasure S ?E = (\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j))"
    using J by (intro emeasure_PiM_emb) simp_all
  also have "(\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j)) * (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (subst mult.commute) (auto simp: J prod.subset_diff[symmetric])
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

lemma PiM_iter:
  "distr (M \<Otimes>\<^sub>M S) S (\<lambda>(s, \<omega>). case_nat s \<omega>) = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (\<Pi>\<^sub>E j\<in>J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets.sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (M \<Otimes>\<^sub>M S) = (if 0 \<in> J then E 0 else space M) \<times>
    (prod_emb ?I ?M (Suc -` J) (\<Pi>\<^sub>E j\<in>Suc -` J. E (Suc j)))" (is "_ = ?E \<times> ?F")
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
    by (rule prod.reindex_cong [of "\<lambda>x. x - 1"])
      (auto simp: image_iff nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure M ?E * (\<Prod>j\<in>J - {0}. emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (auto simp: M.emeasure_space_1 prod.remove J)
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

end

lemma PiM_return:
  assumes "finite I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> {a i} \<in> sets (M i)"
  shows "PiM I (\<lambda>i. return (M i) (a i)) = return (PiM I M) (restrict a I)"
proof -
  have [simp]: "a i \<in> space (M i)" if "i \<in> I" for i
    using assms(2)[OF that] by (meson insert_subset sets.sets_into_space)
  interpret prob_space "PiM I (\<lambda>i. return (M i) (a i))"
    by (intro prob_space_PiM prob_space_return) auto
  have "AE x in PiM I (\<lambda>i. return (M i) (a i)). \<forall>i\<in>I. x i = restrict a I i"
    by (intro eventually_ball_finite ballI AE_PiM_component prob_space_return assms)
       (auto simp: AE_return)
  moreover have "AE x in PiM I (\<lambda>i. return (M i) (a i)). x \<in> space (PiM I (\<lambda>i. return (M i) (a i)))"
    by simp
  ultimately have "AE x in PiM I (\<lambda>i. return (M i) (a i)). x = restrict a I"
    by eventually_elim (auto simp: fun_eq_iff space_PiM)
  hence "Pi\<^sub>M I (\<lambda>i. return (M i) (a i)) = return (Pi\<^sub>M I (\<lambda>i. return (M i) (a i))) (restrict a I)"
    by (rule AE_eq_constD)
  also have "\<dots> = return (PiM I M) (restrict a I)"
    by (intro return_cong sets_PiM_cong) auto
  finally show ?thesis .
qed

lemma distr_PiM_finite_prob_space':
  assumes fin: "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M' i)"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> f \<in> measurable (M i) (M' i)"
  shows   "distr (PiM I M) (PiM I M') (compose I f) = PiM I (\<lambda>i. distr (M i) (M' i) f)"
proof -
  define N where "N = (\<lambda>i. if i \<in> I then M i else return (count_space UNIV) undefined)"
  define N' where "N' = (\<lambda>i. if i \<in> I then M' i else return (count_space UNIV) undefined)"
  have [simp]: "PiM I N = PiM I M" "PiM I N' = PiM I M'"
    by (intro PiM_cong; simp add: N_def N'_def)+

  have "distr (PiM I N) (PiM I N') (compose I f) = PiM I (\<lambda>i. distr (N i) (N' i) f)"
  proof (rule distr_PiM_finite_prob_space)
    show "product_prob_space N"
      by (rule product_prob_spaceI) (auto simp: N_def intro!: prob_space_return assms)
    show "product_prob_space N'"
      by (rule product_prob_spaceI) (auto simp: N'_def intro!: prob_space_return assms)
  qed (auto simp: N_def N'_def fin)
  also have "Pi\<^sub>M I (\<lambda>i. distr (N i) (N' i) f) = Pi\<^sub>M I (\<lambda>i. distr (M i) (M' i) f)"
    by (intro PiM_cong) (simp_all add: N_def N'_def)
  finally show ?thesis by simp
qed

end
