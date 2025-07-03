(*  Title:      HOL/Probability/Projective_Family.thy
    Author:     Fabian Immler, TU München
    Author:     Johannes Hölzl, TU München
*)

section \<open>Projective Family\<close>

theory Projective_Family
imports Giry_Monad
begin

(** Something strange going on here regarding the syntax \<omega>(n := x) vs fun_upd \<omega> n x
    See nn_integral_eP, etc. **)

lemma vimage_restrict_preserve_mono:
  assumes J: "J \<subseteq> I"
  and sets: "A \<subseteq> (\<Pi>\<^sub>E i\<in>J. S i)" "B \<subseteq> (\<Pi>\<^sub>E i\<in>J. S i)" and ne: "(\<Pi>\<^sub>E i\<in>I. S i) \<noteq> {}"
  and eq: "(\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. S i) \<subseteq> (\<lambda>x. restrict x J) -` B \<inter> (\<Pi>\<^sub>E i\<in>I. S i)"
  shows "A \<subseteq> B"
proof  (intro subsetI)
  fix x assume "x \<in> A"
  from ne obtain y where y: "\<And>i. i \<in> I \<Longrightarrow> y i \<in> S i" by auto
  have "J \<inter> (I - J) = {}" by auto
  show "x \<in> B"
  proof cases
    assume x: "x \<in> (\<Pi>\<^sub>E i\<in>J. S i)"
    have "merge J (I - J) (x,y) \<in> (\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. S i)"
      using y x \<open>J \<subseteq> I\<close> PiE_cancel_merge[of "J" "I - J" x y S] \<open>x\<in>A\<close>
      by (auto simp del: PiE_cancel_merge simp add: Un_absorb1)
    also have "\<dots> \<subseteq> (\<lambda>x. restrict x J) -` B \<inter> (\<Pi>\<^sub>E i\<in>I. S i)" by fact
    finally show "x \<in> B"
      using y x \<open>J \<subseteq> I\<close> PiE_cancel_merge[of "J" "I - J" x y S] \<open>x\<in>A\<close> eq
      by (auto simp del: PiE_cancel_merge simp add: Un_absorb1)
  qed (insert \<open>x\<in>A\<close> sets, auto)
qed

locale projective_family =
  fixes I :: "'i set" and P :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a) measure" and M :: "'i \<Rightarrow> 'a measure"
  assumes P: "\<And>J H. J \<subseteq> H \<Longrightarrow> finite H \<Longrightarrow> H \<subseteq> I \<Longrightarrow> P J = distr (P H) (PiM J M) (\<lambda>f. restrict f J)"
  assumes prob_space_P: "\<And>J. finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> prob_space (P J)"
begin

lemma sets_P: "finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> sets (P J) = sets (PiM J M)"
  by (subst P[of J J]) simp_all

lemma space_P: "finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> space (P J) = space (PiM J M)"
  using sets_P by (rule sets_eq_imp_space_eq)

lemma not_empty_M: "i \<in> I \<Longrightarrow> space (M i) \<noteq> {}"
  using prob_space_P[THEN prob_space.not_empty] by (auto simp: space_PiM space_P)

lemma not_empty: "space (PiM I M) \<noteq> {}"
  by (simp add: not_empty_M)

abbreviation
  "emb L K \<equiv> prod_emb L M K"

lemma emb_preserve_mono:
  assumes "J \<subseteq> L" "L \<subseteq> I" and sets: "X \<in> sets (Pi\<^sub>M J M)" "Y \<in> sets (Pi\<^sub>M J M)"
  assumes "emb L J X \<subseteq> emb L J Y"
  shows "X \<subseteq> Y"
proof (rule vimage_restrict_preserve_mono)
  show "X \<subseteq> (\<Pi>\<^sub>E i\<in>J. space (M i))" "Y \<subseteq> (\<Pi>\<^sub>E i\<in>J. space (M i))"
    using sets[THEN sets.sets_into_space] by (auto simp: space_PiM)
  show "(\<Pi>\<^sub>E i\<in>L. space (M i)) \<noteq> {}"
    using \<open>L \<subseteq> I\<close> by (auto simp add: not_empty_M space_PiM[symmetric])
  show "(\<lambda>x. restrict x J) -` X \<inter> (\<Pi>\<^sub>E i\<in>L. space (M i)) \<subseteq> (\<lambda>x. restrict x J) -` Y \<inter> (\<Pi>\<^sub>E i\<in>L. space (M i))"
    using \<open>prod_emb L M J X \<subseteq> prod_emb L M J Y\<close> by (simp add: prod_emb_def)
qed fact

lemma emb_injective:
  assumes L: "J \<subseteq> L" "L \<subseteq> I" and X: "X \<in> sets (Pi\<^sub>M J M)" and Y: "Y \<in> sets (Pi\<^sub>M J M)"
  shows "emb L J X = emb L J Y \<Longrightarrow> X = Y"
  by (intro antisym emb_preserve_mono[OF L X Y] emb_preserve_mono[OF L Y X]) auto

lemma emeasure_P: "J \<subseteq> K \<Longrightarrow> finite K \<Longrightarrow> K \<subseteq> I \<Longrightarrow> X \<in> sets (PiM J M) \<Longrightarrow> P K (emb K J X) = P J X"
  by (auto intro!: emeasure_distr_restrict[symmetric] simp: P sets_P)

inductive_set generator :: "('i \<Rightarrow> 'a) set set" where
  "finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^sub>M J M) \<Longrightarrow> emb I J X \<in> generator"

lemma algebra_generator: "algebra (space (PiM I M)) generator"
  unfolding algebra_iff_Int
proof (safe elim!: generator.cases)
  fix J X assume J: "finite J" "J \<subseteq> I" and X: "X \<in> sets (PiM J M)"

  from X[THEN sets.sets_into_space] J show "x \<in> emb I J X \<Longrightarrow> x \<in> space (PiM I M)" for x
    by (auto simp: prod_emb_def space_PiM)

  have "emb I J (space (PiM J M) - X) \<in> generator"
    by (intro generator.intros J sets.Diff sets.top X)
  with J show "space (Pi\<^sub>M I M) - emb I J X \<in> generator"
    by (simp add: space_PiM prod_emb_PiE)

  fix K Y assume K: "finite K" "K \<subseteq> I" and Y: "Y \<in> sets (PiM K M)"
  have "emb I (J \<union> K) (emb (J \<union> K) J X) \<inter> emb I (J \<union> K) (emb (J \<union> K) K Y) \<in> generator"
    unfolding prod_emb_Int[symmetric]
    by (intro generator.intros sets.Int measurable_prod_emb) (auto intro!: J K X Y)
  with J K X Y show "emb I J X \<inter> emb I K Y \<in> generator"
    by simp
qed (force simp: generator.simps prod_emb_empty[symmetric])

interpretation generator: algebra "space (PiM I M)" generator
  by (rule algebra_generator)

lemma sets_PiM_generator: "sets (PiM I M) = sigma_sets (space (PiM I M)) generator"
proof (intro antisym sets.sigma_sets_subset)
  show "sets (PiM I M) \<subseteq> sigma_sets (space (PiM I M)) generator"
    unfolding sets_PiM_single space_PiM[symmetric]
  proof (intro sigma_sets_mono', safe)
    fix i A assume "i \<in> I" and A: "A \<in> sets (M i)"
    then have "{f \<in> space (Pi\<^sub>M I M). f i \<in> A} = emb I {i} (\<Pi>\<^sub>E j\<in>{i}. A)"
      by (auto simp: prod_emb_def space_PiM restrict_def Pi_iff PiE_iff extensional_def)
    with \<open>i\<in>I\<close> A show "{f \<in> space (Pi\<^sub>M I M). f i \<in> A} \<in> generator"
      by (auto intro!: generator.intros sets_PiM_I_finite)
  qed
qed (auto elim!: generator.cases)

definition mu_G (\<open>\<mu>G\<close>) where
  "\<mu>G A = (THE x. \<forall>J\<subseteq>I. finite J \<longrightarrow> (\<forall>X\<in>sets (Pi\<^sub>M J M). A = emb I J X \<longrightarrow> x = emeasure (P J) X))"

definition lim :: "('i \<Rightarrow> 'a) measure" where
  "lim = extend_measure (space (PiM I M)) generator (\<lambda>x. x) \<mu>G"

lemma space_lim[simp]: "space lim = space (PiM I M)"
  using generator.space_closed
  unfolding lim_def by (intro space_extend_measure) simp

lemma sets_lim[simp, measurable]: "sets lim = sets (PiM I M)"
  using generator.space_closed by (simp add: lim_def sets_PiM_generator sets_extend_measure)

lemma mu_G_spec:
  assumes J: "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^sub>M J M)"
  shows "\<mu>G (emb I J X) = emeasure (P J) X"
  unfolding mu_G_def
proof (intro the_equality allI impI ballI)
  fix K Y assume K: "finite K" "K \<subseteq> I" "Y \<in> sets (Pi\<^sub>M K M)"
    and [simp]: "emb I J X = emb I K Y"
  have "emeasure (P K) Y = emeasure (P (K \<union> J)) (emb (K \<union> J) K Y)"
    using K J by (simp add: emeasure_P)
  also have "emb (K \<union> J) K Y = emb (K \<union> J) J X"
    using K J by (simp add: emb_injective[of "K \<union> J" I])
  also have "emeasure (P (K \<union> J)) (emb (K \<union> J) J X) = emeasure (P J) X"
    using K J by (subst emeasure_P) simp_all
  finally show "emeasure (P J) X = emeasure (P K) Y" ..
qed (insert J, force)

lemma positive_mu_G: "positive generator \<mu>G"
proof -
  show ?thesis
  proof (safe intro!: positive_def[THEN iffD2])
    obtain J where "finite J" "J \<subseteq> I" by auto
    then have "\<mu>G (emb I J {}) = 0"
      by (subst mu_G_spec) auto
    then show "\<mu>G {} = 0" by simp
  qed
qed

lemma additive_mu_G: "additive generator \<mu>G"
proof (safe intro!: additive_def[THEN iffD2] elim!: generator.cases)
  fix J X K Y assume J: "finite J" "J \<subseteq> I" "X \<in> sets (PiM J M)"
    and K: "finite K" "K \<subseteq> I" "Y \<in> sets (PiM K M)"
    and "emb I J X \<inter> emb I K Y = {}"
  then have JK_disj: "emb (J \<union> K) J X \<inter> emb (J \<union> K) K Y = {}"
    by (intro emb_injective[of "J \<union> K" I _ "{}"]) (auto simp: sets.Int prod_emb_Int)
  have "\<mu>G (emb I J X \<union> emb I K Y) = \<mu>G (emb I (J \<union> K) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y))"
    using J K by simp
  also have "\<dots> = emeasure (P (J \<union> K)) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y)"
    using J K by (simp add: mu_G_spec sets.Un del: prod_emb_Un)
  also have "\<dots> = \<mu>G (emb I J X) + \<mu>G (emb I K Y)"
    using J K JK_disj by (simp add: plus_emeasure[symmetric] mu_G_spec emeasure_P sets_P)
  finally show "\<mu>G (emb I J X \<union> emb I K Y) = \<mu>G (emb I J X) + \<mu>G (emb I K Y)" .
qed

lemma emeasure_lim:
  assumes JX: "finite J" "J \<subseteq> I" "X \<in> sets (PiM J M)"
  assumes cont: "\<And>J X. (\<And>i. J i \<subseteq> I) \<Longrightarrow> incseq J \<Longrightarrow> (\<And>i. finite (J i)) \<Longrightarrow> (\<And>i. X i \<in> sets (PiM (J i) M)) \<Longrightarrow>
    decseq (\<lambda>i. emb I (J i) (X i)) \<Longrightarrow> 0 < (INF i. P (J i) (X i)) \<Longrightarrow> (\<Inter>i. emb I (J i) (X i)) \<noteq> {}"
  shows "emeasure lim (emb I J X) = P J X"
proof -
  have "\<exists>\<mu>. (\<forall>s\<in>generator. \<mu> s = \<mu>G s) \<and>
    measure_space (space (PiM I M)) (sigma_sets (space (PiM I M)) generator) \<mu>"
  proof (rule generator.caratheodory_empty_continuous[OF positive_mu_G additive_mu_G])
    show "\<And>A. A \<in> generator \<Longrightarrow> \<mu>G A \<noteq> \<infinity>"
    proof (clarsimp elim!: generator.cases simp: mu_G_spec del: notI)
      fix J assume "finite J" "J \<subseteq> I"
      then interpret prob_space "P J" by (rule prob_space_P)
      show "\<And>X. X \<in> sets (Pi\<^sub>M J M) \<Longrightarrow> emeasure (P J) X \<noteq> top"
        by simp
    qed
  next
    fix A assume "range A \<subseteq> generator" and "decseq A" "(\<Inter>i. A i) = {}"
    then have "\<forall>i. \<exists>J X. A i = emb I J X \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (PiM J M)"
      unfolding image_subset_iff generator.simps by blast
    then obtain J X where A: "\<And>i. A i = emb I (J i) (X i)"
      and *: "\<And>i. finite (J i)" "\<And>i. J i \<subseteq> I" "\<And>i. X i \<in> sets (PiM (J i) M)"
      by metis
    have "(INF i. P (J i) (X i)) = 0"
    proof (rule ccontr)
      assume INF_P: "(INF i. P (J i) (X i)) \<noteq> 0"
      have "(\<Inter>i. emb I (\<Union>n\<le>i. J n) (emb (\<Union>n\<le>i. J n) (J i) (X i))) \<noteq> {}"
      proof (rule cont)
        show "decseq (\<lambda>i. emb I (\<Union>n\<le>i. J n) (emb (\<Union>n\<le>i. J n) (J i) (X i)))"
          using * \<open>decseq A\<close> by (subst prod_emb_trans) (auto simp: A[abs_def])
        show "0 < (INF i. P (\<Union>n\<le>i. J n) (emb (\<Union>n\<le>i. J n) (J i) (X i)))"
           using * INF_P by (subst emeasure_P) (auto simp: less_le intro!: INF_greatest)
        show "incseq (\<lambda>i. \<Union>n\<le>i. J n)"
          by (force simp: incseq_def)
      qed (insert *, auto)
      with \<open>(\<Inter>i. A i) = {}\<close> * show False
        by (subst (asm) prod_emb_trans) (auto simp: A[abs_def])
    qed
    moreover have "(\<lambda>i. P (J i) (X i)) \<longlonglongrightarrow> (INF i. P (J i) (X i))"
    proof (intro LIMSEQ_INF antimonoI)
      fix x y :: nat assume "x \<le> y"
      have "P (J y \<union> J x) (emb (J y \<union> J x) (J y) (X y)) \<le> P (J y \<union> J x) (emb (J y \<union> J x) (J x) (X x))"
        using \<open>decseq A\<close>[THEN decseqD, OF \<open>x\<le>y\<close>] *
        by (auto simp: A sets_P del: subsetI intro!: emeasure_mono  \<open>x \<le> y\<close>
              emb_preserve_mono[of "J y \<union> J x" I, where X="emb (J y \<union> J x) (J y) (X y)"])
      then show "P (J y) (X y) \<le> P (J x) (X x)"
        using * by (simp add: emeasure_P)
    qed
    ultimately show "(\<lambda>i. \<mu>G (A i)) \<longlonglongrightarrow> 0"
      by (auto simp: A[abs_def] mu_G_spec *)
  qed
  then obtain \<mu> where eq: "\<forall>s\<in>generator. \<mu> s = \<mu>G s"
    and ms: "measure_space (space (PiM I M)) (sets (PiM I M)) \<mu>"
    by (metis sets_PiM_generator)
  show ?thesis
  proof (subst emeasure_extend_measure[OF lim_def])
    show "A \<in> generator \<Longrightarrow> \<mu> A = \<mu>G A" for A
      using eq by simp
    show "positive (sets lim) \<mu>" "countably_additive (sets lim) \<mu>"
      using ms by (auto simp add: measure_space_def)
    show "(\<lambda>x. x) ` generator \<subseteq> Pow (space (Pi\<^sub>M I M))"
      using generator.space_closed by simp
    show "emb I J X \<in> generator" "\<mu>G (emb I J X) = emeasure (P J) X"
      using JX by (auto intro: generator.intros simp: mu_G_spec)
  qed
qed

end

sublocale product_prob_space \<subseteq> projective_family I "\<lambda>J. PiM J M" M
  unfolding projective_family_def
proof (intro conjI allI impI distr_restrict)
  show "\<And>J. finite J \<Longrightarrow> prob_space (Pi\<^sub>M J M)"
    by (intro prob_spaceI) (simp add: space_PiM emeasure_PiM emeasure_space_1)
qed auto


txt \<open> Proof due to Ionescu Tulcea. \<close>

locale Ionescu_Tulcea =
  fixes P :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a measure" and M :: "nat \<Rightarrow> 'a measure"
  assumes P[measurable]: "\<And>i. P i \<in> measurable (PiM {0..<i} M) (subprob_algebra (M i))"
  assumes prob_space_P: "\<And>i x. x \<in> space (PiM {0..<i} M) \<Longrightarrow> prob_space (P i x)"
begin

lemma non_empty[simp]: "space (M i) \<noteq> {}"
proof (induction i rule: less_induct)
  case (less i)
  then obtain x where "\<And>j. j < i \<Longrightarrow> x j \<in> space (M j)"
    unfolding ex_in_conv[symmetric] by metis
  then have *: "restrict x {0..<i} \<in> space (PiM {0..<i} M)"
    by (auto simp: space_PiM PiE_iff)
  then interpret prob_space "P i (restrict x {0..<i})"
    by (rule prob_space_P)
  show ?case
    using not_empty subprob_measurableD(1)[OF P, OF *] by simp
qed

lemma space_PiM_not_empty[simp]: "space (PiM UNIV M) \<noteq> {}"
  unfolding space_PiM_empty_iff by auto

lemma space_P: "x \<in> space (PiM {0..<n} M) \<Longrightarrow> space (P n x) = space (M n)"
  by (simp add: P[THEN subprob_measurableD(1)])

lemma sets_P[measurable_cong]: "x \<in> space (PiM {0..<n} M) \<Longrightarrow> sets (P n x) = sets (M n)"
  by (simp add: P[THEN subprob_measurableD(2)])

definition eP :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) measure" where
  "eP n \<omega> = distr (P n \<omega>) (PiM {0..<Suc n} M) (fun_upd \<omega> n)"

lemma measurable_eP[measurable]:
  "eP n \<in> measurable (PiM {0..< n} M) (subprob_algebra (PiM {0..<Suc n} M))"
  by (auto simp: eP_def[abs_def] measurable_split_conv
           intro!: measurable_fun_upd[where J="{0..<n}"] measurable_distr2[OF _ P])

lemma space_eP:
  "x \<in> space (PiM {0..<n} M) \<Longrightarrow> space (eP n x) = space (PiM {0..<Suc n} M)"
  by (simp add: eP_def)

lemma sets_eP[measurable]:
  "x \<in> space (PiM {0..<n} M) \<Longrightarrow> sets (eP n x) = sets (PiM {0..<Suc n} M)"
  by (simp add: eP_def)

lemma prob_space_eP: "x \<in> space (PiM {0..<n} M) \<Longrightarrow> prob_space (eP n x)"
  unfolding eP_def
  by (intro prob_space.prob_space_distr prob_space_P measurable_fun_upd[where J="{0..<n}"]) auto

lemma nn_integral_eP:
  "\<omega> \<in> space (PiM {0..<n} M) \<Longrightarrow> f \<in> borel_measurable (PiM {0..<Suc n} M) \<Longrightarrow>
    (\<integral>\<^sup>+x. f x \<partial>eP n \<omega>) = (\<integral>\<^sup>+x. f (fun_upd \<omega> n x) \<partial>P n \<omega>)"
  unfolding eP_def
  by (subst nn_integral_distr) (auto intro!: measurable_fun_upd[where J="{0..<n}"] simp: space_PiM PiE_iff)

lemma emeasure_eP:
  assumes \<omega>[simp]: "\<omega> \<in> space (PiM {0..<n} M)" and A[measurable]: "A \<in> sets (PiM {0..<Suc n} M)"
  shows "eP n \<omega> A = P n \<omega> ((\<lambda>x. fun_upd \<omega> n x) -` A \<inter> space (M n))"
  using nn_integral_eP[of \<omega> n "indicator A"]
  apply (simp add: sets_eP nn_integral_indicator[symmetric] sets_P del: nn_integral_indicator)
  apply (subst nn_integral_indicator[symmetric])
  using measurable_sets[OF measurable_fun_upd[OF _ measurable_const[OF \<omega>] measurable_id] A, of n]
  apply (auto simp add: sets_P atLeastLessThanSuc space_P simp del: nn_integral_indicator
     intro!: nn_integral_cong split: split_indicator)
  done


primrec C :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) measure" where
  "C n 0 \<omega> = return (PiM {0..<n} M) \<omega>"
| "C n (Suc m) \<omega> = C n m \<omega> \<bind> eP (n + m)"

lemma measurable_C[measurable]:
  "C n m \<in> measurable (PiM {0..<n} M) (subprob_algebra (PiM {0..<n + m} M))"
  by (induction m) auto

lemma space_C:
  "x \<in> space (PiM {0..<n} M) \<Longrightarrow> space (C n m x) = space (PiM {0..<n + m} M)"
  by (simp add: measurable_C[THEN subprob_measurableD(1)])

lemma sets_C[measurable_cong]:
  "x \<in> space (PiM {0..<n} M) \<Longrightarrow> sets (C n m x) = sets (PiM {0..<n + m} M)"
  by (simp add: measurable_C[THEN subprob_measurableD(2)])

lemma prob_space_C: "x \<in> space (PiM {0..<n} M) \<Longrightarrow> prob_space (C n m x)"
proof (induction m)
  case (Suc m) then show ?case
    by (auto intro!: prob_space.prob_space_bind[where S="PiM {0..<Suc (n + m)} M"]
             simp: space_C prob_space_eP)
qed (auto intro!: prob_space_return simp: space_PiM)

lemma split_C:
  assumes \<omega>: "\<omega> \<in> space (PiM {0..<n} M)" shows "(C n m \<omega> \<bind> C (n + m) l) = C n (m + l) \<omega>"
proof (induction l)
  case 0
  with \<omega> show ?case
    by (simp add: bind_return_distr' prob_space_C[THEN prob_space.not_empty]
                  distr_cong[OF refl sets_C[symmetric, OF \<omega>]])
next
  case (Suc l) with \<omega> show ?case
    by (simp add: bind_assoc[symmetric, OF _ measurable_eP]) (simp add: ac_simps)
qed

lemma nn_integral_C:
  assumes "m \<le> m'" and f[measurable]: "f \<in> borel_measurable (PiM {0..<n+m} M)"
    and nonneg: "\<And>x. x \<in> space (PiM {0..<n+m} M) \<Longrightarrow> 0 \<le> f x"
    and x: "x \<in> space (PiM {0..<n} M)"
  shows "(\<integral>\<^sup>+x. f x \<partial>C n m x) = (\<integral>\<^sup>+x. f (restrict x {0..<n+m}) \<partial>C n m' x)"
  using \<open>m \<le> m'\<close>
proof (induction rule: dec_induct)
  case (step i)
  let ?E = "\<lambda>x. f (restrict x {0..<n + m})" and ?C = "\<lambda>i f. \<integral>\<^sup>+x. f x \<partial>C n i x"
  from \<open>m\<le>i\<close> x have "?C i ?E = ?C (Suc i) ?E"
    by (auto simp: nn_integral_bind[where B="PiM {0 ..< Suc (n + i)} M"] space_C nn_integral_eP
             intro!: nn_integral_cong)
       (simp add: space_PiM PiE_iff  nonneg prob_space.emeasure_space_1[OF prob_space_P])
  with step show ?case by (simp del: restrict_apply)
qed (auto simp: space_PiM space_C[OF x] simp del: restrict_apply intro!: nn_integral_cong)

lemma emeasure_C:
  assumes "m \<le> m'" and A[measurable]: "A \<in> sets (PiM {0..<n+m} M)" and [simp]: "x \<in> space (PiM {0..<n} M)"
  shows "emeasure (C n m' x) (prod_emb {0..<n + m'} M {0..<n+m} A) = emeasure (C n m x) A"
  using assms
  by (subst (1 2) nn_integral_indicator[symmetric])
     (auto intro!: nn_integral_cong split: split_indicator simp del: nn_integral_indicator
           simp: nn_integral_C[of m m' _ n] prod_emb_iff space_PiM PiE_iff sets_C space_C)

lemma distr_C:
  assumes "m \<le> m'" and [simp]: "x \<in> space (PiM {0..<n} M)"
  shows "C n m x = distr (C n m' x) (PiM {0..<n+m} M) (\<lambda>x. restrict x {0..<n+m})"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (C n m x)"
  with \<open>m \<le> m'\<close> show "emeasure (C n m x) A = emeasure (distr (C n m' x) (Pi\<^sub>M {0..<n + m} M) (\<lambda>x. restrict x {0..<n + m})) A"
    by (subst emeasure_C[symmetric, OF \<open>m \<le> m'\<close>]) (auto intro!: emeasure_distr_restrict[symmetric] simp: sets_C)
qed (simp add: sets_C)

definition up_to :: "nat set \<Rightarrow> nat" where
  "up_to J = (LEAST n. \<forall>i\<ge>n. i \<notin> J)"

lemma up_to_less: "finite J \<Longrightarrow> i \<in> J \<Longrightarrow> i < up_to J"
  unfolding up_to_def
  by (rule LeastI2[of _ "Suc (Max J)"]) (auto simp: Suc_le_eq not_le[symmetric])

lemma up_to_iff: "finite J \<Longrightarrow> up_to J \<le> n \<longleftrightarrow> (\<forall>i\<in>J. i < n)"
proof safe
  show "finite J \<Longrightarrow> up_to J \<le> n \<Longrightarrow> i \<in> J \<Longrightarrow> i < n" for i
    using up_to_less[of J i] by auto
qed (auto simp: up_to_def intro!: Least_le)

lemma up_to_iff_Ico: "finite J \<Longrightarrow> up_to J \<le> n \<longleftrightarrow> J \<subseteq> {0..<n}"
  by (auto simp: up_to_iff)

lemma up_to: "finite J \<Longrightarrow> J \<subseteq> {0..< up_to J}"
  by (auto simp: up_to_less)

lemma up_to_mono: "J \<subseteq> H \<Longrightarrow> finite H \<Longrightarrow> up_to J \<le> up_to H"
  by (auto simp add: up_to_iff finite_subset up_to_less)

definition CI :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a) measure" where
  "CI J = distr (C 0 (up_to J) (\<lambda>x. undefined)) (PiM J M) (\<lambda>f. restrict f J)"

sublocale PF: projective_family UNIV CI
  unfolding projective_family_def
proof safe
  show "finite J \<Longrightarrow> prob_space (CI J)" for J
    using up_to[of J] unfolding CI_def
    by (intro prob_space.prob_space_distr prob_space_C measurable_restrict) auto
  note measurable_cong_sets[OF sets_C, simp]
  have [simp]: "J \<subseteq> H \<Longrightarrow> (\<lambda>f. restrict f J) \<in> measurable (Pi\<^sub>M H M) (Pi\<^sub>M J M)" for H J
    by (auto intro!: measurable_restrict)

  show "J \<subseteq> H \<Longrightarrow> finite H \<Longrightarrow> CI J = distr (CI H) (Pi\<^sub>M J M) (\<lambda>f. restrict f J)" for J H
    by (simp add: CI_def distr_C[OF up_to_mono[of J H]] up_to up_to_mono distr_distr comp_def
                  inf.absorb2 finite_subset)
qed

lemma emeasure_CI':
  "finite J \<Longrightarrow> X \<in> sets (PiM J M) \<Longrightarrow> CI J X = C 0 (up_to J) (\<lambda>_. undefined) (PF.emb {0..<up_to J} J X)"
  unfolding CI_def using up_to[of J] by (rule emeasure_distr_restrict) (auto simp: sets_C)

lemma emeasure_CI:
  "J \<subseteq> {0..<n} \<Longrightarrow> X \<in> sets (PiM J M) \<Longrightarrow> CI J X = C 0 n (\<lambda>_. undefined) (PF.emb {0..<n} J X)"
  apply (subst emeasure_CI', simp_all add: finite_subset)
  apply (subst emeasure_C[symmetric, of "up_to J" n])
  apply (auto simp: finite_subset up_to_iff_Ico up_to_less)
  apply (subst prod_emb_trans)
  apply (auto simp: up_to_less finite_subset up_to_iff_Ico)
  done

lemma lim:
  assumes J: "finite J" and X: "X \<in> sets (PiM J M)"
  shows "emeasure PF.lim (PF.emb UNIV J X) = emeasure (CI J) X"
proof (rule PF.emeasure_lim[OF J subset_UNIV X])
  fix J X' assume J[simp]: "\<And>i. finite (J i)" and X'[measurable]: "\<And>i. X' i \<in> sets (Pi\<^sub>M (J i) M)"
    and dec: "decseq (\<lambda>i. PF.emb UNIV (J i) (X' i))"
  define X where "X n =
    (\<Inter>i\<in>{i. J i \<subseteq> {0..< n}}. PF.emb {0..<n} (J i) (X' i)) \<inter> space (PiM {0..<n} M)" for n

  have sets_X[measurable]: "X n \<in> sets (PiM {0..<n} M)" for n
    by (cases "{i. J i \<subseteq> {0..< n}} = {}")
       (simp_all add: X_def, auto intro!: sets.countable_INT' sets.Int)

  have dec_X: "n \<le> m \<Longrightarrow> X m \<subseteq> PF.emb {0..<m} {0..<n} (X n)" for n m
    unfolding X_def using ivl_subset[of 0 n 0 m]
    by (cases "{i. J i \<subseteq> {0..< n}} = {}")
       (auto simp add: prod_emb_Int prod_emb_PiE space_PiM simp del: ivl_subset)

  have dec_X': "PF.emb {0..<n} (J j) (X' j) \<subseteq> PF.emb {0..<n} (J i) (X' i)"
    if [simp]: "J i \<subseteq> {0..<n}" "J j \<subseteq> {0..<n}" "i \<le> j" for n i j
    by (rule PF.emb_preserve_mono[of "{0..<n}" UNIV]) (auto del: subsetI intro: dec[THEN antimonoD])

  assume "0 < (INF i. CI (J i) (X' i))"
  also have "\<dots> \<le> (INF i. C 0 i (\<lambda>x. undefined) (X i))"
  proof (intro INF_greatest)
    fix n
    interpret C: prob_space "C 0 n (\<lambda>x. undefined)"
      by (rule prob_space_C) simp
    show "(INF i. CI (J i) (X' i)) \<le> C 0 n (\<lambda>x. undefined) (X n)"
    proof cases
      assume "{i. J i \<subseteq> {0..< n}} = {}" with C.emeasure_space_1  show ?thesis
        by (auto simp add: X_def space_C intro!: INF_lower2[of 0] prob_space.measure_le_1 PF.prob_space_P)
    next
      assume *: "{i. J i \<subseteq> {0..< n}} \<noteq> {}"
      have "(INF i. CI (J i) (X' i)) \<le>
          (INF i\<in>{i. J i \<subseteq> {0..<n}}. C 0 n (\<lambda>_. undefined) (PF.emb {0..<n} (J i) (X' i)))"
        by (intro INF_superset_mono) (auto simp: emeasure_CI)
      also have "\<dots> = C 0 n (\<lambda>_. undefined) (\<Inter>i\<in>{i. J i \<subseteq> {0..<n}}. (PF.emb {0..<n} (J i) (X' i)))"
        using * by (intro emeasure_INT_decseq_subset[symmetric]) (auto intro!: dec_X' del: subsetI simp: sets_C)
      also have "\<dots> = C 0 n (\<lambda>_. undefined) (X n)"
        using * by (auto simp add: X_def INT_extend_simps)
      finally show "(INF i. CI (J i) (X' i)) \<le> C 0 n (\<lambda>_. undefined) (X n)" .
    qed
  qed
  finally have pos: "0 < (INF i. C 0 i (\<lambda>x. undefined) (X i))" .
  from less_INF_D[OF this, of 0] have "X 0 \<noteq> {}"
    by auto

  { fix \<omega> n assume \<omega>: "\<omega> \<in> space (PiM {0..<n} M)"
    let ?C = "\<lambda>i. emeasure (C n i \<omega>) (X (n + i))"
    let ?C' = "\<lambda>i x. emeasure (C (Suc n) i (fun_upd \<omega> n x)) (X (Suc n + i))"
    have M: "\<And>i. ?C' i \<in> borel_measurable (P n \<omega>)"
      using \<omega>[measurable, simp] measurable_fun_upd[where J="{0..<n}"] by measurable auto

    assume "0 < (INF i. ?C i)"
    also have "\<dots> \<le> (INF i. emeasure (C n (1 + i) \<omega>) (X (n + (1 + i))))"
      by (intro INF_greatest INF_lower) auto
    also have "\<dots> = (INF i. \<integral>\<^sup>+x. ?C' i x \<partial>P n \<omega>)"
      using \<omega> measurable_C[of "Suc n"]
      apply (intro INF_cong refl)
      apply (subst split_C[symmetric, OF \<omega>])
      apply (subst emeasure_bind[OF _ _ sets_X])
      apply (simp_all del: C.simps add: space_C)
      apply measurable
      apply simp
      apply (simp add: bind_return[OF measurable_eP] nn_integral_eP)
      done
    also have "\<dots> = (\<integral>\<^sup>+x. (INF i. ?C' i x) \<partial>P n \<omega>)"
    proof (rule nn_integral_monotone_convergence_INF_AE[symmetric])
      have "(\<integral>\<^sup>+x. ?C' 0 x \<partial>P n \<omega>) \<le> (\<integral>\<^sup>+x. 1 \<partial>P n \<omega>)"
        by (intro nn_integral_mono) (auto split: split_indicator)
      also have "\<dots> < \<infinity>"
        using prob_space_P[OF \<omega>, THEN prob_space.emeasure_space_1] by simp
      finally show "(\<integral>\<^sup>+x. ?C' 0 x \<partial>P n \<omega>) < \<infinity>" .
    next
      show "AE x in P n \<omega>. ?C' (Suc i) x \<le> ?C' i x" for i
      proof (rule AE_I2)
        fix x assume "x \<in> space (P n \<omega>)"
        with \<omega> have \<omega>': "fun_upd \<omega> n x \<in> space (PiM {0..<Suc n} M)"
          by (auto simp: space_P[OF \<omega>] space_PiM PiE_iff extensional_def)
        with \<omega> show "?C' (Suc i) x \<le> ?C' i x"
          apply (subst emeasure_C[symmetric, of i "Suc i"])
          apply (auto intro!: emeasure_mono[OF dec_X] del: subsetI
                      simp: sets_C space_P)
          apply (subst sets_bind[OF sets_eP])
          apply (simp_all add: space_C space_P)
          done
      qed
    qed fact
    finally have "(\<integral>\<^sup>+x. (INF i. ?C' i x) \<partial>P n \<omega>) \<noteq> 0"
      by simp
    with M have "\<exists>\<^sub>F x in ae_filter (P n \<omega>). 0 < (INF i. ?C' i x)"
       by (subst (asm) nn_integral_0_iff_AE)
          (auto intro!: borel_measurable_INF simp: Filter.not_eventually not_le zero_less_iff_neq_zero)
    then have "\<exists>\<^sub>F x in ae_filter (P n \<omega>). x \<in> space (M n) \<and> 0 < (INF i. ?C' i x)"
      by (rule frequently_mp[rotated]) (auto simp: space_P \<omega>)
    then obtain x where "x \<in> space (M n)" "0 < (INF i. ?C' i x)"
      by (auto dest: frequently_ex)
    from this(2)[THEN less_INF_D, of 0] this(2)
    have "\<exists>x. fun_upd \<omega> n x \<in> X (Suc n) \<and> 0 < (INF i. ?C' i x)"
      by (intro exI[of _ x]) (simp split: split_indicator_asm) }
  note step = this

  let ?\<omega> = "\<lambda>\<omega> n x. (restrict \<omega> {0..<n})(n := x)"
  let ?L = "\<lambda>\<omega> n r. INF i. emeasure (C (Suc n) i (?\<omega> \<omega> n r)) (X (Suc n + i))"
  have *: "(\<And>i. i < n \<Longrightarrow> ?\<omega> \<omega> i (\<omega> i) \<in> X (Suc i)) \<Longrightarrow>
    restrict \<omega> {0..<n} \<in> space (Pi\<^sub>M {0..<n} M)" for \<omega> n
    using sets.sets_into_space[OF sets_X, of n]
    by (cases n) (auto simp: atLeastLessThanSuc restrict_def[of _ "{}"])
  have "\<exists>\<omega>. \<forall>n. ?\<omega> \<omega> n (\<omega> n) \<in> X (Suc n) \<and> 0 < ?L \<omega> n (\<omega> n)"
  proof (rule dependent_wellorder_choice)
    fix n \<omega> assume IH: "\<And>i. i < n \<Longrightarrow> ?\<omega> \<omega> i (\<omega> i) \<in> X (Suc i) \<and> 0 < ?L \<omega> i (\<omega> i)"
    show "\<exists>r. ?\<omega> \<omega> n r \<in> X (Suc n) \<and> 0 < ?L \<omega> n r"
    proof (rule step)
      show "restrict \<omega> {0..<n} \<in> space (Pi\<^sub>M {0..<n} M)"
        using IH[THEN conjunct1] by (rule *)
      show "0 < (INF i. emeasure (C n i (restrict \<omega> {0..<n})) (X (n + i)))"
      proof (cases n)
        case 0 with pos show ?thesis
          by (simp add: CI_def restrict_def)
      next
        case (Suc i) then show ?thesis
          using IH[of i, THEN conjunct2] by (simp add: atLeastLessThanSuc)
      qed
    qed
  qed (simp cong: restrict_cong)
  then obtain \<omega> where \<omega>: "\<And>n. ?\<omega> \<omega> n (\<omega> n) \<in> X (Suc n)"
    by auto
  from this[THEN *] have \<omega>_space: "\<omega> \<in> space (PiM UNIV M)"
    by (auto simp: space_PiM PiE_iff Ball_def)
  have *: "\<omega> \<in> PF.emb UNIV {0..<n} (X n)" for n
  proof (cases n)
    case 0 with \<omega>_space \<open>X 0 \<noteq> {}\<close> sets.sets_into_space[OF sets_X, of 0] show ?thesis
      by (auto simp add: space_PiM prod_emb_def restrict_def PiE_iff)
  next
    case (Suc i) then show ?thesis
      using \<omega>[of i] \<omega>_space by (auto simp: prod_emb_def space_PiM PiE_iff atLeastLessThanSuc)
  qed
  have **: "{i. J i \<subseteq> {0..<up_to (J n)}} \<noteq> {}" for n
    by (auto intro!: exI[of _ n] up_to J)
  have "\<omega> \<in> PF.emb UNIV (J n) (X' n)" for n
    using *[of "up_to (J n)"] up_to[of "J n"] by (simp add: X_def prod_emb_Int prod_emb_INT[OF **])
  then show "(\<Inter>i. PF.emb UNIV (J i) (X' i)) \<noteq> {}"
    by auto
qed

lemma distr_lim: assumes J[simp]: "finite J" shows "distr PF.lim (PiM J M) (\<lambda>x. restrict x J) = CI J"
  apply (rule measure_eqI)
  apply (simp add: CI_def)
  apply (simp add: emeasure_distr measurable_cong_sets[OF PF.sets_lim] lim[symmetric] prod_emb_def space_PiM)
  done

end

lemma (in product_prob_space) emeasure_lim_emb:
  assumes *: "finite J" "J \<subseteq> I" "X \<in> sets (PiM J M)"
  shows "emeasure lim (emb I J X) = emeasure (Pi\<^sub>M J M) X"
proof (rule emeasure_lim[OF *], goal_cases)
  case (1 J X)

  have "\<exists>Q. (\<forall>i. sets Q = PiM (\<Union>i. J i) M \<and> distr Q (PiM (J i) M) (\<lambda>x. restrict x (J i)) = Pi\<^sub>M (J i) M)"
  proof cases
    assume "finite (\<Union>i. J i)"
    then have "distr (PiM (\<Union>i. J i) M) (Pi\<^sub>M (J i) M) (\<lambda>x. restrict x (J i)) = Pi\<^sub>M (J i) M" for i
      by (intro distr_restrict[symmetric]) auto
    then show ?thesis
      by auto
  next
    assume inf: "infinite (\<Union>i. J i)"
    moreover have count: "countable (\<Union>i. J i)"
      using 1(3) by (auto intro: countable_finite)
    define f where "f = from_nat_into (\<Union>i. J i)"
    define t where "t = to_nat_on (\<Union>i. J i)"
    have ft[simp]: "x \<in> J i \<Longrightarrow> f (t x) = x" for x i
      unfolding f_def t_def using inf count by (intro from_nat_into_to_nat_on) auto
    have tf[simp]: "t (f i) = i" for i
      unfolding t_def f_def by (intro to_nat_on_from_nat_into_infinite inf count)
    have inj_t: "inj_on t (\<Union>i. J i)"
      using count by (auto simp: t_def)
    then have inj_t_J: "inj_on t (J i)" for i
      by (rule inj_on_subset) auto
    interpret IT: Ionescu_Tulcea "\<lambda>i \<omega>. M (f i)" "\<lambda>i. M (f i)"
      by standard auto
    interpret Mf: product_prob_space "\<lambda>x. M (f x)" UNIV
      by standard
    have C_eq_PiM: "IT.C 0 n (\<lambda>_. undefined) = PiM {0..<n} (\<lambda>x. M (f x))" for n
    proof (induction n)
      case 0 then show ?case
        by (auto simp: PiM_empty intro!: measure_eqI dest!: subset_singletonD)
    next
      case (Suc n) then show ?case
        apply (auto intro!: measure_eqI simp: sets_bind[OF IT.sets_eP] emeasure_bind[OF _ IT.measurable_eP])
        apply (auto simp: Mf.product_nn_integral_insert nn_integral_indicator[symmetric] atLeastLessThanSuc IT.emeasure_eP space_PiM
                    split: split_indicator simp del: nn_integral_indicator intro!: nn_integral_cong)
        done
    qed
    have CI_eq_PiM: "IT.CI X = PiM X (\<lambda>x. M (f x))" if X: "finite X" for X
      by (auto simp: IT.up_to_less X  IT.CI_def C_eq_PiM intro!: Mf.distr_restrict[symmetric])

    let ?Q = "distr IT.PF.lim (PiM (\<Union>i. J i) M) (\<lambda>\<omega>. \<lambda>x\<in>\<Union>i. J i. \<omega> (t x))"
    { fix i
      have "distr ?Q (Pi\<^sub>M (J i) M) (\<lambda>x. restrict x (J i)) =
        distr IT.PF.lim (Pi\<^sub>M (J i) M) ((\<lambda>\<omega>. \<lambda>n\<in>J i. \<omega> (t n)) \<circ> (\<lambda>\<omega>. restrict \<omega> (t`J i)))"
      proof (subst distr_distr)
        have "(\<lambda>\<omega>. \<omega> (t x)) \<in> measurable (Pi\<^sub>M UNIV (\<lambda>x. M (f x))) (M x)" if x: "x \<in> J i" for x i
          using measurable_component_singleton[of "t x" "UNIV" "\<lambda>x. M (f x)"] unfolding ft[OF x] by simp
        then show "(\<lambda>\<omega>. \<lambda>x\<in>\<Union>i. J i. \<omega> (t x)) \<in> measurable IT.PF.lim (Pi\<^sub>M (\<Union>(J ` UNIV)) M)"
          by (auto intro!: measurable_restrict simp: measurable_cong_sets[OF IT.PF.sets_lim refl])
      qed (auto intro!: distr_cong measurable_restrict measurable_component_singleton)
      also have "\<dots> = distr (distr IT.PF.lim (PiM (t`J i) (\<lambda>x. M (f x))) (\<lambda>\<omega>. restrict \<omega> (t`J i))) (Pi\<^sub>M (J i) M) (\<lambda>\<omega>. \<lambda>n\<in>J i. \<omega> (t n))"
      proof (intro distr_distr[symmetric])
        have "(\<lambda>\<omega>. \<omega> (t x)) \<in> measurable (Pi\<^sub>M (t`J i) (\<lambda>x. M (f x))) (M x)" if x: "x \<in> J i" for x
          using measurable_component_singleton[of "t x" "t`J i" "\<lambda>x. M (f x)"] x unfolding ft[OF x] by auto
        then show "(\<lambda>\<omega>. \<lambda>n\<in>J i. \<omega> (t n)) \<in> measurable (Pi\<^sub>M (t ` J i) (\<lambda>x. M (f x))) (Pi\<^sub>M (J i) M)"
          by (auto intro!: measurable_restrict)
      qed (auto intro!: measurable_restrict simp: measurable_cong_sets[OF IT.PF.sets_lim refl])
      also have "\<dots> = distr (PiM (t`J i) (\<lambda>x. M (f x))) (Pi\<^sub>M (J i) M) (\<lambda>\<omega>. \<lambda>n\<in>J i. \<omega> (t n))"
        using \<open>finite (J i)\<close> by (subst IT.distr_lim) (auto simp: CI_eq_PiM)
      also have "\<dots> = Pi\<^sub>M (J i) M"
        using Mf.distr_reorder[of t "J i"] by (simp add: 1 inj_t_J cong: PiM_cong)
      finally have "distr ?Q (Pi\<^sub>M (J i) M) (\<lambda>x. restrict x (J i)) = Pi\<^sub>M (J i) M" . }
    then show "\<exists>Q. \<forall>i. sets Q = PiM (\<Union>i. J i) M \<and> distr Q (Pi\<^sub>M (J i) M) (\<lambda>x. restrict x (J i)) = Pi\<^sub>M (J i) M"
      by (intro exI[of _ ?Q]) auto
  qed
  then obtain Q where sets_Q: "sets Q = PiM (\<Union>i. J i) M"
    and Q: "\<And>i. distr Q (PiM (J i) M) (\<lambda>x. restrict x (J i)) = Pi\<^sub>M (J i) M" by blast

  from 1 interpret Q: prob_space Q
    by (intro prob_space_distrD[of "\<lambda>x. restrict x (J 0)" Q "PiM (J 0) M"])
       (auto simp: Q measurable_cong_sets[OF sets_Q]
                intro!: prob_space_P measurable_restrict measurable_component_singleton)

  have "0 < (INF i. emeasure (Pi\<^sub>M (J i) M) (X i))" by fact
  also have "\<dots> = (INF i. emeasure Q (emb (\<Union>i. J i) (J i) (X i)))"
    by (simp add: emeasure_distr_restrict[OF _ sets_Q 1(4), symmetric] SUP_upper Q)
  also have "\<dots> = emeasure Q (\<Inter>i. emb (\<Union>i. J i) (J i) (X i))"
  proof (rule INF_emeasure_decseq)
    from 1 show "decseq (\<lambda>n. emb (\<Union>i. J i) (J n) (X n))"
      by (intro antimonoI emb_preserve_mono[where X="emb (\<Union>i. J i) (J n) (X n)" and L=I and J="\<Union>i. J i" for n]
         measurable_prod_emb)
         (auto simp: SUP_least SUP_upper antimono_def)
  qed (insert 1, auto simp: sets_Q)
  finally have "(\<Inter>i. emb (\<Union>i. J i) (J i) (X i)) \<noteq> {}"
    by auto
  moreover have "(\<Inter>i. emb I (J i) (X i)) = {} \<Longrightarrow> (\<Inter>i. emb (\<Union>i. J i) (J i) (X i)) = {}"
    using 1 by (intro emb_injective[of "\<Union>i. J i" I _ "{}"] sets.countable_INT) (auto simp: SUP_least SUP_upper)
  ultimately show ?case by auto
qed

end
