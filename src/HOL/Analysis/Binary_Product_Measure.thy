(*  Title:      HOL/Analysis/Binary_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

section \<open>Binary Product Measure\<close>

theory Binary_Product_Measure
imports Nonnegative_Lebesgue_Integration
begin

lemma Pair_vimage_times[simp]: "Pair x -` (A \<times> B) = (if x \<in> A then B else {})"
  by auto

lemma rev_Pair_vimage_times[simp]: "(\<lambda>x. (x, y)) -` (A \<times> B) = (if y \<in> B then A else {})"
  by auto

subsection "Binary products"

definition\<^marker>\<open>tag important\<close> pair_measure (infixr "\<Otimes>\<^sub>M" 80) where
  "A \<Otimes>\<^sub>M B = measure_of (space A \<times> space B)
      {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B}
      (\<lambda>X. \<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator X (x,y) \<partial>B) \<partial>A)"

lemma pair_measure_closed: "{a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B} \<subseteq> Pow (space A \<times> space B)"
  using sets.space_closed[of A] sets.space_closed[of B] by auto

lemma space_pair_measure:
  "space (A \<Otimes>\<^sub>M B) = space A \<times> space B"
  unfolding pair_measure_def using pair_measure_closed[of A B]
  by (rule space_measure_of)

lemma SIGMA_Collect_eq: "(SIGMA x:space M. {y\<in>space N. P x y}) = {x\<in>space (M \<Otimes>\<^sub>M N). P (fst x) (snd x)}"
  by (auto simp: space_pair_measure)

lemma sets_pair_measure:
  "sets (A \<Otimes>\<^sub>M B) = sigma_sets (space A \<times> space B) {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B}"
  unfolding pair_measure_def using pair_measure_closed[of A B]
  by (rule sets_measure_of)

lemma sets_pair_measure_cong[measurable_cong, cong]:
  "sets M1 = sets M1' \<Longrightarrow> sets M2 = sets M2' \<Longrightarrow> sets (M1 \<Otimes>\<^sub>M M2) = sets (M1' \<Otimes>\<^sub>M M2')"
  unfolding sets_pair_measure by (simp cong: sets_eq_imp_space_eq)

lemma pair_measureI[intro, simp, measurable]:
  "x \<in> sets A \<Longrightarrow> y \<in> sets B \<Longrightarrow> x \<times> y \<in> sets (A \<Otimes>\<^sub>M B)"
  by (auto simp: sets_pair_measure)

lemma sets_Pair: "{x} \<in> sets M1 \<Longrightarrow> {y} \<in> sets M2 \<Longrightarrow> {(x, y)} \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  using pair_measureI[of "{x}" M1 "{y}" M2] by simp

lemma measurable_pair_measureI:
  assumes 1: "f \<in> space M \<rightarrow> space M1 \<times> space M2"
  assumes 2: "\<And>A B. A \<in> sets M1 \<Longrightarrow> B \<in> sets M2 \<Longrightarrow> f -` (A \<times> B) \<inter> space M \<in> sets M"
  shows "f \<in> measurable M (M1 \<Otimes>\<^sub>M M2)"
  unfolding pair_measure_def using 1 2
  by (intro measurable_measure_of) (auto dest: sets.sets_into_space)

lemma measurable_split_replace[measurable (raw)]:
  "(\<lambda>x. f x (fst (g x)) (snd (g x))) \<in> measurable M N \<Longrightarrow> (\<lambda>x. case_prod (f x) (g x)) \<in> measurable M N"
  unfolding split_beta' .

lemma measurable_Pair[measurable (raw)]:
  assumes f: "f \<in> measurable M M1" and g: "g \<in> measurable M M2"
  shows "(\<lambda>x. (f x, g x)) \<in> measurable M (M1 \<Otimes>\<^sub>M M2)"
proof (rule measurable_pair_measureI)
  show "(\<lambda>x. (f x, g x)) \<in> space M \<rightarrow> space M1 \<times> space M2"
    using f g by (auto simp: measurable_def)
  fix A B assume *: "A \<in> sets M1" "B \<in> sets M2"
  have "(\<lambda>x. (f x, g x)) -` (A \<times> B) \<inter> space M = (f -` A \<inter> space M) \<inter> (g -` B \<inter> space M)"
    by auto
  also have "\<dots> \<in> sets M"
    by (rule sets.Int) (auto intro!: measurable_sets * f g)
  finally show "(\<lambda>x. (f x, g x)) -` (A \<times> B) \<inter> space M \<in> sets M" .
qed

lemma measurable_fst[intro!, simp, measurable]: "fst \<in> measurable (M1 \<Otimes>\<^sub>M M2) M1"
  by (auto simp: fst_vimage_eq_Times space_pair_measure sets.sets_into_space Times_Int_Times
    measurable_def)

lemma measurable_snd[intro!, simp, measurable]: "snd \<in> measurable (M1 \<Otimes>\<^sub>M M2) M2"
  by (auto simp: snd_vimage_eq_Times space_pair_measure sets.sets_into_space Times_Int_Times
    measurable_def)

lemma measurable_Pair_compose_split[measurable_dest]:
  assumes f: "case_prod f \<in> measurable (M1 \<Otimes>\<^sub>M M2) N"
  assumes g: "g \<in> measurable M M1" and h: "h \<in> measurable M M2"
  shows "(\<lambda>x. f (g x) (h x)) \<in> measurable M N"
  using measurable_compose[OF measurable_Pair f, OF g h] by simp

lemma measurable_Pair1_compose[measurable_dest]:
  assumes f: "(\<lambda>x. (f x, g x)) \<in> measurable M (M1 \<Otimes>\<^sub>M M2)"
  assumes [measurable]: "h \<in> measurable N M"
  shows "(\<lambda>x. f (h x)) \<in> measurable N M1"
  using measurable_compose[OF f measurable_fst] by simp

lemma measurable_Pair2_compose[measurable_dest]:
  assumes f: "(\<lambda>x. (f x, g x)) \<in> measurable M (M1 \<Otimes>\<^sub>M M2)"
  assumes [measurable]: "h \<in> measurable N M"
  shows "(\<lambda>x. g (h x)) \<in> measurable N M2"
  using measurable_compose[OF f measurable_snd] by simp

lemma measurable_pair:
  assumes "(fst \<circ> f) \<in> measurable M M1" "(snd \<circ> f) \<in> measurable M M2"
  shows "f \<in> measurable M (M1 \<Otimes>\<^sub>M M2)"
  using measurable_Pair[OF assms] by simp

lemma
  assumes f[measurable]: "f \<in> measurable M (N \<Otimes>\<^sub>M P)"
  shows measurable_fst': "(\<lambda>x. fst (f x)) \<in> measurable M N"
    and measurable_snd': "(\<lambda>x. snd (f x)) \<in> measurable M P"
  by simp_all

lemma
  assumes f[measurable]: "f \<in> measurable M N"
  shows measurable_fst'': "(\<lambda>x. f (fst x)) \<in> measurable (M \<Otimes>\<^sub>M P) N"
    and measurable_snd'': "(\<lambda>x. f (snd x)) \<in> measurable (P \<Otimes>\<^sub>M M) N"
  by simp_all

lemma sets_pair_in_sets:
  assumes "\<And>a b. a \<in> sets A \<Longrightarrow> b \<in> sets B \<Longrightarrow> a \<times> b \<in> sets N"
  shows "sets (A \<Otimes>\<^sub>M B) \<subseteq> sets N"
  unfolding sets_pair_measure
  by (intro sets.sigma_sets_subset') (auto intro!: assms)

lemma  sets_pair_eq_sets_fst_snd:
  "sets (A \<Otimes>\<^sub>M B) = sets (Sup {vimage_algebra (space A \<times> space B) fst A, vimage_algebra (space A \<times> space B) snd B})"
    (is "?P = sets (Sup {?fst, ?snd})")
proof -
  { fix a b assume ab: "a \<in> sets A" "b \<in> sets B"
    then have "a \<times> b = (fst -` a \<inter> (space A \<times> space B)) \<inter> (snd -` b \<inter> (space A \<times> space B))"
      by (auto dest: sets.sets_into_space)
    also have "\<dots> \<in> sets (Sup {?fst, ?snd})"
      apply (rule sets.Int)
      apply (rule in_sets_Sup)
      apply auto []
      apply (rule insertI1)
      apply (auto intro: ab in_vimage_algebra) []
      apply (rule in_sets_Sup)
      apply auto []
      apply (rule insertI2)
      apply (auto intro: ab in_vimage_algebra)
      done
    finally have "a \<times> b \<in> sets (Sup {?fst, ?snd})" . }
  moreover have "sets ?fst \<subseteq> sets (A \<Otimes>\<^sub>M B)"
    by (rule sets_image_in_sets) (auto simp: space_pair_measure[symmetric])
  moreover have "sets ?snd \<subseteq> sets (A \<Otimes>\<^sub>M B)"
    by (rule sets_image_in_sets) (auto simp: space_pair_measure)
  ultimately show ?thesis
    apply (intro antisym[of "sets A" for A] sets_Sup_in_sets sets_pair_in_sets)
    apply simp
    apply simp
    apply simp
    apply (elim disjE)
    apply (simp add: space_pair_measure)
    apply (simp add: space_pair_measure)
    apply (auto simp add: space_pair_measure)
    done
qed

lemma measurable_pair_iff:
  "f \<in> measurable M (M1 \<Otimes>\<^sub>M M2) \<longleftrightarrow> (fst \<circ> f) \<in> measurable M M1 \<and> (snd \<circ> f) \<in> measurable M M2"
  by (auto intro: measurable_pair[of f M M1 M2])

lemma  measurable_split_conv:
  "(\<lambda>(x, y). f x y) \<in> measurable A B \<longleftrightarrow> (\<lambda>x. f (fst x) (snd x)) \<in> measurable A B"
  by (intro arg_cong2[where f="(\<in>)"]) auto

lemma measurable_pair_swap': "(\<lambda>(x,y). (y, x)) \<in> measurable (M1 \<Otimes>\<^sub>M M2) (M2 \<Otimes>\<^sub>M M1)"
  by (auto intro!: measurable_Pair simp: measurable_split_conv)

lemma  measurable_pair_swap:
  assumes f: "f \<in> measurable (M1 \<Otimes>\<^sub>M M2) M" shows "(\<lambda>(x,y). f (y, x)) \<in> measurable (M2 \<Otimes>\<^sub>M M1) M"
  using measurable_comp[OF measurable_Pair f] by (auto simp: measurable_split_conv comp_def)

lemma measurable_pair_swap_iff:
  "f \<in> measurable (M2 \<Otimes>\<^sub>M M1) M \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) \<in> measurable (M1 \<Otimes>\<^sub>M M2) M"
  by (auto dest: measurable_pair_swap)

lemma measurable_Pair1': "x \<in> space M1 \<Longrightarrow> Pair x \<in> measurable M2 (M1 \<Otimes>\<^sub>M M2)"
  by simp

lemma sets_Pair1[measurable (raw)]:
  assumes A: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)" shows "Pair x -` A \<in> sets M2"
proof -
  have "Pair x -` A = (if x \<in> space M1 then Pair x -` A \<inter> space M2 else {})"
    using A[THEN sets.sets_into_space] by (auto simp: space_pair_measure)
  also have "\<dots> \<in> sets M2"
    using A by (auto simp add: measurable_Pair1' intro!: measurable_sets split: if_split_asm)
  finally show ?thesis .
qed

lemma measurable_Pair2': "y \<in> space M2 \<Longrightarrow> (\<lambda>x. (x, y)) \<in> measurable M1 (M1 \<Otimes>\<^sub>M M2)"
  by (auto intro!: measurable_Pair)

lemma sets_Pair2: assumes A: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)" shows "(\<lambda>x. (x, y)) -` A \<in> sets M1"
proof -
  have "(\<lambda>x. (x, y)) -` A = (if y \<in> space M2 then (\<lambda>x. (x, y)) -` A \<inter> space M1 else {})"
    using A[THEN sets.sets_into_space] by (auto simp: space_pair_measure)
  also have "\<dots> \<in> sets M1"
    using A by (auto simp add: measurable_Pair2' intro!: measurable_sets split: if_split_asm)
  finally show ?thesis .
qed

lemma measurable_Pair2:
  assumes f: "f \<in> measurable (M1 \<Otimes>\<^sub>M M2) M" and x: "x \<in> space M1"
  shows "(\<lambda>y. f (x, y)) \<in> measurable M2 M"
  using measurable_comp[OF measurable_Pair1' f, OF x]
  by (simp add: comp_def)

lemma measurable_Pair1:
  assumes f: "f \<in> measurable (M1 \<Otimes>\<^sub>M M2) M" and y: "y \<in> space M2"
  shows "(\<lambda>x. f (x, y)) \<in> measurable M1 M"
  using measurable_comp[OF measurable_Pair2' f, OF y]
  by (simp add: comp_def)

lemma Int_stable_pair_measure_generator: "Int_stable {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B}"
  unfolding Int_stable_def
  by safe (auto simp add: Times_Int_Times)

lemma (in finite_measure) finite_measure_cut_measurable:
  assumes [measurable]: "Q \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. emeasure M (Pair x -` Q)) \<in> borel_measurable N"
    (is "?s Q \<in> _")
  using Int_stable_pair_measure_generator pair_measure_closed assms
  unfolding sets_pair_measure
proof (induct rule: sigma_sets_induct_disjoint)
  case (compl A)
  with sets.sets_into_space have "\<And>x. emeasure M (Pair x -` ((space N \<times> space M) - A)) =
      (if x \<in> space N then emeasure M (space M) - ?s A x else 0)"
    unfolding sets_pair_measure[symmetric]
    by (auto intro!: emeasure_compl simp: vimage_Diff sets_Pair1)
  with compl sets.top show ?case
    by (auto intro!: measurable_If simp: space_pair_measure)
next
  case (union F)
  then have "\<And>x. emeasure M (Pair x -` (\<Union>i. F i)) = (\<Sum>i. ?s (F i) x)"
    by (simp add: suminf_emeasure disjoint_family_on_vimageI subset_eq vimage_UN sets_pair_measure[symmetric])
  with union show ?case
    unfolding sets_pair_measure[symmetric] by simp
qed (auto simp add: if_distrib Int_def[symmetric] intro!: measurable_If)

lemma (in sigma_finite_measure) measurable_emeasure_Pair:
  assumes Q: "Q \<in> sets (N \<Otimes>\<^sub>M M)" shows "(\<lambda>x. emeasure M (Pair x -` Q)) \<in> borel_measurable N" (is "?s Q \<in> _")
proof -
  obtain F :: "nat \<Rightarrow> 'a set" where F:
    "range F \<subseteq> sets M"
    "\<Union> (range F) = space M"
    "\<And>i. emeasure M (F i) \<noteq> \<infinity>"
    "disjoint_family F" by (blast intro: sigma_finite_disjoint)
  then have F_sets: "\<And>i. F i \<in> sets M" by auto
  let ?C = "\<lambda>x i. F i \<inter> Pair x -` Q"
  { fix i
    have [simp]: "space N \<times> F i \<inter> space N \<times> space M = space N \<times> F i"
      using F sets.sets_into_space by auto
    let ?R = "density M (indicator (F i))"
    have "finite_measure ?R"
      using F by (intro finite_measureI) (auto simp: emeasure_restricted subset_eq)
    then have "(\<lambda>x. emeasure ?R (Pair x -` (space N \<times> space ?R \<inter> Q))) \<in> borel_measurable N"
     by (rule finite_measure.finite_measure_cut_measurable) (auto intro: Q)
    moreover have "\<And>x. emeasure ?R (Pair x -` (space N \<times> space ?R \<inter> Q))
        = emeasure M (F i \<inter> Pair x -` (space N \<times> space ?R \<inter> Q))"
      using Q F_sets by (intro emeasure_restricted) (auto intro: sets_Pair1)
    moreover have "\<And>x. F i \<inter> Pair x -` (space N \<times> space ?R \<inter> Q) = ?C x i"
      using sets.sets_into_space[OF Q] by (auto simp: space_pair_measure)
    ultimately have "(\<lambda>x. emeasure M (?C x i)) \<in> borel_measurable N"
      by simp }
  moreover
  { fix x
    have "(\<Sum>i. emeasure M (?C x i)) = emeasure M (\<Union>i. ?C x i)"
    proof (intro suminf_emeasure)
      show "range (?C x) \<subseteq> sets M"
        using F \<open>Q \<in> sets (N \<Otimes>\<^sub>M M)\<close> by (auto intro!: sets_Pair1)
      have "disjoint_family F" using F by auto
      show "disjoint_family (?C x)"
        by (rule disjoint_family_on_bisimulation[OF \<open>disjoint_family F\<close>]) auto
    qed
    also have "(\<Union>i. ?C x i) = Pair x -` Q"
      using F sets.sets_into_space[OF \<open>Q \<in> sets (N \<Otimes>\<^sub>M M)\<close>]
      by (auto simp: space_pair_measure)
    finally have "emeasure M (Pair x -` Q) = (\<Sum>i. emeasure M (?C x i))"
      by simp }
  ultimately show ?thesis using \<open>Q \<in> sets (N \<Otimes>\<^sub>M M)\<close> F_sets
    by auto
qed

lemma (in sigma_finite_measure) measurable_emeasure[measurable (raw)]:
  assumes space: "\<And>x. x \<in> space N \<Longrightarrow> A x \<subseteq> space M"
  assumes A: "{x\<in>space (N \<Otimes>\<^sub>M M). snd x \<in> A (fst x)} \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. emeasure M (A x)) \<in> borel_measurable N"
proof -
  from space have "\<And>x. x \<in> space N \<Longrightarrow> Pair x -` {x \<in> space (N \<Otimes>\<^sub>M M). snd x \<in> A (fst x)} = A x"
    by (auto simp: space_pair_measure)
  with measurable_emeasure_Pair[OF A] show ?thesis
    by (auto cong: measurable_cong)
qed

lemma (in sigma_finite_measure) emeasure_pair_measure:
  assumes "X \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "emeasure (N \<Otimes>\<^sub>M M) X = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator X (x, y) \<partial>M \<partial>N)" (is "_ = ?\<mu> X")
proof (rule emeasure_measure_of[OF pair_measure_def])
  show "positive (sets (N \<Otimes>\<^sub>M M)) ?\<mu>"
    by (auto simp: positive_def)
  have eq[simp]: "\<And>A x y. indicator A (x, y) = indicator (Pair x -` A) y"
    by (auto simp: indicator_def)
  show "countably_additive (sets (N \<Otimes>\<^sub>M M)) ?\<mu>"
  proof (rule countably_additiveI)
    fix F :: "nat \<Rightarrow> ('b \<times> 'a) set" assume F: "range F \<subseteq> sets (N \<Otimes>\<^sub>M M)" "disjoint_family F"
    from F have *: "\<And>i. F i \<in> sets (N \<Otimes>\<^sub>M M)" by auto
    moreover have "\<And>x. disjoint_family (\<lambda>i. Pair x -` F i)"
      by (intro disjoint_family_on_bisimulation[OF F(2)]) auto
    moreover have "\<And>x. range (\<lambda>i. Pair x -` F i) \<subseteq> sets M"
      using F by (auto simp: sets_Pair1)
    ultimately show "(\<Sum>n. ?\<mu> (F n)) = ?\<mu> (\<Union>i. F i)"
      by (auto simp add: nn_integral_suminf[symmetric] vimage_UN suminf_emeasure
               intro!: nn_integral_cong nn_integral_indicator[symmetric])
  qed
  show "{a \<times> b |a b. a \<in> sets N \<and> b \<in> sets M} \<subseteq> Pow (space N \<times> space M)"
    using sets.space_closed[of N] sets.space_closed[of M] by auto
qed fact

lemma (in sigma_finite_measure) emeasure_pair_measure_alt:
  assumes X: "X \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "emeasure (N  \<Otimes>\<^sub>M M) X = (\<integral>\<^sup>+x. emeasure M (Pair x -` X) \<partial>N)"
proof -
  have [simp]: "\<And>x y. indicator X (x, y) = indicator (Pair x -` X) y"
    by (auto simp: indicator_def)
  show ?thesis
    using X by (auto intro!: nn_integral_cong simp: emeasure_pair_measure sets_Pair1)
qed

proposition (in sigma_finite_measure) emeasure_pair_measure_Times:
  assumes A: "A \<in> sets N" and B: "B \<in> sets M"
  shows "emeasure (N \<Otimes>\<^sub>M M) (A \<times> B) = emeasure N A * emeasure M B"
proof -
  have "emeasure (N \<Otimes>\<^sub>M M) (A \<times> B) = (\<integral>\<^sup>+x. emeasure M B * indicator A x \<partial>N)"
    using A B by (auto intro!: nn_integral_cong simp: emeasure_pair_measure_alt)
  also have "\<dots> = emeasure M B * emeasure N A"
    using A by (simp add: nn_integral_cmult_indicator)
  finally show ?thesis
    by (simp add: ac_simps)
qed

subsection \<open>Binary products of \<open>\<sigma>\<close>-finite emeasure spaces\<close>

locale\<^marker>\<open>tag unimportant\<close> pair_sigma_finite = M1?: sigma_finite_measure M1 + M2?: sigma_finite_measure M2
  for M1 :: "'a measure" and M2 :: "'b measure"

lemma (in pair_sigma_finite) measurable_emeasure_Pair1:
  "Q \<in> sets (M1 \<Otimes>\<^sub>M M2) \<Longrightarrow> (\<lambda>x. emeasure M2 (Pair x -` Q)) \<in> borel_measurable M1"
  using M2.measurable_emeasure_Pair .

lemma (in pair_sigma_finite) measurable_emeasure_Pair2:
  assumes Q: "Q \<in> sets (M1 \<Otimes>\<^sub>M M2)" shows "(\<lambda>y. emeasure M1 ((\<lambda>x. (x, y)) -` Q)) \<in> borel_measurable M2"
proof -
  have "(\<lambda>(x, y). (y, x)) -` Q \<inter> space (M2 \<Otimes>\<^sub>M M1) \<in> sets (M2 \<Otimes>\<^sub>M M1)"
    using Q measurable_pair_swap' by (auto intro: measurable_sets)
  note M1.measurable_emeasure_Pair[OF this]
  moreover have "\<And>y. Pair y -` ((\<lambda>(x, y). (y, x)) -` Q \<inter> space (M2 \<Otimes>\<^sub>M M1)) = (\<lambda>x. (x, y)) -` Q"
    using Q[THEN sets.sets_into_space] by (auto simp: space_pair_measure)
  ultimately show ?thesis by simp
qed

proposition (in pair_sigma_finite) sigma_finite_up_in_pair_measure_generator:
  defines "E \<equiv> {A \<times> B | A B. A \<in> sets M1 \<and> B \<in> sets M2}"
  shows "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> E \<and> incseq F \<and> (\<Union>i. F i) = space M1 \<times> space M2 \<and>
    (\<forall>i. emeasure (M1 \<Otimes>\<^sub>M M2) (F i) \<noteq> \<infinity>)"
proof -
  obtain F1 where F1: "range F1 \<subseteq> sets M1"
    "\<Union> (range F1) = space M1"
    "\<And>i. emeasure M1 (F1 i) \<noteq> \<infinity>"
    "incseq F1"
    by (rule M1.sigma_finite_incseq) blast
  obtain F2 where F2: "range F2 \<subseteq> sets M2"
    "\<Union> (range F2) = space M2"
    "\<And>i. emeasure M2 (F2 i) \<noteq> \<infinity>"
    "incseq F2"
    by (rule M2.sigma_finite_incseq) blast
  from F1 F2 have space: "space M1 = (\<Union>i. F1 i)" "space M2 = (\<Union>i. F2 i)" by auto
  let ?F = "\<lambda>i. F1 i \<times> F2 i"
  show ?thesis
  proof (intro exI[of _ ?F] conjI allI)
    show "range ?F \<subseteq> E" using F1 F2 by (auto simp: E_def) (metis range_subsetD)
  next
    have "space M1 \<times> space M2 \<subseteq> (\<Union>i. ?F i)"
    proof (intro subsetI)
      fix x assume "x \<in> space M1 \<times> space M2"
      then obtain i j where "fst x \<in> F1 i" "snd x \<in> F2 j"
        by (auto simp: space)
      then have "fst x \<in> F1 (max i j)" "snd x \<in> F2 (max j i)"
        using \<open>incseq F1\<close> \<open>incseq F2\<close> unfolding incseq_def
        by (force split: split_max)+
      then have "(fst x, snd x) \<in> F1 (max i j) \<times> F2 (max i j)"
        by (intro SigmaI) (auto simp add: max.commute)
      then show "x \<in> (\<Union>i. ?F i)" by auto
    qed
    then show "(\<Union>i. ?F i) = space M1 \<times> space M2"
      using space by (auto simp: space)
  next
    fix i show "incseq (\<lambda>i. F1 i \<times> F2 i)"
      using \<open>incseq F1\<close> \<open>incseq F2\<close> unfolding incseq_Suc_iff by auto
  next
    fix i
    from F1 F2 have "F1 i \<in> sets M1" "F2 i \<in> sets M2" by auto
    with F1 F2 show "emeasure (M1 \<Otimes>\<^sub>M M2) (F1 i \<times> F2 i) \<noteq> \<infinity>"
      by (auto simp add: emeasure_pair_measure_Times ennreal_mult_eq_top_iff)
  qed
qed

sublocale\<^marker>\<open>tag unimportant\<close> pair_sigma_finite \<subseteq> P?: sigma_finite_measure "M1 \<Otimes>\<^sub>M M2"
proof
  obtain F1 :: "'a set set" and F2 :: "'b set set" where
      "countable F1 \<and> F1 \<subseteq> sets M1 \<and> \<Union> F1 = space M1 \<and> (\<forall>a\<in>F1. emeasure M1 a \<noteq> \<infinity>)"
      "countable F2 \<and> F2 \<subseteq> sets M2 \<and> \<Union> F2 = space M2 \<and> (\<forall>a\<in>F2. emeasure M2 a \<noteq> \<infinity>)"
    using M1.sigma_finite_countable M2.sigma_finite_countable by auto
  then show
    "\<exists>A. countable A \<and> A \<subseteq> sets (M1 \<Otimes>\<^sub>M M2) \<and> \<Union>A = space (M1 \<Otimes>\<^sub>M M2) \<and> (\<forall>a\<in>A. emeasure (M1 \<Otimes>\<^sub>M M2) a \<noteq> \<infinity>)"
    by (intro exI[of _ "(\<lambda>(a, b). a \<times> b) ` (F1 \<times> F2)"] conjI)
       (auto simp: M2.emeasure_pair_measure_Times space_pair_measure set_eq_iff subset_eq ennreal_mult_eq_top_iff)
qed

lemma sigma_finite_pair_measure:
  assumes A: "sigma_finite_measure A" and B: "sigma_finite_measure B"
  shows "sigma_finite_measure (A \<Otimes>\<^sub>M B)"
proof -
  interpret A: sigma_finite_measure A by fact
  interpret B: sigma_finite_measure B by fact
  interpret AB: pair_sigma_finite A  B ..
  show ?thesis ..
qed

lemma sets_pair_swap:
  assumes "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<lambda>(x, y). (y, x)) -` A \<inter> space (M2 \<Otimes>\<^sub>M M1) \<in> sets (M2 \<Otimes>\<^sub>M M1)"
  using measurable_pair_swap' assms by (rule measurable_sets)

lemma (in pair_sigma_finite) distr_pair_swap:
  "M1 \<Otimes>\<^sub>M M2 = distr (M2 \<Otimes>\<^sub>M M1) (M1 \<Otimes>\<^sub>M M2) (\<lambda>(x, y). (y, x))" (is "?P = ?D")
proof -
  let ?E = "{a \<times> b |a b. a \<in> sets M1 \<and> b \<in> sets M2}"
  obtain F :: "nat \<Rightarrow> ('a \<times> 'b) set" where F: "range F \<subseteq> ?E"
    "incseq F" "\<Union> (range F) = space M1 \<times> space M2" "\<forall>i. emeasure (M1 \<Otimes>\<^sub>M M2) (F i) \<noteq> \<infinity>"
    using sigma_finite_up_in_pair_measure_generator by auto
  show ?thesis
  proof (rule measure_eqI_generator_eq[OF Int_stable_pair_measure_generator[of M1 M2]])
    show "?E \<subseteq> Pow (space ?P)"
      using sets.space_closed[of M1] sets.space_closed[of M2] by (auto simp: space_pair_measure)
    show "sets ?P = sigma_sets (space ?P) ?E"
      by (simp add: sets_pair_measure space_pair_measure)
    then show "sets ?D = sigma_sets (space ?P) ?E"
      by simp
    from F show "range F \<subseteq> ?E" "(\<Union>i. F i) = space ?P" "\<And>i. emeasure ?P (F i) \<noteq> \<infinity>"
      by (auto simp: space_pair_measure)
  next
    fix X assume "X \<in> ?E"
    then obtain A B where X[simp]: "X = A \<times> B" and A: "A \<in> sets M1" and B: "B \<in> sets M2" by auto
    have "(\<lambda>(y, x). (x, y)) -` X \<inter> space (M2 \<Otimes>\<^sub>M M1) = B \<times> A"
      using sets.sets_into_space[OF A] sets.sets_into_space[OF B] by (auto simp: space_pair_measure)
    with A B show "emeasure (M1 \<Otimes>\<^sub>M M2) X = emeasure ?D X"
      by (simp add: M2.emeasure_pair_measure_Times M1.emeasure_pair_measure_Times emeasure_distr
                    measurable_pair_swap' ac_simps)
  qed
qed

lemma (in pair_sigma_finite) emeasure_pair_measure_alt2:
  assumes A: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  shows "emeasure (M1 \<Otimes>\<^sub>M M2) A = (\<integral>\<^sup>+y. emeasure M1 ((\<lambda>x. (x, y)) -` A) \<partial>M2)"
    (is "_ = ?\<nu> A")
proof -
  have [simp]: "\<And>y. (Pair y -` ((\<lambda>(x, y). (y, x)) -` A \<inter> space (M2 \<Otimes>\<^sub>M M1))) = (\<lambda>x. (x, y)) -` A"
    using sets.sets_into_space[OF A] by (auto simp: space_pair_measure)
  show ?thesis using A
    by (subst distr_pair_swap)
       (simp_all del: vimage_Int add: measurable_sets[OF measurable_pair_swap']
                 M1.emeasure_pair_measure_alt emeasure_distr[OF measurable_pair_swap' A])
qed

lemma (in pair_sigma_finite) AE_pair:
  assumes "AE x in (M1 \<Otimes>\<^sub>M M2). Q x"
  shows "AE x in M1. (AE y in M2. Q (x, y))"
proof -
  obtain N where N: "N \<in> sets (M1 \<Otimes>\<^sub>M M2)" "emeasure (M1 \<Otimes>\<^sub>M M2) N = 0" "{x\<in>space (M1 \<Otimes>\<^sub>M M2). \<not> Q x} \<subseteq> N"
    using assms unfolding eventually_ae_filter by auto
  show ?thesis
  proof (rule AE_I)
    from N measurable_emeasure_Pair1[OF \<open>N \<in> sets (M1 \<Otimes>\<^sub>M M2)\<close>]
    show "emeasure M1 {x\<in>space M1. emeasure M2 (Pair x -` N) \<noteq> 0} = 0"
      by (auto simp: M2.emeasure_pair_measure_alt nn_integral_0_iff)
    show "{x \<in> space M1. emeasure M2 (Pair x -` N) \<noteq> 0} \<in> sets M1"
      by (intro borel_measurable_eq measurable_emeasure_Pair1 N sets.sets_Collect_neg N) simp
    { fix x assume "x \<in> space M1" "emeasure M2 (Pair x -` N) = 0"
      have "AE y in M2. Q (x, y)"
      proof (rule AE_I)
        show "emeasure M2 (Pair x -` N) = 0" by fact
        show "Pair x -` N \<in> sets M2" using N(1) by (rule sets_Pair1)
        show "{y \<in> space M2. \<not> Q (x, y)} \<subseteq> Pair x -` N"
          using N \<open>x \<in> space M1\<close> unfolding space_pair_measure by auto
      qed }
    then show "{x \<in> space M1. \<not> (AE y in M2. Q (x, y))} \<subseteq> {x \<in> space M1. emeasure M2 (Pair x -` N) \<noteq> 0}"
      by auto
  qed
qed

lemma (in pair_sigma_finite) AE_pair_measure:
  assumes "{x\<in>space (M1 \<Otimes>\<^sub>M M2). P x} \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  assumes ae: "AE x in M1. AE y in M2. P (x, y)"
  shows "AE x in M1 \<Otimes>\<^sub>M M2. P x"
proof (subst AE_iff_measurable[OF _ refl])
  show "{x\<in>space (M1 \<Otimes>\<^sub>M M2). \<not> P x} \<in> sets (M1 \<Otimes>\<^sub>M M2)"
    by (rule sets.sets_Collect) fact
  then have "emeasure (M1 \<Otimes>\<^sub>M M2) {x \<in> space (M1 \<Otimes>\<^sub>M M2). \<not> P x} =
      (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator {x \<in> space (M1 \<Otimes>\<^sub>M M2). \<not> P x} (x, y) \<partial>M2 \<partial>M1)"
    by (simp add: M2.emeasure_pair_measure)
  also have "\<dots> = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. 0 \<partial>M2 \<partial>M1)"
    using ae
    apply (safe intro!: nn_integral_cong_AE)
    apply (intro AE_I2)
    apply (safe intro!: nn_integral_cong_AE)
    apply auto
    done
  finally show "emeasure (M1 \<Otimes>\<^sub>M M2) {x \<in> space (M1 \<Otimes>\<^sub>M M2). \<not> P x} = 0" by simp
qed

lemma (in pair_sigma_finite) AE_pair_iff:
  "{x\<in>space (M1 \<Otimes>\<^sub>M M2). P (fst x) (snd x)} \<in> sets (M1 \<Otimes>\<^sub>M M2) \<Longrightarrow>
    (AE x in M1. AE y in M2. P x y) \<longleftrightarrow> (AE x in (M1 \<Otimes>\<^sub>M M2). P (fst x) (snd x))"
  using AE_pair[of "\<lambda>x. P (fst x) (snd x)"] AE_pair_measure[of "\<lambda>x. P (fst x) (snd x)"] by auto

lemma (in pair_sigma_finite) AE_commute:
  assumes P: "{x\<in>space (M1 \<Otimes>\<^sub>M M2). P (fst x) (snd x)} \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  shows "(AE x in M1. AE y in M2. P x y) \<longleftrightarrow> (AE y in M2. AE x in M1. P x y)"
proof -
  interpret Q: pair_sigma_finite M2 M1 ..
  have [simp]: "\<And>x. (fst (case x of (x, y) \<Rightarrow> (y, x))) = snd x" "\<And>x. (snd (case x of (x, y) \<Rightarrow> (y, x))) = fst x"
    by auto
  have "{x \<in> space (M2 \<Otimes>\<^sub>M M1). P (snd x) (fst x)} =
    (\<lambda>(x, y). (y, x)) -` {x \<in> space (M1 \<Otimes>\<^sub>M M2). P (fst x) (snd x)} \<inter> space (M2 \<Otimes>\<^sub>M M1)"
    by (auto simp: space_pair_measure)
  also have "\<dots> \<in> sets (M2 \<Otimes>\<^sub>M M1)"
    by (intro sets_pair_swap P)
  finally show ?thesis
    apply (subst AE_pair_iff[OF P])
    apply (subst distr_pair_swap)
    apply (subst AE_distr_iff[OF measurable_pair_swap' P])
    apply (subst Q.AE_pair_iff)
    apply simp_all
    done
qed

subsection "Fubinis theorem"

lemma measurable_compose_Pair1:
  "x \<in> space M1 \<Longrightarrow> g \<in> measurable (M1 \<Otimes>\<^sub>M M2) L \<Longrightarrow> (\<lambda>y. g (x, y)) \<in> measurable M2 L"
  by simp

lemma (in sigma_finite_measure) borel_measurable_nn_integral_fst:
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. \<integral>\<^sup>+ y. f (x, y) \<partial>M) \<in> borel_measurable M1"
using f proof induct
  case (cong u v)
  then have "\<And>w x. w \<in> space M1 \<Longrightarrow> x \<in> space M \<Longrightarrow> u (w, x) = v (w, x)"
    by (auto simp: space_pair_measure)
  show ?case
    apply (subst measurable_cong)
    apply (rule nn_integral_cong)
    apply fact+
    done
next
  case (set Q)
  have [simp]: "\<And>x y. indicator Q (x, y) = indicator (Pair x -` Q) y"
    by (auto simp: indicator_def)
  have "\<And>x. x \<in> space M1 \<Longrightarrow> emeasure M (Pair x -` Q) = \<integral>\<^sup>+ y. indicator Q (x, y) \<partial>M"
    by (simp add: sets_Pair1[OF set])
  from this measurable_emeasure_Pair[OF set] show ?case
    by (rule measurable_cong[THEN iffD1])
qed (simp_all add: nn_integral_add nn_integral_cmult measurable_compose_Pair1
                   nn_integral_monotone_convergence_SUP incseq_def le_fun_def image_comp
              cong: measurable_cong)

lemma (in sigma_finite_measure) nn_integral_fst:
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
  shows "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x, y) \<partial>M \<partial>M1) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M) f" (is "?I f = _")
  using f proof induct
  case (cong u v)
  then have "?I u = ?I v"
    by (intro nn_integral_cong) (auto simp: space_pair_measure)
  with cong show ?case
    by (simp cong: nn_integral_cong)
qed (simp_all add: emeasure_pair_measure nn_integral_cmult nn_integral_add
                   nn_integral_monotone_convergence_SUP measurable_compose_Pair1
                   borel_measurable_nn_integral_fst nn_integral_mono incseq_def le_fun_def image_comp
              cong: nn_integral_cong)

lemma (in sigma_finite_measure) borel_measurable_nn_integral[measurable (raw)]:
  "case_prod f \<in> borel_measurable (N \<Otimes>\<^sub>M M) \<Longrightarrow> (\<lambda>x. \<integral>\<^sup>+ y. f x y \<partial>M) \<in> borel_measurable N"
  using borel_measurable_nn_integral_fst[of "case_prod f" N] by simp

proposition (in pair_sigma_finite) nn_integral_snd:
  assumes f[measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M2) f"
proof -
  note measurable_pair_swap[OF f]
  from M1.nn_integral_fst[OF this]
  have "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ (x, y). f (y, x) \<partial>(M2 \<Otimes>\<^sub>M M1))"
    by simp
  also have "(\<integral>\<^sup>+ (x, y). f (y, x) \<partial>(M2 \<Otimes>\<^sub>M M1)) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M2) f"
    by (subst distr_pair_swap) (auto simp add: nn_integral_distr intro!: nn_integral_cong)
  finally show ?thesis .
qed

theorem (in pair_sigma_finite) Fubini:
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f (x, y) \<partial>M2) \<partial>M1)"
  unfolding nn_integral_snd[OF assms] M2.nn_integral_fst[OF assms] ..

theorem (in pair_sigma_finite) Fubini':
  assumes f: "case_prod f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>M2) \<partial>M1)"
  using Fubini[OF f] by simp

subsection \<open>Products on counting spaces, densities and distributions\<close>

proposition sigma_prod:
  assumes X_cover: "\<exists>E\<subseteq>A. countable E \<and> X = \<Union>E" and A: "A \<subseteq> Pow X"
  assumes Y_cover: "\<exists>E\<subseteq>B. countable E \<and> Y = \<Union>E" and B: "B \<subseteq> Pow Y"
  shows "sigma X A \<Otimes>\<^sub>M sigma Y B = sigma (X \<times> Y) {a \<times> b | a b. a \<in> A \<and> b \<in> B}"
    (is "?P = ?S")
proof (rule measure_eqI)
  have [simp]: "snd \<in> X \<times> Y \<rightarrow> Y" "fst \<in> X \<times> Y \<rightarrow> X"
    by auto
  let ?XY = "{{fst -` a \<inter> X \<times> Y | a. a \<in> A}, {snd -` b \<inter> X \<times> Y | b. b \<in> B}}"
  have "sets ?P = sets (SUP xy\<in>?XY. sigma (X \<times> Y) xy)"
    by (simp add: vimage_algebra_sigma sets_pair_eq_sets_fst_snd A B)
  also have "\<dots> = sets (sigma (X \<times> Y) (\<Union>?XY))"
    by (intro Sup_sigma arg_cong[where f=sets]) auto
  also have "\<dots> = sets ?S"
  proof (intro arg_cong[where f=sets] sigma_eqI sigma_sets_eqI)
    show "\<Union>?XY \<subseteq> Pow (X \<times> Y)" "{a \<times> b |a b. a \<in> A \<and> b \<in> B} \<subseteq> Pow (X \<times> Y)"
      using A B by auto
  next
    interpret XY: sigma_algebra "X \<times> Y" "sigma_sets (X \<times> Y) {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
      using A B by (intro sigma_algebra_sigma_sets) auto
    fix Z assume "Z \<in> \<Union>?XY"
    then show "Z \<in> sigma_sets (X \<times> Y) {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
    proof safe
      fix a assume "a \<in> A"
      from Y_cover obtain E where E: "E \<subseteq> B" "countable E" and "Y = \<Union>E"
        by auto
      with \<open>a \<in> A\<close> A have eq: "fst -` a \<inter> X \<times> Y = (\<Union>e\<in>E. a \<times> e)"
        by auto
      show "fst -` a \<inter> X \<times> Y \<in> sigma_sets (X \<times> Y) {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
        using \<open>a \<in> A\<close> E unfolding eq by (auto intro!: XY.countable_UN')
    next
      fix b assume "b \<in> B"
      from X_cover obtain E where E: "E \<subseteq> A" "countable E" and "X = \<Union>E"
        by auto
      with \<open>b \<in> B\<close> B have eq: "snd -` b \<inter> X \<times> Y = (\<Union>e\<in>E. e \<times> b)"
        by auto
      show "snd -` b \<inter> X \<times> Y \<in> sigma_sets (X \<times> Y) {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
        using \<open>b \<in> B\<close> E unfolding eq by (auto intro!: XY.countable_UN')
    qed
  next
    fix Z assume "Z \<in> {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
    then obtain a b where "Z = a \<times> b" and ab: "a \<in> A" "b \<in> B"
      by auto
    then have Z: "Z = (fst -` a \<inter> X \<times> Y) \<inter> (snd -` b \<inter> X \<times> Y)"
      using A B by auto
    interpret XY: sigma_algebra "X \<times> Y" "sigma_sets (X \<times> Y) (\<Union>?XY)"
      by (intro sigma_algebra_sigma_sets) auto
    show "Z \<in> sigma_sets (X \<times> Y) (\<Union>?XY)"
      unfolding Z by (rule XY.Int) (blast intro: ab)+
  qed
  finally show "sets ?P = sets ?S" .
next
  interpret finite_measure "sigma X A" for X A
    proof qed (simp add: emeasure_sigma)
  fix A assume "A \<in> sets ?P" then show "emeasure ?P A = emeasure ?S A"
    by (simp add: emeasure_pair_measure_alt emeasure_sigma)
qed

lemma sigma_sets_pair_measure_generator_finite:
  assumes "finite A" and "finite B"
  shows "sigma_sets (A \<times> B) { a \<times> b | a b. a \<subseteq> A \<and> b \<subseteq> B} = Pow (A \<times> B)"
  (is "sigma_sets ?prod ?sets = _")
proof safe
  have fin: "finite (A \<times> B)" using assms by (rule finite_cartesian_product)
  fix x assume subset: "x \<subseteq> A \<times> B"
  hence "finite x" using fin by (rule finite_subset)
  from this subset show "x \<in> sigma_sets ?prod ?sets"
  proof (induct x)
    case empty show ?case by (rule sigma_sets.Empty)
  next
    case (insert a x)
    hence "{a} \<in> sigma_sets ?prod ?sets" by auto
    moreover have "x \<in> sigma_sets ?prod ?sets" using insert by auto
    ultimately show ?case unfolding insert_is_Un[of a x] by (rule sigma_sets_Un)
  qed
next
  fix x a b
  assume "x \<in> sigma_sets ?prod ?sets" and "(a, b) \<in> x"
  from sigma_sets_into_sp[OF _ this(1)] this(2)
  show "a \<in> A" and "b \<in> B" by auto
qed

proposition  sets_pair_eq:
  assumes Ea: "Ea \<subseteq> Pow (space A)" "sets A = sigma_sets (space A) Ea"
    and Ca: "countable Ca" "Ca \<subseteq> Ea" "\<Union>Ca = space A"
    and Eb: "Eb \<subseteq> Pow (space B)" "sets B = sigma_sets (space B) Eb"
    and Cb: "countable Cb" "Cb \<subseteq> Eb" "\<Union>Cb = space B"
  shows "sets (A \<Otimes>\<^sub>M B) = sets (sigma (space A \<times> space B) { a \<times> b | a b. a \<in> Ea \<and> b \<in> Eb })"
    (is "_ = sets (sigma ?\<Omega> ?E)")
proof
  show "sets (sigma ?\<Omega> ?E) \<subseteq> sets (A \<Otimes>\<^sub>M B)"
    using Ea(1) Eb(1) by (subst sigma_le_sets) (auto simp: Ea(2) Eb(2))
  have "?E \<subseteq> Pow ?\<Omega>"
    using Ea(1) Eb(1) by auto
  then have E: "a \<in> Ea \<Longrightarrow> b \<in> Eb \<Longrightarrow> a \<times> b \<in> sets (sigma ?\<Omega> ?E)" for a b
    by auto
  have "sets (A \<Otimes>\<^sub>M B) \<subseteq> sets (Sup {vimage_algebra ?\<Omega> fst A, vimage_algebra ?\<Omega> snd B})"
    unfolding sets_pair_eq_sets_fst_snd ..
  also have "vimage_algebra ?\<Omega> fst A = vimage_algebra ?\<Omega> fst (sigma (space A) Ea)"
    by (intro vimage_algebra_cong[OF refl refl]) (simp add: Ea)
  also have "\<dots> = sigma ?\<Omega> {fst -` A \<inter> ?\<Omega> |A. A \<in> Ea}"
    by (intro Ea vimage_algebra_sigma) auto
  also have "vimage_algebra ?\<Omega> snd B = vimage_algebra ?\<Omega> snd (sigma (space B) Eb)"
    by (intro vimage_algebra_cong[OF refl refl]) (simp add: Eb)
  also have "\<dots> = sigma ?\<Omega> {snd -` A \<inter> ?\<Omega> |A. A \<in> Eb}"
    by (intro Eb vimage_algebra_sigma) auto
  also have "{sigma ?\<Omega> {fst -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Ea}, sigma ?\<Omega> {snd -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Eb}} =
    sigma ?\<Omega> ` {{fst -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Ea}, {snd -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Eb}}"
    by auto
  also have "sets (SUP S\<in>{{fst -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Ea}, {snd -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Eb}}. sigma ?\<Omega> S) =
    sets (sigma ?\<Omega> (\<Union>{{fst -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Ea}, {snd -` Aa \<inter> ?\<Omega> |Aa. Aa \<in> Eb}}))"
    using Ea(1) Eb(1) by (intro sets_Sup_sigma) auto
  also have "\<dots> \<subseteq> sets (sigma ?\<Omega> ?E)"
  proof (subst sigma_le_sets, safe intro!: space_in_measure_of)
    fix a assume "a \<in> Ea"
    then have "fst -` a \<inter> ?\<Omega> = (\<Union>b\<in>Cb. a \<times> b)"
      using Cb(3)[symmetric] Ea(1) by auto
    then show "fst -` a \<inter> ?\<Omega> \<in> sets (sigma ?\<Omega> ?E)"
      using Cb \<open>a \<in> Ea\<close> by (auto intro!: sets.countable_UN' E)
  next
    fix b assume "b \<in> Eb"
    then have "snd -` b \<inter> ?\<Omega> = (\<Union>a\<in>Ca. a \<times> b)"
      using Ca(3)[symmetric] Eb(1) by auto
    then show "snd -` b \<inter> ?\<Omega> \<in> sets (sigma ?\<Omega> ?E)"
      using Ca \<open>b \<in> Eb\<close> by (auto intro!: sets.countable_UN' E)
  qed
  finally show "sets (A \<Otimes>\<^sub>M B) \<subseteq> sets (sigma ?\<Omega> ?E)" .
qed

proposition  borel_prod:
  "(borel \<Otimes>\<^sub>M borel) = (borel :: ('a::second_countable_topology \<times> 'b::second_countable_topology) measure)"
  (is "?P = ?B")
proof -
  have "?B = sigma UNIV {A \<times> B | A B. open A \<and> open B}"
    by (rule second_countable_borel_measurable[OF open_prod_generated])
  also have "\<dots> = ?P"
    unfolding borel_def
    by (subst sigma_prod) (auto intro!: exI[of _ "{UNIV}"])
  finally show ?thesis ..
qed

proposition pair_measure_count_space:
  assumes A: "finite A" and B: "finite B"
  shows "count_space A \<Otimes>\<^sub>M count_space B = count_space (A \<times> B)" (is "?P = ?C")
proof (rule measure_eqI)
  interpret A: finite_measure "count_space A" by (rule finite_measure_count_space) fact
  interpret B: finite_measure "count_space B" by (rule finite_measure_count_space) fact
  interpret P: pair_sigma_finite "count_space A" "count_space B" ..
  show eq: "sets ?P = sets ?C"
    by (simp add: sets_pair_measure sigma_sets_pair_measure_generator_finite A B)
  fix X assume X: "X \<in> sets ?P"
  with eq have X_subset: "X \<subseteq> A \<times> B" by simp
  with A B have fin_Pair: "\<And>x. finite (Pair x -` X)"
    by (intro finite_subset[OF _ B]) auto
  have fin_X: "finite X" using X_subset by (rule finite_subset) (auto simp: A B)
  have card: "0 < card (Pair a -` X)" if "(a, b) \<in> X" for a b
    using card_gt_0_iff fin_Pair that by auto
  then have "emeasure ?P X = \<integral>\<^sup>+ x. emeasure (count_space B) (Pair x -` X)
            \<partial>count_space A"
    by (simp add: B.emeasure_pair_measure_alt X)
  also have "... = emeasure ?C X"
    apply (subst emeasure_count_space)
    using card X_subset A fin_Pair fin_X
    apply (auto simp add: nn_integral_count_space
                           of_nat_sum[symmetric] card_SigmaI[symmetric]
                simp del:  card_SigmaI
                intro!: arg_cong[where f=card])
    done
  finally show "emeasure ?P X = emeasure ?C X" .
qed


lemma emeasure_prod_count_space:
  assumes A: "A \<in> sets (count_space UNIV \<Otimes>\<^sub>M M)" (is "A \<in> sets (?A \<Otimes>\<^sub>M ?B)")
  shows "emeasure (?A \<Otimes>\<^sub>M ?B) A = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>?B \<partial>?A)"
  by (rule emeasure_measure_of[OF pair_measure_def])
     (auto simp: countably_additive_def positive_def suminf_indicator A
                 nn_integral_suminf[symmetric] dest: sets.sets_into_space)

lemma emeasure_prod_count_space_single[simp]: "emeasure (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) {x} = 1"
proof -
  have [simp]: "\<And>a b x y. indicator {(a, b)} (x, y) = (indicator {a} x * indicator {b} y::ennreal)"
    by (auto split: split_indicator)
  show ?thesis
    by (cases x) (auto simp: emeasure_prod_count_space nn_integral_cmult sets_Pair)
qed

lemma emeasure_count_space_prod_eq:
  fixes A :: "('a \<times> 'b) set"
  assumes A: "A \<in> sets (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)" (is "A \<in> sets (?A \<Otimes>\<^sub>M ?B)")
  shows "emeasure (?A \<Otimes>\<^sub>M ?B) A = emeasure (count_space UNIV) A"
proof -
  { fix A :: "('a \<times> 'b) set" assume "countable A"
    then have "emeasure (?A \<Otimes>\<^sub>M ?B) (\<Union>a\<in>A. {a}) = (\<integral>\<^sup>+a. emeasure (?A \<Otimes>\<^sub>M ?B) {a} \<partial>count_space A)"
      by (intro emeasure_UN_countable) (auto simp: sets_Pair disjoint_family_on_def)
    also have "\<dots> = (\<integral>\<^sup>+a. indicator A a \<partial>count_space UNIV)"
      by (subst nn_integral_count_space_indicator) auto
    finally have "emeasure (?A \<Otimes>\<^sub>M ?B) A = emeasure (count_space UNIV) A"
      by simp }
  note * = this

  show ?thesis
  proof cases
    assume "finite A" then show ?thesis
      by (intro * countable_finite)
  next
    assume "infinite A"
    then obtain C where "countable C" and "infinite C" and "C \<subseteq> A"
      by (auto dest: infinite_countable_subset')
    with A have "emeasure (?A \<Otimes>\<^sub>M ?B) C \<le> emeasure (?A \<Otimes>\<^sub>M ?B) A"
      by (intro emeasure_mono) auto
    also have "emeasure (?A \<Otimes>\<^sub>M ?B) C = emeasure (count_space UNIV) C"
      using \<open>countable C\<close> by (rule *)
    finally show ?thesis
      using \<open>infinite C\<close> \<open>infinite A\<close> by (simp add: top_unique)
  qed
qed

lemma nn_integral_count_space_prod_eq:
  "nn_integral (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) f = nn_integral (count_space UNIV) f"
    (is "nn_integral ?P f = _")
proof cases
  assume cntbl: "countable {x. f x \<noteq> 0}"
  have [simp]: "\<And>x. card ({x} \<inter> {x. f x \<noteq> 0}) = (indicator {x. f x \<noteq> 0} x::ennreal)"
    by (auto split: split_indicator)
  have [measurable]: "\<And>y. (\<lambda>x. indicator {y} x) \<in> borel_measurable ?P"
    by (rule measurable_discrete_difference[of "\<lambda>x. 0" _ borel "{y}" "\<lambda>x. indicator {y} x" for y])
       (auto intro: sets_Pair)

  have "(\<integral>\<^sup>+x. f x \<partial>?P) = (\<integral>\<^sup>+x. \<integral>\<^sup>+x'. f x * indicator {x} x' \<partial>count_space {x. f x \<noteq> 0} \<partial>?P)"
    by (auto simp add: nn_integral_cmult nn_integral_indicator' intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+x'. f x' * indicator {x'} x \<partial>count_space {x. f x \<noteq> 0} \<partial>?P)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+x'. \<integral>\<^sup>+x. f x' * indicator {x'} x \<partial>?P \<partial>count_space {x. f x \<noteq> 0})"
    by (intro nn_integral_count_space_nn_integral cntbl) auto
  also have "\<dots> = (\<integral>\<^sup>+x'. f x' \<partial>count_space {x. f x \<noteq> 0})"
    by (intro nn_integral_cong) (auto simp: nn_integral_cmult sets_Pair)
  finally show ?thesis
    by (auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
next
  { fix x assume "f x \<noteq> 0"
    then have "(\<exists>r\<ge>0. 0 < r \<and> f x = ennreal r) \<or> f x = \<infinity>"
      by (cases "f x" rule: ennreal_cases) (auto simp: less_le)
    then have "\<exists>n. ennreal (1 / real (Suc n)) \<le> f x"
      by (auto elim!: nat_approx_posE intro!: less_imp_le) }
  note * = this

  assume cntbl: "uncountable {x. f x \<noteq> 0}"
  also have "{x. f x \<noteq> 0} = (\<Union>n. {x. 1/Suc n \<le> f x})"
    using * by auto
  finally obtain n where "infinite {x. 1/Suc n \<le> f x}"
    by (meson countableI_type countable_UN uncountable_infinite)
  then obtain C where C: "C \<subseteq> {x. 1/Suc n \<le> f x}" and "countable C" "infinite C"
    by (metis infinite_countable_subset')

  have [measurable]: "C \<in> sets ?P"
    using sets.countable[OF _ \<open>countable C\<close>, of ?P] by (auto simp: sets_Pair)

  have "(\<integral>\<^sup>+x. ennreal (1/Suc n) * indicator C x \<partial>?P) \<le> nn_integral ?P f"
    using C by (intro nn_integral_mono) (auto split: split_indicator simp: zero_ereal_def[symmetric])
  moreover have "(\<integral>\<^sup>+x. ennreal (1/Suc n) * indicator C x \<partial>?P) = \<infinity>"
    using \<open>infinite C\<close> by (simp add: nn_integral_cmult emeasure_count_space_prod_eq ennreal_mult_top)
  moreover have "(\<integral>\<^sup>+x. ennreal (1/Suc n) * indicator C x \<partial>count_space UNIV) \<le> nn_integral (count_space UNIV) f"
    using C by (intro nn_integral_mono) (auto split: split_indicator simp: zero_ereal_def[symmetric])
  moreover have "(\<integral>\<^sup>+x. ennreal (1/Suc n) * indicator C x \<partial>count_space UNIV) = \<infinity>"
    using \<open>infinite C\<close> by (simp add: nn_integral_cmult ennreal_mult_top)
  ultimately show ?thesis
    by (simp add: top_unique)
qed

theorem pair_measure_density:
  assumes f: "f \<in> borel_measurable M1"
  assumes g: "g \<in> borel_measurable M2"
  assumes "sigma_finite_measure M2" "sigma_finite_measure (density M2 g)"
  shows "density M1 f \<Otimes>\<^sub>M density M2 g = density (M1 \<Otimes>\<^sub>M M2) (\<lambda>(x,y). f x * g y)" (is "?L = ?R")
proof (rule measure_eqI)
  interpret M2: sigma_finite_measure M2 by fact
  interpret D2: sigma_finite_measure "density M2 g" by fact

  fix A assume A: "A \<in> sets ?L"
  with f g have "(\<integral>\<^sup>+ x. f x * \<integral>\<^sup>+ y. g y * indicator A (x, y) \<partial>M2 \<partial>M1) =
    (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f x * g y * indicator A (x, y) \<partial>M2 \<partial>M1)"
    by (intro nn_integral_cong_AE)
       (auto simp add: nn_integral_cmult[symmetric] ac_simps)
  with A f g show "emeasure ?L A = emeasure ?R A"
    by (simp add: D2.emeasure_pair_measure emeasure_density nn_integral_density
                  M2.nn_integral_fst[symmetric]
             cong: nn_integral_cong)
qed simp

lemma sigma_finite_measure_distr:
  assumes "sigma_finite_measure (distr M N f)" and f: "f \<in> measurable M N"
  shows "sigma_finite_measure M"
proof -
  interpret sigma_finite_measure "distr M N f" by fact
  obtain A where A: "countable A" "A \<subseteq> sets (distr M N f)"
      "\<Union> A = space (distr M N f)" "\<forall>a\<in>A. emeasure (distr M N f) a \<noteq> \<infinity>"
    using sigma_finite_countable by auto
  show ?thesis
  proof
    show "\<exists>A. countable A \<and> A \<subseteq> sets M \<and> \<Union>A = space M \<and> (\<forall>a\<in>A. emeasure M a \<noteq> \<infinity>)"
      using A f
      by (intro exI[of _ "(\<lambda>a. f -` a \<inter> space M) ` A"])
         (auto simp: emeasure_distr set_eq_iff subset_eq intro: measurable_space)
  qed
qed

lemma pair_measure_distr:
  assumes f: "f \<in> measurable M S" and g: "g \<in> measurable N T"
  assumes "sigma_finite_measure (distr N T g)"
  shows "distr M S f \<Otimes>\<^sub>M distr N T g = distr (M \<Otimes>\<^sub>M N) (S \<Otimes>\<^sub>M T) (\<lambda>(x, y). (f x, g y))" (is "?P = ?D")
proof (rule measure_eqI)
  interpret T: sigma_finite_measure "distr N T g" by fact
  interpret N: sigma_finite_measure N by (rule sigma_finite_measure_distr) fact+

  fix A assume A: "A \<in> sets ?P"
  with f g show "emeasure ?P A = emeasure ?D A"
    by (auto simp add: N.emeasure_pair_measure_alt space_pair_measure emeasure_distr
                       T.emeasure_pair_measure_alt nn_integral_distr
             intro!: nn_integral_cong arg_cong[where f="emeasure N"])
qed simp

lemma pair_measure_eqI:
  assumes "sigma_finite_measure M1" "sigma_finite_measure M2"
  assumes sets: "sets (M1 \<Otimes>\<^sub>M M2) = sets M"
  assumes emeasure: "\<And>A B. A \<in> sets M1 \<Longrightarrow> B \<in> sets M2 \<Longrightarrow> emeasure M1 A * emeasure M2 B = emeasure M (A \<times> B)"
  shows "M1 \<Otimes>\<^sub>M M2 = M"
proof -
  interpret M1: sigma_finite_measure M1 by fact
  interpret M2: sigma_finite_measure M2 by fact
  interpret pair_sigma_finite M1 M2 ..
  let ?E = "{a \<times> b |a b. a \<in> sets M1 \<and> b \<in> sets M2}"
  let ?P = "M1 \<Otimes>\<^sub>M M2"
  obtain F :: "nat \<Rightarrow> ('a \<times> 'b) set" where F:
    "range F \<subseteq> ?E" "incseq F" "\<Union> (range F) = space M1 \<times> space M2" "\<forall>i. emeasure ?P (F i) \<noteq> \<infinity>"
    using sigma_finite_up_in_pair_measure_generator
    by blast
  show ?thesis
  proof (rule measure_eqI_generator_eq[OF Int_stable_pair_measure_generator[of M1 M2]])
    show "?E \<subseteq> Pow (space ?P)"
      using sets.space_closed[of M1] sets.space_closed[of M2] by (auto simp: space_pair_measure)
    show "sets ?P = sigma_sets (space ?P) ?E"
      by (simp add: sets_pair_measure space_pair_measure)
    then show "sets M = sigma_sets (space ?P) ?E"
      using sets[symmetric] by simp
  next
    show "range F \<subseteq> ?E" "(\<Union>i. F i) = space ?P" "\<And>i. emeasure ?P (F i) \<noteq> \<infinity>"
      using F by (auto simp: space_pair_measure)
  next
    fix X assume "X \<in> ?E"
    then obtain A B where X[simp]: "X = A \<times> B" and A: "A \<in> sets M1" and B: "B \<in> sets M2" by auto
    then have "emeasure ?P X = emeasure M1 A * emeasure M2 B"
       by (simp add: M2.emeasure_pair_measure_Times)
    also have "\<dots> = emeasure M (A \<times> B)"
      using A B emeasure by auto
    finally show "emeasure ?P X = emeasure M X"
      by simp
  qed
qed

lemma sets_pair_countable:
  assumes "countable S1" "countable S2"
  assumes M: "sets M = Pow S1" and N: "sets N = Pow S2"
  shows "sets (M \<Otimes>\<^sub>M N) = Pow (S1 \<times> S2)"
proof auto
  fix x a b assume x: "x \<in> sets (M \<Otimes>\<^sub>M N)" "(a, b) \<in> x"
  from sets.sets_into_space[OF x(1)] x(2)
    sets_eq_imp_space_eq[of N "count_space S2"] sets_eq_imp_space_eq[of M "count_space S1"] M N
  show "a \<in> S1" "b \<in> S2"
    by (auto simp: space_pair_measure)
next
  fix X assume X: "X \<subseteq> S1 \<times> S2"
  then have "countable X"
    by (metis countable_subset \<open>countable S1\<close> \<open>countable S2\<close> countable_SIGMA)
  have "X = (\<Union>(a, b)\<in>X. {a} \<times> {b})" by auto
  also have "\<dots> \<in> sets (M \<Otimes>\<^sub>M N)"
    using X
    by (safe intro!: sets.countable_UN' \<open>countable X\<close> subsetI pair_measureI) (auto simp: M N)
  finally show "X \<in> sets (M \<Otimes>\<^sub>M N)" .
qed

lemma pair_measure_countable:
  assumes "countable S1" "countable S2"
  shows "count_space S1 \<Otimes>\<^sub>M count_space S2 = count_space (S1 \<times> S2)"
proof (rule pair_measure_eqI)
  show "sigma_finite_measure (count_space S1)" "sigma_finite_measure (count_space S2)"
    using assms by (auto intro!: sigma_finite_measure_count_space_countable)
  show "sets (count_space S1 \<Otimes>\<^sub>M count_space S2) = sets (count_space (S1 \<times> S2))"
    by (subst sets_pair_countable[OF assms]) auto
next
  fix A B assume "A \<in> sets (count_space S1)" "B \<in> sets (count_space S2)"
  then show "emeasure (count_space S1) A * emeasure (count_space S2) B =
    emeasure (count_space (S1 \<times> S2)) (A \<times> B)"
    by (subst (1 2 3) emeasure_count_space) (auto simp: finite_cartesian_product_iff ennreal_mult_top ennreal_top_mult)
qed

proposition nn_integral_fst_count_space:
  "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x, y) \<partial>count_space UNIV \<partial>count_space UNIV) = integral\<^sup>N (count_space UNIV) f"
  (is "?lhs = ?rhs")
proof(cases)
  assume *: "countable {xy. f xy \<noteq> 0}"
  let ?A = "fst ` {xy. f xy \<noteq> 0}"
  let ?B = "snd ` {xy. f xy \<noteq> 0}"
  from * have [simp]: "countable ?A" "countable ?B" by(rule countable_image)+
  have "?lhs = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x, y) \<partial>count_space UNIV \<partial>count_space ?A)"
    by(rule nn_integral_count_space_eq)
      (auto simp add: nn_integral_0_iff_AE AE_count_space not_le intro: rev_image_eqI)
  also have "\<dots> = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x, y) \<partial>count_space ?B \<partial>count_space ?A)"
    by(intro nn_integral_count_space_eq nn_integral_cong)(auto intro: rev_image_eqI)
  also have "\<dots> = (\<integral>\<^sup>+ xy. f xy \<partial>count_space (?A \<times> ?B))"
    by(subst sigma_finite_measure.nn_integral_fst)
      (simp_all add: sigma_finite_measure_count_space_countable pair_measure_countable)
  also have "\<dots> = ?rhs"
    by(rule nn_integral_count_space_eq)(auto intro: rev_image_eqI)
  finally show ?thesis .
next
  { fix xy assume "f xy \<noteq> 0"
    then have "(\<exists>r\<ge>0. 0 < r \<and> f xy = ennreal r) \<or> f xy = \<infinity>"
      by (cases "f xy" rule: ennreal_cases) (auto simp: less_le)
    then have "\<exists>n. ennreal (1 / real (Suc n)) \<le> f xy"
      by (auto elim!: nat_approx_posE intro!: less_imp_le) }
  note * = this

  assume cntbl: "uncountable {xy. f xy \<noteq> 0}"
  also have "{xy. f xy \<noteq> 0} = (\<Union>n. {xy. 1/Suc n \<le> f xy})"
    using * by auto
  finally obtain n where "infinite {xy. 1/Suc n \<le> f xy}"
    by (meson countableI_type countable_UN uncountable_infinite)
  then obtain C where C: "C \<subseteq> {xy. 1/Suc n \<le> f xy}" and "countable C" "infinite C"
    by (metis infinite_countable_subset')

  have "\<infinity> = (\<integral>\<^sup>+ xy. ennreal (1 / Suc n) * indicator C xy \<partial>count_space UNIV)"
    using \<open>infinite C\<close> by(simp add: nn_integral_cmult ennreal_mult_top)
  also have "\<dots> \<le> ?rhs" using C
    by(intro nn_integral_mono)(auto split: split_indicator)
  finally have "?rhs = \<infinity>" by (simp add: top_unique)
  moreover have "?lhs = \<infinity>"
  proof(cases "finite (fst ` C)")
    case True
    then obtain x C' where x: "x \<in> fst ` C"
      and C': "C' = fst -` {x} \<inter> C"
      and "infinite C'"
      using \<open>infinite C\<close> by(auto elim!: inf_img_fin_domE')
    from x C C' have **: "C' \<subseteq> {xy. 1 / Suc n \<le> f xy}" by auto

    from C' \<open>infinite C'\<close> have "infinite (snd ` C')"
      by(auto dest!: finite_imageD simp add: inj_on_def)
    then have "\<infinity> = (\<integral>\<^sup>+ y. ennreal (1 / Suc n) * indicator (snd ` C') y \<partial>count_space UNIV)"
      by(simp add: nn_integral_cmult ennreal_mult_top)
    also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (1 / Suc n) * indicator C' (x, y) \<partial>count_space UNIV)"
      by(rule nn_integral_cong)(force split: split_indicator intro: rev_image_eqI simp add: C')
    also have "\<dots> = (\<integral>\<^sup>+ x'. (\<integral>\<^sup>+ y. ennreal (1 / Suc n) * indicator C' (x, y) \<partial>count_space UNIV) * indicator {x} x' \<partial>count_space UNIV)"
      by(simp add: one_ereal_def[symmetric])
    also have "\<dots> \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (1 / Suc n) * indicator C' (x, y) \<partial>count_space UNIV \<partial>count_space UNIV)"
      by(rule nn_integral_mono)(simp split: split_indicator)
    also have "\<dots> \<le> ?lhs" using **
      by(intro nn_integral_mono)(auto split: split_indicator)
    finally show ?thesis by (simp add: top_unique)
  next
    case False
    define C' where "C' = fst ` C"
    have "\<infinity> = \<integral>\<^sup>+ x. ennreal (1 / Suc n) * indicator C' x \<partial>count_space UNIV"
      using C'_def False by(simp add: nn_integral_cmult ennreal_mult_top)
    also have "\<dots> = \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (1 / Suc n) * indicator C' x * indicator {SOME y. (x, y) \<in> C} y \<partial>count_space UNIV \<partial>count_space UNIV"
      by(auto simp add: one_ereal_def[symmetric] max_def intro: nn_integral_cong)
    also have "\<dots> \<le> \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (1 / Suc n) * indicator C (x, y) \<partial>count_space UNIV \<partial>count_space UNIV"
      by(intro nn_integral_mono)(auto simp add: C'_def split: split_indicator intro: someI)
    also have "\<dots> \<le> ?lhs" using C
      by(intro nn_integral_mono)(auto split: split_indicator)
    finally show ?thesis by (simp add: top_unique)
  qed
  ultimately show ?thesis by simp
qed

proposition nn_integral_snd_count_space:
  "(\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f (x, y) \<partial>count_space UNIV \<partial>count_space UNIV) = integral\<^sup>N (count_space UNIV) f"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. (\<lambda>(y, x). f (x, y)) (y, x) \<partial>count_space UNIV \<partial>count_space UNIV)"
    by(simp)
  also have "\<dots> = \<integral>\<^sup>+ yx. (\<lambda>(y, x). f (x, y)) yx \<partial>count_space UNIV"
    by(rule nn_integral_fst_count_space)
  also have "\<dots> = \<integral>\<^sup>+ xy. f xy \<partial>count_space ((\<lambda>(x, y). (y, x)) ` UNIV)"
    by(subst nn_integral_bij_count_space[OF inj_on_imp_bij_betw, symmetric])
      (simp_all add: inj_on_def split_def)
  also have "\<dots> = ?rhs" by(rule nn_integral_count_space_eq) auto
  finally show ?thesis .
qed

lemma measurable_pair_measure_countable1:
  assumes "countable A"
  and [measurable]: "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) \<in> measurable N K"
  shows "f \<in> measurable (count_space A \<Otimes>\<^sub>M N) K"
using _ _ assms(1)
by(rule measurable_compose_countable'[where f="\<lambda>a b. f (a, snd b)" and g=fst and I=A, simplified])simp_all

subsection \<open>Product of Borel spaces\<close>

theorem borel_Times:
  fixes A :: "'a::topological_space set" and B :: "'b::topological_space set"
  assumes A: "A \<in> sets borel" and B: "B \<in> sets borel"
  shows "A \<times> B \<in> sets borel"
proof -
  have "A \<times> B = (A\<times>UNIV) \<inter> (UNIV \<times> B)"
    by auto
  moreover
  { have "A \<in> sigma_sets UNIV {S. open S}" using A by (simp add: sets_borel)
    then have "A\<times>UNIV \<in> sets borel"
    proof (induct A)
      case (Basic S) then show ?case
        by (auto intro!: borel_open open_Times)
    next
      case (Compl A)
      moreover have *: "(UNIV - A) \<times> UNIV = UNIV - (A \<times> UNIV)"
        by auto
      ultimately show ?case
        unfolding * by auto
    next
      case (Union A)
      moreover have *: "(\<Union>(A ` UNIV)) \<times> UNIV = \<Union>((\<lambda>i. A i \<times> UNIV) ` UNIV)"
        by auto
      ultimately show ?case
        unfolding * by auto
    qed simp }
  moreover
  { have "B \<in> sigma_sets UNIV {S. open S}" using B by (simp add: sets_borel)
    then have "UNIV\<times>B \<in> sets borel"
    proof (induct B)
      case (Basic S) then show ?case
        by (auto intro!: borel_open open_Times)
    next
      case (Compl B)
      moreover have *: "UNIV \<times> (UNIV - B) = UNIV - (UNIV \<times> B)"
        by auto
      ultimately show ?case
        unfolding * by auto
    next
      case (Union B)
      moreover have *: "UNIV \<times> (\<Union>(B ` UNIV)) = \<Union>((\<lambda>i. UNIV \<times> B i) ` UNIV)"
        by auto
      ultimately show ?case
        unfolding * by auto
    qed simp }
  ultimately show ?thesis
    by auto
qed

lemma finite_measure_pair_measure:
  assumes "finite_measure M" "finite_measure N"
  shows "finite_measure (N  \<Otimes>\<^sub>M M)"
proof (rule finite_measureI)
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  show "emeasure (N  \<Otimes>\<^sub>M M) (space (N  \<Otimes>\<^sub>M M)) \<noteq> \<infinity>"
    by (auto simp: space_pair_measure M.emeasure_pair_measure_Times ennreal_mult_eq_top_iff)
qed

end
