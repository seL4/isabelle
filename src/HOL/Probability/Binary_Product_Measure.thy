(*  Title:      HOL/Probability/Binary_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

section {*Binary product measures*}

theory Binary_Product_Measure
imports Nonnegative_Lebesgue_Integration
begin

lemma Pair_vimage_times[simp]: "Pair x -` (A \<times> B) = (if x \<in> A then B else {})"
  by auto

lemma rev_Pair_vimage_times[simp]: "(\<lambda>x. (x, y)) -` (A \<times> B) = (if y \<in> B then A else {})"
  by auto

subsection "Binary products"

definition pair_measure (infixr "\<Otimes>\<^sub>M" 80) where
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

lemma sets_pair_in_sets:
  assumes N: "space A \<times> space B = space N"
  assumes "\<And>a b. a \<in> sets A \<Longrightarrow> b \<in> sets B \<Longrightarrow> a \<times> b \<in> sets N"
  shows "sets (A \<Otimes>\<^sub>M B) \<subseteq> sets N"
  using assms by (auto intro!: sets.sigma_sets_subset simp: sets_pair_measure N)

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
  "(\<lambda>x. f x (fst (g x)) (snd (g x))) \<in> measurable M N \<Longrightarrow> (\<lambda>x. split (f x) (g x)) \<in> measurable M N"
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
  by (auto simp: fst_vimage_eq_Times space_pair_measure sets.sets_into_space times_Int_times
    measurable_def)

lemma measurable_snd[intro!, simp, measurable]: "snd \<in> measurable (M1 \<Otimes>\<^sub>M M2) M2"
  by (auto simp: snd_vimage_eq_Times space_pair_measure sets.sets_into_space times_Int_times
    measurable_def)

lemma measurable_Pair_compose_split[measurable_dest]:
  assumes f: "split f \<in> measurable (M1 \<Otimes>\<^sub>M M2) N"
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

lemma sets_pair_eq_sets_fst_snd:
  "sets (A \<Otimes>\<^sub>M B) = sets (Sup_sigma {vimage_algebra (space A \<times> space B) fst A, vimage_algebra (space A \<times> space B) snd B})"
    (is "?P = sets (Sup_sigma {?fst, ?snd})")
proof -
  { fix a b assume ab: "a \<in> sets A" "b \<in> sets B"
    then have "a \<times> b = (fst -` a \<inter> (space A \<times> space B)) \<inter> (snd -` b \<inter> (space A \<times> space B))"
      by (auto dest: sets.sets_into_space)
    also have "\<dots> \<in> sets (Sup_sigma {?fst, ?snd})"
      using ab by (auto intro: in_Sup_sigma in_vimage_algebra)
    finally have "a \<times> b \<in> sets (Sup_sigma {?fst, ?snd})" . }
  moreover have "sets ?fst \<subseteq> sets (A \<Otimes>\<^sub>M B)"
    by (rule sets_image_in_sets) (auto simp: space_pair_measure[symmetric])
  moreover have "sets ?snd \<subseteq> sets (A \<Otimes>\<^sub>M B)"  
    by (rule sets_image_in_sets) (auto simp: space_pair_measure)
  ultimately show ?thesis
    by (intro antisym[of "sets A" for A] sets_Sup_in_sets sets_pair_in_sets )
       (auto simp add: space_Sup_sigma space_pair_measure)
qed

lemma measurable_pair_iff:
  "f \<in> measurable M (M1 \<Otimes>\<^sub>M M2) \<longleftrightarrow> (fst \<circ> f) \<in> measurable M M1 \<and> (snd \<circ> f) \<in> measurable M M2"
  by (auto intro: measurable_pair[of f M M1 M2]) 

lemma measurable_split_conv:
  "(\<lambda>(x, y). f x y) \<in> measurable A B \<longleftrightarrow> (\<lambda>x. f (fst x) (snd x)) \<in> measurable A B"
  by (intro arg_cong2[where f="op \<in>"]) auto

lemma measurable_pair_swap': "(\<lambda>(x,y). (y, x)) \<in> measurable (M1 \<Otimes>\<^sub>M M2) (M2 \<Otimes>\<^sub>M M1)"
  by (auto intro!: measurable_Pair simp: measurable_split_conv)

lemma measurable_pair_swap:
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
    using A by (auto simp add: measurable_Pair1' intro!: measurable_sets split: split_if_asm)
  finally show ?thesis .
qed

lemma measurable_Pair2': "y \<in> space M2 \<Longrightarrow> (\<lambda>x. (x, y)) \<in> measurable M1 (M1 \<Otimes>\<^sub>M M2)"
  by (auto intro!: measurable_Pair)

lemma sets_Pair2: assumes A: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)" shows "(\<lambda>x. (x, y)) -` A \<in> sets M1"
proof -
  have "(\<lambda>x. (x, y)) -` A = (if y \<in> space M2 then (\<lambda>x. (x, y)) -` A \<inter> space M1 else {})"
    using A[THEN sets.sets_into_space] by (auto simp: space_pair_measure)
  also have "\<dots> \<in> sets M1"
    using A by (auto simp add: measurable_Pair2' intro!: measurable_sets split: split_if_asm)
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
  by safe (auto simp add: times_Int_times)

lemma disjoint_family_vimageI: "disjoint_family F \<Longrightarrow> disjoint_family (\<lambda>i. f -` F i)"
  by (auto simp: disjoint_family_on_def)

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
    by (simp add: suminf_emeasure disjoint_family_vimageI subset_eq vimage_UN sets_pair_measure[symmetric])
  with union show ?case
    unfolding sets_pair_measure[symmetric] by simp
qed (auto simp add: if_distrib Int_def[symmetric] intro!: measurable_If)

lemma (in sigma_finite_measure) measurable_emeasure_Pair:
  assumes Q: "Q \<in> sets (N \<Otimes>\<^sub>M M)" shows "(\<lambda>x. emeasure M (Pair x -` Q)) \<in> borel_measurable N" (is "?s Q \<in> _")
proof -
  from sigma_finite_disjoint guess F . note F = this
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
        using F `Q \<in> sets (N \<Otimes>\<^sub>M M)` by (auto intro!: sets_Pair1)
      have "disjoint_family F" using F by auto
      show "disjoint_family (?C x)"
        by (rule disjoint_family_on_bisimulation[OF `disjoint_family F`]) auto
    qed
    also have "(\<Union>i. ?C x i) = Pair x -` Q"
      using F sets.sets_into_space[OF `Q \<in> sets (N \<Otimes>\<^sub>M M)`]
      by (auto simp: space_pair_measure)
    finally have "emeasure M (Pair x -` Q) = (\<Sum>i. emeasure M (?C x i))"
      by simp }
  ultimately show ?thesis using `Q \<in> sets (N \<Otimes>\<^sub>M M)` F_sets
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
    by (auto simp: positive_def nn_integral_nonneg)
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
      by (auto simp add: nn_integral_suminf[symmetric] vimage_UN suminf_emeasure emeasure_nonneg
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

lemma (in sigma_finite_measure) emeasure_pair_measure_Times:
  assumes A: "A \<in> sets N" and B: "B \<in> sets M"
  shows "emeasure (N \<Otimes>\<^sub>M M) (A \<times> B) = emeasure N A * emeasure M B"
proof -
  have "emeasure (N \<Otimes>\<^sub>M M) (A \<times> B) = (\<integral>\<^sup>+x. emeasure M B * indicator A x \<partial>N)"
    using A B by (auto intro!: nn_integral_cong simp: emeasure_pair_measure_alt)
  also have "\<dots> = emeasure M B * emeasure N A"
    using A by (simp add: emeasure_nonneg nn_integral_cmult_indicator)
  finally show ?thesis
    by (simp add: ac_simps)
qed

subsection {* Binary products of $\sigma$-finite emeasure spaces *}

locale pair_sigma_finite = M1: sigma_finite_measure M1 + M2: sigma_finite_measure M2
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

lemma (in pair_sigma_finite) sigma_finite_up_in_pair_measure_generator:
  defines "E \<equiv> {A \<times> B | A B. A \<in> sets M1 \<and> B \<in> sets M2}"
  shows "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> E \<and> incseq F \<and> (\<Union>i. F i) = space M1 \<times> space M2 \<and>
    (\<forall>i. emeasure (M1 \<Otimes>\<^sub>M M2) (F i) \<noteq> \<infinity>)"
proof -
  from M1.sigma_finite_incseq guess F1 . note F1 = this
  from M2.sigma_finite_incseq guess F2 . note F2 = this
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
        using `incseq F1` `incseq F2` unfolding incseq_def
        by (force split: split_max)+
      then have "(fst x, snd x) \<in> F1 (max i j) \<times> F2 (max i j)"
        by (intro SigmaI) (auto simp add: max.commute)
      then show "x \<in> (\<Union>i. ?F i)" by auto
    qed
    then show "(\<Union>i. ?F i) = space M1 \<times> space M2"
      using space by (auto simp: space)
  next
    fix i show "incseq (\<lambda>i. F1 i \<times> F2 i)"
      using `incseq F1` `incseq F2` unfolding incseq_Suc_iff by auto
  next
    fix i
    from F1 F2 have "F1 i \<in> sets M1" "F2 i \<in> sets M2" by auto
    with F1 F2 emeasure_nonneg[of M1 "F1 i"] emeasure_nonneg[of M2 "F2 i"]
    show "emeasure (M1 \<Otimes>\<^sub>M M2) (F1 i \<times> F2 i) \<noteq> \<infinity>"
      by (auto simp add: emeasure_pair_measure_Times)
  qed
qed

sublocale pair_sigma_finite \<subseteq> P: sigma_finite_measure "M1 \<Otimes>\<^sub>M M2"
proof
  from M1.sigma_finite_countable guess F1 ..
  moreover from M2.sigma_finite_countable guess F2 ..
  ultimately show
    "\<exists>A. countable A \<and> A \<subseteq> sets (M1 \<Otimes>\<^sub>M M2) \<and> \<Union>A = space (M1 \<Otimes>\<^sub>M M2) \<and> (\<forall>a\<in>A. emeasure (M1 \<Otimes>\<^sub>M M2) a \<noteq> \<infinity>)"
    by (intro exI[of _ "(\<lambda>(a, b). a \<times> b) ` (F1 \<times> F2)"] conjI)
       (auto simp: M2.emeasure_pair_measure_Times space_pair_measure set_eq_iff subset_eq
             dest: sets.sets_into_space)
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
  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  let ?E = "{a \<times> b |a b. a \<in> sets M1 \<and> b \<in> sets M2}"
  show ?thesis
  proof (rule measure_eqI_generator_eq[OF Int_stable_pair_measure_generator[of M1 M2]])
    show "?E \<subseteq> Pow (space ?P)"
      using sets.space_closed[of M1] sets.space_closed[of M2] by (auto simp: space_pair_measure)
    show "sets ?P = sigma_sets (space ?P) ?E"
      by (simp add: sets_pair_measure space_pair_measure)
    then show "sets ?D = sigma_sets (space ?P) ?E"
      by simp
  next
    show "range F \<subseteq> ?E" "(\<Union>i. F i) = space ?P" "\<And>i. emeasure ?P (F i) \<noteq> \<infinity>"
      using F by (auto simp: space_pair_measure)
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
    from N measurable_emeasure_Pair1[OF `N \<in> sets (M1 \<Otimes>\<^sub>M M2)`]
    show "emeasure M1 {x\<in>space M1. emeasure M2 (Pair x -` N) \<noteq> 0} = 0"
      by (auto simp: M2.emeasure_pair_measure_alt nn_integral_0_iff emeasure_nonneg)
    show "{x \<in> space M1. emeasure M2 (Pair x -` N) \<noteq> 0} \<in> sets M1"
      by (intro borel_measurable_ereal_neq_const measurable_emeasure_Pair1 N)
    { fix x assume "x \<in> space M1" "emeasure M2 (Pair x -` N) = 0"
      have "AE y in M2. Q (x, y)"
      proof (rule AE_I)
        show "emeasure M2 (Pair x -` N) = 0" by fact
        show "Pair x -` N \<in> sets M2" using N(1) by (rule sets_Pair1)
        show "{y \<in> space M2. \<not> Q (x, y)} \<subseteq> Pair x -` N"
          using N `x \<in> space M1` unfolding space_pair_measure by auto
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

lemma (in sigma_finite_measure) borel_measurable_nn_integral_fst':
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)" "\<And>x. 0 \<le> f x"
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
                   nn_integral_monotone_convergence_SUP incseq_def le_fun_def
              cong: measurable_cong)

lemma (in sigma_finite_measure) nn_integral_fst':
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)" "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x, y) \<partial>M \<partial>M1) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M) f" (is "?I f = _")
using f proof induct
  case (cong u v)
  then have "?I u = ?I v"
    by (intro nn_integral_cong) (auto simp: space_pair_measure)
  with cong show ?case
    by (simp cong: nn_integral_cong)
qed (simp_all add: emeasure_pair_measure nn_integral_cmult nn_integral_add
                   nn_integral_monotone_convergence_SUP
                   measurable_compose_Pair1 nn_integral_nonneg
                   borel_measurable_nn_integral_fst' nn_integral_mono incseq_def le_fun_def
              cong: nn_integral_cong)

lemma (in sigma_finite_measure) nn_integral_fst:
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
  shows "(\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f (x, y) \<partial>M) \<partial>M1) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M) f"
  using f
    borel_measurable_nn_integral_fst'[of "\<lambda>x. max 0 (f x)"]
    nn_integral_fst'[of "\<lambda>x. max 0 (f x)"]
  unfolding nn_integral_max_0 by auto

lemma (in sigma_finite_measure) borel_measurable_nn_integral[measurable (raw)]:
  "split f \<in> borel_measurable (N \<Otimes>\<^sub>M M) \<Longrightarrow> (\<lambda>x. \<integral>\<^sup>+ y. f x y \<partial>M) \<in> borel_measurable N"
  using borel_measurable_nn_integral_fst'[of "\<lambda>x. max 0 (split f x)" N]
  by (simp add: nn_integral_max_0)

lemma (in pair_sigma_finite) nn_integral_snd:
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M2) f"
proof -
  note measurable_pair_swap[OF f]
  from M1.nn_integral_fst[OF this]
  have "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ (x, y). f (y, x) \<partial>(M2 \<Otimes>\<^sub>M M1))"
    by simp
  also have "(\<integral>\<^sup>+ (x, y). f (y, x) \<partial>(M2 \<Otimes>\<^sub>M M1)) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M2) f"
    by (subst distr_pair_swap)
       (auto simp: nn_integral_distr[OF measurable_pair_swap' f] intro!: nn_integral_cong)
  finally show ?thesis .
qed

lemma (in pair_sigma_finite) Fubini:
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f (x, y) \<partial>M2) \<partial>M1)"
  unfolding nn_integral_snd[OF assms] M2.nn_integral_fst[OF assms] ..

lemma (in pair_sigma_finite) Fubini':
  assumes f: "split f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>M2) \<partial>M1)"
  using Fubini[OF f] by simp

subsection {* Products on counting spaces, densities and distributions *}

lemma sigma_prod:
  assumes X_cover: "\<exists>E\<subseteq>A. countable E \<and> X = \<Union>E" and A: "A \<subseteq> Pow X"
  assumes Y_cover: "\<exists>E\<subseteq>B. countable E \<and> Y = \<Union>E" and B: "B \<subseteq> Pow Y"
  shows "sigma X A \<Otimes>\<^sub>M sigma Y B = sigma (X \<times> Y) {a \<times> b | a b. a \<in> A \<and> b \<in> B}"
    (is "?P = ?S")
proof (rule measure_eqI)
  have [simp]: "snd \<in> X \<times> Y \<rightarrow> Y" "fst \<in> X \<times> Y \<rightarrow> X"
    by auto
  let ?XY = "{{fst -` a \<inter> X \<times> Y | a. a \<in> A}, {snd -` b \<inter> X \<times> Y | b. b \<in> B}}"
  have "sets ?P = 
    sets (\<Squnion>\<^sub>\<sigma> xy\<in>?XY. sigma (X \<times> Y) xy)"
    by (simp add: vimage_algebra_sigma sets_pair_eq_sets_fst_snd A B)
  also have "\<dots> = sets (sigma (X \<times> Y) (\<Union>?XY))"
    by (intro Sup_sigma_sigma arg_cong[where f=sets]) auto
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
      with `a \<in> A` A have eq: "fst -` a \<inter> X \<times> Y = (\<Union>e\<in>E. a \<times> e)"
        by auto
      show "fst -` a \<inter> X \<times> Y \<in> sigma_sets (X \<times> Y) {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
        using `a \<in> A` E unfolding eq by (auto intro!: XY.countable_UN')
    next
      fix b assume "b \<in> B"
      from X_cover obtain E where E: "E \<subseteq> A" "countable E" and "X = \<Union>E"
        by auto
      with `b \<in> B` B have eq: "snd -` b \<inter> X \<times> Y = (\<Union>e\<in>E. e \<times> b)"
        by auto
      show "snd -` b \<inter> X \<times> Y \<in> sigma_sets (X \<times> Y) {a \<times> b |a b. a \<in> A \<and> b \<in> B}"
        using `b \<in> B` E unfolding eq by (auto intro!: XY.countable_UN')
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

lemma borel_prod:
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

lemma pair_measure_count_space:
  assumes A: "finite A" and B: "finite B"
  shows "count_space A \<Otimes>\<^sub>M count_space B = count_space (A \<times> B)" (is "?P = ?C")
proof (rule measure_eqI)
  interpret A: finite_measure "count_space A" by (rule finite_measure_count_space) fact
  interpret B: finite_measure "count_space B" by (rule finite_measure_count_space) fact
  interpret P: pair_sigma_finite "count_space A" "count_space B" by default
  show eq: "sets ?P = sets ?C"
    by (simp add: sets_pair_measure sigma_sets_pair_measure_generator_finite A B)
  fix X assume X: "X \<in> sets ?P"
  with eq have X_subset: "X \<subseteq> A \<times> B" by simp
  with A B have fin_Pair: "\<And>x. finite (Pair x -` X)"
    by (intro finite_subset[OF _ B]) auto
  have fin_X: "finite X" using X_subset by (rule finite_subset) (auto simp: A B)
  show "emeasure ?P X = emeasure ?C X"
    apply (subst B.emeasure_pair_measure_alt[OF X])
    apply (subst emeasure_count_space)
    using X_subset apply auto []
    apply (simp add: fin_Pair emeasure_count_space X_subset fin_X)
    apply (subst nn_integral_count_space)
    using A apply simp
    apply (simp del: real_of_nat_setsum add: real_of_nat_setsum[symmetric])
    apply (subst card_gt_0_iff)
    apply (simp add: fin_Pair)
    apply (subst card_SigmaI[symmetric])
    using A apply simp
    using fin_Pair apply simp
    using X_subset apply (auto intro!: arg_cong[where f=card])
    done
qed

lemma pair_measure_density:
  assumes f: "f \<in> borel_measurable M1" "AE x in M1. 0 \<le> f x"
  assumes g: "g \<in> borel_measurable M2" "AE x in M2. 0 \<le> g x"
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
  from sigma_finite_countable guess A .. note A = this
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
  interpret pair_sigma_finite M1 M2 by default
  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  let ?E = "{a \<times> b |a b. a \<in> sets M1 \<and> b \<in> sets M2}"
  let ?P = "M1 \<Otimes>\<^sub>M M2"
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
    by (metis countable_subset `countable S1` `countable S2` countable_SIGMA)
  have "X = (\<Union>(a, b)\<in>X. {a} \<times> {b})" by auto
  also have "\<dots> \<in> sets (M \<Otimes>\<^sub>M N)"
    using X
    by (safe intro!: sets.countable_UN' `countable X` subsetI pair_measureI) (auto simp: M N)
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
    by (subst (1 2 3) emeasure_count_space) (auto simp: finite_cartesian_product_iff)
qed

subsection {* Product of Borel spaces *}

lemma borel_Times:
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
      moreover have *: "(UNION UNIV A) \<times> UNIV = UNION UNIV (\<lambda>i. A i \<times> UNIV)"
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
      moreover have *: "UNIV \<times> (UNION UNIV B) = UNION UNIV (\<lambda>i. UNIV \<times> B i)"
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
    by (auto simp: space_pair_measure M.emeasure_pair_measure_Times)
qed

end