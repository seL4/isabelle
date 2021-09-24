(*  Title:      HOL/Analysis/Finite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

section \<open>Finite Product Measure\<close>

theory Finite_Product_Measure
imports Binary_Product_Measure Function_Topology
begin

lemma PiE_choice: "(\<exists>f\<in>Pi\<^sub>E I F. \<forall>i\<in>I. P i (f i)) \<longleftrightarrow> (\<forall>i\<in>I. \<exists>x\<in>F i. P i x)"
  by (auto simp: Bex_def PiE_iff Ball_def dest!: choice_iff'[THEN iffD1])
     (force intro: exI[of _ "restrict f I" for f])

lemma case_prod_const: "(\<lambda>(i, j). c) = (\<lambda>_. c)"
  by auto

subsection\<^marker>\<open>tag unimportant\<close> \<open>More about Function restricted by \<^const>\<open>extensional\<close>\<close>

definition
  "merge I J = (\<lambda>(x, y) i. if i \<in> I then x i else if i \<in> J then y i else undefined)"

lemma merge_apply[simp]:
  "I \<inter> J = {} \<Longrightarrow> i \<in> I \<Longrightarrow> merge I J (x, y) i = x i"
  "I \<inter> J = {} \<Longrightarrow> i \<in> J \<Longrightarrow> merge I J (x, y) i = y i"
  "J \<inter> I = {} \<Longrightarrow> i \<in> I \<Longrightarrow> merge I J (x, y) i = x i"
  "J \<inter> I = {} \<Longrightarrow> i \<in> J \<Longrightarrow> merge I J (x, y) i = y i"
  "i \<notin> I \<Longrightarrow> i \<notin> J \<Longrightarrow> merge I J (x, y) i = undefined"
  unfolding merge_def by auto

lemma merge_commute:
  "I \<inter> J = {} \<Longrightarrow> merge I J (x, y) = merge J I (y, x)"
  by (force simp: merge_def)

lemma Pi_cancel_merge_range[simp]:
  "I \<inter> J = {} \<Longrightarrow> x \<in> Pi I (merge I J (A, B)) \<longleftrightarrow> x \<in> Pi I A"
  "I \<inter> J = {} \<Longrightarrow> x \<in> Pi I (merge J I (B, A)) \<longleftrightarrow> x \<in> Pi I A"
  "J \<inter> I = {} \<Longrightarrow> x \<in> Pi I (merge I J (A, B)) \<longleftrightarrow> x \<in> Pi I A"
  "J \<inter> I = {} \<Longrightarrow> x \<in> Pi I (merge J I (B, A)) \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: Pi_def)

lemma Pi_cancel_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow> merge I J (x, y) \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  "J \<inter> I = {} \<Longrightarrow> merge I J (x, y) \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  "I \<inter> J = {} \<Longrightarrow> merge I J (x, y) \<in> Pi J B \<longleftrightarrow> y \<in> Pi J B"
  "J \<inter> I = {} \<Longrightarrow> merge I J (x, y) \<in> Pi J B \<longleftrightarrow> y \<in> Pi J B"
  by (auto simp: Pi_def)

lemma extensional_merge[simp]: "merge I J (x, y) \<in> extensional (I \<union> J)"
  by (auto simp: extensional_def)

lemma restrict_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow> restrict (merge I J (x, y)) I = restrict x I"
  "I \<inter> J = {} \<Longrightarrow> restrict (merge I J (x, y)) J = restrict y J"
  "J \<inter> I = {} \<Longrightarrow> restrict (merge I J (x, y)) I = restrict x I"
  "J \<inter> I = {} \<Longrightarrow> restrict (merge I J (x, y)) J = restrict y J"
  by (auto simp: restrict_def)

lemma split_merge: "P (merge I J (x,y) i) \<longleftrightarrow> (i \<in> I \<longrightarrow> P (x i)) \<and> (i \<in> J - I \<longrightarrow> P (y i)) \<and> (i \<notin> I \<union> J \<longrightarrow> P undefined)"
  unfolding merge_def by auto

lemma PiE_cancel_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow>
    merge I J (x, y) \<in> Pi\<^sub>E (I \<union> J) B \<longleftrightarrow> x \<in> Pi I B \<and> y \<in> Pi J B"
  by (auto simp: PiE_def restrict_Pi_cancel)

lemma merge_singleton[simp]: "i \<notin> I \<Longrightarrow> merge I {i} (x,y) = restrict (x(i := y i)) (insert i I)"
  unfolding merge_def by (auto simp: fun_eq_iff)

lemma extensional_merge_sub: "I \<union> J \<subseteq> K \<Longrightarrow> merge I J (x, y) \<in> extensional K"
  unfolding merge_def extensional_def by auto

lemma merge_restrict[simp]:
  "merge I J (restrict x I, y) = merge I J (x, y)"
  "merge I J (x, restrict y J) = merge I J (x, y)"
  unfolding merge_def by auto

lemma merge_x_x_eq_restrict[simp]:
  "merge I J (x, x) = restrict x (I \<union> J)"
  unfolding merge_def by auto

lemma injective_vimage_restrict:
  assumes J: "J \<subseteq> I"
  and sets: "A \<subseteq> (\<Pi>\<^sub>E i\<in>J. S i)" "B \<subseteq> (\<Pi>\<^sub>E i\<in>J. S i)" and ne: "(\<Pi>\<^sub>E i\<in>I. S i) \<noteq> {}"
  and eq: "(\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. S i) = (\<lambda>x. restrict x J) -` B \<inter> (\<Pi>\<^sub>E i\<in>I. S i)"
  shows "A = B"
proof  (intro set_eqI)
  fix x
  from ne obtain y where y: "\<And>i. i \<in> I \<Longrightarrow> y i \<in> S i" by auto
  have "J \<inter> (I - J) = {}" by auto
  show "x \<in> A \<longleftrightarrow> x \<in> B"
  proof cases
    assume x: "x \<in> (\<Pi>\<^sub>E i\<in>J. S i)"
    have "x \<in> A \<longleftrightarrow> merge J (I - J) (x,y) \<in> (\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. S i)"
      using y x \<open>J \<subseteq> I\<close> PiE_cancel_merge[of "J" "I - J" x y S]
      by (auto simp del: PiE_cancel_merge simp add: Un_absorb1)
    then show "x \<in> A \<longleftrightarrow> x \<in> B"
      using y x \<open>J \<subseteq> I\<close> PiE_cancel_merge[of "J" "I - J" x y S]
      by (auto simp del: PiE_cancel_merge simp add: Un_absorb1 eq)
  qed (insert sets, auto)
qed

lemma restrict_vimage:
  "I \<inter> J = {} \<Longrightarrow>
    (\<lambda>x. (restrict x I, restrict x J)) -` (Pi\<^sub>E I E \<times> Pi\<^sub>E J F) = Pi (I \<union> J) (merge I J (E, F))"
  by (auto simp: restrict_Pi_cancel PiE_def)

lemma merge_vimage:
  "I \<inter> J = {} \<Longrightarrow> merge I J -` Pi\<^sub>E (I \<union> J) E = Pi I E \<times> Pi J E"
  by (auto simp: restrict_Pi_cancel PiE_def)

subsection \<open>Finite product spaces\<close>

definition\<^marker>\<open>tag important\<close> prod_emb where
  "prod_emb I M K X = (\<lambda>x. restrict x K) -` X \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i))"

lemma prod_emb_iff:
  "f \<in> prod_emb I M K X \<longleftrightarrow> f \<in> extensional I \<and> (restrict f K \<in> X) \<and> (\<forall>i\<in>I. f i \<in> space (M i))"
  unfolding prod_emb_def PiE_def by auto

lemma
  shows prod_emb_empty[simp]: "prod_emb M L K {} = {}"
    and prod_emb_Un[simp]: "prod_emb M L K (A \<union> B) = prod_emb M L K A \<union> prod_emb M L K B"
    and prod_emb_Int: "prod_emb M L K (A \<inter> B) = prod_emb M L K A \<inter> prod_emb M L K B"
    and prod_emb_UN[simp]: "prod_emb M L K (\<Union>i\<in>I. F i) = (\<Union>i\<in>I. prod_emb M L K (F i))"
    and prod_emb_INT[simp]: "I \<noteq> {} \<Longrightarrow> prod_emb M L K (\<Inter>i\<in>I. F i) = (\<Inter>i\<in>I. prod_emb M L K (F i))"
    and prod_emb_Diff[simp]: "prod_emb M L K (A - B) = prod_emb M L K A - prod_emb M L K B"
  by (auto simp: prod_emb_def)

lemma prod_emb_PiE: "J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> E i \<subseteq> space (M i)) \<Longrightarrow>
    prod_emb I M J (\<Pi>\<^sub>E i\<in>J. E i) = (\<Pi>\<^sub>E i\<in>I. if i \<in> J then E i else space (M i))"
  by (force simp: prod_emb_def PiE_iff if_split_mem2)

lemma prod_emb_PiE_same_index[simp]:
    "(\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> space (M i)) \<Longrightarrow> prod_emb I M I (Pi\<^sub>E I E) = Pi\<^sub>E I E"
  by (auto simp: prod_emb_def PiE_iff)

lemma prod_emb_trans[simp]:
  "J \<subseteq> K \<Longrightarrow> K \<subseteq> L \<Longrightarrow> prod_emb L M K (prod_emb K M J X) = prod_emb L M J X"
  by (auto simp add: Int_absorb1 prod_emb_def PiE_def)

lemma prod_emb_Pi:
  assumes "X \<in> (\<Pi> j\<in>J. sets (M j))" "J \<subseteq> K"
  shows "prod_emb K M J (Pi\<^sub>E J X) = (\<Pi>\<^sub>E i\<in>K. if i \<in> J then X i else space (M i))"
  using assms sets.space_closed
  by (auto simp: prod_emb_def PiE_iff split: if_split_asm) blast+

lemma prod_emb_id:
  "B \<subseteq> (\<Pi>\<^sub>E i\<in>L. space (M i)) \<Longrightarrow> prod_emb L M L B = B"
  by (auto simp: prod_emb_def subset_eq extensional_restrict)

lemma prod_emb_mono:
  "F \<subseteq> G \<Longrightarrow> prod_emb A M B F \<subseteq> prod_emb A M B G"
  by (auto simp: prod_emb_def)

definition\<^marker>\<open>tag important\<close> PiM :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<Rightarrow> 'a) measure" where
  "PiM I M = extend_measure (\<Pi>\<^sub>E i\<in>I. space (M i))
    {(J, X). (J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}
    (\<lambda>(J, X). prod_emb I M J (\<Pi>\<^sub>E j\<in>J. X j))
    (\<lambda>(J, X). \<Prod>j\<in>J \<union> {i\<in>I. emeasure (M i) (space (M i)) \<noteq> 1}. if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j)))"

definition\<^marker>\<open>tag important\<close> prod_algebra :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<Rightarrow> 'a) set set" where
  "prod_algebra I M = (\<lambda>(J, X). prod_emb I M J (\<Pi>\<^sub>E j\<in>J. X j)) `
    {(J, X). (J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}"

abbreviation
  "Pi\<^sub>M I M \<equiv> PiM I M"

syntax
  "_PiM" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a measure \<Rightarrow> ('i => 'a) measure"  ("(3\<Pi>\<^sub>M _\<in>_./ _)"  10)
translations
  "\<Pi>\<^sub>M x\<in>I. M" == "CONST PiM I (%x. M)"

lemma extend_measure_cong:
  assumes "\<Omega> = \<Omega>'" "I = I'" "G = G'" "\<And>i. i \<in> I' \<Longrightarrow> \<mu> i = \<mu>' i"
  shows "extend_measure \<Omega> I G \<mu> = extend_measure \<Omega>' I' G' \<mu>'"
  unfolding extend_measure_def by (auto simp add: assms)

lemma Pi_cong_sets:
    "\<lbrakk>I = J; \<And>x. x \<in> I \<Longrightarrow> M x = N x\<rbrakk> \<Longrightarrow> Pi I M = Pi J N"
  unfolding Pi_def by auto

lemma PiM_cong:
  assumes "I = J" "\<And>x. x \<in> I \<Longrightarrow> M x = N x"
  shows "PiM I M = PiM J N"
  unfolding PiM_def
proof (rule extend_measure_cong, goal_cases)
  case 1
  show ?case using assms
    by (subst assms(1), intro PiE_cong[of J "\<lambda>i. space (M i)" "\<lambda>i. space (N i)"]) simp_all
next
  case 2
  have "\<And>K. K \<subseteq> J \<Longrightarrow> (\<Pi> j\<in>K. sets (M j)) = (\<Pi> j\<in>K. sets (N j))"
    using assms by (intro Pi_cong_sets) auto
  thus ?case by (auto simp: assms)
next
  case 3
  show ?case using assms
    by (intro ext) (auto simp: prod_emb_def dest: PiE_mem)
next
  case (4 x)
  thus ?case using assms
    by (auto intro!: prod.cong split: if_split_asm)
qed


lemma prod_algebra_sets_into_space:
  "prod_algebra I M \<subseteq> Pow (\<Pi>\<^sub>E i\<in>I. space (M i))"
  by (auto simp: prod_emb_def prod_algebra_def)

lemma prod_algebra_eq_finite:
  assumes I: "finite I"
  shows "prod_algebra I M = {(\<Pi>\<^sub>E i\<in>I. X i) |X. X \<in> (\<Pi> j\<in>I. sets (M j))}" (is "?L = ?R")
proof (intro iffI set_eqI)
  fix A assume "A \<in> ?L"
  then obtain J E where J: "J \<noteq> {} \<or> I = {}" "finite J" "J \<subseteq> I" "\<forall>i\<in>J. E i \<in> sets (M i)"
    and A: "A = prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j)"
    by (auto simp: prod_algebra_def)
  let ?A = "\<Pi>\<^sub>E i\<in>I. if i \<in> J then E i else space (M i)"
  have A: "A = ?A"
    unfolding A using J by (intro prod_emb_PiE sets.sets_into_space) auto
  show "A \<in> ?R" unfolding A using J sets.top
    by (intro CollectI exI[of _ "\<lambda>i. if i \<in> J then E i else space (M i)"]) simp
next
  fix A assume "A \<in> ?R"
  then obtain X where A: "A = (\<Pi>\<^sub>E i\<in>I. X i)" and X: "X \<in> (\<Pi> j\<in>I. sets (M j))" by auto
  then have A: "A = prod_emb I M I (\<Pi>\<^sub>E i\<in>I. X i)"
    by (simp add: prod_emb_PiE_same_index[OF sets.sets_into_space] Pi_iff)
  from X I show "A \<in> ?L" unfolding A
    by (auto simp: prod_algebra_def)
qed

lemma prod_algebraI:
  "finite J \<Longrightarrow> (J \<noteq> {} \<or> I = {}) \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> E i \<in> sets (M i))
    \<Longrightarrow> prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j) \<in> prod_algebra I M"
  by (auto simp: prod_algebra_def)

lemma prod_algebraI_finite:
  "finite I \<Longrightarrow> (\<forall>i\<in>I. E i \<in> sets (M i)) \<Longrightarrow> (Pi\<^sub>E I E) \<in> prod_algebra I M"
  using prod_algebraI[of I I E M] prod_emb_PiE_same_index[of I E M, OF sets.sets_into_space] by simp

lemma Int_stable_PiE: "Int_stable {Pi\<^sub>E J E | E. \<forall>i\<in>I. E i \<in> sets (M i)}"
proof (safe intro!: Int_stableI)
  fix E F assume "\<forall>i\<in>I. E i \<in> sets (M i)" "\<forall>i\<in>I. F i \<in> sets (M i)"
  then show "\<exists>G. Pi\<^sub>E J E \<inter> Pi\<^sub>E J F = Pi\<^sub>E J G \<and> (\<forall>i\<in>I. G i \<in> sets (M i))"
    by (auto intro!: exI[of _ "\<lambda>i. E i \<inter> F i"] simp: PiE_Int)
qed

lemma prod_algebraE:
  assumes A: "A \<in> prod_algebra I M"
  obtains J E where "A = prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j)"
    "finite J" "J \<noteq> {} \<or> I = {}" "J \<subseteq> I" "\<And>i. i \<in> J \<Longrightarrow> E i \<in> sets (M i)"
  using A by (auto simp: prod_algebra_def)

lemma prod_algebraE_all:
  assumes A: "A \<in> prod_algebra I M"
  obtains E where "A = Pi\<^sub>E I E" "E \<in> (\<Pi> i\<in>I. sets (M i))"
proof -
  from A obtain E J where A: "A = prod_emb I M J (Pi\<^sub>E J E)"
    and J: "J \<subseteq> I" and E: "E \<in> (\<Pi> i\<in>J. sets (M i))"
    by (auto simp: prod_algebra_def)
  from E have "\<And>i. i \<in> J \<Longrightarrow> E i \<subseteq> space (M i)"
    using sets.sets_into_space by auto
  then have "A = (\<Pi>\<^sub>E i\<in>I. if i\<in>J then E i else space (M i))"
    using A J by (auto simp: prod_emb_PiE)
  moreover have "(\<lambda>i. if i\<in>J then E i else space (M i)) \<in> (\<Pi> i\<in>I. sets (M i))"
    using sets.top E by auto
  ultimately show ?thesis using that by auto
qed

lemma Int_stable_prod_algebra: "Int_stable (prod_algebra I M)"
  unfolding Int_stable_def
proof safe
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] obtain J E where A:
    "A = prod_emb I M J (Pi\<^sub>E J E)"
    "finite J"
    "J \<noteq> {} \<or> I = {}"
    "J \<subseteq> I"
    "\<And>i. i \<in> J \<Longrightarrow> E i \<in> sets (M i)"
    by auto
  fix B assume "B \<in> prod_algebra I M"
  from prod_algebraE[OF this] obtain K F where B:
    "B = prod_emb I M K (Pi\<^sub>E K F)"
    "finite K"
    "K \<noteq> {} \<or> I = {}"
    "K \<subseteq> I"
    "\<And>i. i \<in> K \<Longrightarrow> F i \<in> sets (M i)"
    by auto
  have "A \<inter> B = prod_emb I M (J \<union> K) (\<Pi>\<^sub>E i\<in>J \<union> K. (if i \<in> J then E i else space (M i)) \<inter>
      (if i \<in> K then F i else space (M i)))"
    unfolding A B using A(2,3,4) A(5)[THEN sets.sets_into_space] B(2,3,4)
      B(5)[THEN sets.sets_into_space]
    apply (subst (1 2 3) prod_emb_PiE)
    apply (simp_all add: subset_eq PiE_Int)
    apply blast
    apply (intro PiE_cong)
    apply auto
    done
  also have "\<dots> \<in> prod_algebra I M"
    using A B by (auto intro!: prod_algebraI)
  finally show "A \<inter> B \<in> prod_algebra I M" .
qed

proposition prod_algebra_mono:
  assumes space: "\<And>i. i \<in> I \<Longrightarrow> space (E i) = space (F i)"
  assumes sets: "\<And>i. i \<in> I \<Longrightarrow> sets (E i) \<subseteq> sets (F i)"
  shows "prod_algebra I E \<subseteq> prod_algebra I F"
proof
  fix A assume "A \<in> prod_algebra I E"
  then obtain J G where J: "J \<noteq> {} \<or> I = {}" "finite J" "J \<subseteq> I"
    and A: "A = prod_emb I E J (\<Pi>\<^sub>E i\<in>J. G i)"
    and G: "\<And>i. i \<in> J \<Longrightarrow> G i \<in> sets (E i)"
    by (auto simp: prod_algebra_def)
  moreover
  from space have "(\<Pi>\<^sub>E i\<in>I. space (E i)) = (\<Pi>\<^sub>E i\<in>I. space (F i))"
    by (rule PiE_cong)
  with A have "A = prod_emb I F J (\<Pi>\<^sub>E i\<in>J. G i)"
    by (simp add: prod_emb_def)
  moreover
  from sets G J have "\<And>i. i \<in> J \<Longrightarrow> G i \<in> sets (F i)"
    by auto
  ultimately show "A \<in> prod_algebra I F"
    apply (simp add: prod_algebra_def image_iff)
    apply (intro exI[of _ J] exI[of _ G] conjI)
    apply auto
    done
qed
proposition prod_algebra_cong:
  assumes "I = J" and sets: "(\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets (N i))"
  shows "prod_algebra I M = prod_algebra J N"
proof -
  have space: "\<And>i. i \<in> I \<Longrightarrow> space (M i) = space (N i)"
    using sets_eq_imp_space_eq[OF sets] by auto
  with sets show ?thesis unfolding \<open>I = J\<close>
    by (intro antisym prod_algebra_mono) auto
qed

lemma space_in_prod_algebra:
  "(\<Pi>\<^sub>E i\<in>I. space (M i)) \<in> prod_algebra I M"
proof cases
  assume "I = {}" then show ?thesis
    by (auto simp add: prod_algebra_def image_iff prod_emb_def)
next
  assume "I \<noteq> {}"
  then obtain i where "i \<in> I" by auto
  then have "(\<Pi>\<^sub>E i\<in>I. space (M i)) = prod_emb I M {i} (\<Pi>\<^sub>E i\<in>{i}. space (M i))"
    by (auto simp: prod_emb_def)
  also have "\<dots> \<in> prod_algebra I M"
    using \<open>i \<in> I\<close> by (intro prod_algebraI) auto
  finally show ?thesis .
qed

lemma space_PiM: "space (\<Pi>\<^sub>M i\<in>I. M i) = (\<Pi>\<^sub>E i\<in>I. space (M i))"
  using prod_algebra_sets_into_space unfolding PiM_def prod_algebra_def by (intro space_extend_measure) simp

lemma prod_emb_subset_PiM[simp]: "prod_emb I M K X \<subseteq> space (PiM I M)"
  by (auto simp: prod_emb_def space_PiM)

lemma space_PiM_empty_iff[simp]: "space (PiM I M) = {} \<longleftrightarrow>  (\<exists>i\<in>I. space (M i) = {})"
  by (auto simp: space_PiM PiE_eq_empty_iff)

lemma undefined_in_PiM_empty[simp]: "(\<lambda>x. undefined) \<in> space (PiM {} M)"
  by (auto simp: space_PiM)

lemma sets_PiM: "sets (\<Pi>\<^sub>M i\<in>I. M i) = sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) (prod_algebra I M)"
  using prod_algebra_sets_into_space unfolding PiM_def prod_algebra_def by (intro sets_extend_measure) simp

proposition sets_PiM_single: "sets (PiM I M) =
    sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) {{f\<in>\<Pi>\<^sub>E i\<in>I. space (M i). f i \<in> A} | i A. i \<in> I \<and> A \<in> sets (M i)}"
    (is "_ = sigma_sets ?\<Omega> ?R")
  unfolding sets_PiM
proof (rule sigma_sets_eqI)
  interpret R: sigma_algebra ?\<Omega> "sigma_sets ?\<Omega> ?R" by (rule sigma_algebra_sigma_sets) auto
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] obtain J X where X:
    "A = prod_emb I M J (Pi\<^sub>E J X)"
    "finite J"
    "J \<noteq> {} \<or> I = {}"
    "J \<subseteq> I"
    "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
    by auto
  show "A \<in> sigma_sets ?\<Omega> ?R"
  proof cases
    assume "I = {}"
    with X have "A = {\<lambda>x. undefined}" by (auto simp: prod_emb_def)
    with \<open>I = {}\<close> show ?thesis by (auto intro!: sigma_sets_top)
  next
    assume "I \<noteq> {}"
    with X have "A = (\<Inter>j\<in>J. {f\<in>(\<Pi>\<^sub>E i\<in>I. space (M i)). f j \<in> X j})"
      by (auto simp: prod_emb_def)
    also have "\<dots> \<in> sigma_sets ?\<Omega> ?R"
      using X \<open>I \<noteq> {}\<close> by (intro R.finite_INT sigma_sets.Basic) auto
    finally show "A \<in> sigma_sets ?\<Omega> ?R" .
  qed
next
  fix A assume "A \<in> ?R"
  then obtain i B where A: "A = {f\<in>\<Pi>\<^sub>E i\<in>I. space (M i). f i \<in> B}" "i \<in> I" "B \<in> sets (M i)"
    by auto
  then have "A = prod_emb I M {i} (\<Pi>\<^sub>E i\<in>{i}. B)"
     by (auto simp: prod_emb_def)
  also have "\<dots> \<in> sigma_sets ?\<Omega> (prod_algebra I M)"
    using A by (intro sigma_sets.Basic prod_algebraI) auto
  finally show "A \<in> sigma_sets ?\<Omega> (prod_algebra I M)" .
qed

lemma sets_PiM_eq_proj:
  "I \<noteq> {} \<Longrightarrow> sets (PiM I M) = sets (SUP i\<in>I. vimage_algebra (\<Pi>\<^sub>E i\<in>I. space (M i)) (\<lambda>x. x i) (M i))"
  apply (simp add: sets_PiM_single)
  apply (subst sets_Sup_eq[where X="\<Pi>\<^sub>E i\<in>I. space (M i)"])
  apply auto []
  apply auto []
  apply simp
  apply (subst arg_cong [of _ _ Sup, OF image_cong, OF refl])
  apply (rule sets_vimage_algebra2)
  apply (auto intro!: arg_cong2[where f=sigma_sets])
  done

lemma
  shows space_PiM_empty: "space (Pi\<^sub>M {} M) = {\<lambda>k. undefined}"
    and sets_PiM_empty: "sets (Pi\<^sub>M {} M) = { {}, {\<lambda>k. undefined} }"
  by (simp_all add: space_PiM sets_PiM_single image_constant sigma_sets_empty_eq)

proposition sets_PiM_sigma:
  assumes \<Omega>_cover: "\<And>i. i \<in> I \<Longrightarrow> \<exists>S\<subseteq>E i. countable S \<and> \<Omega> i = \<Union>S"
  assumes E: "\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> Pow (\<Omega> i)"
  assumes J: "\<And>j. j \<in> J \<Longrightarrow> finite j" "\<Union>J = I"
  defines "P \<equiv> {{f\<in>(\<Pi>\<^sub>E i\<in>I. \<Omega> i). \<forall>i\<in>j. f i \<in> A i} | A j. j \<in> J \<and> A \<in> Pi j E}"
  shows "sets (\<Pi>\<^sub>M i\<in>I. sigma (\<Omega> i) (E i)) = sets (sigma (\<Pi>\<^sub>E i\<in>I. \<Omega> i) P)"
proof cases
  assume "I = {}"
  with \<open>\<Union>J = I\<close> have "P = {{\<lambda>_. undefined}} \<or> P = {}"
    by (auto simp: P_def)
  with \<open>I = {}\<close> show ?thesis
    by (auto simp add: sets_PiM_empty sigma_sets_empty_eq)
next
  let ?F = "\<lambda>i. {(\<lambda>x. x i) -` A \<inter> Pi\<^sub>E I \<Omega> |A. A \<in> E i}"
  assume "I \<noteq> {}"
  then have "sets (Pi\<^sub>M I (\<lambda>i. sigma (\<Omega> i) (E i))) =
      sets (SUP i\<in>I. vimage_algebra (\<Pi>\<^sub>E i\<in>I. \<Omega> i) (\<lambda>x. x i) (sigma (\<Omega> i) (E i)))"
    by (subst sets_PiM_eq_proj) (auto simp: space_measure_of_conv)
  also have "\<dots> = sets (SUP i\<in>I. sigma (Pi\<^sub>E I \<Omega>) (?F i))"
    using E by (intro sets_SUP_cong arg_cong[where f=sets] vimage_algebra_sigma) auto
  also have "\<dots> = sets (sigma (Pi\<^sub>E I \<Omega>) (\<Union>i\<in>I. ?F i))"
    using \<open>I \<noteq> {}\<close> by (intro arg_cong[where f=sets] SUP_sigma_sigma) auto
  also have "\<dots> = sets (sigma (Pi\<^sub>E I \<Omega>) P)"
  proof (intro arg_cong[where f=sets] sigma_eqI sigma_sets_eqI)
    show "(\<Union>i\<in>I. ?F i) \<subseteq> Pow (Pi\<^sub>E I \<Omega>)" "P \<subseteq> Pow (Pi\<^sub>E I \<Omega>)"
      by (auto simp: P_def)
  next
    interpret P: sigma_algebra "\<Pi>\<^sub>E i\<in>I. \<Omega> i" "sigma_sets (\<Pi>\<^sub>E i\<in>I. \<Omega> i) P"
      by (auto intro!: sigma_algebra_sigma_sets simp: P_def)

    fix Z assume "Z \<in> (\<Union>i\<in>I. ?F i)"
    then obtain i A where i: "i \<in> I" "A \<in> E i" and Z_def: "Z = (\<lambda>x. x i) -` A \<inter> Pi\<^sub>E I \<Omega>"
      by auto
    from \<open>i \<in> I\<close> J obtain j where j: "i \<in> j" "j \<in> J" "j \<subseteq> I" "finite j"
      by auto
    obtain S where S: "\<And>i. i \<in> j \<Longrightarrow> S i \<subseteq> E i" "\<And>i. i \<in> j \<Longrightarrow> countable (S i)"
      "\<And>i. i \<in> j \<Longrightarrow> \<Omega> i = \<Union>(S i)"
      by (metis subset_eq \<Omega>_cover \<open>j \<subseteq> I\<close>)
    define A' where "A' n = n(i := A)" for n
    then have A'_i: "\<And>n. A' n i = A"
      by simp
    { fix n assume "n \<in> Pi\<^sub>E (j - {i}) S"
      then have "A' n \<in> Pi j E"
        unfolding PiE_def Pi_def using S(1) by (auto simp: A'_def \<open>A \<in> E i\<close> )
      with \<open>j \<in> J\<close> have "{f \<in> Pi\<^sub>E I \<Omega>. \<forall>i\<in>j. f i \<in> A' n i} \<in> P"
        by (auto simp: P_def) }
    note A'_in_P = this

    { fix x assume "x i \<in> A" "x \<in> Pi\<^sub>E I \<Omega>"
      with S(3) \<open>j \<subseteq> I\<close> have "\<forall>i\<in>j. \<exists>s\<in>S i. x i \<in> s"
        by (auto simp: PiE_def Pi_def)
      then obtain s where s: "\<And>i. i \<in> j \<Longrightarrow> s i \<in> S i" "\<And>i. i \<in> j \<Longrightarrow> x i \<in> s i"
        by metis
      with \<open>x i \<in> A\<close> have "\<exists>n\<in>Pi\<^sub>E (j-{i}) S. \<forall>i\<in>j. x i \<in> A' n i"
        by (intro bexI[of _ "restrict (s(i := A)) (j-{i})"]) (auto simp: A'_def split: if_splits) }
    then have "Z = (\<Union>n\<in>Pi\<^sub>E (j-{i}) S. {f\<in>(\<Pi>\<^sub>E i\<in>I. \<Omega> i). \<forall>i\<in>j. f i \<in> A' n i})"
      unfolding Z_def
      by (auto simp add: set_eq_iff ball_conj_distrib \<open>i\<in>j\<close> A'_i dest: bspec[OF _ \<open>i\<in>j\<close>]
               cong: conj_cong)
    also have "\<dots> \<in> sigma_sets (\<Pi>\<^sub>E i\<in>I. \<Omega> i) P"
      using \<open>finite j\<close> S(2)
      by (intro P.countable_UN' countable_PiE) (simp_all add: image_subset_iff A'_in_P)
    finally show "Z \<in> sigma_sets (\<Pi>\<^sub>E i\<in>I. \<Omega> i) P" .
  next
    interpret F: sigma_algebra "\<Pi>\<^sub>E i\<in>I. \<Omega> i" "sigma_sets (\<Pi>\<^sub>E i\<in>I. \<Omega> i) (\<Union>i\<in>I. ?F i)"
      by (auto intro!: sigma_algebra_sigma_sets)

    fix b assume "b \<in> P"
    then obtain A j where b: "b = {f\<in>(\<Pi>\<^sub>E i\<in>I. \<Omega> i). \<forall>i\<in>j. f i \<in> A i}" "j \<in> J" "A \<in> Pi j E"
      by (auto simp: P_def)
    show "b \<in> sigma_sets (Pi\<^sub>E I \<Omega>) (\<Union>i\<in>I. ?F i)"
    proof cases
      assume "j = {}"
      with b have "b = (\<Pi>\<^sub>E i\<in>I. \<Omega> i)"
        by auto
      then show ?thesis
        by blast
    next
      assume "j \<noteq> {}"
      with J b(2,3) have eq: "b = (\<Inter>i\<in>j. ((\<lambda>x. x i) -` A i \<inter> Pi\<^sub>E I \<Omega>))"
        unfolding b(1)
        by (auto simp: PiE_def Pi_def)
      show ?thesis
        unfolding eq using \<open>A \<in> Pi j E\<close> \<open>j \<in> J\<close> J(2)
        by (intro F.finite_INT J \<open>j \<in> J\<close> \<open>j \<noteq> {}\<close> sigma_sets.Basic) blast
    qed
  qed
  finally show "?thesis" .
qed

lemma sets_PiM_in_sets:
  assumes space: "space N = (\<Pi>\<^sub>E i\<in>I. space (M i))"
  assumes sets: "\<And>i A. i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow> {x\<in>space N. x i \<in> A} \<in> sets N"
  shows "sets (\<Pi>\<^sub>M i \<in> I. M i) \<subseteq> sets N"
  unfolding sets_PiM_single space[symmetric]
  by (intro sets.sigma_sets_subset subsetI) (auto intro: sets)

lemma sets_PiM_cong[measurable_cong]:
  assumes "I = J" "\<And>i. i \<in> J \<Longrightarrow> sets (M i) = sets (N i)" shows "sets (PiM I M) = sets (PiM J N)"
  using assms sets_eq_imp_space_eq[OF assms(2)] by (simp add: sets_PiM_single cong: PiE_cong conj_cong)

lemma sets_PiM_I:
  assumes "finite J" "J \<subseteq> I" "\<forall>i\<in>J. E i \<in> sets (M i)"
  shows "prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j) \<in> sets (\<Pi>\<^sub>M i\<in>I. M i)"
proof cases
  assume "J = {}"
  then have "prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j) = (\<Pi>\<^sub>E j\<in>I. space (M j))"
    by (auto simp: prod_emb_def)
  then show ?thesis
    by (auto simp add: sets_PiM intro!: sigma_sets_top)
next
  assume "J \<noteq> {}" with assms show ?thesis
    by (force simp add: sets_PiM prod_algebra_def)
qed

proposition measurable_PiM:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^sub>E i\<in>I. space (M i))"
  assumes sets: "\<And>X J. J \<noteq> {} \<or> I = {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)) \<Longrightarrow>
    f -` prod_emb I M J (Pi\<^sub>E J X) \<inter> space N \<in> sets N"
  shows "f \<in> measurable N (PiM I M)"
  using sets_PiM prod_algebra_sets_into_space space
proof (rule measurable_sigma_sets)
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] obtain J X where
    "A = prod_emb I M J (Pi\<^sub>E J X)"
    "finite J"
    "J \<noteq> {} \<or> I = {}"
    "J \<subseteq> I"
    "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
    by auto
  with sets[of J X] show "f -` A \<inter> space N \<in> sets N" by auto
qed

lemma measurable_PiM_Collect:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^sub>E i\<in>I. space (M i))"
  assumes sets: "\<And>X J. J \<noteq> {} \<or> I = {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)) \<Longrightarrow>
    {\<omega>\<in>space N. \<forall>i\<in>J. f \<omega> i \<in> X i} \<in> sets N"
  shows "f \<in> measurable N (PiM I M)"
  using sets_PiM prod_algebra_sets_into_space space
proof (rule measurable_sigma_sets)
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] obtain J X
    where X:
      "A = prod_emb I M J (Pi\<^sub>E J X)"
      "finite J"
      "J \<noteq> {} \<or> I = {}"
      "J \<subseteq> I"
      "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
    by auto
  then have "f -` A \<inter> space N = {\<omega> \<in> space N. \<forall>i\<in>J. f \<omega> i \<in> X i}"
    using space by (auto simp: prod_emb_def del: PiE_I)
  also have "\<dots> \<in> sets N" using X(3,2,4,5) by (rule sets)
  finally show "f -` A \<inter> space N \<in> sets N" .
qed

lemma measurable_PiM_single:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^sub>E i\<in>I. space (M i))"
  assumes sets: "\<And>A i. i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow> {\<omega> \<in> space N. f \<omega> i \<in> A} \<in> sets N"
  shows "f \<in> measurable N (PiM I M)"
  using sets_PiM_single
proof (rule measurable_sigma_sets)
  fix A assume "A \<in> {{f \<in> \<Pi>\<^sub>E i\<in>I. space (M i). f i \<in> A} |i A. i \<in> I \<and> A \<in> sets (M i)}"
  then obtain B i where "A = {f \<in> \<Pi>\<^sub>E i\<in>I. space (M i). f i \<in> B}" and B: "i \<in> I" "B \<in> sets (M i)"
    by auto
  with space have "f -` A \<inter> space N = {\<omega> \<in> space N. f \<omega> i \<in> B}" by auto
  also have "\<dots> \<in> sets N" using B by (rule sets)
  finally show "f -` A \<inter> space N \<in> sets N" .
qed (auto simp: space)

lemma measurable_PiM_single':
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> measurable N (M i)"
    and "(\<lambda>\<omega> i. f i \<omega>) \<in> space N \<rightarrow> (\<Pi>\<^sub>E i\<in>I. space (M i))"
  shows "(\<lambda>\<omega> i. f i \<omega>) \<in> measurable N (Pi\<^sub>M I M)"
proof (rule measurable_PiM_single)
  fix A i assume A: "i \<in> I" "A \<in> sets (M i)"
  then have "{\<omega> \<in> space N. f i \<omega> \<in> A} = f i -` A \<inter> space N"
    by auto
  then show "{\<omega> \<in> space N. f i \<omega> \<in> A} \<in> sets N"
    using A f by (auto intro!: measurable_sets)
qed fact

lemma sets_PiM_I_finite[measurable]:
  assumes "finite I" and sets: "(\<And>i. i \<in> I \<Longrightarrow> E i \<in> sets (M i))"
  shows "(\<Pi>\<^sub>E j\<in>I. E j) \<in> sets (\<Pi>\<^sub>M i\<in>I. M i)"
  using sets_PiM_I[of I I E M] sets.sets_into_space[OF sets] \<open>finite I\<close> sets by auto

lemma measurable_component_singleton[measurable (raw)]:
  assumes "i \<in> I" shows "(\<lambda>x. x i) \<in> measurable (Pi\<^sub>M I M) (M i)"
proof (unfold measurable_def, intro CollectI conjI ballI)
  fix A assume "A \<in> sets (M i)"
  then have "(\<lambda>x. x i) -` A \<inter> space (Pi\<^sub>M I M) = prod_emb I M {i} (\<Pi>\<^sub>E j\<in>{i}. A)"
    using sets.sets_into_space \<open>i \<in> I\<close>
    by (fastforce dest: Pi_mem simp: prod_emb_def space_PiM split: if_split_asm)
  then show "(\<lambda>x. x i) -` A \<inter> space (Pi\<^sub>M I M) \<in> sets (Pi\<^sub>M I M)"
    using \<open>A \<in> sets (M i)\<close> \<open>i \<in> I\<close> by (auto intro!: sets_PiM_I)
qed (insert \<open>i \<in> I\<close>, auto simp: space_PiM)

lemma measurable_component_singleton'[measurable_dest]:
  assumes f: "f \<in> measurable N (Pi\<^sub>M I M)"
  assumes g: "g \<in> measurable L N"
  assumes i: "i \<in> I"
  shows "(\<lambda>x. (f (g x)) i) \<in> measurable L (M i)"
  using measurable_compose[OF measurable_compose[OF g f] measurable_component_singleton, OF i] .

lemma measurable_PiM_component_rev:
  "i \<in> I \<Longrightarrow> f \<in> measurable (M i) N \<Longrightarrow> (\<lambda>x. f (x i)) \<in> measurable (PiM I M) N"
  by simp

lemma measurable_case_nat[measurable (raw)]:
  assumes [measurable (raw)]: "i = 0 \<Longrightarrow> f \<in> measurable M N"
    "\<And>j. i = Suc j \<Longrightarrow> (\<lambda>x. g x j) \<in> measurable M N"
  shows "(\<lambda>x. case_nat (f x) (g x) i) \<in> measurable M N"
  by (cases i) simp_all

lemma measurable_case_nat'[measurable (raw)]:
  assumes fg[measurable]: "f \<in> measurable N M" "g \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)"
  shows "(\<lambda>x. case_nat (f x) (g x)) \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)"
  using fg[THEN measurable_space]
  by (auto intro!: measurable_PiM_single' simp add: space_PiM PiE_iff split: nat.split)

lemma measurable_add_dim[measurable]:
  "(\<lambda>(f, y). f(i := y)) \<in> measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M M i) (Pi\<^sub>M (insert i I) M)"
    (is "?f \<in> measurable ?P ?I")
proof (rule measurable_PiM_single)
  fix j A assume j: "j \<in> insert i I" and A: "A \<in> sets (M j)"
  have "{\<omega> \<in> space ?P. (\<lambda>(f, x). fun_upd f i x) \<omega> j \<in> A} =
    (if j = i then space (Pi\<^sub>M I M) \<times> A else ((\<lambda>x. x j) \<circ> fst) -` A \<inter> space ?P)"
    using sets.sets_into_space[OF A] by (auto simp add: space_pair_measure space_PiM)
  also have "\<dots> \<in> sets ?P"
    using A j
    by (auto intro!: measurable_sets[OF measurable_comp, OF _ measurable_component_singleton])
  finally show "{\<omega> \<in> space ?P. case_prod (\<lambda>f. fun_upd f i) \<omega> j \<in> A} \<in> sets ?P" .
qed (auto simp: space_pair_measure space_PiM PiE_def)

proposition measurable_fun_upd:
  assumes I: "I = J \<union> {i}"
  assumes f[measurable]: "f \<in> measurable N (PiM J M)"
  assumes h[measurable]: "h \<in> measurable N (M i)"
  shows "(\<lambda>x. (f x) (i := h x)) \<in> measurable N (PiM I M)"
proof (intro measurable_PiM_single')
  fix j assume "j \<in> I" then show "(\<lambda>\<omega>. ((f \<omega>)(i := h \<omega>)) j) \<in> measurable N (M j)"
    unfolding I by (cases "j = i") auto
next
  show "(\<lambda>x. (f x)(i := h x)) \<in> space N \<rightarrow> (\<Pi>\<^sub>E i\<in>I. space (M i))"
    using I f[THEN measurable_space] h[THEN measurable_space]
    by (auto simp: space_PiM PiE_iff extensional_def)
qed

lemma measurable_component_update:
  "x \<in> space (Pi\<^sub>M I M) \<Longrightarrow> i \<notin> I \<Longrightarrow> (\<lambda>v. x(i := v)) \<in> measurable (M i) (Pi\<^sub>M (insert i I) M)"
  by simp

lemma measurable_merge[measurable]:
  "merge I J \<in> measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M) (Pi\<^sub>M (I \<union> J) M)"
    (is "?f \<in> measurable ?P ?U")
proof (rule measurable_PiM_single)
  fix i A assume A: "A \<in> sets (M i)" "i \<in> I \<union> J"
  then have "{\<omega> \<in> space ?P. merge I J \<omega> i \<in> A} =
    (if i \<in> I then ((\<lambda>x. x i) \<circ> fst) -` A \<inter> space ?P else ((\<lambda>x. x i) \<circ> snd) -` A \<inter> space ?P)"
    by (auto simp: merge_def)
  also have "\<dots> \<in> sets ?P"
    using A
    by (auto intro!: measurable_sets[OF measurable_comp, OF _ measurable_component_singleton])
  finally show "{\<omega> \<in> space ?P. merge I J \<omega> i \<in> A} \<in> sets ?P" .
qed (auto simp: space_pair_measure space_PiM PiE_iff merge_def extensional_def)

lemma measurable_restrict[measurable (raw)]:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> measurable N (M i)"
  shows "(\<lambda>x. \<lambda>i\<in>I. X i x) \<in> measurable N (Pi\<^sub>M I M)"
proof (rule measurable_PiM_single)
  fix A i assume A: "i \<in> I" "A \<in> sets (M i)"
  then have "{\<omega> \<in> space N. (\<lambda>i\<in>I. X i \<omega>) i \<in> A} = X i -` A \<inter> space N"
    by auto
  then show "{\<omega> \<in> space N. (\<lambda>i\<in>I. X i \<omega>) i \<in> A} \<in> sets N"
    using A X by (auto intro!: measurable_sets)
qed (insert X, auto simp add: PiE_def dest: measurable_space)

lemma measurable_abs_UNIV:
  "(\<And>n. (\<lambda>\<omega>. f n \<omega>) \<in> measurable M (N n)) \<Longrightarrow> (\<lambda>\<omega> n. f n \<omega>) \<in> measurable M (PiM UNIV N)"
  by (intro measurable_PiM_single) (auto dest: measurable_space)

lemma measurable_restrict_subset: "J \<subseteq> L \<Longrightarrow> (\<lambda>f. restrict f J) \<in> measurable (Pi\<^sub>M L M) (Pi\<^sub>M J M)"
  by (intro measurable_restrict measurable_component_singleton) auto

lemma measurable_restrict_subset':
  assumes "J \<subseteq> L" "\<And>x. x \<in> J \<Longrightarrow> sets (M x) = sets (N x)"
  shows "(\<lambda>f. restrict f J) \<in> measurable (Pi\<^sub>M L M) (Pi\<^sub>M J N)"
proof-
  from assms(1) have "(\<lambda>f. restrict f J) \<in> measurable (Pi\<^sub>M L M) (Pi\<^sub>M J M)"
    by (rule measurable_restrict_subset)
  also from assms(2) have "measurable (Pi\<^sub>M L M) (Pi\<^sub>M J M) = measurable (Pi\<^sub>M L M) (Pi\<^sub>M J N)"
    by (intro sets_PiM_cong measurable_cong_sets) simp_all
  finally show ?thesis .
qed

lemma measurable_prod_emb[intro, simp]:
  "J \<subseteq> L \<Longrightarrow> X \<in> sets (Pi\<^sub>M J M) \<Longrightarrow> prod_emb L M J X \<in> sets (Pi\<^sub>M L M)"
  unfolding prod_emb_def space_PiM[symmetric]
  by (auto intro!: measurable_sets measurable_restrict measurable_component_singleton)

lemma merge_in_prod_emb:
  assumes "y \<in> space (PiM I M)" "x \<in> X" and X: "X \<in> sets (Pi\<^sub>M J M)" and "J \<subseteq> I"
  shows "merge J I (x, y) \<in> prod_emb I M J X"
  using assms sets.sets_into_space[OF X]
  by (simp add: merge_def prod_emb_def subset_eq space_PiM PiE_def extensional_restrict Pi_iff
           cong: if_cong restrict_cong)
     (simp add: extensional_def)

lemma prod_emb_eq_emptyD:
  assumes J: "J \<subseteq> I" and ne: "space (PiM I M) \<noteq> {}" and X: "X \<in> sets (Pi\<^sub>M J M)"
    and *: "prod_emb I M J X = {}"
  shows "X = {}"
proof safe
  fix x assume "x \<in> X"
  obtain \<omega> where "\<omega> \<in> space (PiM I M)"
    using ne by blast
  from merge_in_prod_emb[OF this \<open>x\<in>X\<close> X J] * show "x \<in> {}" by auto
qed

lemma sets_in_Pi_aux:
  "finite I \<Longrightarrow> (\<And>j. j \<in> I \<Longrightarrow> {x\<in>space (M j). x \<in> F j} \<in> sets (M j)) \<Longrightarrow>
  {x\<in>space (PiM I M). x \<in> Pi I F} \<in> sets (PiM I M)"
  by (simp add: subset_eq Pi_iff)

lemma sets_in_Pi[measurable (raw)]:
  "finite I \<Longrightarrow> f \<in> measurable N (PiM I M) \<Longrightarrow>
  (\<And>j. j \<in> I \<Longrightarrow> {x\<in>space (M j). x \<in> F j} \<in> sets (M j)) \<Longrightarrow>
  Measurable.pred N (\<lambda>x. f x \<in> Pi I F)"
  unfolding pred_def
  by (rule measurable_sets_Collect[of f N "PiM I M", OF _ sets_in_Pi_aux]) auto

lemma sets_in_extensional_aux:
  "{x\<in>space (PiM I M). x \<in> extensional I} \<in> sets (PiM I M)"
proof -
  have "{x\<in>space (PiM I M). x \<in> extensional I} = space (PiM I M)"
    by (auto simp add: extensional_def space_PiM)
  then show ?thesis by simp
qed

lemma sets_in_extensional[measurable (raw)]:
  "f \<in> measurable N (PiM I M) \<Longrightarrow> Measurable.pred N (\<lambda>x. f x \<in> extensional I)"
  unfolding pred_def
  by (rule measurable_sets_Collect[of f N "PiM I M", OF _ sets_in_extensional_aux]) auto

lemma sets_PiM_I_countable:
  assumes I: "countable I" and E: "\<And>i. i \<in> I \<Longrightarrow> E i \<in> sets (M i)" shows "Pi\<^sub>E I E \<in> sets (Pi\<^sub>M I M)"
proof cases
  assume "I \<noteq> {}"
  then have "Pi\<^sub>E I E = (\<Inter>i\<in>I. prod_emb I M {i} (Pi\<^sub>E {i} E))"
    using E[THEN sets.sets_into_space] by (auto simp: PiE_iff prod_emb_def fun_eq_iff)
  also have "\<dots> \<in> sets (PiM I M)"
    using I \<open>I \<noteq> {}\<close> by (safe intro!: sets.countable_INT' measurable_prod_emb sets_PiM_I_finite E)
  finally show ?thesis .
qed (simp add: sets_PiM_empty)

lemma sets_PiM_D_countable:
  assumes A: "A \<in> PiM I M"
  shows "\<exists>J\<subseteq>I. \<exists>X\<in>PiM J M. countable J \<and> A = prod_emb I M J X"
  using A[unfolded sets_PiM_single]
proof induction
  case (Basic A)
  then obtain i X where *: "i \<in> I" "X \<in> sets (M i)" and "A = {f \<in> \<Pi>\<^sub>E i\<in>I. space (M i). f i \<in> X}"
    by auto
  then have A: "A = prod_emb I M {i} (\<Pi>\<^sub>E _\<in>{i}. X)"
    by (auto simp: prod_emb_def)
  then show ?case
    by (intro exI[of _ "{i}"] conjI bexI[of _ "\<Pi>\<^sub>E _\<in>{i}. X"])
       (auto intro: countable_finite * sets_PiM_I_finite)
next
  case Empty then show ?case
    by (intro exI[of _ "{}"] conjI bexI[of _ "{}"]) auto
next
  case (Compl A)
  then obtain J X where "J \<subseteq> I" "X \<in> sets (Pi\<^sub>M J M)" "countable J" "A = prod_emb I M J X"
    by auto
  then show ?case
    by (intro exI[of _ J] bexI[of _ "space (PiM J M) - X"] conjI)
       (auto simp add: space_PiM prod_emb_PiE intro!: sets_PiM_I_countable)
next
  case (Union K)
  obtain J X where J: "\<And>i. J i \<subseteq> I" "\<And>i. countable (J i)" and X: "\<And>i. X i \<in> sets (Pi\<^sub>M (J i) M)"
    and K: "\<And>i. K i = prod_emb I M (J i) (X i)"
    by (metis Union.IH)
  show ?case
  proof (intro exI[of _ "\<Union>i. J i"] bexI[of _ "\<Union>i. prod_emb (\<Union>i. J i) M (J i) (X i)"] conjI)
    show "(\<Union>i. J i) \<subseteq> I" "countable (\<Union>i. J i)" using J by auto
    with J show "\<Union>(K ` UNIV) = prod_emb I M (\<Union>i. J i) (\<Union>i. prod_emb (\<Union>i. J i) M (J i) (X i))"
      by (simp add: K[abs_def] SUP_upper)
  qed(auto intro: X)
qed

proposition measure_eqI_PiM_finite:
  assumes [simp]: "finite I" "sets P = PiM I M" "sets Q = PiM I M"
  assumes eq: "\<And>A. (\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> P (Pi\<^sub>E I A) = Q (Pi\<^sub>E I A)"
  assumes A: "range A \<subseteq> prod_algebra I M" "(\<Union>i. A i) = space (PiM I M)" "\<And>i::nat. P (A i) \<noteq> \<infinity>"
  shows "P = Q"
proof (rule measure_eqI_generator_eq[OF Int_stable_prod_algebra prod_algebra_sets_into_space])
  show "range A \<subseteq> prod_algebra I M" "(\<Union>i. A i) = (\<Pi>\<^sub>E i\<in>I. space (M i))" "\<And>i. P (A i) \<noteq> \<infinity>"
    unfolding space_PiM[symmetric] by fact+
  fix X assume "X \<in> prod_algebra I M"
  then obtain J E where X: "X = prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j)"
    and J: "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets (M j)"
    by (force elim!: prod_algebraE)
  then show "emeasure P X = emeasure Q X"
    unfolding X by (subst (1 2) prod_emb_Pi) (auto simp: eq)
qed (simp_all add: sets_PiM)

proposition measure_eqI_PiM_infinite:
  assumes [simp]: "sets P = PiM I M" "sets Q = PiM I M"
  assumes eq: "\<And>A J. finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow>
    P (prod_emb I M J (Pi\<^sub>E J A)) = Q (prod_emb I M J (Pi\<^sub>E J A))"
  assumes A: "finite_measure P"
  shows "P = Q"
proof (rule measure_eqI_generator_eq[OF Int_stable_prod_algebra prod_algebra_sets_into_space])
  interpret finite_measure P by fact
  define i where "i = (SOME i. i \<in> I)"
  have i: "I \<noteq> {} \<Longrightarrow> i \<in> I"
    unfolding i_def by (rule someI_ex) auto
  define A where "A n =
    (if I = {} then prod_emb I M {} (\<Pi>\<^sub>E i\<in>{}. {}) else prod_emb I M {i} (\<Pi>\<^sub>E i\<in>{i}. space (M i)))"
    for n :: nat
  then show "range A \<subseteq> prod_algebra I M"
    using prod_algebraI[of "{}" I "\<lambda>i. space (M i)" M] by (auto intro!: prod_algebraI i)
  have "\<And>i. A i = space (PiM I M)"
    by (auto simp: prod_emb_def space_PiM PiE_iff A_def i ex_in_conv[symmetric] exI)
  then show "(\<Union>i. A i) = (\<Pi>\<^sub>E i\<in>I. space (M i))" "\<And>i. emeasure P (A i) \<noteq> \<infinity>"
    by (auto simp: space_PiM)
next
  fix X assume X: "X \<in> prod_algebra I M"
  then obtain J E where X: "X = prod_emb I M J (\<Pi>\<^sub>E j\<in>J. E j)"
    and J: "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets (M j)"
    by (force elim!: prod_algebraE)
  then show "emeasure P X = emeasure Q X"
    by (auto intro!: eq)
qed (auto simp: sets_PiM)

locale\<^marker>\<open>tag unimportant\<close> product_sigma_finite =
  fixes M :: "'i \<Rightarrow> 'a measure"
  assumes sigma_finite_measures: "\<And>i. sigma_finite_measure (M i)"

sublocale\<^marker>\<open>tag unimportant\<close> product_sigma_finite \<subseteq> M?: sigma_finite_measure "M i" for i
  by (rule sigma_finite_measures)

locale\<^marker>\<open>tag unimportant\<close> finite_product_sigma_finite = product_sigma_finite M for M :: "'i \<Rightarrow> 'a measure" +
  fixes I :: "'i set"
  assumes finite_index: "finite I"

proposition (in finite_product_sigma_finite) sigma_finite_pairs:
  "\<exists>F::'i \<Rightarrow> nat \<Rightarrow> 'a set.
    (\<forall>i\<in>I. range (F i) \<subseteq> sets (M i)) \<and>
    (\<forall>k. \<forall>i\<in>I. emeasure (M i) (F i k) \<noteq> \<infinity>) \<and> incseq (\<lambda>k. \<Pi>\<^sub>E i\<in>I. F i k) \<and>
    (\<Union>k. \<Pi>\<^sub>E i\<in>I. F i k) = space (PiM I M)"
proof -
  have "\<forall>i::'i. \<exists>F::nat \<Rightarrow> 'a set. range F \<subseteq> sets (M i) \<and> incseq F \<and> (\<Union>i. F i) = space (M i) \<and> (\<forall>k. emeasure (M i) (F k) \<noteq> \<infinity>)"
    using M.sigma_finite_incseq by metis
  then obtain F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set"
    where "\<forall>x. range (F x) \<subseteq> sets (M x) \<and> incseq (F x) \<and> \<Union> (range (F x)) = space (M x) \<and> (\<forall>k. emeasure (M x) (F x k) \<noteq> \<infinity>)"
    by metis
  then have F: "\<And>i. range (F i) \<subseteq> sets (M i)" "\<And>i. incseq (F i)" "\<And>i. (\<Union>j. F i j) = space (M i)" "\<And>i k. emeasure (M i) (F i k) \<noteq> \<infinity>"
    by auto
  let ?F = "\<lambda>k. \<Pi>\<^sub>E i\<in>I. F i k"
  note space_PiM[simp]
  show ?thesis
  proof (intro exI[of _ F] conjI allI incseq_SucI set_eqI iffI ballI)
    fix i show "range (F i) \<subseteq> sets (M i)" by fact
  next
    fix i k show "emeasure (M i) (F i k) \<noteq> \<infinity>" by fact
  next
    fix x assume "x \<in> (\<Union>i. ?F i)" with F(1) show "x \<in> space (PiM I M)"
      by (auto simp: PiE_def dest!: sets.sets_into_space)
  next
    fix f assume "f \<in> space (PiM I M)"
    with Pi_UN[OF finite_index, of "\<lambda>k i. F i k"] F
    show "f \<in> (\<Union>i. ?F i)" by (auto simp: incseq_def PiE_def)
  next
    fix i show "?F i \<subseteq> ?F (Suc i)"
      using \<open>\<And>i. incseq (F i)\<close>[THEN incseq_SucD] by auto
  qed
qed

lemma emeasure_PiM_empty[simp]: "emeasure (PiM {} M) {\<lambda>_. undefined} = 1"
proof -
  let ?\<mu> = "\<lambda>A. if A = {} then 0 else (1::ennreal)"
  have "emeasure (Pi\<^sub>M {} M) (prod_emb {} M {} (\<Pi>\<^sub>E i\<in>{}. {})) = 1"
  proof (subst emeasure_extend_measure_Pair[OF PiM_def])
    show "positive (PiM {} M) ?\<mu>"
      by (auto simp: positive_def)
    show "countably_additive (PiM {} M) ?\<mu>"
      by (rule sets.countably_additiveI_finite)
         (auto simp: additive_def positive_def sets_PiM_empty space_PiM_empty intro!: )
  qed (auto simp: prod_emb_def)
  also have "(prod_emb {} M {} (\<Pi>\<^sub>E i\<in>{}. {})) = {\<lambda>_. undefined}"
    by (auto simp: prod_emb_def)
  finally show ?thesis
    by simp
qed

lemma PiM_empty: "PiM {} M = count_space {\<lambda>_. undefined}"
  by (rule measure_eqI) (auto simp add: sets_PiM_empty)

lemma (in product_sigma_finite) emeasure_PiM:
  "finite I \<Longrightarrow> (\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> emeasure (PiM I M) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
proof (induct I arbitrary: A rule: finite_induct)
  case (insert i I)
  interpret finite_product_sigma_finite M I by standard fact
  have "finite (insert i I)" using \<open>finite I\<close> by auto
  interpret I': finite_product_sigma_finite M "insert i I" by standard fact
  let ?h = "(\<lambda>(f, y). f(i := y))"

  let ?P = "distr (Pi\<^sub>M I M \<Otimes>\<^sub>M M i) (Pi\<^sub>M (insert i I) M) ?h"
  let ?\<mu> = "emeasure ?P"
  let ?I = "{j \<in> insert i I. emeasure (M j) (space (M j)) \<noteq> 1}"
  let ?f = "\<lambda>J E j. if j \<in> J then emeasure (M j) (E j) else emeasure (M j) (space (M j))"

  have "emeasure (Pi\<^sub>M (insert i I) M) (prod_emb (insert i I) M (insert i I) (Pi\<^sub>E (insert i I) A)) =
    (\<Prod>i\<in>insert i I. emeasure (M i) (A i))"
  proof (subst emeasure_extend_measure_Pair[OF PiM_def])
    fix J E assume "(J \<noteq> {} \<or> insert i I = {}) \<and> finite J \<and> J \<subseteq> insert i I \<and> E \<in> (\<Pi> j\<in>J. sets (M j))"
    then have J: "J \<noteq> {}" "finite J" "J \<subseteq> insert i I" and E: "\<forall>j\<in>J. E j \<in> sets (M j)" by auto
    let ?p = "prod_emb (insert i I) M J (Pi\<^sub>E J E)"
    let ?p' = "prod_emb I M (J - {i}) (\<Pi>\<^sub>E j\<in>J-{i}. E j)"
    have "?\<mu> ?p =
      emeasure (Pi\<^sub>M I M \<Otimes>\<^sub>M (M i)) (?h -` ?p \<inter> space (Pi\<^sub>M I M \<Otimes>\<^sub>M M i))"
      by (intro emeasure_distr measurable_add_dim sets_PiM_I) fact+
    also have "?h -` ?p \<inter> space (Pi\<^sub>M I M \<Otimes>\<^sub>M M i) = ?p' \<times> (if i \<in> J then E i else space (M i))"
      using J E[rule_format, THEN sets.sets_into_space]
      by (force simp: space_pair_measure space_PiM prod_emb_iff PiE_def Pi_iff split: if_split_asm)
    also have "emeasure (Pi\<^sub>M I M \<Otimes>\<^sub>M (M i)) (?p' \<times> (if i \<in> J then E i else space (M i))) =
      emeasure (Pi\<^sub>M I M) ?p' * emeasure (M i) (if i \<in> J then (E i) else space (M i))"
      using J E by (intro M.emeasure_pair_measure_Times sets_PiM_I) auto
    also have "?p' = (\<Pi>\<^sub>E j\<in>I. if j \<in> J-{i} then E j else space (M j))"
      using J E[rule_format, THEN sets.sets_into_space]
      by (auto simp: prod_emb_iff PiE_def Pi_iff split: if_split_asm) blast+
    also have "emeasure (Pi\<^sub>M I M) (\<Pi>\<^sub>E j\<in>I. if j \<in> J-{i} then E j else space (M j)) =
      (\<Prod> j\<in>I. if j \<in> J-{i} then emeasure (M j) (E j) else emeasure (M j) (space (M j)))"
      using E by (subst insert) (auto intro!: prod.cong)
    also have "(\<Prod>j\<in>I. if j \<in> J - {i} then emeasure (M j) (E j) else emeasure (M j) (space (M j))) *
       emeasure (M i) (if i \<in> J then E i else space (M i)) = (\<Prod>j\<in>insert i I. ?f J E j)"
      using insert by (auto simp: mult.commute intro!: arg_cong2[where f="(*)"] prod.cong)
    also have "\<dots> = (\<Prod>j\<in>J \<union> ?I. ?f J E j)"
      using insert(1,2) J E by (intro prod.mono_neutral_right) auto
    finally show "?\<mu> ?p = \<dots>" .

    show "prod_emb (insert i I) M J (Pi\<^sub>E J E) \<in> Pow (\<Pi>\<^sub>E i\<in>insert i I. space (M i))"
      using J E[rule_format, THEN sets.sets_into_space] by (auto simp: prod_emb_iff PiE_def)
  next
    show "positive (sets (Pi\<^sub>M (insert i I) M)) ?\<mu>" "countably_additive (sets (Pi\<^sub>M (insert i I) M)) ?\<mu>"
      using emeasure_positive[of ?P] emeasure_countably_additive[of ?P] by simp_all
  next
    show "(insert i I \<noteq> {} \<or> insert i I = {}) \<and> finite (insert i I) \<and>
      insert i I \<subseteq> insert i I \<and> A \<in> (\<Pi> j\<in>insert i I. sets (M j))"
      using insert by auto
  qed (auto intro!: prod.cong)
  with insert show ?case
    by (subst (asm) prod_emb_PiE_same_index) (auto intro!: sets.sets_into_space)
qed simp

lemma (in product_sigma_finite) PiM_eqI:
  assumes I[simp]: "finite I" and P: "sets P = PiM I M"
  assumes eq: "\<And>A. (\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> P (Pi\<^sub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
  shows "P = PiM I M"
proof -
  interpret finite_product_sigma_finite M I
    by standard fact
  from sigma_finite_pairs obtain C where C:
    "\<forall>i\<in>I. range (C i) \<subseteq> sets (M i)" "\<forall>k. \<forall>i\<in>I. emeasure (M i) (C i k) \<noteq> \<infinity>"
    "incseq (\<lambda>k. \<Pi>\<^sub>E i\<in>I. C i k)" "(\<Union>k. \<Pi>\<^sub>E i\<in>I. C i k) = space (Pi\<^sub>M I M)"
    by auto
  show ?thesis
  proof (rule measure_eqI_PiM_finite[OF I refl P, symmetric])
    show "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> (Pi\<^sub>M I M) (Pi\<^sub>E I A) = P (Pi\<^sub>E I A)" for A
      by (simp add: eq emeasure_PiM)
    define A where "A n = (\<Pi>\<^sub>E i\<in>I. C i n)" for n
    with C show "range A \<subseteq> prod_algebra I M" "\<And>i. emeasure (Pi\<^sub>M I M) (A i) \<noteq> \<infinity>" "(\<Union>i. A i) = space (PiM I M)"
      by (auto intro!: prod_algebraI_finite simp: emeasure_PiM subset_eq ennreal_prod_eq_top)
  qed
qed

lemma (in product_sigma_finite) sigma_finite:
  assumes "finite I"
  shows "sigma_finite_measure (PiM I M)"
proof
  interpret finite_product_sigma_finite M I by standard fact

  obtain F where F: "\<And>j. countable (F j)" "\<And>j f. f \<in> F j \<Longrightarrow> f \<in> sets (M j)"
    "\<And>j f. f \<in> F j \<Longrightarrow> emeasure (M j) f \<noteq> \<infinity>" and
    in_space: "\<And>j. space (M j) = \<Union>(F j)"
    using sigma_finite_countable by (metis subset_eq)
  moreover have "(\<Union>(Pi\<^sub>E I ` Pi\<^sub>E I F)) = space (Pi\<^sub>M I M)"
    using in_space by (auto simp: space_PiM PiE_iff intro!: PiE_choice[THEN iffD2])
  ultimately show "\<exists>A. countable A \<and> A \<subseteq> sets (Pi\<^sub>M I M) \<and> \<Union>A = space (Pi\<^sub>M I M) \<and> (\<forall>a\<in>A. emeasure (Pi\<^sub>M I M) a \<noteq> \<infinity>)"
    by (intro exI[of _ "Pi\<^sub>E I ` Pi\<^sub>E I F"])
       (auto intro!: countable_PiE sets_PiM_I_finite
             simp: PiE_iff emeasure_PiM finite_index ennreal_prod_eq_top)
qed

sublocale finite_product_sigma_finite \<subseteq> sigma_finite_measure "Pi\<^sub>M I M"
  using sigma_finite[OF finite_index] .

lemma (in finite_product_sigma_finite) measure_times:
  "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> emeasure (Pi\<^sub>M I M) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
  using emeasure_PiM[OF finite_index] by auto

lemma (in product_sigma_finite) nn_integral_empty:
  "0 \<le> f (\<lambda>k. undefined) \<Longrightarrow> integral\<^sup>N (Pi\<^sub>M {} M) f = f (\<lambda>k. undefined)"
  by (simp add: PiM_empty nn_integral_count_space_finite max.absorb2)

lemma\<^marker>\<open>tag important\<close> (in product_sigma_finite) distr_merge:
  assumes IJ[simp]: "I \<inter> J = {}" and fin: "finite I" "finite J"
  shows "distr (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M) (Pi\<^sub>M (I \<union> J) M) (merge I J) = Pi\<^sub>M (I \<union> J) M"
   (is "?D = ?P")
proof (rule PiM_eqI)
  interpret I: finite_product_sigma_finite M I by standard fact
  interpret J: finite_product_sigma_finite M J by standard fact
  fix A assume A: "\<And>i. i \<in> I \<union> J \<Longrightarrow> A i \<in> sets (M i)"
  have *: "(merge I J -` Pi\<^sub>E (I \<union> J) A \<inter> space (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M)) = Pi\<^sub>E I A \<times> Pi\<^sub>E J A"
    using A[THEN sets.sets_into_space] by (auto simp: space_PiM space_pair_measure)
  from A fin show "emeasure (distr (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M) (Pi\<^sub>M (I \<union> J) M) (merge I J)) (Pi\<^sub>E (I \<union> J) A) =
      (\<Prod>i\<in>I \<union> J. emeasure (M i) (A i))"
    by (subst emeasure_distr)
       (auto simp: * J.emeasure_pair_measure_Times I.measure_times J.measure_times prod.union_disjoint)
qed (insert fin, simp_all)

proposition (in product_sigma_finite) product_nn_integral_fold:
  assumes IJ: "I \<inter> J = {}" "finite I" "finite J"
  and f[measurable]: "f \<in> borel_measurable (Pi\<^sub>M (I \<union> J) M)"
  shows "integral\<^sup>N (Pi\<^sub>M (I \<union> J) M) f =
    (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f (merge I J (x, y)) \<partial>(Pi\<^sub>M J M)) \<partial>(Pi\<^sub>M I M))"
proof -
  interpret I: finite_product_sigma_finite M I by standard fact
  interpret J: finite_product_sigma_finite M J by standard fact
  interpret P: pair_sigma_finite "Pi\<^sub>M I M" "Pi\<^sub>M J M" by standard
  have P_borel: "(\<lambda>x. f (merge I J x)) \<in> borel_measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M)"
    using measurable_comp[OF measurable_merge f] by (simp add: comp_def)
  show ?thesis
    apply (subst distr_merge[OF IJ, symmetric])
    apply (subst nn_integral_distr[OF measurable_merge])
    apply measurable []
    apply (subst J.nn_integral_fst[symmetric, OF P_borel])
    apply simp
    done
qed

lemma (in product_sigma_finite) distr_singleton:
  "distr (Pi\<^sub>M {i} M) (M i) (\<lambda>x. x i) = M i" (is "?D = _")
proof (intro measure_eqI[symmetric])
  interpret I: finite_product_sigma_finite M "{i}" by standard simp
  fix A assume A: "A \<in> sets (M i)"
  then have "(\<lambda>x. x i) -` A \<inter> space (Pi\<^sub>M {i} M) = (\<Pi>\<^sub>E i\<in>{i}. A)"
    using sets.sets_into_space by (auto simp: space_PiM)
  then show "emeasure (M i) A = emeasure ?D A"
    using A I.measure_times[of "\<lambda>_. A"]
    by (simp add: emeasure_distr measurable_component_singleton)
qed simp

lemma (in product_sigma_finite) product_nn_integral_singleton:
  assumes f: "f \<in> borel_measurable (M i)"
  shows "integral\<^sup>N (Pi\<^sub>M {i} M) (\<lambda>x. f (x i)) = integral\<^sup>N (M i) f"
proof -
  interpret I: finite_product_sigma_finite M "{i}" by standard simp
  from f show ?thesis
    apply (subst distr_singleton[symmetric])
    apply (subst nn_integral_distr[OF measurable_component_singleton])
    apply simp_all
    done
qed

proposition (in product_sigma_finite) product_nn_integral_insert:
  assumes I[simp]: "finite I" "i \<notin> I"
    and f: "f \<in> borel_measurable (Pi\<^sub>M (insert i I) M)"
  shows "integral\<^sup>N (Pi\<^sub>M (insert i I) M) f = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f (x(i := y)) \<partial>(M i)) \<partial>(Pi\<^sub>M I M))"
proof -
  interpret I: finite_product_sigma_finite M I by standard auto
  interpret i: finite_product_sigma_finite M "{i}" by standard auto
  have IJ: "I \<inter> {i} = {}" and insert: "I \<union> {i} = insert i I"
    using f by auto
  show ?thesis
    unfolding product_nn_integral_fold[OF IJ, unfolded insert, OF I(1) i.finite_index f]
  proof (rule nn_integral_cong, subst product_nn_integral_singleton[symmetric])
    fix x assume x: "x \<in> space (Pi\<^sub>M I M)"
    let ?f = "\<lambda>y. f (x(i := y))"
    show "?f \<in> borel_measurable (M i)"
      using measurable_comp[OF measurable_component_update f, OF x \<open>i \<notin> I\<close>]
      unfolding comp_def .
    show "(\<integral>\<^sup>+ y. f (merge I {i} (x, y)) \<partial>Pi\<^sub>M {i} M) = (\<integral>\<^sup>+ y. f (x(i := y i)) \<partial>Pi\<^sub>M {i} M)"
      using x
      by (auto intro!: nn_integral_cong arg_cong[where f=f]
               simp add: space_PiM extensional_def PiE_def)
  qed
qed

lemma (in product_sigma_finite) product_nn_integral_insert_rev:
  assumes I[simp]: "finite I" "i \<notin> I"
    and [measurable]: "f \<in> borel_measurable (Pi\<^sub>M (insert i I) M)"
  shows "integral\<^sup>N (Pi\<^sub>M (insert i I) M) f = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x(i := y)) \<partial>(Pi\<^sub>M I M)) \<partial>(M i))"
  apply (subst product_nn_integral_insert[OF assms])
  apply (rule pair_sigma_finite.Fubini')
  apply intro_locales []
  apply (rule sigma_finite[OF I(1)])
  apply measurable
  done

lemma (in product_sigma_finite) product_nn_integral_prod:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable (M i)"
  shows "(\<integral>\<^sup>+ x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^sub>M I M) = (\<Prod>i\<in>I. integral\<^sup>N (M i) (f i))"
using assms proof (induction I)
  case (insert i I)
  note insert.prems[measurable]
  note \<open>finite I\<close>[intro, simp]
  interpret I: finite_product_sigma_finite M I by standard auto
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using insert by (auto intro!: prod.cong)
  have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow> (\<lambda>x. (\<Prod>i\<in>J. f i (x i))) \<in> borel_measurable (Pi\<^sub>M J M)"
    using sets.sets_into_space insert
    by (intro borel_measurable_prod_ennreal
              measurable_comp[OF measurable_component_singleton, unfolded comp_def])
       auto
  then show ?case
    apply (simp add: product_nn_integral_insert[OF insert(1,2)])
    apply (simp add: insert(2-) * nn_integral_multc)
    apply (subst nn_integral_cmult)
    apply (auto simp add: insert(2-))
    done
qed (simp add: space_PiM)

proposition (in product_sigma_finite) product_nn_integral_pair:
  assumes [measurable]: "case_prod f \<in> borel_measurable (M x \<Otimes>\<^sub>M M y)"
  assumes xy: "x \<noteq> y"
  shows "(\<integral>\<^sup>+\<sigma>. f (\<sigma> x) (\<sigma> y) \<partial>PiM {x, y} M) = (\<integral>\<^sup>+z. f (fst z) (snd z) \<partial>(M x \<Otimes>\<^sub>M M y))"
proof -
  interpret psm: pair_sigma_finite "M x" "M y"
    unfolding pair_sigma_finite_def using sigma_finite_measures by simp_all
  have "{x, y} = {y, x}" by auto
  also have "(\<integral>\<^sup>+\<sigma>. f (\<sigma> x) (\<sigma> y) \<partial>PiM {y, x} M) = (\<integral>\<^sup>+y. \<integral>\<^sup>+\<sigma>. f (\<sigma> x) y \<partial>PiM {x} M \<partial>M y)"
    using xy by (subst product_nn_integral_insert_rev) simp_all
  also have "... = (\<integral>\<^sup>+y. \<integral>\<^sup>+x. f x y \<partial>M x \<partial>M y)"
    by (intro nn_integral_cong, subst product_nn_integral_singleton) simp_all
  also have "... = (\<integral>\<^sup>+z. f (fst z) (snd z) \<partial>(M x \<Otimes>\<^sub>M M y))"
    by (subst psm.nn_integral_snd[symmetric]) simp_all
  finally show ?thesis .
qed

lemma (in product_sigma_finite) distr_component:
  "distr (M i) (Pi\<^sub>M {i} M) (\<lambda>x. \<lambda>i\<in>{i}. x) = Pi\<^sub>M {i} M" (is "?D = ?P")
proof (intro PiM_eqI)
  fix A assume A: "\<And>ia. ia \<in> {i} \<Longrightarrow> A ia \<in> sets (M ia)"
  then have "(\<lambda>x. \<lambda>i\<in>{i}. x) -` Pi\<^sub>E {i} A \<inter> space (M i) = A i"
    by (fastforce dest: sets.sets_into_space)
  with A show "emeasure (distr (M i) (Pi\<^sub>M {i} M) (\<lambda>x. \<lambda>i\<in>{i}. x)) (Pi\<^sub>E {i} A) = (\<Prod>i\<in>{i}. emeasure (M i) (A i))"
    by (subst emeasure_distr) (auto intro!: sets_PiM_I_finite measurable_restrict)
qed simp_all

lemma (in product_sigma_finite)
  assumes IJ: "I \<inter> J = {}" "finite I" "finite J" and A: "A \<in> sets (Pi\<^sub>M (I \<union> J) M)"
  shows emeasure_fold_integral:
    "emeasure (Pi\<^sub>M (I \<union> J) M) A = (\<integral>\<^sup>+x. emeasure (Pi\<^sub>M J M) ((\<lambda>y. merge I J (x, y)) -` A \<inter> space (Pi\<^sub>M J M)) \<partial>Pi\<^sub>M I M)" (is ?I)
    and emeasure_fold_measurable:
    "(\<lambda>x. emeasure (Pi\<^sub>M J M) ((\<lambda>y. merge I J (x, y)) -` A \<inter> space (Pi\<^sub>M J M))) \<in> borel_measurable (Pi\<^sub>M I M)" (is ?B)
proof -
  interpret I: finite_product_sigma_finite M I by standard fact
  interpret J: finite_product_sigma_finite M J by standard fact
  interpret IJ: pair_sigma_finite "Pi\<^sub>M I M" "Pi\<^sub>M J M" ..
  have merge: "merge I J -` A \<inter> space (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M) \<in> sets (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M)"
    by (intro measurable_sets[OF _ A] measurable_merge assms)

  show ?I
    apply (subst distr_merge[symmetric, OF IJ])
    apply (subst emeasure_distr[OF measurable_merge A])
    apply (subst J.emeasure_pair_measure_alt[OF merge])
    apply (auto intro!: nn_integral_cong arg_cong2[where f=emeasure] simp: space_pair_measure)
    done

  show ?B
    using IJ.measurable_emeasure_Pair1[OF merge]
    by (simp add: vimage_comp comp_def space_pair_measure cong: measurable_cong)
qed

lemma sets_Collect_single:
  "i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow> { x \<in> space (Pi\<^sub>M I M). x i \<in> A } \<in> sets (Pi\<^sub>M I M)"
  by simp

lemma pair_measure_eq_distr_PiM:
  fixes M1 :: "'a measure" and M2 :: "'a measure"
  assumes "sigma_finite_measure M1" "sigma_finite_measure M2"
  shows "(M1 \<Otimes>\<^sub>M M2) = distr (Pi\<^sub>M UNIV (case_bool M1 M2)) (M1 \<Otimes>\<^sub>M M2) (\<lambda>x. (x True, x False))"
    (is "?P = ?D")
proof (rule pair_measure_eqI[OF assms])
  interpret B: product_sigma_finite "case_bool M1 M2"
    unfolding product_sigma_finite_def using assms by (auto split: bool.split)
  let ?B = "Pi\<^sub>M UNIV (case_bool M1 M2)"

  have [simp]: "fst \<circ> (\<lambda>x. (x True, x False)) = (\<lambda>x. x True)" "snd \<circ> (\<lambda>x. (x True, x False)) = (\<lambda>x. x False)"
    by auto
  fix A B assume A: "A \<in> sets M1" and B: "B \<in> sets M2"
  have "emeasure M1 A * emeasure M2 B = (\<Prod> i\<in>UNIV. emeasure (case_bool M1 M2 i) (case_bool A B i))"
    by (simp add: UNIV_bool ac_simps)
  also have "\<dots> = emeasure ?B (Pi\<^sub>E UNIV (case_bool A B))"
    using A B by (subst B.emeasure_PiM) (auto split: bool.split)
  also have "Pi\<^sub>E UNIV (case_bool A B) = (\<lambda>x. (x True, x False)) -` (A \<times> B) \<inter> space ?B"
    using A[THEN sets.sets_into_space] B[THEN sets.sets_into_space]
    by (auto simp: PiE_iff all_bool_eq space_PiM split: bool.split)
  finally show "emeasure M1 A * emeasure M2 B = emeasure ?D (A \<times> B)"
    using A B
      measurable_component_singleton[of True UNIV "case_bool M1 M2"]
      measurable_component_singleton[of False UNIV "case_bool M1 M2"]
    by (subst emeasure_distr) (auto simp: measurable_pair_iff)
qed simp

lemma infprod_in_sets[intro]:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets (M i)"
  shows "Pi UNIV E \<in> sets (\<Pi>\<^sub>M i\<in>UNIV::nat set. M i)"
proof -
  have "Pi UNIV E = (\<Inter>i. prod_emb UNIV M {..i} (\<Pi>\<^sub>E j\<in>{..i}. E j))"
    using E E[THEN sets.sets_into_space]
    by (auto simp: prod_emb_def Pi_iff extensional_def)
  with E show ?thesis by auto
qed



subsection \<open>Measurability\<close>

text \<open>There are two natural sigma-algebras on a product space: the borel sigma algebra,
generated by open sets in the product, and the product sigma algebra, countably generated by
products of measurable sets along finitely many coordinates. The second one is defined and studied
in \<^file>\<open>Finite_Product_Measure.thy\<close>.

These sigma-algebra share a lot of natural properties (measurability of coordinates, for instance),
but there is a fundamental difference: open sets are generated by arbitrary unions, not only
countable ones, so typically many open sets will not be measurable with respect to the product sigma
algebra (while all sets in the product sigma algebra are borel). The two sigma algebras coincide
only when everything is countable (i.e., the product is countable, and the borel sigma algebra in
the factor is countably generated).

In this paragraph, we develop basic measurability properties for the borel sigma algebra, and
compare it with the product sigma algebra as explained above.
\<close>

lemma measurable_product_coordinates [measurable (raw)]:
  "(\<lambda>x. x i) \<in> measurable borel borel"
by (rule borel_measurable_continuous_onI[OF continuous_on_product_coordinates])

lemma measurable_product_then_coordinatewise:
  fixes f::"'a \<Rightarrow> 'b \<Rightarrow> ('c::topological_space)"
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "(\<lambda>x. f x i) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. f x i) = (\<lambda>y. y i) o f"
    unfolding comp_def by auto
  then show ?thesis by simp
qed

text \<open>To compare the Borel sigma algebra with the product sigma algebra, we give a presentation
of the product sigma algebra that is more similar to the one we used above for the product
topology.\<close>

lemma sets_PiM_finite:
  "sets (Pi\<^sub>M I M) = sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i))
        {(\<Pi>\<^sub>E i\<in>I. X i) |X. (\<forall>i. X i \<in> sets (M i)) \<and> finite {i. X i \<noteq> space (M i)}}"
proof
  have "{(\<Pi>\<^sub>E i\<in>I. X i) |X. (\<forall>i. X i \<in> sets (M i)) \<and> finite {i. X i \<noteq> space (M i)}} \<subseteq> sets (Pi\<^sub>M I M)"
  proof (auto)
    fix X assume H: "\<forall>i. X i \<in> sets (M i)" "finite {i. X i \<noteq> space (M i)}"
    then have *: "X i \<in> sets (M i)" for i by simp
    define J where "J = {i \<in> I. X i \<noteq> space (M i)}"
    have "finite J" "J \<subseteq> I" unfolding J_def using H by auto
    define Y where "Y = (\<Pi>\<^sub>E j\<in>J. X j)"
    have "prod_emb I M J Y \<in> sets (Pi\<^sub>M I M)"
      unfolding Y_def apply (rule sets_PiM_I) using \<open>finite J\<close> \<open>J \<subseteq> I\<close> * by auto
    moreover have "prod_emb I M J Y = (\<Pi>\<^sub>E i\<in>I. X i)"
      unfolding prod_emb_def Y_def J_def using H sets.sets_into_space[OF *]
      by (auto simp add: PiE_iff, blast)
    ultimately show "Pi\<^sub>E I X \<in> sets (Pi\<^sub>M I M)" by simp
  qed
  then show "sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) {(\<Pi>\<^sub>E i\<in>I. X i) |X. (\<forall>i. X i \<in> sets (M i)) \<and> finite {i. X i \<noteq> space (M i)}}
              \<subseteq> sets (Pi\<^sub>M I M)"
    by (metis (mono_tags, lifting) sets.sigma_sets_subset' sets.top space_PiM)

  have *: "\<exists>X. {f. (\<forall>i\<in>I. f i \<in> space (M i)) \<and> f \<in> extensional I \<and> f i \<in> A} = Pi\<^sub>E I X \<and>
                (\<forall>i. X i \<in> sets (M i)) \<and> finite {i. X i \<noteq> space (M i)}"
    if "i \<in> I" "A \<in> sets (M i)" for i A
  proof -
    define X where "X = (\<lambda>j. if j = i then A else space (M j))"
    have "{f. (\<forall>i\<in>I. f i \<in> space (M i)) \<and> f \<in> extensional I \<and> f i \<in> A} = Pi\<^sub>E I X"
      unfolding X_def using sets.sets_into_space[OF \<open>A \<in> sets (M i)\<close>] \<open>i \<in> I\<close>
      by (auto simp add: PiE_iff extensional_def, metis subsetCE, metis)
    moreover have "X j \<in> sets (M j)" for j
      unfolding X_def using \<open>A \<in> sets (M i)\<close> by auto
    moreover have "finite {j. X j \<noteq> space (M j)}"
      unfolding X_def by simp
    ultimately show ?thesis by auto
  qed
  show "sets (Pi\<^sub>M I M) \<subseteq> sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) {(\<Pi>\<^sub>E i\<in>I. X i) |X. (\<forall>i. X i \<in> sets (M i)) \<and> finite {i. X i \<noteq> space (M i)}}"
    unfolding sets_PiM_single
    apply (rule sigma_sets_mono')
    apply (auto simp add: PiE_iff *)
    done
qed

lemma sets_PiM_subset_borel:
  "sets (Pi\<^sub>M UNIV (\<lambda>_. borel)) \<subseteq> sets borel"
proof -
  have *: "Pi\<^sub>E UNIV X \<in> sets borel" if [measurable]: "\<And>i. X i \<in> sets borel" "finite {i. X i \<noteq> UNIV}" for X::"'a \<Rightarrow> 'b set"
  proof -
    define I where "I = {i. X i \<noteq> UNIV}"
    have "finite I" unfolding I_def using that by simp
    have "Pi\<^sub>E UNIV X = (\<Inter>i\<in>I. (\<lambda>x. x i)-`(X i) \<inter> space borel) \<inter> space borel"
      unfolding I_def by auto
    also have "... \<in> sets borel"
      using that \<open>finite I\<close> by measurable
    finally show ?thesis by simp
  qed
  then have "{(\<Pi>\<^sub>E i\<in>UNIV. X i) |X::('a \<Rightarrow> 'b set). (\<forall>i. X i \<in> sets borel) \<and> finite {i. X i \<noteq> space borel}} \<subseteq> sets borel"
    by auto
  then show ?thesis unfolding sets_PiM_finite space_borel
    by (simp add: * sets.sigma_sets_subset')
qed

proposition sets_PiM_equal_borel:
  "sets (Pi\<^sub>M UNIV (\<lambda>i::('a::countable). borel::('b::second_countable_topology measure))) = sets borel"
proof
  obtain K::"('a \<Rightarrow> 'b) set set" where K: "topological_basis K" "countable K"
            "\<And>k. k \<in> K \<Longrightarrow> \<exists>X. (k = Pi\<^sub>E UNIV X) \<and> (\<forall>i. open (X i)) \<and> finite {i. X i \<noteq> UNIV}"
    using product_topology_countable_basis by fast
  have *: "k \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel))" if "k \<in> K" for k
  proof -
    obtain X where H: "k = Pi\<^sub>E UNIV X" "\<And>i. open (X i)" "finite {i. X i \<noteq> UNIV}"
      using K(3)[OF \<open>k \<in> K\<close>] by blast
    show ?thesis unfolding H(1) sets_PiM_finite space_borel using borel_open[OF H(2)] H(3) by auto
  qed
  have **: "U \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel))" if "open U" for U::"('a \<Rightarrow> 'b) set"
  proof -
    obtain B where "B \<subseteq> K" "U = (\<Union>B)"
      using \<open>open U\<close> \<open>topological_basis K\<close> by (metis topological_basis_def)
    have "countable B" using \<open>B \<subseteq> K\<close> \<open>countable K\<close> countable_subset by blast
    moreover have "k \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel))" if "k \<in> B" for k
      using \<open>B \<subseteq> K\<close> * that by auto
    ultimately show ?thesis unfolding \<open>U = (\<Union>B)\<close> by auto
  qed
  have "sigma_sets UNIV (Collect open) \<subseteq> sets (Pi\<^sub>M UNIV (\<lambda>i::'a. (borel::('b measure))))"
    apply (rule sets.sigma_sets_subset') using ** by auto
  then show "sets (borel::('a \<Rightarrow> 'b) measure) \<subseteq> sets (Pi\<^sub>M UNIV (\<lambda>_. borel))"
    unfolding borel_def by auto
qed (simp add: sets_PiM_subset_borel)

lemma measurable_coordinatewise_then_product:
  fixes f::"'a \<Rightarrow> ('b::countable) \<Rightarrow> ('c::second_countable_topology)"
  assumes [measurable]: "\<And>i. (\<lambda>x. f x i) \<in> borel_measurable M"
  shows "f \<in> borel_measurable M"
proof -
  have "f \<in> measurable M (Pi\<^sub>M UNIV (\<lambda>_. borel))"
    by (rule measurable_PiM_single', auto simp add: assms)
  then show ?thesis using sets_PiM_equal_borel measurable_cong_sets by blast
qed


end
