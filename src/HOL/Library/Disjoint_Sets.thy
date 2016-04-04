(*  Title:      HOL/Library/Disjoint_Sets.thy
    Author:     Johannes Hölzl, TU München
*)

section \<open>Handling Disjoint Sets\<close>

theory Disjoint_Sets
  imports Main
begin

lemma range_subsetD: "range f \<subseteq> B \<Longrightarrow> f i \<in> B"
  by blast

lemma Int_Diff_disjoint: "A \<inter> B \<inter> (A - B) = {}"
  by blast

lemma Int_Diff_Un: "A \<inter> B \<union> (A - B) = A"
  by blast

lemma mono_Un: "mono A \<Longrightarrow> (\<Union>i\<le>n. A i) = A n"
  unfolding mono_def by auto

subsection \<open>Set of Disjoint Sets\<close>

abbreviation disjoint :: "'a set set \<Rightarrow> bool" where "disjoint \<equiv> pairwise disjnt"

lemma disjoint_def: "disjoint A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>A. a \<noteq> b \<longrightarrow> a \<inter> b = {})"
  unfolding pairwise_def disjnt_def by auto

lemma disjointI:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<inter> b = {}) \<Longrightarrow> disjoint A"
  unfolding disjoint_def by auto

lemma disjointD:
  "disjoint A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<inter> b = {}"
  unfolding disjoint_def by auto

lemma disjoint_INT:
  assumes *: "\<And>i. i \<in> I \<Longrightarrow> disjoint (F i)"
  shows "disjoint {\<Inter>i\<in>I. X i | X. \<forall>i\<in>I. X i \<in> F i}"
proof (safe intro!: disjointI del: equalityI)
  fix A B :: "'a \<Rightarrow> 'b set" assume "(\<Inter>i\<in>I. A i) \<noteq> (\<Inter>i\<in>I. B i)" 
  then obtain i where "A i \<noteq> B i" "i \<in> I"
    by auto
  moreover assume "\<forall>i\<in>I. A i \<in> F i" "\<forall>i\<in>I. B i \<in> F i"
  ultimately show "(\<Inter>i\<in>I. A i) \<inter> (\<Inter>i\<in>I. B i) = {}"
    using *[OF \<open>i\<in>I\<close>, THEN disjointD, of "A i" "B i"]
    by (auto simp: INT_Int_distrib[symmetric])
qed

subsubsection "Family of Disjoint Sets"

definition disjoint_family_on :: "('i \<Rightarrow> 'a set) \<Rightarrow> 'i set \<Rightarrow> bool" where
  "disjoint_family_on A S \<longleftrightarrow> (\<forall>m\<in>S. \<forall>n\<in>S. m \<noteq> n \<longrightarrow> A m \<inter> A n = {})"

abbreviation "disjoint_family A \<equiv> disjoint_family_on A UNIV"

lemma disjoint_family_onD:
  "disjoint_family_on A I \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  by (auto simp: disjoint_family_on_def)

lemma disjoint_family_subset: "disjoint_family A \<Longrightarrow> (\<And>x. B x \<subseteq> A x) \<Longrightarrow> disjoint_family B"
  by (force simp add: disjoint_family_on_def)

lemma disjoint_family_on_bisimulation:
  assumes "disjoint_family_on f S"
  and "\<And>n m. n \<in> S \<Longrightarrow> m \<in> S \<Longrightarrow> n \<noteq> m \<Longrightarrow> f n \<inter> f m = {} \<Longrightarrow> g n \<inter> g m = {}"
  shows "disjoint_family_on g S"
  using assms unfolding disjoint_family_on_def by auto

lemma disjoint_family_on_mono:
  "A \<subseteq> B \<Longrightarrow> disjoint_family_on f B \<Longrightarrow> disjoint_family_on f A"
  unfolding disjoint_family_on_def by auto

lemma disjoint_family_Suc:
  "(\<And>n. A n \<subseteq> A (Suc n)) \<Longrightarrow> disjoint_family (\<lambda>i. A (Suc i) - A i)"
  using lift_Suc_mono_le[of A]
  by (auto simp add: disjoint_family_on_def)
     (metis insert_absorb insert_subset le_SucE le_antisym not_le_imp_less less_imp_le)

lemma disjoint_family_on_disjoint_image:
  "disjoint_family_on A I \<Longrightarrow> disjoint (A ` I)"
  unfolding disjoint_family_on_def disjoint_def by force

lemma disjoint_family_on_vimageI: "disjoint_family_on F I \<Longrightarrow> disjoint_family_on (\<lambda>i. f -` F i) I"
  by (auto simp: disjoint_family_on_def)

lemma disjoint_image_disjoint_family_on:
  assumes d: "disjoint (A ` I)" and i: "inj_on A I"
  shows "disjoint_family_on A I"
  unfolding disjoint_family_on_def
proof (intro ballI impI)
  fix n m assume nm: "m \<in> I" "n \<in> I" and "n \<noteq> m"
  with i[THEN inj_onD, of n m] show "A n \<inter> A m = {}"
    by (intro disjointD[OF d]) auto
qed

lemma disjoint_UN:
  assumes F: "\<And>i. i \<in> I \<Longrightarrow> disjoint (F i)" and *: "disjoint_family_on (\<lambda>i. \<Union>F i) I"
  shows "disjoint (\<Union>i\<in>I. F i)"
proof (safe intro!: disjointI del: equalityI)
  fix A B i j assume "A \<noteq> B" "A \<in> F i" "i \<in> I" "B \<in> F j" "j \<in> I"
  show "A \<inter> B = {}"
  proof cases
    assume "i = j" with F[of i] \<open>i \<in> I\<close> \<open>A \<in> F i\<close> \<open>B \<in> F j\<close> \<open>A \<noteq> B\<close> show "A \<inter> B = {}"
      by (auto dest: disjointD)
  next
    assume "i \<noteq> j"
    with * \<open>i\<in>I\<close> \<open>j\<in>I\<close> have "(\<Union>F i) \<inter> (\<Union>F j) = {}"
      by (rule disjoint_family_onD)
    with \<open>A\<in>F i\<close> \<open>i\<in>I\<close> \<open>B\<in>F j\<close> \<open>j\<in>I\<close>
    show "A \<inter> B = {}"
      by auto
  qed
qed

lemma disjoint_union: "disjoint C \<Longrightarrow> disjoint B \<Longrightarrow> \<Union>C \<inter> \<Union>B = {} \<Longrightarrow> disjoint (C \<union> B)"
  using disjoint_UN[of "{C, B}" "\<lambda>x. x"] by (auto simp add: disjoint_family_on_def)

subsection \<open>Construct Disjoint Sequences\<close>

definition disjointed :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set" where
  "disjointed A n = A n - (\<Union>i\<in>{0..<n}. A i)"

lemma finite_UN_disjointed_eq: "(\<Union>i\<in>{0..<n}. disjointed A i) = (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case by (simp add: atLeastLessThanSuc disjointed_def)
qed

lemma UN_disjointed_eq: "(\<Union>i. disjointed A i) = (\<Union>i. A i)"
  by (rule UN_finite2_eq [where k=0])
     (simp add: finite_UN_disjointed_eq)

lemma less_disjoint_disjointed: "m < n \<Longrightarrow> disjointed A m \<inter> disjointed A n = {}"
  by (auto simp add: disjointed_def)

lemma disjoint_family_disjointed: "disjoint_family (disjointed A)"
  by (simp add: disjoint_family_on_def)
     (metis neq_iff Int_commute less_disjoint_disjointed)

lemma disjointed_subset: "disjointed A n \<subseteq> A n"
  by (auto simp add: disjointed_def)

lemma disjointed_0[simp]: "disjointed A 0 = A 0"
  by (simp add: disjointed_def)

lemma disjointed_mono: "mono A \<Longrightarrow> disjointed A (Suc n) = A (Suc n) - A n"
  using mono_Un[of A] by (simp add: disjointed_def atLeastLessThanSuc_atLeastAtMost atLeast0AtMost)

end
