(*  Title:      HOL/Library/Lub_Glb.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge *)

header {* Definitions of Least Upper Bounds and Greatest Lower Bounds *}

theory Lub_Glb
imports Complex_Main
begin

text {* Thanks to suggestions by James Margetson *}

definition setle :: "'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"  (infixl "*<=" 70)
  where "S *<= x = (ALL y: S. y \<le> x)"

definition setge :: "'a::ord \<Rightarrow> 'a set \<Rightarrow> bool"  (infixl "<=*" 70)
  where "x <=* S = (ALL y: S. x \<le> y)"


subsection {* Rules for the Relations @{text "*<="} and @{text "<=*"} *}

lemma setleI: "ALL y: S. y \<le> x \<Longrightarrow> S *<= x"
  by (simp add: setle_def)

lemma setleD: "S *<= x \<Longrightarrow> y: S \<Longrightarrow> y \<le> x"
  by (simp add: setle_def)

lemma setgeI: "ALL y: S. x \<le> y \<Longrightarrow> x <=* S"
  by (simp add: setge_def)

lemma setgeD: "x <=* S \<Longrightarrow> y: S \<Longrightarrow> x \<le> y"
  by (simp add: setge_def)


definition leastP :: "('a \<Rightarrow> bool) \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "leastP P x = (P x \<and> x <=* Collect P)"

definition isUb :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isUb R S x = (S *<= x \<and> x: R)"

definition isLub :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isLub R S x = leastP (isUb R S) x"

definition ubs :: "'a set \<Rightarrow> 'a::ord set \<Rightarrow> 'a set"
  where "ubs R S = Collect (isUb R S)"


subsection {* Rules about the Operators @{term leastP}, @{term ub} and @{term lub} *}

lemma leastPD1: "leastP P x \<Longrightarrow> P x"
  by (simp add: leastP_def)

lemma leastPD2: "leastP P x \<Longrightarrow> x <=* Collect P"
  by (simp add: leastP_def)

lemma leastPD3: "leastP P x \<Longrightarrow> y: Collect P \<Longrightarrow> x \<le> y"
  by (blast dest!: leastPD2 setgeD)

lemma isLubD1: "isLub R S x \<Longrightarrow> S *<= x"
  by (simp add: isLub_def isUb_def leastP_def)

lemma isLubD1a: "isLub R S x \<Longrightarrow> x: R"
  by (simp add: isLub_def isUb_def leastP_def)

lemma isLub_isUb: "isLub R S x \<Longrightarrow> isUb R S x"
  unfolding isUb_def by (blast dest: isLubD1 isLubD1a)

lemma isLubD2: "isLub R S x \<Longrightarrow> y : S \<Longrightarrow> y \<le> x"
  by (blast dest!: isLubD1 setleD)

lemma isLubD3: "isLub R S x \<Longrightarrow> leastP (isUb R S) x"
  by (simp add: isLub_def)

lemma isLubI1: "leastP(isUb R S) x \<Longrightarrow> isLub R S x"
  by (simp add: isLub_def)

lemma isLubI2: "isUb R S x \<Longrightarrow> x <=* Collect (isUb R S) \<Longrightarrow> isLub R S x"
  by (simp add: isLub_def leastP_def)

lemma isUbD: "isUb R S x \<Longrightarrow> y : S \<Longrightarrow> y \<le> x"
  by (simp add: isUb_def setle_def)

lemma isUbD2: "isUb R S x \<Longrightarrow> S *<= x"
  by (simp add: isUb_def)

lemma isUbD2a: "isUb R S x \<Longrightarrow> x: R"
  by (simp add: isUb_def)

lemma isUbI: "S *<= x \<Longrightarrow> x: R \<Longrightarrow> isUb R S x"
  by (simp add: isUb_def)

lemma isLub_le_isUb: "isLub R S x \<Longrightarrow> isUb R S y \<Longrightarrow> x \<le> y"
  unfolding isLub_def by (blast intro!: leastPD3)

lemma isLub_ubs: "isLub R S x \<Longrightarrow> x <=* ubs R S"
  unfolding ubs_def isLub_def by (rule leastPD2)

lemma isLub_unique: "[| isLub R S x; isLub R S y |] ==> x = (y::'a::linorder)"
  apply (frule isLub_isUb)
  apply (frule_tac x = y in isLub_isUb)
  apply (blast intro!: order_antisym dest!: isLub_le_isUb)
  done

lemma isUb_UNIV_I: "(\<And>y. y \<in> S \<Longrightarrow> y \<le> u) \<Longrightarrow> isUb UNIV S u"
  by (simp add: isUbI setleI)


definition greatestP :: "('a \<Rightarrow> bool) \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "greatestP P x = (P x \<and> Collect P *<=  x)"

definition isLb :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isLb R S x = (x <=* S \<and> x: R)"

definition isGlb :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isGlb R S x = greatestP (isLb R S) x"

definition lbs :: "'a set \<Rightarrow> 'a::ord set \<Rightarrow> 'a set"
  where "lbs R S = Collect (isLb R S)"


subsection {* Rules about the Operators @{term greatestP}, @{term isLb} and @{term isGlb} *}

lemma greatestPD1: "greatestP P x \<Longrightarrow> P x"
  by (simp add: greatestP_def)

lemma greatestPD2: "greatestP P x \<Longrightarrow> Collect P *<= x"
  by (simp add: greatestP_def)

lemma greatestPD3: "greatestP P x \<Longrightarrow> y: Collect P \<Longrightarrow> x \<ge> y"
  by (blast dest!: greatestPD2 setleD)

lemma isGlbD1: "isGlb R S x \<Longrightarrow> x <=* S"
  by (simp add: isGlb_def isLb_def greatestP_def)

lemma isGlbD1a: "isGlb R S x \<Longrightarrow> x: R"
  by (simp add: isGlb_def isLb_def greatestP_def)

lemma isGlb_isLb: "isGlb R S x \<Longrightarrow> isLb R S x"
  unfolding isLb_def by (blast dest: isGlbD1 isGlbD1a)

lemma isGlbD2: "isGlb R S x \<Longrightarrow> y : S \<Longrightarrow> y \<ge> x"
  by (blast dest!: isGlbD1 setgeD)

lemma isGlbD3: "isGlb R S x \<Longrightarrow> greatestP (isLb R S) x"
  by (simp add: isGlb_def)

lemma isGlbI1: "greatestP (isLb R S) x \<Longrightarrow> isGlb R S x"
  by (simp add: isGlb_def)

lemma isGlbI2: "isLb R S x \<Longrightarrow> Collect (isLb R S) *<= x \<Longrightarrow> isGlb R S x"
  by (simp add: isGlb_def greatestP_def)

lemma isLbD: "isLb R S x \<Longrightarrow> y : S \<Longrightarrow> y \<ge> x"
  by (simp add: isLb_def setge_def)

lemma isLbD2: "isLb R S x \<Longrightarrow> x <=* S "
  by (simp add: isLb_def)

lemma isLbD2a: "isLb R S x \<Longrightarrow> x: R"
  by (simp add: isLb_def)

lemma isLbI: "x <=* S \<Longrightarrow> x: R \<Longrightarrow> isLb R S x"
  by (simp add: isLb_def)

lemma isGlb_le_isLb: "isGlb R S x \<Longrightarrow> isLb R S y \<Longrightarrow> x \<ge> y"
  unfolding isGlb_def by (blast intro!: greatestPD3)

lemma isGlb_ubs: "isGlb R S x \<Longrightarrow> lbs R S *<= x"
  unfolding lbs_def isGlb_def by (rule greatestPD2)

lemma isGlb_unique: "[| isGlb R S x; isGlb R S y |] ==> x = (y::'a::linorder)"
  apply (frule isGlb_isLb)
  apply (frule_tac x = y in isGlb_isLb)
  apply (blast intro!: order_antisym dest!: isGlb_le_isLb)
  done

lemma bdd_above_setle: "bdd_above A \<longleftrightarrow> (\<exists>a. A *<= a)"
  by (auto simp: bdd_above_def setle_def)

lemma bdd_below_setge: "bdd_below A \<longleftrightarrow> (\<exists>a. a <=* A)"
  by (auto simp: bdd_below_def setge_def)

lemma isLub_cSup: 
  "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> (\<exists>b. S *<= b) \<Longrightarrow> isLub UNIV S (Sup S)"
  by  (auto simp add: isLub_def setle_def leastP_def isUb_def
            intro!: setgeI cSup_upper cSup_least)

lemma isGlb_cInf: 
  "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> (\<exists>b. b <=* S) \<Longrightarrow> isGlb UNIV S (Inf S)"
  by  (auto simp add: isGlb_def setge_def greatestP_def isLb_def
            intro!: setleI cInf_lower cInf_greatest)

lemma cSup_le: "(S::'a::conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> S *<= b \<Longrightarrow> Sup S \<le> b"
  by (metis cSup_least setle_def)

lemma cInf_ge: "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> b <=* S \<Longrightarrow> Inf S \<ge> b"
  by (metis cInf_greatest setge_def)

lemma cSup_bounds:
  fixes S :: "'a :: conditionally_complete_lattice set"
  shows "S \<noteq> {} \<Longrightarrow> a <=* S \<Longrightarrow> S *<= b \<Longrightarrow> a \<le> Sup S \<and> Sup S \<le> b"
  using cSup_least[of S b] cSup_upper2[of _ S a]
  by (auto simp: bdd_above_setle setge_def setle_def)

lemma cSup_unique: "(S::'a :: {conditionally_complete_linorder, no_bot} set) *<= b \<Longrightarrow> (\<forall>b'<b. \<exists>x\<in>S. b' < x) \<Longrightarrow> Sup S = b"
  by (rule cSup_eq) (auto simp: not_le[symmetric] setle_def)

lemma cInf_unique: "b <=* (S::'a :: {conditionally_complete_linorder, no_top} set) \<Longrightarrow> (\<forall>b'>b. \<exists>x\<in>S. b' > x) \<Longrightarrow> Inf S = b"
  by (rule cInf_eq) (auto simp: not_le[symmetric] setge_def)

text{* Use completeness of reals (supremum property) to show that any bounded sequence has a least upper bound*}

lemma reals_complete: "\<exists>X. X \<in> S \<Longrightarrow> \<exists>Y. isUb (UNIV::real set) S Y \<Longrightarrow> \<exists>t. isLub (UNIV :: real set) S t"
  by (intro exI[of _ "Sup S"] isLub_cSup) (auto simp: setle_def isUb_def intro!: cSup_upper)

lemma Bseq_isUb: "\<And>X :: nat \<Rightarrow> real. Bseq X \<Longrightarrow> \<exists>U. isUb (UNIV::real set) {x. \<exists>n. X n = x} U"
  by (auto intro: isUbI setleI simp add: Bseq_def abs_le_iff)

lemma Bseq_isLub: "\<And>X :: nat \<Rightarrow> real. Bseq X \<Longrightarrow> \<exists>U. isLub (UNIV::real set) {x. \<exists>n. X n = x} U"
  by (blast intro: reals_complete Bseq_isUb)

lemma isLub_mono_imp_LIMSEQ:
  fixes X :: "nat \<Rightarrow> real"
  assumes u: "isLub UNIV {x. \<exists>n. X n = x} u" (* FIXME: use 'range X' *)
  assumes X: "\<forall>m n. m \<le> n \<longrightarrow> X m \<le> X n"
  shows "X ----> u"
proof -
  have "X ----> (SUP i. X i)"
    using u[THEN isLubD1] X
    by (intro LIMSEQ_incseq_SUP) (auto simp: incseq_def image_def eq_commute bdd_above_setle)
  also have "(SUP i. X i) = u"
    using isLub_cSup[of "range X"] u[THEN isLubD1]
    by (intro isLub_unique[OF _ u]) (auto simp add: SUP_def image_def eq_commute)
  finally show ?thesis .
qed

lemmas real_isGlb_unique = isGlb_unique[where 'a=real]

lemma real_le_inf_subset: "t \<noteq> {} \<Longrightarrow> t \<subseteq> s \<Longrightarrow> \<exists>b. b <=* s \<Longrightarrow> Inf s \<le> Inf (t::real set)"
  by (rule cInf_superset_mono) (auto simp: bdd_below_setge)

lemma real_ge_sup_subset: "t \<noteq> {} \<Longrightarrow> t \<subseteq> s \<Longrightarrow> \<exists>b. s *<= b \<Longrightarrow> Sup s \<ge> Sup (t::real set)"
  by (rule cSup_subset_mono) (auto simp: bdd_above_setle)

end
