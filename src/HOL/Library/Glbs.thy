(* Author: Amine Chaieb, University of Cambridge *)

header {* Definitions of Lower Bounds and Greatest Lower Bounds, analogous to Lubs *}

theory Glbs
imports Lubs
begin

definition greatestP :: "('a \<Rightarrow> bool) \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "greatestP P x = (P x \<and> Collect P *<=  x)"

definition isLb :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isLb R S x = (x <=* S \<and> x: R)"

definition isGlb :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isGlb R S x = greatestP (isLb R S) x"

definition lbs :: "'a set \<Rightarrow> 'a::ord set \<Rightarrow> 'a set"
  where "lbs R S = Collect (isLb R S)"


subsection {* Rules about the Operators @{term greatestP}, @{term isLb}
  and @{term isGlb} *}

lemma leastPD1: "greatestP P x \<Longrightarrow> P x"
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

end
