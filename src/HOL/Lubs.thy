(*  Title:      HOL/Lubs.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
*)

header {* Definitions of Upper Bounds and Least Upper Bounds *}

theory Lubs
imports Main
begin

text {* Thanks to suggestions by James Margetson *}

definition setle :: "'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"  (infixl "*<=" 70)
  where "S *<= x = (ALL y: S. y \<le> x)"

definition setge :: "'a::ord \<Rightarrow> 'a set \<Rightarrow> bool"  (infixl "<=*" 70)
  where "x <=* S = (ALL y: S. x \<le> y)"

definition leastP :: "('a \<Rightarrow> bool) \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "leastP P x = (P x \<and> x <=* Collect P)"

definition isUb :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isUb R S x = (S *<= x \<and> x: R)"

definition isLub :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::ord \<Rightarrow> bool"
  where "isLub R S x = leastP (isUb R S) x"

definition ubs :: "'a set \<Rightarrow> 'a::ord set \<Rightarrow> 'a set"
  where "ubs R S = Collect (isUb R S)"


subsection {* Rules for the Relations @{text "*<="} and @{text "<=*"} *}

lemma setleI: "ALL y: S. y \<le> x \<Longrightarrow> S *<= x"
  by (simp add: setle_def)

lemma setleD: "S *<= x \<Longrightarrow> y: S \<Longrightarrow> y \<le> x"
  by (simp add: setle_def)

lemma setgeI: "ALL y: S. x \<le> y \<Longrightarrow> x <=* S"
  by (simp add: setge_def)

lemma setgeD: "x <=* S \<Longrightarrow> y: S \<Longrightarrow> x \<le> y"
  by (simp add: setge_def)


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

end
