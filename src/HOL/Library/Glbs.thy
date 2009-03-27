(* Author: Amine Chaieb, University of Cambridge *)

header {* Definitions of Lower Bounds and Greatest Lower Bounds, analogous to Lubs *}

theory Glbs
imports Lubs
begin

definition
  greatestP      :: "['a =>bool,'a::ord] => bool" where
  "greatestP P x = (P x & Collect P *<=  x)"

definition
  isLb        :: "['a set, 'a set, 'a::ord] => bool" where
  "isLb R S x = (x <=* S & x: R)"

definition
  isGlb       :: "['a set, 'a set, 'a::ord] => bool" where
  "isGlb R S x = greatestP (isLb R S) x"

definition
  lbs         :: "['a set, 'a::ord set] => 'a set" where
  "lbs R S = Collect (isLb R S)"

subsection{*Rules about the Operators @{term greatestP}, @{term isLb}
    and @{term isGlb}*}

lemma leastPD1: "greatestP P x ==> P x"
by (simp add: greatestP_def)

lemma greatestPD2: "greatestP P x ==> Collect P *<= x"
by (simp add: greatestP_def)

lemma greatestPD3: "[| greatestP P x; y: Collect P |] ==> x >= y"
by (blast dest!: greatestPD2 setleD)

lemma isGlbD1: "isGlb R S x ==> x <=* S"
by (simp add: isGlb_def isLb_def greatestP_def)

lemma isGlbD1a: "isGlb R S x ==> x: R"
by (simp add: isGlb_def isLb_def greatestP_def)

lemma isGlb_isLb: "isGlb R S x ==> isLb R S x"
apply (simp add: isLb_def)
apply (blast dest: isGlbD1 isGlbD1a)
done

lemma isGlbD2: "[| isGlb R S x; y : S |] ==> y >= x"
by (blast dest!: isGlbD1 setgeD)

lemma isGlbD3: "isGlb R S x ==> greatestP(isLb R S) x"
by (simp add: isGlb_def)

lemma isGlbI1: "greatestP(isLb R S) x ==> isGlb R S x"
by (simp add: isGlb_def)

lemma isGlbI2: "[| isLb R S x; Collect (isLb R S) *<= x |] ==> isGlb R S x"
by (simp add: isGlb_def greatestP_def)

lemma isLbD: "[| isLb R S x; y : S |] ==> y >= x"
by (simp add: isLb_def setge_def)

lemma isLbD2: "isLb R S x ==> x <=* S "
by (simp add: isLb_def)

lemma isLbD2a: "isLb R S x ==> x: R"
by (simp add: isLb_def)

lemma isLbI: "[| x <=* S ; x: R |] ==> isLb R S x"
by (simp add: isLb_def)

lemma isGlb_le_isLb: "[| isGlb R S x; isLb R S y |] ==> x >= y"
apply (simp add: isGlb_def)
apply (blast intro!: greatestPD3)
done

lemma isGlb_ubs: "isGlb R S x ==> lbs R S *<= x"
apply (simp add: lbs_def isGlb_def)
apply (erule greatestPD2)
done

end
