(*  Title       : Lubs.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
*)

header{*Definitions of Upper Bounds and Least Upper Bounds*}

theory Lubs
imports Main
begin

text{*Thanks to suggestions by James Margetson*}

definition
  setle :: "['a set, 'a::ord] => bool"  (infixl "*<=" 70) where
  "S *<= x = (ALL y: S. y <= x)"

definition
  setge :: "['a::ord, 'a set] => bool"  (infixl "<=*" 70) where
  "x <=* S = (ALL y: S. x <= y)"

definition
  leastP      :: "['a =>bool,'a::ord] => bool" where
  "leastP P x = (P x & x <=* Collect P)"

definition
  isUb        :: "['a set, 'a set, 'a::ord] => bool" where
  "isUb R S x = (S *<= x & x: R)"

definition
  isLub       :: "['a set, 'a set, 'a::ord] => bool" where
  "isLub R S x = leastP (isUb R S) x"

definition
  ubs         :: "['a set, 'a::ord set] => 'a set" where
  "ubs R S = Collect (isUb R S)"



subsection{*Rules for the Relations @{text "*<="} and @{text "<=*"}*}

lemma setleI: "ALL y: S. y <= x ==> S *<= x"
by (simp add: setle_def)

lemma setleD: "[| S *<= x; y: S |] ==> y <= x"
by (simp add: setle_def)

lemma setgeI: "ALL y: S. x<= y ==> x <=* S"
by (simp add: setge_def)

lemma setgeD: "[| x <=* S; y: S |] ==> x <= y"
by (simp add: setge_def)


subsection{*Rules about the Operators @{term leastP}, @{term ub}
    and @{term lub}*}

lemma leastPD1: "leastP P x ==> P x"
by (simp add: leastP_def)

lemma leastPD2: "leastP P x ==> x <=* Collect P"
by (simp add: leastP_def)

lemma leastPD3: "[| leastP P x; y: Collect P |] ==> x <= y"
by (blast dest!: leastPD2 setgeD)

lemma isLubD1: "isLub R S x ==> S *<= x"
by (simp add: isLub_def isUb_def leastP_def)

lemma isLubD1a: "isLub R S x ==> x: R"
by (simp add: isLub_def isUb_def leastP_def)

lemma isLub_isUb: "isLub R S x ==> isUb R S x"
apply (simp add: isUb_def)
apply (blast dest: isLubD1 isLubD1a)
done

lemma isLubD2: "[| isLub R S x; y : S |] ==> y <= x"
by (blast dest!: isLubD1 setleD)

lemma isLubD3: "isLub R S x ==> leastP(isUb R S) x"
by (simp add: isLub_def)

lemma isLubI1: "leastP(isUb R S) x ==> isLub R S x"
by (simp add: isLub_def)

lemma isLubI2: "[| isUb R S x; x <=* Collect (isUb R S) |] ==> isLub R S x"
by (simp add: isLub_def leastP_def)

lemma isUbD: "[| isUb R S x; y : S |] ==> y <= x"
by (simp add: isUb_def setle_def)

lemma isUbD2: "isUb R S x ==> S *<= x"
by (simp add: isUb_def)

lemma isUbD2a: "isUb R S x ==> x: R"
by (simp add: isUb_def)

lemma isUbI: "[| S *<= x; x: R |] ==> isUb R S x"
by (simp add: isUb_def)

lemma isLub_le_isUb: "[| isLub R S x; isUb R S y |] ==> x <= y"
apply (simp add: isLub_def)
apply (blast intro!: leastPD3)
done

lemma isLub_ubs: "isLub R S x ==> x <=* ubs R S"
apply (simp add: ubs_def isLub_def)
apply (erule leastPD2)
done

end
