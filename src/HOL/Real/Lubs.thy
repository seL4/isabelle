(*  Title       : Lubs.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
*)

header{*Definitions of Upper Bounds and Least Upper Bounds*}

theory Lubs = Main:

text{*Thanks to suggestions by James Margetson*}

constdefs

  setle :: "['a set, 'a::ord] => bool"     (infixl "*<=" 70)
    "S *<= x    == (ALL y: S. y <= x)"

  setge :: "['a::ord, 'a set] => bool"     (infixl "<=*" 70)
    "x <=* S    == (ALL y: S. x <= y)"

  leastP      :: "['a =>bool,'a::ord] => bool"
    "leastP P x == (P x & x <=* Collect P)"

  isUb        :: "['a set, 'a set, 'a::ord] => bool"
    "isUb R S x   == S *<= x & x: R"

  isLub       :: "['a set, 'a set, 'a::ord] => bool"
    "isLub R S x  == leastP (isUb R S) x"

  ubs         :: "['a set, 'a::ord set] => 'a set"
    "ubs R S      == Collect (isUb R S)"



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

ML
{*
val setle_def = thm "setle_def";
val setge_def = thm "setge_def";
val leastP_def = thm "leastP_def";
val isLub_def = thm "isLub_def";
val isUb_def = thm "isUb_def";
val ubs_def = thm "ubs_def";

val setleI = thm "setleI";
val setleD = thm "setleD";
val setgeI = thm "setgeI";
val setgeD = thm "setgeD";
val leastPD1 = thm "leastPD1";
val leastPD2 = thm "leastPD2";
val leastPD3 = thm "leastPD3";
val isLubD1 = thm "isLubD1";
val isLubD1a = thm "isLubD1a";
val isLub_isUb = thm "isLub_isUb";
val isLubD2 = thm "isLubD2";
val isLubD3 = thm "isLubD3";
val isLubI1 = thm "isLubI1";
val isLubI2 = thm "isLubI2";
val isUbD = thm "isUbD";
val isUbD2 = thm "isUbD2";
val isUbD2a = thm "isUbD2a";
val isUbI = thm "isUbI";
val isLub_le_isUb = thm "isLub_le_isUb";
val isLub_ubs = thm "isLub_ubs";
*}

end
