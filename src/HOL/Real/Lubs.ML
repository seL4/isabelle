(*  Title       : Lubs.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Completeness of the reals. A few of the 
                  definitions suggested by James Margetson
*) 

(*------------------------------------------------------------------------
                        Rules for *<= and <=*
 ------------------------------------------------------------------------*)
Goalw [setle_def] "ALL y: S. y <= x ==> S *<= x";
by (assume_tac 1);
qed "setleI";

Goalw [setle_def] "[| S *<= x; y: S |] ==> y <= x";
by (Fast_tac 1);
qed "setleD";

Goalw [setge_def] "ALL y: S. x<= y ==> x <=* S";
by (assume_tac 1);
qed "setgeI";

Goalw [setge_def] "[| x <=* S; y: S |] ==> x <= y";
by (Fast_tac 1);
qed "setgeD";

(*------------------------------------------------------------------------
                        Rules about leastP, ub and lub
 ------------------------------------------------------------------------*)
Goalw [leastP_def] "leastP P x ==> P x";
by (Step_tac 1);
qed "leastPD1";

Goalw [leastP_def] "leastP P x ==> x <=* Collect P";
by (Step_tac 1);
qed "leastPD2";

Goal "[| leastP P x; y: Collect P |] ==> x <= y";
by (blast_tac (claset() addSDs [leastPD2,setgeD]) 1);
qed "leastPD3";

Goalw [isLub_def,isUb_def,leastP_def] 
      "isLub R S x ==> S *<= x";
by (Step_tac 1);
qed "isLubD1";

Goalw [isLub_def,isUb_def,leastP_def] 
      "isLub R S x ==> x: R";
by (Step_tac 1);
qed "isLubD1a";

Goalw [isUb_def] "isLub R S x ==> isUb R S x";
by (blast_tac (claset() addDs [isLubD1,isLubD1a]) 1);
qed "isLub_isUb";

Goal "[| isLub R S x; y : S |] ==> y <= x";
by (blast_tac (claset() addSDs [isLubD1,setleD]) 1);
qed "isLubD2";

Goalw [isLub_def] "isLub R S x ==> leastP(isUb R S) x";
by (assume_tac 1);
qed "isLubD3";

Goalw [isLub_def] "leastP(isUb R S) x ==> isLub R S x";
by (assume_tac 1);
qed "isLubI1";

Goalw [isLub_def,leastP_def] 
      "[| isUb R S x; x <=* Collect (isUb R S) |] ==> isLub R S x";
by (Step_tac 1);
qed "isLubI2";

Goalw [isUb_def] "[| isUb R S x; y : S |] ==> y <= x";
by (fast_tac (claset() addDs [setleD]) 1);
qed "isUbD";

Goalw [isUb_def] "isUb R S x ==> S *<= x";
by (Step_tac 1);
qed "isUbD2";

Goalw [isUb_def] "isUb R S x ==> x: R";
by (Step_tac 1);
qed "isUbD2a";

Goalw [isUb_def] "[| S *<= x; x: R |] ==> isUb R S x";
by (Step_tac 1);
qed "isUbI";

Goalw [isLub_def] "[| isLub R S x; isUb R S y |] ==> x <= y";
by (blast_tac (claset() addSIs [leastPD3]) 1);
qed "isLub_le_isUb";

Goalw [ubs_def,isLub_def] "isLub R S x ==> x <=* ubs R S";
by (etac leastPD2 1);
qed "isLub_ubs";




