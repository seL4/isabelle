(*  Title:      ZF/AC/AC0_AC1.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

AC0 is equivalent to AC1
AC0 comes from Suppes, AC1 from Rubin & Rubin
*)

goal thy "!!A. 0~:A ==> A <= Pow(Union(A))-{0}";
by (fast_tac AC_cs 1);
val subset_Pow_Union = result();

goal thy "!!f. [| f:(PROD X:A. X); D<=A |] ==> EX g. g:(PROD X:D. X)";
by (fast_tac (AC_cs addSIs [restrict_type, apply_type]) 1);
val lemma1 = result();

goalw thy AC_defs "!!Z. AC0 ==> AC1"; 
by (fast_tac (FOL_cs addSEs [lemma1, subset_Pow_Union]) 1);
qed "AC0_AC1";

goalw thy AC_defs "!!Z. AC1 ==> AC0";
by (fast_tac (FOL_cs addSIs [notI, singletonI] addSEs [notE, DiffE]) 1);
qed "AC1_AC0";
