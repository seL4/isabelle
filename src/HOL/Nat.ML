(*  Title:      HOL/Nat.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen
*)

goal thy "min 0 n = 0";
by (rtac min_leastL 1);
by (trans_tac 1);
qed "min_0L";

goal thy "min n 0 = 0";
by (rtac min_leastR 1);
by (trans_tac 1);
qed "min_0R";

goalw thy [min_def] "min (Suc m) (Suc n) = Suc(min m n)";
by (Simp_tac 1);
qed "min_Suc_Suc";

Addsimps [min_0L,min_0R,min_Suc_Suc];
