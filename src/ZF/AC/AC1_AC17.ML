(*  Title:      ZF/AC/AC1_AC17.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> AC17
*)

goal thy "!!f. f : (PROD X:Pow(A) - {0}. X) ==> f : (Pow(A) - {0} -> A)";
by (rtac Pi_type 1 THEN (assume_tac 1));
by (dtac apply_type 1 THEN (assume_tac 1));
by (Fast_tac 1);
val lemma1 = result();

goalw thy AC_defs "!!Z. AC1 ==> AC17";
by (rtac allI 1);
by (rtac ballI 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (etac impE 1);
by (Fast_tac 1);
by (etac exE 1);
by (rtac bexI 1);
by (etac lemma1 2);
by (rtac apply_type 1 THEN (assume_tac 1));
by (fast_tac (!claset addSDs [lemma1] addSEs [apply_type]) 1);
qed "AC1_AC17";
