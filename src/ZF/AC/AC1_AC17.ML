(*  Title: 	ZF/AC/AC1_AC17.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

The proof of AC1 ==> AC17
*)

goal thy "!!f. f : (PROD X:Pow(A) - {0}. X) ==> f : (Pow(A) - {0} -> A)";
by (resolve_tac [Pi_type] 1 THEN (assume_tac 1));
by (dresolve_tac [apply_type] 1 THEN (assume_tac 1));
by (fast_tac AC_cs 1);
val lemma1 = result();

goalw thy AC_defs "!!Z. AC1 ==> AC17";
by (resolve_tac [allI] 1);
by (resolve_tac [ballI] 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (eresolve_tac [impE] 1);
by (fast_tac AC_cs 1);
by (eresolve_tac [exE] 1);
by (resolve_tac [bexI] 1);
by (eresolve_tac [lemma1] 2);
by (resolve_tac [apply_type] 1 THEN (assume_tac 1));
by (fast_tac (AC_cs addSDs [lemma1] addSEs [apply_type]) 1);
result();