(*  Title:      ZF/AC/AC1_WO2.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> WO2
*)

open AC1_WO2;

(*Establishing the existence of a bijection -- hence the need for uresult*)
val [prem] = goal thy "f : (PROD X:Pow(x) - {0}. X) ==>  \
\       ?g(f) : bij(x, LEAST i. HH(lam X:Pow(x)-{0}. {f`X}, x, i) = {x})";
by (resolve_tac [bij_Least_HH_x RS bij_converse_bij] 1);
by (rtac f_subsets_imp_UN_HH_eq_x 1);
by (resolve_tac [lam_type RS apply_type] 1 THEN (assume_tac 2));
by (fast_tac (AC_cs addSDs [equals0D, prem RS apply_type]) 1);
by (fast_tac (AC_cs addSIs [prem RS Pi_weaken_type]) 1);
val lemma1 = uresult() |> standard;

goalw thy [AC1_def, WO2_def, eqpoll_def] "!!Z. AC1 ==> WO2";
by (rtac allI 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (fast_tac (AC_cs addSDs [lemma1] addSIs [Ord_Least]) 1);
qed "AC1_WO2";
