(*  Title:      ZF/AC/AC1_WO2.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> WO2
*)

(*Establishing the existence of a bijection -- hence the need for uresult*)
val [prem] = goal thy "f \\<in> (\\<Pi>X \\<in> Pow(x) - {0}. X) ==>  \
\       ?g(f) \\<in> bij(x, LEAST i. HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X}, x, i) = {x})";
by (resolve_tac [bij_Least_HH_x RS bij_converse_bij] 1);
by (rtac f_subsets_imp_UN_HH_eq_x 1);
by (resolve_tac [lam_type RS apply_type] 1 THEN (assume_tac 2));
by (fast_tac (claset() addSDs [prem RS apply_type]) 1);
by (fast_tac (claset() addSIs [prem RS Pi_weaken_type]) 1);
val lemma1 = uresult() |> standard;

Goalw [AC1_def, WO2_def, eqpoll_def] "AC1 ==> WO2";
by (rtac allI 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (fast_tac (claset() addSDs [lemma1] addSIs [Ord_Least]) 1);
qed "AC1_WO2";
