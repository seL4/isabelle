(*  Title:      ZF/AC/WO_AC.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Lemmas used in the proofs like WO? ==> AC?
*)

Goal "[| well_ord(Union(A),r); 0\\<notin>A; B \\<in> A |]  \
\               ==> (THE b. first(b,B,r)) \\<in> B";
by (fast_tac (claset() addSEs [well_ord_imp_ex1_first RS theI RS
                (first_def RS def_imp_iff RS iffD1 RS conjunct1)]) 1);
qed "first_in_B";

Goal "[| well_ord(Union(A), R); 0\\<notin>A |] ==> \\<exists>f. f:(\\<Pi>X \\<in> A. X)";
by (fast_tac (claset() addSEs [first_in_B] addSIs [lam_type]) 1);
qed "ex_choice_fun";

Goal "well_ord(A, R) ==> \\<exists>f. f:(\\<Pi>X \\<in> Pow(A)-{0}. X)";
by (fast_tac (claset() addSEs [well_ord_subset RS ex_choice_fun]) 1);
qed "ex_choice_fun_Pow";
