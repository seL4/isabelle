(*  Title: 	ZF/AC/WO_AC.ML
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Lemmas used in the proofs like WO? ==> AC?
*)

open WO_AC;

goal thy "!!A. [| well_ord(Union(A),r); 0~:A; B:A |]  \
\		==> (THE b. first(b,B,r)) : B";
by (fast_tac (AC_cs addSEs [well_ord_imp_ex1_first RS theI RS
		(first_def RS def_imp_iff RS iffD1 RS conjunct1)]) 1);
val first_in_B = result();

goal thy "!!A. [| well_ord(Union(A), R); 0~:A |] ==> EX f. f:(PROD X:A. X)";
by (fast_tac (AC_cs addSEs [first_in_B] addSIs [lam_type]) 1);
val ex_choice_fun = result();

goal thy "!!A. well_ord(A, R) ==> EX f. f:(PROD X: Pow(A)-{0}. X)";
by (fast_tac (AC_cs addSEs [well_ord_subset RS ex_choice_fun]) 1);
val ex_choice_fun_Pow = result();
