(*  Title:      HOL/ex/Qsort.ML
    ID:         $Id$
    Author:     Tobias Nipkow (tidied by lcp)
    Copyright   1994 TU Muenchen

The verification of Quicksort
*)

(*** Version one: higher-order ***)

Goal "multiset (qsort(le,xs)) x = multiset xs x";
by (res_inst_tac [("v","xs"),("u","le")] qsort.induct 1);
by Auto_tac;
qed "qsort_permutes";
Addsimps [qsort_permutes];

(*Also provable by induction*)
Goal "set (qsort(le,xs)) = set xs";
by (simp_tac (simpset() addsimps [set_via_multiset]) 1);
qed "set_qsort";
Addsimps [set_qsort];

Goal "total(le) --> transf(le) --> sorted le (qsort(le,xs))";
by (res_inst_tac [("v","xs"),("u","le")] qsort.induct 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [Sorting.total_def, Sorting.transf_def]);
by (Blast_tac 1);
qed_spec_mp "sorted_qsort";


(*** Version two: type classes ***)

Goal "multiset (quickSort xs) z = multiset xs z";
by (res_inst_tac [("u","xs")] quickSort.induct 1);
by Auto_tac;
qed "quickSort_permutes";
Addsimps [quickSort_permutes];

(*Also provable by induction*)
Goal "set (quickSort xs) = set xs";
by (simp_tac (simpset() addsimps [set_via_multiset]) 1);
qed "set_quickSort";
Addsimps [set_quickSort];

Goal "sorted (op <=) (quickSort xs)";
by (res_inst_tac [("u","xs")] quickSort.induct 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addIs [linorder_linear RS disjE, order_trans]) 1);
qed_spec_mp "sorted_quickSort";
