(*  Title:      HOL/ex/qsort.ML
    ID:         $Id$
    Author:     Tobias Nipkow (tidied by lcp)
    Copyright   1994 TU Muenchen

The verification of Quicksort
*)

Addsimps qsort.rules;

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

Goal "total(le) & transf(le) --> sorted le (qsort(le,xs))";
by (res_inst_tac [("v","xs"),("u","le")] qsort.induct 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [Sorting.total_def, Sorting.transf_def]);
by (Blast_tac 1);
qed_spec_mp "sorted_qsort";
