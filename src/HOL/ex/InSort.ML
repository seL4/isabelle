(*  Title:      HOL/ex/insort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Correctness proof of insertion sort.
*)

Goal "!y. multiset(ins le x xs) y = multiset (x#xs) y";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "multiset_ins";
Addsimps [multiset_ins];

Goal "!x. multiset(insort le xs) x = multiset xs x";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "insort_permutes";

Goal "set(ins le x xs) = insert x (set xs)";
by (asm_simp_tac (simpset() addsimps [set_via_multiset]) 1);
by (Fast_tac 1);
qed "set_ins";
Addsimps [set_ins];

Goal "total(le) --> transf(le) --> sorted le (ins le x xs) = sorted le xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [Sorting.total_def, Sorting.transf_def]);
by (Blast_tac 1);
qed_spec_mp "sorted_ins";
Addsimps [sorted_ins];

Goal "[| total(le); transf(le) |] ==>  sorted le (insort le xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "sorted_insort";
