(*  Title:      HOL/ex/insort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Correctness proof of insertion sort.
*)

Goal "!y. mset(ins f x xs) y = mset (x#xs) y";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mset_ins";
Addsimps [mset_ins];

Goal "!x. mset(insort f xs) x = mset xs x";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "insort_permutes";

Goal "set(ins f x xs) = insert x (set xs)";
by (asm_simp_tac (simpset() addsimps [set_via_mset]) 1);
by (Fast_tac 1);
qed "set_ins";
Addsimps [set_ins];

val prems = goalw InSort.thy [total_def,transf_def]
  "[| total(f); transf(f) |] ==>  sorted f (ins f x xs) = sorted f xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (cut_facts_tac prems 1);
by (Fast_tac 1);
qed "sorted_ins";
Addsimps [sorted_ins];

Goal "[| total(f); transf(f) |] ==>  sorted f (insort f xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "sorted_insort";
