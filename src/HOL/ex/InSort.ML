(*  Title:      HOL/ex/insort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Correctness proof of insertion sort.
*)

goal thy "!y. mset(ins f x xs) y = mset (x#xs) y";
by (list.induct_tac "xs" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
qed "mset_ins";
Addsimps [mset_ins];

goal thy "!x. mset(insort f xs) x = mset xs x";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "insort_permutes";

goal thy "set(ins f x xs) = insert x (set xs)";
by (asm_simp_tac (!simpset addsimps [set_of_list_via_mset]
                           setloop (split_tac [expand_if])) 1);
by (Fast_tac 1);
qed "set_of_list_ins";
Addsimps [set_of_list_ins];

val prems = goalw InSort.thy [total_def,transf_def]
  "[| total(f); transf(f) |] ==>  sorted f (ins f x xs) = sorted f xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (cut_facts_tac prems 1);
by (Fast_tac 1);
qed "sorted_ins";
Addsimps [sorted_ins];

goal InSort.thy "!!f. [| total(f); transf(f) |] ==>  sorted f (insort f xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "sorted_insort";
