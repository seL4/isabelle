(*  Title:      HOL/ex/insort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Correctness proof of insertion sort.
*)

goalw InSort.thy [Sorting.total_def]
  "!!f. [| total(f); ~f x y |] ==> f y x";
by (Fast_tac 1);
qed "totalD";

goalw InSort.thy [Sorting.transf_def]
  "!!f. [| transf(f); f b a |] ==> !x. f a x --> f b x";
by (Fast_tac 1);
qed "transfD";

goal InSort.thy "list_all p (ins f x xs) = (list_all p xs & p(x))";
by (list.induct_tac "xs" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (Fast_tac 1);
Addsimps [result()];

goal InSort.thy "(!x. p(x) --> q(x)) --> list_all p xs --> list_all q xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "list_all_imp";

val prems = goal InSort.thy
  "[| total(f); transf(f) |] ==>  sorted f (ins f x xs) = sorted f xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (cut_facts_tac prems 1);
by (cut_inst_tac [("p","f(a)"),("q","f(x)")] list_all_imp 1);
by (fast_tac (!claset addDs [totalD,transfD]) 1);
Addsimps [result()];

goal InSort.thy "!!f. [| total(f); transf(f) |] ==>  sorted f (insort f xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "sorted_insort";

