(*  Title:      HOL/ex/qsort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Two verifications of Quicksort
*)

Addsimps ([Qsort.qsort_Nil,Qsort.qsort_Cons]@conj_comms);

goal Qsort.thy "!x. mset (qsort le xs) x = mset xs x";
by(res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by(ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
result();


goal Qsort.thy "(Alls x:[x:xs.P(x)].Q(x)) = (Alls x:xs. P(x)-->Q(x))";
by(list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
Addsimps [result()];

goal Qsort.thy
 "((Alls x:xs.P(x)) & (Alls x:xs.Q(x))) = (Alls x:xs. P(x)&Q(x))";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
val alls_lemma=result();
Addsimps [alls_lemma];

goal HOL.thy "((P --> Q) & (~P --> Q)) = Q";
by(fast_tac HOL_cs 1);
val lemma = result();

goal Qsort.thy "(Alls x:qsort le xs.P(x))  =  (Alls x:xs.P(x))";
by(res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by(Asm_simp_tac 1);
by(asm_simp_tac (!simpset delsimps [alls_lemma, list_all_Cons])1);
by(asm_simp_tac (!simpset addsimps [lemma]) 1);
Addsimps [result()];

goal Qsort.thy
 "sorted le (xs@ys) = (sorted le xs & sorted le ys & \
\                     (Alls x:xs. Alls y:ys. le x y))";
by(list.induct_tac "xs" 1);
by(Asm_simp_tac 1);
by(asm_simp_tac (!simpset delsimps [alls_lemma]) 1);
Addsimps [result()];




goal Qsort.thy 
 "!!le. [| total(le); transf(le) |] ==>  sorted le (qsort le xs)";
by(res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by(Asm_simp_tac 1);
by(asm_full_simp_tac (!simpset addsimps []) 1);
by(asm_full_simp_tac (!simpset addsimps [list_all_mem_conv]) 1);
by(rewrite_goals_tac [Sorting.total_def,Sorting.transf_def]);
by(fast_tac HOL_cs 1);
result();

(* A verification based on predicate calculus rather than combinators *)

val sorted_Cons =
  rewrite_rule [list_all_mem_conv RS eq_reflection] Sorting.sorted_Cons;

Addsimps [sorted_Cons];


goal Qsort.thy "x mem qsort le xs = x mem xs";
by(res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by(ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by(fast_tac HOL_cs 1);
Addsimps [result()];

goal Qsort.thy
 "sorted le (xs@ys) = (sorted le xs & sorted le ys & \
\                     (!x. x mem xs --> (!y. y mem ys --> le x y)))";
by(list.induct_tac "xs" 1);
by(Asm_simp_tac 1);
by(asm_simp_tac (!simpset setloop (split_tac [expand_if])
			  delsimps [list_all_conj]
			  addsimps [list_all_mem_conv]) 1);
by(fast_tac HOL_cs 1);
Addsimps [result()];

goal Qsort.thy
  "!!xs. [| total(le); transf(le) |] ==>  sorted le (qsort le xs)";
by(res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by(Simp_tac 1);
by(asm_simp_tac (!simpset setloop (split_tac [expand_if])
			  delsimps [list_all_conj]
			  addsimps [list_all_mem_conv]) 1);
by(rewrite_goals_tac [Sorting.total_def,Sorting.transf_def]);
by(fast_tac HOL_cs 1);
result();


