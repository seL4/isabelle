(*  Title:      HOL/ex/qsort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Two verifications of Quicksort
*)


Addsimps [Ball_insert,Ball_Un];

(* Towards a proof of qsort_ind

A short proof of Konrad's wf_minimal in WF1.ML:

val [p1] = goalw WF.thy [wf_def]
"wf(R) ==> (!Q. (? x. Q x) --> (? min. Q min & (!b. (b,min):R --> (~ Q b))))";
by (rtac allI 1);
by(cut_inst_tac[("x","%u.~Q u")](p1 RS spec) 1);
by (fast_tac HOL_cs 1);
val wf_minimal = result();

*)


Addsimps ([Qsort.qsort_Nil,Qsort.qsort_Cons]@conj_comms);

goal Qsort.thy "!x. mset (qsort le xs) x = mset xs x";
by (res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "qsort_permutes";

goal Sorting.thy "set_of_list xs = {x.mset xs x ~= 0}";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (Fast_tac 1);
qed "set_of_list_via_mset";

goal Qsort.thy "set_of_list(qsort le xs) = set_of_list xs";
by(simp_tac (!simpset addsimps [set_of_list_via_mset,qsort_permutes]) 1);
qed "set_of_list_qsort";
Addsimps [set_of_list_qsort];

goal List.thy
  "(!x:set_of_list[x:xs.P(x)].Q(x)) = (!x:set_of_list xs. P(x)-->Q(x))";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed"Ball_set_of_list_filter";
Addsimps [Ball_set_of_list_filter];

goal Qsort.thy
 "sorted le (xs@ys) = (sorted le xs & sorted le ys & \
\                     (!x:set_of_list xs. !y:set_of_list ys. le x y))";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "sorted_append";
Addsimps [sorted_append];

goal Qsort.thy 
 "!!le. [| total(le); transf(le) |] ==>  sorted le (qsort le xs)";
by (res_inst_tac[("xs","xs"),("p","le")]Qsort.qsort_ind 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [Sorting.total_def,Sorting.transf_def]);
by (Fast_tac 1);
qed "sorted_qsort";
