(*  Title:      HOL/ex/qsort.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Two verifications of Quicksort
*)

Addsimps [ball_Un];

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
by (ALLGOALS(asm_simp_tac (!simpset addsplits [expand_if])));
qed "qsort_permutes";

goal Qsort.thy "set(qsort le xs) = set xs";
by(simp_tac (!simpset addsimps [set_via_mset,qsort_permutes]) 1);
qed "set_qsort";
Addsimps [set_qsort];

goal List.thy
  "(!x:set[x:xs. P(x)].Q(x)) = (!x:set xs. P(x)-->Q(x))";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset addsplits [expand_if])));
qed"Ball_set_filter";
Addsimps [Ball_set_filter];

goal Qsort.thy
 "sorted le (xs@ys) = (sorted le xs & sorted le ys & \
\                     (!x:set xs. !y:set ys. le x y))";
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
