(*  Title:      HOL/ex/sorting.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Some general lemmas
*)

Goal "multiset (xs@ys) x = multiset xs x + multiset ys x";
by (induct_tac "xs" 1);
by Auto_tac;
qed "multiset_append";

Goal "multiset [x:xs. ~p(x)] x + multiset [x:xs. p(x)] x = multiset xs x";
by (induct_tac "xs" 1);
by Auto_tac;
qed "multiset_compl_add";

Addsimps [multiset_append, multiset_compl_add];

Goal "set xs = {x. multiset xs x ~= 0}";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_via_multiset";

(* Equivalence of two definitions of `sorted' *)

Goal "transf(le) ==> sorted1 le xs = sorted le xs";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [list.split])));
by (rewrite_goals_tac [transf_def]);
by (Blast_tac 1);
qed "sorted1_is_sorted";

Goal "sorted le (xs@ys) = (sorted le xs & sorted le ys & \
\                         (ALL x:set xs. ALL y:set ys. le x y))";
by (induct_tac "xs" 1);
by Auto_tac;
qed "sorted_append";
Addsimps [sorted_append];

