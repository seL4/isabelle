(*  Title: 	HOL/ex/sorting.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994 TU Muenchen

Some general lemmas
*)

val sorting_ss = list_ss addsimps
      [Sorting.mset_Nil,Sorting.mset_Cons,
       Sorting.sorted_Nil,Sorting.sorted_Cons,
       Sorting.sorted1_Nil,Sorting.sorted1_One,Sorting.sorted1_Cons];

goal Sorting.thy "!x.mset (xs@ys) x = mset xs x + mset ys x";
by(list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (sorting_ss setloop (split_tac [expand_if]))));
qed "mset_app_distr";

goal Sorting.thy "!x. mset [x:xs. ~p(x)] x + mset [x:xs.p(x)] x = \
\                     mset xs x";
by(list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (sorting_ss setloop (split_tac [expand_if]))));
qed "mset_compl_add";

val sorting_ss = sorting_ss addsimps
      [mset_app_distr, mset_compl_add];
