(*  Title:      HOL/ex/sorting.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Some general lemmas
*)

goal Sorting.thy "!x. mset (xs@ys) x = mset xs x + mset ys x";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsplits [expand_if])));
qed "mset_append";

goal Sorting.thy "!x. mset [x:xs. ~p(x)] x + mset [x:xs. p(x)] x = \
\                     mset xs x";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsplits [expand_if])));
qed "mset_compl_add";

Addsimps [mset_append, mset_compl_add];

goal Sorting.thy "set xs = {x. mset xs x ~= 0}";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsplits [expand_if])));
by (Fast_tac 1);
qed "set_via_mset";

(* Equivalence of two definitions of `sorted' *)

val prems = goalw Sorting.thy [transf_def]
  "transf(le) ==> sorted1 le xs = sorted le xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsplits [split_list_case])));
by (cut_facts_tac prems 1);
by (Fast_tac 1);
qed "sorted1_is_sorted";
