(*  Title:      HOL/ex/sorting.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Some general lemmas
*)

Goal "!x. mset (xs@ys) x = mset xs x + mset ys x";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mset_append";

Goal "!x. mset [x:xs. ~p(x)] x + mset [x:xs. p(x)] x = \
\                     mset xs x";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mset_compl_add";

Addsimps [mset_append, mset_compl_add];

Goal "set xs = {x. mset xs x ~= 0}";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
qed "set_via_mset";

(* Equivalence of two definitions of `sorted' *)

val prems = goalw Sorting.thy [transf_def]
  "transf(le) ==> sorted1 le xs = sorted le xs";
by (induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsplits [list.split])));
by (cut_facts_tac prems 1);
by (Fast_tac 1);
qed "sorted1_is_sorted";
