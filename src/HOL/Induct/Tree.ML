(*  Title:      HOL/Induct/Tree.ML
    ID:         $Id$
    Author:     Stefan Berghofer,  TU Muenchen
    Copyright   1999  TU Muenchen

Infinitely branching trees
*)

Goal "map_tree g (map_tree f t) = map_tree (g o f) t";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "tree_map_compose";

val prems = Goal "(!!x. P x ==> Q (f x)) ==>  \
   \    exists_tree P ts --> exists_tree Q (map_tree f ts)";
by (induct_tac "ts" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
by (Fast_tac 1);
qed "exists_map";

