(*  Title:      HOL/AxClasses/Tutorial/Xor.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof the instantiation theorem bool :: agroup by hand.
*)

open AxClass;

goal_arity Xor.thy ("bool", [], "agroup");
by (axclass_tac Xor.thy []);
by (rewrite_goals_tac [Xor.prod_bool_def, Xor.inv_bool_def, Xor.unit_bool_def]);
by (ALLGOALS (Fast_tac));
qed "bool_in_agroup";
