(* Lift1.ML *)

open Lift1;

(* ------------------------------------------------------------------------ *)
(* less_lift is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

goalw Lift1.thy [less_lift_def] "less_lift x x";
by (fast_tac HOL_cs 1);
qed"refl_less_lift";

goalw Lift1.thy [less_lift_def] 
  "less_lift x1 x2 & less_lift x2 x1 --> x1 = x2";
by (fast_tac HOL_cs 1);
qed"antisym_less_lift";

goalw Lift1.thy [less_lift_def] 
  "less_lift x1 x2 & less_lift x2 x3 --> less_lift x1 x3";
by (fast_tac HOL_cs 1);
qed"trans_less_lift";
