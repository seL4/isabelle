(*  Title:      HOLCF/Lift1.ML
    ID:         $Id$
    Author:     Olaf Mueller, Robert Sandner
    Copyright   1996 Technische Universitaet Muenchen

Theorems for Lift1.thy
*)


open Lift1;

(* ------------------------------------------------------------------------ *)
(* less_lift is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

goalw thy [less_lift_def] "less (x::'a lift) x";
by (fast_tac HOL_cs 1);
qed"refl_less_lift";

val prems = goalw thy [less_lift_def] 
  "[|less (x1::'a lift) x2; less x2 x1|] ==> x1 = x2";
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
qed"antisym_less_lift";

val prems = goalw Lift1.thy [less_lift_def] 
  "[|less (x1::'a lift) x2; less x2 x3|] ==> less x1 x3";
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
qed"trans_less_lift";
