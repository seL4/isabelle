(*  Title:      HOLCF/Lift1.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996 Technische Universitaet Muenchen

Theorems for Lift1.thy
*)


open Lift1;

(* ------------------------------------------------------------------------ *)
(* less_lift is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

Goalw [less_lift_def] "(x::'a lift) << x";
by (fast_tac HOL_cs 1);
qed"refl_less_lift";

Goalw [less_lift_def] 
  "[|(x1::'a lift) << x2; x2 << x1|] ==> x1 = x2";
by (fast_tac HOL_cs 1);
qed"antisym_less_lift";

Goalw [less_lift_def] 
  "[|(x1::'a lift) << x2; x2 << x3|] ==> x1 << x3";
by (fast_tac HOL_cs 1);
qed"trans_less_lift";
