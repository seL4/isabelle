
open washing;

(* "activate" definitions for use in proof *)

val changeI = [context1] RL ([change] RLN (2,[cut]));
val load1I =  [context1] RL ([load1]  RLN (2,[cut]));
val washI =   [context1] RL ([wash]   RLN (2,[cut]));
val dryI =    [context1] RL ([dry]    RLN (2,[cut]));



(* a load of dirty clothes and two dollars gives you clean clothes *)

Goal "dollar , dollar , dirty |- clean";

by (best_tac (lazy_cs add_safes (changeI @ load1I @ washI @ dryI)) 1);


(* order of premises doesn't matter *)

prove_goal thy "dollar , dirty , dollar |- clean"
(fn _ => [best_tac (lazy_cs add_safes (changeI @ load1I @ washI @ dryI)) 1]);


(* alternative formulation *)

prove_goal thy "dollar , dollar |- dirty -o clean"
(fn _ => [best_tac (lazy_cs add_safes (changeI @ load1I @ washI @ dryI)) 1]);




