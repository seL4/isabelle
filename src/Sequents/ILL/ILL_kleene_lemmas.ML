
(* from [kleene 52] pp 118,119 *)


val k49a = auto1 "|- [* A > ( - ( - A)) *]";

val k49b = auto1 "|- [*( - ( - ( - A))) = ( - A)*]";

val k49c = auto1 "|- [* (A | - A) > ( - - A = A) *]";

val k50a = auto2 "|- [* - (A = - A) *]";

(*
         [rtac impr_contract 1 THEN REPEAT (rtac conj_lemma 1),
	  res_inst_tac [("A","!((! A) -o 0)")] cut 1
	  THEN rtac context1 1
	  THEN ALLGOALS (best_tac power_cs)]);
*)

val k51a = auto2 "|- [* - - (A | - A) *]";
    
val k51b = auto2 "|- [* - - (- - A > A) *]";
    
val k56a = auto1 "|- [* (A | B) > - (- A & - B) *]";

val k56b = auto1 "|- [* (-A | B) > - (A & -B) *]";
    
val k57a = auto1 "|- [* (A & B) > - (-A | -B) *]";
    
val k57b = auto2 "|- [* (A & -B) > -(-A | B) *]";
    
val k58a = auto1 "|- [* (A > B) > - (A & -B) *]";
    
val k58b = auto1 "|- [* (A > -B) = -(A & B) *]";
    
val k58c = auto1 "|- [* - (A & B) = (- - A > - B) *]";
    
val k58d = auto1 "|- [* (- - A > - B) = - - (-A | -B) *]";
    
val k58e = auto1 "! [* - -B > B *] |- [* (- -A > B) = (A > B) *]";
    
val k58f = auto1 "! [* - -B > B *] |- [* (A > B) = - (A & -B) *]";
    
val k58g = auto1 "|- [* (- -A > B) > - (A & -B) *]";
    
val k59a = auto1 "|- [* (-A | B) > (A > B) *]";

val k59b = auto2 "|- [* (A > B) > - - (-A | B) *]";
    
val k59c = auto2 "|- [* (-A > B) > - -(A | B) *]";
    
val k60a = auto1 "|- [* (A & B) > - (A > -B) *]";
    
val k60b = auto1 "|- [* (A & -B) > - (A > B) *]";
    
val k60c = auto1 "|- [* ( - - A & B) > - (A > -B) *]";
    
val k60d = auto1 "|- [* (- - A & - B) = - (A > B) *]";
    
val k60e = auto1 "|- [* - (A > B) = - (-A | B) *]";
    
val k60f = auto1 "|- [* - (-A | B) = - - (A & -B) *]";
    
val k60g = auto2 "|- [* - - (A > B) = - (A & -B) *]";
    
(*
 [step_tac safe_cs 1, best_tac safe_cs 1,
 rtac impr 1 THEN rtac impr_contract 1
 THEN best_tac safe_cs 1];
*)

val k60h = auto1 "|- [* - (A & -B) = (A > - -B) *]";

val k60i = auto1 "|- [* (A > - -B) = (- -A > - -B) *]";

val k61a = auto1 "|- [* (A | B) > (-A > B) *]";

val k61b = auto2 "|- [* - (A | B) = - (-A > B) *]";

val k62a = auto1 "|- [* (-A | -B) > - (A & B) *]";

