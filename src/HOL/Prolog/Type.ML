(*  Title:    HOL/Prolog/Type.ML
    ID:       $Id$
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

val prog_Type = prog_Func @ [good_typeof,common_typeof];
fun pgoal s = (case Goal s of _ => by (prolog_tac prog_Type));
val p = ptac prog_Type 1;

pgoal "typeof (abs(%n. abs(%m. abs(%p. p and (n eq m))))) ?T";

pgoal "typeof (fix (%x. x)) ?T";

pgoal "typeof (fix (%fact. abs(%n. (app fact (n - 0))))) ?T";

pgoal "typeof (fix (%fact. abs(%n. cond (n eq 0) (S 0) \
				\(n * (app fact (n - (S 0))))))) ?T";

pgoal "typeof (abs(%v. 0)) ?T"; (*correct only solution (?A1 -> nat) *)
Goal "typeof (abs(%v. 0)) ?T";
by (prolog_tac [bad1_typeof,common_typeof]); (* 1st result ok*)
back(); (* 2nd result (?A1 -> ?A1) wrong *)

(*pgoal "typeof (abs(%v. abs(%v. app v v))) ?T"; correctly fails*)
Goal "typeof (abs(%v. abs(%v. app v v))) ?T";
by (prolog_tac [bad2_typeof,common_typeof]); 
	(* wrong result ((?A3 -> ?B3) -> ?A3 -> ?B3)*)
