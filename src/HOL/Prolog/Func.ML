open Func;

val prog_Func = prog_HOHH @ [eval];
fun pgoal s = (case Goal s of _ => by(prolog_tac prog_Func));
val p = ptac prog_Func 1;

pgoal "eval ((S (S Z)) + (S Z)) ?X";

pgoal "eval (app (fix (%fact. abs(%n. cond (n eq Z) (S Z) \
			\(n * (app fact (n - (S Z))))))) (S (S (S Z)))) ?X";


