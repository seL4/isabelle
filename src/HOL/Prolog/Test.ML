open Test;

val prog_Test = prog_HOHH@[append, reverse, mappred, mapfun, age, eq, bag_appl];
fun pgoal s = (case Goal s of _ => by (prolog_tac prog_Test));
val p = ptac prog_Test 1;

pgoal "append ?x ?y [a,b,c,d]";
back();
back();
back();
back();

pgoal "append [a,b] y ?L";
pgoal "!y. append [a,b] y (?L y)";

pgoal "reverse [] ?L";

pgoal "reverse [23] ?L";
pgoal "reverse [23,24,?x] ?L";
pgoal "reverse ?L [23,24,?x]";

pgoal "mappred age ?x [23,24]";
back();

pgoal "mappred (%x y. ? z. age z y) ?x [23,24]";

pgoal "mappred ?P [bob,sue] [24,23]";

pgoal "mapfun f [bob,bob,sue] [?x,?y,?z]";

pgoal "mapfun (%x. h x 25) [bob,sue] ?L";

pgoal "mapfun ?F [24,25] [h bob 24,h bob 25]";

pgoal "mapfun ?F [24] [h 24 24]";
back();
back();
back();


(*
goal thy "f a = ?g a a & ?g = x"; 
by (rtac conjI 1);
by (rtac refl 1);
back();
back();
*)

pgoal "True";

pgoal "age ?x 24 & age ?y 23";
back();

pgoal "age ?x 24 | age ?x 23";
back();
back();

pgoal "? x y. age x y";

pgoal "!x y. append [] x x";

pgoal "age sue 24 .. age bob 23 => age ?x ?y";
back();
back();
back();
back();

(*set trace_DEPTH_FIRST;*)
pgoal "age bob 25 :- age bob 24 => age bob 25";
(*reset trace_DEPTH_FIRST;*)

pgoal "(!x. age x 25 :- age x 23) => age ?x 25 & age ?y 25";
back();
back();
back();

pgoal "!x. ? y. eq x y";

pgoal "? P. P & eq P ?x";
(*
back();
back();
back();
back();
back();
back();
back();
back();
*)

pgoal "? P. eq P (True & True) & P";

pgoal "? P. eq P op | & P k True";

pgoal "? P. eq P (Q => True) & P";

(* P flexible: *)
pgoal "(!P k l. P k l :- eq P Q) => Q a b";
(*
loops:
pgoal "(!P k l. P k l :- eq P (%x y. x | y)) => a | b";
*)

(* implication and disjunction in atom: *)
goal thy "? Q. (!p q. R(q :- p) => R(Q p q)) & Q (t | s) (s | t)";
by (fast_tac HOL_cs 1);

(* disjunction in atom: *)
goal thy "(!P. g P :- (P => b | a)) => g(a | b)";
by (step_tac HOL_cs 1);
by (step_tac HOL_cs 1);
by (step_tac HOL_cs 1);
by (fast_tac HOL_cs 2);
by (fast_tac HOL_cs 1);
(*
hangs:
goal thy "(!P. g P :- (P => b | a)) => g(a | b)";
by (fast_tac HOL_cs 1);
*)

pgoal "!Emp Stk.(\
\                       empty    (Emp::'b) .. \
\         (!(X::nat) S. add    X (S::'b)         (Stk X S)) .. \
\         (!(X::nat) S. remove X ((Stk X S)::'b) S))\
\ => bag_appl 23 24 ?X ?Y";

pgoal "!Qu. ( \
\          (!L.            empty    (Qu L L)) .. \
\          (!(X::nat) L K. add    X (Qu L (X#K)) (Qu L K)) ..\
\          (!(X::nat) L K. remove X (Qu (X#L) K) (Qu L K)))\
\ => bag_appl 23 24 ?X ?Y";

pgoal "D & (!y. E) :- (!x. True & True) :- True => D";

pgoal "P x .. P y => P ?X";
back();
(*
back();
-> problem with DEPTH_SOLVE:
Exception- THM ("dest_state", 1, ["P x & P y --> P y"]) raised
Exception raised at run-time
*)