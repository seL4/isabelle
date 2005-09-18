(*  Title:      FOLP/ex/quant.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: quantifier examples (intuitionistic and classical)
Needs declarations of the theory "thy" and the tactic "tac"
*)

Goal "?p : (ALL x y. P(x,y))  -->  (ALL y x. P(x,y))";
by tac;
result();


Goal "?p : (EX x y. P(x,y)) --> (EX y x. P(x,y))";
by tac;
result();


(*Converse is false*)
Goal "?p : (ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))";
by tac;
result();

Goal "?p : (ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))";
by tac;
result();


Goal "?p : (ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)";
by tac;
result();


writeln"Some harder ones";

Goal "?p : (EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))";
by tac;
result();
(*6 secs*)

(*Converse is false*)
Goal "?p : (EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))";
by tac;
result();


writeln"Basic test of quantifier reasoning";
(*TRUE*)
Goal "?p : (EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))";
by tac;
result();


Goal "?p : (ALL x. Q(x))  -->  (EX x. Q(x))";
by tac;
result();


writeln"The following should fail, as they are false!";

Goal "?p : (ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))";
by tac handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1;

Goal "?p : (EX x. Q(x))  -->  (ALL x. Q(x))";
by tac handle ERROR => writeln"Failed, as expected";
getgoal 1;

Goal "?p : P(?a) --> (ALL x. P(x))";
by tac handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1;

Goal
    "?p : (P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))";
by tac handle ERROR => writeln"Failed, as expected";
getgoal 1;


writeln"Back to things that are provable...";

Goal "?p : (ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))";
by tac;
result();


(*An example of why exI should be delayed as long as possible*)
Goal "?p : (P --> (EX x. Q(x))) & P --> (EX x. Q(x))";
by tac;
result();

Goal "?p : (ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)";
by tac;
(*Verify that no subgoals remain.*)
uresult();


Goal "?p : (ALL x. Q(x))  -->  (EX x. Q(x))";
by tac;
result();


writeln"Some slow ones";


(*Principia Mathematica *11.53  *)
Goal "?p : (ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))";
by tac;
result();
(*6 secs*)

(*Principia Mathematica *11.55  *)
Goal "?p : (EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))";
by tac;
result();
(*9 secs*)

(*Principia Mathematica *11.61  *)
Goal "?p : (EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))";
by tac;
result();
(*3 secs*)
