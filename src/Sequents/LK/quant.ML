(*  Title:      LK/ex/quant.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Classical sequent calculus: examples with quantifiers.
*)

goal (theory "LK") "|- (ALL x. P)  <->  P";
by (fast_tac LK_pack 1);
result();

goal (theory "LK") "|- (ALL x y. P(x,y))  <->  (ALL y x. P(x,y))";
by (fast_tac LK_pack 1);
result();

goal (theory "LK") "ALL u. P(u), ALL v. Q(v) |- ALL u v. P(u) & Q(v)";
by (fast_tac LK_pack 1);
result();

writeln"Permutation of existential quantifier.";
goal (theory "LK") "|- (EX x y. P(x,y)) <-> (EX y x. P(x,y))";
by (fast_tac LK_pack 1);
result();

goal (theory "LK") "|- (ALL x. P(x) & Q(x)) <-> (ALL x. P(x)) & (ALL x. Q(x))";
by (fast_tac LK_pack 1);
result();


(*Converse is invalid*)
goal (theory "LK") "|- (ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x)|Q(x))";
by (fast_tac LK_pack 1);
result();


writeln"Pushing ALL into an implication.";
goal (theory "LK") "|- (ALL x. P --> Q(x))  <->  (P --> (ALL x. Q(x)))";
by (fast_tac LK_pack 1);
result();


goal (theory "LK") "|- (ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)";
by (fast_tac LK_pack 1);
result();


goal (theory "LK") "|- (EX x. P)  <->  P";
by (fast_tac LK_pack 1);
result();


writeln"Distribution of EX over disjunction.";
goal (theory "LK") "|- (EX x. P(x) | Q(x)) <-> (EX x. P(x))  |  (EX x. Q(x))";
by (fast_tac LK_pack 1);
result();
(*5 secs*)

(*Converse is invalid*)
goal (theory "LK") "|- (EX x. P(x) & Q(x))  -->  (EX x. P(x))  &  (EX x. Q(x))";
by (fast_tac LK_pack 1);
result();


writeln"Harder examples: classical theorems.";

goal (theory "LK") "|- (EX x. P-->Q(x))  <->  (P --> (EX x. Q(x)))";
by (fast_tac LK_pack 1);
result();
(*3 secs*)


goal (theory "LK") "|- (EX x. P(x)-->Q)  <->  (ALL x. P(x)) --> Q";
by (fast_tac LK_pack 1);
result();
(*5 secs*)


goal (theory "LK") "|- (ALL x. P(x)) | Q  <->  (ALL x. P(x) | Q)";
by (fast_tac LK_pack 1);
result();


writeln"Basic test of quantifier reasoning";
goal (theory "LK")
   "|- (EX y. ALL x. Q(x,y)) --> (ALL x. EX y. Q(x,y))";
by (fast_tac LK_pack 1);
result();


goal (theory "LK") "|- (ALL x. Q(x))  -->  (EX x. Q(x))";
by (fast_tac LK_pack 1);
result();


writeln"The following are invalid!";

(*INVALID*)
goal (theory "LK") "|- (ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1;

(*INVALID*)
goal (theory "LK") "|- (EX x. Q(x))  -->  (ALL x. Q(x))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
getgoal 1;

goal (theory "LK") "|- P(?a) --> (ALL x. P(x))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1;

goal (theory "LK") "|- (P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
getgoal 1;


writeln"Back to things that are provable...";

goal (theory "LK") "|- (ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))";
by (fast_tac LK_pack 1);
result();

(*An example of why exR should be delayed as long as possible*)
goal (theory "LK") "|- (P--> (EX x. Q(x))) & P--> (EX x. Q(x))";
by (fast_tac LK_pack 1);
result();

writeln"Solving for a Var";
goal (theory "LK")
   "|- (ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)";
by (fast_tac LK_pack 1);
result();


writeln"Principia Mathematica *11.53";
goal (theory "LK")
    "|- (ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))";
by (fast_tac LK_pack 1);
result();


writeln"Principia Mathematica *11.55";
goal (theory "LK") "|- (EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))";
by (fast_tac LK_pack 1);
result();

writeln"Principia Mathematica *11.61";
goal (theory "LK")
   "|- (EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))";
by (fast_tac LK_pack 1);
result();

(*21 August 88: loaded in 45.7 secs*)
(*18 September 2005: loaded in 0.114 secs*)
