(*  Title: 	FOL/ex/intro
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manual "Introduction to Isabelle"

Derives some inference rules, illustrating the use of definitions

To generate similar output to manual, execute these commands:
    Pretty.setmargin 72; print_depth 0;
*)


(**** Some simple backward proofs ****)

goal FOL.thy "P|P --> P";
by (resolve_tac [impI] 1);
by (resolve_tac [disjE] 1);
by (assume_tac 3);
by (assume_tac 2);
by (assume_tac 1);
qed "mythm";

goal FOL.thy "(P & Q) | R  --> (P | R)";
by (resolve_tac [impI] 1);
by (eresolve_tac [disjE] 1);
by (dresolve_tac [conjunct1] 1);
by (resolve_tac [disjI1] 1);
by (resolve_tac [disjI2] 2);
by (REPEAT (assume_tac 1));
result();

(*Correct version, delaying use of "spec" until last*)
goal FOL.thy "(ALL x y.P(x,y))  -->  (ALL z w.P(w,z))";
by (resolve_tac [impI] 1);
by (resolve_tac [allI] 1);
by (resolve_tac [allI] 1);
by (dresolve_tac [spec] 1);
by (dresolve_tac [spec] 1);
by (assume_tac 1);
result();


(**** Demonstration of fast_tac ****)

goal FOL.thy "(EX y. ALL x. J(y,x) <-> ~J(x,x))  \
\       -->  ~ (ALL x. EX y. ALL z. J(z,y) <-> ~ J(z,x))";
by (fast_tac FOL_cs 1);
result();

goal FOL.thy "ALL x. P(x,f(x)) <-> \
\       (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (fast_tac FOL_cs 1);
result();


(**** Derivation of conjunction elimination rule ****)

val [major,minor] = goal FOL.thy "[| P&Q;  [| P; Q |] ==> R |] ==> R";
by (resolve_tac [minor] 1);
by (resolve_tac [major RS conjunct1] 1);
by (resolve_tac [major RS conjunct2] 1);
prth (topthm());
result();


(**** Derived rules involving definitions ****)

(** Derivation of negation introduction **)

val prems = goal FOL.thy "(P ==> False) ==> ~P";
by (rewrite_goals_tac [not_def]);
by (resolve_tac [impI] 1);
by (resolve_tac prems 1);
by (assume_tac 1);
result();

val [major,minor] = goal FOL.thy "[| ~P;  P |] ==> R";
by (resolve_tac [FalseE] 1);
by (resolve_tac [mp] 1);
by (resolve_tac [rewrite_rule [not_def] major] 1);
by (resolve_tac [minor] 1);
result();

(*Alternative proof of above result*)
val [major,minor] = goalw FOL.thy [not_def]
    "[| ~P;  P |] ==> R";
by (resolve_tac [minor RS (major RS mp RS FalseE)] 1);
result();

writeln"Reached end of file.";
