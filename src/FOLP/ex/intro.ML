(*  Title:      FOLP/ex/intro.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manual "Introduction to Isabelle"

Derives some inference rules, illustrating the use of definitions

To generate similar output to manual, execute these commands:
    Pretty.setmargin 72; print_depth 0;
*)


(**** Some simple backward proofs ****)

goal FOLP.thy "?p:P|P --> P";
by (rtac impI 1);
by (rtac disjE 1);
by (assume_tac 3);
by (assume_tac 2);
by (assume_tac 1);
val mythm = result();

goal FOLP.thy "?p:(P & Q) | R  --> (P | R)";
by (rtac impI 1);
by (etac disjE 1);
by (dtac conjunct1 1);
by (rtac disjI1 1);
by (rtac disjI2 2);
by (REPEAT (assume_tac 1));
result();

(*Correct version, delaying use of "spec" until last*)
goal FOLP.thy "?p:(ALL x y.P(x,y))  -->  (ALL z w.P(w,z))";
by (rtac impI 1);
by (rtac allI 1);
by (rtac allI 1);
by (dtac spec 1);
by (dtac spec 1);
by (assume_tac 1);
result();


(**** Demonstration of fast_tac ****)

goal FOLP.thy "?p:(EX y. ALL x. J(y,x) <-> ~J(x,x))  \
\       -->  ~ (ALL x. EX y. ALL z. J(z,y) <-> ~ J(z,x))";
by (fast_tac FOLP_cs 1);
result();

goal FOLP.thy "?p:ALL x. P(x,f(x)) <-> \
\       (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (fast_tac FOLP_cs 1);
result();


(**** Derivation of conjunction elimination rule ****)

val [major,minor] = goal FOLP.thy "[| p:P&Q; !!x y.[| x:P; y:Q |] ==>f(x,y):R |] ==> ?p:R";
by (rtac minor 1);
by (resolve_tac [major RS conjunct1] 1);
by (resolve_tac [major RS conjunct2] 1);
prth (topthm());
result();


(**** Derived rules involving definitions ****)

(** Derivation of negation introduction **)

val prems = goal FOLP.thy "(!!x.x:P ==> f(x):False) ==> ?p:~P";
by (rewtac not_def);
by (rtac impI 1);
by (resolve_tac prems 1);
by (assume_tac 1);
result();

val [major,minor] = goal FOLP.thy "[| p:~P;  q:P |] ==> ?p:R";
by (rtac FalseE 1);
by (rtac mp 1);
by (resolve_tac [rewrite_rule [not_def] major] 1);
by (rtac minor 1);
result();

(*Alternative proof of above result*)
val [major,minor] = goalw FOLP.thy [not_def]
    "[| p:~P;  q:P |] ==> ?p:R";
by (resolve_tac [minor RS (major RS mp RS FalseE)] 1);
result();

writeln"Reached end of file.";
