(*  Title: 	LK/ex/quant
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Classical sequent calculus: examples with quantifiers.
*)


writeln"LK/ex/quant: Examples with quantifiers";

goal LK.thy "|- (ALL x. P)  <->  P";
by (fast_tac LK_pack 1);
result(); 

goal LK.thy "|- (ALL x y.P(x,y))  <->  (ALL y x.P(x,y))";
by (fast_tac LK_pack 1);
result(); 

goal LK.thy "ALL u.P(u), ALL v.Q(v) |- ALL u v. P(u) & Q(v)";
by (fast_tac LK_pack 1);
result(); 

writeln"Permutation of existential quantifier.";
goal LK.thy "|- (EX x y.P(x,y)) <-> (EX y x.P(x,y))";
by (fast_tac LK_pack 1);
result(); 

goal LK.thy "|- (ALL x. P(x) & Q(x)) <-> (ALL x.P(x)) & (ALL x.Q(x))";
by (fast_tac LK_pack 1);
result(); 


(*Converse is invalid*)
goal LK.thy "|- (ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x)|Q(x))";
by (fast_tac LK_pack 1);
result(); 


writeln"Pushing ALL into an implication.";
goal LK.thy "|- (ALL x. P --> Q(x))  <->  (P --> (ALL x. Q(x)))";
by (fast_tac LK_pack 1);
result(); 


goal LK.thy "|- (ALL x.P(x)-->Q)  <->  ((EX x.P(x)) --> Q)";
by (fast_tac LK_pack 1);
result(); 


goal LK.thy "|- (EX x. P)  <->  P";
by (fast_tac LK_pack 1);
result(); 


writeln"Distribution of EX over disjunction.";
goal LK.thy "|- (EX x. P(x) | Q(x)) <-> (EX x. P(x))  |  (EX x. Q(x))";
by (fast_tac LK_pack 1);
result(); 
(*5 secs*)

(*Converse is invalid*)
goal LK.thy "|- (EX x. P(x) & Q(x))  -->  (EX x. P(x))  &  (EX x. Q(x))";
by (fast_tac LK_pack 1);
result(); 


writeln"Harder examples: classical theorems.";

goal LK.thy "|- (EX x. P-->Q(x))  <->  (P --> (EX x.Q(x)))";
by (fast_tac LK_pack 1);
result(); 
(*3 secs*)


goal LK.thy "|- (EX x.P(x)-->Q)  <->  (ALL x.P(x)) --> Q";
by (fast_tac LK_pack 1);
result(); 
(*5 secs*)


goal LK.thy "|- (ALL x.P(x)) | Q  <->  (ALL x. P(x) | Q)";
by (fast_tac LK_pack 1);
result(); 


writeln"Basic test of quantifier reasoning";
goal LK.thy
   "|- (EX y. ALL x. Q(x,y)) --> (ALL x. EX y. Q(x,y))";
by (fast_tac LK_pack 1);
result();  


goal LK.thy "|- (ALL x. Q(x))  -->  (EX x. Q(x))";
by (fast_tac LK_pack 1);
result();  


writeln"The following are invalid!";

(*INVALID*)
goal LK.thy "|- (ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected"; 
(*Check that subgoals remain: proof failed.*)
getgoal 1; 

(*INVALID*)
goal LK.thy "|- (EX x. Q(x))  -->  (ALL x. Q(x))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
getgoal 1; 

goal LK.thy "|- P(?a) --> (ALL x.P(x))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1;  

goal LK.thy "|- (P(?a) --> (ALL x.Q(x))) --> (ALL x. P(x) --> Q(x))";
by (fast_tac LK_pack 1) handle ERROR => writeln"Failed, as expected";
getgoal 1;  


writeln"Back to things that are provable...";

goal LK.thy "|- (ALL x. P(x)-->Q(x)) & (EX x.P(x)) --> (EX x.Q(x))";
by (fast_tac LK_pack 1); 
result();  

(*An example of why exR should be delayed as long as possible*)
goal LK.thy "|- (P--> (EX x.Q(x))) & P--> (EX x.Q(x))";
by (fast_tac LK_pack 1);
result();  

writeln"Solving for a Var";
goal LK.thy 
   "|- (ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)";
by (fast_tac LK_pack 1);
result();


writeln"Principia Mathematica *11.53";
goal LK.thy 
    "|- (ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))";
by (fast_tac LK_pack 1);
result();


writeln"Principia Mathematica *11.55";
goal LK.thy "|- (EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y.Q(x,y)))";
by (fast_tac LK_pack 1);
result();

writeln"Principia Mathematica *11.61";
goal LK.thy
   "|- (EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))";
by (fast_tac LK_pack 1);
result();

writeln"Reached end of file.";

(*21 August 88: loaded in 45.7 secs*)
