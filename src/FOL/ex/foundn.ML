(*  Title: 	FOL/ex/foundn
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Intuitionistic FOL: Examples from The Foundation of a Generic Theorem Prover
*)

writeln"File FOL/ex/foundn.";

goal IFOL.thy "A&B  --> (C-->A&C)";
by (resolve_tac [impI] 1);
by (resolve_tac [impI] 1);
by (resolve_tac [conjI] 1);
by (assume_tac 2);
by (resolve_tac [conjunct1] 1);
by (assume_tac 1);
result();

(*A form of conj-elimination*)
val prems = 
goal IFOL.thy "A&B ==> ([| A;  B |] ==> C) ==> C";
by (resolve_tac prems 1);
by (resolve_tac [conjunct1] 1);
by (resolve_tac prems 1);
by (resolve_tac [conjunct2] 1);
by (resolve_tac prems 1);
result();


val prems = 
goal IFOL.thy "(!!A. ~ ~A ==> A) ==> B | ~B";
by (resolve_tac prems 1);
by (resolve_tac [notI] 1);
by (res_inst_tac [ ("P", "~B") ]  notE  1);
by (resolve_tac [notI] 2);
by (res_inst_tac [ ("P", "B | ~B") ]  notE  2);
by (assume_tac 2);
by (resolve_tac [disjI1] 2);
by (assume_tac 2);
by (resolve_tac [notI] 1);
by (res_inst_tac [ ("P", "B | ~B") ]  notE  1);
by (assume_tac 1);
by (resolve_tac [disjI2] 1);
by (assume_tac 1);
result();


val prems = 
goal IFOL.thy "(!!A. ~ ~A ==> A) ==> B | ~B";
by (resolve_tac prems 1);
by (resolve_tac [notI] 1);
by (resolve_tac [notE] 1);
by (resolve_tac [notI] 2);
by (eresolve_tac [notE] 2);
by (eresolve_tac [disjI1] 2);
by (resolve_tac [notI] 1);
by (eresolve_tac [notE] 1);
by (eresolve_tac [disjI2] 1);
result();


val prems = 
goal IFOL.thy "[| A | ~A;  ~ ~A |] ==> A";
by (resolve_tac [disjE] 1);
by (resolve_tac prems 1);
by (assume_tac 1);
by (resolve_tac [FalseE] 1);
by (res_inst_tac [ ("P", "~A") ]  notE  1);
by (resolve_tac prems 1);
by (assume_tac 1);
result();


writeln"Examples with quantifiers";

val prems =
goal IFOL.thy "ALL z. G(z) ==> ALL z. G(z)|H(z)";
by (resolve_tac [allI] 1);
by (resolve_tac [disjI1] 1);
by (resolve_tac (prems RL [spec]) 1); 
  (*can use instead
    by (resolve_tac [spec] 1);  by (resolve_tac prems 1); *)
result();


goal IFOL.thy "ALL x. EX y. x=y";
by (resolve_tac [allI] 1);
by (resolve_tac [exI] 1);
by (resolve_tac [refl] 1);
result();


goal IFOL.thy "EX y. ALL x. x=y";
by (resolve_tac [exI] 1);
by (resolve_tac [allI] 1);
by (resolve_tac [refl] 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 


(*Parallel lifting example. *)
goal IFOL.thy "EX u.ALL x.EX v.ALL y.EX w. P(u,x,v,y,w)";
by (resolve_tac [exI, allI] 1);
by (resolve_tac [exI, allI] 1);
by (resolve_tac [exI, allI] 1);
by (resolve_tac [exI, allI] 1);
by (resolve_tac [exI, allI] 1);


val prems =
goal IFOL.thy "(EX z.F(z)) & B ==> (EX z. F(z) & B)";
by (resolve_tac [conjE] 1);
by (resolve_tac prems 1);
by (resolve_tac [exE] 1);
by (assume_tac 1);
by (resolve_tac [exI] 1);
by (resolve_tac [conjI] 1);
by (assume_tac 1);
by (assume_tac 1);
result();


(*A bigger demonstration of quantifiers -- not in the paper*)
goal IFOL.thy "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))";
by (resolve_tac [impI] 1);
by (resolve_tac [allI] 1);
by (resolve_tac [exE] 1 THEN assume_tac 1);
by (resolve_tac [exI] 1);
by (resolve_tac [allE] 1 THEN assume_tac 1);
by (assume_tac 1);
result();  


writeln"Reached end of file.";
