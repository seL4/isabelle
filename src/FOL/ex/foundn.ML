(*  Title:      FOL/ex/foundn
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Intuitionistic FOL: Examples from The Foundation of a Generic Theorem Prover
*)

writeln"File FOL/ex/foundn.";

goal IFOL.thy "A&B  --> (C-->A&C)";
by (rtac impI 1);
by (rtac impI 1);
by (rtac conjI 1);
by (assume_tac 2);
by (rtac conjunct1 1);
by (assume_tac 1);
result();

(*A form of conj-elimination*)
val prems = 
goal IFOL.thy "A&B ==> ([| A;  B |] ==> C) ==> C";
by (resolve_tac prems 1);
by (rtac conjunct1 1);
by (resolve_tac prems 1);
by (rtac conjunct2 1);
by (resolve_tac prems 1);
result();


val prems = 
goal IFOL.thy "(!!A. ~ ~A ==> A) ==> B | ~B";
by (resolve_tac prems 1);
by (rtac notI 1);
by (res_inst_tac [ ("P", "~B") ]  notE  1);
by (rtac notI 2);
by (res_inst_tac [ ("P", "B | ~B") ]  notE  2);
by (assume_tac 2);
by (rtac disjI1 2);
by (assume_tac 2);
by (rtac notI 1);
by (res_inst_tac [ ("P", "B | ~B") ]  notE  1);
by (assume_tac 1);
by (rtac disjI2 1);
by (assume_tac 1);
result();


val prems = 
goal IFOL.thy "(!!A. ~ ~A ==> A) ==> B | ~B";
by (resolve_tac prems 1);
by (rtac notI 1);
by (rtac notE 1);
by (rtac notI 2);
by (etac notE 2);
by (etac disjI1 2);
by (rtac notI 1);
by (etac notE 1);
by (etac disjI2 1);
result();


val prems = 
goal IFOL.thy "[| A | ~A;  ~ ~A |] ==> A";
by (rtac disjE 1);
by (resolve_tac prems 1);
by (assume_tac 1);
by (rtac FalseE 1);
by (res_inst_tac [ ("P", "~A") ]  notE  1);
by (resolve_tac prems 1);
by (assume_tac 1);
result();


writeln"Examples with quantifiers";

val prems =
goal IFOL.thy "ALL z. G(z) ==> ALL z. G(z)|H(z)";
by (rtac allI 1);
by (rtac disjI1 1);
by (resolve_tac (prems RL [spec]) 1); 
  (*can use instead
    by (rtac spec 1);  by (resolve_tac prems 1); *)
result();


goal IFOL.thy "ALL x. EX y. x=y";
by (rtac allI 1);
by (rtac exI 1);
by (rtac refl 1);
result();


goal IFOL.thy "EX y. ALL x. x=y";
by (rtac exI 1);
by (rtac allI 1);
by (rtac refl 1) handle ERROR => writeln"Failed, as expected";  
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
by (rtac conjE 1);
by (resolve_tac prems 1);
by (rtac exE 1);
by (assume_tac 1);
by (rtac exI 1);
by (rtac conjI 1);
by (assume_tac 1);
by (assume_tac 1);
result();


(*A bigger demonstration of quantifiers -- not in the paper*)
goal IFOL.thy "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))";
by (rtac impI 1);
by (rtac allI 1);
by (rtac exE 1 THEN assume_tac 1);
by (rtac exI 1);
by (rtac allE 1 THEN assume_tac 1);
by (assume_tac 1);
result();  


writeln"Reached end of file.";
