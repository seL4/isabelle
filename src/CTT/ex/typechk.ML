(*  Title:      CTT/ex/typechk
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
  
Easy examples: type checking and type deduction
*)

writeln"Single-step proofs: verifying that a type is well-formed";

goal CTT.thy "?A type";
by (resolve_tac form_rls 1);
result(); 
writeln"getting a second solution";
back();
by (resolve_tac form_rls 1);
by (resolve_tac form_rls 1);
result(); 

goal CTT.thy "PROD z:?A . N + ?B(z) type";
by (resolve_tac form_rls 1);
by (resolve_tac form_rls 1);
by (resolve_tac form_rls 1);
by (resolve_tac form_rls 1);
by (resolve_tac form_rls 1);
uresult(); 


writeln"Multi-step proofs: Type inference";

goal CTT.thy "PROD w:N. N + N type";
by form_tac;
result(); 

goal CTT.thy "<0, succ(0)> : ?A";
by (intr_tac[]);
result(); 

goal CTT.thy "PROD w:N . Eq(?A,w,w) type";
by (typechk_tac[]);
result(); 

goal CTT.thy "PROD x:N . PROD y:N . Eq(?A,x,y) type";
by (typechk_tac[]);
result(); 

writeln"typechecking an application of fst";
goal CTT.thy "(lam u. split(u, %v w. v)) ` <0, succ(0)> : ?A";
by (typechk_tac[]);
result(); 

writeln"typechecking the predecessor function";
goal CTT.thy "lam n. rec(n, 0, %x y. x) : ?A";
by (typechk_tac[]);
result(); 

writeln"typechecking the addition function";
goal CTT.thy "lam n. lam m. rec(n, m, %x y. succ(y)) : ?A";
by (typechk_tac[]);
result(); 

(*Proofs involving arbitrary types.
  For concreteness, every type variable left over is forced to be N*)
val N_tac = TRYALL (rtac NF);

goal CTT.thy "lam w. <w,w> : ?A";
by (typechk_tac[]);
by N_tac;
result(); 

goal CTT.thy "lam x. lam y. x : ?A";
by (typechk_tac[]);
by N_tac;
result(); 

writeln"typechecking fst (as a function object) ";
goal CTT.thy "lam i. split(i, %j k. j) : ?A";
by (typechk_tac[]);
by N_tac;
result(); 

writeln"Reached end of file.";
