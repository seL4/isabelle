(*  Title:      CTT/ex/equal
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Equality reasoning by rewriting.
*)

val prems =
goal CTT.thy "p : Sum(A,B) ==> split(p,pair) = p : Sum(A,B)";
by (rtac EqE 1);
by (resolve_tac elim_rls 1  THEN  resolve_tac prems 1);
by (rew_tac prems);
qed "split_eq";

val prems =
goal CTT.thy
    "[| A type;  B type;  p : A+B |] ==> when(p,inl,inr) = p : A + B";
by (rtac EqE 1);
by (resolve_tac elim_rls 1  THEN  resolve_tac prems 1);
by (rew_tac prems);
qed "when_eq";


(*in the "rec" formulation of addition, 0+n=n *)
val prems =
goal CTT.thy "p:N ==> rec(p,0, %y z. succ(y)) = p : N";
by (rtac EqE 1);
by (resolve_tac elim_rls 1  THEN  resolve_tac prems 1);
by (rew_tac prems);
result();


(*the harder version, n+0=n: recursive, uses induction hypothesis*)
val prems =
goal CTT.thy "p:N ==> rec(p,0, %y z. succ(z)) = p : N";
by (rtac EqE 1);
by (resolve_tac elim_rls 1  THEN  resolve_tac prems 1);
by (hyp_rew_tac prems);
result();


(*Associativity of addition*)
val prems =
goal CTT.thy
   "[| a:N;  b:N;  c:N |] ==> rec(rec(a, b, %x y. succ(y)), c, %x y. succ(y)) = \
\                   rec(a, rec(b, c, %x y. succ(y)), %x y. succ(y)) : N";
by (NE_tac "a" 1);
by (hyp_rew_tac prems);
result();


(*Martin-Lof (1984) page 62: pairing is surjective*)
val prems =
goal CTT.thy
    "p : Sum(A,B) ==> <split(p,%x y. x), split(p,%x y. y)> = p : Sum(A,B)";
by (rtac EqE 1);
by (resolve_tac elim_rls 1  THEN  resolve_tac prems 1);
by (DEPTH_SOLVE_1 (rew_tac prems));   (*!!!!!!!*)
result();


val prems =
goal CTT.thy "[| a : A;  b : B |] ==> \
\    (lam u. split(u, %v w.<w,v>)) ` <a,b> = <b,a> : SUM x:B. A";
by (rew_tac prems);
result();


(*a contrived, complicated simplication, requires sum-elimination also*)
val prems =
goal CTT.thy
   "(lam f. lam x. f`(f`x)) ` (lam u. split(u, %v w.<w,v>)) =  \
\     lam x. x  :  PROD x:(SUM y:N. N). (SUM y:N. N)";
by (resolve_tac reduction_rls 1);
by (resolve_tac intrL_rls 3);
by (rtac EqE 4);
by (rtac SumE 4  THEN  assume_tac 4);
(*order of unifiers is essential here*)
by (rew_tac prems);
result();

writeln"Reached end of file.";
(*28 August 1988: loaded this file in 34 seconds*)
(*2 September 1988: loaded this file in 48 seconds*)
