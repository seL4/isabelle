(*  Title:      ZF/AC.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The Axiom of Choice

This definition comes from Halmos (1960), page 59.
*)

AC = func +

constdefs
  (*Needs to be visible for Zorn.thy*)
  increasing :: i=>i
    "increasing(A) == {f: Pow(A)->Pow(A). ALL x. x<=A --> x<=f`x}"

rules
  AC    "[| a: A;  !!x. x:A ==> (EX y. y:B(x)) |] ==> EX z. z : Pi(A,B)"
end
