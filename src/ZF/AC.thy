(*  Title: 	ZF/AC.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The Axiom of Choice

This definition comes from Halmos (1960), page 59.
*)

AC = ZF + "func" +
rules
  AC	"[| a: A;  !!x. x:A ==> (EX y. y:B(x)) |] ==> EX z. z : Pi(A,B)"
end
