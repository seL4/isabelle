(*  Title: 	ZF/Finite.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator
*)

Finite = Arith + 
consts Fin :: "i=>i"
inductive
  domains   "Fin(A)" <= "Pow(A)"
  intrs
    emptyI  "0 : Fin(A)"
    consI   "[| a: A;  b: Fin(A) |] ==> cons(a,b) : Fin(A)"
  type_intrs "[empty_subsetI, cons_subsetI, PowI]"
  type_elims "[make_elim PowD]"
end
