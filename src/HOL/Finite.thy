(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator
*)

Finite = Lfp +
consts Fin :: 'a set => 'a set set

inductive "Fin(A)"
  intrs
    emptyI  "{} : Fin(A)"
    insertI "[| a: A;  b: Fin(A) |] ==> insert a b : Fin(A)"

end
