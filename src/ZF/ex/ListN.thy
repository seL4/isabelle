(*  Title: 	ZF/ex/ListN
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of lists of n elements

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

ListN = List +
consts	listn ::"i=>i"
inductive
  domains   "listn(A)" <= "nat*list(A)"
  intrs
    NilI  "<0,Nil> : listn(A)"
    ConsI "[| a: A;  <n,l> : listn(A) |] ==> <succ(n), Cons(a,l)> : listn(A)"
  type_intrs "nat_typechecks @ list.intrs"
end
