(*  Title: 	ZF/epsilon.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Epsilon induction and recursion
*)

Epsilon = Nat +
consts
    eclose,rank ::      "i=>i"
    transrec    ::      "[i, [i,i]=>i] =>i"

rules
  eclose_def	"eclose(A) == UN n:nat. nat_rec(n, A, %m r. Union(r))"
  transrec_def	"transrec(a,H) == wfrec(Memrel(eclose({a})), a, H)"
  rank_def    	"rank(a) == transrec(a, %x f. UN y:x. succ(f`y))"
end
