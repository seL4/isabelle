(*  Title:      ZF/epsilon.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Epsilon induction and recursion
*)

Epsilon = Nat + mono +
constdefs
  eclose    :: i=>i
    "eclose(A) == UN n:nat. nat_rec(n, A, %m r. Union(r))"

  transrec  :: [i, [i,i]=>i] =>i
    "transrec(a,H) == wfrec(Memrel(eclose({a})), a, H)"
 
  rank      :: i=>i
    "rank(a) == transrec(a, %x f. UN y:x. succ(f`y))"

  transrec2 :: [i, i, [i,i]=>i] =>i
    "transrec2(k, a, b) ==                     
       transrec(k, 
                %i r. if(i=0, a, 
                        if(EX j. i=succ(j),        
                           b(THE j. i=succ(j), r`(THE j. i=succ(j))),   
                           UN j<i. r`j)))"

end
