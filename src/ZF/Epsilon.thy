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

    recursor  :: [i, [i,i]=>i, i]=>i
     "recursor(a,b,k) ==  transrec(k, %n f. nat_case(a, %m. b(m, f`m), n))"

    rec  :: [i, i, [i,i]=>i]=>i
     "rec(k,a,b) ==  recursor(a,b,k)"

end
