(*  Title: 	ZF/OrderType.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Order types and ordinal arithmetic.

The order type of a well-ordering is the least ordinal isomorphic to it.
*)

OrderType = OrderArith + Ordinal + 
consts
  ordermap  :: [i,i]=>i
  ordertype :: [i,i]=>i

  Ord_alt   :: i => o   

  "**"      :: [i,i]=>i           (infixl 70)
  "++"      :: [i,i]=>i           (infixl 65)
  "--"      :: [i,i]=>i           (infixl 65)
 

defs
  ordermap_def
      "ordermap(A,r) == lam x:A. wfrec[A](r, x, %x f. f `` pred(A,x,r))"

  ordertype_def "ordertype(A,r) == ordermap(A,r)``A"

  Ord_alt_def    (*alternative definition of ordinal numbers*)
  "Ord_alt(X) == well_ord(X, Memrel(X)) & (ALL u:X. u=pred(X, u, Memrel(X)))"
  
  (*ordinal multiplication*)
  omult_def     "i ** j == ordertype(j*i, rmult(j,Memrel(j),i,Memrel(i)))"

  (*ordinal addition*)
  oadd_def      "i ++ j == ordertype(i+j, radd(i,Memrel(i),j,Memrel(j)))"

  (*ordinal subtraction*)
  odiff_def     "i -- j == ordertype(i-j, Memrel(i))"

end
