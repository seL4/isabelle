(*  Title:      ZF/OrderType.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Order types and ordinal arithmetic.

The order type of a well-ordering is the least ordinal isomorphic to it.
*)

OrderType = OrderArith + OrdQuant + 
constdefs
  
  ordermap  :: [i,i]=>i
   "ordermap(A,r) == lam x:A. wfrec[A](r, x, %x f. f `` pred(A,x,r))"

  ordertype :: [i,i]=>i
   "ordertype(A,r) == ordermap(A,r)``A"

  (*alternative definition of ordinal numbers*)
  Ord_alt   :: i => o   
   "Ord_alt(X) == well_ord(X, Memrel(X)) & (ALL u:X. u=pred(X, u, Memrel(X)))"

  (*coercion to ordinal: if not, just 0*)
  ordify    :: i=>i
    "ordify(x) == if Ord(x) then x else 0"

  (*ordinal multiplication*)
  omult      :: [i,i]=>i           (infixl "**" 70)
   "i ** j == ordertype(j*i, rmult(j,Memrel(j),i,Memrel(i)))"

  (*ordinal addition*)
  raw_oadd   :: [i,i]=>i
    "raw_oadd(i,j) == ordertype(i+j, radd(i,Memrel(i),j,Memrel(j)))"

  oadd      :: [i,i]=>i           (infixl "++" 65)
    "i ++ j == raw_oadd(ordify(i),ordify(j))"

  (*ordinal subtraction*)
  odiff      :: [i,i]=>i           (infixl "--" 65)
    "i -- j == ordertype(i-j, Memrel(i))"

  
syntax (xsymbols)
  "op **"     :: [i,i] => i          (infixl "\\<times>\\<times>" 70)

syntax (HTML output)
  "op **"     :: [i,i] => i          (infixl "\\<times>\\<times>" 70)

end
