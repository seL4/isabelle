(*  Title: 	ZF/OrderArith.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Towards ordinal arithmetic 
*)

OrderArith = Order + Sum + 
consts
  radd, rmult      :: "[i,i,i,i]=>i"
  rvimage          :: "[i,i,i]=>i"

defs
  (*disjoint sum of two relations; underlies ordinal addition*)
  radd_def "radd(A,r,B,s) == \
\                {z: (A+B) * (A+B).  \
\                    (EX x y. z = <Inl(x), Inr(y)>)   | 	 \
\                    (EX x' x. z = <Inl(x'), Inl(x)> & <x',x>:r)   | 	 \
\                    (EX y' y. z = <Inr(y'), Inr(y)> & <y',y>:s)}"

  (*lexicographic product of two relations; underlies ordinal multiplication*)
  rmult_def "rmult(A,r,B,s) == \
\                {z: (A*B) * (A*B).  \
\                    EX x' y' x y. z = <<x',y'>, <x,y>> &	 \
\                       (<x',x>: r | (x'=x & <y',y>: s))}"

  (*inverse image of a relation*)
  rvimage_def "rvimage(A,f,r) == {z: A*A. EX x y. z = <x,y> & <f`x,f`y>: r}"

end
