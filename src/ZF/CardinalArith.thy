(*  Title: 	ZF/CardinalArith.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal Arithmetic
*)

CardinalArith = Cardinal + OrderArith + Arith + 
consts
  InfCard     :: "i=>o"
  "|*|"       :: "[i,i]=>i"       (infixl 70)
  "|+|"       :: "[i,i]=>i"       (infixl 65)
  csquare_rel :: "i=>i"

rules

  InfCard_def  "InfCard(i) == Card(i) & nat le i"

  cadd_def     "i |+| j == | i+j |"

  cmult_def    "i |*| j == | i*j |"

  csquare_rel_def
  "csquare_rel(k) == rvimage(k*k, lam z:k*k. split(%x y. <x Un y, <x,y>>, z), \
\                            rmult(k,Memrel(k), k*k, 	\
\                                  rmult(k,Memrel(k), k,Memrel(k))))"

end
