(*  Title: 	ZF/CardinalArith.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal Arithmetic
*)

CardinalArith = Cardinal + OrderArith + Arith + Finite + 
consts

  InfCard     :: "i=>o"
  "|*|"       :: "[i,i]=>i"       (infixl 70)
  "|+|"       :: "[i,i]=>i"       (infixl 65)
  csquare_rel :: "i=>i"
  jump_cardinal :: "i=>i"
  csucc       :: "i=>i"

rules

  InfCard_def  "InfCard(i) == Card(i) & nat le i"

  cadd_def     "i |+| j == | i+j |"

  cmult_def    "i |*| j == | i*j |"

  csquare_rel_def
  "csquare_rel(k) == rvimage(k*k, lam z:k*k. split(%x y. <x Un y, <x,y>>, z), \
\                            rmult(k,Memrel(k), k*k, 	\
\                                  rmult(k,Memrel(k), k,Memrel(k))))"

  (*This def is more complex than Kunen's but it more easily proved to
    be a cardinal*)
  jump_cardinal_def
      "jump_cardinal(K) ==   \
\         UN X:Pow(K). {z. r: Pow(K*K), well_ord(X,r) & z = ordertype(X,r)}"

  (*needed because jump_cardinal(K) might not be the successor of K*)
  csucc_def "csucc(K) == LEAST L. Card(L) & K<L"

end
