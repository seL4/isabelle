(*  Title:      ZF/CardinalArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal Arithmetic
*)

CardinalArith = Cardinal + OrderArith + ArithSimp + Finite + 
consts

  InfCard       :: i=>o
  "|*|"         :: [i,i]=>i       (infixl 70)
  "|+|"         :: [i,i]=>i       (infixl 65)
  csquare_rel   :: i=>i
  jump_cardinal :: i=>i
  csucc         :: i=>i

defs

  InfCard_def  "InfCard(i) == Card(i) & nat le i"

  cadd_def     "i |+| j == |i+j|"

  cmult_def    "i |*| j == |i*j|"

  csquare_rel_def
  "csquare_rel(K) ==   
        rvimage(K*K,   
                lam <x,y>:K*K. <x Un y, x, y>, 
                rmult(K,Memrel(K), K*K, rmult(K,Memrel(K), K,Memrel(K))))"

  (*This def is more complex than Kunen's but it more easily proved to
    be a cardinal*)
  jump_cardinal_def
      "jump_cardinal(K) ==   
         UN X:Pow(K). {z. r: Pow(K*K), well_ord(X,r) & z = ordertype(X,r)}"

  (*needed because jump_cardinal(K) might not be the successor of K*)
  csucc_def "csucc(K) == LEAST L. Card(L) & K<L"

syntax (symbols)
  "op |+|"     :: [i,i] => i          (infixl "\\<oplus>" 65)
  "op |*|"     :: [i,i] => i          (infixl "\\<otimes>" 70)

end
