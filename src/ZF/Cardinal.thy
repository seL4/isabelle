(*  Title: 	ZF/Cardinal.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinals in Zermelo-Fraenkel Set Theory 
*)

Cardinal = OrderType + Fixedpt + Nat + Sum + 
consts
  Least            :: (i=>o) => i    (binder "LEAST " 10)
  eqpoll, lepoll,
          lesspoll :: [i,i] => o     (infixl 50)
  cardinal         :: i=>i           ("|_|")
  Finite, Card     :: i=>o

defs

  (*least ordinal operator*)
  Least_def     "Least(P) == THE i. Ord(i) & P(i) & (ALL j. j<i --> ~P(j))"

  eqpoll_def    "A eqpoll B == EX f. f: bij(A,B)"

  lepoll_def    "A lepoll B == EX f. f: inj(A,B)"

  lesspoll_def  "A lesspoll B == A lepoll B & ~(A eqpoll B)"

  Finite_def    "Finite(A) == EX n:nat. A eqpoll n"

  cardinal_def  "|A| == LEAST i. i eqpoll A"

  Card_def      "Card(i) == (i = |i|)"

end
