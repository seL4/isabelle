(*  Title:      ZF/EquivClass.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Equivalence relations in Zermelo-Fraenkel Set Theory 
*)

EquivClass = Rel + Perm + 

constdefs

  quotient    :: [i,i]=>i    (infixl "'/'/" 90)  (*set of equiv classes*)
      "A//r == {r``{x} . x:A}"

  congruent   :: [i,i=>i]=>o
      "congruent(r,b) == ALL y z. <y,z>:r --> b(y)=b(z)"

  congruent2  :: [i,[i,i]=>i]=>o
      "congruent2(r,b) == ALL y1 z1 y2 z2. 
           <y1,z1>:r --> <y2,z2>:r --> b(y1,y2) = b(z1,z2)"

end
