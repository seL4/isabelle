(*  Title: 	ZF/ex/equiv.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Equivalence relations in Zermelo-Fraenkel Set Theory 
*)

Equiv = Trancl +
consts
    refl,equiv 	::      "[i,i]=>o"
    sym         ::      "i=>o"
    "'/"        ::      "[i,i]=>i"  (infixl 90)  (*set of equiv classes*)
    congruent	::	"[i,i=>i]=>o"
    congruent2  ::      "[i,[i,i]=>i]=>o"

rules
    refl_def      "refl(A,r) == r <= (A*A) & (ALL x: A. <x,x> : r)"
    sym_def       "sym(r) == ALL x y. <x,y>: r --> <y,x>: r"
    equiv_def     "equiv(A,r) == refl(A,r) & sym(r) & trans(r)"
    quotient_def  "A/r == {r``{x} . x:A}"
    congruent_def "congruent(r,b) == ALL y z. <y,z>:r --> b(y)=b(z)"

    congruent2_def
       "congruent2(r,b) == ALL y1 z1 y2 z2. \
\           <y1,z1>:r --> <y2,z2>:r --> b(y1,y2) = b(z1,z2)"

end
