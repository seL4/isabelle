(*  Title: 	Equiv.thy
    ID:         $Id$
    Authors: 	Riccardo Mattolini, Dip. Sistemi e Informatica
        	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge

Equivalence relations in Higher-Order Set Theory 
*)

Equiv = Relation +
consts
    refl,equiv 	::      "['a set,('a*'a) set]=>bool"
    sym         ::      "('a*'a) set=>bool"
    "'/"        ::      "['a set,('a*'a) set]=>'a set set"  (infixl 90) 
                        (*set of equiv classes*)
    congruent	::	"[('a*'a) set,'a=>'b]=>bool"
    congruent2  ::      "[('a*'a) set,['a,'a]=>'b]=>bool"

defs
    refl_def      "refl A r == r <= Sigma A (%x.A) & (ALL x: A. <x,x> : r)"
    sym_def       "sym(r)    == ALL x y. <x,y>: r --> <y,x>: r"
    equiv_def     "equiv A r == refl A r & sym(r) & trans(r)"
    quotient_def  "A/r == UN x:A. {r^^{x}}"  
    congruent_def   "congruent r b  == ALL y z. <y,z>:r --> b(y)=b(z)"
    congruent2_def  "congruent2 r b == ALL y1 z1 y2 z2. \
\           <y1,z1>:r --> <y2,z2>:r --> b y1 y2 = b z1 z2"
end
