(*  Title:      Equiv.thy
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Equivalence relations in Higher-Order Set Theory 
*)

Equiv = Relation + Finite + 
constdefs
  equiv    :: "['a set, ('a*'a) set] => bool"
    "equiv A r == refl A r & sym(r) & trans(r)"

  quotient :: "['a set, ('a*'a) set] => 'a set set"  (infixl "'/'/" 90) 
    "A//r == UN x:A. {r``{x}}"      (*set of equiv classes*)

  congruent  :: "[('a*'a) set, 'a=>'b] => bool"
    "congruent r b  == ALL y z. (y,z):r --> b(y)=b(z)"

  congruent2 :: "[('a*'a) set, ['a,'a]=>'b] => bool"
    "congruent2 r b == ALL y1 z1 y2 z2.
                         (y1,z1):r --> (y2,z2):r --> b y1 y2 = b z1 z2"
end
