(*  Title: 	Relation.thy
    ID:         $Id$
    Author: 	Riccardo Mattolini, Dip. Sistemi e Informatica
        and	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge

Functions represented as relations in Higher-Order Set Theory 
*)

Relation = Trancl +
consts
    converse    ::      "('a*'a) set => ('a*'a) set"
    "^^"        ::      "[('a*'a) set,'a set] => 'a set" (infixl 90)
    Domain      ::      "('a*'a) set => 'a set"
    Range       ::      "('a*'a) set => 'a set"

defs
    converse_def  "converse(r) == {z. (? w:r. ? x y. w=(x,y) & z=(y,x))}"
    Domain_def    "Domain(r) == {z. ! x. (z=x --> (? y. (x,y):r))}"
    Range_def     "Range(r) == Domain(converse(r))"
    Image_def     "r ^^ s == {y. y:Range(r) &  (? x:s. (x,y):r)}"

end
