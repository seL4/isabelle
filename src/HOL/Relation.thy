(*  Title: 	Relation.thy
    ID:         $Id$
    Author: 	Riccardo Mattolini, Dip. Sistemi e Informatica
        and	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge
*)

Relation = Prod +
consts
    id	        :: "('a * 'a)set"               (*the identity relation*)
    O	        :: "[('b * 'c)set, ('a * 'b)set] => ('a * 'c)set" (infixr 60)
    trans       :: "('a * 'a)set => bool" 	(*transitivity predicate*)
    converse    :: "('a*'a) set => ('a*'a) set"
    "^^"        :: "[('a*'a) set,'a set] => 'a set" (infixl 90)
    Domain      :: "('a*'a) set => 'a set"
    Range       :: "('a*'a) set => 'a set"
defs
    id_def	"id == {p. ? x. p = (x,x)}"
    comp_def	(*composition of relations*)
		"r O s == {xz. ? x y z. xz = (x,z) & (x,y):s & (y,z):r}"
    trans_def	  "trans(r) == (!x y z. (x,y):r --> (y,z):r --> (x,z):r)"
    converse_def  "converse(r) == {z. (? w:r. ? x y. w=(x,y) & z=(y,x))}"
    Domain_def    "Domain(r) == {z. ! x. (z=x --> (? y. (x,y):r))}"
    Range_def     "Range(r) == Domain(converse(r))"
    Image_def     "r ^^ s == {y. y:Range(r) &  (? x:s. (x,y):r)}"
end
