(*  Title:      Relation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

Relation = Prod +
consts
    id          :: "('a * 'a)set"               (*the identity relation*)
    O           :: "[('b * 'c)set, ('a * 'b)set] => ('a * 'c)set" (infixr 60)
    trans       :: "('a * 'a)set => bool"       (*transitivity predicate*)
    converse    :: "('a*'b) set => ('b*'a) set"
    "^^"        :: "[('a*'b) set,'a set] => 'b set" (infixl 90)
    Domain      :: "('a*'b) set => 'a set"
    Range       :: "('a*'b) set => 'b set"
defs
    id_def        "id == {p. ? x. p = (x,x)}"
    comp_def      "r O s == {(x,z). ? y. (x,y):s & (y,z):r}"
    trans_def     "trans(r) == (!x y z. (x,y):r --> (y,z):r --> (x,z):r)"
    converse_def  "converse(r) == {(y,x). (x,y):r}"
    Domain_def    "Domain(r) == {x. ? y. (x,y):r}"
    Range_def     "Range(r) == Domain(converse(r))"
    Image_def     "r ^^ s == {y. ? x:s. (x,y):r}"
end
