(*  Title:      HOL/Lex/NA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Nondeterministic automata
*)

NA = List + AutoProj +

types ('a,'s)na = "'s * ('a => 's => 's set) * ('s => bool)"

syntax lift :: ('a => 'b set) => 'a set => 'b set
translations "lift f A" == "Union(f `` A)"

consts delta :: "('a,'s)na => 'a list => 's => 's set"
primrec delta list
"delta A []    p = {p}"
"delta A (a#w) p = lift (delta A w) (next A a p)"

constdefs
 accepts ::   ('a,'s)na => 'a list => bool
"accepts A w == ? q : delta A w (start A). fin A q"

end
