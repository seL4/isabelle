(*  Title:      HOL/Lex/NA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Nondeterministic automata
*)

NA = AutoProj +

types ('a,'s)na = "'s * ('a => 's => 's set) * ('s => bool)"

consts delta :: "('a,'s)na => 'a list => 's => 's set"
primrec
"delta A []    p = {p}"
"delta A (a#w) p = Union(delta A w ` next A a p)"

constdefs
 accepts ::   ('a,'s)na => 'a list => bool
"accepts A w == ? q : delta A w (start A). fin A q"

constdefs
 step :: "('a,'s)na => 'a => ('s * 's)set"
"step A a == {(p,q) . q : next A a p}"

consts steps :: "('a,'s)na => 'a list => ('s * 's)set"
primrec
"steps A [] = Id"
"steps A (a#w) = steps A w  O  step A a"

end
