(*  Title:      HOL/Lex/NAe.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Nondeterministic automata with epsilon transitions
*)

NAe = List + Option + NA +

types ('a,'s)nae = ('a option,'s)na

constdefs
 step :: "('a,'s)nae => 'a option => ('s * 's)set"
"step A a == {(p,q) . q : next A a p}"

syntax eps :: "('a,'s)nae => ('s * 's)set"
translations "eps A" == "step A None"

consts steps :: "('a,'s)nae => 'a list =>   ('s * 's)set"
primrec steps list
"steps A [] = (eps A)^*"
"steps A (a#w) = steps A w  O  step A (Some a)  O  (eps A)^*"

consts delta :: "('a,'s)nae => 'a list => 's => 's set"
primrec delta list
"delta A [] s = (eps A)^* ^^ {s}"
"delta A (a#w) s = lift(delta A w) (lift(next A (Some a)) ((eps A)^* ^^ {s}))"

constdefs
 accepts :: ('a,'s)nae => 'a list => bool
"accepts A w == ? q. (start A,q) : steps A w & fin A q"

end
