(*  Title:      HOLCF/IMP/Denotational.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM

Denotational semantics of commands in HOLCF
*)

Denotational = HOLCF + Natural +

constdefs
   dlift :: "(('a::term) discr -> 'b::pcpo) => ('a lift -> 'b)"
  "dlift f == (LAM x. case x of Undef => UU | Def(y) => f$(Discr y))"

consts D :: "com => state discr -> state lift"

primrec
  "D(SKIP) = (LAM s. Def(undiscr s))"
  "D(X :== a) = (LAM s. Def((undiscr s)[X ::= a(undiscr s)]))"
  "D(c0 ; c1) = (dlift(D c1) oo (D c0))"
  "D(IF b THEN c1 ELSE c2) =
	(LAM s. if b(undiscr s) then (D c1)$s else (D c2)$s)"
  "D(WHILE b DO c) =
	fix$(LAM w s. if b(undiscr s) then (dlift w)$((D c)$s)
                      else Def(undiscr s))"

end
