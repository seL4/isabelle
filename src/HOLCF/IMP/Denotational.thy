(*  Title:      HOL/IMP/Den2.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM

Denotational semantics of commands in HOLCF
*)

Denotational = HOLCF + Natural +

consts D :: "com => state lift -> state lift"

primrec D com
  "D(SKIP) = (LAM s. s)"
  "D(X := a) = flift1(%s. Def(s[a(s)/X]))"
  "D(c0 ; c1) = ((D c1) oo (D c0))"
  "D(IF b THEN c1 ELSE c2) =
	flift1(%s . if b s then (D c1)`(Def s) else (D c2)`(Def s))"
  "D(WHILE b DO c) =
	fix`(LAM w. flift1(%s. if b s then w`((D c)`(Def s)) else Def s))"

end
