(*  Title:      HOL/Integ/Lagrange.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen


The following lemma essentially shows that all composite natural numbers are
sums of fours squares, provided all prime numbers are. However, this is an
abstract thm about commutative rings and has a priori nothing to do with nat.
*)

goalw Lagrange.thy [Lagrange.sq_def] "!!x1::'a::cring. \
\  (sq x1 + sq x2 + sq x3 + sq x4) * (sq y1 + sq y2 + sq y3 + sq y4) = \
\  sq(x1*y1 - x2*y2 - x3*y3 - x4*y4)  + \
\  sq(x1*y2 + x2*y1 + x3*y4 - x4*y3)  + \
\  sq(x1*y3 - x2*y4 + x3*y1 + x4*y2)  + \
\  sq(x1*y4 + x2*y3 - x3*y2 + x4*y1)";
(*Takes up to three minutes...*)
by (cring_simp 1);
qed "Lagrange_lemma";
