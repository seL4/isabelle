(*  Title:      HOL/Integ/IntRing.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   1996 TU Muenchen

The instantiation of Lagrange's lemma for int.
*)

open IntRing;

goal thy "!!i1::int. \
\  (sq i1 + sq i2 + sq i3 + sq i4) * (sq j1 + sq j2 + sq j3 + sq j4) = \
\  sq(i1*j1 - i2*j2 - i3*j3 - i4*j4)  + \
\  sq(i1*j2 + i2*j1 + i3*j4 - i4*j3)  + \
\  sq(i1*j3 - i2*j4 + i3*j1 + i4*j2)  + \
\  sq(i1*j4 + i2*j3 - i3*j2 + i4*j1)";
by (rtac Lagrange_lemma 1);
qed "Lagrange_lemma_int";
