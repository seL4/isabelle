(*  Title:      HOL/ex/Lagrange.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen


This theory only contains a single theorem, which is a lemma in Lagrange's
proof that every natural number is the sum of 4 squares.  Its sole purpose is
to demonstrate ordered rewriting for commutative rings.

The enterprising reader might consider proving all of Lagrange's theorem.
*)
Lagrange = Ring +

constdefs sq :: 'a::times => 'a
         "sq x == x*x"

end
