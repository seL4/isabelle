(*  Title:      HOL/Integ/Lagrange.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen


This theory only contains a single thm, which is a lemma in Lagrange's proof
that every natural number is the sum of 4 squares.  It's sole purpose is to
demonstrate ordered rewriting for commutative rings.

The enterprising reader might consider proving all of Lagrange's thm.
*)
Lagrange = Ring +

constdefs sq :: 'a::times => 'a
         "sq x == x*x"

end
