(*  Title:      HOL/Integ/IntRingDefs.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   1996 TU Muenchen

Provides the basic defs and thms for showing that int is a commutative ring.
Most of it has been defined and shown already.
*)

IntRingDefs = Integ + Ring +

instance int :: zero
defs zero_int_def "zero::int == $# 0"

end
