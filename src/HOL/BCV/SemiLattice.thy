(*  Title:      HOL/BCV/SemiLattice.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Semilattices
*)

SemiLattice = Plus +

constdefs
 semilat :: "('a::{order,plus} set) => bool"
"semilat A == (!x:A. !y:A. x <= x+y)  &
          (!x:A. !y:A. y <= x+y)  &
          (!x:A. !y:A. !z:A. x <= z & y <= z --> x+y <= z) &
          (!x:A. !y:A. x+y : A)"

end
