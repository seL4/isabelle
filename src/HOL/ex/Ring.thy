(*  Title:      HOL/ex/Ring.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen

Bits of rings.
Main output: a simplification tactic for commutative rings.
*)

Ring = Group +

(* Ring *)

axclass  ring < add_agroup, times
  times_assoc "(x*y)*z = x*(y*z)"
  distribL    "x*(y+z) = x*y + x*z"
  distribR    "(x+y)*z = x*z + y*z"

(* Commutative ring *)

axclass cring < ring
  times_commute "x*y = y*x"

end
