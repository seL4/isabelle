(*  Title:      Monoid.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

Monoid = Sigs +

(* monoids *)

axclass
  monoid < times, one
  assoc         "(x * y) * z = x * (y * z)"
  left_unit     "1 * x = x"
  right_unit    "x * 1 = x"

end
