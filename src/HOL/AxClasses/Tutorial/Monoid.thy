(*  Title:      HOL/AxClasses/Tutorial/Monoid.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Define class "monoid".
*)

Monoid = Sigs +

(* monoids *)

axclass
  monoid < term
  assoc         "(x <*> y) <*> z = x <*> (y <*> z)"
  left_unit     "1 <*> x = x"
  right_unit    "x <*> 1 = x"

end
