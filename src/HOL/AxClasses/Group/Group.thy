(*  Title:      Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

Group = Sigs + Fun +

(* semigroups *)

axclass
  semigroup < times
  assoc         "(x * y) * z = x * (y * z)"


(* groups *)

axclass
  group < one, inverse, semigroup
  left_unit     "1 * x = x"
  left_inverse  "inverse x * x = 1"


(* abelian groups *)

axclass
  agroup < group
  commut        "x * y = y * x"

end
