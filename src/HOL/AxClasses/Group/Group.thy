(*  Title:      Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

Group = Sigs + Set +

(* semigroups *)

axclass
  semigroup < times
  assoc         "(x * y) * z = x * (y * z)"


(* groups *)

axclass
  group < one, inv, semigroup
  left_unit     "1 * x = x"
  left_inv      "inv x * x = 1"


(* abelian groups *)

axclass
  agroup < group
  commut        "x * y = y * x"

end
