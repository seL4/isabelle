(*  Title:      HOL/AxClasses/Tutorial/Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Define classes "semigroup", "group", "agroup".
*)

Group = Sigs +

(* semigroups *)

axclass
  semigroup < term
  assoc         "(x <*> y) <*> z = x <*> (y <*> z)"


(* groups *)

axclass
  group < semigroup
  left_unit     "1 <*> x = x"
  left_inverse  "inverse x <*> x = 1"


(* abelian groups *)

axclass
  agroup < group
  commut        "x <*> y = y <*> x"

end
