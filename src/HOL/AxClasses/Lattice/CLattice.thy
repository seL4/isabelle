(*  Title:      CLattice.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Complete lattices are orders with infima and suprema of arbitrary
subsets.

TODO:
  derive some more well-known theorems (e.g. ex_Inf == ex_Sup)
*)

CLattice = Order +

axclass
  clattice < partial_order
  ex_Inf       "ALL A. EX inf. is_Inf A inf"
  ex_Sup       "ALL A. EX sup. is_Sup A sup"

constdefs
  Inf           :: "'a::clattice set => 'a"
  "Inf A == @inf. is_Inf A inf"

  Sup           :: "'a::clattice set => 'a"
  "Sup A == @sup. is_Sup A sup"

end
