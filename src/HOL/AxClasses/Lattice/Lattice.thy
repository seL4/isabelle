(*  Title:      Lattice.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Lattices are orders with binary (finitary) infima and suprema.
*)

Lattice = Order +

axclass
  lattice < order
  ex_inf       "ALL x y. EX inf. is_inf x y inf"
  ex_sup       "ALL x y. EX sup. is_sup x y sup"

consts
  "&&"          :: "['a::lattice, 'a] => 'a"       (infixl 70)
  "||"          :: "['a::lattice, 'a] => 'a"       (infixl 65)

defs
  inf_def       "x && y == @inf. is_inf x y inf"
  sup_def       "x || y == @sup. is_sup x y sup"

end
