(*  Title:      LatMorph.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some lattice morphisms.

TODO:
  more morphisms (?)
  more theorems
*)

LatMorph = LatInsts +

constdefs
  is_mono       :: "('a::le => 'b::le) => bool"
  "is_mono f == ALL x y. x [= y --> f x [= f y"

  is_inf_morph  :: "('a::lattice => 'b::lattice) => bool"
  "is_inf_morph f == ALL x y. f (x && y) = f x && f y"

  is_sup_morph  :: "('a::lattice => 'b::lattice) => bool"
  "is_sup_morph f == ALL x y. f (x || y) = f x || f y"

  is_Inf_morph  :: "('a::clattice => 'b::clattice) => bool"
  "is_Inf_morph f == ALL A. f (Inf A) = Inf {f x |x. x:A}"

  is_Sup_morph  :: "('a::clattice => 'b::clattice) => bool"
  "is_Sup_morph f == ALL A. f (Sup A) = Sup {f x |x. x:A}"

end
