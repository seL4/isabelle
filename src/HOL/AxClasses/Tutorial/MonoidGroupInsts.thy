(*  Title:      HOL/AxClass/Tutorial/MonoidGroupInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Add derived class inclusions monoid < semigroup and group < monoid to
type signature -- some kind of 'abstract instantiations'.
*)

MonoidGroupInsts = Monoid + Group +

(* monoids are semigroups *)

instance
  monoid < semigroup            (Monoid.assoc)


(* groups are monoids *)

instance
  group < monoid                (assoc, left_unit, right_unit)

end
