(*  Title:      MonoidGroupInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some class inclusions or 'abstract instantiations'.
*)

MonoidGroupInsts = Group + Monoid +


(* monoids are semigroups *)

instance
  monoid < semigroup            (Monoid.assoc)


(* groups are monoids *)

instance
  group < monoid                ("Group.assoc", "Group.left_unit", "Group.right_unit")

end
