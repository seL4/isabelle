(*  Title:      GroupInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some concrete instantiations: 'structures' and 'functors'.
*)

GroupInsts = GroupDefs +


(* bool *)

instance
  bool :: semigroup                     (bool_assoc)
instance
  bool :: monoid                        (bool_assoc, bool_left_unit, bool_right_unit)
instance
  bool :: group                         (bool_left_unit, bool_left_inv)
instance
  bool :: agroup                        (bool_commut)


(* cartesian products *)

instance
  "*" :: (semigroup, semigroup) semigroup       (prod_assoc)
instance
  "*" :: (monoid, monoid) monoid                (prod_assoc, prod_left_unit, prod_right_unit)
instance
  "*" :: (group, group) group                   (prod_left_unit, prod_left_inv)
instance
  "*" :: (agroup, agroup) agroup                (prod_commut)


(* function spaces *)

instance
  fun :: (term, semigroup) semigroup            (fun_assoc)
instance
  fun :: (term, monoid) monoid                  (fun_assoc, fun_left_unit, fun_right_unit)
instance
  fun :: (term, group) group                    (fun_left_unit, fun_left_inv)
instance
  fun :: (term, agroup) agroup                  (fun_commut)

end
