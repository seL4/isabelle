(*  Title:      OrdInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some order instantiations.
*)

OrdInsts = OrdDefs +


(* binary / general products of quasi_orders / orders *)

instance
  "*" :: (quasi_order, quasi_order) quasi_order         (le_prod_refl, le_prod_trans)

instance
  "*" :: (partial_order, partial_order) partial_order   (le_prod_antisym)
  

instance
  fun :: (term, quasi_order) quasi_order                (le_fun_refl, le_fun_trans)

instance
  fun :: (term, partial_order) partial_order            (le_fun_antisym)


(* duals of quasi orders / partial orders / linear orders *)

instance
  dual :: (quasi_order) quasi_order                     (le_dual_refl, le_dual_trans)

instance
  dual :: (partial_order) partial_order                 (le_dual_antisym)


(*FIXME: had to be moved to LatInsts.thy due to some unpleasant
  'feature' in Pure/type.ML

instance
  dual :: (linear_order) linear_order                   (le_dual_lin)
*)

end
