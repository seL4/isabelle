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
  "*" :: (order, order) order                           (le_prod_antisym)
  

instance
  fun :: (term, quasi_order) quasi_order                (le_fun_refl, le_fun_trans)

instance
  fun :: (term, order) order                            (le_fun_antisym)


(* duals of quasi_orders / orders / lin_orders *)

instance
  dual :: (quasi_order) quasi_order                     (le_dual_refl, le_dual_trans)

instance
  dual :: (order) order                                 (le_dual_antisym)


(*FIXME: had to be moved to LatInsts.thy due to some unpleasant
  'feature' in Pure/type.ML

instance
  dual :: (lin_order) lin_order                         (le_dual_lin)
*)

end
