(*  Title:      LatInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some lattice instantiations.
*)

LatInsts = LatPreInsts +


(* linear orders are lattices *)

instance
  lin_order < lattice                   (allI, exI, min_is_inf, max_is_sup)


(* complete lattices are lattices *)

instance
  clattice < lattice                    (allI, exI, Inf_is_inf, Sup_is_sup)


(* products of lattices are lattices *)

instance
  "*" :: (lattice, lattice) lattice     (allI, exI, prod_is_inf, prod_is_sup)

instance
  fun :: (term, lattice) lattice        (allI, exI, fun_is_inf, fun_is_sup)


(* duals of lattices are lattices *)

instance
  dual :: (lattice) lattice             (allI, exI, dual_is_inf, dual_is_sup)

(*FIXME bug workaround (see also OrdInsts.thy)*)
instance
  dual :: (lin_order) lin_order         (le_dual_lin)

end
