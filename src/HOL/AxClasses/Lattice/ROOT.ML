(*  Title:      HOL/AxClasses/Lattice/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic theory of lattices and orders via axiomatic type classes.
*)

open AxClass;

reset eta_contract;
set show_types;
set show_sorts;

time_use_thy "Order";
time_use_thy "OrdDefs";
time_use_thy "OrdInsts";

time_use_thy "Lattice";
time_use_thy "CLattice";

time_use_thy "LatPreInsts";
time_use_thy "LatInsts";

time_use_thy "LatMorph";
