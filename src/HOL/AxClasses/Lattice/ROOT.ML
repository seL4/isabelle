(*  Title:      HOL/AxClasses/Lattice/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic theory of lattices and orders via axiomatic type classes.
*)

open AxClass;

reset HOL_quantifiers;
reset eta_contract;
set show_types;
set show_sorts;

use "tools.ML";

use_thy "Order";
use_thy "OrdDefs";
use_thy "OrdInsts";

use_thy "Lattice";
use_thy "CLattice";

use_thy "LatPreInsts";
use_thy "LatInsts";

use_thy "LatMorph";
