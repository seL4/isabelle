(*  Title:      HOL/AxClasses/Tutorial/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some simple axclass demos that go along with the paper "Using
Axiomatic Type Classes in Isabelle --- a tutorial".  (The NatClass
example resides in directory FOL/ex/.)
*)

set show_types;
set show_sorts;


(* Semigroups *)

use_thy "Semigroup";
use_thy "Semigroups";


(* Basic group theory *)

use_thy "Sigs";
use_thy "Monoid";
use_thy "Group";
use_thy "MonoidGroupInsts";
use_thy "Xor";
use_thy "BoolGroupInsts";
use_thy "ProdGroupInsts";


(* Syntactic classes *)

use_thy "Product";
use_thy "ProductInsts";
