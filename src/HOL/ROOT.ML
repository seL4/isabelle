(*  Title:      HOL/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Adds Classical Higher-order Logic to a database containing Pure Isabelle.
Should be executed in the subdirectory HOL.
*)

val banner = "Higher-Order Logic with curried functions";
writeln banner;

print_depth 1;

(* Add user sections *)
use "../Pure/section_utils.ML";
use "thy_syntax.ML";

use "../Provers/splitter.ML";
use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";


use_thy "HOL";

use_thy "Ord";
use_thy "subset";
use     "hologic.ML";
use     "subtype.ML";
use_thy "Prod";
use_thy "Sum";
use_thy "Gfp";
use_thy "Nat";

use "datatype.ML";
use "ind_syntax.ML";
use "add_ind_def.ML";
use "intr_elim.ML";
use "indrule.ML";
use_thy "Inductive";

use_thy "Finite";
use_thy "Sexp";
use_thy "List";

init_pps ();
print_depth 8;

make_chart ();   (*make HTML chart*)

val HOL_build_completed = ();   (*indicate successful build*)
