(*  Title:      HOL/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Adds Classical Higher-order Logic to a database containing Pure Isabelle.
Should be executed in the subdirectory HOL.
*)

val banner = "Higher-Order Logic";
writeln banner;

print_depth 1;

(* Add user sections *)
use "$ISABELLE_HOME/src/Pure/section_utils.ML";
use "thy_syntax.ML";

use "$ISABELLE_HOME/src/Provers/simplifier.ML";
use "$ISABELLE_HOME/src/Provers/splitter.ML";
use "$ISABELLE_HOME/src/Provers/hypsubst.ML";
use "$ISABELLE_HOME/src/Provers/classical.ML";
use "$ISABELLE_HOME/src/Provers/blast.ML";
use "$ISABELLE_HOME/src/Provers/Arith/nat_transitive.ML";
use "$ISABELLE_HOME/src/Provers/Arith/cancel_sums.ML";
use "$ISABELLE_HOME/src/Provers/Arith/cancel_factor.ML";
use "$ISABELLE_HOME/src/Provers/quantifier1.ML";

use "thy_data.ML";

use_thy "HOL";
use "hologic.ML";
use "cladata.ML";
use "simpdata.ML";

use_thy "Ord";
use_thy "subset";
use "Tools/typedef_package.ML";
use_thy "Sum";
use_thy "Gfp";

use "Tools/record_package.ML";
use_thy "Record";

use "datatype.ML";
use_thy "Arith";
use "arith_data.ML";

use "ind_syntax.ML";
use "add_ind_def.ML";
use_thy "intr_elim";
use_thy "indrule";
use_thy "Inductive";

use_thy "RelPow";
use_thy "Finite";
use_thy "Sexp";
use_thy "WF_Rel";
use_thy "Map";

(*TFL: recursive function definitions*)
cd "$ISABELLE_HOME/src/TFL";
use "sys.sml";

print_depth 8;

val HOL_build_completed = ();   (*indicate successful build*)
