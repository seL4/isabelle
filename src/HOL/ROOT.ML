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
use "$ISABELLE_HOME/src/Provers/clasimp.ML";
use "$ISABELLE_HOME/src/Provers/Arith/nat_transitive.ML";
use "$ISABELLE_HOME/src/Provers/Arith/cancel_sums.ML";
use "$ISABELLE_HOME/src/Provers/Arith/cancel_factor.ML";
use "$ISABELLE_HOME/src/Provers/quantifier1.ML";

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

use_thy "NatDef";

use "Tools/inductive_package.ML";
use_thy "Inductive";

use "Tools/datatype_aux.ML";
use "Tools/datatype_prop.ML";
use "Tools/datatype_rep_proofs.ML";
use "Tools/datatype_abs_proofs.ML";
use "Tools/datatype_package.ML";
use "Tools/primrec_package.ML";
use_thy"Datatype";

use_thy "Arith";
use "arith_data.ML";

use_thy "Recdef";
(*TFL: recursive function definitions*)
cd "$ISABELLE_HOME/src/TFL";
use "sys.sml";
cd "$ISABELLE_HOME/src/HOL";

cd "Integ";
use_thy "Bin";
cd "..";

(*the all-in-one theory*)
use_thy "Main";

print_depth 8;

val HOL_build_completed = ();   (*indicate successful build*)
