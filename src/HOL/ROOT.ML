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
use "../Pure/section_utils.ML";
use "thy_syntax.ML";

use "../Provers/simplifier.ML";
use "../Provers/splitter.ML";
use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";
use "../Provers/blast.ML";
use "../Provers/nat_transitive.ML";


use_thy "HOL";
use_thy "Ord";
use_thy "subset";
use     "typedef.ML";
use_thy "Sum";
use_thy "Gfp";

use "datatype.ML";
use "ind_syntax.ML";
use "add_ind_def.ML";
use "intr_elim.ML";
use "indrule.ML";
use_thy "Inductive";

use_thy "RelPow";
use_thy "Finite";
use_thy "Sexp";
use_thy "WF_Rel";
use_thy "List";
use_thy "Map";

(*TFL: recursive function definitions*)
cd "../TFL";
use "sys.sml";
cd "../HOL";

print_depth 8;

val HOL_build_completed = ();   (*indicate successful build*)
