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

(*old-style theory syntax*)
use "~~/src/Pure/section_utils.ML";
use "thy_syntax.ML";
use "hologic.ML";

use "~~/src/Provers/simplifier.ML";
use "~~/src/Provers/split_paired_all.ML";
use "~~/src/Provers/splitter.ML";
use "~~/src/Provers/hypsubst.ML";
use "~~/src/Provers/classical.ML";
use "~~/src/Provers/blast.ML";
use "~~/src/Provers/clasimp.ML";
use "~~/src/Provers/Arith/fast_lin_arith.ML";
use "~~/src/Provers/Arith/cancel_sums.ML";
use "~~/src/Provers/Arith/cancel_factor.ML";
use "~~/src/Provers/Arith/abel_cancel.ML";
use "~~/src/Provers/Arith/assoc_fold.ML";
use "~~/src/Provers/quantifier1.ML";
use "~~/src/Provers/Arith/combine_coeff.ML";

use_thy "subset";
use "Tools/typedef_package.ML";

use_thy "Inductive";
use_thy "NatDef";

use "Tools/datatype_aux.ML";
use "Tools/datatype_prop.ML";
use "Tools/datatype_rep_proofs.ML";
use "Tools/datatype_abs_proofs.ML";
use "Tools/datatype_package.ML";
use "Tools/primrec_package.ML";
use_thy "Datatype";

(*TFL: recursive function definitions*)
use_thy "WF_Rel";
cd "../TFL"; use "sys.sml"; cd "../HOL";
use_thy "Recdef";

use_thy "Numeral";
cd "Integ";
use_thy "IntDef";
use "simproc.ML";
use_thy "NatBin";
use "bin_simprocs.ML";
cd "..";

(*the all-in-one theory*)
use_thy "Main";

print_depth 8;

Goal "True";  (*leave subgoal package empty*)
