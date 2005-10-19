(*  Title:      HOL/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Classical Higher-order Logic.
*)

val banner = "Higher-Order Logic";
writeln banner;

use "hologic.ML";

use "~~/src/Provers/splitter.ML";
use "~~/src/Provers/hypsubst.ML";
use "~~/src/Provers/induct_method.ML";
use "~~/src/Provers/make_elim.ML";
use "~~/src/Provers/classical.ML";
use "~~/src/Provers/blast.ML";
use "~~/src/Provers/clasimp.ML";
use "~~/src/Provers/Arith/fast_lin_arith.ML";
use "~~/src/Provers/Arith/cancel_sums.ML";
use "~~/src/Provers/Arith/assoc_fold.ML";
use "~~/src/Provers/quantifier1.ML";
use "~~/src/Provers/Arith/cancel_numerals.ML";
use "~~/src/Provers/Arith/combine_numerals.ML";
use "~~/src/Provers/Arith/cancel_numeral_factor.ML";
use "~~/src/Provers/Arith/extract_common_term.ML";
use "~~/src/Provers/Arith/cancel_div_mod.ML";
use "~~/src/Provers/quasi.ML";
use "~~/src/Provers/order.ML";

with_path "Integ" use_thy "Main";

path_add "~~/src/HOL/Library";

Goal "True";  (*leave subgoal package empty*)

val HOL_proofs = !proofs;
