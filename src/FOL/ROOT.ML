(*  Title:      FOL/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

First-Order Logic.
*)

val banner = "First-Order Logic with Natural Deduction";

writeln banner;

print_depth 1;  

use "~~/src/Provers/simplifier.ML";
use "~~/src/Provers/splitter.ML";
use "~~/src/Provers/ind.ML";
use "~~/src/Provers/hypsubst.ML";
use "~~/src/Provers/classical.ML";
use "~~/src/Provers/blast.ML";
use "~~/src/Provers/clasimp.ML";
use "~~/src/Provers/quantifier1.ML";

use_thy "FOL";

print_depth 8;
