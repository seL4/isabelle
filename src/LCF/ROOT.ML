(*  Title:      LCF/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

LCF on top of First-Order Logic.

This theory is based on Lawrence Paulson's book Logic and Computation.
*)

val banner = "Logic for Computable Functions (in FOL)";
writeln banner;

print_depth 1;
use_thy "LCF";
use"simpdata.ML";
use_thy"pair";
use_thy"fix";
