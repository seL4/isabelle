(*  Title: 	LCF/ROOT
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

Adds LCF to a database containing First-Order Logic.

This theory is based on Lawrence Paulson's book Logic and Computation.
*)

val banner = "Logic for Computable Functions (in FOL)";
writeln banner;

print_depth 1;
use_thy "lcf";
use"simpdata.ML";
use"pair.ML";
use"fix.ML";

val LCF_build_completed = ();	(*indicate successful build*)
