(*  Title:      Sequents/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Adds Classical Sequent Calculus to a database containing pure Isabelle. 
*)

val banner = "Sequent Calculii";
writeln banner;

print_depth 1;  

use_thy "Sequents";
use "prover.ML";

use_thy "LK";
use_thy "ILL";

use_thy "Modal0";
use_thy"T";
use_thy"S4";
use_thy"S43";

print_depth 8;

val Sequents_build_completed = ();    (*indicate successful build*)
