(*  Title: 	LK/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Adds Classical Sequent Calculus to a database containing pure Isabelle. 
Should be executed in the subdirectory LK.
*)

val banner = "Classical First-Order Sequent Calculus";
writeln banner;

init_thy_reader();

print_depth 1;  

use_thy "LK";

use "../Pure/install_pp.ML";
print_depth 8;

val LK_build_completed = ();	(*indicate successful build*)
