(*  Title: 	CTT/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Adds Constructive Type Theory to a database containing pure Isabelle. 
Should be executed in the subdirectory CTT.
*)

val banner = "Constructive Type Theory";
writeln banner;

print_depth 1;  

use_thy"ctt";
use "../Provers/typedsimp.ML";
use "rew.ML";
use_thy "arith";
use_thy "bool";

use "../Pure/install_pp.ML";
print_depth 8;

val CTT_build_completed = ();	(*indicate successful build*)
