(*  Title: 	Cube/ROOT
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

The Lambda-Cube a la Barendregt
*)

val banner = "Barendregt's Lambda-Cube";
writeln banner;

structure Readthy = ReadthyFUN (structure ThySyn = ThySyn);
open Readthy;

print_depth 1;  
use_thy "Cube";

use "../Pure/install_pp.ML";
print_depth 8;

val Cube_build_completed = ();	(*indicate successful build*)
