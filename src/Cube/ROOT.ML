(*  Title: 	Cube/ROOT
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

The Lambda-Cube a la Barendregt
*)

val banner = "Barendregt's Lambda-Cube";
writeln banner;

print_depth 1;  
use_thy "cube";

use "../Pure/install_pp.ML";
print_depth 8;

val Cube_build_completed = ();	(*indicate successful build*)
