(*  Title: 	Cube/ROOT
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

The Lambda-Cube a la Barendregt
*)

val banner = "Barendregt's Lambda-Cube";
writeln banner;

init_thy_reader();

print_depth 1;  
use_thy "Cube";

use "../Pure/install_pp.ML";
print_depth 8;

make_chart ();   (*make HTML chart*)

val Cube_build_completed = ();	(*indicate successful build*)
