(*  Title:      Cube/ROOT
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

The Lambda-Cube a la Barendregt
*)

val banner = "Barendregt's Lambda-Cube";
writeln banner;

init_thy_reader();

print_depth 1;  
use_thy "Cube";

init_pps ();
print_depth 8;

val Cube_build_completed = ();  (*indicate successful build*)
