(*  Title:      Cube/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

The Lambda-Cube a la Barendregt.
*)

val banner = "Barendregt's Lambda-Cube";
writeln banner;

print_depth 1;  

use_thy "Cube";

print_depth 8;

val Cube_build_completed = ();  (*indicate successful build*)
