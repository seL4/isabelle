(*  Title:	HOLCF/ROOT
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright	1993 Technische Universitaet Muenchen

ROOT file for the conservative extension of HOL by the LCF logic.
Should be executed in subdirectory HOLCF.
*)

val banner = "Higher-order Logic of Computable Functions; curried version";
writeln banner;
print_depth 1;

init_thy_reader();

use_thy "Fix";
use_thy "Dlist";

use "../Pure/install_pp.ML";
print_depth 8;  

val HOLCF_build_completed = ();	(*indicate successful build*)
