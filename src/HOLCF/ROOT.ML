(*  Title:	HOLCF/ROOT
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright	1993 Technische Universitaet Muenchen

ROOT file for the conservative extension of HOL by the LCF logic.
Should be executed in subdirectory HOLCF.
*)

val banner = "HOLCF with sections axioms,ops,domain,generated";
init_thy_reader();

(* start 8bit 1 *)
(* end 8bit 1 *)

writeln banner;
print_depth 1;

use_thy "HOLCF";

(* install sections: axioms, ops *)

use "ax_ops/holcflogic.ML";
use "ax_ops/thy_axioms.ML";
use "ax_ops/thy_ops.ML";
use "ax_ops/thy_syntax.ML";


(* install sections: domain, generated *)

use "domain/library";
use "domain/syntax";
use "domain/axioms";
use "domain/theorems";
use "domain/extender";
use "domain/interface";

init_thy_reader();
init_pps ();

print_depth 100;  

val HOLCF_build_completed = ();	(*indicate successful build*)
