(*  Title:      HOLCF/ROOT.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

ROOT file for the conservative extension of HOL by the LCF logic.
Should be executed in subdirectory HOLCF.
*)

val banner = "HOLCF";
writeln banner;

print_depth 1;

use_thy "HOLCF";

use "HOLCFLogic.ML";
use "contconsts.ML";

(* domain package *)
use "domain/library.ML";
use "domain/syntax.ML";
use "domain/axioms.ML";
use "domain/theorems.ML";
use "domain/extender.ML";
use "domain/interface.ML";

print_depth 10;  

val HOLCF_build_completed = (); (*indicate successful build*)
