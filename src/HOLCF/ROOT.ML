(*  Title:      HOLCF/ROOT.ML
    ID:         $Id$
    Author:     Franz Regensburger

Conservative (semantic) extension of HOL by the LCF logic.
*)

val banner = "HOLCF";
writeln banner;

print_depth 1;

use_thy "HOLCF";

use "holcf_logic.ML";
use "cont_consts.ML";

(* domain package *)
use "domain/library.ML";
use "domain/syntax.ML";
use "domain/axioms.ML";
use "domain/theorems.ML";
use "domain/extender.ML";
use "domain/interface.ML";

path_add "~~/src/HOLCF/ex";
use_thy "Streams";

print_depth 10;  
