(*  Title:      Pure/Tools/ROOT.ML

Miscellaneous tools and packages for Pure Isabelle.
*)

use "named_thms.ML";
use "isabelle_process.ML";

(*basic XML support*)
use "xml_syntax.ML";

use "find_theorems.ML";
use "find_consts.ML";

(*quickcheck/autosolve needed here because of pg preferences*)
use "../../Tools/quickcheck.ML";
use "../../Tools/auto_solve.ML";
