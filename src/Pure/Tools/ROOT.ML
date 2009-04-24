(*  Title:      Pure/Tools/ROOT.ML

Miscellaneous tools and packages for Pure Isabelle.
*)

use "named_thms.ML";

(*basic XML support*)
use "xml_syntax.ML";

use "find_theorems.ML";
use "find_consts.ML";

use "auto_solve.ML";

(*quickcheck stub needed here because of pg preferences*)
structure Quickcheck =
struct

val auto = ref false;
val auto_time_limit = ref 5000;

end;
