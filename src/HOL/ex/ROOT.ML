(*  Title:      HOL/ex/ROOT
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Executes miscellaneous examples for Higher-Order Logic. 
*)

HOL_build_completed;    (*Cause examples to fail if HOL did*)

writeln "Root file for HOL examples";
proof_timing := true;

(**Some examples of recursive function definitions: the TFL package**)
time_use_thy "Fib";
time_use_thy "Primes";

time_use_thy "NatSum";
time_use     "cla.ML";
time_use     "meson.ML";
time_use     "mesontest.ML";
(** time_use "mesontest2.ML";  ULTRA SLOW **)
time_use_thy "String";
time_use_thy "BT";
time_use_thy "InSort";
time_use_thy "Qsort";
time_use_thy "Puzzle";

time_use     "set.ML";
time_use_thy "MT";

writeln "END: Root file for HOL examples";
