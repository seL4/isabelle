(*  Title:      HOL/ex/ROOT
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Executes miscellaneous examples for Higher-Order Logic. 
*)

HOL_build_completed;    (*Cause examples to fail if HOL did*)

writeln "Root file for HOL examples";
set proof_timing;

(**Some examples of recursive function definitions: the TFL package**)
time_use_thy "Recdefs";
time_use_thy "Primes";
time_use_thy "Fib";
time_use_thy "Primrec";

time_use_thy "NatSum";
time_use     "cla.ML";
time_use     "meson.ML";
time_use     "mesontest.ML";
(** time_use "mesontest2.ML";  ULTRA SLOW **)
time_use_thy "BT";
time_use_thy "InSort";
time_use_thy "Qsort";
time_use_thy "Puzzle";

time_use_thy "IntRing";

time_use     "set.ML";
time_use_thy "MT";

time_use_thy "StringEx";
time_use_thy "BinEx";

(*Monoids and Groups as predicates over record schemes*)
time_use_thy "MonoidGroup";

(*Groups via locales*)
time_use_thy "PiSets";
time_use_thy "LocaleGroup";


writeln "END: Root file for HOL examples";
