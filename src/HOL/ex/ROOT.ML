(*  Title:      HOL/ex/ROOT
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Executes miscellaneous examples for Higher-Order Logic. 
*)

HOL_build_completed;    (*Cause examples to fail if HOL did*)

writeln "Root file for HOL examples";
proof_timing := true;
time_use     "cla.ML";
time_use     "meson.ML";
time_use     "mesontest.ML";
time_use_thy "String";
time_use_thy "BT";
time_use_thy "Perm";
time_use_thy "InSort";
time_use_thy "Qsort";
time_use_thy "LexProd";
time_use_thy "Puzzle";
time_use_thy "Mutil";
time_use_thy "NatSum";
time_use     "set.ML";
time_use_thy "SList";
time_use_thy "LList";
time_use_thy "Acc";
time_use_thy "PropLog";
time_use_thy "Term";
time_use_thy "Simult";
time_use_thy "MT";

writeln "END: Root file for HOL examples";
