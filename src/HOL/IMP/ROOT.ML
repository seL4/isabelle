(*  Title:      HOL/IMP/ROOT.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow
    Copyright   1995 TUM
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

writeln"Root file for HOL/IMP";
proof_timing := true;
time_use_thy "Expr";
time_use_thy "Transition";
time_use_thy "VC";
