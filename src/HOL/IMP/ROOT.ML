(*  Title:      HOL/IMP/ROOT.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow
    Copyright   1995 TUM
*)

writeln"Root file for HOL/IMP";

set proof_timing;
time_use_thy "Expr";
time_use_thy "Transition";
time_use_thy "VC";
