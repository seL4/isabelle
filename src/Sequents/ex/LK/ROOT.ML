(*  Title:      LK/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Executes all examples for Classical Logic. 
*)

Sequents_build_completed;    (*Cause examples to fail if LK did*)

writeln"Root file for LK examples";

proof_timing := true;
time_use "ex/LK/prop.ML";
time_use "ex/LK/quant.ML";
time_use "ex/LK/hardquant.ML";

maketest"END: Root file for LK examples";
