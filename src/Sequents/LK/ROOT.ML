(*  Title:      LK/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Executes all examples for Classical Logic. 
*)

Sequents_build_completed;    (*Cause examples to fail if Sequents did*)

writeln"Root file for LK examples";

set proof_timing;
time_use "prop.ML";
time_use "quant.ML";
time_use "hardquant.ML";
