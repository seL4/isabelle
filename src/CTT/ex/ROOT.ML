(*  Title:      CTT/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Executes all examples for Constructive Type Theory. 
*)

CTT_build_completed;    (*Cause examples to fail if CTT did*)

writeln"Root file for CTT examples";

print_depth 2;  
proof_timing := true;
time_use "ex/typechk.ML";
time_use "ex/elim.ML";
time_use "ex/equal.ML";
time_use "ex/synth.ML";

maketest"END: Root file for CTT examples";
