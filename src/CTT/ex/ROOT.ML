(*  Title:      CTT/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Executes all examples for Constructive Type Theory. 
*)

writeln"Root file for CTT examples";

CTT_build_completed;    (*Cause examples to fail if CTT did*)

print_depth 2;  
set proof_timing;

time_use "typechk.ML";
time_use "elim.ML";
time_use "equal.ML";
time_use "synth.ML";
