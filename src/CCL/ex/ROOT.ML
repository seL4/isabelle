(*  Title:      CCL/ex/ROOT
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes all examples for Classical Computational Logic
*)

CCL_build_completed;	(*Cause examples to fail if CCL did*)

writeln"Root file for CCL examples";
proof_timing := true;
loadpath := [".", "ex"];

time_use_thy "ex/Nat";
time_use_thy "ex/List";
time_use_thy "ex/Stream";
time_use_thy "ex/Flag";

make_chart ();   (*make HTML chart*)

maketest"END: Root file for CCL examples";
