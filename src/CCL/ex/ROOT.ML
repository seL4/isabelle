(*  Title:      CCL/ex/ROOT
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes all examples for Classical Computational Logic
*)

CCL_build_completed;	(*Cause examples to fail if CCL did*)

writeln"Root file for CCL examples";
proof_timing := true;
time_use_thy "ex/nat";
time_use_thy "ex/list";
time_use_thy "ex/stream";
time_use_thy "ex/flag";
maketest"END: Root file for CCL examples";
