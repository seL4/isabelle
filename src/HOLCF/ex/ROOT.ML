(*  Title:  	HOLCF/ex/ROOT
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994 TU Muenchen

Executes all examples for HOLCF. 
*)

HOLCF_build_completed;    (*Cause examples to fail if HOLCF did*)

writeln"Root file for HOLCF examples";
proof_timing := true;
time_use_thy "ex/Coind";
time_use_thy "ex/Hoare";
time_use_thy "ex/Loop";
maketest     "END: Root file for HOLCF examples";
