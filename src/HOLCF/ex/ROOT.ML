(*  Title:      HOLCF/ex/ROOT
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Executes all examples for HOLCF. 
*)

HOLCF_build_completed;    (*Cause examples to fail if HOLCF did*)

writeln"Root file for HOLCF examples";
set proof_timing;

time_use_thy "Dnat";
time_use_thy "Stream";
time_use_thy "Dagstuhl";
time_use_thy "Focus_ex";
time_use_thy "Fix2";
time_use_thy "Hoare";
time_use_thy "Loop";
time_use "loeckx.ML";
