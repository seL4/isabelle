(*
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1995 Technische Universitaet Muenchen

*)

HOLCF_build_completed;    (*Cause examples to fail if HOLCF did*)

writeln"Root file for HOLCF examples: explicit domain axiomatisation";
proof_timing := true;

time_use_thy "Dnat";
time_use_thy "Dnat2";
time_use_thy "Stream";
time_use_thy "Stream2";
time_use_thy "Dlist";

time_use_thy "Coind";
time_use_thy "Dagstuhl";
time_use_thy "Focus_ex";

cd "..";
maketest "END: Root file for HOLCF examples: explicit domain axiomatization";
