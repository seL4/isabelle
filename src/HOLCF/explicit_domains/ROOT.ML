(*
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1995 Technische Universitaet Muenchen

*)

HOLCF_build_completed;    (*Cause examples to fail if HOLCF did*)

writeln"Root file for HOLCF examples: explicit domain axiomatisation";
proof_timing := true;
time_use_thy "explicit_domains/Dnat";
time_use_thy "explicit_domains/Dnat2";
time_use_thy "explicit_domains/Stream";
time_use_thy "explicit_domains/Stream2";
time_use_thy "explicit_domains/Dlist";

time_use_thy "explicit_domains/Coind";
time_use_thy "explicit_domains/Dagstuhl";
time_use_thy "explicit_domains/Focus_ex";

maketest "END: Root file for HOLCF examples: explicit domain axiomatization";
