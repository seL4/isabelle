
Sequents_build_completed;    (*Cause examples to fail if LK did*)

writeln"Root file for ILL examples";

proof_timing := true;
time_use_thy "ex/ILL/washing";

time_use_thy "ex/ILL/ILL_predlog";
time_use "ex/ILL/ILL_kleene_lemmas.ML";

maketest"END: Root file for ILL examples";
