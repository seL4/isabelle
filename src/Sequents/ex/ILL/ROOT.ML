
Sequents_build_completed;    (*Cause examples to fail if Sequents did*)
writeln"Root file for ILL examples";

proof_timing := true;
time_use_thy "ILL/washing";

time_use_thy "ILL/ILL_predlog";
time_use "ILL/ILL_kleene_lemmas.ML";

maketest"END: Root file for ILL examples";
