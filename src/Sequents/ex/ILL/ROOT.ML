
Sequents_build_completed;    (*Cause examples to fail if Sequents did*)
writeln"Root file for ILL examples";

set proof_timing;

time_use_thy "ILL/washing";

time_use_thy "ILL/ILL_predlog";
time_use "ILL/ILL_kleene_lemmas.ML";
