
Sequents_build_completed;    (*Cause examples to fail if Sequents did*)
writeln"Root file for ILL examples";

set proof_timing;

time_use_thy "washing";

time_use_thy "ILL_predlog";
time_use "ILL_kleene_lemmas.ML";
