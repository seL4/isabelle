
writeln"Root file for LCF examples";
LCF_build_completed;    (*Cause examples to fail if LCF did*)

proof_timing := true;

use"ex.ML";

cd "..";
maketest"END: file for LCF examples";
