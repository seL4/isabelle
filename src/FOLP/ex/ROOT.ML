(*  Title:      FOLP/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Executes all examples for First-Order Logic. 
*)

writeln"Root file for FOLP examples";

FOLP_build_completed;   (*Cause examples to fail if FOLP did*)

proof_timing := true;

time_use     "intro.ML";
time_use_thy "Nat";
time_use     "foundn.ML";

writeln"\n** Intuitionistic examples **\n";
time_use     "int.ML";

val thy = IFOLP.thy  and  tac = Int.fast_tac 1;
time_use     "prop.ML";
time_use     "quant.ML";

writeln"\n** Classical examples **\n";
time_use     "cla.ML";
time_use_thy "If";

val thy = FOLP.thy  and  tac = Cla.fast_tac FOLP_cs 1;
time_use     "prop.ML";
time_use     "quant.ML";

OS.FileSys.chDir "..";
maketest"END: Root file for FOLP examples";
