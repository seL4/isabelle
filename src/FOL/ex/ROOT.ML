(*  Title:      FOL/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Executes all examples for First-Order Logic. 
*)

writeln"Root file for FOL examples";

FOL_build_completed;    (*Cause examples to fail if FOL did*)

proof_timing := true;

time_use     "intro.ML";
time_use_thy "Nat";
time_use     "foundn.ML";
time_use_thy "Prolog";

writeln"\n** Intuitionistic examples **\n";
time_use     "int.ML";

val thy = IFOL.thy  and  tac = Int.fast_tac 1;
time_use     "prop.ML";
time_use     "quant.ML";

writeln"\n** Classical examples **\n";
time_use     "mini.ML";
time_use     "cla.ML";
time_use_thy "If";

val thy = FOL.thy  and  tac = Cla.fast_tac FOL_cs 1;
time_use     "prop.ML";
time_use     "quant.ML";

writeln"\n** Simplification examples **\n";
time_use_thy "Nat2";
time_use_thy "List";

writeln"\n** How to declare an oracle **\n";
time_use_thy "IffOracle";


OS.FileSys.chDir "..";
maketest"END: Root file for FOL examples";
