(*  Title: 	FOL/ex/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Executes all examples for First-Order Logic. 
*)

writeln"Root file for FOL examples";

FOL_build_completed;	(*Cause examples to fail if FOL did*)

proof_timing := true;

time_use     "ex/intro.ML";
time_use_thy "ex/Nat";
time_use     "ex/foundn.ML";
time_use_thy "ex/Prolog";

writeln"\n** Intuitionistic examples **\n";
time_use     "ex/int.ML";

val thy = IFOL.thy  and  tac = Int.fast_tac 1;
time_use     "ex/prop.ML";
time_use     "ex/quant.ML";

writeln"\n** Classical examples **\n";
time_use     "ex/mini.ML";
time_use     "ex/cla.ML";
time_use_thy "ex/If";

val thy = FOL.thy  and  tac = Cla.fast_tac FOL_cs 1;
time_use     "ex/prop.ML";
time_use     "ex/quant.ML";

writeln"\n** Simplification examples **\n";
time_use_thy "ex/Nat2";
time_use_thy "ex/List";

make_chart ();   (*make HTML chart*)

maketest"END: Root file for FOL examples";
