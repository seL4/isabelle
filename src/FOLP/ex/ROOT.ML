(*  Title: 	FOLP/ex/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Executes all examples for First-Order Logic. 
*)

writeln"Root file for FOLP examples";

FOLP_build_completed;	(*Cause examples to fail if FOLP did*)

proof_timing := true;

time_use     "ex/intro.ML";
time_use_thy "ex/Nat";
time_use     "ex/foundn.ML";

writeln"\n** Intuitionistic examples **\n";
time_use     "ex/int.ML";

val thy = IFOLP.thy  and  tac = Int.fast_tac 1;
time_use     "ex/prop.ML";
time_use     "ex/quant.ML";
commit();

writeln"\n** Classical examples **\n";
time_use     "ex/cla.ML";
time_use_thy "ex/If";

val thy = FOLP.thy  and  tac = Cla.fast_tac FOLP_cs 1;
time_use     "ex/prop.ML";
time_use     "ex/quant.ML";

make_chart ();   (*make HTML chart*)

maketest"END: Root file for FOLP examples";
