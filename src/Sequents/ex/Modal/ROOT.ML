(*  Title:      Modal/ex/ROOT
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

Sequents_build_completed;    (*Cause examples to fail if Sequents did*)

proof_timing := true;

writeln "\nTheorems of T\n";
fun try s = (writeln s; prove_goal T.thy s (fn _=> [T_Prover.solve_tac 2]));
time_use "Modal/Tthms.ML";

writeln "\nTheorems of S4\n";
fun try s = (writeln s; prove_goal S4.thy s (fn _=> [S4_Prover.solve_tac 2]));
time_use "Modal/Tthms.ML";
time_use "Modal/S4thms.ML";

writeln "\nTheorems of S43\n";
fun try s = (writeln s;
             prove_goal S43.thy s (fn _=> [S43_Prover.solve_tac 2 ORELSE 
                                           S43_Prover.solve_tac 3]));
time_use "Modal/Tthms.ML";
time_use "Modal/S4thms.ML";
time_use "Modal/S43thms.ML";

cd "..";
maketest"END: Root file for Modal examples";
