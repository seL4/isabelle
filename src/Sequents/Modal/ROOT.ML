(*  Title:      Modal/ex/ROOT
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

set proof_timing;

writeln "\nTheorems of T\n";
fun try s = (writeln s; prove_goal T.thy s (fn _=> [T_Prover.solve_tac 2]));
time_use "Tthms.ML";

writeln "\nTheorems of S4\n";
fun try s = (writeln s; prove_goal S4.thy s (fn _=> [S4_Prover.solve_tac 2]));
time_use "Tthms.ML";
time_use "S4thms.ML";

writeln "\nTheorems of S43\n";
fun try s = (writeln s;
             prove_goal S43.thy s (fn _=> [S43_Prover.solve_tac 2 ORELSE 
                                           S43_Prover.solve_tac 3]));
time_use "Tthms.ML";
time_use "S4thms.ML";
time_use "S43thms.ML";
