(*  Title:      FOL/ex/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for First-Order Logic. 
*)

time_use_thy "First_Order_Logic";
time_use     "intro.ML";
time_use_thy "Nat";
time_use_thy "Natural_Numbers";
time_use     "foundn.ML";
time_use_thy "Prolog";

writeln"\n** Intuitionistic examples **\n";
time_use_thy "int";

val thy = IFOL.thy  and  tac = IntPr.fast_tac 1;
time_use     "prop.ML";
time_use     "quant.ML";

writeln"\n** Classical examples **\n";
time_use     "mini.ML";
time_use     "cla.ML";
time_use_thy "If";

val thy = FOL.thy  and  tac = Cla.fast_tac FOL_cs 1;
time_use     "prop.ML";
time_use     "quant.ML";

time_use_thy "NatClass";

writeln"\n** Simplification examples **\n";
time_use_thy "Nat2";
time_use_thy "List";

writeln"\n** How to declare an oracle **\n";
time_use_thy "IffOracle";
